(* This is the cooperative concurrency library in Multicore OCaml 4.10.0. *)

type 'a status =
  | Done of 'a
  | Waiting of ('a, unit) continuation list

type 'a promise =
  'a status ref

effect Async : (unit -> 'a) -> 'a promise

let async e =
  perform (Async e)

effect Await : 'a promise -> 'a

let await p =
  perform (Await p)

let run (main : unit -> unit) : unit =
  let q : (unit -> unit) Queue.t =
    Queue.create()
  in
  let next() =
    if not (Queue.is_empty q) then Queue.take q ()
  in
  let rec fulfill : 'a. 'a promise -> (unit -> 'a) -> unit = fun p e ->
    match e() with
    | v ->
        let Waiting ks = !p in
        List.iter (fun k -> Queue.add (fun () -> continue k v) q) ks;
        p := Done v;
        next()
    | effect (Async e') k ->
        let p' = ref (Waiting []) in
        Queue.add (fun () -> continue k p') q;
        fulfill p' e'
    | effect (Await p') k ->
        match !p' with
        | Done v -> continue k v
        | Waiting ks -> p' := Waiting (k :: ks); next()
  in
  fulfill (ref (Waiting [])) main

let main () =
  let r = ref None in
  let p = async (fun () ->
    let rec loop () =
      match !r with
      | None   -> let _ = async (fun () -> ()) in loop ()
      | Some p -> await p
    in
    loop ())
  in
  r := Some p;
  await p

let _ = run main

let main () =
  let p = async (fun () -> 3) in
  Printf.printf "%d\n" ((await p) + (await p))

let _ = run main
