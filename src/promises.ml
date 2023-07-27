(* This is the cooperative concurrency library in Multicore OCaml 4.10.0. *)
open Effect
open Effect.Deep

type exit = Exit_scheduler
type 'a status =
  | Done of 'a
  | Waiting of ('a, exit) continuation list

type 'a promise =
  'a status ref

type _ Effect.t += Async : (unit -> 'a) -> 'a promise t
type _ Effect.t += Await : 'a promise -> 'a t

let async e = perform (Async e)
let await p = perform (Await p)
let yield() = ignore (async(fun _ -> ()))

let new_promise () = ref (Waiting [])

let run (main : unit -> unit) : unit =
  let q : (unit -> exit) Queue.t = Queue.create() in
  let next() =
    if not (Queue.is_empty q) then (Queue.take q) () else Exit_scheduler
  in
  let rec fulfill: type a. a promise -> (unit -> a) -> exit = fun p e ->
    match_with e () {
      retc = (fun v ->
        match !p with
        | Waiting ks ->
            List.iter (fun k -> Queue.add (fun () -> continue k v) q) ks;
            p := Done v;
            next()
        | Done _ ->
            assert false);
      effc = (fun (type a) (eff: a Effect.t) : ((a, exit) continuation -> exit) option ->
        match eff with
        | Async e -> Some (fun k ->
            let p = new_promise () in
            Queue.add (fun () -> continue k p) q;
            fulfill p e)
        | Await p -> Some (fun k -> 
            begin match !p with
            | Done y ->
                continue k y
            | Waiting ks ->
                p := Waiting (k :: ks);
                next()
            end)
        | _ -> None);
      exnc = raise
    }
  in
  let p = new_promise () in
  let Exit_scheduler = fulfill p main in 
  ()


(* let main () =
  let r = ref None in
  let f() =
    let rec loop() =
      match !r with
      | None   ->
          yield(); loop()
      | Some p ->
          Printf.printf "This line shall be printed...\n";
          await p;
          Printf.printf "...but this line shall never know the world!\n"
    in
    loop ()
  in
  let p = async f in
  r := Some p

let _ =
  run main;
  Printf.printf "[run] has terminated.\n" *)

let main () =
  let p = async (fun () -> 3) in
  Printf.printf "I have computed %d\n" ((await p) + (await p))

let _ =
  run main
