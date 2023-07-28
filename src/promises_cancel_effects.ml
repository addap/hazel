open Effect
open Effect.Deep

(* separate unit type *)
type exit = Exit_scheduler

(* Promise is either done or contains a list of waiting fibers. *)
type 'a status =
  | Done of 'a
  | Waiting of ('a, exit) continuation list

type 'a promise =
  'a status ref

(* optional result of fiber 
   option is None if fiber was cancelled and attempted IO *)
type 'a fiber_result = 'a option

(* Each fiber has a cancel context that includes a flag if it's cancelled and the number of successful IO operations. *)
type cancel_ctx = bool ref * int ref
type fiber_input = unit

(* Spawning a new fiber returns a promise to it's result and a cancel context. *)
type _ Effect.t += Async : (fiber_input -> 'a) -> ('a fiber_result promise * cancel_ctx) t
(* Awaiting the promise returns the result. *)
type _ Effect.t += Await : 'a fiber_result promise -> 'a fiber_result t
(* Checking if the current fiber is cancelled. Will not return if it is cancelled. *)
type _ Effect.t += CheckFail : unit -> unit t
(* Cancel the fiber of the given cancel context. *)
type _ Effect.t += Cancel : cancel_ctx -> int t

let async e = perform (Async e)
let await p = perform (Await p)
let yield() = ignore (async(fun _ -> ()))
(* Set the cancel flag to true and return the latest number of successful IO operations. *)
let fiber_cancel (cc: cancel_ctx) = perform (Cancel cc)

(* Generic I/O function with some argument.
   Requests the cancellaiton flag to check if operation is allowed. *)
let io_unchecked x = Printf.printf "%s: Performing IO.\n" x
let io x: unit = 
  perform (CheckFail ());
  io_unchecked x


(* Fiber context is a promise for the result and a cancel context. *)
let new_fiber_ctx () : ('a promise * cancel_ctx) = 
  let p = ref (Waiting []) in
  let c = ref false in
  let state = ref 0 in
  (p, (c, state))

let run (main : fiber_input -> unit) : unit =
  let q : (unit -> exit) Queue.t = Queue.create() in
  let next() =
    if not (Queue.is_empty q) then (Queue.take q) () else Exit_scheduler
  in
  let rec fulfill: type res. (res fiber_result promise * cancel_ctx) -> (fiber_input -> res) -> exit = fun (p, (c, state)) e ->
    (* deep handler in Ocaml5 *)
    match_with e () {
      retc = (fun v ->
        match !p with
        (* The promise is not fulfilled, so wake up all waiting fibers. *)
        | Waiting ks ->
            let result = Some v in 
            List.iter (fun k -> Queue.add (fun () -> continue k result) q) ks;
            p := Done result;
            next()
        | Done _ ->
            assert false);
      effc = (fun (type a) (eff: a Effect.t) : ((a, exit) continuation -> exit) option ->
        match eff with
        (* Create new fiber context and run the function. *)
        | Async e -> Some (fun k ->
            let pc = new_fiber_ctx () in
            Queue.add (fun () -> continue k pc) q;
            fulfill pc e)
        (* Check if promise is done and enqueue in waiting list if necessary. *)
        | Await p -> Some (fun k -> 
            match !p with
            | Done y ->
                continue k y
            | Waiting ks ->
                p := Waiting (k :: ks);
                next())
        (* If cancelled, similar to `retc`, wake up all waiters and run next fiber. *)
        | CheckFail () -> Some (fun k ->
            if !c
            then begin
              Printf.printf "Fail when performing IO while cancelled.\n";
              match !p with
              | Waiting ks ->
                  let result = None in 
                  List.iter (fun k -> Queue.add (fun () -> continue k result) q) ks;
                  p := Done result;
                  next()
              | Done _ ->
                  assert false
              end 
            (* if the fiber is not cancelled, return *)
            else begin
              state := !state + 1;
              continue k ()
            end)
        | Cancel (c', state') -> Some (fun k -> 
            c' := true;
            continue k !state'
          )
        | _ -> None);
      exnc = raise
    }
  in
  let pc = new_fiber_ctx () in
  let Exit_scheduler = fulfill pc main in 
  ()

let main () =
  (* Run two sub-fibers that do IO.
     Cancel one after a while and assert that it does not do IO afterwards. *)
  let (p1, c1) = async (fun () -> 
    for _ = 1 to 5 do
      io "fiber1";
      yield()
    done;
    5) in
  let (p2, c2) = async (fun () -> 
    for _ = 1 to 5 do
      io "fiber2";
      yield()
    done;
    5) in
  (* Let the other fibers run *)
  yield();
  (* Cancel one fiber.  *)
  let io_ops_expected = fiber_cancel c1 in 
  let res1 = await p1 in 
  let res2 = await p2 in 
  (* The number of reported IO ops should never change after cancellation. *)
  assert (io_ops_expected = !(snd c1));
  match (res1, res2) with 
  (Some a, Some b) -> Printf.printf "Both fibers ran to completion.\n"
  | _ -> Printf.printf "A fiber was cancelled.\n";
  Printf.printf "Fiber 1: %d IO ops\tFiber 2: %d IO ops" (!(snd c1)) (!(snd c2))

let _ =
  Printf.printf "\n";
  run main