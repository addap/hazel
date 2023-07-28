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

(* Empty type for exception-like effects *)
type void = |

(* optional result of fiber 
   option is None if fiber was cancelled and attempted IO
   int is the final state of IO operations. *)
type 'a fiber_result = 'a option * int

(* Each fiber has a cancel context that includes a flag if it's cancelled and the number of successful IO operations. *)
type cancel_ctx = bool ref * int ref
(* Same as cancel_ctx but theoretically opaque. Can be used to request a real cancel_ctx to change it. *)
type cancel_handle = cancel_ctx
type fiber_input = unit

(* Spawning a new fiber returns a promise to it's result and a cancel context. *)
type _ Effect.t += Async : (fiber_input -> 'a) -> ('a fiber_result promise * cancel_ctx) t
(* Awaiting the promise returns the result. *)
type _ Effect.t += Await : 'a fiber_result promise -> 'a fiber_result t
(* Failing does not return *)
type _ Effect.t += Fail : unit -> void t
(* GetContext gives a fiber access to its own cancel context. Not sure how to formalize. *)
type _ Effect.t += GetContext : unit -> cancel_ctx t
(* GetOtherContext gives a fiber access to its own cancel context. Not sure how to formalize. *)
type _ Effect.t += GetOtherContext : cancel_handle -> cancel_ctx t

let async e = perform (Async e)
let await p = perform (Await p)
let yield() = ignore (async(fun _ -> ()))
(* Set the cancel flag to true and return the latest number of successful IO operations. 
   After this function returns, it does not access the cancel_ctx anymore. *)
let fiber_cancel (h: cancel_handle) = 
  let (c, state) = perform (GetOtherContext h) in
  c := true;
  !state

let fail() = ignore (perform (Fail ()))

(* Generic I/O function with some argument.
   Requests the cancellaiton flag to check if operation is allowed. *)
let io_unchecked x = Printf.printf "%s: Performing IO.\n" x
let io x: unit = 
  let (c, state) = perform (GetContext ()) in 
  if !c
  then begin
    Printf.printf "Fail when performing IO while cancelled.\n";
    fail ()
  end else begin
    state := !state + 1;
    io_unchecked x
  end

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
            let result = (Some v, !state) in 
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
        (* Return the cancel context that `fulfill` was called with. Works because every continuation includes its callstack. *)
        | GetContext () -> Some (fun k -> continue k (c, state))
        | GetOtherContext (c, state) -> Some (fun k -> continue k (c, state))
        (* Similar to `retc`, wake up all waiters and run next fiber. *)
        | Fail () -> Some (fun _ ->
            match !p with
            | Waiting ks ->
                (* we must be cancelled at this point. *)
                if !c
                then begin
                  let result = (None, !state) in 
                  List.iter (fun k -> Queue.add (fun () -> continue k result) q) ks;
                  p := Done result
                end else 
                  assert false;
                next()
            | Done _ ->
                assert false);
        | _ -> None);
      exnc = raise
    }
  in
  let pc = new_fiber_ctx () in
  let Exit_scheduler = fulfill pc main in 
  ()

let main _ =
  (* Run two sub-fibers that do IO.
     Cancel one after a while and assert that it does not do IO afterwards. *)
  let (p1, h1) = async (fun () -> 
    for _ = 1 to 5 do
      io "fiber1";
      yield()
    done;
    5) in
  let (p2, h2) = async (fun () -> 
    for _ = 1 to 5 do
      io "fiber2";
      yield()
    done;
    5) in
  (* Let the other fibers run *)
  yield();
  (* Cancel one fiber.  *)
  let io_ops_expected = fiber_cancel h1 in 
  let (res1, state1) = await p1 in 
  let (res2, state2) = await p2 in 
  (* The number of reported IO ops should never change after cancellation. *)
  assert (io_ops_expected = state1);
  match (res1, res2) with 
  (Some a, Some b) -> Printf.printf "Both fibers ran to completion.\n"
  | _ -> Printf.printf "A fiber was cancelled.\n";
  Printf.printf "Fiber 1: %d IO ops\tFiber 2: %d IO ops" (state1) (state2)

let _ =
  Printf.printf "\n";
  run main