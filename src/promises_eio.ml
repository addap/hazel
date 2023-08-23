open Effect
open Effect.Deep

module type CQS = sig
  type 'a t
  type req

  val create : unit -> 'a t
  val suspend : 'a t -> 'a -> req
  val cancel : 'a t -> req -> unit
  val resume_all : 'a t -> 'a list
end 

module Implementation(Cqs : CQS) = struct
  (* separate unit type *)
  type exit = Exit_scheduler
  type 'a waker = 'a -> unit
  type 'a suspender = 'a waker -> unit
  
  (* Promise is either done or contains a CQS of waker functions. *)
  type 'a status =
    | Done of 'a
    | Waiting of unit waker Cqs.t

  type 'a promise =
    'a status ref

  (* Forking a new fiber is uninteresting from the scheduler's perspective. The promise handling happens inside the function. *)
  type _ Effect.t += Fork : (unit -> unit) -> unit t
  (* Suspending passes a suspender function to the scheduler which calls it with a waker function, which will put the continuation back into the run queue. *)
  type _ Effect.t += Suspend : 'a suspender -> 'a t

  let fork f = perform (Fork f)
  let suspend suspender = perform (Suspend suspender)

  let new_promise () : 'a promise = 
    ref (Waiting (Cqs.create ()))
    
  let fork_promise f : 'a promise =
    let p = new_promise () in
    fork (fun () ->
      let v = f () in
      match !p with
      | Done _ -> raise (Failure "unreachable")
      | Waiting cqs -> 
        p := Done v;
        let wakers = Cqs.resume_all cqs in
        List.iter (fun waker -> waker ()) wakers
    );
    p
    
  let await (p : 'a promise) : 'a =
    match !p with
    | Done v -> v
    | Waiting cqs ->
      suspend (fun waker ->
        let req = Cqs.suspend cqs waker in
        match !p with
        | Done _ -> 
          Cqs.cancel cqs req; 
          waker()
        | Waiting _ -> ()
      );
      match !p with
      | Done v -> v
      | Waiting _ -> raise (Failure "unreachable")

  let run (main : unit -> unit) : unit =
    let q : (unit -> exit) Queue.t = Queue.create() in
    let next () =
      match Queue.take_opt q with
      | None -> Exit_scheduler
      | Some f -> f ()
    in
    let rec fulfill: (unit -> unit) -> exit = fun e ->
      (* deep handler in Ocaml5 *)
      match_with e () {
        retc = (fun () -> next ());
        effc = (fun (type a) (eff: a Effect.t) : ((a, exit) continuation -> exit) option -> 
          match eff with
          | Fork f -> Some (fun k ->
              Queue.add (fun () -> continue k ()) q;
              fulfill f)
          (* Check if promise is done and enqueue in waiting list if necessary. *)
          | Suspend suspender -> Some (fun k -> 
              let waker = fun v -> Queue.add (fun () -> continue k v) q in
              suspender waker;
              next ())
          | _ -> None);
        exnc = raise 
      }
    in
    let Exit_scheduler = fulfill main in 
    ()
end