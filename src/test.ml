(* [trap()] performs the effect [Trap]. *)

effect Trap : unit -> unit

let trap () =
  perform (Trap())

(* [handle test] evaluates the function call [test trap] under a handler that
   handles the effect [Trap] by invoking the captured continuation twice. It
   exploits [Obj.clone_continuation], an unsafe feature of Multicore OCaml. *)

let handle test =
  match
    test trap
  with
  | effect (Trap()) k ->
      let k' = Obj.clone_continuation k in
      continue k ();
      continue k' ()
  | () ->
      ()

(* The [test] function is taken from de Vilhena and Pottier's paper. When
   [handle test] is executed, the semantics of Multicore OCaml indicates
   that the code that follows the call to [f] is executed twice, so [x]
   is incremented twice, first from 0 to 1, then from 1 to 2, causing
   an assertion failure. *)

(* In reality, with Multicore OCaml 4.10.0, this assertion failure is *not*
   observed, because the compiler performs an *incorrect* optimization.
   Perhaps it decides to allocate [x] on the stack instead of in the heap, or
   perhaps it performs a form of constant propagation; either way, the message
   "Yo, x is 1" is printed twice, and the assertion succeeds twice. This shows
   that the compiler is incorrect in the presence of [clone_continuation]. *)

let test f =
  let x = ref 0 in
  f();
  x := !x + 1;
  Printf.printf "Yo, x is %d\n%!" !x;
  assert (!x = 1)

let () =
  Printf.printf "Test number one:\n%!";
  handle test

(* This variant of the [test] function involves an application of the
   identity function [id] which prevents the compiler from optimizing
   the code. In this case, as expected, the messages "Yo, x is 1" and
   "Yo, x is 2" are observed, then the assertion fails. This shows
   that multi-shot continuations break the simple Separation Logic
   argument (based on the bind rule and on the frame rule) which shows
   that the assertion must succeed. *)

let id x = x

let test f =
  let x = id (ref 0) in
  f();
  x := !x + 1;
  Printf.printf "Yo, x is %d\n%!" !x;
  assert (!x = 1)

let () =
  Printf.printf "Test number two:\n%!";
  handle test
