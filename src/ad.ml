(* Reverse-Mode Automatic Differentiation with Effect Handlers. *)

(* This code works in Multicore OCaml 4.12.0. *)

(* The use of effect handlers in this code is based on the code by KC Sivaramakrishnan:

   https://github.com/ocaml-multicore/effects-examples/blob/master/algorithmic_differentiation.ml

   The packaging is different, though; we use expressions in tagless final style.

   This code can be executed in the OCaml toplevel loop via the following commands:

   opam switch create 4.12.0+domains+effects --no-switch # (only once)
   opam exec --switch 4.12.0+domains+effects ocaml       # runs the toplevel loop

 *)


(* -------------------------------------------------------------------------- *)
(** Type Definitions. *)

type 'v num =
  { zero : 'v; one : 'v; add : 'v -> 'v -> 'v; mul : 'v -> 'v -> 'v }

type exp =
  { eval : (* forall *) 'v. 'v num -> 'v -> 'v }

module type AD = sig
  val diff : exp -> exp
end


(* -------------------------------------------------------------------------- *)
(** Forward-Mode AD. *)

module ForwardMode : AD = struct
  let diff (e : exp) : exp = { eval =
    fun (type v) ({ zero; one; add; mul } : v num) (n : v) ->
      let ( + ), ( * ) = add, mul in
      let open struct
        type t = {v : v ; d : v}

        let mk v d = {v; d}

        let num = 
          let zero    = mk zero zero
          and one     = mk one zero
          and add a b = mk (a.v + b.v) (a.d + b.d)
          and mul a b = mk (a.v * b.v) (a.d * b.v + a.v * b.d) in
          { zero; one; add; mul }

        let x = mk n one
        let y = e.eval num x
      end in
      y.d
    }
end


(* -------------------------------------------------------------------------- *)
(** Reverse-Mode AD Using Effect Handlers. *)

module ReverseMode : AD = struct
  let diff (e : exp) : exp = { eval =
    fun (type v) ({ zero; one; add; mul } : v num) (n : v) ->
      let ( + ), ( * ) = add, mul in
      let open struct
  
        type t = O | I | Var of {v : v ; mutable d : v} (* zero | one | var *)
        effect Add : t * t -> t
        effect Mul : t * t -> t
  
        let mk n       = Var {v = n; d = zero}
        let get_v u    = match u with O -> zero | I -> one  | Var u     -> u.v
        let get_d u    = match u with O | I -> assert false | Var u     -> u.d
        let update u i = match u with O | I -> ()    | Var u -> u.d <- u.d + i
  
        let num = 
          let zero = O
          and one = I
          and add a b = perform (Add (a, b))
          and mul a b = perform (Mul (a, b)) in
          { zero; one; add; mul }
  
        let x = mk n
  
        let () =
          match e.eval num x with
          | effect (Add (a, b)) k ->
             let u = mk (get_v a + get_v b) in
             continue k u;
             update a (get_d u);
             update b (get_d u) 
          | effect (Mul (a, b)) k ->
             let u = mk (get_v a * get_v b) in
             continue k u;
             update a (get_d u * get_v b);
             update b (get_d u * get_v a) 
          | y ->
             update y one
  
      end in
      get_d x
  }
end


(* -------------------------------------------------------------------------- *)
(** Stack-Based Implementation of Reverse-Mode AD. *)

(* This version of the algorithm behaves almost exactly as [ReverseMode].
   The main difference is that, instead of implicitly storing the _Wengert
   list_ in the stack, this version of the algorithm uses an explicit stack
   dynamically allocated in the heap.
*)

module StackBased : AD = struct
  let diff (e : exp) : exp = { eval =
    fun (type v) ({ zero; one; add; mul } : v num) (n : v) ->
      let ( + ), ( * ) = add, mul in
      let open Stack in
      let open struct

        type t = O | I | Var of {v : v ; mutable d : v}

        let mk n       = Var {v = n; d = zero}
        let get_v u    = match u with O -> zero | I -> one  | Var u     -> u.v
        let get_d u    = match u with O | I -> assert false | Var u     -> u.d
        let update u i = match u with O | I -> ()    | Var u -> u.d <- u.d + i

        type op = Add | Mul
        type letbinding = Let of t * (t * op * t)
        type context = letbinding Stack.t

        let _K : context = create()

        let add a b =
          let u = mk (get_v a + get_v b) in push (Let (u, (a, Add, b))) _K; u
        let mul a b =
          let u = mk (get_v a * get_v b) in push (Let (u, (a, Mul, b))) _K; u
        let num = {zero = O; one = I; add; mul}

        let x = mk n

        let y = e.eval num x

        let () =
          update y one;
          while not (is_empty _K) do
            begin match pop _K with
            | Let (u, (a, Add, b)) ->
               update a (get_d u);
               update b (get_d u) 
            | Let (u, (a, Mul, b)) ->
               update a (get_d u * get_v b);
               update b (get_d u * get_v a) 
            end
          done

      end in
      get_d x
  }
end


(* -------------------------------------------------------------------------- *)
(** Examples. *)

let int   = { zero = 0;  one = 1;  add = ( + );  mul = ( * )  }
let float = { zero = 0.; one = 1.; add = ( +. ); mul = ( *. ) }

(* [f] represents the expression [x ↦ (x+1)^3]. *)
let f =
  { eval = fun {one; add; mul; _} x ->
      let ( + ), ( * ) = add, mul in
      let cube x = x * x * x in
      cube (one + x)
  }

(* Test that [f] has been defined correctly. *)
let () =
  assert (f.eval int 2 = 27);
  assert (f.eval float 2.0 = 27.0)

(* [Test(A)] tests that [A] defines a differentiation algorithm [diff]
   that behaves correctly for some simple inputs. The tests are performed
   when the module [Test(A)] is open.
*)
module Test(A : AD) = struct
  open A

  (* [df] should [x ↦ 3(x+1)^2]. *)
  let df = diff f

  (* [ddf] should be [x ↦ 6(x+1)]. *)
  let ddf = diff (diff f)

  let () =
    assert  (df.eval int   2  = 27);
    assert  (df.eval float 2. = 27.);
    assert (ddf.eval int   2  = 18);
    assert (ddf.eval float 2. = 18.)
end

(* A list of implementations of the [AD] interface. *)
let diff_algorithms : (module AD) list = [
  (module ForwardMode);
  (module ReverseMode);
  (module StackBased)
]

(* Test every instance in [diff_algorithms]. *)
let () =
  List.iter (fun (module A : AD) ->
    let open Test(A) in ()
  ) diff_algorithms

(* If control reaches this line, then the tests are successful. *)
let () =
  print_endline "Success."

