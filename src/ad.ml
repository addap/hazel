(* Reverse-Mode Automatic Differentiation with Effect Handlers. *)

(* This code works in Multicore OCaml 4.12.0. *)

(* The use of effect handlers in this code is based on the code by KC
   Sivaramakrishnan:

   https://github.com/ocaml-multicore/effects-examples/blob/master/algorithmic_differentiation.ml

   The packaging is different, though; we use expressions in tagless final
   style.

   This code can be executed in the OCaml toplevel loop via the following
   commands:

   opam switch create 4.12.0+domains+effects --no-switch # (only once) opam
   exec --switch 4.12.0+domains+effects ocaml # runs the toplevel loop

 *)

(* -------------------------------------------------------------------------- *)
(** Type definitions. *)

type 'v num =
  { zero : 'v; one : 'v; add : 'v -> 'v -> 'v; mul : 'v -> 'v -> 'v }

type exp =
  { eval : (* forall *) 'v. 'v num -> 'v -> 'v }

module type AD = sig
  val diff : exp -> exp
end

(* -------------------------------------------------------------------------- *)
(** Forward-mode AD. *)

module ForwardMode : AD = struct

let diff (e : exp) : exp = { eval =
  fun (type v) ({ zero; one; add; mul } : v num) (n : v) ->
    let ( + ), ( * ) = add, mul in
    let open struct
      type t = { v : v ; d : v }
      let mk v d = { v; d }
      let num =
        let zero = mk zero zero
        and one = mk one zero
        and add a b = mk (a.v + b.v) (a.d + b.d)
        and mul a b = mk (a.v * b.v) (a.d * b.v + a.v * b.d)
        in { zero; one; add; mul }
      let x = mk n one
      let y = e.eval num x
    end in
    y.d
}

end

(* -------------------------------------------------------------------------- *)
(** Stack-based implementation of reverse-mode AD. *)

module StackBasedReverseMode : AD = struct

let diff (e : exp) : exp = { eval =
  fun (type v) ({ zero; one; add; mul } : v num) (n : v) ->
    let ( + ), ( * ) = add, mul in
    let open struct
      (* The graph. *)
      type t = O | I | Var of { v : v ; mutable d : v }
      let mk n       = Var { v = n; d = zero }
      let get_v u    = match u with O -> zero | I -> one  | Var u     -> u.v
      let get_d u    = match u with O | I -> assert false | Var u     -> u.d
      let update u i = match u with O | I -> ()    | Var u -> u.d <- u.d + i
      (* The stack. *)
      type op = Add | Mul
      type binding = Let of t * (t * op * t)
      open Stack
      let stack : binding Stack.t = create()
      (* The dictionary used in the forward phase. *)
      let num =
        let zero = O
        and one = I
        and add a b =
          let u = mk (get_v a + get_v b) in
          push (Let (u, (a, Add, b))) stack; u
        and mul a b =
          let u = mk (get_v a * get_v b) in
          push (Let (u, (a, Mul, b))) stack; u
        in { zero; one; add; mul }
      (* The forward phase. *)
      let x = mk n
      let y = e.eval num x
      (* The backward phase. *)
      let () =
        update y one;
        while not (is_empty stack) do
          match pop stack with
          | Let (u, (a, Add, b)) ->
              update a (get_d u);
              update b (get_d u)
          | Let (u, (a, Mul, b)) ->
              update a (get_d u * get_v b);
              update b (get_d u * get_v a)
        done
    end in
    get_d x
}

end

(* -------------------------------------------------------------------------- *)
(** Reverse-mode AD using effect handlers. *)

module EffectHandlerBasedReverseMode : AD = struct

let diff (e : exp) : exp = { eval =
  fun (type v) ({ zero; one; add; mul } : v num) (n : v) ->
    let ( + ), ( * ) = add, mul in
    let open struct
      (* The graph. *)
      type t = O | I | Var of { v : v ; mutable d : v }
      let mk n       = Var { v = n; d = zero }
      let get_v u    = match u with O -> zero | I -> one  | Var u     -> u.v
      let get_d u    = match u with O | I -> assert false | Var u     -> u.d
      let update u i = match u with O | I -> ()    | Var u -> u.d <- u.d + i
      (* The dictionary. *)
      effect Add : t * t -> t
      effect Mul : t * t -> t
      let num =
        let zero = O
        and one = I
        and add a b = perform (Add (a, b))
        and mul a b = perform (Mul (a, b))
        in { zero; one; add; mul }
      (* The forward and backward phases. *)
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
(** Some dictionaries. *)

let int   = { zero = 0; one = 1; add = ( + ); mul = ( * ) }
let float = { zero = 0.0; one = 1.0; add = ( +. ); mul = ( *. ) }

(* -------------------------------------------------------------------------- *)
(** Some expressions. *)

(* [f] represents the expression [x ↦ (x+1)^3]. *)

let f =
  { eval = fun {one; add; mul; _} x ->
      let ( + ), ( * ) = add, mul in
      let cube x = x * x * x in
      cube (one + x)
  }

(* Test. *)

let () =
  assert (f.eval int 2 = 27);
  assert (f.eval float 2.0 = 27.0);
  ()

(* [var] represents the expression x. *)

let var : exp =
  { eval =
      fun (type v) _dict (x : v) ->
        x
  }

(* [subst e1 e2] substitutes the expression [e1] for the (unique) variable
   in the expression [e2], yielding a new expression. *)

let subst (e1 : exp) (e2 : exp) : exp =
  { eval =
      fun (type v) dict (x : v) ->
        e2.eval dict (e1.eval dict x)
  }

(* Monomial and power. *)

(* The expression x^k. *)
let monomial (k : int) : exp = { eval =
  fun (type v) { one; mul; _ } (x : v) ->
    let ( * ) = mul in
    let result, x, k = ref one, ref x, ref k in
    while !k > 0 do
      result := !result * (if !k mod 2 = 0 then one else !x);
      x := !x * !x;
      k := !k / 2
    done;
    !result }

let pow (k : int) (e : exp) : exp =
  subst e (monomial k)

(* Test. *)
let () =
  assert ((monomial 8).eval float 2.0 = 256.0);
  assert ((pow 2 (pow 4 var)).eval float 2.0 = 256.0);
  ()

(* -------------------------------------------------------------------------- *)
(** Testing an implementation of AD. *)

(* [Test(A)] tests that [A.diff] behaves correctly on some simple inputs. *)
module Test (A : AD) = struct

  open A

  (* [df] should be [x ↦ 3(x+1)^2]. *)
  let df = diff f

  (* [ddf] should be [x ↦ 6(x+1)]. *)
  let ddf = diff (diff f)

  let () =
    assert  (df.eval int   2  = 27);
    assert  (df.eval float 2. = 27.);
    assert (ddf.eval int   2  = 18);
    assert (ddf.eval float 2. = 18.);
    ()

  (* [monomial 4] is [x^4], so its derivative its [4.x^3], whose evaluation
     at 2 should yield 32. *)
  let () =
    assert ((diff (monomial 4)).eval float 2.0 = 32.0);
    ()

end

(* -------------------------------------------------------------------------- *)
(** Testing each of our three implementations. *)

(* A list of our implementations of AD. *)
let algorithms : (module AD) list = [
  (module ForwardMode);
  (module StackBasedReverseMode);
  (module EffectHandlerBasedReverseMode);
]

(* Test every instance in [algorithms]. *)
let () =
  List.iter (fun (module A : AD) ->
    let module T = Test(A) in ()
  ) algorithms

(* If we reach this point, then the tests have succeeded. *)
let () =
  print_endline "Success."
