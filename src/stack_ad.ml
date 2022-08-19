(* stack_ad.ml *)

(* This module provides an implementation of reverse-mode automatic
   differentiation that does not use control operators. (In particular,
   it does not use effect handlers.)
*)


(* -------------------------------------------------------------------------- *)
(** Type Definitions. *)

type 'n num = {
  zero : 'n;
  one  : 'n;
  add  : 'n -> 'n -> 'n;
  mul  : 'n -> 'n -> 'n
}

type exp = {
  eval : 'n. 'n num -> 'n -> 'n
}


(* -------------------------------------------------------------------------- *)
(** The Differentiation Algorithm. *)

(* This version of the algorithm behaves almost exactly as the one implemented
   in the file [ad.ml]. The main difference is that, instead of implicitly
   storing the _Wengert list_ in the stack, this version of the algorithm uses
   an explicit stack dynamically allocated in the heap.
*)

open Stack

let diff (e : exp) : exp = { eval =
  fun (type v) ({ zero; one; add; mul } : v num) (n : v) ->
    let ( + ), ( * ) = add, mul in
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


(* -------------------------------------------------------------------------- *)
(** Examples. *)

let int   = { zero = 0;  one = 1;  add = ( + );  mul = ( * )  }
let float = { zero = 0.; one = 1.; add = ( +. ); mul = ( *. ) }

(* [f] represents the expression [x ↦ (x+1)^3]. *)
let f = { eval = fun (type v) ({ zero; one; add; mul } : v num) x ->
  let ( + ), ( * ) = add, mul in
  let cube x = x * x * x in
  cube (one + x)
}

(* [df] should be [x ↦ 3(x+1)^2]. *)
let df = diff f

(* [ddf] should be [x ↦ 6(x+1)]. *)
let ddf = diff (diff f)

(* Tests. *)
let () =
  assert (f.eval int 2 = 27);
  assert (f.eval float 2.0 = 27.0);

  assert (df.eval int 2 = 27);
  assert (df.eval float 2.0 = 27.0);

  assert (ddf.eval int 2 = 18);
  assert (ddf.eval float 2.0 = 18.0)

let () =
  print_endline "Success."
