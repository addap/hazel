(* Reverse-Mode Automatic Differentiation with Effect Handlers. *)

(* This code works in Multicore OCaml 4.12.0. *)

(* The use of effect handlers in this code is based on the code by KC Sivaramakrishnan:

   https://github.com/ocaml-multicore/effects-examples/blob/master/algorithmic_differentiation.ml

   The packaging is different, though; we use expressions in tagless final style.

   This code can be executed in the OCaml toplevel loop via the following commands:

   opam switch create 4.12.0+domains+effects --no-switch # (only once)
   opam exec --switch 4.12.0+domains+effects ocaml       # runs the toplevel loop

 *)
(* BEGINPAPER *)
type 'v num =
  { zero : 'v; one : 'v; add : 'v -> 'v -> 'v; mul : 'v -> 'v -> 'v }

type exp =
  { eval : (* forall *) 'v. 'v num -> 'v -> 'v }

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
(* ENDPAPER *)

let int   = { zero = 0; one = 1; add = ( + ); mul = ( * ) }
let float = { zero = 0.0; one = 1.0; add = ( +. ); mul = ( *. ) }

(* f represents the expression (x+1)^3. *)
let f =
  {eval = fun (type v) ({ zero; one; add; mul } : v num) x ->
    let ( + ), ( * ) = add, mul in
    let cube x = x * x * x in
    cube (one + x)
  }

(* Test. *)
let () =
  assert (f.eval int 2 = 27);
  assert (f.eval float 2.0 = 27.0)

(* f' should 3(x+1)^2 *)
let f' = diff f

(* Test. *)
let () =
  assert (f'.eval int 2 = 27);
  assert (f'.eval float 2.0 = 27.0)

(* f'' should be 6(x+1) *)
let f'' = diff (diff f)

(* Test. *)
let () =
  assert (f''.eval int 2 = 18);
  assert (f''.eval float 2.0 = 18.0)

let () =
  print_endline "Success."
