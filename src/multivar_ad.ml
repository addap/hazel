(* multivar_ad.ml *)

(* This module implements reverse-mode automatic differentiation of
   multivariate functions.

   It offers the type [('d, 'l) exp], on which users can define functions
   from tuples of size ['d] to tuples of size ['l]. (The size denoted by the
   type [Dim.zero] is zero, and the size denoted by ['d Dim.succ] is one plus
   the size denoted by ['d]. The size denoted by a type that is not construct
   by [Dim.zero] or [Dim.succ] is not defined.) More specifically, an
   inhabitant of the type [('d, 'l) exp] is a ['l]-sized tuple of polynomials
   in ['d] variables. This property follows from parametricity of value
   polymorphism. It is a technique known as tagless final style.

   To perform differentiation, the library introduces a function [diff] with
   the following type:

     [diff : ('d, Dim.one) exp -> ('d, 'd) exp]

   [diff] takes a polynomial in ['d] variables and produces its gradient,
   a tuple of ['d] polynomials in ['d] variables.
 *)

(* -------------------------------------------------------------------------- *)
(** Type Definitions. *)

(* Type ['n num]. *)

(* The type of a ring with elements in ['n]. *)
type 'n num = {
  zero : 'n;
  one  : 'n;
  add  : 'n -> 'n -> 'n;
  mul  : 'n -> 'n -> 'n
}

(* Type [('d, 'l) exp]. *)

(* An element of type [('d, 'l) exp] is a function [eval] from ['d]-sized
   [('n, 'd) Vector.t] tuples to ['n]-sized [('n, 'l) Vector.t] tuples.
   [eval] is polymorphic on the type type of elements ['n]. This type is
   equipped with the operations of a ring given by a ['n num] dictionary to
   which [eval] has access. Because, [eval] is polymorphic in ['n], it can
   only construct elements in ['n] by combining its input variables through
   the arithmetical operations given by the ['n num] dictionary.
*)
type ('d, 'l) exp = {
  eval : 'n. 'n num -> ('n, 'd) Vector.t -> ('n, 'l) Vector.t
}


(* -------------------------------------------------------------------------- *)
(** The Differentiation Algorithm. *)

(* The key idea of the algorithm is to spy a particular evaluation of
   [e : (d, Dim.one) expr] to infer the arithmetical expression [E]
   built by [e]. The algorithm implicitly stores [E] in the form of a
   _Wengert list_ (a series of let-bindings where a bound expression
   is either an addition or a product of variables), which it enrolls
   to perform the classic backpropagation algorithm to compute derivatives.
*)

let diff (type d) (e : (d, Dim.one) exp) : (d, d) exp = {eval =
  fun (type n) ({ zero; one; add; mul } : n num) (ns : (n, d) Vector.t) ->
    let ( + ), ( * ) = add, mul in
    let open struct

    (* Ring of Dual Numbers. *)
      (* Define the type of dual numbers. *)
      type t = O | I | Var of {v : n ; mutable d : n}
      (* Generate fresh effects. *)
      effect Add : t * t -> t
      effect Mul : t * t -> t
      (* Define the ring operations. *)
      let num =
        let add a b = perform (Add (a, b)) in
        let mul a b = perform (Mul (a, b)) in
      {
        zero = O;
        one  = I;
        add  = add;
        mul  = mul
      }

    (* Internal Functions. *)
      (* Create a dual number. *)
      let mk v = Var {v = v; d = zero}
      (* Get the [v]-field of a dual number. *)
      let get_v = function O -> zero| I -> one | Var u -> u.v
      (* Get the [d]-field of a dual number. *)
      let get_d = function O | I -> assert false | Var u -> u.d
      (* Update the [d]-field of a dual number. *)
      let update u i = match u with O | I -> () | Var u -> u.d <- u.d + i

    (* Create initial tuple of dual numbers. *)
      let xs = Vector.map mk ns

    (* Evaluation of [e.eval]. *)
      let () =
        match e.eval num xs with
        | effect (Add (a, b)) k ->
           (* Answer the [Add] query at _call time_. *)
           let u = mk (get_v a + get_v b) in
           continue k u;
           (* Compute derivatives at _return time_. *)
           update a (get_d u);
           update b (get_d u)
        | effect (Mul (a, b)) k ->
           let u = mk (get_v a * get_v b) in
           continue k u;
           update a (get_d u * get_v b);
           update b (get_d u * get_v a)
        | Cons (r, Nil) ->
           (* Plant seed at [d]-field of the produced dual number. *)
           update r one

    end in

    (* Read the derivatives stored in [xs]. *)
    Vector.map get_d xs
}


(* --------------------------------------------------------------------------- *)
(** Useful Functions on Expressions. *)

open Vector

(* [compose g f] constructs the functional composition of [f] and [g]. *)
let compose : type d l k. (l, k) exp -> (d, l) exp -> (d, k) exp =
  fun (type d l k) (g : (l, k) exp) (f : (d, l) exp) ->
    { eval = fun num vec ->
        g.eval num (f.eval num vec)
    }
  
(* [fst] projects the first component of a pair [(x,y) ↦ x]. *)
let fst : (Dim.two, Dim.one) exp =
  { eval = fun _num ->
      curry_two (fun x _y -> ret_one x)
  }

(* [snd] projects the second component of a pair [(x,y) ↦ y]. *)
let snd : (Dim.two, Dim.one) exp =
  { eval = fun _num ->
      curry_two (fun _x y -> ret_one y)
  }

(* [pow n] represents the expression [x ↦ x^n]. *)
let pow n : (Dim.one, Dim.one) exp =
  { eval = fun { one; mul; _ } ->
      curry_one (fun x ->
        (* We implement fast exponentiation using references only to
           increase the complexity (of the behavior) of this function. *)
        let res, e, b = ref one, ref x, ref n in
        while !b > 0 do
          let resv, ev, bv = !res, !e, !b in
          res := mul resv (if bv mod 2 = 0 then one else ev);
          e := mul ev ev;
          b := bv / 2
        done;
        ret_one !res)
  }

(* [bin_prod f g] creates the binary product of [f] and [g],
   that is, the function [vec ↦ (f vec, g vec)]. *)
let bin_prod : type d. (d, Dim.one) exp -> (d, Dim.one) exp -> (d, Dim.two) exp =
  fun (type d) (f : (d, Dim.one) exp) (g : (d, Dim.one) exp) ->
    { eval = fun num vec ->
        bind_one (f.eval num vec) (fun res_f ->
        bind_one (g.eval num vec) (fun res_g ->
        ret_two res_f res_g))
    }

(* [id] represents the expression [vec ↦ vec]. *)
let id : type d. (d, d) exp =
  { eval = fun _num vec -> vec }

(* [one] represents the expression [_ ↦ 1]. *)
let one : type d. (d, Dim.one) exp =
  { eval = fun {one; _} _vec -> ret_one one }

(* [zero] represents the expression [_ ↦ 0]. *)
let zero : type d. (d, Dim.one) exp =
  { eval = fun {zero; _} _vec -> ret_one zero }

(* [add] represents the expression [(x,y) ↦ x+y]. *)
let add : (Dim.two, Dim.one) exp =
  { eval = fun {add; _} ->
      curry_two (fun x y -> ret_one (add x y))
  }

(* [mul] represents the expression [(x,y) ↦ x*y]. *)
let mul : (Dim.two, Dim.one) exp =
  { eval = fun {mul; _} ->
      curry_two (fun x y -> ret_one (mul x y))
  }

(* [const n] represents the expression [_ ↦ n]. *)
let const n : (Dim.one, Dim.one) exp =
  compose (diff (pow n)) one

(* --------------------------------------------------------------------------- *)
(** Examples. *)

(* Instances of the [n' num] type. *)

(* The ring of integers. *)
let int : int num = {
  zero = 0;
  one  = 1;
  add  = ( + );
  mul  = ( * )
}

(* The ring of floats. *)
let float : float num = {
  zero = 0.0;
  one  = 1.0;
  add  = ( +. );
  mul  = ( *. )
}


(* Differentiating the function [pow]. *)

(* [dpow n] and [dpow' n] should both represent
   the expression [x ↦ n*x^(n-1)]. *)
let dpow n : (Dim.one, Dim.one) exp =
  diff (pow n)
let dpow'  n : (Dim.one, Dim.one) exp =
  compose mul (bin_prod (const n) (pow (n - 1)))

(* Tests. *)
let () =
  (* Check the result of [pow] at simple values. *)
  assert ((pow 11).eval int    (ret_one 2)  = ret_one 2048);
  assert ((pow 11).eval float  (ret_one 2.) = ret_one 2048.);

  (* Check the result of [dpow] at simple values. *)
  assert ((dpow 11).eval int    (ret_one 2)  = ret_one 11264);
  assert ((dpow 11).eval float  (ret_one 2.) = ret_one 11264.);

  (* Check that [dpow] and [dpow'] behave similarly. *)
  let n = 5 in
  for x=0 to 10 do
    assert ((dpow  n).eval int (ret_one x) =
            (dpow' n).eval int (ret_one x))
  done


(* Differentiating the polynomial [(x+1)^3] . *)

(* [f] represents the expression [x ↦ (x+1)^3]. *)
let f : (Dim.one, Dim.one) exp =
  compose (pow 3) (compose add (bin_prod id one))

(* [df] should be [x ↦ 3(x+1)^2]. *)
let df = diff f

(* [ddf] should be [x ↦ 6(x+1)]. *)
let ddf = diff (diff f)

(* Tests. *)
let () =
  assert (f.eval int   (ret_one 2)  = ret_one 27);
  assert (f.eval float (ret_one 2.) = ret_one 27.);

  assert (df.eval int   (ret_one 2)  = ret_one 27);
  assert (df.eval float (ret_one 2.) = ret_one 27.);

  assert (ddf.eval int   (ret_one 2)  = ret_one 18);
  assert (ddf.eval float (ret_one 2.) = ret_one 18.)


(* Differentiating the polynomial [(x+y^2)^3] . *)

(* [f] represents the expression [(x,y) ↦ (x+y^2)^3]. *)
let f : (Dim.two, Dim.one) exp =
  compose (pow 3)
    { eval = fun {add; mul; _} ->
        curry_two (fun x y ->
          let ( + ), ( * ) = add, mul in
          ret_one (x + (y * y))
      )
    }

(* [df] should be [(x,y) ↦ (3(x+y^2)^2, 6y(x+y^2)^2)]. *)
let df = diff f

(* [df_x] represents [(x,y) ↦ 3(x+y^2)^2]. *)
let df_x = compose fst df

(* [ddf_x] should be [(x, y) ↦ (6(x+y^2), 12y(x+y^2))]. *)
let ddf_x = diff df_x

(* Test. *)
let () =
  assert (f.eval int   (ret_two 2   1  ) = ret_one 27  );
  assert (f.eval float (ret_two 2.0 1.0) = ret_one 27.0);

  assert (df.eval int   (ret_two 2  1 ) = ret_two 27   54   );
  assert (df.eval float (ret_two 2. 3.) = ret_two 363. 2178.);

  assert (ddf_x.eval int (ret_two 2 1) = ret_two 18 36)

