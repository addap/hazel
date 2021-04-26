(* Automatic Differentiation in Multicore OCaml 4.10.0 *)

(* The code presented here is not original. It was taken from the link bellow:

       https://github.com/ocaml-multicore/effects-examples/blob/master/algorithmic_differentiation.ml

*)

module type Num = sig
  type t
  val one   : t
  val zero  : t
  val ( + ) : t -> t -> t
  val ( * ) : t -> t -> t
end

module type AD = sig
  type a
  type t
  val one   : t
  val zero  : t
  val ( + ) : t -> t -> t
  val ( * ) : t -> t -> t
  val diff  : (t     -> t) -> (a     -> a)
  val grad  : (t * t -> t) -> (a * a -> a * a)
end

module AD (A : Num) : (AD with type a := A.t) = struct

  type t = { v : A.t; mutable d : A.t }

  let mk (a : A.t) : t = { v = a; d = A.zero }

  let one  = mk A.one
  let zero = mk A.zero

  effect Add  : t * t -> t
  effect Mult : t * t -> t

  let ( + ) : t -> t -> t = fun a b -> perform (Add  (a, b))
  let ( * ) : t -> t -> t = fun a b -> perform (Mult (a, b))

  let run : (unit -> t) -> unit =
    fun client ->
      match client () with
      | effect (Add (a, b)) k ->
          let x = mk A.(a.v + b.v) in
          continue k x;
          a.d <- A.(a.d + x.d);
          b.d <- A.(b.d + x.d)
      | effect (Mult (a, b)) k ->
          let x = mk A.(a.v * b.v) in
          continue k x;
          a.d <- A.(a.d + (x.d * b.v));
          b.d <- A.(b.d + (x.d * a.v))
      | r ->
          r.d <- A.one

  let diff : (t -> t) -> (A.t -> A.t) =
    fun f a ->
      let x = mk a in
      run (fun () -> f x);
      x.d

  let grad : (t * t -> t) -> (A.t * A.t -> A.t * A.t) =
    fun f (a, b) ->
      let x, y = mk a, mk b in
      run (fun () -> f (x, y));
      x.d, y.d
end

let _ =
  let module IntNum : (Num with type t = int) = struct
      type t = int
      let one = 1
      let zero = 0
      let ( + ) = ( + )
      let ( * ) = ( * )
    end
  in
  let module D1 = AD (IntNum) in
  let module D2 = AD (D1)     in

  let x_cube'' = D1.diff (D2.diff D2.(fun x -> x * x * x)) in
  assert (x_cube'' 0 = 0);
  assert (x_cube'' 1 = 6);
  assert (x_cube'' 2 = 12);
  assert (x_cube'' 3 = 18);

  let dx, _ = D1.(grad (fun (x, z) ->
    let _, dy = D2.(grad (fun (x, y) -> x + y) (x, z)) in
    x * dy) (1, 1))
  in
  assert (dx = 1)

