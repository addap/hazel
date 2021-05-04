(* Reverse-Mode Automatic Differentiation with Effect Handlers. *)

(* This code works in Multicore OCaml 4.10.0. *)

(* This code is based on the code by KC Sivaramakrishnan:

   https://github.com/ocaml-multicore/effects-examples/blob/master/algorithmic_differentiation.ml

 *)

module type NUM = sig 
  type t
  val one   : t
  val zero  : t
  val ( + ) : t -> t -> t
  val ( * ) : t -> t -> t
end

module type AD = sig 
  include NUM 
  type n
  val diff  : (t -> t) -> (n -> n)
  val grad  : (t * t -> t) -> (n * n -> n * n)
end

module RMAD (N : NUM) = struct
  open N
  type n = t
  type t = { v : n; mutable d : n }
  effect Add  : t * t -> t
  effect Mult : t * t -> t

  let mk v =
    { v = v; d = zero }

  let handle f seed =
    match f seed with
    | effect (Add (a, b)) k ->
        let x = mk (a.v + b.v) in
        continue k x;
        a.d <- a.d + x.d;
        b.d <- b.d + x.d
    | effect (Mult (a, b)) k ->
        let x = mk (a.v * b.v) in
        continue k x;
        a.d <- a.d + (x.d * b.v);
        b.d <- b.d + (x.d * a.v)
    | r ->
        r.d <- one

  let diff f a =
    let x = mk a in handle f x; x.d

  let grad f (a, b) =
    let (x, y) = (mk a, mk b) in handle f (x, y); (x.d, y.d)

  let zero = mk zero
  let one = mk one
  let ( + ) a b = perform (Add  (a, b))
  let ( * ) a b = perform (Mult (a, b))
end
