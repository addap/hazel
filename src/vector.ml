
open Dim

type ('a, _) t =
  | Nil : ('a, zero) t
  | Cons : 'a * ('a, 'd) t -> ('a, 'd succ) t

let rec map : type a b d. (a -> b) -> (a, d) t -> (b, d) t =
  fun f xs ->
    match xs with
    | Nil -> Nil
    | Cons (x, xs) -> Cons (f x, map f xs)

let curry_one (f : 'a -> 'b) : ('a, one) t -> 'b =
  function (Cons (x, _)) -> f x
let curry_two (f : 'a -> 'a -> 'b) : ('a, two) t -> 'b =
  function (Cons (x, (Cons (y, _)))) -> f x y
let curry_three (f : 'a -> 'a -> 'a -> 'b) : ('a, three) t -> 'b =
  function (Cons (x, (Cons (y, (Cons (z, _)))))) -> f x y z

let bind_one vec f = curry_one f vec
let bind_two vec f = curry_two f vec
let bind_three vec f = curry_three f vec

let ret_one x =
  Cons (x, Nil)
let ret_two x y =
  Cons (x, (Cons (y, Nil)))
let ret_three x y z =
  Cons (x, (Cons (y, (Cons (z, Nil)))))
