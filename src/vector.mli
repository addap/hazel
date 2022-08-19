
open Dim

type ('a, _) t =
| Nil  : ('a, zero) t
| Cons : 'a * ('a, 'd) t -> ('a, 'd succ) t

val map : ('a -> 'b) -> ('a, 'd) t -> ('b, 'd) t

val curry_one : ('a -> 'b) -> ('a, one) t -> 'b
val curry_two : ('a -> 'a -> 'b) ->  ('a, two) t -> 'b
val curry_three : ('a -> 'a -> 'a -> 'b) ->  ('a, three) t -> 'b

val bind_one : ('a, one) t -> ('a -> 'b) -> 'b
val bind_two : ('a, two) t -> ('a -> 'a -> 'b) -> 'b
val bind_three : ('a, three) t -> ('a -> 'a -> 'a -> 'b) -> 'b

val ret_one : 'a -> ('a, one) t
val ret_two : 'a -> 'a -> ('a, two) t
val ret_three : 'a -> 'a -> 'a -> ('a, three) t
