(* [('a, 'd) t] is the type of tuples with elements in ['a] and size ['d]. *)
type ('a, _) t =
| Nil  : ('a, Dim.zero) t
| Cons : 'a * ('a, 'd) t -> ('a, 'd Dim.succ) t

(* [map f xs] maps the function [f] over the elements of [xs]. *)
val map : ('a -> 'b) -> ('a, 'd) t -> ('b, 'd) t

(* [curry_* f] transforms a function [f] with multiple arguments into
   a function with a single tuple as its argument. *)
val curry_one : ('a -> 'b) -> ('a, Dim.one) t -> 'b
val curry_two : ('a -> 'a -> 'b) ->  ('a, Dim.two) t -> 'b
val curry_three : ('a -> 'a -> 'a -> 'b) ->  ('a, Dim.three) t -> 'b

(* [bind_* vec f] performs the application of [f] to the elements of [vec]. *)
val bind_one : ('a, Dim.one) t -> ('a -> 'b) -> 'b
val bind_two : ('a, Dim.two) t -> ('a -> 'a -> 'b) -> 'b
val bind_three : ('a, Dim.three) t -> ('a -> 'a -> 'a -> 'b) -> 'b

(* [ret_* x0 ... xn] constructs a tuple with elements [x0] to [xn]. *)
val ret_one : 'a -> ('a, Dim.one) t
val ret_two : 'a -> 'a -> ('a, Dim.two) t
val ret_three : 'a -> 'a -> 'a -> ('a, Dim.three) t
