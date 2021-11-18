(* A record of the ring operations over a numeric type 'v. *)
type 'v num = 
  { zero : 'v; one : 'v; add : 'v -> 'v -> 'v; mul : 'v -> 'v -> 'v }

(* An expression of one variable in tagless final style. *)
type exp = 
  { eval : (* forall *) 'v. 'v num -> 'v -> 'v }

(* The automatic differentiation algorithm. *)
val diff : exp -> exp 
