(* This is [invert] in Multicore OCaml 4.10.0. *)

let invert (type a) (iter : (a -> unit) -> unit) : a Seq.t =
  let open struct effect Yield : a -> unit end in
  let yield x = perform (Yield x) in
  fun () ->
    match iter yield with
    | effect (Yield x) k -> Seq.Cons (x, continue k)
    | ()                 -> Seq.Nil

(* Subtlety: the sequence produced by [invert iter] is persistent;
   it does not hold any resource, and can be used several times.
   However, its subsequences are *not* persistent: every [Cons]
   node holds a continuation that must be used at most once. *)

let rec iter f xs =
  match xs() with
  | Seq.Nil -> ()
  | Seq.Cons (x, xs) ->
      f x;
      iter f xs

let tail xs =
  match xs() with
  | Seq.Nil          -> assert false
  | Seq.Cons (_, xs) -> xs

let print x =
  Printf.printf "%d\n" x

let list_to_sequence xs =
  invert (fun yield -> List.iter yield xs)

let () =
  let xs : int list = [0; 1; 2; 3; 4] in
  let xs : int Seq.t = list_to_sequence xs in
  (* This works: *)
  iter print xs;
  iter print xs

let () =
  let xs : int list = [5;6] in
  let xs : int Seq.t = list_to_sequence xs in
  (* This fails because a continuation is used twice: *)
  let xs = tail xs in
  iter print xs; (* this prints "6" *)
  try
    iter print xs; (* this fails *)
    assert false
  with Invalid_argument _ ->
    ()
