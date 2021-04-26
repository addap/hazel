(* ref.ml

   The GitHub repository [effect-examples] shows that it is possible to
   implement ML-like reference cells using effect handlers. The purpose of this
   module is to show that it is possible to adapt such implementation to our
   calculus [HH].

*)

(* Effects.

   Like in our calculus [HH], we restrict effects to a single constructor
   named [Eff]. We fix both its argument and answer types to [value]. This
   type is an extensible type that emulates the fact that [HH] is untyped.

*)

type value = ..

effect Eff : value -> value

(* Handlers.

   [HH] offers shallow handlers as the primitive construct for capturing
   effects. Since OCaml handlers follow a deep handler semantics by default,
   we first implement a shallow handler (for the effect [Eff]) and then we
   continue as if this was the only handling mechanism.

*)

type 'a split = Val of 'a | Cont of value * (value -> 'a)

let split (e : unit -> 'a) : 'a split =
  match e () with
  | effect (Eff v) k ->
    let k w =
      match continue k w with
      | Cont (v', k') -> k' (perform (Eff v'))
      | Val result    -> result
    in
    Cont (v, k)
  | result -> Val result

let shallow_handler (e : unit -> 'a)
  ~handler:(h : value -> (value -> 'a) -> 'b)
  ~return:(r : 'a -> 'b)
  =
  match split e with
  | Cont (v, k) -> h v k
  | Val result -> r result

let rec deep_handler (e : unit -> 'a)
  ~handler:(h : value -> (value -> 'b) -> 'b)
  ~return:(r : 'a -> 'b)
  =
  shallow_handler e ~return:r ~handler:(fun v k ->
    h v (fun w -> deep_handler (fun () -> k w) ~handler:h ~return:r))

let selective_handler (f : value -> bool) (e : unit -> 'a)
  ~handler:(h : value -> (value -> 'b) -> 'b)
  ~return:(r : 'a -> 'b)
  =
  deep_handler e
    ~handler:(fun v k -> if f v then h v k else k (perform (Eff v)))
    ~return:r


module type STATE = sig
  type t

  val ref : value -> t
  val (!) : t -> value
  val (:=) : t -> value -> unit

  val run : (unit -> 'a) -> 'a
end

module State : STATE = struct

  type name = ..

  type label = RefL | StateL of name

  let fresh () : name =
    let module M = struct
      type name += A
    end
    in
    M.A

  type t = name

  type value +=
  | Arg of label * value
  | Ref of t
  | Unit
  | Get
  | Set of value

  let ref init =
    match (perform (Eff (Arg (RefL, init)))) with
    | Ref r -> r
    | _     -> assert false

  let (!) r =
    perform (Eff (Arg (StateL r, Get)))

  let (:=) r w =
    match perform (Eff (Arg (StateL r, Set w))) with
    | Unit -> ()
    | _    -> assert false

  let label_selection l =
    function Arg (r, _) when l = r -> true | _ -> false

  let proj =
    function Arg (_, v) -> v | _ -> assert false

  let run client =
    selective_handler (label_selection RefL) client
      ~return:(fun result -> result)
      ~handler:(fun arg k ->
         let init = proj arg in
         let r = fresh () in
         let client = fun () -> k (Ref r) in
         let comp =
           selective_handler (label_selection (StateL r)) client
             ~return:(fun result -> fun _ -> result)
             ~handler:(fun request k ->
                match proj request with
                | Get   -> fun v -> k v v
                | Set w -> fun _ -> k Unit w
                | _     -> assert false)
         in
         comp init)

end

type value += Int of int

let _ =
  let open State in
  run (fun () ->

    let r = ref (Int 0) in
    r := Int 3;

    let l = ref (Int 4) in
    l := Int (-1);

    (!r, !l))
