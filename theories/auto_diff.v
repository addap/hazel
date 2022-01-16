From iris.algebra   Require Import gmap_view.            (* Definition of [gmap_view] RA. *)
From iris.proofmode Require Import base tactics classes. (* Iris's tactics.               *)

From hazel          Require Import weakestpre deep_handler.
From hazel          Require Import notation tactics.

Set Default Proof Using "Type".

(* auto_diff.v *)


(** * Implementation. *)

(** In this section, we introduce an implementation of reverse mode automatic
    differentiation written in our calculus [HH]. This is the code that we are
    going to study throughout this theory. The idea is to use effects as a way
    to infer the sequence of arithmetic operations performed by the client
    during its evaluation. This list is known in the literature as the Wengert
    list.

    Notice that this idea is not new. Many implementations of reverse mode AD
    using effect handlers or delimited continuations already exist.
*)

Section implementation.

(** The typeclass [Num] provides a concrete implementation of a semiring [R]
    (to be defined later). This means that elements of [R] are accessible in
    [HH] trough the interface [Num].
*)

Class Num := {
  nzero  : val;
  none   : val; (* <- Not to be confused with [None]! *)
  nadd   : val;
  nmul   : val;
}.

Section RMAD.

  Definition create {N : Num} : val := λ: "n", InjR ("n", ref nzero).

  Definition zero  : val := InjLV (InjLV #()).
  Definition one   : val := InjLV (InjRV #()).
  Definition add   : val := λ: "a" "b", do: (InjLV #(), ("a", "b")).
  Definition mul   : val := λ: "a" "b", do: (InjRV #(), ("a", "b")).

  Definition get_val {N : Num} : val := λ: "x",
    match: "x" with
      (* Constant. *) InjL "x" =>
       match: "x" with
         (* Zero. *) InjL <> => nzero
       | (* One.  *) InjR <> => none
       end
    | (* Variable. *) InjR "x" => Fst "x"
    end.

  Definition get_diff : val := λ: "x",
    match: "x" with
      (* Constant. *) InjL <>  => #() #() (* Unreachable. *)
    | (* Variable. *) InjR "x" => Load (Snd "x")
    end.

  Definition update {N : Num} : val := λ: "x" "incr",
    match: "x" with
      (* Constant. *) InjL <>  => #()
    | (* Variable. *) InjR "x" =>
      let: "xd" := Snd "x" in
      "xd" <- nadd (Load "xd") "incr"
    end.

  Definition handle {N : Num} : val := λ: "f" "seed",
    try: "f" "seed" with
      effect (λ: "args" "k",
        let: "op" := Fst      "args"  in
        let: "a"  := Fst (Snd "args") in
        let: "b"  := Snd (Snd "args") in

        let: "av" := get_val "a"      in
        let: "bv" := get_val "b"      in

        match: "op" with
          (* Add *) InjL <> =>
           let: "x" := create (nadd "av" "bv") in
           "k" "x";;
           let: "xd" := get_diff "x" in
           update "a" "xd";;
           update "b" "xd"

        | (* Mul *) InjR <> =>
           let: "x" := create (nmul "av" "bv") in
           "k" "x";;
           let: "xd" := get_diff "x"   in
           let: "ad" := nmul "bv" "xd" in
           let: "bd" := nmul "av" "xd" in
           update "a" "ad";;
           update "b" "bd"
        end
      )
    | return (λ: "res",
           update "res" none)
    end.

  Program Instance ADNum : Num := {
    nzero := zero;
    none  := one;
    nadd  := add;
    nmul  := mul;
  }.

  Definition diff (f : Num → expr) (N : Num) : expr :=
    let: "vf" := f ADNum in
    λ: "a",
      let: "x" := @create N "a" in
      @handle N "vf" "x";;
      get_diff "x".

End RMAD.

End implementation.


(** * Mathematics. *)

(** We define the mathematical notions for this case study. These definitions
    form the basis of a precise language for explaining AD. They appear in the
    specification of the algorithm and in the arguments conveying its correctness.
*)

(** The typeclass [RingSig] bundles the operations of a ring and [IsRing]
    bundles the axioms of a semiring. It will be useful in specifying the
    interface of numerical values.
*)

Class RingSig (R : Set) := {
  rzero : R;
  rone  : R;
  radd  : R → R → R;
  rmul  : R → R → R;
  req   : R → R → Prop;
}.

Class IsRing (R : Set) {RS : RingSig R} := {
  req_equiv :> Equivalence req;
  radd_ext  :> Proper (req ==> req ==> req) radd;
  rmul_ext  :> Proper (req ==> req ==> req) rmul;

  is_semi_ring : semi_ring_theory rzero rone radd rmul req
}.

Section definitions.

Inductive Binop : Set := Add | Mul.

Inductive Expr (I : Set) : Set :=
  Zero | One | Leaf (i : I) | Node (op : Binop) (el er : Expr I).

Definition vars {I : Set} `{CI : Countable I} : Expr I → gset I :=
  fix vars (e : Expr I) : gset I :=
    match e with
    | Zero _
    | One  _         => ∅
    | Leaf _ i       => {[i]}
    | Node _ _ el er => vars el ∪ vars er
    end.

Definition bind {I J : Set} (f : I → Expr J) : Expr I → Expr J :=
  fix bind (e : Expr I) : Expr J :=
    match e with
    | Zero _          => Zero _
    | One  _          => One  _
    | Leaf _ i        => f i
    | Node _ op el er => Node _ op (bind el) (bind er)
    end.

Definition map {I J : Set} (ϱ : I → J) : Expr I → Expr J :=
  bind (λ i, Leaf _ (ϱ i)).

Definition denote {R : Set} {RS : RingSig R} : Binop → R → R → R :=
  λ op, match op with Add => radd | Mul => rmul end.

Definition eval {R : Set} {RS : RingSig R} : Expr R → R :=
  fix eval (e : Expr R) : R :=
    match e with
    | Zero _          => rzero
    | One  _          => rone
    | Leaf _ r        => r
    | Node _ op el er => denote op (eval el) (eval er)
    end.

Inductive Expr_equiv {I : Set} : Expr I → Expr I → Prop :=
 (* Equivalence. *)
 | Expr_equiv_refl  e        :
     Expr_equiv e e
 | Expr_equiv_symm  e₁ e₂    :
     Expr_equiv e₁ e₂ → Expr_equiv e₂ e₁
 | Expr_equiv_trans e₁ e₂ e₃ :
     Expr_equiv e₁ e₂ → Expr_equiv e₂ e₃ → Expr_equiv e₁ e₃

 (* [Node _ Add] and [Node _ Mul] are instances of [Proper]. *)
 | Expr_equiv_ext op :
     Proper (Expr_equiv ==> Expr_equiv ==> Expr_equiv) (Node _ op)

 (* Semiring axioms. *)
 | (* SRadd_0_l. *)
   Expr_equiv_add_0_l e :
     Expr_equiv (Node _ Add (Zero _) e) e
 | (* SR(add|mul)_comm. *)
   Expr_equiv_comm op e₁ e₂ :
     Expr_equiv (Node _ op e₁ e₂) (Node _ op e₂ e₁)
 | (* SR(add|mul)_assoc. *)
   Expr_equiv_assoc op e₁ e₂ e₃ :
     Expr_equiv (Node _ op e₁ (Node _ op e₂ e₃))
                (Node _ op (Node _ op e₁ e₂) e₃)
 | (* SRmul_1_l. *)
   Expr_equiv_mul_1_l e :
     Expr_equiv (Node _ Mul (One  _) e) e
 | (* SRmul_0_l. *)
   Expr_equiv_mul_0_l e :
     Expr_equiv (Node _ Mul (Zero _) e) (Zero _)
 | (* SRdistr_l. *)
   Expr_equiv_distr_l e₁ e₂ e₃ :
     Expr_equiv (Node _ Mul (Node _ Add e₁ e₂) e₃)
                (Node _ Add (Node _ Mul e₁ e₃) (Node _ Mul e₂ e₃)).

Global Instance ExprRing (I : Set) : RingSig (Expr I) := {
  rzero := Zero I;
  rone  := One  I;
  radd  := Node I Add;
  rmul  := Node I Mul;
  req   := Expr_equiv;
}.

Definition diffₑ
  {R : Set} {RS : RingSig R}
  {I : Set} {EI : EqDecision I}
  (ϱ : I → R) : Expr I → I → R :=
  fix diff (e : Expr I) (i : I) : R :=
    match e with
    | Zero _           => rzero
    | One  _           => rzero
    | Leaf _ j         => if decide (i = j) then rone else rzero
    | Node _ Add el er => radd (diff el i) (diff er i)
    | Node _ Mul el er => radd (rmul (diff el i) (eval (map ϱ er)))
                               (rmul (eval (map ϱ el)) (diff er i))
    end.

Definition node : Set := (Binop * val * val)%type.

Definition context : Set := list (val * node)%type.

Definition defs (K : context) : list val := K.*1.

Definition overwrite {A B : Set} {EA : EqDecision A} (f : A → B) (a : A) (b : B) : A → B :=
  λ x, if decide (a = x) then b else f x.

Definition filling : context → val → Expr val :=
  foldl
    (* Inductive case: *) (λ filling '(x, (op, a, b)),
      overwrite filling x (Node _ op (filling a) (filling b)))
    (* Base case: *) (λ y, Leaf _ y).

Definition extension {R : Set} {RS : RingSig R} (ϱ : val → R) (K : context) : val → R :=
  foldl (λ ϱ '(x, (op, a, b)), overwrite ϱ x (denote op (ϱ a) (ϱ b))) ϱ K.

End definitions.

(** Mathematical notation. *)

(* TODO: Better ways to define notation? *)
Notation "'Oᵣ'" := rzero (at level 50).
Notation "'Iᵣ'" := rone  (at level 50).
Infix "+ᵣ" := radd (at level 70).
Infix "×ᵣ" := rmul (at level 50).
Infix "=ᵣ" := req  (at level 70).

Notation "'Oₑ'" := (Zero _) (at level 50).
Notation "'Iₑ'" := (One  _) (at level 50).
Notation "'Xₑ'" := (Leaf () tt) (at level 50).
Infix "+ₑ" := (Node _ Add) (at level 70).
Infix "×ₑ" := (Node _ Mul) (at level 50).
Infix "=ₑ" := (Expr_equiv) (at level 70).

Notation "'Let' K '.in' y" := (filling K y) (at level 70).
Notation "f '.{[' a ':=' b ']}'" := (overwrite f a b) (at level 70).
Notation "ϱ '.{[' K ']}'" := (extension ϱ K) (at level 70).
Notation "'∂' e './' '∂' i '.at' ϱ" := (diffₑ ϱ e i) (at level 70).

Section properties.

Global Instance Binop_eq_dec : EqDecision Binop.
Proof. solve_decision. Qed.

Global Instance Expr_eq_dec {I : Set} {EI : EqDecision I} : EqDecision (Expr I).
Proof. solve_decision. Qed.

Global Instance context_eq_dec : EqDecision context.
Proof. solve_decision. Qed.

(** [vars]. *)

Section vars.
  Context {I : Set} `{CI : Countable I}.

  Lemma vars_zero : vars (Oₑ) = (∅ : gset loc).
  Proof. done. Qed.

  Lemma vars_one : vars (Iₑ) = (∅ : gset loc).
  Proof. done. Qed.

  Lemma vars_leaf (i : I) : vars (Leaf _ i) = {[i]}.
  Proof. done. Qed.

  Lemma vars_node (op : Binop) (el er : Expr I) :
    vars (Node _ op el er) = vars el ∪ vars er.
  Proof. done. Qed.

  Lemma vars_suppressing (e : Expr I) (f : I → Expr I) (i : I) :
    vars (f i) = ∅ →
      (∀ j, vars (f j) ⊆ {[j]}) →
        vars (bind f e) ⊆ (vars e) ∖ {[i]}.
  Proof. induction e; [done|done| |]; set_solver. Qed.

  Instance eq_vars_proper (e : Expr I) :
    Proper (equiv ==> flip impl) (eq (vars e)).
  Proof. intros ??? [=->]. by apply gset_leibniz. Qed.

End vars.

(** [bind]. *)

Section bind.

  Lemma bind_leaf {I : Set} (e : Expr I) :
    bind (Leaf _) e = e.
  Proof. by induction e as [| | |?? IHl ? IHr]; last rewrite //= IHl IHr. Qed.

  Lemma bind_compose {I J K : Set} (e : Expr I) (g : I → Expr J) (f : J → Expr K) :
    bind f (bind g e) = bind (bind f ∘ g) e.
  Proof. by induction e as [| | |?? IHl ? IHr]; last rewrite //= IHl IHr. Qed.

  (* From iris.algebra Require Import gset.

  Definition vars_bind
    {I : Set} `{CI : Countable I}
    {J : Set} `{CJ : Countable J} (e : Expr I) (f : I → Expr J) : Prop :=
    vars (bind f e) = [^(∪) set] i ∈ vars e, vars (f i). *)

End bind.

(** [map]. *)

Section map.

  Lemma map_compose {I J K : Set} (ϱ : I → J) (ϑ : J → K) (e : Expr I) :
    map (ϑ ∘ ϱ) e = map ϑ (map ϱ e).
  Proof. by induction e as [| | |?? IHl ? IHr]; last rewrite //= IHl IHr. Qed.

  Lemma map_strong_ext
    {I J : Set} `{CI : Countable I} (ϱ ϑ : I → J) (e : Expr I) :
    (∀ i, i ∈ vars e → ϱ i = ϑ i) →
      map ϱ e = map ϑ e.
  Proof.
    induction e as [| | |op el IHel er IHer]; [done|done| |].
    { intros Hvars. simpl. f_equal. apply Hvars. set_solver. }
    { intros Hvars. rewrite //= IHel; [rewrite IHer; [done|]|]; set_solver. }
  Qed.

  Lemma map_ext {I J : Set} (ϱ ϑ : I → J) (e : Expr I) :
    (∀ i, ϱ i = ϑ i) → map ϱ e = map ϑ e.
  Proof.
    by intros Hext; induction e as [| | |?? IHl ? IHr];
    [| |rewrite //= Hext|rewrite //= IHl IHr].
  Qed.

End map.

(** [defs]. *)

Section defs.

  Lemma defs_cons x n K : defs ((x, n) :: K) = x :: defs K.
  Proof. done. Qed.

  Lemma defs_singleton x n : defs [(x, n)] = [x].
  Proof. done. Qed.

  Lemma defs_app K₁ K₂ : defs (K₁ ++ K₂) = defs K₁ ++ defs K₂.
  Proof. by rewrite /defs fmap_app. Qed.

  Lemma defs_cons_middle K₁ K₂ x n :
    defs (K₁ ++ (x, n) :: K₂) = defs K₁ ++ x :: defs K₂.
  Proof. by rewrite defs_app. Qed.

End defs.

(** [overwrite]. *)

Section overwrite.
  Context {A B : Set} {EA : EqDecision A}.

  Lemma overwrite_eq (f : A → B) (a : A) (b : B) : f.{[a := b]} a = b.
  Proof. by rewrite /overwrite decide_True. Qed.

  Lemma overwrite_eq' (f : A → B) (a x : A) (b : B) :
    a = x →
      f.{[a := b]} x = b.
  Proof. intros ->. apply overwrite_eq. Qed.

  Lemma overwrite_neq (f : A → B) (a x : A) (b : B) :
    a ≠ x →
      f.{[a := b]} x = f x.
  Proof. intros ?. by rewrite /overwrite decide_False. Qed.

End overwrite.

(** [filling]. *)

Section filling.

  Lemma filling_nil y : Let [] .in y = Leaf _ y.
  Proof. done. Qed.

  Lemma filling_snoc K x op a b y :
    Let (K ++ [(x, (op, a, b))]) .in y =
      if decide (x = y) then
        Node _ op
          (Let K .in a)
          (Let K .in b)
      else
        Let K .in y.
  Proof. rewrite /filling foldl_app -/filling. done. Qed.

  Corollary filling_snoc_eq K x op a b :
    Let (K ++ [(x, (op, a, b))]) .in x = Node _ op (Let K .in a) (Let K .in b).
  Proof. by rewrite filling_snoc decide_True. Qed.

  Corollary filling_snoc_eq' K x op a b y :
    x = y →
      Let (K ++ [(x, (op, a, b))]) .in y = Node _ op (Let K .in a) (Let K .in b).
  Proof. intros ->. apply filling_snoc_eq. Qed.

  Corollary filling_snoc_neq K x n y :
    x ≠ y →
      Let (K ++ [(x, n)]) .in y = Let K .in y.
  Proof.
    intros. destruct n as ((?,?),?).
    by rewrite filling_snoc decide_False.
  Qed.
  
  Lemma filling_singleton x op a b y :
    Let [(x, (op, a, b))] .in y =
      if decide (x = y) then
        Node _ op (Leaf _ a) (Leaf _ b)
      else
        (Leaf _ y).
  Proof. by rewrite -(app_nil_l [_]) filling_snoc //=. Qed.

  Corollary filling_singleton_eq x op a b :
    Let [(x, (op, a, b))] .in x = Node _ op (Leaf _ a) (Leaf _ b).
  Proof. by rewrite filling_singleton decide_True. Qed.

  Corollary filling_singleton_eq' x op a b y :
    x = y →
      Let [(x, (op, a, b))] .in y = Node _ op (Leaf _ a) (Leaf _ b).
  Proof. intros ->. apply filling_singleton_eq. Qed.

  Corollary filling_singleton_neq x n y :
    x ≠ y → Let [(x, n)] .in y = Leaf _ y.
  Proof.
    intros. destruct n as ((?, ?), ?).
    by rewrite filling_singleton decide_False.
  Qed.
  
  Lemma filling_app K₁ K₂ y :
    y ∉ defs K₂ →
      Let (K₁ ++ K₂) .in y = Let K₁ .in y.
  Proof.
    induction K₂ as [|(x, ((op, a), b)) K₂ IHK₂] using rev_ind.
    { by rewrite app_nil_r. }
    { rewrite defs_app not_elem_of_app not_elem_of_cons
              app_assoc filling_snoc //=.
      intros [Hy [Hneq _]].
      case (decide (x = y)); [by intros ->|]. by rewrite IHK₂.
    }
  Qed.
  
  Corollary filling_undefined K y : y ∉ defs K → Let K .in y = Leaf _ y.
  Proof. intros Hy. by rewrite -(app_nil_l K) filling_app. Qed.

  Lemma filling_cons_middle K₁ K₂ x op a b y :
    y ∉ defs K₂ →
      Let (K₁ ++ (x, (op, a, b)) :: K₂) .in y =
        Let (K₁ ++ [(x, (op, a, b))]) .in y.
  Proof. by rewrite cons_middle app_assoc; apply filling_app. Qed.

  Corollary filling_cons_middle_eq K₁ K₂ x op a b :
    x ∉ defs K₂ →
      Let (K₁ ++ (x, (op, a, b)) :: K₂) .in x =
        Node _ op (Let K₁ .in a) (Let K₁ .in b).
  Proof. intros. by rewrite filling_cons_middle; [apply filling_snoc_eq|]. Qed.

  Corollary filling_cons_middle_eq' K₁ K₂ x op a b y :
    x = y → y ∉ defs K₂ →
      Let (K₁ ++ (x, (op, a, b)) :: K₂) .in y =
        Node _ op (Let K₁ .in a) (Let K₁ .in b).
  Proof.
    intros -> ?. by rewrite filling_cons_middle; [apply filling_snoc_eq|].
  Qed.

  Corollary filling_cons_middle_neq K₁ K₂ x n y :
    x ≠ y → y ∉ defs K₂ →
      Let (K₁ ++ (x, n) :: K₂) .in y = Let K₁ .in y.
  Proof.
    intros ??. destruct n as ((?, ?), ?).
    by rewrite filling_cons_middle; [apply filling_snoc_neq|].
  Qed.

End filling.

(** [extension]. *)

Section extension.
  Context {R : Set} {RS : RingSig R}.

  Lemma extension_snoc (ϱ : val → R) (K : context) x op a b :
    ϱ.{[K ++ [(x, (op, a, b))]]} =
      let ϱ := ϱ.{[K]} in
      ϱ.{[x := denote op (ϱ a) (ϱ b)]}.
  Proof. by rewrite /extension foldl_app. Qed.

  Lemma extension_alt (ϱ : val → R) (K : context) :
    ∀ y, ϱ.{[K]} y = eval (map ϱ (Let K .in y)).
  Proof.
    induction K as [|(x, ((op, a), b)) K IHK] using rev_ind; [done|].
    intro y. rewrite extension_snoc //=.
    case (decide (x = y)) as [->|Hneq].
    { by rewrite filling_snoc_eq overwrite_eq !IHK. }
    { rewrite filling_snoc_neq; [|done].
      rewrite overwrite_neq; [|done].
      by apply IHK. }
  Qed.

End extension.

(** [eval]. *)

Section eval.
  Context {R : Set} {RS : RingSig R}.

  Lemma eval_filling (ϱ : val → R) (K : context) x op a b y :
    let ϑ := ϱ.{[x := denote op (ϱ a) (ϱ b)]} in
    eval (map ϱ (Let ((x, (op, a, b)) :: K) .in y)) = eval (map ϑ (Let K .in y)).
  Proof.
    revert y op. induction K as [|(x', ((op', a'), b')) K IHK] using rev_ind.
    { intros y op. simpl. rewrite filling_singleton.
      case (decide (x = y)).
      - intros ->. simpl. rewrite overwrite_eq. done.
      - intros ?. simpl. rewrite overwrite_neq; done.
    }
    { intros y op. simpl. rewrite app_comm_cons !filling_snoc.
      case (decide (x' = y)).
      - intros ->. simpl. f_equal; apply IHK.
      - intros ?. apply IHK.
    }
  Qed.

  Lemma eval_trivial {I : Set} (e : Expr I) :
    eval (map (λ i, Leaf _ i) e) = e.
  Proof. induction e as [| |j|[|]]; try done; by rewrite //= IHe1 IHe2. Qed.

End eval.

(** [diff]. *)

Section diff.
  Context {I : Set} {EI : EqDecision I}
          {R : Set} {RS : RingSig R}.

  Lemma diff_leaf_eq (i : I) :
    ∀ (ϱ : I → R),
      (∂ (Leaf _ i) ./ ∂ i .at ϱ) = Iᵣ.
  Proof. intros ?. by rewrite //= decide_True. Qed.
  
  Corollary diff_leaf_eq' (i j : I) :
    i = j →
      ∀ (ϱ : I → R),
        (∂ (Leaf _ i) ./ ∂ j .at ϱ) = Iᵣ.
  Proof. intros ->. apply diff_leaf_eq. Qed.
  
  Lemma diff_leaf_neq (i j : I) :
    i ≠ j →
      ∀ (ϱ : I → R),
        (∂ (Leaf _ i) ./ ∂ j .at ϱ) = Oᵣ.
  Proof. intros ??. by rewrite //= decide_False. Qed.

  Lemma diff_bind_overwrite_leaf_id
    (ϱ : I → R) (e eⱼ : Expr I) (i j : I) :
    let f := (λ i, Leaf _ i).{[j := eⱼ]} in
    let ϑ := ϱ.{[j := eval (map ϱ eⱼ)]} in
    i ≠ j →
      (∂ eⱼ ./ ∂ i .at ϱ) = (Oᵣ) →
        (∂ (bind f e) ./ ∂ i .at ϱ) = (∂ e ./ ∂ i .at ϑ).
  Proof.
    intros ?? Hneq Hdiff.
    assert (∀ e, eval (map ϱ (bind f e)) = (eval (map ϑ e))) as Heval_bind.
    { clear e.
      induction e as [| |i'|[|] el IHel er IHer]; simpl;
      [done|done| |by rewrite IHel IHer|by rewrite IHel IHer].
      case (decide (i' = j)).
      - intros ->. unfold f, ϑ. by rewrite !overwrite_eq.
      - intros  ?. unfold f, ϑ. by rewrite !overwrite_neq.
    }
    induction e as [| |i'|[|] el IHel er IHer]; simpl;
    [done|done| |by rewrite IHel IHer|by rewrite IHel IHer !Heval_bind].
    { case (decide (j = i')).
      - intros ->. unfold f. by rewrite overwrite_eq Hdiff decide_False.
      - intros  ?. unfold f. by rewrite overwrite_neq.
    }
  Qed.

  Corollary diff_bind_overwrite_leaf_id_with_zero
    (ϱ : I → R) (e : Expr I) (i j : I) :
    let f := (λ i, Leaf _ i).{[j := (Oₑ)]} in
    let ϑ := ϱ.{[j := (Oᵣ)]} in
    i ≠ j →
      (∂ (bind f e) ./ ∂ i .at ϱ) = (∂ e ./ ∂ i .at ϑ).
  Proof. intros. by rewrite diff_bind_overwrite_leaf_id; [simpl; fold ϑ| |]. Qed.

  Corollary diff_bind_overwrite_leaf_id_with_one
    (ϱ : I → R) (e : Expr I) (i j : I) :
    let f := (λ i, Leaf _ i).{[j := (Iₑ)]} in
    let ϑ := ϱ.{[j := (Iᵣ)]} in
    i ≠ j →
      (∂ (bind f e) ./ ∂ i .at ϱ) = (∂ e ./ ∂ i .at ϑ).
  Proof. intros. by rewrite diff_bind_overwrite_leaf_id; [simpl; fold ϑ| |]. Qed.

  Lemma diff_strong_ext {CI : Countable I}
    (ϱ ϑ : I → R) (e : Expr I) (i : I) :
    (∀ j, j ∈ vars e → ϱ j = ϑ j) →
      (∂ e ./ ∂ i .at ϱ) = (∂ e ./ ∂ i .at ϑ).
  Proof.
    induction e as [| | |[|] ? IHl ? IHr]; [done|done|done| |].
    { intros Hvars. rewrite //= IHl; [rewrite IHr; [done|]|]; set_solver. }
    { intros Hvars. rewrite //= IHl; [rewrite IHr; [|]|]; [|set_solver|set_solver].
      rewrite !(map_strong_ext ϱ ϑ); [done| |]; set_solver.
    }
  Qed.

  Lemma diff_ext (ϱ ϑ : I → R) (e : Expr I) (i : I) :
    (∀ j, ϱ j = ϑ j) → (∂ e ./ ∂ i .at ϱ) = (∂ e ./ ∂ i .at ϑ).
  Proof.
    intros Hext. induction e as [| | |[|] ? IHl ? IHr]; [done|done|done| |].
    { by rewrite //= IHl IHr. }
    { by rewrite //= IHl IHr !(map_ext ϱ ϑ). }
  Qed.

  Lemma diff_map
               {CI : Countable  I}
    {J : Set}  {EJ : EqDecision J}
    (ϱ : I → J) (ϑ : J → R) (e : Expr I) (i : I) :
    (∀ j, j ∈ vars e → ϱ i = ϱ j → i = j) →
      (∂ (map ϱ e) ./ ∂ (ϱ i) .at ϑ) = (∂ e ./ ∂ i .at (ϑ ∘ ϱ)).
  Proof.
    induction e as [| |j|[|] el IHel er IHer]; [done|done| | |].
    { intros Hϱ. simpl.
      case (decide (ϱ i = ϱ j)).
      - intros Heq. rewrite (Hϱ j _ Heq); [|set_solver]. by rewrite decide_True.
      - case (decide (i = j)); [|done]. intros ->. contradiction.
    }
    { intros ?. rewrite //= IHel; [|set_solver]. by rewrite IHer; [|set_solver]. }
    { intros ?. rewrite //= IHel; [|set_solver]. rewrite IHer; [|set_solver].
      rewrite map_compose map_compose. done.
    }
  Qed.

  Lemma diff_trivial (e : Expr I) (i : I) (r : R) :
    eval (map (λ _, r) (∂ e ./ ∂ i .at (λ j, Leaf _ j))) = 
      (∂ e ./ ∂ i .at (λ _, r)).
  Proof.
    induction e as [| |j|[|]]; try done.
    { simpl. by case (decide (i = j)). }
    { by rewrite //= IHe1 IHe2. }
    { by rewrite //= IHe1 IHe2 !eval_trivial. }
  Qed.

End diff.

Section univariate_expr.

  Lemma eval_univariate_expr (e : Expr ()) :
    eval (map (λ _, Xₑ) e) = e.
  Proof.
   evar(e' : Expr ()).
   transitivity ?e';[|apply (eval_trivial e)].
   f_equal. apply map_ext. by intros ().
  Qed.

  Lemma diff_univariate_expr
    {R : Set} {RS : RingSig R}
    (e : Expr ()) (r : R) :
    eval (map (λ _, r) (∂ e ./ ∂ tt .at (λ _, Xₑ))) = 
      (∂ e ./ ∂ tt .at (λ _, r)).
  Proof.
    evar (s : R).
    transitivity ?s; [| apply (diff_trivial e tt r)].
    do 2 f_equal. apply diff_ext. by intros ().
  Qed.

End univariate_expr.

Section proofs_using_ring_tactic.
  Context {R : Set} {RS : RingSig R} {RA : IsRing R}.

  Add Ring LocalRing : is_semi_ring.

  Lemma diff_filling (ϱ : val → R) (K : context) x op a b y u :
    let ϑ   := overwrite ϱ x (denote op (ϱ a) (ϱ b)) in
    let a_b := Node _ op (Leaf _ a) (Leaf _ b) in
    x ≠ u →
      (∂ (Let ((x, (op, a, b)) :: K) .in y) ./ ∂ u .at ϱ) =ᵣ
        ((∂ (Let K .in y) ./ ∂ u .at ϑ) +ᵣ
         (∂ (Let K .in y) ./ ∂ x .at ϑ) ×ᵣ (∂ a_b ./ ∂ u .at ϱ)).
  Proof using RA.
    intros ??. revert y.
    induction K as [|(x', ((op', a'), b')) K'] using rev_ind.
    { intros y ?. rewrite filling_singleton filling_nil.
      case (decide (x = y)).
      - intros ->. rewrite diff_leaf_eq diff_leaf_neq; [|done]. fold a_b. ring.
      - intros  ?. rewrite(diff_leaf_neq y x); [|done]. simpl. ring.
    }
    { intros y ?. rewrite app_comm_cons !filling_snoc.
      case (decide (x' = y)); intros ?; [|by apply IHK'].
      destruct op'.
      - simpl. rewrite !IHK'; [|done|done]. simpl. ring.
      - simpl. rewrite !IHK'; [|done|done]. simpl.
        rewrite -!eval_filling. ring.
    }
  Qed.

  Lemma eval_equiv {I : Set} (e₁ e₂ : Expr I) (ϱ : I → R) :
    e₁ =ₑ e₂ →
      eval (map ϱ e₁) =ᵣ eval (map ϱ e₂).
  Proof using RA.
    induction 1; try done; try (try (destruct op); simpl; ring).
    { by rewrite IHExpr_equiv1. }
    { by destruct op; simpl; rewrite IHExpr_equiv1 IHExpr_equiv2. }
  Qed.

  Lemma diff_equiv
    {I : Set} {EI : EqDecision I}
    (e₁ e₂ : Expr I) (ϱ : I → R) (i : I) :
    e₁ =ₑ e₂ →
      (∂ e₁ ./ ∂ i .at ϱ) =ᵣ (∂ e₂ ./ ∂ i .at ϱ).
  Proof using RA.
    induction 1; try done; try (try (destruct op); simpl; ring).
    { by rewrite IHExpr_equiv1. }
    { destruct op; simpl; rewrite IHExpr_equiv1 IHExpr_equiv2; [done|].
      rewrite eval_equiv; [|done]. by rewrite (eval_equiv x). }
  Qed.

End proofs_using_ring_tactic.

(** Small detour on the chain rule. *)

Section chain_rule.
  Context {R : Set} {RS : RingSig R} {RA : IsRing R}
          {I : Set} `{CI : Countable I}
          {J : Set}  {EJ : EqDecision J}.

  Definition Sum (f : I → R) : gset I → R :=
    set_fold (λ i acc, acc +ᵣ f i) (Oᵣ).

  Notation "'Σ' i '.∈' S ';' e" := (Sum (λ i, e) S) (at level 70).

  (* Here is how the chain rule could be stated. The lemmas [diff_map],
     [diff_bind_overwrite_leaf_id] and [diff_filling] could be proven as
     corollaries of this property. However, we find that proving them
     directly ends up being simpler.
   *)
  Definition chain_rule_statement (e : Expr I) (f : I → Expr J) (ϱ : J → R) (j : J) :=
    let ϑ : I → R := λ i, eval (map ϱ (f i)) in
    (∂ (bind f e) ./ ∂ j .at ϱ) =ᵣ
      Σ i .∈ (vars e) ;
        (∂ e ./ ∂ i .at ϑ) ×ᵣ (∂ (f i) ./ ∂ j .at ϱ).

End chain_rule.

End properties.

Section ring_instances.

Global Instance UnitRing : RingSig () := {
  rzero := tt;
  rone  := tt;
  radd  := λ _ _, tt;
  rmul  := λ _ _, tt;
  req   := λ _ _, True;
}.

Global Program Instance UnitIsRing : IsRing ().
Next Obligation. done. Qed.

Global Instance ZRing : RingSig Z := {
  rzero := 0;
  rone  := 1;
  radd  := Z.add;
  rmul  := Z.mul;
  req   := (@eq Z);
}.

Global Program Instance ZIsRing : IsRing Z.
Next Obligation. split; simpl; lia. Qed.

Global Instance Expr_equiv_Equivalence {I : Set} :
  Equivalence (@Expr_equiv I) := {
    Equivalence_Reflexive  := Expr_equiv_refl;
    Equivalence_Symmetric  := Expr_equiv_symm;
    Equivalence_Transitive := Expr_equiv_trans;
}.

Definition ExprRing_srt {I : Set} :
  semi_ring_theory (Zero I) (One I) (Node I Add) (Node I Mul) Expr_equiv := {|
    SRadd_0_l   := Expr_equiv_add_0_l;
    SRadd_comm  := Expr_equiv_comm  Add;
    SRadd_assoc := Expr_equiv_assoc Add;
    SRmul_1_l   := Expr_equiv_mul_1_l;
    SRmul_0_l   := Expr_equiv_mul_0_l;
    SRmul_comm  := Expr_equiv_comm  Mul;
    SRmul_assoc := Expr_equiv_assoc Mul;
    SRdistr_l   := Expr_equiv_distr_l;
|}.

Program Instance ExprIsRing {I : Set} : IsRing (Expr I) := {
  req_equiv    := Expr_equiv_Equivalence;
  radd_ext     := Expr_equiv_ext Add;
  rmul_ext     := Expr_equiv_ext Mul;
  is_semi_ring := ExprRing_srt;
}.

End ring_instances.


(** * Specification. *)

Section specification.

Context `{!irisGS eff_lang Σ}.

Class NumSpec (N : Num) (Ψ : iEff Σ) {R : Set} (RS : RingSig R) := {
  implements : val → R → iProp Σ;

  nzero_spec : ⊢ implements nzero rzero;
  none_spec  : ⊢ implements none  rone;

  (* The following specifications are an alternative to the above ones.
     The difference is that [nzero] and [none] would no longer be values.
     They would be programs that the client could choose to execute to have
     access to a representation of the neutral elements of the ring.
     However, doing so leads to trickier internal specifications (the internal
     definition of [implements]), because the derivative field would not
     have meaning. It would have to be described by an invariant just so
     the update operations could go through. The same idea applies if we
     expose the function [create] to the client.
   *)
  (* nzero_spec E : ⊢ EWP nzero @ E <| Ψ |> {{ x, implements x rzero }}; *)
  (* none_spec  E : ⊢ EWP none  @ E <| Ψ |> {{ x, implements x rone  }}; *)

  nadd_spec E a b r s :
    implements a r -∗
      implements b s -∗
        EWP nadd a b @ E <| Ψ |> {{ x,
          implements x (radd r s) }};

  nmul_spec E a b r s :
    implements a r -∗
      implements b s -∗
        EWP nmul a b @ E <| Ψ |> {{ x,
          implements x (rmul r s) }};

  implements_pers u r :> Persistent (implements u r);

  (* See the remark bellow to understand the purpose of the following line. *)
  (* implements_ne   u n : Proper (req ==> (dist n)) (implements u); *)
}.

Definition isExp (f : Num → expr) (e : Expr ()) : iProp Σ :=
  (∀ (N : Num),
    EWP (f N) <| ⊥ |> {{ vf,
      (∀ (R : Set) (RS : RingSig R) (RA : IsRing R),
        (∀ (Ψ : iEff Σ) (NSpec : NumSpec N Ψ RS),
          (∀ x r,
            implements x r -∗
              EWP vf x <| Ψ |> {{ y, ∃ s,
                implements y s ∗ ⌜ s =ᵣ (eval (map (λ _, r) e)) ⌝ }})))}}).

(* Remark:
   -- The existentially quantified ring element [s] that appears in the
      postcondition of [diff] could be avoided by asking the predicate
      [implements] to be non-expansive. However, this would complicate the
      verification of [diff] because the numerical implementation of symbolic
      expressions that it provides to the client doesn't satisfy this property.
      The same trick of the existential quantification might work for turning
      the [implements] predicate non-expansive, but again, we choose simplicity.
*)

Definition diff_spec : iProp Σ :=
  (∀ (f : Num → expr) (e : Expr ()),
    isExp f e -∗
      isExp (diff f) (∂ e ./ ∂ tt .at (λ _, Xₑ))).

Lemma isExp_ext (f : Num → expr) (e₁ e₂ : Expr ()) :
  e₁ =ₑ e₂ →
    isExp f e₁ -∗ isExp f e₂.
Proof.
  iIntros (He) "Hf". iIntros (N).
  iApply (ewp_mono' with "Hf").
  iIntros (vf) "Hvf". iModIntro.
  iIntros (R RS RA Ψ NSpec x r) "Hx".
  iSpecialize ("Hvf" with "Hx").
  iApply (ewp_mono' with "Hvf").
  iIntros (y) . iDestruct 1 as (s) "[Hs %]".
  iExists s. iModIntro. iFrame. iPureIntro.
  rewrite H. by apply eval_equiv.
Qed.

End specification.


(** * Verification. *)

Section verification.

(** Camera setup. *)

(** We define our personalised notion of resource. This means that we have
    defined a structure whose elements can be claimed to be owned. We have
    thus extended the language of logical propositions. Within this newly
    added fragment of the language, we will be able to write what it means
    for the current context to be in a certain state or for one to known
    that it contains a certain entry.
*)

Section camera.

  Canonical Structure nodeO := leibnizO node.

  (* Our personalised resource is [gmap_viewR loc nodeO] and here we define
     a typeclass claiming for it to be among the underlying resources
     parameterizing [iProp].
  *)
  Class cgraphG Σ := {
    cgraph_mapG :> inG Σ (gmap_viewR val nodeO);
  }.

  (* Now we prove that this claim can be satisfied by exhibiting a concrete
     list of resources containing our personalised one. (This isn't trivial,
     because the resource definition could depend on the list of resources
     to which it must belong.)
   *)
  Definition cgraphΣ := #[
    GFunctor (gmap_viewR val nodeO)
  ].

  Instance subG_cgraphΣ {Σ} : subG cgraphΣ Σ → cgraphG Σ.
  Proof. solve_inG. Qed.

End camera.

(** Ghost theory. *)

(** The derived definitions and their properties. *)

Section ghost_theory.
  Context `{!cgraphG Σ}.

  Definition context_to_map (K : context) : gmap val node :=
    list_to_map (reverse K).

  Definition is_current_context (γ : gname) (K : context) : iProp Σ :=
    own γ (gmap_view_auth (V:=nodeO) (DfracOwn 1) (context_to_map K)).

  Definition is_entry (γ : gname) (u : val) (n : node) : iProp Σ :=
    own γ (gmap_view_frag (V:=nodeO) u DfracDiscarded n).

  Lemma context_alloc : ⊢ |==> ∃ γ, is_current_context γ [].
  Proof.
    iMod (own_alloc (gmap_view_auth (V:=nodeO) (DfracOwn 1) ∅)) as (γ) "Hauth".
    { by apply gmap_view_auth_valid. }
    { by eauto. }
  Qed.

  Lemma context_lookup (γ : gname) (K : context) (u : val) (n : node) :
    is_current_context γ K -∗
      is_entry γ u n -∗
        ⌜ context_to_map K !! u = Some n ⌝.
  Proof.
    iIntros "Hauth Hfrag".
    by iDestruct (own_valid_2 with "Hauth Hfrag")
      as %[_[_?]]%gmap_view_both_dfrac_valid_L.
  Qed.

  Lemma context_update (γ : gname) (K : context) (u : val) (n : node) :
    context_to_map K !! u = None →
      is_current_context γ K ==∗
        is_current_context γ (K ++ [(u, n)]) ∗ is_entry γ u n.
  Proof.
    iIntros (Hlookup) "Hauth". rewrite -own_op.
    iApply own_update. unfold context_to_map.
    rewrite reverse_app. simpl.
    by apply gmap_view_alloc. done.
  Qed.

  Global Instance is_entry_pers γ u n : Persistent (is_entry γ u n).
  Proof. apply _. Qed.

End ghost_theory.

Section represents.
  Context `{!cgraphG Σ, !heapG Σ}
           {R : Set} {RS : RingSig R}
           {N : Num} {Ψ : iEff Σ} {NSpec : NumSpec N Ψ RS}.

  Variables (γ  : gname) (* Identifies assertions of the same ghost theory.  *)
            (ℓₓ : loc)   (* Memory location associated with the input value. *)
            (r  : R)     (* The point at which the derivative was asked.     *)
            (nᵣ : val).  (* A value representing [r].                        *)

  Notation a₀ := (InjLV (InjLV #()))%V  (only parsing).
  Notation a₁ := (InjLV (InjRV #()))%V  (only parsing).
  Notation aₓ := (InjRV (nᵣ,   #ℓₓ))%V  (only parsing).

  Definition represents : val → Expr () → iProp Σ :=
    fix represents (u : val) (e : Expr ()) : iProp Σ :=
      match e with
      | Zero _          => ⌜ u = a₀ ⌝
      | One  _          => ⌜ u = a₁ ⌝
      | Leaf _ _        => ⌜ u = aₓ ⌝
      | Node _ op el er => ∃ a b,
         is_entry γ u (op, a, b) ∗
         represents a el         ∗
         represents b er
      end%I.

  Global Instance represents_pers x e : Persistent (represents x e).
  Proof. revert e x. induction e; apply _. Qed.

End represents.

(* The following section contains general facts that are useful in the
   subsequent sections.
*)

Section general_facts.

  Lemma NoDup_cons_middle {A : Type} (y : A) (xs ys : list A) :
    NoDup (xs ++ y :: ys) →
      NoDup xs ∧
      (y ∉ xs) ∧
      (∀ x, x ∈ xs → x ∉ ys) ∧
      (y ∉ ys) ∧
      NoDup ys.
  Proof.
    rewrite cons_middle app_assoc !NoDup_app.
    intros ((HNoDup_xs & Hnot_in_xs & _) & Hnot_in_ys & HNoDup_ys).
    split; [done|]. split; [|split; [|split; [|done]]].
    { intro Hin. by apply (Hnot_in_xs _ Hin), elem_of_list_singleton. }
    { intros x Hin. apply Hnot_in_ys, elem_of_app. by left. }
    { apply Hnot_in_ys, elem_of_app. right. by apply elem_of_list_singleton. }
  Qed.

  Lemma NoDup_app_11 {A : Type} (xs ys : list A) : NoDup (xs ++ ys) → NoDup xs.
  Proof. rewrite NoDup_app. by intros [? _]. Qed.

  Lemma NoDup_app_12 {A : Type} (xs ys : list A) :
    NoDup (xs ++ ys) → ∀ x, x ∈ xs → x ∉ ys.
  Proof. rewrite NoDup_app. by intros (_ & ? & _). Qed.

  Lemma NoDup_app_13 {A : Type} (xs ys : list A) : NoDup (xs ++ ys) → NoDup ys.
  Proof. rewrite NoDup_app. by intros (_ & _ & ?). Qed.

  (* Although very specific, this lemma is useful in
     combination with the invariants.
   *)
  Lemma big_sepL_NoDup `{!heapG Σ} us :
    ([∗ list] u ∈ us, ∃ v w ℓ,
       ℓ ↦ w ∗ ⌜ u = InjRV (v, #ℓ)%V ⌝) -∗
      ⌜ NoDup us ⌝.
  Proof.
    iIntros "Hus". iInduction us as [|u us] "IH".
    { iPureIntro. by apply NoDup_nil. }
    { iDestruct "Hus" as "[Hu Hus]". iAssert (⌜ u ∉ us ⌝)%I as "%".
      { iIntros (Hin).
        iDestruct (big_sepL_elem_of _ _ _ Hin with "Hus") as "Hu'".
        iDestruct "Hu"  as (???) "[Hu  ->]".
        iDestruct "Hu'" as (???) "[Hu' %]".
        rename H into Heq. inversion Heq.
        by iDestruct (mapsto_ne with "Hu Hu'") as "%".
      }
      iDestruct ("IH" with "Hus") as "%". rename H0 into HNoDup.
      iPureIntro. by apply NoDup_cons_2.
    }
  Qed.

  Lemma big_sepL_strong_mono `{!irisGS eff_lang Σ}
    {A : Type} (us : list A) (Φ₁ Φ₂ : nat → A → iProp Σ) :
    (∀ i u, us !! i = Some u → Φ₁ i u -∗ Φ₂ i u) →
      ([∗ list] i ↦ u ∈ us, Φ₁ i u) -∗
        ([∗ list] i ↦ u ∈ us, Φ₂ i u).
  Proof.
    revert Φ₁ Φ₂.
    induction us as [|u us]; [done|].
    intros Φ₁ Φ₂ Hmono. simpl. iIntros "[Hu Hus]". iSplitL "Hu".
    { by iApply (Hmono with "Hu"). }
    {  iApply (IHus with "Hus"). naive_solver. }
  Qed.

  Lemma big_sepL_strong_mono' `{!irisGS eff_lang Σ}
    {A : Type} (us : list A) (Φ₁ Φ₂ : A → iProp Σ) :
    (∀ u, u ∈ us → Φ₁ u -∗ Φ₂ u) →
      ([∗ list] u ∈ us, Φ₁ u) -∗
        ([∗ list] u ∈ us, Φ₂ u).
  Proof.
    intros Hmono. apply big_sepL_strong_mono.
    intros i u Hlkp. apply Hmono.
    by apply (elem_of_list_lookup_2 _ i).
  Qed.

End general_facts.

(** Forward invariant. *)

(** The forward invariant is a predicate on contexts. If we imagine the
    execution of the client as a trace indexed by the sequence of arithmetic
    operations (that is, a context), then the invariant asserts what holds
    for each such sequence at each step.
*)

Section forward_invariant.
  Context `{!cgraphG Σ, !heapG Σ}
           {R : Set} {RS : RingSig R}
           {N : Num} {Ψ : iEff Σ} {NSpec : NumSpec N Ψ RS}.

  Variables (γ  : gname) (* Identifies assertions of the same ghost theory.  *)
            (ℓₓ : loc)   (* Memory location associated with the input value. *)
            (r  : R)     (* The point at which the derivative was asked.     *)
            (nᵣ : val).  (* A value representing [r].                        *)

  Notation a₀         := (InjLV (InjLV #()))%V (only parsing).
  Notation a₁         := (InjLV (InjRV #()))%V (only parsing).
  Notation aₓ         := (InjRV (nᵣ,   #ℓₓ))%V (only parsing).
  Notation adj_vars   := ([a₀; a₁; aₓ])        (only parsing).
  Notation represents := (represents γ ℓₓ nᵣ)  (only parsing).

  Definition forward_inv (K : context) : iProp Σ := (
    let ϱ := (λ _, r).{[a₀ := Oᵣ]}.{[a₁ := Iᵣ]} in

    is_current_context γ K                    ∗
    ⌜ ∀ u, u ∈ defs K →
        vars (Let K .in u) ⊆ {[a₀; a₁; aₓ]} ⌝ ∗
    ( [∗ list] u ∈ defs K ++ [aₓ], ∃ v ℓ,
        implements v (ϱ.{[K]} u)              ∗
        ℓ ↦ nzero                             ∗
        ⌜ u = InjRV (v, #ℓ)%V ⌝               )
  )%I.

  Lemma NoDup_defs_app_adj_vars K :
    forward_inv K -∗ ⌜ NoDup (defs K ++ [aₓ]) ⌝.
  Proof.
    iIntros "(_ & _ & HK)". iApply big_sepL_NoDup.
    iApply (big_sepL_mono with "HK"). iIntros (i u _). simpl.
    iDestruct 1 as (v ℓ) "[_ Hu]". by eauto.
  Qed.

  Corollary NoDup_defs K :
    forward_inv K -∗ ⌜ NoDup (defs K) ⌝.
  Proof.
    iIntros "Hinv".
    by iDestruct (NoDup_defs_app_adj_vars with "Hinv")
      as %?%NoDup_app_11.
  Qed.

  Lemma distinct_adj_vars_1x : a₁ ≠ aₓ.
  Proof. done. Qed.

  Lemma distinct_adj_vars_0x : a₀ ≠ aₓ.
  Proof. done. Qed.

  Lemma elem_of_defs_inv K :
    forward_inv K -∗ ⌜ ∀ a, a ∈ defs K → ∃ v (ℓ : loc), a = InjRV (v, #ℓ)%V ⌝.
  Proof.
    iIntros "[_ [_ Hheap]]" (a Hin).
    destruct (elem_of_list_lookup_1 _ _ Hin) as [i Hi].
    rewrite big_sepL_app (big_sepL_delete' _ _ _ _ Hi).
    iDestruct "Hheap" as "[[Ha _] _]".
    iDestruct "Ha" as (v ℓ) "(_ & _ & ->)". by eauto.
  Qed.

  Lemma elem_of_defs_inv' K :
    forward_inv K -∗
      ⌜ ∀ a, a ∈ defs K ++ [aₓ] → ∃ v (ℓ : loc), a = InjRV (v, #ℓ)%V ⌝.
  Proof.
    iIntros "Hinv". iDestruct (elem_of_defs_inv with "Hinv") as %?.
    iPureIntro. intros a. rewrite elem_of_app elem_of_cons elem_of_nil.
    by intros [|[->|]]; eauto.
  Qed.

  Lemma adj_vars_not_in_defs K :
    forward_inv K -∗ ⌜ a₀ ∉ defs K ∧ a₁ ∉ defs K ∧ aₓ ∉ defs K ⌝.
  Proof.
    iIntros "Hinv".
    iDestruct (NoDup_defs_app_adj_vars with "Hinv") as %HND.
    iDestruct (elem_of_defs_inv        with "Hinv") as %Hdefs.
    revert HND. rewrite NoDup_app. intros (_&Hinter&_).
    iPureIntro. set_solver.
  Qed.

  Corollary adj_var_0_not_in_defs K :
    forward_inv K -∗ ⌜ a₀ ∉ defs K ⌝.
  Proof.
    iIntros "Hinv".
    by iDestruct (adj_vars_not_in_defs with "Hinv") as %(?&_&_).
  Qed.

  Corollary adj_var_1_not_in_defs K :
    forward_inv K -∗ ⌜ a₁ ∉ defs K ⌝.
  Proof.
    iIntros "Hinv".
    by iDestruct (adj_vars_not_in_defs with "Hinv") as %(_&?&_).
  Qed.

  Corollary adj_var_x_not_in_defs K :
    forward_inv K -∗ ⌜ aₓ ∉ defs K ⌝.
  Proof.
    iIntros "Hinv".
    by iDestruct (adj_vars_not_in_defs with "Hinv") as %(_&_&?).
  Qed.

  Lemma context_wf_aux K K₁ K₂ x op a b c :
    c = a ∨ c = b →
    K = K₁ ++ (x, (op, a, b)) :: K₂ →
      forward_inv K -∗ ⌜ c ∉ x :: defs K₂ ⌝.
  Proof.
    intros Hc ->. iIntros "Hinv" (Hin).
    iDestruct (adj_vars_not_in_defs with "Hinv") as %(Ha₀&Ha₁&Haₓ).
    iDestruct (NoDup_defs_app_adj_vars with "Hinv") as %HNoDup.
    iDestruct "Hinv" as "[_ [% _]]". rename H into Hvars.
    iPureIntro.
    rewrite defs_cons_middle in HNoDup, Hvars, Ha₀, Ha₁, Haₓ.
    cut (c ∈ [a₀; a₁; aₓ]).
    { rewrite !elem_of_cons elem_of_nil.
      intros [->|[->|[->|]]]; last done;
      [apply Ha₀|apply Ha₁|apply Haₓ];
      rewrite elem_of_app; by right.
    }
    { cut (c ∈ ({[a₀; a₁; aₓ]} : gset val)); [set_solver|].
      have Hx_in: x ∈ defs K₁ ++ x :: defs K₂. { set_solver. }
      apply (Hvars x Hx_in).
      have Hc_notin: c ∉ defs K₁.
      { destruct Hc as [<-|<-]; intros Hin_K₁;
        by apply (NoDup_app_12 _ _ (NoDup_app_11 _ _ HNoDup) c).
      }
      rewrite filling_cons_middle_eq.
      - destruct Hc as [<-|<-];
        rewrite //= (filling_undefined _ c Hc_notin); set_solver.
      - by specialize (NoDup_cons_middle _ _ _
                      (NoDup_app_11 _ _ HNoDup)) as (_&_&_&?&_).
    }
  Qed.

  Corollary context_wf_1 K K₁ K₂ x op a b :
    K = K₁ ++ (x, (op, a, b)) :: K₂ →
      forward_inv K -∗ ⌜ a ∉ x :: defs K₂ ⌝.
  Proof. apply context_wf_aux. by left. Qed.

  Corollary context_wf_2 K K₁ K₂ x op a b :
    K = K₁ ++ (x, (op, a, b)) :: K₂ →
      forward_inv K -∗ ⌜ b ∉ x :: defs K₂ ⌝.
  Proof. apply context_wf_aux. by right. Qed.

  Lemma elem_of_context K x op el er :
    forward_inv K -∗
      represents x (Node _ op el er) -∗ 
        forward_inv K ∗ ∃ a b,
        represents a el       ∗
        represents b er       ∗
        ⌜ (x, (op, a, b)) ∈ K ⌝.
  Proof.
    iIntros "[Hauth Hrest]". simpl. iDestruct 1 as (a b) "(Hfrag&Ha&Hb)".
    iDestruct (context_lookup with "Hauth Hfrag") as %Hlkp. iFrame.
    iExists a, b. iFrame.
    iPureIntro. rewrite -elem_of_reverse.
    by apply (elem_of_list_to_map_2 (K:=val) (M:=gmap val)).
  Qed.

  Lemma elem_of_defs K x op el er :
    forward_inv K -∗
      represents x (Node _ op el er) -∗ 
        ⌜ x ∈ defs K ⌝.
  Proof.
    iIntros "Hinv Hx".
    iDestruct (elem_of_context with "Hinv Hx") as "[_ Hin]".
    iDestruct "Hin" as (a b) "(_&_&%)". iPureIntro.
    rewrite elem_of_list_fmap.
    by exists (x, (op, a, b)).
  Qed.

  Lemma elem_of_defs_app_adj_vars K u e :
    forward_inv K -∗ represents u e -∗ ⌜ u ∈ defs K ++ adj_vars ⌝.
  Proof.
    iIntros "Hinv Hu". destruct e as [| | |op el er]; try (
    iDestruct "Hu" as "->"; iPureIntro; set_solver).
    iDestruct (elem_of_defs with "Hinv Hu") as %Hin.
    iPureIntro. rewrite elem_of_app. by left.
  Qed.

  Lemma adj_var_cases K u e :
    forward_inv K -∗
      represents u e -∗
        ⌜ u ∈ defs K ++ [aₓ] ∨ u = a₀ ∨ u = a₁ ⌝.
  Proof.
    iIntros "Hinv Hu".
    iDestruct (elem_of_defs_app_adj_vars with "Hinv Hu") as %Hu.
    iPureIntro.
    revert Hu; rewrite !elem_of_app !elem_of_cons elem_of_nil.
    naive_solver.
  Qed.

  Lemma elem_of_adj_vars u :
    u ∈ adj_vars → u = a₀ ∨ u = a₁ ∨ u = aₓ.
  Proof. by rewrite !elem_of_cons elem_of_nil; naive_solver. Qed.

  Lemma vars_subseteq K u e :
    forward_inv K -∗
      represents u e -∗
        ⌜ vars (Let K .in u) ⊆ {[a₀; a₁; aₓ]} ⌝.
  Proof.
    iIntros "Hinv #Hu".
    iDestruct (adj_var_0_not_in_defs with "Hinv") as %Ha₀.
    iDestruct (adj_var_1_not_in_defs with "Hinv") as %Ha₁.
    iDestruct (adj_var_x_not_in_defs with "Hinv") as %Haₓ.
    iDestruct (elem_of_defs_app_adj_vars with "Hinv Hu")
      as %[Hu|Hu]%elem_of_app; [|
    destruct (elem_of_adj_vars u Hu) as [Hu'|[Hu'|Hu']];
    rewrite Hu'; iPureIntro;
    by rewrite filling_undefined; [set_solver|]].
    iDestruct "Hinv" as "[_ [% _]]". rename H into Hvars.
    iPureIntro. by apply Hvars.
  Qed.

  Lemma forward_inv_agree_aux e :
    let f := (Leaf _).{[a₀ := Oₑ]} in
    let g := (Leaf _).{[a₁ := Iₑ]} in
    ∀ K₁ K₂ u,
      u ∉ defs K₂ →
        forward_inv (K₁ ++ K₂) -∗
          represents u e -∗
            ⌜ e = (map (λ _, tt)
                  (bind f (bind g (Let K₁ .in u)))) ⌝.
  Proof.
    intros ??. induction e as [| |()|?? IHl ? IHr].
    { intros K₁ K₂ u Hnot_in. iIntros "Hinv ->".
      iDestruct (adj_var_0_not_in_defs with "Hinv") as %Hℓ₀.
      iPureIntro. rewrite filling_undefined; [|set_solver].
      simpl. unfold f, g.
      rewrite overwrite_neq; [|done]. simpl.
      rewrite overwrite_eq. done.
    }
    { intros K₁ K₂ u Hnot_in. iIntros "Hinv ->".
      iDestruct (adj_var_1_not_in_defs with "Hinv") as %Hℓ₁.
      iPureIntro. rewrite filling_undefined; [|set_solver].
      simpl. unfold f, g. rewrite overwrite_eq. done.
    }
    { intros K₁ K₂ u Hnot_in. iIntros "Hinv ->".
      iDestruct (adj_var_x_not_in_defs with "Hinv") as %Hℓₓ.
      iPureIntro. rewrite filling_undefined; [|set_solver].
      simpl. unfold f, g.
      rewrite overwrite_neq; [|done]. simpl.
      rewrite overwrite_neq; done.
    }
    { intros K₁ K₂ u Hnot_in. iIntros "Hinv Hrepr".
      iDestruct (NoDup_defs with "Hinv") as %HNoDup.
      iDestruct (elem_of_context with "Hinv Hrepr") as "[Hinv Hrepr]".
      iDestruct "Hrepr" as (a b) "(Ha & Hb & %)". rename H into Hin.
      revert Hin. rewrite elem_of_app. intros [Hin|Hin]; [|
      by cut (u ∈ defs K₂);[|rewrite elem_of_list_fmap; exists (u, (op, a, b))]].
      destruct (elem_of_list_split_r _ _ Hin) as [K₁₁ [K₁₂ [-> Hnot_in']]].
      rewrite defs_app defs_cons_middle in HNoDup.
      destruct (NoDup_cons_middle _ _ _ (NoDup_app_11 _ _ HNoDup))
        as (_&_&_&?&_).
      rewrite filling_cons_middle_eq; [|done].
      rewrite -app_assoc. simpl.
      iDestruct (context_wf_1 (K₁₁ ++ _) K₁₁ _ with "Hinv") as %Ha; [done|].
      iDestruct (context_wf_2 (K₁₁ ++ _) K₁₁ _ with "Hinv") as %Hb; [done|].
      iDestruct (IHl K₁₁ _ a with "Hinv Ha") as %->; [done|].
      iDestruct (IHr K₁₁ _ b with "Hinv Hb") as %->;  done.
    }
  Qed.

  Corollary forward_inv_agree K u e :
    let f := (Leaf _).{[a₀ := Oₑ]} in
    let g := (Leaf _).{[a₁ := Iₑ]} in
    forward_inv K -∗
      represents u e -∗
        ⌜ e = (map (λ _, tt)
              (bind f (bind g (Let K .in u)))) ⌝.
  Proof.
    intros ??. rewrite -{1}(app_nil_r K).
    apply forward_inv_agree_aux, not_elem_of_nil.
  Qed.

  Lemma diff_output K y e :
    let ϱ := (λ _, r).{[a₀ := Oᵣ]}.{[a₁ := Iᵣ]} in
    forward_inv K -∗
      represents y e -∗
        ⌜ ∂ e             ./ ∂ tt .at (λ _, r) =
          ∂ (Let K .in y) ./ ∂ aₓ .at       ϱ  ⌝.
  Proof.
    set f := (Leaf _).{[a₀ := Oₑ]}.
    set g := (Leaf _).{[a₁ := Iₑ]}.
    intros ?. iIntros "Hinv Hy".
    iDestruct (forward_inv_agree with "Hinv Hy") as %->.
    iDestruct (vars_subseteq with "Hinv Hy") as %Hvars.
    iPureIntro. fold f g. rewrite (diff_map _ _ _ aₓ).
    { rewrite (diff_ext ((λ _, r) ∘ (λ _, ())) (λ _, r)); [|done].
      rewrite diff_bind_overwrite_leaf_id_with_zero; [|done].
      rewrite diff_bind_overwrite_leaf_id_with_one; done.
    }
    { (* TODO: Avoid the duplication of proofs here. *)
      intros j Hj _.
      have Hfi: vars (f a₀) = ∅. { by rewrite /f overwrite_eq. }
      have Hfj: ∀ j, vars (f j) ⊆ {[j]}. {
       intros k. case (decide (k = a₀)) as[->|Hneq].
       + unfold f. by rewrite overwrite_eq.
       + unfold f. by rewrite overwrite_neq.
      }
      have Hgi: vars (g a₁) = ∅. { by rewrite /g overwrite_eq. }
      have Hgj: ∀ j, vars (g j) ⊆ {[j]}. {
       intros k. case (decide (k = a₁)) as[->|Hneq].
       + unfold g. by rewrite overwrite_eq.
       + unfold g. by rewrite overwrite_neq.
      }
      specialize (vars_suppressing _ f a₀ Hfi Hfj _ Hj) as Hf.
      specialize (vars_suppressing (Let K .in y) g a₁ Hgi Hgj) as Hg.
      cut (j ∈ ({[a₀; a₁; aₓ]} ∖ {[a₁]} ∖ {[a₀]} : gset val)). set_solver.
      cut (j ∈ (vars (Let K .in y) ∖ {[a₁]} ∖ {[a₀]})). set_solver.
      cut (j ∈ (vars (bind g (Let K .in y)) ∖ {[a₀]})); set_solver.
    }
  Qed.

  Lemma forward_inv_fresh_loc K ℓ d :
    ℓ ↦ d -∗
      forward_inv K -∗
        ⌜ ∀ v, InjRV (v, #ℓ)%V ∉ defs K ++ [aₓ] ⌝.
  Proof.
    iIntros "Hu [_ [_ Hheap]]" (v).
    iInduction (defs K ++ [aₓ]) as [|u us] "IH".
    { iPureIntro. by apply not_elem_of_nil. }
    { rewrite not_elem_of_cons. simpl.
      iDestruct "Hheap" as "[Hy Hheap]".
      iDestruct "Hy" as (v' ℓ') "[_ [Hy ->]]".
      iSplit.
      { iDestruct (mapsto_ne with "Hu Hy") as %H.
        iPureIntro. inversion 1. contradiction. }
      { by iApply ("IH" with "Hu Hheap"). }
    }
  Qed.

  Corollary forward_inv_lookup K ℓ d :
    ℓ ↦ d -∗
      forward_inv K -∗
        ⌜ ∀ v, context_to_map K !! (InjRV (v, #ℓ))%V = None ⌝.
  Proof.
    iIntros "Hx Hinv" (v).
    iDestruct (forward_inv_fresh_loc with "Hx Hinv") as %Hnot_in.
    iPureIntro. apply not_elem_of_list_to_map_1. set_solver.
  Qed.

  Lemma forward_inv_update K x op a b v (ℓ : loc) el er :
    let ϱ  := (λ _, r).{[a₀ := Oᵣ]}.{[a₁ := Iᵣ]} in
    let K' := K ++ [(x, (op, a, b))] in
    x = InjRV (v, #ℓ)%V →
      forward_inv K -∗
        represents a el -∗
          represents b er -∗
            implements v (ϱ.{[K']} x) -∗
              ℓ ↦ nzero ==∗
                forward_inv K' ∗
                represents x (Node _ op el er).
  Proof.
    intros ??. iIntros (->) "Hinv #Ha #Hb Hv Hx". fold ϱ.
    iDestruct (forward_inv_fresh_loc with "Hx Hinv") as %Hnot_in.
    iDestruct (forward_inv_lookup with "Hx Hinv") as %Hlkp.
    iDestruct (vars_subseteq with "Hinv Ha") as %Hvars_a.
    iDestruct (vars_subseteq with "Hinv Hb") as %Hvars_b.
    iDestruct "Hinv" as "(HK & % & Hheap)". rename H into Hvars.
    iMod (context_update _ _ _ (op,a,b) (Hlkp v) with "HK")
      as "[HK' Hentry]".
    iModIntro. iSplitL "HK' Hheap Hx Hv"; [|
    iExists a, b; iFrame; iSplit; by iFrame ].
    iSplitL "HK'"; [by iApply "HK'"|]. fold ϱ. iSplit; [iPureIntro|].
    { intro u. rewrite defs_app elem_of_app //= elem_of_list_singleton.
      intros [|]; rename H into Hu; [|rewrite Hu].
      - rewrite filling_snoc_neq; [by apply Hvars|]. set_solver.
      - rewrite filling_snoc_eq //= union_subseteq. done.
    }
    { rewrite (big_opL_permutation _ (defs K' ++ _) (_ :: defs K ++ [aₓ]));[|
      by rewrite /K' defs_app defs_cons
         -(Permutation_cons_append _ (InjRV (v, _))%V) //=].
      iSplitL "Hx Hv"; [iExists v, ℓ; iSplit; by iFrame|].
      iApply (big_sepL_strong_mono' with "Hheap").
      intros. unfold K'.
      by rewrite extension_snoc //= overwrite_neq; [|set_solver].
    }
  Qed.

End forward_invariant.

Section forward_invariant_alloc.
  Context `{!cgraphG Σ, !heapG Σ}
           {R : Set} {RS : RingSig R}
           {N : Num} {Ψ : iEff Σ} {NSpec : NumSpec N Ψ RS}.

  Variables (ℓₓ : loc) (r  : R) (nᵣ : val).

  Lemma forward_inv_alloc :
    implements nᵣ r -∗
      ℓₓ ↦ nzero ==∗
        ∃ γ, forward_inv γ ℓₓ r nᵣ [].
  Proof.
    iIntros "Hnᵣ Hℓₓ".
    iMod (context_alloc) as (γ) "Hcontext".
    iModIntro. iExists γ. iFrame. iSplit.
    { iPureIntro. intros ?. by rewrite elem_of_nil. }
    { rewrite //=.
      iSplit; [|done]. iExists nᵣ, ℓₓ. iFrame.
      rewrite overwrite_neq; [|done].
      rewrite overwrite_neq; [|done].
      by iFrame.
    }
  Qed.

End forward_invariant_alloc.

(** Backward invariant. *)

(** After the execution of the client, the handler traverses the complete
    sequence of operations in reverse order. We can thus split this complete
    sequence into a pair of contexts, its prefix and suffix, and state what
    holds at each step of this phase in terms of those.
*)

Section backward_invariant.
  Context `{!cgraphG Σ, !heapG Σ}
           {R : Set} {RS : RingSig R} {RA : IsRing R}
           {N : Num} {Ψ : iEff Σ} {NSpec : NumSpec N Ψ RS}.

  Variables (γ  : gname)
            (ℓₓ : loc)
            (r  : R)
            (nᵣ : val)
            (e : Expr ()). (* The expression implemented by the client. *)

  Notation a₀         := (InjLV (InjLV #()))%V (only parsing).
  Notation a₁         := (InjLV (InjRV #()))%V (only parsing).
  Notation aₓ         := (InjRV (nᵣ,   #ℓₓ))%V (only parsing).
  Notation adj_vars   := ([a₀; a₁; aₓ])        (only parsing).
  Notation represents := (represents γ ℓₓ nᵣ)  (only parsing).

  Definition mapsto_diff (K₁ K₂ : context) (y u : val) : iProp Σ :=
    let ϱ := (λ _, r).{[a₀ := Oᵣ]}.{[a₁ := Iᵣ]} in
    let ϑ := ϱ.{[K₁]} in
    (∀ v (ℓ : loc), ⌜ u = InjRV (v, #ℓ)%V ⌝ →
      (∃ d s,
        implements d s                         ∗
        ⌜ s =ᵣ ∂ (Let K₂ .in y) ./ ∂ u .at ϑ ⌝ ∗
        ℓ ↦ d                                  )
    )%I.

  Definition backward_inv (K₁ K₂ : context) (y : val) : iProp Σ := (
    let ϱ := (λ _, r).{[a₀ := Oᵣ]}.{[a₁ := Iᵣ]} in
    ⌜ ∂ e                      ./ ∂ tt .at (λ _, r) =ᵣ
      ∂ (Let (K₁ ++ K₂) .in y) ./ ∂ aₓ .at       ϱ    ⌝ ∗
    ( [∗ list] u ∈ defs K₁ ++ [aₓ], ∃ v (ℓ : loc),
        mapsto_diff K₁ K₂ y u                           ∗
        ⌜ u = InjRV (v, #ℓ)%V ⌝                         )
  )%I.

  Definition is_adj_var (a : val) : iProp Σ :=
    ⌜ (∃ (w : val),           a = InjLV  w       ) ∨
      (∃ (n : val) (ℓ : loc), a = InjRV (n, #ℓ)%V) ⌝.

  Definition both_mapto_diff (K₁ K₂ : context) (y a b : val) : iProp Σ :=
    (is_adj_var a ∗ mapsto_diff K₁ K₂ y a) ∗ (⌜ a ≠ b ⌝ -∗
    (is_adj_var b ∗ mapsto_diff K₁ K₂ y b)).

  Lemma mapsto_diff_update (K₁ K₂ : context) y x op a b u v (ℓ : loc) :
    u = InjRV (v, #ℓ)%V → x ≠ u → a ≠ u → b ≠ u →
      mapsto_diff (K₁ ++ [(x, (op, a, b))]) K₂ y u -∗
        mapsto_diff  K₁    ((x, (op, a, b)) :: K₂) y u.
  Proof using RA.
    set ϱ := (λ _ : val, r).{[a₀ := Oᵣ]}.{[a₁ := Iᵣ]}.
    iIntros (Hu Hux Hua Hub) "Hu".
    iDestruct ("Hu" with "[//]") as (d s) "(Hd & % & HH)".
    rename H into Hs.
    iIntros (v' ℓ' Hu').
    assert (v' = v ∧ ℓ' = ℓ) as [-> ->]; [naive_solver|].
    iExists d, s. iFrame. iPureIntro. fold ϱ.
    rewrite Hs diff_filling; [|done].
    rewrite (_ :
      ∂ (Node val op (Leaf val a) (Leaf val b)) ./ ∂ u .at _ =ᵣ Oᵣ).
    { rewrite (SRmul_comm is_semi_ring).
      rewrite (SRmul_0_l  is_semi_ring).
      rewrite (SRadd_comm is_semi_ring).
      rewrite (SRadd_0_l  is_semi_ring).
      rewrite extension_snoc //=; done.
    }
    { destruct op; try (do 2 (rewrite //= decide_False; [|done])).
      - rewrite (SRadd_0_l  is_semi_ring); done.
      - rewrite (SRmul_0_l  is_semi_ring).
        rewrite (SRmul_comm is_semi_ring).
        rewrite (SRmul_0_l  is_semi_ring).
        rewrite (SRadd_0_l  is_semi_ring); done.
    }
  Qed.

  (* Remark: the first assumptions could be suppressed,
             but in the actual proof they are easily met.
   *)
  Lemma backward_inv_update (K₁ K₂ : context) y x op a b :
    (∀ a, a ∈ (defs K₁ ++ [aₓ]) → ∃ v (ℓ : loc), a = InjRV (v, #ℓ)%V) →
      NoDup (defs K₁ ++ [aₓ]) →
        x ∉ defs K₁ ++ [aₓ] →
          a ∈ defs K₁ ++ adj_vars →
            b ∈ defs K₁ ++ adj_vars →
              backward_inv (K₁ ++ [(x, (op, a, b))]) K₂ y -∗
                (    mapsto_diff (K₁ ++ [(x, (op, a, b))])  K₂  y x  ) ∗
                (both_mapto_diff (K₁ ++ [(x, (op, a, b))])  K₂  y a b) ∗
                (both_mapto_diff  K₁    ((x, (op, a, b)) :: K₂) y a b -∗
                     backward_inv K₁    ((x, (op, a, b)) :: K₂) y).
  Proof using RA.
    set aₓ := aₓ.
    set ϱ := (λ _, r).{[a₀ := Oᵣ]}.{[a₁ := Iᵣ]}.
    intros Hdefs HND Hx Ha Hb. iIntros "[% HK₁]".
    rename H into Hdiff.
    fold aₓ ϱ in Hdiff. fold aₓ.
    rewrite defs_app defs_cons //=.
    rewrite (big_opL_permutation _ _ (x :: defs K₁ ++ [aₓ])); [|
    by rewrite -(Permutation_cons_append _ x)].
    iDestruct "HK₁" as "[Hx HK₁]".
    iDestruct "Hx" as (v ℓ) "[$ _]".
    (* TODO: cleanup. *)
    assert ((a ∈ defs K₁ ++ [aₓ] ∨ a = a₀ ∨ a = a₁) ∧
            (b ∈ defs K₁ ++ [aₓ] ∨ b = a₀ ∨ b = a₁)) as [Ha' Hb'].
    { revert Ha Hb.
      rewrite !elem_of_app !elem_of_cons; naive_solver.
    }
    destruct Ha' as [Ha'|Ha']; destruct Hb' as [Hb'|Hb'].
    { destruct (elem_of_list_lookup_1 _ _ Ha') as [i Hi].
      destruct (elem_of_list_lookup_1 _ _ Hb') as [j Hj].
      rewrite (big_sepL_delete' _ _ _ _ Hi).
      rewrite (big_sepL_delete' _ _ _ _ Hj).
      iDestruct "HK₁" as "(Ha & Hb & HK₁)".
      iSplitR "HK₁"; [iSplitL "Ha"|].
      - iDestruct "Ha" as (w ℓ') "[Hy ->]". iFrame.
        iPureIntro; right; naive_solver.
      - iIntros (Hab).
        iSpecialize ("Hb" with "[]"); [
        iPureIntro; naive_solver|].
        iDestruct "Hb" as (w ℓ') "[Hy ->]". iFrame.
        iPureIntro; right; naive_solver.
      - destruct (Hdefs _ Ha') as [av [ℓa Ha'']].
        destruct (Hdefs _ Hb') as [bv [ℓb Hb'']].
        iIntros "[[_ Ha] Hb]". iSplit; [iPureIntro;
        fold ϱ; by rewrite cons_middle app_assoc|].
        rewrite (big_sepL_delete' (λ _ _,     ∃ _, _)%I _ _ _ Hi).
        rewrite (big_sepL_delete' (λ _ _, _ → ∃ _, _)%I _ _ _ Hj).
        iSplitL "Ha"; [by iExists av, ℓa; iFrame|iSplitL "Hb"].
        + iIntros (Hij). iDestruct ("Hb" with "[]") as "[_ Hb]"; [
          iIntros (->); by destruct (NoDup_lookup _ _ _ _ HND Hi Hj)|].
          by iExists bv, ℓb; iFrame.
        + iApply (big_sepL_mono with "HK₁").
          iIntros (k u Hk) "Hu". iIntros (Hkj Hki).
          specialize (elem_of_list_lookup_2 _ _ _ Hk) as ?.
          iDestruct ("Hu" with "[//] [//]") as (w ℓ') "[Hu ->]".
          iExists w, ℓ'. iSplit; [|done].
          iApply (mapsto_diff_update with "Hu"); [done| | | ];
          intros ->; [done                             |
          by destruct (NoDup_lookup _ _ _ _ HND Hk Hi) |
          by destruct (NoDup_lookup _ _ _ _ HND Hk Hj) ].
    }
    { destruct (elem_of_list_lookup_1 _ _ Ha') as [i Hi].
      rewrite (big_sepL_delete' _ _ _ _ Hi).
      destruct (Hdefs _ Ha') as [av [ℓa Ha'']].
      iDestruct "HK₁" as "(Ha & HK₁)".
      iSplitR "HK₁"; [iSplitL "Ha"|].
      - iDestruct "Ha" as (w ℓ') "[Hy ->]". iFrame.
        iPureIntro; right; naive_solver.
      - iIntros (_). iSplit;[
        by iPureIntro; left; naive_solver |
        by iIntros (v' ℓ' Heq); inversion Heq; naive_solver].
      - iIntros "[[_ Ha] _]". iSplit; [iPureIntro;
        fold ϱ; by rewrite cons_middle app_assoc|].
        rewrite (big_sepL_delete' (λ _ _, ∃ _, _)%I _ _ _ Hi).
        iSplitL "Ha"; [by iExists av, ℓa; iFrame|].
        iApply (big_sepL_mono with "HK₁").
        iIntros (k u Hk) "Hu". iIntros (Hki).
        specialize (elem_of_list_lookup_2 _ _ _ Hk) as ?.
        iDestruct ("Hu" with "[//]") as (w ℓ') "[Hu ->]".
        iExists w, ℓ'. iSplit; [|done].
        iApply (mapsto_diff_update with "Hu"); [done| | | ];
        intros ->; [done                             |
        by destruct (NoDup_lookup _ _ _ _ HND Hk Hi) |
        naive_solver                                 ].
    }
    { destruct (elem_of_list_lookup_1 _ _ Hb') as [i Hi].
      rewrite (big_sepL_delete' _ _ _ _ Hi).
      destruct (Hdefs _ Hb') as [bv [ℓb Hb'']].
      iDestruct "HK₁" as "(Hb & HK₁)".
      iSplitR "HK₁"; [iSplitR "Hb"|].
      - iSplit;[
        by iPureIntro; left; naive_solver |
        by iIntros (v' ℓ' Heq); inversion Heq; naive_solver].
      - iDestruct "Hb" as (w ℓ') "[Hy ->]". iFrame.
        iPureIntro; right; naive_solver.
      - iIntros "[_ Hb]". iSplit; [iPureIntro;
        fold ϱ; by rewrite cons_middle app_assoc|].
        rewrite (big_sepL_delete' (λ _ _, ∃ _, _)%I _ _ _ Hi).
        iDestruct ("Hb" with "[]") as "[_ Hb]"; [naive_solver|].
        iSplitL "Hb"; [by iExists bv, ℓb; iFrame|].
        iApply (big_sepL_mono with "HK₁").
        iIntros (k u Hk) "Hu". iIntros (Hki).
        specialize (elem_of_list_lookup_2 _ _ _ Hk) as ?.
        iDestruct ("Hu" with "[//]") as (w ℓ') "[Hu ->]".
        iExists w, ℓ'. iSplit; [|done].
        iApply (mapsto_diff_update with "Hu"); [done| | | ];
        intros ->; [done                             |
        naive_solver                                 |
        by destruct (NoDup_lookup _ _ _ _ HND Hk Hi) ].
    }
    { iSplitR "HK₁".
      - iSplitL; [|iIntros "_"]; iSplit; try (
        by iIntros (v' ℓ' Heq); inversion Heq; naive_solver);
        iPureIntro; left; naive_solver.
      - iIntros "_". iSplitR "HK₁"; [
        fold ϱ; by rewrite cons_middle app_assoc|].
        iApply (big_sepL_mono with "HK₁").
        iIntros (k y' Hk). simpl.
        specialize (elem_of_list_lookup_2 _ _ _ Hk) as ?.
        iDestruct 1 as (w ℓ') "[Hy ->]".
        iExists w, ℓ'. iSplit; [|done].
        iApply (mapsto_diff_update with "Hy");
        [done|by intros ->| |];
        intros ->; naive_solver.
    }
  Qed.

End backward_invariant.

Section library_implementation_of_expressions.
  Context `{!cgraphG Σ, !heapG Σ}
           {R : Set} {RS : RingSig R}
           {N : Num} {Ψ : iEff Σ} {NSpec : NumSpec N Ψ RS}.

  Variables (γ  : gname)
            (ℓₓ : loc)
            (r  : R)
            (nᵣ : val).

  Notation a₀         := (InjLV (InjLV #()))%V.
  Notation a₁         := (InjLV (InjRV #()))%V.
  Notation aₓ         := (InjRV (nᵣ,   #ℓₓ))%V.
  Notation adj_vars   := ([a₀; a₁; aₓ])        (only parsing).
  Notation represents := (represents γ ℓₓ nᵣ)  (only parsing).

  (* If we give the predicate [represents] directly in the definition
     of [ExprNumSpec], then some unsolved goals remain. With this
     silly definition they don't.
   *)
  Definition implements_expr : val → Expr () → iProp Σ :=
    represents.

  Definition to_val : Binop → val :=
    λ op, match op with Add => InjLV #() | Mul => InjRV #() end.

  Definition args : Binop → val → val → val :=
    λ op a b, ((to_val op), (a, b)%V)%V.

  Definition AD : iEff Σ :=
    (>> (op : Binop) (a b : val) (el er : Expr ()) >>
       ! (args op a b) {{ represents a el ∗ represents b er }};
     << (x : val) <<
       ? (x)           {{ represents x (Node _ op el er)    }}).

  Lemma AD_agreement v Φ : protocol_agreement v AD Φ ≡
    (∃ (op : Binop) (a b : val) (el er : Expr ()),
      ⌜ v = args op a b ⌝                          ∗
      (represents a el ∗ represents b er)          ∗
      (∀ x, represents x (Node _ op el er) -∗ Φ x))%I.
  Proof.
    rewrite /AD (protocol_agreement_tele' [tele _ _ _ _ _] [tele _]). by auto.
  Qed.

  Definition perform (op : Binop) : val := λ: "a" "b",
    do: (to_val op, ("a", "b")).

  Lemma perform_spec E (op : Binop) (a b : val) (el er : Expr ()) :
    implements_expr a el -∗
      implements_expr b er -∗
        EWP (perform op) a b @ E <| AD |> {{ x,
          implements_expr x (Node _ op el er) }}.
  Proof.
    iIntros "Ha Hb".
    unfold perform. ewp_pure_steps.
    iApply ewp_eff.
    rewrite AD_agreement.
    iExists op, a, b, el, er.
    iFrame. iSplit; [done|].
    iIntros (x) "Hx". iNext.
    iApply ewp_value. iFrame.
  Qed.

  Corollary add_spec E (a b : val) (el er : Expr ()) :
    implements_expr a el -∗
      implements_expr b er -∗
        EWP add a b @ E <| AD |> {{ x,
          implements_expr x (el +ₑ er) }}.
  Proof. apply (perform_spec E Add). Qed.

  Corollary mul_spec E (a b : val) (el er : Expr ()) :
    implements_expr a el -∗
      implements_expr b er -∗
        EWP mul a b @ E <| AD |> {{ x,
          implements_expr x (el ×ₑ er) }}.
  Proof. apply (perform_spec E Mul). Qed.

  Lemma adj_var_0_spec : ⊢ implements_expr a₀ (Oₑ).
  Proof. by iPureIntro. Qed.

  Lemma adj_var_1_spec : ⊢ implements_expr a₁ (Iₑ).
  Proof. by iPureIntro. Qed.

  Program Instance ADNumSpec : NumSpec ADNum AD (ExprRing ()) := {
    implements := implements_expr;

    nzero_spec := adj_var_0_spec;
    none_spec  := adj_var_1_spec;

    nadd_spec  := add_spec;
    nmul_spec  := mul_spec;
  }.

End library_implementation_of_expressions.

Section proof_of_handle.
  Context `{!cgraphG Σ, !heapG Σ}
           {R : Set} {RS : RingSig R} {RA : IsRing R}
           {N : Num} {Ψ : iEff Σ} {NSpec : NumSpec N Ψ RS}.

  Variables (γ  : gname)
            (ℓₓ : loc)
            (r  : R)
            (nᵣ : val)
            (e : Expr ()). (* The expression implemented by the client. *)

  Notation a₀         := (InjLV (InjLV #()))%V.
  Notation a₁         := (InjLV (InjRV #()))%V.
  Notation aₓ         := (InjRV (nᵣ,   #ℓₓ))%V.

  Notation adj_vars        := ([a₀; a₁; aₓ])             (only parsing).
  Notation represents      := (represents   γ ℓₓ   nᵣ)   (only parsing).
  Notation AD              := (AD           γ ℓₓ   nᵣ)   (only parsing).
  Notation mapsto_diff     := (mapsto_diff       r)      (only parsing).
  Notation both_mapto_diff := (both_mapto_diff   r)      (only parsing).
  Notation forward_inv     := (forward_inv  γ ℓₓ r nᵣ)   (only parsing).
  Notation backward_inv    := (backward_inv   ℓₓ r nᵣ e) (only parsing).

  Lemma create_spec (v : val) :
    ⊢ EWP create v <| Ψ |> {{ w, ∃ (ℓ : loc),
        ⌜ w = InjRV (v, #ℓ)%V ⌝ ∗ ℓ ↦ nzero }}.
  Proof.
    unfold create. ewp_pure_steps. ewp_bind_rule.
    iApply ewp_mono'; [by iApply ewp_alloc|].
    iIntros (l) "Hl".
    iDestruct "Hl" as (ℓ) "[-> Hℓ]". iModIntro.
    simpl. ewp_pure_steps.
    by iExists ℓ; eauto.
  Qed.

  Lemma get_val_spec K u eᵤ :
    let ϱ := (λ _, r).{[a₀ := Oᵣ]}.{[a₁ := Iᵣ]} in
    forward_inv K -∗
      represents u eᵤ -∗
        EWP get_val u <| Ψ |> {{ v,
          forward_inv K            ∗
          implements v (ϱ.{[K]} u) }}.
  Proof.
    iIntros (?) "Hinv Hu".
    iDestruct (adj_var_0_not_in_defs with "Hinv") as %Ha₀.
    iDestruct (adj_var_1_not_in_defs with "Hinv") as %Ha₁.
    iDestruct (adj_var_cases with "Hinv Hu") as %Hcases.
    unfold get_val. ewp_pure_steps.
    destruct Hcases as [Hu|[Hu|Hu]]; try rewrite Hu.
    (* TODO: cleanup. *)
    { iDestruct "Hinv" as "(? & ? & Hheap)".
      destruct (elem_of_list_lookup_1 _ _ Hu) as [i Hi].
      rewrite (big_sepL_delete' _ _ _ _ Hi).
      iDestruct "Hheap" as "[Hu' Hheap]".
      iDestruct "Hu'" as (v ℓ) "(#? & ? & ->)".
      ewp_pure_steps. iFrame.
      rewrite (big_sepL_delete' (λ _ u, ∃ _ _, _)%I _ _ _ Hi).
      iFrame. fold ϱ. iSplit; [|done].
      iExists v, ℓ. iFrame. by auto.
    }
    { ewp_pure_steps. iFrame.
      rewrite extension_alt filling_undefined; [|done]. simpl.
      unfold ϱ.
      rewrite overwrite_neq; [|done].
      rewrite overwrite_eq.
      by iApply nzero_spec.
    }
    { ewp_pure_steps. iFrame.
      rewrite extension_alt filling_undefined; [|done]. simpl.
      unfold ϱ.
      rewrite overwrite_eq.
      by iApply none_spec.
    }
  Qed.

  Corollary get_diff_spec K₁ K₂ y x v (ℓ : loc) :
    let ϱ := (λ _, r).{[a₀ := Oᵣ]}.{[a₁ := Iᵣ]} in
    let ϑ := ϱ.{[K₁]} in
    x = InjRV (v, #ℓ)%V →
      mapsto_diff K₁ K₂ y x -∗
        EWP get_diff x <| Ψ |> {{ d,
          mapsto_diff K₁ K₂ y x ∗ ∃ (s : R),
          implements d s ∗
          ⌜ s =ᵣ ∂ (Let K₂ .in y) ./ ∂ x .at ϑ ⌝ }}.
  Proof.
    iIntros (?? Hx) "Hx".
    iDestruct ("Hx" $! v ℓ Hx) as (d s) "(#Hs & % & Hℓ)".
    rename H into Hs.
    unfold get_diff. ewp_pure_steps.
    rewrite_strat outermost Hx.
    ewp_pure_steps.
    iApply (ewp_mono' with "[Hℓ]"); [iApply (ewp_load with "Hℓ")|].
    iIntros (d') "[-> Hℓ]". iModIntro.
    iSplitL "Hℓ".
    { iIntros (v' ℓ' ->).
      inversion Hx. simplify_eq.
      iExists d, s. by auto.
    }
    { iExists s. unfold ϑ. by iSplit. }
  Qed.

  Lemma update_spec_crude x v (ℓ : loc) (d i : val) (s ds : R) :
    x = InjRV (v, #ℓ)%V →
      ℓ ↦ d -∗
        implements d  s -∗
          implements i ds -∗
            EWP update x i <| Ψ |> {{ _, ∃ d,
              ℓ ↦ d ∗ implements d (s +ᵣ ds) }}.
  Proof.
    iIntros (->) "Hℓ #Hd #Hi".
    unfold update.
    ewp_pure_steps.
    ewp_bind_rule.
    iApply (ewp_mono' with "[Hℓ]"); [iApply (ewp_load with "Hℓ")|].
    iIntros (w) "[-> Hℓ]". iModIntro. simpl.
    iApply (Ectxi_ewp_bind (StoreRCtx _)). done.
    iApply ewp_mono'; [iApply (nadd_spec with "Hd Hi")|].
    iIntros (w) "Hw". iModIntro.
    iApply (ewp_mono' with "[Hℓ]"); [iApply (ewp_store with "Hℓ")|].
    iIntros (u) "Hℓ". iModIntro. by eauto.
  Qed.

  Lemma update_constant_spec (x w i : val) :
    x = InjLV w →
      ⊢ EWP update x i <| Ψ |> {{ _, True }}.
  Proof. intros ->. unfold update. by ewp_pure_steps. Qed.

  (* This lemma will be useful in the verification of the return branch. *)
  Lemma trigger_backward_phase K y s :
    e =ₑ s →
      forward_inv K -∗
        represents y s -∗
          EWP update y none <| Ψ |> {{_,
            backward_inv K [] y }}.
  Proof using RA.
    iIntros (He) "Hinv Hy".
    iDestruct (diff_output               with "Hinv Hy") as %Hs.
    iDestruct (adj_var_cases             with "Hinv Hy") as %Hcases.
    iDestruct (NoDup_defs_app_adj_vars   with "Hinv")    as %HND.
    iDestruct (elem_of_defs_inv'         with "Hinv")    as %Hdefs.
    iDestruct "Hinv" as "(_ & _ & Hheap)". iClear "Hy".
    destruct Hcases as [Hin|Hy].
    { specialize (elem_of_list_lookup_1 _ _ Hin) as [i Hi].
      rewrite (big_sepL_delete' _ _ _ _ Hi).
      iDestruct "Hheap" as       "[Hy Hheap]".
      iDestruct "Hy"    as (v ℓ) "(_ & Hℓ & ->)".
      iApply (ewp_mono' with "[Hℓ]"); [
      iApply (update_spec_crude with "Hℓ"); [done|
        iApply nzero_spec |
        iApply none_spec  ]|].
      iIntros (_). iDestruct 1 as (d) "[Hℓ #Hd]".
      iModIntro. iSplit; [iPureIntro;
      by rewrite (diff_equiv e s); [
      rewrite app_nil_r Hs|apply He]|].
      rewrite (big_sepL_delete' (λ _ u, ∃ _, _)%I _ _ _ Hi).
      iSplitL "Hℓ".
      { iExists v, ℓ. iSplit; [|done].
        iIntros (v' ℓ' ?). simplify_eq.
        iExists d, (Oᵣ +ᵣ Iᵣ). iFrame. iSplit; [done|].
        iPureIntro. rewrite //= decide_True; [|done].
        rewrite (SRadd_0_l is_semi_ring); done.
      }
      { iApply (big_sepL_mono with "Hheap").
        intros k x Hk. clear d.
        iIntros "Hx %".
        iDestruct ("Hx" with "[//]") as (v' ℓ') "[_ [Hx ->]]".
        iExists v', ℓ'. iSplit; [|done].
        iIntros (w ℓ'' ?). simplify_eq.
        iExists nzero, (Oᵣ). iFrame.
        iSplit; [iApply nzero_spec|]. simpl.
        rewrite decide_False; [done|].
        intros [=-> ->]. by destruct (NoDup_lookup _ _ _ _ HND Hi Hk).
      }
    }
    { iApply ewp_mono'; [
      by destruct Hy as [|]; iApply update_constant_spec|].
      iIntros (v) "_". iModIntro.
      iSplit; [iPureIntro;
      by rewrite (diff_equiv e s); [
      rewrite app_nil_r Hs|apply He]|].
      iApply (big_sepL_mono with "Hheap").
      intros k x Hk.
      iIntros "Hx".
      iDestruct "Hx" as (v' ℓ') "[_ [Hx ->]]".
      iExists v', ℓ'. iSplit; [|done].
      iIntros (w ℓ'' ?). simplify_eq.
      iExists nzero, (Oᵣ). iFrame.
      iSplit; [iApply nzero_spec|]. simpl.
      rewrite decide_False; [done|].
      by destruct Hy as [Hy|Hy]; rewrite Hy.
    }
  Qed.

  Section update_twice_spec.

    Add Ring LocalRing : is_semi_ring.  

    Lemma update_twice_spec K₁ K₂ y x (op : Binop) a b ia ib da db :
      let ϱ := (λ _, r).{[a₀ := Oᵣ]}.{[a₁ := Iᵣ]} in
      let ϑ := ϱ.{[K₁ ++ [(x, (op, a, b))]]} in
      x ≠ a → x ≠ b →
        da =ᵣ (if op then               (∂ (Let K₂ .in y) ./ ∂ x .at ϑ)
                     else ϱ.{[K₁]} b ×ᵣ (∂ (Let K₂ .in y) ./ ∂ x .at ϑ)) →
        db =ᵣ (if op then               (∂ (Let K₂ .in y) ./ ∂ x .at ϑ)
                     else ϱ.{[K₁]} a ×ᵣ (∂ (Let K₂ .in y) ./ ∂ x .at ϑ)) →
          implements ia da -∗
            implements ib db -∗
              both_mapto_diff (K₁ ++ [(x, (op, a, b))]) K₂ y a b -∗
                EWP update a ia;;
                    update b ib  <| Ψ |> {{ _,
                  both_mapto_diff K₁ ((x, (op, a, b)) :: K₂) y a b }}.
    Proof using RA.
      intros ?? Hxa Hxb Hda Hdb.
      iIntros "#Hia #Hib". iDestruct 1 as "[[% Ha] Hb]".
      rename H into Ha.
      iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
      case Ha as [[w Ha]|[v [ℓ Ha]]].
      { iApply ewp_mono'; [
        iApply update_constant_spec|]; [done|].
        iIntros (v') "_". iModIntro. simpl.
        iApply (Ectxi_ewp_bind (AppLCtx _)); [done|].
        iApply ewp_pure_step; [apply pure_prim_step_rec |].
        iApply ewp_value. simpl.
        iApply ewp_pure_step; [apply pure_prim_step_beta|]. simpl.
        case (decide (a = b)) as [<-|Hab].
        { iApply ewp_mono'; [
          iApply update_constant_spec|]; [done|].
          iIntros (_) "_". iModIntro.
          iSplitL; [|iIntros "_"];
          try (iSplitL; [iPureIntro; naive_solver|]);
          by iIntros (w' ℓ' ?); simplify_eq.
        }
        { iDestruct ("Hb" with "[//]") as "[% Hb]".
          rename H into Hb. clear v'.
          case Hb as [[w' Hb]|[v' [ℓ' Hb]]].
          { iApply ewp_mono'; [
            iApply update_constant_spec|]; [done|].
            iIntros (_) "_". iModIntro.
            iSplitL; [|iIntros "_"];
            try (iSplitL; [iPureIntro; naive_solver|]);
            by iIntros (w'' ℓ'' ?); simplify_eq.
          }
          { iDestruct ("Hb" with "[//]") as (d s) "(#Hd & % & Hℓ')".
            rename H into Hs. iClear "Ha".
            iApply (ewp_mono' with "[Hℓ']"); [
            by iApply (update_spec_crude with "Hℓ' Hd Hib")|].
            iIntros (_). iClear "Hd". clear d.
            iDestruct 1 as (d) "[Hℓ' #Hd]". iModIntro.
            iSplitR; [|iIntros "_"];
            try (iSplit; [iPureIntro; naive_solver|]);
            iIntros (???); [by simplify_eq|].
            iExists d, (s +ᵣ db). iSplit; [done|].
            iSplitR "Hℓ'";[|by simplify_eq].
            iPureIntro.
            rewrite Hs Hdb. fold ϱ. unfold ϑ.
            rewrite diff_filling; [|done].
            rewrite extension_snoc //=.
            destruct op; try (
              rewrite decide_False; [|done];
              rewrite decide_True;  [|done]);
            ring.
          }
        }
      }
      { iDestruct ("Ha" with "[//]") as (d s) "(#Hd & % & Hℓ)".
        rename H into Hs.
        iApply (ewp_mono' with "[Hℓ]"); [
        by iApply (update_spec_crude with "Hℓ Hd Hia")|].
        iIntros (w). iClear "Hd". clear d.
        iDestruct 1 as (d) "[Hℓ #Hd]". iModIntro. simpl.
        iApply (Ectxi_ewp_bind (AppLCtx _)); [done|].
        iApply ewp_pure_step; [apply pure_prim_step_rec |].
        iApply ewp_value.
        iApply ewp_pure_step; [apply pure_prim_step_beta|]. simpl.
        clear w.
        case (decide (a = b)) as [<-|Hab].
        { iApply (ewp_mono' with "[Hℓ]"); [
          by iApply (update_spec_crude with "Hℓ Hd Hib")|].
          iIntros (w). iClear "Hd". clear d.
          iDestruct 1 as (d) "[Hℓ #Hd]". iModIntro. simpl.
          iSplitL; [|by iIntros (?)].
          iSplit; [iPureIntro; naive_solver|].
          iIntros (v' ℓ' ?).
          assert (v' = v) as ->. { by simplify_eq. }
          assert (ℓ' = ℓ) as ->. { by simplify_eq. }
          iExists d, ((s +ᵣ da) +ᵣ db).
          iSplit; [done|]. iFrame. iPureIntro.
          rewrite Hs Hda Hdb. fold ϱ. unfold ϑ.
          rewrite diff_filling; [|done].
          rewrite extension_snoc //=.
          by destruct op; repeat (rewrite decide_True; [|done]); ring.
        }
        { iDestruct ("Hb" with "[//]") as "[% Hb]". rename H into Hb.
          case Hb as [[w' Hb]|[v' [ℓ' Hb]]].
          { iApply ewp_mono'; [by iApply update_constant_spec|].
            iIntros (_) "_". iModIntro.
            iSplitL "Hℓ"; [|iIntros "_"];
            try (iSplit; [iPureIntro; naive_solver|]);
            iIntros (w l ?); [|by simplify_eq].
            assert (w = v) as ->. { by simplify_eq. }
            assert (l = ℓ) as ->. { by simplify_eq. }
            iExists d, (s +ᵣ da). iSplit; [done|].
            iSplitR "Hℓ";[|by simplify_eq].
            iPureIntro.
            rewrite Hs Hda. fold ϱ. unfold ϑ.
            rewrite diff_filling; [|done].
            rewrite extension_snoc //=.
            destruct op; try (
              rewrite decide_True;  [|done];
              rewrite decide_False; [|done]);
            ring.
          }
          { iDestruct ("Hb" with "[//]") as (d' s') "(#Hd' & % & Hℓ')".
            rename H into Hs'.
            iApply (ewp_mono' with "[Hℓ']"); [
            by iApply (update_spec_crude with "Hℓ' Hd' Hib")|].
            iIntros (w). iClear "Hd'". clear d'.
            iDestruct 1 as (d') "[Hℓ' #Hd']". iModIntro.
            iSplitL "Hℓ"; [|iIntros "_"]; iSplit;
            try (iPureIntro; naive_solver);
            iIntros (???); simplify_eq; [
            iExists d , (s  +ᵣ da)| iExists d', (s' +ᵣ db)];
            iFrame; try (iSplit; [done|]); iPureIntro; [
            rewrite Hs  Hda| rewrite Hs' Hdb]; fold ϱ; unfold ϑ;
            try (rewrite diff_filling; [|done]);
            rewrite extension_snoc //=.
            - destruct op; try (
                rewrite decide_True;  [|done];
                rewrite decide_False; [|done]);
              ring.
            - destruct op; try (
                rewrite decide_False; [|done];
                rewrite decide_True;  [|done]);
              ring.
          }
        }
      }
    Qed.

  End update_twice_spec.

  Lemma handle_spec K₁ (f : val) :
    EWP f aₓ <| AD |> {{ y, ∃ s, represents y s ∗ ⌜ e =ₑ s ⌝ }} -∗
      forward_inv K₁ -∗
        EWP handle f aₓ <| Ψ |> {{_, ∃ K₂ y,
          backward_inv K₁ K₂ y }}.
  Proof using RA.
    set ϱ := (λ _, r).{[a₀ := Oᵣ]}.{[a₁ := Iᵣ]}.
    iIntros "Hf Hinv".
    unfold handle.
    do 8 (ewp_bind_rule; ewp_pure_step; try iNext; simpl).
    iApply (ewp_deep_try_with with "Hf").

    iLöb as "IH" forall (K₁).
    rewrite deep_handler_unfold. iSplit.

    (* Return branch. *)
    { iClear "IH". iIntros (y) "#Hy". iNext.
      iDestruct "Hy" as (s) "[Hs %]". rename H into He.
      ewp_pure_steps.
      iApply (ewp_mono' with "[Hinv]"); [
      by iApply (trigger_backward_phase with "Hinv Hs")|].
      by eauto.
    }

    (* Effect branch. *)
    { iIntros (args k) "Hprot". iNext.
      ewp_pure_steps.
      rewrite AD_agreement.
      iDestruct "Hprot" as (op a b el er) "(-> & [#Ha #Hb] & Hk)".
      unfold args.
      ewp_pure_steps.
      iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
      iApply (ewp_mono' with "[Hinv]"); [
      iApply (get_val_spec with "Hinv Ha")|]. fold ϱ.
      iIntros (av) "[Hinv #Hav]". iModIntro. simpl.
      ewp_pure_steps.
      iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
      iApply (ewp_mono' with "[Hinv]"); [
      iApply (get_val_spec with "Hinv Hb")|]. fold ϱ.
      iIntros (bv) "[Hinv #Hbv]". iModIntro. simpl.
      ewp_pure_steps.
      iDestruct   (NoDup_defs_app_adj_vars with "Hinv"   ) as %HND.
      iDestruct (elem_of_defs_app_adj_vars with "Hinv Ha") as %Ha.
      iDestruct (elem_of_defs_app_adj_vars with "Hinv Hb") as %Hb.
      iDestruct (elem_of_defs_inv'         with "Hinv")    as %Hdefs.
      destruct op.

      (* Add. *)
      { ewp_pure_steps.
        iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
        iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
        iApply ewp_mono'; [
        iApply (nadd_spec with "Hav Hbv")|].
        iIntros (xv) "#Hxv". iModIntro. simpl.
        iApply ewp_mono'; [iApply create_spec|].
        iIntros (x'). iDestruct 1 as (x) "[-> Hx]".
        iDestruct (forward_inv_fresh_loc with "Hx Hinv") as %Hx.
        iMod ((forward_inv_update _ _ _ _ _ _ Add)
          with "Hinv Ha Hb [] Hx") as "[Hinv #Hx']"; [done| |].
        { fold ϱ. rewrite extension_snoc //= overwrite_eq. by iApply "Hxv". }
        iModIntro.
        ewp_pure_steps.

        (* Continuation call. *)
        ewp_bind_rule.
        iApply (ewp_mono' with "[Hinv Hk]").
        { iApply ("Hk" with "Hx'"). by iApply ("IH" with "Hinv"). }
        iClear "IH Hx' Ha Hb Hav Hbv Hxv".

        iIntros (w). iDestruct 1 as (K₂ y) "Hinv".
        iModIntro. simpl.
        ewp_pure_steps.
        iDestruct (backward_inv_update with "Hinv")
          as "(Hx & Hab & Hfinisher)"; try done.
        iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
        iApply (ewp_mono' with "[Hx]"); [
        by iApply (get_diff_spec with "Hx")|].
        iIntros (xd) "[_ Hxd]". fold ϱ.
        iDestruct "Hxd" as (s) "[#Hxd %]". rename H into Hs.
        iModIntro. simpl.
        ewp_pure_steps.
        iApply (ewp_mono' with "[Hab]");[
        iApply (update_twice_spec K₁ K₂ y _ Add with "Hxd Hxd Hab");
        try done; set_solver|].
        iIntros (_) "Hinv !>".
        iExists ((_, (Add, a ,b)) :: K₂), y.
        by iApply "Hfinisher".
      }

      (* Mul. *)
      { ewp_pure_steps.
        iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
        iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
        iApply ewp_mono'; [
        iApply (nmul_spec with "Hav Hbv")|].
        iIntros (xv) "#Hxv". iModIntro. simpl.
        iApply ewp_mono'; [iApply create_spec|].
        iIntros (x'). iDestruct 1 as (x) "[-> Hx]".
        iDestruct (forward_inv_fresh_loc with "Hx Hinv") as %Hx.
        iMod ((forward_inv_update _ _ _ _ _ _ Mul)
          with "Hinv Ha Hb [] Hx") as "[Hinv #Hx']"; [done| |].
        { fold ϱ. rewrite extension_snoc //= overwrite_eq. by iApply "Hxv". }
        iModIntro. ewp_pure_steps.
    
        (* Continuation call. *)
        ewp_bind_rule.
        iApply (ewp_mono' with "[Hinv Hk]").
        { iApply ("Hk" with "Hx'"). by iApply ("IH" with "Hinv"). }
        iClear "IH Hx' Ha Hb Hxv".

        iIntros (w). iDestruct 1 as (K₂ y) "Hinv".
        iModIntro. simpl.
        ewp_pure_steps. ewp_bind_rule.
        iDestruct (backward_inv_update with "Hinv")
          as "(Hx & Hab & Hfinisher)"; try done.
        iApply (ewp_mono' with "[Hx]"); [
        by iApply (get_diff_spec with "Hx")|].
        iIntros (xd) "[_ Hxd]". fold ϱ.
        iDestruct "Hxd" as (s) "[#Hxd %]". rename H into Hs.
        iModIntro. simpl.
        ewp_pure_steps.
        iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
        iApply ewp_mono'; [iApply (nmul_spec with "Hbv Hxd")|].
        iIntros (ad) "#Had". iModIntro. simpl.
        ewp_pure_steps.
        iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
        iApply ewp_mono'; [iApply (nmul_spec with "Hav Hxd")|].
        iIntros (bd) "#Hbd". iModIntro. simpl.
        ewp_pure_steps.
        iApply (ewp_mono' with "[Hab]"); [
        iApply (update_twice_spec K₁ K₂ y _ Mul with "Had Hbd Hab");
        try (fold ϱ; by rewrite Hs); set_solver|].
        iIntros (_) "Hinv !>".
        iExists ((_, (Mul, a ,b)) :: K₂), y.
        by iApply "Hfinisher".
      }
    }
  Qed.

End proof_of_handle.

Section proof_of_diff.
  Context `{R₁: !cgraphG Σ, R₂: !heapG Σ}.

  Theorem diff_correct : ⊢ diff_spec.
  Proof using R₁ R₂.
    iIntros (f e) "Hclient".
    iIntros (N).
    unfold diff.
    iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
    iSpecialize ("Hclient" $! ADNum).
    iApply (ewp_mono' with "Hclient").
    iIntros (vf) "Hvf". iModIntro. simpl.
    ewp_pure_steps.
    iIntros (R RS RA Ψ NSpec x r) "Hx".
    ewp_pure_steps.
    iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
    iApply ewp_mono'; [iApply create_spec|].
    iIntros (ℓₓ') "Hℓₓ !>".
    iDestruct "Hℓₓ" as (ℓₓ) "[-> Hℓₓ]". simpl.
    ewp_pure_steps.
    iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
    iApply fupd_ewp.
    iMod (forward_inv_alloc with "Hx Hℓₓ") as (γ) "Hinv".
    iModIntro.
    set Ψ_client := AD γ ℓₓ x.
    set NSpec_client := ADNumSpec γ ℓₓ x.
    set aₓ := InjRV (x, #ℓₓ)%V.
    iSpecialize ("Hvf" $! (Expr ()) (ExprRing ()) ExprIsRing).
    iSpecialize ("Hvf" $! Ψ_client NSpec_client aₓ (Xₑ) with "[//]").
    iApply (ewp_mono' with "[Hinv Hvf]").
    { iApply (handle_spec with "[Hvf] Hinv").
      iApply (ewp_mono' with "Hvf"). iIntros (y).
      iDestruct 1 as (s) "[Hs %]". rename H into He.
      iModIntro. iExists s. iFrame. iPureIntro.
      symmetry. by apply He.
    }
    iIntros (w).
    iDestruct 1 as (K y) "Hinv". iModIntro. simpl.
    iDestruct "Hinv" as "[% Hheap]". rename H into Hdiff_output.
    iDestruct "Hheap" as "(_ & Hx & _)".
    iDestruct "Hx" as (v ℓ) "[Hx %]". simplify_eq. fold aₓ.
    ewp_pure_steps.
    iApply (ewp_mono' with "[Hx]");[
    by iApply (get_diff_spec with "Hx")|].
    iIntros (d). iIntros "[_ Hd] !>". 
    iDestruct "Hd" as (s) "[Hs %]".
    iExists s. iFrame. iPureIntro.
    rewrite eval_univariate_expr in Hdiff_output.
    rewrite diff_univariate_expr.
    by rewrite Hdiff_output.
  Qed.

End proof_of_diff.

End verification.


(** * Clients. *)

(** We have proved that [diff] satisfies a given specification.
    Now, we implement some clients of [diff] to see what kind of
    results we can derive from that.
*)

Section clients.

  (* First, we provide a concrete implementation of integers. (Integers are
     unbounded in our calculus.) This will unlock the derivation functionality
     where arithmetical operators are interpreted as the standard addition and
     multiplication on integers.
   *)

  Section ring_of_integers.
    Context `{!irisGS eff_lang Σ}.

    Program Instance ZNum : Num := {
      nzero := #0%Z;
      none  := #1%Z;
      nadd  := (λ: "a" "b", "a" + "b")%V;
      nmul  := (λ: "a" "b", "a" * "b")%V;
    }.

    Program Instance ZNumSpec : NumSpec ZNum ⊥%ieff ZRing := {
      implements := λ v n, ⌜ v = #n ⌝%I;
    }.
    (* Implements Oᵣ. *)
    Next Obligation. auto. Qed.
    (* Implements Iᵣ. *)
    Next Obligation. auto. Qed.
    (* Implements +ᵣ. *)
    Next Obligation. iIntros (E a b r s) "-> ->". by ewp_pure_steps. Qed.
    (* Implements ×ᵣ. *)
    Next Obligation. iIntros (E a b r s) "-> ->". by ewp_pure_steps. Qed.


  End ring_of_integers.

  Section x_cube.
    Context `{R₁: !cgraphG Σ, R₂: !heapG Σ}.

    Definition x_cube (N : Num) : val := λ: "x",
      nmul "x" (nmul "x" "x").

    Lemma x_cube_spec :
      ⊢ isExp (@x_cube) (Xₑ ×ₑ (Xₑ ×ₑ Xₑ)).
    Proof.
      iIntros (?). iApply ewp_value.
      iIntros (?? ??? ??) "#Hx". unfold x_cube. ewp_pure_steps.
      iApply (Ectxi_ewp_bind (AppRCtx _)); [done|].
      iApply ewp_mono'; [iApply (nmul_spec with "Hx Hx")|].
      iIntros (y) "#Hy". iModIntro. simpl.
      iApply ewp_mono'; [iApply (nmul_spec with "Hx Hy")|].
      iIntros (z) "Hz". iModIntro.
      iExists (r ×ᵣ (r ×ᵣ r)). by iFrame.
    Qed.

    Lemma x_cube'_spec :
      ⊢ isExp (diff x_cube)
          (∂ (Xₑ ×ₑ (Xₑ ×ₑ Xₑ)) ./ ∂ tt .at (λ _, Xₑ)).
    Proof using R₁ R₂.
      iPoseProof (diff_correct $! (@x_cube) (Xₑ ×ₑ (Xₑ ×ₑ Xₑ))) as "Hdiff".
      iApply "Hdiff". by iApply x_cube_spec.
    Qed.

    Lemma x_cube''_spec :
      ⊢ isExp
          (diff (diff x_cube))
          (∂ (∂ (Xₑ ×ₑ (Xₑ ×ₑ Xₑ)) ./ ∂ tt .at (λ _, Xₑ)) ./ ∂ tt .at (λ _, Xₑ)).
    Proof using R₁ R₂.
      iPoseProof (diff_correct $! _
        (∂ (Xₑ ×ₑ (Xₑ ×ₑ Xₑ)) ./ ∂ tt .at (λ _, Xₑ)))
      as "Hdiff".
      iApply "Hdiff". by iApply x_cube'_spec.
    Qed.

    Lemma x_cube'_int_spec (n : Z) :
      ⊢ EWP (diff (x_cube)) ZNum #n {{ y, ⌜ y = #(3 * (n * n))%Z ⌝ }}.
    Proof using R₁ R₂.
      iPoseProof (x_cube'_spec $! ZNum) as "Hdiff".
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply (ewp_mono' with "Hdiff").
      iClear "Hdiff".
      iIntros (vdiff) "Hdiff".
      iSpecialize ("Hdiff" $!
        Z ZRing ZIsRing ⊥%ieff ZNumSpec #n%Z n with "[//]").
      iApply (ewp_mono' with "Hdiff"). iModIntro.
      iIntros (v). iDestruct 1 as (s) "[-> ->]". iPureIntro. simpl. f_equal.
      rewrite (_: (∀ (n : Z), 3 * n = n + n + n)%Z); [|lia].
      by rewrite !Z.mul_1_l Z.mul_1_r Z.mul_add_distr_l Z.add_assoc.
    Qed.

    Lemma x_cube''_int_spec (n : Z) :
      ⊢ EWP (diff (diff (x_cube))) ZNum #n {{ y, ⌜ y = #(6 * n)%Z ⌝ }}.
    Proof using R₁ R₂.
      iPoseProof (x_cube''_spec $! ZNum) as "Hdiff".
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply (ewp_mono' with "Hdiff").
      iClear "Hdiff". iIntros (vdiff) "Hdiff".
      iSpecialize ("Hdiff" $!
        Z ZRing ZIsRing ⊥%ieff ZNumSpec #n%Z n with "[//]").
      iApply (ewp_mono' with "Hdiff"). iModIntro.
      iIntros (v). iDestruct 1 as (s) "[-> ->]". iPureIntro. simpl. f_equal.
      rewrite !Z.mul_1_l Z.mul_add_distr_l //=.
      rewrite !Z.mul_0_l !Z.mul_0_r !Z.add_0_l !Z.add_0_r !Z.mul_1_r //=.
      rewrite (_: (∀ (n : Z), 6 * n = n + n + n + n + n + n)%Z); [|lia].
      by rewrite !Z.add_assoc.
    Qed.

  End x_cube.

End clients.


(** * Implementation in HH. *)

(** An attentive reader might have noticed that the algorithm we verified
    in the previous sections was not entirely written in [HH]. Indeed,
    the function [diff] is a Coq function of two arguments. One of its
    arguments, for example, is a record of type [Num], which is used in
    the definition of [diff] as the provider of arithmetical operations and
    constants. This diverges from the actual code that we would write in [HH]
    or in another programming language, because that is not how these numerical
    operations would be accessed. A program that takes such record as one of
    its arguments would have to deconstruct it and bind its components using
    binders of the language itself, not meta-level ones.

    Writing the code with constructors and deconstrutors for these record
    values would make it harder to decompose the implementation of [diff]
    as separate functions -- [handle], [update], [create] -- which would
    consequently complicate the Coq proofs. Nevertheless, in the following
    section, we show that our effort from previous sections was not in vain:
    we can reuse what was proven for [diff] in verifying a full [HH]
    implementation of automatic differentiation.
*)

Section hh_implementation.
  Context `{R₁: !cgraphG Σ, R₂: !heapG Σ}.

  Definition to_struct (N : Num) : val :=
    (nzero, (none, (nadd, nmul)))%V.

  Definition to_Num (zero one add mul : val) : Num :=
    {| nzero := zero; none := one; nadd := add; nmul := mul |}.

  Definition hh_diff : val := λ: "f" "num",
    let: "nzero" := Fst "num" in
    let: "none"  := Fst (Snd "num") in
    let: "nadd"  := Fst (Snd (Snd "num")) in
    let: "nmul"  := Snd (Snd (Snd "num")) in

    let: "create" := λ: "n", InjR ("n", ref "nzero") in

    let: "get_val" := λ: "x",
      match: "x" with
        (* Constant. *) InjL "x" =>
         match: "x" with
           (* Zero. *) InjL <> => "nzero"
         | (* One.  *) InjR <> => "none"
         end
      | (* Variable. *) InjR "x" => Fst "x"
      end
    in

    let: "update" := λ: "x" "incr",
      match: "x" with
        (* Constant. *) InjL <>  => #()
      | (* Variable. *) InjR "x" =>
        let: "xd" := Snd "x" in
        "xd" <- "nadd" (Load "xd") "incr"
      end
    in

    let: "handle" := λ: "f" "seed",
      try: "f" "seed" with
        effect (λ: "args" "k",
          let: "op" := Fst      "args"  in
          let: "a"  := Fst (Snd "args") in
          let: "b"  := Snd (Snd "args") in

          let: "av" := "get_val" "a"      in
          let: "bv" := "get_val" "b"      in

          match: "op" with
            (* Add *) InjL <> =>
             let: "x" := "create" ("nadd" "av" "bv") in
             "k" "x";;
             let: "xd" := get_diff "x" in
             "update" "a" "xd";;
             "update" "b" "xd"

          | (* Mul *) InjR <> =>
             let: "x" := "create" ("nmul" "av" "bv") in
             "k" "x";;
             let: "xd" := get_diff "x"   in
             let: "ad" := "nmul" "bv" "xd" in
             let: "bd" := "nmul" "av" "xd" in
             "update" "a" "ad";;
             "update" "b" "bd"
          end
        )
      | return (λ: "res",
             "update" "res" "none")
      end
    in

    let: "vf" := "f" (to_struct ADNum) in
    λ: "a",
      let: "x" := "create" "a" in
      "handle" "vf" "x";;
      get_diff "x".

  (* The class [NumSpec N Ψ RS] can be seen as the domain of predicates
     [implements : val → R → iProp Σ] for which the assertions [nzero_spec],
     [none_spec], [nadd_spec], [nmul_spec] and [implements_pers] hold.

     In the following, we detach the type of predicates, [val → R → iProp Σ],
     from its restrictions, which will be bundled into the new typeclass [numSpec].

     This allows the specification of [hh_diff] to quantify directly over
     predicates, instead of terms of type [NumSpec N Ψ RS]. We believe this
     leads to a more readable definition of [IsExp].
   *)

  Class numSpec {R : Set}
    (zero one add mul : val)
    (implements : val → R → iProp Σ)
    (Ψ : iEff Σ)
    (RS : RingSig R) :=
  {
    nzero_spec' : ⊢ implements zero (Oᵣ);
    none_spec'  : ⊢ implements one  (Iᵣ);

    nadd_spec' E a b r s :
      implements a r -∗
        implements b s -∗
          EWP add a b @ E <| Ψ |> {{ x,
            implements x (radd r s) }};

    nmul_spec' E a b r s :
      implements a r -∗
        implements b s -∗
          EWP mul a b @ E <| Ψ |> {{ x,
            implements x (rmul r s) }};

    implements_pers' u r :> Persistent (implements u r);
  }.

  Program Instance NumSpec' {R : Set} (RS : RingSig R)
    (zero one add mul : val)
    (implements : val → R → iProp Σ)
    (Ψ : iEff Σ)
    (nSpec : numSpec zero one add mul implements Ψ RS) :
    NumSpec (to_Num zero one add mul) Ψ RS :=
  {|
    implements := implements;
    nzero_spec := nzero_spec';
    none_spec  := none_spec';
    nadd_spec  := nadd_spec';
    nmul_spec  := nmul_spec';
    implements_pers := implements_pers'
  |}.

  Program Instance numSpec'  {R : Set}
    (RS : RingSig R) (N : Num) (Ψ : iEff Σ)
    (NSpec : NumSpec N Ψ RS) :
    numSpec nzero none nadd nmul implements Ψ RS :=
  {|
    nzero_spec' := nzero_spec;
    none_spec'  := none_spec;
    nadd_spec'  := nadd_spec;
    nmul_spec'  := nmul_spec;
    implements_pers' := implements_pers
  |}.

  Definition IsExp (e : val) (E : Expr ()) : iProp Σ :=
    ∀ (zero one add mul : val),
      EWP (e (zero, (one, (add, mul)))%V) {{ f,
        ∀ (R : Set) (RS : RingSig R) (RA : IsRing R) (Ψ : iEff Σ),
          ∀ (implements : val → R → iProp Σ),
            ⌜ numSpec zero one add mul implements Ψ RS ⌝ -∗
              ∀ (x : val) (r : R),
                implements x r -∗
                  EWP (f x) <| Ψ |> {{ y, ∃ s,
                    implements y s ∗
                      ⌜ s =ᵣ eval (map (λ _, r) E) ⌝ }} }}.

  Definition hh_diff_spec : Prop :=
    ⊢ ∀ (e : val) (E : Expr ()),
        IsExp e E -∗
          EWP hh_diff e {{ e',
            IsExp e' (∂ E ./ ∂ tt .at (λ _, Xₑ)) }}.

  Theorem hh_diff_correct : hh_diff_spec.
  Proof using R₁ R₂ Σ.
    iIntros (e E) "He".
    unfold hh_diff. ewp_pure_steps.
    iIntros (zero one add mul). ewp_pure_steps.
    iPoseProof (diff_correct) as "Hdiff".
    iSpecialize ("Hdiff" $! (λ N, e (to_struct N)) E).
    iSpecialize ("Hdiff" with "[He]").
    { iIntros (N). destruct N as [nzero none nadd nmul].
      rewrite /to_struct //=.
      iSpecialize ("He" $! nzero none nadd nmul).
      iApply (ewp_mono with "He").
      iIntros (f) "Hf". simpl. iModIntro.
      iIntros (R RS RA Ψ NSpec).
      set N := to_Num nzero none nadd nmul.
      by iApply ("Hf" $! R RS RA Ψ implements
        (numSpec' RS N Ψ NSpec)).
    }
    set N := to_Num zero one add mul.
    iSpecialize ("Hdiff" $! N).
    iApply (ewp_mono with "Hdiff").
    iIntros (f) "Hf". simpl. iModIntro.
    iIntros (R RS RA Ψ implements) "%".
    iSpecialize ("Hf" $! R RS RA Ψ).
    iSpecialize ("Hf" $!
      (NumSpec' RS zero one add mul implements Ψ H)).
    iIntros (x X) "Hx".
    iSpecialize ("Hf" $! x X with "Hx").
    iApply (ewp_mono with "Hf"). simpl.
    by iIntros (y) "Hy".
  Qed.

End hh_implementation.
