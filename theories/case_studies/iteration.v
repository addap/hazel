(* iteration.v *)

(* This theory introduces the building blocks to specify iteration in terms of
   [EWP]. It introduces general concepts such as the notion of a data structure,
   which is formalized as a Coq type family [G : Type → Type] equipped with a
   polymorphic representation predicate; and it introduces the specification of
   iteration methods and lazy sequences. *)

From iris.proofmode Require Import base tactics classes.
From language Require Import eff_lang.
From program_logic Require Import reasoning_rules.
From case_studies Require Import list_lib.

Set Default Proof Using "Type".


(* ========================================================================== *)
(** * Representation Predicates. *)

(* A meta-level type [A] is representable in [HH]
   if it admits a representation predicate. *)
Class Representable Σ (A : Type) :=
  represents : val → A → iProp Σ.

(* A representable type [A] is persistently representable
   if its representation predicate holds persistently. *)
Class PersRepresentable Σ A `{Representable Σ A} :=
  pers_representable x X :> Persistent (represents x X).


(* ========================================================================== *)
(** * Data Structure. *)

(* We formalize a data structure as a type family [G], such that
   [G A] is representable for every repesentable type [A]. *)
Class DataStructure Σ (G : Type → Type) :=
  is_representable A `{Representable Σ A} :> Representable Σ (G A).

(* A data structure [G] is persistent if [G A] is persistently
   representable for every persistently representable type [A]. *)
Class PersStructure Σ G `{DataStructure Σ G} :=
  is_pers_representable A `{PersRepresentable Σ A} :>
    PersRepresentable Σ (G A).


(* ========================================================================== *)
(** * Iteration Descriptors. *)

Class Iterable (G : Type → Type) := {
  (* [permitted T Xs] holds if [Xs] is a possible prefix
     of visited elements of the collection [T]. *)
  permitted {A : Type} : G A → list A → Prop;

  (* [complete T Xs] holds if [Xs] is the complete list
     of elements of the collection [T]. *)
  complete  {A : Type} : G A → list A → Prop;
}.

(* A finitely iterable data structure is one whose elements can
   be named in advance, before the iteration has terminated. *)
Class FinIterable G `{Iterable G, ∀ A, Elements A (G A)} := {
  permitted_elements {A : Type} :
    ∀ (T : G A) (Xs : list A), permitted T Xs → Xs ⊆ elements T;

  complete_elements {A : Type} :
    ∀ (T : G A) (Xs : list A), complete T Xs → Xs ≡ₚ elements T;
}.


(* ========================================================================== *)
(** * Higher-Order Iteration Methods. *)

Section iteration_methods.
  Context `{!irisGS eff_lang Σ}.
  Context {G : Type → Type} `{DataStructure Σ G, Iterable G}
          {A : Type}        `{Representable Σ A}.

  Variables (t : val) (T : G A).

  Definition isIter (Ψ1 Ψ2 : iEff Σ) (iter : val) : iProp Σ :=
    ∀ E (I : list A → iProp Σ) (f : val),

      □ (∀ (Xs : list A) (X : A) (x : val),
           ⌜ permitted T (Xs ++ [X]) ⌝ -∗
             I Xs -∗
               represents x X -∗
                 EWP f x @ E <| Ψ1 |> {| Ψ2 |} {{ _,
                   represents x X ∗ I (Xs ++ [X]) }})

      -∗

        represents t T -∗
          I [] -∗
            EWP iter f t @ E <| Ψ1 |> {| Ψ2 |} {{ _,
              represents t T ∗ ∃ Xs, I Xs ∗ ⌜ complete T Xs ⌝ }}
  .

  (* Indicator of effect polymorphism. *)
  Inductive eff_poly_ind : Set := Both | Only (m : mode).

  Definition isEffPolyIter (i : eff_poly_ind) (iter : val) : iProp Σ :=
    match i with
    | Both => ∀ Ψ1 Ψ2, isIter Ψ1 Ψ2 iter
    | Only OS => ∀ Ψ1, isIter Ψ1 ⊥ iter
    | Only MS => ∀ Ψ2, isIter ⊥ Ψ2 iter
    end.

End iteration_methods.


(* ========================================================================== *)
(** * Lazy Sequences. *)

Section lazy_sequences.
  Context `{!irisGS eff_lang Σ}.
  Context  {G : Type → Type} `{DataStructure Σ G, Iterable G}
           {A : Type}        `{Representable Σ A}.

  Variables (t : val) (T : G A).

  (* ------------------------------------------------------------------------ *)
  (** Specification of Heads. *)

  (* The predicate [isHead] is defined as [isHead_pre isSeq], where [isSeq] is
     the fixpoint of [isSeq_pre]. *)
  (* A head is either a [Cons] pair or a [Nil] marker. *)
  Definition isHead_pre
    (isSeq :  iEff Σ -d> iEff Σ -d> val -d> list A -d> iPropO Σ)
           :  iEff Σ -d> iEff Σ -d> val -d> list A -d> iPropO Σ  :=
    λ Ψ1 Ψ2 h Xs,
      match h with
      | NONEV        =>
          represents t T ∗ ⌜ complete T Xs ⌝
      | SOMEV (x, k)%V =>
          ∃ X, ⌜ permitted T (Xs ++ [X]) ⌝ ∗ ▷ isSeq Ψ1 Ψ2 k (Xs ++ [X])
      | _ =>
          False
      end%I.

  (* ------------------------------------------------------------------------ *)
  (** Specification of Sequences. *)

  (* A sequence is a thunk [k] that, when applied to [#()], produces a head
     [h] s.t. [isHead Ψ1 Ψ2 h Xs]. *)
  Definition isSeq_pre
    (isSeq :  iEff Σ -d> iEff Σ -d> val -d> list A -d> iPropO Σ)
           : (iEff Σ -d> iEff Σ -d> val -d> list A -d> iPropO Σ) :=
    λ Ψ1 Ψ2 k Xs,
      EWP k #() <| Ψ1 |> {| Ψ2 |} {{ h, isHead_pre isSeq Ψ1 Ψ2 h Xs }}%I.

  (* [isSeq_pre] is contractive, therefore it admits a fixpoint. *)
  Local Instance isHead_pre_contractive : Contractive isSeq_pre.
  Proof.
    rewrite /isSeq_pre /isHead_pre => n isSeq isSeq' HisSeq Ψ1 Ψ2 k us.
    f_equiv=>?. simpl. repeat (f_contractive || f_equiv). by apply HisSeq.
  Qed.
  Definition isSeq_def :
    iEff Σ -d> iEff Σ -d> val -d> list A -d> iPropO Σ :=
    fixpoint (isSeq_pre).
  Definition isSeq_aux : seal isSeq_def. Proof. by eexists. Qed.
  Definition isSeq := isSeq_aux.(unseal).
  Definition isHead := isHead_pre isSeq.
  Definition isSeq_eq : isSeq = isSeq_def := isSeq_aux.(seal_eq).
  Global Lemma isSeq_unfold Ψ1 Ψ2 k us :
    isSeq Ψ1 Ψ2 k us ⊣⊢ isSeq_pre isSeq Ψ1 Ψ2 k us.
  Proof. by rewrite isSeq_eq/isSeq_def;apply(fixpoint_unfold isSeq_pre). Qed.
  Global Lemma isHead_unfold Ψ1 Ψ2 :
    isHead Ψ1 Ψ2 = isHead_pre isSeq Ψ1 Ψ2.
  Proof. done. Qed.

End lazy_sequences.


(* ========================================================================== *)
(** * Higher-Order Data Structures. *)

(* We prove that
   (1) if [G] is a data structure, then [G ∘ G] is a data structure;
   (2) if [G] is iterable, then [G ∘ G] is iterable; and
   (3) if [iter] is an iteration method for an arbitrary representation of the
       structure [G A], then we can derive an iteration method [lift_iter] for
       an arbitrary structure [G (G A)]. *)

Section higher_order.
  Context `{!heapGS Σ}.

  (* ------------------------------------------------------------------------ *)
  (** Lift Data Structure. *)

  Global Instance lift_data_structure G `{DataStructure Σ G} :
    DataStructure Σ (G ∘ G).
  Proof. intros ??. simpl. by apply _. Defined.


  (* ------------------------------------------------------------------------ *)
  (** Lift Iterable. *)

  Section iterable.
    Context G `{DataStructure Σ G, Iterable G}.

    Definition lift_permitted {A} (TT : (G (G A))) (Xs : list A) : Prop :=
      (* We match over [last Xs] to facilitate the simplification of
         assertions of the form [permitted _ (_ ++ [X])]. *)
      match last Xs with None => True | _ =>
        ∃ (Ts : list (G A)) (T : G A) (Xss : list (list A)) (Ys : list A),
          Xs = concat Xss ++ Ys    ∧
          permitted TT (Ts ++ [T]) ∧ 
          permitted T Ys           ∧
          Forall2 complete Ts Xss
      end.

    Definition lift_complete {A} (TT : G (G A)) (Xs : list A) : Prop :=
      ∃ (Ts : list (G A)) (Xss : list (list A)),
        Xs = concat Xss         ∧
        complete TT Ts          ∧
        Forall2 complete Ts Xss.

    Global Program Instance lift_iterable : Iterable (G ∘ G) := {
      permitted := @lift_permitted;
      complete  := @lift_complete;
    }.

  End iterable.


  (* ------------------------------------------------------------------------ *)
  (** Lift Iteration Method. *)

  Section lift_iteration_method. 
    Context G `{DataStructure Σ G, Iterable G}.

    Definition lift_iter (iter : val) : val := (λ: "f" "tt",
      iter (λ: "t", iter "f" "t") "tt")%V.

    Lemma lift_iter_isIter (iter : val) (Ψ1 Ψ2 : iEff Σ) :
      □ (∀ (A : Type) `{Representable Σ A} (t : val) (T : G A),
          isIter t T Ψ1 Ψ2 iter)
        -∗
      □ (∀ (A : Type) `{Representable Σ A} (tt : val) (TT : (G ∘ G) A),
          isIter tt TT Ψ1 Ψ2 (lift_iter iter)).
    Proof.
      iIntros "#Hiter" (????) "!#".
      iIntros (E I f) "#Hf Hrepr HI". unfold lift_iter.
      ewp_pure_steps. simpl in TT.
      iApply (ewp_pers_mono with "[Hrepr HI]").
      iApply ("Hiter" $!
        ((* Type of the elements. *) G A) (is_representable A)
        ((* Value represention. *) tt)
        ((* Data structure. *) TT)
        ((* Mask. *) E)
        ((* Invariant. *) λ (Ts : list (G A)), ∃ Xss,
           I (concat Xss) ∗ ⌜ Forall2 complete Ts Xss ⌝)%I
        ((* Iteratee. *) (λ: "t", iter f "t")%V)
        with "[] Hrepr [HI]"); [|by iExists []; iFrame].
      - iIntros "!#" (Ts T t) "%Hpermitted [%Xss [HI %Hcomplete]] Ht". 
        ewp_pure_steps.
        iApply (ewp_pers_mono with "[HI Ht]").
        iApply ("Hiter" $! A H1 t T E
          ((* Invariant. *) λ (Xs : list A), I (concat Xss ++ Xs))%I
          ((* Iteratee. *) f)
          with "[] Ht [HI]"); [|rewrite app_nil_r; by iFrame].
        + iIntros "!#" (Xs X x) "%Hpermitted_T HI Hx".
          rewrite app_assoc.
          iApply ("Hf" $! _ X x with "[] HI Hx").
          iPureIntro. rewrite /lift_permitted last_app last_cons //=.
          exists Ts, T, Xss, (Xs ++ [X]).
          rewrite app_assoc. by repeat split.
        + iIntros "!#" (?) "[$ [%Xs [HI %Hcomplete_T]]] !>".
          iExists (Xss ++ [Xs]). rewrite concat_app //= app_nil_r.
          iFrame. iPureIntro. by decompose_Forall.
      - iIntros "!#" (y) "[$ [%Ts [[%Xss [HI %Hxs]] %Hcomplete_TT]]] !>".
        iExists (concat Xss). iFrame. iPureIntro.
        rewrite /lift_complete. by exists Ts, Xss.
    Qed.

  End lift_iteration_method.

End higher_order.


(* ========================================================================== *)
(** * Examples of Data Structures and Iteration Methods. *)

(* -------------------------------------------------------------------------- *)
(** References. *)

Section refs.
  Context `{!heapGS Σ}.

  Definition Ref (A : Type) := A.

  Global Program Instance ref_structure : DataStructure Σ Ref := {
    is_representable (A : Type) `{Representable Σ A} := (λ r X,
      ∃ (ℓ : loc) (x : val), ⌜ r = #ℓ ⌝ ∗ ℓ ↦ x ∗ represents x X)%I
  }.

  Definition ref_permitted {A} : A → list A → Prop := λ X, (.⊆ [X]).
  Definition ref_complete  {A} : A → list A → Prop := λ X, (.= [X]).

  Global Instance ref_iterable : Iterable Ref := {
    permitted := @ref_permitted;
    complete  := @ref_complete;
  }.

  (* Example of an iteration method over the structure [Ref]. *)
  Definition ref_iter : val := (λ: "f" "r", "f" (Load "r"))%V.

  (* Because [represents r (T : Ref A)] is an ephemeral resource,
     the method [ref_iter] is not polymorphic w.r.t. multi-shot
     effects. *)
  Lemma ref_iter_isIter {A} `{Representable Σ A} (r : val) (T : Ref A) :
    ⊢ isEffPolyIter r T (Only OS) ref_iter.
  Proof.
    iIntros (????) "#Hf [%ℓ [%x (->&Hℓ&Hrepr)]] HI". unfold ref_iter.
    ewp_pure_steps. ewp_bind_rule. simpl.
    iApply (ewp_load with "Hℓ"). iNext.
    iIntros "Hℓ". iModIntro.
    iApply (ewp_mono with "[Hrepr HI]").
    { iApply ("Hf" with "[] HI Hrepr"). by iPureIntro; set_solver. }
    iIntros (_) "[Hx HI]". iModIntro.
    iSplitL "Hx Hℓ" ; [by iExists ℓ, x; iFrame|].
    iExists [T]. by iFrame.
  Qed.

End refs.


(* -------------------------------------------------------------------------- *)
(** Persistent Lists. *)

Section persistent_lists.
  Context `{!heapGS Σ}.

  Definition PersList (A : Type) := list A.

  Fixpoint list_encoding' (us : list val) : val :=
    match us with
    | [] =>
         InjLV #()
    | u :: us =>
         InjRV (u, list_encoding' us)%V
    end.

  Global
  Program Instance pers_list_structure : DataStructure Σ PersList := {
    is_representable (A : Type) `{Representable Σ A} := (λ l Xs, ∃ us,
      ⌜ l = list_encoding' us ⌝ ∗ [∗ list] u; X ∈ us; Xs, represents u X)%I
  }.

  Global
  Program Instance pers_list_pers_structure : PersStructure Σ PersList.
  Next Obligation. iIntros (?????); by apply _. Qed.

  Definition list_permitted {A} : list A → list A → Prop := flip prefix.
  Definition list_complete  {A} : list A → list A → Prop := (=).

  Global Instance pers_list_iterable : Iterable PersList := {
    permitted := @list_permitted;
    complete  := @list_complete;
  }.

  Lemma list_iter_isIter {A} `{PersRepresentable Σ A} (l : val) (Xs : PersList A) :
    ⊢ isEffPolyIter l Xs Both list_iter'.
  Proof.
    iIntros (?????) "#Hf #Hrepr HI". unfold list_iter'.
    do 3 ewp_value_or_step.
    iInduction Xs as [|X Xs] "IH" forall (l I);
    iDestruct "Hrepr" as "[%us [-> #Hus]]".
    - destruct us; [|done]. simpl. ewp_pure_steps.
      iSplit; iExists []; try by simpl. by iFrame.
    - destruct us as [|u us]; [done|]. simpl.
      ewp_pure_steps. ewp_bind_rule. simpl.
      iDestruct "Hus" as "[Hu Hus]".
      iApply (ewp_pers_mono with "[HI Hu] [Hus]"); [
      iApply ("Hf" with "[] HI Hu");
      iPureIntro; by exists Xs|].
      iIntros "!#" (y) "[_ HI] !>". simpl.
      do 3 ewp_value_or_step.
      iApply (ewp_pers_mono with "[HI Hus]").
      + iApply ("IH" $! _
          ((* invariant. *) λ Ys, I (X :: Ys))
          with "[] [Hus] [$]");
        last (by iModIntro; iExists us; iSplit).
        iIntros "!>" (Ys Z z) "%Hprefix HI Hz".
        iApply ("Hf" $! (X :: Ys) Z z with "[] HI Hz").
        iPureIntro.
        destruct Hprefix as [Ys' ->].
        by exists Ys'.
      + unfold list_complete.
        iIntros "!#" (?) "[[%vs [%Heq Hvs]] [%Ys [HI <-]]] !>".
        iSplitR "HI"; [|iExists (X :: Xs); by iFrame].
        iExists (u :: us). iFrame.
        iSplit; [done|].
        rewrite (_: us = vs); [by simpl; iFrame|].
        revert Heq. revert vs.
        induction us; destruct vs; try done.
        simpl. injection 1. intros Hus ->.
        f_equal. by apply IHus.
  Qed.

End persistent_lists.


(* -------------------------------------------------------------------------- *)
(** Linked Lists. *)

Section linked_lists.
  Context `{!heapGS Σ}.

  Definition LinkedList (A : Type) := list A.

  Global
  Program Instance linked_list_structure : DataStructure Σ LinkedList := {
    is_representable (A : Type) `{Representable Σ A} :=
      fix is_llist (xs : val) (Xs : list A) {struct Xs} :=
        match Xs with
        | []      => ∃ (ℓ : loc), ⌜ xs = #ℓ ⌝ ∗ ℓ ↦ InjLV #()
        | X :: Xs => ∃ (ℓ : loc), ⌜ xs = #ℓ ⌝ ∗
                     ∃ (x xs : val),
                       ℓ ↦ InjRV (x, xs)%V ∗
                       represents x X      ∗
                       is_llist xs Xs
        end%I
  }.

  Global
  Program Instance linked_list_iterable : Iterable LinkedList := {
    permitted := @list_permitted;
    complete  := @list_complete;
  }.

  Definition llist_iter : val := (λ: "f",
    rec: "iter" "l" :=
      match: Load "l" with
        InjL <> =>
          #()
      | InjR "args" =>
          let: "u" := Fst "args" in
          let: "l" := Snd "args" in
          "f" "u";; "iter" "l"
      end
  )%V.

  Lemma llist_iter_isIter {A} `{Representable Σ A} l (Xs : LinkedList A) :
    ⊢ isEffPolyIter l Xs (Only OS) llist_iter.
  Proof.
    iIntros (????) "#Hf Hxs HI".
    rewrite /llist_iter. do 3 ewp_value_or_step.
    iInduction Xs as [|X Xs] "IH" forall (I l).
    - iDestruct "Hxs" as "[%ℓ [-> Hℓ]]"; ewp_pure_steps.
      ewp_bind_rule. simpl.
      iApply (ewp_load with "Hℓ").
      iIntros "!> Hℓ !>". ewp_pure_steps.
      iSplitR "HI"; [iExists ℓ|iExists []]; by iFrame.
    - iDestruct "Hxs" as "[%ℓ [-> [%x [%xs (Hℓ&Hx&Hxs)]]]]"; ewp_pure_steps.
      ewp_bind_rule. simpl.
      iApply (ewp_load with "Hℓ").
      iIntros "!> Hℓ !>". ewp_pure_steps. ewp_bind_rule. simpl.
      iApply (ewp_mono with "[HI Hx] [Hxs Hℓ]"); [
      iApply ("Hf" with "[] HI Hx");
      iPureIntro; by exists Xs|].
      iIntros (y) "[Hx HI] !>". simpl.
      do 3 ewp_value_or_step.
      iApply (ewp_mono with "[HI Hxs]").
      + iApply ("IH" $!
          ((* invariant. *) λ Ys, I (X :: Ys))
          with "[] [Hxs] [$]"); last done.
        iIntros "!>" (Ys Z z) "%Hprefix HI Hz".
        iApply ("Hf" $! (X :: Ys) Z z with "[] HI Hz").
        iPureIntro.
        destruct Hprefix as [Ys' ->].
        by exists Ys'.
      + unfold list_complete.
        iIntros (?) "[Hxs [%Ys [HI <-]]] !>".
        iSplitR "HI"; [|iExists (X :: Xs); by iFrame].
        iExists ℓ. iSplit; [done|].
        iExists x, xs. by iFrame.
  Qed.

End linked_lists.
