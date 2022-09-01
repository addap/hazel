(* iterable.v *)

(* In the file [cascade.v], we introduce the type class [IterLib], which
   includes the specification of the iteration method of a given collection of
   elements. This specification is sufficient to verify many programs that
   iterate over data structures. However, it is unclear how to handle programs
   that iterate over higher-order data structures in a nested fashion, such as,
   for example, a program traversing a list of lists. The problem is that the
   specification from [IterLib] implicitly assumes a fixed collection of
   elements. Thus, if we wish to reason about iteration over a collection of
   collections, then we would need one instance of [IterLib] per collection.
   This is unsatisfactory because an iteration method is usually polymorphic.
   The same function that traverses a list of integers is the one that
   traverses a list of lists of integers. So we would like to apply the same
   specification to reason about these two kinds of iteration.

   In this file, we propose a solution for this problem of specifying iteration
   methods in such a way that one can reason about nested iteration. There are
   two key ideas. The first one is to introduce the abstract notion of a data
   structure. And the second one is to generalize [IterLib] with respect to
   this notion.
*)

From iris.proofmode Require Import base tactics classes.

From hazel Require Import weakestpre heap.
From hazel Require Import notation tactics.

Set Default Proof Using "Type".


(** * Representation Predicates. *)

Section representation.
  Context `{!heapG Σ}.

  (* A meta-level type [A] is representable in [HH]
     if it admits a representation predicate. *)
  Class Representable (A : Type) := represents : val → A → iProp Σ.

  (* A representable type [A] is persistently representable
     if its representation predicate holds persistently. *)
  Class PersRepresentable A `{Representable A} :=
    pers_representable x X :> Persistent (represents x X).

  (* A type family [G] is a data structure if [G A] is
     representable for every repesentable type [A]. *)
  Class DataStructure (G : Type → Type) :=
    is_representable A `{Representable A} :> Representable (G A).

  (* A data structure [G] is persistent if [G A] is persistently
     representable for every persistently representable type [A]. *)
  Class PersStructure G `{DataStructure G} :=
    is_pers_representable A `{PersRepresentable A} :>
      PersRepresentable (G A).

End representation.


(** * Iterable Interface. *)

Section iterable.
  Context `{!heapG Σ}.

  Class Iterable G `{DataStructure _ G} := {

    (* [iter] is the iteration method. *)
    iter : val;

    (* [permitted T Xs] holds if [Xs] is a possible prefix
       of visited elements of the collection [T]. *)
    permitted {A : Type} : G A → list A → Prop;

    (* [complete T Xs] holds if [Xs] is the complete list
       of elements of the collection [T]. *)
    complete  {A : Type} : G A → list A → Prop;

    (* Specification of [iter]. *)
    iter_spec E (A : Type) `{Representable _ A}
                (I : list A → iProp Σ)
                (Ψ : iEff Σ)
                (T : G A)
                (f : val)
                (t : val) :

        □ (∀ (Xs : list A) (X : A) (x : val),
             ⌜ permitted T (Xs ++ [X]) ⌝ -∗
               I Xs -∗
                 represents x X -∗
                   EWP f x @ E <| Ψ |> {{ _,
                     represents x X ∗ I (Xs ++ [X]) }})

      -∗

        represents t T -∗
          I [] -∗
            EWP iter f t @ E <| Ψ |> {{ _,
              represents t T ∗ ∃ xs, I xs ∗ ⌜ complete T xs ⌝ }};
  }.


  (* A finitely iterable data structure is one whose elements can
     be named in advance, before the iteration has terminated. *)
  Class FinIterable G `{Iterable G, ∀ A, Elements A (G A)} := {

    permitted_elements {A : Type} :
      ∀ (T : G A) (Xs : list A), permitted T Xs → Xs ⊆ elements T;

    complete_elements {A : Type} :
      ∀ (T : G A) (Xs : list A), complete T Xs → Xs ≡ₚ elements T;

  }.

End iterable.


(** * Higher-Order Structures. *)

(* We prove that, if [G] is a data structure, then [G ∘ G] is a data structure.
   Moreover, if [G] is iterable, then so is [G ∘ G]. *)

Section higher_order.
  Context `{!heapG Σ}.

  Section data_structure.
    Context G `{!DataStructure (Σ:=Σ) G}.

    Global Instance lift_data_structure : DataStructure (Σ:=Σ) (G ∘ G).
      intros ??. simpl. by apply _.
    Defined.

  End data_structure.

  Section iterable.
    Context G `{Iterable (Σ:=Σ) G}.

    Definition lift_iter : val := λ: "f" "tt",
      iter (λ: "t", iter "f" "t") "tt".

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

    Global Program Instance lift_iterable : Iterable (Σ:=Σ) (G ∘ G) := {
      iter      := lift_iter;
      permitted := @lift_permitted;
      complete  := @lift_complete;
    }.
    Next Obligation.
      iIntros (????? TT ? tt) "#Hf Htt HI". simpl in TT.
      rewrite /lift_iter. ewp_pure_steps.
      iApply (ewp_mono' with "[Htt HI]").
      iApply (iter_spec E
        ((* type of the elements. *) G A)
        ((* invariant. *) λ (Ts : list (G A)), ∃ Xss,
           I (concat Xss) ∗ ⌜ Forall2 complete Ts Xss ⌝)%I
        ((* protocol. *) Ψ)
        ((* data structure. *) TT)
        ((* iteratee. *) (λ: "t", iter f "t")%V)
        ((* value represention. *) tt)
        with "[] Htt [HI]"); [|iExists []; by iFrame].
      { iIntros "!>" (Ts T t) "%Hpermitted [%Xss [HI %Hcomplete]] Ht". 
        ewp_pure_steps.
        iApply (ewp_mono' with "[HI Ht]").
        iApply (iter_spec E
          ((* type of the elements. *) A)
          ((* invariant. *) λ (Xs : list A), I (concat Xss ++ Xs))%I
          ((* protocol. *) Ψ)
          ((* data structure. *) T)
          ((* iteratee. *) f)
          ((* value representation. *) t)
          with "[] Ht [HI]"); [|rewrite app_nil_r; by iFrame].
        { iIntros "!>" (Xs X x) "%Hpermitted_T HI Hx".
          rewrite app_assoc.
          iApply ("Hf" $! _ X x with "[] HI Hx").
          iPureIntro. rewrite /lift_permitted last_app last_cons //=.
          exists Ts, T, Xss, (Xs ++ [X]).
          rewrite app_assoc. by repeat split.
        }
        { iIntros (?) "[$ [%Xs [HI %Hcomplete_T]]] !>".
          iExists (Xss ++ [Xs]). rewrite concat_app //= app_nil_r.
          iFrame. iPureIntro. by decompose_Forall.
        }
      }
      { iIntros (y) "[$ [%Ts [[%Xss [HI %Hxs]] %Hcomplete_TT]]] !>".
        iExists (concat Xss). iFrame. iPureIntro.
        rewrite /lift_complete. by exists Ts, Xss.
      }
    Qed.

  End iterable.

End higher_order.


(** * Examples. *)

(** References. *)

Section refs.
  Context `{!heapG Σ}.

  Definition Ref (A : Type) := A.

  Global Program Instance ref_structure : DataStructure (Σ:=Σ) Ref := {
    is_representable (A : Type) `{!Representable A} := (λ r X,
      ∃ (ℓ : loc) (x : val), ⌜ r = #ℓ ⌝ ∗ ℓ ↦ x ∗ represents x X)%I
  }.

  Definition ref_permitted {A} : A → list A → Prop := λ X, (.⊆ [X]).
  Definition ref_complete  {A} : A → list A → Prop := λ X, (.= [X]).

  Global Program Instance ref_iterable : Iterable (Σ:=Σ) Ref := {
    permitted := @ref_permitted;
    complete  := @ref_complete;
    iter      := (λ: "f" "r", "f" (Load "r"))%V
  }.
  Next Obligation.
    iIntros (????? X ? r) "#Hf [%ℓ [%x (-> & Hℓ & Hx)]] HI".
    ewp_pure_steps. ewp_bind_rule. simpl.
    iApply (ewp_load with "Hℓ"). iNext.
    iIntros "Hℓ". iModIntro.
    iApply (ewp_mono' with "[HI Hx]").
    iApply ("Hf" with "[] HI Hx").
    { by iPureIntro; set_solver. }
    iIntros (?) "[Hx HI]". iModIntro.
    iSplitL "Hℓ Hx" ; [by iExists ℓ, x; iFrame|].
    iExists [X]. by iFrame.
  Qed.

End refs.


(** Persistent lists. *)

From hazel Require Import list_lib.

Section persistent_lists.
  Context `{!heapG Σ}.

  Definition PersList (A : Type) := list A.

  Global
  Program Instance pers_list_structure : DataStructure (Σ:=Σ) PersList := {
    is_representable (A : Type) `{!Representable A} := (λ l Xs, ∃ us,
      ⌜ l = list_encoding' us ⌝ ∗ [∗ list] u; X ∈ us; Xs, represents u X)%I
  }.

  Global
  Program Instance pers_list_pers_structure : PersStructure PersList.
  Next Obligation. iIntros (?????); by apply _. Qed.

  Definition list_permitted {A} : list A → list A → Prop := flip prefix.
  Definition list_complete  {A} : list A → list A → Prop := (=).

  Global Program Instance pers_list_iterable : Iterable (Σ:=Σ) PersList := {
    permitted := @list_permitted;
    complete  := @list_complete;
    iter      := list_iter';
  }.
  Next Obligation.
    iIntros (????? Xs ? xs) "#Hf Hxs HI".
    rewrite /list_iter'. do 3 ewp_value_or_step.
    (* We generalize the statement over the invariant [I]
       before applying induction. Later, we specialize the induction
       principle with the invariant [λ Ys, I (X :: Ys)], where [X] is
       the head of [Xs] in the inductive case. *)
    iInduction Xs as [|X Xs] "IH" forall (I xs); ewp_pure_steps.
    - iDestruct "Hxs" as "[%us [-> Hus]]".
      destruct us; [|done]. simpl. ewp_pure_steps.
      by iSplitR; iExists []; [iSplit| iFrame].
    - iDestruct "Hxs" as "[%us [-> Hus]]".
      destruct us as [|u us]; [done|]. simpl.
      ewp_pure_steps. ewp_bind_rule. simpl.
      iDestruct "Hus" as "[Hu Hus]".
      iApply (ewp_mono' with "[HI Hu] [Hus]"); [
      iApply ("Hf" with "[] HI Hu");
      iPureIntro; by exists Xs|].
      iIntros (y) "[Hu HI] !>". simpl.
      do 5 ewp_value_or_step.
      iApply (ewp_mono' with "[HI Hus]").
      + iApply ("IH" $!
          ((* invariant. *) λ Ys, I (X :: Ys))
          with "[] [Hus] [$]");
        last (iExists us; by iFrame).
        iIntros "!>" (Ys Z z) "%Hprefix HI Hz".
        iApply ("Hf" $! (X :: Ys) Z z with "[] HI Hz").
        iPureIntro.
        destruct Hprefix as [Ys' ->].
        by exists Ys'.
      + unfold list_complete.
        iIntros (?) "[[%vs [%Heq Hvs]] [%Ys [HI <-]]] !>".
        iSplitR "HI"; [|iExists (X :: Xs); by iFrame].
        iExists (u :: us). iFrame.
        iSplit; [done|].
        rewrite (_: us = vs); [done|].
        revert Heq. revert vs.
        induction us; destruct vs; try done.
        simpl. injection 1. intros Hus ->.
        f_equal. by apply IHus.
  Qed.

End persistent_lists.


(** Linked lists. *)

Section linked_lists.
  Context `{!heapG Σ}.

  Definition LinkedList (A : Type) := list A.

  Definition llist_iter : val := λ: "f",
    rec: "iter" "xs" :=
      match: Load "xs" with InjL <> => #() | InjR "args" =>
        "f" (Fst "args");; "iter" (Snd "args")
      end.

  Global
  Program Instance linked_list_structure : DataStructure (Σ:=Σ) LinkedList := {
    is_representable (A : Type) `{!Representable A} :=
      fix is_llist (xs : val) (Xs : list A) {struct Xs} :=
        match Xs with
        | []      => ∃ (ℓ : loc), ⌜ xs = #ℓ ⌝ ∗ ℓ ↦ InjLV #()
        | X :: Xs => ∃ (ℓ : loc), ⌜ xs = #ℓ ⌝ ∗
                     ∃ (x xs : val),
                       ℓ ↦ InjRV (PairV x xs) ∗
                       represents x X         ∗
                       is_llist xs Xs
        end%I
  }.

  Global
  Program Instance linked_list_iterable : Iterable (Σ:=Σ) LinkedList := {
    permitted := @list_permitted;
    complete  := @list_complete;
    iter      := llist_iter;
  }.
  Next Obligation.
    iIntros (????? Xs ? xs) "#Hf Hxs HI".
    rewrite /llist_iter. do 3 ewp_value_or_step.
    iInduction Xs as [|X Xs] "IH" forall (I xs); ewp_pure_steps.
    - iDestruct "Hxs" as "[%ℓ [-> Hℓ]]".
      ewp_bind_rule. simpl.
      iApply (ewp_load with "Hℓ").
      iIntros "!> Hℓ !>". ewp_pure_steps.
      iSplitR "HI"; [iExists ℓ|iExists []]; by iFrame.
    - iDestruct "Hxs" as "[%ℓ [-> [%x [%xs (Hℓ & Hx & Hxs)]]]]".
      ewp_bind_rule. simpl.
      iApply (ewp_load with "Hℓ").
      iIntros "!> Hℓ !>". ewp_pure_steps. ewp_bind_rule. simpl.
      iApply (ewp_mono' with "[HI Hx] [Hxs Hℓ]"); [
      iApply ("Hf" with "[] HI Hx");
      iPureIntro; by exists Xs|].
      iIntros (y) "[Hx HI] !>". simpl.
      do 5 ewp_value_or_step.
      iApply (ewp_mono' with "[HI Hxs]").
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
