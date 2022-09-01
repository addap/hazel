(* cascade.v *)

(* This file contains the verification of [invert], a program that
   applies an effect handler to transform a higher-order iteration
   method into a lazy sequence. A higher-order iteration method is
   a function [iter] of type [('a -> unit) -> unit]. It applies an
   input function [f : 'a -> unit] to the elements of a collection.
   It "consumes" the elements of this collection. A lazy sequence
   "produces" elements. It is a thunk that, when forced, produces
   either a pair of one element of the structure and a sequence for
   the remaining elements, or a marker of the end of the collection.
*)

From stdpp Require Import list.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth.
From iris.program_logic Require Import weakestpre.
From hazel Require Import notation weakestpre deep_handler tactics.


(** Implementation. *)

(* Implementation of [invert] in HH. *)

Section implementation.

  (* Sequences. *)

  (* In OCaml, the type of sequences can be defined as follows:

       type 'a seq  = unit -> 'a head
        and 'a head = Nil | Cons of 'a * 'a seq

     In HH, we encode sequences as functions from unit to binary
     sums encoding the inhabitants of the type ['a head]:
  *)

  Definition sCons (x k : expr) : expr := SOME (x, k).
  Definition sNil               : val  := NONEV%V.


  (* Invert. *)

  (* The program [invert] installs a handler over the application
     of [iter] to [yield]. The function [yield] performs an effect
     every time it is applied to an element of the collection. When
     [yield] performs an effect with such an element [x], the effect
     branch receives this element as well as a continuation [k]
     representing the paused execution of [iter]. It then packages
     both of these values into a [Cons] pair. When the iteration
     terminates, the return branch assumes control and returns a
     [Nil] head.
  *)

  Definition invert : val := λ: "iter", λ: <>,
    let: "yield" := λ: "x", do: "x" in
    try: "iter" "yield" with
      effect λ: "x" "k", sCons "x" "k"
    | return λ: <>, sNil
    end.

End implementation.


(** Specification. *)

(* The specification of [invert] depends on (1) the specification
   of a iteration method and (2) the specification of a lazy sequence,
   Both of which depend on the predicates [permitted], [complete],
   and [canTraverse]. These predicates are tied to the implicit data
   structure that an iteration method [iter] traverses and whose
   elements a lazy sequence produces.
*)

Section specification.

  (* Specification of iteration methods. *)

  Section iteration_methods.

    Class isIter Σ `{!irisGS eff_lang Σ} := {
      (* Program that traverses the structure. *)
      iter : val;

      (* Predicate that describes the possible partial paths. *)
      permitted : list val → iProp Σ;

      (* Predicate that describes the possible complete paths. *)
      complete : list val → iProp Σ;

      (* Permission to traverse a structure. *)
      canTraverse : iProp Σ;

      (* Specification of [iter]. *)
      iter_spec E
        (I : list val → iProp Σ) (* Loop invariant. *)
        (Ψ : iEff Σ)             (* Iteratee's effects. *)
        (f : val) :

        (* "If [f] bumps [I] by one step, ..." *)
        □ (∀ us u,
             permitted (us ++ [u]) -∗
               I us -∗
                 EWP f u @ E <| Ψ |> {{ _, I (us ++ [u]) }}) -∗

      (* "... then [iter f] bumps [I] by [us] steps." *)
       canTraverse -∗
          I [] -∗
            EWP iter f @ E <| Ψ |>
              {{ _, ∃ xs,
                      I xs ∗ complete xs ∗ canTraverse
              }};
    }.

  End iteration_methods.


  (* Specification of lazy sequences. *)

  Section lazy_sequences.
    Context `{!heapG Σ}
             {HisIter: isIter Σ}. (* The specification of lazy sequences
                                     depends on the predicates [permitted],
                                     [complete], and [canTraverse]. *)

    (* Specification of heads. *)

    (* The predicate [isHead] is defined as [isHead_pre isSeq],
       where [isSeq] is the fixpoint of [isSeq_pre]. *)
    (* A head is either a [Cons] pair or a [Nil] marker. *)
    Definition isHead_pre
      (isSeq :  val -d> list val -d> iPropO Σ)
             : (val -d> list val -d> iPropO Σ) := λ h us,
      match h with
      | NONEV        => complete   us         ∗ canTraverse
      | SOMEV (u, k) => permitted (us ++ [u]) ∗ ▷ isSeq k (us ++ [u])
      | _ => False
      end%I.

    (* Specification of sequences. *)

    (* A sequence is a thunk [k] that, when applied to [#()],
       produces a head [h] s.t. [isHead h us]. *)
    Definition isSeq_pre
      (isSeq :  val -d> list val -d> iPropO Σ)
             : (val -d> list val -d> iPropO Σ) := λ k us,
      EWP k #() {{ h, isHead_pre isSeq h us }}%I.

    (* [isSeq_pre] is contractive, therefore it admits a fixpoint. *)
    Local Instance isHead_pre_contractive : Contractive isSeq_pre.
    Proof.
      rewrite /isSeq_pre /isHead_pre => n isSeq isSeq' HisSeq k us.
      f_equiv=>?. simpl. by repeat (f_contractive || f_equiv).
    Qed.
    Definition isSeq_def : val -d> list val -d> iPropO Σ := fixpoint (isSeq_pre).
    Definition isSeq_aux : seal isSeq_def. Proof. by eexists. Qed.
    Definition isSeq := isSeq_aux.(unseal).
    Definition isHead := isHead_pre isSeq.
    Definition isSeq_eq : isSeq = isSeq_def := isSeq_aux.(seal_eq).
    Global Lemma isSeq_unfold k us : isSeq k us ⊣⊢ isSeq_pre isSeq k us.
    Proof. by rewrite isSeq_eq/isSeq_def;apply(fixpoint_unfold isSeq_pre). Qed.
    Global Lemma isHead_unfold h us : isHead h us = isHead_pre isSeq h us.
    Proof. done. Qed.

  End lazy_sequences.


  (* Specification of [invert]. *)

  Section invert.
    Context `{!heapG Σ} {HisIter: isIter Σ}.

    Definition invert_spec : iProp Σ :=
      canTraverse -∗
        EWP invert iter <| ⊥ |> {{ k,
          isSeq k [] }}.

  End invert.

End specification.


(** Verification. *)

(* The key ideas in the verification of [invert] are the
   introduction of a piece of ghost state to describe the
   elements seen by handler and handlee, and the application
   of the reasoning rule for deep handlers.
*)

Section verification.

  Section ghost_theory.
    (* We use ghost variables with contents in the CMRA [Auth(Ex(List Val))]. *)
    Context `{!inG Σ (excl_authR (leibnizO (list val)))}.

    (* The assertion [own γ (●E us)] states that the handler
       has seen the elements [us]. *)
    Definition handlerSt γ us : iProp Σ :=
      own γ (●E (us : ofe_car (leibnizO (list val)))).
    (* The assertion [own γ (◯E us)] states that [iter]
       has seen the elements [us]. *)
    Definition iterSt γ us : iProp Σ :=
      own γ (◯E (us : ofe_car (leibnizO (list val)))).

    (* Create a new ghost cell from this CMRA. *)
    (* In the verification of [invert], the ghost variable [γ]
       initially holds the empty list. *)
    Lemma new_cell us : ⊢ (|==> ∃ γ, handlerSt γ us ∗ iterSt γ us)%I.
    Proof.
      iMod (own_alloc ((●E (us : ofe_car (leibnizO (list val)))) ⋅
                       (◯E (us : ofe_car (leibnizO (list val)))))) as (γ) "[??]";
      [ apply excl_auth_valid | eauto with iFrame ]; done.
    Qed.

    (* Handler and [iter]'s views are in agreement. *)
    Lemma confront_views γ us vs : handlerSt γ us -∗ iterSt γ vs -∗ ⌜us = vs⌝.
    Proof.
      iIntros "Hγ● Hγ◯".
      by iDestruct (own_valid_2 with "Hγ● Hγ◯") as %?%excl_auth_agree_L.
    Qed.

    (* With the ownership of both views, one can update the contents of [γ]. *)
    Lemma update_cell γ ws us vs :
      handlerSt γ us -∗ iterSt γ vs ==∗ handlerSt γ ws  ∗ iterSt γ ws.
    Proof.
      iIntros "Hγ● Hγ◯".
      iMod (own_update_2 _ _ _ (●E (ws : ofe_car (leibnizO (list val))) ⋅
                                ◯E (ws : ofe_car (leibnizO (list val))))
        with "Hγ● Hγ◯") as "[$$]";
      [ apply excl_auth_update |]; done.
    Qed.

  End ghost_theory.

  Section invert_correct.
    Context `{!heapG Σ}
             {HisIter: isIter Σ}
            `{!inG Σ (excl_authR (leibnizO (list val)))}.

    (* This protocol describes the effects performed by [yield]. *)
     Definition Ψ_yield I : iEff Σ :=
      (>> us u >> !u   {{ I us ∗ permitted (us ++ [u]) }};
                  ?#() {{ I (us ++ [u]) }}).

    (* The [yield] handler is correct. *)
    Lemma yield_handler_correct γ (vs : list val) :
      handlerSt γ vs -∗
        deep_handler ⊤ (λ: "x" "k", sCons "x" "k")%V (λ: <>, sNil)%V
         (* Client's protocol:  *)
           (Ψ_yield (iterSt γ))
         (* Handler's protocol: *)
           ⊥
         (* Client's postcondition:  *)
           (λ _, ∃ (us : list val), iterSt γ us ∗ complete us ∗ canTraverse)
         (* Handler's postcondition: *)
           (λ h , isHead h vs).
    Proof.
      iLöb as "IH" forall (vs γ).
      rewrite !deep_handler_unfold /deep_handler_eq.
      iIntros "HhandlerSt". iSplit.
      - iIntros (v) "HΦ".
        iDestruct "HΦ" as (us) "(HiterSt & Hcomplete & HcanTraverse)".
        iDestruct (confront_views with "HhandlerSt HiterSt") as "<-".
        iNext. unfold sNil. ewp_pure_steps. by iFrame.
      - iIntros (u k) "Hhandler". iNext.
        rewrite /(Ψ_yield (iterSt γ)).
        rewrite (protocol_agreement_tele' [tele _ _] [tele]) //=.
        iDestruct "Hhandler" as (us u') "(<- & [HiterSt Hpermitted] & Hk)".
        iApply fupd_ewp.
        iDestruct (confront_views with "HhandlerSt HiterSt") as "%Heq".
        rewrite Heq. clear Heq.
        iMod (update_cell _ (us ++ [u]) with "HhandlerSt HiterSt")
          as "[HhandlerSt HiterSt]".
        iModIntro.
        iSpecialize ("Hk" with "HiterSt").
        unfold sCons. ewp_pure_steps. iFrame. iNext.
        rewrite !isSeq_unfold /isSeq_pre.
        iSpecialize ("IH" with "HhandlerSt").
        by iApply ("Hk" with "IH").
    Qed.

    (* [invert] is correct. *)
    Lemma invert_correct : ⊢ invert_spec.
    Proof.
      iIntros "HcanTraverse". unfold invert.
      iApply fupd_ewp.
      iMod (new_cell []) as (γ) "[HhandlerSt HiterSt]".
      iModIntro. ewp_pure_steps.
      rewrite !isSeq_unfold isSeq_eq /isSeq_pre.
      do 10 ewp_value_or_step.
      iApply (ewp_deep_try_with with "[HcanTraverse HiterSt]").
      - iApply (iter_spec _ (iterSt γ) (Ψ_yield (iterSt γ))
          with "[] HcanTraverse HiterSt").
        iModIntro. iIntros (us u) "Hpermitted HiterSt".
        ewp_pure_steps. iApply ewp_eff. rewrite /Ψ_yield.
        rewrite (protocol_agreement_tele' [tele _ _] [tele]) //=.
        iExists us, u. iFrame. iSplit; [done|].
        iIntros "HiterSt". by ewp_pure_steps.
      - rewrite -isSeq_eq.
        by iApply (yield_handler_correct with "HhandlerSt").
    Qed.

  End invert_correct.

End verification.
