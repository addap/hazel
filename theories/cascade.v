(* cascade.v

   Verification of the program [invert], an example of control inversion using
   effect handlers.
*)

From stdpp              Require Import list.
From iris.proofmode     Require Import base tactics classes.
From iris.algebra       Require Import excl_auth.
From iris.program_logic Require Import weakestpre.
From hazel              Require Import notation weakestpre deep_handler.

Section iter.

(** Folds. *)

(* Specification of an iterator. *)

Class IterLib Σ `{!irisGS eff_lang Σ} := {
  iter      : val;
  permitted : list val → iProp Σ;
  complete  : list val → iProp Σ;
  S         : iProp Σ;            
  S'        : iProp Σ;

  iter_spec E (I : list val → iProp Σ)
              (Ψ : iEff Σ) (f : val) :

    □ (∀ us u, permitted (us ++ [u]) -∗
       S' -∗
         I us -∗
           EWP f u @ E <| Ψ |> {{ _, S' ∗ I (us ++ [u]) }}) -∗

    S -∗
      I [] -∗
        EWP iter f @ E <| Ψ |> {{ _, ∃ xs, S ∗ I xs ∗ complete xs }};
}.

End iter.


Section invert.
Context `{!heapG Σ} {HIterLib: IterLib Σ}.

(** Control Invertion. *)

(* The program [invert] takes an iterator as input and returns a stream of the
   elements in the underlying collection. It does so by halting the iteration
   each time it bumps into a new element.
*)

Definition invert : val := λ: "iter",
  let: "yield" := λ: "x", do: "x" in
  λ: <>,
    try: "iter" "yield" with
      effect (λ: "u" "k", SOME ("u", "k"))%V
    | return (λ: <>, NONEV)%V
    end.


(** Cascades. *)

(* Definition of the predicate [cascade]. *)

Definition cascade_pre :
  (val -d> list val -d> iPropO Σ) → (val -d> list val -d> iPropO Σ)
  := λ cascade k us,
     EWP k #() {{ y,
       match y with
       | NONEV        => complete   us         ∗ S
       | SOMEV (u, k) => permitted (us ++ [u]) ∗ ▷ cascade k (us ++ [u])
       | _ => False
       end }}%I.

Local Instance cascade_pre_contractive : Contractive cascade_pre.
Proof.
  rewrite /cascade_pre => n cascade cascade' Hcascade k us.
  f_equiv=>?. simpl.
  repeat (f_contractive || f_equiv); try apply Hcascade.
Qed.
Definition cascade_def : val -d> list val -d> iPropO Σ :=
  fixpoint (cascade_pre).
Definition cascade_aux : seal cascade_def. Proof. by eexists. Qed.
Definition cascade := cascade_aux.(unseal).
Definition cascade_eq : cascade = cascade_def := cascade_aux.(seal_eq).
Global Lemma cascade_unfold k us : cascade k us ⊣⊢ cascade_pre cascade k us.
Proof.
  rewrite cascade_eq /cascade_def.
  by apply (fixpoint_unfold cascade_pre).
Qed.


(** Protocol. *)

(* The protocol [Ψ_seq] is used in the verification of [invert]. It describes
   the interaction between the computation [iter yield] and its handler. *)

Definition Ψ_seq I : iEff Σ :=
  (>> us u >> 
    !  u  {{ I  us         ∗ permitted (us ++ [u]) }};
    ? #() {{ I (us ++ [u])                         }}).

(** Verification. *)

(* Camera setup. *)

Context `{!inG Σ (excl_authR (leibnizO (list val)))}.

Definition handler_state γ us : iProp Σ := own γ (●E (us : ofe_car (leibnizO (list val)))).
Definition  client_state γ us : iProp Σ := own γ (◯E (us : ofe_car (leibnizO (list val)))).

(* Ghost theory. *)

Lemma ghost_state_alloc us : ⊢ (|==> ∃ γ, handler_state γ us ∗ client_state γ us)%I.
Proof.
  iMod (own_alloc ((●E (us : ofe_car (leibnizO (list val)))) ⋅
                   (◯E (us : ofe_car (leibnizO (list val)))))) as (γ) "[??]";
  [ apply excl_auth_valid | eauto with iFrame ]; done.
Qed.
Lemma ghost_state_agree γ us vs : handler_state γ us -∗ client_state γ vs -∗ ⌜ us = vs ⌝.
Proof.
  iIntros "Hγ● Hγ◯".
  by iDestruct (own_valid_2 with "Hγ● Hγ◯") as %?%excl_auth_agree_L.
Qed.
Lemma ghost_var_update γ ws us vs :
  handler_state γ us -∗ client_state γ vs ==∗ handler_state γ ws  ∗ client_state γ ws.
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (●E (ws : ofe_car (leibnizO (list val))) ⋅
                            ◯E (ws : ofe_car (leibnizO (list val))))
    with "Hγ● Hγ◯") as "[$$]";
  [ apply excl_auth_update |]; done.
Qed.

(* Correctness of the handler. *)

Lemma invert_handler E γ us :
  handler_state γ us -∗
    deep_handler E (λ: "u" "k", SOME ("u", "k"))%V (λ: <>, NONEV)%V
     (* Ψ  *) (Ψ_seq (client_state γ))
     (* Ψ' *) ⊥
     (* Φ  *) (λ _, ∃ vs, S ∗ client_state γ vs ∗ complete vs)
     (* Φ' *) (λ y , match y with
               | NONEV        => complete   us         ∗ S
               | SOMEV (u, k) => permitted (us ++ [u]) ∗ cascade k (us ++ [u])
               | _ => False
               end)%I.
Proof.
  iLöb as "IH" forall (us γ).
  rewrite !deep_handler_unfold /deep_handler_eq.
  iIntros "Hhstate". iSplit.
  - iIntros (v) "HΦ". iDestruct "HΦ" as (vs) "(HS & Hcstate & Hcomplete)".
    iDestruct (ghost_state_agree with "Hhstate Hcstate") as "<-". iNext.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply ewp_value. by iFrame.
  - iIntros (u k) "Hhandler". iNext.
    rewrite /(Ψ_seq (client_state γ)).
    rewrite (protocol_agreement_tele' [tele _ _] [tele]) //=.
    iApply fupd_ewp.
    iDestruct "Hhandler" as (us' u') "(<- & [Hcstate Hpermitted] & Hk)".
    iDestruct (ghost_state_agree with "Hhstate Hcstate") as "%".
    rewrite -H. clear H.
    iMod (ghost_var_update _ (us ++ [u]) with "Hhstate Hcstate") as "[Hhstate Hcstate]".
    iSpecialize ("Hk" with "Hcstate"). iModIntro.
    iApply (Ectxi_ewp_bind (AppLCtx _)). reflexivity.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind InjRCtx). reflexivity.
    iApply ewp_pure_step. apply pure_prim_step_pair.
    iApply ewp_value. simpl.
    iApply ewp_pure_step'. apply pure_prim_step_InjR.
    iApply ewp_value. simpl. iNext.
    rewrite !cascade_unfold /cascade_pre.
    iFrame. iSpecialize ("IH" with "Hhstate").
    iSpecialize ("Hk" with "IH"). iApply (ewp_strong_mono with "Hk").
    done. iApply iEff_le_refl.
    iIntros (v). simpl.
    destruct v; try naive_solver.
    destruct v; try naive_solver.
    iIntros "[HP Hcascade]". iModIntro. by iFrame.
Qed.

(* Spec and proof of [invert]. *)

Lemma invert_spec :
  S -∗ EWP invert iter {{ k, cascade k [] }}.
Proof.
  iIntros "HS". unfold invert.
  iApply fupd_ewp. iMod (ghost_state_alloc []) as (γ) "[Hhstate Hcstate]". iModIntro.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  rewrite !cascade_unfold cascade_eq.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (ewp_mono with "[HS Hhstate Hcstate]"); [|
  iApply (ewp_deep_try_with with "[HS Hcstate]"); [|
  iApply (invert_handler with "Hhstate") ]].
  - iIntros (v). simpl. rewrite cascade_eq.
    destruct v; try naive_solver.
    destruct v; try naive_solver.
    iIntros "[HP Hcascade]". iModIntro. by iFrame.
  - iApply (ewp_mono with "[HS Hcstate]"); [|
    iApply (iter_spec _ (client_state γ) (Ψ_seq _)
               (λ: "x", do: "x")%V with "[] HS Hcstate") ].
    + simpl. iIntros (_) "H". iModIntro.
      iDestruct "H" as (vs) "(HS & Hcstate & Hcomplete)".
      iExists vs. by iFrame.
    + iModIntro. iIntros (us u) "Hpermitted HS' Hcstate".
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply ewp_pure_step. apply pure_prim_step_do. simpl.
      iApply ewp_eff. rewrite /Ψ_seq.
      rewrite (protocol_agreement_tele' [tele _ _] [tele]) //=.
      iExists us, u. iFrame. iSplit; [done|].
      iIntros "Hcstate". iModIntro. iApply ewp_value. by iFrame.
Qed.

End invert.
