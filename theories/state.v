(* state.v

   In this theory, we study the encoding of a single mutable cell using handlers
   in parameter passing style.
*)

From stdpp               Require Import list.
From iris.proofmode      Require Import base tactics classes.
From iris.algebra        Require Import excl_auth.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation ieff
                                        protocol_agreement
                                        weakestpre deep_handler.

Section state_eff.

Context `{!irisG eff_lang Σ}.


(** Effect markers. *)

Definition read  : val → val := InjLV.
Definition write : val → val := InjRV.


(** Handler. *)

(* The function [run] takes a program [main] that performs the effects
   [read] and [write] to manipulate the state of a mutable cell initialized
   with [init]. Its job is to handle the eventual requests sent by [main] during
   its execution.
*)


Definition run : val := λ: "main" "init",
  let: "comp" :=
    try: "main" #() with
      effect λ: "v" "k", match: "v" with
        (* Read. *)
          InjL <>  => λ: "v",
            let: "comp" := "k" "v" in "comp" "v"
        (* Write. *)
        | InjR "w" => λ: <> ,
            let: "comp" := "k" #() in "comp" "w"
        end
    | return λ: "v" <>, "v"
    end
  in
  "comp" "init".


(** Protocol. *)

(* The interaction between [main] and [run] is arrenged by the protocol [Ψ_state]. *)

Definition Ψ_read  I : iEff Σ := (read  #> (>> v   >> ! #() {{ I v }}; ? (v) {{ I v }})).
Definition Ψ_write I : iEff Σ := (write #> (>> v w >> ! (w) {{ I v }}; ? #() {{ I w }})).
Definition Ψ_state I : iEff Σ := (Ψ_read I <+> Ψ_write I)%ieff.

Lemma Ψ_state_agreement E v Φ' I :
  protocol_agreement E v (Ψ_state I) Φ' ⊢
    ((protocol_agreement E v (Ψ_read I) Φ') ∨ (protocol_agreement E v (Ψ_write I) Φ')).
Proof.
  iIntros "Hprot_agr".
  iDestruct (protocol_agreement_sum_elim with "Hprot_agr") as "[H|H]"; by eauto.
Qed.
Lemma Ψ_read_agreement E u Φ' I :
  protocol_agreement E u (Ψ_read I) Φ' ≡
    (|={E,∅}=> ∃ v, ⌜ u = read #() ⌝ ∗ I v ∗ (I v ={∅,E}=∗ Φ' v))%I.
Proof.
  rewrite /Ψ_read (iEff_marker_tele' [tele _] [tele]).
  rewrite (protocol_agreement_tele' [tele _] [tele]). by auto.
Qed.
Lemma Ψ_write_agreement E u Φ' I :
  protocol_agreement E u (Ψ_write I) Φ' ≡
    (|={E,∅}=> ∃ v w, ⌜ u = write w ⌝ ∗ I v ∗ (I w ={∅,E}=∗ Φ' #()))%I.
Proof.
  rewrite /Ψ_write (iEff_marker_tele' [tele _ _] [tele]).
  rewrite (protocol_agreement_tele' [tele _ _] [tele]). by auto.
Qed.


(** Verification. *)

(* Camera setup. *)

Context `{!inG Σ (excl_authR (leibnizO val))}.

Definition state     γ v := own γ (●E (v : ofe_car (leibnizO val))).
Definition points_to γ v := own γ (◯E (v : ofe_car (leibnizO val))).

(* Ghost theory. *)

Lemma ghost_var_alloc v : ⊢ (|==> ∃ γ, state γ v ∗ points_to γ v)%I.
Proof.
  iMod (own_alloc ((●E (v : ofe_car (leibnizO val))) ⋅
                   (◯E (v : ofe_car (leibnizO val))))) as (γ) "[??]";
  [ apply excl_auth_valid | eauto with iFrame ]; done.
Qed.
Lemma ghost_var_agree γ v w : ⊢ (state γ v ∗ points_to γ w) → ⌜ v = w ⌝.
Proof.
  iIntros "[H● H◯]".
  by iDestruct (own_valid_2 with "H● H◯") as %?%excl_auth_agreeL.
Qed.
Lemma ghost_var_update γ w u v :
  state γ u -∗ points_to γ v ==∗ state γ w  ∗ points_to γ w.
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (●E (w : ofe_car (leibnizO val)) ⋅
                            ◯E (w : ofe_car (leibnizO val)))
    with "Hγ● Hγ◯") as "[$$]";
  [ apply excl_auth_update | ]; done.
Qed.

(* Spec and proof. *)

Lemma run_spec Φ (init main : val) :
  (∀ I, I init -∗ EWP main #() <| Ψ_state I |> {{ v, Φ v }})
  -∗
  EWP run main init {{ v, Φ v }}.
Proof.
  unfold run.
  iIntros "Hspec". iApply fupd_ewp.
  iMod (ghost_var_alloc init) as (γ) "[Hstate Hpoints_to]". iModIntro.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  iApply (ewp_bind (ConsCtx (AppLCtx _)
                   (ConsCtx (AppRCtx _) EmptyCtx))). done.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  iSpecialize ("Hspec" with "Hpoints_to").
  iApply ewp_mono; [|
  iApply (ewp_deep_try_with _ _ _ _ (
         (λ comp, EWP comp init {{ v, Φ v }}))%I with "Hspec") ].
  + iIntros (v) "Hspec". simpl.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. done.
  + iLöb as "IH" forall (γ init).
    rewrite !deep_handler_unfold. iSplit.
    - iIntros (v) "HP". iNext.
      iApply ewp_pure_step. apply pure_prim_step_beta.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      by iApply ewp_value.
    - iIntros (v k) "Hprot_agr".
      iDestruct (Ψ_state_agreement with "Hprot_agr") as "[Hread|Hwrite]".
      { (* Read. *)
        rewrite Ψ_read_agreement.
        iNext. iApply fupd_ewp. iMod "Hread" as (w) "(-> & Hpoints_to & Hk)".
        iDestruct (ghost_var_agree γ init w with "[$]") as "%". rewrite H.
        iSpecialize ("Hk" with "Hpoints_to"). iMod "Hk". iModIntro.
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step'. apply pure_prim_step_beta. simpl.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value.
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        iApply ewp_pure_step. apply pure_prim_step_case_InjL.
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value. simpl.
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value. simpl.
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        iApply (Ectxi_ewp_bind (AppRCtx _)). done.
        iNext. iSpecialize ("IH" with "Hstate").
        iSpecialize ("Hk" with "IH"). simpl.
        iApply (ewp_mono with "Hk").
        iIntros (v') "H". iModIntro.
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value. simpl.
        iApply ewp_pure_step. apply pure_prim_step_beta. done. }
      { (* Write. *)
        rewrite Ψ_write_agreement.
        iNext. iApply fupd_ewp.
        iMod "Hwrite" as (v' w') "(-> & Hpoints_to & Hk)".
        iMod ((ghost_var_update _ w') with "Hstate Hpoints_to") as
          "[Hstate Hpoints_to]".
        iSpecialize ("Hk" with "Hpoints_to"). iMod "Hk". iModIntro.
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step'. apply pure_prim_step_beta. simpl.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value.
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        iApply ewp_pure_step. apply pure_prim_step_case_InjR.
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value. simpl.
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value. simpl.
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        iApply (Ectxi_ewp_bind (AppRCtx _)). done.
        iNext. iSpecialize ("IH" with "Hstate").
        iSpecialize ("Hk" with "IH"). simpl.
        iApply (ewp_mono with "Hk").
        iIntros (u) "H". iModIntro.
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value. simpl.
        iApply ewp_pure_step. apply pure_prim_step_beta. done. }
Qed.

End state_eff.
