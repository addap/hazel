(* selective_handler.v

*)

From stdpp               Require Import list.
From iris.proofmode      Require Import base tactics classes.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation weakestpre shallow_handler deep_handler.


(** * Selective Handler. *)

(* Program definition. *)

Definition selective_try_with : val := λ: "f" "e" "h" "r",
  try: "e" #() with
    effect (λ: "v" "k",
      if: "f" "v" then "h" "v" "k" else "k" (do: "v"))
  | return "r"
  end.

(** * Reasoning Rules. *)

Section selective_handler.
Context `{!heapG Σ}.

(* Selective handler judgement. *)

Definition selective_handler_pre :
  (coPset -d> expr -d> expr -d> (val → Prop) -d>
        iEff Σ -d> iEff Σ -d> (val -d> iPropO Σ) -d> (val -d> iPropO Σ) -d> iPropO Σ) →
  (coPset -d> expr -d> expr -d> (val → Prop) -d>
        iEff Σ -d> iEff Σ -d> (val -d> iPropO Σ) -d> (val -d> iPropO Σ) -d> iPropO Σ)
  := λ selective_handler E h r P Ψ Ψ' Φ Φ',
  ((shallow_return_handler E r Ψ' Φ Φ') ∧

   (∀ v k,
     protocol_agreement v (P ?> Ψ) (λ w, ∀ Ψ'' Φ'',
       ( ▷ selective_handler E h r P Ψ Ψ'' Φ Φ'' -∗
         EWP (Val k) (Val w) @ E <| Ψ'' |> {{ Φ'' }})) -∗
     ▷ EWP App (App h (Val v)) (Val k) @ E <| Ψ' |> {{ Φ' }}) ∧

   (∀ v k,
     protocol_agreement v ((λ v, ¬ P v : Prop) ?> Ψ) (λ w, ∀ Ψ'' Φ'',
       ( ▷ selective_handler E h r P Ψ Ψ'' Φ Φ'' -∗
         EWP (Val k) (Val w) @ E <| Ψ'' |> {{ Φ'' }})) -∗
     ▷ protocol_agreement v Ψ' (λ w,
         EWP (Val k) (Val w) @ E <| Ψ' |> {{ Φ' }})))%I.
Arguments selective_handler_pre _ _%E _%E _ _%ieff _%ieff _%I _%I.

Local Instance selective_handler_pre_contractive : Contractive selective_handler_pre.
Proof.
  rewrite /selective_handler_pre => n hanlder handler' Hhandler E h r P Ψ Ψ' Φ Φ'.
  repeat (f_contractive || f_equiv); intros ?; simpl;
  repeat (f_contractive || f_equiv); apply Hhandler.
Qed.
Definition selective_handler_def := fixpoint selective_handler_pre.
Definition selective_handler_aux : seal selective_handler_def. Proof. by eexists. Qed.
Definition selective_handler := selective_handler_aux.(unseal).
Definition selective_handler_eq : selective_handler = selective_handler_def
  := selective_handler_aux.(seal_eq).
Arguments selective_handler _ _%E _%E _ _%ieff _%ieff _%I _%I.

Global Lemma selective_handler_unfold E h r P Ψ Ψ' Φ Φ' :
  selective_handler E h r P Ψ Ψ' Φ Φ' ⊣⊢
  selective_handler_pre selective_handler E h r P Ψ Ψ' Φ Φ'.
Proof.
  rewrite selective_handler_eq /selective_handler_def.
  by apply (fixpoint_unfold selective_handler_pre).
Qed.

Global Instance selective_handler_ne E h r P n :
  Proper
    ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n))
  (selective_handler E h r P).
Proof.
  induction (lt_wf n) as [n _ IH]=> Ψ1 Ψ2 HΨ Ψ'1 Ψ'2 HΨ' Φ1 Φ2 HΦ Φ'1 Φ'2 HΦ'.
  rewrite !selective_handler_unfold /selective_handler_pre.
  repeat (apply protocol_agreement_ne||apply ewp_ne||f_contractive||f_equiv);
  try done; try (eapply dist_le; eauto with lia).
  intros ?. do 2 (f_equiv=>?). f_equiv. f_contractive.
  apply IH; try lia; eapply dist_le; eauto with lia.
  intros ?. do 2 (f_equiv=>?). f_equiv. f_contractive.
  apply IH; try lia; eapply dist_le; eauto with lia.
  intros ?. f_equiv; eapply dist_le; eauto with lia.
Qed.
Global Instance selective_handler_proper E h r P :
  Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) (selective_handler E h r P).
Proof.
  intros ??? ??? ??? ???.
  apply equiv_dist=>n. apply selective_handler_ne; apply equiv_dist; done.
Qed.


(* Selective handler reasoning rule. *)

Lemma ewp_selective_try_with P `{!∀ x, Decision (P x)}
  E Ψ Ψ' Φ Φ' (f : val) (e : expr) (h r : val) :
  EWP e @ E <| Ψ |> {{ Φ }}
    -∗
      □ (∀ x, EWP f x @ E {{ λ y, ⌜ y = #(bool_decide (P x)) ⌝ }} )
        -∗
          selective_handler E h r P Ψ Ψ' Φ Φ'
 -∗
   EWP (selective_try_with f (λ: <>, e) h r) @ E <| Ψ' |> {{ Φ' }}.
Proof.
  iIntros "He #f_spec Hhandler".  
  unfold selective_try_with.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppRCtx _) EmptyCtx))). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply (ewp_deep_try_with with "[He] [Hhandler]").
  { iApply ewp_pure_step. apply pure_prim_step_beta. simpl. by iApply "He". }
  { iLöb as "IH" forall (Ψ Ψ' Φ Φ').
    rewrite deep_handler_unfold selective_handler_unfold.
    iSplit; [by iDestruct "Hhandler" as "[H _]"|].
    iIntros (v k) "Hprot". iNext.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (IfCtx _ _)). done.
    iApply (ewp_strong_mono with "f_spec"); [done|iApply iEff_le_bottom|].
    iIntros (b) "->". iModIntro. simpl.
    case_eq (bool_decide (P v)); intro HP;
    iApply ewp_pure_step'; try apply pure_prim_step_if.
    { iDestruct "Hhandler" as "[_ [Hh _]]". iApply "Hh".
      rewrite protocol_agreement_filter. iSplit; [
      iPureIntro; apply (bool_decide_eq_true_1 (P v) HP) |].
      iApply (protocol_agreement_strong_mono with "Hprot").
      { by iApply iEff_le_refl. }
      { iIntros (v') "Hk".  iIntros (Ψ'' Φ'') "Hhandler".
        iApply "Hk". by iApply "IH".
      }
    }
    { iDestruct "Hhandler" as "[_ [_ Hk]]".
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_do.
      iApply ewp_eff. iSpecialize ("Hk" with "[Hprot]").
      { rewrite protocol_agreement_filter.  iSplit; [
        iPureIntro; apply (bool_decide_eq_false_1 (P v) HP) |].
        iApply (protocol_agreement_strong_mono with "Hprot").
        { by iApply iEff_le_refl. }
        { iIntros (v') "Hk".  iIntros (Ψ'' Φ'') "Hhandler".
          iApply "Hk". by iApply "IH".
        }
      }
      iNext. iApply (protocol_agreement_mono with "Hk").
      iIntros (v') "Hk". iNext. by iApply ewp_value.
    }
  }
Qed.

End selective_handler.
