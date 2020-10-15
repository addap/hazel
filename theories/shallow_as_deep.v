(* shallow_handler.v

   Here we show that it is possible to correctly implement
   a shallow handler using a deep handler as the sole
   mechanism for catching effects. The implementation is correct
   in the sense that it satisfies the same specification
   as the primitive "try-with" instruction of the language
   called [TryWith].
*)

From stdpp               Require Import list.
From iris.proofmode      Require Import base tactics classes.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation weakestpre
                                        shallow_handler deep_handler.

Definition eff_tree_split : val := λ: "e",
  try: "e" #() with
    effect (λ: "v" "k",
      let: "k" := λ: "w",
        match: "k" "w" with
          InjL "p" => (Snd "p") (eff: (Fst "p"))
        | InjR "v" => "v"
        end
      in
      InjL ("v", "k"))%V
  | return (λ: "v",
      InjR "v")%V
  end.

Definition shallow_try_with : val := λ: "e" "h" "r",
  match: (eff_tree_split "e") with
    (* effect: *)  InjL "p" => "h" (Fst "p") (Snd "p")
  | (* return: *)  InjR "v" => "r" "v"
  end.

Section shallow_handler.
Context `{!heapG Σ}.

Lemma eff_tree_split_spec E Ψ Φ (e : val) :
  EWP e #() @ E <| Ψ |> {{ Φ }} ⊢
    EWP (eff_tree_split e) @ E {{ y,
      match y with
      | InjRV  v     => Φ v
      | InjLV (v, k) =>
          protocol_agreement E v Ψ (λ w,
            ▷ EWP k w @ E <| Ψ |> {{ Φ }})
      | _            => False
      end%I }}.
Proof.
  unfold eff_tree_split.
  iIntros "e_spec".
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (ewp_deep_try_with with "e_spec").
  iLöb as "IH" forall (Ψ).
  rewrite !deep_handler_unfold /deep_handler_pre; iSplit.
  - iIntros (v) "H". iNext.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply ewp_pure_step. apply pure_prim_step_InjR.
    by iApply ewp_value.
  - iIntros (v k) "H". iNext.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (AppRCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind InjLCtx). done.
    iApply ewp_pure_step. apply pure_prim_step_pair.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_InjL.
    iApply ewp_value. simpl.
    iApply (protocol_agreement_strong_mono with "H"); try done.
    iApply iEff_le_refl.
    iIntros (u) "H". iModIntro. iNext.
    iSpecialize ("IH" $! Ψ). iSpecialize ("H" with "IH").
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (CaseCtx _ _)). done.
    iApply (ewp_strong_mono with "H"); try done.
    iApply iEff_le_bottom. clear u. iIntros (u) "H".
    case u; try naive_solver.
    + intros w. case w; try naive_solver.
      iIntros (v' k'). iModIntro.
      iApply ewp_pure_step. apply pure_prim_step_case_InjL.
      iApply (Ectxi_ewp_bind (AppLCtx _ )). done.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _ )). done.
      iApply (Ectxi_ewp_bind (EffCtx _ )). done.
      iApply ewp_pure_step. apply pure_prim_step_Fst.
      iApply ewp_value. iApply ewp_eff. 
      iApply (protocol_agreement_strong_mono with "H"); try done.
      iApply iEff_le_refl.
      iIntros (w') "HQ'". iModIntro. iNext.
      iApply ewp_value. simpl.
      iApply (Ectxi_ewp_bind (AppLCtx _ )). done.
      iApply ewp_pure_step. apply pure_prim_step_Snd.
      by iApply ewp_value.
    + iIntros (v'). iModIntro.
      iApply ewp_pure_step. apply pure_prim_step_case_InjR.
      iApply (Ectxi_ewp_bind (AppLCtx _ )). done.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      by iApply ewp_value.
Qed.

Lemma ewp_shallow_try_with E Ψ Ψ' Φ Φ' (e : expr) (h r : val) :
  EWP e @ E <| Ψ |> {{ Φ }} -∗ shallow_handler E h r Ψ Ψ Ψ' Φ Φ' -∗
  EWP (shallow_try_with (λ: <>, e) h r) @ E <| Ψ' |> {{ Φ' }}.
Proof.
  unfold shallow_try_with.
  iIntros "He Hhandler".
  iApply (Ectxi_ewp_bind (AppLCtx _)); try done.
  iApply (Ectxi_ewp_bind (AppLCtx _)); try done.
  iApply (Ectxi_ewp_bind (AppRCtx _)); try done.
  iApply ewp_pure_step; try by apply pure_prim_step_rec; simpl.
  iApply ewp_value; simpl.
  iApply ewp_pure_step; try by apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step; try by apply pure_prim_step_rec; simpl.
  iApply ewp_value; simpl.
  iApply ewp_pure_step; try by apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step; try by apply pure_prim_step_rec; simpl.
  iApply ewp_value; simpl.
  iApply ewp_pure_step; try by apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (CaseCtx _ _)); try done.
  iApply (ewp_strong_mono E _ ⊥%ieff with "[He] [] [Hhandler]"); try done.
  - iApply eff_tree_split_spec.
    iApply ewp_pure_step; try by apply pure_prim_step_beta. simpl.
    by iApply "He".
  - iApply iEff_le_bottom.
  - iIntros (v) "H". case v; try naive_solver.
    + iIntros (v0); case v0; try naive_solver.
      intros v' k. simpl.
      iModIntro.
      iApply ewp_pure_step'. apply pure_prim_step_case_InjL. iNext.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_Snd.
      iApply ewp_value. simpl.
      iApply (ewp_bind (ConsCtx (AppLCtx _) (
                        ConsCtx (AppRCtx _) EmptyCtx))). done.
      iApply ewp_pure_step'. apply pure_prim_step_Fst.
      iApply ewp_value.
      rewrite /shallow_handler /shallow_effect_handler //=.
      iDestruct "Hhandler" as "[_ Hh]". by iApply "Hh".
    + iIntros (u). simpl. iModIntro.
      iDestruct "Hhandler" as "[Hhandler _]".
      iSpecialize ("Hhandler" with "H").
      iApply ewp_pure_step'. apply pure_prim_step_case_InjR. iNext.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value. simpl.
      by iApply ewp_pure_step; first apply pure_prim_step_beta.
Qed.

End shallow_handler.
