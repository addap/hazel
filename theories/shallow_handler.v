(* shallow_handler.v
*)

From iris.proofmode      Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation weakestpre.
From hazel               Require Export heap.

Section shallow_handler.
Context `{!heapG Σ}.

(** * Shallow Handlers. *)

(* Return clause judgement. *)

Definition shallow_return_handler E r Ψ' (Φ Φ' : _ -d> _) :=
  (∀ v, Φ v -∗ ▷ EWP (App r (Val v)) @ E <| Ψ' |> {{ Φ' }})%I.
Arguments shallow_return_handler _ _%E _%ieff _%I _%I.

Global Instance shallow_return_handler_ne E r n :
  Proper
    ((dist n) ==> (dist n) ==> (dist n) ==> (dist n))
  (shallow_return_handler E r).
Proof.
  intros ?????????. rewrite /shallow_return_handler.
  f_equiv=>v. f_equiv. done. by solve_proper.
Qed.
Global Instance is_shallow_return_proper E h :
  Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (shallow_return_handler E h).
Proof.
  intros ?????????. apply equiv_dist=>n;
  apply shallow_return_handler_ne; by apply equiv_dist.
Qed.

(* Effect clause judgement. *)

Definition shallow_effect_handler E h Ψ_eff Ψ Ψ' (Φ Φ' : _ -d> _) :=
  (∀ v k,
    protocol_agreement v Ψ_eff (λ w,
        EWP App (Val k) (Val w) @ E <| Ψ |> {{ Φ }}) -∗
    ▷ EWP App (App h (Val v)) (Val k) @ E <| Ψ' |> {{ Φ' }})%I.
Arguments shallow_effect_handler _ _%E _%ieff _%ieff _%ieff _%I _%I.

Global Instance shallow_effect_handler_ne E h n :
  Proper
    ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n))
  (shallow_effect_handler E h).
Proof.
  intros ??? ??? ??? ??? ???. rewrite /shallow_effect_handler /protocol_agreement.
  by repeat (apply H || solve_proper || f_equiv).
Qed.
Global Instance is_shallow_handler_proper E h :
  Proper
    ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡))
  (shallow_effect_handler E h).
Proof.
  intros ??? ??? ??? ??? ???. apply equiv_dist=>n;
  apply shallow_effect_handler_ne; by apply equiv_dist.
Qed.

Lemma shallow_effect_handler_bottom E h Ψ Ψ' Φ Φ' :
  ⊢ shallow_effect_handler E h ⊥ Ψ Ψ' Φ Φ'.
Proof. iIntros (v k) "H". by rewrite protocol_agreement_bottom. Qed.

Lemma shallow_effect_handler_marker_elim E f h Ψ_eff Ψ Ψ' Φ Φ' :
  shallow_effect_handler E h (f #> Ψ_eff) Ψ Ψ' Φ Φ' ⊢
    (∀ v k,
      protocol_agreement v Ψ_eff (λ w,
          EWP App (Val k) (Val w) @ E <| Ψ |> {{ Φ }}) -∗
      ▷ EWP App (App h (Val (f v))) (Val k) @ E <| Ψ' |> {{ Φ' }}).
Proof.
  iIntros "Hewp" (v k) "Hprot_agr".
  iApply "Hewp". by iApply protocol_agreement_marker_intro.
Qed.

Lemma shallow_effect_handler_marker_intro E f {Hf: Marker f} h Ψ_eff Ψ Ψ' Φ Φ' :
  (∀ v k,
    protocol_agreement v Ψ_eff (λ w,
        EWP App (Val k) (Val w) @ E <| Ψ |> {{ Φ }}) -∗
    ▷ EWP App (App h (Val (f v))) (Val k) @ E <| Ψ' |> {{ Φ' }}) ⊢
    shallow_effect_handler E h (f #> Ψ_eff) Ψ Ψ' Φ Φ'.
Proof.
  iIntros "Hewp" (v k) "Hprot_agr".
  case (marker_dec_range v) as [(w & Hw)|Hv].
  { inversion Hw. iApply "Hewp".
    by iApply (@protocol_agreement_marker_elim _ f marker_inj). }
  { iNext. iDestruct "Hprot_agr" as (Q) "[HP _]".
    rewrite iEff_marker_eq. iDestruct "HP" as (w) "[-> _]". by case (Hv w). }
Qed.

Lemma shallow_effect_handler_sum_intro E h Ψ1 Ψ2 Ψ Ψ' Φ Φ' :
  ((shallow_effect_handler E h Ψ1 Ψ Ψ' Φ Φ') ∧
   (shallow_effect_handler E h Ψ2 Ψ Ψ' Φ Φ')) ⊢
     shallow_effect_handler E h (Ψ1 <+> Ψ2) Ψ Ψ' Φ Φ'.
Proof.
  iIntros "Hhandler" (v k) "Hprot_agr".
  iDestruct (protocol_agreement_sum_elim with "Hprot_agr") as "[H|H]".
  { iDestruct "Hhandler" as "[Hhandler _]"; by iApply "Hhandler". }
  { iDestruct "Hhandler" as "[_ Hhandler]"; by iApply "Hhandler". }
Qed.

Lemma shallow_effect_handler_sum_elim E h Ψ1 Ψ2 Ψ Ψ' Φ Φ' :
  shallow_effect_handler E h (Ψ1 <+> Ψ2) Ψ Ψ' Φ Φ' ⊢
    (shallow_effect_handler E h Ψ1 Ψ Ψ' Φ Φ') ∧
    (shallow_effect_handler E h Ψ2 Ψ Ψ' Φ Φ').
Proof.
  iIntros "Hhandler". iSplit; iIntros (v k) "Hprot_agr"; iApply "Hhandler".
  { by iApply protocol_agreement_sum_intro_l. }
  { by iApply protocol_agreement_sum_intro_r. }
Qed.

Lemma shallow_effect_handler_strong_mono
  E h Ψ1_eff Ψ2_eff Ψ1 Ψ2 Ψ' Φ1 Φ2 Φ' :
   (shallow_effect_handler E h Ψ2_eff Ψ2 Ψ' Φ2 Φ' -∗
      Ψ1_eff ⊑ Ψ2_eff -∗ Ψ1 ⊑ Ψ2 -∗ (∀ v, Φ1 v ={E}=∗ Φ2 v) -∗
    shallow_effect_handler E h Ψ1_eff Ψ1 Ψ' Φ1 Φ')%ieff.
Proof.
  iIntros "Hhandler #HΨ_eff #HΨ HΦ". iIntros (v k) "Hp".
  iAssert (protocol_agreement v Ψ2_eff (λ w,
              EWP App (Val k) (Val w) @ E <|Ψ2|> {{Φ2}}))%I
  with "[HΦ Hp]" as "Hp".
  { iApply (protocol_agreement_strong_mono with "Hp"); try auto.
    iIntros (w) "Hewp". iApply (ewp_strong_mono with "Hewp"); by auto. }
  iSpecialize ("Hhandler" with "Hp"). iNext.
  iApply (ewp_strong_mono with "Hhandler"); try auto.
  by iApply iEff_le_refl.
Qed.

(* Shallow handler judgement. *)

Definition shallow_handler E h r Ψ_eff Ψ Ψ' (Φ Φ' : _ -d> _) : iProp Σ :=
  (shallow_return_handler E   r         Ψ' Φ Φ') ∧
  (shallow_effect_handler E h   Ψ_eff Ψ Ψ' Φ Φ').
Arguments shallow_handler _ _%E _%E _%ieff _%ieff _%ieff _%I _%I.

Global Instance shallow_handler_ne E h r n :
  Proper
    ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n))
  (shallow_handler E h r).
Proof.
  intros ??? ??? ??? ??? ???. rewrite /shallow_handler.
  f_equiv. solve_proper. by apply shallow_effect_handler_ne.
Qed.
Global Instance shallow_handler_proper E h r :
  Proper
    ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡))
  (shallow_handler E h r).
Proof.
  intros ??? ??? ??? ??? ???.
  apply equiv_dist=>n. apply shallow_handler_ne; apply equiv_dist; done.
Qed.

(* Reasoning rule for [TryWith]: a shallow single-effect handler. *)

Lemma ewp_contv E Ψ Φ k (w : val) l :
  ▷ EWP  fill  k    w @ E <| Ψ |> {{ Φ }} -∗ l ↦ #true -∗
    EWP (ContV k l) w @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros "Hk Hl".
  rewrite !(ewp_unfold _ (App _ _)) /ewp_pre //=.
  iIntros (σ ????) "Hσ".
  iDestruct (gen_heap_valid with "Hσ Hl") as "%".
  rename H into heap_valid.
  iMod (gen_heap_update _ _ _ #false with "Hσ Hl") as "[Hσ Hl]".
  iMod (fupd_mask_subseteq ∅) as "Hclose". by apply empty_subseteq.
  iModIntro. iSplitR.
  - iPureIntro. rewrite /reducible //=.
    exists [], (fill k w), (state_upd_heap <[l:=#false]> σ), []. simpl.
    apply (Ectx_prim_step _ _ _ _ EmptyCtx (ContV k l w) (fill k w)); try done.
    apply ContS; by eauto.
  - iIntros (e₂ σ₂ Hstep).
    destruct κ; [|done]. simpl in Hstep.
    destruct Hstep; destruct K  as [|Ki K]; [| destruct Ki; try naive_solver ].
    + simpl in H, H0. simplify_eq. inversion H1. simplify_eq. iFrame. by auto.
    + simpl in H, H0. destruct K as [|Ki K] ; [| destruct Ki; try naive_solver ].
      simpl in H. inversion H. simplify_eq. by inversion H1.
    + simpl in H, H0. destruct K as [|Ki K] ; [| destruct Ki; try naive_solver ].
      simpl in H. inversion H. simplify_eq. by inversion H1.
Qed.

Lemma ewp_try_with E Ψ Ψ' Φ Φ' e h r :
  EWP          e      @ E <| Ψ  |> {{ Φ  }} -∗ shallow_handler E h r Ψ Ψ Ψ' Φ Φ' -∗
  EWP (TryWith e h r) @ E <| Ψ' |> {{ Φ' }}.
Proof.
  iLöb as "IH" forall (e Ψ).
  destruct (to_val e) as [ v    |] eqn:He; [|
  destruct (to_eff e) as [(v, k)|] eqn:He' ].
  - rewrite <-(of_to_val _ _ He).
    iIntros "HΦ [Hr _]".
    iApply fupd_ewp. iMod (ewp_value_inv with "HΦ") as "HΦ". iModIntro.
    iApply ewp_pure_step'. apply pure_prim_step_try_with_val.
    by iApply ("Hr" with "HΦ").
  - rewrite <-(of_to_eff _ _ _ He').
    iIntros "H Hhandler".
    iDestruct (ewp_eff_inv with "H") as "H".
    iDestruct "Hhandler" as "[_ Hh]".
    rewrite !ewp_unfold /ewp_pre //=.
    iIntros (σ ????) "Hσ".
    iMod (fupd_mask_subseteq ∅) as "Hclose". by apply empty_subseteq.
    iModIntro. iSplitR.
    + iPureIntro. rewrite /reducible //=.
      set (l := fresh_locs (dom (gset loc) σ.(heap))).
      exists [], (h v (ContV k l)), (state_upd_heap <[l:=#true]> σ), []. simpl.
      apply (Ectx_prim_step _ _ _ _ EmptyCtx (TryWith (Eff v k) h r) (h v (ContV k l))).
      done. done. by apply try_with_fresh.
    + iIntros (e₂ σ₂ Hstep).
      destruct κ; [|done]. simpl in Hstep.
      destruct Hstep; destruct K  as [|Ki K]; [| destruct Ki; try naive_solver ].
      * simpl in H, H0. simplify_eq. inversion H1.
        iMod (gen_heap_alloc _ l #true with "Hσ") as "($ & Hl & Hm)". { done. }
        iSpecialize ("Hh" $! v (ContV k l) with "[H Hl]").
        { iApply (protocol_agreement_mono with "H").
          iIntros (w) "Hk". by iApply (ewp_contv with "Hk Hl").
        }
        iIntros "!> !> !>". by iMod "Hclose".
      * destruct (fill_eff' K e1' v k) as [-> ->]; [naive_solver | ];
        simpl in H; simplify_eq; by inversion H1.
  - iIntros "He Hhandler".
    rewrite !(ewp_unfold _ (TryWith _ _ _))
            !(ewp_unfold _ e) /ewp_pre He He' //=.
    iIntros (σ₁ ns k ks nt) "Hs".
    iMod ("He" $! σ₁ ns k ks nt with "Hs") as "[% He]".
    iSplitR.
    + iPureIntro. revert H; unfold reducible. simpl.
      rewrite /prim_step'; simpl.
      destruct 1 as [obs [e₄ [σ₄ [efs Hstep]]]].
      case obs in Hstep; [|done].
      case efs in Hstep; [|done].
      inversion Hstep. simplify_eq.
      exists [], (TryWith (fill K e2') h r), σ₄, [].
      by apply (Ectx_prim_step _ _ _ _ (ConsCtx (TryWithCtx h r) K) e1' e2').
    + iModIntro. iIntros (e₄ σ₄) "%".
      destruct k; [|done]. rename H0 into Hstep. simpl in Hstep.
      assert (Hstep' : ∃ e₅, prim_step e σ₁ e₅ σ₄ ∧ e₄ = TryWith e₅ h r).
      { inversion Hstep. destruct K as [|Ki K].
        - simpl in H; simplify_eq. inversion H2; naive_solver.
        - destruct Ki; try naive_solver. simpl in H0, H1, H2; simplify_eq.
          exists (fill K e2'). simpl. split;[| done].
          by apply (Ectx_prim_step _ _ _ _ K e1' e2').
      }
      destruct Hstep' as [e₅ [Hstep' ->]].
      iDestruct ("He" $! e₅ σ₄ Hstep') as "> He".
      iIntros "!> !>". iMod "He". iModIntro.
      iMod "He" as "[$ He]". iModIntro.
      by iApply ("IH" with "He Hhandler").
Qed.

End shallow_handler.
