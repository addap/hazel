From iris.proofmode      Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat.
From iris.program_logic  Require Import weakestpre adequacy.
From hazel               Require Import notation weakestpre heap.

Lemma ewp_imp_wp `{!irisG eff_lang Σ} e Φ :
 EWP e <| ⊥ |> {{ v, Φ v }} ⊢ WP e @ NotStuck; ⊤ {{ Φ }}.
Proof.
  iLöb as "IH" forall (e).
  destruct (to_val e) as [ v    |] eqn:?; [|
  destruct (to_eff e) as [(v, k)|] eqn:?  ].
  - rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo. by auto.
  - rewrite -(of_to_eff _ _ _ Heqo0).
    iIntros "Hewp".
    iPoseProof (ewp_eff_inv with "Hewp") as "HFalse".
    by rewrite protocol_agreement_bottom.
  - rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo Heqo0.
    iIntros "Hewp" (σ k ks n) "Hs".
    iMod ("Hewp" with "Hs") as "[$ H]". iModIntro.
    iIntros (e2 σ2 efs).
    case k as [|??]; case efs as [|??]; iIntros (Hstep); try done.
    iMod ("H" with "[//]") as "H". iIntros "!> !>". iMod "H" as "[$ H]".
    iModIntro. by iSplitL; [iApply "IH"|].
Qed.

Section adequacy.
  Context `{!heapPreG Σ}.

  Lemma eff_heap_adequacy s e σ φ :
    (∀ `{!heapG Σ}, ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
    adequate s e σ (λ v _, φ v).
  Proof.
    intros Hwp; eapply (wp_adequacy _ _); iIntros (??) "".
    iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
    iMod (inv_heap_init loc val) as (?) ">Hi".
    iModIntro. iExists
      (λ σ κs, gen_heap_interp σ.(heap)),
      (λ _, True%I).
    iFrame. iApply (Hwp (HeapG _ _ _ _)).
  Qed.

  Lemma eff_adequacy e σ φ :
    (∀ `{!heapG Σ}, ⊢ EWP e <| ⊥ |> {{ v, ⌜φ v⌝ }}) →
    adequate NotStuck e σ (λ v _, φ v).
  Proof.
    intros Hwp.
    apply eff_heap_adequacy.
    intros.
    iApply ewp_imp_wp. iApply Hwp.
  Qed.

  Lemma eff_adequate_not_stuck e σ Φ :
  (∀ `{!heapG Σ}, ⊢ EWP e <| ⊥ |> {{ Φ }}) →
  ∀ e' σ', rtc erased_step ([e], σ) ([e'], σ') →
            not_stuck e' σ'.
  Proof.
    intros Hewp ?? Hstep.
    assert (adequate NotStuck e σ (λ _ _, True)) as Hadequate.
    { apply eff_adequacy.
      intros.
      iApply ewp_mono'; [ iApply Hewp | ].
      by iIntros (?) "_". }
    eapply adequate_alt in Hadequate as [_ Hnot_stuck]; eauto.
    apply Hnot_stuck; auto.
    set_solver.
  Qed.
End adequacy.
