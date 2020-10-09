From iris.proofmode      Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation ieff weakestpre
                                        protocol_agreement.

Section adequacy.
Context `{!irisG eff_lang Σ}.

Lemma ewp_imp_wp e Φ :
 EWP e <| ⊥ |> {{ v, Φ v }} ⊢ WP e @ NotStuck; ⊤ {{ Φ }}.
Proof.
  iLöb as "IH" forall (e).
  destruct (to_val e) as [ v    |] eqn:?; [|
  destruct (to_eff e) as [(v, k)|] eqn:?  ].
  - rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo. by auto.
  - rewrite -(of_to_eff _ _ _ Heqo0).
    iIntros "Hewp".
    iPoseProof (ewp_eff_inv with "Hewp") as "HFalse".
    rewrite protocol_agreement_bottom. iApply fupd_wp. by iMod "HFalse".
  - rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo Heqo0.
    iIntros "Hewp" (σ k ks n) "Hs".
    iMod ("Hewp" with "Hs") as "[$ H]". iModIntro.
    iIntros (e2 σ2 efs).
    case k as [|??]; case efs as [|??]; iIntros (Hstep); try done.
    iMod ("H" with "[//]") as "H". iIntros "!> !>". iMod "H" as "[$ H]".
    iModIntro. by iSplitL; [iApply "IH"|].
Qed.

End adequacy.

