(* shift_reset.v *)

(* This file proposes reasoning rules for the delimited-control
   operators [shift0] and [reset0], which are introduced in [HH]
   as derived constructs.
*)

From iris.proofmode      Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic  Require Import weakestpre.

From hazel Require Import lang notation weakestpre.
From hazel Require Export deep_handler heap tactics.


(** Implementation. *)

(*
    reset0 K[shift0 t] -> t (λ w. reset0 K[w])  (reset0 ∉ K)
*)

Section implementation.

  Definition reset0 (e : expr) : expr :=
    try: e with effect (λ: "t" "k", "t" "k")%V | return (λ: "y", "y")%V end.

  Definition shift0 (b : binder) (e : expr) : expr :=
    do: (Lam b e).

End implementation.


(** Specification. *)

Section specification.

  Section definitions.
    Context `{!irisGS eff_lang Σ}.

    Definition is_shift (Ψ : iEff Σ) (Φ Q : val → iPropO Σ) (t : val) : iProp Σ :=
      ∀ (k : val), (∀ w, Q w -∗ EWP k w <|Ψ|> {{Φ}}) -∗ EWP t k <|Ψ|> {{Φ}}.

    Definition SHIFT0 Ψ Φ : iEff Σ :=
      >> t Q >> !(t) {{ is_shift Ψ Φ Q t }};
      << w   << ?(w) {{ Q w }}.

    Lemma SHIFT0_agreement Ψ Φ v Φ' :
      protocol_agreement v (SHIFT0 Ψ Φ) Φ' ≡
        (∃ t Q,
           ⌜ v = t ⌝ ∗ is_shift Ψ Φ Q t ∗
           (∀ (w : val), Q w -∗ Φ' w))%I.
    Proof. by rewrite (protocol_agreement_tele' [tele _ _] [tele _]) //. Qed.

  End definitions.

  Section reasoning_rules.
    Context `{!irisGS eff_lang Σ}.

    Definition reset0_spec (e : expr) (Ψ : iEff Σ) (Φ : val → iProp Σ) : Prop :=
      ⊢ EWP e <|SHIFT0 Ψ Φ|> {{Φ}} -∗
          EWP reset0 e <|Ψ|> {{Φ}}.

    Definition shift0_spec (b : binder) (e : expr) (Ψ : iEff Σ) (Φ Q : val → iProp Σ) : Prop :=
      ⊢ is_shift Ψ Φ Q (LamV b e) -∗
          EWP shift0 b e <|SHIFT0 Ψ Φ|> {{Q}}.

  End reasoning_rules.

End specification.

Section verification.
  Context `{!heapG Σ}.

  Lemma ewp_reset0 e Ψ Φ : reset0_spec e Ψ Φ.
  Proof.
    iIntros "He". unfold reset0.
    iApply (ewp_deep_try_with with "He").
    iLöb as "IH".
    rewrite {-1}deep_handler_unfold.
    iSplit. { by iIntros (y) "Hy !>"; ewp_pure_steps. }
    iIntros (v k) "Hprot !>".
    rewrite SHIFT0_agreement.
    iDestruct "Hprot" as (t Q) "[-> [Hshift Hk]]".
    ewp_pure_steps.
    iApply "Hshift".
    iIntros (w) "Hw".
    by iApply ("Hk" with "Hw").
  Qed.

  Lemma ewp_shift0 b e Ψ Φ Q : shift0_spec b e Ψ Φ Q.
  Proof.
    iIntros "Hshift". unfold shift0. ewp_pure_steps.
    iApply ewp_eff. rewrite SHIFT0_agreement.
    iExists (LamV b e), Q. iSplit; [done|]. iFrame.
    iIntros (w) "Hw". by ewp_pure_steps.
  Qed.

End verification.
