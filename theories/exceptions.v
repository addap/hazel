(* exceptions.v

   In this theory, we study the standard example of using effecr handlers
   to encode exceptions.
*)

From iris.proofmode      Require Import base tactics classes.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation weakestpre shallow_handler.

Section exceptions.
Context `{!heapG Σ}.

(** Protocl. *)

(* The protocol for exceptions imposes a restriction over the value that is
   raised: it must satisfy [Ψ]. Moreover, it declares everything that comes
   after as dead code by declaring the postcondition to be [False]. *)

Definition exn (Ψ : val → iProp Σ) : iEff Σ :=
  (>> u >> ! u {{ Ψ u }}; ? #() {{ False }}).


(** Reasoning Rules. *)

(* Raise. *)

Definition raise : val := λ: "u", do: "u".

Lemma ewp_raise E (Φ Ψ : val → iProp Σ) u :
  Ψ u -∗ EWP raise u @ E <| exn Ψ |> {{ v, Φ v }}.
Proof.
  iIntros "H". unfold raise.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_do.
  iApply ewp_eff.
  unfold exn. rewrite (protocol_agreement_tele' [tele _] [tele]) //=.
  iExists u. iFrame. iSplit; [done|]. by iIntros "H".
Qed.


(* Try-With. *)

Lemma ewp_exn_try_with (Φ Ψ : val → iProp Σ) (e₁ : expr) (e₂ e₃ : val) :
  EWP e₁ @ ∅ <| exn (λ v, EWP (e₂ v) @ ∅ <| exn Ψ |> {{ v, Φ v }}) |>
             {{        v, EWP (e₃ v) @ ∅ <| exn Ψ |> {{ v, Φ v }}  }}
  -∗
  EWP TryWith e₁ (λ: "v" <>, e₂ "v") e₃ @ ∅ <| exn Ψ |> {{ v, Φ v }}.
Proof.
  iIntros "He₁".
  iApply (ewp_try_with with "He₁").
  iSplitL.
  - iIntros (v) " H". by iNext.
  - iIntros (v k) "Hhandler".
    iNext. iApply fupd_ewp. unfold exn.
    rewrite {1}(protocol_agreement_tele' [tele _] [tele]) //=.
    iDestruct "Hhandler" as (x) "(<- & Hewp & _)".
    iApply (Ectxi_ewp_bind (AppLCtx k)). done.
    iApply (Ectxi_ewp_bind (AppLCtx v)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step'. apply pure_prim_step_beta. simpl.
    iModIntro. by iApply "Hewp".
Qed.

End exceptions.
