(* exceptions.v *)

(* This theory exploits the standard encoding of exception handlers by means of
   effect handlers to introduce reasoning rules for raising and handling
   exceptions. *)

From iris.proofmode Require Import base tactics classes.
From program_logic Require Import reasoning_rules.


(* ========================================================================== *)
(** * Implementation. *)

Definition raise : val := (λ: "u", do: "u")%V.

Definition ExnTryWith (e1 e2 e3 : expr) : expr :=
  TryWith e1 (λ: "v" <>, e2 "v")%V e3.


(* ========================================================================== *)
(** * Exception Protocol. *)

Definition exn {Σ} (Φ : val → iProp Σ) : iEff Σ :=
  (>> u >> ! u {{ Φ u }}; ? #() {{ False }} @ OS).

Lemma upcl_exn {Σ} Φ v Φ' :
  iEff_car (upcl OS (exn (Σ:=Σ) Φ)) v Φ' ≡
    (∃ (u : val), ⌜ v = u ⌝ ∗ Φ u ∗ (False -∗ Φ' #()))%I.
Proof. by rewrite /exn (upcl_tele' [tele _ ] [tele ]). Qed.


(* ========================================================================== *)
(** * Reasoning Rules. *)

(* -------------------------------------------------------------------------- *)
(** Raise. *)

Lemma ewp_raise `{!heapGS Σ} E (Φ Φ' : val → iProp Σ) x :
  Φ x -∗ EWP raise x @ E <| exn Φ |> {{ Φ' }}.
Proof.
  iIntros "Hx". unfold raise. ewp_pure_steps.
  iApply ewp_do_os. rewrite upcl_exn. iExists x. iFrame.
  by iSplit; [|iIntros "HFalse"].
Qed.


(* -------------------------------------------------------------------------- *)
(** Exception Handler. *)

Lemma ewp_exn_try_with `{!heapGS Σ} E Φ Φ' (e1 : expr) (e2 e3 : val) :
  EWP e1 @ E <| exn (λ v, EWP e2 v @ E <| exn Φ |> {{ Φ' }}) |>
             {{        v, EWP e3 v @ E <| exn Φ |> {{ Φ' }}  }}
  -∗
  EWP ExnTryWith e1 e2 e3          @ E <| exn Φ |> {{ Φ' }}.
Proof.
  iIntros "He1". iApply (ewp_try_with with "He1").
  iSplit; [by auto|iSplit]; iIntros (v k);
  last by iIntros "HFalse"; rewrite upcl_bottom.
  rewrite upcl_exn. iIntros "[%x [-> [He2 _]]]".
  by ewp_pure_steps.
Qed.
