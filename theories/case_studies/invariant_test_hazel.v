From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth gset gmap agree csum frac excl.
From iris.base_logic Require Import invariants.
From iris.base_logic.lib Require Import iprop wsat.
From program_logic Require Import reasoning_rules.

Section name.
Context `{!heapGS Σ}.

Definition invN : namespace := nroot .@ "inv".

Definition inner (l: loc): iProp Σ := ∃ n, l ↦ n.

Definition MyInv (l: loc) := inv invN (inner l).

Global Instance MyInv_Persistent (l: loc): Persistent (MyInv l).
Proof.
  by apply _.
Qed.

Definition setone : val := (λ: "l",
  "l" <- #1)%V.

Lemma ewp_setone (l: loc): 
  MyInv l ⊢ EWP (setone #l) {{_, True}}.
Proof.
  iIntros "HInv". rewrite /setone. ewp_pure_steps.
  rewrite /MyInv /inner.
  assert (H: Atomic StronglyAtomic (Store (LitV l) (LitV (Zpos xH)))).
    by admit.
  iApply (@ewp_atomic _ _ ⊤ (⊤ ∖ ↑invN) (Store (LitV l) (LitV (Zpos xH))) _ _ _ H). 
  iMod (inv_acc with "HInv") as "(HInv1 & HInv2)".
  done.
  iDestruct "HInv1" as "[%n Hl]".
  iApply (ewp_store with "Hl").
  iIntros "!> !> Hl !>".
  iApply (fupd_elim (⊤ ∖ ↑invN) ⊤ ⊤ True True).
  iIntros "e !>". done.
  iApply "HInv2". iNext. iExists #1. done.
Qed.
  
  (* Unset Printing Notations. *)
(*
"Hl" : ▷ l ↦ n
--------------------------------------∗
|={⊤ ∖ ↑invN}=> ▷ (∃ n0 : val, l ↦ n0) ∗ (|={⊤}=> EWP #l <- #1 {{ _, True }}) 
*)

(fupd (difference top (up_close invN)) (difference top (up_close invN))
     (bi_sep (bi_later (bi_exist (fun n0 : val => mapsto l (DfracOwn (pos_to_Qp xH)) n0)))
        (fupd top top
           (ewp_def top (Store (LitV l) (LitV (Zpos xH))) iEff_bottom iEff_bottom
              (fun _ : val => bi_pure True)))))

  iInv "HInv" as (n) "Hl" "Hclose".
(* 
"Hl" : ▷ l ↦ n
"Hclose" : ▷ (∃ n0 : val, l ↦ n0) ={⊤ ∖ ↑invN,⊤}=∗ emp
--------------------------------------∗
|={⊤ ∖ ↑invN,⊤}=> EWP #l <- #1 {{ _, True }} 
*)


Lemma allocate_MyInv: 
  ⊢ |==> ∃ l, MyInv l.
Proof.
  (* iInv () *)
(* Goal ∀ l, MyInv  *)
Admitted.

End name.