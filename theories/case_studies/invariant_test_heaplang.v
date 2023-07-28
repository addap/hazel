From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth gset gmap agree csum frac excl.
From iris.base_logic Require Import invariants.
From iris.base_logic.lib Require Import iprop wsat.
From iris.heap_lang Require Import notation.
(* a.d. what's in here? *)
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

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
  MyInv l ⊢ WP (setone #l) {{_, True}}.
Proof.
  iIntros "HInv". rewrite /setone. wp_pures.
  rewrite /MyInv /inner.
  iInv "HInv" as (n) "Hl".
  iApply (wp_store with "Hl"). iIntros "!> Hl !>".
  iSplit; last done.
  iNext. iExists #1. done.
Restart.
  iIntros "HInv". rewrite /setone. wp_pures.
  rewrite /MyInv /inner.
  iInv "HInv" as (n) "Hl" "Hclose".
  iApply (wp_store with "Hl").
  (* the update modality here is mask-changing
    i.e. two different masks. So we cannot intros it.
    Instead, we need to change it to a non-mask-changing update using Hclose. 
    This is done with the FUP-CHANGE-MASK rule in "Iris from the ground up".
    Which is apparently fupd_elim in coq *)
  iIntros "!> Hl".
  iApply (fupd_elim (⊤ ∖ ↑invN) ⊤ ⊤ True emp).
  iIntros "e !>". done.
  iApply "Hclose". iNext. iExists #1. done.
Restart.
  (* when the head is a wp, iInv seems to use WP-INV.
    If we instead have an update modality as the head, then it uses something like INV-ACCESS.
    Which is the same failure as in Hazel.
    So it appears to me that we "just" need to add a EWP-INV rule to Hazel. *)
  iIntros "HInv". rewrite /setone. wp_pures.
  rewrite /MyInv /inner.
  iApply fupd_wp.
  Locate fupd_wp.
  Search inv.
  iInv "HInv" as (n) "Hl".
  (* it's basically the same as above but there is an update modality infront of the WP
  Above, there was a mask annotation on the WP and an update in the postcondition. *)
Restart.
  iIntros "HInv". rewrite /setone. wp_pures.
  rewrite /MyInv /inner.
  assert (H: Atomic (stuckness_to_atomicity NotStuck) (Store (LitV l) (LitV (Zpos xH)))).
    by apply _.
  iApply (@wp_atomic _ _ _ NotStuck ⊤ (⊤ ∖ ↑invN) (Store (LitV l) (LitV (Zpos xH))) _ H).
  (* iApply (@wp_atomic _ _ _ _ ⊤ (⊤ ∖ ↑invN) (Store (LitV l) (LitV (Zpos xH)))). *)
  Show Proof.
  iMod (inv_acc with "HInv") as "(HInv1 & HInv2)".
  done.
  iDestruct "HInv1" as "[%n Hl]".
  iApply (wp_store with "Hl").
  iIntros "!> !> Hl".
  iApply (fupd_elim (⊤ ∖ ↑invN) ⊤ ⊤ True True).
  iIntros "e !>". done.
  iApply "HInv2". iNext. iExists #1. done.
  Show Proof.
Qed.

Lemma allocate_MyInv: 
  ⊢ |==> ∃ l, MyInv l.
Proof.
  (* iInv () *)
(* Goal ∀ l, MyInv  *)
Admitted.

End name.