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
  "l" <- #1
)%V.
  
Definition program : val := (λ: <>,
  let: "l" := ref #0 in
  setone "l"
)%V.
  
Lemma ewp_setone (l: loc): 
  MyInv l ⊢ EWP (setone #l) {{_, True}}.
Proof.
  iIntros "HInv". rewrite /setone. ewp_pure_steps.
  iInv "HInv" as (n) "Hl" .
  iApply (ewp_store with "Hl"). iIntros "!> Hl !>!>".
  iSplit; last done.
  iNext. iExists #1. done.
Restart.
  iIntros "HInv". rewrite /setone. ewp_pure_steps.
  rewrite /MyInv /inner.
  iInv "HInv" as (n) "Hl" "Hclose".
  iApply (ewp_store with "Hl").
  (* the update modality here is mask-changing
    i.e. two different masks. So we cannot intros it.
    Instead, we need to change it to a non-mask-changing update using Hclose. 
    This is done with the FUP-CHANGE-MASK rule in "Iris from the ground up".
    Which is apparently fupd_elim in coq *)
  iIntros "!> Hl !>".
  iApply "Hclose". iNext. iExists #1. done.
Restart.
  iIntros "HInv". rewrite /setone. ewp_pure_steps.
  rewrite /MyInv /inner.
  assert (H: Atomic StronglyAtomic (Store (LitV l) (LitV (Zpos xH)))).
  1: by apply _.
  iApply (@ewp_atomic _ _ ⊤ (⊤ ∖ ↑invN) (Store (LitV l) (LitV (Zpos xH))) _ _ _ H). 
  iMod (inv_acc with "HInv") as "((%n & Hl) & Hclose)".
  1: done.
  iModIntro.
  iApply (ewp_store with "Hl").
  iIntros "!> Hl !>".
  iApply (fupd_elim (⊤ ∖ ↑invN) ⊤ ⊤ True True).
  1: by iIntros "_ !>". 
  iApply "Hclose". iNext. iExists #1. done.
Restart.
  iIntros "HInv". rewrite /setone. ewp_pure_steps.
  rewrite /MyInv /inner.
  assert (H: Atomic StronglyAtomic (Store (LitV l) (LitV (Zpos xH)))).
  1: by apply _.
  iApply (@ewp_atomic _ _ ⊤ (⊤ ∖ ↑invN) (Store (LitV l) (LitV (Zpos xH))) _ _ _ H). 
  iMod (inv_acc with "HInv") as "((%n & Hl) & Hclose)".
  1: done.
  iModIntro.
  iApply (ewp_store with "Hl").
  iIntros "!> Hl !>".
  iApply "Hclose".
  iNext. iExists _.
  by done.
Qed.
  
Lemma allocate_MyInv (l: loc) (n: nat): 
  (l ↦ #n) ⊢ |={⊤}=> MyInv l.
Proof.
  Check inv_alloc.
  iIntros "Hl".
  rewrite /MyInv.
  iMod (inv_alloc invN ⊤ (inner l) with "[-]") as "#HInv".
  { iNext. rewrite /inner. by iExists #n. }
  done.
Qed.

Lemma ewp_program: 
  ⊢ EWP (program #()) {{_, True}}.
Proof.
  iIntros. rewrite /program.
  ewp_pure_steps.
  ewp_bind_rule. simpl.
  iApply ewp_alloc. iIntros "!> %l Hl".
  iMod (allocate_MyInv l 0 with "Hl") as "#HInv".
  iModIntro. ewp_pure_steps.
  by iApply ewp_setone.
Qed.

End name.

Print Assumptions ewp_program.