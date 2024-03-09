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
  "l" <- #1
)%V.

Definition program : val := (λ: <>,
  let: "l" := ref #0 in
  setone "l"
)%V.

Lemma ewp_setone (l: loc): 
  MyInv l ⊢ WP (setone #l) {{_, True}}.
Proof.
  iIntros "HInv". rewrite /setone. wp_pures.
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
  Fail iModIntro.
  iApply (fupd_elim (⊤ ∖ ↑invN) ⊤ ⊤ True emp).
    by iIntros "_ !>". 
  iApply "Hclose". iNext. iExists #1. done.
Restart.
  (* when the head is a wp, iInv seems to use WP-INV.
    If we instead have an update modality as the head, then it uses something like INV-ACCESS.
    Which is the same failure as in Hazel.
    So it appears to me that we "just" need to add a EWP-INV rule to Hazel.
     *)
  iIntros "#HInv". rewrite /setone. wp_pures.
  rewrite /MyInv /inner.
  iApply fupd_wp.
  Locate fupd_wp.
  iInv "HInv" as (n) "Hl" "Hclose".
  Check wp_atomic.
  (* We have a mask-changing update, so to to be able to get to the WP we first need to change
  the mast. And we can only do that with "HClose". And for that we need to give up l ↦ n. *)
Restart.
  iIntros "HInv". rewrite /setone. wp_pures.
  rewrite /MyInv /inner.
  assert (H: Atomic (stuckness_to_atomicity NotStuck) (Store (LitV l) (LitV (Zpos xH)))).
    by apply _.
  iApply (@wp_atomic _ _ _ NotStuck ⊤ (⊤ ∖ ↑invN) (Store (LitV l) (LitV (Zpos xH))) _ H).
  (* iApply (@wp_atomic _ _ _ _ ⊤ (⊤ ∖ ↑invN) (Store (LitV l) (LitV (Zpos xH)))). *)
  Show Proof.
  iMod (inv_acc with "HInv") as "((%n & Hl) & Hclose)".
  done.
  iApply (wp_store with "Hl").
  iIntros "!> !> Hl".
  iApply (fupd_elim (⊤ ∖ ↑invN) ⊤ ⊤ True True).
  iIntros "e !>". done.
  iApply "Hclose". iNext. iExists #1. done.
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

Lemma wp_program: 
  ⊢ WP (program #()) {{_, True}}.
Proof.
  iIntros. rewrite /program.
  wp_pures.
  (wp_bind (ref _)%E). simpl.
  iApply wp_alloc; first done. iIntros "!> %l [Hl _]".
  iMod (allocate_MyInv l 0 with "Hl") as "#HInv".
  wp_pures.
  by iApply ewp_setone.
Qed.

Parameter P2 Q2 : iProp Σ.
Parameter P2_Timeless' : Timeless P2.
Parameter Q2_Timeless' : Timeless Q2.
Parameter P2_Persistent' : Persistent P2.
Parameter Q2_Persistent' : Persistent Q2.

Global Instance P2_Timeless : Timeless P2.
Proof. by apply P2_Timeless'. Qed.
Global Instance Q2_Timeless : Timeless Q2.
Proof. by apply Q2_Timeless'. Qed.
Global Instance P2_Persistent : Persistent P2.
Proof. by apply P2_Persistent'. Qed.
Global Instance Q2_Persistent : Persistent Q2.
Proof. by apply Q2_Persistent'. Qed.

Definition inv2N : namespace := nroot .@ "inv2".

Definition inner2 (l: loc): iProp Σ := 
  (l ↦ (InjLV #()) ∗ P2)
  ∨ (l ↦ (InjRV #()) ∗ Q2).

Definition MyInv2 (l: loc) := inv inv2N (inner2 l).

Global Instance MyInv2_Timeless (l: loc): Timeless (inner2 l).
Proof. 
  by apply _.
Qed.

Global Instance MyInv2_Persistent (l: loc): Persistent (MyInv2 l).
Proof.
  by apply _.
Qed.

Definition read_l : val := (λ: "l" "e", 
  match: ! "l" with
  InjL <> => "e" #()
  | InjR <> => "e" #()
  end)%V.
    
Search "fupd".

Lemma copy_persistent_out_of_inv (l: loc) (ee: val):
  (P2 -∗ WP ee #() {{_, True}}) ∗
  (Q2 -∗ WP ee #() {{_, True}}) ∗ 
  MyInv2 l ⊢ WP (read_l #l ee) {{_, True}}.
Proof.
  iIntros "(Hpz & Hqz & HInv)".
  rewrite /read_l. wp_pures.
  (wp_bind (!_)%E).
  rewrite /MyInv2 /inner2.
  iInv "HInv" as "> [[Hl #Hp]|[Hl #Hq]]".
  - wp_load. iModIntro. iSplitL "Hl".
    + (* need to close invariant again *)
      iNext. iLeft. by iFrame.
    + wp_pures. by iApply "Hpz".
  - wp_load. iModIntro. iSplitL "Hl".
    + iNext. iRight. by iFrame.
    + wp_pures. by iApply "Hqz".
Restart.
  iIntros "(Hpz & Hqz & HInv)".
  rewrite /read_l. wp_pures.
  (wp_bind (!_)%E).
  rewrite /MyInv2 /inner2.
  iInv "HInv" as "> [[Hl #Hp]|[Hl #Hq]]" "Hclose".
  - wp_load. 
    iApply (fupd_trans_frame (⊤ ∖ ↑inv2N) (⊤ ∖ ↑inv2N) ⊤ _ (▷ (l ↦ InjLV #() ∗ P2 ∨ l ↦ InjRV #() ∗ Q2))).
    iSplitL "Hclose"; first by iAssumption. iModIntro.
    iSplitL "Hl". 
    iNext. iLeft. by iFrame.
    wp_pures. by iApply "Hpz".
  - wp_load.
    iApply (fupd_trans_frame (⊤ ∖ ↑inv2N) (⊤ ∖ ↑inv2N) ⊤ _ (▷ (l ↦ InjLV #() ∗ P2 ∨ l ↦ InjRV #() ∗ Q2))).
    iSplitL "Hclose"; first by iAssumption. iModIntro.
    iSplitL "Hl". 
    iNext. iRight. by iFrame.
    wp_pures. by iApply "Hqz".
Restart.
  iIntros "(Hpz & Hqz & HInv)".
  rewrite /read_l. wp_pures.
  (wp_bind (!_)%E).
  rewrite /MyInv2 /inner2.
  assert (H: Atomic (stuckness_to_atomicity NotStuck) (Load #l)).
    by apply _.
  iApply (@wp_atomic _ _ _ NotStuck ⊤ (⊤ ∖ ↑inv2N)).
  iMod (inv_acc with "HInv") as "(> [[Hl #Hp]|[Hl #Hq]] & Hclose)".
  done. 
  - iModIntro. wp_load. 
    iApply (fupd_trans_frame (⊤ ∖ ↑inv2N) (⊤ ∖ ↑inv2N) ⊤ _ (▷ (l ↦ InjLV #() ∗ P2 ∨ l ↦ InjRV #() ∗ Q2))).
    iSplitL "Hclose"; first by iAssumption. iModIntro.
    iSplitL "Hl". 
    iNext. iLeft. by iFrame.
    wp_pures. by iApply "Hpz".
  - iModIntro. wp_load.
    iApply (fupd_trans_frame (⊤ ∖ ↑inv2N) (⊤ ∖ ↑inv2N) ⊤ _ (▷ (l ↦ InjLV #() ∗ P2 ∨ l ↦ InjRV #() ∗ Q2))).
    iSplitL "Hclose"; first by iAssumption. iModIntro.
    iSplitL "Hl". 
    iNext. iRight. by iFrame.
    wp_pures. by iApply "Hqz".
Qed.

End name.