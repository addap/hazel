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
  
Definition program : val := (λ: <>,
  let: "l" := ref #0 in
  setone "l")%V.
  
Definition sub_redexes_are_values (e : expr) :=
  ∀ K e', e = fill K e' → to_val e' = None → K = [].

Definition head_atomic (a : atomicity) (e : expr) : Prop :=
  ∀ σ e' σ' ,
    head_step e σ e' σ' →
    if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

Lemma ectx_language_atomic a e :
  head_atomic a e → sub_redexes_are_values e → Atomic a e.
Proof.
  intros Hatomic_step Hatomic_fill σ e' κ σ' efs H.
  unfold language.prim_step in H. simpl in H. unfold prim_step' in H.
  destruct κ, efs; try by destruct H.
  destruct H as [K e1' e2' -> -> Hstep].
  assert (K = []) as -> by eauto 10 using val_head_stuck.
  simpl fill. simpl fill in Hatomic_step.
  eapply Hatomic_step. by apply Hstep.
Qed.

Lemma fill_val2 (k : ectx) (e: expr) :
  is_Some (to_val (fill k e)) → is_Some (to_val e).
Proof.
  intros (v & [-> ->]%fill_val).
  simpl. done.
Qed.

Lemma ectxi_language_sub_redexes_are_values e :
  (∀ Ki e', e = fill Ki e' → is_Some (to_val e')) →
  sub_redexes_are_values e.
Proof.
  intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
  intros []%eq_None_not_Some. eapply fill_val2, Hsub. by rewrite /= fill_app.
Qed.

Local Ltac solve_atomic :=
  apply ectx_language_atomic;
  [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

Lemma fill_no_value (k: ectx) (e: expr) (v: val) :
  to_val e = None → fill k e = v → False.
Proof.
  intros Hv Hfill.
  specialize (fill_not_val k _ Hv) as Hfill'.
  rewrite Hfill in Hfill'.
  simpl in Hfill'. discriminate Hfill'.
Qed.

Global Instance store_atomic v1 v2 : Atomic StronglyAtomic (Store (Val v1) (Val v2)).
Proof. 
  apply ectx_language_atomic.
  - inversion 1. naive_solver. 
  - unfold sub_redexes_are_values.
    intros [] **. naive_solver.
    exfalso.
    simpl in H. destruct f; simpl in H; try discriminate H.
    inversion H. apply (fill_no_value l e' v1 H0). symmetry. apply H2.
    inversion H. apply (fill_no_value l e' v2 H0). symmetry. apply H3.
Qed.

Global Instance load_atomic v : Atomic StronglyAtomic (Load (Val v)).
Proof.
  apply ectx_language_atomic.
  - inversion 1. naive_solver.
  - unfold sub_redexes_are_values.
    intros [] **. naive_solver.
    exfalso.
    simpl in H. destruct f; simpl in H; try discriminate H.
    inversion H. apply (fill_no_value l e' v H0). symmetry. apply H2.
Qed.

Lemma ewp_setone (l: loc): 
  MyInv l ⊢ EWP (setone #l) {{_, True}}.
Proof.
  iIntros "HInv". rewrite /setone. ewp_pure_steps.
  rewrite /MyInv /inner.
  assert (H: Atomic StronglyAtomic (Store (LitV l) (LitV (Zpos xH)))).
    by apply _.
  Locate StronglyAtomic.
  iApply (@ewp_atomic _ _ ⊤ (⊤ ∖ ↑invN) (Store (LitV l) (LitV (Zpos xH))) _ _ _ H). 
  iMod (inv_acc with "HInv") as "((%n & Hl) & Hclose)".
  done.
  iModIntro.
  iApply (ewp_store with "Hl").
  iIntros "!> Hl !>".
  iApply (fupd_elim (⊤ ∖ ↑invN) ⊤ ⊤ True True).
    by iIntros "_ !>". 
  iApply "Hclose". iNext. iExists #1. done.
Restart.
  iIntros "HInv". rewrite /setone. ewp_pure_steps.
  rewrite /MyInv /inner.
  assert (H: Atomic StronglyAtomic (Store (LitV l) (LitV (Zpos xH)))).
    by apply _.
  Locate StronglyAtomic.
  iApply (@ewp_atomic _ _ ⊤ (⊤ ∖ ↑invN) (Store (LitV l) (LitV (Zpos xH))) _ _ _ H). 
  iMod (inv_acc with "HInv") as "((%n & Hl) & Hclose)".
  done.
  iModIntro.
  iApply (ewp_store with "Hl").
  iIntros "!> Hl !>".
  iApply "Hclose".
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