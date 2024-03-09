From program_logic Require Import state_interpretation.

(* I'm not sure why they call it sub_redexes, but this says that all subexpressions of 
   e are values, i.e. if we decompose it into K[e'] where e' is not a value then K must be empty. *)
Definition sub_redexes_are_values (e : expr) :=
  ∀ K e', e = fill K e' → to_val e' = None → K = [].

(* This says that e takes one step to a value. *)
Definition head_atomic (a : atomicity) (e : expr) : Prop :=
  ∀ σ e' σ' efs,
    head_step e σ e' σ' efs →
    if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

Lemma ectx_language_atomic a e :
  head_atomic a e → sub_redexes_are_values e → Atomic a e.
Proof.
  intros Hatomic_step Hatomic_fill σ e' κ σ' efs H.
  unfold language.prim_step in H. simpl in H. unfold prim_step' in H.
  destruct κ; last by destruct H.
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

Lemma fill_no_value (k: ectx) (e: expr) (v: val) :
  to_val e = None → fill k e = v → False.
Proof.
  intros Hv Hfill.
  specialize (fill_not_val k _ Hv) as Hfill'.
  rewrite Hfill in Hfill'.
  simpl in Hfill'. discriminate Hfill'.
Qed.

Local Ltac solve_atomic := 
  apply ectx_language_atomic;
  [ inversion 1; naive_solver
  | intros [|f?] ? H ?; [|
    exfalso; destruct f; inversion H; by eapply fill_no_value ]].

Global Instance store_atomic v1 v2 : Atomic StronglyAtomic (Store (Val v1) (Val v2)).
Proof. by solve_atomic. Qed.

Global Instance load_atomic v : Atomic StronglyAtomic (Load (Val v)).
Proof. by solve_atomic. Qed.

Global Instance alloc_atomic v : Atomic StronglyAtomic (Alloc (Val v)).
Proof. by solve_atomic. Qed.

Global Instance cmpxchg_atomic v1 v2 v3 : Atomic StronglyAtomic (CmpXchg (Val v1) (Val v2) (Val v3)).
Proof. by solve_atomic. Qed.

