(* heap.v

   In this theory, we prove reasoning rules for the three main heap
   manipulating operations: [Alloc], [Load] and [Store].
*)

From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From hazel Require Export lang.
From hazel Require Import weakestpre notation ieff.

Set Default Proof Using "Type".

Class heapPreG Σ := HeapPreG {
  heap_preG_iris :> invPreG Σ;
  heap_preG_heap :> gen_heapPreG loc val Σ;
  heap_preG_inv_heap :> inv_heapPreG loc val Σ;
}.

Definition heapΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc val; inv_heapΣ loc val].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. solve_inG. Qed.

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ;
  heapG_inv_heapG :> inv_heapG loc val Σ;
}.

Global Instance heapG_irisG `{!heapG Σ} : irisG eff_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ _ _ := (gen_heap_ctx σ.(heap))%I;
  fork_post _ := True%I;
}.

Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q (v%V))
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" := (mapsto (L:=loc) (V:=val) l 1%Qp (v%V))
  (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

Section lifting.
Context `{!heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val]. *)

Global Instance ex_mapsto_fractional l : Fractional (λ q, l ↦{q} -)%I.
Proof.
  intros p q. iSplit.
  - iDestruct 1 as (v) "[H1 H2]". iSplitL "H1"; eauto.
  - iIntros "[H1 H2]". iDestruct "H1" as (v1) "H1". iDestruct "H2" as (v2) "H2".
    iDestruct (mapsto_agree with "H1 H2") as %->. iExists v2. by iFrame.
Qed.
Global Instance ex_mapsto_as_fractional l q :
  AsFractional (l ↦{q} -) (λ q, l ↦{q} -)%I q.
Proof. split. done. apply _. Qed.

Lemma mapsto_agree l q1 q2 v1 v2 : l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iDestruct (mapsto_agree with "H1 H2") as %[=?]. done. Qed.

Lemma mapsto_combine l q1 q2 v1 v2 :
  l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ l ↦{q1 + q2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hl1 Hl2". iDestruct (mapsto_agree with "Hl1 Hl2") as %->.
  iCombine "Hl1 Hl2" as "Hl". eauto with iFrame.
Qed.

Lemma mapsto_valid l q v : l ↦{q} v -∗ ✓ q.
Proof. apply mapsto_valid. Qed.
Lemma mapsto_valid_2 l q1 q2 v1 v2 : l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ✓ (q1 + q2)%Qp.
Proof. apply mapsto_valid_2. Qed.
Lemma mapsto_mapsto_ne l1 l2 q1 q2 v1 v2 :
  ¬ ✓(q1 + q2)%Qp → l1 ↦{q1} v1 -∗ l2 ↦{q2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. apply mapsto_mapsto_ne. Qed.

Lemma ewp_alloc E (v : val) :
  ⊢ EWP ref v @ E {{ lk, ∃ (l : loc), ⌜ lk = #l ⌝ ∗ l ↦ v }}.
Proof.
  rewrite ewp_unfold /ewp_pre //=.
  iIntros (σ ??) "Hσ".
  iMod (fupd_intro_mask' E ∅) as "Hclose". by apply empty_subseteq.
  iModIntro. iSplitR.
  - iPureIntro. rewrite /reducible //=.
    set (l := fresh_locs (dom (gset loc) σ.(heap))).
    exists [], #l, (state_upd_heap <[l:=v]> σ), []. simpl.
    apply (Ectx_prim_step _ _ _ _ EmptyCtx (ref v) (#l)); try done.
    by apply alloc_fresh.
  - iIntros (e₂ σ₂ Hstep).
    destruct Hstep; destruct K  as [|Ki K]; [| destruct Ki; try naive_solver ].
    + simpl in H, H0. simplify_eq. inversion H1.
      iMod (gen_heap_alloc _ l v with "Hσ") as "($ & Hl & Hm)". { done. }
      iApply ewp_value. simpl. iExists l. iFrame.
      iIntros "!> !>". iMod "Hclose". iModIntro. by iPureIntro.
    + destruct (fill_val' K e1' v) as [-> ->]. naive_solver. by inversion H1.
Qed.

Lemma ewp_load E (l : loc) q (v : val) :
  l ↦{q} v -∗ EWP (Load #l)%E @ E {{ v', ⌜ v' = v ⌝ ∗ l ↦{q} v }}.
Proof.
  iIntros "Hl". rewrite ewp_unfold /ewp_pre //=.
  iIntros (σ _ _) "Hσ".
  iDestruct (gen_heap_valid (heap σ) l q v with "Hσ Hl") as "%".
  rename H into heap_valid.
  iMod (fupd_intro_mask' E ∅) as "Hclose". by apply empty_subseteq.
  iModIntro. iSplitR.
  - iPureIntro. rewrite /reducible //=.
    exists [], (Val v), σ, []. simpl.
    apply (Ectx_prim_step _ _ _ _ EmptyCtx (Load #l) v); try done.
    by apply LoadS.
  - iIntros (e₂ σ₂ Hstep).
    destruct Hstep; destruct K  as [|Ki K]; [| destruct Ki; try naive_solver ].
    + simpl in H, H0. simplify_eq. inversion H1. simplify_eq. iFrame.
      iApply ewp_value. simpl. iFrame.
      iIntros "!> !>". iMod "Hclose". iModIntro. by iPureIntro.
    + destruct (fill_val' K e1' #l) as [-> ->]. naive_solver. by inversion H1.
Qed.

Lemma ewp_store E (l : loc) (v' v : val) :
  l ↦ v' -∗ EWP #l <- v @ E {{ _, l ↦ v }}.
Proof.
  iIntros "Hl". rewrite ewp_unfold /ewp_pre //=.
  iIntros (σ _ _) "Hσ".
  iDestruct (gen_heap_valid with "Hσ Hl") as "%".
  rename H into heap_valid.
  iMod (gen_heap_update _ _ _ v with "Hσ Hl") as "[Hσ Hl]".
  iMod (fupd_intro_mask' E ∅) as "Hclose". by apply empty_subseteq.
  iModIntro. iSplitR.
  - iPureIntro. rewrite /reducible //=.
    exists [], (#()), (state_upd_heap <[ l := v ]> σ), []. simpl.
    apply (Ectx_prim_step _ _ _ _ EmptyCtx (#l <- v) #()); try done.
    apply StoreS. by eauto.
  - iIntros (e₂ σ₂ Hstep).
    destruct Hstep; destruct K  as [|Ki K]; [| destruct Ki; try naive_solver ].
    + simpl in H, H0. simplify_eq. inversion H1. simplify_eq. iFrame.
      iApply ewp_value. simpl. by iFrame.
    + destruct (fill_val' K e1' #l) as [-> ->]. naive_solver. by inversion H1.
    + destruct (fill_val' K e1' v)  as [-> ->]. naive_solver. by inversion H1.
Qed.

End lifting.

