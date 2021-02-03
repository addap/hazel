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
  state_interp σ _ _ := (gen_heap_interp σ.(heap))%I;
  fork_post _ := True%I;
}.


Notation "l ↦{ dq } v" := (mapsto (L:=loc) (V:=val) l dq (v%V))
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (mapsto (L:=loc) (V:=val) l DfracDiscarded (v%V))
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (mapsto (L:=loc) (V:=val) l (DfracOwn q) (v%V))
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (mapsto (L:=loc) (V:=val) l (DfracOwn 1) (v%V))
  (at level 20, format "l  ↦  v") : bi_scope.


Section lifting.
Context `{!heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Ψ : iEff Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Heap *)

Lemma ewp_alloc E Ψ v :
  ⊢ EWP ref v @ E <| Ψ |> {{ lk, ∃ (l : loc), ⌜ lk = #l ⌝ ∗ l ↦ v }}.
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

Lemma ewp_load E Ψ l q v :
  l ↦{q} v -∗ EWP (Load #l)%E @ E <| Ψ |> {{ v', ⌜ v' = v ⌝ ∗ l ↦{q} v }}.
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

Lemma ewp_store E Ψ l (v' v : val) :
  l ↦ v' -∗ EWP #l <- v @ E <| Ψ |> {{ _, l ↦ v }}.
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
