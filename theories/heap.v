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
  heap_preG_iris :> invGpreS Σ;
  heap_preG_heap :> gen_heapGpreS loc val Σ;
  heap_preG_inv_heap :> inv_heapGpreS loc val Σ;
}.

Definition heapΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc val; inv_heapΣ loc val].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. solve_inG. Qed.

Class heapG Σ := HeapG {
  heapG_invG : invGS Σ;
  heapG_gen_heapG :> gen_heapGS loc val Σ;
  heapG_inv_heapG :> inv_heapGS loc val Σ;
}.

Global Instance heapG_irisG `{!heapG Σ} : irisGS eff_lang Σ := {
  iris_invGS := heapG_invG;
  state_interp σ _ _ _ := (gen_heap_interp σ.(heap))%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
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

Lemma ewp_alloc E Ψ Φ v :
  ▷ (∀ (l : loc), l ↦ v ={E}=∗  Φ #l) -∗
    EWP ref v @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros "HΦ".
  rewrite ewp_unfold /ewp_pre //=.
  iIntros (σ ????) "Hσ".
  iMod (fupd_mask_subseteq ∅) as "Hclose". by apply empty_subseteq.
  iModIntro. iSplitR.
  - iPureIntro. rewrite /reducible //=.
    set (l := fresh_locs (dom (gset loc) σ.(heap))).
    exists [], #l, (state_upd_heap <[l:=v]> σ), []. simpl.
    apply (Ectx_prim_step _ _ _ _ EmptyCtx (ref v) (#l)); try done.
    by apply alloc_fresh.
  - iIntros (e₂ σ₂ Hstep).
    destruct κ; [|done]. simpl in Hstep.
    destruct Hstep; destruct K  as [|Ki K]; [| destruct Ki; try naive_solver ].
    + simpl in H, H0. simplify_eq. inversion H1.
      iMod (gen_heap_alloc _ l v with "Hσ") as "($ & Hl & Hm)". { done. }
      iApply ewp_value.
      iIntros "!> !> !>". iMod "Hclose". by iMod ("HΦ" with "Hl").
    + destruct (fill_val' K e1' v) as [-> ->]. naive_solver. by inversion H1.
Qed.

Lemma ewp_load E Ψ Φ l q v :
  ▷ l ↦{q} v -∗
    ▷ (l ↦{q} v ={E}=∗ Φ v) -∗
      EWP (Load #l)%E @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros "Hl HΦ".
  rewrite ewp_unfold /ewp_pre //=.
  iIntros (σ ????) "Hσ".
  iAssert (▷ (l ↦{q} v ∗ gen_heap_interp (heap σ) ∗ ⌜ heap σ !! l = Some v ⌝))%I
    with "[Hl Hσ]" as "(Hl & Hσ & >%)".
  { iNext. iDestruct (gen_heap_valid (heap σ) l q v with "Hσ Hl") as %H. by iFrame. }
  rename H into heap_valid.
  iMod (fupd_mask_subseteq ∅) as "Hclose". by apply empty_subseteq.
  iModIntro. iSplitR.
  - iPureIntro. rewrite /reducible //=.
    exists [], (Val v), σ, []. simpl.
    apply (Ectx_prim_step _ _ _ _ EmptyCtx (Load #l) v); try done.
    by apply LoadS.
  - iIntros (e₂ σ₂ Hstep).
    destruct κ; [|done]. simpl in Hstep.
    destruct Hstep; destruct K  as [|Ki K]; [| destruct Ki; try naive_solver ].
    + simpl in H, H0. simplify_eq. inversion H1. simplify_eq. iFrame.
      iApply ewp_value. simpl.
      iIntros "!> !> !>". iMod "Hclose". by iMod ("HΦ" with "Hl").
    + destruct (fill_val' K e1' #l) as [-> ->]. naive_solver. by inversion H1.
Qed.

Lemma ewp_store E Ψ Φ l v w :
  ▷ l ↦ v -∗
    ▷ (l ↦ w ={E}=∗ Φ #()) -∗
      EWP (#l <- w)%E @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros "Hl HΦ".
  rewrite ewp_unfold /ewp_pre //=.
  iIntros (σ ????) "Hσ".
  iAssert (▷ (l ↦ v ∗ gen_heap_interp (heap σ) ∗ ⌜ heap σ !! l = Some v ⌝))%I
    with "[Hl Hσ]" as "(Hl & Hσ & >%Hvalid)".
  { iNext. iDestruct (gen_heap_valid (heap σ) l _ v with "Hσ Hl") as %H. by iFrame. }
  iApply fupd_mask_intro. by apply empty_subseteq. iIntros "Hclose".
  iSplitR.
  - iPureIntro. rewrite /reducible //=.
    exists [], (#()), (state_upd_heap <[ l := w ]> σ), []. simpl.
    apply (Ectx_prim_step _ _ _ _ EmptyCtx (#l <- w) #()); try done.
    apply StoreS. by eauto.
  - iIntros (e₂ σ₂ Hstep) "!>!>".
    iMod (gen_heap_update  _ _ _ w with "Hσ Hl") as "[Hσ Hl]".
    destruct κ; [|done]. simpl in Hstep.
    destruct Hstep; destruct K  as [|Ki K]; [| destruct Ki; try naive_solver ].
    + simpl in H, H0. simplify_eq. inversion H1. simplify_eq. iFrame.
      iMod "Hclose". iMod ("HΦ" with "Hl").
      iApply fupd_mask_intro. by apply empty_subseteq. iIntros "Hclose'".
      iMod "Hclose'". iModIntro.
      by iApply ewp_value.
    + destruct (fill_val' K e1' #l) as [-> ->]. naive_solver. by inversion H1.
    + destruct (fill_val' K e1' w)  as [-> ->]. naive_solver. by inversion H1.
Qed.

End lifting.
