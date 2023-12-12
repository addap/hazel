(* state_reasoning.v *)

(* This theory introduces rules for reasoning about heap-manipulating
   operations, such as allocation, read, and update of memory locations. *)

From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From program_logic Require Import weakest_precondition basic_reasoning_rules state_interpretation.
From language Require Export eff_lang.

(* -------------------------------------------------------------------------- *)
(** Notation. *)

(* Derived notation for points-to predicates. *)

Notation "l ↦{ dq } v" := (mapsto (L:=loc) (V:=val) l dq (v%V))
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦□ v" := (mapsto (L:=loc) (V:=val) l DfracDiscarded (v%V))
  (at level 20, format "l  ↦□  v") : bi_scope.
Notation "l ↦{# q } v" := (mapsto (L:=loc) (V:=val) l (DfracOwn q) (v%V))
  (at level 20, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" := (mapsto (L:=loc) (V:=val) l (DfracOwn 1) (v%V))
  (at level 20, format "l  ↦  v") : bi_scope.


(* ========================================================================== *)
(** * Reasoning Rules. *)

Section reasoning_rules.
  Context `{!heapGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types Ψ : iEff Σ.
  Implicit Types efs : list expr.
  Implicit Types σ : state.
  Implicit Types v : val.
  Implicit Types l : loc.

  (* ------------------------------------------------------------------------ *)
  (** Allocation. *)

  Lemma ewp_alloc E Ψ1 Ψ2 Φ v :
    ▷ (∀ (l : loc), l ↦ v ={E}=∗  Φ #l) -∗
      EWP ref v @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    iIntros "HΦ".
    rewrite ewp_unfold /ewp_pre //=.
    iIntros (σ ????) "Hσ".
    iMod (fupd_mask_subseteq ∅) as "Hclose".
    { by apply empty_subseteq. }
    iModIntro. iSplitR.
    - iPureIntro. rewrite /reducible //=.
      set (l := fresh_locs (dom (gset loc) σ.(heap))).
      exists [], #l, (heap_upd <[l:=v]> σ), []. simpl.
      apply (Ectx_prim_step _ _ _ _ [] [] (ref v)%E (#l)); try done.
      by apply alloc_fresh.
    - iIntros (e₂ σ₂ efs₂ Hstep).
      destruct κ; [|done]. simpl in Hstep.
      destruct Hstep; destruct k  as [|f k];
      [| destruct f; try naive_solver ].
      + simpl in H, H0. simplify_eq. inversion H1.
        iMod (gen_heap_alloc _ l v with "Hσ") as "($ & Hl & Hm)". { done. }
        iIntros "!> !> !>". iMod "Hclose".
        iSplitL; last by iModIntro.
        iApply ewp_value.
         by iMod ("HΦ" with "Hl").
      + destruct (fill_val' k e1' v) as [-> ->]. naive_solver. by inversion H1.
  Qed.


  (* ------------------------------------------------------------------------ *)
  (** Load. *)

  Lemma ewp_load E Ψ1 Ψ2 Φ l q v :
    ▷ l ↦{q} v -∗
      ▷ (l ↦{q} v ={E}=∗ Φ v) -∗
        EWP (Load #l)%E @ E <| Ψ1 |> {| Ψ2 |}  {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    rewrite ewp_unfold /ewp_pre //=.
    iIntros (σ ????) "Hσ".
    iAssert (▷ (l ↦{q} v ∗ gen_heap_interp (heap σ) ∗ ⌜ heap σ !! l = Some v ⌝))%I
      with "[Hl Hσ]" as "(Hl & Hσ & >%heap_valid)".
    { iNext. iDestruct (gen_heap_valid with "Hσ Hl") as %H. by iFrame. }
    iMod (fupd_mask_subseteq ∅) as "Hclose". by apply empty_subseteq.
    iModIntro. iSplitR.
    - iPureIntro. rewrite /reducible //=.
      exists [], (Val v), σ, []. simpl.
      apply (Ectx_prim_step _ _ _ _ [] [] (Load #l) v); try done.
      by apply LoadS.
    - iIntros (e₂ σ₂ efs₂ Hstep).
      destruct κ; [|done]. simpl in Hstep.
      destruct Hstep; destruct k  as [|f k]; [| destruct f; try naive_solver ].
      + simpl in H, H0. simplify_eq. inversion H1. simplify_eq. iFrame.
        iIntros "!> !> !>". iMod "Hclose".
        iSplitL; last by iModIntro.
        iApply ewp_value. simpl.
         by iMod ("HΦ" with "Hl").
      + destruct (fill_val' k e1' #l) as [-> ->]. naive_solver. by inversion H1.
  Qed.


  (* ------------------------------------------------------------------------ *)
  (** Store. *)

  Lemma ewp_store E Ψ1 Ψ2 Φ l v w :
    ▷ l ↦ v -∗
      ▷ (l ↦ w ={E}=∗ Φ #()) -∗
        EWP (#l <- w)%E @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    rewrite ewp_unfold /ewp_pre //=.
    iIntros (σ ????) "Hσ".
    iAssert (▷ (l ↦ v ∗ gen_heap_interp (heap σ) ∗ ⌜ heap σ !! l = Some v ⌝))%I
      with "[Hl Hσ]" as "(Hl & Hσ & >%Hvalid)".
    { iNext. iDestruct (gen_heap_valid with "Hσ Hl") as %H. by iFrame. }
    iApply fupd_mask_intro. by apply empty_subseteq. iIntros "Hclose".
    iSplitR.
    - iPureIntro. rewrite /reducible //=.
      exists [], (#()), (heap_upd <[ l := w ]> σ), []. simpl.
      apply (Ectx_prim_step _ _ _ _ [] [] (#l <- w)%E #()); try done.
      apply StoreS. by eauto.
    - iIntros (e₂ σ₂ efs₂ Hstep) "!>!>".
      iMod (gen_heap_update  _ _ _ w with "Hσ Hl") as "[Hσ Hl]".
      destruct κ; [|done]. simpl in Hstep.
      destruct Hstep; destruct k  as [|f k]; [| destruct f; try naive_solver ].
      + simpl in H, H0. simplify_eq. inversion H1. simplify_eq. iFrame.
        iMod "Hclose". iMod ("HΦ" with "Hl") as "HΦ".
        iApply fupd_mask_intro. by apply empty_subseteq. iIntros "Hclose'".
        iMod "Hclose'". iModIntro.
        iSplitL; last by done.
        by iApply ewp_value.
      + destruct (fill_val' k e1' #l) as [-> ->]. naive_solver. by inversion H1.
      + destruct (fill_val' k e1' w)  as [-> ->]. naive_solver. by inversion H1.
  Qed.
  
  (* ------------------------------------------------------------------------ *)
  (** CmpXchg. *)
(* Lemma twp_cmpxchg_fail s E l dq v' v1 v2 :
  v' ≠ v1 → vals_compare_safe v' v1 →
  [[{ l ↦{dq} v' }]] CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  [[{ RET PairV v' (LitV $ LitBool false); l ↦{dq} v' }]].
Proof.
  iIntros (?? Φ) "Hl HΦ". iApply twp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 ns κs nt) "(Hσ & Hκs & Hsteps) !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with base_step.
  iIntros (κ v2' σ2 efs Hstep); inv_base_step.
  rewrite bool_decide_false //.
  iMod (steps_auth_update_S with "Hsteps") as "Hsteps".
  iModIntro; iSplit; first done. iSplit; first done. iFrame. by iApply "HΦ".
Qed. *)

  Lemma ewp_cmpxchg_fail E Ψ1 Ψ2 Φ l v' v1 v2 :
    v' ≠ v1 → vals_compare_safe v' v1 →
    ▷ l ↦ v' -∗ 
      ▷ (l ↦ v' ={E}=∗ Φ (PairV v' (LitV $ LitBool false))) -∗ 
        EWP (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    iIntros (Hneq Hsafe) "Hl HΦ". 
    rewrite ewp_unfold /ewp_pre //=.
    iIntros (σ ????) "Hσ".
    iAssert (▷ (l ↦ v' ∗ gen_heap_interp (heap σ) ∗ ⌜ heap σ !! l = Some v' ⌝))%I
      with "[Hl Hσ]" as "(Hl & >Hσ & >%Hvalid)".
    { iNext. iDestruct (gen_heap_valid with "Hσ Hl") as %H. by iFrame. }
    iApply fupd_mask_intro; first by apply empty_subseteq. iIntros "Hclose".
    iSplitR.
    - iPureIntro. rewrite /reducible //=.
      exists [], (v', #false)%V, σ, []. simpl.
      apply (Ectx_prim_step _ _ _ _ [] [] (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) (v', #false)%V); try done.
      apply CmpXchgS. assumption. assumption. 
      by rewrite bool_decide_false.
    - iIntros (e₂ σ₂ efs₂ Hstep) "!>!>!>".
      destruct κ; [|done]. simpl in Hstep.
      (* a.d. TODO This is basically a pure step, can we use the pure_prim_step things from iris_language.v? *)
      (* Since we know e1' does a head_step, we can deduce k is empty. The other cases lead to a contradiction. *)
      destruct Hstep. destruct k  as [|f k]; [| destruct f; try naive_solver ].
      + simpl in H, H0. simplify_eq. inversion H1. simplify_eq. 
        rewrite bool_decide_false in H1; last by assumption. rewrite bool_decide_false; last by assumption.
        iFrame.
        iMod "Hclose". iMod ("HΦ" with "Hl") as "HΦ".
        iModIntro.
        iSplitL; last by done.
        by iApply ewp_value.
      + destruct (fill_val' k e1' #l) as [-> ->]. naive_solver. by inversion H1.
      + destruct (fill_val' k e1' v1) as [-> ->]. naive_solver. by inversion H1.
      + destruct (fill_val' k e1' v2) as [-> ->]. naive_solver. by inversion H1.
  Qed.

  Lemma ewp_cmpxchg_suc E Ψ1 Ψ2 Φ l v' v1 v2 :
    v' = v1 → vals_compare_safe v' v1 →
    ▷ l ↦ v' -∗ 
      ▷ (l ↦ v2 ={E}=∗ Φ (PairV v' (LitV $ LitBool true))) -∗ 
        EWP (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    iIntros (Heq Hsafe) "Hl HΦ". 
    rewrite ewp_unfold /ewp_pre //=.
    iIntros (σ ????) "Hσ".
    iAssert (▷ (l ↦ v' ∗ gen_heap_interp (heap σ) ∗ ⌜ heap σ !! l = Some v' ⌝))%I
      with "[Hl Hσ]" as "(Hl & >Hσ & >%Hvalid)".
    { iNext. iDestruct (gen_heap_valid with "Hσ Hl") as %H. by iFrame. }
    iApply fupd_mask_intro; first by apply empty_subseteq. iIntros "Hclose".
    iSplitR.
    - iPureIntro. rewrite /reducible //=.
      exists [], (v', #true)%V, (heap_upd <[ l := v2 ]> σ), []. simpl.
      apply (Ectx_prim_step _ _ _ _ [] [] (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) (v', #true)%V); try done.
      apply CmpXchgS. assumption. assumption. 
      by rewrite bool_decide_true.
    - iIntros (e₂ σ₂ efs₂ Hstep) "!>!>!>".
      iMod (gen_heap_update  _ _ _ v2 with "Hσ Hl") as "[Hσ Hl]".
      destruct κ; [|done]. simpl in Hstep.
      destruct Hstep. destruct k  as [|f k]; [| destruct f; try naive_solver ].
      + simpl in H, H0. revert Heq. simplify_eq. inversion H1. simplify_eq. intros Heq.
        rewrite bool_decide_true in H1; last by assumption. rewrite bool_decide_true; last by assumption.
        iFrame.
        iMod "Hclose". iMod ("HΦ" with "Hl") as "HΦ".
        iModIntro.
        iSplitL; last by done.
        by iApply ewp_value.
      + destruct (fill_val' k e1' #l) as [-> ->]. naive_solver. by inversion H1.
      + destruct (fill_val' k e1' v1) as [-> ->]. naive_solver. by inversion H1.
      + destruct (fill_val' k e1' v2) as [-> ->]. naive_solver. by inversion H1.
  Qed.

End reasoning_rules.
