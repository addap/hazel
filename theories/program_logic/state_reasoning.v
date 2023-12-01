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
From program_logic Require Import weakest_precondition basic_reasoning_rules.
From language Require Export eff_lang.

Set Default Proof Using "Type".


(* ========================================================================== *)
(** * State Interpretation. *)

(* Our custom notion of weakest precondition [EWP] (like the standard weakest
   precondition notion from Iris) is parameterized by a _state-interpretation
   predicate_ [S]. This predicate allows one to assign a logical description
   to the state of the physical heap. We exploit this ability to derive a
   specialized version of [EWP] that allows reasoning about the state. The
   idea (which is standard) is to introduce a ghost cell [γ_heap] holding
   elements of the following authoritative camera:

     [Auth(Loc -fin-> (Frac * Ag Val))]

   The physical heap [σ] is then interpreted as the assertion that the
   _authoritative piece_ of [γ_heap] is [σ]. A points-to predicate [l ↦{q} v]
   is defined as the assertion that the authoritative piece of [γ_heap]
   includes the singleton map [{l ↦ (q, ag(v))}]. *)


(* -------------------------------------------------------------------------- *)
(** Setup of Ghost-State. *)

(* This type class formalizes the assumptions
   on the global list of cameras [Σ]. *)
Class heapGpreS Σ := {
  heap_GpreS_iris :> invGpreS Σ;
  heap_GpreS_heap :> gen_heapGpreS loc val Σ;
  heap_GpreS_inv_heap :> inv_heapGpreS loc val Σ;
}.

(* We provide an explicit instance of such a list [Σ]
   to make sure that we do not perform vacuous reasoning. *)
Definition heapΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc val; inv_heapΣ loc val].

Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapGpreS Σ.
Proof. solve_inG. Qed.

(* This type class, in addition to formalizing which cameras are
   available in [Σ], includes fixed ghost cells, such as [γ_heap]
   and other ghost cells related to invariants. *)
Class heapGS Σ := HeapGS {
  heapG_invG : invGS Σ;
  heapG_gen_heapG :> gen_heapGS loc val Σ;
  heapG_inv_heapG :> inv_heapGS loc val Σ;
}.


(* -------------------------------------------------------------------------- *)
(** Specification of the State Interpretation. *)

Global Instance heapG_irisG `{!heapGS Σ} : irisGS eff_lang Σ := {
  iris_invGS := heapG_invG;
  state_interp σ _ _ _ := (gen_heap_interp σ.(heap))%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.


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

End reasoning_rules.
