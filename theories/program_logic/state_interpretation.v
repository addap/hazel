From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
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
