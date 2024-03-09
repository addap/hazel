From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl excl_auth gset gmap agree csum frac excl.
From iris.base_logic Require Import invariants.
From iris.base_logic.lib Require Import iprop wsat saved_prop.
From iris.heap_lang Require Import proofmode notation.

Definition spawn : val :=
  (λ: "f",
    let: "c" := ref NONE in
    Fork ("c" <- SOME ("f" #())) ;; "c")%V.
Definition join : val :=
  (rec: "join" "c" :=
    match: Load "c" with
      SOME "x" => "x"
    | NONE => "join" "c"
    end)%V.

(** The CMRA & functor we need. *)
(* Not bundling heapGS, as it may be shared with other users. *)
Class spawnG Σ := SpawnG { spawn_tokG : inG Σ (exclR unitO) }.
Local Existing Instance spawn_tokG.

Definition spawnΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_spawnΣ {Σ} : subG spawnΣ Σ → spawnG Σ.
Proof. solve_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context `{!heapGS Σ, !spawnG Σ} (N : namespace).

Definition spawn_inv (γ : gname) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ lv, l ↦ lv ∗ (⌜lv = NONEV⌝ ∨
                  ∃ w, ⌜lv = SOMEV w⌝ ∗ (Ψ w ∨ own γ (Excl ()))).

Definition join_handle (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ γ, own γ (Excl ()) ∗ inv N (spawn_inv γ l Ψ).

Global Instance spawn_inv_ne n γ l :
  Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γ l).
Proof. solve_proper. Qed.
Global Instance join_handle_ne n l :
  Proper (pointwise_relation val (dist n) ==> dist n) (join_handle l).
Proof. solve_proper. Qed.

(** The main proofs. *)
Lemma spawn_spec (Q : val → iProp Σ) (f : val) :
  WP (f #()) {{ Q }} -∗ WP (spawn f) {{ v, ∃ (l: loc), ⌜ v = #l ⌝ ∗ join_handle l Q }}.
Proof.
  iIntros "Hf". rewrite /spawn. 
  (* a.d. TODO ewp_pure_steps is broken. *)
  wp_pures. 
  (wp_bind (ref _)%E). 
  iApply wp_alloc; first done. iNext.
  iIntros (l) "[Hl _]". 
  iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
  iMod (inv_alloc N _ (spawn_inv γ l Q) with "[Hl]") as "#HInv".
  { iNext. iExists NONEV. iFrame; eauto. }
  wp_pures.
  wp_bind (Fork _)%E.
  iApply (wp_fork with "[Hf]").
  { iNext. 
    wp_bind (f #())%E. iApply (wp_strong_mono with "Hf"); try done.
    iIntros (v) "Hv !>".
    wp_pures.
    iInv "HInv" as "HpInvIn" "Hclose".
    iDestruct "HpInvIn" as (lv) "(Hlv & HRest)".
    iApply (wp_store with "Hlv"). 
    iIntros "!> Hlv". 
    iMod ("Hclose" with "[Hlv HRest Hv]") as "_".
    2: by done.
    iNext. iExists _. iFrame "Hlv".
    iRight. iExists _. iSplit; first done. by iLeft. 
  }
  iNext. wp_pures. iModIntro.
  iExists _. iSplit; first done.
  iExists _. iSplit; first done. done.
Qed.

Lemma join_spec (Q : val → iProp Σ) l :
  join_handle l Q -∗ WP join #l {{ v, Q v }}.
Proof.
  iIntros "H". iDestruct "H" as (γ) "[Hγ #HInv]".
  iLöb as "IH".
  rewrite /join.
  wp_pures.
  wp_bind (! _)%E.
  iInv "HInv" as "HpInvIn" "Hclose".
  iDestruct "HpInvIn" as (lv) "(Hl & Hlv)".
  iApply (wp_load with "Hl"). 
  iIntros "!> Hl". 
  iDestruct "Hlv" as "[->|(% & -> & Hlv)]".
  - iMod ("Hclose" with "[Hl]") as "_".
    { iNext. iExists _. iFrame "Hl".
      by iLeft. }
    iModIntro.
    iSpecialize ("IH" with "Hγ").
    wp_match.
    iApply ("IH").
  - iDestruct "Hlv" as "[HQ|Hγ']".
    (* a.d. TODO iCombine as %[] does not work. *)
    2: {
      iCombine "Hγ Hγ'" as "H".
      iPoseProof (own_valid with "H") as "%H".
      destruct (exclusive_l _ _ H).
    }
    iMod ("Hclose" with "[Hl Hγ]") as "_".
    { iNext. iExists _. iFrame "Hl".
      iRight. iExists _. iSplit; first by done. by iRight. }
    iModIntro.
    wp_pures. by iAssumption.
Qed.
End proof.

Typeclasses Opaque join_handle.