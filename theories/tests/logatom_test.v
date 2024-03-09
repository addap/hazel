From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
(* From iris.base_logic.lib Require Export invariants. *)
(* From iris.program_logic Require Export atomic. *)
(* From iris.heap_lang Require Import proofmode notation atomic_heap par. *)
From iris.prelude Require Import options.
From program_logic Require Import reasoning_rules logatom.

(* From iris.proofmode Require Import base tactics classes. *)
(* From iris.algebra Require Import excl_auth gset gmap agree csum frac excl. *)
From iris.base_logic Require Import invariants.

(** Show that implementing fetch-and-add on top of CAS preserves logical
atomicity. *)

(** First: logically atomic increment directly on top of the physical heap. *)
(* a.d. This file is from iris_heap_lang/iris/lib/increment.v *)

Section increment_physical.
  Context `{!heapGS Σ}.

  Definition incr_phy : val :=
    (rec: "incr" "l" :=
       let: "oldv" := Load "l" in
       if: Snd (CmpXchg "l" "oldv" ("oldv" + #1))
         then "oldv" (* return old value if success *)
         else "incr" "l")%V.

  Lemma incr_phy_spec (l: loc) :
    ⊢ <<< ∀ (v : Z), l ↦ #v >>> incr_phy #l @ ∅ <<< l ↦ #(v + 1), RET #v >>>.
  Proof.
    Unset Printing Notations.
    iIntros (Φ) "AU". iLöb as "IH". 
    rewrite /incr_phy.
    ewp_pure_steps.
    ewp_bind_rule. simpl.
    iMod "AU" as (v) "[Hl [Hclose _]]".
    iApply (ewp_load with "Hl").
    iIntros "!> Hl !>".
    iMod ("Hclose" with "Hl") as "AU". iModIntro.
    ewp_pure_steps.
    iApply (ewp_bind' (IfCtx _ _)); [done|]. simpl.
    iApply (ewp_bind' SndCtx); [done|]. simpl.
    iApply (ewp_bind' (CmpXchgRCtx #l #v)). 1: done. simpl.
    (* a.d. TODO is bin_op_eval broken? (#v + #1) should have reduced to #(v + 1) before I even bind IfCtx. *)
    ewp_pure_steps; first done.
    iMod "AU" as (w) "[Hl Hclose]".
    destruct (decide (#v = #w)) as [[= ->]|Hx].
    - iApply (ewp_cmpxchg_suc with "Hl"); first by done. 
      (* a.d. something also seems broken here. done does not solve "True ∨ True". *)
      1: { simpl. by left. }
      iIntros "!> Hl !>".
      iDestruct "Hclose" as "[_ Hclose]". iMod ("Hclose" with "Hl") as "HΦ".
      iModIntro. ewp_pure_steps. done.
    - iApply (ewp_cmpxchg_fail with "Hl"); first by done.
      1: { simpl. by left. }
      iIntros "!> Hl !>".
      iDestruct "Hclose" as "[Hclose _]". iMod ("Hclose" with "Hl") as "AU".
      iModIntro. do 3 ewp_value_or_step. iApply "IH". done.
  Qed.
End increment_physical.

(** Next: logically atomic increment on top of an arbitrary logically atomic heap *)

Section increment_client.
  Context `{!heapGS Σ, !spawnG Σ}.

  Definition incr_client : val :=
    (λ: "x",
       let: "l" := ref "x" in
       incr_phy "l")%V.

  Lemma incr_client_safe (x: Z):
    ⊢ EWP incr_client #x {{ _, True }}.
  Proof using Type*.
    rewrite /incr_client.
    ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply ewp_alloc.
    iIntros "!>" (l) "Hl !>".
    iMod (inv_alloc nroot _ (∃x':Z, l ↦ #x')%I with "[Hl]") as "#Hinv"; first eauto.
    ewp_pure_steps.
    iApply incr_phy_spec. iAuIntro.
    clear x.
    iInv nroot as (x) ">H↦". iAaccIntro with "H↦"; first by eauto 10.
    iIntros "H↦ !>". iSplitL "H↦"; first by eauto 10.
    (* The continuation: From after the atomic triple to the postcondition of the WP *)
    done.
  Qed.

End increment_client.