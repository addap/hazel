From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
(* From iris.program_logic Require Export language. *)
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From iris.bi Require Export weakestpre.
From iris.prelude Require Import options.
From program_logic Require Import state_interpretation weakest_precondition basic_reasoning_rules.
Import uPred.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!heapGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types v : val .
  Implicit Types e : expr .

  Global Instance frame_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed. 

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p E e P Φ :
    TCEq (to_eff e) None → 
    ElimModal True p false (|==> P) P (EWP e @ E {{ Φ }}) (EWP e @ E {{ Φ }}).
  Proof.
    intros HEq.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_ewp.
  Qed.

  Global Instance elim_modal_fupd_wp p E e P Φ :
    TCEq (to_eff e) None → 
    ElimModal True p false (|={E}=> P) P (EWP e @ E {{ Φ }}) (EWP e @ E {{ Φ }}).
  Proof.
    intros HEq.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_ewp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p E1 E2 e P Φ :
    TCEq (to_eff e) None → 
    ElimModal (Atomic StronglyAtomic e) p false
            (|={E1,E2}=> P) P
            (EWP e @ E1 {{ Φ }}) (EWP e @ E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof.
    intros ??. rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r. by apply ewp_atomic.
  Qed.

  Global Instance add_modal_fupd_wp E e P Φ :
    TCEq (to_eff e) None → 
    AddModal (|={E}=> P) P (EWP e @ E {{ Φ }}).
  Proof. intros ?. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_ewp. Qed.

  Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e Φ :
    TCEq (to_eff e) None → 
    ElimAcc (X:=X) (Atomic StronglyAtomic e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (EWP e @ E1 {{ Φ }})
            (λ x, EWP e @ E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I | 100.
  Proof.
    iIntros (??) "Hinner >Hacc".
    iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (ewp_mono with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    TCEq (to_eff e) None → 
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (? _) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.