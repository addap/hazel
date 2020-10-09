(* protocol_agreement.v

   We introduce the notion of [protocol_agreement] which intuitevely
   states when a value can be raised as the argument of an effect.

   This definition is very important because it is endowed of a
   proof theory that when correctly manipulated allows the user
   to never rely on the semantic model of protocols.
*)


From iris.proofmode      Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import lib lang ieff.

(** * Protocol Agreement. *)

Section protocol_agreement.
Context `{!irisG eff_lang Σ}.

(* Comment: In defining [protocol_agreement], we could have followed a
            different approach by removing the fancy update modalities
            and letting the user decide when to introduce them.
            Here we choose to follow the same approach as in the
            definition of [ewp]. *)

Definition protocol_agreement E v Ψ (Φ : val -d> iPropO Σ) :=
  (|={E,∅}=>
    let: P := iEff_car Ψ in
    ∃ Q, P v Q ∗ (∀ w, Q w ={∅,E}=∗ Φ w))%I.
Arguments protocol_agreement _ _%V _%ieff _%I.

Global Instance protocol_agreement_ne E v n :
  Proper ((dist n) ==> (dist n) ==> (dist n)) (protocol_agreement E v).
Proof.
  intros ??? ???. rewrite /protocol_agreement.
  by repeat (apply H || apply H0 || f_equiv).
Qed.
Global Instance protocol_agreement_proper E v :
  Proper ((≡) ==> (≡) ==> (≡)) (protocol_agreement E v).
Proof.
  intros ??? ???. apply equiv_dist=>n.
  apply protocol_agreement_ne; by apply equiv_dist.
Qed.

Lemma protocol_agreement_bottom E v Φ :
  protocol_agreement E v ⊥ Φ ≡ (|={E,∅}=> False)%I.
Proof.
  rewrite /protocol_agreement. f_equiv.
  iSplit; iIntros "H"; [|done]. by iDestruct "H" as (Q) "[H _]".
Qed.

Lemma protocol_agreement_tele {TT1 TT2 : tele} E v
  (v' : TT1 →       val) (P : TT1 →       iProp Σ)
  (w' : TT1 → TT2 → val) (Q : TT1 → TT2 → iProp Σ) Φ :
  protocol_agreement E v
    (>>.. x >> ! (v' x)   {{ P x   }};
     <<.. y << ? (w' x y) {{ Q x y }}) Φ ≡
  (|={E,∅}=>
    (∃.. x, ⌜ v = v' x ⌝ ∗ P x ∗
      (∀.. y, Q x y ={∅,E}=∗ Φ (w' x y))))%I.
Proof.
  rewrite /protocol_agreement. f_equiv. iSplit.

  - iIntros "H". iDestruct "H" as (Q') "[HP HQ']".
    rewrite iEffPre_texist_eq iEffPre_base_eq /iEffPre_base_def.
    iDestruct "HP" as (x) "(<- & HP & #Heq)". iExists x. iFrame.
    iSplit; [done|]. iIntros (y) "HQ". iApply "HQ'".
    rewrite discrete_fun_equivI. iRewrite ("Heq" $! (w' x y)). iClear "Heq".
    rewrite iEffPost_texist_eq iEffPost_base_eq /iEffPost_base_def.
    iExists y. by iFrame.

  - iIntros "H". iDestruct "H" as (x) "(-> & HP & HQ)".
    iExists (<<.. y << ? (w' x y) {{ Q x y }})%ieff.
    rewrite iEffPre_texist_eq. iSplitL "HP".
    + iExists x. rewrite iEffPre_base_eq /iEffPre_base_def //=. by iFrame.
    + iIntros (w) "HQ'".
      rewrite iEffPost_texist_eq iEffPost_base_eq.
      iDestruct "HQ'" as (y) "[<- HQ']". by iApply "HQ".
Qed.

Lemma protocol_agreement_tele' (TT1 TT2 : tele) E v
  (v' : TT1 -t>         val) (P : TT1 -t>         iProp Σ)
  (w' : TT1 -t> TT2 -t> val) (Q : TT1 -t> TT2 -t> iProp Σ) Φ :
  protocol_agreement E v
    (>>.. x >> !           (tele_app v' x)
               {{          (tele_app P  x)   }};
     <<.. y << ? (tele_app (tele_app w' x) y)
               {{ tele_app (tele_app Q  x) y }}) Φ ≡
  (|={E,∅}=>
     ∃.. x, ⌜ v = tele_app v' x ⌝ ∗ tele_app P x ∗
       ∀.. y, tele_app (tele_app Q  x) y ={∅,E}=∗
           Φ (tele_app (tele_app w' x) y))%I.
Proof. by rewrite (protocol_agreement_tele E _ (tele_app v') (tele_app P)
                  (λ x y, tele_app (tele_app w' x) y)
                  (λ x y, tele_app (tele_app Q  x) y)).
Qed.

Lemma protocol_agreement_marker_tele {TT1 TT2 : tele} E f v
  (v' : TT1 →       val) (P : TT1 →       iProp Σ)
  (w' : TT1 → TT2 → val) (Q : TT1 → TT2 → iProp Σ) Φ :
  protocol_agreement E v
    (f #> (>>.. x >> !    (v' x  )  {{ P x   }};
           <<.. y << ?    (w' x y)  {{ Q x y }})) Φ ≡
  protocol_agreement E v
          (>>.. x >> ! (f (v' x  )) {{ P x   }};
           <<.. y << ? (  (w' x y)) {{ Q x y }})  Φ.
Proof. by rewrite iEff_marker_tele. Qed.

Lemma protocol_agreement_marker_intro E f v Ψ Φ :
  protocol_agreement E v Ψ Φ ⊢ protocol_agreement E (f v) (f #> Ψ) Φ.
Proof.
  rewrite /protocol_agreement iEff_marker_eq.
  iIntros "H". iMod "H" as (Q) "[He HQ]".
  iExists Q. iFrame. iExists v. by iFrame.
Qed.

Lemma protocol_agreement_marker_elim E f {Hf: Inj (=) (=) f} v Ψ Φ :
  protocol_agreement E (f v) (f #> Ψ) Φ ⊢ protocol_agreement E v Ψ Φ.
Proof.
  iIntros "H". rewrite iEff_marker_eq /protocol_agreement //=.
  iMod "H" as (Q) "[HP HQ]".
  iDestruct "HP" as (w') "[% HP]". rewrite (Hf _ _ H).
  iModIntro. iExists Q. by iFrame.
Qed.

Lemma protocol_agreement_sum_assoc E v Ψ1 Ψ2 Ψ3 Φ :
  protocol_agreement E v (Ψ1 <+> (Ψ2 <+> Ψ3)) Φ ≡
    protocol_agreement E v ((Ψ1 <+> Ψ2) <+> Ψ3) Φ.
Proof. by rewrite iEff_sum_assoc. Qed.

Lemma protocol_agreement_sum_comm E v Ψ1 Ψ2 Φ :
  protocol_agreement E v (Ψ2 <+> Ψ1) Φ ≡ protocol_agreement E v (Ψ1 <+> Ψ2) Φ.
Proof. by rewrite iEff_sum_comm. Qed.

Lemma protocol_agreement_sum_intro_l E v Ψ1 Ψ2 Φ :
  protocol_agreement E v Ψ1 Φ ⊢ protocol_agreement E v (Ψ1 <+> Ψ2) Φ.
Proof.
  rewrite /protocol_agreement iEff_sum_eq.
  iIntros "H". iMod "H" as (Q) "[He HQ]". iExists Q. by iFrame.
Qed.

Lemma protocol_agreement_sum_intro_r E v Ψ1 Ψ2 Φ :
  protocol_agreement E v Ψ2 Φ ⊢ protocol_agreement E v (Ψ1 <+> Ψ2) Φ.
Proof.
  iIntros "H". rewrite protocol_agreement_sum_comm.
  by iApply protocol_agreement_sum_intro_l.
Qed.

Lemma protocol_agreement_sum_elim E (f g : val → val)
  {Hf: Marker f} {Hg: Marker g} {Hfg: DisjRange f g} v Ψ1 Ψ2 Φ :
  protocol_agreement E v ((f #> Ψ1) <+> (g #> Ψ2)) Φ ⊢
    (protocol_agreement E v (f #> Ψ1) Φ) ∨
    (protocol_agreement E v (g #> Ψ2) Φ).
Proof.
  iAssert (∀ (f g : val → val) (Hfg: DisjRange f g) v Ψ1 Ψ2,
    (protocol_agreement E (f v) ((f #> Ψ1) <+> (g #> Ψ2)) Φ -∗
      (protocol_agreement E (f v) (f #> Ψ1) Φ)))%I
  as "Haux".
  { clear Hfg Hf Hg f g v Ψ1 Ψ2. iIntros (f g Hfg v Ψ1 Ψ2) "H".
    rewrite iEff_marker_eq iEff_sum_eq /protocol_agreement //=.
    iMod "H" as (Q) "[HP HQ]". iDestruct "HP" as "[HP|HP]".
    - iModIntro. iDestruct "HP" as (v') "[% HP]".
      iExists Q. iFrame. iExists v'. by iFrame.
    - iClear "HQ". iDestruct "HP" as (v') "[% _]".
      by destruct (disj_range v v' H). }

  iIntros "H".
  case (@marker_dec_range _ _ _ _ f Hf v) as [(v' & Hv')|Hf']; [|
  case (@marker_dec_range _ _ _ _ g Hg v) as [(v' & Hv')|Hg']];
  try inversion Hv'.
  { iLeft. iSpecialize ("Haux" $! f g Hfg). by iApply "Haux". }
  { iRight. rewrite protocol_agreement_sum_comm.
    have Hgf: (DisjRange g f). by apply DisjRange_comm.
    iSpecialize ("Haux" $! g f Hgf). by iApply "Haux". }
  { iLeft. rewrite iEff_sum_eq iEff_marker_eq.
    iMod "H" as (Q) "[HP _]". iDestruct "HP" as "[HP|HP]";
    iDestruct "HP" as (w) "[-> _]"; [case (Hf' w)|case (Hg' w)]; done. }
Qed.

Lemma protocol_agreement_strong_mono E1 E2 v (Ψ1 Ψ2 : iEff Σ) Φ1 Φ2 :
  E1 ⊆ E2 →
  (protocol_agreement E1 v Ψ1 Φ1
     -∗ Ψ1 ⊑ Ψ2 -∗ (∀ v, Φ1 v ={E2}=∗ Φ2 v) -∗
   protocol_agreement E2 v Ψ2 Φ2)%ieff.
Proof.
  iIntros (HE) "Hprot_agr #HΨ HΦ".
  iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
  iMod "Hprot_agr" as (Q) "[HP Hk]".
  iDestruct ("HΨ" with "HP") as (Q') "[HP' HQ]".
  iModIntro. iExists Q'. iFrame. iIntros (w) "HQ'".
  iSpecialize ("HQ" with "HQ'"). iSpecialize ("Hk" with "HQ").
  iMod "Hk". iMod "Hclose". by iApply "HΦ".
Qed.

Lemma protocol_agreement_mono E v (Ψ1 Ψ2 : iEff Σ) Φ :
  (protocol_agreement E v Ψ1 Φ -∗ Ψ1 ⊑ Ψ2 -∗
   protocol_agreement E v Ψ2 Φ)%ieff.
Proof.
  iIntros "H #HΨ".
  by iApply (protocol_agreement_strong_mono with "H"); auto.
Qed.

Lemma protocol_agreement_mask_mono E1 E2 v Ψ Φ :
  E1 ⊆ E2 →
    protocol_agreement E1 v Ψ Φ -∗
    protocol_agreement E2 v Ψ Φ.
Proof.
  iIntros (HE) "H".
  iApply (protocol_agreement_strong_mono with "H"); auto.
  { by iApply iEff_le_refl. }
Qed.

End protocol_agreement.
