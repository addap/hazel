(* protocol_agreement.v

   We introduce the notion of [protocol_agreement]: a logical
   proposition describing which values are allowed to be sent
   as effect arguments when a certain protocol is in place.
*)


From iris.proofmode      Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import lib lang ieff.

(** * Protocol Agreement. *)

Section protocol_agreement.
Context `{!irisGS eff_lang Σ}.

Definition protocol_agreement v Ψ (Φ : val -d> iPropO Σ) :=
  let: P := iEff_car Ψ in
  (∃ Q, P v Q ∗ (∀ w, Q w -∗ Φ w))%I.
Arguments protocol_agreement _%V _%ieff _%I.

Global Instance protocol_agreement_ne v n :
  Proper ((dist n) ==> (dist n) ==> (dist n)) (protocol_agreement v).
Proof.
  intros ??? ???. rewrite /protocol_agreement.
  by repeat (apply H || apply H0 || f_equiv).
Qed.
Global Instance protocol_agreement_proper v :
  Proper ((≡) ==> (≡) ==> (≡)) (protocol_agreement v).
Proof.
  intros ??? ???. apply equiv_dist=>n.
  apply protocol_agreement_ne; by apply equiv_dist.
Qed.

Lemma protocol_agreement_bottom v Φ :
  protocol_agreement v ⊥ Φ ≡ False%I.
Proof.
  rewrite /protocol_agreement.
  iSplit; iIntros "H"; [|done]. by iDestruct "H" as (Q) "[H _]".
Qed.

Lemma protocol_agreement_tele {TT1 TT2 : tele} v
  (v' : TT1 →       val) (P : TT1 →       iProp Σ)
  (w' : TT1 → TT2 → val) (Q : TT1 → TT2 → iProp Σ) Φ :
  protocol_agreement v
    (>>.. x >> ! (v' x)   {{ P x   }};
     <<.. y << ? (w' x y) {{ Q x y }}) Φ ≡
  (∃.. x, ⌜ v = v' x ⌝ ∗ P x ∗
    (∀.. y, Q x y -∗ Φ (w' x y)))%I.
Proof.
  rewrite /protocol_agreement. iSplit.

  - iIntros "H". iDestruct "H" as (Q') "[HP HQ']".
    rewrite iEffPre_texist_eq iEffPre_base_eq /iEffPre_base_def.
    iDestruct "HP" as (x) "(<- & HP & HΦ)". iExists x. iFrame.
    iSplit; [done|]. iIntros (y) "HQ". iApply "HQ'". iApply "HΦ".
    rewrite iEffPost_texist_eq iEffPost_base_eq /iEffPost_base_def.
    iExists y. by iFrame.

  - iIntros "H". iDestruct "H" as (x) "(-> & HP & HQ)".
    iExists (<<.. y << ? (w' x y) {{ Q x y }})%ieff.
    rewrite iEffPre_texist_eq. iSplitL "HP".
    + iExists x. rewrite iEffPre_base_eq /iEffPre_base_def //=. iFrame. by auto.
    + iIntros (w) "HQ'".
      rewrite iEffPost_texist_eq iEffPost_base_eq.
      iDestruct "HQ'" as (y) "[<- HQ']". by iApply "HQ".
Qed.

Lemma protocol_agreement_tele' (TT1 TT2 : tele) v
  (v' : TT1 -t>         val) (P : TT1 -t>         iProp Σ)
  (w' : TT1 -t> TT2 -t> val) (Q : TT1 -t> TT2 -t> iProp Σ) Φ :
  protocol_agreement v
    (>>.. x >> !           (tele_app v' x)
               {{          (tele_app P  x)   }};
     <<.. y << ? (tele_app (tele_app w' x) y)
               {{ tele_app (tele_app Q  x) y }}) Φ ≡
  (∃.. x, ⌜ v = tele_app v' x ⌝ ∗ tele_app P x ∗
     ∀.. y, tele_app (tele_app Q  x) y -∗
         Φ (tele_app (tele_app w' x) y))%I.
Proof. by rewrite (protocol_agreement_tele _ (tele_app v') (tele_app P)
                  (λ x y, tele_app (tele_app w' x) y)
                  (λ x y, tele_app (tele_app Q  x) y)).
Qed.

Lemma protocol_agreement_marker_tele {TT1 TT2 : tele} f v
  (v' : TT1 →       val) (P : TT1 →       iProp Σ)
  (w' : TT1 → TT2 → val) (Q : TT1 → TT2 → iProp Σ) Φ :
  protocol_agreement v
    (f #> (>>.. x >> !    (v' x  )  {{ P x   }};
           <<.. y << ?    (w' x y)  {{ Q x y }})) Φ ≡
  protocol_agreement v
          (>>.. x >> ! (f (v' x  )) {{ P x   }};
           <<.. y << ? (  (w' x y)) {{ Q x y }})  Φ.
Proof. by rewrite iEff_marker_tele. Qed.

Lemma protocol_agreement_marker_intro f v Ψ Φ :
  protocol_agreement v Ψ Φ ⊢ protocol_agreement (f v) (f #> Ψ) Φ.
Proof.
  rewrite /protocol_agreement iEff_marker_eq.
  iIntros "H". iDestruct "H" as (Q) "[He HQ]".
  iExists Q. iFrame. iExists v. by iFrame.
Qed.

Lemma protocol_agreement_marker_elim f {Hf: Inj (=) (=) f} v Ψ Φ :
  protocol_agreement (f v) (f #> Ψ) Φ ⊢ protocol_agreement v Ψ Φ.
Proof.
  iIntros "H". rewrite iEff_marker_eq /protocol_agreement //=.
  iDestruct "H" as (Q) "[HP HQ]".
  iDestruct "HP" as (w') "[% HP]". rewrite (Hf _ _ H).
  iExists Q. by iFrame.
Qed.

Lemma protocol_agreement_marker_elim' f v Ψ Φ :
  protocol_agreement v (f #> Ψ) Φ ⊢ ∃ w, ⌜ v = f w ⌝ ∗ protocol_agreement w Ψ Φ.
Proof.
  iIntros "H". rewrite iEff_marker_eq /protocol_agreement //=.
  iDestruct "H" as (Q) "[HP HQ]". iDestruct "HP" as (w) "[-> HP]".
  iExists w. iSplit; [done|]. iExists Q. by iFrame.
Qed.

Lemma protocol_agreement_filter v P Ψ Φ :
  protocol_agreement v (P ?> Ψ) Φ ⊣⊢ ⌜ P v ⌝ ∗ protocol_agreement v Ψ Φ.
Proof.
  rewrite iEff_filter_eq /protocol_agreement //=. iSplit.
  - iIntros "H". iDestruct "H" as (Q) "[[% HP] HQ]".
    iSplit; [done|]. by eauto with iFrame.
  - iIntros "[% H]". iDestruct "H" as (Q) "[HP HQ]".
    by eauto with iFrame.
Qed.

Lemma protocol_agreement_sum_assoc v Ψ1 Ψ2 Ψ3 Φ :
  protocol_agreement v (Ψ1 <+> (Ψ2 <+> Ψ3)) Φ ≡
    protocol_agreement v ((Ψ1 <+> Ψ2) <+> Ψ3) Φ.
Proof. by rewrite iEff_sum_assoc. Qed.

Lemma protocol_agreement_sum_comm v Ψ1 Ψ2 Φ :
  protocol_agreement v (Ψ2 <+> Ψ1) Φ ≡ protocol_agreement v (Ψ1 <+> Ψ2) Φ.
Proof. by rewrite iEff_sum_comm. Qed.

Lemma protocol_agreement_sum_intro_l v Ψ1 Ψ2 Φ :
  protocol_agreement v Ψ1 Φ ⊢ protocol_agreement v (Ψ1 <+> Ψ2) Φ.
Proof.
  rewrite /protocol_agreement iEff_sum_eq.
  iIntros "H". iDestruct "H" as (Q) "[He HQ]". iExists Q. by iFrame.
Qed.

Lemma protocol_agreement_sum_intro_r v Ψ1 Ψ2 Φ :
  protocol_agreement v Ψ2 Φ ⊢ protocol_agreement v (Ψ1 <+> Ψ2) Φ.
Proof.
  iIntros "H". rewrite protocol_agreement_sum_comm.
  by iApply protocol_agreement_sum_intro_l.
Qed.

Lemma protocol_agreement_sum_elim v Ψ1 Ψ2 Φ :
  protocol_agreement v (Ψ1 <+> Ψ2) Φ ⊢
    (protocol_agreement v Ψ1 Φ) ∨ (protocol_agreement v Ψ2 Φ).
Proof.
  iIntros "H". iDestruct "H" as (Q) "[HP HQ]".
  rewrite iEff_sum_eq. iDestruct "HP" as "[HP|HP]".
  { iLeft;  iExists Q; by iFrame. }
  { iRight; iExists Q; by iFrame. }
Qed.

Lemma protocol_agreement_mono v (Ψ : iEff Σ) Φ1 Φ2 :
  (protocol_agreement v Ψ Φ1 -∗ (∀ w, Φ1 w -∗ Φ2 w) -∗
   protocol_agreement v Ψ Φ2)%ieff.
Proof.
  iIntros "Hprot_agr HΦ2". iDestruct "Hprot_agr" as (Φ0) "[HP HΦ1]".
  iExists Φ0. iFrame. iIntros (w) "HΦ0". iApply "HΦ2". by iApply "HΦ1".
Qed.

End protocol_agreement.


(** * Protocol Ordering. *)

Program Definition iEff_le {Σ} : iEffO -n> iEffO -n> iPropO Σ :=
  λne Ψ1 Ψ2,
    (□ (∀ v Φ, protocol_agreement v Ψ1 Φ -∗ protocol_agreement v Ψ2 Φ))%I.
Next Obligation. intros ??????. repeat (apply iEff_car_ne || f_equiv); done. Defined.
Next Obligation. intros ??????. simpl. repeat (apply iEff_car_ne || f_equiv); done. Defined.
(*Arguments iEff_le {_} _%ieff _%ieff.*)
Instance: Params (@iEff_le) 3 := {}.

Infix "⊑" := (iEff_le) (at level 70, only parsing) : ieff_scope.

Section protocol_ordering.
Context {Σ : gFunctors}.

Global Instance iEff_le_ne n :
  Proper ((dist n) ==> (dist n)) (iEff_le (Σ:=Σ)).
Proof.
  rewrite /iEff_le. intros ????.
  repeat (apply iEff_car_ne || f_equiv); done.
Qed.
Global Instance iEff_le_proper :  Proper ((≡) ==> (≡)) (iEff_le (Σ:=Σ)).
Proof.
  intros ????. apply equiv_dist=>n; apply iEff_le_ne; by apply equiv_dist.
Qed.

Lemma iEff_le_bottom (Ψ : iEff Σ) : ⊢ (⊥ ⊑ Ψ)%ieff.
Proof. iModIntro. iIntros (v Φ) "H". by rewrite protocol_agreement_bottom. Qed.

Lemma iEff_le_refl (Ψ : iEff Σ) : ⊢ (Ψ ⊑ Ψ)%ieff.
Proof. iModIntro. by iIntros (v Φ) "H". Qed.

Lemma iEff_le_trans (Ψ1 Ψ2 Ψ3 : iEff Σ) : (Ψ1 ⊑ Ψ2 -∗ Ψ2 ⊑ Ψ3 -∗ Ψ1 ⊑ Ψ3)%ieff.
Proof.
  iIntros "#H12 #H23". iModIntro. iIntros (v Φ) "H1".
  iApply "H23". by iApply "H12".
Qed.

Lemma iEff_le_sum_l (Ψ1 Ψ2 : iEff Σ) : ⊢ (Ψ1 ⊑ Ψ1 <+> Ψ2)%ieff.
Proof. iModIntro. iIntros (v Φ) "H". by iApply protocol_agreement_sum_intro_l. Qed.

Lemma iEff_le_sum_r (Ψ1 Ψ2 : iEff Σ) : ⊢ (Ψ2 ⊑ Ψ1 <+> Ψ2)%ieff.
Proof. rewrite (iEff_sum_comm Ψ1 Ψ2). by iApply iEff_le_sum_l. Qed.

Lemma iEff_le_sum (Ψ1 Ψ2 Ψ1' Ψ2' : iEff Σ) :
  (Ψ1 ⊑ Ψ1' -∗ Ψ2 ⊑ Ψ2' -∗ Ψ1 <+> Ψ2 ⊑ Ψ1' <+> Ψ2')%ieff.
Proof.
  iIntros "#HΨ1 #HΨ2". iModIntro. iIntros (v Φ) "Hprot".
  iDestruct (protocol_agreement_sum_elim with "Hprot") as "[Hprot|Hprot]".
  { iApply protocol_agreement_sum_intro_l. by iApply "HΨ1". }
  { iApply protocol_agreement_sum_intro_r. by iApply "HΨ2". }
Qed.

Lemma iEff_le_marker f (Ψ1 Ψ2 : iEff Σ) : (Ψ1 ⊑ Ψ2 -∗ (f #> Ψ1) ⊑ (f #> Ψ2))%ieff.
Proof.
  iIntros "#HΨ". iModIntro. iIntros (v Φ) "Hprot".
  iDestruct (protocol_agreement_marker_elim' with "Hprot") as (w) "[-> Hprot]".
  iApply protocol_agreement_marker_intro. by iApply "HΨ".
Qed.

Lemma iEff_le_tele {TT1 TT2 TT1' TT2' : tele}
  (v  : TT1  →        val) (P  : TT1  →        iProp Σ)
  (w  : TT1  → TT2  → val) (Q  : TT1  → TT2  → iProp Σ)
  (v' : TT1' →        val) (P' : TT1' →        iProp Σ)
  (w' : TT1' → TT2' → val) (Q' : TT1' → TT2' → iProp Σ) :
   ((>>.. x  >> ! (v  x   )  {{ P  x     }};
     <<.. y  << ? (w  x  y)  {{ Q  x  y  }})
      ⊑
    (>>.. x' >> ! (v' x'   ) {{ P' x'    }};
     <<.. y' << ? (w' x' y') {{ Q' x' y' }}))%ieff
   ⊣⊢
     □ (∀.. x,  P  x     -∗ (∃.. x', P' x'  ∗ ⌜ v x   = v' x'    ⌝ ∗
       (∀.. y', Q' x' y' -∗ (∃.. y,  Q  x y ∗ ⌜ w x y = w' x' y' ⌝)))).
Proof.
  iSplit; iIntros "#Hle"; iModIntro.
  - iIntros (x) "HP".
    iSpecialize ("Hle" $! (v x) (<<..y<<?(w x y){{Q x y}})%ieff with "[HP]").
    { iExists (<<..y<<?(w x y){{Q x y}})%ieff.
      rewrite iEffPre_texist_eq iEffPre_base_eq.
      iSplitL; [iExists x; iFrame|]; by auto. }
    iDestruct "Hle" as (Φ) "[HP HQ]".
    rewrite iEffPre_texist_eq iEffPre_base_eq.
    iDestruct "HP" as (x') "[<- [HP HΦ]]". iExists x'. iFrame.
    iSplit; [done|]. iIntros (y') "HQ'".
    iSpecialize ("HΦ" $! (w' x' y') with "[HQ']").
    { rewrite iEffPost_texist_eq iEffPost_base_eq. iExists y'. by iFrame. }
    iSpecialize ("HQ" with "HΦ").
    rewrite iEffPost_texist_eq iEffPost_base_eq.
    iDestruct "HQ" as (y) "[<- HQ]". iExists y. by iFrame.
  - iIntros (u Φ) "Hprot".
    iDestruct "Hprot" as (Φ') "[HP HΦ']".
    rewrite iEffPre_texist_eq iEffPre_base_eq.
    iDestruct "HP" as (x) "[<- [HP HΦ]]".
    iDestruct ("Hle" with "HP") as (x') "(HP' & -> & HQ)". iClear "Hle".
    iExists (<<.. y<< ?(w x y){{ Q x y }})%ieff.
    iSplitR "HΦ HΦ'".
    { rewrite iEffPre_texist_eq. iExists x'. iFrame. iSplit; [done|].
      iIntros (u') "HQ'". rewrite !iEffPost_texist_eq iEffPost_base_eq.
      iDestruct "HQ'" as (y') "[<- HQ']".
      iDestruct ("HQ" with "HQ'") as (y) "[HQ <-]".
      iExists y. by iFrame. }
    { iIntros (u) "HQ'". iApply "HΦ'". by iApply "HΦ". }
Qed.

End protocol_ordering.


(** * Monotonicity. *)

Section protocol_agreement_monotonicity.
Context `{!irisGS eff_lang Σ}.

Lemma protocol_agreement_strong_mono v (Ψ1 Ψ2 : iEff Σ) Φ1 Φ2 :
  (protocol_agreement v Ψ1 Φ1 -∗ Ψ1 ⊑ Ψ2 -∗ (∀ v, Φ1 v -∗ Φ2 v) -∗
   protocol_agreement v Ψ2 Φ2)%ieff.
Proof.
  iIntros "Hprot_agr #HΨ HΦ". iApply "HΨ".
  by iApply (protocol_agreement_mono with "Hprot_agr HΦ").
Qed.

End protocol_agreement_monotonicity.
