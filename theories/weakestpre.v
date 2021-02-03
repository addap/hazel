(* weakestpre.v

   We define a notion of weakest precondition that is adapted
   to effects and their handlers. Most of this theory is
   dedicated to the proof of our version of the usual separation
   logic reasoning rules. In the end, we prove a novel reasoning
   rule for the [TryWith] construct of the language.
*)

From iris.proofmode      Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Export lib lang ieff protocol_agreement.

(** * Weakest Precondition. *)

Definition ewp_pre `{!irisG eff_lang Σ} :
  (coPset -d> expr -d> iEff Σ -d> (val -d> iPropO Σ) -d> iPropO Σ) →
  (coPset -d> expr -d> iEff Σ -d> (val -d> iPropO Σ) -d> iPropO Σ)
  := λ ewp E e₁ Ψ Φ,
  match to_val e₁ with Some  v     => |={E}=> Φ v | None =>
  match to_eff e₁ with Some (v, k) =>
    protocol_agreement v Ψ (λ w, ▷ ewp E (fill k (Val w)) Ψ Φ)
  | None =>
    ∀ σ₁ ks n,
     state_interp σ₁ ks n ={E,∅}=∗
       ⌜ reducible e₁ σ₁ ⌝ ∗ 
       ∀ e₂ σ₂, ⌜ prim_step e₁ σ₁ e₂ σ₂ ⌝ ={∅}=∗ ▷ |={∅,E}=>
         state_interp σ₂ ks n ∗ ewp E e₂ Ψ Φ
  end
  end%I.

Local Instance ewp_pre_contractive `{!irisG eff_lang Σ} : Contractive ewp_pre.
Proof.
  rewrite /ewp_pre /from_option /protocol_agreement=> n ewp ewp' Hwp E e Ψ Φ.
  repeat (f_contractive || f_equiv); try apply Hwp.
Qed.
Definition ewp_def `{!irisG eff_lang Σ} :
  coPset -d> expr -d> iEff Σ -d> (val -d> iPropO Σ) -d> iPropO Σ :=
  fixpoint ewp_pre.
Definition ewp_aux `{!irisG eff_lang Σ} : seal ewp_def. Proof. by eexists. Qed.
Definition ewp_eq `{!irisG eff_lang Σ} := ewp_aux.(seal_eq).

(* Notation. *)

Notation "'EWP' e @ E {{ Φ } }" :=
  (ewp_def E e%E iEff_bottom Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ '|' '>'  {{ Φ } }" :=
  (ewp_def E e%E Ψ%ieff Φ)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ  '|' '>'  {{  Φ  } } ']' ']'") : bi_scope.

Notation "'EWP' e @ E {{ v , Φ } }" :=
  (ewp_def E e%E iEff_bottom (λ v, Φ)%I)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  {{  v ,  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ '|' '>'  {{ v , Φ } }" :=
  (ewp_def E e%E Ψ%ieff (λ v, Φ)%I)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ  '|' '>'  {{  v ,  Φ  } } ']' ']'") : bi_scope.

Notation "'EWP' e {{ Φ } }" :=
  (ewp_def ⊤ e%E iEff_bottom Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e <| Ψ '|' '>'  {{ Φ } }" :=
  (ewp_def ⊤ e%E Ψ%ieff Φ)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' <|  Ψ  '|' '>'  {{  Φ  } } ']' ']'") : bi_scope.

Notation "'EWP' e {{ v , Φ } }" :=
  (ewp_def ⊤ e%E iEff_bottom (λ v, Φ)%I)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' {{  v ,  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e <| Ψ '|' '>'  {{ v , Φ } }" :=
  (ewp_def ⊤ e%E Ψ%ieff (λ v, Φ)%I)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' <|  Ψ  '|' '>'  {{  v ,  Φ  } } ']' ']'") : bi_scope.


Section ewp.
Context `{!irisG eff_lang Σ}.


(* Non-expansiveness of EWP and simple lemmas. *)

Lemma ewp_unfold E e Ψ Φ : EWP e @ E <| Ψ |> {{ Φ }} ⊣⊢ ewp_pre ewp_def E e Ψ Φ.
Proof. unfold ewp_def. apply (fixpoint_unfold ewp_pre). Qed.

Global Instance ewp_ne E e n :
  Proper ((dist n) ==> (dist n) ==> (dist n)) (ewp_def E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Ψ Ψ' HΨ Φ Φ' HΦ.
  rewrite !ewp_unfold /ewp_pre /protocol_agreement.
  f_equiv. { by f_equiv. }
  do 6 f_equiv.
  - by apply HΨ.
  - intros ?. do 2 (f_contractive || f_equiv).
    apply IH; try lia; eapply dist_le; eauto with lia.
  - do 13 (f_contractive || f_equiv).
    apply IH; try lia; eapply dist_le; eauto with lia.
Qed.

Global Instance ewp_proper E e : Proper ((≡) ==> (≡) ==> (≡)) (ewp_def E e).
Proof.
  by intros Ψ Ψ' ? Φ Φ' ?; apply equiv_dist=>n; apply ewp_ne; apply equiv_dist.
Qed.


(** * Derived Reasoning Rules. *)

Lemma ewp_value E Ψ Φ v : Φ v ⊢ EWP of_val v @ E <| Ψ |> {{ Φ }}.
Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.
Lemma ewp_value_inv E Ψ Φ v :
  EWP of_val v @ E <| Ψ |> {{ Φ }} ={E}=∗ Φ v.
Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.
Lemma ewp_value_fupd E Ψ Φ v :
  (|={E}=> Φ v)%I ⊢ EWP of_val v @ E <| Ψ |> {{ Φ }}.
Proof. intros. by rewrite !ewp_unfold /ewp_pre. Qed.
Lemma ewp_eff_eq E Ψ Φ v k :
  protocol_agreement v Ψ (λ w, ▷ EWP fill k (Val w) @ E <| Ψ |> {{ Φ }}) ⊣⊢
  EWP of_eff v k @ E <| Ψ |> {{ Φ }}.
Proof. by rewrite ewp_unfold /ewp_pre /=. Qed.
Lemma ewp_eff E Ψ Φ v k :
  protocol_agreement v Ψ (λ w, ▷ EWP fill k (Val w) @ E <| Ψ |> {{ Φ }}) ⊢
  EWP of_eff v k @ E <| Ψ |> {{ Φ }}.
Proof. by rewrite ewp_eff_eq. Qed.
Lemma ewp_eff_inv E Ψ Φ v k :
  EWP of_eff v k @ E <| Ψ |> {{ Φ }} ⊢
  protocol_agreement v Ψ (λ w, ▷ EWP fill k (Val w) @ E <| Ψ |> {{ Φ }}).
Proof. by rewrite ewp_eff_eq. Qed.

Goal forall A (P : A → iProp Σ) Φ (Ψ : iEff Σ) (v : val) x,
  (P x -∗
  EWP (Eff v EmptyCtx)
    <| >> x >> ! v {{ P x }};
       << w << ? w {{ Φ w }}
    |>
    {{ w, Φ w }})%ieff.
Proof.
  intros A P Φ Ψ v x.
  iIntros "HP". iApply ewp_eff.
  rewrite (protocol_agreement_tele' [tele _] [tele _]) //=.
  iExists x. iFrame.
  iSplit; [done|]. iIntros (w) "HΦ". iNext.
  by iApply ewp_value.
Qed.

(* Monotonicity and the frame rule. *)

Lemma ewp_strong_mono E1 E2 Ψ1 Ψ2 Φ1 Φ2 e :
  E1 ⊆ E2 →
  EWP e @ E1 <| Ψ1 |> {{ Φ1 }} -∗ (Ψ1 ⊑ Ψ2)%ieff -∗ (∀ v, Φ1 v ={E2}=∗ Φ2 v) -∗
  EWP e @ E2 <| Ψ2 |> {{ Φ2 }}.
Proof.
  iIntros (HE) "Hewp #HΨ HΦ". iLöb as "IH" forall (e).
    destruct (to_val e) as [ v    |] eqn:?;
  [|destruct (to_eff e) as [(v, k)|] eqn:?].
  - rewrite !ewp_unfold /ewp_pre Heqo.
    iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _).
  - rewrite -(of_to_eff _ _ _ Heqo0) -!ewp_eff_eq.
    iApply (protocol_agreement_strong_mono with "Hewp"); auto.
    iIntros (w) "Hk". iNext.
    by iApply ("IH" with "Hk HΦ").
  - rewrite !ewp_unfold /ewp_pre Heqo Heqo0.
    iIntros (σ₁ ks n) "Hσ". iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
    iMod ("Hewp" with "[$]") as "[$ H]".
    iModIntro. iIntros (e₂ σ₂ Hstep).
    iMod ("H" with "[//]") as "H". iIntros "!> !>".
    iMod "H" as "(Hσ & Hewp)".
    iMod "Hclose" as "_". iModIntro. iFrame "Hσ".
    by iApply ("IH" with "Hewp HΦ").
Qed.

Lemma ewp_mono E Ψ Φ Φ' e :
  (∀ v, Φ v ⊢ |={E}=> Φ' v) →
    EWP e @ E <| Ψ |> {{ Φ }} ⊢ EWP e @ E <| Ψ |> {{ Φ' }}.
Proof.
  iIntros (HΦ) "H"; iApply (ewp_strong_mono with "H"); first done.
  { by iApply iEff_le_refl. } { iIntros (v) "?". by iApply HΦ. }
Qed.

Lemma ewp_mono' E Ψ Φ Φ' e :
  EWP e @ E <| Ψ |> {{ Φ  }} -∗ (∀ v, Φ v ={E}=∗ Φ' v) -∗
  EWP e @ E <| Ψ |> {{ Φ' }}.
Proof.
  iIntros "H HΦ"; iApply (ewp_strong_mono with "H"); first done.
  { by iApply iEff_le_refl. } { iIntros (v) "?". by iApply "HΦ". }
Qed.

Lemma ewp_mask_mono E1 E2 e Ψ Φ :
  E1 ⊆ E2 → EWP e @ E1 <| Ψ |> {{ Φ }} ⊢ EWP e @ E2 <| Ψ |> {{ Φ }}.
Proof.
  iIntros (?) "H"; iApply (ewp_strong_mono with "H"); auto.
  { by iApply iEff_le_refl. }
Qed.

Lemma ewp_frame_r E R Ψ Φ e :
  EWP e @ E <| Ψ |> {{ v, Φ v }} ∗ R ⊢
  EWP e @ E <| Ψ |> {{ v, Φ v    ∗ R }}.
Proof.
  iIntros "[H HR]"; iApply (ewp_strong_mono with "H"); first done.
  { by iApply iEff_le_refl. } { iIntros (v) "?". by iFrame. }
Qed.

Lemma ewp_frame_l R Ψ Φ e :
  R ∗ EWP e <| Ψ |> {{ v,     Φ v }} ⊢
      EWP e <| Ψ |> {{ v, R ∗ Φ v }}.
Proof.
  iIntros "[HR H]". iApply ewp_mono; [|
  iApply (ewp_frame_r _ R Ψ Φ with "[H HR]")].
  { by iIntros (v) "[$ $]". } { by iFrame. }
Qed.  

Lemma fupd_ewp E e Ψ Φ :
  TCEq (to_eff e) None →
  (|={E}=> EWP e @ E <| Ψ |> {{ Φ }}) ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros (?) "H"; rewrite ewp_unfold /ewp_pre.
    destruct (to_val e) as [ v    |] eqn:?;
  [|destruct (to_eff e) as [(v, k)|] eqn:?].
  { by iMod "H". } { by inversion H. }
  { iIntros (σ1 ks n) "Hσ1". iMod "H". by iApply "H". }
Qed.

Lemma ewp_fupd E e Ψ Φ :
  EWP e @ E <| Ψ |> {{ v, |={E}=> Φ v }} ⊢ EWP e @ E <| Ψ |> {{ v, Φ v }}.
Proof. iIntros "H". iApply (ewp_mono with "H"); auto. Qed.

Lemma ewp_atomic E1 E2 e Ψ Φ `{!Atomic StronglyAtomic e} :
  TCEq (to_eff e) None →
  (|={E1,E2}=>
     EWP e @ E2 <| Ψ |> {{ v, |={E2,E1}=> Φ v }}) ⊢
     EWP e @ E1 <| Ψ |> {{ Φ }}.
Proof.
  iIntros (?) "H". rewrite !ewp_unfold /ewp_pre.
    destruct (to_val e) as [ v    |] eqn:He;
  [|destruct (to_eff e) as [(v, k)|] eqn:He'].
  - by iDestruct "H" as ">>> $".
  - by inversion H.
  - iIntros (σ1 κs n) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
    iModIntro. iIntros (e2 σ2 Hstep).
    iMod ("H" with "[//]") as "H". iIntros "!>!>".
    iMod "H" as "(Hσ & H)".
    rewrite !ewp_unfold /ewp_pre.
      destruct (to_val e2) as [ v2     |] eqn:He2;
    [|destruct (to_eff e2) as [(v2, k2)|] eqn:He2'].
    + iFrame. by iDestruct "H" as ">> $".
    + have Hstep' : prim_step' e σ1 [] e2 σ2 []. { by apply Hstep. }
      edestruct (atomic _ _ _ _ _ Hstep'); by naive_solver.
    + iMod ("H" with "Hσ") as "[H _]". iDestruct "H" as %(? & ? & ? & ? & ?).
      have Hstep' : prim_step' e σ1 [] e2 σ2 []. { by apply Hstep. }
      edestruct (atomic _ _ _ _ _ Hstep'); by naive_solver.
Qed.

Lemma ewp_step_fupd E1 E2 e P Ψ Φ :
  TCEq (to_val e) None →
    TCEq (to_eff e) None →
      E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗
    EWP e @ E2 <| Ψ |> {{ v, P ={E1}=∗ Φ v }} -∗
    EWP e @ E1 <| Ψ |> {{ Φ }}.
Proof.
  rewrite !ewp_unfold /ewp_pre. iIntros (-> -> ?) "HR H".
  iIntros (σ1 ks n) "Hσ". iMod "HR". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!>" (e2 σ2 Hstep). iMod ("H" $! e2 σ2 with "[% //]") as "H".
  iIntros "!>!>". iMod "H" as "(Hσ & H)".
  iMod "HR". iModIntro. iFrame "Hσ".
  iApply (ewp_strong_mono E2 with "H");[done..| |].
  { by iApply iEff_le_refl. }
  { iIntros (v) "H". by iApply "H". }
Qed.

(* Pure steps. *)

Lemma ewp_pure_step' E e e' Ψ Φ :
  pure_prim_step e e' → 
    ▷ EWP e' @ E <| Ψ |> {{ Φ }} ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof.
  intros Hstep.
    destruct (to_val e) as [ v    |] eqn:He;
  [|destruct (to_eff e) as [(v, k)|] eqn:He'].
  - by specialize (val_not_pure' _ _   e' He).
  - by specialize (eff_not_pure' _ _ _ e' He').
  - rewrite !(ewp_unfold E e) /ewp_pre He He'.
    iIntros "Hewp" (σ₁ ks n) "Hs".
    iMod (fupd_intro_mask' E ∅) as "Hclose"; [by apply empty_subseteq|].
    iModIntro. iSplitR; [iPureIntro; by apply (pure_prim_step_imp_reducible _ e')|].
    iIntros (e₂ σ₂ Hstep').
    destruct (pure_prim_step_det _ _ Hstep _ _ _ Hstep') as [-> ->].
    by iFrame.
Qed.

Lemma ewp_pure_step E e e' Ψ Φ :
  pure_prim_step e e' → 
    EWP e' @ E <| Ψ |> {{ Φ }} ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof. iIntros "% Hwp". by iApply (ewp_pure_step' with "Hwp"). Qed.

Lemma ewp_pure_steps' E e e' Ψ Φ :
  tc pure_prim_step e e' → 
    ▷ EWP e' @ E <| Ψ |> {{ Φ }} ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof.
  intros Hstep; iInduction Hstep as [|] "IH".
  - by iApply ewp_pure_step'.
  - iIntros "Hewp". iApply ewp_pure_step'. apply H. iNext. by iApply "IH".
Qed.

Lemma ewp_pure_steps E e e' Ψ Φ :
  rtc pure_prim_step e e' → 
    EWP e' @ E <| Ψ |> {{ Φ }} ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof.
  intros Hstep; iInduction Hstep as [|] "IH".
  - by iIntros "?".  
  - iIntros "Hewp". iApply ewp_pure_step. apply H. by iApply "IH".
Qed.

(* Bind rule. *)

Lemma ewp_eff_steps K `{NeutralEctx K} E Ψ Φ v k :
  EWP Eff v (ectx_app K k) @ E <| Ψ |> {{ Φ }} ⊢
  EWP fill K (Eff v k)     @ E <| Ψ |> {{ Φ }}.
Proof. apply ewp_pure_steps. by apply rtc_pure_prim_step_eff. Qed.

Lemma ewp_bind K `{NeutralEctx K} E Ψ Φ e e' :
  e' = fill K e  →
  EWP e  @ E <| Ψ |> {{ v, EWP fill K (of_val v) @ E <| Ψ |> {{ Φ }} }} ⊢
  EWP e' @ E <| Ψ |> {{ Φ }}.
Proof.
  intros ->. iLöb as "IH" forall (e Ψ).
  rewrite !(ewp_unfold E e) /ewp_pre.
    destruct (to_val e) as [ v    |] eqn:He;
  [|destruct (to_eff e) as [(v, k)|] eqn:He'].
  - rewrite <- (of_to_val _ _ He). iIntros "H".
    by iApply fupd_ewp; first rewrite fill_not_eff.
  - iIntros "H".
    rewrite <- (of_to_eff _ _ _ He').
    iApply ewp_eff_steps. iApply ewp_eff.
    iDestruct "H" as (Q) "[HP HQ]".
    iExists Q. iFrame. iIntros (w) "HQ'".
    iDestruct ("HQ" with "HQ'") as "HQ". iNext.
    rewrite fill_ectx_app. by iApply "IH".
  - rewrite !ewp_unfold /ewp_pre.
    rewrite (fill_not_val _ _ He) (fill_not_eff K _ He').
    iIntros "Hewp" (σ₁ ks n) "Hs".
    iMod ("Hewp" $! σ₁ with "Hs") as "[% Hewp]". iModIntro.
    iSplitR; [iPureIntro; by apply reducible_fill|].
    iIntros (e₂ σ₂) "%". rename H1 into Hstep.
    destruct (Ectx_prim_step_inv K _ _ _ _ He He' Hstep) as [e' [Hstep' ->]].
    iMod ("Hewp" $! e' σ₂ Hstep') as "Hewp". iIntros "!> !>".
    iMod "Hewp" as "[$ Hewp]". by iApply "IH".
Qed.

Lemma Ectxi_ewp_bind Ki `{NeutralEctxi Ki} E Ψ Φ e e' :
  e' = fill_item Ki e  →
  EWP e  @ E <| Ψ |> {{ v, EWP fill_item Ki (of_val v) @ E <| Ψ |> {{ Φ }} }} ⊢
  EWP e' @ E <| Ψ |> {{ Φ }}.
Proof. intros ->. by iApply (ewp_bind (ConsCtx Ki EmptyCtx)). Qed.

Lemma ewp_pure_bind K E Ψ Φ e e' :
  e' = fill K e  →
  EWP                 e @ E <| ⊥ |> {{ v,
  EWP fill K (of_val v) @ E <| Ψ |> {{ Φ }} }} ⊢
  EWP                e' @ E <| Ψ |> {{ Φ }}.
Proof.
  intros ->. iLöb as "IH" forall (e).
  rewrite !(ewp_unfold E e) /ewp_pre.
    destruct (to_val e) as [ v    |] eqn:He;
  [|destruct (to_eff e) as [(v, k)|] eqn:He'].
  - rewrite <- (of_to_val _ _ He).
    iIntros "H". by iApply fupd_ewp; first rewrite fill_not_eff.
  - iIntros "Hprot_agr". by rewrite protocol_agreement_bottom.
  - rewrite !ewp_unfold /ewp_pre.
    rewrite (fill_not_val _ _ He) (fill_not_eff K _ He').
    iIntros "Hewp" (σ₁ ks n) "Hs".
    iMod ("Hewp" $! σ₁ with "Hs") as "[% Hewp]". iModIntro.
    iSplitR; [iPureIntro; by apply reducible_fill|].
    iIntros (e₂ σ₂) "%". rename H0 into Hstep, H into Hred.
    destruct (Ectx_prim_step_inv K _ _ _ _ He He' Hstep) as [e' [Hstep' ->]].
    iMod ("Hewp" $! e' σ₂ Hstep') as "Hewp". iIntros "!> !>".
    iMod "Hewp" as "[$ Hewp]". by iApply "IH".
Qed.

End ewp.
