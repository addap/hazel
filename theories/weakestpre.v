(* weakestpre.v

   We defise a notion of weakest precondition that is adapted
   to effects and their handlers. Most of this theory is
   dedicated to the proof of our version of the usual separation
   logic reasoning rules. In the end, we prove a novel reasoning
   rule for the [TryWith] construct of the language.
*)

From iris.proofmode      Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import lib lang ieff protocol_agreement.

(** * Weakest Precondition. *)

Definition ewp_pre `{!irisG eff_lang Σ} :
  (coPset -d> expr -d> iEff Σ -d> (val -d> iPropO Σ) -d> iPropO Σ) →
  (coPset -d> expr -d> iEff Σ -d> (val -d> iPropO Σ) -d> iPropO Σ)
  := λ ewp E e₁ Ψ Φ,
  match to_val e₁ with Some  v     => |={E}=> Φ v | None =>
  match to_eff e₁ with Some (v, k) =>
    protocol_agreement E v Ψ (λ w, ▷ ewp E (fill k (Val w)) Ψ Φ)
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
  do 7 f_equiv.
  - by apply HΨ.
  - intros ?. do 3 (f_contractive || f_equiv).
    apply IH; try lia; eapply dist_le; eauto with lia.
  - do 12 (f_contractive || f_equiv).
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
  protocol_agreement E v Ψ (λ w, ▷ EWP fill k (Val w) @ E <| Ψ |> {{ Φ }}) ⊣⊢
  EWP of_eff v k @ E <| Ψ |> {{ Φ }}.
Proof. by rewrite ewp_unfold /ewp_pre /=. Qed.
Lemma ewp_eff E Ψ Φ v k :
  protocol_agreement E v Ψ (λ w, ▷ EWP fill k (Val w) @ E <| Ψ |> {{ Φ }}) ⊢
  EWP of_eff v k @ E <| Ψ |> {{ Φ }}.
Proof. by rewrite ewp_eff_eq. Qed.
Lemma ewp_eff_inv E Ψ Φ v k :
  EWP of_eff v k @ E <| Ψ |> {{ Φ }} ⊢
  protocol_agreement E v Ψ (λ w, ▷ EWP fill k (Val w) @ E <| Ψ |> {{ Φ }}).
Proof. by rewrite ewp_eff_eq. Qed.

Goal forall A (P : A → iProp Σ) Φ (Ψ : iEff Σ) (v : val) x,
  (P x -∗
  EWP (Eff (Val v) EmptyCtx)
    <| >> x >> ! v {{ P x }};
       << w << ? w {{ Φ w }}
    |>
    {{ w, Φ w }})%ieff.
Proof.
  intros A P Φ Ψ v x.
  iIntros "HP". iApply ewp_eff.
  rewrite (protocol_agreement_tele' [tele _] [tele _]).
  iMod (fupd_intro_mask' ⊤ ∅) as "Hclose"; first done.
  iExists x. iFrame.
  iModIntro. iSplit; [done|]. iIntros (w) "HΦ". iMod "Hclose". iModIntro.
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
    iIntros (w) "Hk". iModIntro. iNext.
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
  (|={E}=> EWP e @ E <| Ψ |> {{ Φ }}) ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros "H"; rewrite ewp_unfold /ewp_pre.
    destruct (to_val e) as [ v    |] eqn:?;
  [|destruct (to_eff e) as [(v, k)|] eqn:?].
  { by iMod "H". } { iMod "H". by iFrame. }
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
  EWP Eff (Val v) (ectx_app K k) @ E <| Ψ |> {{ Φ }} ⊢
  EWP fill K (Eff (Val v) k) @ E <| Ψ |> {{ Φ }}.
Proof. apply ewp_pure_steps. by apply rtc_pure_prim_step_eff. Qed.

Lemma ewp_bind K `{NeutralEctx K} E Ψ Φ e e' :
  e' = fill K e  →
  EWP e @ E <| Ψ |> {{ v, EWP fill K (of_val v) @ E <| Ψ |> {{ Φ }} }} ⊢ EWP e' @ E <| Ψ |> {{ Φ }}.
Proof.
  intros ->. iLöb as "IH" forall (e Ψ).
  rewrite !(ewp_unfold E e) /ewp_pre.
    destruct (to_val e) as [ v    |] eqn:He;
  [|destruct (to_eff e) as [(v, k)|] eqn:He'].
  - rewrite <- (of_to_val _ _ He). iIntros "H". by iApply fupd_ewp.
  - iIntros "H".
    rewrite <- (of_to_eff _ _ _ He').
    iApply ewp_eff_steps. iApply ewp_eff.
    iMod "H" as (Q) "[HP HQ]". iModIntro.
    iExists Q. iFrame. iIntros (w) "HQ'".
    iMod ("HQ" with "HQ'") as "HQ". iIntros "!> !>".
    rewrite fill_ectx_app. by iApply "IH".
  - rewrite !ewp_unfold /ewp_pre.
    rewrite (fill_not_val _ _ He) (fill_not_eff K _ He He').
    iIntros "Hewp" (σ₁ ks n) "Hs".
    iMod ("Hewp" $! σ₁ with "Hs") as "[% Hewp]". iModIntro.
    iSplitR; [iPureIntro; by apply reducible_fill|].
    iIntros (e₂ σ₂) "%". rename a into Hstep.
    destruct (Ectx_prim_step_inv K _ _ _ _ He He' Hstep) as [e' [Hstep' ->]].
    iMod ("Hewp" $! e' σ₂ Hstep') as "Hewp". iIntros "!> !>".
    iMod "Hewp" as "[$ Hewp]". by iApply "IH".
Qed.

Lemma Ectxi_ewp_bind Ki `{NeutralEctxi Ki} E Ψ Φ e e' :
  e' = fill_item Ki e  →
  EWP e  @ E <| Ψ |> {{ v, EWP fill_item Ki (of_val v) @ E <| Ψ |> {{ Φ }} }} ⊢
  EWP e' @ E <| Ψ |> {{ Φ }}.
Proof. intros ->. by iApply (ewp_bind (ConsCtx Ki EmptyCtx)). Qed.

(* TODO: Prove another version of this lemma where
         the program [e] abides a protocol [Ψ1],
         the program [fill K (of_val v)],
         a protocol [Ψ2] and their combination
         satisfies the protocol sum [Ψ1 <+> Ψ2]. *)
(*Lemma ewp_pure_bind K E Ψ Φ e e' :
  e' = fill K e  →
  EWP                 e @ E <| Done |> {{ v,
  EWP fill K (of_val v) @ E <| Ψ    |> {{ Φ }} }} ⊢
  EWP                e' @ E <| Ψ    |> {{ Φ }}.
Proof.
  intros ->. iLöb as "IH" forall (e).
  rewrite !(ewp_unfold E e) /ewp_pre.
    destruct (to_val e) as [ v    |] eqn:He;
  [|destruct (to_eff e) as [(v, k)|] eqn:He'].
  - rewrite <- (of_to_val _ _ He). iIntros "H". by iApply fupd_ewp.
  - iIntros "H".
    iApply fupd_ewp. by iMod "H".
  - rewrite !ewp_unfold /ewp_pre.
    rewrite (fill_not_val _ _ He) (fill_not_eff K _ He He').
    iIntros "Hewp" (σ₁ ks n) "Hs".
    iMod ("Hewp" $! σ₁ with "Hs") as "[% Hewp]". iModIntro.
    iSplitR; [iPureIntro; by apply reducible_fill|].
    iIntros (e₂ σ₂) "%". rename a into Hstep, H into Hred.
    destruct (Ectx_prim_step_inv K _ _ _ _ He He' Hstep) as [e' [Hstep' ->]].
    iMod ("Hewp" $! e' σ₂ Hstep') as "Hewp". iIntros "!> !>".
    iMod "Hewp" as "[$ Hewp]". by iApply "IH".
Qed.*)


(** * Shallow Handlers. *)

(* Return clause judgement. *)

Definition shallow_return_handler E r Ψ' (Φ Φ' : _ -d> _) :=
  (∀ v, Φ v -∗ ▷ EWP (App r (Val v)) @ E <| Ψ' |> {{ Φ' }})%I.
Arguments shallow_return_handler _ _%E _%ieff _%I _%I.

Global Instance shallow_return_handler_ne E r n :
  Proper
    ((dist n) ==> (dist n) ==> (dist n) ==> (dist n))
  (shallow_return_handler E r).
Proof.
  intros ?????????. rewrite /shallow_return_handler.
  f_equiv=>v. f_equiv. done. by solve_proper.
Qed.
Global Instance is_shallow_return_proper E h :
  Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (shallow_return_handler E h).
Proof.
  intros ?????????. apply equiv_dist=>n;
  apply shallow_return_handler_ne; by apply equiv_dist.
Qed.

(* Effect clause judgement. *)

Definition shallow_effect_handler E h Ψ_eff Ψ Ψ' (Φ Φ' : _ -d> _) :=
  (∀ v k,
    protocol_agreement E v Ψ_eff (λ w,
      ▷ EWP App (Val k) (Val w) @ E <| Ψ |> {{ Φ }}) -∗
    ▷ EWP App (App h (Val v)) (Val k) @ E <| Ψ' |> {{ Φ' }})%I.
Arguments shallow_effect_handler _ _%E _%ieff _%ieff _%ieff _%I _%I.

Global Instance shallow_effect_handler_ne E h n :
  Proper
    ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n))
  (shallow_effect_handler E h).
Proof.
  intros ??? ??? ??? ??? ???. rewrite /shallow_effect_handler /protocol_agreement.
  by repeat (apply H || solve_proper || f_equiv).
Qed.
Global Instance is_shallow_handler_proper E h :
  Proper
    ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡))
  (shallow_effect_handler E h).
Proof.
  intros ??? ??? ??? ??? ???. apply equiv_dist=>n;
  apply shallow_effect_handler_ne; by apply equiv_dist.
Qed.

Lemma shallow_effect_handler_bottom E h Ψ Ψ' Φ Φ' :
  ⊢ shallow_effect_handler E h ⊥ Ψ Ψ' Φ Φ'.
Proof.
  iIntros (v k) "H". rewrite protocol_agreement_bottom.
  iNext. iApply fupd_ewp. by iMod "H".
Qed.

Lemma shallow_effect_handler_marker_elim E f h Ψ_eff Ψ Ψ' Φ Φ' :
  shallow_effect_handler E h (f #> Ψ_eff) Ψ Ψ' Φ Φ' ⊢
    (∀ v k,
      protocol_agreement E v Ψ_eff (λ w,
        ▷ EWP App (Val k) (Val w) @ E <| Ψ |> {{ Φ }}) -∗
      ▷ EWP App (App h (Val (f v))) (Val k) @ E <| Ψ' |> {{ Φ' }}).
Proof.
  iIntros "Hewp" (v k) "Hprot_agr".
  iApply "Hewp". by iApply protocol_agreement_marker_intro.
Qed.

Lemma shallow_effect_handler_marker_intro E f {Hf: Marker f} h Ψ_eff Ψ Ψ' Φ Φ' :
  (∀ v k,
    protocol_agreement E v Ψ_eff (λ w,
      ▷ EWP App (Val k) (Val w) @ E <| Ψ |> {{ Φ }}) -∗
    ▷ EWP App (App h (Val (f v))) (Val k) @ E <| Ψ' |> {{ Φ' }}) ⊢
    shallow_effect_handler E h (f #> Ψ_eff) Ψ Ψ' Φ Φ'.
Proof.
  iIntros "Hewp" (v k) "Hprot_agr".
  case (marker_dec_range v) as [(w & Hw)|Hv].
  { inversion Hw. iApply "Hewp".
    by iApply (@protocol_agreement_marker_elim _ _ _ f marker_inj). }
  { iNext. iApply fupd_ewp. iMod "Hprot_agr" as (Q) "[HP _]".
    rewrite iEff_marker_eq. iDestruct "HP" as (w) "[-> _]". by case (Hv w). }
Qed.

Lemma shallow_effect_handler_sum_intro E (f g : val → val)
  {Hf: Marker f} {Hg: Marker g} {Hfg: DisjRange f g} h Ψ1 Ψ2 Ψ Ψ' Φ Φ' :
  ((shallow_effect_handler E h (f #> Ψ1) Ψ Ψ' Φ Φ') ∧
   (shallow_effect_handler E h (g #> Ψ2) Ψ Ψ' Φ Φ')) ⊢
     shallow_effect_handler E h ((f #> Ψ1) <+> (g #> Ψ2)) Ψ Ψ' Φ Φ'.
Proof.
  iIntros "Hhandler" (v k) "Hprot_agr".
  iDestruct (protocol_agreement_sum_elim with "Hprot_agr") as "[H|H]".
  { iDestruct "Hhandler" as "[Hhandler _]"; by iApply "Hhandler". }
  { iDestruct "Hhandler" as "[_ Hhandler]"; by iApply "Hhandler". }
Qed.

Lemma shallow_effect_handler_sum_elim E f g h Ψ1 Ψ2 Ψ Ψ' Φ Φ' :
  shallow_effect_handler E h ((f #> Ψ1) <+> (g #> Ψ2)) Ψ Ψ' Φ Φ' ⊢
    (shallow_effect_handler E h (f #> Ψ1) Ψ Ψ' Φ Φ') ∧
    (shallow_effect_handler E h (g #> Ψ2) Ψ Ψ' Φ Φ').
Proof.
  iIntros "Hhandler". iSplit; iIntros (v k) "Hprot_agr"; iApply "Hhandler".
  { by iApply protocol_agreement_sum_intro_l. }
  { by iApply protocol_agreement_sum_intro_r. }
Qed.

Lemma shallow_effect_handler_strong_mono
  E h Ψ1_eff Ψ2_eff Ψ1 Ψ2 Ψ' Φ1 Φ2 Φ' :
   (shallow_effect_handler E h Ψ2_eff Ψ2 Ψ' Φ2 Φ' -∗
      Ψ1_eff ⊑ Ψ2_eff -∗ Ψ1 ⊑ Ψ2 -∗ (∀ v, Φ1 v ={E}=∗ Φ2 v) -∗
    shallow_effect_handler E h Ψ1_eff Ψ1 Ψ' Φ1 Φ')%ieff.
Proof.
  iIntros "Hhandler #HΨ_eff #HΨ HΦ". iIntros (v k) "Hp".
  iAssert (protocol_agreement E v Ψ2_eff (λ w,
              ▷ EWP App (Val k) (Val w) @ E <|Ψ2|> {{Φ2}}))%I
  with "[HΦ Hp]" as "Hp".
  { iApply (protocol_agreement_strong_mono with "Hp"); try auto.
    iIntros (w) "Hewp". iModIntro. iNext.
    iApply (ewp_strong_mono with "Hewp"); by auto. }
  iSpecialize ("Hhandler" with "Hp"). iNext.
  iApply (ewp_strong_mono with "Hhandler"); try auto.
  by iApply iEff_le_refl.
Qed.

(* Shallow handler judgement. *)

Definition shallow_handler E h r Ψ_eff Ψ Ψ' (Φ Φ' : _ -d> _) : iProp Σ :=
  (shallow_return_handler E   r         Ψ' Φ Φ') ∧
  (shallow_effect_handler E h   Ψ_eff Ψ Ψ' Φ Φ').
Arguments shallow_handler _ _%E _%E _%ieff _%ieff _%ieff _%I _%I.

Global Instance shallow_handler_ne E h r n :
  Proper
    ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n))
  (shallow_handler E h r).
Proof.
  intros ??? ??? ??? ??? ???. rewrite /shallow_handler.
  f_equiv. solve_proper. by apply shallow_effect_handler_ne.
Qed.
Global Instance shallow_handler_proper E h r :
  Proper
    ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡))
  (shallow_handler E h r).
Proof.
  intros ??? ??? ??? ??? ???.
  apply equiv_dist=>n. apply shallow_handler_ne; apply equiv_dist; done.
Qed.

(* Reasoning rule for [TryWith]: a shallow single-effect handler. *)

Lemma ewp_try_with E Ψ Ψ' Φ Φ' e h r :
  EWP          e      @ E <| Ψ  |> {{ Φ  }} -∗ shallow_handler E h r Ψ Ψ Ψ' Φ Φ' -∗
  EWP (TryWith e h r) @ E <| Ψ' |> {{ Φ' }}.
Proof.
  iLöb as "IH" forall (e Ψ).
  destruct (to_val e) as [ v    |] eqn:He; [|
  destruct (to_eff e) as [(v, k)|] eqn:He' ].
  - rewrite <-(of_to_val _ _ He).
    iIntros "HΦ [Hr _]".
    iApply fupd_ewp. iMod (ewp_value_inv with "HΦ") as "HΦ". iModIntro.
    iApply ewp_pure_step'. apply pure_prim_step_try_with_val.
    by iApply ("Hr" with "HΦ").
  - rewrite <-(of_to_eff _ _ _ He').
    iIntros "H Hhandler".
    iDestruct (ewp_eff_inv with "H") as "H".
    iDestruct "Hhandler" as "[_ Hh]".
    iApply ewp_pure_step'. apply pure_prim_step_try_with_eff.
    iApply "Hh". iApply (protocol_agreement_strong_mono with "H").
    { done. } { by iApply iEff_le_refl. }
    { iIntros (w) "Hk". iModIntro. iNext.
      iApply ewp_pure_step'. apply pure_prim_step_cont. done. }
  - iIntros "He Hhandler".
    rewrite !(ewp_unfold _ (TryWith _ _ _))
            !(ewp_unfold _ e) /ewp_pre He He' //=.
    iIntros (σ₁ ks n) "Hs". iMod ("He" $! σ₁ with "Hs") as "[% He]".
    iSplitR.
    + iPureIntro. revert H; unfold reducible. simpl.
      rewrite /prim_step'; simpl.
      destruct 1 as [obs [e₄ [σ₄ [efs Hstep]]]].
      case obs in Hstep; [|done].
      case efs in Hstep; [|done].
      inversion Hstep. simplify_eq.
      exists [], (TryWith (fill K e2') h r), σ₄, [].
      by apply (Ectx_prim_step _ _ _ _ (ConsCtx (TryWithCtx h r) K) e1' e2').
    + iModIntro. iIntros (e₄ σ₄) "%". rename a into Hstep.
      assert (Hstep' : ∃ e₅, prim_step e σ₁ e₅ σ₄ ∧ e₄ = TryWith e₅ h r).
      { inversion Hstep. destruct K as [|Ki K].
        - simpl in H; simplify_eq. inversion H2; naive_solver.
        - destruct Ki; try naive_solver. simpl in H0, H1, H2; simplify_eq.
          exists (fill K e2'). simpl. split;[| done].
          by apply (Ectx_prim_step _ _ _ _ K e1' e2').
      }
      destruct Hstep' as [e₅ [Hstep' ->]].
      iDestruct ("He" $! e₅ σ₄ Hstep') as "> He". iIntros "!> !>".
      iMod "He" as "[$ He]".
      by iApply ("IH" with "He Hhandler").
Qed.

End ewp.
