(* named_effects_another_approach.v *)

(* In the file [named_effects.v], we define a program logic for reasoning about
   multiple named effects. In particular, the logic allows one to reason about
   three operations: (1) the allocation of a fresh effect name, (2) the
   handling of a named effect, and (3) the action of raising a named effect.
   In this file, we propose another approach for reasoning about these same
   operations. The key differences between the two approaches are: (1) here, we
   propose a weakest precondition assertion parameterized with an association
   list rather than a map, and (2) the claim that an effect name is valid is
   an ephemeral assertion rather than a persistent assertion. The advantage of
   doing so is that we can implicitly assume that effect names are distinct.
*)

From iris.proofmode Require Import base tactics classes.


From hazel Require Import named_effects. (* Program definitions from the
                                            Implementation Section. *)
From hazel Require Import weakestpre shallow_handler deep_handler.
From hazel Require Import notation tactics.

Set Default Proof Using "Type".



(** * Logical Definitions. *)

(** Abbreviations. *)

Definition eff_name     : Type := loc.
Definition eff_list {Σ} : Type := list (eff_name * iEff Σ).


(** Protocol. *)

Section protocol.
  Context `{!heapG Σ}.

  (* [eff s] is the claim that [s] is a unique effect name. *)
  Definition eff (s : eff_name) : iProp Σ := s ↦ #().

  (* [Eff E] asserts that the effect names in [E]
     are distinct from one another. *)
  Definition Eff (E : list eff_name) : iProp Σ :=
    ([∗ list] s ∈ E, eff s)%I.

  (* [EFF E] is the protocol describing the effects of programs written in
     an idiom of [HH] where an effect is always the pair of a name [s] and
     a value [v]. *)
  Definition EFF (E : eff_list) : iEff Σ :=
    (>> (s : eff_name) (v : val) (Ψ : iEff Σ) (Q : val → iProp Σ) >>
       ! (#s, v)%V     {{ Eff E.*1 ∗ ⌜ (s, Ψ) ∈ E ⌝ ∗ iEff_car Ψ v Q }};
     << (w : val) <<
       ? (w)           {{ Eff E.*1 ∗ Q w }})%ieff.

  Lemma EFF_agreement v' E Φ : protocol_agreement v' (EFF E) Φ ≡
    (∃ (s : eff_name) (v : val) (Ψ : iEff Σ) (Q : val → iProp Σ),
      ⌜ v' = (#s, v)%V ⌝ ∗
      (Eff E.*1 ∗ ⌜ (s, Ψ) ∈ E ⌝ ∗ iEff_car Ψ v Q) ∗
      (∀ (w : val), (Eff E.*1 ∗ Q w) -∗ Φ w))%I.
  Proof.
    rewrite /EFF (protocol_agreement_tele' [tele _ _ _ _] [tele _]). by auto.
  Qed.

End protocol.


(** Weakest precondition. *)

Section weakest_precondition.
  Context `{!heapG Σ}.

  (* We define a notion of weakest precondition tailored for this idiom
     of [HH] where an effect carries a name. *)
  Definition wp_def :
    expr -d> eff_list -d> (val -d> iPropO Σ) -d> iPropO Σ :=
    (λ e E Φ,
      Eff (E.*1) -∗
        EWP e <| EFF E |> {{ y, Eff (E.*1) ∗ Φ y }})%I.

  Global Instance wp_ne e E n :
    Proper ((dist n) ==> (dist n)) (wp_def e E).
  Proof. unfold wp_def. intros => ???. by repeat (f_equiv; try intros ?). Qed.

  Global Instance wp_proper e E : Proper ((≡) ==> (≡)) (wp_def e E).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne; apply equiv_dist.
  Qed.

End weakest_precondition.


Notation "'WP' e <| E '|' '>' {{ Φ  } }" :=
  (wp_def e%E E Φ)
  (at level 20, e, E, Φ at level 200).

Notation "'WP' e <| E '|' '>' {{ v , Φ } }" :=
  (wp_def e%E E (λ v, Φ)%I)
  (at level 20, e, E, Φ at level 200).


Section handler_judgement.
  Context `{!heapG Σ}.

  Definition is_handler_pre :
    (expr -d> expr -d> eff_list -d> iEff Σ -d> (_ -d> iPropO Σ) -d>
       (_ -d> iPropO Σ) -d> iPropO Σ) →
    (expr -d> expr -d> eff_list -d> iEff Σ -d> (_ -d> iPropO Σ) -d>
       (_ -d> iPropO Σ) -d> iPropO Σ)
    := λ is_handler h r E Ψ Φ Φ',
    ((∀ (v : val), Φ v -∗ WP (r v) <| E |> {{ Φ' }}) ∧
     (∀ (v k : val),
       protocol_agreement v Ψ (λ (w : val), ∀ Φ'',
         ▷ is_handler h r E Ψ Φ Φ'' -∗
           WP (k w) <| E |> {{ Φ'' }}) -∗
       ▷ WP (h v k) <| E |> {{ Φ' }}))%I.
  Arguments is_handler_pre _%E _%E _ _%ieff _%I _%I.

  Local Instance is_handler_pre_contractive : Contractive is_handler_pre.
  Proof.
    rewrite /is_handler_pre => n hanlder handler' Hhandler E Ψ Φ h r Φ'.
    repeat (f_contractive || f_equiv). intros ?; simpl.
    repeat (f_contractive || f_equiv). apply Hhandler.
  Qed.
  Definition is_handler_def := fixpoint is_handler_pre.
  Definition is_handler_aux : seal is_handler_def. Proof. by eexists. Qed.
  Definition is_handler := is_handler_aux.(unseal).
  Definition is_handler_eq : is_handler = is_handler_def
    := is_handler_aux.(seal_eq).
  Arguments is_handler _%E _%E _ _%ieff _%I _%I.

  Global Lemma is_handler_unfold h r E Ψ Φ Φ' :
    is_handler h r E Ψ Φ Φ' ⊣⊢ is_handler_pre is_handler h r E Ψ Φ Φ'.
  Proof.
    rewrite is_handler_eq /is_handler_def.
    by apply (fixpoint_unfold is_handler_pre).
  Qed.

  Global Instance is_handler_ne h r E n :
    Proper
      ((dist n) ==> (dist n) ==> (dist n) ==> (dist n))
    (is_handler h r E).
  Proof.
    revert E.
    induction (lt_wf n) as [n _ IH]=> E Ψ1 Ψ2 HΨ Φ1 Φ2 HΦ Φ'1 Φ'2 HΦ'.
    rewrite !is_handler_unfold /is_handler_pre.
    repeat (apply protocol_agreement_ne||apply wp_ne||f_contractive||f_equiv);
    try done; try (eapply dist_le; eauto with lia).
    intros ?. do 3 (f_equiv). f_contractive.
    apply IH; try lia; eapply dist_le; eauto with lia.
  Qed.
  Global Instance is_handler_proper h r E :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (is_handler h r E).
  Proof.
    intros ??? ??? ???.
    apply equiv_dist=>n. apply is_handler_ne; apply equiv_dist; done.
  Qed.

End handler_judgement.



(** * Reasoning Rules. *)

(** Auxiliary lemmas about [eff] and [Eff]. *)

Section auxiliary_lemmas.
  Context `{!heapG Σ}.

  Lemma Eff_cons s E : Eff (s :: E) = (eff s ∗ Eff E)%I.
  Proof. by unfold Eff. Qed.

  Lemma distinct_eff_name (s : eff_name) E :
    eff s -∗ Eff E -∗ ⌜ s ∉ E ⌝%I.
  Proof.
    iIntros "Hs HE".
    iInduction E as [|s' E Hnot_in] "IH".
    - iPureIntro. by apply not_elem_of_nil.
    - rewrite Eff_cons not_elem_of_cons.
      iDestruct "HE" as "[Hs' HE]". iSplit.
      { by iApply (mapsto_ne with "Hs Hs'"). }
      { by iApply ("IH" with "Hs HE"). }
  Qed.

  Lemma Eff_NoDup E : Eff E -∗ ⌜ NoDup E ⌝.
  Proof.
    induction E as [|s E].
    - iIntros "_".
      iPureIntro.
      by constructor.
    - rewrite Eff_cons.
      iIntros "[Hs HE]".
      iDestruct (IHE with "HE") as %NoDup_E.
      iDestruct (distinct_eff_name with "Hs HE") as %not_in_E.
      iPureIntro.
      by constructor.
  Qed.

  (* Because the effect names in [E] appear exactly once in [E'],
     we can split [Eff E'] into [Eff E] and [Eff E -∗ Eff E']. *)
  Lemma Eff_frame E E' :
    E ⊆+ E' →
      Eff E' -∗ (Eff E ∗ (Eff E -∗ Eff E')).
  Proof.
    induction 1 as [|s ss es| s e ss| s ss es| ss es fs].
    - by auto.
    - rewrite !Eff_cons.
      iIntros "[$ Hes]".
      iPoseProof (IHsubmseteq with "Hes") as "[$ Hes]".
      iIntros "[$ Hss]".
      by iApply ("Hes" with "Hss").
    - rewrite !Eff_cons.
      by iIntros "($ & $ & $) ($ & $ & $)".
    - rewrite !Eff_cons.
      iIntros "[$ Hes]".
      by iPoseProof (IHsubmseteq with "Hes") as "[$ Hes]".
    - iIntros "Hfs".
      iPoseProof (IHsubmseteq2 with "Hfs") as "[Hes Hfs]".
      iPoseProof (IHsubmseteq1 with "Hes") as "[Hss Hes]".
      iFrame. iIntros "Hss".
      iApply "Hfs". by iApply "Hes".
  Qed.

  Lemma EFF_weaken s Ψ Ψ' E :
    (Ψ ⊑ Ψ')%ieff -∗
      (EFF ((s, Ψ) :: E) ⊑ EFF ((s, Ψ') :: E))%ieff.
  Proof.
    iIntros "#Hle !>" (v Φ) "HE".
    rewrite !EFF_agreement.
    iDestruct "HE" as (s' v' Ψ'' Q) "(-> & (HE & % & HΨ'') & Hk)".
    revert H. rewrite elem_of_cons. intros [Heq|Hin].
    - injection Heq. intros -> ->.
      iDestruct ("Hle" $! v' Q with "[HΨ'']") as "[%Q' [HΨ HQ]]".
      { iExists Q. iFrame. by iIntros (?) "$". }
      iExists s, v', Ψ', Q'. iFrame. iSplit; [done|].
      iSplit; [iPureIntro; by set_solver|].
      iIntros (w) "[[Hs HE] HQ']". iApply "Hk".
      iFrame. by iApply "HQ".
    - iExists s', v', Ψ'', Q. iFrame. iSplit; [done|].
      iPureIntro; by set_solver.
  Qed.

  Lemma EFF_introduce s E : ⊢ (EFF ((s, ⊥) :: E) ⊑ EFF E)%ieff.
  Proof.
    iIntros "!>" (v Φ) "HE".
    rewrite !EFF_agreement.
    iDestruct "HE" as (s' v' Ψ' Q) "(-> & (HE & % & HΨ') & Hk)".
    revert H. rewrite elem_of_cons. intros [Heq|Hin].
    - injection Heq. by intros -> ->.
    - iExists s', v', Ψ', Q. iFrame. iSplit; [done|].
      rewrite !fmap_cons !Eff_cons.
      iDestruct "HE" as "[Hs $]". iSplit; [done|].
      iIntros (y) "[HE HQ]". iApply "Hk".
      by iFrame.
  Qed.

End auxiliary_lemmas.


(** Main reasoning rules: value, step, and bind rules. *)

Section reasoning_rules.
  Context `{!heapG Σ}.

  Lemma wp_value E Φ v : Φ v ⊢ WP of_val v <| E |> {{ Φ }}.
  Proof. iIntros "HΦ HS". iApply ewp_value. by iFrame. Qed.

  Lemma wp_pure_step e e' E Φ :
    pure_prim_step e e' → 
      ▷ WP e' <| E |> {{ Φ }} ⊢ WP e <| E |> {{ Φ }}.
  Proof.
    iIntros "% He' HS".
    iApply (ewp_pure_step' _ _ e'); first done.
    iNext. by iApply "He'".
  Qed.

  Lemma wp_bind K `{NeutralEctx K} E Φ e e' :
    e' = fill K e  →
      WP e  <| E |> {{ v, WP fill K (of_val v) <| E |> {{ Φ }} }} ⊢
      WP e' <| E |> {{ Φ }}.
  Proof.
    iIntros (->) "He HS".
    iSpecialize ("He" with "HS").
    iApply (ewp_bind K); first done.
    iApply (ewp_mono' with "He").
    iIntros (v) "[HS HK]".
    by iApply "HK".
  Qed.

  Lemma fupd_wp e E Φ :
    TCEq (to_eff e) None →
    (|==> WP e <| E |> {{ Φ }}) ⊢ WP e <| E |> {{ Φ }}.
  Proof.
    iIntros (?) "He HS". iApply fupd_ewp.
    iMod "He". iModIntro. by iApply "He".
  Qed.

End reasoning_rules.


(** Tactics. *)

Ltac match_wp_goal lemma tac :=
  match goal with
  | [ |- @bi_emp_valid _                (wp_def ?e _ _) ] => tac lemma e
  | [ |- @environments.envs_entails _ _ (wp_def ?e _ _) ] => tac lemma e
  end.

Ltac wp_pure_step_lemma :=
  iApply wp_pure_step.

Ltac wp_bind_rule_lemma K :=
  iApply (wp_bind K).

Ltac wp_pure_step :=
  match_wp_goal wp_pure_step_lemma pure_step_tac.

Ltac wp_bind_rule :=
  match_wp_goal wp_bind_rule_lemma bind_rule_tac.

Ltac wp_value_or_step :=
  ((iApply wp_value) || (wp_bind_rule; wp_pure_step));
  try iNext; simpl.

Ltac wp_pure_steps :=
  repeat wp_value_or_step.


(** Monotonicity. *)

Section monotonicity.
  Context `{!heapG Σ}.

  Lemma wp_mono E Φ Φ' e :
    (∀ v, Φ v ==∗ Φ' v) -∗
      WP e <| E |> {{ Φ }} -∗
        WP e <| E |> {{ Φ' }}.
  Proof.
    iIntros "HΦ' He HE".
    iSpecialize ("He" with "HE").
    iApply (ewp_strong_mono with "He"); first done.
    { by iApply iEff_le_refl. }
    iIntros (y) "[$ H]".
    by iMod ("HΦ'" with "H") as "$".
  Qed.

  Lemma wp_frame E Φ R e :
    R -∗
      WP e <| E |> {{ Φ }} -∗
        WP e <| E |> {{ y, R ∗ Φ y }}.
  Proof.
    iIntros "HR He".
    iApply (wp_mono with "[HR] He").
    by iIntros (y) "$".
  Qed.

  (* Unfortunately, the assertion [EFF E ⊑ EFF E'] does not hold
     because it is guarded by a persistently modality, thus forbidding
     the use of an ephemeral assertion such as [Eff E -∗ Eff E'].
     Therefore, we cannot rely on the monotonicity lemma for [ewp]. *)
  Lemma wp_eff_frame E E' Φ e :
    E ⊆+ E' →
      WP e <| E |> {{ Φ }} -∗
        WP e <| E' |> {{ Φ }}.
  Proof.
    iIntros (Hsub) "He HE'".
    iDestruct (Eff_frame _ _
      (fmap_submseteq fst _ _ Hsub) with "HE'") as "[HE HE']".
    iSpecialize ("He" with "HE").
    iLöb as "IH" forall (e).
      destruct (to_val e) as [ v    |] eqn:?;
    [|destruct (to_eff e) as [(v, k)|] eqn:?].
    - rewrite !ewp_unfold /ewp_pre Heqo.
      iMod "He" as "[HE $]". by iApply "HE'".
    - rewrite -(of_to_eff _ _ _ Heqo0) -!ewp_eff_eq !EFF_agreement.
      iDestruct "He" as (s v' Ψ Q) "(-> & (HE & % & HΨ') & Hk)".
      rename H into Hin.
      iExists s, v', Ψ, Q. iFrame. iSplit; [done|].
      iSpecialize ("HE'" with "HE"). iFrame.
      iSplit; [by iPureIntro;
      apply (elem_of_submseteq _ _  _ Hin Hsub)|].
      iIntros (w) "[HE' HQ]".
      iDestruct (Eff_frame _ _
        (fmap_submseteq fst _ _ Hsub) with "HE'") as "[HE HE']".
      iSpecialize ("Hk" $! w with "[HE HQ]"); [by iFrame|]; iNext.
      by iApply ("IH" with "Hk HE'").
    - rewrite !ewp_unfold /ewp_pre Heqo Heqo0.
      iIntros (σ₁ ns k ks nt) "Hσ".
      iMod ("He" with "[$]") as "[$ H]".
      iModIntro. iIntros (e₂ σ₂ Hstep).
      iMod ("H" with "[//]") as "H". iIntros "!> !>".
      iMod "H".
      iApply (step_fupdN_wand with "[H]"); first by iApply "H".
      iModIntro. iIntros "H". iMod "H" as "[$ He₂]".
      iModIntro.
      by iApply ("IH" with "He₂ HE'").
  Qed.

  Corollary wp_eff_app_r E E' Φ e :
    WP e <| E |> {{ Φ }} -∗
      WP e <| E ++ E' |> {{ Φ }}.
  Proof.
    iIntros "He".
    iApply (wp_eff_frame with "He").
    apply (submseteq_inserts_r E').
    by set_solver.
  Qed.

  Corollary wp_eff_app_l E E' Φ e :
    WP e <| E |> {{ Φ }} -∗
      WP e <| E' ++ E |> {{ Φ }}.
  Proof.
    iIntros "He".
    iApply (wp_eff_frame with "He").
    apply (submseteq_inserts_l E').
    by set_solver.
  Qed.

  (* The order of effect names does not matter. *)
  Corollary wp_eff_permute E E' Φ e :
    E ≡ₚ E' →
      WP e <| E |> {{ Φ }} -∗
        WP e <| E' |> {{ Φ }}.
  Proof.
    rewrite Permutation_alt; intros [_ Hp].
    by iApply wp_eff_frame.
  Qed.

  Corollary wp_strong_mono E E' Φ Φ' e :
    E ⊆+ E' →
      (∀ v, Φ v ==∗ Φ' v) -∗
        WP e <| E |> {{ Φ }} -∗
          WP e <| E' |> {{ Φ' }}.
  Proof.
    iIntros (Hsub) "HΦ He".
    iApply (wp_eff_frame _ _ _ _ Hsub).
    by iApply (wp_mono with "HΦ He").
  Qed.

  Lemma wp_weaken s E (Ψ Ψ' : iEff Σ) Φ e :
    (Ψ ⊑ Ψ')%ieff -∗
      WP e <| (s, Ψ) :: E |> {{ Φ }} -∗
        WP e <| (s, Ψ') :: E |> {{ Φ }}.
  Proof.
    iIntros "#Hle He HE".
    iSpecialize ("He" with "[$]").
    rewrite fmap_cons Eff_cons //=.
    (* Proof by monotonicity of [ewp]. *)
    iApply (ewp_strong_mono with "He");
    first done;
    last by iIntros (y) "[[$ $] $]".
    by iApply EFF_weaken.
  Qed.

  Corollary wp_dismiss s E Ψ Φ e :
    WP e <| (s, ⊥) :: E |> {{ Φ }} -∗
      WP e <| (s, Ψ) :: E |> {{ Φ }}.
  Proof. iApply wp_weaken. by iApply iEff_le_bottom. Qed.

End monotonicity.


(** Client side. *)

(* Reasoning rules for allocating a fresh effect name,
   performing an effect, and introducing a name to the
   list of effects. *)

Section effects.
  Context `{!heapG Σ}.

  Lemma wp_effect E Φ :
    (∀ (s : eff_name), eff s -∗ Φ #s) -∗
      WP effect #() <| E |> {{ Φ }}.
  Proof.
    iIntros "HPost HEff".
    unfold effect. ewp_pure_steps.
    iApply ewp_mono'; [by iApply ewp_alloc|].
    iIntros (v). iDestruct 1 as (s) "[-> Hs]".
    iModIntro. iFrame. by iApply "HPost".
  Qed.

  Lemma wp_perform (s : eff_name) (v : val) E Ψ Φ :
    (s, Ψ) ∈ E →
      protocol_agreement v Ψ Φ -∗
        WP (perform #s v) <| E |> {{ Φ }}.
  Proof.
    iIntros (?) "Hprot HEff". rename H into Hin.
    unfold perform. ewp_pure_steps.
    iApply ewp_eff. rewrite EFF_agreement.
    iDestruct "Hprot" as (Q) "[HP Hk]".
    iExists s, v, Ψ, Q. iSplit; [done|]. iFrame.
    iSplit; [done|].
    iIntros (w) "[HE HQ]". iNext.
    iApply ewp_value. iFrame.
    by iApply "Hk".
  Qed.

  Lemma wp_introduce s E Φ e :
    WP e <| (s, ⊥) :: E |> {{ Φ }} -∗
      eff s -∗ WP e <| E |> {{ y, Φ y ∗ eff s }}.
  Proof.
    iIntros "He Hs HE".
    iSpecialize ("He" with "[$]").
    rewrite fmap_cons Eff_cons //=.
    (* Proof by monotonicity of [ewp]. *)
    iApply (ewp_strong_mono with "He");
    first done;
    last by iIntros (y) "[[$ $] $]".
    by iApply EFF_introduce.
  Qed.

End effects.


(** Handler side. *)

(* Reasoning rule for installing an effect handler. *)

Section handler.
  Context `{!heapG Σ}.

  Lemma wp_handle (s : eff_name) E Ψ Φ Φ' (client h r : val) :
    WP client #() <| (s, Ψ) :: E |> {{ Φ }} -∗
      is_handler h r ((s, ⊥) :: E) Ψ Φ Φ' -∗
        WP (handle #s client h r) <| (s, ⊥) :: E |> {{ Φ' }}.
  Proof.
    iIntros "Hclient Hhandler HEff".
    unfold handle.
    do 14 ewp_value_or_step.
    rewrite Eff_cons.
    iDestruct "HEff" as "[Hs HEff]".
    iDestruct (distinct_eff_name with "Hs HEff") as %Hnot_in.
    iSpecialize ("Hclient" with "[Hs HEff]"); first by iFrame.
    iApply (ewp_deep_try_with with "Hclient").

    iLöb as "IH" forall (Φ').
    rewrite deep_handler_unfold. iSplit.

    (* Return branch. *)
    { rewrite fmap_cons !Eff_cons.
      iIntros (v) "([Hs HE] & HΦ)".
      rewrite is_handler_unfold.
      iNext. ewp_pure_steps.
      iDestruct "Hhandler" as "[Hr _]".
      iSpecialize ("Hr" with "HΦ [Hs HE]"); first by iFrame.
      iApply (ewp_strong_mono with "Hr"); first auto.
      - by iApply iEff_le_refl.
      - rewrite Eff_cons.
        by iIntros (y) "[$ $]".
    }

    (* Effect branch. *)
    { iIntros (v' k) "Hprot". iNext.
      rewrite EFF_agreement fmap_cons !Eff_cons.
      iDestruct "Hprot" as (s' v Ψ' Q) "(-> & ([Hs HE] & % & HΨ') & Hk)".
      revert H; rewrite elem_of_cons or_comm; intro Hs'.
      ewp_pure_steps; [done|].
      case (decide (s = s')) as [->|Hneq].
      { rewrite bool_decide_eq_true_2; [|done].
        case Hs'.
        { intro Hin. cut (s' ∈ E.*1); [done|].
          by apply (elem_of_list_fmap_1 fst _ _ Hin).
        }
        { injection 1. intros ->.
          rewrite is_handler_unfold.
          iDestruct "Hhandler" as "[_ Hh]".
          iSpecialize ("Hh" $! v k with "[HΨ' Hk]").
          { iExists Q. iFrame.
            iIntros (w) "HQ". iIntros (Φ'') "Hhandler HE".
            rewrite fmap_cons Eff_cons.
            iApply ("Hk" with "[HQ HE]"); first by iFrame.
            iNext.
            by iApply "IH".
          }
          ewp_pure_steps.
          by iApply ("Hh" with "[Hs HE]"); by iFrame.
        }
      }
      { rewrite bool_decide_eq_false_2; [|by injection 1; intros ->].
        ewp_pure_steps.
        iApply ewp_eff.
        rewrite EFF_agreement.
        iExists s', v, Ψ', Q. iFrame.
        iSplit; [done|]. iSplit; [iPureIntro; set_solver|].
        iIntros (w) "[HE HQ]".
        iSpecialize ("Hk" $! w with "[HE HQ]"); [by iFrame|].
        iNext. simpl. ewp_pure_steps.
        iApply "Hk". iNext.
        by iApply ("IH" with "Hhandler").
      }
    }
  Qed.

End handler.


(** * Examples. *)

From hazel Require Import cascade exceptions.


Section lexically_scoped_handlers.
  Context `{!heapG Σ}.

  (* A lexically-scoped handler is defined as the handler of a
     freshly-generated effect name. *)
  Definition lex_handle : val :=  λ: "client" "h" "r",
    let: "s" := effect #() in
    handle "s" (λ: <>, "client" "s") "h" "r".

  Lemma wp_lex_handle E Ψ Φ Φ' (client h r : val) :
    (∀ (s : eff_name) , WP client #s <| (s, Ψ) :: E |> {{ Φ }}) -∗
      is_handler h r E Ψ Φ Φ' -∗
        WP (lex_handle client h r) <| E |> {{ Φ' }}.
  Proof.
    iIntros "Hclient Hhandler".
    unfold lex_handle.
    wp_pure_steps. wp_bind_rule.
    iApply wp_effect. iIntros (s) "Hs". simpl.
    wp_pure_steps.
    unfold handle. iIntros "HE".
    do 14 ewp_value_or_step.
    iDestruct (distinct_eff_name with "Hs HE") as %Hnot_in.
    iSpecialize ("Hclient" with "[Hs HE]"); first by iFrame.
    iApply (ewp_deep_try_with with "[Hclient]").
    { ewp_value_or_step; by iApply "Hclient". }

    iLöb as "IH" forall (Φ').
    rewrite deep_handler_unfold. iSplit.

    (* Return branch. *)
    { rewrite !Eff_cons.
      iIntros (v) "([Hs HE] & HΦ)".
      rewrite is_handler_unfold.
      iNext. ewp_pure_steps.
      iDestruct "Hhandler" as "[Hr _]".
      iSpecialize ("Hr" with "HΦ [Hs HE]"); first by iFrame.
      iApply (ewp_strong_mono with "Hr"); first auto.
      - by iApply iEff_le_refl.
      - by iIntros (y) "[$ $]".
    }

    (* Effect branch. *)
    { iIntros (v' k) "Hprot". iNext.
      rewrite EFF_agreement fmap_cons !Eff_cons.
      iDestruct "Hprot" as (s' v Ψ' Q) "(-> & ([Hs HE] & % & HΨ') & Hk)".
      revert H; rewrite elem_of_cons or_comm; intro Hs'.
      ewp_pure_steps; [done|].
      case (decide (s = s')) as [->|Hneq].
      { rewrite bool_decide_eq_true_2; [|done].
        case Hs'.
        { intro Hin. cut (s' ∈ E.*1); [done|].
          by apply (elem_of_list_fmap_1 fst _ _ Hin).
        }
        { injection 1. intros ->.
          rewrite is_handler_unfold.
          iDestruct "Hhandler" as "[_ Hh]".
          iSpecialize ("Hh" $! v k with "[HΨ' Hk Hs]").
          { iExists Q. iFrame.
            iIntros (w) "HQ". iIntros (Φ'') "Hhandler HE".
            iApply ("Hk" with "[HQ Hs HE]"); first by iFrame.
            iNext.
            by iApply "IH".
          }
          ewp_pure_steps.
          by iApply ("Hh" with "[$]").
        }
      }
      { rewrite bool_decide_eq_false_2; [|by injection 1; intros ->].
        ewp_pure_steps.
        iApply ewp_eff.
        rewrite EFF_agreement.
        iExists s', v, Ψ', Q. iFrame.
        iSplit; [done|]. iSplit; [iPureIntro; set_solver|].
        iIntros (w) "[HE HQ]".
        iSpecialize ("Hk" $! w with "[Hs HE HQ]"); [by iFrame|].
        iNext. simpl. ewp_pure_steps.
        iApply "Hk". iNext.
        by iApply ("IH" with "Hhandler").
      }
    }
  Qed.

End lexically_scoped_handlers.


Section find.
  Context `{!heapG Σ} {HIterLib: IterLib Σ}.
  Variable Not_found : eff_name.

  (* Implementation of [find] using both lexically-scoped
     and top-level effects. *)
  Definition find : val := λ: "p",

    lex_handle
      ((* client. *) λ: "Found",
         iter (λ: "x",
           if: "p" "x" then
             perform "Found" "x"
           else
             #()))

      ((* effect branch. *)
        λ: "x" <>, "x")%V

      ((* return branch. *)
        λ: <>, perform #Not_found #())%V.


  (* Implementation of [exists'] by running [find] under
     a handler for the top-level effect [Not_found]. *)
  Definition exists' : val := λ: "p",

    handle #Not_found
      ((* client. *) λ: <>, find "p")

      ((* effect branch. *) λ: <> <>,
         #false)%V

      ((* return branch. *) λ: <>,
         #true)%V.


  (* Specification of [iter] written in terms of [WP] to
     account for the presence of multiple named effects. *)
  Lemma iter_spec' (I : list val → iProp Σ) (E : eff_list) (f : val) :

    □ (∀ us u, permitted (us ++ [u]) -∗
       S' -∗
         I us -∗
           WP f u <| E |> {{ _, S' ∗ I (us ++ [u]) }}) -∗

      S -∗
        I [] -∗
          WP iter f <| E |> {{ _, ∃ xs, S ∗ I xs ∗ complete xs }}.

  Proof.
    iIntros "#Hf HS HI HE".
    iPoseProof
      (iter_spec
         ((* mask. *) ⊥)
         ((* loop invariant. *) λ xs, Eff (E.*1) ∗ I xs)%I
         ((* protocol. *) _)
         ((* iteratee. *) f)
       with "[] [$] [$]") as "Hiter".
    { iIntros "!>" (us u) "Hpermitted HS' [HE HI]".
      iSpecialize ("Hf" with "Hpermitted [$] [$] HE").
      iApply ewp_mono; [|by iApply "Hf"].
      by iIntros (y) "[$ [$ $]]".
    }
    { iApply ewp_mono; [|by iApply "Hiter"].
      iIntros (y) "[%xs (? & [$ ?] & ?)]".
      by iExists xs; iFrame.
    }
  Qed.


  (* Specification of [find]. *)
  Lemma find_spec (p : val) (P : val → bool) (E : eff_list) :

      □ (∀ (x : val),
           S' -∗
             WP (p x) <| (Not_found, ⊥) :: E |>
                      {{ b, ⌜ b = #(P x) ⌝ ∗ S' }}) -∗
  
        S -∗
          WP (find p) (* Effects. *)
                      <| (Not_found, exn (λ _, S        ∗
                            ∃ xs, complete   xs         ∗
                                  ⌜ Forall (not ∘ P) xs ⌝))
                          :: E
                      |>

                      (* Normal termination. *)
                      {{ x, S' ∗ ⌜ is_true (P x) ⌝      ∗
                            ∃ xs, permitted (xs ++ [x]) ∗
                                  ⌜ Forall (not ∘ P) xs ⌝
                      }}.

  Proof.
    iIntros "#Hp HS". unfold find.
    wp_pure_steps.
    iApply (wp_lex_handle
      ((* effect list. *) _ :: E)
      ((* protocol. *) exn (λ x, S' ∗ ⌜ is_true (P x) ⌝      ∗
                                 ∃ xs, permitted (xs ++ [x]) ∗
                                       ⌜ Forall (not ∘ P) xs ⌝)%I)
      with "[HS]");
    last (rewrite is_handler_unfold; iSplit).

    (* client. *)
    { iIntros (Found). wp_pure_steps.
      iApply (iter_spec'
        ((* loop invariant. *) λ xs, ⌜ Forall (not ∘ P) xs ⌝)%I
        with "[] HS [//]").
      iIntros "!>" (us u) "Hpermitted HS' %Hus".
      wp_pure_steps. wp_bind_rule.
      iApply (wp_eff_app_l _ [(Found, _)]).
      iApply wp_dismiss.
      iSpecialize ("Hp" $! u with "HS'").
      iApply (wp_mono with "[Hpermitted] Hp").
      iIntros (b) "[-> HS'] !>".
      destruct (P u) as [|] eqn:?; simpl; wp_pure_steps.
      - iApply wp_perform; [apply elem_of_cons; by left|].
        rewrite exn_agreement.
        iExists u. rewrite Heqb. iFrame.
        iSplit; [done|]. iSplitL; [|by iIntros "HFalse"].
        iSplit; [done|].
        iExists us. by iFrame.
      - iFrame.
        iPureIntro.
        decompose_Forall; try done.
        rewrite Heqb. intros ?.
        contradiction.
    }

    (* return branch. *)
    { iIntros (?) "[%us (HS & %Hus & Hus)]".
      wp_pure_steps.
      iApply wp_perform; [apply elem_of_cons; by left|].
      rewrite exn_agreement.
      iExists #(). iFrame.
      iSplit; [done|]. iSplitL; [|by iIntros "HFalse"].
      iExists us. by iFrame.
    }

    (* effect branch. *)
    { iIntros (x k) "Hprot".
      rewrite exn_agreement.
      iDestruct "Hprot" as "[%u [-> [HPost _]]]".
      iNext. by wp_pure_steps.
    }
  Qed.


  Lemma exists_spec (p : val) (P : val → bool) (E : eff_list) :

      □ (∀ (x : val),
           S' -∗
             WP (p x) <| (Not_found, ⊥) :: E |>
                      {{ b, ⌜ b = #(P x) ⌝ ∗ S' }}) -∗

        S -∗
          WP (exists' p) (* Effects. *)
                         <| (Not_found, ⊥) :: E |>

                         (* Normal termination. *)
                         {{ b, match b with
                               | #true  => S' ∗ ∃ x xs,
                                   ⌜ is_true (P x) ⌝     ∗
                                   permitted (xs ++ [x]) ∗
                                   ⌜ Forall (not ∘ P) xs ⌝
                               | #false => S ∗ ∃ xs,
                                   complete   xs         ∗
                                   ⌜ Forall (not ∘ P) xs ⌝
                               | _ => False%I
                               end
                         }}.

  Proof.
    iIntros "#Hp HS". unfold exists'.
    wp_pure_steps.
    iApply (wp_handle with "[HS]");
    last (rewrite is_handler_unfold; iSplit).
    { wp_pure_steps. by iApply (find_spec with "Hp HS"). }
    { iIntros (x) "(HS & %Hx & [%xs [Hpermitted HForall]])".
      wp_pure_steps. iFrame. iExists x, xs. by iFrame.
    }
    { iIntros (v k). rewrite exn_agreement.
      iIntros "[%u [<- [[HS Hxs] _]]] !>".
      wp_pure_steps. by iFrame.
    }
  Qed.

End find.
