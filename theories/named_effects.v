From iris.proofmode      Require Import base tactics classes.
From iris.algebra        Require Import gmap_view excl_auth.

From hazel               Require Import weakestpre shallow_handler deep_handler.
From hazel               Require Import notation tactics.

Set Default Proof Using "Type".

(* multiple_named_effects.v *)

(** Implementation. *)

Section implementation.

Definition effect : val := λ: <>, Alloc #().

Definition perform : val := λ: "l" "v", do:("l", "v").

Definition handle : val := λ: "l" "client" "h" "r",
  try: "client" #() with
  (* Effect branch: *)
    effect (λ: "args" "k",
      let: "l'" := Fst "args" in
      let: "v" := Snd "args" in
      if: "l" = "l'" then
        #();;
        "h" "v" "k"
      else
        "k" (do: "args"))
  (* Return branch: *)
  | return (λ: "res", "r" "res")
  end.

End implementation.


(** * Logical Definitions. *)

(** Camera. *)

Section camera.

  Class effMapPreG (Σ : gFunctors) : Set := InvPreG {
    effMapPre_inG :> inG Σ
      (authR
        (gmapUR loc
          (agreeR
            (laterO
              (valO -d> (valO -d> iPropO Σ) -n> iPropO Σ)))));
  }.

  Class effMapG (Σ : gFunctors) : Set := InvG {
    effMap_inG :> effMapPreG Σ;
    effMap_name : gname;
  }.

  Definition effMapΣ := #[
    GFunctor
      (authRF
        (gmapURF loc
          (agreeRF
            (laterOF
              (valO -d> (valO -d> idOF) -n> idOF)))))
  ].

  Global Instance subG_effMapΣ {Σ} : subG effMapΣ Σ → effMapPreG Σ.
  Proof. solve_inG. Qed.

End camera.

(** Ghost theory. *)

Section ghost_theory.
  Context `{!heapG Σ, !effMapG Σ}.

  Definition protocol_unfold (Ψ : iEff Σ) :
    agree (later (valO -d> (valO -d> iPropO Σ) -n> iPropO Σ)) :=
    to_agree (Next (iEff_car Ψ)).

  Definition eff (ℓ : loc) (Ψ : iEff Σ) :=
    own effMap_name (◯ {[ ℓ := protocol_unfold Ψ ]}).

  Definition current_protocol_map (Π : gmap loc (iEff Σ)) : iProp Σ :=
    own effMap_name (● (protocol_unfold <$> Π : gmap _ _)).

  Definition Δ : iProp Σ :=
    (∃ (Π : gmap loc (iEff Σ)),
      ([∗ set] ℓ ∈ (dom (gset loc) Π), ℓ ↦ #()) ∗
      current_protocol_map Π)%I.

  Definition seen (S : gset loc) : iProp Σ :=
    ([∗ set] ℓ ∈ S, ∃ Ψ, eff ℓ Ψ)%I.

  Global Instance mapsto_protocol_pers ℓ Ψ : Persistent (eff ℓ Ψ).
  Proof. apply _. Qed.

  Global Instance seen_pers S : Persistent (seen S).
  Proof. apply _. Qed.

  Lemma seen_empty : ⊢ seen ∅.
  Proof. by unfold seen; auto. Qed.

  Lemma low_level_protocol_lookup (Π : gmap loc (iEff Σ)) ℓ Ψ :
    current_protocol_map Π ∗ eff ℓ Ψ ⊢
    ∃ Ψ', ⌜ Π !! ℓ = Some Ψ' ⌝ ∗ (protocol_unfold Ψ' ≡ protocol_unfold Ψ).
  Proof.
    rewrite -own_op own_valid auth_both_validI /=.
    iIntros "[HS #HvS]". iDestruct "HS" as (Π') "#HS".
    rewrite gmap_equivI gmap_validI.
    iSpecialize ("HS" $! ℓ). iSpecialize ("HvS" $! ℓ).
    rewrite lookup_fmap lookup_op lookup_singleton.
    rewrite option_equivI.
    case: (Π !! ℓ)=> [Ψ'|] /=; [|
    case: (Π' !! ℓ)=> [Ψ'|] /=; by iExFalso].
    iExists Ψ'. iSplit; first done.
    case: (Π' !! ℓ)=> [Ψ''|] //=.
    iRewrite "HS" in "HvS". rewrite option_validI agree_validI.
    iRewrite -"HvS" in "HS". by rewrite agree_idemp.
  Qed.

  Lemma protocol_unfold_equiv (Ψ Ψ' : iEff Σ) :
    protocol_unfold Ψ ≡ protocol_unfold Ψ' -∗ ▷ (iEff_car Ψ ≡ iEff_car Ψ' : iProp Σ).
  Proof.
    rewrite /protocol_unfold agree_equivI.
    iIntros "Heq". by iNext.
  Qed.

  Lemma protocol_map_lookup ℓ (Ψ Ψ' : iEff Σ) :
    Δ -∗ eff ℓ Ψ -∗ eff ℓ Ψ' -∗  ▷ (iEff_car Ψ ≡ iEff_car Ψ' : iProp Σ).
  Proof.
    iDestruct 1 as (Π) "[_ HS]". iIntros "#Hℓ #Hℓ'".
    iDestruct (low_level_protocol_lookup with "[HS]")
      as (ψ) "[% #Hψ]"; [iFrame; by iApply "Hℓ"|].
    iDestruct (low_level_protocol_lookup with "[HS]")
      as (ψ') "[% #Hψ']"; [iFrame; by iApply "Hℓ'"|].
    rewrite H in H0. inversion H0.
    iApply protocol_unfold_equiv.
    by iRewrite -"Hψ".
  Qed.

  Lemma low_level_protocol_map_update (Π : gmap loc (iEff Σ)) ℓ Ψ :
    Π !! ℓ = None →
      current_protocol_map Π ==∗
        current_protocol_map (<[ℓ := Ψ]> Π) ∗ eff ℓ Ψ.
  Proof.
    iIntros (Hlookup) "HΠ".
    iMod (own_update with "HΠ") as "[HΠ Hℓ]".
    { apply (@auth_update_alloc (gmapUR _ _) (protocol_unfold <$> Π)).
      apply (alloc_singleton_local_update _ ℓ (protocol_unfold Ψ)).
      by rewrite /= lookup_fmap Hlookup. done. }
    iModIntro. iFrame. unfold current_protocol_map.
    by rewrite fmap_insert.
  Qed.

  Lemma protocol_map_update' (ℓ : loc) Ψ S :
    ℓ ↦ #() -∗ seen S -∗ Δ ==∗ Δ ∗ eff ℓ Ψ ∗ ⌜ ℓ ∉ S ⌝ ∗ seen ({[ℓ]} ∪ S).
  Proof.
    iIntros "Hℓ #HS HΔ".
    iDestruct "HΔ" as (Π) "[Hdom HΠ]".

    iAssert (⌜ S ⊆ dom (gset loc) Π ⌝)%I with "[HS Hdom HΠ]" as %Hincl.
    { iInduction S as [|ℓ' S Hnot_in] "IH" using set_ind_L; [done|].
      rewrite /seen big_opS_insert; [|done].
      iDestruct "HS" as "[H HS]".
      iDestruct "H" as (Ψ') "Hℓ'".
      iDestruct ("IH" with "HS Hdom HΠ") as %IH.
      iDestruct (low_level_protocol_lookup with "[HΠ Hℓ']")
        as (Ψ'') "[% #_]"; [by iFrame|].
      iPureIntro. apply union_least;[|by apply IH].
      intros ?. rewrite elem_of_singleton elem_of_dom.
      intros ->. by exists Ψ''.
    }

    iAssert (⌜ Π !! ℓ = None ⌝)%I with "[Hℓ Hdom]" as %Hnot_in.
    { rewrite -not_elem_of_dom. clear Hincl.
      iInduction (dom (gset loc) Π) as [|ℓ' S' Hnot_in] "IH"
        using set_ind_L; [done|].
      rewrite big_opS_insert; [|done].
      rewrite not_elem_of_union not_elem_of_singleton.
      iDestruct "Hdom" as "[Hℓ' Hdom]". iSplit.
      { by iApply (mapsto_ne with "Hℓ Hℓ'"). }
      { by iApply ("IH" with "Hℓ Hdom"). }
    }

    iMod (low_level_protocol_map_update Π ℓ Ψ Hnot_in with "HΠ")
      as "[HΠ #Heff]".
    iModIntro. iSplitL "HΠ Hℓ Hdom".
    - iExists (<[ℓ:=Ψ]> Π). iFrame.
      rewrite dom_insert_L big_opS_insert; [by iFrame|].
      by rewrite not_elem_of_dom.
    - iSplitL; [by iApply "Heff"|].
      assert (ℓ ∉ S) as Hnot_in'.
      { intro Hin. cut (ℓ ∈ dom (gset loc) Π);
        [by apply not_elem_of_dom|by apply Hincl]. }
      iSplit; [done|].
      rewrite /seen big_opS_insert; [|done].
      iSplit; [|done]. by iExists Ψ.
  Qed.

End ghost_theory.

(** Protocol. *)

Section protocol.
  Context `{!heapG Σ, !effMapG Σ}.

  Definition EFF (S : gset loc) : iEff Σ :=
    (>> (ℓ : loc) (v : val) (Ψ : iEff Σ) (Q : val → iProp Σ) >>
       ! (#ℓ, v)%V     {{ Δ ∗ eff ℓ Ψ ∗ ⌜ ℓ ∈ S ⌝ ∗ iEff_car Ψ v Q }};
     << (w : val) <<
       ? (w)           {{ Δ ∗ Q w }})%ieff.

  Lemma EFF_agreement v' S Φ : protocol_agreement v' (EFF S) Φ ≡
    (∃ (ℓ : loc) (v : val) (Ψ : iEff Σ) (Q : val → iProp Σ),
      ⌜ v' = (#ℓ, v)%V ⌝ ∗
      (Δ ∗ eff ℓ Ψ ∗ ⌜ ℓ ∈ S ⌝ ∗ iEff_car Ψ v Q) ∗
      (∀ (w : val), (Δ ∗ Q w) -∗ Φ w))%I.
  Proof.
    rewrite /EFF (protocol_agreement_tele' [tele _ _ _ _] [tele _]). by auto.
  Qed.

End protocol.

(** Wekest Precondition. *)

Section weakest_precondition.
  Context `{!heapG Σ, !effMapG Σ}.

  Definition nwp_def : expr -d> gset loc -d> (val -d> iPropO Σ) -d> iPropO Σ :=
    (λ e S Φ, Δ -∗ EWP e <| EFF S |> {{ v, Δ ∗ Φ v }})%I.

  Global Instance nwp_ne e S n :
    Proper ((dist n) ==> (dist n)) (nwp_def e S).
  Proof. unfold nwp_def. intros => ???. by repeat (f_equiv; try intros ?). Qed.

  Global Instance nwp_proper e S : Proper ((≡) ==> (≡)) (nwp_def e S).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply nwp_ne; apply equiv_dist.
  Qed.

End weakest_precondition.

Notation "'WP' e ; S .{{ Φ  } }" :=
  (nwp_def e%E S Φ)
  (at level 20, e, S, Φ at level 200).

Notation "'WP' e ; S .{{ v , Φ } }" :=
  (nwp_def e%E S (λ v, Φ)%I)
  (at level 20, e, S, Φ at level 200).

(** Handler judgement. *)

Section handler_judgement.
  Context `{!heapG Σ, !effMapG Σ}.

  Definition is_handler_pre :
    (expr -d> expr -d> gset loc -d> iEff Σ -d> (_ -d> iPropO Σ) -d>
       (_ -d> iPropO Σ) -d> iPropO Σ) →
    (expr -d> expr -d> gset loc -d> iEff Σ -d> (_ -d> iPropO Σ) -d>
       (_ -d> iPropO Σ) -d> iPropO Σ)
    := λ is_handler h r S Ψ Φ Φ',
    ((∀ (v : val), Φ v -∗ WP (r v) ; S .{{ Φ' }}) ∧
     (∀ (v k : val),
       protocol_agreement v Ψ (λ (w : val), ∀ Φ'',
         ▷ is_handler h r S Ψ Φ Φ'' -∗
           WP (k w) ; S .{{ Φ'' }}) -∗
       ▷ WP (h v k) ; S .{{ Φ' }}))%I.
  Arguments is_handler_pre _%E _%E _ _%ieff _%I _%I.

  Local Instance is_handler_pre_contractive : Contractive is_handler_pre.
  Proof.
    rewrite /is_handler_pre => n hanlder handler' Hhandler S Ψ Φ h r Φ'.
    repeat (f_contractive || f_equiv). intros ?; simpl.
    repeat (f_contractive || f_equiv). apply Hhandler.
  Qed.
  Definition is_handler_def := fixpoint is_handler_pre.
  Definition is_handler_aux : seal is_handler_def. Proof. by eexists. Qed.
  Definition is_handler := is_handler_aux.(unseal).
  Definition is_handler_eq : is_handler = is_handler_def
    := is_handler_aux.(seal_eq).
  Arguments is_handler _%E _%E _ _%ieff _%I _%I.

  Global Lemma is_handler_unfold h r S Ψ Φ Φ' :
    is_handler h r S Ψ Φ Φ' ⊣⊢ is_handler_pre is_handler h r S Ψ Φ Φ'.
  Proof.
    rewrite is_handler_eq /is_handler_def.
    by apply (fixpoint_unfold is_handler_pre).
  Qed.

  Global Instance is_handler_ne h r S n :
    Proper
      ((dist n) ==> (dist n) ==> (dist n) ==> (dist n))
    (is_handler h r S).
  Proof.
    revert S.
    induction (lt_wf n) as [n _ IH]=> S Ψ1 Ψ2 HΨ Φ1 Φ2 HΦ Φ'1 Φ'2 HΦ'.
    rewrite !is_handler_unfold /is_handler_pre.
    repeat (apply protocol_agreement_ne||apply wp_ne||f_contractive||f_equiv);
    try done; try (eapply dist_le; eauto with lia).
    intros ?. do 3 (f_equiv). f_contractive.
    apply IH; try lia; eapply dist_le; eauto with lia.
  Qed.
  Global Instance is_handler_proper h r S :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (is_handler h r S).
  Proof.
    intros ??? ??? ???.
    apply equiv_dist=>n. apply is_handler_ne; apply equiv_dist; done.
  Qed.

End handler_judgement.


(** * Reasoning Rules. *)

Section reasoning_rules.
  Context `{!heapG Σ, !effMapG Σ}.

  Lemma wp_value S Φ v : Φ v ⊢ WP of_val v ; S .{{ Φ }}.
  Proof. iIntros "HΦ HΔ". iApply ewp_value. by iFrame. Qed.

  Lemma wp_pure_step e e' S Φ :
    pure_prim_step e e' → 
      ▷ WP e' ; S .{{ Φ }} ⊢ WP e ; S .{{ Φ }}.
  Proof.
    iIntros "% He' HΔ".
    iApply (ewp_pure_step' _ _ e'); first done.
    iNext. by iApply "He'".
  Qed.

  Lemma wp_bind K `{NeutralEctx K} S Φ e e' :
    e' = fill K e  →
      WP e  ; S .{{ v, WP fill K (of_val v) ; S .{{ Φ }} }} ⊢
      WP e' ; S .{{ Φ }}.
  Proof.
    iIntros (->) "He HΔ".
    iSpecialize ("He" with "HΔ").
    iApply (ewp_bind K); first done.
    iApply (ewp_mono' with "He").
    iIntros (v) "[HΔ HK]".
    by iApply "HK".
  Qed.

  Lemma fupd_wp e S Φ :
    TCEq (to_eff e) None →
    (|==> WP e ; S .{{ Φ }}) ⊢ WP e ; S .{{ Φ }}.
  Proof.
    iIntros (?) "He HΔ". iApply fupd_ewp.
    iMod "He". iModIntro. by iApply "He".
  Qed.

  Lemma EFF_mono S S' :
    S ⊆ S' →
      ⊢ (EFF S ⊑ EFF S')%ieff.
  Proof.
    iIntros (?) "!#". iIntros (v Φ).
    rewrite !EFF_agreement.
    iDestruct 1 as (ℓ v' Ψ Q) "(-> & (HΔ & Heff & % & HΨ) & Hk)".
    iExists ℓ, v', Ψ, Q. iFrame. iPureIntro. by auto.
  Qed.

  Lemma wp_mono S S' Φ Φ' e :
    S ⊆ S' →
      (∀ v, Φ v -∗ Φ' v) -∗
        WP e ; S .{{ Φ }} -∗
          WP e ; S' .{{ Φ' }}.
  Proof.
    iIntros (?) "HΦ He HΔ".
    iSpecialize ("He" with "HΔ").
    iApply (ewp_strong_mono with "He"). done.
    - by iApply EFF_mono.
    - iIntros (?) "[HΔ H]". iFrame.
      by iApply "HΦ".
  Qed.

  Lemma wp_perform (ℓ : loc) (v : val) S Ψ Φ :
    ℓ ∈ S →
      eff ℓ Ψ -∗
        protocol_agreement v Ψ Φ -∗
          WP (perform #ℓ v) ; S .{{ v, Φ v }}.
  Proof.
    iIntros (?) "Heff Hprot HΔ". rename H into Hin.
    unfold perform. ewp_pure_steps.
    iApply ewp_eff. rewrite EFF_agreement.
    iDestruct "Hprot" as (Q) "[HP Hk]".
    iExists ℓ, v, Ψ, Q. iSplit; [done|]. iFrame.
    iSplit; [done|].
    iIntros (w) "[HΔ HQ]". iNext.
    iApply ewp_value. iFrame.
    by iApply "Hk".
  Qed.

  Lemma wp_effect S S' Ψ Φ :
    seen S' -∗
      (∀ (ℓ : loc), eff ℓ Ψ -∗ ⌜ ℓ ∉ S' ⌝ -∗ seen ({[ℓ]} ∪ S') -∗ Φ #ℓ) -∗
        WP effect #() ; S .{{ v, Φ v }}.
  Proof.
    iIntros "Hseen HPost HΔ".
    unfold effect. ewp_pure_steps.
    iApply ewp_alloc.
    iIntros "!>" (ℓ) "Hℓ".
    iMod (protocol_map_update' _ Ψ with "Hℓ Hseen HΔ")
      as "(HΔ & Heff & % & Hseen)".
    iFrame. iModIntro. by iApply ("HPost" with "Heff [//] Hseen").
  Qed.

  Lemma wp_effect' S Ψ Φ :
    (∀ (ℓ : loc), eff ℓ Ψ -∗ Φ #ℓ) -∗
      WP effect #() ; S .{{ v, Φ v }}.
  Proof.
    iIntros "HPost". iApply wp_effect.
    - by iApply seen_empty.
    - iIntros (?) "? _ _".
      by iApply "HPost".
  Qed.

  Lemma wp_handle ℓ S Ψ Φ Φ' (client h r : val) :
    eff ℓ Ψ -∗
      WP client #() ; ({[ℓ]} ∪ S) .{{ v, Φ v }} -∗
        is_handler h r S Ψ Φ Φ' -∗
          WP (handle #ℓ client h r) ; S .{{ Φ' }}.
  Proof.
    iIntros "#Heff Hclient Hhandler HΔ".
    unfold handle.
    do 14 ewp_value_or_step.
    iSpecialize ("Hclient" with "HΔ").
    iApply (ewp_deep_try_with with "Hclient").

    iLöb as "IH" forall (Φ').
    rewrite deep_handler_unfold. iSplit.

    (* Return branch. *)
    { iIntros (v) "(HΔ & HΦ)".
      rewrite is_handler_unfold.
      iNext. ewp_pure_steps.
      iDestruct "Hhandler" as "[Hr _]".
      by iApply ("Hr" with "HΦ").
    }

    (* Effect branch. *)
    { iIntros (v' k) "Hprot". iNext.
      rewrite EFF_agreement.
      iDestruct "Hprot" as (ℓ' v Ψ' Q) "(-> & (HΔ & Hℓ' & % & HΨ') & Hk)".
      revert H.
      rewrite elem_of_union elem_of_singleton.
      intro HS.
      ewp_pure_steps; [done|].
      case (decide (ℓ = ℓ')) as [->|Hneq].
      { rewrite bool_decide_eq_true_2; [|done].
        iDestruct (protocol_map_lookup with "HΔ Hℓ' Heff") as "#Heq".
        rewrite is_handler_unfold.
        iDestruct "Hhandler" as "[_ Hh]".
        ewp_pure_step. iNext.
        rewrite -iEff_equivI' iEff_equivI.
        iSpecialize ("Heq" $! v Q).
        iRewrite "Heq" in "HΨ'".
        iSpecialize ("Hh" $! v k with "[HΨ' Hk]").
        { iExists Q. iFrame.
          iIntros (w) "HQ". iIntros (Φ'') "Hhandler HΔ".
          iApply ("Hk" with "[HQ HΔ]"). iFrame. iNext.
          iApply ("IH" with "Hhandler").
        }
        ewp_pure_steps.
        by iApply ("Hh" with "HΔ").
      }
      { rewrite bool_decide_eq_false_2; [|by injection 1; intros ->].
        ewp_pure_steps.
        iApply ewp_eff.
        rewrite EFF_agreement.
        iExists ℓ', v, Ψ', Q. iFrame.
        iSplit; [done|]. iSplit; [iPureIntro; set_solver|].
        iIntros (w) "[HΔ HQ]".
        iSpecialize ("Hk" $! w with "[HΔ HQ]"); [by iFrame|].
        iNext. simpl. ewp_pure_steps.
        iApply "Hk". iNext.
        by iApply ("IH" with "Hhandler").
      }
    }
  Qed.

End reasoning_rules.


(** * Tactics. *)

Ltac match_wp_goal lemma tac :=
  match goal with
  | [ |- @bi_emp_valid _                (nwp_def ?e ?S ?ϕ) ] => tac lemma e
  | [ |- @environments.envs_entails _ _ (nwp_def ?e ?S ?ϕ) ] => tac lemma e
  end.

Ltac wp_pure_step_lemma :=
  iApply wp_pure_step.

Ltac wp_bind_rule_lemma K :=
  iApply (wp_bind K).

Ltac wp_bind_rule :=
  match_wp_goal wp_bind_rule_lemma bind_rule_tac.

Ltac wp_pure_step :=
  match_wp_goal wp_pure_step_lemma pure_step_tac.

Ltac wp_value_or_step :=
  ((iApply wp_value) || (wp_bind_rule; wp_pure_step));
  try iNext; simpl.

Ltac wp_pure_steps :=
  repeat wp_value_or_step.


(** * Examples. *)

From hazel Require Import state.

Section examples.
  Context `{!heapG Σ, !effMapG Σ}.
  Context `{!inG Σ (excl_authR (leibnizO val))}.

  Definition state_handler : val := λ: "init" "client",
    let: "l" := effect #() in
    (handle "l" (λ: <>, "client" "l")
    (* effect branch: *)
      (λ: "v" "k",
         match: "v" with
         (* Read. *)
           InjL <>  => λ: "v", "k" "v" "v"
         (* Write. *)
         | InjR "w" => λ: <> , "k" #() "w"
         end)%V
    (* return branch: *)
      (λ: "v" <>, "v")%V) "init".

  Definition two_mem_cells : expr :=
    state_handler #() (λ: "a",
      state_handler #() (λ: "b",
        perform "a" (write #1);;
        perform "b" (write #2);;
        (perform "a" (read #()),
         perform "b" (read #()))))%V.

  (** Verification. *)

  (* Specification and proof of [state_handler]. *)
  Lemma state_handler_spec (client init : val) S (Φ : val → iProp Σ) :
    (∀ (a : loc) (I : val → iProp Σ),
       eff a (Ψ_state I) -∗
         I init -∗
           WP (client #a) ; ({[a]} ∪ S) .{{ Φ }}) -∗
     WP state_handler init client ; S .{{ Φ }}.
  Proof using effMapG0 heapG0 inG0 Σ.
    iIntros "Hspec". iApply fupd_wp.
    iMod (ghost_var_alloc init) as (γ) "[Hstate Hpoints_to]". iModIntro.
    unfold state_handler.
    wp_pure_steps. wp_bind_rule. simpl.
    iApply (wp_effect' _ (Ψ_state (points_to γ))).
    iIntros (a) "#Heff_a".
    wp_pure_steps.
    iApply (wp_bind (ConsCtx (AppLCtx _) EmptyCtx)). done. simpl.
    iApply (wp_handle with "Heff_a [Hspec Hpoints_to]").
    { wp_pure_step; by iApply ("Hspec" with "Heff_a Hpoints_to"). }
    { iClear "Heff_a".
      iLöb as "IH" forall (γ init).
      rewrite !is_handler_unfold. iSplit.
      { iIntros (v) "HΦ". by wp_pure_steps. }
      { iIntros (v k) "Hprot_agr".
        iDestruct (Ψ_state_agreement with "Hprot_agr") as "[Hread|Hwrite]".
        { (* Read. *)
          rewrite Ψ_read_agreement.
          iNext. iApply fupd_wp.
          iDestruct "Hread" as (w) "(-> & Hpoints_to & Hk)".
          iDestruct (ghost_var_agree γ init w with "[$]") as "%". rewrite H.
          iSpecialize ("Hk" with "Hpoints_to"). iModIntro. unfold read.
          wp_pure_steps. wp_bind_rule. simpl.
          iSpecialize ("IH" with "Hstate").
          by iApply ("Hk" with "IH").
        }
        { (* Write. *)
          rewrite Ψ_write_agreement.
          iNext. iApply fupd_wp.
          iDestruct "Hwrite" as (v' w') "(-> & Hpoints_to & Hk)".
          iMod ((ghost_var_update _ w') with "Hstate Hpoints_to") as
            "[Hstate Hpoints_to]".
          iSpecialize ("Hk" with "Hpoints_to"). iModIntro. unfold write.
          wp_pure_steps. wp_bind_rule. simpl.
          iSpecialize ("IH" with "Hstate").
          by iApply ("Hk" with "IH").
        }
      }
    }
  Qed.

  (* Specification and proof of [two_mem_cells]. *)
  Lemma two_mem_cells_spec :
    ⊢ WP two_mem_cells ; ∅ .{{ y, ⌜ y = (#1, #2)%V ⌝ }}.
  Proof using effMapG0 heapG0 inG0 Σ.
    iApply state_handler_spec.
    iIntros (a I) "#Heff_a HI".
    wp_pure_steps.
    iApply state_handler_spec.
    iIntros (b J) "#Heff_b HJ".
    wp_pure_steps.
    iApply (wp_bind (ConsCtx (AppRCtx _) EmptyCtx)). done. simpl.
    iApply (wp_perform with "Heff_a"). set_solver.
    iApply protocol_agreement_sum_intro_r.
    rewrite Ψ_write_agreement.
    iExists #(), #1. iFrame. iSplitR; [done|].
    iIntros "HI". wp_pure_steps.
    iApply (wp_bind (ConsCtx (AppRCtx _) EmptyCtx)). done. simpl.
    iApply (wp_perform with "Heff_b"). set_solver.
    iApply protocol_agreement_sum_intro_r.
    rewrite Ψ_write_agreement.
    iExists #(), #2. iFrame. iSplitR; [done|].
    iIntros "HJ". wp_pure_steps.
    iApply (wp_bind (ConsCtx (PairRCtx _) EmptyCtx)). done. simpl.
    iApply (wp_perform with "Heff_b"). set_solver.
    iApply protocol_agreement_sum_intro_l.
    rewrite Ψ_read_agreement.
    iExists #2. iFrame. iSplitR; [done|iIntros "_"].
    iApply (wp_bind (ConsCtx (PairLCtx _) EmptyCtx)). done. simpl.
    iApply (wp_perform with "Heff_a"). set_solver.
    iApply protocol_agreement_sum_intro_l.
    rewrite Ψ_read_agreement.
    iExists #1. iFrame. iSplitR; [done|iIntros "_"].
    by wp_pure_steps.
  Qed.

End examples.
