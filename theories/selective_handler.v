(* selective_handler.v

*)

From stdpp               Require Import list.
From iris.proofmode      Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation weakestpre shallow_handler deep_handler.
From hazel               Require Export heap.


(** * Selective Handler. *)

(* Program definition. *)

Definition selective_try_with : val := λ: "e" "f" "h" "r",
  try: "e" #() with
    effect (λ: "v" "k",
      if: "f" "v" then "h" "v" "k" else "k" (do: "v"))
  | return "r"
  end.

(** * Reasoning Rules. *)

Section selective_handler.
Context `{!heapG Σ}.

(* Selective handler judgement. *)

Definition selective_handler_pre :
  (coPset -d> (val → Prop) -d> expr -d> expr -d>
        iEff Σ -d> iEff Σ -d> (val -d> iPropO Σ) -d> (val -d> iPropO Σ) -d> iPropO Σ) →
  (coPset -d> (val → Prop) -d> expr -d> expr -d>
        iEff Σ -d> iEff Σ -d> (val -d> iPropO Σ) -d> (val -d> iPropO Σ) -d> iPropO Σ)
  := λ selective_handler E P h r Ψ Ψ' Φ Φ',

  ((shallow_return_handler E r Ψ' Φ Φ') ∧

   (∀ v k,
     protocol_agreement v (P ?> Ψ) (λ w, ∀ Ψ'' Φ'',
       ( ▷ selective_handler E P h r Ψ Ψ'' Φ Φ'' -∗
         EWP (Val k) (Val w) @ E <| Ψ'' |> {{ Φ'' }})) -∗
     ▷ EWP App (App h (Val v)) (Val k) @ E <| Ψ' |> {{ Φ' }}) ∧

   (∀ v k,
     protocol_agreement v ((λ v, ¬ P v : Prop) ?> Ψ) (λ w, ∀ Ψ'' Φ'',
       ( ▷ selective_handler E P h r Ψ Ψ'' Φ Φ'' -∗
         EWP (Val k) (Val w) @ E <| Ψ'' |> {{ Φ'' }})) -∗
     ▷ protocol_agreement v Ψ' (λ w,
         EWP (Val k) (Val w) @ E <| Ψ' |> {{ Φ' }})))%I.

Arguments selective_handler_pre _ _ _%E _%E _%ieff _%ieff _%I _%I.

Local Instance selective_handler_pre_contractive : Contractive selective_handler_pre.
Proof.
  rewrite /selective_handler_pre => n hanlder handler' Hhandler E P h r Ψ Ψ' Φ Φ'.
  repeat (f_contractive || f_equiv); intros ?; simpl;
  repeat (f_contractive || f_equiv); apply Hhandler.
Qed.
Definition selective_handler_def := fixpoint selective_handler_pre.
Definition selective_handler_aux : seal selective_handler_def. Proof. by eexists. Qed.
Definition selective_handler := selective_handler_aux.(unseal).
Definition selective_handler_eq : selective_handler = selective_handler_def
  := selective_handler_aux.(seal_eq).
Arguments selective_handler _ _ _%E _%E _%ieff _%ieff _%I _%I.

Global Lemma selective_handler_unfold E P h r Ψ Ψ' Φ Φ' :
  selective_handler E P h r Ψ Ψ' Φ Φ' ⊣⊢
  selective_handler_pre selective_handler E P h r Ψ Ψ' Φ Φ'.
Proof.
  rewrite selective_handler_eq /selective_handler_def.
  by apply (fixpoint_unfold selective_handler_pre).
Qed.

Global Instance selective_handler_ne E P h r n :
  Proper
    ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n))
  (selective_handler E P h r).
Proof.
  induction (lt_wf n) as [n _ IH]=> Ψ1 Ψ2 HΨ Ψ'1 Ψ'2 HΨ' Φ1 Φ2 HΦ Φ'1 Φ'2 HΦ'.
  rewrite !selective_handler_unfold /selective_handler_pre.
  repeat (apply protocol_agreement_ne||apply ewp_ne||f_contractive||f_equiv);
  try done; try (eapply dist_le; eauto with lia).
  intros ?. do 2 (f_equiv=>?). f_equiv. f_contractive.
  apply IH; try lia; eapply dist_le; eauto with lia.
  intros ?. do 2 (f_equiv=>?). f_equiv. f_contractive.
  apply IH; try lia; eapply dist_le; eauto with lia.
  intros ?. f_equiv; eapply dist_le; eauto with lia.
Qed.
Global Instance selective_handler_proper E P h r :
  Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) (selective_handler E P h r).
Proof.
  intros ??? ??? ??? ???.
  apply equiv_dist=>n. apply selective_handler_ne; apply equiv_dist; done.
Qed.


(* Selective handler reasoning rule. *)

Lemma ewp_selective_try_with (P : val → Prop) `{!∀ x, Decision (P x)}
  E Ψ Ψ' Φ Φ' (f : val) (e : expr) (h r : val) :
  EWP e @ E <| Ψ |> {{ Φ }}
    -∗
      □ (∀ (x : val), EWP f x @ E {{ λ y, ⌜ y = #(bool_decide (P x)) ⌝ }} )
        -∗
          selective_handler E P h r Ψ Ψ' Φ Φ'
 -∗
   EWP (selective_try_with (λ: <>, e) f h r) @ E <| Ψ' |> {{ Φ' }}.
Proof.
  iIntros "He #f_spec Hhandler".  
  unfold selective_try_with.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppRCtx _) EmptyCtx))). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply (ewp_deep_try_with with "[He] [Hhandler]").
  { iApply ewp_pure_step. apply pure_prim_step_beta. simpl. by iApply "He". }
  { iLöb as "IH" forall (Ψ Ψ' Φ Φ').
    rewrite deep_handler_unfold selective_handler_unfold.
    iSplit; [by iDestruct "Hhandler" as "[H _]"|].
    iIntros (v k) "Hprot". iNext.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (IfCtx _ _)). done.
    iApply (ewp_strong_mono with "f_spec"); [done|iApply iEff_le_bottom|].
    iIntros (b) "->". iModIntro. simpl.
    case_eq (bool_decide (P v)); intro HP;
    iApply ewp_pure_step'; try apply pure_prim_step_if.
    { iDestruct "Hhandler" as "[_ [Hh _]]". iApply "Hh".
      rewrite protocol_agreement_filter. iSplit; [
      iPureIntro; apply (bool_decide_eq_true_1 (P v) HP) |].
      iApply (protocol_agreement_strong_mono with "Hprot").
      { by iApply iEff_le_refl. }
      { iIntros (v') "Hk".  iIntros (Ψ'' Φ'') "Hhandler".
        iApply "Hk". by iApply "IH".
      }
    }
    { iDestruct "Hhandler" as "[_ [_ Hk]]".
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_do.
      iApply ewp_eff. iSpecialize ("Hk" with "[Hprot]").
      { rewrite protocol_agreement_filter.  iSplit; [
        iPureIntro; apply (bool_decide_eq_false_1 (P v) HP) |].
        iApply (protocol_agreement_strong_mono with "Hprot").
        { by iApply iEff_le_refl. }
        { iIntros (v') "Hk".  iIntros (Ψ'' Φ'') "Hhandler".
          iApply "Hk". by iApply "IH".
        }
      }
      iNext. iApply (protocol_agreement_mono with "Hk").
      iIntros (v') "Hk". iNext. by iApply ewp_value.
    }
  }
Qed.

End selective_handler.


Section label_selection.
Context `{!heapG Σ}.

Definition fresh_label : val := λ: <>, ref #().

Definition label_selection : val := λ: "l" "v", "l" = Fst "v".

Definition label_try_with : val := λ: "e" "l" "h" "r",
  selective_try_with (λ: <>, "e" #()) (λ: "v", label_selection "l" "v") "h" "r".


(* Specification of [fresh_label]. *)

Definition known_labels : gset loc → iProp Σ := λ S,
  ([∗ set] l ∈ S, l ↦□ #())%I.

Global Instance known_labels_persistent S : Persistent (known_labels S).
Proof. rewrite /ownI. apply _. Qed.

Lemma known_labels_empty : ⊢ known_labels ∅.
Proof. unfold known_labels. by auto. Qed.

Lemma fresh_label_spec E Ψ S :
  known_labels S -∗
    EWP fresh_label #() @ E <| Ψ |> {{ lk, ∃ (l : loc), ⌜ lk = #l ⌝ ∗
      ⌜ l ∉ S ⌝ ∗ known_labels ({[l]} ∪ S) }}.
Proof.
  iIntros "HS". iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_mono'; [by iApply ewp_alloc|].
  iIntros (v) "H". iDestruct "H" as (l) "[-> Hl]".

  iAssert (⌜l ∉ S⌝ ∗ known_labels S ∗ l ↦ #())%I
    with "[HS Hl]" as "(% & HS & Hl)".
  { iSplit; [|iFrame].
    iInduction S as [|l' S Hnot_in] "IH" using set_ind_L.
    { iPureIntro. by apply not_elem_of_empty. }
    { rewrite not_elem_of_union not_elem_of_singleton /known_labels.
      rewrite big_opS_insert; [|done].
      iDestruct "HS" as "[Hl' HS]". iSplit.
      { by iApply (mapsto_ne with "Hl Hl'"). }
      { by iApply ("IH" with "HS Hl"). }
    }
  }

  iMod (mapsto_persist with "Hl") as "Hl". iModIntro.
  iExists l. rewrite /known_labels big_opS_insert; [|done].
  by iFrame.
Qed.


(* Specification of [label_selection]. *)

Definition compare_label (l : val) : val → Prop := λ v,
  match v with PairV r _ => l = r | _ => False end.

Global Instance compare_label_dec l v : Decision (compare_label l v).
Proof. unfold compare_label. case v; solve_decision. Qed.

(* **************************************************************** *)
(* FIXME: the lemma bellow is false: if [v] is not a value pair,
          then [label_selection #l v] blocks. Moreover, there is no
          implementation written in [eff_lang] that would satisfy
          this specification, because the language doesn't provide
          pair deconstructors other than [Fst] and [Snd].

          Here are some ideas for fixing this in the future:
          (1) Extend [eff_lang] with dynamic pair deconstructors.
          (2) Add an "and" operation on protocols to describe
              effect arguments sent in the form of value pairs.
*)

Lemma label_selection_spec E Ψ (l : val) (v : val) :
  ⊢ EWP label_selection l v @ E <| Ψ |> {{ b,
      ⌜ b = #(bool_decide (compare_label l v)) ⌝ }}.
Admitted.
(* **************************************************************** *)


(* Labelled-effect handler reasoning rule. *)

Lemma ewp_label_try_with E Ψ Ψ' Φ Φ' (l : val) (e : expr) (h r : val) :
  EWP e @ E <| Ψ |> {{ Φ }}
    -∗
      selective_handler E (compare_label l) h r Ψ Ψ' Φ Φ'
 -∗
   EWP (label_try_with (λ: <>, e) l h r) @ E <| Ψ' |> {{ Φ' }}.
Proof.
  iIntros "He Hhandler".
  iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppLCtx _)
                   (ConsCtx (AppLCtx _) (ConsCtx (AppRCtx _) EmptyCtx))))). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  unfold label_try_with.
  iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppLCtx _)
                   (ConsCtx (AppLCtx _) EmptyCtx)))). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppLCtx _) EmptyCtx))). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply (ewp_bind (ConsCtx (AppLCtx _) EmptyCtx)). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppLCtx _)
                   (ConsCtx (AppRCtx _) (EmptyCtx))))). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply (ewp_selective_try_with  with "[He] [] [Hhandler]").
  { iApply ewp_pure_step. apply pure_prim_step_beta. simpl. by iApply "He". }
  { iModIntro. iIntros (v). iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    by iApply label_selection_spec.
  }
  { by iApply "Hhandler". }
Qed.

End label_selection.


Notation LabelTryWith e l h r :=
  (App (App (App (App label_try_with (Lam BAnon e)) l) h) r) (only parsing).

Notation "'try:' e 'with' 'label' l 'effect' h | 'return' r 'end'" :=
  (LabelTryWith e l h r)
  (e, l, h, r at level 200, only parsing) : expr_scope.

