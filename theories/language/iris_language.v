(* iris_language.v *)

(* This file proves that [eff_lang] is a language in the Iris sense: it
   satisfies the record type [LanguageMixin] defined in the Iris project.

   Consequently, a default notion of [wp] is automatically available in Iris
   as a (sound) tool to reason about [eff_lang] programs. This notion is not
   well-suited to [eff_lang] programs, however because it lacks a way of
   describing the effects that a program may throw. It is nevertheless useful
   in the proof that out custom notion of [wp] is sound, which claim is
   formalized and proved in file [program_logic/adequacy.v].
*)

From iris.program_logic Require Import language.
From language Require Import syntax semantics neutral_contexts.


(* ========================================================================== *)
(** * Language. *)

(* Reduction relation in the Iris format. *)
(* To prove that [eff_lang] is a language, we must define a reduction
   relation that fits the format formalized by Iris. *)
Definition prim_step' e1 σ1 (obs : list unit) e2 σ2 (efs : list expr) :=
  match obs with _ :: _ => False | [] =>
      prim_step e1 σ1 e2 σ2 efs
  end.

(* [eff_lang] satisfies the record type [LanguageMixin]. *)
Lemma eff_lang_mixin : LanguageMixin of_val to_val prim_step'.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val.
  unfold prim_step'.
  intros e σ obs e' σ' efs.
  case obs; [|done].
  induction 1 as [K e1' e2' -> ? ?].
  case K as [|f K].
  - revert H0. apply val_head_stuck.
  - apply fill_frame_val.
Qed.

(* [eff_lang] is a language in the Iris sense. *)
Canonical Structure eff_lang : language := Language eff_lang_mixin.


(* ========================================================================== *)
(** * Reducible Predicate. *)

(* Properties of the predicate [reducible] defined by Iris and
   specialized here to [eff_lang]. *)

Lemma reducible_fill_frame_eff f `{NeutralFrame f} m v k σ :
  reducible (fill_frame f (Eff m v k)) σ.
Proof.
  unfold reducible. simpl. exists [], (Eff m v (f :: k)), σ, [].
  apply (Ectx_prim_step _ _ _ _ _ [] (fill_frame f (Eff m v k))
                                        (Eff m v (f :: k))); eauto.
  by apply neutral_frame.
Qed.

Lemma reducible_fill k e σ : reducible e σ → reducible (fill k e) σ.
Proof.
  unfold reducible; simpl; rewrite /prim_step'; simpl.
  destruct 1 as [obs [e' [σ' [efs Hstep]]]].
  case obs in Hstep; [|done].
  inversion Hstep. simplify_eq. exists [], (fill (k ++ k0) e2'), σ', efs.
  apply (Ectx_prim_step _ _ _ _ _ (k ++ k0) e1' e2'); eauto.
  by rewrite fill_app.
Qed.

Lemma reducible_fill_frame f e σ : reducible e σ → reducible (fill_frame f e) σ.
Proof. by apply (reducible_fill [f]). Qed.

Lemma eff_irreducible m v k σ : irreducible (Eff m v k) σ.
Proof.
  unfold irreducible; simpl. unfold prim_step'; simpl.
  intros obs ???.
  case obs; last auto. 
  inversion 1.
  destruct k0 as [|f k0].
  - by simpl in H0; simplify_eq; inversion H2.
  - by destruct f; naive_solver.
Qed.

Lemma reducible_not_eff e σ : reducible e σ → to_eff e = None.
Proof.
  intros Hred. case_eq (to_eff e);[|done]. destruct p as ((m, v), k).
  intros Heq. rewrite -(of_to_eff e m v k Heq) in Hred.
  specialize (eff_irreducible m v k σ). by rewrite <-not_reducible.
Qed.

Lemma reducible_fill_frame_inv f e σ :
  to_val e = None →
    to_eff e = None →
      reducible (fill_frame f e) σ →
        reducible e σ.
Proof.
  intros ??. unfold reducible; simpl; unfold prim_step'; simpl.
  intros [obs [e₂ [σ' [efs Hstep]]]].
  case obs in Hstep; [|done].
  destruct (Ectxi_prim_step_inv _ _ _ _ _ _ H H0 Hstep) as [e' [Hstep' _]].
  by exists [], e', σ', efs.
Qed.


(* ========================================================================== *)
(** * Pure Steps. *)

(* -------------------------------------------------------------------------- *)
(** Definition of [pure_prim_step]. *)

(* [pure_prim_step] is the pure-step reduction relation:
   the relation [pure_prim_step e1 e2] holds if [e1] reduces to [e2]
   deterministically and without updating the state. *)
Record pure_prim_step (e1 e2 : expr) efs := {
  pure_prim_step_safe σ :
    prim_step e1 σ e2 σ efs;
  pure_prim_step_det σ1 e2' σ2 efs' :
    prim_step e1 σ1 e2' σ2 efs' → σ2 = σ1 ∧ e2' = e2 ∧ efs = efs'
}.


(* -------------------------------------------------------------------------- *)
(** Properties of [pure_prim_step]. *)

Lemma pure_prim_step_imp_reducible e1 e2 efs:
  pure_prim_step e1 e2 efs → (∀ σ, reducible e1 σ).
Proof. intros Hstep ?. exists [], e2, σ, efs. by apply Hstep. Qed.

Lemma pure_prim_stepI e1 e2 efs :
  (∀ σ, head_step e1 σ e2 σ efs) →
    (∀ σ1 e2' σ2 efs', prim_step e1 σ1 e2' σ2 efs' → σ2 = σ1 ∧ e2' = e2 ∧ efs = efs') →
      pure_prim_step e1 e2 efs.
Proof.
  intros Hhead_step Hstep_det. constructor; auto.
  intros ?. apply (Ectx_prim_step _ _ _ _ _ [] e1 e2); by eauto.
Qed.

Lemma pure_prim_stepI' e1 e2 efs :
  (∀ σ, head_step e1 σ e2 σ efs) →
    (* If this holds, then we look at the prim_step and know that either k = [], in which case the goal follows from
        head_step determinism, or e1' is a value, in which case e1' could not do a head_step which leads to contradiction. *)
    (∀ k e1', e1 = fill k e1' → k = [] ∨ ∃ v, e1' = Val v) →
      pure_prim_step e1 e2 efs.
Proof.
  intros Hstep Hfill. apply pure_prim_stepI; auto.
  intros ????. inversion 1. simplify_eq.
  destruct (Hfill k e1' eq_refl) as [->|[v ->]]; [|by inversion H2].
  specialize (Hstep σ1) as H3.
  simpl in H3.
  (* now we to a big case analysis for head_step determinism. *)
  inversion H2; simplify_eq; try naive_solver;
  inversion H3; simplify_eq; try naive_solver.
  - unfold heap_upd in H10. simpl in H10.
    rewrite lookup_insert in H10. by contradict H10.
  - (* Alloc *)
    unfold heap_upd in H4. simpl in H4.
    rewrite lookup_insert in H4. by contradict H4.
  - (* Store *)
    split; [|done]. destruct σ1 as [σ1].
    by rewrite /heap_upd /= insert_insert.
  - (* CmpXchg *)
    (* There are 3 cases for CmpXchg:
       1. Location is updated to a new value, this leads to a contradiction.
       2. Location is updated to the same value, this does not change the state so it's valid.
       3. Comparison fails, so location is not updated so it's valid. 
       
       Case 1 is automatically solved by inversion above.
       *)
    destruct (bool_decide (vl0 = v1)) eqn:Evl0.
    + (* from this we know vl = vl0 = v2, so we are in case 2. *)
      assert (heap (heap_upd <[l:=v2]> σ1) !! l = Some vl0) as H8 by exact H7.
      unfold heap_upd in H7. simpl in H7.
      rewrite lookup_insert in H7. injection H7 as ->.
      rewrite H10 in H8.
      rewrite H8 in H0. injection H0 as ->.
      rewrite Evl0 in H2. rewrite Evl0.
      split; [|by split].
      by rewrite /heap_upd /= insert_insert.
    + rewrite H7 in H0. injection H0 as ->.
      rewrite Evl0.
      by split; split.
  - unfold heap_upd in H11. simpl in H11.
    rewrite lookup_insert in H11. done.
Qed.

Lemma val_not_pure v e efs : ¬ pure_prim_step (Val v) e efs.
Proof.
  intros Hstep.
  specialize (pure_prim_step_imp_reducible _ _ _ Hstep {|heap:=∅|}) as H.
  specialize (reducible_not_val (Val v) {|heap:=∅|} H); done.
Qed.

Lemma val_not_pure' v e e' efs : to_val e = Some v → ¬ pure_prim_step e e' efs.
Proof. intro H1; rewrite <- (of_to_val _ _ H1). by apply val_not_pure. Qed.

Lemma eff_not_pure m v k e efs : ¬ pure_prim_step (Eff m v k) e efs.
Proof.
  intros H0.
  specialize (pure_prim_step_imp_reducible _ _ _ H0 {|heap:=∅|}).
  specialize (eff_irreducible m v k {|heap:=∅|}).
  by rewrite <-not_reducible.
Qed.

Lemma eff_not_pure' p e e' efs : to_eff e = Some p → ¬ pure_prim_step e e' efs.
Proof.
  intro H1. destruct p as ((m, v), k).
  rewrite <- (of_to_eff _ _ _ _ H1).
  by apply eff_not_pure.
Qed.

Lemma pure_prim_step_UnOp op v v' :
  un_op_eval op v = Some v' →
    pure_prim_step (UnOp op (Val v)) (Val v') [].
Proof.
  intro Heval. apply pure_prim_stepI'; [intros ?; by apply UnOpS|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H1)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_BinOp op v1 v2 v' :
  bin_op_eval op v1 v2 = Some v' →
    pure_prim_step (BinOp op (Val v1) (Val v2)) (Val v') [].
Proof.
  intro Heval. apply pure_prim_stepI'; [intros ?; by apply BinOpS|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H1)) as [-> ->]; by eauto.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H2)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_beta f x e v :
  pure_prim_step ((App (Val $ RecV f x e) (Val v)))
                 (subst' x v (subst' f (RecV f x e) e)) [].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply BetaS|].
  intros ??. destruct k as [|f' k]; [intros _; by left|].
  intros Hfill; right.
  destruct f'; try naive_solver. simpl in Hfill.
  - exists (RecV f x e). inversion Hfill.
    by destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->].
  - exists v. inversion Hfill.
    by destruct (fill_val' _ _ _ (eq_sym H1)) as [-> ->].
Qed.

Lemma pure_prim_step_Rec f x e :
  pure_prim_step (Rec f x e) (Val $ RecV f x e) [].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply RecS|].
  intros ??. destruct k as [|f' k]; try destruct f'; by naive_solver.
Qed.

Lemma pure_prim_step_InjL v :
  pure_prim_step (InjL $ Val v) (Val $ InjLV v) [].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply InjLS|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_InjR v :
  pure_prim_step (InjR $ Val v) (Val $ InjRV v) [].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply InjRS|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_Case_InjL v e1 e2 :
  pure_prim_step (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)) [].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply CaseLS|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_Case_InjR v e1 e2 :
  pure_prim_step (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)) [].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply CaseRS|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_If e1 e2 b :
  pure_prim_step (If (Val $ LitV $ LitBool b) e1 e2) (if b then e1 else e2) [].
Proof.
  apply pure_prim_stepI'; [
  intros ?; case b; [by apply IfTrueS|by apply IfFalseS]|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_If_true e1 e2 :
  pure_prim_step (If (Val $ LitV $ LitBool true) e1 e2) e1 [].
Proof. by apply pure_prim_step_If. Qed.

Lemma pure_prim_step_If_false e1 e2 :
  pure_prim_step (If (Val $ LitV $ LitBool false) e1 e2) e2 [].
Proof. by apply pure_prim_step_If. Qed.

Lemma pure_prim_step_Pair v1 v2 :
  pure_prim_step (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2) [].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply PairS|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
  - intros [=]; destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
  - intros [=]; destruct (fill_val' _ _ _ (eq_sym H1)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_Fst v1 v2 :
  pure_prim_step (Fst (Val $ PairV v1 v2)) (Val v1) [].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply FstS|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
  intros [=]; destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_Snd v1 v2 :
  pure_prim_step (Snd (Val $ PairV v1 v2)) (Val v2) [].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply SndS|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
  intros [=]; destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_Fork e :
  pure_prim_step (Fork e) (Val $ LitV LitUnit) [e].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply ForkS|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
Qed.

Lemma pure_prim_step_TryWithVal v h r :
  pure_prim_step (TryWith (Val v) h r) (App r (Val v)) [].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply TryWithRetS|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_TryWithMSEff v k h r :
  pure_prim_step (TryWith (Eff MS v k) h r)
                 (App (App h (Val v)) (Val $ KontV k)) [].
Proof.
  apply pure_prim_stepI.
  - intros ?. by apply TryWithMSEffS.
  - intros ???. inversion 1; simplify_eq.
    destruct k0 as [|f k0]; try destruct f; try naive_solver.
    + simpl in *. simplify_eq. by inversion H2.
    + destruct k0 as [|f k0]; try destruct f; try naive_solver.
      simpl in *. simplify_eq. by inversion H2.
Qed.

Lemma pure_prim_step_Kont k w :
  pure_prim_step (App (Val $ KontV k) (Val w)) (fill k (Val w)) [].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply KontS|].
  intros ??. destruct k0 as [|f k0]; try destruct f; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
  intros [=]. destruct k0 as [|f k0]; try destruct f; try naive_solver.
Qed.

Lemma pure_prim_step_Do m v :
  pure_prim_step (Do m (Val v)) (Eff m v []) [].
Proof.
  apply pure_prim_stepI'; [intros ?; by apply DoS|].
  intros ??. destruct k as [|f k]; try destruct f; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H1)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_Eff `{NeutralFrame f} m v k :
  pure_prim_step (fill_frame f (Eff m v k)) (Eff m v (f :: k)) [].
Proof.
  apply pure_prim_stepI; [intros ?; by apply H|].
  intros ??.
  inversion 1. destruct k0 as [|f1 k0]; simpl in *; simplify_eq.
  - destruct f; simpl in H3; inversion H3; try naive_solver;
    by specialize (TryWithCtx_not_neutral e2 e3).
  - cut ((fill k0 e1' = Eff m v k) ∨ (∃ v', fill k0 e1' = Val v')).
    + destruct k0 as [|f2 k0]; simpl.
      * case; [intros -> | destruct 1 as [v' ->]]; by inversion H3.
      * case; [| destruct 1 as [v' H4]; destruct f2; by naive_solver].
        destruct k0 as [|f3 k0]; [| destruct f2, f3; by naive_solver].
        simpl. destruct f2; try naive_solver.
    + destruct f, f1; simpl in H1; by naive_solver.
Qed.

Lemma pure_prim_step_fill_frame f e e' efs :
  pure_prim_step e e' efs →
    pure_prim_step (fill_frame f e) (fill_frame f e') efs.
Proof.
  constructor.
  - intros ?. by apply (Ectxi_prim_step' f e e'), H.
  - intros ???? Hstep.
    have not_val : to_val e = None.
    { by apply (reducible_not_val _ σ1),
               (pure_prim_step_imp_reducible _ e' efs). }
    have not_eff : to_eff e = None.
    { by apply (reducible_not_eff _ σ1),
               (pure_prim_step_imp_reducible _ e' efs). }
    destruct (Ectxi_prim_step_inv f e _ _ _ _ not_val not_eff Hstep) as [e'' [He'' ->]].
    by destruct (pure_prim_step_det _ _ _ H _ _ _ _ He'') as (-> & -> & ->).
Qed.

Lemma pure_prim_step_fill k e e' efs :
  pure_prim_step e e' efs →
    pure_prim_step (fill k e) (fill k e') efs.
Proof.
  induction k as [|f k]; [done|].
  intros ?. simpl. apply pure_prim_step_fill_frame.
  apply IHk; eauto.
Qed.

(* a.d. TODO describe why we add this. *)
Definition pure_prim_step_no_fork e e' := pure_prim_step e e' [].

Lemma tc_pure_prim_step_no_fork_fill k e e' :
  tc pure_prim_step_no_fork e e' →
    tc pure_prim_step_no_fork (fill k e) (fill k e').
Proof.
  induction 1.
  - apply tc_once.
    by apply pure_prim_step_fill.
  - apply (tc_l _ _ (fill k y)); [|done].
    by apply pure_prim_step_fill.
Qed.

Lemma rtc_pure_prim_step_no_fork_fill k e e' :
  rtc pure_prim_step_no_fork e e' →
    rtc pure_prim_step_no_fork (fill k e) (fill k e').
Proof.
  induction 1; [done|].
  apply (rtc_l _ _ (fill k y)); [|done].
  by apply pure_prim_step_fill.
Qed.

Lemma tc_pure_prim_step_no_fork_fill_frame f e e' :
  tc pure_prim_step_no_fork e e' →
    tc pure_prim_step_no_fork (fill_frame f e) (fill_frame f e').
Proof. by apply (tc_pure_prim_step_no_fork_fill [f]). Qed.

Lemma rtc_pure_prim_step_no_fork_fill_frame f e e' :
  rtc pure_prim_step_no_fork e e' →
    rtc pure_prim_step_no_fork (fill_frame f e) (fill_frame f e').
Proof. by apply (rtc_pure_prim_step_no_fork_fill [f]). Qed.

Lemma rtc_pure_prim_step_no_fork_Eff `{NeutralEctx k} m v k' :
  rtc pure_prim_step_no_fork (fill k (Eff m v k')) (Eff m v (k ++ k')).
Proof.
  induction k as [|f k].
  - done.
  - specialize (ConsCtx_neutral_inv' _ _ H) as f_neutral.
    specialize (ConsCtx_neutral_inv  _ _ H) as  K_neutral.
    apply (rtc_r _ (fill_frame f (Eff m v (k ++ k')))); simpl.
    + by apply rtc_pure_prim_step_no_fork_fill_frame; auto.
    + by apply pure_prim_step_Eff.
Qed.


(* ========================================================================== *)
(** * Stateful Steps. *)

(* Inversion principle for reduction of a one-shot continuation. *)
Lemma prim_step_inv_Cont k l (w : val) σ e' σ' efs :
  prim_step (App (Val $ (ContV k l)) (Val w)) σ e' σ' efs →
    e' = fill k (Val w) ∧ σ' = heap_upd <[l := LitV $ LitBool $ true]> σ ∧ efs = [].
Proof.
  intros Hstep. inversion Hstep.
  repeat ((destruct k0 as [|f k0]; [|destruct f; try naive_solver];
  simpl in *; simplify_eq) || (try by inversion H1)).
Qed.

(* Inversion principle for the reification of evaluation
   context [k] as a one-shot continuation. *)
Lemma prim_step_inv_TryWithOSEff (v : val) k h r σ e' σ' efs :
  prim_step (TryWith (Eff OS v k) h r) σ e' σ' efs →
    ∃ l, σ.(heap) !! l = None ∧
         σ' = heap_upd <[l := LitV $ LitBool $ false]> σ ∧
         e' = (App (App h (Val v)) (Val $ ContV k l)) ∧
         efs = [].
Proof.
  intros Hstep. inversion Hstep.
  repeat ((destruct k0 as [|f k0]; [|destruct f; try naive_solver];
  simpl in *; simplify_eq) || (try by inversion H1)).
  inversion H1. by exists l.
Qed.
