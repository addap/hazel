(* deep_handler_reasoning.v *)

(* This file introduces reasoning rules for deep handlers. *)

From iris.proofmode Require Import base tactics classes.
From program_logic Require Import protocols weakest_precondition
                                  basic_reasoning_rules state_reasoning
                                  shallow_handler_reasoning tactics.

(* ========================================================================== *)
(** * Implementation. *)

(* We introduce deep handlers as a derived construct of [eff_lang]. A deep
   handler is expressed as a recursive shallow handler that wraps itself
   over the captured continuation. *)

Definition deep_try_with : val := (
  rec: "deep" "tk" "h" "r" :=
    TryWith ("tk" #())
      (* Effect: *) (λ: "v" "k",
        "h" "v" (λ: "w", "deep" (λ: <>, "k" "w") "h" "r"))
      (* Return: *) "r"
)%V.
Arguments deep_try_with : simpl never.

Definition DeepTryWith' (e : expr) (h r : val) : expr := (

  let: "tk" := λ: <>, e in (* Introduce [tk] before [deep], because [e] is
                               an expression, so [e] might have free
                               occurrences of [deep]. *)
  deep_try_with "tk" h r

)%E.

Notation DeepTryWith e h r :=
  (App (App (App deep_try_with (Lam BAnon e)) h) r) (only parsing).

Notation DeepTryWithV e h r :=
  (App (App (App deep_try_with (LamV BAnon e)) h) r) (only parsing).

Notation "'deep-try:' e 'with' 'effect' h | 'return' r 'end'" :=
  (DeepTryWith e h r)
  (e, h, r at level 200, only parsing) : expr_scope.


(* ========================================================================== *)
(** * Deep-Handler Judgment. *)

(* To specify deep handlers, and thereby state their reasoning principles,
   we introduce the _deep-handler judgment_, an assertion comprising the
   specification of both return and effect branches. The deep-handler
   judgment is a recursive definition, which fact reflects the recursive
   behavior of deep handlers: to reason about the resumption of the
   continuation, one must reason about the new handler instance that
   is consequently installed. *)

Section deep_handler_judgment.
  Context `{!heapGS Σ}.

  (* ------------------------------------------------------------------------ *)
  (** Definition. *)

  Notation deep_handler_type :=
    (coPset -d>
       iEffO (Σ:=Σ) -d> iEffO (Σ:=Σ) -d> (val -d> iPropO Σ) -d>
         expr -d> expr -d>
           iEffO (Σ:=Σ) -d> iEffO (Σ:=Σ) -d> (val -d> iPropO Σ) -d> iPropO Σ)
    (only parsing).

  Definition deep_handler_pre : deep_handler_type → deep_handler_type :=
    (λ deep_handler E Ψ1 Ψ2 Φ h r Ψ1' Ψ2' Φ',

      (* Correctness of the return branch. *)
      (∀ (y : val), Φ y -∗ EWP r y @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}) ∧

      (* Correctness of the effect branch -- one-shot case. *)
      (∀ (v k : val),
         iEff_car (upcl OS Ψ1) v (λ w, ∀ Ψ1'' Ψ2'' Φ'',
           ▷ deep_handler E Ψ1 Ψ2 Φ h r Ψ1'' Ψ2'' Φ'' -∗
             EWP k w @ E <| Ψ1'' |> {| Ψ2'' |} {{ Φ'' }}) -∗
           EWP h v k @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}) ∧

      (* Correctness of the effect branch -- multi-shot case. *)
      (∀ (v k : val),
         iEff_car (upcl MS Ψ2) v (λ w, ∀ Ψ1'' Ψ2'' Φ'',
           ▷ deep_handler E Ψ1 Ψ2 Φ h r Ψ1'' Ψ2'' Φ'' -∗
             EWP k w @ E <| Ψ1'' |> {| Ψ2'' |} {{ Φ'' }}) -∗
           EWP h v k @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }})

    )%I.

  Local Instance deep_handler_pre_contractive : Contractive deep_handler_pre.
  Proof.
    rewrite /deep_handler_pre => n deep deep' Hne E Ψ1 Ψ2 Φ h r Ψ1' Ψ2' Φ'.
    repeat (f_contractive || f_equiv). intros ?; simpl.
    repeat (f_contractive || f_equiv). apply Hne.
    repeat (f_contractive || f_equiv). intros ?; simpl.
    repeat (f_contractive || f_equiv). apply Hne.
  Qed.
  Definition deep_handler_def := fixpoint deep_handler_pre.
  Definition deep_handler_aux : seal deep_handler_def. Proof. by eexists. Qed.
  Definition deep_handler := deep_handler_aux.(unseal).
  Definition deep_handler_eq : deep_handler = deep_handler_def
    := deep_handler_aux.(seal_eq).
  Arguments deep_handler _ _%ieff _%ieff _%I _%V _%V _%ieff _%ieff _%I.

  Global Lemma deep_handler_unfold E Ψ1 Ψ2 Φ h r Ψ1' Ψ2' Φ' :
    deep_handler E Ψ1 Ψ2 Φ h r Ψ1' Ψ2' Φ' ⊣⊢
      deep_handler_pre deep_handler E Ψ1 Ψ2 Φ h r Ψ1' Ψ2' Φ'.
  Proof.
    rewrite deep_handler_eq /deep_handler_def.
    by apply (fixpoint_unfold deep_handler_pre).
  Qed.


  (* ------------------------------------------------------------------------ *)
  (** Non-expansiveness. *)

  Global Instance deep_handler_ne E n:
    Proper
      ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==>
         (dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n))
    (deep_handler E).
  Proof.
    induction (lt_wf n) as [n _ IH]=>
      Ψ11  Ψ12  HΨ1  Ψ21  Ψ22  HΨ2  Φ1  Φ2  HΦ ??-> ??->
      Ψ11' Ψ12' HΨ1' Ψ21' Ψ22' HΨ2' Φ1' Φ2' HΦ'.
    rewrite !deep_handler_unfold /deep_handler_pre.
    repeat (apply iEff_car_ne||apply upcl_ne||apply ewp_ne||f_contractive||f_equiv);
    try done; try (eapply dist_le; eauto with lia).
    intros ?. do 3 (f_equiv=>?). f_equiv; f_contractive;
    apply IH; try lia; eapply dist_le; eauto with lia.
    intros ?. do 3 (f_equiv=>?). f_equiv; f_contractive;
    apply IH; try lia; eapply dist_le; eauto with lia.
  Qed.
  Global Instance deep_handler_proper E :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==>
              (≡) ==> (≡) ==> (≡) ==> (≡)) (deep_handler E).
  Proof. repeat intros ?. apply equiv_dist=>n.
         by apply deep_handler_ne; apply equiv_dist.
  Qed.

End deep_handler_judgment.


(* ========================================================================== *)
(** * Reasoning Rule for Deep Handlers. *)

Lemma ewp_deep_try_with `{!heapGS Σ} E Ψ1 Ψ2 Φ (h r : val) Ψ1' Ψ2' Φ' e :
  EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
    deep_handler E Ψ1 Ψ2 Φ h r Ψ1' Ψ2' Φ' -∗
      EWP DeepTryWithV e h r @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}.
Proof.
  iIntros "He Hhandler". unfold deep_try_with.
  ewp_pure_steps.
  iLöb as "IH" forall (Ψ1 Ψ2 Φ Ψ1' Ψ2' Φ' e).
  rewrite deep_handler_unfold.
  ewp_pure_steps.
  iApply (ewp_try_with with "[He] [Hhandler]");[|iSplit; [|iSplit]].
  - ewp_pure_steps. by iApply "He".
  - iIntros (y) "Hy". ewp_pure_steps. by iApply "Hhandler".
  - iIntros (v k) "Hk". ewp_pure_steps.
    iDestruct "Hhandler" as "(_&Hh&_)". iApply "Hh".
    iApply (@monotonic_prot _ (upcl OS Ψ1) with "[] Hk").
    iIntros (w) "Hk". iIntros (Ψ1'' Ψ2'' Φ'') "Hdeep".
    ewp_pure_steps. iApply ("IH" with "[Hk] Hdeep").
    by ewp_pure_steps.
  - iIntros (v k) "Hk". ewp_pure_steps.
    iDestruct "Hhandler" as "(_&_&Hh)". iApply "Hh".
    iApply (@pers_monotonic_prot _ (upcl MS Ψ2) with "[] Hk").
    iIntros "!#" (w) "Hk". iIntros (Ψ1'' Ψ2'' Φ'') "Hdeep".
    ewp_pure_steps. iApply ("IH" with "[Hk] Hdeep").
    by ewp_pure_steps.
Qed.
