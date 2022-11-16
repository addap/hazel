(* queue_lib.v *)

(* This file introduces an API for manipulating queues. *)

From stdpp Require Import list.
From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
From program_logic Require Import reasoning_rules.
From case_studies Require Import list_lib.


(* ========================================================================== *)
(** * Queue Interface. *)

Class QueueLib Σ `{!irisGS eff_lang Σ} := {
  queue_create : val;
  queue_push   : val;
  queue_pop    : val;
  queue_empty  : val;

  is_queue :
    val -d> (val -d> iPropO Σ) -d> natO -d> iPropO Σ;

  is_queue_ne q n :
    Proper ((dist n) ==> (dist n) ==> (dist n)) (is_queue q);

  queue_create_spec E Ψ1 Ψ2 :
    ⊢ EWP queue_create #() @ E <| Ψ1 |> {| Ψ2 |} {{ q,
        ∀ I, is_queue q I 0%nat }};

  queue_push_spec E Ψ1 Ψ2 q I (n : nat) v :
    is_queue q I n -∗
      I v -∗
        EWP queue_push q v @ E <| Ψ1 |> {| Ψ2 |} {{ _,
          is_queue q I (S n) }};

  queue_pop_spec E Ψ1 Ψ2 q I n :
    is_queue q I (S n) -∗
      EWP queue_pop q @ E <| Ψ1 |> {| Ψ2 |} {{ v,
        is_queue q I n ∗ I v }};

  queue_empty_spec E Ψ1 Ψ2 q I n :
    is_queue q I n -∗
      EWP queue_empty q @ E <| Ψ1 |> {| Ψ2 |} {{ v,
        is_queue q I n ∗
        match n with
        | 0%nat =>
            ⌜ v = #true  ⌝
        | S n =>
            ⌜ v = #false ⌝
        end
      }};
}.

Global Instance is_queue_proper `{QueueLib} q :
  Proper ((≡) ==> (≡) ==> (≡)) (is_queue q).
Proof.
  intros ??????. apply equiv_dist=>n. apply is_queue_ne; by apply equiv_dist.
Qed.


(* ========================================================================== *)
(** * Model. *)

Section QueueLibModel.
  Context `{!heapGS Σ}.

  (* ------------------------------------------------------------------------ *)
  (** Implementation. *)

  (* Representation Predicate. *)
  Definition is_queue' : val -d> (val -d> iPropO Σ) -d> natO -d> iPropO Σ :=
    λ q I n,
      (∃ (l : loc) (us : list val),
         ⌜ q = #l ⌝ ∗ l ↦ (list_encoding' us) ∗
         ⌜ length us = n  ⌝ ∗ [∗ list] u ∈ us, I u)%I.

  (* Non-expansiveness. *)
  Instance is_queue_ne' q n :
    Proper ((dist n) ==> (dist n) ==> (dist n)) (is_queue' q).
  Proof. solve_proper. Qed.

  (* Queue Operations. *)
  Definition queue_create' : val := (λ: <>, ref (list_encoding' []))%V.
  Definition queue_push': val := (λ: "q" "v",
    "q" <- (list_cons' "v" (Load "q")))%V.
  Definition queue_pop' : val := (λ: "q",
    match: Load "q" with
      InjL <>  =>
        #()
    | InjR "args" =>
        let: "u"  := Fst "args" in
        let: "us" := Snd "args" in
        "q" <- "us";; "u"
    end
  )%V.
  Definition queue_empty' : val := (λ: "q",
    match: (Load "q") with
      InjL <> =>
        #true
    | InjR <> =>
        #false
    end
  )%V.


  (* ------------------------------------------------------------------------ *)
  (** Verification. *)

  Lemma queue_create_spec' E Ψ1 Ψ2 :
    ⊢ EWP queue_create' #() @ E <| Ψ1 |> {| Ψ2 |} {{ q,
        ∀ I, is_queue' q I 0%nat }}.
  Proof.
    unfold queue_create'. ewp_pure_steps.
    iApply ewp_alloc. iIntros "!>" (q) "Hq".
    iModIntro. iIntros (I). iExists q, []. by eauto with iFrame.
  Qed.

  Lemma queue_push_spec' E Ψ1 Ψ2 q I (n : nat) v :
    is_queue' q I n -∗
      I v -∗
        EWP queue_push' q v @ E <| Ψ1 |> {| Ψ2 |} {{ _,
          is_queue' q I (S n) }}.
  Proof.
    iIntros "[%l [%us (-> & Hl & % & Hinv)]] HI".
    unfold queue_push'. ewp_pure_steps.
    ewp_bind_rule.
    iApply (ewp_load with "Hl"). iIntros "!> Hl !>". simpl.
    unfold list_cons'. ewp_pure_steps.
    iApply (ewp_store with "Hl").
    iIntros "!> Hl". iModIntro. iExists l, (v :: us). iFrame.
    iPureIntro. split; [done|]. simpl. by rewrite H.
  Qed.

  Lemma queue_pop_spec' E Ψ1 Ψ2 q I n :
    is_queue' q I (S n) -∗
      EWP queue_pop' q @ E <| Ψ1 |> {| Ψ2 |} {{ v,
        is_queue' q I n ∗ I v }}.
  Proof.
    iIntros "[%l [%us (-> & Hl & % & Hinv)]]".
    unfold queue_pop'. ewp_pure_steps.
    ewp_bind_rule.
    iApply (ewp_load with "Hl"). iIntros "!> Hl !>". simpl.
    case us as [|u us]; [done|]. iDestruct "Hinv" as "[HI Hinv]".
    simpl. ewp_pure_steps. ewp_bind_rule.
    iApply (ewp_store with "Hl"). iIntros "!> Hl !>".
    simpl. ewp_pure_steps.
    iFrame. iExists l, us. by eauto with iFrame.
  Qed.

  Lemma queue_empty_spec' E Ψ1 Ψ2 q I n :
    is_queue' q I n -∗
      EWP queue_empty' q @ E <| Ψ1 |> {| Ψ2 |} {{ v,
        is_queue' q I n ∗
        match n with
        | 0%nat =>
            ⌜ v = #true  ⌝
        | S n =>
            ⌜ v = #false ⌝
        end
      }}.
  Proof.
    iIntros "[%l [%us (-> & Hl & %Heq & Hinv)]]".
    unfold queue_empty'. ewp_pure_steps. ewp_bind_rule.
    iApply (ewp_load with "Hl"). iIntros "!> Hl !>". simpl.
    case us as [|u us].
    - simpl. ewp_pure_steps. rewrite <-Heq. simpl.
      iSplit; [|done]. iExists l, []. by auto.
    - case n as [|n]; [done|]. simpl. ewp_pure_steps.
      iSplit; [|done]. iExists l, (u :: us). by iFrame.
  Qed.


  (* ------------------------------------------------------------------------ *)
  (** Instantiating the [QueueLib] Interface. *)

  Program Instance QueueLib_valid : QueueLib Σ := {
    queue_create      := queue_create';
    queue_push        := queue_push';
    queue_pop         := queue_pop';
    queue_empty       := queue_empty';
    is_queue          := is_queue';  
    is_queue_ne       := is_queue_ne';
    queue_create_spec := queue_create_spec';
    queue_push_spec   := queue_push_spec';
    queue_pop_spec    := queue_pop_spec';
    queue_empty_spec  := queue_empty_spec';
  }.

End QueueLibModel.
