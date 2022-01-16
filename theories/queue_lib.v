From stdpp              Require Import list.
From iris.proofmode     Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
From hazel              Require Import notation weakestpre list_lib heap.

Class QueueLib Σ `{!irisGS eff_lang Σ} := {
  queue_create : val;
  queue_push   : val;
  queue_pop    : val;
  queue_empty  : val;

  is_queue :
    val -d> (val -d> iPropO Σ) -d> natO -d> iPropO Σ;

  is_queue_ne q n :
    Proper ((dist n) ==> (dist n) ==> (dist n)) (is_queue q);

  queue_create_spec E :
    ⊢ EWP queue_create #() @ E {{ q, ∀ I, is_queue q I 0%nat }};

  queue_push_spec E q I (n : nat) v :
    ▷ is_queue q I n -∗
      ▷ I v -∗
        EWP queue_push q v @ E {{ _, is_queue q I (S n) }};

  queue_pop_spec E q I n :
    ▷ is_queue q I (S n) -∗
      EWP queue_pop q @ E {{ v, is_queue q I n ∗ I v }};

  queue_empty_spec E q I n :
    ▷ is_queue q I n -∗
      EWP queue_empty q @ E {{ v, is_queue q I n ∗
                              match n with
                              | 0%nat => ⌜ v = #true  ⌝
                              | S n   => ⌜ v = #false ⌝
                              end
                            }};
}.

Global Instance is_queue_proper `{QueueLib} q :
  Proper ((≡) ==> (≡) ==> (≡)) (is_queue q).
Proof.
  intros ??????. apply equiv_dist=>n. apply is_queue_ne; by apply equiv_dist.
Qed.


Section QueueLibModel.
Context `{!heapG Σ}.

Definition is_queue' : val -d> (val -d> iPropO Σ) -d> natO -d> iPropO Σ := λ q I n,
  (∃ l us, ⌜ q = #(l : loc) ⌝ ∗ l ↦ (list_encoding' us) ∗
           ⌜ length us = n  ⌝ ∗ [∗ list] u ∈ us, I u)%I.
Instance is_queue_ne' q n : Proper ((dist n) ==> (dist n) ==> (dist n)) (is_queue' q).
Proof. solve_proper. Qed.

Definition queue_create' : val := λ: <>, ref (list_encoding' []).
Definition queue_push'   : val := λ: "q" "v", "q" <- (list_cons' "v" (Load "q")).
Definition queue_pop'    : val := λ: "q",
  match: (Load "q") with InjL <>  => #() | InjR "p" => "q" <- (Snd "p");; Fst "p" end.
Definition queue_empty'  : val := λ: "q",
  match: (Load "q") with InjL <>  => #true | InjR <> => #false end.

Lemma queue_create_spec' E :
  ⊢ EWP queue_create' #() @ E {{ q, ∀ I, is_queue' q I 0%nat }}.
Proof.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_mono'. { by iApply ewp_alloc. }
  iIntros (q) "H". iDestruct "H" as (l) "[-> Hl]".
  iModIntro. iIntros (I). iExists l, []. by eauto with iFrame.
Qed.

Lemma queue_push_spec' E q I (n : nat) v :
  ▷ is_queue' q I n -∗
    ▷ I v -∗
      EWP queue_push' q v @ E {{ _, is_queue' q I (S n) }}.
Proof.
  iIntros "Hq HI".
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step'. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step.  apply pure_prim_step_rec.
  iApply ewp_value.
  iApply ewp_pure_step.  apply pure_prim_step_beta. simpl.
  iNext. iDestruct "Hq" as (l us) "(-> & Hl & % & Hinv)".
  iApply (Ectxi_ewp_bind (StoreRCtx _)). done.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (ewp_mono' with "[Hl]"). { by iApply (ewp_load with "Hl"). }
  iIntros (w) "[-> Hl]". iModIntro. simpl.
  iApply ewp_mono'. { by iApply (list_cons_spec' _ _ _ us). }
  iIntros (w) "->". iModIntro. simpl.
  iApply (ewp_mono' with "[Hl]"). { by iApply (ewp_store with "Hl"). }
  iIntros (_) "Hl". iModIntro. iExists l, (v :: us). iFrame.
  iPureIntro. split; [done|]. simpl. by rewrite H.
Qed.

Lemma queue_pop_spec' E q I n :
  ▷ is_queue' q I (S n) -∗
    EWP queue_pop' q @ E {{ v, is_queue' q I n ∗ I v }}.
Proof.
  iIntros "Hq".
  iApply ewp_pure_step'. apply pure_prim_step_beta. simpl.
  iNext. iDestruct "Hq" as (l us) "(-> & Hl & % & Hinv)".
  case us as [|u us]; [done|]. iDestruct "Hinv" as "[HI Hinv]".
  iApply (Ectxi_ewp_bind (CaseCtx _ _)). done.
  iApply (ewp_mono' with "[Hl]"). { by iApply (ewp_load with "Hl"). }
  iIntros (w) "[-> Hl]". iModIntro. simpl.
  iApply ewp_pure_step. apply pure_prim_step_case_InjR.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx   _)). done.
  iApply (Ectxi_ewp_bind (StoreRCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_Snd.
  iApply ewp_value. simpl.
  iApply (ewp_mono' with "[Hl]"). { by iApply (ewp_store with "Hl"). }
  iIntros (w) "Hl". iModIntro.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_Fst. iApply ewp_value.
  iFrame. iExists l, us. by eauto with iFrame.
Qed.

Lemma queue_empty_spec' E q I n :
  ▷ is_queue' q I n -∗
    EWP queue_empty' q @ E {{ v, is_queue' q I n ∗
                             match n with
                             | 0%nat => ⌜ v = #true  ⌝
                             | S n   => ⌜ v = #false ⌝
                             end
                           }}.
Proof.
  iIntros "Hq".
  iApply ewp_pure_step'. apply pure_prim_step_beta. simpl.
  iNext. iDestruct "Hq" as (l us) "(-> & Hl & % & Hinv)".
  iApply (Ectxi_ewp_bind (CaseCtx _ _)). done.
  iApply (ewp_mono' with "[Hl]"). { by iApply (ewp_load with "Hl"). }
  iIntros (w) "[-> Hl]". iModIntro. simpl.
  case us as [|u us].
  - iApply ewp_pure_step. apply pure_prim_step_case_InjL.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.  iApply ewp_value.
    iApply ewp_pure_step. apply pure_prim_step_beta. iApply ewp_value.
    rewrite <-H. simpl. iSplit; [|done]. iExists l, []. by auto.
  - case n as [|n]; [done|].
    iApply ewp_pure_step. apply pure_prim_step_case_InjR.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.  iApply ewp_value.
    iApply ewp_pure_step. apply pure_prim_step_beta. iApply ewp_value.
    iSplit; [|done]. iExists l, (u :: us). by iFrame.
Qed.

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
