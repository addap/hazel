From stdpp               Require Import list.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation weakestpre.

Class QueueLib Σ `{!irisG eff_lang Σ} := {
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

  queue_push_spec E q I n v :
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
