From iris.base_logic.lib Require Import iprop.
From program_logic Require Import reasoning_rules.

Section concurrent_queue.
Context `{!heapGS Σ}.

Parameter queue_create : val.
Parameter queue_push   : val.
Parameter queue_pop    : val.

Parameter is_queue :
  val -d> (val -d> iPropO Σ) -d> iPropO Σ.
  
Parameter is_queue_ne_proof : ∀ (q: val) (n: nat),
  Proper ((dist n) ==> (dist n)) (is_queue q).

Parameter is_queue_proper_proof : ∀ (q: val),
  Proper ((≡) ==> (≡)) (is_queue q).

Parameter is_queue_Persistent_proof : ∀ (q: val) (I: val -> iProp Σ),
  Persistent (is_queue q I).

Parameter queue_create_spec : ∀ (Ψ1 Ψ2: iEff Σ),
  ⊢ EWP queue_create #() <| Ψ1 |> {| Ψ2 |} {{ q,
      ∀ I, is_queue q I }}.

Parameter queue_push_spec : ∀ (Ψ1 Ψ2: iEff Σ) (q: val) (I: val -> iProp Σ) v,
  is_queue q I -∗
    I v -∗
      EWP queue_push q v <| Ψ1 |> {| Ψ2 |} {{ _, True }}.

Parameter queue_pop_spec : ∀ (Ψ1 Ψ2: iEff Σ) (q: val) (I: val -> iProp Σ),
  is_queue q I -∗
    EWP queue_pop q <| Ψ1 |> {| Ψ2 |} {{ y,
      ⌜ y = NONEV ⌝ ∨ 
      ∃ (v: val), ⌜ y = SOMEV v ⌝ ∗ I v }}.

Global Instance is_queue_ne q n:
  Proper ((dist n) ==> (dist n)) (is_queue q).
Proof.
  apply is_queue_ne_proof.
Qed.

Global Instance is_queue_proper q :
  Proper ((≡) ==> (≡)) (is_queue q).
Proof.
  apply is_queue_proper_proof.
Qed.

Global Instance is_queue_Persistent q I:
  Persistent (is_queue q I).
Proof.
  apply is_queue_Persistent_proof.
Qed.

End concurrent_queue.