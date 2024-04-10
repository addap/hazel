From iris.base_logic.lib Require Import iprop invariants.
From program_logic Require Import reasoning_rules.

Section concurrent_queue.
Context `{!heapGS Σ}.
Context (N : namespace).

Parameter queue_change_state : val.
Parameter queue_create : val.
Parameter queue_push   : val.
Parameter queue_pop    : val.

Parameter is_queue :
  valO -d> (valO -d> iPropO Σ) -d> iPropO Σ.
Parameter is_queue_reader :
  valO -d> (valO -d> iPropO Σ) -d> iPropO Σ.

Parameter push_permission :
  gnameO -d> iPropO Σ -d> iPropO Σ.
Parameter fulfill_permission :
  iPropO Σ -d> iPropO Σ.

Parameter is_queue_ne_proof : ∀ (q: val) (n: nat),
  Proper ((dist n) ==> (dist n)) (is_queue q).

Parameter is_queue_Persistent_proof : ∀ (q : val) (I : val -> iProp Σ),
  Persistent (is_queue q I).

Parameter is_queue_reader_ne_proof : ∀ (q: val) (n: nat),
  Proper ((dist n) ==> (dist n)) (is_queue_reader q).

Parameter queue_register_push : ∀ (Q : iProp Σ) (q : val) (I: val -> iProp Σ),
  ⊢ is_queue_reader q I -∗
      EWP queue_change_state #() {{ _, 
        is_queue q I ∗
        fulfill_permission Q ∗
        ∃ γ, push_permission γ Q }}.

Parameter queue_fulfill_Q : ∀ (Q : iProp Σ) (q : val) (I : val -> iProp Σ),
  ⊢ is_queue q I -∗
    fulfill_permission Q -∗
    □ Q -∗
      EWP queue_change_state #() {{ _, is_queue_reader q I }}.

Parameter queue_create_spec :
  ⊢ EWP queue_create #() {{ q, ∀ (I : val -> iProp Σ),
      |={⊤}=> is_queue_reader q I }}.

Parameter queue_push_spec : ∀ (γ : gname) (Q : iProp Σ) (I : val -> iProp Σ) (q : val) v,
  ⊢ is_queue q I -∗ 
    push_permission γ Q -∗
    ▷ (Q -∗ I v) -∗
      EWP queue_push q v {{ _, True }}.

Parameter queue_pop_spec : ∀ (I: val -> iProp Σ) (q: val),
  is_queue_reader q I -∗
    EWP queue_pop q {{ ov, is_queue_reader q I ∗ (
        ⌜ ov = NONEV ⌝ 
      ∨ ∃ (v: val), ⌜ ov = SOMEV v ⌝ ∗ I v 
    ) }}.

Global Instance is_queue_ne q n:
  Proper ((dist n) ==> (dist n)) (is_queue q).
Proof.
  apply is_queue_ne_proof.
Qed.

Global Instance is_queue_Persistent q I :
  Persistent (is_queue q I).
Proof.
  apply is_queue_Persistent_proof.
Qed.

Global Instance is_queue_reader_ne q n:
  Proper ((dist n) ==> (dist n)) (is_queue_reader q).
Proof.
  apply is_queue_reader_ne_proof.
Qed.

End concurrent_queue.