From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth gset gmap agree csum frac excl.
From iris.base_logic Require Import invariants.
From iris.base_logic.lib Require Import iprop wsat saved_prop.
From program_logic Require Import reasoning_rules.
From case_studies Require Import list_lib .

(* An axiomatization of CQS *)
Section cqs.
Context `{!heapGS Σ, !ListLib Σ}.

Variable R : iProp Σ.

Definition is_waker (P: val -> iProp Σ) (k : val): iProp Σ := ∀ v, P v -∗ EWP (k v) {{_, True}}.
Definition V' v := (⌜ v = #() ⌝ ∗ R)%I.

Parameter cqs_new     : val.
Parameter cqs_suspend    : val.
Parameter cqs_resume_all : val.
Parameter cqs_try_cancel     : val.

(* put the suspend proposition into the queue *)
Parameter is_thread_queue :
  val -> iProp Σ.
Parameter thread_queue_state :
  nat -> iProp Σ.
Parameter resume_all_permit :
  iProp Σ.
Parameter is_thread_queue_suspend_result :
  gname -> val -> val -> iProp Σ.
Parameter suspension_permit :
  iProp Σ.

Parameter is_thread_queue_Persistent_proof : ∀ q,
  Persistent (is_thread_queue q).
Parameter thread_queue_state_timeless_proof : ∀ n,
  Timeless (thread_queue_state n).
Parameter resume_all_permit_timeless_proof : 
  Timeless (resume_all_permit).

Parameter thread_queue_append': ∀ n q E',
  is_thread_queue q -∗
  ▷ thread_queue_state n ={E'}=∗
  thread_queue_state (S n) ∗ suspension_permit .
    
Parameter newThreadQueue_spec:
  ⊢ EWP cqs_new #()
  {{ q, is_thread_queue q 
      ∗ thread_queue_state 0 ∗ resume_all_permit }}.
        
(* todo use parameters correctly and make V'/R also a parameter. *)
Parameter cqs_suspend_spec: ∀ q k ,
      is_thread_queue q ∗ 
  (* a generic permit to call suspend *)
      suspension_permit ∗ 
  (* the WP of the closure k so that we can create a callback. *)
      is_waker V' k
  ⊢
    EWP cqs_suspend q k
  {{ v, ⌜v = NONEV⌝ ∨
                ∃ γk v', ⌜v = SOMEV v'⌝ ∗
                         is_thread_queue_suspend_result γk v' k }}.

Parameter cqs_try_cancel_spec: ∀ q γk r k,
  (* the invariant about the state of CQS. *)
      is_thread_queue q ∗ 
      is_thread_queue_suspend_result γk r k
  ⊢
    EWP cqs_try_cancel r
  {{ v, ∃ (b: bool), ⌜ v = #b ⌝ ∗ if b then 
                  (* is_waker gives us the WP for executing k *)
                  is_waker V' k 
                  (* if cancellation fails we don't know anything (on the metalevel we know that another thread will eventually call k, but we don't have this linearity in the Iris proof yet). *)
                  else True }}.

Parameter cqs_resume_all_spec: ∀ q n,
    is_thread_queue q ∗
    □ ▷ R ∗
    resume_all_permit ∗
    thread_queue_state n
  ⊢
    EWP cqs_resume_all q
    {{ _, True }}.

Global Instance is_cqs_Persistent q:
  Persistent (is_thread_queue q).
Proof.
  apply is_thread_queue_Persistent_proof.
Qed.

Global Instance thread_queue_state_Timeless n:
  Timeless (thread_queue_state n).
Proof.
  apply thread_queue_state_timeless_proof.
Qed.

Global Instance resume_all_permit_Timeless:
  Timeless (resume_all_permit).
Proof.
  apply resume_all_permit_timeless_proof.
Qed.

End cqs.

