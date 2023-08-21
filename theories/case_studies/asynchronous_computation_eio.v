(* asynchronous_computation.v *)

(* The ability offered by effect handlers (or any other interface for
   programming with continuations) to suspend a computation and reify it as a
   first-class value can be used to implement _asynchronous computation_: the
   concurrent completion of multiple _tasks_ under the condition that progress
   can be made by at most one task at a time.

   Tasks are represented by thunks, which we call _fibers_. During its
   completion, a fiber can "spawn" new tasks, or "await" for the completion of
   other tasks. The responsible for (1) keeping track of the unfinished tasks,
   (2) resuming tasks when possible, and (3) making sure that at most one task
   makes progress at a time is the _scheduler_.

   In this case study, we implement and verify such a scheduler. Our
   implementation can be seen as a simplified version of Dolan et al.'s
   scheduler from the paper "Concurrent System Programming with Effect
   Handlers" (TFP'17) -- our implementation ignores exceptions: we assume that
   the only form of control effect are calls to the operations [await] and
   [async]; in particular, we assume that fibers do not raise exceptions. *)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth gset gmap agree csum frac excl.
From iris.base_logic Require Import invariants.
From iris.base_logic.lib Require Import iprop wsat.
From program_logic Require Import reasoning_rules.
From case_studies Require Import list_lib .


(* ========================================================================== *)
(** * Implementation of the Scheduler. *)

Notation Fork e := (InjL e) (only parsing).
Notation Suspend f := (InjR f) (only parsing).

Notation Fork' e := (InjLV e) (only parsing).
Notation Suspend' f := (InjRV f) (only parsing).

Notation Done y := (InjL y) (only parsing).
Notation Waiting ks := (InjR ks) (only parsing).

Notation Done' y := (InjLV y) (only parsing).
Notation Waiting' ks := (InjRV ks) (only parsing).

Notation ONone := (InjL #()) (only parsing).
Notation OSome v := (InjR v) (only parsing).
Notation ONone' := (InjLV #()) (only parsing).
Notation OSome' v := (InjRV v) (only parsing).

(* Section partial_apply_spec.
  Context `{!heapGS Σ}.

  Axiom A: iProp Σ.
  Axiom A_Persistent_proof : Persistent A.
  Instance A_Persistent: Persistent A.
  Proof.
    apply A_Persistent_proof.
  Qed.
  
  Axiom f: val.
  (* the function f needs has some persistent precondition A. *)
  Axiom ewp_f : 
    A ⊢ EWP (f #()) <| ⊥ |> {{_, True}}.

  (* now we have a function that builds a closure around f and which has access to A.
     Can we return a closure without a precodition? *)
  Definition build_closure : val := (λ: <> <>, f #())%V.
  
  Lemma ewp_build_closure :
    A ⊢ EWP (build_closure #()) {{v, EWP (v #()) {{_, True}} }}.
  Proof.
    iIntros "#a". rewrite /build_closure. ewp_pure_steps.
    by iApply ewp_f.
  Qed. 
End partial_apply_spec. *)

Section atomics.
  Definition sub_redexes_are_values (e : expr) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = [].

  Definition head_atomic (a : atomicity) (e : expr) : Prop :=
    ∀ σ e' σ' ,
      head_step e σ e' σ' →
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  Lemma ectx_language_atomic a e :
    head_atomic a e → sub_redexes_are_values e → Atomic a e.
  Proof.
    intros Hatomic_step Hatomic_fill σ e' κ σ' efs H.
    unfold language.prim_step in H. simpl in H. unfold prim_step' in H.
    destruct κ, efs; try by destruct H.
    destruct H as [K e1' e2' -> -> Hstep].
    assert (K = []) as -> by eauto 10 using val_head_stuck.
    simpl fill. simpl fill in Hatomic_step.
    eapply Hatomic_step. by apply Hstep.
  Qed.

  Lemma fill_val2 (k : ectx) (e: expr) :
    is_Some (to_val (fill k e)) → is_Some (to_val e).
  Proof.
    intros (v & [-> ->]%fill_val).
    simpl. done.
  Qed.

  (* Lemma ectxi_language_sub_redexes_are_values e :
    (∀ Ki e', e = fill Ki e' → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
    intros []%eq_None_not_Some. eapply fill_val2, Hsub. by rewrite /= fill_app.
  Qed. *)

  Lemma fill_no_value (k: ectx) (e: expr) (v: val) :
    to_val e = None → fill k e = v → False.
  Proof.
    intros Hv Hfill.
    specialize (fill_not_val k _ Hv) as Hfill'.
    rewrite Hfill in Hfill'.
    simpl in Hfill'. discriminate Hfill'.
  Qed.

  Global Instance store_atomic v1 v2 : Atomic StronglyAtomic (Store (Val v1) (Val v2)).
  Proof. 
    apply ectx_language_atomic.
    - inversion 1. naive_solver. 
    - unfold sub_redexes_are_values.
      intros [] **. naive_solver.
      exfalso.
      simpl in H. destruct f; simpl in H; try discriminate H.
      inversion H. apply (fill_no_value l e' v1 H0). symmetry. apply H2.
      inversion H. apply (fill_no_value l e' v2 H0). symmetry. apply H3.
  Qed.

  Global Instance load_atomic v : Atomic StronglyAtomic (Load (Val v)).
  Proof.
    apply ectx_language_atomic.
    - inversion 1. naive_solver.
    - unfold sub_redexes_are_values.
      intros [] **. naive_solver.
      exfalso.
      simpl in H. destruct f; simpl in H; try discriminate H.
      inversion H. apply (fill_no_value l e' v H0). symmetry. apply H2.
  Qed.
  
  Global Instance alloc_atomic v : Atomic StronglyAtomic (Alloc (Val v)).
  Proof.
    apply ectx_language_atomic.
    - inversion 1. naive_solver.
    - unfold sub_redexes_are_values.
      intros [] **. naive_solver.
      exfalso.
      simpl in H. destruct f; simpl in H; try discriminate H.
      inversion H. apply (fill_no_value l e' v H0). symmetry. apply H2.
  Qed.
End atomics. 

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
        ⌜ y = ONone' ⌝ ∨ 
        ∃ (v: val), ⌜ y = OSome' v ⌝ ∗ I v }}.

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

(* An axiomatization of CQS *)
Section cqs.
  Context `{!heapGS Σ, !ListLib Σ}.

  Parameter cqs_create     : val.
  Parameter cqs_suspend    : val.
  Parameter cqs_resume_all : val.
  Parameter cqs_cancel     : val.

  (* put the suspend proposition into the queue *)
  Parameter is_cqs :
    val -d> (val -d> iPropO Σ) -d> iPropO Σ.

  Parameter is_cqs_request : 
    val -d> val -d> iPropO Σ.
    
  Parameter is_cqs_ne_proof : ∀ (q: val) (n: nat),
    Proper ((dist n) ==> (dist n)) (is_cqs q).
  
  Parameter is_cqs_proper_proof : ∀ (q: val),
    Proper ((≡) ==> (≡)) (is_cqs q).
  
  Parameter is_cqs_Persistent_proof : ∀ (q: val) (I: val -> iProp Σ),
    Persistent (is_cqs q I).

  Parameter cqs_create_spec : ∀ (Ψ1 Ψ2: iEff Σ),
    ⊢ EWP cqs_create #() <| Ψ1 |> {| Ψ2 |} {{ q,
        ∀ I, is_cqs q I }}.
  
  Parameter cqs_suspend_spec : ∀ (Ψ1 Ψ2: iEff Σ) (q: val) (I: val -> iProp Σ) v,
    is_cqs q I -∗ I v -∗
      EWP cqs_suspend q v <| Ψ1 |> {| Ψ2 |} {{ r, is_cqs_request r v }}.
          
  (* a.d. cancel does not really give you back v, but it should give you back (I v) for the v that you originally suspended. 
     TODO how do I do that? *)
  Parameter cqs_cancel_spec : ∀ (Ψ1 Ψ2: iEff Σ) (q: val) (I: val -> iProp Σ) v r,
    is_cqs q I -∗ is_cqs_request r v -∗ 
      EWP cqs_cancel q r <| Ψ1 |> {| Ψ2 |} {{ _, I v }}.

  Parameter cqs_resume_all_spec : ∀ (Ψ1 Ψ2: iEff Σ) (q: val) (I: val -> iProp Σ),
    is_cqs q I -∗
      EWP cqs_resume_all q <| Ψ1 |> {| Ψ2 |} {{ l, ∃ ks, (is_list l ks ∗ [∗ list] k ∈ ks, I k)%I }}.

  Global Instance is_cqs_ne q n:
    Proper ((dist n) ==> (dist n)) (is_cqs q).
  Proof.
    apply is_cqs_ne_proof.
  Qed.

  Global Instance is_cqs_proper q :
    Proper ((≡) ==> (≡)) (is_cqs q).
  Proof.
    apply is_cqs_proper_proof.
  Qed.

  Global Instance is_cqs_Persistent q I:
    Persistent (is_cqs q I).
  Proof.
    apply is_cqs_Persistent_proof.
  Qed.
End cqs.

Section implementation.
  Context `{!heapGS Σ, !ListLib Σ}.

  (* a.d. TODO, promises should contain a CQS instead of a list.
  Then we copy take the persistent isCQS out of the invariant, pass it to the callback in await and use it there. *)
  Definition new_promise : val := (λ: <>,
    ref (Waiting (cqs_create #()))
  )%V.
  Definition fork : val := (λ: "f", do: (Fork "f"))%V.
  Definition suspend : val := (λ: "f", do: (Suspend "f"))%V.
  Definition next : val := (λ: "q",
    match: queue_pop "q" with
      (* Empty *) InjL <> => #()
    | (* Nonempty *) InjR "f" => "f" #()
    end)%V.

  Definition fork_wrap_f : val := (λ: "f" "p", (λ: <>, 
    let: "v" := "f" #() in
    match: Load "p" with
      (* Done: *) InjL <> =>
        #() #() (* Unreachable! *)
    | (* Waiting: *) InjR "enqs" =>
        let: "resumed" := cqs_resume_all "enqs" in
        (* a.d. TODO interestingly we need to first set p so that we can change the promise_state.
        Iirc in Eio it was the other way around. Check if that is sound. *)
        "p" <- Done "v";;
        list_iter (λ: "enqueue", "enqueue" #()) "resumed"
    end))%V.

  (* fork a new fiber "f" and return a promise to get the result. *)
  Definition fork_promise : val := (λ: "f", 
    let: "p" := new_promise #() in
    let: "wrapped_f" := fork_wrap_f "f" "p" in
    fork "wrapped_f";;
    "p")%V.
   
  Definition await_callback : val := (λ: "p" "ks", (λ: "enqueue", 
    (* We do the same as Eio and suspend in CQS and then check the state of the promise again. 
       Since we gave enqueue to the queue in suspend, if p is Done, we first need to cancel the reques to get the permission to
       call enqueue back. *)
    let: "req" := cqs_suspend "ks" "enqueue" in
    match: Load "p" with
        (* Done: *) InjL <>  => 
        cqs_cancel "ks" "req";;
        "enqueue" #()
    | (* Waiting: *) InjR "ks" => #()
    end
  ))%V.

  Definition await : val := (λ: "p",
    match: Load "p" with
      (* Done: *) InjL "v"  =>
        "v"
    | (* Waiting: *) InjR "ks" =>
        let: "callback" := await_callback "p" "ks" in 
        suspend "callback";;
        match: Load "p" with
          (* Now Done: *) InjL "v" =>
            "v"
        | (* Waiting: *) InjR <> =>
            #() #() (* unreachable *)
        end
    end
  )%V.

  Definition run : val := (λ: "main",
    let: "q" := queue_create #() in
    let: "fulfill" := rec: "fulfill" "e" :=
      deep-try: "e" #() with
        effect (λ: "request" "k",
          match: "request" with
            (* Fork: *) InjL "e" =>
              queue_push "q" (λ: <>, "k" #());;
              "fulfill" "e"
          | (* Suspend: *) InjR "f" =>
              (* a.d. probably the most complicated line 
              When you call enqueue with a value, you cause the continuation to be put back into the run_queue. 
              f can either put enqueue somewhere that causes it to be called later or just call it directly. *)
              let: "enqueue" := (λ: "v", queue_push "q" (λ: <>, "k" "v")) in
              "f" "enqueue";;
              next "q"
          end)
      | return (λ: <>, next "q")
      end
    in
    "fulfill" "main"
  )%V.

End implementation.



(* ========================================================================== *)
(** * Internal Logical Definitions. *)

(* -------------------------------------------------------------------------- *)
(** Cameras. *)

(* The verification relies on ghost cells of two kinds: either from the
   camera [M],

     M ≜ Auth ((Loc * GName) -fin-> Ag(Later(val -d> iProp)));

   or from the camera [T],

     T ≜ Excl Unit.

   One single global cell from [M] is used to associate a promise [p] to a
   predicate [Φ] describing the values with which this promise can be fulfilled.

   Multiple (dynamically allocated) cells from the camera [T] are used to
   simulate unique tokens. Every fiber carries such a token, which is allocated
   at the moment the fiber is spawned. The ownership of this token is
   transferred to the promise upon termination of the fiber. Because this token
   is unique, we can argue that the line carrying the comment "unreachable" is
   indeed unreachable: if a fiber cannot find its own promise fulfilled by
   another fiber, then its token has been duplicated, which situation is
   contradictory. *)
   
(* The assumption that certain cameras are available. *)
Class promiseGpreS Σ := {
  promise_mapG :> inG Σ
    (authR (gmapUR (loc * gname) (agreeR (laterO (val -d> (iPropO Σ))))));
  torchG :> inG Σ (csumR fracR (agreeR unitO));
}.
  
(* A concrete instance of [Σ] for which the assumption [promisesGS Σ] holds. *)
Definition promiseΣ := #[
  GFunctor (authRF
    (gmapURF (loc * gname) (agreeRF (laterOF (valO -d> idOF)))));
  GFunctor (csumR fracR (agreeR unitO))
].
  
(* The proof of the previous claim. *)
Instance subG_promiseΣ {Σ} : subG promiseΣ Σ → promiseGpreS Σ.
Proof. solve_inG. Qed.

Class promiseGS Σ := {
  promise_inG :> promiseGpreS Σ;
  promise_name : gname;
}.
  
(* -------------------------------------------------------------------------- *)
(** Predicates. *)

Section predicates.
  Context `{!heapGS Σ, !promiseGS Σ}.

  (* ------------------------------------------------------------------------ *)
  (* Definitions. *)

  (* torch γ ≜ own γ (Excl ())

     isPromise p Φ ≜
       ∃ γ, own promise_name (◯ {[(p,γ) := Φ]})

     isPromiseMap M ≜
       own promise_name (● M)

     promiseInv ≜
       ∃ M, promiseMap M ∗
         [∗ map] (p,γ) ↦ Φ ∈ M,
             (∃y, p ↦ Done y ∗ □ Φ y ∗ torch γ)
           ∨
             (∃l ks,
                p ↦ Waiting l ∗
                isList l ks   ∗
                [∗ list] k ∈ ks, ready q Φ k)

     ready q Φ k ≜
       ∀ y.
         □ Φ y -∗
           ▷ promiseInv -∗
             ▷ is_queue q (ready q (λ y. y = ())) -∗
               EWP (k y) <| ⊥ |> {{ _. True }}
  *)

  (* Unique token [γ]: a fiber holds possession of [torch γ] while running. *)
  Definition promise_state_whole γ := own γ (Cinl 1%Qp).
  Definition promise_state_waiting γ := own γ (Cinl (1/2)%Qp).
  Definition promise_state_waiting4 γ := own γ (Cinl (1/4)%Qp).
  Definition promise_state_done γ := own γ (Cinr (to_agree ())).

  (* Inject a predicate [Φ] into the camera [Ag(Next(val -d> iProp))]. *)
  Definition promise_unfold (Φ : val → iProp Σ) :
    agree (later (discrete_fun (λ (_ : val), iPropO Σ))) :=
    to_agree (Next (λ v, (Φ v))).

  Definition isMember p γ Φ :=
    own promise_name (◯ {[(p, γ) := promise_unfold Φ]}).

  Definition isPromise (p : loc) Φ := (
    ∃ γ, isMember p γ Φ
  )%I.

  Definition isPromiseMap (M : gmap (loc * gname) (val → iProp Σ)) :=
    own promise_name (● (promise_unfold <$> M : gmap _ _)).

  (* invariant stuff *)
  Definition promiseN : namespace := nroot .@ "promise".

  (* we can remove the ready & q from promiseInv because we keep all the queue handling inside the 
     effect handler. This makes it much easier since
     1. we don't need to parameterize the protocol with q
     2. it might now be easier to use in a multithreaded setting (might still need to put it in an invariant) 
     
     As for use in a multithreaded setting.
    promiseInv should be put into an actual invariant. But at the moment the means of accessing a promiseSt 
    seem to be overly conservative and only give you access to a ▷ promiseSt, which is pretty impractical for
    an invariant. The later seems to be necessary due to Φ (recursive occurence of iProp).
    It might be possible to separate out the □ Φ v so that lookup_promiseInv can return a part that is available
    immediately, and a (▷ □ Φ v) (and b/c ▷ and □ commutes, we can take a copy and use it after closing the invariant)
     *)
     
  Definition promise_cqs (enqs: val) (γ : gname) : iProp Σ :=
    (is_cqs enqs (λ enq, ∀ (v: val), 
            let P := (λ v, ⌜ v = #() ⌝ ∗ promise_state_done γ) in
            P v -∗
            (* a.d. can we remove the my_queue precondition by saying is_queue is persistent and "partially-applying" the specification? *)
            (* is_queue q (ready q (λ v, ⌜ v = #() ⌝)%I) -∗  *)
              EWP (App (Val enq) v)%I <| ⊥ |> {{_, True }} ))%I.
    
  Definition promiseInv_inner : iProp Σ := (
    ∃ M, isPromiseMap M ∗ 
      [∗ map] args ↦ Φ ∈ M, let '(p, γ) := args in
        ((* Fulfilled: *) ∃ y,
          (p ↦ Done' y ∗ promise_state_done γ) ∗ □ Φ y)
      ∨
        ((* Unfulfilled: *) ∃ enqs,
          p ↦ Waiting' enqs ∗
          promise_state_waiting γ ∗
          (* ks now does not contain a list of continuations but a list of enqueue functions. 
             Each of these functions will change the run queue (in the future they can change an arbitrary run queue)
             so we have is_queue as a precondition
          *)
          promise_cqs enqs γ)
  )%I.
    
  Definition promiseInv := inv promiseN promiseInv_inner.
  
  Global Instance promiseInv_Persistent : Persistent promiseInv.
  Proof. by apply _. Qed.

  (* by now ready is just a predicate on a function value f, that f is safe to execute under the assumption
     that promiseInv holds. When promiseInv becomes an actual invariant, then probably even this precondition
     goes away. *)
  Definition ready (k: val) : iProp Σ := (
    promiseInv -∗ EWP (k #()) {{ _, True }}
  )%I.

  Definition promiseSt p γ (Φ : val -d> iPropO Σ) : iProp Σ :=
    ((* Fulfilled: *) ∃ y,
       (p ↦ Done' y ∗ promise_state_done γ) ∗ □ Φ y)
  ∨
    ((* Unfulfilled: *) ∃ enqs,
      p ↦ Waiting' enqs ∗
      promise_state_waiting γ ∗
      promise_cqs enqs γ).

  Definition promiseSt_later p γ (Φ : val -d> iPropO Σ) : iProp Σ :=
    ((* Fulfilled: *) ∃ y,
       (p ↦ Done' y ∗ promise_state_done γ) ∗ ▷ □ Φ y)
  ∨
    ((* Unfulfilled: *) ∃ enqs,
      p ↦ Waiting' enqs ∗
      promise_state_waiting γ ∗
      promise_cqs enqs γ).

  (* ------------------------------------------------------------------------ *)
  (* Non-expansiveness. *)

  (* [ready]. *)
  Global Instance ready_ne n :
    Proper ((dist n) ==> (dist n)) ready.
  Proof.
    induction (lt_wf n) as [n _ IH]=>k k' ->.
    rewrite /ready.
    by repeat (f_contractive
           || f_equiv || apply IH 
           || case x1 as ()         || case x2 as ()
           || case y1 as (y11, y12) || case y2 as (y21, y22)
           || apply H0 || apply H1 ).
  Qed.
  Global Instance ready_proper : Proper ((≡) ==> (≡)) ready.
  Proof. intros ???. apply equiv_dist=>n.
         by apply ready_ne; apply equiv_dist.
  Qed.

  (* [promiseSt]. *)
  Global Instance promiseSt_ne n  p γ :
    Proper ((dist n) ==> (dist n)) (promiseSt  p γ).
  Proof. by solve_proper. Qed.
  Global Instance promiseSt_proper  p γ :
    Proper ((≡) ==> (≡)) (promiseSt  p γ).
  Proof. by solve_proper. Qed.


  (* ------------------------------------------------------------------------ *)
  (* Properties. *)

  (* Logical rules governing the predicate [torch]. *)
  Section promise_state.

    Global Instance promise_state_done_Persistent γ : Persistent (promise_state_done γ).
    Proof. by apply _. Qed.

    Lemma promise_state_create : ⊢ |==> ∃ γ, promise_state_whole γ.
    Proof. by iMod (own_alloc (Cinl 1%Qp)) as (γ) "Hps"; last iExists γ. Qed.

    Lemma promise_state_split γ :
      ⊢ promise_state_whole γ ==∗ promise_state_waiting γ ∗ promise_state_waiting γ.
    Proof.
      rewrite /promise_state_whole /promise_state_waiting.
      rewrite -own_op.
      iApply own_update.
      rewrite -Cinl_op.
      apply csum_update_l.
      rewrite frac_op.
      rewrite cmra_update_updateP.
      apply cmra_updateP_id. 
      apply Qp_half_half.
    Qed. 

    Lemma promise_state_split2 γ :
      ⊢ promise_state_waiting γ ==∗ promise_state_waiting4 γ ∗ promise_state_waiting4 γ.
    Proof.
      rewrite /promise_state_waiting /promise_state_waiting4.
      rewrite -own_op.
      iApply own_update.
      rewrite -Cinl_op.
      apply csum_update_l.
      rewrite frac_op.
      rewrite cmra_update_updateP.
      apply cmra_updateP_id. 
      apply Qp_quarter_quarter.
    Qed. 

    Lemma promise_state_join γ :
      ⊢ promise_state_waiting γ ∗ promise_state_waiting γ ==∗ promise_state_whole γ.
    Proof.
      rewrite /promise_state_whole /promise_state_waiting.
      rewrite -own_op.
      iApply own_update.
      rewrite -Cinl_op.
      apply csum_update_l.
      rewrite frac_op.
      rewrite cmra_update_updateP.
      apply cmra_updateP_id. 
      by rewrite Qp_half_half.
    Qed.

    Lemma promise_state_fulfill γ :
      ⊢ promise_state_whole γ ==∗ promise_state_done γ.
    Proof.
      iApply own_update.
      apply cmra_update_exclusive.
      apply Cinr_valid.
      done.
    Qed.
    
    Lemma promise_state_disjoint γ : (promise_state_waiting γ ∗ promise_state_done γ) -∗ False.
    Proof. 
      by rewrite /promise_state_waiting /promise_state_done -own_op own_valid csum_validI.
    Qed.

    Lemma promise_state_disjoint2 γ : (promise_state_waiting4 γ ∗ promise_state_done γ) -∗ False.
    Proof. 
      by rewrite /promise_state_waiting4 /promise_state_done -own_op own_valid csum_validI.
    Qed.
  End promise_state.

  (* Logical rules governing the predicate [ready]. *)
  Section ready.

  End ready.

  (* Logical rules governing the predicates [isPromiseMap], [isPromise], and
     [promiseInv]. *)
  Section promise_preds.

    (* Persistent predicates. *)
    Global Instance isMember_Persistent p γ Φ : Persistent (isMember p γ Φ).
    Proof. by apply _. Qed.
    Global Instance isPromise_Persistent p Φ : Persistent (isPromise p Φ).
    Proof. by apply _. Qed.

    Lemma update_promise_map M p γ Φ :
      M !! (p, γ) = None →
        isPromiseMap M ==∗
          isPromiseMap (<[(p,γ):=Φ]> M) ∗ isMember p γ Φ.
    Proof.
      intros Hlkp. unfold isPromiseMap. iIntros "HM".
      iMod (own_update with "HM") as "[HM HiP]".
      { apply (@auth_update_alloc (gmapUR _ _) (promise_unfold <$> M)).
        apply (alloc_singleton_local_update _ (p, γ) (promise_unfold Φ)).
        by rewrite /= lookup_fmap Hlkp. done. }
      iModIntro. iFrame. by rewrite fmap_insert.
    Qed.

    Lemma claim_membership M p γ Φ :
      isPromiseMap M ∗ isMember p γ Φ -∗ ∃ Φ',
        ⌜ M !! (p, γ) = Some Φ' ⌝ ∗ (promise_unfold Φ' ≡ promise_unfold Φ).
    Proof.
      rewrite /isPromiseMap /isMember.
      rewrite -own_op own_valid auth_both_validI /=.
      iIntros "[HM #HpM]". iDestruct "HM" as (M') "#HM".
      rewrite gmap_equivI gmap_validI.
      iSpecialize ("HM" $! (p, γ)). iSpecialize ("HpM" $! (p, γ)).
      rewrite lookup_fmap lookup_op lookup_singleton.
      rewrite option_equivI.
      case: (M  !! (p, γ))=> [Φ'|] /=; [|
      case: (M' !! (p, γ))=> [Φ'|] /=; by iExFalso].
      iExists Φ'. iSplit; first done.
      case: (M' !! (p, γ))=> [Ψ'|] //=.
      iRewrite "HM" in "HpM". rewrite option_validI agree_validI.
      iRewrite -"HpM" in "HM". by rewrite agree_idemp.
    Qed.

    Lemma promise_unfold_equiv (Φ' Φ : val → iProp Σ) :
      promise_unfold Φ' ≡ promise_unfold Φ -∗
        ▷ (∀ v, Φ' v ≡ Φ v : iProp Σ).
    Proof.
      rewrite /promise_unfold.
      rewrite agree_equivI. iIntros "Heq". iNext. iIntros (v).
      iDestruct (discrete_fun_equivI with "Heq") as "Heq".
      by iSpecialize ("Heq" $! v).
    Qed.

    Lemma promiseSt_non_duplicable p γ γ' Φ Φ' :
      promiseSt p γ Φ -∗ promiseSt p γ' Φ' -∗ False.
    Proof.
      assert (⊢ ∀ p γ Φ, promiseSt p γ Φ -∗ ∃ v, p ↦ v)%I as Haux.
      { by iIntros (???) "[[%v[(Hp & _) _]]|[%ks[Hp _]]]"; auto. }
      iIntros "Hp Hp'".
      iPoseProof (Haux with "Hp")  as "[%v  Hp]".
      iPoseProof (Haux with "Hp'") as "[%v' Hp']".
      by iDestruct (mapsto_ne with "Hp Hp'") as "%Hneq".
    Qed.

    Lemma promiseSt_proper' p γ Φ Φ' :
      (Φ ≡ Φ') -∗ promiseSt p γ Φ -∗ promiseSt p γ Φ'.
    Proof. by iIntros "HΦ Hp"; iRewrite -"HΦ". Qed.

    Lemma update_promiseInv_inner p γ Φ :
    (* a.d. probably need a later here *)
      promiseInv_inner ∗ promiseSt p γ Φ ==∗
        promiseInv_inner ∗ isMember p γ Φ.
    Proof.
      iIntros "[HpInv Hp]". rewrite /promiseInv_inner.
      iDestruct "HpInv" as (M) "[HM HInv]".
      (* remove the later from *)
      destruct (M !! (p, γ)) as [Ψ|] eqn:Hlkp.
      - rewrite (big_opM_delete _ _ _ _ Hlkp).
        iDestruct "HInv" as "[Hp' _]".
        by iDestruct (promiseSt_non_duplicable with "Hp Hp'") as "HFalse".
      - iMod (update_promise_map M p γ Φ Hlkp with "HM") as "[HM Hmem]".
        iModIntro. iFrame. iExists (<[(p, γ):=Φ]> M). iFrame.
        rewrite big_opM_insert; last done. by iFrame.
    Qed.

    Lemma promiseSt_promiseSt_later p γ Φ :
      promiseSt p γ Φ -∗ promiseSt_later p γ Φ.
    Proof.
      rewrite /promiseSt_later.
      iIntros "[[%y ((Hp&#Hps)&Hy)]|[%enqs (Hp&Hps&Hks)]]".
      iLeft. iExists y. by iFrame.
      iRight. iExists enqs. by iFrame.
    Qed.
    
    (* Global Instance isPromiseMap_timeless M : Timeless (isPromiseMap M).
    Proof. by apply _. *)
    
    Lemma lookup_promiseInv_inner p γ Φ :
      ▷ promiseInv_inner -∗ isMember p γ Φ -∗
        (▷ (promiseSt p γ Φ -∗ promiseInv_inner) ∗ promiseSt_later p γ Φ).
    Proof.
      (* iIntros "HpInv Hmem". rewrite /promiseInv_inner.
      iDestruct "HpInv" as (M) "[HM HInv]".
      iDestruct (claim_membership M p γ Φ with "[$]") as "[%Φ' [%Hlkp #Heq]]".
      iPoseProof (promise_unfold_equiv with "Heq") as "#Heq'".
      iDestruct (big_sepM_delete _ _ (p, γ) with "HInv")
        as "[HpSt HInv]"; first done.
      iSplitL "HInv HM".
      - iNext.
        iIntros "HpSt". iExists M. iFrame.
        rewrite (big_opM_delete _ _ _ _ Hlkp). iFrame.
        iApply (promiseSt_proper' p γ Φ Φ' with "[] HpSt").
        rewrite discrete_fun_equivI. iIntros (x).
        by iRewrite ("Heq'" $! x).
      - rewrite /promiseSt_later.
        iDestruct "HpSt" as  "[[%y ((Hp&#Hps)&Hy)]|[%l [%enqs (Hp&Hps&Hl&Hks)]]]".
        + iLeft. iExists y. iFrame. iSplit; first done.
          iNext. iSpecialize ("Heq'" $! y). by iRewrite -"Heq'".
        + iRight. iExists l, enqs. by iFrame.
    Qed. *)
    Admitted.

    Lemma allocate_promiseInv :
      promiseInv_inner ⊢ |={⊤}=> promiseInv.
    Proof.
      iIntros "Hinner". rewrite /promiseInv.
      by iMod (inv_alloc promiseN ⊤ promiseInv_inner with "[Hinner]").
    Qed.
  End promise_preds.

End predicates.


(* -------------------------------------------------------------------------- *)
(** Protocol [Coop]. *)

Section protocol_coop.
  Context `{!heapGS Σ, !promiseGS Σ}.

  Definition FORK_pre (Coop : iEff Σ) : iEff Σ :=
    >> e >> !(Fork'  e) {{promiseInv ∗ ▷ (promiseInv -∗  EWP e #() <|Coop |> {{_, True}} ) }};
    << (_: val) << ?(#())        {{ True }} @ OS.
      
  (* a.d. for the suspend call in await, we want to instantiate P with (λ v, v = #() ∧ done p)
    where done p shows that the promise is fulfilled
    1. it's maybe not okay for P to close over the promise p.
    2. we want to change torch γ to a oneshot (torch γ) + (done γ)  
  *)
  Definition SUSPEND : iEff Σ :=
    >> (f: val) (P: val → iProp Σ) >> !(Suspend' f) {{
      (* We call f with the enqueue function and enqueue receives a value satisfying P and accesses the run queue. *)
        ( (∀ (enqueue: val),
          (∀ (v: val), P v -∗  (EWP (enqueue v) <| ⊥ |> {{_, True }}) ) -∗
          promiseInv -∗ (▷ EWP (f enqueue) <| ⊥ |> {{_, True  }}) ) 
      ∗
        promiseInv)%I
    }};
    << y           << ?(y)         {{ P y }} @ OS.

  Definition Coop_pre : (iEffO) → (iEffO) := (λ Coop,
    FORK_pre Coop <+> SUSPEND
  )%ieff.

  Local Instance Coop_pre_contractive : Contractive (Coop_pre).
  Proof.
    rewrite /Coop_pre /SUSPEND /FORK_pre=> n Coop Coop' HCoop.
    by repeat (apply ewp_ne||apply iEffPre_base_ne||f_contractive||f_equiv).
  Qed.
  Definition Coop_def : (iEff Σ) := fixpoint Coop_pre.
  Definition Coop_aux : seal Coop_def. Proof. by eexists. Qed.
  Definition Coop := Coop_aux.(unseal).
  Definition Coop_eq : Coop = Coop_def := Coop_aux.(seal_eq).
  Global Lemma Coop_unfold  : Coop  ≡ Coop_pre (Coop).
  Proof. rewrite Coop_eq /Coop_def.
         by apply (fixpoint_unfold (Coop_pre)).
  Qed.
  Definition FORK := FORK_pre Coop.

  Lemma upcl_Coop v Φ' :
    iEff_car (upcl OS (Coop )) v Φ' ⊣⊢
      iEff_car (upcl OS (FORK )) v Φ' ∨
      iEff_car (upcl OS (SUSPEND )) v Φ'.
  Proof.
    transitivity (iEff_car (upcl OS (Coop_pre Coop )) v Φ').
    - iApply iEff_car_proper. by rewrite {1}Coop_unfold.
    - by rewrite upcl_sum (upcl_tele' [tele _ _] [tele _]) //.
  Qed.

  Lemma upcl_FORK  v Φ' :
    iEff_car (upcl OS (FORK )) v Φ' ≡
      (∃ e, ⌜ v = Fork' e ⌝ ∗ (promiseInv ∗ ▷ (promiseInv -∗ EWP e #() <|Coop|> {{_, True }})) ∗
            (∀ (_ : val), True -∗ Φ' #()))%I.
  Proof. by rewrite /FORK (upcl_tele' [tele _] [tele _]). Qed.

  Lemma upcl_SUSPEND  v Φ' :
    iEff_car (upcl OS (SUSPEND )) v Φ' ≡
      (∃ (f : val) (P: val → iProp Σ), ⌜ v = Suspend' f ⌝ 
      ∗ 
      (* the big precondition of the protocol *)
        ( (∀ (enqueue: val),
          (∀ (v: val), P v -∗ (EWP (enqueue v) <| ⊥ |> {{_, True }}) ) -∗
          promiseInv -∗ (▷ EWP (f enqueue) <| ⊥ |> {{_, True }}) )
      ∗
          promiseInv) 
      ∗
          (∀ v, P v -∗ Φ' v))%I.
  Proof. by rewrite /SUSPEND (upcl_tele' [tele _ _] [tele _]). Qed.

End protocol_coop.


(* ========================================================================== *)
(** * Verification. *)

Section verification.
  Context `{!heapGS Σ, !promiseGS Σ, !ListLib Σ}.

  Lemma ewp_new_promise Ψ Φ :
    promiseInv ⊢ EWP (new_promise #()) <| Ψ |> {{ y,
        ∃ p γ, ⌜ y = #(p : loc) ⌝ ∗ promise_state_waiting γ ∗ isMember p γ Φ }}.
  Proof.
    iIntros "HpInv".
    unfold new_promise. ewp_pure_steps. ewp_bind_rule. simpl.
    iApply ewp_mono. { by iApply cqs_create_spec. }
    iIntros (enqs) "#Hcqs !>". ewp_pure_steps.
    (* open the invariant -> evaluate the alloc -> change and close the invariant *)
    rewrite /promiseInv.
    assert (Hatom: Atomic StronglyAtomic (Alloc (InjRV enqs))).
      by apply _.
    iApply (ewp_atomic ⊤ (⊤ ∖ ↑promiseN)).
    iMod (inv_acc with "HpInv") as "(HpInvIn & Hclose)"; first by done.
    iModIntro.
    iApply ewp_alloc. iIntros "!>" (p) "Hp".

    iMod promise_state_create as "[%γ Hps]".
    iMod (promise_state_split with "Hps") as "[Hps1 Hps2]".
    iAssert (promiseSt p γ Φ) with "[Hp Hps1]" as "HpSt".
    { iRight. iExists enqs. by iFrame. }
    iMod (update_promiseInv_inner with "[HpInvIn HpSt]") as "(HpInvIn & #Hmem)"; first by iFrame.
    iModIntro.
    iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
    iSplitL "Hclose". iApply "Hclose".
    iModIntro. iFrame.
    iExists p, γ. iFrame. by iSplit.
  Qed.
  
  Lemma ewp_next q Ψ :
    promiseInv -∗
      is_queue q ready -∗
         EWP (next q) <| Ψ |> {{ _, True }}.
  Proof.
    iIntros "HpInv #Hq". unfold next. ewp_pure_steps. ewp_bind_rule.
    iApply ewp_mono; [iApply (queue_pop_spec with "Hq")|].
    simpl. iIntros (y) "[->|(%k & -> & Hk)] !>".
    - (* queue is empty *) 
      by ewp_pure_steps.
    - (* queue has a continuation *)
      ewp_pure_steps.
      rewrite /ready.
      iSpecialize ("Hk" with "HpInv").
      iApply ewp_os_prot_mono. { by iApply iEff_le_bottom. } { done. }
  Qed.

  Lemma ewp_fork (e : val) :
    promiseInv  ∗ 
    (promiseInv -∗ EWP e #() <| Coop |> {{ _, True }})
  ⊢
      EWP (fork e) <| Coop |> {{ _, True }}.
  Proof.
    iIntros "(HpInv &  He)". rewrite /fork. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_FORK. iLeft.
    iExists e. iSplit; [done|]. iFrame.
    iIntros (_) "H". by iFrame.
  Qed.

  Lemma ewp_suspend (f : val) (P: val → iProp Σ) :
      ( (∀ (enqueue: val),
        (∀ (v: val), P v -∗ (EWP (enqueue v) <| ⊥ |> {{_, True}}) ) -∗
        promiseInv -∗ (▷ EWP (f enqueue) <| ⊥ |> {{_, True }})) 
    ∗
      promiseInv) 
    ⊢
      EWP (suspend f) <| Coop |> {{ v, P v }}.
  Proof.
    iIntros "(He & HpInv)". rewrite /suspend. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_SUSPEND. iRight.
    iExists f, P. iSplit; [done|]. iFrame.
    iIntros (v) "Hv". by iFrame.
  Qed.

  Lemma ewp_await_callback (p: loc) (enqs: val) γ Φ:
  let P := (λ v, ⌜ v = #() ⌝ ∗ promise_state_done γ)%I in
    isMember p γ Φ ∗ promise_cqs enqs γ
  ⊢
    EWP (await_callback #p enqs) <| ⊥ |> {{f, 
      ∀ (enqueue: val), (∀ (v: val), P v -∗ EWP (enqueue v) <| ⊥ |> {{_, True }}) -∗
      promiseInv -∗ 
        (▷ EWP (f enqueue) <| ⊥ |> {{_, True }}) }}.
  Proof.
    iIntros "(#Hmem & #Hcqs)". rewrite /await_callback. ewp_pure_steps.
    iIntros (enqueue) "Henq #HpInv". iNext.
    ewp_pure_steps. 
    (* now we suspend enq*)
    iApply (ewp_bind [(AppRCtx _)]); first done. simpl.
    iApply (ewp_mono with "[Henq]").
      by iApply (cqs_suspend_spec with "Hcqs Henq").
    (* a.d. TODO where did that update modality come from? *)
    iIntros (r) "Hreq !>".
    ewp_pure_steps. ewp_bind_rule. simpl.
    (* a.d. here we need to open the invariant to read the promise *)
    rewrite /promiseInv.
    assert (Hatom: Atomic StronglyAtomic (Load #p)).
      by apply _.
    iApply (ewp_atomic ⊤ (⊤ ∖ ↑promiseN)).
    iMod (inv_acc with "HpInv") as "(HpInvIn & Hclose)"; first by done.
    iModIntro.
    (* a.d. using the maybe unsound rule of getting the inner promise state *)
    iDestruct (lookup_promiseInv_inner with "HpInvIn Hmem") as "[HpInvIn HpSt]".
    iDestruct "HpSt" as "[[%y ((Hp&#Hps) & Hy)]| (%enqs' & Hp & Hps & Henqs) ]".
    - (* the promise was fulfilled *)
      iApply (ewp_load with "Hp"). 
      iIntros "!> Hp !>".
      iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
      iSplitL "Hclose". iApply "Hclose".
      iModIntro.
      iSplitR "Hreq".
      + iNext. iApply "HpInvIn".
        iLeft. iExists y. by iFrame.
      + ewp_pure_steps.
        iApply (ewp_bind [(AppRCtx _)]); first by done. simpl.
        iApply (ewp_mono with "[Hreq]").
        iApply (cqs_cancel_spec with "Hcqs Hreq").
        iIntros (dummy) "Henq !>".
        ewp_pure_steps.
        iApply "Henq". by iSplit.
    - (* the promise is not yet fulifilled, our job is done and we don't do anything *)
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>". 
      iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
      iSplitL "Hclose". iApply "Hclose".
      iModIntro.
      iSplitL.
      + iNext. iApply "HpInvIn".
        iRight. iExists enqs'. by iFrame. 
      + ewp_pure_steps. by done.
  Qed.

  Lemma ewp_await (p: loc) Φ :
    promiseInv ∗ isPromise p Φ ⊢ 
      EWP (await #p) <| Coop |> {{v, □ Φ v}}.
  Proof.
    iIntros "(#HpInv & %γ & #Hmem)". rewrite /await. 
    ewp_pure_steps. ewp_bind_rule. simpl.
    (* a.d. here we need to open the invariant to read the promise *)
    rewrite /promiseInv.
    assert (Hatom: Atomic StronglyAtomic (Load #p)).
      by apply _.
    iApply (ewp_atomic ⊤ (⊤ ∖ ↑promiseN)).
    iMod (inv_acc with "HpInv") as "(HpInvIn & Hclose)"; first by done.
    iModIntro.
    (* a.d. using the maybe unsound rule of getting the inner promise state *)
    iDestruct (lookup_promiseInv_inner with "HpInvIn Hmem") as "[HpInvIn HpSt]".
    iDestruct "HpSt" as "[[%y ((Hp&#Hps) & #Hy)]| (%enqs & Hp & Hps & #Henqs) ]".
    - (* the promise is already fulfilled *)
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>". 
      iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
      iSplitL "Hclose". iApply "Hclose".
      iModIntro.
      iSplitL.
      iNext. iApply "HpInvIn". iLeft. iExists y. iSplit; last done. by iSplit.
      ewp_pure_steps. by iAssumption.
    - (* the promise is not yet fulfilled, so we create a callback and perform the suspend effect.
         After the suspend returns, we know the promise is fulfilled. *)
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>".
      iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
      iSplitL "Hclose". iApply "Hclose".
      iModIntro.
      iSplitL.
      iNext. iApply "HpInvIn". iRight. iExists enqs. by iFrame.
      ewp_pure_steps. 
      iApply (ewp_bind ([AppRCtx _])); first by done. simpl.
      iApply ewp_mono. 
      iApply ewp_os_prot_mono. iApply iEff_le_bottom.
      iApply ewp_await_callback. iSplit; by iAssumption.
      iIntros (callback) "Hf !>".
      ewp_pure_steps.
      ewp_bind_rule. simpl.
      iApply (ewp_mono with "[Hf]").
      { iApply (ewp_suspend callback (λ v, ⌜ v = #() ⌝ ∗ promise_state_done γ)%I). 
        by iFrame. }
      (* after we have performed the effect we get promise_state_done. *)
      iIntros (v) "(-> & Hps) !>".
      ewp_pure_steps. ewp_bind_rule. simpl.
      (* now we match on the promise again but this time we know it must be fulfilled *)
      iApply (ewp_atomic ⊤ (⊤ ∖ ↑promiseN)).
      iMod (inv_acc with "HpInv") as "(HpInvIn & Hclose)"; first by done.
      iModIntro.
      (* a.d. using the maybe unsound rule of getting the inner promise state *)
      iDestruct (lookup_promiseInv_inner with "HpInvIn Hmem") as "[HpInvIn HpSt]".
      iDestruct "HpSt" as "[[%y ((Hp&#Hps') & #Hy)]| (%enqs' & Hp & Hps' & #Henqs') ]";
        last by iDestruct (promise_state_disjoint γ with "[$]") as "HFalse".
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>". 
      iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
      iSplitL "Hclose". iApply "Hclose".
      iModIntro.
      iSplitL.
      iNext. iApply "HpInvIn". iLeft. iExists y. iSplit; last done. by iSplit.
      ewp_pure_steps. done.
  Qed.

  (* the wrapped function is passed via the FORK effect to the handler.
     the handler should then pass is_queue to wrapped_f so that it is able to change the run_queue.
     is_queue should be passed between client and handler the same as promiseInv, for every performed effect. *)
  Lemma ewp_fork_wrap (f: val) (p: loc) γ Φ :
    promise_state_waiting γ ∗ isMember p γ Φ ∗ EWP (f #()) <| Coop |> {{v, □ Φ v}} 
  ⊢
    EWP (fork_wrap_f f #p) <| ⊥ |> {{wrapped_f, 
        (* promiseInv and is_queue are passed here because they come from the effect handler *)
          promiseInv -∗
          EWP (wrapped_f #()) <| Coop |> {{_, True}} }}.
  Proof.
    iIntros "(Hps_start & #Hmem & Hf)". 
    (* split the waiting state b/c we need a fragment to write to p at the end. *)
    (* iApply fupd_ewp.
    iMod (promise_state_split2 with "Hps") as "(Hps1 & Hps2)".
    iModIntro. *)
    rewrite /fork_wrap_f. ewp_pure_steps.
    iIntros "#HpInv". ewp_pure_steps.
    ewp_bind_rule. simpl. iApply (ewp_mono with "Hf"). 
    iIntros (v) "#Hv !>".
    ewp_pure_steps. ewp_bind_rule. simpl.
    (* a.d. here we need to open the invariant *)
    rewrite /promiseInv.
    assert (Hatom: Atomic StronglyAtomic (Load #p)).
      by apply _.
    iApply (ewp_atomic ⊤ (⊤ ∖ ↑promiseN)).
    iMod (inv_acc with "HpInv") as "(HpInvIn & Hclose)"; first by done.
    iModIntro.
    (* a.d. using the maybe unsound rule of getting the inner promise state *)
    iDestruct (lookup_promiseInv_inner with "HpInvIn Hmem") as "[HpInvIn HpSt]".
    iDestruct "HpSt" as "[[%y ((Hp&#Hps) & #Hy)]| (%enqs & Hp & Hps & #Henqs) ]";
      first by iDestruct (promise_state_disjoint γ with "[$]") as "HFalse".
    iApply (ewp_load with "Hp").
    iIntros "!> Hp !>". 
    iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
    iSplitL "Hclose". iApply "Hclose".
    iModIntro.
    iSplitR "Hps_start".
    iNext. iApply "HpInvIn". iRight. iExists enqs. by iFrame.
    ewp_pure_steps. ewp_bind_rule. simpl.
    iApply ewp_mono. 
    iApply (cqs_resume_all_spec with "Henqs").
    (* now we have a list of resumed enq's and call them all *)
    iIntros (resumed) "(%ks & Hl & Hks) !>".
    ewp_pure_steps. ewp_bind_rule. simpl.
    iApply (ewp_atomic ⊤ (⊤ ∖ ↑promiseN)).
    iMod (inv_acc with "HpInv") as "(HpInvIn & Hclose)"; first by done.
    (* iModIntro. *)
    (* a.d. using the maybe unsound rule of getting the inner promise state *)
    iDestruct (lookup_promiseInv_inner with "HpInvIn Hmem") as "[HpInvIn HpSt]".
    iDestruct "HpSt" as "[[%y ((Hp&#Hps) & #Hy)]| (%enqs' & Hp & Hps & #Henqs') ]";
      first by iDestruct (promise_state_disjoint γ with "[$]") as "HFalse".
    (* now we change the logical promise state, but for that we need to open it again. *)
    iMod (promise_state_join with "[$]") as "Hps".
    iMod (promise_state_fulfill with "Hps") as "#Hps".
    iModIntro. 
    iApply (ewp_store with "Hp"). iIntros "!> Hp !>".
    iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
    iSplitL "Hclose". iApply "Hclose".
    iModIntro.
    iSplitR "Hl Hks".
    iNext. iApply "HpInvIn". iLeft. iExists v. iFrame. by iSplit.
    ewp_pure_steps.
    (* now we just call all the enqueue functions. *)
    set I : list val → iProp Σ := (λ us,
      ∃ vs, ⌜ us ++ vs = ks ⌝ ∗ [∗ list] enq ∈ vs, 
        ∀ v0 : val, ⌜v0 = #()⌝ ∗ promise_state_done γ -∗
                    EWP (App (Val enq) v0) <| ⊥ |> {{ _, True }}
      )%I.
    iApply (ewp_mono with "[Hks Hl]").
    { iApply ewp_os_prot_mono. iApply iEff_le_bottom.
      iApply (list_iter_spec _ I with "[] Hl [Hks]").
      2: by iExists ks; iFrame.
      iIntros "!#" (us enq vs) "<- [%vs' [%Heq Hvs']]".
      specialize (app_inj_1 us us vs' (enq :: vs) eq_refl Heq) as [_ ->].
      iDestruct "Hvs'" as "[Hk Hvs]". 
      ewp_pure_steps. iApply (ewp_mono with "[Hk]").
      { iApply ("Hk" $! #()). by iSplit. }
      iIntros (?) "_ !>".
      rewrite /I.
      iFrame.
      iExists vs. iFrame.
      iPureIntro. by rewrite -app_assoc.
    }
    iIntros (?) "[Hl _] !>". done.
  Qed.

  (* Definition fork_wrap_f : val := (λ: "f" "p", (λ: <>, 
    let: "v" := "f" #() in
    match: Load "p" with
      (* Done: *) InjL <> =>
        #() #() (* Unreachable! *)
    | (* Waiting: *) InjR "ks" =>
        cqs_resume_all "ks";;
        "p" <- Done "v"
    end))%V. *)

  Lemma ewp_fork_promise  (f: val) Φ :
    promiseInv ∗ EWP (f #()) <| Coop  |> {{v, □ Φ v}}
  ⊢ 
    EWP (fork_promise f) <| Coop  |> {{ y, 
      ∃ (p: loc), ⌜ y = #p ⌝ ∗ isPromise p Φ }}.
  Proof.
    iIntros "(#HpInv & Hf)". rewrite /fork_promise. ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply ewp_mono. iApply (ewp_new_promise _ Φ with "HpInv").
    iIntros (v) "(%p & %γ & -> & Hps & #Hmem) !>".
    ewp_pure_steps.
    iApply (ewp_bind' (AppRCtx _)); first done. simpl.
    iApply (ewp_mono with "[Hf Hps]").
    { iApply ewp_os_prot_mono. iApply iEff_le_bottom.
      iApply ewp_fork_wrap. by iFrame. }
    iIntros (wrapped_f) "Hwrapped_f !>".
    ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply (ewp_mono with "[HpInv Hwrapped_f]").
    iApply ewp_fork. by iFrame.
    iIntros (?) "_ !>".
    ewp_pure_steps. iExists p.
    iFrame. iSplit; first done.
    by iExists γ.
  Qed.
    
    (* this guy needs
    1. promiseInv because he gets promiseSt and promise_state_waiting from new_promise
       then it will insert into promiseInv and get isPromise
    2. then to call fork it needs an ewp like `I -∗ EWP wrapped_f () <| Coop |> { I }`
    3. then it can return promiseInv and isPromise
    *)

  (* Definition fork_promise : val := (λ: "f", 
    let: "p" := new_promise #() in
    let: "wrapped_f" := fork_wrap_f "f" "p" in
    fork "wrapped_f";;
    "p")%V. *)
      
  Lemma ewp_run (main : val) Φ :
    promiseInv -∗
      (promiseInv -∗ EWP main #() <| Coop |> {{ v, □ Φ v }}) -∗
        EWP run main {{ _, True }}.
  Proof.
    iIntros "#HpInv Hmain". unfold run. ewp_pure_steps.
    ewp_bind_rule. iApply ewp_mono. { by iApply queue_create_spec. }
    iIntros (q) "Hq !>". simpl. ewp_pure_steps.
    iSpecialize ("Hq" $! ready).
    iSpecialize ("Hmain" with "HpInv").
    iLöb as "IH" forall (main q Φ).
    iApply (ewp_deep_try_with with "Hmain").
    iLöb as "IH_handler" forall (q Φ).
    iDestruct "Hq" as "#Hq".
    rewrite deep_handler_unfold.
    iSplit; [|iSplit]; last (by iIntros (??) "HFalse"; rewrite upcl_bottom).
    (* Return branch. *)
    - iIntros (?) "_".
      ewp_pure_steps. iApply (ewp_next with "HpInv Hq").
    (* Effect branch. *)
    - iIntros (request k). rewrite upcl_Coop upcl_FORK upcl_SUSPEND.
      iIntros "[(%e & -> & (_ & He) & Hk)
               |(%f & %P & -> & (Hf & _) & Hk)]".
      (* Fork. *)
      + ewp_pure_steps.
        iApply (ewp_bind' (AppRCtx _)); first by done. simpl.
        iApply (ewp_mono with "[Hk]").
        { iApply (queue_push_spec with "Hq"). rewrite /ready.
          iIntros "#HpInv'". ewp_pure_steps.
          iSpecialize ("Hk" $! #() with "[//]").
          iApply "Hk". iNext.
          by iApply ("IH_handler" with "Hq").
        }
        iIntros (?) "_ !>". ewp_pure_steps.
        iSpecialize ("He" with "HpInv").
        iApply ("IH" with "[He] Hq").
        instantiate (1:=(λ _, True)%I).
        iApply (ewp_mono with "He"). 
        iIntros (?) "_ !>". by iFrame. 
      (* Suspend. *)
      + do 9 ewp_value_or_step.
        (* here we bind the creation of enqueue. Now we should prove a spec for it. *)
        iApply (ewp_mono with "[Hk]").
        { set (Henq := (λ (enqueue: val), (∀ (v : val),
              P v -∗
              EWP enqueue v <| ⊥ |> {{ _, True }})%I)).
          ewp_pure_steps.
          instantiate (1:=Henq). rewrite /Henq.
          iIntros (v) "HP".
          ewp_pure_steps.
          iApply (queue_push_spec with "Hq"). rewrite /ready.
          iIntros "#HpInv'". ewp_pure_steps.
          iSpecialize ("Hk" $! v with "[$]").
          iApply "Hk". iNext.
          by iApply ("IH_handler" with "Hq").
        }
        iIntros (enqueue) "Henq !>".
        iSpecialize ("Hf" $! enqueue with "Henq HpInv").
        ewp_pure_steps.
        ewp_bind_rule. simpl.
        iApply (ewp_mono with "Hf").
        iIntros (?) "_ !>". ewp_pure_steps.
        iApply (ewp_next with "HpInv Hq").
  Qed.

End verification.

Print Assumptions ewp_run.
Print Assumptions ewp_fork_promise.
Print Assumptions ewp_await.

(* ========================================================================== *)
(** * Specification. *)

Section specification.
  Context `{!heapGS Σ}.
  Context `{!ListLib Σ}.

  Class AsyncCompLib := {
    coop : val -> iEff Σ;
    is_promise : val → (val -> iProp Σ) → iProp Σ;
    is_promise_Persistent p Φ : Persistent (is_promise p Φ);
    fork_spec (e : val) Φ :
      EWP e #() <| coop |> {{ y, □ Φ y }} -∗
        EWP async e <| coop |> {{ p, is_promise p Φ }};
    _spec p Φ :
      is_promise p Φ -∗
        EWP await p <| coop |> {{ y, □ Φ y }};
  }.

  Definition run_spec (main : val) :=
    (∀ _ : AsyncCompLib, EWP main #() <| coop |> {{ _, True }}) ==∗
      EWP run main <| ⊥ |> {{ _, True }}.

End specification.



Section closed_proof.
  Context `{!heapGS Σ, !promiseGpreS Σ}.
  Context `{!ListLib Σ}.

  Lemma promiseInv_init :
    ⊢ |==> ∃ _ : promiseGS Σ, ∀ q, promiseInv.
  Proof.
    iIntros. iMod (own_alloc (● (∅ : gmap (loc * gname) _))) as (γ) "HI";
      first by rewrite auth_auth_valid.
    iModIntro. iExists {| promise_inG := _; promise_name := γ; |}.
    iIntros (q). iExists ∅. rewrite /isPromiseMap fmap_empty. by iFrame.
  Qed.

  Local Program Instance async_comp_lib `{!promiseGS Σ} :
    AsyncCompLib (Σ:=Σ) := {
    coop := Coop;
    is_promise := λ v Φ, (∃ (p : loc), ⌜ v = #p ⌝ ∗ isPromise p Φ)%I;
    is_promise_Persistent := _;
  }.
  Next Obligation. by iIntros (???) "?"; iApply ewp_async. Qed.
  Next Obligation. by iIntros (???) "[% [-> ?]]"; iApply ewp_await. Qed.

  Theorem run_correct main : run_spec main.
  Proof.
    iIntros "He". iMod promiseInv_init as "[%HpromiseGS HpInv]".
    iSpecialize ("He" $! async_comp_lib). iModIntro.
    iApply (ewp_run _ (λ _, True)%I with "HpInv").
    iApply (ewp_mono with "He"). by auto.
  Qed.

End closed_proof.
