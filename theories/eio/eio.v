(* asynchronous_computation.v *)

(* a.d. TODO do we really need the saved proposition. Check again if the lookup lemma can be proven without it.
If not, write an explanation why. *)
(* a.d. TODO clean up + convert everything to camelCase. *)

(* a.d. TODO rewrite
   The ability offered by effect handlers (or any other interface for
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
From iris.base_logic.lib Require Import iprop wsat saved_prop.

From eio Require Import deferred_stack cqs.
From program_logic Require Import reasoning_rules.

(* ========================================================================== *)
(** * Implementation of the Scheduler. *)

Notation Fork tlv e := (InjL (Pair tlv e)) (only parsing).
Notation Suspend f := (InjR (InjL f)) (only parsing).
Notation GetContext := (InjR (InjR #())) (only parsing).

Notation Fork' tlv e := (InjLV (PairV tlv e)) (only parsing).
Notation Suspend' f := (InjRV (InjLV f)) (only parsing).
Notation GetContext' := (InjRV (InjRV #())) (only parsing).

Notation Done y := (InjL y) (only parsing).
Notation Waiting ws := (InjR ws) (only parsing).

Notation Done' y := (InjLV y) (only parsing).
Notation Waiting' ws := (InjRV ws) (only parsing).

Section implementation.
  Context `{!heapGS Σ }.

  Definition new_scheduler_result : val := (λ: <>,
    ref NONEV
  )%V.
  Definition new_promise : val := (λ: <>,
    ref (Waiting (cqs_new #()))
  )%V.
  Definition new_context : val := (λ: "init",
    ref "init"
  )%V.
  Definition fork : val := (λ: "tlv" "f", do: (Fork "tlv" "f"))%V.
  Definition suspend : val := (λ: "f", do: (Suspend "f"))%V.
  Definition get_context : val := (λ: <>, do: GetContext)%V.
  
  Definition yield : val := (λ: <>,
    let: "register" := λ: "waker", "waker" #() in
    suspend "register"
  )%V.

  Definition next : val := (rec: "next" "result" "q" :=
    match: queue_pop "q" with
      (* Empty *) InjL <> => 
        match: Load "result" with
          (* Not Done *) InjL <> => "next" "result" "q"
        | (* Done *)     InjR <> => #() 
        end
    | (* Nonempty *) InjR "f" => "f" #()
    end)%V.

  Definition fork_wrap_f : val := (λ: "f" "p", (λ: <>, 
    let: "v" := "f" #() in
    match: Load "p" with
      (* Done: *) InjL <> =>
        #() #() (* Unreachable! *)
    | (* Waiting: *) InjR "ws" =>
        (* First set the promise to Done, so that we can update the logical promise state and call enqueue *)
        "p" <- Done "v";;
        cqs_resume_all "ws"
    end))%V.

  (* fork a new fiber "f" and return a promise to get the result. *)
  Definition fork_promise : val := (λ: "f", 
    let: "tlv" := get_context #() in
    let: "p" := new_promise #() in
    let: "wrapped_f" := fork_wrap_f "f" "p" in
    fork "tlv" "wrapped_f";;
    "p")%V.
   
  Definition await_callback : val := (λ: "p" "ws", (λ: "waker", 
    (* We do the same as Eio and suspend in CQS and then check the state of the promise again. 
       Since we gave enqueue to the queue in suspend, if p is Done, we first need to cancel the reques to get the permission to
       call enqueue back. *)
    let: "res" := cqs_suspend "ws" "waker" in
    match: "res" with
      InjL <> => #()
    | InjR "req" =>
        match: Load "p" with
            (* Done: *) InjL <>  => 
            if: cqs_try_cancel "req"
            then "waker" #()
            else #()
        | (* Waiting: *) InjR <> => #()
        end
      end
  ))%V.

  Definition await : val := (λ: "p",
    match: Load "p" with
      (* Done: *) InjL "y"  =>
        "y"
    | (* Waiting: *) InjR "ws" =>
        let: "callback" := await_callback "p" "ws" in 
        suspend "callback";;
        match: Load "p" with
          (* Now Done: *) InjL "y" =>
            "y"
        | (* Waiting: *) InjR <> =>
            #() #() (* unreachable *)
        end
    end
  )%V.


  Definition execute : val := (λ: "q" "result", rec: "execute" "context" "f" :=
    deep-try: "f" #() with
      effect (λ: "request" "k",
        match: "request" with
          (* Fork: *) InjL "contextf" =>
            let: "new_context" := Fst "contextf" in 
            let: "f" := Snd "contextf" in
            queue_change_state #();;
            queue_push "q" (λ: <>, "k" #());;
            queue_change_state #();;
            "execute" "new_context" "f"
        | (* Suspend/GetContext: *) InjR "e1" =>
          match: "e1" with
            (* Suspend: *) InjL "suspender" =>
              (* a.d. probably the most complicated line 
              When waker is called with a value v, a closure calling the continuation with v is put into the run_queue. 
              suspender can either put waker somewhere that causes it to be called later or just call it directly. *)
              queue_change_state #();;
              let: "waker" := (λ: "v", queue_push "q" (λ: <>, "k" "v")) in
              "suspender" "waker";;
              queue_change_state #();;
              next "result" "q"
          | (* GetContext: *) InjR <> =>
              "k" "context"
          end
        end)
    | return (λ: <>, next "result" "q")
    end)%V.
    
  Definition run : val := (λ: "init" "main",
    let: "result" := new_scheduler_result #() in
    let: "initial_context" := new_context "init" in
    let: "q" := queue_create #() in
    execute "q" "result" "initial_context" (λ: <>, "result" <- SOME ("main" #()));;
    match: Load "result" with
      (* Not Done *) InjL <> => #() #() (* unreachable *)
    | (* Done *) InjR "x" => "x"
    end
  )%V.

End implementation.

(* ========================================================================== *)
(** * Internal Logical Definitions. *)

(* -------------------------------------------------------------------------- *)
(** Cameras. *)

(* a.d. TODO rewrite
   The verification relies on ghost cells of two kinds: either from the
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
    (authR (gmapUR (loc * gname * gname) unitR));
  (* state_mapG :> inG Σ
    (authR (gmapUR gname (agreeR locO))); *)
  (* mainG :> inG Σ (csumR fracR (agreeR valO)); *)
  torchG :> inG Σ (csumR fracR (agreeR valO));
  stateG :> inG Σ (agreeR locO);
}.
  
(* A concrete instance of [Σ] for which the assumption [promisesGS Σ] holds. *)
Definition promiseΣ := #[
  GFunctor (authRF
    (gmapURF (loc * gname * gname) unitR));
  (* GFunctor (authRF
    (gmapURF gname (agreeR locO))); *)
  (* GFunctor (csumR fracR (agreeR valO)); *)
  GFunctor (csumR fracR (agreeR valO));
  GFunctor (agreeR locO)
].
  
(* The proof of the previous claim. *)
#[export]
Instance subG_promiseΣ {Σ} : subG promiseΣ Σ → promiseGpreS Σ.
Proof. solve_inG. Qed.

Class promiseGS Σ := {
  promise_inG :> promiseGpreS Σ;
  promise_name : gname;
}.
  
(* -------------------------------------------------------------------------- *)
(** Predicates. *)

Section predicates.
  Context `{!heapGS Σ, !promiseGS Σ, !savedPredG Σ val, !deferredGS Σ, !savedPropG Σ}.

  (* ------------------------------------------------------------------------ *)
  (* Definitions. *)

  (* Promise state starts as whole, then it's split up and half is saved in the invariant and half is kept by the fiber.
     When the fiber is done, it updates the state to done. *)
  Definition promise_state_whole γ := own γ (Cinl 1%Qp).
  Definition promise_state_waiting γ := own γ (Cinl (1/2)%Qp).
  Definition promise_state_done γ v := own γ (Cinr (to_agree v)).
  
  Definition isFiberContext (l : loc) (I : valO -d> iPropO Σ) : iProp Σ := 
    (∃ v, l ↦ v ∗ I v)%I.

  (* This resource is always held by the active fiber, so we need to pass it in and out of effects 
     and need it as a precondition of a ready fiber. *)
  Definition fiberResourcesArgs : Type := (locO * (valO -d> iPropO Σ)).
  Definition fiberResources (lI : fiberResourcesArgs) := (
    isFiberContext lI.1 lI.2
  )%I.

  Context (resultN : namespace).
  Definition mainResult_inv γ ℓres Φ := (
    (ℓres ↦ NONEV ∗ promise_state_waiting γ)
  ∨ (∃ (v: val), ℓres ↦ SOMEV v ∗ promise_state_done γ #() ∗ □ Φ v)
  )%I.

  Definition mainResult γ ℓres Φ := inv resultN (mainResult_inv γ ℓres Φ).
    
  (* Fragment of the promise map. *)
  Definition isMember p γ ε :=
    own promise_name (◯ {[(p, γ, ε) := tt]}).
  
  (* Saved predicate for the promise result. *)
  Definition isPromiseResult ε (Φ : val -d> iPropO Σ) := 
    saved_pred_own ε DfracDiscarded Φ.

  Definition isPromise (p : loc) Φ := (
    ∃ γ ε, isMember p γ ε ∗ isPromiseResult ε Φ
  )%I.

  (* Authoritative promise map. *)
  Definition isPromiseMap (M : gmap (loc * gname * gname) unit) :=
    own promise_name (● M).

  (* Using the indirection of the saved predicate, the promise map is now timeless.
     a.d. TODO actually I don't think we need this. Removing Φ from the type of the map is enough. *)
  Definition isPromiseMap_timeless M : Timeless (isPromiseMap M).
  Proof. by apply _. Qed. 

  (* invariant stuff *)
  Definition promiseN : namespace := nroot .@ "promise".
  Definition queueN : namespace := nroot .@ "queue".

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
     
  (*  *)
  Definition promise_cqs (wakers: val): iProp Σ :=
    (is_thread_queue wakers)%I.
    
  (* The inner proposition of the invariant.
     A promise is either done or waiting.
     If done, then there exists some predicate identified by ε that satisfies the value.
        Using saved_pred we can get look up one promise in the promise map and then get a (▷ Φ y) 
     If waiting, then there exists a cqs that contains wakers. *)
  Definition promiseInv_inner : iProp Σ := (
    ∃ M, isPromiseMap M ∗
      ([∗ map] args ↦ tt ∈ M, let '(p, γ, ε) := args in
        ((* Fulfilled: *) ∃ y,
          p ↦ Done' y ∗ promise_state_done γ y ∗ 
          ∃ (Φ: val -d> iPropO Σ), isPromiseResult ε Φ ∗ □ Φ y)
      ∨
        ((* Unfulfilled: *) ∃ wakers,
          p ↦ Waiting' wakers ∗
          promise_state_waiting γ ∗
          (∃ n, thread_queue_state n) ∗
          resume_all_permit ∗
          promise_cqs wakers))
  )%I.
    
  Definition promiseInv := inv promiseN promiseInv_inner.
  
  Global Instance promiseInv_Persistent : Persistent promiseInv.
  Proof. by apply _. Qed.

  (* Definition main_whole θ := own θ (Cinl 1%Qp).
  Definition main_running θ := own θ (Cinl (1/2)%Qp).
  Definition main_done θ (v: val) := own θ (Cinr (to_agree v)).

  Global Instance main_done_Persistent θ v : Persistent (main_done θ v).
  Proof. by apply _. Qed. *)

  (* Now ready is just a predicate on a continuation k, that k is safe to execute under the assumption
     that promiseInv holds.
    a.d. TODO remove promiseInv *)
  (* Definition ready_pre δ ℓres (q k: val) : iProp Σ := (
    is_queue q fiberResources δ ℓres -∗ EWP (k #()) {{ _, fiberResources δ ℓres ∗ ∃ v, promise_state_done (fst (snd δ)) v }}
  )%I. *)

  Definition ready_pre :
    (fiberResourcesArgs -d> gnameO -d> val -d> val -d> iPropO Σ) →
    (fiberResourcesArgs -d> gnameO -d> val -d> val -d> iPropO Σ) := (λ ready fargs γ q k,
    fiberResources fargs -∗
    ▷ is_queue_reader queueN (ready fargs γ q) q -∗ 
      EWP (k #()) {{ _, fiberResources fargs ∗ ▷ is_queue_reader queueN (ready fargs γ q) q ∗ promise_state_done γ #() }}
  )%I.

  Local Instance ready_contractive : Contractive ready_pre.
  Proof.
    rewrite /ready_pre=> n ready ready' Hn fargs γ q k.
    f_equiv. f_equiv.
    - f_contractive. apply is_queue_reader_ne. apply Hn.
    - f_equiv.
      intros _. do 2 f_equiv. 
      f_contractive. apply is_queue_reader_ne. apply Hn.
  Qed.
  Definition ready_def : (fiberResourcesArgs -d> gnameO -d> val -d> val -d> iPropO Σ) :=
    fixpoint ready_pre.
  Definition ready_aux : seal ready_def. Proof. by eexists. Qed.
  Definition ready := ready_aux.(unseal).
  Definition ready_eq : ready = ready_def :=
    ready_aux.(seal_eq).
  Global Lemma ready_unfold fargs γ q k : ready fargs γ q k ⊣⊢ ready_pre ready fargs γ q k.
  Proof. rewrite ready_eq /ready_def. apply (fixpoint_unfold ready_pre). Qed.

  Definition promiseSt p γ ε: iProp Σ :=
    ((* Fulfilled: *) ∃ y,
       p ↦ Done' y ∗ promise_state_done γ y ∗
       ∃ (Φ: val -d> iPropO Σ), isPromiseResult ε Φ ∗ □ Φ y)
  ∨
    ((* Unfulfilled: *) ∃ wakers,
      p ↦ Waiting' wakers ∗
      promise_state_waiting γ ∗
      (∃ n, thread_queue_state n) ∗
      resume_all_permit ∗
      promise_cqs wakers).
      
  Definition promiseSt_later p γ ε : iProp Σ :=
    ((* Fulfilled: *) ∃ y,
       p ↦ Done' y ∗ promise_state_done γ y ∗
       ∃ (Φ: val -d> iPropO Σ), ▷ (isPromiseResult ε Φ ∗ □ Φ y))
  ∨
    ((* Unfulfilled: *) ∃ wakers,
      p ↦ Waiting' wakers ∗
      promise_state_waiting γ ∗
      (∃ n, thread_queue_state n) ∗
      resume_all_permit ∗
      ▷ promise_cqs wakers).

  (* ------------------------------------------------------------------------ *)
  (* Non-expansiveness. *)

  (* a.d. TODO we don't need it anymore since ready is not recursive, but it should still hold with the new formulation.
      It broke after I added the δ argument. *)
  (* [ready]. *)
  (* Global Instance ready_ne δ n :
    Proper ((dist n) ==> (dist n) ==> (dist n)) ready.
  Proof.
    induction (lt_wf n) as [n _ IH]=>k k' ->.
    rewrite /ready.
    (* by repeat (f_contractive
           || f_equiv || apply IH 
           || case x1 as ()         || case x2 as ()
           || case y1 as (y11, y12) || case y2 as (y21, y22)
           || apply H0 || apply H1 ). *)
  Admitted.
  Global Instance ready_proper : Proper ((≡) ==> (≡) ==> (≡)) ready.
  (* Proof. intros ???. apply equiv_dist=>n.
         by apply ready_ne; apply equiv_dist. *)
  Admitted. *)


  (* ------------------------------------------------------------------------ *)
  (* Properties. *)

  (* Logical rules governing the predicate [torch]. *)
  Section promise_state.

    Global Instance promise_state_done_Persistent γ v : Persistent (promise_state_done γ v).
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
      apply Qp.half_half.
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
      by rewrite Qp.half_half.
    Qed.

    Lemma promise_state_fulfill γ v :
      ⊢ promise_state_whole γ ==∗ promise_state_done γ v.
    Proof.
      iApply own_update.
      apply cmra_update_exclusive.
      apply Cinr_valid.
      done.
    Qed.
    
    Lemma promise_state_disjoint γ v : (promise_state_waiting γ ∗ promise_state_done γ v) -∗ False.
    Proof. 
      by rewrite /promise_state_waiting /promise_state_done -own_op own_valid csum_validI.
    Qed.

    Lemma promise_state_done_agree γ (v v' : val) : 
      promise_state_done γ v -∗ promise_state_done γ v' -∗ ⌜ v = v' ⌝.
    Proof.
      iIntros "H H'". 
      iCombine "H H'" as "H".
      iPoseProof (own_valid with "H") as "%".
      iPureIntro.
      by apply to_agree_op_inv_L.
    Qed.

  End promise_state.
  
  (* Logical rules governing the predicate [ready]. *)
  Section ready.
    (* a.d. TODO remove and unify with promise_state *)
    (* Lemma main_running_split θ :
      main_whole θ ==∗ main_running θ ∗ main_running θ.
    Proof.
      rewrite /main_running.
      rewrite -own_op.
      iApply own_update.
      rewrite -Cinl_op.
      apply csum_update_l.
      rewrite frac_op.
      rewrite cmra_update_updateP.
      apply cmra_updateP_id. 
      apply Qp_half_half.
    Qed.

    Lemma main_running_join θ :
      ⊢ main_running θ ∗ main_running θ ==∗ main_whole θ.
    Proof.
      rewrite /main_running.
      rewrite -own_op.
      iApply own_update.
      rewrite -Cinl_op.
      apply csum_update_l.
      rewrite frac_op.
      rewrite cmra_update_updateP.
      apply cmra_updateP_id. 
      by rewrite Qp_half_half.
    Qed.

    Lemma isMainResult_alloc result : 
      result ↦ NONE' ==∗ ∃ θ, isMainResult θ result ∗ main_running θ.
    Proof.
      iIntros "Hres".
      iMod (own_alloc (Cinl (1%Qp))) as (θ) "Hrun"; first by done.
      iMod (main_running_split with "Hrun") as "[Hrun1 Hrun2]".
      iModIntro. iExists _.
      iSplitR "Hrun2".
      iLeft. by iFrame. 
      by iAssumption.
    Qed.

    Lemma main_complete θ v :
      ⊢ main_whole θ ==∗ main_done θ v.
    Proof.
      iIntros "H".
      iApply (own_update with "H").
      apply cmra_update_exclusive.
      apply Cinr_valid.
      done.
    Qed. *)
  End ready.

  (* Logical rules governing the predicates [isPromiseMap], [isPromise], and
     [promiseInv]. *)
  Section promise_preds.

    (* Persistent predicates. *)
    Global Instance isMember_Persistent p γ ε: Persistent (isMember p γ ε).
    Proof. by apply _. Qed.
    Global Instance isPromiseResult_Persistent ε Φ: Persistent (isPromiseResult ε Φ).
    Proof. by apply _. Qed.
    Global Instance isPromise_Persistent p Φ : Persistent (isPromise p Φ).
    Proof. by apply _. Qed.

    Lemma update_promise_map M p γ ε : 
      M !! (p, γ, ε) = None →
        isPromiseMap M ==∗
          isPromiseMap (<[(p,γ,ε):=tt]> M) ∗ isMember p γ ε.
    Proof.
      intros Hlkp. iIntros "HM".
      iMod (own_update with "HM") as "[HM HiP]".
      { apply (@auth_update_alloc (gmapUR _ _) M).
        apply (alloc_singleton_local_update _ (p, γ, ε) tt).
        by rewrite /= Hlkp. done. }
      by iFrame. 
    Qed.

    Lemma claim_membership M p γ ε :
      isPromiseMap M ∗ isMember p γ ε -∗
        ⌜ M !! (p, γ, ε) = Some tt ⌝.
    Proof.
      rewrite /isPromiseMap /isMember.
      rewrite -own_op own_valid auth_both_validI /=.
      iIntros "(HM & #HpM)". iDestruct "HM" as (M') "#HM".
      rewrite gmap_equivI gmap_validI.
      iSpecialize ("HM" $! (p, γ, ε)). iSpecialize ("HpM" $! (p, γ, ε)).
      rewrite lookup_op lookup_singleton.
      rewrite option_equivI.
      case: (M  !! (p, γ, ε))=> [[]|] /=; [|
      case: (M' !! (p, γ, ε))=> [[]|] /=; by iExFalso].
      done.
    Qed.

    Lemma promiseSt_non_duplicable p γ γ' ε ε' :
      promiseSt p γ ε -∗ promiseSt p γ' ε' -∗ False.
    Proof.
      assert (⊢ ∀ p γ Φ, promiseSt p γ Φ -∗ ∃ v, p ↦ v)%I as Haux.
      { by iIntros (???) "[[%v[Hp _]]|[%ks[Hp _]]]"; auto. }
      iIntros "Hp Hp'".
      iPoseProof (Haux with "Hp")  as "[%v  Hp]".
      iPoseProof (Haux with "Hp'") as "[%v' Hp']".
      by iDestruct (mapsto_ne with "Hp Hp'") as "%Hneq".
    Qed.

    Lemma update_promiseInv_inner p γ ε :
      promiseInv_inner ∗ promiseSt p γ ε ==∗
        promiseInv_inner ∗ isMember p γ ε.
    Proof.
      iIntros "(HpInv & Hp)". rewrite /promiseInv_inner.
      iDestruct "HpInv" as (M) "(HM & HInv)".
      destruct (M !! (p, γ, ε)) as [Ψ|] eqn:Hlkp.
      - rewrite (big_opM_delete _ _ _ _ Hlkp).
        iDestruct "HInv" as "[Hp' _]".
        by iDestruct (promiseSt_non_duplicable with "Hp Hp'") as "HFalse".
      - iMod (update_promise_map M p γ ε Hlkp with "HM") as "[HM Hmem]".
        iModIntro. iFrame. iExists (<[(p, γ, ε):=tt]> M). iFrame.
        rewrite big_opM_insert; last done. by iFrame.
    Qed.

    Lemma later_promiseSt_promiseSt_later p γ ε Ε :
      ▷ promiseSt p γ ε ={Ε}=∗ promiseSt_later p γ ε.
    Proof.
      rewrite /promiseSt_later.
      iIntros "[[%y (>Hp&#>Hps&%Φ&Hεy)]|[%enqs (>Hp&>Hps&>Htqstate&>Hres&#Hks)]]".
      - iModIntro.
        iLeft. iExists y. iFrame. iSplit; first iAssumption.
        iExists Φ. by iFrame. 
      - iModIntro. 
        iRight. iExists enqs. by iFrame.
    Qed.
    
    Lemma lookup_promiseInv_inner' p γ ε :
      promiseInv_inner -∗ isMember p γ ε -∗
        ((promiseSt p γ ε -∗ promiseInv_inner) ∗ promiseSt p γ ε).
    Proof.
      iIntros "HpInv Hmem". rewrite /promiseInv_inner.
      iDestruct "HpInv" as (M) "[HM HInv]".
      iDestruct (claim_membership M p γ ε with "[$]") as "%Hlkp".
      iDestruct (big_sepM_delete _ _ (p, γ, ε) with "HInv")
        as "[HpSt HInv]"; first done.
      iSplitL "HInv HM".
      - iIntros "HpSt". iExists M. iFrame.
        rewrite (big_opM_delete _ _ _ _ Hlkp). iFrame.
      - done.
    Qed.
    
    Lemma lookup_promiseInv_inner p γ ε Ε :
      ▷ promiseInv_inner -∗ isMember p γ ε ={Ε}=∗
        (▷ (promiseSt p γ ε -∗ promiseInv_inner) ∗ promiseSt_later p γ ε).
    Proof.
      iIntros "HpInv #Hmem". 
      iAssert (▷ ((promiseSt p γ ε -∗ promiseInv_inner) ∗ promiseSt p γ ε))%I with "[HpInv]" as "(HpClose & HpSt)".
      2: iFrame; by iApply later_promiseSt_promiseSt_later.
      iModIntro. 
      iApply (lookup_promiseInv_inner' with "HpInv Hmem").
    Qed.

  End promise_preds.

End predicates.


(* -------------------------------------------------------------------------- *)
(** Protocol [Coop]. *)

Section protocol_coop.
  Context `{!heapGS Σ, !promiseGS Σ, !savedPredG Σ val}.
  
  Notation pEff := (fiberResourcesArgs -d> iEffO) (only parsing).

  Definition FORK_pre (Coop : pEff) (fargs : fiberResourcesArgs) : iEff Σ :=
    let ℓtlv := fargs.1 in
    >> e >> !(Fork' #ℓtlv e) {{fiberResources fargs ∗ ▷ (fiberResources fargs -∗ EWP e #() <| Coop fargs |> {{_, fiberResources fargs }}) }};
    << (_: val) << ?(#())        {{ fiberResources fargs }} @ OS.

  Definition SUSPEND (fargs : fiberResourcesArgs) : iEff Σ :=
    >> (reg: val) (P: val → iProp Σ) (Q: iProp Σ)>> !(Suspend' reg) {{
        fiberResources fargs ∗
        ∀ (waker: val),
          (∀ (v: val), P v -∗  (EWP (waker v) <| ⊥ |> {{_, True }}) ) -∗
          ( EWP (reg waker) <| ⊥ |> {{_, □ Q }})
    }};
    << y           << ?(y)         {{ fiberResources fargs ∗ P y ∗ Q }} @ OS.

  Definition GET_CONTEXT (fargs : @fiberResourcesArgs Σ) : iEff Σ :=
    let ℓtlv := fargs.1 in
    >> (_: val) >> !(GetContext') {{ True }};
    << (_: val) << ?(#ℓtlv) {{ True }} @ OS.

  Definition Coop_pre : pEff → pEff := (λ Coop,
    λ fargs, FORK_pre Coop fargs <+> SUSPEND fargs <+> GET_CONTEXT fargs
  )%ieff.

  Local Instance Coop_pre_contractive : Contractive (Coop_pre).
  Proof.
    intros n'.
    rewrite /Coop_pre /SUSPEND /FORK_pre /GET_CONTEXT=> Coop Coop' HCoop fargs.
    by repeat (apply ewp_ne||apply iEffPre_base_ne||f_contractive||f_equiv).
  Qed.
  Definition Coop_def : pEff := fixpoint Coop_pre.
  Definition Coop_aux : seal Coop_def. Proof. by eexists. Qed.
  Definition Coop := Coop_aux.(unseal).
  Definition Coop_eq : Coop = Coop_def := Coop_aux.(seal_eq).
  Global Lemma Coop_unfold fargs : Coop fargs ≡ Coop_pre Coop fargs.
  Proof. rewrite Coop_eq /Coop_def.
         by apply (fixpoint_unfold (Coop_pre)).
  Qed.
  Definition FORK := FORK_pre Coop.

  Lemma upcl_Coop v Φ' fargs:
    iEff_car (upcl OS (Coop fargs)) v Φ' ⊣⊢
      iEff_car (upcl OS (FORK fargs)) v Φ' ∨
      iEff_car (upcl OS (SUSPEND fargs)) v Φ' ∨
      iEff_car (upcl OS (GET_CONTEXT fargs)) v Φ'.
  Proof.
    transitivity (iEff_car (upcl OS (Coop_pre Coop fargs)) v Φ').
    - iApply iEff_car_proper. by rewrite {1}Coop_unfold.
    - by rewrite upcl_sum upcl_sum (upcl_tele' [tele _] [tele _]) //.
  Qed.

  Lemma upcl_FORK v Φ' fargs :
    let ℓtlv := fargs.1 in
    iEff_car (upcl OS (FORK fargs)) v Φ' ≡
      (∃ e, ⌜ v = Fork' #ℓtlv e ⌝ ∗ (fiberResources fargs ∗ ▷ (fiberResources fargs -∗ EWP e #() <|Coop fargs|> {{_, fiberResources fargs }})) ∗
            (∀ (_ : val), fiberResources fargs -∗ Φ' #()))%I.
  Proof. by rewrite /FORK (upcl_tele' [tele _] [tele _]). Qed.

  Lemma upcl_SUSPEND v Φ' fargs :
    iEff_car (upcl OS (SUSPEND fargs)) v Φ' ≡
      (∃ (f : val) (P: val → iProp Σ) (Q: iProp Σ), ⌜ v = Suspend' f ⌝ 
      ∗ 
      ( fiberResources fargs ∗ 
        ∀ (waker: val),
          (∀ (v: val), P v -∗ (EWP (waker v) <| ⊥ |> {{_, True }}) ) -∗
          ( EWP (f waker) <| ⊥ |> {{_, □ Q }}) )
      ∗
          (∀ v, (fiberResources fargs ∗ P v ∗ Q ) -∗ Φ' v))%I.
  Proof. by rewrite /SUSPEND (upcl_tele' [tele _ _ _] [tele _]). Qed.

  Lemma upcl_GET_CONTEXT v Φ' fargs :
    let ℓtlv := fargs.1 in
    iEff_car (upcl OS (GET_CONTEXT fargs)) v Φ' ≡ 
      (∃ (_: val), ⌜ v = GetContext' ⌝ ∗ True ∗
        (∀ (_ : val), True -∗ Φ' #ℓtlv)
      )%I.
  Proof.
    by rewrite /GET_CONTEXT (upcl_tele' [tele _] [tele _]). 
  Qed.

End protocol_coop.


(* ========================================================================== *)
(** * Verification. *)

Section verification.
  Context `{!heapGS Σ, !promiseGS Σ, !savedPredG Σ val, !deferredGS Σ, !savedPropG Σ}.
  Context (resultN : namespace).

  Lemma ewp_new_scheduler_result (Φ : val -> iProp Σ) :
  ⊢ EWP (new_scheduler_result #()) {{ v, ∃ (ℓres : loc) (γ : gname), ⌜ v = #ℓres ⌝ ∗ mainResult resultN γ ℓres Φ ∗ promise_state_waiting γ }}.
  Proof.
    rewrite /new_scheduler_result.
    ewp_pure_steps.
    iApply ewp_alloc.
    iIntros "!> %ℓres Hres".
    iMod (promise_state_create) as (γ) "Hγ".
    iMod (promise_state_split with "Hγ") as "[Hγ Hγ']".
    iMod (inv_alloc resultN ⊤ (mainResult_inv γ ℓres Φ) with "[Hres Hγ]") as "HresInv".
    { iNext. iLeft. by iFrame. }
    iModIntro.
    iExists _, _. iSplit; first done.
    by iFrame.
  Qed.

  Lemma ewp_new_promise Φ :
    promiseInv ⊢ EWP (new_promise #()) {{ y,
        ∃ p γ ε, ⌜ y = #(p : loc) ⌝ ∗ promise_state_waiting γ ∗ isMember p γ ε ∗ isPromiseResult ε Φ}}.
  Proof.
    iIntros "HpInv".
    unfold new_promise. ewp_pure_steps. 
    (* a.d. TODO here it should be okay to use ewp_bind_rule. Something is broken. *)
    iApply (ewp_bind' (AllocNRCtx _)); first by done. simpl.
    iApply (ewp_bind' (InjRCtx)); first by done. simpl.
    iApply ewp_mono. { by iApply newThreadQueue_spec. }
    iIntros (enqs) "(#Hcqs & Htqstate & Hres) !>". ewp_pure_steps.
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
    iMod (saved_pred_alloc Φ) as "[%ε #Hε]". done.
    iAssert (promiseSt p γ ε) with "[Hp Hps1 Htqstate Hres]" as "HpSt".
    { iRight. iExists enqs. iFrame.
      iSplit; last by done.
      iExists _. by iAssumption. }
    iMod (update_promiseInv_inner with "[HpInvIn Hε HpSt]") as "(HpInvIn & #Hmem)"; first by iFrame.
    iModIntro.
    iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
    iSplitL "Hclose". iApply "Hclose".
    iModIntro. iFrame.
    iExists p, γ, ε. iFrame. by auto.
  Qed.
  
  Lemma ewp_new_context init (I : val -> iProp Σ) :
    I init ⊢ EWP new_context init {{ tlv, ∃ (ℓtlv : loc), ⌜ tlv = #ℓtlv ⌝ ∗ isFiberContext ℓtlv I }}.
  Proof.
    iIntros "HI". rewrite /new_context.
    ewp_pure_steps.
    iApply ewp_alloc.
    iIntros "!>" (ℓtlv) "Htlv".
    iModIntro.
    iExists ℓtlv.
    iSplit; first by done.
    iExists init. by iFrame.
  Qed.
    
  Lemma ewp_next fargs γ ℓres q Ψ Φ :
  ⊢ fiberResources fargs -∗ 
    is_queue_reader queueN (ready fargs γ q) q -∗
    mainResult resultN γ ℓres Φ  -∗
      EWP (next #ℓres q) <| Ψ |> {{ _, fiberResources fargs ∗ ▷ is_queue_reader queueN (ready fargs γ q) q ∗ promise_state_done γ #() }}.
  Proof. 
    iIntros "HfRes Hq #HmRes".
    iLöb as "IH".
    unfold next. ewp_pure_steps. 
    ewp_bind_rule; simpl.
    iApply ewp_os_prot_mono; [by iApply iEff_le_bottom|].
    iApply (ewp_mono with "[Hq]"); [iApply (queue_pop_spec with "Hq")|].
    iIntros (y) "(Hq & [->|(%k & -> & Hk)]) !>".
    - (* queue is empty *) 
      ewp_pure_steps.
      ewp_bind_rule; simpl.
      iApply (ewp_atomic ⊤ (⊤ ∖ ↑resultN)).
      iMod (inv_acc with "HmRes") as "([(Hres & Hwaiting)|(%v & Hres & #Hdone & #Hv)] & Hclose)"; first by done.
      + (* Main fiber is not done. Busy wait. *)
        iApply (ewp_load with "Hres").
        iIntros "!> !> Hres !>".
        iMod ("Hclose" with "[Hres Hwaiting]") as "_".
        { iLeft; by iFrame. }
        iModIntro.
        do 4 ewp_value_or_step. 
        by iApply ("IH" with "HfRes Hq"). 
      + (* Main fiber is done. *)
        iApply (ewp_load with "Hres").
        iIntros "!> !> Hres !>".
        iMod ("Hclose" with "[Hres]") as "_".
        { iRight; iExists _; by iFrame "Hres Hdone Hv". }
        iModIntro.
        ewp_pure_steps. 
        by iFrame "HfRes Hq Hdone".
    - (* queue has a continuation *)
      ewp_pure_steps.
      rewrite ready_unfold /ready_pre.
      iSpecialize ("Hk" with "HfRes Hq").
      iApply ewp_os_prot_mono. { by iApply iEff_le_bottom. } 
      by iApply "Hk".
  Qed.

  Lemma ewp_fork (fargs : fiberResourcesArgs) (e : val) :
  ⊢ fiberResources fargs -∗ 
    (fiberResources fargs -∗ EWP e #() <| Coop fargs |> {{ _, fiberResources fargs }}) -∗
      EWP (fork #fargs.1 e) <| Coop fargs |> {{ _, fiberResources fargs }}.
  Proof.
    destruct fargs as [ℓtlv I]; simpl.
    iIntros "HfRes He". rewrite /fork. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_FORK. iLeft.
    iExists e. iSplit; first by done. iFrame.
    by iIntros (_) "$".
  Qed.

  Lemma ewp_suspend (fargs : fiberResourcesArgs) (f : val) (W: val → iProp Σ) (S: iProp Σ) :
  ⊢ fiberResources fargs -∗
    (∀ (waker: val),
      (∀ (v: val), W v -∗ (EWP (waker v) <| ⊥ |> {{_, True}}) ) -∗
      ( EWP (f waker) <| ⊥ |> {{_, □ S }}) ) -∗
      EWP (suspend f) <| Coop fargs |> {{ v, fiberResources fargs ∗ W v ∗ S }}.
  Proof.
    iIntros "HfRes He". rewrite /suspend. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_SUSPEND. iRight; iLeft.
    iExists f, W, S. iSplit; [done|]. iFrame.
    by iIntros (v) "$".
  Qed.

  Lemma ewp_yield (fargs : fiberResourcesArgs) :
  ⊢ fiberResources fargs -∗
      EWP (yield #()) <| Coop fargs |> {{ _, fiberResources fargs }}.
  Proof.
    iIntros "HfRes".
    rewrite /yield. ewp_pure_steps.
    iApply (ewp_mono with "[HfRes]").
    { iApply (ewp_suspend _ _ (λ _, True)%I True with "HfRes").
      iIntros (waker) "Hwaker". 
      iSpecialize ("Hwaker" $! #() with "[//]").
      ewp_pure_steps.
      iApply (ewp_mono with "[Hwaker]"); [iApply "Hwaker"|].
      iIntros (_) "_ !>". by done. }
    by iIntros (?) "[$ _] !>".
  Qed.
  
  Lemma ewp_get_context fargs : 
  ⊢ EWP (get_context #()) <| Coop fargs |> {{ tlv, ⌜ tlv = #fargs.1 ⌝ }}.
  Proof.
    destruct fargs as [ℓtlv I]; simpl.
    iIntros. rewrite /get_context. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_GET_CONTEXT. iRight; iRight.
    iExists #(). iSplit; [done|]. iSplit; [done|].
    iIntros (?) "_". 
    by done.
  Qed.
  
  Lemma ewp_await_callback (p: loc) (wakers: val) γ ε Φ:
  ⊢ promiseInv -∗ 
    suspension_permit -∗ 
    isMember p γ ε -∗ 
    isPromiseResult ε Φ -∗ 
    promise_cqs wakers -∗
      EWP (await_callback #p wakers) <| ⊥ |> {{f, 
        ∀ (waker: val), (∀ (v: val), (⌜ v = #() ⌝ ∗ ∃ v', promise_state_done γ v')%I -∗ EWP (waker v) <| ⊥ |> {{_, True }}) -∗
          ( EWP (f waker) <| ⊥ |> {{_, □ True }}) }}.
  Proof.
    iIntros "#HpInv HIsSus #Hmem #Hε #Hcqs". rewrite /await_callback. ewp_pure_steps.
    iIntros (waker) "Hwaker".
    ewp_pure_steps. 
    (* now we suspend waker*)
    iApply (ewp_bind' (AppRCtx _)); first by done. simpl.
    iApply (ewp_mono with "[HIsSus Hwaker]").
    { iApply (cqs_suspend_spec (∃ v', promise_state_done γ v') with "[HIsSus Hwaker]").
      iFrame.
      by done.
    }
    iIntros (res) "[-> | (% & % & -> & Hreq)] !>".
    { (* we are already resumed so return. *) 
      ewp_pure_steps. by done. }
    ewp_pure_steps. ewp_bind_rule. simpl.
    (* a.d. here we need to open the invariant to read the promise *)
    rewrite /promiseInv.
    iApply (ewp_atomic ⊤ (⊤ ∖ ↑promiseN)).
    iMod (inv_acc with "HpInv") as "(HpInvIn & Hclose)"; first by done.
    iMod (lookup_promiseInv_inner with "HpInvIn Hmem") as "[HpInvIn HpSt]".
    iModIntro.
    iDestruct "HpSt" as "[[%y (Hp&#Hps&%Φ'&#Hε'&#Hy)]| (%wakers' & Hp & Hps & Htqstate & Hres & #Hwakers') ]".
    - (* the promise was fulfilled *)
      iApply (ewp_load with "Hp"). 
      iIntros "!> Hp !>".
      iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
      iSplitL "Hclose". iApply "Hclose".
      iModIntro.
      iSplitR "Hreq".
      { iNext. iApply "HpInvIn".
        iLeft. iExists y. iFrame. iSplit; first done.
        iExists Φ'. by iSplit. }
      (* try cancellation. If it works we call the callback ourselves. *)
      ewp_pure_steps.
      iApply (ewp_bind' (IfCtx _ _)); first by done. simpl.
      iApply (ewp_mono with "[Hreq]").
      iApply (cqs_try_cancel_spec (∃ v', promise_state_done γ v') with "[Hreq]").
      by iFrame.
      iIntros (?) "(% & -> & Hk) !>".
      destruct b.
      2: {
        (* cancellation failed so we are not responsible anymore. *)
        ewp_pure_steps. by done.
      }
      ewp_pure_steps.
      iApply (ewp_mono _ _ (λ _, True)%I with "[Hk]").
      2: by done.
      iApply "Hk".
      rewrite /V'.
      iSplit; first done.
      iExists _. by iAssumption.
    - (* the promise is not yet fulifilled, our job is done and we don't do anything *)
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>". 
      iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
      iSplitL "Hclose". iApply "Hclose".
      iModIntro.
      iSplitL.
      + iNext. iApply "HpInvIn".
        iRight. iExists wakers'. by iFrame. 
      + ewp_pure_steps. by done.
  Qed.
  
  Lemma ewp_await (fargs : fiberResourcesArgs) (p: loc) Φ :
  ⊢ promiseInv -∗ 
    fiberResources fargs -∗ 
    isPromise p Φ -∗ 
      EWP (await #p) <| Coop fargs |> {{v, □ Φ v ∗ fiberResources fargs }}.
  Proof.
    iIntros "#HpInv HfRes (%γ & %ε & #Hmem & #Hε)". rewrite /await. 
    ewp_pure_steps. ewp_bind_rule. simpl.
    (* a.d. here we need to open the invariant to read the promise *)
    rewrite /promiseInv.
    iApply (ewp_atomic ⊤ (⊤ ∖ ↑promiseN)).
    iMod (inv_acc with "HpInv") as "(HpInvIn & Hclose)"; first by done.
    iMod (lookup_promiseInv_inner with "HpInvIn Hmem") as "[HpInvIn HpSt]".
    iModIntro.
    iDestruct "HpSt" as "[[%y (Hp&#Hps&%Φ'&#Hε'&#Hy)]| (%wakers & Hp & Hps & Htqstate & Hres & #Hwakers) ]".
    - (* the promise is already fulfilled *)
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>". 
      iPoseProof (saved_pred_agree ε _ _ Φ Φ' y with "Hε Hε'") as "Heqv".
      iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
      iSplitL "Hclose". iApply "Hclose".
      iModIntro.
      iSplitR "HfRes".
      iNext. iApply "HpInvIn". iLeft. iExists y. iFrame. iSplit; first by done.
      iExists Φ'. by iSplit.
      ewp_pure_steps. 
      iFrame. iModIntro.
      by iRewrite "Heqv".
    - (* the promise is not yet fulfilled, so we create a callback and perform the suspend effect.
         After the suspend returns, we know the promise is fulfilled. *)
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>".
      (* do the suspend registration *)
      iDestruct "Htqstate" as (n) "Htqstate".
      iMod (thread_queue_append' with "Hwakers Htqstate") as "(Htqstate & HIsSus)".
      iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
      iSplitL "Hclose". iApply "Hclose".
      iModIntro.
      iSplitR "HIsSus HfRes".
      iNext. iApply "HpInvIn". iRight. iExists wakers. iFrame.
      iSplit; last done. by iExists (S n). 
      ewp_pure_steps. 
      iApply (ewp_bind' (AppRCtx _)); first by done. simpl.
      iApply (ewp_mono with "[HIsSus]"). 
      iApply ewp_os_prot_mono. iApply iEff_le_bottom.
      iApply (ewp_await_callback with "HpInv HIsSus Hmem Hε Hwakers").
      iIntros (callback) "Hf !>".
      ewp_pure_steps.
      ewp_bind_rule. simpl.
      iApply (ewp_mono with "[Hf HfRes]").
      { iApply (ewp_suspend _ callback (λ v, ⌜ v = #() ⌝ ∗ ∃ v', promise_state_done γ v')%I True%I with "HfRes Hf"). }
      (* after we have performed the effect we get promise_state_done. *)
      iIntros (v) "(HfCtx & (-> & (%&Hps)) & _) !>".
      ewp_pure_steps. ewp_bind_rule. simpl.
      (* now we match on the promise again but this time we know it must be fulfilled *)
      iClear "Hwakers". clear wakers.
      iApply (ewp_atomic ⊤ (⊤ ∖ ↑promiseN)).
      iMod (inv_acc with "HpInv") as "(HpInvIn & Hclose)"; first by done.
      iMod (lookup_promiseInv_inner with "HpInvIn Hmem") as "[HpInvIn HpSt]".
      iDestruct "HpSt" as "[[%y (Hp&#Hps'&%Φ'&#Hε'&#Hy)]| (%wakers & Hp & Hps' & Htqstate & Hres & #Hwakers) ]";
        last by iDestruct (promise_state_disjoint γ _ with "[$]") as "HFalse".
      iDestruct (promise_state_done_agree with "Hps Hps'") as "->".
      iModIntro.
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>". 
      iPoseProof (saved_pred_agree ε _ _ Φ Φ' y with "Hε Hε'") as "Heqv".
      iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
      iSplitL "Hclose". iApply "Hclose".
      iModIntro.
      iSplitR "HfCtx".
      iNext. iApply "HpInvIn". iLeft.
      iExists y. iFrame. 
      iSplit; first done.
      iExists Φ'. by iSplit.
      ewp_pure_steps.
      iFrame.
      by iRewrite "Heqv".
  Qed.

  (* the wrapped function is passed via the FORK effect to the handler.
     the handler should then pass is_queue to wrapped_f so that it is able to change the run_queue.
     is_queue should be passed between client and handler the same as promiseInv, for every performed effect. *)
  Lemma ewp_fork_wrap (fargs : fiberResourcesArgs) (f: val) (p: loc) γ ε Φ :
  ⊢ promise_state_waiting γ -∗ 
    isMember p γ ε -∗ 
    isPromiseResult ε Φ -∗ 
    (fiberResources fargs -∗ EWP (f #()) <| Coop fargs |> {{v, □ Φ v ∗ fiberResources fargs }}) -∗
      EWP (fork_wrap_f f #p) <| ⊥ |> {{wrapped_f, 
          (* promiseInv and is_queue are passed here because they come from the effect handler *)
            promiseInv -∗
            fiberResources fargs -∗
              EWP (wrapped_f #()) <| Coop fargs |> {{_, fiberResources fargs }} }}.
  Proof.
    iIntros "Hps_start #Hmem #Hε Hf". 
    rewrite /fork_wrap_f. ewp_pure_steps.
    iIntros "#HpInv HfCtx". ewp_pure_steps.
    iSpecialize ("Hf" with "HfCtx").
    ewp_bind_rule. simpl. iApply (ewp_mono with "Hf"). 
    iIntros (v) "(#Hv & HfCtx) !>".
    ewp_pure_steps. ewp_bind_rule. simpl.
    (* a.d. here we need to open the invariant *)
    rewrite /promiseInv.
    iApply (ewp_atomic ⊤ (⊤ ∖ ↑promiseN)).
    iMod (inv_acc with "HpInv") as "(HpInvIn & Hclose)"; first by done.
    (* a.d. using the maybe unsound rule of getting the inner promise state *)
    iMod (lookup_promiseInv_inner with "HpInvIn Hmem") as "[HpInvIn HpSt]".
    iModIntro.
    iDestruct "HpSt" as "[[%y (Hp&#Hps&%Φ'&#Hε'&#Hy)]| (%wakers & Hp & Hps & Htqstate & Hres & #Hwakers) ]";
      first by iDestruct (promise_state_disjoint γ with "[$]") as "HFalse".
    iApply (ewp_load with "Hp").
    iIntros "!> Hp !>". 
    iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
    iSplitL "Hclose". iApply "Hclose".
    iModIntro.
    iSplitR "Hps_start HfCtx".
    iNext. iApply "HpInvIn". iRight. iExists wakers. by iFrame.
    ewp_pure_steps. ewp_bind_rule. simpl.
    (* now we change the logical promise state, but for that we need to open it again. *)
    iApply (ewp_atomic ⊤ (⊤ ∖ ↑promiseN)).
    iMod (inv_acc with "HpInv") as "(HpInvIn & Hclose)"; first by done.
    iMod (lookup_promiseInv_inner with "HpInvIn Hmem") as "[HpInvIn HpSt]".
    iDestruct "HpSt" as "[[%y (Hp&#Hps&%Φ'&#Hε'&#Hy)]| (%enqs' & Hp & Hps & Htqstate & Hres & #Henqs') ]";
      first by iDestruct (promise_state_disjoint γ with "[$]") as "HFalse".
    iMod (promise_state_join with "[$]") as "Hps".
    iMod (promise_state_fulfill with "Hps") as "#Hps".
    iModIntro. 
    iApply (ewp_store with "Hp"). iIntros "!> Hp !>".
    iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
    iSplitL "Hclose". iApply "Hclose".
    iModIntro.
    iSplitR "Htqstate Hres HfCtx".
    iNext. iApply "HpInvIn". iLeft. iExists v. iFrame. iSplit; first done.
    iExists Φ. by iSplit.
    ewp_pure_steps. ewp_bind_rule. simpl.
    iApply (ewp_mono with "[Htqstate Hres]"). 
    { iApply ewp_os_prot_mono. iApply iEff_le_bottom.
      iDestruct "Htqstate" as (n) "Htqstate".
      iApply (cqs_resume_all_spec (∃ v', promise_state_done γ v') with "[Htqstate Hres Hwakers]").
      iFrame. iSplit; first done. 
      iModIntro. iNext. by iExists _. }
    iIntros (?) "_ !>". by done.
  Qed.

  Lemma ewp_fork_promise (fargs : fiberResourcesArgs) (f: val) Φ :
  ⊢ promiseInv -∗
    fiberResources fargs -∗ 
    (fiberResources fargs -∗ EWP (f #()) <| Coop fargs |> {{v, □ Φ v ∗ fiberResources fargs }}) -∗
      EWP (fork_promise f) <| Coop fargs |> {{ y, 
        ∃ (p: loc), ⌜ y = #p ⌝ ∗ isPromise p Φ ∗ fiberResources fargs }}.
  Proof.
    iIntros "#HpInv HfRes Hf". rewrite /fork_promise. ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply ewp_mono; [iApply ewp_get_context|].
    iIntros (tlv) "-> !>".
    ewp_pure_steps.
    ewp_bind_rule; simpl.
    iApply ewp_mono. 
    iApply ewp_os_prot_mono. 
      by iApply iEff_le_bottom. 
    iApply (ewp_new_promise Φ with "HpInv").
    iIntros (v) "(%p & %γ & %ε & -> & Hps & #(Hmem & HRes)) !>".
    ewp_pure_steps.
    iApply (ewp_bind' (AppRCtx _)); first done. simpl.
    iApply (ewp_mono with "[Hf Hps]").
    { iApply ewp_os_prot_mono. iApply iEff_le_bottom.
      iApply (ewp_fork_wrap with "Hps Hmem HRes Hf"). }
    iIntros (wrapped_f) "Hwrapped_f !>".
    iSpecialize ("Hwrapped_f" with "HpInv").
    ewp_pure_steps.
    iApply (ewp_bind' (AppRCtx _)); first done. simpl.
    iApply (ewp_mono with "[Hwrapped_f HfRes]").
    iApply (ewp_fork with "HfRes Hwrapped_f"). 
    iIntros (?) "HfState !>".
    ewp_pure_steps. iExists p.
    iFrame. iSplit; first done.
    iExists γ, ε. by iSplit.
  Qed.

  Lemma ewp_execute (fargs : fiberResourcesArgs) γ ℓres Φ (q fiber : val) :
  ⊢ is_queue_reader queueN (ready fargs γ q) q -∗
    fiberResources fargs -∗
    mainResult resultN γ ℓres Φ -∗
    (fiberResources fargs -∗ EWP fiber #() <| Coop fargs |> {{ _, fiberResources fargs }}) -∗
      EWP execute q #ℓres #fargs.1 fiber {{_, fiberResources fargs ∗ ▷ is_queue_reader queueN (ready fargs γ q) q ∗ promise_state_done γ #() }}.
  Proof.
    iIntros "Hq HfRes #HmRes Hfiber".
    iDestruct (is_queue_reader_is_queue with "Hq") as "[#Hq Hqr]".
    rewrite /execute.
    do 6 ewp_value_or_step.
    iLöb as "IH" forall (fiber).
    iSpecialize ("Hfiber" with "HfRes").
    ewp_pure_steps.
    iApply (ewp_deep_try_with with "Hfiber").
    iLöb as "IH_handler".
    rewrite deep_handler_unfold.
    iSplit; [|iSplit]; last (by iIntros (??) "HFalse"; rewrite upcl_bottom).
    (* Return branch. *)
    - iIntros (?) "HfRes".
      ewp_pure_steps. 
      by iApply (ewp_next with "HfRes Hqr").
    (* Effect branch. *)
    - iIntros (request k). rewrite upcl_Coop upcl_FORK upcl_SUSPEND upcl_GET_CONTEXT.
      iIntros "[(%e & -> & (HfRes & He) & Hk)
               |[(%suspender & %P & %Q & -> & (HfCtx & Hsuspender) & Hk)
               |(%_ & -> & _ & Hk)]]".
      (* Fork. *)
      + ewp_pure_steps.
        (* change queue state to register a push. *)
        ewp_bind_rule; simpl.
        iApply (ewp_mono with "[Hqr]"); [iApply (queue_register_push_Q queueN True%I with "Hqr")|].
        iIntros (?) "(Hfulfill & % & % & Hpush) !>".
        ewp_pure_steps.
        (* prepare the push, this one does not have a precondition bc the fiber is immediately ready. *)
        iApply (ewp_bind' (AppRCtx _)); first by done. simpl.
        iApply (ewp_mono with "[Hk Hpush]").
        { iApply (queue_push_spec with "Hq Hpush [Hk]").
          iIntros "!> _".
          rewrite ready_unfold /ready_pre.
          iIntros "HfRes Hqr". ewp_pure_steps.
          iSpecialize ("Hk" $! #() with "HfRes").
          (* iApply (ewp_mono _ _ (λ _, isMainResult θ ℓres ∗ (∃ v : valO, promise_state_done θ v ∗ □ Φ v))%I (λ _, isMainResult θ ℓres ∗ (∃ v : valO, promise_state_done θ v))%I with "[Hk Hres]").
          2: {
            iIntros (?) "($ & (% & Hdone & _)) !>".
            by iExists _.
          } *)
          iApply "Hk". iNext. 
          rewrite -deep_handler_unfold.
          iApply "IH_handler".
          by iAssumption.
        }
        iIntros (?) "_ !>". do 3 ewp_value_or_step.
        (* fulfill the Q *)
        ewp_bind_rule; simpl.
        iApply (ewp_mono with "[Hfulfill]").
        { iApply (queue_fulfill_Q with "Hq Hfulfill []").
          done. }
        iIntros (?) "Hqr !>". do 3 ewp_value_or_step.
        by iApply ("IH" $! e with "HfRes He Hqr").
      (* Suspend/GetContext. *)
      + do 12 ewp_value_or_step.
        (* prepare the push, this one must take the Q as a precondition. Not sure if it's okay to use the string "v" in the definition of the value. *)
        ewp_bind_rule; simpl.
        iApply (ewp_mono with "[Hqr]"); [iApply (queue_register_push_Q queueN Q with "Hqr")|].
        iIntros (?) "(Hfulfill & % & % & Hpush) !>".
        do 3 ewp_value_or_step.
        ewp_bind_rule; simpl.
        (* here we bind the creation of waker. Now we should prove a spec for it. *)
        set (Hwaker := (λ (waker: val), (∀ (v : val),
              P v -∗
              EWP waker v <| ⊥ |> {{ _, True }})%I)).
        iApply (ewp_mono _ _ Hwaker with "[Hpush Hk]").
        { 
          rewrite /Hwaker.
          ewp_pure_steps.
          iIntros (?) "HP".
          ewp_pure_steps.
          iApply (queue_push_spec with "Hq Hpush").
          iIntros "!> HQ".
          rewrite ready_unfold /ready_pre.
          iClear "Hq".
          iIntros "HfRes Hq". ewp_pure_steps.
          iSpecialize ("Hk" $! v0 with "[$]").
          iApply "Hk". iNext.
          iSpecialize ("IH_handler" with "Hq").
          rewrite -deep_handler_unfold.
          iApply "IH_handler".
        }
        iIntros (waker) "Hwaker !>".
        rewrite /Hwaker.
        iSpecialize ("Hsuspender" $! waker with "Hwaker").
        ewp_pure_steps.
        ewp_bind_rule; simpl.
        iApply (ewp_mono with "Hsuspender").
        iIntros (?) "HQ !>". ewp_pure_steps.
        (* fulfill the Q *)
        ewp_bind_rule; simpl.
        iApply (ewp_mono with "[Hfulfill HQ]");
          [iApply (queue_fulfill_Q with "Hq Hfulfill HQ")|].
        iIntros (?) "Hqr !>".
        ewp_pure_steps.
        by iApply (ewp_next with "HfCtx Hqr").
      + do 12 ewp_value_or_step.
        iSpecialize ("IH_handler" with "Hqr").
        iApply ("Hk" $! #() with "[//]").
        rewrite -deep_handler_unfold.
        iApply "IH_handler".
  Qed.
End verification.

Section verification_run.
  Context `{!heapGS Σ, !promiseGS Σ, !savedPredG Σ val, !deferredGpreS Σ, !savedPropG Σ}.
  Context (resultN: namespace).

  Lemma ewp_run (init main : val) I Φ :
  ⊢ I init -∗ 
    (∀ ℓtlv, fiberResources (ℓtlv, I) -∗ EWP main #() <| Coop (ℓtlv, I) |> {{ v, □ Φ v ∗ fiberResources (ℓtlv, I) }}) -∗
      EWP run init main {{ v, □ Φ v }}.
  Proof.
    iIntros "HI Hmain". unfold run. ewp_pure_steps.
    (* Main fiber result *)
    ewp_bind_rule; simpl. 
    iApply ewp_mono; [iApply (ewp_new_scheduler_result resultN Φ)|].
    iIntros (vres) "(%ℓres & %γ & -> & #HmRes & Hwaiting) !>".
    ewp_pure_steps.
    (* Initial fiber context. *) 
    ewp_bind_rule. simpl. iApply (ewp_mono with "[HI]"). 
    { by iApply (ewp_new_context with "HI"). }
    iIntros (tlv) "(%ℓtlv & -> & HfCtx) !>".
    (* a.d. We must do this up here so that ∀ δ does not appear in IH.
       a.d. TODO can we speciaize Hℓstate, too? *)
    set (fargs := (ℓtlv, I) : fiberResourcesArgs).
    iSpecialize ("Hmain" $! ℓtlv).
    ewp_pure_steps.
    ewp_bind_rule; simpl. 
    iApply ewp_mono; [iApply (queue_create_spec queueN)|].
    iIntros (q) "(%H & Hqcreate) !>". 
    (* a.d. it's kind of interesting that ready is now also scheduler specific. But it's nice to know that
       we cannot schedule a fiber in a different scheduler. *)
    iSpecialize ("Hqcreate" $! (ready fargs γ q)).
    iDestruct "Hqcreate" as ">(#Hq & Hqr)".
    ewp_pure_steps.
    iApply (ewp_bind' (AppRCtx _)); [by done|simpl].
    iApply (ewp_mono with "[Hmain Hqr HfCtx Hwaiting]").
    { iApply (ewp_execute resultN with "Hqr HfCtx HmRes [Hmain Hwaiting]").
      iIntros "HfRes".
      ewp_pure_steps.
      iSpecialize ("Hmain" with "HfRes").
      ewp_bind_rule; simpl. iApply (ewp_mono with "Hmain").
      iIntros (vres) "(#Hvres & HfRes) !>".
      ewp_pure_steps. 
      iApply (ewp_atomic ⊤ (⊤ ∖ ↑resultN)).
      iMod (inv_acc with "HmRes") as "([(Hres & >Hwaiting')|(%v & _ & >Hdone & _)] & Hclose)"; first by done.
      2: {
        by iDestruct (promise_state_disjoint with "[$]") as "%HFalse".
      }
      iApply (ewp_store with "Hres").
      (* update main_running to main_done *)
      iIntros "!> !> Hres !>".
      iMod (promise_state_join with "[$]") as "Hγ".
      iMod (promise_state_fulfill _ #() with "Hγ") as "#Hdone".
      iMod ("Hclose" with "[Hres]") as "_".
      { iNext. iRight. iExists vres. 
        by iFrame "Hvres Hdone". }
      by iFrame. }
    iIntros (?) "(_ & _ & #Hdone) !>".
    ewp_pure_steps.
    ewp_bind_rule; simpl.
    iApply (ewp_atomic ⊤ (⊤ ∖ ↑resultN)).
    iMod (inv_acc with "HmRes") as "([(Hres & >Hwaiting')|(%vres & Hres & >#Hdone' & #Hvres)] & Hclose)"; first by done.
    1: {
      by iDestruct (promise_state_disjoint with "[$]") as "%HFalse".
    }
    iApply (ewp_load with "Hres").
    iIntros "!> !> Hres !>".
    iMod ("Hclose" with "[Hres]") as "_".
    { iNext. iRight. iExists vres. 
      by iFrame "Hvres Hdone". }
    iModIntro.
    ewp_pure_steps.
    by iFrame "Hvres".
  Qed.
End verification_run.

(* ========================================================================== *)
(** * Specification. *)

(* TODO can we do this without the AsyncCompLib? *)
Section specification.
  Context `{!heapGS Σ}.

  Definition run_spec (init main : val) (I Φ : val -> iProp Σ)  :=
    I init -∗ 
    (∀ ℓres, fiberResources (ℓres, I) -∗ EWP main #() <| Coop (ℓres, I) |> {{ v, □ Φ v ∗ fiberResources (ℓres, I) }}) ={⊤}=∗
      EWP run init main <| ⊥ |> {{ v, □ Φ v }}.
End specification.

Section closed_proof.
  Context `{!heapGS Σ, !promiseGpreS Σ, !savedPredG Σ val, !savedPropG Σ, !deferredGpreS Σ}.
  Context (resultN : namespace).

  Lemma promiseInv_inner_init :
    ⊢ |==> ∃ _ : promiseGS Σ, promiseInv_inner.
  Proof.
    iIntros. iMod (own_alloc (● (∅ : gmap (loc * gname * gname) _))) as (γ) "HI";
      first by rewrite auth_auth_valid.
    iExists {| promise_inG := _; promise_name := γ; |}.
    iModIntro.
    iExists ∅. rewrite /isPromiseMap. by iFrame.
  Qed.
    
  Lemma promiseInv_init :
    ⊢ |={⊤}=> ∃ _ : promiseGS Σ, promiseInv.
  Proof.
    iIntros.
    iMod (promiseInv_inner_init) as "(%pg & Hinner)".
    iMod (inv_alloc promiseN ⊤ promiseInv_inner with "[Hinner]").
    by done. by iExists pg.
  Qed.

  Theorem run_correct init main (I Φ : val -> iProp Σ) : run_spec init main I Φ.
  Proof.
    rewrite /run_spec.
    iIntros "Hinit He".
    iMod promiseInv_init as "[%HpromiseGS #HpInv]".
    iModIntro.
    iApply (ewp_run resultN init main I Φ with "Hinit He").
  Qed.
End closed_proof.

(* The only assumptions are from the CQS formalization and the deferred queue.
 * TODO port the deferred queue to this Iris version. 
 * TODO port the CQS to this Iris version. *)
Print Assumptions run_correct.