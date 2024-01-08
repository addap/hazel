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
From program_logic Require Import reasoning_rules.
From case_studies Require Import list_lib .

From case_studies.eio Require Import atomics concurrent_queue cqs.

(* ========================================================================== *)
(** * Implementation of the Scheduler. *)

Notation Fork state e := (InjL (Pair state e)) (only parsing).
Notation Suspend f := (InjR (InjL f)) (only parsing).
Notation GetContext := (InjR (InjR #())) (only parsing).

Notation Fork' state e := (InjLV (PairV state e)) (only parsing).
Notation Suspend' f := (InjRV (InjLV f)) (only parsing).
Notation GetContext' := (InjRV (InjRV #())) (only parsing).

Notation Done y := (InjL y) (only parsing).
Notation Waiting ws := (InjR ws) (only parsing).

Notation Done' y := (InjLV y) (only parsing).
Notation Waiting' ws := (InjRV ws) (only parsing).

Section implementation.
  Context `{!heapGS Σ, !ListLib Σ}.

  Definition new_promise : val := (λ: <>,
    ref (Waiting (cqs_new #()))
  )%V.
  Definition new_fiber_state : val := (λ: <>,
    ref #0
  )%V.
  Definition fork : val := (λ: "state" "f", do: (Fork "state" "f"))%V.
  Definition suspend : val := (λ: "f", do: (Suspend "f"))%V.
  Definition get_context : val := (λ: <>, do: GetContext)%V.

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
    | (* Waiting: *) InjR "ws" =>
        (* First set the promise to Done, so that we can update the logical promise state and call enqueue *)
        "p" <- Done "v";;
        cqs_resume_all "ws"
    end))%V.

  (* fork a new fiber "f" and return a promise to get the result. *)
  Definition fork_promise : val := (λ: "f", 
    let: "state" := get_context #() in
    let: "p" := new_promise #() in
    let: "wrapped_f" := fork_wrap_f "f" "p" in
    fork "state" "wrapped_f";;
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
    
  Definition run : val := (λ: "main",
    let: "initial_state" := new_fiber_state #() in
    let: "q" := queue_create #() in
    let: "fulfill" := rec: "fulfill" "state" "f" :=
      deep-try: "f" #() with
        effect (λ: "request" "k",
          match: "request" with
            (* Fork: *) InjL "statef" =>
              let: "fork_state" := Fst "statef" in
              let: "fork_f" := Snd "statef" in
              queue_push "q" (λ: <>, "k" #());;
              "fulfill" "fork_state" "fork_f"
          | (* Suspend/GetContext: *) InjR "e1" =>
            match: "e1" with
              (* Suspend: *) InjL "suspender" =>
                (* a.d. probably the most complicated line 
                When waker is called with a value v, a closure calling the continuation with v is put into the run_queue. 
                suspender can either put waker somewhere that causes it to be called later or just call it directly. *)
                let: "waker" := (λ: "v", queue_push "q" (λ: <>, "k" "v")) in
                "suspender" "waker";;
                next "q"
            | (* GetContext: *) InjR <> =>
                "k" "state"
            end
          end)
      | return (λ: <>, next "q")
      end
    in
    "fulfill" "initial_state" "main"
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
  torchG :> inG Σ (csumR fracR (agreeR unitO));
  stateG :> inG Σ (agreeR locO);
}.
  
(* A concrete instance of [Σ] for which the assumption [promisesGS Σ] holds. *)
Definition promiseΣ := #[
  GFunctor (authRF
    (gmapURF (loc * gname * gname) unitR));
  (* GFunctor (authRF
    (gmapURF gname (agreeR locO))); *)
  GFunctor (csumR fracR (agreeR unitO));
  GFunctor (agreeR locO)
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
  Context `{!heapGS Σ, !promiseGS Σ, !savedPredG Σ val}.

  (* ------------------------------------------------------------------------ *)
  (* Definitions. *)

  (* Promise state starts as whole, then it's split up and half is saved in the invariant and half is kept by the fiber.
     When the fiber is done, it updates the state to done. *)
  Definition promise_state_whole γ := own γ (Cinl 1%Qp).
  Definition promise_state_waiting γ := own γ (Cinl (1/2)%Qp).
  Definition promise_state_done γ := own γ (Cinr (to_agree ())).
  
  (* a.d. TODO I wonder if we can reformulate isMember so that we don't even need isState.
     We need it so that we have a single gname γ to identify each thread for use in the GetContext effect.
     *)
  Definition isFiberState δ (l: loc): iProp Σ :=
    own δ (to_agree l).
    
  Definition fiberState δ (l : loc) : iProp Σ := 
    (isFiberState δ l ∗ ∃ (n:nat), l ↦ #n)%I.

  (* This resource is always held by the active fiber, so we need to pass it in and out of effects 
     and need it as a precondition of a ready fiber. *)
  Definition fiberContext δ := (∃ (l : loc), fiberState δ l)%I.
    
  (* Fragment of the promise map. *)
  Definition isMember p γ ε :=
    own promise_name (◯ {[(p, γ, ε) := tt]}).
  
  (* Saved predicate for the promise result. *)
  Definition isPromiseResult ε (Φ : val -d> iPropO Σ) := 
    saved_pred_own ε Φ.

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
          p ↦ Done' y ∗ promise_state_done γ ∗ 
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

  (* Now ready is just a predicate on a continuation k, that k is safe to execute under the assumption
     that promiseInv holds. *)
  Definition ready (δ : gname) (k: val) : iProp Σ := (
    fiberContext δ -∗ promiseInv -∗ EWP (k #()) {{ _, True }}
  )%I.

  Definition promiseSt p γ ε: iProp Σ :=
    ((* Fulfilled: *) ∃ y,
       p ↦ Done' y ∗ promise_state_done γ ∗
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
       p ↦ Done' y ∗ promise_state_done γ ∗
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

  End promise_state.
  
  Section fiber_state.
    Global Instance isFiberState_persistent δ l: Persistent (isFiberState δ l).
    Proof. by apply _. Qed.

    Lemma fiber_state_create (l: loc) : ⊢ |==> ∃ δ, isFiberState δ l.
    Proof. by iMod (own_alloc (to_agree l)) as (δ) "Hfs"; last iExists δ. Qed.
    
    Lemma is_fiber_state_agree (l l' : loc) δ : 
      isFiberState δ l -∗ isFiberState δ l' -∗ ⌜ l = l' ⌝.
    Proof.
      iIntros "H H'". 
      iCombine "H H'" as "H".
      iPoseProof (own_valid with "H") as "%".
      iPureIntro.
      by apply to_agree_op_inv_L.
    Qed.

    Lemma fiber_state_agree (l l' : loc) δ : 
      fiberState δ l -∗ isFiberState δ l' -∗ ⌜ l = l' ⌝ ∗ fiberState δ l.
    Proof.
      iIntros "(#H & HRest) #H'". 
      iSplitR; first by iApply is_fiber_state_agree.
      by iFrame.
    Qed.
    
    Lemma fiber_context_agree (l : loc) δ :
      fiberContext δ -∗ isFiberState δ l -∗ fiberState δ l.
    Proof.
      iIntros "(% & HfState) H".
      by iDestruct (fiber_state_agree with "HfState H") as (->) "HfState".
    Qed.
  End fiber_state.

  (* Logical rules governing the predicate [ready]. *)
  Section ready.

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
  
  Notation pEff := (gnameO -d> iEffO) (only parsing).
  
  Definition FORK_pre (Coop : pEff) (δ : gname): iEff Σ :=
    >> (ℓstate : loc) e >> !(Fork' #ℓstate e) {{fiberState δ ℓstate ∗ ▷ (fiberContext δ -∗ EWP e #() <|Coop δ |> {{_, fiberContext δ}}) }};
    << (_: val) << ?(#())        {{ fiberState δ ℓstate }} @ OS.

      (* a.d. TODO I think I can delete promiseInv from SUSPEND *)
  Definition SUSPEND (δ : gname) : iEff Σ :=
    >> (f: val) (P: val → iProp Σ) >> !(Suspend' f) {{
      (* We call suspender with the waker function and waker receives a value satisfying P. *)
        ( (∀ (waker: val),
          (∀ (v: val), P v -∗  (EWP (waker v) <| ⊥ |> {{_, True }}) ) -∗
          promiseInv -∗ (▷ EWP (f waker) <| ⊥ |> {{_, True  }}) ) 
      ∗
        fiberContext δ ∗ promiseInv)%I
    }};
    << y           << ?(y)         {{ P y ∗ fiberContext δ }} @ OS.

  Definition GET_CONTEXT (δ: gname ): iEff Σ :=
    >> (_: val) >> !(GetContext') {{ True }};
    << (state : loc) << ?(#state) 
        {{isFiberState δ state}} @ OS.

  Definition Coop_pre : pEff → pEff := (λ Coop,
    λ δ, FORK_pre Coop δ <+> SUSPEND δ <+> GET_CONTEXT δ
  )%ieff.

  Local Instance Coop_pre_contractive : Contractive (Coop_pre).
  Proof.
    intros n'.
    rewrite /Coop_pre /SUSPEND /FORK_pre /GET_CONTEXT=> n Coop Coop' HCoop.
    by repeat (apply ewp_ne||apply iEffPre_base_ne||f_contractive||f_equiv).
  Qed.
  Definition Coop_def : (gname → iEff Σ) := fixpoint Coop_pre.
  Definition Coop_aux : seal Coop_def. Proof. by eexists. Qed.
  Definition Coop := Coop_aux.(unseal).
  Definition Coop_eq : Coop = Coop_def := Coop_aux.(seal_eq).
  Global Lemma Coop_unfold δ : Coop δ  ≡ Coop_pre Coop δ.
  Proof. rewrite Coop_eq /Coop_def.
         by apply (fixpoint_unfold (Coop_pre)).
  Qed.
  Definition FORK := FORK_pre Coop.

  Lemma upcl_Coop v Φ' δ:
    iEff_car (upcl OS (Coop δ)) v Φ' ⊣⊢
      iEff_car (upcl OS (FORK δ)) v Φ' ∨
      iEff_car (upcl OS (SUSPEND δ)) v Φ' ∨
      iEff_car (upcl OS (GET_CONTEXT δ)) v Φ'.
  Proof.
    transitivity (iEff_car (upcl OS (Coop_pre Coop δ)) v Φ').
    - iApply iEff_car_proper. by rewrite {1}Coop_unfold.
    - by rewrite upcl_sum upcl_sum (upcl_tele' [tele _ _] [tele _]) //.
  Qed.

  Lemma upcl_FORK δ v Φ' :
    iEff_car (upcl OS (FORK δ)) v Φ' ≡
      (∃ (ℓstate: loc) e, ⌜ v = Fork' #ℓstate e ⌝ ∗ (fiberState δ ℓstate ∗ ▷ (fiberContext δ -∗ EWP e #() <|Coop δ|> {{_, fiberContext δ }})) ∗
            (∀ (_ : val), fiberState δ ℓstate -∗ Φ' #()))%I.
  Proof. by rewrite /FORK (upcl_tele' [tele _ _] [tele _]). Qed.

  Lemma upcl_SUSPEND δ v Φ' :
    iEff_car (upcl OS (SUSPEND δ)) v Φ' ≡
      (∃ (f : val) (P: val → iProp Σ), ⌜ v = Suspend' f ⌝ 
      ∗ 
      (* the big precondition of the protocol *)
        ( (∀ (waker: val),
          (∀ (v: val), P v -∗ (EWP (waker v) <| ⊥ |> {{_, True }}) ) -∗
          promiseInv -∗ (▷ EWP (f waker) <| ⊥ |> {{_, True }}) )
      ∗
          fiberContext δ ∗ promiseInv) 
      ∗
          (∀ v, (P v ∗ fiberContext δ) -∗ Φ' v))%I.
  Proof. by rewrite /SUSPEND (upcl_tele' [tele _ _] [tele _]). Qed.

  Lemma upcl_GET_CONTEXT δ v Φ' :
    iEff_car (upcl OS (GET_CONTEXT δ)) v Φ' ≡ 
      (∃ (_: val), ⌜ v = GetContext' ⌝ ∗ True ∗
        (∀ (ℓstate : loc), isFiberState δ ℓstate -∗ Φ' #ℓstate)
      )%I.
  Proof. by rewrite /GET_CONTEXT (upcl_tele' [tele _] [tele _]). Qed.

End protocol_coop.


(* ========================================================================== *)
(** * Verification. *)

Section verification.
  Context `{!heapGS Σ, !promiseGS Σ, !ListLib Σ, !savedPredG Σ val}.

  Lemma ewp_new_promise Φ :
    promiseInv ⊢ EWP (new_promise #()) {{ y,
        ∃ p γ ε, ⌜ y = #(p : loc) ⌝ ∗ promise_state_waiting γ ∗ isMember p γ ε ∗ isPromiseResult ε Φ}}.
  Proof.
    iIntros "HpInv".
    unfold new_promise. ewp_pure_steps. ewp_bind_rule. simpl.
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
    iMod (saved_pred_alloc Φ) as "[%ε #Hε]".
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
  
  Lemma ewp_new_fiber_state :
    ⊢ EWP new_fiber_state #() {{ state, ∃ (ℓstate : loc) (n: nat), ⌜ state = #ℓstate ⌝ ∗ ℓstate ↦ #n }}.
  Proof.
    iIntros. rewrite /new_fiber_state.
    ewp_pure_steps. iApply ewp_alloc.
    iIntros "!>" (ℓstate) "Hstate !>".
    iExists _, 0. by iFrame. 
  Qed.
    
  Lemma ewp_next δ q Ψ :
    fiberContext δ -∗
    promiseInv -∗
      is_queue q (ready δ) -∗
         EWP (next q) <| Ψ |> {{ _, True }}.
  Proof.
    iIntros "HfCtx HpInv #Hq". unfold next. ewp_pure_steps. ewp_bind_rule.
    iApply ewp_mono; [iApply (queue_pop_spec with "Hq")|].
    simpl. iIntros (y) "[->|(%k & -> & Hk)] !>".
    - (* queue is empty *) 
      by ewp_pure_steps.
    - (* queue has a continuation *)
      ewp_pure_steps.
      rewrite /ready.
      iSpecialize ("Hk" with "HfCtx HpInv").
      iApply ewp_os_prot_mono. { by iApply iEff_le_bottom. } { done. }
  Qed.

  Lemma ewp_fork (ℓstate : loc) (e : val) δ :
    fiberState δ ℓstate ∗ (fiberContext δ -∗ EWP e #() <| Coop δ|> {{ _, fiberContext δ }})
  ⊢
      EWP (fork #ℓstate e) <| Coop δ |> {{ _, fiberState δ ℓstate }}.
  Proof.
    iIntros "(Hfstate & He)". rewrite /fork. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_FORK. iLeft.
    iExists ℓstate, e. iSplit; [done|]. iFrame.
    iIntros (_) "H". by done.
  Qed.

  Lemma ewp_suspend (f : val) (P: val → iProp Σ) δ :
      ( (∀ (waker: val),
        (∀ (v: val), P v -∗ (EWP (waker v) <| ⊥ |> {{_, True}}) ) -∗
        promiseInv -∗ (▷ EWP (f waker) <| ⊥ |> {{_, True }})) 
    ∗
      fiberContext δ ∗ promiseInv) 
    ⊢
      EWP (suspend f) <| Coop δ |> {{ v, P v ∗ fiberContext δ }}.
  Proof.
    iIntros "(He & HpInv)". rewrite /suspend. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_SUSPEND. iRight; iLeft.
    iExists f, P. iSplit; [done|]. iFrame.
    iIntros (v) "Hv". by iFrame.
  Qed.
  
  Lemma ewp_get_context δ : 
    ⊢ EWP (get_context #()) <| Coop δ |> {{ state, ∃ (ℓstate: loc), ⌜ state = #ℓstate ⌝ ∗ isFiberState δ ℓstate }}.
  Proof.
    iIntros. rewrite /get_context. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_GET_CONTEXT. iRight; iRight.
    iExists #(). iSplit; [done|]. iSplit; [done|].
    iIntros (?) "H". iExists ℓstate. iSplit; first done.
    done.
  Qed.
  
  Lemma ewp_await_callback (p: loc) (wakers: val) γ ε Φ:
    suspension_permit ∗ isMember p γ ε ∗ isPromiseResult ε Φ ∗ promise_cqs wakers 
  ⊢
    EWP (await_callback #p wakers) <| ⊥ |> {{f, 
      ∀ (waker: val), (∀ (v: val), (⌜ v = #() ⌝ ∗ promise_state_done γ)%I -∗ EWP (waker v) <| ⊥ |> {{_, True }}) -∗
      promiseInv -∗ 
        (▷ EWP (f waker) <| ⊥ |> {{_, True }}) }}.
  Proof.
    iIntros "(HIsSus & #Hmem & #Hε & #Hcqs)". rewrite /await_callback. ewp_pure_steps.
    iIntros (waker) "Hwaker #HpInv". iNext.
    ewp_pure_steps. 
    (* now we suspend waker*)
    iApply (ewp_bind' (AppRCtx _)); first by done. simpl.
    iApply (ewp_mono with "[HIsSus Hwaker]").
    { iApply (cqs_suspend_spec (promise_state_done γ) with "[HIsSus Hwaker]").
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
      iApply (cqs_try_cancel_spec (promise_state_done γ) with "[Hreq]").
      by iFrame.
      iIntros (?) "(% & -> & Hk) !>".
      destruct b.
      2: {
        (* cancellation failed so we are not responsible anymore. *)
        ewp_pure_steps. by done.
      }
      ewp_pure_steps.
      iApply "Hk". by iSplit.
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
  
  Lemma ewp_await (p: loc) Φ δ :
    fiberContext δ ∗ promiseInv ∗ isPromise p Φ ⊢ 
      EWP (await #p) <| Coop δ |> {{v, □ Φ v ∗ fiberContext δ}}.
  Proof.
    iIntros "(HfCtx & #HpInv & %γ & %ε & #Hmem & #Hε)". rewrite /await. 
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
      iPoseProof (saved_pred_agree ε Φ Φ' y with "Hε Hε'") as "Heqv".
      iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
      iSplitL "Hclose". iApply "Hclose".
      iModIntro.
      iSplitR "HfCtx".
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
      iSplitR "HIsSus HfCtx".
      iNext. iApply "HpInvIn". iRight. iExists wakers. iFrame.
      iSplit; last done. by iExists (S n). 
      ewp_pure_steps. 
      iApply (ewp_bind' (AppRCtx _)); first by done. simpl.
      iApply (ewp_mono with "[HIsSus]"). 
      iApply ewp_os_prot_mono. iApply iEff_le_bottom.
      iApply (ewp_await_callback with "[HIsSus]"). iFrame. 
      iSplit; first done.
      iSplit; first done.
      by done.
      iIntros (callback) "Hf !>".
      ewp_pure_steps.
      ewp_bind_rule. simpl.
      iApply (ewp_mono with "[Hf HfCtx]").
      { iApply (ewp_suspend callback (λ v, ⌜ v = #() ⌝ ∗ promise_state_done γ)%I). 
        by iFrame. }
      (* after we have performed the effect we get promise_state_done. *)
      iIntros (v) "((-> & Hps) & HfCtx) !>".
      ewp_pure_steps. ewp_bind_rule. simpl.
      (* now we match on the promise again but this time we know it must be fulfilled *)
      iClear "Hwakers". clear wakers.
      iApply (ewp_atomic ⊤ (⊤ ∖ ↑promiseN)).
      iMod (inv_acc with "HpInv") as "(HpInvIn & Hclose)"; first by done.
      iMod (lookup_promiseInv_inner with "HpInvIn Hmem") as "[HpInvIn HpSt]".
      iDestruct "HpSt" as "[[%y (Hp&#Hps'&%Φ'&#Hε'&#Hy)]| (%wakers & Hp & Hps' & Htqstate & Hres & #Hwakers) ]";
        last by iDestruct (promise_state_disjoint γ with "[$]") as "HFalse".
      iModIntro.
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>". 
      iPoseProof (saved_pred_agree ε Φ Φ' y with "Hε Hε'") as "Heqv".
      iApply (fupd_trans_frame (⊤ ∖ ↑promiseN) (⊤ ∖ ↑promiseN) ⊤ _ (▷ promiseInv_inner)).
      iSplitL "Hclose". iApply "Hclose".
      iModIntro.
      iSplitR "HfCtx".
      iNext. iApply "HpInvIn". iLeft. iExists y. iFrame. 
      iExists Φ'. by iSplit.
      ewp_pure_steps.
      iFrame.
      by iRewrite "Heqv".
  Qed.

  (* the wrapped function is passed via the FORK effect to the handler.
     the handler should then pass is_queue to wrapped_f so that it is able to change the run_queue.
     is_queue should be passed between client and handler the same as promiseInv, for every performed effect. *)
  Lemma ewp_fork_wrap (f: val) (p: loc) γ δ ε Φ :
    promise_state_waiting γ ∗ isMember p γ ε ∗ isPromiseResult ε Φ ∗ (fiberContext δ -∗ EWP (f #()) <| Coop δ |> {{v, □ Φ v ∗ fiberContext δ}}) 
  ⊢
    EWP (fork_wrap_f f #p) <| ⊥ |> {{wrapped_f, 
        (* promiseInv and is_queue are passed here because they come from the effect handler *)
          promiseInv -∗
          fiberContext δ -∗ EWP (wrapped_f #()) <| Coop δ |> {{_, fiberContext δ }} }}.
  Proof.
    iIntros "(Hps_start & #Hmem & #Hε & Hf)". 
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
      iApply (cqs_resume_all_spec (promise_state_done γ) with "[Htqstate Hres Hwakers]").
      iFrame. iSplit; first done. 
      by done. }
    iIntros (?) "_ !>". by done.
  Qed.

  Lemma ewp_fork_promise (f: val) Φ δ :
    fiberContext δ ∗ promiseInv ∗ (fiberContext δ -∗ EWP (f #()) <| Coop δ |> {{v, □ Φ v ∗ fiberContext δ}})
  ⊢ 
    EWP (fork_promise f) <| Coop δ |> {{ y, 
      ∃ (p: loc), ⌜ y = #p ⌝ ∗ isPromise p Φ ∗ fiberContext δ }}.
  Proof.
    iIntros "(HfCtx & #HpInv & Hf)". rewrite /fork_promise. ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply ewp_mono.
    iApply ewp_get_context.
    iIntros (state) "(%ℓstate & -> & #HIsState) !>".
    ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply ewp_mono. 
    iApply ewp_os_prot_mono. 
      by iApply iEff_le_bottom. 
    iApply (ewp_new_promise Φ with "HpInv").
    iIntros (v) "(%p & %γ & %ε & -> & Hps & #(Hmem & HRes)) !>".
    ewp_pure_steps.
    iApply (ewp_bind' (AppRCtx _)); first done. simpl.
    iApply (ewp_mono with "[Hf Hps]").
    { iApply ewp_os_prot_mono. iApply iEff_le_bottom.
      iApply ewp_fork_wrap. iFrame. by iSplit. }
    iIntros (wrapped_f) "Hwrapped_f !>".
    iSpecialize ("Hwrapped_f" with "HpInv").
    ewp_pure_steps.
    iApply (ewp_bind' (AppRCtx _)); first done. simpl.
    iApply (ewp_mono with "[Hwrapped_f HfCtx]").
    iApply ewp_fork. 
    iPoseProof (fiber_context_agree with "HfCtx HIsState") as "HfState".
    by iFrame.
    iIntros (?) "HfState !>".
    ewp_pure_steps. iExists p.
    iFrame. iSplit; first done.
    iSplitR.
    iExists γ, ε. by iSplit.
    by iExists _.
  Qed.
      
  Lemma ewp_run (main : val) Φ :
    promiseInv ∗ (∀ δ, fiberContext δ -∗ EWP main #() <| Coop δ |> {{ v, □ Φ v ∗ fiberContext δ }}) ⊢
      EWP run main {{ _, True }}.
  Proof.
    iIntros "(#HpInv & Hmain)". unfold run. ewp_pure_steps.
    ewp_bind_rule. simpl. iApply ewp_mono. { by iApply ewp_new_fiber_state. }
    iIntros (state) "H".
    iDestruct "H" as (ℓstate n) "(-> & Hℓstate)".
    iMod (fiber_state_create ℓstate) as (δ) "#HIsState".
    (* a.d. We must do this up here so that ∀ δ does not appear in IH.
       a.d. TODO can we speciaize Hℓstate, too? *)
    iSpecialize ("Hmain" $! δ).
    iModIntro. ewp_pure_steps.
    ewp_bind_rule. simpl. iApply ewp_mono. { by iApply queue_create_spec. }
    iIntros (q) "Hq !>". 
    (* a.d. it's kind of interesting that ready is now also scheduler specific. But it's nice to know that
       we cannot schedule a fiber in a different scheduler. *)
    iSpecialize ("Hq" $! (ready δ)).
    ewp_pure_steps.
    iLöb as "IH" forall (main q Φ n).
    iSpecialize ("Hmain" with "[Hℓstate]").
    { rewrite /fiberContext /fiberState. iExists _. iSplit; first done. by iExists _. }
    iApply (ewp_deep_try_with with "Hmain").
    iLöb as "IH_handler" forall (q Φ).
    iDestruct "Hq" as "#Hq".
    rewrite deep_handler_unfold.
    iSplit; [|iSplit]; last (by iIntros (??) "HFalse"; rewrite upcl_bottom).
    (* Return branch. *)
    - iIntros (?) "(_ & HfCtx)".
      ewp_pure_steps. 
      by iApply (ewp_next with "HfCtx HpInv Hq").
    (* Effect branch. *)
    - iIntros (request k). rewrite upcl_Coop upcl_FORK upcl_SUSPEND upcl_GET_CONTEXT.
      iIntros "[(%ℓstate' & %e & -> & (HfState' & He) & Hk)
               |[(%suspender & %P & -> & (Hsuspender & HfCtx & _) & Hk)
               |(%_ & -> & _ & Hk)]]".
      (* Fork. *)
      + iDestruct (fiber_state_agree with "HfState' HIsState") as (->) "HfState'".
        ewp_pure_steps.
        iApply (ewp_bind' (AppRCtx _)); first by done. simpl.
        iApply (ewp_mono with "[Hk]").
        { iApply (queue_push_spec with "Hq"). rewrite /ready.
          iIntros "HfCtx #HpInv'". ewp_pure_steps.
          iDestruct (fiber_context_agree with "HfCtx HIsState") as "HfState''".
          iSpecialize ("Hk" $! #() with "HfState''").
          iApply "Hk". iNext. 
          by iApply ("IH_handler" with "Hq").
        }
        iIntros (?) "_ !>". ewp_pure_steps.
        (* find out the current state. a.d. TODO it should be sufficient to just have n existentially quantified
           in the precondition of IH. *)
        iDestruct "HfState'" as "(_ & (% & Hℓstate))".
        iApply ("IH" with "[He] Hℓstate Hq").
        { instantiate (1:=(λ _, True)%I).
          iIntros "HfCtx".
          iSpecialize ("He" with "HfCtx").
          iApply (ewp_mono with "He"). 
          iIntros (?) "HfCtx !>". by iFrame. }
      (* Suspend/GetContext. *)
      + do 12 ewp_value_or_step.
        ewp_bind_rule. simpl.
        (* here we bind the creation of waker. Now we should prove a spec for it. *)
        set (Hwaker := (λ (waker: val), (∀ (v : val),
              P v -∗
              EWP waker v <| ⊥ |> {{ _, True }})%I)).
        iApply (ewp_mono _ _ Hwaker with "[Hk]").
        { 
          ewp_pure_steps.
          iIntros (v) "HP".
          ewp_pure_steps.
          iApply (queue_push_spec with "Hq"). rewrite /ready.
          iIntros "HfCtx _". ewp_pure_steps.
          iSpecialize ("Hk" $! v with "[$]").
          iApply "Hk". iNext.
          by iApply ("IH_handler" with "Hq").
        }
        iIntros (waker) "Hwaker !>".
        iSpecialize ("Hsuspender" $! waker with "Hwaker HpInv").
        ewp_pure_steps.
        ewp_bind_rule. simpl.
        iApply (ewp_mono with "Hsuspender").
        iIntros (?) "_ !>". ewp_pure_steps.
        iApply (ewp_next with "HfCtx HpInv Hq").
      + do 12 ewp_value_or_step.
        iApply ("Hk" with "[$]"). iNext.
        iApply ("IH_handler" with "Hq").
  Qed.

End verification.

(* ========================================================================== *)
(** * Specification. *)

Section specification.
  Context `{!heapGS Σ}.
  Context `{!ListLib Σ}.

  Class AsyncCompLib := {
    coop : gname → iEff Σ;
    is_fiber_state : gname → loc → iProp Σ;
    fiber_context : gname → iProp Σ;
    is_promise : val → (val -> iProp Σ) → iProp Σ;
    is_promise_Persistent p Φ : Persistent (is_promise p Φ);
    promise_inv : iProp Σ;
    fork_spec δ (f : val) Φ :
      fiber_context δ ∗ promise_inv ∗ (fiber_context δ -∗ EWP f #() <| coop δ |> {{ y, □ Φ y ∗ fiber_context δ }}) -∗
        EWP fork_promise f <| coop δ |> {{ p, is_promise p Φ ∗ fiber_context δ }};
    await_spec δ p Φ :
      fiber_context δ ∗ promise_inv ∗ is_promise p Φ -∗
        EWP await p <| coop δ |> {{ y, □ Φ y ∗ fiber_context δ }};
    get_context_spec δ :
      ⊢ EWP get_context #() <| coop δ |> {{ state, ∃ (ℓstate: loc), ⌜ state = #ℓstate ⌝ ∗ is_fiber_state δ ℓstate }} ;    
  }.

  Definition run_spec (main : val) :=
    (* a.d. TODO remove the □ True *)
    (∀ _ : AsyncCompLib, ∀ δ, fiber_context δ -∗ EWP main #() <| coop δ |> {{ _, □ True ∗ fiber_context δ }}) ={⊤}=∗
      EWP run main <| ⊥ |> {{ _, True }}.

End specification.

Section closed_proof.
  Context `{!heapGS Σ, !promiseGpreS Σ, !savedPredG Σ val}.
  Context `{!ListLib Σ}.

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

  Local Program Instance async_comp_lib `{!promiseGS Σ} :
    AsyncCompLib (Σ:=Σ) := {
    coop := Coop;
    is_fiber_state := isFiberState;
    fiber_context := fiberContext;
    is_promise := λ v Φ, (∃ (p : loc), ⌜ v = #p ⌝ ∗ isPromise p Φ)%I;
    is_promise_Persistent := _;
    promise_inv := promiseInv;
    get_context_spec := ewp_get_context;
  }.
  Next Obligation.
   iIntros (????) "(HfCtx&HpInv&Hf)". 
   iApply (ewp_mono with "[HfCtx HpInv Hf]").
   iApply ewp_fork_promise. iFrame.
   iIntros (?) "(%&->&H2&H3)".
   iModIntro.
   iFrame. iExists _. by iFrame.
  Qed.
  Next Obligation. 
    iIntros (????) "(HfCtx & ? & % & -> & ?)". 
    iApply ewp_await; iFrame. 
  Qed.

  Theorem run_correct main : run_spec main.
  Proof.
    rewrite /run_spec.
    iIntros "He".
    iMod promiseInv_init as "[%HpromiseGS #HpInv]".
    iSpecialize ("He" $! async_comp_lib). iModIntro.
    iApply (ewp_run _ (λ _, True)%I with "[HpInv He]").
    iFrame.
    by iAssumption.
  Qed.
End closed_proof.

Print Assumptions  run_correct.