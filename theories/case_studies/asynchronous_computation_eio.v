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
From iris.base_logic.lib Require Import iprop wsat invariants.
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

Section implementation.
  Context `{!heapGS Σ}.
  Context `{!ListLib Σ}.

  Definition new_promise : val := (λ: <>,
    ref (Waiting (list_nil #()))
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
    | (* Waiting: *) InjR "ks" =>
        list_iter (λ: "enqueue", "enqueue" #()) "ks";;
        "p" <- Done "v"
    end))%V.

  (* fork a new fiber "f" and return a promise to get the result. *)
  Definition fork_promise : val := (λ: "f", 
    let: "p" := new_promise #() in
    let: "wrapped_f" := fork_wrap_f "f" "p" in
    fork "wrapped_f";;
    "p")%V.
   
  Definition await_callback : val := (λ: "p", (λ: "enqueue", 
    (* We do it the same as Eio and check p again in here and then either call enqueue or put it in the waiting list.
      await should probably pass in Hmem p when it constructs the callback and the handler should pass in promiseInv when it calls the callback.
      Then we can take the promise out of promiseInv here. *)
    match: Load "p" with
        (* Done: *) InjL <>  => "enqueue" #()
    | (* Waiting: *) InjR "ks" =>
        "p" <- InjR (list_cons "enqueue" "ks")
    end
  ))%V.

  Definition await : val := (λ: "p",
    match: Load "p" with
      (* Done: *) InjL "v"  =>
        "v"
    | (* Waiting: *) InjR "ks" =>
        let: "callback" := await_callback "p" in 
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
  Context `{!ListLib Σ}.

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
  Definition promiseInv : iProp Σ := (
    ∃ M, isPromiseMap M ∗
      [∗ map] args ↦ Φ ∈ M, let '(p, γ) := args in
        ((* Fulfilled: *) ∃ y,
          p ↦ Done' y ∗ □ Φ y ∗ promise_state_done γ)
      ∨
        ((* Unfulfilled: *) ∃ l enqs,
          p ↦ Waiting' l ∗
          promise_state_waiting γ ∗
          is_list l enqs   ∗
          (* ks now does not contain a list of continuations but a list of enqueue functions. 
             Each of these functions will change the run queue (in the future they can change an arbitrary run queue)
             so we have is_queue as a precondition
          *)
          [∗ list] enq ∈ enqs, (∀ (v: val), 
            let P := (λ v, ⌜ v = #() ⌝ ∗ promise_state_done γ) in
            P v -∗
            (* a.d. can we remove the my_queue precondition by saying is_queue is persistent and "partially-applying" the specification? *)
            (* is_queue q (ready q (λ v, ⌜ v = #() ⌝)%I) -∗  *)
              EWP (App (Val enq) v)%I <| ⊥ |> {{_, True }} ))
  )%I.
    

  Definition ready_pre :
    (val -d> (val -d> iPropO Σ) -d> val -d> iPropO Σ) →
    (val -d> (val -d> iPropO Σ) -d> val -d> iPropO Σ) := (λ ready q Φ k,
    ∀ (y : val),
      □ Φ y -∗
        promiseInv -∗
          ▷ is_queue q (ready q (λ v, ⌜ v = #() ⌝)%I) -∗
             EWP (k : val) y {{ _, True }}
  )%I.

  Local Instance ready_contractive : Contractive ready_pre.
  Proof.
    rewrite /ready_pre /promiseInv=> n ready ready' Hn q Φ k.
    repeat (f_contractive || apply is_queue_ne  || f_equiv);
    try apply Hn; try done; try (intros=>?; apply Hn).
  Qed.
  Definition ready_def : val -d> (val -d> iPropO Σ) -d> val -d> iPropO Σ :=
    fixpoint ready_pre.
  Definition ready_aux : seal ready_def. Proof. by eexists. Qed.
  Definition ready := ready_aux.(unseal).
  Definition ready_eq : ready = ready_def :=
    ready_aux.(seal_eq).
  Global Lemma ready_unfold q Φ k : ready q Φ k ⊣⊢ ready_pre ready q Φ k.
  Proof. rewrite ready_eq /ready_def. apply (fixpoint_unfold ready_pre). Qed.

  Definition promiseSt p γ (Φ : val -d> iPropO Σ) : iProp Σ :=
    ((* Fulfilled: *) ∃ y,
       p ↦ Done' y ∗ □ Φ y ∗ promise_state_done γ)
  ∨
    ((* Unfulfilled: *) ∃ l enqs,
      p ↦ Waiting' l ∗
      promise_state_waiting γ ∗
      is_list l enqs   ∗
      (* ks now does not contain a list of continuations but a list of enqueue functions. 
         Each of these functions will change the run queue (in the future they can change an arbitrary run queue)
         so we have is_queue as a precondition and get it back after.
      *)
      [∗ list] enq ∈ enqs, (∀ (v: val), 
        let P := (λ v, ⌜ v = #() ⌝ ∗ promise_state_done γ) in
        P v -∗
          EWP (App (Val enq) v)%I <| ⊥ |> {{_, True }} )).

  (* ------------------------------------------------------------------------ *)
  (* Non-expansiveness. *)

  (* [ready]. *)
  Global Instance ready_ne n :
    Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) ready.
  Proof.
    induction (lt_wf n) as [n _ IH]=> q q' -> Φ Φ' HΦ k k' ->.
    rewrite !ready_unfold /ready_pre.
    by repeat (f_contractive || apply is_queue_ne
           || apply IH || f_equiv
           || case x1 as ()         || case x2 as ()
           || case y1 as (y11, y12) || case y2 as (y21, y22)
           || apply H0 || apply H1 ).
  Qed.
  Global Instance ready_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) ready.
  Proof. intros ?????????. apply equiv_dist=>n.
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
      { by iIntros (???) "[[%v[Hp _]]|[%l[%ks[Hp _]]]]"; auto. }
      iIntros "Hp Hp'".
      iPoseProof (Haux with "Hp")  as "[%v  Hp]".
      iPoseProof (Haux with "Hp'") as "[%v' Hp']".
      by iDestruct (mapsto_ne with "Hp Hp'") as "%Hneq".
    Qed.

    Lemma promiseSt_proper' p γ Φ Φ' :
      (Φ ≡ Φ') -∗ promiseSt p γ Φ -∗ promiseSt p γ Φ'.
    Proof. by iIntros "HΦ Hp"; iRewrite -"HΦ". Qed.

    Lemma update_promiseInv p γ Φ :
      promiseInv ∗ promiseSt p γ Φ ==∗
        promiseInv ∗ isMember p γ Φ.
    Proof.
      iIntros "[HpInv Hp]". rewrite /promiseInv.
      iDestruct "HpInv" as (M) "[HM HInv]".
      destruct (M !! (p, γ)) as [Ψ|] eqn:Hlkp.
      - rewrite (big_opM_delete _ _ _ _ Hlkp).
        iDestruct "HInv" as "[Hp' _]".
        by iDestruct (promiseSt_non_duplicable with "Hp Hp'") as "HFalse".
      - iMod (update_promise_map M p γ Φ Hlkp with "HM") as "[HM Hmem]".
        iModIntro. iFrame. iExists (<[(p, γ):=Φ]> M). iFrame.
        rewrite big_opM_insert; last done. by iFrame.
    Qed.

    Lemma lookup_promiseInv p γ Φ :
      promiseInv -∗ isMember p γ Φ -∗
        ▷ ((promiseSt p γ Φ -∗ promiseInv) ∗ promiseSt p γ Φ).
    Proof.
      iIntros "HpInv Hmem". rewrite /promiseInv.
      iDestruct "HpInv" as (M) "[HM HInv]".
      iDestruct (claim_membership M p γ Φ with "[$]") as "[%Φ' [%Hlkp #Heq]]".
      iPoseProof (promise_unfold_equiv with "Heq") as "#Heq'". iNext.
      iDestruct (big_sepM_delete _ _ (p, γ) with "HInv")
        as "[HpSt HInv]"; first done.
      iSplitL "HInv HM".
      - iIntros "HpSt". iExists M. iFrame.
        rewrite (big_opM_delete _ _ _ _ Hlkp). iFrame.
        iApply (promiseSt_proper' p γ Φ Φ' with "[] HpSt").
        rewrite discrete_fun_equivI. iIntros (x).
        by iRewrite ("Heq'" $! x).
      - iApply (promiseSt_proper' p γ Φ' Φ with "[] HpSt").
        by rewrite discrete_fun_equivI.
    Qed.

  End promise_preds.

End predicates.


(* -------------------------------------------------------------------------- *)
(** Protocol [Coop]. *)

Section protocol_coop.
  Context `{!heapGS Σ, !promiseGS Σ}.
  Context `{!ListLib Σ}.

  Definition FORK_pre (Coop : iEff Σ) : iEff Σ :=
    >> e >> !(Fork'  e) {{promiseInv ∗ ▷ (promiseInv -∗  EWP e #() <|Coop |> {{_, promiseInv}} ) }};
    << (_: val) << ?(#())        {{promiseInv }} @ OS.
      
  (* a.d. for the suspend call in await, we want to instantiate P with (λ v, v = #() ∧ done p)
    where done p shows that the promise is fulfilled
    1. it's maybe not okay for P to close over the promise p.
    2. we want to change torch γ to a oneshot (torch γ) + (done γ)  
  *)
  Definition SUSPEND : iEff Σ :=
    >> (f: val) (P: val → iProp Σ) >> !(Suspend' f) {{
      (* We call f with the enqueue function and enqueue receives a value satisfying P and accesses the run queue. *)
      ( (∀ (enqueue: val),
        (∀ (v: val), P v -∗ 
                      (EWP (enqueue v) <| ⊥ |> {{_, True }}) ) -∗
        promiseInv -∗ 
          (▷ EWP (f enqueue) <| ⊥ |> {{_, promiseInv  }})) ∗
        promiseInv)%I
    }};
    << y           << ?(y)         {{P y ∗ promiseInv }} @ OS.

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
      (∃ e, ⌜ v = Fork' e ⌝ ∗ (promiseInv ∗ ▷ (promiseInv -∗ EWP e #() <|Coop|> {{_, promiseInv }})) ∗
            (∀ (_ : val), (promiseInv) -∗ Φ' #()))%I.
  Proof. by rewrite /FORK (upcl_tele' [tele _] [tele _]). Qed.

  Lemma upcl_SUSPEND  v Φ' :
    iEff_car (upcl OS (SUSPEND )) v Φ' ≡
      (∃ (f : val) (P: val → iProp Σ), ⌜ v = Suspend' f ⌝ 
      ∗ 
      (* the big precondition of the protocol *)
      ( (∀ (enqueue: val),
        (∀ (v: val), P v -∗ 
                      (EWP (enqueue v) <| ⊥ |> {{_, True }}) ) -∗
        promiseInv -∗ 
          (▷ EWP (f enqueue) <| ⊥ |> {{_, promiseInv }})) ∗
        promiseInv) 
      ∗
          (∀ v, (P v ∗ promiseInv) -∗ Φ' v))%I.
  Proof. by rewrite /SUSPEND (upcl_tele' [tele _ _] [tele _]). Qed.

End protocol_coop.


(* ========================================================================== *)
(** * Verification. *)

Section verification.
  Context `{!heapGS Σ, !promiseGS Σ}.
  Context `{!ListLib Σ}.

  Lemma ewp_new_promise Ψ Φ :
    ⊢ EWP (new_promise #()) <| Ψ |> {{ y,
        ∃ p γ, ⌜ y = #(p : loc) ⌝ ∗ promise_state_waiting γ ∗ promiseSt p γ Φ }}.
  Proof.
    unfold new_promise. ewp_pure_steps. ewp_bind_rule.
    iApply ewp_mono. { by iApply list_nil_spec. }
    iIntros (l) "Hlist !>". simpl. ewp_pure_steps.
    iApply ewp_alloc. iIntros "!>" (p) "Hp".
    iMod promise_state_create as "[%γ Hps]".
    iMod (promise_state_split with "Hps") as "[Hps1 Hps2]".
    iModIntro.
    iExists p, γ. iFrame. iSplit; [done|]. iRight.
    iExists l, []. by iFrame.
  Qed.
  
  (* a.d. If we ever want to return promiseInv from main, then next should contitionally return promiseInv (or maybe return the next k itself and then the handler calls it) *)
  Lemma ewp_next q Ψ :
    promiseInv -∗
      is_queue q (ready q (λ v, ⌜ v = #() ⌝)) -∗
         EWP (next q) <| Ψ |> {{ _, True }}.
  Proof.
    iIntros "HpInv #Hq". unfold next. ewp_pure_steps. ewp_bind_rule.
    iApply ewp_mono; [iApply (queue_pop_spec with "Hq")|].
    simpl. iIntros (y) "[->|(%k & -> & Hk)] !>".
    - (* queue is empty *) 
      by ewp_pure_steps.
    - (* queue has a continuation *)
      ewp_pure_steps.
      rewrite ready_unfold /ready_pre.
      iSpecialize ("Hk" $! #() with "[//] HpInv Hq").
      iApply ewp_os_prot_mono. { by iApply iEff_le_bottom. } { done. }
  Qed.

  Lemma ewp_fork (e : val) :
    promiseInv  ∗ 
    (promiseInv -∗ EWP e #() <| Coop |> {{ _, promiseInv }})
  ⊢
      EWP (fork e) <| Coop |> {{ _, promiseInv }}.
  Proof.
    iIntros "(HpInv &  He)". rewrite /fork. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_FORK. iLeft.
    iExists e. iSplit; [done|]. iFrame.
    iIntros (_) "H". by iFrame.
  Qed.

  Lemma ewp_suspend (f : val) (P: val → iProp Σ) :
    ( (∀ (enqueue: val),
      (∀ (v: val), P v -∗ 
                    (EWP (enqueue v) <| ⊥ |> {{_, True}}) ) -∗
      promiseInv -∗ 
        (▷ EWP (f enqueue) <| ⊥ |> {{_, promiseInv }})) ∗
      promiseInv) 
    ⊢
      EWP (suspend f) <| Coop |> {{ v, P v ∗ promiseInv}}.
  Proof.
    iIntros "(He & HpInv)". rewrite /suspend. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_SUSPEND. iRight.
    iExists f, P. iSplit; [done|]. iFrame.
    iIntros (v) "Hv". by iFrame.
  Qed.

  Lemma ewp_await_callback (p: loc) γ Φ:
  let P := (λ v, ⌜ v = #() ⌝ ∗ promise_state_done γ)%I in
    isMember p γ Φ
  ⊢
    EWP (await_callback #p) <| ⊥ |> {{f, ∀ (enqueue: val), 
      (∀ (v: val), P v -∗ 
                    (EWP (enqueue v) <| ⊥ |> {{_, True }}) ) -∗
      promiseInv -∗ 
        (▷ EWP (f enqueue) <| ⊥ |> {{_, promiseInv }}) }}.
  Proof.
    iIntros "Hmem". rewrite /await_callback. ewp_pure_steps.
    iIntros (enqueue) "Henq HpInv". 
    iDestruct (lookup_promiseInv with "HpInv Hmem") as "[HpInv HpSt]".
    iNext. ewp_pure_steps. ewp_bind_rule. simpl.
    iDestruct "HpSt" as "[[%y (Hp&Hy&#Hps)]|[%l [%enqs (Hp&Hps&Hl&Hks)]]]".
    - (* the promise was fulfilled (cannot yet happen without concurrency) *)
      iApply (ewp_load with "Hp"). 
      iIntros "!> Hp !>". ewp_pure_steps.
      iApply (ewp_mono with "[Henq]").
      + iApply ("Henq" with "[]"). iSplit; done.
      + iIntros (v) "_ !>". 
        iApply "HpInv". iLeft. iExists y. by iFrame. 
    - (* the promise is not yet fulifilled so we put enqueue into the list *)
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>". ewp_pure_steps.
      iApply (ewp_bind [(StoreRCtx _); InjRCtx]); first done.
      iApply (ewp_mono with "[Hl]"); [iApply (list_cons_spec with "Hl")|].
      iIntros (l') "Hl' !>". simpl. ewp_pure_steps. ewp_bind_rule.
      iApply (ewp_store with "Hp"). iIntros "!> Hp !>". 
      iApply "HpInv". iRight. iExists l', (enqueue :: enqs). iFrame.
  Qed.

  (* Definition await_callback : val := (λ: "p", (λ: "enqueue", 
    (* We do it the same as Eio and check p again in here and then either call enqueue or put it in the waiting list.
      await should probably pass in Hmem p when it constructs the callback and the handler should pass in promiseInv when it calls the callback.
      Then we can take the promise out of promiseInv here. *)
    match: Load "p" with
      (* Done: *) InjL <>  => "enqueue" #()
    | (* Waiting: *) InjR "ks" =>
        "p" <- InjR (list_cons "enqueue" "ks")
    end
  ))%V. *)

  Lemma ewp_await (p: loc) Φ :
    promiseInv ∗ isPromise p Φ ⊢ 
      EWP (await #p) <| Coop |> {{v, promiseInv ∗ □ Φ v}}.
  Proof.
    iIntros "(HpInv & %γ & #Hmem)". rewrite /await. 
    iDestruct (lookup_promiseInv with "HpInv Hmem") as "[HpInv HpSt]".
    ewp_pure_steps. ewp_bind_rule. simpl.
    iDestruct "HpSt" as "[[%y (Hp&#Hy&#Hps)]|[%l [%enqs (Hp&Hps&Hl&Hks)]]]".
    - (* the promise is already fulfilled *)
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>". ewp_pure_steps. iSplit; last by iAssumption.
      iApply "HpInv". iLeft. iExists y. iFrame. by iSplit.
    - (* the promise is not yet fulfilled, so we create a callback and perform the suspend effect.
         After the suspend returns, we know the promise is fulfilled. *)
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>". ewp_pure_steps. 
      ewp_bind_rule. simpl.
      iApply (ewp_mono). 
      iApply ewp_os_prot_mono. iApply iEff_le_bottom.
      iApply ewp_await_callback. iApply "Hmem".
      iIntros (callback) "Hf !>".
      ewp_pure_steps.
      iAssert (promiseInv) with "[HpInv Hps Hl Hks Hp]" as "HpInv".
      { iApply "HpInv". iRight. iExists l, enqs. iFrame. }
      ewp_bind_rule. simpl.
      iApply (ewp_mono with "[Hf HpInv]").
      { iApply (ewp_suspend callback (λ v, ⌜ v = #() ⌝ ∗ promise_state_done γ)%I). 
        by iFrame. }
      (* after we have performed the effect we get promise_state_done.
        a.d. TODO the promiseInv would have to be given to the effect and we also get it back here. *)
      iIntros (v) "((-> & Hps') & HpInv) !>".
      (* now we match on the promise again but this time we know it must be fulfilled *)
      iDestruct (lookup_promiseInv with "HpInv Hmem") as "[HpInv HpSt]".
      ewp_pure_steps. ewp_bind_rule. simpl.
      iDestruct "HpSt" as "[[%y (Hp&#Hy&#Hps)]|[%l' [%enqs' (Hp&Hps&Hl&Hks)]]]";
        last by iDestruct (promise_state_disjoint γ with "[$]") as "HFalse".
      iApply (ewp_load with "Hp").
      iIntros "!> Hp !>". ewp_pure_steps. iSplit; last done.
      iApply "HpInv". iLeft. iExists y. by iFrame.
  Qed.

  (* Definition await : val := (λ: "p",
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
  )%V. *)
  
  (* the wrapped function is passed via the FORK effect to the handler.
     the handler should then pass is_queue to wrapped_f so that it is able to change the run_queue.
     is_queue should be passed between client and handler the same as promiseInv, for every performed effect. *)
  Lemma ewp_fork_wrap (f: val) (p: loc) γ Φ :
    promise_state_waiting γ ∗ isMember p γ Φ ∗ EWP (f #()) <| Coop |> {{v, □ Φ v}} 
  ⊢
    EWP (fork_wrap_f f #p) <| ⊥ |> {{wrapped_f, 
        (* promiseInv and is_queue are passed here because they come from the effect handler *)
          promiseInv -∗
          EWP (wrapped_f #()) <| Coop |> {{_, promiseInv}} }}.
  Proof.
    iIntros "(Hps & #Hmem & Hf)". rewrite /fork_wrap_f. ewp_pure_steps.
    iIntros "HpInv". ewp_pure_steps.
    ewp_bind_rule. simpl. iApply (ewp_mono with "Hf"). 
    iIntros (v) "#Hv !>".
    iDestruct (lookup_promiseInv with "HpInv Hmem") as "[HpInv HpSt]".
    ewp_pure_steps.
    iDestruct "HpSt" as "[[%y' (_&_&Hps')]|[%l [%ks (Hp&Hps'&Hl&Hks)]]]";
      first by iDestruct (promise_state_disjoint with "[$]") as "HFalse".
    ewp_bind_rule. iApply (ewp_load with "Hp"). simpl.
    iIntros "!> Hp".
    (* now we change the logical promise state *)
    iMod (promise_state_join with "[$]") as "Hps".
    iMod (promise_state_fulfill with "Hps") as "#Hps".
    iModIntro. ewp_pure_steps.
    iApply (ewp_bind' (AppRCtx _)); first done.
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
    iIntros (?) "[Hl _] !>". simpl.
    ewp_pure_steps. ewp_bind_rule.
    iApply (ewp_store with "Hp"). iIntros "!> Hp !>". simpl.
    iFrame. iApply "HpInv".
    iLeft. iExists v. iFrame. by iSplit.
  Qed.


  (* Definition fork_wrap_f : val := (λ: "f" "p", (λ: <>, 
    let: "v" := "f" #() in
    match: Load "p" with
      (* Done: *) InjL <> =>
        #() #() (* Unreachable! *)
    | (* Waiting: *) InjR "ks" =>
        list_iter (λ: "callback", "callback" #()) "ks";;
        "p" <- Done "v"
    end))%V. *)

  Lemma ewp_fork_promise  (f: val) Φ :
    promiseInv ∗ EWP (f #()) <| Coop  |> {{v, □ Φ v}}
  ⊢ 
    EWP (fork_promise f) <| Coop  |> {{ y, 
      ∃ (p: loc), ⌜ y = #p ⌝ ∗ isPromise p Φ ∗ 
      promiseInv  }}.
  Proof.
    iIntros "(HpInv & Hf)". rewrite /fork_promise. ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply ewp_mono. iApply (ewp_new_promise _ Φ).
    iIntros (v) "(%p & %γ & -> & Hps & HSt)".
    iMod (update_promiseInv with "[$]") as "[HpInv #Hmem]".
    iModIntro.
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
    iIntros (?) "HpInv !>".
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
      (promiseInv -∗ EWP main #() <| Coop |> {{ v, □ Φ v ∗ promiseInv }}) -∗
        EWP run main {{ _, True }}.
  Proof.
    iIntros "HpInv Hmain". unfold run. ewp_pure_steps.
    ewp_bind_rule. iApply ewp_mono. { by iApply queue_create_spec. }
    iIntros (q) "Hq !>". simpl. ewp_pure_steps.
    iSpecialize ("Hq" $! (ready q (λ v : val, ⌜v = #()⌝))%I).
    iSpecialize ("Hmain" with "HpInv").
    iLöb as "IH" forall (main q Φ).
    iApply (ewp_deep_try_with with "Hmain").
    iLöb as "IH_handler" forall (q Φ).
    iDestruct "Hq" as "#Hq".
    rewrite deep_handler_unfold.
    iSplit; [|iSplit]; last (by iIntros (??) "HFalse"; rewrite upcl_bottom).
    (* Return branch. *)
    - iIntros (y) "(_ & HpInv)".
      ewp_pure_steps. iApply (ewp_next with "HpInv Hq").
    (* Effect branch. *)
    - iIntros (request k). rewrite upcl_Coop upcl_FORK upcl_SUSPEND.
      iIntros "[(%e & -> & (HpInv & He) & Hk)
               |(%f & %P & -> & (Hf & HpInv) & Hk)]".
      (* Fork. *)
      + ewp_pure_steps.
        iApply (ewp_bind' (AppRCtx _)). { done. } simpl.
        iApply (ewp_mono with "[Hk]").
        { iApply (queue_push_spec with "Hq"). rewrite ready_unfold /ready_pre.
          (* a.d. maybe can remove is_queue from ready *)
          iIntros (y) "-> HpInv _". ewp_pure_steps.
          iSpecialize ("Hk" $! #() with "HpInv").
          iApply "Hk". iNext.
          by iApply ("IH_handler" with "Hq").
        }
        iIntros (?) "_ !>". ewp_pure_steps.
        iSpecialize ("He" with "HpInv").
        iApply ("IH" with "[He] Hq").
        instantiate (1:=(λ _, True)%I).
        iApply (ewp_mono with "He"). 
        iIntros (?) "HpInv !>". by iFrame. 
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
          iApply (queue_push_spec with "Hq"). rewrite ready_unfold /ready_pre.
          iIntros (y) "-> HpInv _". ewp_pure_steps.
          iSpecialize ("Hk" $! v with "[$]").
          iApply "Hk". iNext.
          by iApply ("IH_handler" with "Hq").
        }
        iIntros (enqueue) "Henq !>".
        iSpecialize ("Hf" $! enqueue with "Henq HpInv").
        ewp_pure_steps.
        ewp_bind_rule. simpl.
        iApply (ewp_mono with "Hf").
        iIntros (?) "HpInv !>". ewp_pure_steps.
        iApply (ewp_next with "HpInv Hq").
  Qed.

End verification.

Print Assumptions ewp_run.
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
