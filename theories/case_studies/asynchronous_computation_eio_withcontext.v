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
From iris.algebra Require Import excl_auth gset gmap agree csum.
From iris.base_logic.lib Require Import iprop wsat invariants.
From program_logic Require Import reasoning_rules.
From case_studies Require Import list_lib queue_lib.

(* ========================================================================== *)
(** * Implementation of the Scheduler. *)

Notation Async e := (InjL (InjL e)) (only parsing).
Notation Await p := (InjL (InjR p)) (only parsing).
Notation FFail := (InjR (InjL #())) (only parsing).
Notation WithOtherContext cfstatef := (InjR (InjR (InjL cfstatef))) (only parsing).
Notation WithContext f := (InjR (InjR (InjR f))) (only parsing).

Notation Async' e := (InjLV (InjLV e)) (only parsing).
Notation Await' p := (InjLV (InjRV p)) (only parsing).
Notation FFail' := (InjRV (InjLV #())) (only parsing).
Notation WithOtherContext' cfstatef := (InjRV (InjRV (InjLV cfstatef))) (only parsing).
Notation WithContext' f := (InjRV (InjRV (InjRV f))) (only parsing).

Notation Done y := (InjL y) (only parsing).
Notation Waiting ks := (InjR ks) (only parsing).

Notation Done' y := (InjLV y) (only parsing).
Notation Waiting' ks := (InjRV ks) (only parsing).

Notation RNone := (InjL #()) (only parsing).
Notation RSome v := (InjR v) (only parsing).

Notation RNone' := (InjLV #()) (only parsing).
Notation RSome' v := (InjRV v) (only parsing).

Section implementation.
  Context `{!heapGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Definition new_promise : val := (λ: <>,
    ref (Waiting (list_nil #()))
  )%V.
  Definition new_cancel_ctx : val := (λ: <>,
    (ref #false, ref #0)
  )%V.
  Definition async : val := (λ: "f", do: (Async "f"))%V.
  Definition await : val := (λ: "p", do: (Await "p"))%V.
  Definition ffail : val := (λ: <>, do: (FFail))%V.
  Definition with_other_context : val := (λ: "cfstatef", do: (WithOtherContext "cfstatef"))%V.
  Definition with_context : val := (λ: "f", do: (WithContext "f"))%V.

  Definition io : val := (λ: <>,
    let: "cancelled" := with_context (λ: "cfstate",
      let: "cf" := Fst "cfstate" in
      let: "state" := Snd "cfstate" in 
      if: Load "cf"
      then #true
      else
        (* if the fiber is not cancelled, increment and return. *)
        "state" <- (Load "state") + #1;;
        #false) in
    if "cancelled"
    then 
      (* because we cannot perform effects inside the lambda above we need to 
         do another if here and call fail. *)
      ffail #()
    else
      #())%V.

  Definition fiber_cancel : val := (λ: "cfstate",
    (* effect returns the same cfstate but with permission to mutate it. *)
    let: "i" := with_other_context ("cfstate", λ: "cfstate2",
      let: "cf2" := Fst "cfstate2" in
      let: "state2" := Snd "cfstate2" in
      "cf2" <- #true;;
      Load "state2") in
    "i")%V.

  Definition next : val := (λ: "q",
    if: queue_empty "q" then #() else queue_pop "q" #()
  )%V.
  Definition run : val := (λ: "main",
    let: "q" := queue_create #() in
    let: "fulfill" := rec: "fulfill" "p" "cfstate" "e" :=
      let: "cf" := Fst "cfstate" in
      let: "state" := Snd "cfstate" in
      deep-try: "e" #() with
        effect (λ: "request" "k",
          match: "request" with
            (* Async/Await*) InjL "e1" =>
              (match: "e1" with
                (* Async: *) InjL "e" =>
                  let: "p" := new_promise #() in
                  let: "cfstate" := new_cancel_ctx #() in
                  queue_push "q" (λ: <>, "k" ("p", "cfstate"));;
                  "fulfill" "p" "cfstate" "e"
              | (* Await: *) InjR "p" =>
                  match: Load "p" with
                    (* Done: *) InjL "v" => "k" "v"
                  | (* Waiting: *) InjR "ks" =>
                      "p" <- InjR (list_cons "k" "ks");;
                      next "q"
                  end
              end)
          | (* FFail/WithOtherContext/WithContext *) InjR "e1" =>
              (match: "e1" with
                (* FFail *) InjL <> =>
                  (match: Load "p" with
                    (* Done: *) InjL <> => #() #() (* Unreachable! *)
                  | (* Waiting: *) InjR "ks" =>
                    (* a.d. TODO maybe assert "cf" == #true *)
                    let: "result" := RNone' in
                    list_iter (λ: "k", queue_push "q" (λ: <>, "k" "result")) "ks";;
                    "p" <- Done "result";;
                    next "q"
                  end)
              | (* WithOtherContext/WithContext *) InjR "e2" =>
                (match: "e2" with
                  (* WithOtherContext *) InjL "cfstate2f" =>
                  let: "cfstate2" := Fst "cfstate2f" in
                  let: "f" := Snd "cfstate2f" in
                  let: "res" := "f" "cfstate2" in
                  "k" "res"
                | (* WithContext *) InjR "f" =>
                  let: "res" := "f" "cfstate" in
                  "k" "res"
                end)
              end)
          end)
      | return (λ: "v",
          match: Load "p" with
            (* Done: *) InjL <> => #() #() (* Unreachable! *)
          | (* Waiting: *) InjR "ks" =>
              let: "result" := RSome "v" in
              list_iter (λ: "k", queue_push "q" (λ: <>, "k" "result")) "ks";;
              "p" <- Done "result";;
              next "q"
          end)
      end
    in
    let: "p" := new_promise #() in
    let: "cfstate" := new_cancel_ctx #() in
    "fulfill" "p" "cfstate" "main"
  )%V.

End implementation.


(* ========================================================================== *)
(** * Specification. *)

Section specification.
  Context `{!heapGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Class AsyncCompLib := {
    coop : iEff Σ;
    is_promise : val → (val → iProp Σ) → iProp Σ;
    is_promise_Persistent p Φ : Persistent (is_promise p Φ);
    is_cancel : val → val → iProp Σ;
    is_cancel_Persistent cf state : Persistent (is_cancel cf state);
    io_log : val -> iProp Σ;
    io_log_Persistent i : Persistent (io_log i);
    async_spec (e : val) Φ :
      (□ Φ RNone' ∗ EWP e #() <| coop |> {{ y, □ Φ (RSome' y) }}) -∗
        EWP async e <| coop |> {{ y, ∃ (p cf state : val), ⌜ y = (p, (cf, state))%V ⌝ ∗ is_promise p Φ ∗ is_cancel cf state }};
    await_spec p Φ :
      is_promise p Φ -∗
        EWP await p <| coop |> {{ y, □ Φ y }};
    fiber_cancel_spec (cf state : val) :
      is_cancel cf state -∗
        EWP fiber_cancel (cf, state)%V <| coop |> {{ i, io_log i }};
  }.

  Definition run_spec (main : val) :=
    (∀ _ : AsyncCompLib, EWP main #() <| coop |> {{ _, True }}) ==∗
      EWP run main <| ⊥ |> {{ _, True }}.

End specification.


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
   contradictory. 
   
   The cancel camera is used to keep track of successful IO operations.
   As long as a fiber is not cancelled it is in the left exclusive variant and can update the count.
   If it is cancelled, this gets switched to the right variant. The count cannot be updated anymore, but can be shared.

     C ≜ Excl nat + Ag nat
    
   *)

(* The assumption that certain cameras are available. *)
Class promiseGpreS Σ := {
  promise_mapG :> inG Σ
    (authR (gmapUR (loc * gname) (agreeR (laterO (val -d> (iPropO Σ))))));
  torchG :> inG Σ (exclR unitO);
}.

Class cancelGpreS Σ := {
  cancelG :> inG Σ (csumR (exclR natO) (agreeR natO));
  cancel_mapG :> inG Σ
    (authR (gmapUR (loc * loc * gname) unitR));
}.

(* A concrete instance of [Σ] for which the assumption [promisesGS Σ] holds. *)
Definition promiseΣ := #[
  GFunctor (authRF
    (gmapURF (loc * gname) (agreeRF (laterOF (valO -d> idOF)))));
  GFunctor (exclR unitO)
].

Definition cancelΣ := #[
  GFunctor (csumR (exclR natO) (agreeR natO));
  GFunctor (authRF
    (gmapUR (loc * loc * gname) unitR))
].

(* The proof of the previous claim. *)
Instance subG_promiseΣ {Σ} : subG promiseΣ Σ → promiseGpreS Σ.
Proof. solve_inG. Qed.

Instance subG_cancelΣ {Σ} : subG cancelΣ Σ → cancelGpreS Σ.
Proof. solve_inG. Qed.

Class promiseGS Σ := {
  promise_inG :> promiseGpreS Σ;
  promise_name : gname;
}.

Class cancelGS Σ := {
  cancel_inG :> cancelGpreS Σ;
  cancel_name : gname;
}.


(* -------------------------------------------------------------------------- *)
(** Predicates. *)

Section predicates.
  Context `{!heapGS Σ, !promiseGS Σ, !cancelGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  (* ------------------------------------------------------------------------ *)
  (* Definitions. *)

  (* torch γ ≜ own γ (Excl ())

     isPromise p Φ ≜
       ∃ γ, own promise_name (◯ {[(p,γ) := Φ]})

     isPromiseMap M ≜
       own promise_name (● M)

     promiseInv q ≜
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
           ▷ promiseInv q -∗
             ▷ is_queue q (ready q (λ y. y = ())) -∗
               EWP (k y) <| ⊥ |> {{ _. True }}
  *)

  (* Unique token [γ]: a fiber holds possession of [torch γ] while running. *)
  Definition torch γ := @own _ _ (torchG) γ (Excl tt).

  (* Inject a predicate [Φ] into the camera [Ag(Next(val -d> iProp))]. *)
  Definition promise_unfold (Φ : val → iProp Σ) :
    agree (later (discrete_fun (λ (_ : val), iPropO Σ))) :=
    to_agree (Next (λ v, (Φ v))).

  Definition isMember p γ Φ :=
    own promise_name (◯ {[(p, γ) := promise_unfold Φ]}).

  Definition isPromise (p : loc) Φ : iProp Σ := (
    ∃ γ, isMember p γ Φ
  ).

  Definition isPromiseMap (M : gmap (loc * gname) (val → iProp Σ)) :=
    own promise_name (● (promise_unfold <$> M : gmap _ _)).

  Definition io_log_active (δ : gname) (i : nat) : iProp Σ :=
    own δ (Cinl (Excl i)).
  Definition io_log_cancelled (δ : gname) (i : nat) : iProp Σ :=
    own δ (Cinr (to_agree i)).

  Definition isMemberCancel cf state δ :=
    own cancel_name (◯ {[(cf, state, δ) := tt]}).

  Definition isCancel (cf state : loc) : iProp Σ := (
    ∃ δ, isMemberCancel cf state δ
  ).

  Definition isCancelMap (M : gmap (loc * loc * gname) unit) :=
    own cancel_name (● M).

  Definition cancelInv : iProp Σ := (
    ∃ M, isCancelMap M ∗
      [∗ map] args ↦ tt ∈ M, let '(cf, state, δ) := args in
        ∃ (i: nat), state ↦ #i ∗ (
          (cf ↦ #false ∗ io_log_active δ i)
        ∨ 
          (cf ↦ #true ∗ io_log_cancelled δ i)
        )
  )%I.
  (* a.d. TODO maybe have to add cancelInv to ready_pre *)


  Definition promiseInv_pre
    (ready : val -d> (val -d> iPropO Σ) -d> val -d> iPropO Σ)
    (q : val) : iProp Σ := (
    ∃ M, isPromiseMap M ∗
      [∗ map] args ↦ Φ ∈ M, let '(p, γ) := args in
        ((* Fulfilled: *) ∃ y,
           p ↦ Done' y ∗ □ Φ y ∗ torch γ)
      ∨
        ((* Unfulfilled: *) ∃ l ks,
           p ↦ Waiting' l ∗
           □ Φ RNone' ∗
           is_list l ks   ∗
           [∗ list] k ∈ ks, ready q Φ k)
  )%I.

  Definition ready_pre :
    (val -d> (val -d> iPropO Σ) -d> val -d> iPropO Σ) →
    (val -d> (val -d> iPropO Σ) -d> val -d> iPropO Σ) := (λ ready q Φ k,
    ∀ (y : val) n,
      □ Φ y -∗
        ▷ promiseInv_pre ready q -∗ ▷ cancelInv -∗
          ▷ is_queue q (ready q (λ v, ⌜ v = #() ⌝)%I) n -∗
             EWP (k : val) y <| ⊥ |> {{ _, True }}
  )%I.

  Local Instance ready_contractive : Contractive ready_pre.
  Proof.
    rewrite /ready_pre /promiseInv_pre=> n ready ready' Hn q Φ k.
    repeat (f_contractive || apply is_queue_ne || f_equiv);
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

  Definition promiseInv (q : val) : iProp Σ :=
    promiseInv_pre ready q.

  Definition promiseSt q p γ (Φ : val -d> iPropO Σ) : iProp Σ :=
    ((* Fulfilled: *) ∃ y,
       p ↦ Done' y ∗ □ Φ y ∗ torch γ)
  ∨
    ((* Unfulfilled: *) ∃ l ks,
       p ↦ Waiting' l ∗
       □ Φ RNone' ∗
       is_list l ks   ∗
       [∗ list] k ∈ ks, ready q Φ k).

  Definition cancelSt (cf state : loc) (δ : gname) : iProp Σ := (
    ∃ (i: nat), state ↦ #i ∗ (
      (cf ↦ #false ∗ io_log_active δ i
      )
    ∨ 
      (cf ↦ #true ∗ io_log_cancelled δ i
      )
  )).

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

  (* [promiseInv]. *)
  Global Instance promiseInv_ne n : Proper ((dist n) ==> (dist n)) promiseInv.
  Proof. by solve_proper. Qed.
  Global Instance promiseInv_proper : Proper ((≡) ==> (≡)) promiseInv.
  Proof. by solve_proper. Qed.

  (* [promiseSt]. *)
  Global Instance promiseSt_ne n q p γ :
    Proper ((dist n) ==> (dist n)) (promiseSt q p γ ).
  Proof. by solve_proper. Qed.
  Global Instance promiseSt_proper q p γ :
    Proper ((≡) ==> (≡)) (promiseSt q p γ ).
  Proof. by solve_proper. Qed.

  (* ------------------------------------------------------------------------ *)
  (* Properties. *)

  (* Logical rules governing the predicate [torch]. *)
  Section torch.

    Lemma forge_torch : ⊢ |==> ∃ γ, torch γ.
    Proof. by iMod (own_alloc (Excl tt)) as (γ) "Htorch"; last iExists γ. Qed.

    Lemma claim_uniqueness γ : (torch γ ∗ torch γ) -∗ False.
    Proof. rewrite /torch -own_op own_valid excl_validI.
    by easy. Qed.
  End torch.

  Section cancel.
    Lemma new_cancel : ⊢ |==> ∃ δ, io_log_active δ 0.
    Proof.
      iMod (own_alloc (Cinl (Excl 0))) as (δ) "Hcancel".
      by easy. by iExists δ.
    Qed.

    Lemma claim_active_uniqueness δ : ∀ i j, (io_log_active δ i ∗ io_log_active δ j) -∗ False.
    Proof.
      intros i j.
      rewrite /io_log_active -own_op own_valid csum_validI. 
      simpl. (* a.d. TODO how to remove cinl . cinl? *)
      by rewrite excl_validI.
    Qed.

    Lemma claim_cancelled_agreement δ : ∀ i j, (io_log_cancelled δ i ∗ io_log_cancelled δ j) -∗ ⌜i = j⌝.
    Proof.
      intros i j.
      rewrite /io_log_cancelled -own_op own_valid csum_validI.
      simpl.
      iIntros "%Hagree".
      iPureIntro.
      by specialize (to_agree_op_inv_L _ _ Hagree) as Hagree'.
    Qed.

    (* From iris.algebra Require Import excl. *)
    Lemma cancel_io_log (δ : gname) (i : nat) :
      io_log_active δ i ==∗ io_log_cancelled δ i.
    Proof.
      iApply own_update.
      apply cmra_update_exclusive.
      apply Cinr_valid.
      done.
    Qed.

    Lemma update_io_log (δ : gname) (i j: nat) :
      io_log_active δ i ==∗ io_log_active δ j.
    Proof.
      iApply own_update.
      apply cmra_update_exclusive.
      apply Cinl_valid.
      done.
    Qed.
  End cancel.

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
      isPromiseMap M ∗ isMember p γ  Φ -∗ ∃ Φ',
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

    Lemma promiseSt_non_duplicable q p γ γ' Φ Φ' :
      promiseSt q p γ  Φ -∗ promiseSt q p γ' Φ' -∗ False.
    Proof.
      assert (⊢ ∀ q p γ  Φ, promiseSt q p γ  Φ -∗ ∃ v, p ↦ v)%I as Haux.
      { iIntros (????) "[[%v[Hp _]]|[%l[%ks[Hp _]]]]"; auto. }
      iIntros "Hp Hp'".
      iPoseProof (Haux with "Hp")  as "[%v  Hp]".
      iPoseProof (Haux with "Hp'") as "[%v' Hp']".
      by iDestruct (mapsto_ne with "Hp Hp'") as "%Hneq".
    Qed.

    Lemma promiseSt_proper' q p γ  Φ Φ' :
      (Φ ≡ Φ') -∗ promiseSt q p γ  Φ -∗ promiseSt q p γ  Φ'.
    Proof. by iIntros "HΦ Hp"; iRewrite -"HΦ". Qed.

    Lemma update_promiseInv q p γ  Φ :
      promiseInv q ∗ promiseSt q p γ  Φ ==∗
        promiseInv q ∗ isMember p γ  Φ.
    Proof.
      iIntros "[HpInv Hp]". rewrite /promiseInv.
      iDestruct "HpInv" as (M) "[HM HInv]".
      destruct (M !! (p, γ)) as [Ψ|] eqn:Hlkp.
      - rewrite (big_opM_delete _ _ _ _ Hlkp).
        iDestruct "HInv" as "[Hp' _]".
        by iDestruct (promiseSt_non_duplicable with "Hp Hp'") as "HFalse".
      - iMod (update_promise_map M p γ  Φ Hlkp with "HM") as "[HM Hmem]".
        iModIntro. iFrame. iExists (<[(p, γ):=Φ]> M). iFrame.
        rewrite big_opM_insert; last done. by iFrame.
    Qed.

    Lemma lookup_promiseInv q p γ  Φ :
      promiseInv q -∗ isMember p γ  Φ -∗
        ▷ ((promiseSt q p γ  Φ -∗ promiseInv q) ∗ promiseSt q p γ  Φ).
    Proof.
      iIntros "HpInv Hmem". rewrite /promiseInv.
      iDestruct "HpInv" as (M) "[HM HInv]".
      iDestruct (claim_membership M p γ  Φ with "[$]") as "[%Φ' [%Hlkp #Heq]]".
      iPoseProof (promise_unfold_equiv with "Heq") as "#Heq'". iNext.
      iDestruct (big_sepM_delete _ _ (p, γ) with "HInv")
        as "[HpSt HInv]"; first done.
      iSplitL "HInv HM".
      - iIntros "HpSt". iExists M. iFrame.
        rewrite (big_opM_delete _ _ _ _ Hlkp). iFrame.
        iApply (promiseSt_proper' q p γ  Φ Φ' with "[] HpSt").
        rewrite discrete_fun_equivI. iIntros (x).
        by iRewrite ("Heq'" $! x).
      - iApply (promiseSt_proper' q p γ  Φ' Φ with "[] HpSt").
        by rewrite discrete_fun_equivI.
    Qed.

  End promise_preds.

  Section cancel_preds.
    (* Persistent predicates. *)
    Global Instance isMemberCancel_Persistent cf state δ : Persistent (isMemberCancel cf state δ).
    Proof. by apply _. Qed.
    Global Instance isCancel_Persistent cf state : Persistent (isCancel cf state).
    Proof. by apply _. Qed.

    Lemma update_cancel_map M cf state δ :
      M !! (cf, state, δ) = None →
        isCancelMap M ==∗
          isCancelMap (<[(cf, state, δ):=tt]> M) ∗ isMemberCancel cf state δ.
    Proof.
      intros Hlkp. unfold isCancelMap. iIntros "HM".
      iMod (own_update with "HM") as "[HM HiP]".
      { apply (@auth_update_alloc (gmapUR _ _) M).
        apply (alloc_singleton_local_update _ (cf, state, δ) tt).
        by rewrite /= Hlkp. done. }
      iModIntro. iFrame. 
    Qed.

    Lemma claim_membership_cancel M cf state δ :
      isCancelMap M ∗ isMemberCancel cf state δ -∗ 
        ⌜ M !! (cf, state, δ) = Some tt ⌝.
    Proof.
      rewrite /isCancelMap /isMemberCancel.
      rewrite -own_op own_valid auth_both_validI /=.
      iIntros "[HM #HpM]". iDestruct "HM" as (M') "#HM".
      rewrite gmap_equivI gmap_validI.
      iSpecialize ("HM" $! (cf, state, δ)). iSpecialize ("HpM" $! (cf, state, δ)).
      rewrite lookup_op lookup_singleton.
      rewrite option_equivI.
      case: (M  !! (cf, state, δ))=> [[]|] /=; [|
      case: (M' !! (cf, state, δ))=> [[]|] /=; by iExFalso].
      done.
    Qed.

    Lemma cancelSt_non_duplicable cf state δ δ' :
      cancelSt cf state δ -∗ cancelSt cf state δ' -∗ False.
    Proof.
      assert (⊢ ∀ cf state δ, cancelSt cf state δ -∗ ∃ v, cf ↦ v)%I as Haux.
      { iIntros (???) "(%i & Hstate & 
                         [ [Hcf _] | [Hcf _] ])"; auto. }
      iIntros "Hc Hc'".
      iPoseProof (Haux with "Hc")  as "(%v1 & Hc)".
      iPoseProof (Haux with "Hc'") as "(%v1' & Hc')".
      by iDestruct (mapsto_ne with "Hc Hc'") as "%Hneq".
    Qed.

    Lemma update_cancelInv cf state δ :
      cancelInv ∗ cancelSt cf state δ ==∗
        cancelInv ∗ isMemberCancel cf state δ.
    Proof.
      iIntros "[HcInv Hc]". rewrite /promiseInv.
      iDestruct "HcInv" as (M) "[HM HInv]".
      destruct (M !! (cf, state, δ)) as [Ψ|] eqn:Hlkp.
      - rewrite (big_opM_delete _ _ _ _ Hlkp).
        iDestruct "HInv" as "[Hc' _]".
        by iDestruct (cancelSt_non_duplicable with "Hc Hc'") as "HFalse".
      - iMod (update_cancel_map M cf state δ Hlkp with "HM") as "[HM Hmem]".
        iModIntro. iFrame. iExists (<[(cf, state, δ):=tt]> M). iFrame.
        rewrite big_opM_insert; last done. by iFrame.
    Qed.

    Lemma lookup_cancelInv cf state δ :
      cancelInv -∗ isMemberCancel cf state δ -∗
        ▷ ((cancelSt cf state δ -∗ cancelInv) ∗ cancelSt cf state δ).
    Proof.
      iIntros "HpInv Hmem". rewrite /promiseInv.
      iDestruct "HpInv" as (M) "[HM HInv]".
      iDestruct (claim_membership_cancel M cf state δ with "[$]") as "%Hlkp".
      iNext.
      iDestruct (big_sepM_delete _ _ (cf, state, δ) with "HInv")
        as "[HpSt HInv]"; first done.
      iSplitL "HInv HM".
      - iIntros "HpSt". iExists M. iFrame.
        rewrite (big_opM_delete _ _ _ _ Hlkp). iFrame.
      - done.
    Qed.
  End cancel_preds.
End predicates.


(* -------------------------------------------------------------------------- *)
(** Protocol [Coop]. *)

Section protocol_coop.
  Context `{!heapGS Σ, !promiseGS Σ, !cancelGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Definition ASYNC_pre (Coop : iEff Σ) : iEff Σ :=
    >> e Φ >> !(Async'  e) {{□ Φ RNone' ∗ ▷ EWP e #() <|Coop|> {{v, □ Φ (RSome' v)}} }};
    << (p : loc) (cf state : loc) << ?((#p, (#cf, #state))%V)        {{isPromise p Φ ∗ isCancel cf state }} @ OS.
  Definition AWAIT : iEff Σ :=
    >> (p : loc) Φ >> !(Await' #p) {{isPromise p Φ}};
    << y           << ?(y)         {{□ Φ y        }} @ OS.

  Definition FAIL : iEff Σ :=
    >> (_: val) >> !(FFail') {{True}};
    << (_: val) << ?(#()) {{False}} @ OS.
  Definition WITH_OTHER_CONTEXT : iEff Σ :=
    >> (cf state : loc) P f >> !(WithOtherContext' ((#cf, #state), f)%V) {{isCancel cf state 
      ∗ ∀ δ, cancelSt cf state δ -∗ EWP f (#cf, #state)%V <| ⊥ |> {{v, P v ∗ cancelSt cf state δ}} }};
    << v << ?(v) {{P v}} @ OS.
  Definition WITH_CONTEXT : iEff Σ :=
    >> P f >> !(WithContext' f) {{∀ cf state δ, cancelSt cf state δ -∗ EWP f (#cf, #state)%V <| ⊥ |> {{v, P v ∗ cancelSt cf state δ}} }};
    << v << ?(v) {{P v}} @ OS.
  
  Definition Coop_pre : iEff Σ → iEff Σ := (λ Coop,
    ASYNC_pre Coop <+> AWAIT <+> FAIL <+> WITH_OTHER_CONTEXT <+> WITH_CONTEXT
  )%ieff.

  Local Instance Coop_pre_contractive : Contractive (Coop_pre).
  Proof.
    rewrite /Coop_pre /AWAIT /ASYNC_pre=> n Coop Coop' HCoop.
    by repeat (apply ewp_ne||apply iEffPre_base_ne||f_contractive||f_equiv).
  Qed.
  Definition Coop_def : iEff Σ := fixpoint (Coop_pre).
  Definition Coop_aux : seal Coop_def. Proof. by eexists. Qed.
  Definition Coop := Coop_aux.(unseal).
  Definition Coop_eq : Coop = Coop_def := Coop_aux.(seal_eq).
  Global Lemma Coop_unfold : Coop ≡ Coop_pre (Coop).
  Proof. rewrite Coop_eq /Coop_def.
         by apply (fixpoint_unfold (Coop_pre)).
  Qed.
  Definition ASYNC := ASYNC_pre Coop.

  Lemma upcl_Coop v Φ' :
    iEff_car (upcl OS Coop) v Φ' ⊣⊢
      iEff_car (upcl OS ASYNC) v Φ' ∨
      iEff_car (upcl OS AWAIT) v Φ' ∨
      iEff_car (upcl OS FAIL) v Φ' ∨ 
      iEff_car (upcl OS WITH_OTHER_CONTEXT) v Φ' ∨ 
      iEff_car (upcl OS WITH_CONTEXT) v Φ'.
  Proof.
    transitivity (iEff_car (upcl OS (Coop_pre Coop)) v Φ').
    - iApply iEff_car_proper. by rewrite {1}Coop_unfold.
    - rewrite upcl_sum upcl_sum upcl_sum upcl_sum (upcl_tele' [tele _ _] [tele _]) //.
  Qed.

  Lemma upcl_ASYNC v Φ' :
    iEff_car (upcl OS ASYNC) v Φ' ≡
      (∃ e Φ, ⌜ v = Async' e ⌝ ∗ (□ Φ RNone' ∗ ▷ EWP e #() <| Coop |> {{ v, □ Φ (RSome' v) }}) ∗
            (∀ (p : loc) (cf state : loc), (isPromise p Φ ∗ isCancel cf state) -∗ Φ' ((#p, (#cf, #state))%V) ))%I.
  Proof. by rewrite /ASYNC (upcl_tele' [tele _ _] [tele _ _ _]). Qed.

  Lemma upcl_AWAIT v Φ' :
    iEff_car (upcl OS AWAIT) v Φ' ≡
      (∃ (p : loc) Φ, ⌜ v = Await' #p ⌝ ∗ isPromise p Φ ∗
          (∀ v, □ Φ v -∗ Φ' v))%I.
  Proof. rewrite /AWAIT. rewrite (upcl_tele' [tele _ _] [tele _]). by easy. Qed.

  Lemma upcl_FAIL v Φ' :
    iEff_car (upcl OS FAIL) v Φ' ≡
      (⌜ v = FFail' ⌝ ∗ True ∗ 
        (False -∗ Φ' #()))%I.
  Proof.
(* rewrite /FAIL. rewrite (upcl_tele' [tele _] [tele _]). by easy. *)
    iSplit.
    - iIntros "Hallows".
      rewrite (upcl_tele' [tele _] [tele _]).
      iDestruct "Hallows" as (v') "[Heq [_ HΦ']]".
      iSplit; first done. iSplit; first done.
      iIntros "[]".
    - iIntros "(-> & _ & HΦ')".
      rewrite (upcl_tele' [tele _] [tele _]). simpl.
      iExists (FFail'). 
      iSplit; first done. iSplit; first done.
      iIntros (_) "[]".
  Qed.

  Lemma upcl_WITH_OTHER_CONTEXT v Φ' :
    iEff_car (upcl OS WITH_OTHER_CONTEXT) v Φ' ≡ 
      (∃ (cf state: loc) (P : val → iProp Σ) (f : val), ⌜ v = WithOtherContext' ((#cf, #state), f)%V ⌝ 
      ∗ (isCancel cf state ∗ (∀ δ, cancelSt cf state δ -∗ EWP f (#cf, #state)%V <| ⊥ |> {{v, P v ∗ cancelSt cf state δ}})) ∗
        (∀ v, P v -∗ Φ' v)
      )%I.
  Proof.
    rewrite /WITH_OTHER_CONTEXT. rewrite (upcl_tele' [tele _ _ _ _] [tele _]). by easy.
  Qed. 

  Lemma upcl_WITH_CONTEXT v Φ' :
    iEff_car (upcl OS WITH_CONTEXT) v Φ' ≡ 
      (∃ (P : val → iProp Σ) (f : val), ⌜ v = WithContext' f ⌝ 
      ∗ (∀ cf state δ, cancelSt cf state δ -∗ EWP f (#cf, #state)%V <| ⊥ |> {{v, P v ∗ cancelSt cf state δ}}) ∗
        (∀ v, P v -∗ Φ' v)
      )%I.
  Proof.
    rewrite /WITH_CONTEXT. rewrite (upcl_tele' [tele _ _] [tele _]). by easy.
  Qed. 
End protocol_coop.


(* ========================================================================== *)
(** * Verification. *)

Section verification.
  Context `{!heapGS Σ, !promiseGS Σ, !cancelGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Lemma ewp_new_cancel_ctx Ψ :
    ⊢ EWP (new_cancel_ctx #()) <| Ψ |> {{ y, 
        ∃ (cf state : loc) (δ: gname), ⌜ y = PairV #cf #state ⌝ ∗ cancelSt cf state δ }}.
  Proof.
    unfold new_cancel_ctx. ewp_pure_steps. ewp_bind_rule.
    iApply ewp_alloc. iNext. 
    iIntros "%state Hstate".
    simpl.
    iModIntro.
    ewp_bind_rule.
    iApply ewp_alloc. iNext.
    iIntros "%cf Hcf".
    iMod new_cancel as "[%δ Hδ]".
    iModIntro.
    simpl.
    ewp_pure_steps.
    iExists cf, state, δ.
    iSplit; first done.
    rewrite /cancelSt.
    iExists 0.
    iFrame. iLeft. iFrame. 
  Qed.

  Lemma ewp_new_promise Ψ q Φ :
    □ Φ RNone' ⊢ EWP (new_promise #()) <| Ψ |> {{ y,
        ∃ p γ, ⌜ y = #(p : loc) ⌝ ∗ torch γ ∗ promiseSt q p γ Φ }}.
  Proof.
    iIntros "#Hnone".
    unfold new_promise. ewp_pure_steps. ewp_bind_rule.
    iApply ewp_mono. { by iApply list_nil_spec. }
    iIntros (l) "Hlist !>". simpl. ewp_pure_steps.
    iApply ewp_alloc. iIntros "!>" (p) "Hp".
    iMod forge_torch as "[%γ Hγ]".
    iModIntro.
    iExists p, γ. iFrame. iSplit; [done|]. iRight.
    iExists l, []. iFrame. 
    iSplit. by iAssumption. by done.
  Qed.

  Lemma ewp_next q n Ψ :
    promiseInv q -∗ cancelInv -∗
      is_queue q (ready q (λ v, ⌜ v = #() ⌝)) n -∗
         EWP (next q) <| Ψ |> {{ _, True }}.
  Proof.
    iIntros "HpInv HcInv Hq". unfold next. ewp_pure_steps. ewp_bind_rule.
    iApply (ewp_mono with "[Hq]"); [iApply (queue_empty_spec with "Hq")|].
    iIntros (b) "[Hq Hb] !>". simpl.
    case n as [|?]; iDestruct "Hb" as %->; ewp_pure_steps; [done|].
    ewp_bind_rule.
    iApply (ewp_mono with "[Hq]"); [iApply (queue_pop_spec with "Hq")|].
    simpl. iIntros (k) "[Hq Hk] !>".
    rewrite ready_unfold.
    iSpecialize ("Hk" $! #() n with "[//] HpInv HcInv Hq").
    iApply ewp_os_prot_mono. { by iApply iEff_le_bottom. } { done. }
  Qed.

  Lemma ewp_async (e : val) Φ :
    □ Φ RNone' ∗ EWP e #() <| Coop |> {{ v, □ Φ (RSome' v) }} ⊢
      EWP (async e) <| Coop |> {{ y,
        ∃ (p : loc) (cf state : loc), ⌜ y = (#p, (#cf, #state))%V ⌝ ∗ isPromise p Φ ∗ isCancel cf state }}.
  Proof.
    iIntros "[Hnone He]". unfold async. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_ASYNC. iLeft.
    iExists e, Φ. iSplit; [done|].
    iSplitL. iSplit.
    iFrame.
    iNext. iFrame.
    iIntros (p cf state) "[Hp Hcancel]".
    iExists p, cf, state. by iFrame.
  Qed.

  Lemma ewp_await (p : loc) Φ :
    isPromise p Φ -∗ EWP (await #p) <| Coop |> {{ v, □ Φ v }}.
  Proof.
    iIntros "Hp". unfold await. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_AWAIT. iRight. iLeft.
    iExists p, Φ. iSplit; [done|]. iFrame. by auto.
  Qed.

  Lemma ewp_ffail:
    (* a.d. TODO standalone ewp did not work. *)
    ⊢ EWP (ffail #()) <| Coop |> {{ _, False }}.
  Proof.
    unfold ffail. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_FAIL.
    iRight. iRight. iLeft.
    iSplit; first done. iSplit; first done.
    by done.    
  Qed.

  Global Instance io_log_cancelled_Persistent (δ: gname) (i: nat) : Persistent (io_log_cancelled δ i).
  Proof. by apply _. Qed.

  Lemma ewp_fiber_cancel (cf state : loc) :
    isCancel cf state -∗ 
    EWP (fiber_cancel (#cf, #state)%V) <| Coop |> {{ v, ∃ (δ: gname) (i: nat), ⌜ v = #i ⌝ ∗ io_log_cancelled δ i }}.
  Proof.
    iIntros "#Hcancel". 
    rewrite /fiber_cancel. ewp_pure_steps.
    set (P := (λ v, ∃ (δ: gname) (i: nat), ⌜ v = #i ⌝ ∗ io_log_cancelled δ i)%I).
    set (f := (λ: "cfstate2",
      let: "cf2" := Fst "cfstate2" in
      let: "state2" := Snd "cfstate2" in
      "cf2" <- #true;;
      Load "state2")%V).
    ewp_bind_rule. simpl. unfold with_other_context.
    ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_WITH_OTHER_CONTEXT.
    iRight; iRight; iRight; iLeft.
    iExists cf, state.
    iExists P, f.
    iSplit; first done.
    iSplitL.
    - iSplit; first done.
      iIntros (δ) "(%i & Hstate & [[Hcf Hio]|[Hcf #Hio]])".
      * (* it was active before *)
        unfold f. ewp_pure_steps.
        ewp_bind_rule.
        iApply (ewp_store with "Hcf"). 
        iNext. iIntros "Hcf".
        iMod (cancel_io_log with "Hio") as "#Hio".
        iModIntro.
        simpl. ewp_pure_steps.
        iApply (ewp_load with "Hstate"). iIntros "!> Hstate !>".
        iAssert (cancelSt cf state δ) with "[Hstate Hcf]" as "HcSt".
        { iExists i. iFrame. iRight. by iFrame. }
        iFrame.
        unfold P.
        iExists δ, i. by iSplit.
      * (* it was not active *)
        unfold f. ewp_pure_steps.
        ewp_bind_rule.
        iApply (ewp_store with "Hcf"). 
        iNext. iIntros "Hcf".
        iModIntro.
        simpl. ewp_pure_steps.
        iApply (ewp_load with "Hstate"). iIntros "!> Hstate !>".
        iAssert (cancelSt cf state δ) with "[Hstate Hcf]" as "HcSt".
        { iExists i. iFrame. iRight. by iFrame. }
        iFrame.
        unfold P.
        iExists δ, i. by iSplit.
    - iIntros (v) "P".
      ewp_pure_steps.
      by iAssumption.
  Qed.

  Lemma ewp_io :
    ⊢ EWP io #() <| Coop |> {{ _, True }}.
  Proof.
    unfold io. 
    unfold with_context.
    ewp_pure_steps.
    set (f := (λ: "cfstate",
              let: "cf" := Fst "cfstate" in
              let: "state" := Snd "cfstate" in
              if: Load "cf" then #true else "state" <- Load "state" + #1;; #false)%V).
    iApply ewp_do_os. rewrite upcl_Coop upcl_WITH_CONTEXT.
    iRight; iRight; iRight; iRight.
    iExists (λ _, True)%I, f.
    iSplit; first done.
    iSplitL.
    - iIntros (cf state δ) "(%i & Hstate & [[Hcf Hio]|[Hcf #Hio]])".
      * unfold f. 
        ewp_pure_steps.
        ewp_bind_rule. simpl.
        iApply (ewp_load with "Hcf"). iIntros "!> Hcf !>".
        ewp_pure_step. iNext.
        (* changing io log *)
        ewp_bind_rule.
        iApply (ewp_load with "Hstate"). iIntros "!> Hstate !>".
        simpl.
        ewp_bind_rule. ewp_pure_steps.
        { instantiate (1 := #(Z.of_nat (i + 1))).
          replace (Z.of_nat (i + 1)) with (Z.add (Z.of_nat i) (Z.of_nat 1)). 
          done. lia. }
        ewp_bind_rule. simpl.
        iApply (ewp_store with "Hstate"). iIntros "!> Hstate".
        iMod ((update_io_log _ i (i+1)) with "Hio") as "Hio".
        (* restore the cancelSt *)
        iAssert (cancelSt cf state δ) with "[Hstate Hcf Hio]" as "HcSt".
        { iExists (i + 1).
          iFrame. iLeft. by iFrame. }
        iModIntro. ewp_pure_steps.
        by iFrame.
      * unfold f.
        ewp_pure_steps. ewp_bind_rule. simpl.
        iApply (ewp_load with "Hcf"). iIntros "!> Hcf !>".
        ewp_pure_steps. 
        iAssert (cancelSt cf state δ) with "[Hstate Hcf Hio]" as "HcSt".
        { iExists (i).
          iFrame. iRight. by iFrame. }
        by iFrame.
    - iIntros (v) "_".
      ewp_pure_steps. done.
  Qed.
  
  Inductive LongProof := longproof.
  Print longproof.

  Lemma ewp_run (main : val) Φ :
    □ Φ RNone' -∗ (∀ q, promiseInv q) -∗ cancelInv -∗
      EWP main #() <| Coop |> {{ v, □ Φ (RSome' v) }} -∗
        EWP run main {{ _, True }}.
  Proof.
    (* a.d. TODO where is promiseInv kept? *)
    iIntros "#Hnone HpInv HcInv Hmain ". unfold run. ewp_pure_steps.
    ewp_bind_rule. iApply ewp_mono. { by iApply queue_create_spec. }
    iIntros (q) "Hq !>". simpl. ewp_pure_steps.
    ewp_bind_rule. iApply ewp_mono. { by iApply (ewp_new_promise _ q Φ). }
    iIntros (y) "[%p [%γ (->&Hγ&HpSt)]] !>". simpl.
    do 3 ewp_value_or_step.
    ewp_bind_rule. iApply ewp_mono. { by iApply (ewp_new_cancel_ctx _). }
    iIntros (y) "[%cf [%state [%δ (-> & HcSt)]]] !>". simpl.
    do 3 ewp_value_or_step.
    iSpecialize ("HpInv" $! q).
    iAssert (∃ (n : nat), is_queue q (ready q (λ v : val, ⌜v = #()⌝)) n)%I
      with "[Hq]" as "[%n Hq]". { by iExists 0. }
    iApply fupd_ewp.
    iMod (update_promiseInv with "[HpInv HpSt]") as "[HpInv Hmem]"; first by iFrame.
    iMod (update_cancelInv with "[HcInv HcSt]") as "[HcInv Hcmem]"; first by iFrame.
    iModIntro.
    (* does Φ really need to be quantified? *)
    iRevert "Hnone". iIntros "Hnone".
    iLöb as "IH" forall (main q p γ Φ n cf state δ).
    ewp_pure_steps.
    idtac.
    iApply (ewp_deep_try_with with "Hmain").
    iLöb as "IH_handler" forall (q γ Φ n cf state δ).
    iDestruct "Hmem" as "#Hmem".
    iDestruct "Hcmem" as "#Hcmem".
    iDestruct "Hnone" as "#Hnone".
    rewrite deep_handler_unfold.
    iSplit; [|iSplit]; last (by iIntros (??) "HFalse"; rewrite upcl_bottom).
    (* Return branch. *)
    - iIntros (y) "#Hy".
      iDestruct (lookup_promiseInv with "HpInv Hmem") as "[HpInv HpSt]".
      (* iDestruct (lookup_cancelInv with "HcInv Hcmem") as "[HcInv HcSt]". *)
      ewp_pure_steps.
      unfold promiseSt.
      iDestruct "HpSt" as "[[%y' (_&_&Hγ')]|[%l [%ks (Hp&_&Hl&Hks)]]]";
      first by iDestruct (claim_uniqueness γ with "[$]") as "HFalse".
      ewp_bind_rule. iApply (ewp_load with "Hp"). simpl.
      iIntros "!> Hp !>". ewp_pure_steps.
      iApply (ewp_bind' (AppRCtx _)); first done.
      set I : list val → iProp Σ := (λ us,
        (∃ n, is_queue q (ready q (λ v : val, ⌜v = #()⌝)) n) ∗
        (∃ vs, ⌜ us ++ vs = ks ⌝ ∗ [∗ list] k ∈ vs, ready q Φ k))%I.
      iApply (ewp_mono with "[Hks Hl Hq]").
      { iApply (list_iter_spec _ I with "[] Hl [Hq Hks]");
        last (by iSplitL "Hq"; [iExists n|iExists ks]; iFrame).
        iIntros "!#" (us k vs) "<- [Hq  [%vs' [%Heq Hvs']]]".
        specialize (app_inj_1 us us vs' (k :: vs) eq_refl Heq) as [_ ->].
        iDestruct "Hvs'" as "[Hk Hvs]". iDestruct "Hq" as "[%m Hq]".
        ewp_pure_steps. iApply (ewp_mono with "[Hq Hk]").
        { iApply (queue_push_spec with "Hq"). rewrite !ready_unfold.
          iIntros (y' n') "-> HpInv HcInv Hq". ewp_pure_steps.
          by iSpecialize ("Hk" with "Hy HpInv HcInv Hq").
        }
        iIntros (?) "Hq !>".

        iSplitL "Hq"; [iExists (S m)|iExists vs]; iFrame.
        iPureIntro. by rewrite -app_assoc.
      }
      iIntros (?) "[Hl [[%m Hq]  _]] !>". simpl.
      ewp_pure_steps. ewp_bind_rule.
      iApply (ewp_store with "Hp"). iIntros "!> Hp !>". simpl.
      ewp_pure_steps. iApply (ewp_next with "[HpInv Hγ Hp] HcInv Hq").
      { iApply "HpInv". iLeft. iExists (InjRV y). by iFrame. }
    (* Effect branch. *)
    - iIntros (request k). rewrite upcl_Coop upcl_AWAIT upcl_ASYNC upcl_FAIL upcl_WITH_OTHER_CONTEXT upcl_WITH_CONTEXT.
      idtac.
      iIntros "[ (%e & %Φ' & ->&[#Hnone' He]&Hk) 
              | [ [%p' [%Φ' (->&[%γ' #Hmem']&Hk)]] 
              | [ (->&_&_) 
              | [ (%cf' & %state' & %P & %f & -> & [Hcancel' Hf] &Hk) 
              | (%P & %f & -> & Hf & Hk)  ] ] ] ]";
      first ewp_pure_steps.
      (* Async. *)
      + 
        ewp_bind_rule. iApply ewp_mono; [iApply ((ewp_new_promise _ q Φ') with "Hnone'")|].
        iIntros (y) "[%p' [%γ' (->&Hγ'&HpSt')]] !>". simpl.
        ewp_pure_steps.
        ewp_bind_rule. iApply ewp_mono; [iApply (ewp_new_cancel_ctx _ )|].
        iIntros (y) "[%cf' [%state' [%δ' (->&HcSt')]]] !>". simpl.
        ewp_pure_steps.
        iApply fupd_ewp.
        iMod (update_promiseInv with "[$]") as "[HpInv #Hmem']". 
        iMod (update_cancelInv with "[$]") as "[HcInv #Hcmem']". 
        iModIntro.
        ewp_pure_steps. iApply (ewp_bind' (AppRCtx _)). { done. }
        iApply (ewp_mono with "[Hq Hk Hγ]").
        { iApply (queue_push_spec with "Hq"). rewrite ready_unfold.
          iIntros (y m) "-> HpInv HcInv Hq". ewp_pure_steps.
          iApply "Hk".
          iSplit. by iExists γ'. by iExists δ'. iNext.
          (* a.d. TODO how does HcInv and Hmem fit together here? *)
          iApply ("IH_handler" with "Hγ Hq HpInv Hmem HcInv Hcmem Hnone").
        }
        iIntros (?) "Hq !>". simpl. do 3 ewp_value_or_step.
        iApply ("IH" with "He Hγ' Hq HpInv Hmem' HcInv Hcmem' Hnone'").
      (* Await. *)
      + 
        iDestruct (lookup_promiseInv with "HpInv Hmem'") as "[HpInv HpSt']".
        ewp_pure_steps. ewp_bind_rule. simpl.
        iDestruct "HpSt'" as "[[%y' (Hp'&#Hy&Hγ')]|[%l [%ks (Hp'&#Hnone'&Hl&Hks)]]]".
        (* Promise is fulfilled. *)
        * iApply (ewp_load with "Hp'"). iIntros "!> Hp' !>".
          ewp_pure_steps. iApply ("Hk" with "Hy").
          iApply ("IH_handler" with "Hγ Hq [HpInv Hp' Hγ'] Hmem HcInv Hcmem Hnone").
          iApply "HpInv". iLeft. by iExists y'; iFrame.
        (* Promise is unfulfilled. *)
        * iApply (ewp_load with "Hp'"). iIntros "!> Hp' !>".
          ewp_pure_steps.
          iApply (ewp_bind [(AppRCtx _); (StoreRCtx _); InjRCtx]); first done.
          iApply (ewp_mono with "[Hl]"); [iApply (list_cons_spec with "Hl")|].
          iIntros (l') "Hl' !>". simpl. ewp_pure_steps. ewp_bind_rule.
          iApply (ewp_store with "Hp'"). iIntros "!> Hp' !>". simpl.
          ewp_pure_steps.
          iApply (ewp_next with "[HpInv Hks Hl' Hp' Hk Hγ] HcInv Hq").
          iApply "HpInv". iRight. iExists l', (k :: ks). iFrame.
          iSplit; first by iAssumption.
          rewrite ready_unfold. iIntros (y' m) "#Hy' HpInv HcInv Hq".
          iApply ("Hk" with "Hy'"). iNext.
          by iApply ("IH_handler" with "Hγ Hq HpInv Hmem HcInv Hcmem Hnone").
      (* Fail *)
      + 
        iDestruct (lookup_promiseInv with "HpInv Hmem") as "[HpInv HpSt]".
        (* iDestruct (lookup_cancelInv with "HcInv Hcmem") as "[HcInv HcSt]". *)
        ewp_pure_steps. ewp_bind_rule. simpl.
        iDestruct "HpSt" as "[[%y' (_&_&Hγ')]|[%l [%ks (Hp&#Hnone'&Hl&Hks)]]]";
        first by iDestruct (claim_uniqueness γ with "[$]") as "HFalse".
        ewp_bind_rule. simpl.
        iApply (ewp_load with "Hp"). simpl.
        iIntros "!> Hp !>". ewp_pure_steps.
        iApply (ewp_bind' (AppRCtx _)); first done.
        set I : list val → iProp Σ := (λ us,
          (∃ n, is_queue q (ready q (λ v : val, ⌜v = #()⌝)) n) ∗
          (∃ vs, ⌜ us ++ vs = ks ⌝ ∗ [∗ list] k ∈ vs, ready q Φ k))%I.
        iApply (ewp_mono with "[Hks Hl Hq]").
        { iApply (list_iter_spec _ I with "[] Hl [Hq Hks]");
          last (by iSplitL "Hq"; [iExists n|iExists ks]; iFrame).
          iIntros "!#" (us k' vs) "<- [Hq  [%vs' [%Heq Hvs']]]".
          specialize (app_inj_1 us us vs' (k' :: vs) eq_refl Heq) as [_ ->].
          iDestruct "Hvs'" as "[Hk' Hvs]". iDestruct "Hq" as "[%m Hq]".
          ewp_pure_steps. iApply (ewp_mono with "[Hq Hk']").
          { iApply (queue_push_spec with "Hq"). rewrite !ready_unfold.
            iIntros (y' n') "-> HpInv HcInv Hq". ewp_pure_steps.
            iApply ("Hk'" with "[] [HpInv] [HcInv]").
            - iAssumption.
            - iFrame.
            - iFrame.
            - iFrame.  
            (* by iSpecialize ("Hk'" with "Hy HpInv HcInv Hq"). *)
          }
          iIntros (?) "Hq !>".
          iSplitL "Hq"; [iExists (S m)|iExists vs]; iFrame.
          iPureIntro. by rewrite -app_assoc.
        }
        iIntros (?) "[Hl [[%m Hq]  _]] !>". simpl.
        ewp_pure_steps. ewp_bind_rule.
        iApply (ewp_store with "Hp"). iIntros "!> Hp !>". simpl.
        ewp_pure_steps. 
        (* a.d. TODO where does the return branch get the Phi from? *)
        iAssert (promiseSt q p γ Φ) with "[Hp Hγ]" as "HpSt".
        { iLeft. iExists (RNone'). iFrame. by iAssumption. }
        iApply (ewp_next with "[HpInv HpSt] HcInv").
        { iApply "HpInv". iApply "HpSt". }
        by iApply "Hq".
      (* WithOtherContext *)
      + iDestruct "Hcancel'" as "(%δ' & Hcmem')".
        iDestruct (lookup_cancelInv with "HcInv Hcmem'") as "[HcInv HcSt]".
        ewp_pure_steps.
        ewp_bind_rule.
        iApply (ewp_mono with "[Hf HcSt]").
        { iApply "Hf". by iFrame. }
        iIntros (v) "[HP HcSt] !>". simpl.
        ewp_pure_steps. 
        iApply ("Hk" with "HP").
        iApply ("IH_handler" with "Hγ Hq HpInv Hmem [HcInv HcSt] Hcmem Hnone").
        by iApply "HcInv".
      (* WithContext *)
      + iDestruct (lookup_cancelInv with "HcInv Hcmem") as "[HcInv HcSt]".
        ewp_pure_steps.
        ewp_bind_rule. simpl.
        iApply (ewp_mono with "[Hf HcSt]").
        { iApply "Hf". by iFrame. }
        iIntros (v) "[HP HcSt] !>". simpl.
        ewp_pure_steps. 
        iApply ("Hk" with "HP").
        iApply ("IH_handler" with "Hγ Hq HpInv Hmem [HcInv HcSt] Hcmem Hnone").
        by iApply "HcInv".
  Qed.

  Print longproof.

End verification.

Section closed_proof.
  Context `{!heapGS Σ, !promiseGpreS Σ, !cancelGpreS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Lemma promise_and_cancelInv_init :
    ⊢ |==> ∃ (_ : promiseGS Σ) (_ : cancelGS Σ), (∀ q, promiseInv q) ∗ cancelInv.
  Proof.
    iIntros. 
    iMod (own_alloc (● (∅ : gmap (loc * gname) _))) as (γ) "HI";
      first by rewrite auth_auth_valid.
    iMod (own_alloc (● (∅ : gmap (loc * loc * gname) _))) as (δ) "HJ";
      first by rewrite auth_auth_valid.
    iModIntro. iExists {| promise_inG := _; promise_name := γ; |}.
    iExists {| cancel_inG := _; cancel_name := δ; |}.
    iSplitL "HI".
    - iIntros (q). iExists ∅. rewrite /isPromiseMap fmap_empty. by iFrame.
    - iExists ∅. rewrite /isCancelMap. by iFrame.
  Qed.

  Local Program Instance async_comp_lib `{!promiseGS Σ} `{!cancelGS Σ}:
    AsyncCompLib (Σ:=Σ) := {
    coop := Coop;
    is_promise := λ v Φ, (∃ (p : loc), ⌜ v = #p ⌝ ∗ isPromise p Φ)%I;
    is_promise_Persistent := _;
    is_cancel := λ v1 v2, (∃ (cf state : loc), ⌜ v1 = #cf ⌝ ∗ ⌜ v2 = #state ⌝ ∗ isCancel cf state)%I;
    is_cancel_Persistent := _;
    io_log := λ v, (∃ δ (i : nat), ⌜ v = #i ⌝ ∗ io_log_cancelled δ i)%I;
    io_log_Persistent := _;
  }.
  Next Obligation. 
    iIntros (????) "[#Hnone He]"; 
    iApply (ewp_mono with "[He]").
    iApply ewp_async.
    iSplit. by iAssumption. by iApply "He".
    iIntros (?) "(%p & %cf & %state & -> & Hp & Hc)".
    iModIntro. iExists #p, #cf, #state.
    iSplit; first done.
    iSplitL "Hp".
    iExists p. iSplit; by done.
    iExists cf, state. by iSplit; [done|iSplit]; done.
  Qed.
  Next Obligation.
    by iIntros (????) "[% [-> ?]]"; iApply ewp_await. Qed.
  Next Obligation.
    iIntros (????) "(%cf' & %state' & -> & -> & Hc)". by iApply ewp_fiber_cancel.
  Qed.

  Theorem run_correct main : run_spec main.
  Proof.
    iIntros "He". 
    iMod promise_and_cancelInv_init as "(%HpromiseGS & %HcancelGS & HpInv & HcInv)".
    iSpecialize ("He" $! async_comp_lib). iModIntro.
    iApply (ewp_run _ (λ _, True)%I with "[] HpInv HcInv").
    - done.
    - iApply (ewp_mono with "He"). by auto.
  Qed.

End closed_proof.

Print Assumptions run_correct.