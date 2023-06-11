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

(* a.d. TODO 
  make q a variable instead of parameterizing the protocol.
  use -∗ instead of ∗ for preconditions. 
  maybe remove nat from Φ
  consistent naming and proof structure *)

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
Notation GetContext := (InjR (InjR #())) (only parsing).

Notation Async' e := (InjLV (InjLV e)) (only parsing).
Notation Await' p := (InjLV (InjRV p)) (only parsing).
Notation FFail' := (InjRV (InjLV #())) (only parsing).
Notation GetContext' := (InjRV (InjRV #())) (only parsing).

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
  Definition get_context : val := (λ: <>, do: (GetContext))%V.

  Definition yield : val := (λ: <>, async (λ: <>, #()))%V.

  Definition io : val := (λ: <>,
    let: "cfstate" := get_context #() in
    let: "cf" := Fst "cfstate" in
    let: "state" := Snd "cfstate" in 
    if: Load "cf"
    then 
      ffail #()
    else
      (* if the fiber is not cancelled, increment and return. *)
      "state" <- (Load "state") + #1;;
      #())%V.

  Definition fiber_cancel : val := (λ: "cfstate",
    (* effect returns the same cfstate but with permission to mutate it. *)
    let: "cf" := Fst "cfstate" in
    let: "state" := Snd "cfstate" in
    "cf" <- #true;;
    Load "state")%V.

  (* a.d. the actual programs we want to run. *)
  Definition child : val := (λ: <>, 
    io #();;
    yield #();;
    io #();;
    #())%V.

  Definition parent : val := (λ: <>,
    let: "pcfstate" := async child in
    let: "p" := Fst "pcfstate" in
    let: "cfstate" := Snd "pcfstate" in
    let: "state1" := fiber_cancel "cfstate" in
    let: "result" := await "p" in
    let: "state2" := Snd "result" in
    if: "state1" = "state2"
      then #()
      else #() #() (* Unreachable *)
  )%V.

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
                  let: "cfstate" := new_cancel_ctx #() in
                  let: "p" := new_promise #() in
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
          | (* FFail/GetContext *) InjR "e1" =>
              (match: "e1" with
                (* FFail *) InjL <> =>
                  (match: Load "p" with
                    (* Done: *) InjL <> => #() #() (* Unreachable! *)
                  | (* Waiting: *) InjR "ks" =>
                    (* a.d. TODO maybe assert "cf" == #true *)
                    let: "result" := (RNone', Load "state") in
                    list_iter (λ: "k", queue_push "q" (λ: <>, "k" "result")) "ks";;
                    "p" <- Done "result";;
                    next "q"
                  end)
              | (* GetContext *) InjR <> =>
                "k" "cfstate"
              end)
          end)
      | return (λ: "v",
          match: Load "p" with
            (* Done: *) InjL <> => #() #() (* Unreachable! *)
          | (* Waiting: *) InjR "ks" =>
              let: "result" := (RSome "v", Load "state") in
              list_iter (λ: "k", queue_push "q" (λ: <>, "k" "result")) "ks";;
              "p" <- Done "result";;
              next "q"
          end)
      end
    in
    let: "cfstate" := new_cancel_ctx #() in
    let: "p" := new_promise #() in
    "fulfill" "p" "cfstate" "main"
  )%V.

End implementation.


(* ========================================================================== *)
(** * Specification. *)



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
(* fstate = fiber state (promise + cancellation context) *)
Class fstateGpreS Σ := {
  fstate_mapG :> inG Σ
    (authR (gmapUR ((loc * gname) * (loc * loc * gname)) (agreeR (laterO (val -d> (iPropO Σ))))));
  torchG :> inG Σ (exclR unitO);
  cancelG :> inG Σ (csumR (exclR natO) (agreeR natO));
}.

(* A concrete instance of [Σ] for which the assumption [promisesGS Σ] holds. *)
Definition fstateΣ := #[
  GFunctor (authRF
    (gmapURF ((loc * gname) * (loc * loc * gname)) (agreeRF (laterOF (valO -d> idOF)))));
  GFunctor (exclR unitO);
  GFunctor (csumR (exclR natO) (agreeR natO))
].

(* The proof of the previous claim. *)
Instance subG_promiseΣ {Σ} : subG fstateΣ Σ → fstateGpreS Σ.
Proof. solve_inG. Qed.

Class fstateGS Σ := {
  fstate_inG :> fstateGpreS Σ;
  fstate_name : gname;
}.


(* -------------------------------------------------------------------------- *)
(** Predicates. *)

Section predicates.
  Context `{!heapGS Σ, !fstateGS Σ}.
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

  Definition isMember p γ cf state δ Φ :=
    own fstate_name (◯ {[((p, γ), (cf, state, δ)) := promise_unfold Φ]}).

  Definition isFstate (p : loc) (cf state : loc) Φ : iProp Σ := (
    ∃ γ δ, isMember p γ cf state δ Φ
  ).

  Definition isFstateMap (M : gmap ((loc * gname) * (loc * loc * gname)) (val → iProp Σ)) :=
    own fstate_name (● (promise_unfold <$> M : gmap _ _)).

  Definition io_log_active (δ : gname) (i : nat) : iProp Σ :=
    own δ (Cinl (Excl i)).
  Definition io_log_frozen (δ : gname) (i : nat) : iProp Σ :=
    own δ (Cinr (to_agree i)).

  Definition fstateInv_pre
    (ready : val -d> (val -d> iPropO Σ) -d> val -d> iPropO Σ)
    (q : val) : iProp Σ := (
    ∃ M, isFstateMap M ∗
      [∗ map] args ↦ Φ ∈ M, let '((p, γ), (cf, state, δ)) := args in
      (* state always points to some value *)
      ∃ (i: nat), state ↦ #i ∗
        (((* Fulfilled ∧ cancellation does not matter: *) 
          ∃ (b : bool) (res: val), cf ↦ #b ∗ io_log_frozen δ i ∗
            p ↦ Done' res ∗ □ Φ res ∗ torch γ ∗
            (⌜ res = (RNone', #i)%V ⌝ ∨ ∃ (y: val), ⌜ res = (RSome' y, #i)%V ⌝ ))
      ∨
        ((* Unfulfilled *) 
          (∃ (b : bool), cf ↦ #b ∗ 
            (if b then io_log_frozen δ i
                 else io_log_active δ i)) ∗
          (∀ (i: nat), □ Φ (RNone', #i)%V) ∗
          (∃ l ks,
           p ↦ Waiting' l ∗ 
           is_list l ks   ∗
          (* a.d. TODO predicate for ready is not closed! needs the delta from above. *)
           ▷ [∗ list] k ∈ ks, ready q (λ res, Φ res ∗ ∃ (j: nat) (y: val), ⌜ res = (y, #j)%V ⌝ ∗ io_log_frozen δ j) k))
      )
  )%I.

  Definition ready_pre :
    (val -d> (val -d> iPropO Σ) -d> val -d> iPropO Σ) →
    (val -d> (val -d> iPropO Σ) -d> val -d> iPropO Σ) := (λ ready q Φ k,
    ∀ (y : val) n,
      □ Φ y -∗
        fstateInv_pre ready q -∗
          ▷ is_queue q (ready q (λ v, ⌜ v = #() ⌝)%I) n -∗
             EWP (k : val) y <| ⊥ |> {{ _, True }}
    )%I.

  Local Instance ready_contractive : Contractive ready_pre.
  Proof.
    rewrite /ready_pre /fstateInv_pre=> n ready ready' Hn q Φ k.
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

  Definition fstateInv (q : val) : iProp Σ :=
    fstateInv_pre ready q.

  Definition fstateSt q p γ cf state δ (Φ : val -d> iPropO Σ) : iProp Σ :=
    ∃ (i: nat), state ↦ #i ∗
      (((* Fulfilled ∧ cancellation does not matter: *) 
        ∃ (b : bool) (res: val), cf ↦ #b ∗ io_log_frozen δ i ∗
          p ↦ Done' res ∗ □ Φ res ∗ torch γ ∗
          (⌜ res = (RNone', #i)%V ⌝ ∨ ∃ (y: val), ⌜ res = (RSome' y, #i)%V ⌝ ))
    ∨
      ((* Unfulfilled *) 
        (∃ (b : bool), cf ↦ #b ∗ 
          (if b then io_log_frozen δ i
                else io_log_active δ i)) ∗
        (∀ (i: nat), □ Φ (RNone', #i)%V) ∗
        (∃ l ks,
          p ↦ Waiting' l ∗ 
          is_list l ks   ∗
          ▷ [∗ list] k ∈ ks, ready q (λ res, Φ res ∗ ∃ (j: nat) (y: val), ⌜ res = (y, #j)%V ⌝ ∗ io_log_frozen δ j) k))
    ).

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
  Global Instance fstateInv_ne n : Proper ((dist n) ==> (dist n)) fstateInv.
  Proof. by solve_proper. Qed.
  Global Instance fstateInv_proper : Proper ((≡) ==> (≡)) fstateInv.
  Proof. by solve_proper. Qed.

  (* [promiseSt]. *)
  Global Instance fstateSt_ne n q p γ cf state δ:
    Proper ((dist n) ==> (dist n)) (fstateSt q p γ cf state δ ).
  (* Proof. by solve_proper. Qed. *)
  Admitted.
  Global Instance fstateSt_proper q p γ cf state δ :
    Proper ((≡) ==> (≡)) (fstateSt q p γ cf state δ ).
  (* Proof. by solve_proper. Qed. *)
  Admitted.

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

    Lemma claim_froze_agreement δ : ∀ i j, (io_log_frozen δ i ∗ io_log_frozen δ j) -∗ ⌜i = j⌝.
    Proof.
      intros i j.
      rewrite /io_log_frozen -own_op own_valid csum_validI.
      simpl.
      iIntros "%Hagree".
      iPureIntro.
      by specialize (to_agree_op_inv_L _ _ Hagree) as Hagree'.
    Qed.

    (* From iris.algebra Require Import excl. *)
    Lemma freeze_io_log (δ : gname) (i : nat) :
      io_log_active δ i ==∗ io_log_frozen δ i.
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
    Global Instance isMember_Persistent p γ cf state δ Φ : Persistent (isMember p γ cf state δ Φ).
    Proof. by apply _. Qed.
    Global Instance isFstate_Persistent p cf state Φ: Persistent (isFstate p cf state Φ).
    Proof. by apply _. Qed.
    Global Instance io_log_frozen_Persistent (δ: gname) (i: nat) : Persistent (io_log_frozen δ i).
    Proof. by apply _. Qed.

    Lemma update_fstate_map M p γ cf state δ Φ:
      M !! ((p, γ), (cf, state, δ)) = None →
        isFstateMap M ==∗
          isFstateMap (<[((p,γ),(cf,state,δ)):=Φ]> M) ∗ isMember p γ cf state δ Φ.
    Proof.
      intros Hlkp. unfold isFstateMap. iIntros "HM".
      iMod (own_update with "HM") as "[HM HiP]".
      { apply (@auth_update_alloc (gmapUR _ _) (promise_unfold <$> M)).
        apply (alloc_singleton_local_update _ ((p, γ), (cf, state, δ)) (promise_unfold Φ)).
        by rewrite /= lookup_fmap Hlkp. done. }
      iModIntro. iFrame. by rewrite fmap_insert.
    Qed.

    Lemma claim_membership M p γ cf state δ Φ:
      isFstateMap M ∗ isMember p γ cf state δ Φ -∗ ∃ Φ',
        ⌜ M !! ((p, γ), (cf, state, δ)) = Some Φ' ⌝ ∗ (promise_unfold Φ' ≡ promise_unfold Φ).
    Proof.
      rewrite /isFstateMap /isMember.
      rewrite -own_op own_valid auth_both_validI /=.
      iIntros "[HM #HpM]". iDestruct "HM" as (M') "#HM".
      rewrite gmap_equivI gmap_validI.
      iSpecialize ("HM" $! ((p, γ), (cf, state, δ))). iSpecialize ("HpM" $! ((p, γ), (cf, state, δ))).
      rewrite lookup_fmap lookup_op lookup_singleton.
      rewrite option_equivI.
      case: (M  !! ((p, γ), (cf, state, δ)))=> [Φ'|] /=; [|
      case: (M' !! ((p, γ), (cf, state, δ)))=> [Φ'|] /=; by iExFalso].
      iExists Φ'. iSplit; first done.
      case: (M' !! ((p, γ), (cf, state, δ)))=> [Ψ'|] //=.
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

    Lemma fstateSt_non_duplicable q p γ γ' cf state δ δ' Φ Φ' :
      fstateSt q p γ cf state δ Φ -∗ fstateSt q p γ' cf state δ' Φ' -∗ False.
    Proof.
      assert (⊢ ∀ q p γ cf state δ Φ, fstateSt q p γ cf state δ Φ -∗ ∃ v, p ↦ v)%I as Haux.
      { rewrite /fstateSt.
        iIntros (???????) "(%i & Hstate & 
                           [ (%b & %res & Hcf & Hio & Hp & H)
                           | (_ & _ & %l & %ks & Hp & _ ) ])";
          auto. }
      iIntros "Hp Hp'".
      iPoseProof (Haux with "Hp")  as "[%v  Hp]".
      iPoseProof (Haux with "Hp'") as "[%v' Hp']".
      by iDestruct (mapsto_ne with "Hp Hp'") as "%Hneq".
    Qed.

    Lemma fstateSt_proper' q p γ cf state δ Φ Φ':
      (Φ ≡ Φ') -∗ fstateSt q p γ cf state δ Φ -∗ fstateSt q p γ cf state δ Φ'.
    Proof. iIntros "HΦ Hp". by iRewrite -"HΦ". Qed.

    Lemma update_fstateInv q p γ cf state δ Φ :
      fstateInv q ∗ fstateSt q p γ cf state δ Φ ==∗
        fstateInv q ∗ isMember p γ cf state δ Φ.
    Proof.
      iIntros "[HpInv Hp]". rewrite /fstateInv.
      iDestruct "HpInv" as (M) "[HM HInv]".
      destruct (M !! ((p, γ), (cf, state, δ))) as [Ψ|] eqn:Hlkp.
      - rewrite (big_opM_delete _ _ _ _ Hlkp).
        iDestruct "HInv" as "[Hp' _]".
        rewrite /fstateSt.
        iDestruct (fstateSt_non_duplicable with "Hp Hp'") as "HFalse"; by iExFalso.
      - iMod (update_fstate_map M p γ cf state δ Φ Hlkp with "HM") as "[HM Hmem]".
        iModIntro. iFrame. iExists (<[((p, γ), (cf, state, δ)):=Φ]> M). iFrame.
        rewrite big_opM_insert; last done. by iFrame.
    Qed.

    Lemma lookup_fstateInv q p γ cf state δ Φ :
      fstateInv q -∗ isMember p γ cf state δ Φ -∗
        ▷ ((fstateSt q p γ cf state δ Φ -∗ fstateInv q) ∗ fstateSt q p γ cf state δ Φ).
    Proof.
      iIntros "HpInv Hmem". rewrite /fstateInv.
      iDestruct "HpInv" as (M) "[HM HInv]".
      iDestruct (claim_membership M p γ cf state δ Φ with "[$]") as "[%Φ' [%Hlkp #Heq]]".
      iPoseProof (promise_unfold_equiv with "Heq") as "#Heq'". iNext.
      iDestruct (big_sepM_delete _ _ ((p, γ), (cf, state, δ)) with "HInv")
        as "[HpSt HInv]"; first done.
      iSplitL "HInv HM".
      - iIntros "HpSt". iExists M. iFrame.
        rewrite (big_opM_delete _ _ _ _ Hlkp). iFrame.
        iApply (fstateSt_proper' q p γ cf state δ Φ Φ' with "[] HpSt").
        rewrite discrete_fun_equivI. iIntros (x).
        by iRewrite ("Heq'" $! x).
      - iApply (fstateSt_proper' q p γ cf state δ Φ' Φ with "[] HpSt").
        by rewrite discrete_fun_equivI.
    Qed.

  End promise_preds.
End predicates.


(* -------------------------------------------------------------------------- *)
(** Protocol [Coop]. *)

Section protocol_coop.
  Context `{!heapGS Σ, !fstateGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  (* a.d. TODO do we need q'' for the postcondition of e? *)
  (* a.d. TODO I think q must also be a parameter of the protocol. *)
  Definition pEff := (gname * val) -> iEff Σ.
  Definition ASYNC_pre (Coop : pEff) (q: val): iEff Σ :=
    >> e Φ >> !(Async'  e) {{ fstateInv q ∗ (∀ (i: nat), □ Φ (RNone', #i)%V) ∗ (∀ γ, torch γ ∗ fstateInv q -∗ EWP e #() <|Coop (γ, q) |> {{v, torch γ ∗ fstateInv q ∗ ∀ (i: nat), □ Φ (RSome' v, #i)%V}}) }};
    << (p : loc) (cf state : loc) << ?((#p, (#cf, #state))%V)        {{fstateInv q ∗ isFstate p cf state Φ }} @ OS.
  Definition AWAIT (q: val): iEff Σ :=
    >> (p : loc) Φ (cf state : loc) (δ : gname) >> !(Await' #p) {{fstateInv q ∗ (∃ γ, isMember p γ cf state δ Φ)}};
    << (res: val) << ?(res)         {{∃ (y_opt: val) (i : nat), ⌜ res = (y_opt, #i)%V ⌝ ∗ fstateInv q ∗ □ Φ res ∗ io_log_frozen δ i }} @ OS.

  Definition FAIL (γ: gname) (q: val) : iEff Σ :=
    >> (_: val) >> !(FFail') {{torch γ ∗ fstateInv q}};
    << (_: val) << ?(#()) {{False}} @ OS.
  Definition GET_CONTEXT (γ: gname ): iEff Σ :=
    >> (_: val) >> !(GetContext') {{torch γ}};
    << (cf state : loc) (δ : gname) << ?((#cf, #state)%V) {{torch γ ∗ ∃ p Φ, isMember p γ cf state δ Φ}} @ OS.
  
  Definition Coop_pre : pEff → pEff := (λ Coop,
    λ '(γ, q), ASYNC_pre Coop q <+> AWAIT q <+> FAIL γ q <+> GET_CONTEXT γ
  )%ieff.

  (* Local Instance Coop_pre_contractive : Contractive (Coop_pre).
  Proof.
    intros γ.
    rewrite /Coop_pre /AWAIT /ASYNC_pre=> n Coop Coop' HCoop.
    by repeat (apply ewp_ne||apply iEffPre_base_ne||f_contractive||f_equiv).
  Qed. *)
  (* Definition Coop_def: (gname → iEff Σ) := fixpoint (Coop_pre).
  Definition Coop_aux : seal Coop_def. Proof. by eexists. Qed.
  Definition Coop := Coop_aux.(unseal).
  Definition Coop_eq : Coop = Coop_def := Coop_aux.(seal_eq).*)
  Axiom Coop: pEff.
  Global Lemma Coop_unfold : ∀ γq, Coop γq ≡ Coop_pre Coop γq.
  Proof.
    (* intros γ.
    rewrite Coop_eq /Coop_def.
    by apply (fixpoint_unfold (Coop_pre γ)). *)
  Admitted.

  Definition ASYNC  := ASYNC_pre (Coop).

  Lemma upcl_Coop γ q v Φ' :
    iEff_car (upcl OS (Coop (γ, q))) v Φ' ⊣⊢
      iEff_car (upcl OS (ASYNC q)) v Φ' ∨
      iEff_car (upcl OS (AWAIT q)) v Φ' ∨
      iEff_car (upcl OS (FAIL γ q)) v Φ' ∨ 
      iEff_car (upcl OS (GET_CONTEXT γ)) v Φ'.
  Proof.
    transitivity (iEff_car (upcl OS (Coop_pre Coop (γ, q))) v Φ').
    - iApply iEff_car_proper. by rewrite {1}Coop_unfold.
    - rewrite upcl_sum upcl_sum upcl_sum /ASYNC.
      done.
  Qed.

  Lemma upcl_ASYNC q v Φ' :
    iEff_car (upcl OS (ASYNC q)) v Φ' ≡
      (∃ e Φ, ⌜ v = Async' e ⌝ ∗ (fstateInv q ∗ (∀ (i: nat), □ Φ (RNone', #i)%V) ∗ (∀ γ', torch γ' ∗ fstateInv q -∗ EWP e #() <| Coop (γ', q) |> {{ v, torch γ' ∗ fstateInv q ∗ ∀ (i: nat), □ Φ (RSome' v, #i)%V }})) ∗
            (∀ (p : loc) (cf state : loc), (fstateInv q ∗ isFstate p cf state Φ) -∗ Φ' ((#p, (#cf, #state))%V) ))%I.
  Proof. 
    rewrite /ASYNC (upcl_tele' [tele _ _] [tele _ _ _]); by done.
  Qed.

  Lemma upcl_AWAIT q v Φ' :
    iEff_car (upcl OS (AWAIT q)) v Φ' ≡
      (∃ (p : loc) Φ (cf state : loc) δ, ⌜ v = Await' #p ⌝ ∗ (fstateInv q ∗ (∃ γ, isMember p γ cf state δ Φ)) ∗
          (∀ (res: val), (∃ (y_opt: val) (i: nat), ⌜ res = (y_opt, #i)%V ⌝ ∗ fstateInv q ∗ □ Φ res ∗ io_log_frozen δ i) -∗ Φ' res%V))%I.
  Proof. 
    rewrite /AWAIT. rewrite (upcl_tele' [tele _ _ _ _ _] [tele _]); by done. 
  Qed.

  Lemma upcl_FAIL γ q v Φ' :
    iEff_car (upcl OS (FAIL γ q)) v Φ' ≡
      (∃ (_: val), ⌜ v = FFail' ⌝ ∗ (torch γ ∗ fstateInv q) ∗
        (∀ (_: val), False -∗ Φ' #()))%I.
  Proof.
    rewrite /FAIL. rewrite (upcl_tele' [tele _] [tele _]); by done.
  Qed.

  Lemma upcl_GET_CONTEXT γ v Φ' :
    iEff_car (upcl OS (GET_CONTEXT γ)) v Φ' ≡ 
      (∃ (_: val), ⌜ v = GetContext' ⌝ ∗ torch γ ∗
        (∀ (cf state : loc) (δ : gname), (torch γ ∗ ∃ p Φ, isMember p γ cf state δ Φ) -∗ Φ' (#cf, #state)%V)
      )%I.
  Proof.
    rewrite /GET_CONTEXT (upcl_tele' [tele _] [tele _ _ _]); by easy.
  Qed. 
End protocol_coop.


(* ========================================================================== *)
(** * Verification. *)

Section verification.
  Context `{!heapGS Σ, !fstateGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Lemma ewp_new_cancel_ctx Ψ :
    ⊢ EWP (new_cancel_ctx #()) <| Ψ |> {{ y, 
        ∃ (cf state : loc) (δ: gname), ⌜ y = PairV #cf #state ⌝ ∗ cf ↦ #false ∗ state ↦ #0 ∗ io_log_active δ 0 }}.
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
    iFrame.
  Qed.

  Lemma ewp_new_promise Ψ q Φ δ :
    ⊢ EWP (new_promise #()) <| Ψ |> {{ y,
        ∃ p γ, ⌜ y = #(p : loc) ⌝ ∗ torch γ ∗ 
        (∃ l ks,
           p ↦ Waiting' l ∗ 
           is_list l ks   ∗
          ▷ [∗ list] k ∈ ks, ready q (λ res, Φ res ∗ ∃ (j: nat) (y: val), ⌜ res = (y, #j)%V ⌝ ∗ io_log_frozen δ j ) k) }}.
  Proof.
    unfold new_promise. ewp_pure_steps. ewp_bind_rule.
    iApply ewp_mono. { by iApply list_nil_spec. }
    iIntros (l) "Hlist !>". simpl. ewp_pure_steps.
    iApply ewp_alloc. iIntros "!>" (p) "Hp".
    iMod forge_torch as "[%γ Hγ]".
    iModIntro.
    iExists p, γ. iFrame. iSplit; [done|].
    iExists l, []. iFrame. 
    iNext. by done.
  Qed.

  Lemma ewp_next q n Ψ :
    fstateInv q -∗
      is_queue q (ready q (λ v, ⌜ v = #() ⌝)) n -∗
         EWP (next q) <| Ψ |> {{ _, True }}.
  Proof.
    iIntros "HpInv Hq". unfold next. ewp_pure_steps. ewp_bind_rule.
    iApply (ewp_mono with "[Hq]"); [iApply (queue_empty_spec with "Hq")|].
    iIntros (b) "[Hq Hb] !>". simpl.
    case n as [|?]; iDestruct "Hb" as %->; ewp_pure_steps; [done|].
    ewp_bind_rule.
    iApply (ewp_mono with "[Hq]"); [iApply (queue_pop_spec with "Hq")|].
    simpl. iIntros (k) "[Hq Hk] !>".
    rewrite ready_unfold.
    iSpecialize ("Hk" $! #() n with "[//] HpInv Hq").
    iApply ewp_os_prot_mono. { by iApply iEff_le_bottom. } { done. }
  Qed.

  Lemma ewp_async (γ: gname) q (e : val) Φ :
    fstateInv q ∗ (∀ (i: nat), □ Φ (RNone', #i)%V) ∗ (∀ γ', torch γ' ∗ fstateInv q -∗ EWP e #() <| Coop (γ', q) |> {{ v, torch γ' ∗ fstateInv q ∗ ∀ (i: nat), □ Φ (RSome' v, #i)%V }}) ⊢
      EWP (async e) <| Coop (γ, q) |> {{ y,
        ∃ (p : loc) (cf state : loc), ⌜ y = (#p, (#cf, #state))%V ⌝ ∗ fstateInv q ∗ isFstate p cf state Φ }}.
  Proof.
    iIntros "(HfInv & Hnone & He)". unfold async. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_ASYNC. iLeft.
    iExists e, Φ. iSplit; [done|].
    iSplitL.
    - iFrame.
    - iIntros (p cf state) "(HfInv & HfSt)".
      iExists p, cf, state. by iFrame.
  Qed.

  Lemma ewp_await (γ γ': gname) q (p : loc) Φ (cf state : loc) δ' :
    fstateInv q ∗ isMember p γ' cf state δ' Φ ⊢ 
      EWP (await #p) <| Coop (γ, q) |> {{ res, ∃ (y_opt: val) (i: nat), ⌜ res = (y_opt, #i)%V ⌝ ∗ fstateInv q ∗ □ Φ res ∗ io_log_frozen δ' i }}.
  Proof.
    iIntros "[HfInv Hmem]". unfold await. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_AWAIT. iRight; iLeft.
    iExists p, Φ, cf, state, δ'. iSplit; [done|]. iFrame.
    iSplitL "Hmem". by iExists γ'. 
    by auto.
  Qed.

  Lemma ewp_ffail γ q:
    (* a.d. TODO standalone ewp did not work. *)
    fstateInv q ∗ torch γ ⊢ EWP (ffail #()) <| Coop (γ, q) |> {{ _, False }}.
  Proof.
    iIntros "(HfInv & Htorch)".
    unfold ffail. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_FAIL.
    iRight; iRight; iLeft.
    iExists q.
    iSplit; first done. iFrame.
    iIntros (_) "[]".
  Qed.

  Lemma ewp_get_context γ q: 
    torch γ ⊢ EWP (get_context #()) <| Coop (γ, q) |> {{ v, ∃ (cf state : loc) (δ : gname) (p : loc) Φ, ⌜ v = (#cf, #state)%V ⌝ ∗ torch γ ∗ isMember p γ cf state δ Φ}}.
  Proof.
    iIntros "Htorch".
    rewrite /get_context. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_GET_CONTEXT.
    iRight; iRight; iRight.
    iExists #().
    iSplit; first done. iFrame. 
    iIntros (cf state δ) "(Htorch & (%p & %Φ & Hmem))".
    iExists cf, state, δ, p, Φ. iSplit; first done.
    by iFrame.
  Qed.

  Lemma ewp_fiber_cancel γ γ' q (p cf state : loc) (δ' : gname) Φ:
    isMember p γ' cf state δ' Φ ∗ fstateInv q ⊢
    EWP (fiber_cancel (#cf, #state)%V) <| Coop (γ, q) |> {{ v, ∃ (i: nat), ⌜ v = #i ⌝ ∗ fstateInv q ∗ io_log_frozen δ' i }}.
  Proof.
    iIntros "(#Hfmem & HfInv)". 
    rewrite /fiber_cancel. 
    iDestruct (lookup_fstateInv with "HfInv Hfmem") as "[HcInv HcSt]".
    rewrite /fstateSt.
    ewp_pure_steps.
    ewp_bind_rule. simpl. 
    iDestruct "HcSt" as "(%i & Hstate & [ (%b & %res & Hcf & #Hio & Hp & #HΦ & Hγ & Hres) | [(%b & Hcf & Hio) (#HΦ & Hp)] ])".
    2: destruct b.
    - (* fiber is already stopped. Don't have to do anything.
        EIO gives an error for finished fibers *)
      iApply (ewp_store with "Hcf"). 
      iNext. iIntros "Hcf".
      iModIntro.
      simpl. ewp_pure_steps.
      iApply (ewp_load with "Hstate"). iIntros "!> Hstate !>".
      iAssert (fstateSt q p γ' cf state δ' Φ) with "[Hstate Hcf Hp Hγ Hres]" as "HcSt".
      { rewrite /fstateSt.
         iExists i. iFrame. iLeft.
         iExists true, res. iFrame. by iSplit. }
      iExists i. iSplit; first done.
      iSplit; last done.
      by iApply "HcInv".
    - (* running but already cancelled. *)
      iDestruct "Hio" as "#Hio".
      iApply (ewp_store with "Hcf"). 
      iNext. iIntros "Hcf".
      iModIntro.
      simpl. ewp_pure_steps.
      iApply (ewp_load with "Hstate"). iIntros "!> Hstate !>".
      iAssert (fstateSt q p γ' cf state δ' Φ) with "[Hstate Hcf Hp HΦ]" as "HcSt".
      { rewrite /fstateSt.
        iExists i. iFrame. iRight. iSplitL "Hcf".
        iExists true. by iFrame.
        iSplit. by iAssumption.
        iDestruct "Hp" as "(%l & %ks & Hp & Hks & Hlst)".
        iExists l, ks. by iFrame. }
      iExists i. iSplit; first done.
      iSplit; last done.
      by iApply "HcInv".
    - (* running and not yet cancelled. *)
      iApply (ewp_store with "Hcf"). 
      iNext. iIntros "Hcf".
      iMod (freeze_io_log with "Hio") as "#Hio".
      iModIntro.
      simpl. ewp_pure_steps.
      iApply (ewp_load with "Hstate"). iIntros "!> Hstate !>".
      iAssert (fstateSt q p γ' cf state δ' Φ) with "[Hstate Hcf Hp HΦ]" as "HcSt".
      { iExists i. iFrame. iRight. iSplitL "Hcf".
        iExists true. by iFrame.
        iDestruct "Hp" as "(%l & %ks & Hp & Hks & Hlst)".
        iSplit; first by iAssumption.
        iExists l, ks. by iFrame. }
      iExists i. iSplit; first done.
      iSplit; last done.
      by iApply "HcInv".
  Qed.

  Lemma ewp_io γ q:
    torch γ ∗ fstateInv q ⊢ EWP io #() <| Coop (γ, q) |> {{ _, torch γ ∗ fstateInv q }}.
  Proof.
    iIntros "(Htorch & HcInv)".
    rewrite /io.
    ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply (ewp_mono with "[Htorch]"). 
      by iApply ewp_get_context.
    iIntros (v) "(%cf & %state & %δ & %p & %Φ & -> & (Htorch & #Hfmem)) !>".
    iDestruct (lookup_fstateInv with "HcInv Hfmem") as "[HcInv HcSt]".
    ewp_pure_steps.
    ewp_bind_rule. simpl.
    iDestruct "HcSt" as "(%i & Hstate & [ (%b & %res & Hcf & #Hio & Hp & #HΦ & Hγ & Hres) | [(%b & Hcf & Hio) (#HΦ & Hp)] ])".
    2: destruct b.
    - (* can never happen.
         Since we are running, our fiber cannot be finished.
         But at the moment we don't know that we get our own fiber context.  *)
      iPoseProof (claim_uniqueness with "[Htorch Hγ]") as "Hfalse"; first by iFrame.
      by iExFalso.
    - (* the fiber is cancelled *)
      iDestruct "Hio" as "#Hio".
      iApply (ewp_load with "Hcf"). iIntros "!> Hcf !>".
      ewp_pure_steps. 
      iAssert (fstateSt q p γ cf state δ Φ) with "[Hstate Hcf Hio Hp HΦ]" as "HcSt".
      { iExists i.
        iFrame. iRight. iSplitL "Hcf".
        iExists true. by iFrame.
        iSplit; first by iAssumption.
        iDestruct "Hp" as "(%l & %ks & Hp & Hks & Hlst)".
        iExists l, ks. by iFrame. }
      iSpecialize ("HcInv" with "HcSt").
      iApply (ewp_mono with "[HcInv Htorch]").
        iApply ewp_ffail.
        by iFrame.
      iIntros (_) "[]".
    - (* the fiber is not cancelled. *)
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
      iAssert (fstateSt q p γ cf state δ Φ) with "[Hstate Hcf Hio Hp]" as "HcSt".
      { iExists (i + 1).
        iFrame. iRight. iSplitL "Hcf Hio".
        iExists false. by iFrame.
        iSplit; first by iAssumption.
        iDestruct "Hp" as "(%l & %ks & Hp & Hks & Hlst)".
        iExists l, ks. by iFrame. }
      iSpecialize ("HcInv" with "HcSt").
      iModIntro. ewp_pure_steps.
      by iFrame.
  Qed.
  
  Lemma ewp_child γ q:
    torch γ ∗ fstateInv q -∗
      EWP child #() <| Coop (γ, q) |> {{_, torch γ ∗ fstateInv q}}.
  Proof.
    iIntros "(Htorch & HInv)".
    rewrite /child. ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply (ewp_mono with "[-]"); first iApply ewp_io; iFrame.
    iIntros (v) "(Htorch & HInv) !>".
    ewp_pure_steps.
    ewp_bind_rule. simpl.
    rewrite /yield. ewp_pure_steps.
    iApply (ewp_mono with "[HInv]").
      iApply ewp_async. instantiate (1:=(λ _, True )%I). simpl.
      iFrame. iSplit; first done.
      iIntros (γ') "(Htorch & HInv)". ewp_pure_steps. iFrame. done.
    iIntros (v') "(%p & %cf & %state & -> & HInv & _) !>".
    ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply (ewp_mono with "[-]"); first iApply ewp_io; iFrame.
    iIntros (v'') "(Htorch & HInv) !>".
    ewp_pure_steps. by iFrame.
  Qed.

  Lemma ewp_parent γ q:
    torch γ ∗ fstateInv q -∗ 
      EWP parent #() <| Coop (γ, q) |> {{_, torch γ ∗ fstateInv q}}.
  Proof.
    iIntros "(Htorch & HInv)".
    rewrite /parent. ewp_pure_steps.
    
    ewp_bind_rule. simpl.
    iApply (ewp_mono with "[HInv]"). iApply (ewp_async with "[HInv]").
      instantiate (1:=(λ _, True)%I). iFrame. iSplit; first done.
      iIntros (γ') "(Htorch & HInv)". iApply (ewp_mono with "[-]").
      iApply ewp_child. by iFrame. 
      iIntros (v) "(Htorch & HInv) !>". by iFrame.
    iIntros (v) "(%p & %cf & %state & -> & HInv & (%γ' & %δ' & #Hmem)) !>".
    ewp_pure_steps.

    ewp_bind_rule. simpl.
    iApply (ewp_mono with "[HInv]"). iApply ((ewp_fiber_cancel γ γ') with "[-]").
      by iFrame.
    iIntros (v) "(%i1 & -> & HInv & #Hio1) !>".
    ewp_pure_steps.

    ewp_bind_rule. simpl.
    iApply (ewp_mono with "[HInv]"). iApply (ewp_await with "[HInv]"). 
      by iFrame.
    iIntros (v) "(%y_opt & %i2 & -> & HInv & _ & #Hio2) !>".
    do 8 ewp_value_or_step.
    
    ewp_bind_rule. simpl.
    iDestruct (claim_froze_agreement with "[Hio1 Hio2]") as "->".
      by iSplit; iAssumption.
    ewp_pure_steps. done.
    rewrite bool_decide_eq_true_2; last done.
    ewp_pure_steps. by iFrame.
  Qed.

  Inductive LongProof := longproof.
  Print longproof.

  Lemma ewp_run (main: val) Φ :
    (∀ (i: nat), □ Φ (RNone', #i)%V) -∗ (∀ q, fstateInv q) -∗ 
      (∀ q γ, torch γ ∗ fstateInv q -∗ EWP main #() <| Coop (γ, q) |> {{ v, torch γ ∗ fstateInv q ∗ ∀ (i: nat), □ Φ (PairV (RSome' v) #i)%V }}) -∗
        EWP run main {{ _, True }}.
  Proof.
    (* a.d. TODO where is promiseInv kept? *)
    iIntros "#Hnone HpInv Hmain". unfold run. ewp_pure_steps.
    ewp_bind_rule. iApply ewp_mono. { by iApply queue_create_spec. }
    iIntros (q) "Hq !>". simpl. ewp_pure_steps.
    ewp_bind_rule. simpl. iApply ewp_mono. { by iApply (ewp_new_cancel_ctx _). }
    iIntros (y) "[%cf [%state [%δ (-> & HcSt)]]] !>".
    do 3 ewp_value_or_step.
    ewp_bind_rule. simpl. iApply ewp_mono. { by iApply (ewp_new_promise _ q Φ δ). }
    iIntros (y) "[%p [%γ (->&Hγ&HpSt)]] !>". 
    do 3 ewp_value_or_step.
    iSpecialize ("HpInv" $! q).
    iSpecialize ("Hmain" $! q).
    iAssert (∃ (n : nat), is_queue q (ready q (λ v : val, ⌜v = #()⌝)) n)%I
      with "[Hq]" as "[%n Hq]". { by iExists 0. }
    iApply fupd_ewp.
    iMod (update_fstateInv with "[HpInv HpSt HcSt]") as "[HpInv Hmem]".
    { iSplitL "HpInv". by iAssumption.
      iDestruct "HcSt" as "(Hcf & Hstate & Hio)".
      iExists 0. iSplitL "Hstate". by iAssumption.
      iRight. iSplitL "Hcf Hio".
      iExists false. by iFrame.
      iDestruct "HpSt" as "(%l & %ks & Hp & Hks & Hlst)".
      iSplit; first by iAssumption.
      iExists l, ks. iFrame.
      }
    (* γ not instantiated above. *)
    instantiate (1:=γ).
    iModIntro.
    (* does Φ really need to be quantified? *)
    iRevert "Hnone". iIntros "Hnone".
    (* iSpecialize ("Hmain" with "HcInv"). *)
    iLöb as "IH" forall (main q p γ Φ n cf state δ).
    ewp_pure_steps.
    idtac.
    iSpecialize ("Hmain" $! γ with "[Hγ HpInv]").
      by iFrame.
    iApply (ewp_deep_try_with with "Hmain").
    iLöb as "IH_handler" forall (q γ Φ n cf state δ).
    iDestruct "Hmem" as "#Hmem".
    iDestruct "Hnone" as "#Hnone".
    rewrite deep_handler_unfold.
    iSplit; [|iSplit]; last (by iIntros (??) "HFalse"; rewrite upcl_bottom).
    (* Return branch. *)
    - iIntros (y) "(Hγ & HpInv & #Hsome)".
      iDestruct (lookup_fstateInv with "HpInv Hmem") as "[HpInv HpSt]".
      ewp_pure_steps.
      unfold fstateSt.
      iDestruct "HpSt" as "(%i & Hstate & [ (%b & %res & Hcf & #Hio & Hp & #HΦ & Hγ' & Hres) | [(%b & Hcf & Hio) (#HΦ & (%l & %ks & Hp & Hl & Hks))] ])".
      by iDestruct (claim_uniqueness γ with "[$]") as "HFalse".
      ewp_bind_rule. iApply (ewp_load with "Hp"). simpl.
      iIntros "!> Hp". 
      (* now we can freeze the io log. *)
      iAssert (|==> cf ↦ #b ∗ io_log_frozen δ i)%I with "[Hcf Hio]" as "H".
      { destruct b. by iFrame.
        iFrame. iApply (freeze_io_log with "Hio"). }
      iMod "H" as "(Hcf & #Hio)".
      iModIntro.
      ewp_pure_steps.
      iApply (ewp_bind' (AppRCtx _)); first done.
      ewp_bind_rule.
      iApply (ewp_load with "Hstate"). simpl.
      iIntros "!> Hstate !>". ewp_pure_steps.
      iApply (ewp_bind' (AppRCtx _)); first done. simpl.
      set I : list val → iProp Σ := (λ us,
        (∃ n, is_queue q (ready q (λ v : val, ⌜v = #()⌝)) n) ∗
        (∃ vs, ⌜ us ++ vs = ks ⌝ ∗ [∗ list] k ∈ vs, ready q (λ res, Φ res ∗ ∃ (j: nat) (y: val), ⌜ res = (y, #j)%V ⌝ ∗ io_log_frozen δ j) k))%I.
      iApply (ewp_mono with "[Hks Hl Hq]").
      { iApply (list_iter_spec _ I with "[] Hl [Hq Hks]").
        2: { iSplitL "Hq". iExists n. iFrame. iExists ks. iFrame. done. }
        iIntros "!#" (us k vs) "<- [Hq  [%vs' [%Heq Hvs']]]".
        specialize (app_inj_1 us us vs' (k :: vs) eq_refl Heq) as [_ ->].
        iDestruct "Hvs'" as "[Hk Hvs]". iDestruct "Hq" as "[%m Hq]".
        ewp_pure_steps. iApply (ewp_mono with "[Hq Hk]").
        { iApply (queue_push_spec with "Hq"). rewrite !ready_unfold.
          iIntros (y' n') "-> HpInv Hq". ewp_pure_steps.
          unfold ready_pre.
          iSpecialize ("Hsome" $! i).
          iSpecialize ("Hk" $! (RSome' y, #i)%V n' with "[Hsome] HpInv Hq").
          iModIntro. iSplit; first by iApply "Hsome". iExists i, (RSome' y). by iSplit. 
          iApply "Hk".
        }
        iIntros (?) "Hq !>".
        iSplitL "Hq"; [iExists (S m)|iExists vs]; iFrame.
        iPureIntro. by rewrite -app_assoc.
      }
      iIntros (?) "[Hl [[%m Hq]  _]] !>". simpl.
      ewp_pure_steps. ewp_bind_rule. simpl.
      iApply (ewp_store with "Hp"). iIntros "!> Hp !>".
      ewp_pure_steps. iApply (ewp_next with "[-Hq]").
      { iApply "HpInv". iExists i. iFrame. iLeft. 
        iExists b, (InjRV y, #i)%V. iFrame.
        iSplit; first done.
        iSplit; first iApply "Hsome".
        iRight. iExists y. done. }
      iApply "Hq".
    (* Effect branch. *)
    - iIntros (request k). rewrite upcl_Coop upcl_AWAIT upcl_ASYNC upcl_FAIL upcl_GET_CONTEXT.
      idtac.
      iIntros "[ (%e & %Φ' & ->&(HpInv & #Hnone' & He)&Hk)
              | [ (%p' & %Φ' & %cf' & %state' & %δ' & -> &(HpInv & [%γ' #Hmem'])&Hk)
              | [ (%_ & -> & (Hγ & HcInv) & _) 
              | (%_ & -> & Htorch & Hk) ] ] ]";
      first ewp_pure_steps.
      (* Async. *)
      + ewp_pure_steps.
        ewp_bind_rule. simpl. iApply ewp_mono; [iApply (ewp_new_cancel_ctx _ )|].
        iIntros (y) "[%cf' [%state' [%δ' (->&HcSt')]]] !>".
        ewp_pure_steps.
        ewp_bind_rule. simpl. iApply ewp_mono; [iApply (ewp_new_promise _ q Φ' δ')|].
        iIntros (y) "[%p' [%γ' (->&Hγ'&HpSt')]] !>". 
        ewp_pure_steps.
        iApply fupd_ewp.
        iMod (update_fstateInv with "[HpInv HpSt' HcSt']") as "[HpInv #Hmem']".
        { iSplitL "HpInv". by iAssumption.
          iDestruct "HcSt'" as "(Hcf & Hstate & Hio)".
          iExists 0. iSplitL "Hstate". by iAssumption.
          iRight. iSplitL "Hcf Hio".
          iExists false. by iFrame.
          iDestruct "HpSt'" as "(%l & %ks & Hp & Hks & Hlst)".
          iSplit; first by iAssumption.
          iExists l, ks. iFrame.
          }
        (* γ not instantiated above. *)
        instantiate (1:=γ').
        (* iSpecialize ("He" $! γ' with "[Hγ' HpInv]").
          by iFrame. *)
        iModIntro.
        ewp_pure_steps.
        iApply (ewp_bind' (AppRCtx _)). { done. } simpl.
        iApply (ewp_mono with "[Hq Hk]").
        { iApply (queue_push_spec with "Hq"). rewrite ready_unfold.
          iIntros (y m) "-> HpInv Hq". ewp_pure_steps.
          iApply ("Hk" with "[HpInv]").
          rewrite /fstateInv.
          iFrame. iExists γ', δ'. by iAssumption.
          iNext.
          (* a.d. TODO how does HcInv and Hmem fit together here? *)
          iApply ("IH_handler" with "Hq Hmem Hnone").
        }
        iIntros (?) "Hq !>". simpl. do 3 ewp_value_or_step.
        iApply ("IH" with "He Hγ' Hq HpInv Hmem' Hnone'").
      (* Await. *)
      + (* check promise and return value or wait. should not change much from original. *)
        (* look up fiber state by provided Hmem' *)
        iDestruct (lookup_fstateInv with "HpInv Hmem'") as "[HpInv HpSt']".
        ewp_pure_steps. ewp_bind_rule. simpl.
        iDestruct "HpSt'" as "(%i' & Hstate' & [ (%b' & %res' & Hcf' & #Hio' & Hp' & #HΦ' & Hγ' & Hres') | [(%b' & Hcf' & Hio') (#HΦ' & (%l' & %ks' & Hp' & Hl' & Hks'))] ])".
        (* Promise is fulfilled. *)
        * iApply (ewp_load with "Hp'"). iIntros "!> Hp' !>".
          ewp_pure_steps. iApply ("Hk" with "[-Hq]").
          { iDestruct "Hres'" as "[Hres'|(%y & Hres')]".
            - iExists RNone', i'. iSplit; first done.
              iSplitL; last by iSplit.
              iApply "HpInv".
              iExists i'. iFrame. iLeft.
              iExists b', res'. iFrame. by iSplit.
            - iExists (RSome' y), i'. iSplit; first done.
              iSplitL; last by iSplit.
              iApply "HpInv".
              iExists i'. iFrame. iLeft.
              iExists b', res'. iFrame. 
              iSplit; [done|iSplit]; [done|]. iRight.
              by iExists y. }
          iApply ("IH_handler" with "Hq Hmem Hnone").
        (* Promise is unfulfilled. *)
        * iApply (ewp_load with "Hp'"). iIntros "!> Hp' !>".
          ewp_pure_steps.
          iApply (ewp_bind [(AppRCtx _); (StoreRCtx _); InjRCtx]); first done.
          iApply (ewp_mono with "[Hl']"); [iApply (list_cons_spec with "Hl'")|].
          iIntros (l'') "Hl'' !>". simpl. ewp_pure_steps. ewp_bind_rule.
          iApply (ewp_store with "Hp'"). iIntros "!> Hp' !>". simpl.
          ewp_pure_steps.
          iApply (ewp_next with "[-Hq] Hq").
          iApply "HpInv".
          iExists i'. iFrame. 
          iRight. 
          iSplitL "Hcf' Hio'". iExists b'. iFrame.
          iSplit; first done.
          iExists l'', (k :: ks'). iFrame.
          (* a.d. here it's necessary that cancelInv is in ready without a later. *)
          iNext.
          rewrite ready_unfold /ready_pre. iIntros (y' m) "#(Hy' & %j & %y'' & -> & #Hio') HpInv Hq".
          iApply ("Hk" with "[HpInv Hy']").
          -- iExists y'', j.
             iSplit; first done. iFrame.
             iSplit; first done. iAssumption.
          -- iNext.
             iApply ("IH_handler" with "Hq Hmem Hnone").
      (* Fail *)
      + 
        iDestruct (lookup_fstateInv with "HcInv Hmem") as "[HpInv HpSt]".
        ewp_pure_steps. ewp_bind_rule. simpl.
        iDestruct "HpSt" as "(%i & Hstate & [ (%b & %res & Hcf & #Hio & Hp & #HΦ & Hγ' & Hres) | [(%b & Hcf & Hio) (#HΦ & (%l & %ks & Hp & Hl & Hks))] ])".
        by iDestruct (claim_uniqueness γ with "[$]") as "HFalse".
        ewp_bind_rule. simpl.
        iApply (ewp_load with "Hp"). simpl.
        iIntros "!> Hp". 
        (* now we can freeze the io log. *)
        iAssert (|==> cf ↦ #b ∗ io_log_frozen δ i)%I with "[Hcf Hio]" as "H".
        { destruct b. by iFrame.
          iFrame. iApply (freeze_io_log with "Hio"). }
        iMod "H" as "(Hcf & #Hio)".
        iModIntro.
        ewp_pure_steps.
        ewp_bind_rule.
        iApply (ewp_load with "Hstate"). simpl.
        iIntros "!> Hstate !>". ewp_pure_steps.
        iApply (ewp_bind' (AppRCtx _)); first done.
        set I : list val → iProp Σ := (λ us,
          (∃ n, is_queue q (ready q (λ v : val, ⌜v = #()⌝)) n) ∗
          (∃ vs, ⌜ us ++ vs = ks ⌝ ∗ [∗ list] k ∈ vs, ready q (λ res, Φ res ∗ ∃ (j: nat) (y: val), ⌜ res = (y, #j)%V ⌝ ∗ io_log_frozen δ j) k))%I.
        iApply (ewp_mono with "[Hks Hl Hq]").
        { iApply (list_iter_spec _ I with "[] Hl [Hq Hks]").
          2: { iSplitL "Hq". iExists n. iFrame. iExists ks. iFrame. done. }
          iIntros "!#" (us k' vs) "<- [Hq  [%vs' [%Heq Hvs']]]".
          specialize (app_inj_1 us us vs' (k' :: vs) eq_refl Heq) as [_ ->].
          iDestruct "Hvs'" as "[Hk Hvs]". iDestruct "Hq" as "[%m Hq]".
          ewp_pure_steps. iApply (ewp_mono with "[Hq Hk]").
          { iApply (queue_push_spec with "Hq"). rewrite !ready_unfold.
            iIntros (y' n') "-> HpInv Hq". ewp_pure_steps.
            unfold ready_pre.
            iSpecialize ("Hk" $! (RNone', #i)%V n' with "[] HpInv Hq").
            - iModIntro. iSplit; first by iApply "Hnone".
              iExists i, RNone'. by iSplit.
            - iApply "Hk".
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
        iAssert (fstateSt q p γ cf state δ Φ) with "[-HpInv Hq]" as "HpSt".
        { rewrite /fstateSt.
          iExists i. iFrame. iLeft.
          iExists b, (RNone', #i)%V. iFrame.
          iSplit; first done.
          iSplit; first iApply "Hnone".
          by iLeft. }
        iSpecialize ("HpInv" with "HpSt").
        iApply (ewp_next with "HpInv").
        by iApply "Hq".
      (* GetContext *)
      + ewp_pure_steps.
        iApply ("Hk" with "[Htorch]").
          iFrame. by iExists p, Φ.
        iNext.
        iApply ("IH_handler" with "Hq Hmem Hnone"). 
  Qed.

  Print longproof.


End verification.

Section specification.
  Context `{!heapGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Class AsyncCompLib := {
    coop : (gname * val) → iEff Σ;
    is_fstate : val → val → val → (val → iProp Σ) → iProp Σ;
    is_fstate_Persistent p cf state Φ : Persistent (is_fstate p cf state Φ);
    is_member : val → gname → val → val → gname → (val → iProp Σ) → iProp Σ;
    is_member_Persistent p γ cf state δ Φ : Persistent (is_member p γ cf state δ Φ);
    io_log1 : gname → nat -> iProp Σ;
    io_log2 : gname → nat -> iProp Σ;
    io_log2_Persistent δ i : Persistent (io_log2 δ i);
    fstate_inv : val → iProp Σ;
    fiber_torch : gname -> iProp Σ;
    async_spec γ q (e : val) Φ :
      fstate_inv q ∗ (∀ (i: nat), □ Φ (RNone', #i)%V) ∗ (∀ γ', fiber_torch γ' ∗ fstate_inv q -∗ EWP e #() <| coop (γ', q) |> {{ y, fiber_torch γ' ∗ fstate_inv q ∗ (∀ (i:nat), □ Φ (RSome' y, #i)%V) }}) -∗
        EWP async e <| coop (γ, q) |> {{ y, ∃ (p cf state : val), ⌜ y = (p, (cf, state))%V ⌝ ∗ fstate_inv q ∗ is_fstate p cf state Φ }};
    await_spec γ q p cf state δ Φ :
      fstate_inv q ∗ is_member p γ cf state δ Φ -∗
        EWP await p <| coop (γ, q) |> {{ y, ∃ (v : val) (i : nat), ⌜ y = (v, #i)%V ⌝ ∗ fstate_inv q ∗ □ Φ y ∗ io_log2 δ i }};
    fiber_cancel_spec γ q p cf state δ Φ :
      fstate_inv q ∗ is_member p γ cf state δ Φ -∗
        EWP fiber_cancel (cf, state)%V <| coop (γ, q) |> {{ v, ∃ (i: nat), ⌜ v = #i ⌝ ∗ fstate_inv q ∗ io_log2 δ i }};
  }.

  Definition run_spec (main : val) :=
    (∀ (_ : AsyncCompLib) (γ : gname) (q : val), fiber_torch γ ∗ fstate_inv q -∗ EWP main #() <| coop (γ, q) |> {{ _, fiber_torch γ ∗ fstate_inv q }}) -∗
      EWP run main <| ⊥ |> {{ _, True }}.

End specification.

Section closed_proof.
  Context `{!heapGS Σ, !fstateGpreS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Lemma promise_and_cancelInv_init :
    ⊢ |==> ∃ (_ : fstateGS Σ) , (∀ q, fstateInv q).
  Proof.
    iIntros. 
    iMod (own_alloc (● (∅ : gmap ((loc * gname) * (loc * loc * gname)) _))) as (γ) "HI";
      first by rewrite auth_auth_valid.
    iModIntro. iExists {| fstate_inG := _; fstate_name := γ; |}.
    iIntros (q). iExists ∅. rewrite /isFstateMap fmap_empty. by iFrame.
  Qed.

  Local Program Instance async_comp_lib `{!fstateGS Σ} :
    AsyncCompLib (Σ:=Σ) := {
    coop := Coop;
    is_fstate := λ v1 v2 v3 Φ, (∃ (p cf state: loc), ⌜ v1 = #p ⌝ ∗ ⌜ v2 = #cf ⌝ ∗ ⌜ v3 = #state ⌝ ∗ isFstate p cf state Φ)%I;
    is_fstate_Persistent := _;
    is_member := λ v1 γ v2 v3 δ Φ, (∃ (p cf state: loc), ⌜ v1 = #p ⌝ ∗ ⌜ v2 = #cf ⌝ ∗ ⌜ v3 = #state ⌝ ∗ isMember p γ cf state δ Φ)%I;
    is_member_Persistent := _;
    io_log1 := io_log_active;
    io_log2 := io_log_frozen;
    io_log2_Persistent := _;
    fstate_inv := fstateInv;
    fiber_torch := torch;
  }.
  Next Obligation. 
    iIntros (?????) "(HcInv & #Hnone & He)"; 
    iApply (ewp_mono with "[He HcInv]").
    iApply ewp_async.
    iFrame. done.
    iIntros (?) "(%p & %cf & %state & -> & HcInv & Hf) !>".
    iExists #p, #cf, #state.
    iSplit; first done.
    iFrame.
    iExists p, cf, state.
    by repeat iSplit.
  Qed.
  Next Obligation.
    iIntros (????????) "(HcInv & (%p' & %cf' & %state' & -> & -> & -> & Hp))". 
    iApply (ewp_mono with "[HcInv Hp]").
      iApply ewp_await.
      iSplitL "HcInv".
      iAssumption.
      iAssumption.
    iIntros (v) "(%y & %i & -> & HfInv & #Hnone & #Hio) !>".
    iExists y, i. iSplit; first done.
    iFrame. iSplit; first done.
    by iAssumption.
  Qed.
  Next Obligation.
    iIntros (????????) "(HcInv & (%p' & %cf' & %state' & -> & -> & -> & Hp))". 
    iApply (ewp_mono with "[HcInv Hp]"). 
      iApply (ewp_fiber_cancel).
      by iFrame.
    iIntros (v) "(%i & -> & HcInv & #Hio) !>".
    iFrame. iExists i. by iSplit.
  Qed.

  Theorem run_correct main : run_spec main.
  Proof.
    iIntros "He". 
    iApply fupd_ewp.
    iMod promise_and_cancelInv_init as "(%HfstateGS  & HpInv)".
    iModIntro.
    iSpecialize ("He" $! async_comp_lib).
    iApply (ewp_run _ (λ _, True)%I with "[] HpInv").
    - done.
    - iIntros (q γ) "(Htorch & HcInv)".
      iSpecialize ("He" with "[Htorch HcInv]"); first by iFrame. 
      iApply (ewp_mono with "He").
      iIntros (_) "(Htorch & HcInv)".
      iModIntro. iFrame. done.
  Qed.

  Theorem parent_correct : 
    ⊢ EWP run parent <| ⊥ |> {{ _, True }}.
  Proof.
    iIntros "".
    iApply (run_correct parent).
    iIntros (H γ q) "(Htorch & HInv)".
    iApply (ewp_mono with "[-]").
      instantiate (1:=(λ _, torch γ ∗ fstateInv q)%I).
      (* whatever it's correct *)
  Admitted.
End closed_proof.