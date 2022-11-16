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
From iris.algebra Require Import excl_auth gset gmap agree.
From iris.base_logic.lib Require Import iprop wsat invariants.
From program_logic Require Import reasoning_rules.
From case_studies Require Import list_lib queue_lib.


(* ========================================================================== *)
(** * Implementation of the Scheduler. *)

Notation Async e := (InjL e) (only parsing).
Notation Await p := (InjR p) (only parsing).

Notation Async' e := (InjLV e) (only parsing).
Notation Await' p := (InjRV p) (only parsing).

Notation Done y := (InjL y) (only parsing).
Notation Waiting ks := (InjR ks) (only parsing).

Notation Done' y := (InjLV y) (only parsing).
Notation Waiting' ks := (InjRV ks) (only parsing).

Section implementation.
  Context `{!heapGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Definition new_promise : val := (λ: <>,
    ref (Waiting (list_nil #()))
  )%V.
  Definition async : val := (λ: "f", do: (Async "f"))%V.
  Definition await : val := (λ: "p", do: (Await "p"))%V.
  Definition next : val := (λ: "q",
    if: queue_empty "q" then #() else queue_pop "q" #()
  )%V.
  Definition run : val := (λ: "main",
    let: "q" := queue_create #() in
    let: "fulfill" := rec: "fulfill" "p" "e" :=
      deep-try: "e" #() with
        effect (λ: "request" "k",
          match: "request" with
            (* Async: *) InjL "e" =>
              let: "p" := new_promise #() in
              queue_push "q" (λ: <>, "k" "p");;
              "fulfill" "p" "e"
          | (* Await: *) InjR "p" =>
              match: Load "p" with
                (* Done: *) InjL "v"  =>
                  "k" "v"
              | (* Waiting: *) InjR "ks" =>
                  "p" <- InjR (list_cons "k" "ks");;
                  next "q"
              end
          end)
      | return (λ: "v",
          match: Load "p" with
            (* Done: *) InjL <> =>
              #() #() (* Unreachable! *)
          | (* Waiting: *) InjR "ks" =>
              list_iter (λ: "k", queue_push "q" (λ: <>, "k" "v")) "ks";;
              "p" <- Done "v";;
              next "q"
          end)
      end
    in
    let: "p" := new_promise #() in
    "fulfill" "p" "main"
  )%V.

End implementation.


(* ========================================================================== *)
(** * Specification. *)

Section specification.
  Context `{!heapGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Class AsyncCompLib := {
    coop : iEff Σ;
    is_promise : val → (val -> iProp Σ) → iProp Σ;
    is_promise_Persistent p Φ : Persistent (is_promise p Φ);
    async_spec (e : val) Φ :
      EWP e #() <| coop |> {{ y, □ Φ y }} -∗
        EWP async e <| coop |> {{ p, is_promise p Φ }};
    await_spec p Φ :
      is_promise p Φ -∗
        EWP await p <| coop |> {{ y, □ Φ y }};
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
   contradictory. *)

(* The assumption that certain cameras are available. *)
Class promiseGpreS Σ := {
  promise_mapG :> inG Σ
    (authR (gmapUR (loc * gname) (agreeR (laterO (val -d> (iPropO Σ))))));
  torchG :> inG Σ (exclR unitO);
}.

(* A concrete instance of [Σ] for which the assumption [promisesGS Σ] holds. *)
Definition promiseΣ := #[
  GFunctor (authRF
    (gmapURF (loc * gname) (agreeRF (laterOF (valO -d> idOF)))));
  GFunctor (exclR unitO)
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
  Definition torch γ := own γ (Excl tt).

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
           is_list l ks   ∗
           [∗ list] k ∈ ks, ready q Φ k)
  )%I.

  Definition ready_pre :
    (val -d> (val -d> iPropO Σ) -d> val -d> iPropO Σ) →
    (val -d> (val -d> iPropO Σ) -d> val -d> iPropO Σ) := (λ ready q Φ k,
    ∀ (y : val) n,
      □ Φ y -∗
        ▷ promiseInv_pre ready q -∗
          ▷ is_queue q (ready q (λ v, ⌜ v = #() ⌝)%I) n -∗
             EWP (k : val) y {{ _, True }}
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
       is_list l ks   ∗
       [∗ list] k ∈ ks, ready q Φ k).


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
    Proper ((dist n) ==> (dist n)) (promiseSt q p γ).
  Proof. by solve_proper. Qed.
  Global Instance promiseSt_proper q p γ :
    Proper ((≡) ==> (≡)) (promiseSt q p γ).
  Proof. by solve_proper. Qed.


  (* ------------------------------------------------------------------------ *)
  (* Properties. *)

  (* Logical rules governing the predicate [torch]. *)
  Section torch.

    Lemma forge_torch : ⊢ |==> ∃ γ, torch γ.
    Proof. by iMod (own_alloc (Excl tt)) as (γ) "Htorch"; last iExists γ. Qed.

    Lemma claim_uniqueness γ : (torch γ ∗ torch γ) -∗ False.
    Proof. by rewrite /torch -own_op own_valid excl_validI. Qed.

  End torch.

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

    Lemma promiseSt_non_duplicable q p γ γ' Φ Φ' :
      promiseSt q p γ Φ -∗ promiseSt q p γ' Φ' -∗ False.
    Proof.
      assert (⊢ ∀ q p γ Φ, promiseSt q p γ Φ -∗ ∃ v, p ↦ v)%I as Haux.
      { by iIntros (????) "[[%v[Hp _]]|[%l[%ks[Hp _]]]]"; auto. }
      iIntros "Hp Hp'".
      iPoseProof (Haux with "Hp")  as "[%v  Hp]".
      iPoseProof (Haux with "Hp'") as "[%v' Hp']".
      by iDestruct (mapsto_ne with "Hp Hp'") as "%Hneq".
    Qed.

    Lemma promiseSt_proper' q p γ Φ Φ' :
      (Φ ≡ Φ') -∗ promiseSt q p γ Φ -∗ promiseSt q p γ Φ'.
    Proof. by iIntros "HΦ Hp"; iRewrite -"HΦ". Qed.

    Lemma update_promiseInv q p γ Φ :
      promiseInv q ∗ promiseSt q p γ Φ ==∗
        promiseInv q ∗ isMember p γ Φ.
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

    Lemma lookup_promiseInv q p γ Φ :
      promiseInv q -∗ isMember p γ Φ -∗
        ▷ ((promiseSt q p γ Φ -∗ promiseInv q) ∗ promiseSt q p γ Φ).
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
        iApply (promiseSt_proper' q p γ Φ Φ' with "[] HpSt").
        rewrite discrete_fun_equivI. iIntros (x).
        by iRewrite ("Heq'" $! x).
      - iApply (promiseSt_proper' q p γ Φ' Φ with "[] HpSt").
        by rewrite discrete_fun_equivI.
    Qed.

  End promise_preds.

End predicates.


(* -------------------------------------------------------------------------- *)
(** Protocol [Coop]. *)

Section protocol_coop.
  Context `{!heapGS Σ, !promiseGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Definition ASYNC_pre (Coop : iEff Σ) : iEff Σ :=
    >> e Φ       >> !(Async'  e) {{▷ EWP e #() <|Coop|> {{v, □ Φ v}}}};
    << (p : loc) << ?(#p)        {{isPromise p Φ                    }} @ OS.
  Definition AWAIT : iEff Σ :=
    >> (p : loc) Φ >> !(Await' #p) {{isPromise p Φ}};
    << y           << ?(y)         {{□ Φ y        }} @ OS.
  Definition Coop_pre : iEff Σ → iEff Σ := (λ Coop,
    ASYNC_pre Coop <+> AWAIT
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
      iEff_car (upcl OS AWAIT) v Φ'.
  Proof.
    transitivity (iEff_car (upcl OS (Coop_pre Coop)) v Φ').
    - iApply iEff_car_proper. by rewrite {1}Coop_unfold.
    - by rewrite upcl_sum (upcl_tele' [tele _ _] [tele _]) //.
  Qed.

  Lemma upcl_ASYNC v Φ' :
    iEff_car (upcl OS ASYNC) v Φ' ≡
      (∃ e Φ, ⌜ v = Async' e ⌝ ∗ (▷ EWP e #() <| Coop |> {{ v, □ Φ v }}) ∗
            (∀ (p : loc), isPromise p Φ -∗ Φ' #p))%I.
  Proof. by rewrite /ASYNC (upcl_tele' [tele _ _] [tele _]). Qed.

  Lemma upcl_AWAIT v Φ' :
    iEff_car (upcl OS AWAIT) v Φ' ≡
      (∃ (p : loc) Φ, ⌜ v = Await' #p ⌝ ∗ isPromise p Φ ∗
          (∀ v, □ Φ v -∗ Φ' v))%I.
  Proof. by rewrite /AWAIT (upcl_tele' [tele _ _] [tele _]). Qed.

End protocol_coop.


(* ========================================================================== *)
(** * Verification. *)

Section verification.
  Context `{!heapGS Σ, !promiseGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Lemma ewp_new_promise Ψ q Φ :
    ⊢ EWP (new_promise #()) <| Ψ |> {{ y,
        ∃ p γ, ⌜ y = #(p : loc) ⌝ ∗ torch γ ∗ promiseSt q p γ Φ }}.
  Proof.
    unfold new_promise. ewp_pure_steps. ewp_bind_rule.
    iApply ewp_mono. { by iApply list_nil_spec. }
    iIntros (l) "Hlist !>". simpl. ewp_pure_steps.
    iApply ewp_alloc. iIntros "!>" (p) "Hp".
    iMod forge_torch as "[%γ Hγ]". iModIntro.
    iExists p, γ. iFrame. iSplit; [done|]. iRight.
    iExists l, []. by iFrame.
  Qed.

  Lemma ewp_next q n Ψ :
    promiseInv q -∗
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

  Lemma ewp_async (e : val) Φ :
    EWP e #() <| Coop |> {{ v, □ Φ v }} ⊢
      EWP (async e) <| Coop |> {{ y,
        ∃ p, ⌜ y = #(p : loc) ⌝ ∗ isPromise p Φ }}.
  Proof.
    iIntros "He". unfold async. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_ASYNC. iLeft.
    iExists e, Φ. iSplit; [done|]. iFrame.
    iIntros (p) "Hp". iExists p. by iFrame.
  Qed.

  Lemma ewp_await (p : loc) Φ :
    isPromise p Φ -∗ EWP (await #p) <| Coop |> {{ v, □ Φ v }}.
  Proof.
    iIntros "Hp". unfold await. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_Coop upcl_AWAIT. iRight.
    iExists p, Φ. iSplit; [done|]. iFrame. by auto.
  Qed.

  Lemma ewp_run (main : val) Φ :
    (∀ q, promiseInv q) -∗
      EWP main #() <| Coop |> {{ v, □ Φ v }} -∗
        EWP run main {{ _, True }}.
  Proof.
    iIntros "HpInv Hmain". unfold run. ewp_pure_steps.
    ewp_bind_rule. iApply ewp_mono. { by iApply queue_create_spec. }
    iIntros (q) "Hq !>". simpl. ewp_pure_steps.
    ewp_bind_rule. iApply ewp_mono. { by iApply (ewp_new_promise _ q Φ). }
    iIntros (y) "[%p [%γ (->&Hγ&HpSt)]] !>". simpl.
    iSpecialize ("HpInv" $! q).
    iAssert (∃ (n : nat), is_queue q (ready q (λ v : val, ⌜v = #()⌝)) n)%I
      with "[Hq]" as "[%n Hq]". { by iExists 0. }
    do 3 ewp_value_or_step.
    iApply fupd_ewp.
    iMod (update_promiseInv with "[$]") as "[HpInv Hmem]".
    iModIntro.
    iLöb as "IH" forall (main q p γ Φ n).
    ewp_pure_steps.
    iApply (ewp_deep_try_with with "Hmain").
    iLöb as "IH_handler" forall (q γ Φ n).
    iDestruct "Hmem" as "#Hmem".
    rewrite deep_handler_unfold.
    iSplit; [|iSplit]; last (by iIntros (??) "HFalse"; rewrite upcl_bottom).
    (* Return branch. *)
    - iIntros (y) "#Hy".
      iDestruct (lookup_promiseInv with "HpInv Hmem") as "[HpInv HpSt]".
      ewp_pure_steps.
      iDestruct "HpSt" as "[[%y' (_&_&Hγ')]|[%l [%ks (Hp&Hl&Hks)]]]";
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
          iIntros (y' n') "-> HpInv Hq". ewp_pure_steps.
          by iApply ("Hk" with "Hy HpInv Hq").
        }
        iIntros (?) "Hq !>".
        iSplitL "Hq"; [iExists (S m)|iExists vs]; iFrame.
        iPureIntro. by rewrite -app_assoc.
      }
      iIntros (?) "[Hl [[%m Hq]  _]] !>". simpl.
      ewp_pure_steps. ewp_bind_rule.
      iApply (ewp_store with "Hp"). iIntros "!> Hp !>". simpl.
      ewp_pure_steps. iApply (ewp_next with "[HpInv Hγ Hp] Hq").
      { iApply "HpInv". iLeft. iExists y. by iFrame. }
    (* Effect branch. *)
    - iIntros (request k). rewrite upcl_Coop upcl_AWAIT upcl_ASYNC.
      iIntros "[[%e [%Φ' (->&He&Hk)]]| [%p' [%Φ' (->&[%γ' #Hmem']&Hk)]]]";
      first ewp_pure_steps.
      (* Async. *)
      + ewp_bind_rule. iApply ewp_mono; [iApply (ewp_new_promise _ q Φ')|].
        iIntros (y) "[%p' [%γ' (->&Hγ'&HpSt')]] !>". simpl.
        iApply fupd_ewp.
        iMod (update_promiseInv with "[$]") as "[HpInv #Hmem']". iModIntro.
        ewp_pure_steps. iApply (ewp_bind' (AppRCtx _)). { done. }
        iApply (ewp_mono with "[Hq Hk Hγ]").
        { iApply (queue_push_spec with "Hq"). rewrite ready_unfold.
          iIntros (y m) "-> HpInv Hq". ewp_pure_steps.
          iApply "Hk"; [by iExists γ'|]. iNext.
          by iApply ("IH_handler" with "Hγ Hq HpInv").
        }
        iIntros (?) "Hq !>". simpl. do 3 ewp_value_or_step.
        by iApply ("IH" with "He Hγ' Hq HpInv Hmem'").
      (* Await. *)
      + iDestruct (lookup_promiseInv with "HpInv Hmem'") as "[HpInv HpSt']".
        ewp_pure_steps. ewp_bind_rule. simpl.
        iDestruct "HpSt'" as "[[%y' (Hp'&#Hy&Hγ')]|[%l [%ks (Hp'&Hl&Hks)]]]".
        (* Promise is fulfilled. *)
        * iApply (ewp_load with "Hp'"). iIntros "!> Hp' !>".
          ewp_pure_steps. iApply ("Hk" with "Hy").
          iApply ("IH_handler" with "Hγ Hq [HpInv Hp' Hγ'] Hmem").
          iApply "HpInv". iLeft. by iExists y'; iFrame.
        (* Promise is unfulfilled. *)
        * iApply (ewp_load with "Hp'"). iIntros "!> Hp' !>".
          ewp_pure_steps.
          iApply (ewp_bind [(AppRCtx _); (StoreRCtx _); InjRCtx]); first done.
          iApply (ewp_mono with "[Hl]"); [iApply (list_cons_spec with "Hl")|].
          iIntros (l') "Hl' !>". simpl. ewp_pure_steps. ewp_bind_rule.
          iApply (ewp_store with "Hp'"). iIntros "!> Hp' !>". simpl.
          ewp_pure_steps.
          iApply (ewp_next with "[HpInv Hks Hl' Hp' Hk Hγ] Hq").
          iApply "HpInv". iRight. iExists l', (k :: ks). iFrame.
          rewrite ready_unfold. iIntros (y' m) "#Hy' HpInv Hq".
          iApply ("Hk" with "Hy'"). iNext.
          by iApply ("IH_handler" with "Hγ Hq HpInv Hmem").
  Qed.

End verification.


Section closed_proof.
  Context `{!heapGS Σ, !promiseGpreS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Lemma promiseInv_init :
    ⊢ |==> ∃ _ : promiseGS Σ, ∀ q, promiseInv q.
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
