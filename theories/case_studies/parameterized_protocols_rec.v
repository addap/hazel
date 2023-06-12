(* parameterized_protocols.v *)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth gset gset gmap agree csum.
From iris.base_logic.lib Require Import iprop wsat invariants.
From program_logic Require Import reasoning_rules.
From case_studies Require Import list_lib queue_lib.

Notation GetMyState := (InjL #()) (only parsing).
Notation Spawn e := (InjR e) (only parsing).

Notation GetMyState' := (InjLV #())%V (only parsing).
Notation Spawn' e := (InjRV e)%V (only parsing).

(* ========================================================================== *)
(** * Implementation of the Scheduler. *)

Section implementation.
  Context `{!heapGS Σ}.

  Definition new_state : val := (λ: <>,
    ref #0
  )%V.
  Definition get_my_state : val := (λ: <>, do: GetMyState)%V.
  Definition spawn : val := (λ: "e", do: (Spawn "e"))%V.

  Definition inc : val := (λ: <>,
    let: "r" := get_my_state #() in
    "r" <- (Load "r") + #1
  )%V.

  Definition e2 : val := (λ: <>,
    inc #();;
    #()
  )%V.

  Definition e1 : val := (λ: <>,
    let: "res2" := spawn e2 in
    #()
  )%V.

  (* a fiber can spawn a new fiber but automatically blocks until it is finished.
     should be enough for recursive protocols, but cannot implement the cancel->await->assert equal property.
     This could wait until we do it in the real scheduler. *)

  Definition run : val := (λ: "e1",
    let: "fulfill" := rec: "fulfill" "r" "e" :=
      deep-try: "e" #() with
        effect (λ: "request" "k", 
          match: "request" with
            (* GetMyState *) InjL <> => "k" "r"
          | (* Spawn *) InjR "e2" => 
            let: "r2" := new_state #() in
            let: "res2" := "fulfill" "r2" "e2" in
            "k" "res2"
          end)
      | return (λ: <>, Load "r")
      end 
    in
    let: "r1" := new_state #() in
    "fulfill" "r1" "e1"
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
  fstate_setG :> inG Σ
    (authR (gmapUR (loc * gname * gname) unitR));
  torchG :> inG Σ (exclR unitO);
  cancelG :> inG Σ (csumR (exclR natO) (agreeR natO));
}.

(* A concrete instance of [Σ] for which the assumption [promisesGS Σ] holds. *)
Definition fstateΣ := #[
  GFunctor (authRF
    (gmapUR (loc * gname * gname) unitR));
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

  (* ------------------------------------------------------------------------ *)
  (* Definitions. *)

  (* torch γ ≜ own γ (Excl ())

     isMember r ≜
       ∃ γ δ, own fstate_name (◯ {[(r,γ,δ)]})

     stateSet ≜
       own fstate_name (● S)

     stateInv ≜
       ∃ M, stateSet S ∗
         [∗ set] (r,γ,δ) ∈ S,
          ∃ n, r ↦ n ∗ (
             (torch γ ∗ frozen δ n)
           ∨
             (active δ n))

  *)

  (* Unique token [γ]: a fiber holds possession of [torch γ] while running. *)
  Definition torch γ := @own _ _ (torchG) γ (Excl tt).

  Definition isMember r γ δ :=
    own fstate_name (◯ {[(r, γ, δ) := tt]}).

  Definition isMemberMap (M : gmap (loc * gname * gname) unit) :=
    own fstate_name (● M).

  Definition active (δ : gname) (i : nat) : iProp Σ :=
    own δ (Cinl (Excl i)).
  Definition frozen (δ : gname) (i : nat) : iProp Σ :=
    own δ (Cinr (to_agree i)).

  Definition stateInv : iProp Σ := (
    ∃ M, isMemberMap M ∗
      [∗ map] elem ↦ tt ∈ M, let '(r, γ, δ) := elem in
      (* state always points to some value *)
      ∃ (i: nat), r ↦ #i ∗ (
          (frozen δ i ∗ torch γ)
      ∨
          (active δ i)
      )
  )%I.

  Definition stateSt r γ δ : iProp Σ :=
      ∃ (i: nat), r ↦ #i ∗ (
          (frozen δ i ∗ torch γ)
      ∨
          (active δ i)
      ).

  (* ------------------------------------------------------------------------ *)
  (* Non-expansiveness. *)

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
    Lemma new_cancel : ⊢ |==> ∃ δ, active δ 0.
    Proof.
      iMod (own_alloc (Cinl (Excl 0))) as (δ) "Hcancel".
      by easy. by iExists δ.
    Qed.

    Lemma claim_active_uniqueness δ : ∀ i j, (active δ i ∗ active δ j) -∗ False.
    Proof.
      intros i j.
      rewrite /active -own_op own_valid csum_validI. 
      simpl. 
      by rewrite excl_validI.
    Qed.

    Lemma claim_frozen_agreement δ : ∀ i j, (frozen δ i ∗ frozen δ j) -∗ ⌜i = j⌝.
    Proof.
      intros i j.
      rewrite /frozen -own_op own_valid csum_validI.
      simpl.
      iIntros "%Hagree".
      iPureIntro.
      by specialize (to_agree_op_inv_L _ _ Hagree) as Hagree'.
    Qed.

    Lemma freeze (δ : gname) (i : nat) :
      active δ i ==∗ frozen δ i.
    Proof.
      iApply own_update.
      apply cmra_update_exclusive.
      apply Cinr_valid.
      done.
    Qed.

    Lemma update_active (δ : gname) (i j: nat) :
      active δ i ==∗ active δ j.
    Proof.
      iApply own_update.
      apply cmra_update_exclusive.
      apply Cinl_valid.
      done.
    Qed.
  End cancel.

  (* Logical rules governing the predicates [isPromiseMap], [isPromise], and
     [promiseInv]. *)
  Section promise_preds.

    (* Persistent predicates. *)
    Global Instance isMember_Persistent r γ δ : Persistent (isMember r γ δ).
    Proof. by apply _. Qed.
    Global Instance frozen_Persistent (δ: gname) (i: nat) : Persistent (frozen δ i).
    Proof. by apply _. Qed.

    Lemma update_fstate_map M r γ δ:
      M !! (r, γ, δ) = None →
        isMemberMap M ==∗
          isMemberMap (<[(r,γ,δ):=tt]> M) ∗ isMember r γ δ.
    Proof.
      intros Hlkp. unfold isMemberMap. iIntros "HM".
      iMod (own_update with "HM") as "[HM HiP]".
      { apply (@auth_update_alloc (gmapUR _ _) (M)).
        apply (alloc_singleton_local_update _ (r, γ, δ) tt).
        by rewrite /= Hlkp. done. }
      iModIntro. iFrame.
    Qed.

    Lemma claim_membership M r γ δ:
      isMemberMap M ∗ isMember r γ δ -∗
        ⌜ M !! (r, γ, δ) = Some tt ⌝.
    Proof.
      rewrite /isMemberMap /isMember.
      rewrite -own_op own_valid auth_both_validI /=.
      iIntros "[HM #HpM]". iDestruct "HM" as (M') "#HM".
      rewrite gmap_equivI gmap_validI.
      iSpecialize ("HM" $! (r, γ, δ)). iSpecialize ("HpM" $! (r, γ, δ)).
      rewrite lookup_op lookup_singleton.
      rewrite option_equivI.
      case: (M  !! (r, γ, δ)) => [[]|] /=; [|
      case: (M' !! (r, γ, δ))=> [[]|] /=; by iExFalso].
      done.
    Qed.

    Lemma fstateSt_non_duplicable r γ γ' δ δ' :
      stateSt r γ δ -∗ stateSt r γ' δ' -∗ False.
    Proof.
      assert (⊢ ∀ r γ δ, stateSt r γ δ -∗ ∃ v, r ↦ v)%I as Haux.
      { rewrite /stateSt.
        iIntros (???) "(%i & Hr & _)"; auto. }
      iIntros "Hp Hp'".
      iPoseProof (Haux with "Hp")  as "[%v  Hp]".
      iPoseProof (Haux with "Hp'") as "[%v' Hp']".
      by iDestruct (mapsto_ne with "Hp Hp'") as "%Hneq".
    Qed.

    Lemma update_stateInv r γ δ :
      stateInv ∗ stateSt r γ δ ==∗
        stateInv ∗ isMember r γ δ.
    Proof.
      iIntros "[HpInv Hp]". rewrite /stateInv.
      iDestruct "HpInv" as (M) "[HM HInv]".
      destruct (M !! (r, γ, δ)) as [[]|] eqn:Hlkp.
      - rewrite (big_opM_delete _ _ _ _ Hlkp).
        iDestruct "HInv" as "[Hp' _]".
        by iDestruct (fstateSt_non_duplicable with "Hp Hp'") as "HFalse".
      - iMod (update_fstate_map M r γ δ Hlkp with "HM") as "[HM Hmem]".
        iModIntro. iFrame. iExists (<[(r, γ, δ):=tt]> M). iFrame.
        rewrite big_opM_insert; last done. by iFrame.
    Qed.

    Lemma lookup_stateInv r γ δ :
      stateInv -∗ isMember r γ δ -∗
        ▷ ((stateSt r γ δ -∗ stateInv) ∗ stateSt r γ δ).
    Proof.
      iIntros "HpInv Hmem". rewrite /stateInv.
      iDestruct "HpInv" as (M) "[HM HInv]".
      iDestruct (claim_membership M r γ δ with "[$]") as "%Hlkp".
      iNext.
      iDestruct (big_sepM_delete _ _ (r, γ, δ) with "HInv")
        as "[HpSt HInv]"; first done.
      iSplitL "HInv HM".
      - iIntros "HpSt". iExists M. iFrame.
        rewrite (big_opM_delete _ _ _ _ Hlkp). iFrame.
      - iFrame.
    Qed.

  End promise_preds.
End predicates.


(* -------------------------------------------------------------------------- *)
(** Protocol [GetState]. *)

Section protocol_getstate.
  Context `{!heapGS Σ, !fstateGS Σ}.

  (* a.d. protocols parameterized by a gname so that we know which isMember we get from GET_STATE 

  There are two interesting use cases of parameterized protocols. 
  1. In SPAWN, the given expression must obey a protocol R γ for the new ghost name γ that we allocate for its torch.
  2. so that this e can perform GET_STATE γ and know that it will receive an isMember r γ δ.
      The isMember is used to retrieve the permission `r ↦ i` out of stateInv.
      The γ in the isMember r γ δ must coincide with the torch γ the fiber owns, so that it can eliminate certain cases 
        e.g. the case that the fiber is already over, which is evidently untrue since the fiber is currently running. 
      I think we need parameterized protocols so that fibers can reason about their own state. 
      Prof. Pottier also mentioned fiber-local storage as a possible application. (Eio already has this but I removed it from the thinned-out version.) *)

  (* SPAWN is recursive, and for the given e, we want to run it under the same protocol but with a different parameter. 
     The parameter is the ghost name associated with the currently running fiber, so that the fiber has a sense of "self".
     After e has run to completion, we return some δ with a frozen δ i to the caller. *)
  Definition SPAWN_pre (R: gname → iEff Σ): iEff Σ :=
    >> (e: val) >> !(Spawn' e) {{ stateInv ∗ (∀ γ', torch γ' ∗ stateInv -∗ EWP e #() <| R γ' |> {{ _, torch γ' ∗ stateInv }}) }};
    << (i: nat) (δ: gname) << ?((#i)%V) {{ stateInv ∗ frozen δ i }} @ OS.

  Definition GET_STATE (γ: gname): iEff Σ :=
    >> (_: val) >> !(GetMyState') {{torch γ}};
    << (r : loc) (δ : gname) << ?((#r)%V) {{torch γ ∗ isMember r γ δ}} @ OS.

  Definition R_pre: (gname → iEff Σ) → (gname → iEff Σ) := (λ R,
    λ γ, SPAWN_pre R <+> GET_STATE γ
  )%ieff.

  Fail Check (gname -d> iEff Σ).
  (* The proofs about contractiveness don't work with (gname → iEff Σ).
     (gname -d> iEff Σ) fails because iEff is a Type, not an ofe.
     We might be able to add "gname -d>" to the definition of iEff. *)

  (* Local Instance R_pre_contractive : Contractive (R_pre).
  Proof.
    intros γ.
    rewrite /Coop_pre /AWAIT /ASYNC_pre=> n Coop Coop' HCoop.
    by repeat (apply ewp_ne||apply iEffPre_base_ne||f_contractive||f_equiv).
  Qed. *)
  (* Definition R_def: (gname → iEff Σ) := fixpoint (R_pre).
  Definition R_aux : seal R_def. Proof. by eexists. Qed.
  Definition R := R_aux.(unseal).
  Definition R_eq : R = R_def := R_aux.(seal_eq).*)
  Axiom R: gname → iEff Σ.
  Global Lemma R_unfold : ∀ γ, R γ ≡ R_pre R γ.
  Proof.
    (* intros γ.
    rewrite R_eq /R_def.
    by apply (fixpoint_unfold (R_pre γ)). *)
  Admitted.

  Definition SPAWN  := SPAWN_pre R.

  Lemma upcl_R γ v Φ' :
    iEff_car (upcl OS (R γ)) v Φ' ⊣⊢
      iEff_car (upcl OS SPAWN) v Φ' ∨
      iEff_car (upcl OS (GET_STATE γ)) v Φ'.
  Proof.
    transitivity (iEff_car (upcl OS (R_pre R γ)) v Φ').
    - iApply iEff_car_proper. by rewrite {1}R_unfold.
    - rewrite upcl_sum. by rewrite /SPAWN.
  Qed.

  Lemma upcl_SPAWN v Φ' :
    iEff_car (upcl OS SPAWN) v Φ' ≡
      (∃ (e: val), ⌜ v = Spawn' e ⌝ ∗ (stateInv ∗ (∀ γ', torch γ' ∗ stateInv -∗ EWP e #() <| R γ' |> {{ _, torch γ' ∗ stateInv }})) ∗
        (∀ (i: nat) (δ: gname), (stateInv ∗ frozen δ i) -∗ Φ' #i)
      )%I.
  Proof.
    rewrite /SPAWN (upcl_tele' [tele _] [tele _ _]).
    simpl. done.
  Qed.

  Lemma upcl_GET_STATE γ v Φ' :
    iEff_car (upcl OS (GET_STATE γ)) v Φ' ≡
      (∃ (_: val), ⌜ v = GetMyState' ⌝ ∗ torch γ ∗
            (∀ (r : loc) (δ : gname), (torch γ ∗ isMember r γ δ) -∗ Φ' (#r)%V ))%I.
  Proof. 
    rewrite /GET_STATE (upcl_tele' [tele _] [tele _ _]). 
    simpl. done.
  Qed.

End protocol_getstate.

Check R.

(* ========================================================================== *)
(** * Verification. *)

Section verification.
  Context `{!heapGS Σ, !fstateGS Σ}.

  Lemma ewp_new_state Ψ :
    ⊢ EWP (new_state #()) <| Ψ |> {{ y, 
        ∃ (r : loc) (γ δ: gname), ⌜ y = #r ⌝ ∗ r ↦ #0 ∗ active δ 0 ∗ torch γ}}.
  Proof.
    unfold new_state. ewp_pure_steps.
    iApply ewp_alloc. iNext. 
    iIntros "%r Hr".
    iMod new_cancel as "[%δ Hδ]".
    iMod forge_torch as "[%γ Hγ]".
    iModIntro.
    iExists r, γ, δ.
    iSplit; first done.
    iFrame.
  Qed.

  Lemma ewp_get_my_state γ: 
    torch γ ⊢ 
      EWP (get_my_state #()) <| R γ |> {{ v, ∃ (r : loc) (δ : gname), ⌜ v = #r ⌝ ∗ torch γ ∗ isMember r γ δ}}.
  Proof.
    iIntros "Htorch".
    rewrite /get_my_state. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_R upcl_GET_STATE.
    iRight.
    iExists #().
    iSplit; first done. iFrame.
    iIntros (r δ) "Hstate".
    iExists r, δ. iSplit; first done.
    by iFrame.
  Qed.

  Lemma ewp_spawn (e: val) γ :
    stateInv ∗ (∀ γ', torch γ' ∗ stateInv -∗ EWP e #() <| R γ' |> {{ _, torch γ' ∗ stateInv }}) ⊢
      EWP (spawn e) <| R γ |> {{v, ∃ (i: nat) (δ: gname), ⌜ v = #i ⌝ ∗ stateInv ∗ frozen δ i }}.
  Proof.
    iIntros "(HInv & He)".
    rewrite /spawn. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_R upcl_SPAWN.
    iLeft.
    iExists e. iSplit; first done.
    iFrame. 
    iIntros (i δ) "(HInv & Hfrozen)".
    iExists i, δ. by iFrame.
  Qed.

  Lemma ewp_inc γ:
    torch γ ∗ stateInv ⊢ EWP inc #() <| R γ |> {{ v, ⌜ v = #() ⌝ ∗ torch γ ∗ stateInv }}.
  Proof.
    iIntros "(Htorch & HInv)".
    rewrite /inc.
    ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply (ewp_mono with "[Htorch]"). 
      by iApply ewp_get_my_state.
    iIntros (v) "(%r & %δ & -> & Htorch & Hmem) !>".
    iDestruct (lookup_stateInv with "HInv Hmem") as "[HInv HcSt]".
    ewp_pure_steps.
    iDestruct "HcSt" as "(%i & Hr & 
                         [ (Hfrozen & Htorch') | Hactive ])".
    - (* can never happen.
         Since we are running, our fiber cannot be finished. *)
      iPoseProof (claim_uniqueness with "[Htorch Htorch']") as "Hfalse"; first by iFrame.
      by iExFalso.
    -
      ewp_bind_rule. simpl.
      iApply (ewp_load with "Hr"). iIntros "!> Hr !>".
      (* changing io log *)
      ewp_bind_rule. simpl.
      ewp_pure_steps.
      { instantiate (1 := #(Z.of_nat (i + 1))).
        replace (Z.of_nat (i + 1)) with (Z.add (Z.of_nat i) (Z.of_nat 1)). 
        done. lia. }
      iApply (ewp_store with "Hr"). iIntros "!> Hr".
      iMod ((update_active _ i (i+1)) with "Hactive") as "Hactive".
      (* restore the cancelSt *)
      iAssert (stateSt r γ δ) with "[Hr Hactive]" as "HcSt".
      { iExists (i + 1).
        iFrame. }
      iSpecialize ("HInv" with "HcSt").
      iModIntro.
      by iFrame.
  Qed.

  (* with the limited protocol we cannot prove interesting specifications of the example programs.
    But this is only meant to show the use of parameterized protocols. *)
  Lemma ewp_e2 γ:
    torch γ ∗ stateInv ⊢
      EWP e2 #() <| R γ |> {{_, torch γ ∗ stateInv }}.
  Proof.
    iIntros "(Htorch & HInv)".
    rewrite /e2. ewp_pure_steps. iFrame.
    ewp_bind_rule. simpl.
    iApply (ewp_mono with "[Htorch HInv]").
      iApply ewp_inc. by iFrame.
    iIntros (v) "(-> & Htorch & HInv) !>".
    ewp_pure_steps. by iFrame.
  Qed.

  Lemma ewp_e1 γ:
    stateInv ⊢
      EWP e1 #() <| R γ |> {{_, stateInv }}.
  Proof.
    iIntros "HInv".
    rewrite /e1. ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply (ewp_mono with "[HInv]").
    { iApply ewp_spawn. iFrame.
      iIntros (γ') "(Htorch' & HInv)".
      iApply ewp_e2. iFrame. }
    iIntros (v) "(%i & %δ & -> & HInv & Hfrozen) !>".
    ewp_pure_steps. iFrame.
  Qed.
  
  Lemma ewp_run (e1 : val):
    stateInv ⊢
      (∀ γ, torch γ ∗ stateInv -∗ EWP e1 #() <| R γ |> {{ _, torch γ ∗ stateInv }}) -∗
        EWP run e1 <| ⊥ |> {{ v, ∃ (i: nat) (δ: gname), ⌜ v = #i ⌝ ∗ stateInv ∗ frozen δ i }}.
  Proof.
    iIntros "HInv He1". unfold run. ewp_pure_steps.
    ewp_bind_rule. simpl. iApply ewp_mono. { by iApply (ewp_new_state). }
    iIntros (r1v) "(%r1 & %γ1 & %δ1 & -> & Hr1 & Hactive1 & Htorch1) !>". ewp_pure_steps. 
    (* ewp_bind_rule. simpl. iApply ewp_mono. { by iApply (ewp_new_state). }
    iIntros (r2v) "(%r2 & %δ2 & -> & Hr2 & Hactive2) !>". ewp_pure_steps.  *)
    iApply fupd_ewp.
    iAssert (stateSt r1 γ1 δ1) with "[Hr1 Hactive1]" as "Hstate1".
    { iExists 0. by iFrame. }
    iMod (update_stateInv with "[HInv Hstate1]") as "[HInv Hmem1]".
    { iFrame. }
    (* iMod (update_stateInv with "[HInv Hr2 Hactive2]") as "[HInv Hmem2]".
    { iFrame. iExists 0. by iFrame. } *)
    iModIntro.
    (* does Φ really need to be quantified? *)
    iSpecialize ("He1" with "[Htorch1 HInv]"); first by iFrame.
    iLöb as "IH" forall (r1 γ1 δ1 e1).
    iApply (ewp_deep_try_with with "He1").
    iLöb as "IH_handler".
    iDestruct "Hmem1" as "#Hmem1".
    rewrite deep_handler_unfold.
    iSplit; [|iSplit]; last (by iIntros (??) "HFalse"; rewrite upcl_bottom).
    (* Return branch. *)
    - iIntros (y) "(Htorch & HInv)".
      iDestruct (lookup_stateInv with "HInv Hmem1") as "[HInv HpSt]".
      ewp_pure_steps.
      unfold stateSt.
      iDestruct "HpSt" as "(%i & Hr & [[Hfrozen Htorch'] | Hactive])".
      { iPoseProof (claim_uniqueness with "[Htorch Htorch']") as "HFalse". by iFrame.
        by iExFalso. }
      ewp_bind_rule. iApply (ewp_load with "Hr"). simpl.
      iIntros "!> Hr".
      (* freeze log *)
      iMod (freeze with "Hactive") as "#Hfrozen".
      iModIntro.
      ewp_pure_steps.
      iExists i, δ1. iSplit; first done.
      iSplit; last done.
      iApply "HInv".
      iExists i. iFrame. iLeft. by iFrame.
    (* Effect branch. *)
    - iIntros (request k). rewrite upcl_R upcl_SPAWN upcl_GET_STATE.
      idtac.
      iIntros "[ (%e2 & -> & (HInv & He2) & Hk)
               | (%_ & -> & Htorch & Hk) ]";
      ewp_pure_steps.
      + (* Spawn *)
        ewp_bind_rule. simpl. 
        (* state management *)
        iApply ewp_mono. { by iApply (ewp_new_state). }
        iIntros (r2v) "(%r2 & %γ2 & %δ2 & -> & Hr2 & Hactive2 & Htorch2) !>". ewp_pure_steps. 
        iApply fupd_ewp.
        iAssert (stateSt r2 γ2 δ2) with "[Hr2 Hactive2]" as "Hstate2".
        { iExists 0. by iFrame. }
        iMod (update_stateInv with "[HInv Hstate2]") as "[HInv #Hmem2]".
        { iFrame. }
        iModIntro.
        (* /state management *)
        (* recursive call under protocol with different parameter. *)
        iApply (ewp_mono with "[He2 Htorch2 HInv]").
        { iApply "IH". iApply "Hmem2". 
          iApply "He2". iFrame. }
        (* now we get back the stateInv from the spawned execution *)
        iIntros (v) "(%i & %δ & -> & HInv & #Hfrozen) !>".
        ewp_pure_steps. iApply ("Hk" with "[HInv]").
        iFrame. iApply "Hfrozen".
        iNext.
        rewrite deep_handler_unfold.
        iApply "IH_handler". iAssumption.
      + (* GetMyState *)
        iApply ("Hk" with "[Htorch]"). by iFrame.
        iNext. rewrite deep_handler_unfold.
        iApply "IH_handler". by iAssumption.
  Qed.    

  Lemma ewp_run_e1:
    stateInv ⊢ EWP run e1 <| ⊥ |> {{v, ∃ (i: nat) (δ: gname), ⌜ v = #i ⌝ ∗ stateInv ∗ frozen δ i}}.
  Proof.
    iIntros "HInv".
    iApply (ewp_run with "HInv").
    iIntros (γ) "(Htorch & HInv)".
    iApply (ewp_mono with "[HInv]").
      by iApply ewp_e1.
    iIntros (_) "HInv !>". by iFrame.
  Qed.
End verification.

Section specification.
  Context `{!heapGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Class RCompLib := {
    prot : gname → iEff Σ;
    is_member : loc → gname → gname → iProp Σ;
    is_member_Persistent r γ δ : Persistent (is_member r γ δ);
    is_torch : gname → iProp Σ;
    state_active : gname → nat -> iProp Σ;
    state_frozen : gname → nat -> iProp Σ;
    state_frozen_Persistent δ i : Persistent (state_frozen δ i);
    state_inv : iProp Σ;
    spawn_spec γ (e : val) :
      state_inv ∗ (∀ γ', is_torch γ' ∗ state_inv -∗ EWP e #() <| prot γ' |> {{ _, is_torch γ' ∗ state_inv }}) -∗
        EWP spawn e <| prot γ |> {{ v, ∃ (i : nat) (δ : gname), ⌜ v = #i ⌝ ∗ state_inv ∗ state_frozen δ i }};
    get_my_state_spec γ :
      is_torch γ -∗
        EWP get_my_state #() <| prot γ |> {{ v, ∃ (r: loc) (δ : gname), ⌜ v = #r ⌝ ∗ is_torch γ ∗ is_member r γ δ }};
  }.

  Definition run_spec (main : val) :=
    (∀ (_ : RCompLib) (γ : gname), (is_torch γ ∗ state_inv -∗ EWP main #() <| prot γ |> {{ _, is_torch γ ∗ state_inv }})) ==∗
      EWP run main <| ⊥ |> {{ _, True }}.

End specification.

Section closed_proof.
  Context `{!heapGS Σ, !fstateGpreS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Lemma stateInv_init :
    ⊢ |==> ∃ (_ : fstateGS Σ) , stateInv.
  Proof.
    iIntros. 
    iMod (own_alloc (● (∅ : gmap (loc * gname * gname) _))) as (γ) "HI";
      first by rewrite auth_auth_valid.
    iModIntro. iExists {| fstate_inG := _; fstate_name := γ; |}.
    iExists ∅. rewrite /isMemberMap. by iFrame.
  Qed.

  Local Program Instance r_comp_lib `{!fstateGS Σ} :
    RCompLib (Σ:=Σ) := {
    prot := R;
    is_member := isMember;
    is_member_Persistent := _;
    is_torch := torch;
    state_active := active;
    state_frozen := frozen;
    state_frozen_Persistent := _;
    state_inv := stateInv
  }.
  Next Obligation. 
    iIntros (???) "(HInv & He)".
    iApply (ewp_mono with "[He HInv]").
    iApply ewp_spawn.
    iFrame. 
    iIntros (?) "(%i & %δ &HInv & Hfroze) !>".
    iExists i, δ.
    iSplit; first done.
    iFrame.
  Qed.
  Next Obligation.
    iIntros (??) "Htorch". 
    by iApply ewp_get_my_state.
  Qed.

  Theorem run_correct main : run_spec main.
  Proof.
    iIntros "He". 
    iMod stateInv_init as "(%HfstateGS  & HInv)".
    iSpecialize ("He" $! r_comp_lib). iModIntro.
    iApply (ewp_mono with "[He HInv]").
    iApply (ewp_run with "HInv He").
    by iIntros (v) "_ !>".
  Qed.

End closed_proof.

Print Assumptions  run_correct.