(* parameterized_protocols.v *)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth gset gset gmap agree csum.
From iris.base_logic.lib Require Import iprop wsat invariants.
From program_logic Require Import reasoning_rules.
From case_studies Require Import list_lib queue_lib.

(* ========================================================================== *)
(** * Implementation of the Scheduler. *)

Section implementation.
  Context `{!heapGS Σ}.

  Definition new_state : val := (λ: <>,
    ref #0
  )%V.
  Definition get_my_state : val := (λ: <>, do: #())%V.

  Definition inc : val := (λ: <>,
    let: "r" := get_my_state #() in
    "r" <- (Load "r") + #1
  )%V.

  Definition e : val := (λ: <>,
    inc #();;
    inc #();;
    #()
  )%V.

  Definition run : val := (λ: "e1",
    let: "fulfill" := (λ: "r" "e",
      deep-try: "e" #() with
        effect (λ: <> "k", "k" "r")
      | return (λ: <>, Load "r")
      end) in
    let: "r1" := new_state #() in
    (* let: "r2" := new_state #() in *)
    let: "res1" := "fulfill" "r1" "e1" in 
    (* let: "res2" := "fulfill" "r2" "e1" in  *)
    "res1"
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

     isState r ≜
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

  Definition isState r γ δ :=
    own fstate_name (◯ {[(r, γ, δ) := tt]}).

  Definition isStateMap (M : gmap (loc * gname * gname) unit) :=
    own fstate_name (● M).

  Definition active (δ : gname) (i : nat) : iProp Σ :=
    own δ (Cinl (Excl i)).
  Definition frozen (δ : gname) (i : nat) : iProp Σ :=
    own δ (Cinr (to_agree i)).

  Definition stateInv : iProp Σ := (
    ∃ M, isStateMap M ∗
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
    Global Instance isState_Persistent r γ δ : Persistent (isState r γ δ).
    Proof. by apply _. Qed.

    Lemma update_fstate_map M r γ δ:
      M !! (r, γ, δ) = None →
        isStateMap M ==∗
          isStateMap (<[(r,γ,δ):=tt]> M) ∗ isState r γ δ.
    Proof.
      (* intros Hlkp. unfold isFstateMap. iIntros "HM".
      iMod (own_update with "HM") as "[HM HiP]".
      { apply (@auth_update_alloc (gmapUR _ _) (promise_unfold <$> M)).
        apply (alloc_singleton_local_update _ ((p, γ), (cf, state, δ)) (promise_unfold Φ)).
        by rewrite /= lookup_fmap Hlkp. done. }
      iModIntro. iFrame. by rewrite fmap_insert. *)
    Admitted.

    Lemma claim_membership M r γ δ:
      isStateMap M ∗ isState r γ δ -∗
        ⌜ M !! (r, γ, δ) = Some tt ⌝.
    Proof.
      (* rewrite /isFstateMap /isMember.
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
      iRewrite -"HpM" in "HM". by rewrite agree_idemp. *)
    Admitted.

    Lemma fstateSt_non_duplicable r γ γ' δ δ' :
      stateSt r γ δ -∗ stateSt r γ' δ' -∗ False.
    Proof.
      (* assert (⊢ ∀ q p γ cf state δ Φ, fstateSt q p γ cf state δ Φ -∗ ∃ v, p ↦ v)%I as Haux.
      { rewrite /fstateSt.
        iIntros (???????) "(%i & Hstate & 
                           [ (_ & %y & Hp & _) 
                           | (_ & %l & %ks & Hp & _ ) ])";
          auto. }
      iIntros "Hp Hp'".
      iPoseProof (Haux with "Hp")  as "[%v  Hp]".
      iPoseProof (Haux with "Hp'") as "[%v' Hp']".
      by iDestruct (mapsto_ne with "Hp Hp'") as "%Hneq". *)
    Admitted.

    Lemma update_stateInv r γ δ :
      stateInv ∗ stateSt r γ δ ==∗
        stateInv ∗ isState r γ δ.
    Proof.
      (* iIntros "[HpInv Hp]". rewrite /fstateInv.
      iDestruct "HpInv" as (M) "[HM HInv]".
      destruct (M !! ((p, γ), (cf, state, δ))) as [Ψ|] eqn:Hlkp.
      - rewrite (big_opM_delete _ _ _ _ Hlkp).
        iDestruct "HInv" as "[Hp' _]".
        by iDestruct (fstateSt_non_duplicable with "Hp Hp'") as "HFalse".
      - iMod (update_fstate_map M p γ cf state δ Φ Hlkp with "HM") as "[HM Hmem]".
        iModIntro. iFrame. iExists (<[((p, γ), (cf, state, δ)):=Φ]> M). iFrame.
        rewrite big_opM_insert; last done. by iFrame. *)
    Admitted.

    Lemma lookup_stateInv r γ δ :
      stateInv -∗ isState r γ δ -∗
        ▷ ((stateSt r γ δ -∗ stateInv) ∗ stateSt r γ δ).
    Proof.
      (* iIntros "HpInv Hmem". rewrite /fstateInv.
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
        by rewrite discrete_fun_equivI. *)
    Admitted.

  End promise_preds.
End predicates.


(* -------------------------------------------------------------------------- *)
(** Protocol [GetState]. *)

Section protocol_getstate.
  Context `{!heapGS Σ, !fstateGS Σ}.

  (* a.d. protocols parameterized by a gname so that we know which isMember we get from GET_CONTEXT *)
  (* Definition GET_STATE (γδ: gname * gname): iEff Σ :=
    let '(γ, δ) := γδ in
    >> (_: val) >> !(#()) {{True}};
    << (r : loc) << ?((#r)%V) {{isState r γ δ}} @ OS.

  Lemma upcl_GetState γ δ v Φ' :
    iEff_car (upcl OS (GET_STATE (γ, δ))) v Φ' ≡
      (∃ (_: val), ⌜ v = #() ⌝ ∗
            (∀ (r : loc), isState r γ δ -∗ Φ' (#r)%V ))%I.
  Proof. 
    rewrite /GET_STATE (upcl_tele' [tele _] [tele _]). 
    simpl. iSplit.
    - iIntros "(%_ & -> & _ & H)".
      iExists #(). iSplit; first done.
      iIntros (r) "Hstate".
      iSpecialize ("H" $! r with "Hstate").
      iApply "H".
    - iIntros "(%_ & -> & H)".
      iExists #(). iSplit; first done.
      iSplit; first done.
      iIntros (r) "Hstate".
      iSpecialize ("H" $! r with "Hstate").
      iApply "H".
  Qed. *)

  Definition GET_STATE (γ: gname): iEff Σ :=
    >> (_: val) >> !(#()) {{True}};
    << (r : loc) (δ : gname) << ?((#r)%V) {{isState r γ δ}} @ OS.

  Lemma upcl_GetState γ v Φ' :
    iEff_car (upcl OS (GET_STATE γ)) v Φ' ≡
      (∃ (_: val), ⌜ v = #() ⌝ ∗
            (∀ (r : loc) (δ : gname), isState r γ δ -∗ Φ' (#r)%V ))%I.
  Proof. 
    rewrite /GET_STATE (upcl_tele' [tele _] [tele _ _]). 
    simpl. iSplit.
    - iIntros "(%_ & -> & _ & H)".
      iExists #(). iSplit; first done.
      iIntros (r δ) "Hstate".
      iSpecialize ("H" $! r δ with "Hstate").
      iApply "H".
    - iIntros "(%_ & -> & H)".
      iExists #(). iSplit; first done.
      iSplit; first done.
      iIntros (r δ) "Hstate".
      iSpecialize ("H" $! r δ with "Hstate").
      iApply "H".
  Qed.

End protocol_getstate.


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
    ⊢ EWP (get_my_state #()) <| GET_STATE γ |> {{ v, ∃ (r : loc) (δ : gname), ⌜ v = #r ⌝ ∗ isState r γ δ}}.
  Proof.
    rewrite /get_my_state. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_GetState.
    iExists #().
    iSplit; first done.
    iIntros (r δ) "Hstate".
    iExists r, δ. iSplit; first done.
    by iFrame.
  Qed.

  Global Instance frozen_Persistent (δ: gname) (i: nat) : Persistent (frozen δ i).
  Proof. by apply _. Qed.

  Lemma ewp_inc γ:
    torch γ ∗ stateInv ⊢ EWP inc #() <| GET_STATE γ |> {{ _, torch γ ∗ stateInv }}.
  Proof.
    iIntros "(Htorch & HInv)".
    rewrite /inc.
    ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply (ewp_mono). 
      by iApply ewp_get_my_state.
    iIntros (v) "(%r & %δ & -> & Hmem) !>".
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
  
  Inductive LongProof := longproof.
  Print longproof.

  Lemma ewp_run (e1 : val):
    stateInv ⊢
      (∀ γ, torch γ ∗ stateInv -∗ EWP e1 #() <| GET_STATE γ |> {{ _, torch γ ∗ stateInv }}) -∗
      (* (∀ γ, torch γ ∗ stateInv -∗ EWP e2 #() <| GET_STATE γ |> {{ _, torch γ ∗ stateInv }}) -∗ *)
        EWP run e1 {{ v, ∃ (i: nat) (δ: gname), ⌜ v = #i ⌝ ∗ stateInv ∗ frozen δ i }}.
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
    iLöb as "IH".
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
    - iIntros (request k). rewrite upcl_GetState.
      idtac.
      iIntros "(%_ & -> & Hk)".
      ewp_pure_steps.
      iApply "Hk".
      iApply "Hmem1".
      iNext. rewrite deep_handler_unfold.
      iApply "IH_handler". iAssumption.
  Qed.    

  Print longproof.

End verification.

Section specification.
  Context `{!heapGS Σ}.
  Context `{!ListLib Σ, !QueueLib Σ}.

  Class AsyncCompLib := {
    coop : gname → iEff Σ;
    is_fstate : val → val → val → (val → iProp Σ) → iProp Σ;
    is_fstate_Persistent p cf state Φ : Persistent (is_fstate p cf state Φ);
    is_member : val → gname → val → val → gname → (val → iProp Σ) → iProp Σ;
    is_member_Persistent p γ cf state δ Φ : Persistent (is_member p γ cf state δ Φ);
    io_log1 : gname → val -> iProp Σ;
    io_log2 : gname → val -> iProp Σ;
    io_log2_Persistent δ i : Persistent (io_log2 δ i);
    fstate_inv : val → iProp Σ;
    async_spec γ q (e : val) Φ :
      fstate_inv q ∗ □ Φ RNone' ∗ (∀ γ', fstate_inv q -∗ EWP e #() <| coop γ' |> {{ y, fstate_inv q ∗ □ Φ (RSome' y) }}) -∗
        EWP async e <| coop γ |> {{ y, ∃ (p cf state : val), ⌜ y = (p, (cf, state))%V ⌝ ∗ fstate_inv q ∗ is_fstate p cf state Φ }};
    await_spec γ q p cf state δ Φ :
      fstate_inv q ∗ is_member p γ cf state δ Φ -∗
        EWP await p <| coop γ |> {{ y, ∃ (v i : val), ⌜ y = (v, i)%V ⌝ ∗ fstate_inv q ∗ □ Φ v ∗ io_log2 δ i }};
    fiber_cancel_spec γ q p cf state δ Φ :
      fstate_inv q ∗ is_member p γ cf state δ Φ -∗
        EWP fiber_cancel (cf, state)%V <| coop γ |> {{ i, fstate_inv q ∗ io_log2 δ i }};
  }.

  Definition run_spec (main : val) :=
    (∀ (_ : AsyncCompLib) (γ : gname), EWP main #() <| coop γ |> {{ _, True }}) ==∗
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
    io_log1 := λ δ v, (∃ (i : nat), ⌜ v = #i ⌝ ∗ io_log_active δ i)%I;
    io_log2 := λ δ v, (∃ (i : nat), ⌜ v = #i ⌝ ∗ io_log_frozen δ i)%I;
    io_log2_Persistent := _;
    fstate_inv := λ (q: val), fstateInv q
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
    iExists y, #i. iSplit; first done.
    iFrame. iSplit; first done.
    iExists i. by iSplit.
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
    iMod promise_and_cancelInv_init as "(%HfstateGS  & HpInv)".
    iSpecialize ("He" $! async_comp_lib). iModIntro.
    iApply (ewp_run _ (λ _, True)%I with "[] HpInv").
    - done.
    - iIntros (γ q) "(_ & HcInv)".
      iApply (ewp_mono with "He [HcInv]"). by auto.
  Qed.

End closed_proof.