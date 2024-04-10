From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth gset gmap agree csum frac excl.
From iris.base_logic Require Import invariants.
From iris.base_logic.lib Require Import iprop wsat saved_prop.
From program_logic Require Import reasoning_rules.
From case_studies Require Import list_lib .
From case_studies.eio Require Import eio.
From case_studies.mt Require Import spawn domain_manager.

Section simple.
  Context `{AsyncCompLib}.
  
  Existing Instance promise_inv_Persistent.

  Definition simple_dispatch : val := (λ: <>, 
    #1
  )%V.
  Definition simple_main : val := (λ: <>, 
    let: "p" := fork_promise simple_dispatch in
    let: "r" := await "p" in
    "r"
  )%V.

  Lemma ewp_simple_dispatch δ ℓres : 
    ⊢ EWP simple_dispatch #() <| coop (δ, ℓres) |> {{ v, ⌜ v = #1 ⌝ }}.
  Proof.
    iIntros.
    rewrite /simple_dispatch.
    ewp_pure_steps.
    done.
  Qed.
    
  Lemma ewp_simple_main δ ℓres : 
    fiber_resources δ ℓres ∗ promise_inv
    ⊢ EWP simple_main #() <| coop (δ, ℓres) |> {{ v, ⌜ v = #1 ⌝ }}.
  Proof.
    iIntros "(HfRes & #HpInv)".
    rewrite /simple_main. ewp_pure_steps.
    ewp_bind_rule; simpl.
    iApply (ewp_mono _ _ with "[HfRes]"). 
    { iApply fork_spec. iFrame. iSplit; first by done.
      iIntros "HfRes". iApply (ewp_mono). iApply ewp_simple_dispatch.
      iIntros (?) "-> !>".
      Unshelve. 2: exact (λ v, ⌜ v = #1 ⌝%I).
      simpl. iSplit; first done. done.
    }
    iIntros (p) "(Hp & HfRes) !>".
    ewp_pure_steps.
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[HfRes Hp]").
    { iApply await_spec. iFrame. by iAssumption. }
    iIntros (?) "(-> & HfRes) !>".
    ewp_pure_steps.
    done.
  Qed.
End simple.

Section complex.
  (* main fiber spawns N schedulers in other threads and collects their results. *)

  (* fiber that gets spawned in a new thread *)
  Definition work : val := (λ: "seed" <>,
    yield #();;
    "seed"
  )%V.

  (* fiber that spawns the given "f" in a new thread. *)
  Definition spawnwork : val := (λ: "f",
    fork_promise (λ: <>, spawn_scheduler2 #() "f")
  )%V.

  Definition wait_for_data : val := (rec: "loop" "ctx" := 
    match: Load "ctx" with
      NONE => yield #();; "loop" "ctx"
    | SOME "data" => "data"
    end)%V.

  (* fiber that forks "spawnwork" multiple times. *)
  Definition dispatch : val := (λ: <>,
    let: "ctx" := get_context #() in
    let: "data" := wait_for_data "ctx" in
    let: "p1" := spawnwork (work (Fst "data")) in 
    let: "p2" := spawnwork (work (Snd "data")) in 
    let: "r1" := await "p1" in
    let: "r2" := await "p2" in
    "r1" + "r2"
  )%V.

  Definition main_fiber : val := (λ: "i1" "i2" <>, 
    let: "p" := fork_promise dispatch in
    let: "ctx" := get_context #() in
    "ctx" <- SOME ("i1", "i2");;
    await "p"
  )%V.

  Definition main : val := (λ: <>,
    let: "f" := main_fiber #17 #25 in
    run NONEV "f"
  )%V.
Section complex.

Class exampleG Σ := {
  tlvContentG :> inG Σ (agreeR (prodO ZO ZO))
}.

Definition exampleΣ := #[
  GFunctor (agreeR (prodO ZO ZO))
].

Instance subG_exampleΣ {Σ} : subG exampleΣ Σ → exampleG Σ.
Proof. solve_inG. Qed.

Section spec.
  Context `{!exampleG Σ}.

  Definition tlvContent γ (i1 i2 : Z) := own γ (to_agree (i1, i2)).
  Definition tlvI γ (v : val) : iProp Σ := (
    ⌜ v = NONEV ⌝ ∨ ∃ (i1 i2 : Z), ⌜ v = SOMEV (PairV #i1 #i2) ⌝ ∗ tlvContent γ i1 i2
  )%I.

  Lemma tlvContent_create i1 i2 :
    ⊢ |==> ∃ γ, tlvContent γ i1 i2.
  Proof. by iMod (own_alloc (to_agree (i1, i2))) as (γ) "Htlvc"; last iExists γ. Qed.

  Lemma tlvContent_agree γ i1 i1' i2 i2' :
    ⊢ tlvContent γ i1 i2 -∗ tlvContent γ i1' i2' -∗ ⌜ i1 = i1' ∧ i2 = i2' ⌝.
  Proof.
    iIntros "H H'". 
    iCombine "H H'" as "H".
    iPoseProof (own_valid with "H") as "%".
    iPureIntro.
    pose proof (to_agree_op_inv_L _ _ H) as H'.
    by injection H'.
  Qed.
End spec.

Section proof.
  Context `{!heapGS Σ, !promiseGS Σ, !savedPredG Σ val, !spawnG Σ, !domainG Σ, !exampleG Σ}.
  
  Existing Instance promise_inv_Persistent.
  Existing Instance tlv_agree_Persistent.
  Existing Instance is_promise_Persistent.

  Lemma ewp_work (n : Z) :
    ⊢ EWP (work #n) {{f, ∀ δ ℓres, fiberResources δ ℓres -∗
        EWP f #() <| Coop (δ, ℓres) |> {{v, □ ⌜ v = #n ⌝ ∗ fiberResources δ ℓres }}
      }}.
  Proof.
    rewrite /work.
    ewp_pure_steps.
    iIntros (δ ℓres) "HfRes".
    ewp_pure_steps.
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[HfRes]"); [iApply (ewp_yield with "HfRes")|].
    iIntros (?) "HfRes !>".
    ewp_pure_steps. 
    by iFrame.
  Qed.

  Context (N Njoin : namespace).

  Lemma ewp_spawnwork δ ℓres (f : val) Φ :
    ⊢ promiseInv -∗ 
      fiberResources δ ℓres -∗
      (∀ δ' ℓres', fiberResources δ' ℓres' -∗ EWP f #() <| Coop (δ', ℓres') |> {{v, □ Φ v ∗ fiberResources δ' ℓres' }}) -∗ 
        EWP (spawnwork f) <| Coop (δ, ℓres) |> {{v, 
          ∃ (p: loc), ⌜ v = #p ⌝ ∗ isPromise p Φ ∗ fiberResources δ ℓres}}.
  Proof.
    iIntros "#HInv HfRes Hf".
    rewrite /spawnwork.
    ewp_pure_steps.
    iApply (ewp_fork_promise).
    iFrame "HfRes HInv".
    iIntros "HfRes".
    ewp_pure_steps.
    iApply (spawn_scheduler2_spec N Njoin _ _ (λ _, True)%I Φ #() f with "HInv [] [Hf]").
    - by done.
    - iIntros "% _ HfRes".
      destruct δℓ as [δ' ℓres'].
      iSpecialize ("Hf" $! δ' ℓres' with "HfRes").
      iApply (ewp_mono with "[Hf]"); [iApply "Hf"|].
      iIntros (?) "HΦ !>".
      by iFrame.
    - by iFrame.
  Qed.

  Lemma ewp_wait_for_data γ δ ℓres ℓtlv :
    ⊢ isTlvPred δ.1.2 (tlvI γ) -∗ 
      tlvAgree δ.1.1 ℓtlv -∗
      fiberResources δ ℓres -∗
        EWP wait_for_data #ℓtlv <| Coop (δ, ℓres) |> {{v, fiberResources δ ℓres ∗ ∃ (i1 i2 : Z), ⌜ v = (PairV #i1 #i2) ⌝ ∗ tlvContent γ i1 i2 }}.
  Proof.
    iIntros "#HPred #HℓtlvAg HfRes".
    rewrite /wait_for_data.
    iLöb as "IH".
    ewp_pure_steps.
    destruct δ as [[δ11 δ12] δ2].
    iDestruct "HfRes" as "((%ℓtlv' & #HℓtlvAg' & % & % & #HPred' & Hℓtlv & HI) & HRest)".
    rewrite /tlvAgree /isTlvPred.
    iDestruct (tlvAgree_agree with "HℓtlvAg HℓtlvAg'") as "->".
    iDestruct (saved_pred_agree _ _ _ v with "HPred HPred'") as "Heq".
    ewp_bind_rule; simpl.
    iApply (ewp_load with "Hℓtlv").
    iIntros "!> Hℓtlv !>".
    iRewrite -"Heq" in "HI".
    rewrite /tlvI.
    iDestruct "HI" as "[->|(%&%&->&#Hi)]".
    - ewp_pure_steps.
      ewp_bind_rule; simpl.
      iApply (ewp_mono with "[Hℓtlv HRest]").
      { iApply (ewp_yield with "[Hℓtlv HRest]").
        iFrame "HRest". iExists ℓtlv'.
        rewrite /isFiberContext.
        simpl.
        repeat iSplit; try done.
        iExists (InjLV #()), (tlvI γ). 
        repeat iSplit; try done.
        by iLeft. }
      iIntros (?) "HfRes !>".
      do 3 ewp_value_or_step.
      iApply ("IH" with "HfRes").
    - ewp_pure_steps.
      iSplitL. 
      { iFrame "HRest". iExists ℓtlv'.
        rewrite /isFiberContext.
        simpl.
        repeat iSplit; try done.
        iExists (InjRV (PairV #i1 #i2)), (tlvI γ). 
        repeat iSplit; try done.
        rewrite /tlvI.
        iRight. iExists _, _.
        repeat iSplit; try done. }
      iExists _, _. by iSplit.
  Qed.

  Lemma ewp_dispach γ δ ℓres i1 i2 : 
    ⊢ promiseInv -∗
      isTlvPred δ.1.2 (tlvI γ) -∗
      tlvContent γ i1 i2 -∗ 
      fiberResources δ ℓres -∗
        EWP dispatch #() <| Coop (δ, ℓres) |> {{v, ⌜ v = #(i1 + i2) ⌝ ∗ fiberResources δ ℓres }}.
  Proof.
    iIntros "#HInv #HPred #Htlvc HfRes".
    rewrite /dispatch.
    ewp_pure_steps.
    (* get context *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono); [iApply (ewp_get_context)|].
    iIntros (?) "(%ℓtlv & -> & #HℓtlvAg) !>".
    ewp_pure_steps.
    (* wait until tlv is filled *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[HfRes]"); [iApply (ewp_wait_for_data with "HPred HℓtlvAg HfRes")|].
    iIntros (?) "(HfRes&%i1'&%i2'&->&#Htlvc') !>".
    iDestruct (tlvContent_agree with "Htlvc Htlvc'") as "[<- <-]".
    ewp_pure_steps.
    (* p1 *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono).
    { iApply ewp_os_prot_mono; [iApply iEff_le_bottom|iApply (ewp_work i1)]. }
    iIntros (f1) "Hf1 !>".
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[Hf1 HfRes]"); [iApply (ewp_spawnwork with "HInv HfRes Hf1")|].
    iIntros (?) "(%p1 & -> & Hp1 & HfRes) !>".
    ewp_pure_steps.
    (* p2 *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono).
    { iApply ewp_os_prot_mono; [iApply iEff_le_bottom|iApply (ewp_work i2)]. }
    iIntros (f2) "Hf2 !>".
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[Hf2 HfRes]"); [iApply (ewp_spawnwork with "HInv HfRes Hf2")|].
    iIntros (?) "(%p2 & -> & Hp2 & HfRes) !>".
    ewp_pure_steps.
    (* r1 *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[Hp1 HfRes]"); [iApply (ewp_await with "[$]")|].
    iIntros (r1) "(-> & HfRes) !>". 
    ewp_pure_steps.
    (* r2 *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[Hp2 HfRes]"); [iApply (ewp_await with "[$]")|].
    iIntros (r2) "(-> & HfRes) !>". 
    ewp_pure_steps.
    (* calculate *)
    by reflexivity.
    by iFrame.
  Qed.

  Lemma ewp_main_fiber γ i1 i2 : 
    ⊢ promiseInv -∗
      tlvContent γ i1 i2 -∗ 
        EWP main_fiber #i1 #i2 {{f, 
          ∀ δ ℓres, isTlvPred δ.1.2 (tlvI γ) -∗ fiberResources δ ℓres -∗
            EWP f #() <| Coop (δ, ℓres) |> {{v, □ ⌜ v = #(i1 + i2) ⌝ ∗ fiberResources δ ℓres }}
        }}.
  Proof.
    iIntros "#HInv #Htlvc".
    rewrite /main_fiber.
    ewp_pure_steps.
    iIntros (? ?) "#HPred HfRes".
    ewp_pure_steps.
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[HfRes]").
    { iApply (ewp_fork_promise _ _ (λ v, ⌜ v = #(i1 + i2) ⌝)%I).
      iFrame "HfRes HInv".
      iIntros "HfRes".
      iApply (ewp_mono with "[HfRes]").
      iApply (ewp_dispach with "HInv HPred Htlvc HfRes").
      iIntros (?) "(-> & HfRes) !>".
      by iFrame. }
    iIntros (?) "(% & -> & #HisPr & HfRes) !>".
    ewp_pure_steps.
    (* get context *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono); [iApply (ewp_get_context)|].
    iIntros (?) "(%ℓtlv & -> & #HℓtlvAg) !>".
    iDestruct "HfRes" as "((%ℓtlv' & #HℓtlvAg' & % & % & #HPred' & Hℓtlv & _) & HRest)".
    iDestruct (tlvAgree_agree with "HℓtlvAg HℓtlvAg'") as "->".
    (* iDestruct (saved_pred_agree _ _ _ v with "HPred HPred'") as "Heq". *)
    ewp_pure_steps.
    ewp_bind_rule; simpl.
    iApply (ewp_store with "Hℓtlv").
    iIntros "!> Hℓtlv !>".
    ewp_pure_steps.
    (* await the result *)
    iApply (ewp_mono with "[Hℓtlv HRest]").
    { iApply (ewp_await with "[Hℓtlv HRest]").
      iFrame "HInv HisPr HRest".
      iExists ℓtlv'. 
      iFrame "HℓtlvAg".
      iExists _, _. iFrame "HPred Hℓtlv".
      iRight. iExists _, _. by repeat iSplit. }
    by iIntros (?) "(-> & $)".
  Qed.
End proof.

Section closed.
  Context `{!heapGS Σ, !promiseGpreS Σ, !savedPredG Σ val, !spawnG Σ, !domainG Σ, !exampleG Σ}.
  Context (N Njoin : namespace).

  Lemma ewp_main :
    ⊢ EWP main #() {{v, ⌜ v = #42 ⌝ }}.
  Proof.
    rewrite /main.
    ewp_pure_steps.
    rewrite -fupd_ewp.
    iMod (promiseInv_init) as (?) "#HInv".
    iMod (tlvContent_create 17 25) as (γ) "#Htlvc".
    iModIntro.
    iApply (ewp_bind' (AppRCtx _)); [by done|simpl].
    iApply (ewp_mono); [iApply (ewp_main_fiber N Njoin with "HInv Htlvc")|].
    iIntros (f) "Hf !>".
    ewp_pure_steps.
    iApply (ewp_mono with "[Hf]").
    iApply (ewp_run _ _ (tlvI γ) with "[Hf]").
    iFrame "Hf".
    by iLeft.
    iIntros (?) "-> !>".
    iPureIntro.
    by compute.
  Qed.
End closed.


  

