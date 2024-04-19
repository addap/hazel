From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth gset gmap agree csum frac excl.
From iris.base_logic Require Import invariants.
From iris.base_logic.lib Require Import iprop wsat saved_prop.
From program_logic Require Import reasoning_rules.
From case_studies Require Import list_lib .
From case_studies.eio Require Import eio.
From case_studies.mt Require Import spawn domain_manager.

Section complex.

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
  Context (Nresult : namespace).
  
  Lemma ewp_work (n : Z) :
    ⊢ EWP (work #n) {{f, ∀ fargs, fiberResources fargs -∗
        EWP f #() <| Coop fargs |> {{v, □ ⌜ v = #n ⌝ ∗ fiberResources fargs }}
      }}.
  Proof.
    rewrite /work.
    ewp_pure_steps.
    iIntros (fargs) "HfRes".
    ewp_pure_steps.
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[HfRes]"); [iApply (ewp_yield with "HfRes")|].
    iIntros (?) "HfRes !>".
    ewp_pure_steps. 
    by iFrame.
  Qed.

  Context (N Njoin : namespace).

  Lemma ewp_spawnwork fargs (f : val) Φ :
    ⊢ promiseInv -∗ 
      fiberResources fargs -∗
      (∀ fargs', fiberResources fargs' -∗ EWP f #() <| Coop fargs' |> {{v, □ Φ v ∗ fiberResources fargs' }}) -∗ 
        EWP (spawnwork f) <| Coop fargs |> {{v, 
          ∃ (p: loc), ⌜ v = #p ⌝ ∗ isPromise p Φ ∗ fiberResources fargs }}.
  Proof.
    iIntros "#HInv HfRes Hf".
    rewrite /spawnwork.
    ewp_pure_steps.
    iApply (ewp_fork_promise with "HInv HfRes").
    iIntros "HfRes".
    ewp_pure_steps.
    iApply (spawn_scheduler2_spec N Njoin Nresult _ (λ _, True)%I Φ #() f with "[//] HfRes [Hf]").
    iIntros "% HfRes".
    iApply ("Hf" $! (ℓres, (λ _, True)%I) with "HfRes").
  Qed.

  Lemma ewp_wait_for_data γ ℓtlv :
    ⊢ fiberResources (ℓtlv, tlvI γ) -∗
        EWP wait_for_data #ℓtlv <| Coop (ℓtlv, tlvI γ) |> {{v, ∃ (i1 i2 : Z), ⌜ v = (PairV #i1 #i2) ⌝ ∗ tlvContent γ i1 i2 ∗ fiberResources (ℓtlv, tlvI γ) }}.
  Proof.
    iIntros "HfRes".
    rewrite /wait_for_data.
    iLöb as "IH".
    ewp_pure_steps.
    iDestruct "HfRes" as "(% & Hℓtlv & HI)".
    ewp_bind_rule; simpl.
    iApply (ewp_load with "Hℓtlv").
    iIntros "!> Hℓtlv !>".
    rewrite /tlvI.
    iDestruct "HI" as "[->|(%&%&->&#Hi)]".
    - ewp_pure_steps.
      ewp_bind_rule; simpl.
      iApply (ewp_mono with "[Hℓtlv]").
      { iApply (ewp_yield with "[Hℓtlv]").
        iExists _. simpl.
        iFrame "Hℓtlv".
        by iLeft. }
      iIntros (?) "HfRes !>".
      do 3 ewp_value_or_step.
      iApply ("IH" with "HfRes").
    - ewp_pure_steps.
      iExists _, _. 
      iSplitR; first done.
      iSplit; first done.
      iExists _. simpl.
      iFrame "Hℓtlv".
      iRight. iExists _, _.
      iSplit; done.
  Qed.

  Lemma ewp_dispach γ ℓtlv i1 i2 : 
    ⊢ promiseInv -∗
      tlvContent γ i1 i2 -∗ 
      fiberResources (ℓtlv, tlvI γ) -∗
        EWP dispatch #() <| Coop (ℓtlv, tlvI γ) |> {{v, ⌜ v = #(i1 + i2) ⌝ ∗ fiberResources (ℓtlv, tlvI γ) }}.
  Proof.
    iIntros "#HInv #Htlvc HfRes".
    rewrite /dispatch.
    ewp_pure_steps.
    (* get context *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono); [iApply (ewp_get_context)|].
    iIntros (?) "-> !>".
    ewp_pure_steps.
    (* wait until tlv is filled *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[HfRes]"); [iApply (ewp_wait_for_data with "HfRes")|].
    iIntros (?) "(%i1'&%i2'&->&#Htlvc'&HfRes) !>".
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
    iApply (ewp_mono with "[Hp1 HfRes]"); [iApply (ewp_await with "HInv HfRes Hp1")|].
    iIntros (r1) "(-> & HfRes) !>". 
    ewp_pure_steps.
    (* r2 *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[Hp2 HfRes]"); [iApply (ewp_await with "HInv HfRes Hp2")|].
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
          ∀ ℓtlv, fiberResources (ℓtlv, tlvI γ) -∗
            EWP f #() <| Coop (ℓtlv, tlvI γ) |> {{v, □ ⌜ v = #(i1 + i2) ⌝ ∗ fiberResources (ℓtlv, tlvI γ) }}
        }}.
  Proof.
    iIntros "#HInv #Htlvc".
    rewrite /main_fiber.
    ewp_pure_steps.
    iIntros (?) "HfRes".
    ewp_pure_steps.
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[HfRes]").
    { iApply (ewp_fork_promise _ _ (λ v, ⌜ v = #(i1 + i2) ⌝)%I with "HInv HfRes").
      iIntros "HfRes".
      iApply (ewp_mono with "[HfRes]").
      iApply (ewp_dispach with "HInv Htlvc HfRes").
      iIntros (?) "(-> & HfRes) !>".
      by iFrame. }
    iIntros (?) "(% & -> & #HisPr & HfRes) !>".
    ewp_pure_steps.
    (* get context *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono); [iApply (ewp_get_context)|].
    iIntros (?) "-> !>".
    iDestruct "HfRes" as "(% & Hℓtlv & HI)".
    ewp_pure_steps.
    ewp_bind_rule; simpl.
    iApply (ewp_store with "Hℓtlv").
    iIntros "!> Hℓtlv !>".
    ewp_pure_steps.
    (* await the result *)
    iApply (ewp_mono with "[Hℓtlv]").
    { iApply (ewp_await with "HInv [Hℓtlv] HisPr").
      iExists _. simpl.
      iFrame "Hℓtlv".
      iRight. iExists _, _.
      iSplit; done. }
    by iIntros (?) "(-> & $)".
  Qed.
End proof.

Section closed.
  Context `{!heapGS Σ, !promiseGpreS Σ, !savedPredG Σ val, !spawnG Σ, !domainG Σ, !exampleG Σ}.
  Context (N Njoin Nresult : namespace).

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
    iApply (ewp_mono); [iApply (ewp_main_fiber N Njoin Nresult with "HInv Htlvc")|].
    iIntros (f) "Hf !>".
    ewp_pure_steps.
    iApply (ewp_mono with "[Hf]").
    iApply (ewp_run Nresult _ _ (tlvI γ) with "[] Hf").
    by iLeft.
    iIntros (?) "-> !>".
    iPureIntro.
    by compute.
  Qed.
End closed.


  

