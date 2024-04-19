From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl excl_auth gset gmap agree csum frac excl.
From iris.base_logic Require Import invariants.
From iris.base_logic.lib Require Import iprop wsat saved_prop.
From program_logic Require Import reasoning_rules.

From case_studies.eio Require Import eio.
From case_studies.mt Require Import spawn.

Definition make_register : val :=
  (λ: "domain" "init" "f", (λ: "waker",
      let: "new_scheduler" := (λ: <>, 
        let: "result" := run "init" "f" in
        "waker" #();;
        "result"
      ) in
      let: "joinh" := spawn "new_scheduler" in
      "domain" <- SOME "joinh"
  ))%V.
Definition spawn_scheduler2 : val :=
  (λ: "init" "f",
    let: "domain" := ref NONEV in
    let: "register" := make_register "domain" "init" "f" in
    suspend "register";;
    match: Load "domain" with
      NONE => #() #()
    | SOME "joinh" => join "joinh"
    end)%V.

Class domainG Σ := DomainG { 
  domain_tokG : inG Σ (exclR unitO)
}.
Local Existing Instance domain_tokG.

Definition domainΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_domainΣ {Σ} : subG domainΣ Σ → domainG Σ.
Proof. solve_inG. Qed.

Section spec.
  Context `{!heapGS Σ, !spawnG Σ, !promiseGS Σ, !domainG Σ}.
  Context (N Njoin: namespace).

  Definition domain_state_fresh γ := own γ (Cinl 1%Qp).
  Definition domain_state_unset γ := own γ (Cinl (1/2)%Qp).
  Definition domain_state_set γ := own γ (Cinr (to_agree #())).

  Definition domain_inv γ δ ℓ Φ := (
    ∃ v, ℓ ↦ v ∗ (
      (⌜ v = NONEV ⌝ ∗ domain_state_unset γ)
    ∨ (∃ (ℓ' : loc), ⌜ v = SOMEV #ℓ' ⌝ ∗ domain_state_set γ ∗ (join_handle Njoin ℓ' (λ v, □ Φ v)%I ∨ own δ (Excl ())))
  ))%I.

  Definition is_domain_ref γ δ ℓ Φ := inv N (domain_inv γ δ ℓ Φ).
  Definition domain_handle γ δ ℓ Φ := (
    own δ (Excl ()) ∗ is_domain_ref γ δ ℓ Φ
  )%I.

  Global Instance domain_state_set_Persistent γ : Persistent (domain_state_set γ).
  Proof. by apply _. Qed.

  Lemma domain_state_fresh_create : ⊢ |==> ∃ γ, domain_state_fresh γ.
  Proof. by iMod (own_alloc (Cinl 1%Qp)) as (γ) "Hps"; last iExists γ. Qed.

  Lemma domain_state_split γ :
    ⊢ domain_state_fresh γ ==∗ domain_state_unset γ ∗ domain_state_unset γ.
  Proof.
    rewrite /domain_state_fresh /domain_state_unset.
    rewrite -own_op.
    iApply own_update.
    rewrite -Cinl_op.
    apply csum_update_l.
    rewrite frac_op.
    rewrite cmra_update_updateP.
    apply cmra_updateP_id. 
    apply Qp_half_half.
  Qed. 

  Lemma domain_state_join γ :
    ⊢ domain_state_unset γ ∗ domain_state_unset γ ==∗ domain_state_fresh γ.
  Proof.
    rewrite /domain_state_fresh /domain_state_unset.
    rewrite -own_op.
    iApply own_update.
    rewrite -Cinl_op.
    apply csum_update_l.
    rewrite frac_op.
    rewrite cmra_update_updateP.
    apply cmra_updateP_id. 
    by rewrite Qp_half_half.
  Qed.

  Lemma domain_state_create ℓ Φ :
    ⊢ ℓ ↦ NONEV ={⊤}=∗ ∃ γ δ, domain_handle γ δ ℓ Φ ∗ domain_state_unset γ.
  Proof.
    iIntros "Hℓ".
    iMod (domain_state_fresh_create) as "(%γ & Hds)".
    iMod (domain_state_split with "Hds") as "(Hds & Hds')".
    iMod (own_alloc (Excl ())) as (δ) "Hδ"; first done.
    iExists γ, δ.
    iFrame. 
    iApply (inv_alloc _ _ (domain_inv γ δ ℓ Φ) with "[Hℓ Hds]").
    iNext. rewrite /domain_inv.
    iExists NONEV. iFrame.
    iLeft. by iFrame.
  Qed.

  Lemma domain_state_fulfill γ :
    ⊢ domain_state_fresh γ ==∗ domain_state_set γ.
  Proof.
    iApply own_update.
    apply cmra_update_exclusive.
    apply Cinr_valid.
    done.
  Qed.
  
  Lemma domain_state_disjoint γ : 
    ⊢ domain_state_unset γ -∗ domain_state_set γ -∗ False.
  Proof. 
    iIntros "H1 H2".
    rewrite /domain_state_unset /domain_state_set.
    iPoseProof (own_valid_2 with "H1 H2") as "H".
    by rewrite csum_validI.
  Qed.
End spec.
      
Section proof.
  Context `{!heapGS Σ, !spawnG Σ, !promiseGS Σ, !savedPredG Σ val, !domainG Σ}.
  Context (N Njoin Nreturn: namespace).

  Lemma make_register_spec γ δ ℓ (I Φ : val -> iProp Σ) (init f: val) :
    ⊢ I init -∗ 
      (∀ ℓres, fiberResources (ℓres, I) -∗ EWP (f #()) <| Coop (ℓres, I) |> {{ v, □ Φ v ∗ fiberResources (ℓres, I) }}) -∗
      is_domain_ref N Njoin γ δ ℓ Φ -∗ 
      domain_state_unset γ -∗
        EWP (make_register #ℓ init f) <| ⊥ |> {{reg, 
          ∀ (waker: val), (∀ (v: val), □ True -∗ EWP (waker v) <| ⊥ |> {{_, True }}) -∗
            (EWP (reg waker) <| ⊥ |> {{_, □ domain_state_set γ }}) }}.
  Proof.
    iIntros "Hinit Hf Hdr Hγ". rewrite /make_register.
    ewp_pure_steps.
    iIntros (waker) "Hwaker".
    ewp_pure_steps.
    (* spawn the new thread *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[Hwaker Hinit Hf]").
    { iApply (spawn_spec Njoin (λ v, □ Φ v)%I with "[Hwaker Hinit Hf]").
      ewp_pure_steps.
      iApply (ewp_bind' (AppRCtx _)); [by done|simpl].
      iApply (ewp_mono with "[Hinit Hf]").
      { iApply (ewp_run Nreturn _ _ I Φ with "Hinit Hf"). }
      iIntros (?) "Hv !>".
      ewp_pure_steps.
      (* call the waker function *)
      ewp_bind_rule; simpl.
      iApply (ewp_mono with "[Hwaker]"); [by iApply "Hwaker"|].
      iIntros (?) "_ !>".
      ewp_pure_steps.
      by iAssumption. }
    iIntros (?) "(%ℓ' & -> & Hj) !>".
    ewp_pure_steps.
    iInv N as "(% & Hℓ & Hds)" "Hclose".
    iApply (ewp_store with "Hℓ").
    iIntros "!> Hℓ !>".
    iDestruct "Hds" as "[(_ & Hγ')|(% & _ & Hγ' & _)]".
    2: {
      (* impossible *)
      by iDestruct (domain_state_disjoint with "Hγ Hγ'") as "%HFalse".
    }
    iMod (domain_state_join γ with "[$]") as "Hγ".
    iMod (domain_state_fulfill with "Hγ") as "#Hγ".
    iMod ("Hclose" with "[Hj Hℓ Hγ]") as "_".
    { iNext. rewrite /domain_inv. 
      iExists _. iFrame "Hℓ". iRight.
      iExists _. iSplit; first by done.
      iFrame "Hγ". by iLeft. }
    iModIntro. by iAssumption.
  Qed.

  Lemma spawn_scheduler2_spec fargs (I Φ : val -> iProp Σ) (init f: val) :
    ⊢ I init -∗ 
      fiberResources fargs -∗ 
      (∀ ℓres, fiberResources (ℓres, I) -∗ EWP (f #()) <| Coop (ℓres, I) |> {{ v, □ Φ v ∗ fiberResources (ℓres, I) }}) -∗
        EWP (spawn_scheduler2 init f) <| Coop fargs |> {{ v, □ Φ v ∗ fiberResources fargs }}.
  Proof.
    iIntros "Hinit HfRes Hf". rewrite /spawn_scheduler2.
    ewp_pure_steps.
    (* Allocate domain ref and its invariant. *)
    (* a.d. TODO bind rule does not work for binding ref *)
    iApply (ewp_bind' (AppRCtx _)); [by done|simpl].
    iApply (ewp_alloc); iIntros "!> %ℓ Hℓ".
    iMod (domain_state_create N Njoin _ Φ with "Hℓ") as (γ δ) "((Hδ & #Hdr) & Hγ)".
    iModIntro. ewp_pure_steps.
    (* Create the register function. *)
    iApply (ewp_bind' (AppRCtx _)); [by done|simpl].
    iApply (ewp_mono with "[Hdr Hinit Hf Hγ]").
    { iApply (ewp_os_prot_mono _ ⊥); first iApply iEff_le_bottom.
      iApply (make_register_spec with "Hinit Hf Hdr Hγ"). }
    iIntros (reg) "Hreg !>".
    ewp_pure_steps.
    (* Perform suspend effect to get back domain_state_set γ *)
    ewp_bind_rule; simpl.
    iApply (ewp_mono with "[Hreg HfRes]").
    { iApply (ewp_suspend _ _ (λ _, □ True)%I (domain_state_set γ) with "HfRes Hreg"). }
    iIntros (?) "(HfRes & _ & Hγ) !>".
    ewp_pure_steps.
    (* Match the domain ref and contradict the second case. *)
    ewp_bind_rule; simpl.
    rewrite /is_domain_ref.
    iApply (ewp_atomic ⊤ (⊤ ∖ ↑N)).
    iMod (inv_acc with "Hdr") as "(Hd & Hclose)"; first by done.
    iModIntro.
    iDestruct "Hd" as "(% & Hℓ & [(_ & Hγ')|(%ℓ' & Heq & Hγ' & [Hj|Hδ'])])".
    1: {
      (* impossible *)
      iApply (ewp_load with "Hℓ").
      iIntros "!>".
      by iDestruct (domain_state_disjoint with "Hγ' Hγ") as "%HFalse". 
    }
    2: {
      (* impossible *)
      iApply (ewp_load with "Hℓ").
      iIntros "!>".
      iCombine "Hδ Hδ'" as "H".
      iPoseProof (own_valid with "H") as "%H".
      destruct (exclusive_l _ _ H).
    }
    iApply (ewp_load with "Hℓ").
    iIntros "!> Hℓ !>".
    iDestruct "Heq" as "->".
    iMod ("Hclose" with "[Hδ Hℓ Hγ']") as "_".
    { 
      iNext. rewrite /domain_inv.
      iExists _. iFrame "Hℓ". iRight.
      iExists _. iSplit; first done.
      by iFrame.
    }
    iModIntro.
    ewp_pure_steps.
    iApply (ewp_mono with "[Hj]").
    { iApply (ewp_os_prot_mono); [iApply iEff_le_bottom|].
      iApply (join_spec with "Hj"). }
    iIntros (?) "Hv !>".
    iFrame.
  Qed.

End proof.