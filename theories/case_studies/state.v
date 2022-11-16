(* state.v *)

(* We verify the implementation of a memory cell using effect handlers. *)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth.
From program_logic Require Import reasoning_rules.


(* ========================================================================== *)
(** * Implementation. *)

Definition read : val := (λ: <>, do: InjLV #())%V.

Definition write : val := (λ: "y", do: InjR "y")%V.

Definition run : val := (λ: "main" "init",
  let: "comp" :=
    deep-try: "main" #() with
      effect λ: "args" "k",
        match: "args" with
          (* Read: *) InjL <>  => λ: "x",
            let: "comp" := "k" "x" in
            "comp" "x"
        | (* Write: *) InjR "y" => λ: <> ,
            let: "comp" := "k" #() in
            "comp" "y"
        end
    | return λ: "res",
        λ: <>, "res"
    end
  in
  "comp" "init"
)%V.


(* ========================================================================== *)
(** * Protocol. *)

Definition READ {Σ} St : iEff Σ :=
  (>> x >> ! (InjLV #()) {{ St x }}; ? (x) {{ St x }} @ OS).
Definition WRITE {Σ} St : iEff Σ :=
  (>> x y >> ! (InjRV y) {{ St x }}; ? #() {{ St y }} @ OS).
Definition STATE {Σ} St : iEff Σ := (READ St <+> WRITE St)%ieff.

Lemma upcl_state {Σ} St v Φ :
  iEff_car (upcl OS (STATE (Σ:=Σ) St)) v Φ ⊣⊢
    ((iEff_car (upcl OS (READ  St)) v Φ) ∨
     (iEff_car (upcl OS (WRITE St)) v Φ)).
Proof. by rewrite /STATE; apply upcl_sum. Qed.

Lemma upcl_read {Σ} St v Φ :
  iEff_car (upcl OS (READ (Σ:=Σ) St)) v Φ ⊣⊢
    (∃ x, ⌜ v = InjLV #() ⌝ ∗ St x ∗ (St x -∗ Φ x))%I.
Proof. by rewrite /READ (upcl_tele' [tele _] [tele]). Qed.

Lemma upcl_write {Σ} St v Φ :
  iEff_car (upcl OS (WRITE (Σ:=Σ) St)) v Φ ⊣⊢
    (∃ x y, ⌜ v = InjRV y ⌝ ∗ St x ∗ (St y -∗ Φ #()))%I.
Proof. by rewrite /WRITE (upcl_tele' [tele _ _] [tele]). Qed.


(* ========================================================================== *)
(** * Verification. *)

(* -------------------------------------------------------------------------- *)
(** Ghost Theory. *)

Section ghost_theory.
  Context `{!inG Σ (excl_authR (leibnizO val))}.

  Definition state     γ v := own γ (●E (v : ofe_car (leibnizO val))).
  Definition points_to γ v := own γ (◯E (v : ofe_car (leibnizO val))).

  Lemma ghost_var_alloc v : ⊢ (|==> ∃ γ, state γ v ∗ points_to γ v)%I.
  Proof.
    iMod (own_alloc ((●E (v : ofe_car (leibnizO val))) ⋅
                     (◯E (v : ofe_car (leibnizO val))))) as (γ) "[??]";
    [ apply excl_auth_valid | eauto with iFrame ]; done.
  Qed.
  Lemma ghost_var_agree γ v w : ⊢ (state γ v ∗ points_to γ w) → ⌜ v = w ⌝.
  Proof.
    iIntros "[H● H◯]".
    by iDestruct (own_valid_2 with "H● H◯") as %?%excl_auth_agree_L.
  Qed.
  Lemma ghost_var_update γ w u v :
    state γ u -∗ points_to γ v ==∗ state γ w  ∗ points_to γ w.
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E (w : ofe_car (leibnizO val)) ⋅
                              ◯E (w : ofe_car (leibnizO val)))
      with "Hγ● Hγ◯") as "[$$]";
    [ apply excl_auth_update | ]; done.
  Qed.

End ghost_theory.


(* -------------------------------------------------------------------------- *)
(** Specification & Verification. *)

Section verification.
  Context `{!heapGS Σ} `{!inG Σ (excl_authR (leibnizO val))}.

  Lemma run_spec Φ (init main : val) :
    (∀ St, St init -∗ EWP main #() <| STATE St |> {{ v, Φ v }}) -∗
      EWP run main init {{ v, Φ v }}.
  Proof.
    unfold run.
    iIntros "Hmain". iApply fupd_ewp.
    iMod (ghost_var_alloc init) as (γ) "[Hstate Hpoints_to]". iModIntro.
    ewp_pure_steps. iApply (ewp_bind' (AppRCtx _)). { done. }
    iApply (ewp_deep_try_with with "[Hstate Hmain]").
    { iApply "Hmain". by iApply "Hstate". }
    iLöb as "IH" forall (γ init).
    rewrite !deep_handler_unfold. iSplit; [|iSplit];
    last by iIntros (??) "HFalse"; rewrite upcl_bottom.
    - iIntros (y) "Hy". by ewp_pure_steps.
    - iIntros (args k).
      rewrite upcl_state upcl_write upcl_read.
      iIntros "[[%x (->&Hx&Hk)]|[%x [%y (->&Hx&Hk)]]]";
      ewp_pure_steps; ewp_bind_rule.
      + iDestruct (ghost_var_agree γ x init with "[$]") as %->.
        iApply (ewp_mono with "[Hk Hpoints_to Hx]").
        { iSpecialize ("IH" with "Hpoints_to").
          by iApply ("Hk" with "Hx IH"). }
        by auto.
      + iApply fupd_ewp.
        iMod ((ghost_var_update _ y) with "Hx Hpoints_to") as
          "[Hy Hpoints_to]".
        iModIntro. simpl. iApply ("Hk" with "Hy").
        by iApply "IH".
  Qed.

End verification.
