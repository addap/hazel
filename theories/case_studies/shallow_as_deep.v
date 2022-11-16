(* shallow_as_deep.v *)

(* We show that the encoding of shallow handlers using deep handlers is correct
   in the sense that this encoding enjoys the same reasoning rule as the
   primitive shallow-handler construct of [eff_lang].

   (In fact, this encoding meets a specification slightly different from the
   reasoning rule for shallow handlers. Because the same effect branch [h]
   handles both multi-shot and one-shot effects, the language offers no way
   to distinguish between these two flavors of effects. We are thus obliged
   to make an assumption: effects are either all one-shot or all multi-shot. *)

From iris.proofmode Require Import base tactics classes.
From program_logic Require Import reasoning_rules.


(* ========================================================================== *)
(** * From Deep to Shallow. *)

(* Returns [InjR y] if [tk()] terminates normally with the value [y], and
   returns [InjL (x, k)] if [tk()] performs an effect with payload [x]
   under a context [k]. (Effects are supposed one-shot.) *)
Definition eff_or_ret : val := (λ: "tk",
  deep-try: "tk" #() with
    effect (λ: "x" "k",
      let: "k" := λ: "w",
        match: "k" "w" with
          InjL "args" =>
            let: "x" := Fst "args" in
            let: "k" := Snd "args" in
            "k" (do: "x")
        | InjR "y" =>
            "y"
        end
      in
      InjL ("x", "k"))%V
  | return (λ: "y",
      InjR "y")%V
  end
)%V.

Definition shallow_try_with : val := (λ: "tk" "h" "r",
  match: eff_or_ret "tk" with
    (* Effect: *) InjL "args" =>
      let: "x" := Fst "args" in
      let: "k" := Snd "args" in
      "h" "x" "k"
  | (* Return. *) InjR "y" =>
      "r" "y"
  end
)%V.


(* ========================================================================== *)
(** * Specification & Verification. *)

Section correctness.
  Context `{!heapGS Σ}.

  (* ------------------------------------------------------------------------ *)
  (** Correctness of [eff_or_ret]. *)

  Lemma eff_or_ret_spec E Ψ Φ (tk : val) :
    EWP tk #() @ E <| Ψ |> {{ Φ }} -∗
      EWP eff_or_ret tk @ E {{ y,
        match y with
        | InjRV v =>
            Φ v
        | InjLV (x, k)%V =>
            iEff_car (upcl OS Ψ) x (λ w,
              EWP k w @ E <| Ψ |> {{ Φ }})
        | _ =>
            False
        end%I
      }}.
  Proof.
    unfold eff_or_ret.
    iIntros "Htk". ewp_pure_steps.
    iApply (ewp_deep_try_with with "Htk").
    iLöb as "IH" forall (Ψ).
    rewrite !deep_handler_unfold /deep_handler_pre; iSplit; [|iSplit].
    - iIntros (y) "Hy". by ewp_pure_steps.
    - iIntros (x k) "HΨ". ewp_pure_steps.
      iApply (@monotonic_prot _ (upcl OS Ψ) with "[] HΨ").
      iIntros (w) "Hk". ewp_pure_steps.
      ewp_bind_rule. simpl.
      iSpecialize ("IH" $! Ψ). iSpecialize ("Hk" with "IH").
      iApply ewp_os_prot_mono. { by iApply iEff_le_bottom. }
      iApply (ewp_mono with "Hk").
      iIntros (w') "HΨ".
      case w'; try naive_solver.
      + intros args. case args; try naive_solver.
        iIntros (v' k'). iModIntro. ewp_pure_steps.
        by iApply ewp_do_os.
      + intros y. iModIntro. by ewp_pure_steps.
    - iIntros (??) "HFalse". by rewrite upcl_bottom.
  Qed.


  (* ------------------------------------------------------------------------ *)
  (** Correctness of [shallow_try_with]. *)

  Lemma ewp_shallow_try_with E Ψ Ψ' Φ Φ' (e : expr) (h r : val) :
    EWP e @ E <| Ψ |> {{ Φ }} -∗
      shallow_handler E Ψ ⊥ Φ h r Ψ' ⊥ Φ' -∗
        EWP (shallow_try_with (λ: <>, e)%V h r) @ E <| Ψ' |> {{ Φ' }}.
   Proof.
     unfold shallow_try_with.
     iIntros "He Hhandler". ewp_pure_steps.
     ewp_bind_rule. simpl.
     iApply (ewp_mono with "[He]").
     - iApply ewp_os_prot_mono. { by iApply iEff_le_bottom. }
       iApply eff_or_ret_spec. ewp_pure_steps. by iApply "He".
     - iIntros (pack) "Hpack". case pack; try naive_solver.
       + iIntros (args) "!>"; case args; try naive_solver.
         intros v' k. simpl.
         ewp_pure_steps.
         iDestruct "Hhandler" as "[_ [Hh _]]".
         by iApply "Hh".
       + iIntros (y) "!>". ewp_pure_steps.
         by iApply "Hhandler".
  Qed.

End correctness.
