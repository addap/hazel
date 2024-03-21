
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl excl_auth gset gmap agree csum frac excl.
From iris.base_logic Require Import invariants.
From iris.base_logic.lib Require Import iprop wsat saved_prop.
From program_logic Require Import reasoning_rules.

From case_studies.eio Require Import eio.
From case_studies.mt Require Import spawn.


(* Proof-of-concept spawn function that blocks the thread. *)
Definition spawn_scheduler : val := 
  (λ: "init" "f",
    let: "new_scheduler" := (λ: <>, run "init" "f") in
    let: "c" := spawn "new_scheduler" in
    join "c")%V.
      
Section proof.
Context `{!heapGS Σ, !spawnG Σ, !promiseGS Σ, !savedPredG Σ val}.
Context (N : namespace).
(* What would the specification of spawn_scheduler be? 
  Nothing interesting I think since it just wraps run.

  EWP f #() <| Ψ |> {{ Q }}
  ---------------------
  EWP (spawn_scheduler f) <| ⊥ |> {{ Q }}
*)

Lemma spawn_scheduler_spec (I Φ : val -> iProp Σ) (init f: val) :
  promiseInv -∗ I init -∗ (∀ δℓ, EWP (f #()) <| Coop δℓ |> {{ v, □ Φ v }}) -∗
    EWP (spawn_scheduler init f) {{ v, □ Φ v }}.
Proof.
  iIntros "HInv Hinit Hf". rewrite /spawn_scheduler.
  ewp_pure_steps.
  ewp_bind_rule. simpl.
  iApply (ewp_mono with "[HInv Hinit Hf]").
  iApply (spawn_spec N with "[HInv Hinit Hf]").
  { ewp_pure_steps. 
    iApply (ewp_run init f I Φ with "[HInv Hinit Hf]"). iFrame.
    iIntros (δ ℓres) "HfRes".
    iSpecialize ("Hf" $! (δ, ℓres)).
    (* a.d. TODO remove the stupid box true *)
    iApply (ewp_mono with "Hf"). iIntros (?) "HΦ !>". by iFrame. }
  iIntros (v) "(% & -> & Hjoin) !>".
  ewp_pure_steps.
  iApply (join_spec with "Hjoin").
Qed.

End proof.