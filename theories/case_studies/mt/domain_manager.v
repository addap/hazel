
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl excl_auth gset gmap agree csum frac excl.
From iris.base_logic Require Import invariants.
From iris.base_logic.lib Require Import iprop wsat saved_prop.
From program_logic Require Import reasoning_rules.

From case_studies.eio Require Import eio.
From case_studies.mt Require Import spawn.


Definition spawn_scheduler : val :=
  (λ: "f",
    let: "new_scheduler" := (λ: <>, run "f") in
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

Lemma spawn_scheduler_spec (Q : val -> iProp Σ) (f: val) :
  promiseInv -∗ (∀ δ, EWP (f #()) <| Coop δ |> {{ _, True }}) -∗
    EWP (spawn_scheduler f) {{ _, True }}.
Proof.
  iIntros "HInv Hf". rewrite /spawn_scheduler.
  ewp_pure_steps.
  ewp_bind_rule. simpl.
  iApply (ewp_mono with "[HInv Hf]").
  iApply (spawn_spec N with "[HInv Hf]").
  { ewp_pure_steps. 
    iApply (ewp_run f (λ _, True)%I with "[HInv Hf]"). iFrame.
    iIntros (δ) "Hctx".
    iSpecialize ("Hf" $! δ).
    (* a.d. TODO remove the stupid box true *)
    iApply (ewp_mono with "Hf"). iIntros (_) "_ !>". by iFrame. }
  iIntros (v) "(% & -> & Hjoin) !>".
  ewp_pure_steps.
  iApply (join_spec with "Hjoin").
Qed.

End proof.