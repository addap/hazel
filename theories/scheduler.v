(* scheduler.v

   Verification of a asynchronous computation library implementation
   that uses effects and handlers.
*)

From stdpp               Require Import list.
From iris.proofmode      Require Import base tactics classes.
From iris.algebra        Require Import excl_auth gset gmap agree.
From iris.base_logic.lib Require Import iprop wsat invariants.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation weakestpre deep_handler
                                        list_lib queue_lib.


(* ************************************************************************** *)
(** Camera setup. *)

(* The first camera is required for the definition of [running_auth]
   and [running_frang] while the second is for the definition of
   [is_promise], [promise_inv] and [ready]. *)

Class promiseG Σ := {
  promise_mapG :> inG Σ (authR (gmapUR
                               (loc * gname)
                               (agreeR (laterO (val -d> (iPrePropO Σ))))));
  runningG :> inG Σ (excl_authR boolO);
}.

Definition promiseΣ := #[
  GFunctor (authRF (gmapURF (loc * gname) (agreeRF (laterOF (valO -d> idOF)))));
  GFunctor (excl_authR boolO)
].

Instance subG_promiseΣ {Σ} : subG promiseΣ Σ → promiseG Σ.
Proof. solve_inG. Qed.


Section scheduler.
Context `{!heapG Σ, !promiseG Σ}.

(* ************************************************************************** *)
(** Data structures. *)

Context {HList: ListLib Σ} {HQueue: QueueLib Σ}.


(* ************************************************************************** *)
(** Protocols. *)

(* [is_promise p Φ] is the persistent proposition given to a thread after
   an [async] effect. Any thread possesing this proposition can reclaim a
   value [v] satisfying [□ Φ v]. *)

Context (δ : gname).

Definition promise_unfold (Φ : val → iProp Σ) :
  agree (later (discrete_fun (λ (_ : val), iPrePropO Σ))) :=
  to_agree (Next (λ v, iProp_unfold (Φ v))).

Definition is_promise p Φ := (∃ γ, own δ (◯ {[ (p, γ) := promise_unfold Φ ]}))%I.

Global Instance is_promise_persistent p Φ : Persistent (is_promise p Φ).
Proof. rewrite /ownI. apply _. Qed.

(*  Effects markers. *)

Definition async : val → val := InjLV.
Definition await : val → val := InjRV.

(* [Ψ_conc] is the protocol for concurrency effects (async and await).
   It is defined as the fixpoint of [Ψ_conc_pre]. *)

Definition Ψ_conc_pre : iEff Σ → iEff Σ := (λ Ψ,
    (async #> (>> e Φ >> !  (e)       {{ ▷ EWP e #() <| Ψ |> {{ v, □ Φ v }} }};
               << p   << ? #(p : loc) {{ is_promise p Φ                     }}))
      <+>
    (await #> (>> p Φ >> ! #(p : loc) {{ is_promise p Φ }};
               << v   << ?  (v)       {{ □ Φ v          }})))%ieff.


Local Instance Ψ_conc_pre_contractive : Contractive (Ψ_conc_pre).
Proof. rewrite /Ψ_conc_pre=> n Ψ Ψ' HΨ.
       by repeat (apply ewp_ne||apply iEffPre_base_ne||f_contractive||f_equiv).
Qed.
Definition Ψ_conc_def : iEff Σ := fixpoint (Ψ_conc_pre).
Definition Ψ_conc_aux : seal Ψ_conc_def. Proof. by eexists. Qed.
Definition Ψ_conc := Ψ_conc_aux.(unseal).
Definition Ψ_conc_eq : Ψ_conc = Ψ_conc_def := Ψ_conc_aux.(seal_eq).
Global Lemma Ψ_conc_unfold : Ψ_conc ≡ Ψ_conc_pre (Ψ_conc).
Proof. rewrite Ψ_conc_eq /Ψ_conc_def.
       by apply (fixpoint_unfold (Ψ_conc_pre)).
Qed.

(* Properties of the protocol [Ψ_conc]. *)

Section Ψ_conc.

  Definition Ψ_async : iEff Σ :=
    (async #> (>> e Φ >> !  (e)       {{ ▷ EWP e #() <|Ψ_conc|> {{v, □ Φ v}} }};
               << p   << ? #(p : loc) {{ is_promise p Φ                      }})).
  Definition Ψ_await : iEff Σ :=
    (await #> (>> p Φ >> ! #(p : loc) {{ is_promise p Φ }};
               << v   << ?   v        {{ □ Φ v          }})).

  Lemma Ψ_conc_eq_sum : (Ψ_conc ≡ Ψ_async <+> Ψ_await)%ieff.
  Proof. by rewrite Ψ_conc_unfold. Qed.

  Lemma Ψ_conc_agreement v Φ' :
    protocol_agreement v Ψ_conc Φ' ⊣⊢ ((protocol_agreement v Ψ_async Φ') ∨
                                       (protocol_agreement v Ψ_await Φ')).
  Proof.
    rewrite Ψ_conc_eq_sum. iSplit; iIntros "Hprot_agr".
    - iDestruct (protocol_agreement_sum_elim with "Hprot_agr") as "[H|H]"; by eauto.
    - iDestruct "Hprot_agr" as "[H|H]"; [
      by iApply protocol_agreement_sum_intro_l |
      by iApply protocol_agreement_sum_intro_r ].
  Qed.
  Lemma Ψ_async_agreement v Φ' : protocol_agreement v Ψ_async Φ' ≡
    (∃ e Φ, ⌜ v = async e ⌝ ∗ (▷ EWP e #() <| Ψ_conc |> {{ v, □ Φ v }}) ∗
          (∀ (p : loc), is_promise p Φ -∗ Φ' #p))%I.
  Proof.
    rewrite /Ψ_async (iEff_marker_tele' [tele _ _] [tele _]).
    rewrite (protocol_agreement_tele' [tele _ _] [tele _]). by auto.
  Qed.
  Lemma Ψ_await_agreement v Φ' : protocol_agreement v Ψ_await Φ' ≡
    (∃ (p : loc) Φ, ⌜ v = await #p ⌝ ∗ is_promise p Φ ∗
        (∀ v, □ Φ v -∗ Φ' v))%I.
  Proof.
    rewrite /Ψ_await (iEff_marker_tele' [tele _ _] [tele _]) //=.
    rewrite (protocol_agreement_tele' [tele _ _] [tele _]). by auto.
  Qed.

End Ψ_conc.

(* Properties of [promise_unfold] and [is_promise]. *)

Section promise_unfold.

  Lemma promise_lookup (S : gmap (loc * gname) (val → iProp Σ)) γ p Φ :
    own δ (● (promise_unfold <$> S : gmap _ _)) ∗
    own δ (◯ {[(p, γ) := promise_unfold Φ]}) ⊢
    ∃ Ψ, ⌜ S !! (p, γ) = Some Ψ ⌝ ∗ (promise_unfold Ψ ≡ promise_unfold Φ).
  Proof.
    rewrite -own_op own_valid auth_both_validI /=.
    iIntros "[_ [#HS #HvS]]". iDestruct "HS" as (S') "HS".
    rewrite gmap_equivI gmap_validI.
    iSpecialize ("HS" $! (p, γ)). iSpecialize ("HvS" $! (p, γ)).
    rewrite lookup_fmap lookup_op lookup_singleton.
    rewrite option_equivI.
    case: (S  !! (p, γ))=> [Ψ|] /=; [|
    case: (S' !! (p, γ))=> [Ψ'|] /=; by iExFalso].
    iExists Ψ. iSplit; first done.
    case: (S' !! (p, γ))=> [Ψ'|] //=.
    iRewrite "HS" in "HvS". rewrite uPred.option_validI agree_validI.
    iRewrite -"HvS" in "HS". by rewrite agree_idemp.
  Qed.

  Lemma promise_unfold_equiv (Ψ Φ : val → iProp Σ) :
    promise_unfold Ψ ≡ promise_unfold Φ -∗ ▷ (∀ v, Ψ v ≡ Φ v : iProp Σ).
  Proof.
    rewrite /promise_unfold.
    rewrite agree_equivI. iIntros "Heq". iNext. iIntros (v).
    iDestruct (discrete_fun_equivI with "Heq") as "Heq".
    iSpecialize ("Heq" $! v).
    by iApply iProp_unfold_equivI.  
  Qed.

End promise_unfold.


(* ************************************************************************** *)
(** Proof Invariants. *)

Definition running_auth γ (b : bool) := own γ (●E b).
Definition running_frag γ (b : bool) := own γ (◯E b).

(* Properties of [running_auth] and [running_frag]. *)

Section running.

  Lemma running_auth_twice γ b b' : (running_auth γ b ∗ running_auth γ b') ⊢ False.
  Proof.
    rewrite /running_auth -own_op own_valid. iIntros "#H".
    iAssert (⌜ Excl' b = Excl' b' ⌝)%I as "%"; iRevert "H".
    { iIntros (H). iPureIntro. by apply (auth_auth_frac_op_invL _ _ _ _ H). }
    inversion H. rewrite -auth_auth_frac_op auth_validI. by iIntros "#[% _]".
  Qed.
  Lemma running_frag_twice γ b b' : running_frag γ b ∗ running_frag γ b' ⊢ False.
  Proof.
    rewrite /running_frag -own_op own_valid.
    iIntros (H). by destruct (excl_auth_frag_valid_op_1_l _ _ H).
  Qed.
  Lemma running_agree γ b b' : ⊢ running_auth γ b ∗ running_frag γ b' → ⌜ b = b' ⌝.
  Proof. iIntros "[H● H◯]". by iDestruct (own_valid_2 with "H● H◯") as %?%excl_auth_agreeL. Qed.
  Lemma running_agree' γ b b' : b ≠ b' → running_auth γ b -∗ running_frag γ b' -∗ False.
  Proof.
    iIntros (Hneq) "H● H◯".
    by iDestruct (running_agree γ b b' with "[H● H◯]") as "->"; iFrame.
  Qed.
  Lemma running_upd γ b1 b1' b2 : 
    running_auth γ b1 -∗ running_frag γ b1' ==∗ running_auth γ b2  ∗ running_frag γ b2.
  Proof.
    iIntros "H● H◯".
    iMod (own_update_2 _ _ _ (●E b2 ⋅ ◯E (b2 : ofe_car boolO)) with "H● H◯") as "[$$]".
    { by apply excl_auth_update. } { done. }
  Qed.

End running.

(* [promise_inv] is the main proof invariant. It asserts the existence of a
   set of promises, each of which has either already been fulfilled or not.
   If not, a number of threads might be waiting for this event to happen.

   [ready] is the specification satisfied by paused threads.
*)

(* [mut_def] defines [promise_inv] and [ready] by mutual recursion. *)

Definition mut_def_pre :
  (val -d> (() + (val -d> iPropO Σ) * val) -d> iPropO Σ) →
  (val -d> (() + (val -d> iPropO Σ) * val) -d> iPropO Σ)
  := λ mut_def q choice,
  let promise_inv := mut_def q (inl ()) in
  let ready k := mut_def q (inr ((λ v, ⌜ v = #() ⌝)%I, k)) in
  match choice with
  | inr (Φ, k) =>
     ∀ (v : val), □ Φ v -∗
       ▷ promise_inv -∗
         ▷ (∃ (n : nat), is_queue q ready n) -∗
           EWP (k : val) v {{ _, True }}
  | inl () =>
     ∃ (S : gmap (loc * gname) (val → iProp Σ)),
     own δ (● (promise_unfold <$> S : gmap _ _)) ∗
     [∗ map] key ↦ Φ ∈ S,
     match key with (p, γ) =>
       ∃ b, running_auth γ b ∗ 
       if b then
          ∃ l ks, p ↦ InjRV l ∗ is_list l ks ∗
          [∗ list] k ∈ ks, ∀ (v : val), □ Φ v -∗
            ▷ promise_inv -∗
              ▷ (∃ (n : nat), is_queue q ready n) -∗
                EWP (k : val) v {{ _, True }}
       else
          ∃ v, p ↦ InjLV v ∗ □ Φ v
     end
  end%I.

Local Instance mut_def_inv_pre_contractive : Contractive mut_def_pre.
Proof.
  rewrite /mut_def_pre=> n mut_def_inv mut_def_inv' HW q choice.
  repeat (f_contractive || apply is_queue_ne || f_equiv);
  try apply HW; try done; try (intros=>?; apply HW).
Qed.
Definition mut_def_def := fixpoint mut_def_pre.
Definition mut_def_aux : seal mut_def_def. Proof. by eexists. Qed.
Definition mut_def := mut_def_aux.(unseal).
Definition mut_def_eq : mut_def = mut_def_def :=
  mut_def_aux.(seal_eq).
Global Lemma mut_def_unfold q choice :
  mut_def q choice ⊣⊢ mut_def_pre mut_def q choice.
Proof. rewrite mut_def_eq /mut_def_def.
       apply (fixpoint_unfold mut_def_pre).
Qed.
Global Instance mut_def_ne n :
  Proper ((dist n) ==> (dist n) ==> (dist n)) mut_def.
Proof.
  induction (lt_wf n) as [n _ IH]=> q q' Hq ready ready' Hready.
  inversion Hq. rewrite !mut_def_unfold /mut_def_pre.
  repeat (f_contractive || apply mut_def_ne || apply is_queue_ne
         ||    apply IH || f_equiv
         || case x1 as ()         || case x2 as ()
         || case y1 as (y11, y12) || case y2 as (y21, y22) ).
  apply H0. apply H1.
Qed.
Global Instance mut_def_proper : Proper ((≡) ==> (≡) ==> (≡)) mut_def.
Proof. intros ??????. apply equiv_dist=>n.
       by apply mut_def_ne; apply equiv_dist.
Qed.

Definition promise_inv : val -d> iPropO Σ := λ q, mut_def q (inl ()).
Definition ready : val -d> (val -d> iPropO Σ) -d> val -d> iPropO Σ :=
  λ q Φ k, mut_def q (inr (Φ, k)).

Global Instance ready_ne n : Proper ((dist n) ==> (dist n) ==> (dist n)) ready.
Proof. by solve_proper. Qed.
Global Instance ready_proper : Proper ((≡) ==> (≡) ==> (≡)) ready.
Proof. by solve_proper. Qed.
Lemma ready_unfold q Φ k : ready q Φ k ⊣⊢
  ∀ (v : val), □ Φ v -∗ ▷ promise_inv q -∗
    ▷ (∃ (n : nat), is_queue q (ready q (λ v, ⌜ v = #() ⌝)) n) -∗
      EWP k v {{ _, True }}.
Proof. by rewrite /ready /promise_inv mut_def_unfold /mut_def_pre. Qed.

Global Instance promise_inv_ne n : Proper ((dist n) ==> (dist n)) promise_inv.
Proof. by solve_proper. Qed.
Global Instance promise_inv_proper : Proper ((≡) ==> (≡)) promise_inv.
Proof. by solve_proper. Qed.
Lemma promise_inv_unfold q : promise_inv q ⊣⊢ 
  ∃ (S : gmap (loc * gname) (val → iProp Σ)),
  own δ (● (promise_unfold <$> S : gmap _ _)) ∗
  [∗ map] key ↦ Φ ∈ S,
  match key with (p, γ) =>
    ∃ b, running_auth γ b ∗ 
    if b then
       ∃ l ks, p ↦ InjRV l ∗ is_list l ks ∗ [∗ list] k ∈ ks, ready q Φ k
    else
       ∃ v, p ↦ InjLV v ∗ □ Φ v
  end.
Proof.
  rewrite /promise_inv /ready mut_def_unfold /mut_def_pre.
  repeat f_equiv. fold (ready q a1 a4). by rewrite ready_unfold.
Qed.

(* Properties of [promise_inv]. *)

Section promise_inv.
  Context (q : val).

  Definition points_to p γ Φ : iProp Σ :=
    ∃ b, running_auth γ b ∗ 
    if b then
       ∃ l ks, p ↦ InjRV l ∗ is_list l ks ∗ [∗ list] k ∈ ks, ready q Φ k
    else
       ∃ v, p ↦ InjLV v ∗ □ Φ v.

  Lemma promise_alloc Φ :
    ⊢ EWP ref (InjR (list_nil #())) {{ p',
        ∃ (p : loc) γ, ⌜ p' = #p ⌝ ∗ running_frag γ true ∗ points_to p γ Φ }}.
  Proof.
    iApply (ewp_bind (ConsCtx AllocCtx (ConsCtx InjRCtx EmptyCtx))). done.
    iApply ewp_mono; [|iApply list_nil_spec].
    iIntros (l) "Hlist". iModIntro.
    iApply (Ectxi_ewp_bind AllocCtx). done.
    iApply ewp_pure_step. apply pure_prim_step_InjR.
    iApply ewp_value. simpl.
    iApply ewp_mono'. { by iApply (ewp_alloc _ (InjRV l)). }
    iIntros (v) "Hp". iDestruct "Hp" as (p) "[-> Hp]".
    iMod (own_alloc (●E true ⋅ ◯E true)) as (γ) "[Hauth Hfrag]".
    - by apply excl_auth_valid.
    - iModIntro. iExists p, γ. iFrame. iSplit; first auto.
      iExists true. iFrame. iExists l, []. by iFrame.
  Qed.

  Lemma promise_upd p γ Φ :
    promise_inv q ∗ points_to p γ Φ ==∗
    promise_inv q ∗ own δ (◯ {[ (p, γ) := promise_unfold Φ ]}).
  Proof.
    iIntros "[Hpromise_inv Hpoints_to]". rewrite {1}promise_inv_unfold.
    iDestruct "Hpromise_inv" as (S) "[HS Hinv]".
    destruct (S !! (p, γ)) as [Ψ|] eqn:Heq.
    - rewrite (big_opM_delete _ _ _ _ Heq).
      iDestruct "Hinv" as "[Hpoints_to' _]".
      iDestruct "Hpoints_to'" as (b') "[Hrunning' _]".
      iDestruct "Hpoints_to"  as (b)  "[Hrunning  _]".
      by iDestruct (running_auth_twice with "[Hrunning' Hrunning]") as "H"; iFrame.
    - iMod (own_update with "HS") as "[HS HiP]".
      { apply (@auth_update_alloc (gmapUR _ _) (promise_unfold <$> S)).
        apply (alloc_singleton_local_update _ (p, γ) (promise_unfold Φ)).
        by rewrite /= lookup_fmap Heq. done. }
      iModIntro. iFrame.
      rewrite promise_inv_unfold. iExists (<[(p, γ):= Φ]> S).
      rewrite /= fmap_insert. iFrame.
      rewrite big_opM_insert. iFrame. done.
  Qed.

  Lemma promise_agree p γ Φ :
    promise_inv q ∗
    own δ (◯ {[(p, γ) := promise_unfold Φ]}) -∗
    (∃ S, own δ (● (promise_unfold <$> S : gmap _ _)) ∗
      ([∗ map] key ↦ Φ ∈ delete (p, γ) S,
          match key with (p, γ) => points_to p γ Φ end) ∗
        (∃ Ψ, ⌜ S !! (p, γ) = Some Ψ ⌝ ∗ points_to p γ Ψ ∗
          (promise_unfold Ψ ≡ promise_unfold Φ))).
  Proof.
    iIntros "[Hpromise_inv Hpoints_to]". rewrite promise_inv_unfold.
    iDestruct "Hpromise_inv" as (S) "[HS Hinv]".
    iDestruct (promise_lookup S γ p Φ with "[$]") as (Ψ Hlookup) "#Heq".
    iDestruct (big_sepM_delete _ _ (p, γ) with "Hinv") as "[Hpromise_inv Hinv]".
    eauto. iExists S. iFrame. iExists Ψ. iFrame. by iSplit; first auto.
  Qed.

End promise_inv.


(* ************************************************************************** *)
(** Verification of the Library. *)

Lemma ewp_async (e : val) Φ :
  EWP e #() <| Ψ_conc |> {{ v, □ Φ v }} ⊢
    EWP do: (async e) <| Ψ_conc |>
      {{ p', ∃ (p : loc), ⌜ p' = #p ⌝ ∗ is_promise p Φ }}.
Proof.
  iIntros "He".
  iApply ewp_pure_step. apply pure_prim_step_do.
  iApply ewp_eff. rewrite Ψ_conc_agreement Ψ_async_agreement.
  iLeft. iExists e, Φ. iSplit; [done|]. iFrame.
  iIntros (p) "Hp". iApply ewp_value. iExists p. by iFrame.
Qed.

Lemma ewp_await (p : loc) Φ :
  is_promise p Φ ⊢ EWP do: (await #p) <| Ψ_conc |> {{ v, □ Φ v }}.
Proof.
  iIntros "Hp".
  iApply ewp_pure_step. apply pure_prim_step_do.
  iApply ewp_eff. rewrite Ψ_conc_agreement Ψ_await_agreement.
  iRight. iExists p, Φ. iSplit; [done|]. iFrame.
  iIntros (v) "#HΦ". by iApply ewp_value.
Qed.

Definition run : val := λ: "main",
  let: "q" := queue_create #() in

  let: "next" := λ: <>,
    if: queue_empty "q" then #() else (queue_pop "q") #()
  in

  let: "fulfill" := rec: "fulfill" "p" "e" :=
    try: "e" #() with
      effect (λ: "v" "k",
        match: "v" with
        (* Async: *)
          InjL "e" =>
            let: "p" := ref (InjR (list_nil #())) in
            queue_push "q" (λ: <>, "k" "p");;
            "fulfill" "p" "e"
        (* Await: *)
        | InjR "p" =>
            match: Load "p" with
              InjL "v"  => "k" "v"
            | InjR "ks" =>
                "p" <- InjR (list_cons "k" "ks");;
                "next" #()
            end
        end)
    | return (λ: "v",
        match: Load "p" with InjL <> => #() | InjR "ks" =>
          list_iter (λ: "k", queue_push "q" (λ: <>, "k" "v")) "ks";;
          "p" <- InjL "v";;
          "next" #()
        end)
    end
  in

  "fulfill" (ref (InjR (list_nil #()))) "main".

Lemma run_spec' (main : val) Φ :
  (∀ q, promise_inv q) -∗
    EWP main #() <| Ψ_conc |> {{ v, □ Φ v }} -∗
      EWP run main {{ _, True }}.
Proof.
  iIntros "Hpromise_inv Hmain".
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_strong_mono; first done; [
  iApply queue_create_spec | iApply iEff_le_refl |].
  iIntros (q) "Hq".
  iSpecialize ("Hq" $! (ready q (λ v, ⌜ v = #() ⌝)%I)).
  iSpecialize ("Hpromise_inv" $! q).

  (* ************************************************************** *)
  (** Verification of [next]. *)

  (* Specification. *)
  iAssert (∀ q,
    □ (▷ promise_inv q -∗
         ▷ (∃ n, is_queue q (ready q (λ v, ⌜ v = #() ⌝)%I) n) -∗
           EWP
             (λ: <>, if: queue_empty q then #() else queue_pop q #())%V #()
           {{ _, True }}))%I
  as "#next_spec".

  (* Proof. *)
  { iIntros (q'). iModIntro. iIntros "Hpromise_inv Hq".
    iApply ewp_pure_step'. apply pure_prim_step_beta. simpl. iNext.
    iApply (Ectxi_ewp_bind (IfCtx _ _)). done.
    iDestruct "Hq" as (n) "Hq".
    iApply (ewp_mono' with "[Hq]"); [
    iApply (queue_empty_spec with "Hq") |].
    simpl. case n.
    - iIntros (b') "[Hq ->]".
      iApply ewp_pure_step. apply pure_prim_step_if_true.
      iApply ewp_value. simpl. by iFrame.
    - iIntros (m b') "[Hq ->]".
      iApply ewp_pure_step. apply pure_prim_step_if_false.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply (ewp_mono' with "[Hq]");  [
      iApply (queue_pop_spec with "Hq")|].
      simpl. iModIntro. iIntros (k) "[Hq Hk]".
      rewrite ready_unfold.
      iApply (ewp_mono' with "[Hk Hpromise_inv Hq]").
      { iApply ("Hk" $! #() with "[//] Hpromise_inv"). iExists m. by iFrame. }
      { by auto. }
  }
  (* ************************************************************** *)

  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppRCtx _) EmptyCtx))). done.
  iApply ewp_mono'; [
  iApply (promise_alloc q Φ) |]. simpl.
  iModIntro. iIntros (v) "H".
  iDestruct "H" as (p γ) "(-> & Hrunning & Hpoints_to)".
  iMod (promise_upd with "[$]") as "[Hpromise_inv Hp]".
  iAssert (∃ (n : nat), is_queue q (ready q (λ v, ⌜ v = #() ⌝)) n)%I
  with "[Hq]" as "Hq". { by iExists 0%nat. }
  iModIntro.

  (* ************************************************************** *)
  (** Verification of [fulfill]. *)

  (* Step 1 - Löb induction. *)
  iLöb as "IH" forall (main q p γ Φ).

  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.
  iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppRCtx _) EmptyCtx))). done.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value. simpl.

  (* Step 2 - Reasoning rule for deep handlers. *)
  iApply (ewp_deep_try_with with "Hmain").

  (* Step 3 - Proof of [is_deep_hanlder] judgment. *)
  iAssert (▷ ∃ (n : nat), is_queue q (ready q (λ v, ⌜ v = #() ⌝)) n)%I
  with "Hq" as "Hq".
  iLöb as "IH_handler" forall (q p γ Φ).
  rewrite deep_handler_unfold.
  iSplit.

  (* Return branch. *)
  - iIntros (v) "#Hv".
    iDestruct (promise_agree q with "[$]") as (S) "(HS & Hinv & H)".
    iDestruct "H" as (Ψ) "(% & Hpoints_to & Heq')".
    rename H into lookup_S.
    iDestruct "Hpoints_to" as (b) "[Hrunning' Hp]".
    iDestruct (running_agree with "[$]") as "%". rewrite H; clear H.
    iDestruct "Hp" as (l ks) "(Hp & Hl & Hks)".
    iPoseProof (promise_unfold_equiv with "Heq'") as "#Heq". iClear "Heq'".
    iNext. iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (CaseCtx _ _)). done.
    iApply (ewp_mono' with "[Hp]"). { by iApply (ewp_load with "Hp"). }
    iIntros (w) "[-> Hp]".
    iApply ewp_pure_step. apply pure_prim_step_case_InjR.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (AppRCtx _)). done.
    iApply (ewp_mono' with "[Hks Hl Hq]").
    { iApply (ewp_bind (ConsCtx (AppLCtx _)
                       (ConsCtx (AppRCtx _) EmptyCtx))). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. simpl.
      iApply ewp_value.
      iApply (list_iter_spec' _
             (λ fs, (∃ (n : nat), is_queue q (ready q (λ v, ⌜ v = #() ⌝)) n) ∗
                    ([∗ list] f ∈ fs, ∀ (v : val), □ Ψ v -∗ ▷ promise_inv q -∗
                       ▷ (∃ (n : nat), is_queue q (ready q (λ v, ⌜ v = #() ⌝)) n) -∗
                         EWP (f : val) v <|⊥|> {{ _, True }}))%I _ _ ks with "[] Hl").
      - iModIntro. iIntros (gs f fs <-) "[Hq Hfs]".
        rewrite big_opL_cons. iDestruct "Hfs" as "[Hf Hfs]".
        iAssert (ready q (λ v, ⌜ v = #() ⌝) (λ: <>, f v)%V)%I with "[Hf]" as "Hready".
        { rewrite ready_unfold. iIntros (w) "-> Hpromise_inv Hq".
          iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
          iApply ("Hf" with "[] Hpromise_inv Hq"). by iRewrite ("Heq" $! v).
        }
        iDestruct "Hq" as (n) "Hq".
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        iApply (Ectxi_ewp_bind (AppRCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value. simpl.
        iApply (ewp_mono' with "[Hq Hready]"). { by iApply (queue_push_spec with "Hq Hready"). }
        iIntros (_) "Hq". iModIntro. by eauto with iFrame.
      - iNext. iFrame. iApply (big_sepL_mono with "Hks"). simpl.
        iIntros (n f) "% Hready". by rewrite ready_unfold.
    }
    iModIntro. iIntros (w) "(_ & Hq & _)".
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (AppRCtx _)). done.
    iApply (Ectxi_ewp_bind (StoreRCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_InjL.
    iApply ewp_value. simpl.
    iApply (ewp_mono' with "[Hp]"). { by iApply (ewp_store with "Hp"). }
    iModIntro. iIntros (u) "Hp".
    iMod (running_upd _ _ _ false with "Hrunning' Hrunning") as "[Hrunning' Hrunning]".
    iAssert (points_to q p γ Ψ) with "[Hp Hrunning']" as "Hpoints_to".
    { iExists false. iFrame. iExists v. iFrame. by iRewrite ("Heq" $! v). }
    iAssert (promise_inv q) with "[HS Hinv Hpoints_to]" as "Hpromise_inv".
    { rewrite promise_inv_unfold. iExists S. iFrame.
      rewrite (big_sepM_delete _ S (p, γ) _ lookup_S). by iFrame. }
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    by iApply ("next_spec" with "Hpromise_inv Hq").

  (* Effect branch. *)
  - iIntros (v k) "Hprot_agr".
    iDestruct (Ψ_conc_agreement with "Hprot_agr") as "[Hasync|Hawait]".

    (* Async. *)
    + iClear "next_spec". rewrite Ψ_async_agreement. 
      iDestruct "Hasync" as (e Φ') "(-> & He & Hk)".
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply ewp_pure_step. apply pure_prim_step_case_InjL.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply ewp_mono'. { by iApply (promise_alloc q Φ'). }
      iNext. iIntros (_p') "Hp'". simpl.
      iDestruct "Hp'" as (p' γ') "(-> & Hrunning' & Hpoints_to)".
      iMod (promise_upd with "[$]") as "[Hpromise_inv #Hp']". iModIntro.
      iSpecialize ("Hk" $! p' with "[Hp']"). { by iExists γ'. }
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step'. apply pure_prim_step_rec.
      iNext. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value. simpl.
      iAssert (ready q (λ v, ⌜ v = #() ⌝) (λ: <>, k #p')%V)%I
      with "[Hk Hrunning Hp]" as "Hready".
      { rewrite ready_unfold. iIntros (w) "-> Hpromise_inv Hq".
        iApply ewp_pure_step'. apply pure_prim_step_beta.
        iNext. iApply "Hk".
        by iApply ("IH_handler" with "Hrunning Hpromise_inv Hp Hq").
      }
      iDestruct "Hq" as (n) "Hq".
      iApply (ewp_mono' with "[Hq Hready]").
      { by iApply (queue_push_spec with "Hq Hready"). }
      iIntros (v) "Hq". iModIntro.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      by iApply ("IH" with "He Hrunning' Hpromise_inv Hp'"); eauto.

    (* Await. *)
    + iClear "IH". rewrite Ψ_await_agreement.
      iDestruct "Hawait" as (p' Φ') "(-> & #His_promise & Hk)".
      iDestruct "His_promise" as (γ') "#His_promise".
      iDestruct (promise_agree with "[Hpromise_inv]") as (S) "(HS & Hinv & H)".
      { by eauto with iFrame. }
      iDestruct "H" as (Ψ) "(% & Hpoints_to & Heq')". rename H into lookup_S.
      iDestruct (promise_unfold_equiv with "Heq'") as "#Heq". iClear "Heq'".
      iDestruct "Hpoints_to" as (b) "[Hrunning' Hp']".
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply ewp_pure_step. apply pure_prim_step_case_InjR.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. simpl.
      iApply ewp_value.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iNext. case b.
      { iDestruct "Hp'" as (l ks) "(Hp' & Hl & Hks)".
        iApply (Ectxi_ewp_bind (CaseCtx _ _)). done.
        iApply (ewp_mono' with "[Hp']"). { by iApply (ewp_load with "Hp'"). }
        iIntros (w) "[-> Hp']". iModIntro. simpl.
        iApply ewp_pure_step. apply pure_prim_step_case_InjR.
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec. simpl.
        iApply ewp_value. simpl.
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        iApply (Ectxi_ewp_bind (AppRCtx _)). done.
        iApply (ewp_bind (ConsCtx (StoreRCtx _)
                         (ConsCtx  InjRCtx EmptyCtx))). done.
        iApply (ewp_mono' with "[Hl]"). { by iApply (list_cons_spec with "Hl"). }
        iIntros (l') "Hl'". iModIntro. simpl.
        iApply (Ectxi_ewp_bind (StoreRCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_InjR.
        iApply ewp_value. simpl.
        iApply (ewp_mono' with "[Hp']"). { by iApply (ewp_store with "Hp'"). }
        iIntros (w) "Hp'".
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec. simpl.
        iApply ewp_value.
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        iAssert (points_to q p' γ' Ψ)
        with "[Hrunning Hp Hrunning' Hks Hl' Hp' Hk]" as "Hpoints_to".
        { iExists true. iFrame. iExists l', (_ :: ks). iFrame.
          rewrite ready_unfold.
          iIntros (v) "#HΨ Hpromise_inv Hq". iRewrite ("Heq" $! v) in "HΨ".
          iSpecialize ("Hk" with "HΨ").
          iApply "Hk". iNext.
          by iApply ("IH_handler" with "Hrunning Hpromise_inv Hp Hq").
        }
        iAssert (promise_inv q)%I with "[HS Hinv Hpoints_to]" as "Hpromise_inv".
        { rewrite promise_inv_unfold. iExists S. iFrame.
          rewrite (big_sepM_delete _ S (p', γ') _ lookup_S). by iFrame.
        }
        by iApply ("next_spec" with "Hpromise_inv Hq").
      }
      { iDestruct "Hp'" as (v) "[Hp' #Hv]".
        iRewrite ("Heq" $! v) in "Hv". iSpecialize("Hk" $! v with "Hv").
        iApply (Ectxi_ewp_bind (CaseCtx _ _)). done.
        iApply (ewp_mono' with "[Hp']"). { by iApply (ewp_load with "Hp'"). }
        iIntros (w) "[-> Hp']". simpl.
        iModIntro. iApply ewp_pure_step. apply pure_prim_step_case_InjL.
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value. simpl.
        iApply ewp_pure_step'. apply pure_prim_step_beta. simpl.
        iNext. iApply "Hk".
        iApply ("IH_handler" with "Hrunning [HS Hinv Hrunning' Hp'] Hp Hq").
        iAssert (points_to q p' γ' Ψ)%I with "[Hrunning' Hp']" as "Hpoints_to".
        { iExists false. iFrame. iExists v. iRewrite ("Heq" $! v). by iFrame. }
        rewrite promise_inv_unfold. iExists S. iFrame.
        rewrite (big_sepM_delete _ S (p', γ') _ lookup_S). by iFrame.
      }
  (* ************************************************************** *)
Qed.

End scheduler.

Section spec.
Context `{!heapG Σ, !promiseG Σ}.

Context {HList: ListLib Σ} {HQueue: QueueLib Σ}.

Lemma promise_inv_alloc : ⊢ |==> ∃ γ, ∀ q, promise_inv γ q.
Proof.
  iIntros. iMod (own_alloc (● (∅ : gmap (loc * gname) _))) as (γI) "HI";
    first by rewrite auth_auth_valid.
  iModIntro. iExists γI. iIntros (q).
  rewrite promise_inv_unfold.
  iExists ∅. rewrite fmap_empty. by iFrame.
Qed.

Lemma run_spec (main : val) : ⊢ |==> ∃ γ,
  EWP main #() <| Ψ_conc γ |> {{ _, True }} -∗
    EWP run main {{ _, True }}.
Proof.
  iMod promise_inv_alloc as (γ) "Hpromise_inv".
  iModIntro. iExists γ. iIntros "Hmain".
  iApply (run_spec' _ _ (λ _, True%I) with "Hpromise_inv").
  iApply (ewp_mono with "Hmain"). by auto.
Qed.

End spec.
