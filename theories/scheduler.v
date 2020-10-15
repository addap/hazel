From stdpp               Require Import list.
From iris.proofmode      Require Import base tactics classes.
From iris.algebra        Require Import excl_auth gset gmap agree.
From iris.base_logic.lib Require Import iprop wsat invariants.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation weakestpre deep_handler
                                        list_lib queue_lib.

Section scheduler.
Context `{!heapG Σ}.

(**  Effects. *)

(* Effect markers. *)

Definition async : val → val := InjLV.
Definition await : val → val := InjRV.

(** Proof. *)

(* Data structures. *)

Context {HList: ListLib Σ} {HQueue: QueueLib Σ}.

(* Camera setup. We need the first cmra for the definition of [running_auth] and
   [running_frang], and we need the second for the definition of [is_promise]
   and [handler_inv]. *)

Context `{!inG Σ (excl_authR boolO)}.
Context `{!inG Σ (authR (gmapUR
                          (loc * gname)
                          (agreeR (laterO (val -d> (iPrePropO Σ))))))}.

Context (promise_name : gname).

Definition promise_unfold (Φ : val → iProp Σ) :
  agree (later (discrete_fun (λ (_ : val), iPrePropO Σ)))
  :=
  to_agree (Next (λ v, iProp_unfold (Φ v))).

(* [promise_inv γ p Φ] describes the invariant over the promise [p]: it is
   either a reference to a value [v] satisfying [□ Φ v], or a reference to a
   list of threads waiting for such a value [v]. The parameter [W_inv] is used
   to specify threads waiting for the termination of a process associated with
   a given promise. *)

Definition running_auth γ (b : bool) := own γ (●E b).
Definition running_frag γ (b : bool) := own γ (◯E b).
Definition promise_inv γ p
  (W_inv : (val -d> iPropO Σ) -d> (val -d> iPropO Σ))
  (Φ : val -d> iPropO Σ) : iPropO Σ :=
  (∃ b, running_auth γ b ∗ 
    if b then
      (∃ l ks, p ↦ InjRV l ∗ is_list l ks ∗ [∗ list] f ∈ ks, ▷ W_inv Φ f)
    else
      (∃ v, p ↦ InjLV v ∗ □ Φ v))%I.

(* [handler_inv W_inv] is the internal state of the handler. It enforces that
   the set of created promises respect [promise_inv]. *)

Definition handler_inv W_inv :=
  (∃ (S : gmap (loc * gname) (val → iProp Σ)),
    own promise_name (● (promise_unfold <$> S : gmap _ _)) ∗
    [∗ map] key ↦ Φ ∈ S, match key with (p, γ) => promise_inv γ p W_inv Φ end)%I.

(* [is_promise' γ p Φ] is the persistent proposition given to a thread after an
   [async] effect. Any thread possesing this proposition can reclaim a value [v]
   satisfying [□ Φ v]. *)

Definition is_promise' γ p Φ :=
  own promise_name (◯ {[ (p, γ) := promise_unfold Φ ]}).
Definition is_promise p Φ : iProp Σ := ∃ γ, is_promise' γ p Φ.

(* [W_inv] is the specification of wainting threads. *)

Definition W_inv_pre :
  (val -d> (val -d> iPropO Σ) -d> (val -d> iPropO Σ) -d> (val -d> iPropO Σ)) →
  (val -d> (val -d> iPropO Σ) -d> (val -d> iPropO Σ) -d> (val -d> iPropO Σ))
  :=
  (λ W_inv q Ready Φ f,
    ∀ v, handler_inv (W_inv q Ready) -∗ (∃ n, is_queue q Ready n) -∗ □ Φ v -∗
      EWP f v @ ∅ {{ _, True }})%I.

Local Instance W_inv_pre_contractive : Contractive W_inv_pre.
Proof.
  rewrite /W_inv_pre=> n W_inv W_inv' HW q Ready Ψ f.
  rewrite /handler_inv /promise_inv.
  repeat (f_contractive || f_equiv); try apply HW.
Qed.
Definition W_inv_def : 
   val -d> (val -d> iPropO Σ) -d> (val -d> iPropO Σ) -d> (val -d> iPropO Σ)
 :=
  fixpoint W_inv_pre.
Definition W_inv_aux : seal W_inv_def. Proof. by eexists. Qed.
Definition W_inv := W_inv_aux.(unseal).
Definition W_inv_eq : W_inv = W_inv_def := W_inv_aux.(seal_eq).
Global Lemma W_inv_unfold q Ready Φ f :
  W_inv q Ready Φ f ⊣⊢ W_inv_pre W_inv q Ready Φ f.
Proof. rewrite W_inv_eq /W_inv_def. apply (fixpoint_unfold W_inv_pre). Qed.
Global Instance W_inv_ne n :
  Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n)) W_inv.
Proof.
  induction (lt_wf n) as [n _ IH]=> q q' Hq Q Q' HQ Φ Φ' HΦ f f' Hf.
  rewrite !W_inv_unfold /W_inv_pre /handler_inv /promise_inv.
  do 3 f_equiv.
  - do 20 f_equiv. f_contractive.
    apply IH; try lia; eapply dist_le; eauto with lia.
  - destruct Hq. destruct Hf. do 3 f_equiv; [| auto]; apply is_queue_ne; auto.
Qed.
Global Instance W_inv_proper : Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) W_inv.
Proof. intros ????????????. apply equiv_dist=>n. by apply W_inv_ne; apply equiv_dist. Qed.

(* [Ready] is the specification of paused threads that were put in the queue. *)

Definition Ready_pre q : (val -d> iPropO Σ) → (val -d> iPropO Σ)
  :=
  (λ Ready e, handler_inv (W_inv q Ready) -∗ (∃ n, ▷ is_queue q Ready n) -∗
      EWP e #() @ ∅ {{ _, True }})%I.

Local Instance Ready_pre_contractive q : Contractive (Ready_pre q).
Proof.
  rewrite /Ready_pre=> n Ready Ready' HQ e.
  rewrite /handler_inv /promise_inv.
  repeat (f_contractive || apply is_queue_ne || f_equiv); done.
Qed.

Definition Ready_def q : (val -d> iPropO Σ) := fixpoint (Ready_pre q).
Definition Ready_aux : seal Ready_def. Proof. by eexists. Qed.
Definition Ready := Ready_aux.(unseal).
Definition Ready_eq : Ready = Ready_def := Ready_aux.(seal_eq).
Global Lemma Ready_unfold q e : Ready q e ⊣⊢ Ready_pre q (Ready q) e.
Proof. rewrite Ready_eq /Ready_def. apply (fixpoint_unfold (Ready_pre q)). Qed.
Global Instance Ready_ne q n : Proper ((dist n) ==> (dist n)) (Ready q).
Proof. solve_proper. Qed.
Global Instance Ready_proper q : Proper ((≡) ==> (≡)) (Ready q).
Proof. solve_proper. Qed.

(* [Ψ_concurrency] is the protocol for concurrency effects (async and await).
   It is defined as the fixpoint of [Ψ_concurrency_pre]. *)

Definition Ψ_concurrency_pre : iEff Σ → iEff Σ := (λ Ψ,

    (async #> (>> e Φ >> !  (e)       {{ ▷ EWP e #() @ ∅ <| Ψ |> {{ v, □ Φ v }} }};
               << p   << ? #(p : loc) {{ is_promise p Φ                         }}))
      <+>

    (await #> (>> p Φ >> ! #(p : loc) {{ is_promise p Φ }};
               << v   << ?  (v)       {{ □ Φ v          }})))%ieff.


Local Instance Ψ_concurrecy_pre_contractive : Contractive (Ψ_concurrency_pre).
Proof. rewrite /Ψ_concurrency_pre=> n Ψ Ψ' HΨ.
       by repeat (apply ewp_ne||apply iEffPre_base_ne||f_contractive||f_equiv).
Qed.
Definition Ψ_concurrency_def : iEff Σ := fixpoint (Ψ_concurrency_pre).
Definition Ψ_concurrency_aux : seal Ψ_concurrency_def. Proof. by eexists. Qed.
Definition Ψ_concurrency := Ψ_concurrency_aux.(unseal).
Definition Ψ_concurrency_eq : Ψ_concurrency = Ψ_concurrency_def :=
  Ψ_concurrency_aux.(seal_eq).
Global Lemma Ψ_concurrency_unfold : Ψ_concurrency ≡ Ψ_concurrency_pre (Ψ_concurrency).
Proof. rewrite Ψ_concurrency_eq /Ψ_concurrency_def.
       by apply (fixpoint_unfold (Ψ_concurrency_pre)).
Qed.

Definition Ψ_async : iEff Σ :=
  (async #>
    (>> e Φ       >> !  e {{ ▷ EWP e #() @ ∅ <|Ψ_concurrency|> {{v, □ Φ v}} }};
     << (p : loc) << ? #p {{ is_promise p Φ                                 }})).

Definition Ψ_await : iEff Σ :=
  (await #>
    (>> p Φ >> ! #(p : loc) {{ is_promise p Φ }};
     << v   << ?   v        {{ □ Φ v          }})).

Lemma Ψ_concurrency_eq_sum : (Ψ_concurrency ≡ Ψ_async <+> Ψ_await)%ieff.
Proof. by rewrite Ψ_concurrency_unfold. Qed.

Lemma Ψ_concurrency_agreement E v Φ' :
  protocol_agreement E v Ψ_concurrency Φ' ⊢
    ((protocol_agreement E v Ψ_async Φ') ∨ (protocol_agreement E v Ψ_await Φ')).
Proof.
  iIntros "Hprot_agr". rewrite Ψ_concurrency_eq_sum.
  iDestruct (protocol_agreement_sum_elim with "Hprot_agr") as "[H|H]"; by eauto.
Qed.

Lemma Ψ_async_agreement E v Φ' :
  protocol_agreement E v Ψ_async Φ' ≡
    (|={E,∅}=>
       ∃ e Φ, ⌜ v = async e ⌝ ∗ (▷ EWP e #() @ ∅ <|Ψ_concurrency|> {{v, □ Φ v}}) ∗
          (∀ (p : loc), is_promise p Φ ={∅,E}=∗ Φ' #p))%I.
Proof.
  rewrite /Ψ_async (iEff_marker_tele' [tele _ _] [tele _]).
  rewrite (protocol_agreement_tele' [tele _ _] [tele _]). by auto.
Qed.

Lemma Ψ_await_agreement E v Φ' :
  protocol_agreement E v Ψ_await Φ' ≡
    (|={E,∅}=>
       ∃ (p : loc) Φ, ⌜ v = await #p ⌝ ∗ is_promise p Φ ∗
          (∀ v, □ Φ v ={∅,E}=∗ Φ' v))%I.
Proof.
  rewrite /Ψ_await (iEff_marker_tele' [tele _ _] [tele _]).
  rewrite (protocol_agreement_tele' [tele _ _] [tele _]). by auto.
Qed.

(* Auxiliary lemmas. *)

Local Instance promise_inv_ne γ p q n :
  Proper ((dist n) ==> (dist n)) (promise_inv γ p (W_inv q (Ready q))).
Proof.
  intros ???. rewrite /promise_inv.
  do 8 f_equiv; last eauto. solve_proper.
Qed.

Local Instance promise_inv_proper γ p q :
  Proper ((≡) ==> (≡)) (promise_inv γ p (W_inv q (Ready q))).
Proof. intros ???. apply equiv_dist=>n. by apply promise_inv_ne, equiv_dist. Qed.

Lemma running_auth_twice γ b b' : running_auth γ b ∗ running_auth γ b' ⊢ False.
Proof.
  rewrite /running_auth. rewrite -own_op own_valid.
  case (bool_dec b b').
  + intros ->. rewrite -auth_auth_frac_op auth_validI. by iIntros ([? _]).
  + iIntros (Heq' Hvalid).
    cut (b = b'); [done|].
    cut (Some (Excl b) = Some (Excl b')). naive_solver.
    by apply (auth_auth_frac_op_invL _ _ _ _ Hvalid).
Qed.

Lemma running_frag_twice γ b b' : running_frag γ b ∗ running_frag γ b' ⊢ False.
Proof.
  rewrite /running_frag. rewrite -own_op own_valid.
  iIntros (Hvalid). by destruct (excl_auth_frag_valid_op_1_l _ _ Hvalid).
Qed.

Lemma running_agree γ b b' : ⊢ running_auth γ b ∗ running_frag γ b' → ⌜ b = b' ⌝.
Proof.
  iIntros "[H● H◯]". by iDestruct (own_valid_2 with "H● H◯") as %?%excl_auth_agreeL.
Qed.

Lemma running_agree' γ b b' : 
  b ≠ b' → running_auth γ b -∗ running_frag γ b' -∗ False.
Proof.
  intros Hneq. iIntros "Hauth Hfrag".
  iPoseProof (running_agree with "[Hauth Hfrag]") as "%". by iFrame. done.
Qed.

Lemma running_upd γ b1 b2 b : 
  running_auth γ b1 -∗ running_frag γ b2 ==∗
  running_auth γ b   ∗ running_frag γ b.
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (●E (b : ofe_car boolO) ⋅ ◯E (b : ofe_car boolO))
    with "Hγ● Hγ◯") as "[$$]".
  { by apply excl_auth_update. }
  done.
Qed.

Instance is_promise_persistent γ p Φ : Persistent (is_promise' γ p Φ).
Proof. rewrite /ownI. apply _. Qed.

Lemma promise_alloc E Φ W_inv :
  ⊢ EWP ref (InjR (list_nil #())) @ E
      {{ v, ∃ (p : loc) γ, ⌜ v = #p ⌝ ∗ running_frag γ true ∗ promise_inv γ p Φ W_inv }}.
Proof.
  iApply (ewp_bind (ConsCtx AllocCtx (ConsCtx InjRCtx EmptyCtx))). done.
  iApply ewp_mono; [|iApply list_nil_spec].
  iIntros (l) "Hlist". iModIntro.
  iApply (Ectxi_ewp_bind AllocCtx). done.
  iApply ewp_pure_step. apply pure_prim_step_InjR.
  iApply ewp_value. simpl.
  iApply ewp_mono'. { by iApply (ewp_alloc E (InjRV l)). }
  iIntros (v) "Hp". iDestruct "Hp" as (p) "[-> Hp]".
  iMod (own_alloc (●E true ⋅ ◯E true)) as (γ) "[Hauth Hfrag]".
  - by apply excl_auth_valid.
  - iModIntro. iExists p, γ. iFrame. iSplit; first auto.
    iExists true. iFrame. iExists l, []. by iFrame.
Qed.

Lemma promise_upd γ p W_inv Φ :
  handler_inv W_inv ∗ promise_inv γ p W_inv Φ ==∗
  handler_inv W_inv ∗ is_promise' γ p Φ.
Proof.
  iIntros "[Hhandler_inv Hpromise]".
  iDestruct "Hhandler_inv" as (S) "[HS Hinv]".
  destruct (S !! (p, γ)) as [Ψ|] eqn:Heq.
  - rewrite (big_opM_delete _ _ _ _ Heq).
    iDestruct "Hinv" as "[Hpromise' _]".
    iDestruct "Hpromise'" as (b') "[Hrunning' _]".
    iDestruct "Hpromise"  as (b)  "[Hrunning  _]".
    by iDestruct (running_auth_twice with "[Hrunning' Hrunning]") as "H"; iFrame.
  - iMod (own_update with "HS") as "[HS HiP]".
    { apply (@auth_update_alloc (gmapUR _ _) (promise_unfold <$> S)).
      apply (alloc_singleton_local_update _ (p, γ) (promise_unfold Φ)).
      by rewrite /= lookup_fmap Heq. done. }
    iModIntro. iFrame. iExists (<[(p, γ):= Φ]> S).
    rewrite /= fmap_insert. iFrame.
    rewrite big_opM_insert. iFrame. done.
Qed.

Lemma promise_lookup (S : gmap (loc * gname) (val → iProp Σ)) γ p Φ :
  own promise_name (● (promise_unfold <$> S : gmap _ _)) ∗
  own promise_name (◯ {[(p, γ) := promise_unfold Φ]}) ⊢
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

Lemma promise_agree γ p W_inv Φ :
  handler_inv W_inv ∗ is_promise' γ p Φ -∗
  (∃ S, own promise_name (● (promise_unfold <$> S : gmap _ _)) ∗
    ([∗ map] key ↦ Φ ∈ delete (p, γ) S,
        match key with (p, γ) => promise_inv γ p W_inv Φ end) ∗
      (∃ Ψ, ⌜ S !! (p, γ) = Some Ψ ⌝ ∗ promise_inv γ p W_inv Ψ ∗
        (promise_unfold Ψ ≡ promise_unfold Φ))).
Proof.
  iIntros "[Hhandler_inv Hpromise]".
  iDestruct "Hhandler_inv" as (S) "[HS Hinv]".
  rewrite /is_promise.
  iDestruct (promise_lookup S γ p Φ with "[$]") as (Ψ Hlookup) "#Heq".
  iDestruct (big_sepM_delete _ _ (p, γ) with "Hinv") as "[Hpromise_inv Hinv]".
  eauto. iExists S. iFrame. iExists Ψ. iFrame. by iSplit; first auto.
Qed.

Definition run : val := λ: "main",
  let: "q" := queue_create #() in

  let: "run_next" := λ: <>,
    if: queue_empty "q" then #() else
      (queue_pop "q") #()
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
                "p" <- InjR (list_cons (λ: "x", "k" "x") "ks");;
                "run_next" #()
            end
        end)
    | return (λ: "v",
        match: Load "p" with InjL <> => #() | InjR "ks" =>
          list_iter (λ: "k", queue_push "q" (λ: <>, "k" "v")) "ks";;
          "p" <- InjL "v";;
          "run_next" #()
        end)
    end
  in

  "fulfill" (ref (InjR (list_nil #()))) "main".

Lemma run_spec' (main : val) Φ :
  (∀ W_inv, handler_inv W_inv) -∗
    EWP main #() @ ∅ <| Ψ_concurrency |> {{ v, □ Φ v }} -∗
      EWP run main @ ∅ {{ _, True }}.
Proof.
  iIntros "Hhandler Hmain". unfold run.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_strong_mono; first done; [
  iApply queue_create_spec | iApply iEff_le_refl |].
  iIntros (q) "Hq". iSpecialize ("Hq" $! (Ready q)).
  iSpecialize ("Hhandler" $! (W_inv q (Ready q))).

  (* ************************************************************************ *)
  (** Verification of [run_next]. *)

  (* Specification. *)
  iAssert (□ (∀ n, handler_inv (W_inv q (Ready q)) -∗ is_queue q (Ready q) n -∗
    EWP
      (λ: <>, if: queue_empty q then #() else queue_pop q #())%V #() @ ∅
    {{ _, True }}))%I
  as "#run_next_spec".

  (* Proof. *)
  { iModIntro. iIntros (n) "Hhandler_inv Hq".
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (IfCtx _ _)). done.
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
      rewrite !Ready_unfold /Ready_pre.
      iApply (ewp_mono' with "[Hk Hhandler_inv Hq]").
      { iApply ("Hk" with "Hhandler_inv"). iExists m. by iFrame. }
      { by auto. }
  }
  (* ************************************************************************ *)

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
  iApply (promise_alloc _ (W_inv q (Ready q)) Φ) |]. simpl.
  iModIntro. iIntros (v) "H".
  iDestruct "H" as (p γ) "(-> & Hrunning & Hpromise_inv)".
  iMod (promise_upd with "[$]") as "[Hhandler Hp]".
  iAssert (∃ n, is_queue q (Ready q) n)%I with "[Hq]" as "Hq".
  { by iExists 0%nat. }
  iModIntro.

  (* ************************************************************************ *)
  (** Verification of [fulfill]. *)

  (* Step 1 - Löb induction. *)
  iLöb as "IH" forall (γ p Φ main). iDestruct "Hp" as "#Hp".

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
  iDestruct "Hq" as (n) "Hq".

  (* Step 2 - Reasoning rule for deep handlers. *)
  iApply (ewp_deep_try_with with "Hmain").

  (* Step 3 - Proof of [is_deep_hanlder] judgement. *)
  iAssert (▷ is_queue q (Ready q) n)%I with "Hq" as "Hq".
  iRevert "Hp". iLöb as "IH_handler" forall (n Φ γ p). iIntros "#Hp".
  rewrite deep_handler_unfold.
  iSplit.

  (* Return branch. *)
  - iIntros (v) "#Hv".
    iDestruct (promise_agree with "[$]") as (S) "(HS & Hinv & H)".
    iDestruct "H" as (Ψ) "(% & Hpromise_inv & H)".
    rename H into Hlookup.
    iDestruct (promise_unfold_equiv with "H") as "#Heq". iNext.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iDestruct "Hpromise_inv" as (b) "[Hrunning' Hp_inv]".
    iPoseProof (running_agree with "[$]") as "%". rewrite H. clear H.
    iDestruct "Hp_inv" as (l ks) "(Href & Hl & HW_inv)".
    iApply (Ectxi_ewp_bind (CaseCtx _ _)). done.
    iApply (ewp_mono' with "[Href]").
    iApply (ewp_load with "Href").
    simpl. iIntros (w) "[-> Href]".
    iApply ewp_pure_step. apply pure_prim_step_case_InjR.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (AppRCtx _)). done.
    iApply (ewp_mono' with "[HW_inv Hl Hq]").
    { iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppRCtx _) EmptyCtx))). done.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value. simpl.
      iApply (list_iter_spec _
             (λ ys, (∃ n : natO, is_queue q (Ready q) n) ∗
                    ([∗ list] f ∈ (drop (length ys) ks),
                      ▷ W_inv q (Ready q) Ψ f))%I _ _ ks with "[] [Hl]").
      - iModIntro. iIntros (ks' k vs <-) "[Hq HI]".
        rewrite -app_assoc -cons_middle drop_app big_opL_cons.
        iDestruct "HI" as "[Hk HI]". iDestruct "Hq" as (m) "Hq".
        iApply ewp_pure_step'. apply pure_prim_step_beta. simpl.
        iNext. iApply (ewp_mono' with "[Hq Hk]").
        iApply (Ectxi_ewp_bind (AppRCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value. simpl.
        iApply (queue_push_spec with "Hq [Hk]").
        { iNext. rewrite !Ready_unfold /Ready_pre !W_inv_unfold /W_inv_pre.
          iIntros "Hhandler Hq". iDestruct "Hq" as (n') "Hq".
          iApply ewp_pure_step'. apply pure_prim_step_beta. simpl. iNext.
          iApply ("Hk" with "Hhandler [Hq]").
          - by iExists n'. - by iRewrite ("Heq" $! v).
        }
        simpl. iIntros (_) "Hq". iSplitL "Hq"; [ by iExists (Datatypes.S m) |].
        rewrite (cons_middle k ks' vs) app_assoc  drop_app.
        iModIntro. iApply (big_sepL_mono with "HI"). by auto.
      - done.
      - iNext. rewrite drop_0. iSplitL "Hq".
        by eauto. iApply (big_sepL_mono with "HW_inv"). by auto.
    }
    simpl. iModIntro. iIntros (w) "(_ & Hq & _)".
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (AppRCtx _)). done.
    iApply (Ectxi_ewp_bind (StoreRCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_InjL.
    iApply ewp_value. simpl.
    iApply (ewp_mono' with "[Href]").
    iApply (ewp_store with "Href"). simpl. iModIntro.
    iIntros (w') "Href".
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iMod (running_upd _ _ _ false
      with "Hrunning' Hrunning") as "[Hrunning' Hrunning]".
    iAssert (promise_inv γ p (W_inv q (Ready q)) Ψ)%I
      with "[Href Hrunning']" as "Hpromise_inv".
    { iExists false. iFrame. iExists v.
      iRewrite ("Heq" $! v). by iFrame. }
    iAssert (handler_inv (W_inv q (Ready q)))%I
      with "[HS Hinv Hpromise_inv]" as "Hhandler_inv".
    { iExists S. iFrame.
      rewrite (big_sepM_delete _ S (p, γ) _ Hlookup).
      by iFrame. }
    iModIntro. iClear "H Hp Hv Heq". iDestruct "Hq" as (n') "Hq".
    iApply (ewp_mono' with "[Hhandler_inv Hq]").
    iApply ("run_next_spec" $! n' with "[$] [$]"). by auto.

  (* Effect branch. *)
  - iIntros (v k) "Hprot_agr".
    iDestruct (Ψ_concurrency_agreement with "Hprot_agr") as "[Hasync|Hawait]".

    (* Async. *)
    + rewrite Ψ_async_agreement. iNext. iApply fupd_ewp.
      iMod "Hasync" as (e Φ') "(-> & He & Hk)".
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
      iApply ewp_mono'.
      iApply (promise_alloc _ (W_inv q (Ready q)) Φ').
      iModIntro. simpl. iIntros (_p') "Hp'". 
      iDestruct "Hp'" as (p' γ') "(-> & Hrunning' & Hpromise_inv)".
      iMod (promise_upd with "[$]") as "[Hhandler_inv #Hp']".
      iMod ("Hk" $! p' with "[Hp']") as "Hk". { by iExists γ'. }
      iModIntro.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step'. apply pure_prim_step_rec.
      iNext. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply (ewp_mono' with "[Hq Hk Hrunning]").
      { iApply (Ectxi_ewp_bind (AppRCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value. simpl.
        iApply (queue_push_spec with "Hq"). iNext.
        rewrite Ready_unfold /Ready_pre.
        iIntros "Hhandler_inv Hq".
        iDestruct "Hq" as (n') "Hq".
        iSpecialize ("IH_handler" with "Hrunning Hhandler_inv Hq Hp").
        iApply ewp_pure_step'. apply pure_prim_step_beta.
        iNext. simpl. by iApply "Hk".
      }
      simpl. iIntros (v) "Hq". iModIntro.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step'. apply pure_prim_step_rec. iNext.
      iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply ("IH" with "He Hrunning' Hhandler_inv Hp'").
      by iExists (Datatypes.S n).

    (* Await. *)
    + iClear "IH".
      rewrite Ψ_await_agreement. iNext. iApply fupd_ewp.
      iMod "Hawait" as (p' Φ') "(-> & #Hp' & Hk)".
      iDestruct "Hp'" as (γ') "#Hp'".
      iDestruct (promise_agree with "[Hhandler]") as (S) "(HS & Hinv & H)".
      { iFrame. by iApply "Hp'". }
      iDestruct "H" as (Ψ) "(% & Hpromise_inv & H)".
      rename H into Hlookup.
      iDestruct (promise_unfold_equiv with "H") as "#Heq'". iClear "H".
      iDestruct "Hpromise_inv" as (b) "[Hrunning' Hpromise_inv]".
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply ewp_pure_step'. apply pure_prim_step_case_InjR.
      iModIntro. iNext. case b.
      { iDestruct "Hpromise_inv" as (l ks) "(Href & Hl & HW_inv)".
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step'. apply pure_prim_step_rec. simpl.
        iIntros "!>". iApply ewp_value. simpl.
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        iApply (Ectxi_ewp_bind (CaseCtx _ _)). done.
        iApply (ewp_mono' with "[Href]").
        iApply (ewp_load with "Href"). simpl.
        iIntros (w) "[-> Href]".
        iApply ewp_pure_step. apply pure_prim_step_case_InjR.
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec. simpl.
        iApply ewp_value. simpl.
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        iApply (Ectxi_ewp_bind (AppRCtx _)). done.
        iApply (ewp_bind (ConsCtx (StoreRCtx _)
                         (ConsCtx  InjRCtx EmptyCtx))). done.
        iApply (ewp_bind (ConsCtx (AppLCtx _)
                         (ConsCtx (AppRCtx _) EmptyCtx))). done.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value. simpl.
        iApply (ewp_mono' with "[Hl]").
        iApply (list_cons_spec with "Hl"). simpl.
        iModIntro. iIntros (l') "Hl'".
        iApply (Ectxi_ewp_bind (StoreRCtx _)). done.
        iApply ewp_pure_step'. apply pure_prim_step_InjR.
        iModIntro. iNext.
        iApply ewp_value. simpl.
        iApply (ewp_mono' with "[Href]").
        iApply (ewp_store with "Href"). simpl.
        iIntros (w) "Href".
        iAssert (W_inv q (Ready q) Ψ (λ: "x", k "x")%V)%I
          with "[Hk Hrunning]" as "Hk".
        { rewrite W_inv_unfold /W_inv_pre. iIntros (v) "Hhandler_inv Hq #Hv".
          iSpecialize("Hk" $! v with "[]").
          { iModIntro. by iRewrite -("Heq'" $! v). }
          iApply fupd_ewp. iMod "Hk".
          iApply ewp_pure_step'. apply pure_prim_step_beta. simpl.
          iModIntro. iNext. iApply "Hk".
          iDestruct "Hq" as (n') "Hq".
          iSpecialize ("IH_handler" with "Hrunning Hhandler_inv Hq Hp").
          by iApply "IH_handler".
        }
        iAssert (promise_inv γ' p' (W_inv q (Ready q)) Ψ)%I
          with "[Href Hl' Hrunning' HW_inv Hk]" as "Hpromise_inv".
        { iExists true. iFrame. iExists l', ((λ: "x", k "x")%V :: ks).
          iFrame. iApply (big_sepL_mono with "HW_inv"). by auto. }
        iAssert (handler_inv (W_inv q (Ready q)))%I
          with "[HS Hinv Hpromise_inv]" as "Hhandler_inv".
        { iExists S. iFrame.
          rewrite (big_sepM_delete _ S (p', γ') _ Hlookup).
          by iFrame. }
        iModIntro.
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec. simpl.
        iApply ewp_value. simpl.
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        by iApply ("run_next_spec" with "Hhandler_inv Hq").
      }
      { iDestruct "Hpromise_inv" as (v) "[Href #Hv]".
        iSpecialize("Hk" $! v with "[]").
        { iModIntro. by iRewrite -("Heq'" $! v). }
        iApply fupd_ewp. iMod "Hk". iModIntro.
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step'. apply pure_prim_step_rec. simpl.
        iIntros "!>". iSpecialize ("Hk" $! ⊥%ieff (λ _, True%I)).
        iApply ewp_value. simpl.
        iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
        iApply (Ectxi_ewp_bind (CaseCtx _ _)). done.
        iApply (ewp_mono' with "[Href]").
        iApply (ewp_load with "Href"). simpl.
        iIntros (w) "[-> Href]".
        iAssert (promise_inv γ' p' (W_inv q (Ready q)) Ψ)%I
          with "[Href Hrunning']" as "Hpromise_inv".
        { iExists false. iFrame. iExists v. by iFrame. }
        iAssert (handler_inv (W_inv q (Ready q)))%I
          with "[HS Hinv Hpromise_inv]" as "Hhandler_inv".
        { iExists S. iFrame.
          rewrite (big_sepM_delete _ S (p', γ') _ Hlookup).
          by iFrame. }
        iSpecialize ("IH_handler" with "Hrunning Hhandler_inv Hq Hp").
        iSpecialize("Hk" with "IH_handler").
        iModIntro. iApply ewp_pure_step. apply pure_prim_step_case_InjL.
        iApply (Ectxi_ewp_bind (AppLCtx _)). done.
        iApply ewp_pure_step. apply pure_prim_step_rec.
        iApply ewp_value. simpl.
        iApply ewp_pure_step. apply pure_prim_step_beta.
        by iApply "Hk".
      }
  (* ************************************************************************ *)
Qed.

End scheduler.

Section spec.

Context `{!heapG Σ}.

Context {HList: ListLib Σ} {HQueue: QueueLib Σ}.

Context `{!inG Σ (excl_authR boolO)}.
Context `{!inG Σ (authR (gmapUR
                          (loc * gname)
                          (agreeR (laterO (val -d> (iPrePropO Σ))))))}.

Lemma handler_inv_alloc : ⊢ |==> ∃ γ, ∀ W_inv, handler_inv γ W_inv.
Proof.
  iIntros.
  iMod (own_alloc (● (∅ : gmap (loc * gname) _))) as (γI) "HI";
    first by rewrite auth_auth_valid.
  iModIntro. iExists γI. iIntros (W_inv).
  iExists ∅. rewrite fmap_empty. by iFrame.
Qed.

Lemma run_spec (main : val) : ⊢ |==> ∃ γ,
  EWP main #() @ ∅ <| Ψ_concurrency γ |> {{ _, True }} -∗
    EWP run main @ ∅ {{ _, True }}.
Proof.
  iMod handler_inv_alloc as (γ) "Hhandler_inv".
  iModIntro. iExists γ. iIntros "Hmain".
  iApply (run_spec' _ _ (λ _, True%I) with "Hhandler_inv").
  iApply (ewp_mono with "Hmain"). by auto.
Qed.

End spec.
