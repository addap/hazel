(* ml_references.v

   We study an implementation of ML-like references by means of effect handlers.
   Although our calculus is untyped, this implementation could be adapted
   to typed languages, providing an interface identical to that of polymorphic
   references. The GitHub repository [effect-examples]
   (https://github.com/ocaml-multicore/effects-examples/blob/master/ref.ml)
   provides such an implementation in Multicore OCaml.

*)


From stdpp               Require Import list.
From iris.proofmode      Require Import base tactics classes.
From iris.algebra        Require Import excl_auth gset gmap agree gmap_view.
From iris.base_logic.lib Require Import iprop wsat invariants.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation weakestpre selective_handler.


(** Prophecy variables. *)

Class ProphLib Σ `{!heapG Σ} := {
  NewProph     : val;
  ResolveProph : val;

  Proph :
    loc -d> (list val) -d> iPropO Σ;

  ewp_new_proph_spec E Ψ :
    ⊢ EWP NewProph #() @ E <| Ψ |> {{ y,
        ∃ (p : loc) us, ⌜ y = #p ⌝ ∗ Proph p us }};

  ewp_resolve_proph_spec E Ψ p us (u : val) :
    Proph p us -∗
      EWP ResolveProph #p u @ E <| Ψ |> {{ _,
        ∃ us', ⌜ us = u :: us' ⌝ ∗ Proph p us' }};

}.

Section proph_lib.
Context `{!heapG Σ} `{!ProphLib Σ}.

Definition to_loc_list : list val → list loc :=
  fix go (us : list val) {struct us} : list loc :=
    match us with (LitV (LitLoc r)) :: us' => r :: go us' | _ => [] end.

Definition Proph' (p : loc) (S L : gset (loc)) : iProp Σ :=
  ∃ us, Proph p us ∗ ⌜ L = (list_to_set (to_loc_list us)) ∖ S ⌝.

Lemma ewp_new_proph_spec' E Ψ :
  ⊢ EWP NewProph #() @ E <| Ψ |> {{ y, ∃ (p : loc) L, ⌜ y = #p ⌝ ∗ Proph' p ∅ L }}.
Proof.
  iApply ewp_mono; [|iApply ewp_new_proph_spec].
  iIntros (v). iDestruct 1 as (p us) "[-> Hp]". iModIntro.
  iExists p, (list_to_set (to_loc_list us)). iSplit; [done|].
  iExists us. iFrame. by rewrite difference_empty_L.
Qed.

Lemma  ewp_resolve_proph_spec' E Ψ p S L (r : loc) :
  ⌜ r ∉ S ⌝ -∗ Proph' p S L -∗
    EWP ResolveProph #p #r @ E <| Ψ |> {{ _,
      ∃ L', ⌜ r ∉ L' ⌝ ∗ ⌜ L = {[r]} ∪ L' ⌝ ∗ Proph' p ({[r]} ∪ S) L' }}.
Proof.
  iIntros (Hnot_in). iDestruct 1 as (us) "[Hp %]". rename H into HL.
  iApply (ewp_mono' with "[Hp]"); [iApply (ewp_resolve_proph_spec with "Hp")|].
  iIntros (v). iDestruct 1 as (ls') "[-> Hp]". iModIntro.
  iExists (L ∖ {[r]}). iSplit; [iPureIntro|iSplit; [iPureIntro|]].
  { set_solver. }
  { apply union_difference_L. rewrite HL. simpl.
    apply subseteq_difference_r; set_solver.
  }
  { iExists ls'. iFrame. iPureIntro. rewrite HL. simpl. set_solver. }
Qed.

End proph_lib.


(** Implementation. *)

Section code.
Context `{!heapG Σ} `{!ProphLib Σ}.

Definition ref' : val := λ: "init",
  do: (InjLV #(), "init").

Definition get' : val := λ: "r",
  do: (InjR "r", InjLV #()).

Definition set' : val := λ: "r" "y",
  do: (InjR "r", InjR "y").

Definition run : val := λ: "client",
  let: "p" := NewProph #() in
  try: "client" #() with label (InjLV #())
  (* Effect branch: *)
    effect (λ: "v" "k",
    let: "init" := Snd "v" in
    let: "r" := fresh_label #() in
    ResolveProph "p" "r";;
    let: "comp" :=
      try: "k" "r" with label (InjR "r")
      (* Effect branch: *)
        effect (λ: "v" "k",
        match: Snd "v" with
          InjL <>  => λ: "x", ("k" "x") "x"
        | InjR "y" => λ:  <>, ("k" #()) "y"
        end)
      (* Return branch: *)
      | return (λ: "res", λ: <>, "res")
      end
    in
    "comp" "init")
  (* Return branch: *)
  | return (λ: "res", "res")
  end.

End code.


(** State protocol. *)

Section protocol.
Context `{!heapG Σ}.
Context (mapsto : loc → val → iProp Σ).

Definition ref_prot : iEff Σ :=
  (>> (init : val) >> ! (InjLV #(), init) {{ True          }};
   << (r : loc)    << ? #(r)              {{ mapsto r init }}).

Definition get_prot : iEff Σ :=
  (>> (r : loc) (x : val) >> ! (InjRV #r, InjLV #()) {{ mapsto r x }};
                             ? (x)                   {{ mapsto r x }}).

Definition set_prot : iEff Σ :=
  (>> (r : loc) (x y : val) >> ! (InjRV #r, InjRV y) {{ mapsto r x }};
                               ? #()                 {{ mapsto r y }}).

Definition state_prot : iEff Σ := ref_prot <+> get_prot <+> set_prot.


Lemma ref_agreement v Φ : protocol_agreement v ref_prot Φ ≡
  (∃ (init : val), ⌜ v = PairV (InjLV #()) init ⌝ ∗ True ∗
    (∀ (r : loc), mapsto r init -∗ Φ #r))%I.
Proof.
  rewrite /ref_prot (protocol_agreement_tele' [tele _] [tele _]). by auto.
Qed.

Lemma get_agreement v Φ : protocol_agreement v get_prot Φ ≡
  (∃ (r : loc) (x : val), ⌜ v = PairV (InjRV #r) (InjLV #()) ⌝ ∗ mapsto r x ∗
    (mapsto r x -∗ Φ x))%I.
Proof.
  rewrite /get_prot (protocol_agreement_tele' [tele _ _] [tele]). by auto.
Qed.

Lemma set_agreement v Φ : protocol_agreement v set_prot Φ ≡
  (∃ (r : loc) (x y : val), ⌜ v = PairV (InjRV #r) (InjRV y) ⌝ ∗ mapsto r x ∗
    (mapsto r y -∗ Φ #()))%I.
Proof.
  rewrite /set_prot (protocol_agreement_tele' [tele _ _ _] [tele]). by auto.
Qed.


Lemma ref_spec E (init : val) :
  ⊢ EWP ref' init @ E <| state_prot |> {{ lk,
      ∃ (r : loc), ⌜ lk = #r ⌝ ∗ mapsto r init }}.
Proof. 
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind DoCtx). done.
  iApply ewp_pure_step. apply pure_prim_step_pair. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_do.
  iApply ewp_eff. iApply protocol_agreement_sum_intro_l.
  rewrite ref_agreement. iExists init. iSplit; [done|]. iSplit; [done|].
  iIntros (r) "Hr". iNext. iApply ewp_value. iExists r. by iFrame.
Qed.

Lemma get_spec E (r : loc) (x : val) :
  mapsto r x -∗
    EWP get' #r @ E <| state_prot |> {{ v, ⌜ v = x ⌝ ∗ mapsto r x }}.
Proof.
  iIntros "Hr".
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind DoCtx). done.
  iApply (Ectxi_ewp_bind (PairLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_InjR. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_pair. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_do.
  iApply ewp_eff.
  iApply protocol_agreement_sum_intro_r.
  iApply protocol_agreement_sum_intro_l.
  rewrite get_agreement. iExists r, x. iSplit; [done|]. iFrame.
  iIntros "Hr". iNext. iApply ewp_value. by iFrame.
Qed.

Lemma set_spec E (r : loc) (x y : val) :
  mapsto r x -∗
    EWP set' #r y @ E <| state_prot |> {{ _, mapsto r y }}.
Proof.
  iIntros "Hr".
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind DoCtx). done.
  iApply (Ectxi_ewp_bind (PairRCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_InjR. iApply ewp_value. simpl.
  iApply (Ectxi_ewp_bind (PairLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_InjR. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_pair. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_do.
  iApply ewp_eff.
  iApply protocol_agreement_sum_intro_r.
  iApply protocol_agreement_sum_intro_r.
  rewrite set_agreement. iExists r, x, y. iSplit; [done|]. iFrame.
  iIntros "Hr". iNext. by iApply ewp_value.
Qed.

End protocol.


(** Camera setup. *)

Class stateG Σ := {
  gname_mapG :> inG Σ (gmap_viewR loc gnameO);
  mem_cellG  :> inG Σ (excl_authR valO);
}.

Definition stateΣ := #[
  GFunctor (gmap_viewR loc gnameO);
  GFunctor (excl_authR valO)
].

Instance subG_stateΣ {Σ} : subG stateΣ Σ → stateG Σ.
Proof. solve_inG. Qed.


(** Ghost state theory. *)

Section ghost_theory.
Context `{!heapG Σ} `{!stateG Σ} `{!ProphLib Σ}.

Definition handler_inv (M : gmap loc gname) (S L : gset loc) (p : loc) : iProp Σ :=
  known_labels S ∗ Proph' p S L ∗ ⌜ dom (gset loc) M = S ∪ L ⌝ ∗
  ([∗ set] r ∈ L, ∃ γ, ⌜ M !! r = Some γ ⌝ ∗ own γ (●E #()) ∗ own γ (◯E #()))%I.

Definition mapsto (M : gmap loc gname) (r : loc) (x : val) : iProp Σ :=
  ∃ γ, ⌜ M !! r = Some γ ⌝ ∗ own γ (◯E x).


Lemma mem_cell_alloc : ⊢ |==> ∃ γ, own γ (●E #()) ∗ own γ (◯E #())%I.
Proof.
  iMod (own_alloc (●E #() ⋅ ◯E #())) as (γ) "[??]";
  [ apply excl_auth_valid | eauto with iFrame ]; done.
Qed.
Lemma mem_cell_agree γ (x x' : val) : ⊢ (own γ (●E x) ∗ own γ (◯E x')) → ⌜ x' = x ⌝.
Proof.
  iIntros "[H● H◯]".
  by iDestruct (own_valid_2 with "H● H◯") as %?%excl_auth_agree_L.
Qed.

Lemma mem_cell_update γ (y x x' : val) :
  own γ (●E x) -∗ own γ (◯E x') ==∗ own γ (●E y)  ∗ own γ (◯E y).
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (●E y ⋅ ◯E y) with "Hγ● Hγ◯") as "[$$]";
  [ apply excl_auth_update | ]; done.
Qed.

Lemma heap_alloc (L : gset loc) :
  ⊢ |==> ∃ (M : gmap loc gname), ⌜ dom (gset loc) M = L ⌝ ∗
           [∗ set] r ∈ L, ∃ γ, ⌜ M !! r = Some γ ⌝ ∗ own γ (●E #()) ∗ own γ (◯E #()).
Proof.
  iInduction L as [|l L not_in] "IH" using set_ind_L.
  { iModIntro. iExists ∅. rewrite dom_empty_L. by auto. }
  { iMod "IH" as (M) "[% HM]". iMod mem_cell_alloc as (γ) "Hγ". iModIntro.
    iExists (<[l:=γ]>M). iSplit; [by rewrite dom_insert_L H|].
    rewrite big_opS_insert; [|done]. iSplitL "Hγ".
    { iExists γ. iFrame. by rewrite lookup_insert. }
    { iApply (big_opS_proper with "HM"). iIntros (l' Hin). simpl.
      have Hneq: l ≠ l'. { by intros ->. }
      iSplit; iDestruct 1 as (γ') "[% ?]"; iExists γ'; iFrame.
      { by rewrite lookup_insert_ne in H0. } { by rewrite lookup_insert_ne. }
    }
  }
Qed.

Lemma handler_inv_alloc (p : loc) (L : gset loc) :
  Proph' p ∅ L ==∗ ∃ M, handler_inv M ∅ L p.
Proof.
  iIntros "Hp". iMod (heap_alloc L) as (M) "[% HM]". iModIntro.
  iExists M. iFrame. rewrite union_empty_l_L. by iSplit; [iApply known_labels_empty|].
Qed.

Lemma mapsto_imp_valid_label M S L p r x :
  ⊢ handler_inv M S L p ∗ mapsto M r x → ⌜ r ∈ S ⌝.
Proof.
  iIntros "[(_ & _ & % & Hinv) Hmapsto]". rename H into Hdom.
  iDestruct "Hmapsto" as (γ) "[% H◯]".
  have Helem_of_dom: (r ∈ S ∨ r ∈ L).
  { rewrite -elem_of_union -Hdom elem_of_dom. by eauto. }
  case (decide (r ∈ L)) as [Hin_L|Hnot_in_L].
  { rewrite (big_opS_delete _ _ _ Hin_L). iDestruct "Hinv" as "[H _]".
    iDestruct "H" as (γ') "(% & _ & H◯')".
    rewrite H in H0. inversion H0. rewrite -H2. 
    by iDestruct (own_valid_2 with "H◯ H◯'") as %?%excl_auth_frag_valid_op_1_l.
  }
  { iPureIntro. by case Helem_of_dom. }
Qed.

End ghost_theory.


(** Verification. *)

Section verification.
Context `{!heapG Σ} `{!stateG Σ} `{!ProphLib Σ}.

Definition valid_label (S : gset loc) : val → Prop := λ v,
  match v with
  | PairV (InjRV (LitV (LitLoc r))) _ => r ∈ S
  | _ => False
  end.

Lemma get_set_handler_spec E (M : gmap loc gname) (S : gset loc) (r : loc) (γ : gname) (x : val) Φ :
  M !! r = Some γ → r ∉ S →
    own γ (●E x) -∗
      selective_handler E (compare_label (InjRV #r))
        (* Effect branch: *) (λ: "v" "k",
            match: Snd "v" with
              InjL <>  => λ: "x", ("k" "x") "x"
            | InjR "y" => λ:  <>, ("k" #()) "y"
            end)%V
        (* Return branch: *) (λ: "res", λ: <>, "res")%V
        (* Client protocol: *)((valid_label ({[r]} ∪ S)) ?>
          (get_prot (mapsto M) <+> set_prot (mapsto M)))%ieff
        (* Handler protocol: *) ((valid_label S) ?>
            (get_prot (mapsto M) <+> set_prot (mapsto M)))%ieff
        (* Client postcondition: *) Φ
        (* Handler postcondition: *) (λ (comp : val),
          EWP comp x @ E <| (valid_label S) ?>
            (get_prot (mapsto M) <+> set_prot (mapsto M)) |> {{ Φ }}).
Proof.
  iIntros (Hlkup Hnot_in) "H●". iLöb as "IH" forall (x).
  rewrite selective_handler_unfold. iSplit; [|iSplit].
  { iClear "IH H●". iIntros (res) "HΦ".
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    by iApply ewp_value.
  }
  { iIntros (v k) "Hprot". iNext.
    rewrite !protocol_agreement_filter protocol_agreement_sum_elim.
    iDestruct "Hprot" as "(% & _ & [Hprot|Hprot])"; rename H into Heq_r.
    { rewrite get_agreement. iDestruct "Hprot" as (r' x') "(-> & Hmapsto & Hk)".
      simpl in Heq_r. inversion Heq_r. destruct H0. clear Heq_r.
      iDestruct "Hmapsto" as (γ') "[% H◯]". rename H into Hlkup'.
      assert (γ' = γ) as ->. { rewrite Hlkup' in Hlkup. by inversion Hlkup. }
      iDestruct (mem_cell_agree γ x x' with "[H● H◯]") as %->. { by iFrame. }
      iSpecialize ("Hk" with "[H◯] [H●]"). { iExists γ. by iFrame. } { by iApply "IH". }
      iClear "IH". clear Hlkup Hlkup'.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (CaseCtx _ _)). done.
      iApply ewp_pure_step. apply pure_prim_step_Snd. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_case_InjL.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done. by iApply "Hk".
    }
    { rewrite set_agreement. iDestruct "Hprot" as (r' x' y) "(-> & Hmapsto & Hk)".
      simpl in Heq_r. inversion Heq_r. destruct H0. clear Heq_r.
      iDestruct "Hmapsto" as (γ') "[% H◯]". rename H into Hlkup'.
      assert (γ' = γ) as ->. { rewrite Hlkup' in Hlkup. by inversion Hlkup. }
      iApply fupd_ewp. iMod (mem_cell_update γ y with "H● H◯") as "[H● H◯]". iModIntro.
      iSpecialize ("Hk" with "[H◯] [H●]"). { iExists γ. by iFrame. } { by iApply "IH". }
      iClear "IH". clear Hlkup Hlkup'.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (CaseCtx _ _)). done.
      iApply ewp_pure_step. apply pure_prim_step_Snd. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_case_InjR.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done. by iApply "Hk".
    }
  }
  { iIntros (v k) "Hprot". iNext. iSpecialize ("IH" with "H●").
    rewrite !protocol_agreement_filter. iDestruct "Hprot" as "(% & % & Hprot)".
    rename H into Hnot_r, H0 into Hvalid. iSplit.
    { iPureIntro.
      destruct v; try naive_solver. simpl.
      destruct v1; try naive_solver.
      destruct v1; try naive_solver.
      destruct l; try naive_solver. simpl in Hvalid, Hnot_r.
      have Hnot_eq: (l ≠ r). { by intros ->. }
      revert Hvalid. rewrite elem_of_union elem_of_singleton. by destruct 1 as [|].
    }
    { iApply (protocol_agreement_mono with "Hprot"). iIntros (w) "Hk". by iApply "Hk". }
  }
Qed.

Lemma ref_handler_spec E M S L p Φ :
  handler_inv M S L p -∗
    selective_handler E (compare_label (InjLV #()))
      (* Effect branch: *) (λ: "v" "k",
        let: "init" := Snd "v" in
        let: "r" := fresh_label #() in
        ResolveProph #p "r";;
        let: "comp" := try: "k" "r" with label (InjR "r")
          effect (λ: "v" "k", match: Snd "v" with
            InjL <>  => λ: "x", ("k" "x") "x"
          | InjR "y" => λ:  <>, ("k" #()) "y"
          end)
        | return (λ: "res", λ: <>, "res")
        end in "comp" "init")%V
      (* Return branch: *) (λ: "res", "res")%V
      (* Client protocol: *) (state_prot (mapsto M))
      (* Handler protocol: *) ((valid_label S) ?>
        (get_prot (mapsto M) <+> set_prot (mapsto M)))%ieff
      (* Client postcondition: *) Φ
      (* Handler postcondition: *) Φ.
Proof.
  iLöb as "IH" forall (S L). iIntros "Hinv".
  rewrite selective_handler_unfold. iSplit; [|iSplit].
  { iClear "IH Hinv". iIntros (res) "HΦ". iNext.
    iApply ewp_pure_step. apply pure_prim_step_beta. by iApply ewp_value.
  }
  { iIntros (v k) "Hprot". rewrite protocol_agreement_filter.
    iDestruct "Hprot" as "[% Hprot]". rewrite !protocol_agreement_sum_elim.
    iDestruct "Hprot" as "[Hprot|[Hprot|Hprot]]"; [|
    rewrite get_agreement; by iDestruct "Hprot" as (r x)   "[-> _]"|
    rewrite set_agreement; by iDestruct "Hprot" as (r x y) "[-> _]"].
    rewrite ref_agreement. iDestruct "Hprot" as (init) "[-> [_ Hk]]".
    iDestruct "Hinv" as "(#Hlabels & Hp & % & Hinv)".
    clear H. rename H0 into Hdom.
    iNext. iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (AppRCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_Snd. iApply ewp_value. simpl.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (AppRCtx _)). done.
    iApply ewp_strong_mono; first done;[
    iApply (fresh_label_spec with "Hlabels")|iApply iEff_le_refl|].
    iIntros (lk). iClear "Hlabels". iDestruct 1 as (r) "[-> [% Hlabels]]".
    simpl. rename H into Hnot_in.
    iModIntro. iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (AppRCtx _)). done.
    iApply (ewp_strong_mono with "[Hp]"); first done; [
    iApply (ewp_resolve_proph_spec' with "[//] Hp")|iApply iEff_le_refl|].
    iDestruct (1) as (L') "(% & -> & Hp)". rename H into Hnot_in'. simpl.
    iModIntro. iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl. clear v.
    rewrite big_opS_insert; [|done]. iDestruct "Hinv" as "[H Hinv]".
    iDestruct "H" as (γ) "(% & H● & H◯)". rename H into Hlkup.
    iApply fupd_ewp. iMod (mem_cell_update _ init with "H● H◯") as "[H● H◯]".
    iAssert (mapsto M r init) with "[H◯]" as "Hmapsto". { iExists γ. by iFrame. }
    iAssert (handler_inv M ({[r]} ∪ S) L' p) with "[Hinv Hp Hlabels]" as "Hinv".
    { iFrame. iPureIntro. rewrite Hdom. set_solver. }
    iSpecialize ("IH" with "Hinv"). iSpecialize ("Hk" with "Hmapsto IH").
    iModIntro. iApply (Ectxi_ewp_bind (AppRCtx _)). done.
    iApply (Ectxi_ewp_bind (AppRCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
    iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppRCtx _) EmptyCtx))). done.
    iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
    iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppLCtx _)
                     (ConsCtx (AppRCtx _) EmptyCtx)))). done.
    iApply ewp_pure_step. apply pure_prim_step_InjR. iApply ewp_value. simpl.
    iApply (ewp_strong_mono with "[Hk H●]"). done.
    { iApply (ewp_label_try_with with "Hk"). by iApply (get_set_handler_spec with "H●"). }
    { iApply iEff_le_refl. }
    { iIntros (comp) "Hcomp". iModIntro. iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl. by iApply "Hcomp".
    }
  }
  { iIntros (v k) "Hprot". iNext. rewrite !protocol_agreement_filter.
    iDestruct "Hprot" as "[% Hprot]".
    rewrite /state_prot protocol_agreement_sum_elim.
    iDestruct "Hprot" as "[Hprot|Hprot]"; [
    rewrite ref_agreement; by iDestruct "Hprot" as (init) "[-> _]"|].
    iSplit; [rewrite protocol_agreement_sum_elim;
    iDestruct "Hprot" as "[Hprot|Hprot]"; iClear "IH"; clear H |].
    { rewrite get_agreement. iDestruct "Hprot" as (r x) "[-> [Hr _]]". simpl.
      iApply mapsto_imp_valid_label. by iFrame.
    }
    { rewrite set_agreement. iDestruct "Hprot" as (r x y) "[-> [Hr _]]". simpl.
      iApply mapsto_imp_valid_label. by iFrame.
    }
    { iApply (protocol_agreement_mono with "Hprot").
      iIntros (w) "Hk". iApply "Hk". by iApply ("IH" with "Hinv").
    }
  }
Qed.

Lemma run_spec E Φ (client : val) :
  (∀ mapsto,
     EWP client #() @ E <| state_prot mapsto |> {{ Φ }}) ⊢
       EWP run client @ E {{ Φ }}.
Proof.
  iIntros "Hclient". iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_mono'; [by iApply ewp_new_proph_spec'|].
  iIntros (v). iDestruct 1 as (p L) "[-> Hp]". simpl.
  iMod (handler_inv_alloc with "Hp") as (M) "Hinv". iModIntro.
  iSpecialize ("Hclient" $! (mapsto M)).
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppRCtx _) EmptyCtx))). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply (ewp_strong_mono with "[Hclient Hinv]"). done.
  { iApply (ewp_label_try_with with "Hclient [Hinv]").
    by iApply (ref_handler_spec with "Hinv").
  }
  { iIntros (v Φ'). iModIntro. rewrite protocol_agreement_filter.
    iIntros "[% _]". exfalso.
    destruct v; try naive_solver. simpl.
    destruct v1; try naive_solver.
    destruct v1; try naive_solver.
    destruct l; try naive_solver. done.
  }
  { by auto. }
Qed.

End verification.
