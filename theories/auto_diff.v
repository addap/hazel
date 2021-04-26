(* auto_diff.v *)

From stdpp               Require Import list gmap.
From iris.proofmode      Require Import base tactics classes.
From iris.algebra        Require Import excl_auth gset gmap agree gmap_view.
From iris.base_logic.lib Require Import iprop wsat invariants.
From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation weakestpre deep_handler.


Section differentiation.

Definition name := loc.

Inductive op := Add | Mult.

Definition node : Set := op * name * name.

Definition let_expr : Set := list (name * node).

Inductive expr (A : Set) :=
  | ENode : op → expr A → expr A → expr A
  | ELeaf :  A →                   expr A.

Global Arguments ENode {_} _ _ _.
Global Arguments ELeaf {_} _.

Definition interp (K : let_expr) : name → expr name :=
  (fix interp (K : let_expr) (y : name) {struct K} : expr name :=
     match K with [] => ELeaf y | (x, (op, a, b)) :: K =>
       if (decide (x = y)) then ENode op (interp K a) (interp K b) else (interp K y)
     end) (reverse K).

Definition variables {A : Set} : expr A → list A :=
  (fix variables (e : expr A) {struct e} :=
     match e with ELeaf x => [x] | ENode _ e e' =>
       variables e ++ variables e'
     end).

Definition emap {A B : Set} (f : A → B) : expr A → expr B :=
  fix emap (e : expr A) {struct e} : expr B :=
    match e with ELeaf x => ELeaf (f x) | ENode op ea eb =>
      ENode op (emap ea) (emap eb)
    end.

Definition emap' {A B : Set} `{Countable A, Inhabited B} (E : gmap A B) : expr A → expr B :=
  emap (λ i, lookup_total i E).

Definition eval_op : op → nat → nat → nat :=
  λ op n n', match op with Add => n + n' | Mult => n * n' end%nat.

Definition eval : expr nat → nat :=
  fix eval (e : expr nat) {struct e} : nat :=
    match e with ELeaf n => n | ENode op ea eb =>
       eval_op op (eval ea) (eval eb)
    end.

Definition diff_var {A : Set} `{EqDecision A} (r u : A) : nat :=
  if (decide (r = u)) then 1%nat else 0%nat.

Definition diff {A : Set} `{EqDecision A} (E : A → nat) : expr A → A → nat :=
  fix diff (e : expr A) (u : A) {struct e} : nat :=
    match e with
    | ELeaf r => diff_var r u
    | ENode Add ea eb =>
       let ad := diff ea u in
       let bd := diff eb u in
       (ad + bd)%nat
    | ENode Mult ea eb =>
       let av := eval (emap E ea) in
       let bv := eval (emap E eb) in
       let ad := diff ea u in
       let bd := diff eb u in
       (ad * bv + av * bd)%nat
    end.

Definition diff' {A : Set} `{Countable A} (E : gmap A nat) : expr A → A → nat :=
  diff (λ i, lookup_total i E).

Global Instance op_eq_dec : EqDecision op.
Proof. solve_decision. Qed.

Global Instance node_eq_dec : EqDecision node.
Proof. solve_decision. Qed.

Global Instance let_expr_eq_dec : EqDecision let_expr.
Proof. solve_decision. Qed.

Global Instance expr_eq_dec {A : Set} `{EqDecision A} : EqDecision (expr A).
Proof. solve_decision. Qed.

Lemma emap_compose {A B C : Set} (f : A → B) (g : B → C) (e : expr A) :
  emap (g ∘ f) e = emap g (emap f e).
Proof. by induction e; simpl; [rewrite IHe1 IHe2|]. Qed.

Lemma emap_ext {A B : Set} (f : A → B) (g : A → B) (e : expr A) :
  (∀ x, x ∈ variables e → f x = g x) →
    emap f e = emap g  e.
Proof.
  induction e as [op a IHa b IHb|].
  { intros Hvar. rewrite //= IHa; [rewrite IHb; [done|]|]; set_solver. }
  { intros Hvar. simpl. f_equal. apply Hvar. set_solver. }
Qed.

Lemma diff_ext {A : Set} `{EqDecision A} (f : A → nat) (g : A → nat) (e : expr A) (x : A) :
  (∀ x, x ∈ variables e → f x = g x) →
    diff f e x = diff g e x.
Proof.
  induction e as [[|] a IHa b IHb|]; [| |done].
  { intros Hvar. rewrite //= IHa; [rewrite IHb; [done|]|]; set_solver. }
  { intros Hvar. rewrite //= IHa; [rewrite IHb; [|]|]; [|set_solver|set_solver].
    rewrite !(emap_ext f g); [done| |]; set_solver.
  }
Qed.

Lemma interp_snoc K x op a b y :
  interp (K ++ [(x, (op, a, b))]) y =
    if (decide (x = y)) then
      ENode op (interp K a) (interp K b)
    else
      interp K y.
Proof. by rewrite /interp reverse_app. Qed.

Lemma interp_nil y : interp [] y = ELeaf y.
Proof. done. Qed.

Lemma diff_var_eq {A : Set} `{EqDecision A} (r : A) : diff_var r r = 1%nat.
Proof. by rewrite /diff_var decide_True. Qed.

Lemma diff_var_neq {A : Set} `{EqDecision A} (r u : A) : r ≠ u → diff_var r u = 0%nat.
Proof. intros ?. by rewrite /diff_var decide_False. Qed.

Lemma eval_interp (E : gmap name nat) (K : let_expr) r x op a b av bv :
  E !! a = Some av →
  E !! b = Some bv →
    eval (emap' E (interp ((x, (op, a, b)) :: K) r)) =
      eval (emap' (<[x:=eval_op op av bv]> E) (interp K r)).
Proof.
  intros Heval_a Heval_b. rewrite -(reverse_involutive K).
  revert r op; induction (reverse K) as [|(y, ((op', a'), b')) K']; intros r op.
  { rewrite reverse_nil -(app_nil_l [(x, _)]) interp_snoc //=.
    case (decide (x = r)).
    { revert Heval_a Heval_b. simpl. rewrite !lookup_total_alt.
      intros -> -> ->. by rewrite lookup_insert //=. }
    { simpl. rewrite !lookup_total_alt.
      intros ?. by rewrite lookup_insert_ne. }
  }
  { rewrite reverse_cons app_comm_cons !interp_snoc.
    case (decide (y = r)); case op; case op'; try simpl; by rewrite !IHK'.
  }
Qed.

Lemma diff_interp_cons av bv E K r u x op a b :
  x ≠ u →
  E !! a = Some av →
  E !! b = Some bv →
    diff' E (interp ((x, (op, a, b)) :: K) r) u =
      let opd := diff' E (ENode op (ELeaf a) (ELeaf b)) u  in
      let ud :=  diff' (<[x:=eval_op op av bv]> E) (interp K r) u in
      let xd :=  diff' (<[x:=eval_op op av bv]> E) (interp K r) x in
      (ud + opd * xd)%nat.
Proof.
  revert r u E. induction K as [|(y, ((op', a'), b')) K'] using rev_ind;
  intros r u E Hneq Heval_a Heval_b.
  { rewrite /interp //=. case (decide (x = r)).
    { intros ->. by rewrite diff_var_eq (diff_var_neq _ _ Hneq) Nat.mul_1_r. }
    { intros Hneq'. rewrite (diff_var_neq r x); [|done].
      by rewrite Nat.mul_0_r Nat.add_0_r.
    }
  }
  { rewrite app_comm_cons !interp_snoc //=.
    case (decide (y = r)); case op'; try by rewrite !IHK'.
    { intros ->. simpl. rewrite !IHK'; try done. simpl. lia. }
    { intros ->. simpl.
      rewrite !(eval_interp _ _ _ _ _ _ _ av bv); try done.
      rewrite !IHK'; try done. simpl.  unfold emap'. lia.
    }
  }
Qed.

Lemma diff_emap (A B : Set) `{EqDecision A, EqDecision B} (f : A → B) (g : B → nat) (e : expr A) (x : A) :
  (∀ y, y ∈ variables e → f x = f y → x = y) →
      diff g (emap f e) (f x) = diff (g ∘ f) e x.
Proof.
  intros Hf_inj. induction e as [op ea IHea eb IHeb|y].
  { simpl. rewrite !IHea; [rewrite !IHeb|]; [by rewrite emap_compose emap_compose| |];
    intros ??; apply Hf_inj; rewrite elem_of_app; [by right|by left]. }
  { case (decide (f y = f x)) as [Heq|Hneq]; simpl.
    { specialize (Hf_inj y). rewrite Hf_inj; [by rewrite !diff_var_eq| |done].
      by apply elem_of_list_singleton. }
    { case (decide (y = x)) as [->|Hneq']; [done|]. by rewrite !diff_var_neq. }
  }
Qed.

Lemma interp_app K K' x : x ∉ K'.*1 → interp (K ++ K') x = interp K x.
Proof.
  revert x. induction K' as [|(y, ((op, a), b)) K'] using rev_ind.
  { by rewrite app_nil_r. }
  { intro x. rewrite fmap_app not_elem_of_app not_elem_of_cons app_assoc interp_snoc //=.
    intros [Hnot_in [Hneq _]]. case (decide (y = x)); [by intros ->|]. by rewrite IHK'.
  }
Qed.

Lemma interp_leaf K x : x ∉ K.*1 → interp K x = ELeaf x.
Proof.
  revert x. induction K as [|(y, ((op, a), b)) K'] using rev_ind; [done|].
  intro x. rewrite fmap_app not_elem_of_app not_elem_of_cons interp_snoc //=.
  intros [Hnot_in [Hneq _]]. case (decide (y = x)); [by intros ->|]. by rewrite IHK'.
Qed.

End differentiation.


(** Implementation. *)

Section code.
Context `{!heapG Σ}.

Definition add : val := λ: "a" "b",
  do: InjL ("a", "b").

Definition mult : val := λ: "a" "b",
  do: InjR ("a", "b").

Definition mk : val := λ: "x",
  ref ("x", #0%nat).

Definition get_val : val := λ: "x",
  Fst (Load "x").

Definition get_diff : val := λ: "x",
  Snd (Load "x").

Definition set_diff : val := λ: "x" "d",
  "x" <- (Fst (Load "x"), "d").

Definition run : val := λ: "client",
  try: "client" #() with
  (* Effect branch: *)
    effect (λ: "v" "k",
      match: "v" with
        InjL "p" =>
          let: "a" := Fst "p" in
          let: "b" := Snd "p" in
          let: "u" := mk ((get_val "a") + (get_val "b")) in
          "k" "u";;
          let: "ud" := get_diff "u" in
          set_diff "a" ((get_diff "a") + "ud");;
          set_diff "b" ((get_diff "b") + "ud")
      | InjR "p" =>
          let: "a" := Fst "p" in
          let: "b" := Snd "p" in
          let: "av" := get_val "a" in
          let: "bv" := get_val "b" in
          let: "u" := mk ("av" * "bv") in
          "k" "u";;
          let: "ud" := get_diff "u" in
          set_diff "a" ((get_diff "a") + ("bv" * "ud"));;
          set_diff "b" ((get_diff "b") + ("av" * "ud"))
      end)
  (* Return branch: *)
  | return (λ: "r", set_diff "r" #1%nat)
  end.

Definition grad : val := λ: "f" "n",
  let: "x" := mk "n" in
  run (λ: <>, "f" "x");;
  get_diff "x".

End code.


(** AD protocol. *)

Section protocol.
Context `{!heapG Σ}.

Definition op_repr : op → name → name → val :=
  λ op a b, match op with Add => InjLV (PairV #a #b) | Mult => InjRV (PairV #a #b) end.


Context {A : Set} (represents : name → expr A → iProp Σ).

Definition AD_prot : iEff Σ :=
  (>> (op : op) (a b : name) (av bv : expr A) >>
     ! (op_repr op a b) {{ represents a av ∗ represents b bv }};
   << (x : name) <<
     ? (#x)             {{ represents x (ENode op av bv) }}).


Lemma AD_agreement v Φ : protocol_agreement v AD_prot Φ ≡
  (∃ (op : op) (a b : name) (av bv : expr A),
    ⌜ v = op_repr op a b ⌝ ∗ (represents a av ∗ represents b bv) ∗
    (∀ (x : name), represents x (ENode op av bv) -∗ Φ #x))%I.
Proof.
  rewrite /AD_prot (protocol_agreement_tele' [tele _ _ _ _ _] [tele _]). by auto.
Qed.


Lemma add_spec E (a b : name) (av bv : expr A) :
  represents a av -∗ represents b bv -∗
    EWP add #a #b @ E <| AD_prot |> {{ y,
      ∃ (x : name), ⌜ y = #x ⌝ ∗ represents x (ENode Add av bv) }}.
Proof.
  iIntros "Ha Hb". iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind DoCtx). done.
  iApply (Ectxi_ewp_bind InjLCtx). done.
  iApply ewp_pure_step. apply pure_prim_step_pair. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_InjL. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_do.
  iApply ewp_eff.
  rewrite AD_agreement. iExists Add, a, b, av, bv. iSplit; [done|]. iFrame.
  iIntros (r) "Hr". iNext. iApply ewp_value. iExists r. by iFrame.
Qed.

Lemma mult_spec E (a b : name) (av bv : expr A) :
  represents a av -∗ represents b bv -∗
    EWP mult #a #b @ E <| AD_prot |> {{ y,
      ∃ (x : name), ⌜ y = #x ⌝ ∗ represents x (ENode Mult av bv) }}.
Proof.
  iIntros "Ha Hb". iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind DoCtx). done.
  iApply (Ectxi_ewp_bind InjRCtx). done.
  iApply ewp_pure_step. apply pure_prim_step_pair. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_InjR. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_do.
  iApply ewp_eff.
  rewrite AD_agreement. iExists Mult, a, b, av, bv. iSplit; [done|]. iFrame.
  iIntros (r) "Hr". iNext. iApply ewp_value. iExists r. by iFrame.
Qed.

End protocol.


(** Camera setup. *)

Canonical Structure nodeO := leibnizO node.

Class cgraphG Σ := {
  cgraph_mapG :> inG Σ (gmap_viewR name (leibnizO node));
}.

Definition cgraphΣ := #[
  GFunctor (gmap_viewR name (leibnizO node))
].

Instance subG_cgraphΣ {Σ} : subG cgraphΣ Σ → cgraphG Σ.
Proof. solve_inG. Qed.


(** Ghost theory. *)

Section ghost_theory_defs.
Context `{!heapG Σ} `{!cgraphG Σ}.

Definition to_cgraph : let_expr → gmap name node := list_to_map.

Definition let_expr_auth γ (K : let_expr) : iProp Σ :=
  own γ (gmap_view_auth (V:=leibnizO node) 1%Qp (to_cgraph K : gmap name node)).

Definition let_expr_frag γ (x : name) (n : node) : iProp Σ :=
  own γ (gmap_view_frag (V:=leibnizO node) x DfracDiscarded n).

Definition represents γ (x : name) : name → expr unit → iProp Σ :=
  fix represents (y : name) (yv : expr unit) {struct yv} : iProp Σ :=
    match yv with
    | ENode op av bv => ∃ a b,
        let_expr_frag γ y (op, a, b) ∗ represents a av ∗ represents b bv
    | ELeaf _ =>
        ⌜ x = y ⌝
    end%I.

Definition handler_inv γ (x : name) (xv : nat) (K : let_expr) : iProp Σ :=
  (let_expr_auth γ K ∗
  ⌜ ∀ u, u ∈ K.*1 → variables (interp K u) ⊆ [x] ⌝ ∗
  ([∗ list] u ∈ x :: K.*1,
      u ↦ PairV #(eval (emap' {[x:=xv]} (interp K u))) #0%nat))%I.

Definition env_extension (x : name) (xv : nat) (K : let_expr) : gmap name nat:=
  list_to_map ((λ '(u, _),
    (u, eval (emap' {[x:=xv]} (interp K u)))
  ) <$> K).

Definition backpropagation_inv (x : name) (xv : nat) (K : let_expr) (e : expr unit) : iProp Σ :=
  (∃ K' r,
     ⌜ interp (K ++ K') r = emap (λ _, x) e ⌝ ∗
  (* ⌜ ∀ u, u ∈ (x :: K.*1) → u ∈ K'.*1 → False ⌝ ∗ *)
  (* ⌜ ∀ u, u ∈ K.*1 → variables (interp K u) ⊆ [x] ⌝ ∗ *)
     let E := env_extension x xv K in
     [∗ list] u ∈ x :: K.*1,
        let uv := eval (emap' {[x:=xv]} (interp K u)) in
        let ud := diff' (<[x:=xv]> E) (interp K' r) u in
        u ↦ PairV #uv #ud)%I.

End ghost_theory_defs.


Section ghost_theory_proofs.
Context `{!heapG Σ} `{!cgraphG Σ}.

Global Instance represents_persistent γ x u uv : Persistent (represents γ x u uv).
Proof. revert uv u. induction uv; intros ?; rewrite /ownI; apply _. Qed.

Lemma handler_inv_alloc (x : name) (xv : nat) :
  x ↦ (#xv, #0%nat) ==∗ ∃ γ, handler_inv γ x xv [].
Proof.
  iIntros "Hx". iMod (own_alloc (gmap_view_auth (V:=leibnizO node) 1 ∅))
      as (γ) "Hauth". { apply gmap_view_auth_valid. }
  iModIntro. iExists γ. iFrame. rewrite //= lookup_total_singleton. iFrame.
  iPureIntro; intros u. by rewrite elem_of_nil.
Qed.

Lemma cgraph_lookup γ (G : gmap name node) (x : name) (n : node) :
  own γ (gmap_view_auth (V:=leibnizO node) 1%Qp G) -∗
    own γ (gmap_view_frag (V:=leibnizO node) x DfracDiscarded n) -∗
      ⌜ G !! x = Some n ⌝.
Proof.
 iIntros "Hauth Hfrag".
 by iDestruct (own_valid_2 with "Hauth Hfrag")
    as %[_[_?]]%gmap_view_both_frac_valid_L.
Qed.

Lemma cgraph_update γ (G : gmap name node) (x : name) (n : node) :
  G !! x = None →
    own γ (gmap_view_auth (V:=leibnizO node) 1%Qp G) ==∗
      own γ (gmap_view_auth (V:=leibnizO node) 1%Qp (<[x:=n]>G)) ∗
      own γ (gmap_view_frag (V:=leibnizO node) x DfracDiscarded n).
Proof.
 iIntros (Hlookup) "Hauth". rewrite -own_op.
 iApply own_update. by apply gmap_view_alloc. done.
Qed.

Lemma big_sepL_mapsto_NoDup us : ([∗ list] u ∈ us, ∃ v, u ↦ v) -∗ ⌜ NoDup us ⌝.
Proof.
  iIntros "Hus". iInduction us as [|u us] "IH".
  - iPureIntro. by apply NoDup_nil.
  - iDestruct "Hus" as "[Hu Hus]". iAssert (⌜ u ∉ us ⌝)%I as "%".
    { iIntros (Hin).
      iDestruct (big_sepL_elem_of _ _ _ Hin with "Hus") as "Hu'".
      iDestruct "Hu" as (?) "Hu". iDestruct "Hu'" as (?) "Hu'".
      by iDestruct (mapsto_ne with "Hu Hu'") as "%".
    }
    iDestruct ("IH" with "Hus") as "%". rename H0 into HNoDup.
    iPureIntro. by apply NoDup_cons_2.
Qed.

Lemma handler_inv_NoDup γ x xv K : handler_inv γ x xv K -∗ ⌜ NoDup (x :: K.*1) ⌝.
Proof.
  iIntros "(_ & _ & HK)". iApply big_sepL_mapsto_NoDup.
  iApply (big_sepL_mono with "HK"). iIntros (i u Hin) "Hu".
  by iExists _.
Qed.

Lemma backpropagation_inv_NoDup x xv K e :
  backpropagation_inv x xv K e -∗ ⌜ NoDup (x :: K.*1) ⌝.
Proof.
  iDestruct 1 as (r K') "(_ & HK)". iApply big_sepL_mapsto_NoDup.
  iApply (big_sepL_mono with "HK"). iIntros (i u Hin) "Hu".
  by iExists _.
Qed.

(* FIXME: move this lemma to a proper place (stdpp maybe?). *)
Lemma NoDup_cons_middle {A : Type} (y : A) (xs ys : list A) :
  NoDup (xs ++ y :: ys) →
    NoDup xs ∧
    (y ∉ xs) ∧
    (∀ x, x ∈ xs → x ∉ ys) ∧
    (y ∉ ys) ∧
    NoDup ys.
Proof.
  rewrite cons_middle app_assoc !NoDup_app.
  intros ((HNoDup_xs & Hnot_in_xs & _) & Hnot_in_ys & HNoDup_ys).
  split; [done|]. split; [|split; [|split; [|done]]].
  { intro Hin. by apply (Hnot_in_xs _ Hin), elem_of_list_singleton. }
  { intros x Hin. apply Hnot_in_ys, elem_of_app. by left. }
  { apply Hnot_in_ys, elem_of_app. right. by apply elem_of_list_singleton. }
Qed.

Lemma NoDup_app_11 {A : Type} (xs ys : list A) : NoDup (xs ++ ys) → NoDup xs.
Proof. rewrite NoDup_app. by intros [? _]. Qed.

Lemma NoDup_app_12 {A : Type} (xs ys : list A) : NoDup (xs ++ ys) → ∀ x, x ∈ xs → x ∉ ys.
Proof. rewrite NoDup_app. by intros (_ & ? & _). Qed.

Lemma NoDup_app_13 {A : Type} (xs ys : list A) : NoDup (xs ++ ys) → NoDup ys.
Proof. rewrite NoDup_app. by intros (_ & _ & ?). Qed.
(* ******************************************************** *)

Lemma handler_inv_let_expr_wf_1 γ x xv K us vs u op a b :
  K = us ++ (u, (op, a, b)) :: vs →
    handler_inv γ x xv K -∗ ⌜ a ∉ u :: vs.*1 ⌝.
Proof.
  intros ->. iIntros "Hinv" (Hin).
  iDestruct (handler_inv_NoDup with "Hinv") as %HNoDup.
  iDestruct "Hinv" as "[_ [% _]]". rename H into Hvar. iPureIntro.
  specialize (Hvar u). rewrite fmap_app fmap_cons //= in Hvar, HNoDup.
  apply (NoDup_cons_11 _ _ HNoDup). rewrite elem_of_app. right.
  cut (a = x); [by intros ->|]. apply elem_of_list_singleton.
  have Hin': u ∈ (us.*1 ++ u :: vs.*1). { rewrite elem_of_app elem_of_cons. by right; left. }
  specialize (Hvar Hin'). revert Hvar. rewrite cons_middle app_assoc interp_app;[|
  by specialize (NoDup_cons_middle _ _ _ (NoDup_cons_12 _ _ HNoDup)) as (_&_&_&Hnot_in&_)].
  rewrite interp_snoc decide_True; [|done]. rewrite interp_leaf; [set_solver|]. intro Hin''.
  by apply (NoDup_app_12 _ _ (NoDup_cons_12 _ _ HNoDup) a).
Qed.

Lemma handler_inv_let_expr_wf_2 γ x xv K us vs u op a b :
  K = us ++ (u, (op, a, b)) :: vs →
    handler_inv γ x xv K -∗ ⌜ b ∉ u :: vs.*1 ⌝.
Proof.
  intros ->. iIntros "Hinv" (Hin).
  iDestruct (handler_inv_NoDup with "Hinv") as %HNoDup.
  iDestruct "Hinv" as "[_ [% _]]". rename H into Hvar. iPureIntro.
  specialize (Hvar u). rewrite fmap_app fmap_cons //= in Hvar, HNoDup.
  apply (NoDup_cons_11 _ _ HNoDup). rewrite elem_of_app. right.
  cut (b = x); [by intros ->|]. apply elem_of_list_singleton.
  have Hin': u ∈ (us.*1 ++ u :: vs.*1). { rewrite elem_of_app elem_of_cons. by right; left. }
  specialize (Hvar Hin'). revert Hvar. rewrite cons_middle app_assoc interp_app;[|
  by specialize (NoDup_cons_middle _ _ _ (NoDup_cons_12 _ _ HNoDup)) as (_&_&_&Hnot_in&_)].
  rewrite interp_snoc decide_True; [|done]. rewrite (interp_leaf _ b); [set_solver|]. intro Hin''.
  by apply (NoDup_app_12 _ _ (NoDup_cons_12 _ _ HNoDup) b).
Qed.

Lemma handler_inv_elem_of γ x xv K u op av bv :
  handler_inv γ x xv K -∗ represents γ x u (ENode op av bv) -∗ 
    handler_inv γ x xv K ∗ ∃ a b,
      represents γ x a av ∗ represents γ x b bv ∗ ⌜ (u, (op, a, b)) ∈ K ⌝.
Proof.
  iIntros "[Hauth Hrest]". simpl. iDestruct 1 as (a b) "(Hfrag&Ha&Hb)".
  iDestruct (cgraph_lookup with "Hauth Hfrag") as %Hlkp. iFrame.
  iSplitL "Hrest";[done|]. iExists a, b. iFrame.
  iPureIntro. by apply (elem_of_list_to_map_2 (K:=name) (M:=gmap name)).
Qed.

Lemma handler_inv_elem_of' γ x xv K u uv :
  handler_inv γ x xv K -∗ represents γ x u uv -∗ ⌜ u ∈ x :: K.*1 ⌝.
Proof.
  iIntros "Hinv Hrepr". destruct uv as [op av bv|()].
  { iDestruct (handler_inv_elem_of with "Hinv Hrepr") as "[_ Hin]".
    iDestruct "Hin" as (a b) "(_&_&%)". iPureIntro.
    rewrite elem_of_cons elem_of_list_fmap. right. by exists (u, (op, a, b)).
  }
  { iDestruct "Hrepr" as "->". iPureIntro. apply elem_of_cons. by left. }
Qed.

Lemma handler_inv_agree γ x xv K u uv :
  handler_inv γ x xv K -∗ represents γ x u uv -∗ ⌜ interp K u = emap (λ _, x) uv ⌝.
Proof.
  revert uv u. induction uv as [op av IHa bv IHb|y]; intro u; [|
  by iIntros "HK ->"; iDestruct (handler_inv_NoDup with "HK")
      as %?%NoDup_cons_11%interp_leaf].
  iIntros "HK Hrepr". iDestruct (handler_inv_elem_of with "HK Hrepr") as "[HK Hrepr]".
  iDestruct "Hrepr" as (a b) "(Ha&Hb&%)". rename H into Helem_of. simpl.
  iDestruct (IHa with "HK Ha") as %<-.
  iDestruct (IHb with "HK Hb") as %<-.
  iDestruct (handler_inv_NoDup with "HK") as %HNoDup.
  specialize (elem_of_list_split_r _ _ Helem_of) as [us [vs [HK_eq Hu_not_in]]].
  iDestruct (handler_inv_let_expr_wf_1 with "HK") as %Ha_not_in. { by apply HK_eq. }
  iDestruct (handler_inv_let_expr_wf_2 with "HK") as %Hb_not_in. { by apply HK_eq. }
  iDestruct "HK" as "[_ [% _]]". rename H into Hvar.
  iPureIntro. clear IHa IHb.
  rewrite HK_eq fmap_app fmap_cons //= in HNoDup.
  have HNoDup': NoDup ((x :: us.*1) ++ u :: vs.*1); [done|].
  specialize (NoDup_cons_middle _ _ _ HNoDup') as
    (HNoDup_xs & Hy_not_in1 & Hinter & Hy_not_in2 & HNoDup_ys).
  have Hinterp_u: interp K u = ENode op (interp us a) (interp us b).
  { by rewrite HK_eq cons_middle app_assoc interp_app; [rewrite interp_snoc decide_True|]. }
  by rewrite Hinterp_u HK_eq !interp_app.
Qed.

Lemma handler_inv_fresh_name γ x xv K u v :
  u ↦ v -∗ handler_inv γ x xv K -∗ ⌜ u ∉ x :: K.*1 ⌝.
Proof.
  iIntros "Hu [_ [_ HK]]". iInduction (x :: K.*1) as [|y ys] "IH". 
  { iPureIntro. by apply not_elem_of_nil. }
  { rewrite not_elem_of_cons. simpl.
    iDestruct "HK" as "[Hy HK]". iSplit.
    { by iApply (mapsto_ne with "Hu Hy"). }
    { by iApply ("IH" with "Hu HK"). }
  }
Qed.

Lemma handler_inv_update γ x xv K u op a b av bv :
  u ↦ PairV #(eval (emap' {[x:=xv]} (ENode op (interp K a) (interp K b)))) #0%nat -∗
    handler_inv γ x xv K -∗ represents γ x a av -∗ represents γ x b bv ==∗
      handler_inv γ x xv (K ++ [(u, (op, a, b))]) ∗ represents γ x u (ENode op av bv).
Proof.
  iIntros "Hu Hhandler_inv Ha Hb".
  iDestruct (handler_inv_elem_of' with "Hhandler_inv Ha") as %Ha_in%elem_of_cons.
  iDestruct (handler_inv_elem_of' with "Hhandler_inv Hb") as %Hb_in%elem_of_cons.
  iDestruct (handler_inv_fresh_name with "Hu Hhandler_inv")
      as %[Hneq Hnot_in]%not_elem_of_cons.
  iDestruct (handler_inv_NoDup with "Hhandler_inv") as %[Hnot_in' HNoDup]%NoDup_cons.
  iDestruct "Hhandler_inv" as "[Hauth [% HK]]". rename H into Hvar.
  iMod ((cgraph_update _ _ u (op, a, b)) with "Hauth") as "[Hauth Hfrag]".
  { by apply not_elem_of_list_to_map_1. }
  iModIntro. iSplit; [|iExists a, b; iFrame; by iSplit].
  iClear "Hfrag". iSplitL "Hauth"; [|iSplit;[iPureIntro|]].
  { unfold let_expr_auth, to_cgraph. rewrite -list_to_map_cons.
    rewrite (list_to_map_proper _ (K ++ [(u, (op, a, b))])); [done| |].
    { rewrite fmap_cons //=. apply NoDup_cons. by split. }
    { by apply Permutation_cons_append. }
  }
  { intros v. rewrite fmap_app interp_snoc //=.
    case (decide (u = v)); [intros -> _|intros ??; apply Hvar; set_solver].
    have Hx: (interp K x = ELeaf x); [by apply interp_leaf|]. simpl.
    case Ha_in as [->|Ha_in]; [rewrite Hx|];
    case Hb_in as [->|Hb_in]; [rewrite Hx| |rewrite Hx|]; set_solver.
  }
  { rewrite fmap_app fmap_cons fmap_nil app_comm_cons big_sepL_app.
    iSplitL "HK"; [|by rewrite //= interp_snoc decide_True; [iFrame|]].
    have H: u ∉ x :: K.*1; [set_solver|]. clear Hvar HNoDup Hneq Hnot_in.
    iRevert (H). iInduction (x :: K.*1) as [|y ys] "IH"; [by iIntros (?)|].
    rewrite not_elem_of_cons. iIntros ([Hneq H]). iDestruct "HK" as "[Hy HK]".
    iSplitL "Hy"; [|by iApply ("IH" with "HK")].
    by rewrite interp_snoc decide_False.
  }
Qed.

Lemma env_extension_app x xv K op u a b :
  u ∉ K.*1 →
  let av := eval (emap' {[x:=xv]} (interp K a)) in
  let bv := eval (emap' {[x:=xv]} (interp K b)) in
  env_extension x xv (K ++ [(u, (op, a, b))]) =
   <[u:=eval_op op av bv]> (env_extension x xv K).
Proof.
  intros Hnot_in. simpl. unfold env_extension.
  rewrite fmap_app fmap_cons //= list_to_map_snoc;[|
  rewrite -list_fmap_compose (list_fmap_ext _ fst K K); [|intros (?,?)|]; done].
  rewrite interp_snoc decide_True; [|done]. simpl. f_equiv. f_equiv.
  apply Forall_fmap_ext_1. rewrite Forall_forall. intros (u',uv') Hin. f_equiv.
  rewrite interp_snoc decide_False; [done|]. intros ->. apply Hnot_in.
  rewrite elem_of_list_fmap. by exists (u', uv').
Qed.

Lemma env_extension_app' x xv K op u a b :
  u ∉ x :: K.*1 →
  let av := eval (emap' {[x:=xv]} (interp K a)) in
  let bv := eval (emap' {[x:=xv]} (interp K b)) in
  <[x:=xv]> (env_extension x xv (K ++ [(u, (op, a, b))])) =
   <[u:=eval_op op av bv]> (<[x:=xv]> (env_extension x xv K)).
Proof.
  intros [Hneq Hnot_in]%not_elem_of_cons. simpl.
  rewrite env_extension_app; [|done]. by rewrite insert_commute.
Qed.

Lemma lookup_env_extension x xv K y :
  NoDup K.*1 → y ∈ K.*1 →
  let yv := eval (emap' {[x:=xv]} (interp K y)) in
  (env_extension x xv K) !! y = Some yv.
Proof.
  intros HNoDup Hin. simpl. unfold env_extension.
  apply elem_of_list_to_map_1;[
  rewrite -list_fmap_compose (list_fmap_ext _ fst K K); [|intros (?,?)|]; done|].
  revert Hin. rewrite !elem_of_list_fmap.
  intros [(y',n) [-> Hin]]. by exists (y', n).
Qed.

Lemma lookup_env_extension' x xv K y :
  NoDup (x :: K.*1) → y ∈ x :: K.*1 →
  let yv := eval (emap' {[x:=xv]} (interp K y)) in
  (<[x:=xv]> (env_extension x xv K)) !! y = Some yv.
Proof.
  intros [Hnot_in HNoDup]%NoDup_cons [->|Hin]%elem_of_cons; simpl.
  { by rewrite lookup_insert interp_leaf //= lookup_total_insert. }
  { by rewrite lookup_insert_ne; [apply lookup_env_extension|intros ->]. }
Qed.

(*Lemma handler_inv_backpropagation_inv E e γ x xv K r rv :
  (r ↦ PairV #(eval (emap' {[x:=xv]} (emap (λ _, x) rv))) #0%nat -∗
    EWP e @ E {{_, r ↦ PairV #(eval (emap' {[x:=xv]} (emap (λ _, x) rv))) #1%nat }}) -∗
      handler_inv γ x xv K -∗ represents γ x r rv -∗
        EWP e @ E {{ _, backpropagation_inv x xv K rv }}.
Proof.
  iIntros "He Hhinv Hr".
Qed.*)

End ghost_theory_proofs.


(** Verification. *)

Section verification.
Context `{!heapG Σ} `{!cgraphG Σ}.

Lemma set_diff_spec E x xv xd xd' :
  x ↦ PairV #xv #xd -∗
    EWP set_diff #x #xd' @ E {{ _, x ↦ PairV #xv #xd' }}.
Proof.
  iIntros "Hx". iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (StoreRCtx _)). done.
  iApply (Ectxi_ewp_bind (PairLCtx _)). done.
  iApply (Ectxi_ewp_bind FstCtx). done.
  iApply (ewp_mono' with "[Hx]"). { by iApply (ewp_load with "Hx"). }
  iIntros (y) "[-> Hx]". iModIntro. simpl.
  iApply ewp_pure_step. apply pure_prim_step_Fst. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_pair. iApply ewp_value.
  by iApply (ewp_store with "Hx").
Qed.

Lemma get_diff_spec E x xv xd :
  x ↦ PairV #xv #xd -∗
    EWP get_diff #x @ E {{ y, ⌜ y = #xd ⌝ ∗ x ↦ PairV #xv #xd }}.
  iIntros "Hx".
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind SndCtx). done.
  iApply (ewp_mono' with "[Hx]"). { by iApply (ewp_load with "Hx"). }
  iIntros (y) "[-> Hx]". iModIntro. simpl.
  iApply ewp_pure_step. apply pure_prim_step_Snd. iApply ewp_value.
  by iFrame.
Qed.

Lemma get_val_spec γ x xv K u uv :
  represents γ x u uv -∗
    handler_inv γ x xv K -∗
      EWP get_val #u {{ y,
        ⌜ y = #(eval (emap' {[x:=xv]} (emap (λ _, x) uv))) ⌝ ∗
          handler_inv γ x xv K }}.
Proof.
  iIntros "Hu Hhinv".
  iDestruct (handler_inv_agree with "Hhinv Hu") as %Hinterp.
  iDestruct (handler_inv_elem_of' with "Hhinv Hu") as %Hin.
  iDestruct "Hhinv" as "[Hauth [Hvar HK]]".
  specialize (elem_of_list_split _ _ Hin) as [us [vs HK_eq]].
  rewrite HK_eq. rewrite (big_opL_permutation _ _ (u :: (vs ++ us))); [|
  by rewrite Permutation_app_comm].
  iDestruct "HK" as "[Hu' HK]".
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind FstCtx). done.
  iApply (ewp_mono' with "[Hu']"). { by iApply (ewp_load with "Hu'"). }
  iIntros (y) "[-> Hu']". iModIntro. simpl.
  iApply ewp_pure_step. apply pure_prim_step_Fst. iApply ewp_value.
  rewrite -!Hinterp. iSplit; [done|]. iFrame.
  rewrite HK_eq. rewrite (big_opL_permutation _ (us ++ _) (u :: (vs ++ us))); [|
  by rewrite Permutation_app_comm].
  by iFrame.
Qed.

Lemma mk_spec E (xv : val) :
  ⊢ EWP mk xv @ E {{ y, ∃ (x : name), ⌜ y = #x ⌝ ∗ x ↦ (PairV xv #0%nat) }}.
Proof.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind AllocCtx). done.
  iApply ewp_pure_step. apply pure_prim_step_pair. iApply ewp_value. simpl.
  by iApply ewp_alloc.
Qed.

Lemma return_spec γ x xv K r (e : expr unit) :
  handler_inv γ x xv K -∗ represents γ x r e -∗ 
    EWP set_diff #r #1%nat {{ _, backpropagation_inv x xv K e }}.
Proof.
  iIntros "Hhinv Hrepr".
  iDestruct (handler_inv_agree with "Hhinv Hrepr") as %Hinterp.
  iDestruct (handler_inv_elem_of' with "Hhinv Hrepr") as %[i Hin]%elem_of_list_lookup_1.
  iDestruct (handler_inv_NoDup with "Hhinv") as %HNoDup.
  iDestruct "Hhinv" as "[_ [Hvar HK]]". iClear "Hrepr".
  iDestruct (big_sepL_delete' _ _ _ _ Hin with "HK") as "[Hu HK]".
  iApply (ewp_mono' with "[Hu]"). { by iApply (set_diff_spec with "Hu"). }
  iIntros (_) "Hu !>". iExists [], r. rewrite app_nil_r Hinterp.
  (* iSplit; [done|]. iSplit; [iIntros (?); by rewrite elem_of_nil|]. *) iSplit; [done|].
  rewrite (big_sepL_delete' (λ _ u, u ↦ (_, #(diff' _ _ _)))%I _ _ _ Hin).
  iSplitL "Hu"; [by rewrite //= Hinterp diff_var_eq|].
  iApply (big_sepL_mono with "HK").
  iIntros (k v Hin') "Hv". iIntros (Hneq). iSpecialize ("Hv" $! Hneq).
  rewrite //= diff_var_neq; [done|]. intros ->.
  by destruct (NoDup_lookup _ _ _ _ HNoDup Hin Hin').
Qed.

Lemma add_update_spec_1 x xv K u a e :
  NoDup (x :: K.*1) → a ∈ x :: K.*1 → u ∉ x :: K.*1 →
    backpropagation_inv x xv (K ++ [(u, (Add, a, a))]) e -∗
      EWP let: "ud" := get_diff #u in
          set_diff #a ((get_diff #a) + "ud");;
          set_diff #a ((get_diff #a) + "ud")
      {{_, backpropagation_inv x xv K e }}.
Proof.
  intros HNoDup Hin Hnot_in.
  iDestruct 1 as (K' r) "(% & HK)". rename H into Hr.
  rewrite fmap_app fmap_cons app_comm_cons big_opL_app. iDestruct "HK" as "[HK [Hu _]]".
  assert (∃ l, l = (x :: K.*1)) as [l Hl]; [by eauto|].
  destruct (elem_of_list_lookup_1 _ _ Hin) as [i Hlkp].
  iDestruct (big_sepL_delete' _ _ _ _ Hlkp with "HK") as "[Ha HK]".
  iApply (Ectxi_ewp_bind (AppRCtx _)). done. rewrite -Hl //=.
  iApply (ewp_mono' with "[Hu]"). { by iApply (get_diff_spec with "Hu"). }
  iIntros (v) "[-> Hu]". iModIntro.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (BinOpLCtx _ _)). done.
  iApply (ewp_mono' with "[Ha]"). { by iApply (get_diff_spec with "Ha"). }
  iIntros (y) "[-> Ha]". iModIntro. simpl.
  iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value.
  iApply (ewp_mono' with "[Ha]"). { by iApply (set_diff_spec with "Ha"). }
  iIntros (v) "Ha". iModIntro.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (BinOpLCtx _ _)). done.
  iApply (ewp_mono' with "[Ha]"). { by iApply (get_diff_spec with "Ha"). }
  iIntros (y) "[-> Ha]". iModIntro. simpl.
  iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value.
  iApply (ewp_mono' with "[Ha]"). { by iApply (set_diff_spec with "Ha"). }
  clear v. iIntros (v) "Ha". iModIntro.
  iExists ((u, (Add, a, a)) :: K'), r.
  iSplit; [iPureIntro; by rewrite cons_middle app_assoc Hr|].
  rewrite (big_sepL_delete' _ _ _ _ Hlkp).
  have Hneq: a ≠ u. { by intros ->. }
  iClear "Hu". iSplitL "Ha"; [|rewrite Hl; iApply (big_sepL_mono with "HK")].
  { rewrite interp_snoc decide_False; [|done].
    rewrite (diff_interp_cons (eval (emap' {[x:=xv]} (interp K a)))
                              (eval (emap' {[x:=xv]} (interp K a))));
    try (by apply lookup_env_extension'); try done.
    rewrite -env_extension_app'; [|done]. simpl. rewrite diff_var_eq //=.
    rewrite Nat.add_0_r Nat.add_assoc !Nat2Z.inj_add. done.
  }
  { intros k y Hlkp'. simpl. iIntros "Hy". iIntros (Hneq').
    have Hneq'': u ≠ y; [
    intros ->; by apply Hnot_in, (elem_of_list_lookup_2 _ k)|].
    iSpecialize ("Hy" $! Hneq'). rewrite interp_snoc decide_False; [|done].
    rewrite (diff_interp_cons (eval (emap' {[x:=xv]} (interp K a)))
                              (eval (emap' {[x:=xv]} (interp K a))));
    try (by apply lookup_env_extension'); try done.
    rewrite -env_extension_app'; [|done]. simpl. rewrite diff_var_neq //=;[|
    by intros ->; destruct (NoDup_lookup _ _ _ _ HNoDup Hlkp Hlkp')].
    rewrite Nat.add_0_r. done.
  }
Qed.

Lemma add_update_spec_2 x xv K u a b e :
  NoDup (x :: K.*1) → a ∈ x :: K.*1 → b ∈ x :: K.*1 → a ≠ b → u ∉ x :: K.*1 →
    backpropagation_inv x xv (K ++ [(u, (Add, a, b))]) e -∗
      EWP let: "ud" := get_diff #u in
          set_diff #a ((get_diff #a) + "ud");;
          set_diff #b ((get_diff #b) + "ud")
      {{_, backpropagation_inv x xv K e }}.
Proof.
  intros HNoDup Ha_in Hb_in Hab Hnot_in.
  iDestruct 1 as (K' r) "(% & HK)". rename H into Hr.
  rewrite fmap_app fmap_cons app_comm_cons big_opL_app. iDestruct "HK" as "[HK [Hu _]]".
  assert (∃ l, l = (x :: K.*1)) as [l Hl]; [by eauto|].
  destruct (elem_of_list_lookup_1 _ _ Ha_in) as [i Hlkp_a].
  destruct (elem_of_list_lookup_1 _ _ Hb_in) as [j Hlkp_b].
  iDestruct (big_sepL_delete' _ _ _ _ Hlkp_a with "HK") as "[Ha HK]".
  iDestruct (big_sepL_delete' _ _ _ _ Hlkp_b with "HK") as "[Hb HK]".
  have Hij: i ≠ j; [
  by intros ->; cut (Some a = Some b); [inversion 1|rewrite -Hlkp_a -Hlkp_b]|].
  iSpecialize ("Hb" with "[]"); [done|].
  iApply (Ectxi_ewp_bind (AppRCtx _)). done. rewrite -Hl //=.
  iApply (ewp_mono' with "[Hu]"). { by iApply (get_diff_spec with "Hu"). }
  iIntros (v) "[-> Hu]". iModIntro.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (BinOpLCtx _ _)). done.
  iApply (ewp_mono' with "[Ha]"). { by iApply (get_diff_spec with "Ha"). }
  iIntros (y) "[-> Ha]". iModIntro. simpl.
  iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value.
  iApply (ewp_mono' with "[Ha]"). { by iApply (set_diff_spec with "Ha"). }
  iIntros (v) "Ha". iModIntro.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (BinOpLCtx _ _)). done.
  iApply (ewp_mono' with "[Hb]"). { by iApply (get_diff_spec with "Hb"). }
  iIntros (y) "[-> Hb]". iModIntro. simpl.
  iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value.
  iApply (ewp_mono' with "[Hb]"). { by iApply (set_diff_spec with "Hb"). }
  clear v. iIntros (v) "Hb". iModIntro.
  iExists ((u, (Add, a, b)) :: K'), r.
  iSplit; [iPureIntro; by rewrite cons_middle app_assoc Hr|].
  rewrite (big_sepL_delete' _ _ _ _ Hlkp_a).
  rewrite (big_sepL_delete' _ _ _ _ Hlkp_b).
  have Hau: a ≠ u. { by intros ->. }
  have Hbu: b ≠ u. { by intros ->. }
  iClear "Hu". rewrite !interp_snoc !decide_False; try done.
  rewrite !(diff_interp_cons (eval (emap' {[x:=xv]} (interp K a)))
                             (eval (emap' {[x:=xv]} (interp K b))));
    try (by apply lookup_env_extension'); try done.
  rewrite -!env_extension_app'; [|done].
  iSplitL "Ha"; [|iSplitL "Hb"; [|rewrite Hl; iApply (big_sepL_mono with "HK")]].
  { by simpl; rewrite diff_var_eq diff_var_neq; [
    rewrite Nat.add_0_r Nat.add_assoc Nat.add_0_r !Nat2Z.inj_add|].
  }
  { iIntros (_). by simpl; rewrite diff_var_eq diff_var_neq; [
    rewrite Nat.add_0_l Nat.add_assoc Nat.add_0_r !Nat2Z.inj_add|].
  }
  { intros k y Hlkp'. simpl. iIntros "Hy". iIntros (Hkj Hki).
    iSpecialize ("Hy" $! Hkj Hki).
    have Hneq'': u ≠ y; [
    intros ->; by apply Hnot_in, (elem_of_list_lookup_2 _ k)|].
    rewrite interp_snoc decide_False; [|done].
    rewrite (diff_interp_cons (eval (emap' {[x:=xv]} (interp K a)))
                              (eval (emap' {[x:=xv]} (interp K b))));
    try (by apply lookup_env_extension'); try done.
    rewrite -env_extension_app'; [|done]. simpl.
    rewrite diff_var_neq //=;[|
    by intros ->; destruct (NoDup_lookup _ _ _ _ HNoDup Hlkp_a Hlkp')].
    rewrite diff_var_neq //=;[|
    by intros ->; destruct (NoDup_lookup _ _ _ _ HNoDup Hlkp_b Hlkp')].
    rewrite Nat.add_0_r. done. 
  }
Qed.

Lemma mult_update_spec_1 x xv K u a e :
  let av := eval (emap' {[x:=xv]} (interp K a)) in
  NoDup (x :: K.*1) → a ∈ x :: K.*1 → u ∉ x :: K.*1 →
    backpropagation_inv x xv (K ++ [(u, (Mult, a, a))]) e -∗
      EWP let: "ud" := get_diff #u in
          set_diff #a ((get_diff #a) + (#av * "ud"));;
          set_diff #a ((get_diff #a) + (#av * "ud"))
      {{_, backpropagation_inv x xv K e }}.
Proof.
  simpl. intros HNoDup Hin Hnot_in.
  iDestruct 1 as (K' r) "(% & HK)". rename H into Hr.
  rewrite fmap_app fmap_cons app_comm_cons big_opL_app. iDestruct "HK" as "[HK [Hu _]]".
  assert (∃ l, l = (x :: K.*1)) as [l Hl]; [by eauto|].
  destruct (elem_of_list_lookup_1 _ _ Hin) as [i Hlkp].
  iDestruct (big_sepL_delete' _ _ _ _ Hlkp with "HK") as "[Ha HK]".
  iApply (Ectxi_ewp_bind (AppRCtx _)). done. rewrite -Hl //=.
  iApply (ewp_mono' with "[Hu]"). { by iApply (get_diff_spec with "Hu"). }
  iIntros (v) "[-> Hu]". iModIntro.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (BinOpRCtx _ _)). done.
  iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value. simpl.
  iApply (Ectxi_ewp_bind (BinOpLCtx _ _)). done.
  iApply (ewp_mono' with "[Ha]"). { by iApply (get_diff_spec with "Ha"). }
  iIntros (y) "[-> Ha]". iModIntro. simpl.
  iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value.
  iApply (ewp_mono' with "[Ha]"). { by iApply (set_diff_spec with "Ha"). }
  iIntros (v) "Ha". iModIntro.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (BinOpRCtx _ _)). done.
  iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value. simpl.
  iApply (Ectxi_ewp_bind (BinOpLCtx _ _)). done.
  iApply (ewp_mono' with "[Ha]"). { by iApply (get_diff_spec with "Ha"). }
  iIntros (y) "[-> Ha]". iModIntro. simpl.
  iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value.
  iApply (ewp_mono' with "[Ha]"). { by iApply (set_diff_spec with "Ha"). }
  clear v. iIntros (v) "Ha". iModIntro.
  iExists ((u, (Mult, a, a)) :: K'), r.
  iSplit; [iPureIntro; by rewrite cons_middle app_assoc Hr|].
  rewrite (big_sepL_delete' _ _ _ _ Hlkp).
  have Hau: a ≠ u. { by intros ->. }
  iClear "Hu". rewrite !interp_snoc !decide_False; try done.
  rewrite !(diff_interp_cons (eval (emap' {[x:=xv]} (interp K a)))
                             (eval (emap' {[x:=xv]} (interp K a))));
    try (by apply lookup_env_extension'); try done.
  rewrite -!env_extension_app'; [|done].
  iSplitL "Ha"; [|rewrite Hl; iApply (big_sepL_mono with "HK")].
  { rewrite //= diff_var_eq lookup_total_alt lookup_env_extension' //=.
    rewrite Nat.mul_1_r Nat.add_0_r Nat.mul_add_distr_r Nat.add_assoc.
    rewrite !Nat2Z.inj_add Nat2Z.inj_mul. done.
  }
  { intros k y Hlkp'. simpl. iIntros "Hy". iIntros (Hki).
    iSpecialize ("Hy" $! Hki). have Hneq'': u ≠ y; [
    intros ->; by apply Hnot_in, (elem_of_list_lookup_2 _ k)|].
    rewrite interp_snoc decide_False; [|done].
    rewrite (diff_interp_cons (eval (emap' {[x:=xv]} (interp K a)))
                              (eval (emap' {[x:=xv]} (interp K a))));
    try (by apply lookup_env_extension'); try done.
    rewrite -env_extension_app'; [|done]. simpl.
    rewrite diff_var_neq //=;[|
    by intros ->; destruct (NoDup_lookup _ _ _ _ HNoDup Hlkp Hlkp')].
    rewrite Nat.mul_0_r Nat.mul_0_l Nat.add_0_r. done. 
  }
Qed.

Lemma mult_update_spec_2 x xv K u a b e :
  let av := eval (emap' {[x:=xv]} (interp K a)) in
  let bv := eval (emap' {[x:=xv]} (interp K b)) in
  NoDup (x :: K.*1) → a ∈ x :: K.*1 → b ∈ x :: K.*1 → a ≠ b → u ∉ x :: K.*1 →
    backpropagation_inv x xv (K ++ [(u, (Mult, a, b))]) e -∗
      EWP let: "ud" := get_diff #u in
          set_diff #a ((get_diff #a) + (#bv * "ud"));;
          set_diff #b ((get_diff #b) + (#av * "ud"))
      {{_, backpropagation_inv x xv K e }}.
Proof.
  simpl. intros HNoDup Ha_in Hb_in Hab Hnot_in.
  iDestruct 1 as (K' r) "(% & HK)". rename H into Hr.
  rewrite fmap_app fmap_cons app_comm_cons big_opL_app. iDestruct "HK" as "[HK [Hu _]]".
  assert (∃ l, l = (x :: K.*1)) as [l Hl]; [by eauto|].
  destruct (elem_of_list_lookup_1 _ _ Ha_in) as [i Hlkp_a].
  destruct (elem_of_list_lookup_1 _ _ Hb_in) as [j Hlkp_b].
  iDestruct (big_sepL_delete' _ _ _ _ Hlkp_a with "HK") as "[Ha HK]".
  iDestruct (big_sepL_delete' _ _ _ _ Hlkp_b with "HK") as "[Hb HK]".
  have Hij: i ≠ j; [
  by intros ->; cut (Some a = Some b); [inversion 1|rewrite -Hlkp_a -Hlkp_b]|].
  iSpecialize ("Hb" with "[]"); [done|].
  iApply (Ectxi_ewp_bind (AppRCtx _)). done. rewrite -Hl //=.
  iApply (ewp_mono' with "[Hu]"). { by iApply (get_diff_spec with "Hu"). }
  iIntros (v) "[-> Hu]". iModIntro.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (BinOpRCtx _ _)). done.
  iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value. simpl.
  iApply (Ectxi_ewp_bind (BinOpLCtx _ _)). done.
  iApply (ewp_mono' with "[Ha]"). { by iApply (get_diff_spec with "Ha"). }
  iIntros (y) "[-> Ha]". iModIntro. simpl.
  iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value.
  iApply (ewp_mono' with "[Ha]"). { by iApply (set_diff_spec with "Ha"). }
  iIntros (v) "Ha". iModIntro.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (BinOpRCtx _ _)). done.
  iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value. simpl.
  iApply (Ectxi_ewp_bind (BinOpLCtx _ _)). done.
  iApply (ewp_mono' with "[Hb]"). { by iApply (get_diff_spec with "Hb"). }
  iIntros (y) "[-> Hb]". iModIntro. simpl.
  iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value.
  iApply (ewp_mono' with "[Hb]"). { by iApply (set_diff_spec with "Hb"). }
  clear v. iIntros (v) "Hb". iModIntro.
  iExists ((u, (Mult, a, b)) :: K'), r.
  iSplit; [iPureIntro; by rewrite cons_middle app_assoc Hr|].
  rewrite (big_sepL_delete' _ _ _ _ Hlkp_a).
  rewrite (big_sepL_delete' _ _ _ _ Hlkp_b).
  have Hau: a ≠ u. { by intros ->. }
  have Hbu: b ≠ u. { by intros ->. }
  iClear "Hu". rewrite !interp_snoc !decide_False; try done.
  rewrite !(diff_interp_cons (eval (emap' {[x:=xv]} (interp K a)))
                             (eval (emap' {[x:=xv]} (interp K b))));
    try (by apply lookup_env_extension'); try done.
  rewrite -!env_extension_app'; [|done].
  iSplitL "Ha"; [|iSplitL "Hb"; [|rewrite Hl; iApply (big_sepL_mono with "HK")]].
  { rewrite //= diff_var_eq diff_var_neq //=.
    rewrite lookup_total_alt lookup_env_extension' //=.
    rewrite Nat.mul_0_r !Nat.add_0_r !Nat2Z.inj_add Nat2Z.inj_mul. done.
  }
  { iIntros (_). rewrite //= diff_var_eq diff_var_neq //=.
    rewrite lookup_total_alt lookup_env_extension' //=.
    rewrite Nat.mul_1_r !Nat2Z.inj_add Nat2Z.inj_mul. done.
  }
  { intros k y Hlkp'. simpl. iIntros "Hy". iIntros (Hkj Hki).
    iSpecialize ("Hy" $! Hkj Hki). have Hneq'': u ≠ y; [
    intros ->; by apply Hnot_in, (elem_of_list_lookup_2 _ k)|].
    rewrite interp_snoc decide_False; [|done].
    rewrite (diff_interp_cons (eval (emap' {[x:=xv]} (interp K a)))
                              (eval (emap' {[x:=xv]} (interp K b))));
    try (by apply lookup_env_extension'); try done.
    rewrite -env_extension_app'; [|done]. simpl.
    rewrite diff_var_neq //=;[|
    by intros ->; destruct (NoDup_lookup _ _ _ _ HNoDup Hlkp_a Hlkp')].
    rewrite diff_var_neq //=;[|
    by intros ->; destruct (NoDup_lookup _ _ _ _ HNoDup Hlkp_b Hlkp')].
    rewrite Nat.mul_0_r Nat.mul_0_l Nat.add_0_r. done. 
  }
Qed.

Lemma run_spec γ x xv (client : val) K (e : expr unit) :
  EWP client #() <| AD_prot (represents γ x) |> {{ y,
    ∃ (r : name), ⌜ y = #r ⌝ ∗ represents γ x r e }} -∗
      handler_inv γ x xv K -∗
        EWP run client {{ _, backpropagation_inv x xv K e }}.
Proof.
  iIntros "Hclient Hhandler".
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (ewp_bind (ConsCtx (AppRCtx _) EmptyCtx)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply (ewp_bind (ConsCtx (AppLCtx _) (ConsCtx (AppRCtx _) EmptyCtx))). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply (ewp_deep_try_with with "Hclient").
  iLöb as "IH" forall (γ K).

  (* Return branch. *)
  rewrite deep_handler_unfold. iSplit.
  { iClear "IH". iIntros (v). iDestruct 1 as (r) "[-> Hrepr]". iNext.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (return_spec with "Hhandler Hrepr").
  }

  (* Effect branch. *)
  { iIntros (v k) "Hprot". iNext.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    rewrite AD_agreement. iDestruct "Hprot" as (op a b av bv) "(-> & [#Ha #Hb] & Hk)".
    case op.

    (* Add. *)
    { iDestruct (handler_inv_agree with "Hhandler Ha") as %Hinterp_a.
      iDestruct (handler_inv_agree with "Hhandler Hb") as %Hinterp_b.
      iDestruct (handler_inv_elem_of' with "Hhandler Ha") as %Ha_in.
      iDestruct (handler_inv_elem_of' with "Hhandler Hb") as %Hb_in.
      iDestruct (handler_inv_NoDup with "Hhandler") as %HNoDup.
      iApply ewp_pure_step. apply pure_prim_step_case_InjL.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_Fst. iApply ewp_value. simpl.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_Snd. iApply ewp_value. simpl.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply (Ectxi_ewp_bind (BinOpRCtx _ _)). done.
      iApply (ewp_mono' with "[Hhandler]").
      { by iApply (get_val_spec with "Hb Hhandler"). }
      iIntros (y) "[-> Hhandler]". iModIntro. simpl.
      iApply (Ectxi_ewp_bind (BinOpLCtx _ _)). done.
      iApply (ewp_mono' with "[Hhandler]").
      { by iApply (get_val_spec with "Ha Hhandler"). }
      iIntros (y) "[-> Hhandler]". iModIntro. simpl.
      iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value.
      iApply ewp_mono'. { by iApply mk_spec. }
      iIntros (y). iDestruct 1 as (u) "[-> Hu]".
      iDestruct (handler_inv_fresh_name with "Hu Hhandler") as %Hu_not_in.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done. simpl.
      iMod (handler_inv_update _ x xv K u Add a b av bv with "[Hu] Hhandler Ha Hb")
        as "[Hhandler #Hu]"; [by rewrite Hinterp_a Hinterp_b //= Nat2Z.inj_add|].

      (* Continuation. *)
      iModIntro. iApply (ewp_mono' with "[Hhandler Hk]").
      { iApply ("Hk" with "Hu"). by iApply ("IH" with "Hhandler"). }
      iClear "IH".

      iIntros (v) "Hback_inv". iModIntro.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      case (decide (a = b)) as [->|Hab];[
      by iApply (add_update_spec_1 with "Hback_inv")|
      by iApply (add_update_spec_2 with "Hback_inv")].
    }

    (* Mult. *)
    { iDestruct (handler_inv_agree with "Hhandler Ha") as %Hinterp_a.
      iDestruct (handler_inv_agree with "Hhandler Hb") as %Hinterp_b.
      iDestruct (handler_inv_elem_of' with "Hhandler Ha") as %Ha_in.
      iDestruct (handler_inv_elem_of' with "Hhandler Hb") as %Hb_in.
      iDestruct (handler_inv_NoDup with "Hhandler") as %HNoDup.
      iApply ewp_pure_step. apply pure_prim_step_case_InjR.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_Fst. iApply ewp_value. simpl.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_Snd. iApply ewp_value. simpl.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply (ewp_mono' with "[Hhandler]").
      { by iApply (get_val_spec with "Ha Hhandler"). }
      iIntros (y) "[-> Hhandler]". iModIntro. simpl.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply (ewp_mono' with "[Hhandler]").
      { by iApply (get_val_spec with "Hb Hhandler"). }
      iIntros (y) "[-> Hhandler]". iModIntro. simpl.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply ewp_pure_step. by apply pure_prim_step_binop. iApply ewp_value.
      iApply ewp_mono'. { by iApply mk_spec. }
      iIntros (y). iDestruct 1 as (u) "[-> Hu]". simpl.
      iDestruct (handler_inv_fresh_name with "Hu Hhandler") as %Hu_not_in.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done. simpl.
      iMod (handler_inv_update _ x xv K u Mult a b av bv with "[Hu] Hhandler Ha Hb")
        as "[Hhandler #Hu]"; [by rewrite Hinterp_a Hinterp_b //= Nat2Z.inj_mul|].

      (* Continuation. *)
      iModIntro. iApply (ewp_mono' with "[Hhandler Hk]").
      { iApply ("Hk" with "Hu"). by iApply ("IH" with "Hhandler"). }
      iClear "IH".


      iIntros (v) "Hback_inv". iModIntro.
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      rewrite -Hinterp_a -Hinterp_b.
      case (decide (a = b)) as [->|Hab];[
      by iApply (mult_update_spec_1 with "Hback_inv")|
      by iApply (mult_update_spec_2 with "Hback_inv")].
    }
  }
Qed.

Lemma grad_spec (n : nat) (f : val) (e : expr unit) :
  (∀ (represents : name → expr unit → iProp Σ) (x : name),
    represents x (ELeaf ()) -∗
      EWP f #x <| AD_prot represents |> {{ y,
        ∃ (r : name), ⌜ y = #r ⌝ ∗ represents r e }})
    -∗
  EWP grad f #n {{ y, ⌜ y = #(diff (λ _, n) e tt) ⌝ }}.
Proof.
  iIntros "f_spec".
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_mono'. { by iApply mk_spec. }
  iIntros (y). iDestruct 1 as (x) "[-> Hx]". iModIntro. simpl.
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply (Ectxi_ewp_bind (AppRCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
  iApply (ewp_mono' with "[f_spec Hx]").
  { iApply fupd_ewp. iMod (handler_inv_alloc with "Hx") as (γ) "Hhandler".
    iModIntro. iApply (run_spec with "[f_spec] Hhandler").
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    by iApply "f_spec".
  }
  { iIntros (?). iDestruct 1 as (K' r) "[% [Hx _]]". rename H into Hr. iModIntro.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec. iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (ewp_mono' with "[Hx]"). { by iApply (get_diff_spec with "Hx"). }
    iIntros (y) "[-> _]". iPureIntro. rewrite Hr.
    unfold env_extension, diff'. simpl.
    rewrite (diff_emap unit name (λ _, x) _ e tt); [|by intros ()].
    do 3 f_equiv. apply diff_ext. simpl. intros () _.
    by rewrite lookup_total_alt lookup_insert.
  }
Qed.

End verification.
