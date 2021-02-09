(* ieff.v

   In this theory, we define the domain of protocols [iEff Σ] and
   we give the translation of the main protocol operators into
   the semantic model. For instance, the empty protocol [iEff_bottom]
   and the sum of protocols [iEff_sum] are both defined here.

   Towards the end of the file, we define the notion of protocol
   ordering and prove some of its basic properties.
*)

From iris.proofmode  Require Import tactics.
From iris.base_logic Require Export lib.iprop.
From iris.algebra    Require Import excl_auth.
From iris.base_logic Require Import lib.own.
From hazel           Require Import lib lang.

Set Default Proof Using "Type".


(** * Setup of Iris's cameras. *)

Class ieffG Σ :=
  ieffG_authG :>
    inG Σ (excl_authR (laterO (valO -d> (valO -d> iPropO Σ) -n> iPropO Σ))).

Definition ieffΣ := #[
  GFunctor (authRF (optionURF (exclRF (laterOF (valO -d> (valO -d> idOF) -n> idOF)))))
].

Instance subG_ieffΣ {Σ} : subG ieffΣ Σ → ieffG Σ.
Proof. solve_inG. Qed.


(** * Protocols. *)

Section iEff.
  Set Primitive Projections.
  Record iEff Σ := IEff {
    iEff_car : (val -d> (val -d> iPropO Σ) -n> iPropO Σ)
  }.
End iEff.
Arguments IEff {_} _.
Arguments iEff_car {_} _.

Declare Scope ieff_scope.
Delimit Scope ieff_scope with ieff.
Bind Scope ieff_scope with iEff.
Local Open Scope ieff.

Instance iEff_inhabited {Σ} : Inhabited (iEff Σ) := populate (IEff inhabitant).

Section ieff_ofe.
  Context {Σ : gFunctors}.

  Instance iEff_equiv : Equiv (iEff Σ) := λ e1 e2,
    iEff_car e1 ≡ iEff_car e2.
  Instance iEff_dist : Dist (iEff Σ) := λ n e1 e2,
    iEff_car e1 ≡{n}≡ iEff_car e2.

  Lemma iEff_ofe_mixin : OfeMixin (iEff Σ).
  Proof. by apply (iso_ofe_mixin iEff_car). Qed.
  Canonical Structure iEffO := Ofe (iEff Σ) iEff_ofe_mixin.

  Global Instance iEff_cofe : Cofe iEffO.
  Proof. by apply (iso_cofe IEff iEff_car). Qed.
End ieff_ofe.

Global Instance IEff_ne {Σ} : NonExpansive (IEff (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance IEff_proper {Σ} : Proper ((≡) ==> (≡)) (IEff (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance iEff_car_ne {Σ} : NonExpansive (iEff_car (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance iEff_car_proper {Σ} : Proper ((≡) ==> (≡)) (iEff_car (Σ:=Σ)).
Proof. by intros ???. Qed.

Lemma iEff_equivI' {Σ} `{!BiInternalEq SPROP} (e1 e2 : iEff Σ) :
  e1 ≡ e2 ⊣⊢@{SPROP} iEff_car e1 ≡ iEff_car e2.
Proof.
  apply (anti_symm _).
  - by apply f_equivI, iEff_car_ne.
  - destruct e1; destruct e2. simpl.
    by apply f_equivI, IEff_ne.
Qed.

Lemma iEff_equivI {Σ} `{!BiInternalEq SPROP} (e1 e2 : iEff Σ) :
  e1 ≡ e2 ⊣⊢@{SPROP} ∀ v q, iEff_car e1 v q ≡ iEff_car e2 v q.
Proof.
  trans (iEff_car e1 ≡ iEff_car e2 : SPROP)%I.
  - by apply iEff_equivI'.
  - rewrite discrete_fun_equivI. f_equiv=>v.
    by apply ofe_morO_equivI.
Qed.


(** * Operators. *)

(* iEff_bottom. *)
Instance iEff_bottom {Σ} : Bottom (iEff Σ) := IEff (λ _, λne _, False%I).

Program Definition iEffPre_base_def {Σ}
  (v : val) (P : iProp Σ) (Q : val -d> iPropO Σ) : iEff Σ
  := IEff (λ v', λne Q', ⌜ v = v' ⌝ ∗ P ∗ (∀ w, Q w -∗ Q' w))%I.
Next Obligation. intros ??? ??? ???. repeat f_equiv. by apply H. Qed.
Definition iEffPre_base_aux : seal (@iEffPre_base_def). by eexists. Qed.
Definition iEffPre_base := iEffPre_base_aux.(unseal).
Definition iEffPre_base_eq : @iEffPre_base = @iEffPre_base_def :=
  iEffPre_base_aux.(seal_eq).
Arguments iEffPre_base {_} _%V _%I _%ieff.
Instance: Params (@iEffPre_base) 3 := {}.

Program Definition iEffPre_exist_def {Σ A} (e : A → iEff Σ) : iEff Σ :=
  IEff (λ v', λne q', ∃ a, iEff_car (e a) v' q')%I.
Next Obligation. solve_proper. Qed.
Definition iEffPre_exist_aux : seal (@iEffPre_exist_def). by eexists. Qed.
Definition iEffPre_exist := iEffPre_exist_aux.(unseal).
Definition iEffPre_exist_eq : @iEffPre_exist = @iEffPre_exist_def :=
  iEffPre_exist_aux.(seal_eq).
Arguments iEffPre_exist {_ _} _%ieff.
Instance: Params (@iEffPre_exist) 3 := {}.

Definition iEffPre_texist {Σ} {TT : tele} (e : TT → iEff Σ) : iEff Σ :=
  tele_fold (@iEffPre_exist Σ) (λ x, x) (tele_bind e).
Arguments iEffPre_texist {_ _} _%ieff /.

Definition iEffPost_base_def {Σ} (w : val) (Q : iProp Σ) : val -d> iPropO Σ
  := (λ w', ⌜ w = w' ⌝ ∗ Q)%I.
Definition iEffPost_base_aux : seal (@iEffPost_base_def). by eexists. Qed.
Definition iEffPost_base := iEffPost_base_aux.(unseal).
Definition iEffPost_base_eq : @iEffPost_base = @iEffPost_base_def :=
  iEffPost_base_aux.(seal_eq).
Arguments iEffPost_base {_} _%V _%I.
Instance: Params (@iEffPost_base) 2 := {}.

Program Definition iEffPost_exist_def {Σ A}
  (e : A → (val -d> iPropO Σ)) : val -d> iPropO Σ :=
  (λ w', ∃ a, e a w')%I.
Definition iEffPost_exist_aux : seal (@iEffPost_exist_def). by eexists. Qed.
Definition iEffPost_exist := iEffPost_exist_aux.(unseal).
Definition iEffPost_exist_eq : @iEffPost_exist = @iEffPost_exist_def :=
  iEffPost_exist_aux.(seal_eq).
Arguments iEffPost_exist {_ _} _%ieff.
Instance: Params (@iEffPost_exist) 2 := {}.

Definition iEffPost_texist {Σ} {TT : tele}
  (e : TT → (val -d> iPropO Σ)) : val -d> iPropO Σ :=
  tele_fold (@iEffPost_exist Σ) (λ x, x) (tele_bind e).
Arguments iEffPost_texist {_ _} _%ieff /.

(* Notation. *)
Notation "'!' v {{ P } } ; Q'" := (iEffPre_base v P Q')
  (at level 200, v at level 20, right associativity,
   format "'!' v  {{  P  } } ; Q'") : ieff_scope.

Notation "'?' w {{ Q } }" := (iEffPost_base w Q)
  (at level 200, w at level 20, right associativity,
   format "'?' w  {{  Q  } }") : ieff_scope.

Notation ">> x .. y >> e" := 
  (iEffPre_exist (λ x, .. (iEffPre_exist (λ y, e)) .. )%ieff)
  (at level 200, x binder, y binder, right associativity,
   format ">>  x  ..  y >>  e") : ieff_scope.

Notation "<< x .. y << e" := 
  (iEffPost_exist (λ x, .. (iEffPost_exist (λ y, e)) .. )%ieff)
  (at level 200, x binder, y binder, right associativity,
   format "<<  x  ..  y <<  e") : ieff_scope.

Notation "'>>..' x .. y >> e" := 
  (iEffPre_texist (λ x, .. (iEffPre_texist (λ y, e)) .. )%ieff)
  (at level 200, x binder, y binder, right associativity,
   format ">>..  x  ..  y >>  e") : ieff_scope.

Notation "'<<..' x .. y << e" := 
  (iEffPost_texist (λ x, .. (iEffPost_texist (λ y, e)) .. )%ieff)
  (at level 200, x binder, y binder, right associativity,
   format "<<..  x  ..  y <<  e") : ieff_scope.

(* Test. *)
(* Check (λ Σ P Q, (>> v >> ! v {{ P }} ; << w << ? w {{ Q }})).*)

Lemma iEffPre_texist_eq {Σ} {TT : tele} v p (e : TT → iEff Σ) :
  iEff_car (>>.. x >> (e x))%ieff v p ⊣⊢ (∃.. x, iEff_car (e x) v p).
Proof.
  rewrite /iEffPre_texist iEffPre_exist_eq.
  induction TT as [|T TT IH]; simpl; [done|]. f_equiv=> x. by apply IH.
Qed.

Lemma iEffPost_texist_eq {Σ} {TT : tele} w (e : TT → _ -d> iPropO Σ) :
  (<<.. y << (e y))%ieff w ⊣⊢ (∃.. y, (e y) w).
Proof.
  rewrite /iEffPost_texist iEffPost_exist_eq.
  induction TT as [|T TT IH]; simpl; [done|].
  rewrite /iEffPost_exist_def. f_equiv=>x. by apply IH.
Qed.

Lemma iEff_tele_eq {Σ} {TT1 TT2 : tele}
  (v : TT1 →       val) (P : TT1 →       iProp Σ)
  (w : TT1 → TT2 → val) (Q : TT1 → TT2 → iProp Σ) v' Φ' :
    iEff_car (>>.. x >> ! (v x  ) {{ P x }};
              <<.. y << ? (w x y) {{ Q x y }}) v' Φ'
   ⊣⊢
    (∃.. x, ⌜ v x = v' ⌝ ∗ P x ∗ (∀.. y, Q x y -∗ Φ' (w x y)))%I.
Proof.
  rewrite iEffPre_texist_eq iEffPre_base_eq. do 2 f_equiv.
  iSplit; iIntros "(-> & HP & HΦ')"; iSplit; try done; iFrame.
  { iIntros (y) "HQ". iApply "HΦ'". rewrite iEffPost_texist_eq.
    iExists y. rewrite iEffPost_base_eq. by iFrame. }
  { iIntros (y) "HQ". rewrite iEffPost_texist_eq iEffPost_base_eq.
    iDestruct "HQ" as (w') "(<- & HQ)". by iApply "HΦ'". }
Qed.

(* iEff_marker. *)
Program Definition iEff_marker_def {Σ} (f : val → val) (e : iEff Σ) : iEff Σ :=
  IEff (λ v', λne q', ∃ w', ⌜ v' = f w' ⌝ ∗ iEff_car e w' q')%I.
Next Obligation. solve_proper. Qed.
Definition iEff_marker_aux : seal (@iEff_marker_def). by eexists. Qed.
Definition iEff_marker := iEff_marker_aux.(unseal).
Definition iEff_marker_eq : @iEff_marker = @iEff_marker_def :=
  iEff_marker_aux.(seal_eq).
Arguments iEff_marker {_} _ _%ieff.
Instance: Params (@iEff_marker) 3 := {}.

(* iEff_filter. *)
Program Definition iEff_filter_def {Σ} (P : val → Prop) (e : iEff Σ) : iEff Σ :=
  IEff (λ v', λne q', ⌜ P v' ⌝ ∗ iEff_car e v' q')%I.
Next Obligation. solve_proper. Qed.
Definition iEff_filter_aux : seal (@iEff_filter_def). by eexists. Qed.
Definition iEff_filter := iEff_filter_aux.(unseal).
Definition iEff_filter_eq : @iEff_filter = @iEff_filter_def :=
  iEff_filter_aux.(seal_eq).
Arguments iEff_filter {_} _ _%ieff.
Instance: Params (@iEff_marker) 3 := {}.

(* iEff_sum. *)
Program Definition iEff_sum_def {Σ} (e1 e2 : iEff Σ) : iEff Σ :=
  IEff (λ w', λne q', (iEff_car e1 w' q') ∨ (iEff_car e2 w' q'))%I.
Next Obligation. solve_proper. Qed.
Definition iEff_sum_aux : seal (@iEff_sum_def). by eexists. Qed.
Definition iEff_sum := iEff_sum_aux.(unseal).
Definition iEff_sum_eq : @iEff_sum = @iEff_sum_def :=
  iEff_sum_aux.(seal_eq).
Arguments iEff_sum {_} _%ieff _%ieff.
Instance: Params (@iEff_sum) 3 := {}.

(* Sum and marker notation. *)
Notation "Ψ1 '<+>' Ψ2"  := (iEff_sum Ψ1 Ψ2)
  (at level 20, right associativity,
   format "Ψ1 <+> Ψ2") : ieff_scope.

Notation "f '#>' Ψ"  := (iEff_marker f Ψ)
  (at level 15, right associativity,
   format "f #> Ψ") : ieff_scope.

Notation "P '?>' Ψ"  := (iEff_filter P Ψ)
  (at level 15, right associativity,
   format "P ?> Ψ") : ieff_scope.


(** * Basic Properties. *)

Section ieff_proofs.
  Context {Σ : gFunctors}.
  Implicit Types e : iEff Σ.

  (** ** Non-expansiveness of operators *)
  Global Instance iEffPre_base_ne n :
    Proper
      ((dist n) ==> (dist n) ==> (dist n) ==> (dist n))
      (iEffPre_base (Σ:=Σ)).
  Proof.
    intros ?????????. rewrite iEffPre_base_eq /iEffPre_base_def.
    intros ??. simpl. by repeat (apply H || f_equiv).
  Qed.
  Global Instance iEffPre_base_proper :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (iEffPre_base (Σ:=Σ)).
  Proof.
    intros ?????????.
    apply equiv_dist=>n; apply iEffPre_base_ne; by apply equiv_dist.
  Qed.
  Global Instance iEffPost_base_ne n :
    Proper
      ((dist n) ==> (dist n) ==> (dist n) ==> (dist n))
      (iEffPost_base (Σ:=Σ)).
  Proof.
    intros ?????????. rewrite iEffPost_base_eq /iEffPost_base_def.
    solve_proper.
  Qed.
  Global Instance iEffPost_base_proper :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (iEffPost_base (Σ:=Σ)).
  Proof.
    intros ?????????.
    apply equiv_dist=>n; apply iEffPost_base_ne; by apply equiv_dist.
  Qed.
  Global Instance iEff_sum_ne n :
    Proper ((dist n) ==> (dist n) ==> (dist n)) (iEff_sum (Σ:=Σ)).
  Proof.
    intros ??????. rewrite iEff_sum_eq /iEff_sum_def.
    f_equiv=>w' q' //=. f_equiv; by apply iEff_car_ne.
  Qed.
  Global Instance iEff_sum_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (iEff_sum (Σ:=Σ)).
  Proof.
    intros ??????.
    apply equiv_dist=>n; apply iEff_sum_ne; by apply equiv_dist.
  Qed.
  Global Instance iEff_marker_ne f n :
    Proper ((dist n) ==> (dist n)) (iEff_marker (Σ:=Σ) f).
  Proof.
    intros ???. rewrite iEff_marker_eq /iEff_marker_def.
    f_equiv=>w' q' //=. f_equiv=> v'. f_equiv; by apply iEff_car_ne.
  Qed.
  Global Instance iEff_marker_proper f :
    Proper ((≡) ==> (≡)) (iEff_marker (Σ:=Σ) f).
  Proof.
    intros ???. apply equiv_dist=>n; apply iEff_marker_ne; by apply equiv_dist.
  Qed.
  Global Instance iEff_filter_ne P n :
    Proper ((dist n) ==> (dist n)) (iEff_filter (Σ:=Σ) P).
  Proof.
    intros ???. rewrite iEff_filter_eq /iEff_filter_def.
    f_equiv=>v' q' //=. f_equiv; by apply iEff_car_ne.
  Qed.
  Global Instance iEff_filter_proper P :
    Proper ((≡) ==> (≡)) (iEff_filter (Σ:=Σ) P).
  Proof.
    intros ???. apply equiv_dist=>n; apply iEff_filter_ne; by apply equiv_dist.
  Qed.


  Global Instance iEffPre_exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> (dist n)) (@iEffPre_exist Σ A).
  Proof. rewrite iEffPre_exist_eq=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.
  Global Instance iEffPre_exist_proper A :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@iEffPre_exist Σ A).
  Proof. rewrite iEffPre_exist_eq=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.

  Global Instance iEffPost_exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> (dist n)) (@iEffPost_exist Σ A).
  Proof.
    rewrite iEffPost_exist_eq /iEffPost_exist_def => m1 m2 Hm w /=.
    f_equiv=>x. apply Hm.
  Qed.
  Global Instance iEffPost_exist_proper A :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@iEffPost_exist Σ A).
  Proof.
    rewrite iEffPost_exist_eq /iEffPost_exist_def => m1 m2 Hm w /=.
    f_equiv=> x. apply Hm.
  Qed.


  Global Instance iEff_sum_comm : Comm (≡) (iEff_sum (Σ:=Σ)).
  Proof.
    intros e1 e2 v q. rewrite iEff_sum_eq /iEff_sum_def //=.
    iSplit; iIntros "H"; iDestruct "H" as "[H|H]".
    { by iRight. } { by iLeft. } { by iRight. } { by iLeft. }
  Qed.
  Global Instance iEff_sum_assoc : Assoc (≡) (iEff_sum (Σ:=Σ)).
  Proof.
    intros e1 e2 e3 v q. rewrite iEff_sum_eq /iEff_sum_def //=.
    iSplit; iIntros "H";
    [ iDestruct "H" as "[H|[H|H]]"
    | iDestruct "H" as "[[H|H]|H]" ].
    { by iLeft; iLeft. } { by iLeft; iRight. } { by iRight. }
    { by iLeft. } { by iRight; iLeft. } { by iRight; iRight. }
  Qed.
  Global Instance iEff_sum_left_id : LeftId (≡) (⊥) (iEff_sum (Σ:=Σ)).
  Proof.
    intros e v q. rewrite iEff_sum_eq /iEff_sum_def //=.
    iSplit; iIntros "H"; [iDestruct "H" as "[H|H]"|]; by iFrame.
  Qed.
  Global Instance iEff_sum_right_id : RightId (≡) (⊥) (iEff_sum (Σ:=Σ)).
  Proof. intros e. rewrite iEff_sum_comm. by apply iEff_sum_left_id. Qed.


  Lemma iEff_filter_bottom P : (P ?> ⊥ ≡ (⊥ : iEff Σ))%ieff.
  Proof.
    intros v q. rewrite iEff_filter_eq /iEff_filter_def //=.
    by iSplit; [iIntros "[_ H]"|].
  Qed.
  Lemma iEff_filter_true (Ψ : iEff Σ) : ((λ _, True) ?> Ψ ≡ Ψ)%ieff.
  Proof.
    intros v q. rewrite iEff_filter_eq /iEff_filter_def //=.
    iSplit; [iIntros "[_ H]"|iIntros "H"]; by auto.
  Qed.
  Lemma iEff_filter_false (Ψ : iEff Σ) : ((λ _, False) ?> Ψ ≡ (⊥ : iEff Σ))%ieff.
  Proof.
    intros v q. rewrite iEff_filter_eq /iEff_filter_def //=.
    iSplit; [iIntros "[H _]"|iIntros "H"]; by auto.
  Qed.
  Lemma iEff_filter_filter P Q (Ψ : iEff Σ) :
    (P ?> (Q ?> Ψ) ≡ (λ (v : val), P v ∧ Q v) ?> Ψ)%ieff.
  Proof.
    intros v q. rewrite iEff_filter_eq /iEff_filter_def //=.
    iSplit; [iIntros "(% & % & H)"|iIntros "[[% %] H]"]; by auto.
  Qed.
  Lemma iEff_filter_filter_l (P Q : val → Prop) (Ψ : iEff Σ) :
    (∀ v, P v → Q v) → (P ?> (Q ?> Ψ) ≡ P ?> Ψ)%ieff.
  Proof.
    intros H v q. rewrite iEff_filter_eq /iEff_filter_def //=.
    iSplit; [iIntros "(% & % & H)"|iIntros "[% H]"]; by auto.
  Qed.
  Lemma iEff_filter_filter_r (P Q : val → Prop) (Ψ : iEff Σ) :
    (∀ v, Q v → P v) → (P ?> (Q ?> Ψ) ≡ Q ?> Ψ)%ieff.
  Proof.
    intros H v q. rewrite iEff_filter_eq /iEff_filter_def //=.
    iSplit; [iIntros "(% & % & H)"|iIntros "[% H]"]; by auto.
  Qed.
  Lemma iEff_filter_sum_distr P (Ψ1 Ψ2 : iEff Σ) :
    ((P ?> (Ψ1 <+> Ψ2)) ≡ (P ?> Ψ1) <+> (P ?> Ψ2))%ieff.
  Proof.
    intros v q. rewrite iEff_sum_eq iEff_filter_eq /iEff_sum_def /iEff_filter_def.
    simpl. iSplit; [iIntros "[% [H|H]]"|iIntros "[[% H]|[% H]]"]; by auto.
  Qed.
  Lemma iEff_sum_filter_eq (P : val → Prop) `{!∀ v, Decision (P v)} (Ψ : iEff Σ) :
    (Ψ ≡ (P ?> Ψ) <+> ((λ v, ¬ P v) ?> Ψ))%ieff.
  Proof.
    intros v q. rewrite iEff_sum_eq iEff_filter_eq /iEff_sum_def /iEff_filter_def.
    simpl. iSplit; [iIntros "H"|iIntros "[[% H]|[% H]]"]; iFrame.
    iPureIntro. case (decide (P v)); by auto.
  Qed.

  Lemma iEff_marker_bottom f : (f #> ⊥ ≡ (⊥ : iEff Σ))%ieff.
  Proof.
    intros v q. rewrite iEff_marker_eq /iEff_marker_def //=.
    iSplit; iIntros "H"; [iDestruct "H" as (w) "[_ H]"|]; done.
  Qed.
  Lemma iEff_marker_sum_distr f (Ψ1 Ψ2 : iEff Σ) :
    ((f #> (Ψ1 <+> Ψ2)) ≡ (f #> Ψ1) <+> (f #> Ψ2))%ieff.
  Proof.
    intros v q. rewrite iEff_sum_eq iEff_marker_eq /iEff_sum_def /iEff_marker_def.
    simpl. iSplit; iIntros "H".
    - iDestruct "H" as (w') "[-> [H|H]]"; by eauto.
    - iDestruct "H" as "[H|H]"; iDestruct "H" as (w') "[-> H]"; by eauto.
  Qed.
  Lemma iEff_marker_compose f g (Ψ : iEff Σ) :
    ((f #> (g #> Ψ)) ≡ ((f ∘ g) #> Ψ))%ieff.
  Proof.
    intros v q. rewrite iEff_marker_eq /iEff_marker_def.
    simpl. iSplit; iIntros "H".
    - iDestruct "H" as (u') "[-> H]"; iDestruct "H" as (w') "[-> H]"; by eauto.
    - iDestruct "H" as (w') "[-> H]"; by eauto.
  Qed.
  Lemma iEff_marker_tele {TT1 TT2 : tele} f
  (v : TT1 →       val) (P : TT1 →       iProp Σ)
  (w : TT1 → TT2 → val) (Q : TT1 → TT2 → iProp Σ) :
    (f #> (>>.. x >> !    (v x  )  {{ P x }};
           <<.. y << ?    (w x y)  {{ Q x y }}))
   ≡
          (>>.. x >> ! (f (v x  )) {{ P x }};
           <<.. y << ? (  (w x y)) {{ Q x y }}).
  Proof.
    intros u' q'. iSplit; rewrite iEff_marker_eq /iEff_marker_def //=.
    { iIntros "H". iDestruct "H" as (u) "[-> H]".
      rewrite !iEffPre_texist_eq iEffPre_base_eq //=.
      iDestruct "H" as (x) "(<- & HP & Hk)". iExists x. by iFrame. }
    { iIntros "H". rewrite !iEffPre_texist_eq iEffPre_base_eq //=.
      iDestruct "H" as (u) "(<- & HP & Heq)". iExists (v u).
      iSplit; [done|]. rewrite iEffPre_texist_eq. iExists u. by iFrame. }
  Qed.
  Lemma iEff_marker_tele' (TT1 TT2 : tele) f
  (v : TT1 -t>         val) (P : TT1 -t>         iProp Σ)
  (w : TT1 -t> TT2 -t> val) (Q : TT1 -t> TT2 -t> iProp Σ) :
    (f #> (>>.. x >> !           (tele_app v x)
                     {{          (tele_app P x)   }};
           <<.. y << ? (tele_app (tele_app w x) y)
                     {{ tele_app (tele_app Q x) y }}))
   ≡
          (>>.. x >> !        (f (tele_app v x))
                     {{          (tele_app P x)   }};
           <<.. y << ? (tele_app (tele_app w x) y)
                     {{ tele_app (tele_app Q x) y }}).
  Proof. by rewrite (iEff_marker_tele _ (tele_app v) (tele_app P)
                  (λ x y, tele_app (tele_app w x) y)
                  (λ x y, tele_app (tele_app Q  x) y)).
  Qed.

End ieff_proofs.
