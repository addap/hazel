(* shift_reset.v *)

(* This file introduces reasoning rules for the delimited-control operators
   [shift0/reset0] and [shift/reset]. *)

From iris.proofmode Require Import base tactics classes.
From program_logic Require Import reasoning_rules.


(* ========================================================================== *)
(** * Implementation. *)

(* -------------------------------------------------------------------------- *)
(** Shit0 & Reset0 *)

(*  reset0 K[shift0 t]  --->  t (λ w. reset0 K[w])  (reset0 ∉ K) *)

Definition reset0 : val := (λ: "t",
  deep-try: "t" #() with
    effect (λ: "h" "k", "h" "k")%V
  | return (λ: "y", "y")%V
  end
)%V.

Definition shift0 : val := (λ: "h",
  do: "h"
)%V.

(* Notation to state the reasoning rules. *)
Notation Reset0 e := (App reset0 (LamV BAnon e)) (only parsing).
Notation Shift0 b e := (App shift0 (LamV b e)) (only parsing).


(* -------------------------------------------------------------------------- *)
(** Shit & Reset *)

(*  reset K[shift t]  --->  reset (t (λ w. reset K[w]))  (reset ∉ K) *)

Definition reset : val := (rec: "reset" "t" :=
  deep-try: "t" #() with
    effect (λ: "h" "k", "reset" (λ: <>, "h" "k"))
  | return (λ: "y", "y")%V
  end
)%V.

Definition shift : val := (λ: "h",
  do: "h"
)%V.

(* Notation to state the reasoning rules. *)
Notation Reset e := (App reset (LamV BAnon e)) (only parsing).
Notation Shift b e := (App shift (LamV b e)) (only parsing).


(* ========================================================================== *)
(** * Specification. *)

Section specification.
  Context `{!irisGS eff_lang Σ}.

  (* ------------------------------------------------------------------------ *)
  (** Shift0 Protocol. *)

  Section shift0_protocol.

    Definition is_shift0 (Ψ : iEff Σ) (Φ Q : val → iPropO Σ) (h : val) : iProp Σ :=
      ∀ (k : val),
        (∀ w, Q w -∗ EWP k w <| Ψ |> {{ Φ }}) -∗
          EWP h k <| Ψ |> {{ Φ }}.

    Definition SHIFT0 Ψ Φ : iEff Σ :=
      >> h Q >> !(h) {{ is_shift0 Ψ Φ Q h }};
      << w   << ?(w) {{ Q w }} @ OS.

    Lemma upcl_SHIFT0 Ψ Φ v Φ' :
      iEff_car (upcl OS (SHIFT0 Ψ Φ)) v Φ' ≡
        (∃ h Q,
           ⌜ v = h ⌝ ∗ is_shift0 Ψ Φ Q h ∗
           (∀ (w : val), Q w -∗ Φ' w))%I.
    Proof. by rewrite (upcl_tele' [tele _ _] [tele _]) //. Qed.

  End shift0_protocol.


  (* ------------------------------------------------------------------------ *)
  (** Shift Protocol. *)

  Section shift_protocol.

    Definition is_shift_pre
      (SHIFT : iEffO -d> (val -d> iPropO Σ) -d> iEffO)
      (Ψ : iEff Σ) (Φ Q : val → iPropO Σ) (h : val) : iProp Σ :=
      ∀ (k : val),
        (∀ w, Q w -∗ EWP k w <| Ψ |> {{ Φ }}) -∗
          ▷ EWP h k <| SHIFT Ψ Φ |> {{ Φ }}.

    Definition SHIFT_pre
      (SHIFT : iEffO -d> (val -d> iPropO Σ) -d> iEffO) :
              (iEffO -d> (val -d> iPropO Σ) -d> iEffO) := λ Ψ Φ,
      (>> h Q >> !(h) {{ is_shift_pre SHIFT Ψ Φ Q h }};
       << w   << ?(w) {{ Q w }} @ OS)%ieff.

    Local Instance shift_pre_contractive : Contractive SHIFT_pre.
    Proof.
      intros n SHIFT SHIFT' HS Ψ Φ. rewrite /SHIFT_pre /is_shift_pre.
      by repeat (apply iEffPre_base_ne ||
                 rewrite iEffPost_base_eq || unfold iEffPost_base_def ||
                 apply HS || f_contractive || f_equiv || intros =>?).
    Qed.
    Definition SHIFT_def : iEffO -d> (val -d> iPropO Σ) -d>  iEffO :=
      fixpoint (SHIFT_pre).
    Definition SHIFT_aux : seal SHIFT_def. Proof. by eexists. Qed.
    Definition SHIFT := SHIFT_aux.(unseal).
    Definition SHIFT_eq : SHIFT = SHIFT_def := SHIFT_aux.(seal_eq).
    Global Lemma SHIFT_unfold Ψ Φ : SHIFT Ψ Φ ≡ SHIFT_pre SHIFT Ψ Φ.
    Proof. by rewrite SHIFT_eq /SHIFT_def;
           apply (fixpoint_unfold (SHIFT_pre)).
    Qed.
    Definition is_shift := is_shift_pre SHIFT.
    Global Lemma is_shift_unfold Ψ Φ Q h :
      is_shift Ψ Φ Q h = is_shift_pre SHIFT Ψ Φ Q h.
    Proof. done. Qed.

    Lemma upcl_SHIFT Ψ Φ v Φ' :
      iEff_car (upcl OS (SHIFT Ψ Φ)) v Φ' ≡
        (∃ t Q,
           ⌜ v = t ⌝ ∗ is_shift Ψ Φ Q t ∗
           (∀ (w : val), Q w -∗ Φ' w))%I.
    Proof.
      transitivity (iEff_car (upcl OS (SHIFT_pre SHIFT Ψ Φ)) v Φ').
      - iApply iEff_car_proper. by rewrite SHIFT_unfold.
      - by rewrite (upcl_tele' [tele _ _] [tele _]) //.
    Qed.

  End shift_protocol.


  (* ------------------------------------------------------------------------ *)
  (** Reasoning Rules. *)

  Section reasoning_rules.

    Definition reset0_spec
      (e : expr) (Ψ : iEff Σ) (Φ : val → iProp Σ) : Prop :=
      ⊢ EWP e <|SHIFT0 Ψ Φ|> {{Φ}} -∗
          EWP Reset0 e <|Ψ|> {{Φ}}.

    Definition shift0_spec
      (b : binder) (e : expr) (Ψ : iEff Σ) (Φ Q : val → iProp Σ) : Prop :=
      ⊢ is_shift0 Ψ Φ Q (LamV b e) -∗
          EWP Shift0 b e <|SHIFT0 Ψ Φ|> {{Q}}.

    Definition reset_spec
      (e : expr) (Ψ : iEff Σ) (Φ : val → iProp Σ) : Prop :=
      ⊢ EWP e <|SHIFT Ψ Φ|> {{Φ}} -∗
          EWP Reset e <|Ψ|> {{Φ}}.

    Definition shift_spec
      (b : binder) (e : expr) (Ψ : iEff Σ) (Φ Q : val → iProp Σ) : Prop :=
      ⊢ is_shift Ψ Φ Q (LamV b e) -∗
          EWP Shift b e <|SHIFT Ψ Φ|> {{Q}}.

  End reasoning_rules.

End specification.


(* ========================================================================== *)
(** * Verification. *)

Section verification.
  Context `{!heapGS Σ}.

  Lemma ewp_reset0 e Ψ Φ : reset0_spec e Ψ Φ.
  Proof.
    iIntros "He". unfold reset0. ewp_pure_steps.
    iApply (ewp_deep_try_with with "[He]"). { by ewp_pure_steps. }
    iLöb as "IH".
    rewrite {-1}deep_handler_unfold.
    iSplit; [|iSplit];[
    by iIntros (y) "Hy"; ewp_pure_steps| |
    by iIntros (??) "HFalse"; rewrite upcl_bottom ].
    iIntros (v k) "Hprot". rewrite upcl_SHIFT0.
    iDestruct "Hprot" as (t Q) "[-> [Hshift Hk]]".
    ewp_pure_steps.
    iApply "Hshift".
    iIntros (w) "Hw".
    by iApply ("Hk" with "Hw").
  Qed.

  Lemma ewp_shift0 b e Ψ Φ Q : shift0_spec b e Ψ Φ Q.
  Proof.
    iIntros "Hshift". unfold shift0. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_SHIFT0.
    iExists (LamV b e), Q. iSplit; [done|]. iFrame.
    iIntros (w) "Hw". by ewp_pure_steps.
  Qed.

  Lemma ewp_reset e Ψ Φ : reset_spec e Ψ Φ.
  Proof.
    iIntros "He". unfold reset. ewp_pure_steps.
    iApply (ewp_deep_try_with with "[He]"). { by ewp_pure_steps. }
    iLöb as "IH".
    rewrite {-1}deep_handler_unfold.
    iSplit; [|iSplit];[
    by iIntros (y) "Hy"; ewp_pure_steps| |
    by iIntros (??) "HFalse"; rewrite upcl_bottom ].
    iIntros (v k) "Hprot". rewrite upcl_SHIFT.
    iDestruct "Hprot" as (t Q) "[-> [Hshift Hk]]".
    ewp_pure_steps.
    iApply (ewp_deep_try_with with "[Hshift Hk] IH").
    rewrite is_shift_unfold /is_shift_pre.
    iSpecialize ("Hshift" $! k with "[Hk]").
    { iIntros (w) "Hw". by iApply ("Hk" with "Hw IH"). }
    by ewp_pure_steps. 
  Qed.

  Lemma ewp_shift b e Ψ Φ Q : shift_spec b e Ψ Φ Q.
  Proof.
    iIntros "Hshift". unfold shift. ewp_pure_steps.
    iApply ewp_do_os. rewrite upcl_SHIFT.
    iExists (LamV b e), Q. iSplit; [done|]. iFrame.
    iIntros (w) "Hw". by ewp_pure_steps.
  Qed.

End verification.

