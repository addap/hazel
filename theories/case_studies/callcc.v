(* callcc.v *)

(* This theory introduces reasoning rules for [callcc] and [throw]. *)

From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop.
From iris.program_logic Require Import weakestpre.
From language Require Import eff_lang.
From program_logic Require Import reasoning_rules.


(* ========================================================================== *)
(** * Implementation. *)

(* The encoding of [callcc] and [throw] in [eff_lang] is based on a third
   function, [toplevel], which delimits the environment under which a program
   performs calls to [callcc] and [throw]. These operations are then simply
   encoded as effect-performing instructions. *)

Definition callcc : val := (λ: "t",
  let: "f" := doₘ: (InjL "t") in "f" #()
)%V.
Definition throw : val := (λ: "k" "w",
  doₘ: (InjR ("k", "w"))
)%V.
Definition toplevel : val := (λ: "tk",
  deep-try: "tk" #() with
    effect (λ: "request" "k",
      match: "request" with
        (* Callcc: *) InjL "t" =>
          "k" (λ: <>, "t" "k")
      | (* Throw:  *) InjR "args" =>
          let: "k'" := Fst "args" in
          let: "w"  := Snd "args" in
          "k'" (λ: <>, "w")
      end)%V
  | return (λ: "y", "y")%V
  end
)%V.

Notation Callcc b e := (App callcc (LamV b e)) (only parsing).
Notation Throw k w := (App (App throw k) w) (only parsing).
Notation Toplevel e := (App toplevel (LamV BAnon e)) (only parsing).


(* ========================================================================== *)
(** * Specification. *)

Section specification.

  (* ------------------------------------------------------------------------ *)
  (** Protocol. *)

  Section protocol.
    Context `{!irisGS eff_lang Σ}.

    Definition isCont (k : val) (Φ : val → iProp Σ) : iProp Σ :=
      □ ∀ (f : val), EWP f #() {{ Φ }} -∗ EWP (k f) {{ _, True }}.

    Definition THROW : iEff Σ :=
      >> k w Φ >> !(InjRV (k, w)%V) {{ isCont k Φ ∗ Φ w }};
      << y     << ?(y)              {{ False }} @ MS.

    Definition CALLCC_pre (CALLCC : iEff Σ): iEff Σ :=
      let CT := (CALLCC <+> THROW)%ieff in
      >> t Φ >> !(InjLV t) {{ ∀ k, isCont k Φ -∗ ▷ EWP t k .{| CT |} {{ Φ }} }};
      << f   << ?(f)       {{ ▷ EWP f #() .{| CT |} {{ Φ }} }} @ MS.

    Local Instance CALLCC_pre_contractive : Contractive CALLCC_pre.
    Proof.
      rewrite /CALLCC_pre => n CALLCC CALLCC' HI.
      by repeat (apply iEffPre_base_ne ||
                 rewrite iEffPost_base_eq || unfold iEffPost_base_def ||
                 apply HI || f_contractive || f_equiv || intros =>?).
    Qed.
    Definition CALLCC_def : iEff Σ := fixpoint (CALLCC_pre).
    Definition CALLCC_aux : seal CALLCC_def. Proof. by eexists. Qed.
    Definition CALLCC := CALLCC_aux.(unseal).
    Definition CALLCC_eq : CALLCC = CALLCC_def := CALLCC_aux.(seal_eq).
    Global Lemma CALLCC_unfold : CALLCC ≡ CALLCC_pre CALLCC.
    Proof. by rewrite CALLCC_eq /CALLCC_def;
           apply (fixpoint_unfold (CALLCC_pre)).
    Qed.

    (* The abstract protocol [CT]. *)
    Definition CT : iEff Σ := CALLCC<+>THROW.
    Arguments CT : simpl never.

    Lemma pers_upcl_CALLCC v Φ' :
      iEff_car (upcl MS CALLCC) v Φ' ≡
        (∃ t Φ,
           ⌜ v = InjLV t ⌝ ∗
           (∀ (k : val), isCont k Φ -∗ ▷ EWP t k .{| CT |} {{ Φ }}) ∗
           □ (∀ (f : val), ▷ EWP f #() .{| CT |} {{ Φ }} -∗ Φ' f))%I.
    Proof.
      transitivity (iEff_car (upcl MS (CALLCC_pre CALLCC)) v Φ').
      - iApply iEff_car_proper. by rewrite {1}CALLCC_unfold.
      - by rewrite (pers_upcl_tele' [tele _ _] [tele _]) //.
    Qed.

    Lemma pers_upcl_THROW v Φ' :
      iEff_car (upcl MS THROW) v Φ' ≡
        (∃ k w Φ,
           ⌜ v = InjRV (k, w)%V ⌝ ∗
           (isCont k Φ ∗ Φ w) ∗ □ (∀ y, False -∗ Φ' y))%I.
    Proof. by rewrite /THROW (pers_upcl_tele' [tele _ _ _] [tele _]) //. Qed.

    Lemma pers_upcl_CT v  Φ' :
      iEff_car (upcl MS CT) v Φ' ≡
        (iEff_car (upcl MS CALLCC) v Φ' ∨ iEff_car (upcl MS THROW) v Φ')%I.
    Proof. by apply upcl_sum. Qed.

  End protocol.


  (* ------------------------------------------------------------------------ *)
  (** Reasoning Rules. *)

  Section reasoning_rules.
    Context `{!irisGS eff_lang Σ}.

    Definition toplevel_spec (e : expr) : Prop :=
      ⊢ EWP e .{| CT |} {{_, True}} -∗
          EWP Toplevel e {{_, True}}.

    Definition callcc_spec Φ (b : binder) (e : expr) : Prop :=
      ⊢ (∀ k, isCont k Φ -∗ EWP (subst' b k e) .{| CT |} {{ Φ }}) -∗
          EWP Callcc b e .{| CT |} {{ Φ }}.

    Definition throw_spec Φ Φ' (k w : val) : Prop :=
      ⊢ Φ w -∗ isCont k Φ -∗
         EWP Throw k w .{| CT |} {{ Φ' }}.

  End reasoning_rules.

End specification.


(* ========================================================================== *)
(** * Verification. *)

Section verification.
  Context `{!heapGS Σ}.

  Lemma ewp_toplevel e : toplevel_spec e.
  Proof.
    iIntros "He". unfold toplevel. ewp_pure_steps.
    iApply (ewp_deep_try_with with "[He]"). { by ewp_pure_steps. }
    iLöb as "IH".
    rewrite {-1}deep_handler_unfold. iSplit; [|iSplit].
    - iIntros (y) "_". by ewp_pure_steps.
    - iIntros (v k) "HFalse". by rewrite upcl_bottom.
    - iIntros (v k).
      rewrite pers_upcl_CT pers_upcl_CALLCC pers_upcl_THROW.
      iIntros "[[%t  [%Φ (-> & Ht & #Hk)]]|
                [%k' [%w [%Φ (-> & [#Hk' Hw] & _)]]]]";
      ewp_pure_steps.
      + iApply ("Hk" with "[Ht] IH").
        iSpecialize ("Ht" $! k with "[]").
        { iIntros "!#" (f) "Hf".
          iApply ("Hk" with "[Hf] IH").
          iApply (ewp_ms_prot_mono with "[] Hf").
          by iApply iEff_le_bottom.
        }
        iNext. by ewp_pure_steps.
      + by iApply "Hk'"; ewp_pure_steps.
  Qed.

  Lemma ewp_callcc Φ b e : callcc_spec Φ b e.
  Proof.
    iIntros "He". unfold callcc. ewp_pure_steps.
    iApply ewp_do_ms.
    rewrite pers_upcl_CT pers_upcl_CALLCC; iLeft.
    iExists (λ: b, e)%V, Φ. iSplit; [done|iSplit].
    - iIntros (k) "Hk". iNext.
      ewp_pure_steps. by iApply "He".
    - iIntros "!#" (f) "Hf". by ewp_pure_steps.
  Qed.

  Lemma ewp_throw Φ Φ' k w : throw_spec Φ Φ' k w.
  Proof.
    iIntros "Hw Hk". unfold throw.
    ewp_pure_steps.
    iApply ewp_do_ms.
    rewrite pers_upcl_CT pers_upcl_THROW. iRight.
    iExists k, w, Φ. iSplit; [done|]. iFrame.
    by iIntros "!#" (y) "?".
  Qed.

End verification.


(* ========================================================================== *)
(** * Examples. *)

(* -------------------------------------------------------------------------- *)
(** Inc3.  *)

(* We verify the function [inc3] introduced by Delbianco and Nanevski in the
   paper "Hoare-Style Reasoning with (Algebraic) Continuations" (ICFP'13). *)

Section inc3.
  Context `{!heapGS Σ}.

  Definition inc (x : loc) : expr := (#x <- (Load #x) + #1%Z)%E.

  Definition inc3 (x : loc) : expr := (
    let: "c" := Callcc "k" (λ: <>, inc x;; throw "k" (λ: <>, #())) in
    inc x;; "c" #()
  )%E.

  Lemma inc_spec x (i : Z) Ψ1 Ψ2 Φ :
    ▷ (x ↦ #(i + 1) ={⊤}=∗ Φ #()) -∗
      x ↦ #i -∗ EWP (inc x) <| Ψ1 |> {| Ψ2 |} {{Φ}}.
  Proof.
    iIntros "HΦ Hx". unfold inc. ewp_bind_rule.
    iApply (ewp_load with "Hx").
    iIntros "!> Hx !>". simpl. ewp_pure_steps. done.
    by iApply (ewp_store with "Hx").
  Qed.

  Lemma inc3_spec R x (i : Z) :
    R -∗ x ↦ #i -∗ EWP (inc3 x) .{|CT|} {{_, R ∗ x ↦ #(i + 3)%Z}}.
  Proof.
    unfold inc3. iIntros "HR Hx".
    iApply (ewp_bind' (AppRCtx _)). { done. }
    iApply ewp_callcc.
    iIntros (k) "#Hk". simpl. ewp_pure_steps.
    iApply (ewp_bind' (AppRCtx _)). { done. }
    iApply (inc_spec with "[HR] Hx").
    iIntros "!> Hx !>". simpl. ewp_pure_steps.
    iApply (ewp_bind' (AppRCtx _)). { done. }
    iApply (inc_spec with "[HR] Hx").
    iIntros "!> Hx !>". simpl.
    do 5 ewp_value_or_step.
    iApply (ewp_throw with "[HR Hx] Hk").
    simpl.
    ewp_pure_steps.
    iApply (ewp_bind' (AppRCtx _)). { done. }
    iApply (inc_spec with "[HR] Hx").
    iIntros "!> Hx !>". simpl. ewp_pure_steps. iFrame.
    by rewrite (_: (i + 1 + 1 + 1 = i + 3)%Z); [|lia].
  Qed.

End inc3.


(* -------------------------------------------------------------------------- *)
(** Shift & Reset. *)

(* We specify and verify Filinski's encoding of [shift] and [reset]. The
   original encoding is written in Standard ML and presented in the paper
   "Representing Monads" (POPL'94). The paper "Final Shift for Call/cc: Direct
   Implementation of Shift and Reset" (SIGPLAN Notices - 2002) by Gasbichler
   and Sperber contains a translation (attributed to Danvy) of this encoding
   to Scheme 48. *)

Section shift_reset.
  Context `{!heapGS Σ}.

  Variables (mc : loc). (* The meta-continuation. *)

  (* Implementation. *)

  Definition abort : val := (λ: "tk",
    let: "y" := "tk" #() in
    let: "m" := Load #mc in
    "m" "y"
  )%V.

  Definition reset : val := (λ: "t", callcc (λ: "k",
      let: "m" := Load #mc in
      #mc <- (λ: "y", #mc <- "m";; throw "k" "y");;
      abort "t"
    )
  )%V.

  Definition shift : val := (λ: "h", callcc (λ: "k",
      abort (λ: <>, "h" (λ: "y", reset (λ: <>, throw "k" "y")))
    )
  )%V.

  Definition inMetaCont (k : val) (Φ : option (val → iProp Σ)) :=
    match Φ with
    | None =>
        True%I
    | Some Φ =>
        ∀ (y k' : val) Φ',
          Φ y -∗
            mc ↦ k' -∗
              EWP (k y) .{| CT |} {{ Φ' }}
    end%I.


  (* Logical definitions. *)

  Definition isMetaCont (Φopt : option (val → iProp Σ)) :=
    (∃ (k : val), mc ↦ k ∗ inMetaCont k Φopt)%I.

  Definition wpmc
    (e : expr) (Φopt : option (val → iProp Σ)) (Φ : val → iProp Σ) : iProp Σ :=
    isMetaCont Φopt -∗
      EWP e .{| CT |} {{ y, Φ y ∗ isMetaCont Φopt }}.


  (* Reasoning rules. *)

  Lemma abort_spec (tk : val) Φ Φ' :
    EWP (tk #()) .{| CT |} {{ y, Φ y ∗ isMetaCont (Some Φ) }} -∗
      EWP (abort tk) .{| CT |} {{ Φ' }}.
  Proof.
    iIntros "Htk".
    unfold abort. ewp_pure_steps.
    ewp_bind_rule. simpl.
    iApply (ewp_pers_mono with "Htk").
    iIntros "!#" (y) "[Hy Hmc] !>". ewp_pure_steps.
    ewp_bind_rule.
    iDestruct "Hmc" as "[%k [Hmc Hk]]".
    iApply (ewp_load with "Hmc").
    iIntros "!> Hmc !>". simpl. ewp_pure_steps.
    by iApply ("Hk" with "Hy Hmc").
  Qed.

  Lemma reset_spec (t : val) Φopt Φ :
    wpmc (t #())%E (Some Φ) Φ -∗
      wpmc (reset t) Φopt Φ.
  Proof.
    iIntros "Ht Hmc". unfold reset. ewp_pure_steps.
    iApply ewp_callcc. iIntros (k) "#Hk". simpl.
    ewp_bind_rule.
    iDestruct "Hmc" as "[%m [Hmc Hm]]".
    iApply (ewp_load with "Hmc").
    iIntros "!> Hmc !>". simpl. ewp_pure_steps.
    ewp_bind_rule.
    iApply (ewp_store with "Hmc").
    iIntros "!> Hmc !>". simpl. ewp_pure_steps.
    iSpecialize ("Ht" with "[Hm Hmc]").
    { iExists (λ: "y", #mc <- m;; throw k "y")%V. iFrame.
      iIntros (y k' ?) "Hy Hk'". ewp_pure_steps.
      ewp_bind_rule.
      iApply (ewp_store with "Hk'").
      iIntros "!> Hmc !>". simpl. ewp_pure_steps.
      iApply (ewp_throw with "[Hy Hm Hmc] Hk").
      iFrame. iExists m. by iFrame.
    }
    by iApply (abort_spec with "Ht").
  Qed.

  Lemma shift_spec (h : val) Φ Φ' :
    (∀ (k : val),
      □ (∀ (y : val) Φopt, Φ' y -∗ wpmc (k y) Φopt Φ) -∗
        wpmc (h k) (Some Φ) Φ) -∗
      wpmc (shift h) (Some Φ) Φ'.
  Proof.
    iIntros "Hh Hmc". unfold shift. ewp_pure_steps.
    iApply ewp_callcc. iIntros (k) "#Hk". simpl.
    ewp_pure_steps.
    iApply (abort_spec _ Φ). ewp_pure_steps.
    iApply ("Hh" with "[] Hmc").
    iIntros "!#" (y Φs') "Hy Hmc". ewp_pure_steps.
    iApply (reset_spec with "[Hy] Hmc").
    iIntros "Hmc". ewp_pure_steps.
    iApply (ewp_throw with "[Hmc Hy] Hk").
    simpl. by iFrame.
  Qed.

End shift_reset.
