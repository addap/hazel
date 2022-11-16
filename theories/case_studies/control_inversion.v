(* control_inversion.v *)

(* The theory [iteration.v] proposes two interfaces to iterate an action over
   the elements of a data structure: (1) higher-order iteration methods and
   (2) lazy sequences. A higher-order iteration method [iter] is eager: given
   a function [f : 'a -> unit] describing the action over a single element of
   type ['a], it applies [f] to all the elements of the structure at once.
   Therefore, an iteration interface exposed by means of higher-order iteration
   methods privileges the _producer_, the data structure itself, in prejudice of
   the _consumer_, a client who wishes to iterate a data structure and who,
   consequently, must write the function [f]. A lazy sequence, in contrast,
   produces elements on demand, thereby privileging the consumer who can define
   the action over elements of the data structure one at a time.

   This seeming tension between iteration methods and lazy sequences is
   nonexistent if the language has support for control operators. Indeed, in
   such language, it is possible to define generic "inverters", that transform
   iteration methods into a lazy sequences. In this file, we implement, specify,
   and verify two such generic inverters. The first implementation is based on
   plain effect handlers for one-shot effects. The second implementation is
   based on [callcc] and [throw]. This second implementation exploits a common
   pattern (when programming with [callcc] and [throw]), which is to introduce
   a reference that is updated with the current evaluation context immediately
   before the instruction [throw] is performed. The evaluation context is thus
   not completely erased after a [throw]. *)

From stdpp Require Import list.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth.
From language Require Import eff_lang.
From program_logic Require Import reasoning_rules.
From case_studies Require Import iteration callcc.


(* ========================================================================== *)
(** * Implemenation. *)

Section implementation.

  (* ------------------------------------------------------------------------ *)
  (** Head Constructors. *)

  (* In OCaml, the type of sequences can be defined as follows:

       type 'a seq  = unit -> 'a head
        and 'a head = Nil | Cons of 'a * 'a seq

     In [eff_lang], we use binary sums to encode the inhabitants of the
     type ['a head]: *)
  Definition sCons (x k : expr) : expr := SOME (x, k)%E.
  Definition sNil               : val  := NONEV%V.


  (* ------------------------------------------------------------------------ *)
  (** Effect-Handler--Based Implementation. *)

  Definition invert : val := (λ: "iter", λ: <>,
    let: "yield" := λ: "x", do: "x" in
    deep-try: "iter" "yield" with
      effect λ: "x" "k", sCons "x" "k"
    | return λ: <>,      sNil
    end
  )%V.


  (* ------------------------------------------------------------------------ *)
  (** Callcc-Based Implementation. *)

  (* The function [yield x] jumps to the position stored in [r] (which is global
     in the scope of [yield]) with a [sCons] head. The second component of this
     pair is a closure that (1) updates [r] with its own position and (2) jumps
     back to the position where [yield] was called. *)
  Definition yield (r : expr) : expr := (λ: "x", callcc (λ: "kp",
    throw (Load r) (sCons "x" (λ: <>, callcc (λ: "kc",
      r <- "kc";; throw "kp" #()))))
  )%E.

  Definition invertcc : val := (λ: "iter", λ: <>, callcc (λ: "kc",
    let: "r" := ref "kc" in "iter" (yield "r");; throw (Load "r") sNil)
  )%V.

End implementation.


(* ========================================================================== *)
(** * Specification. *)

(* The specification of [invert] depends on (1) the specification of a
   iteration method [isIter] and (2) the specification of a lazy sequence
   [isSeq], both of which are introduced in the theory [iteration.v]. *)

Section specification.
  Context `{!irisGS eff_lang Σ}.
  Context  {G : Type → Type} `{DataStructure Σ G, Iterable G}
           {A : Type}        `{Representable Σ A}.

  (* ------------------------------------------------------------------------ *)
  (** Specification of [invert]. *)

  Definition invert_spec : iProp Σ :=
    (∀ (t : val) (T : G A) (iter : val),
      represents t T -∗
        isEffPolyIter t T (Only OS) iter -∗
          EWP invert (λ: "f", iter "f" t)%V {{ k,
            isSeq t T ⊥ ⊥ k [] }})%I.


  (* ------------------------------------------------------------------------ *)
  (** Specification of [invertcc]. *)

  Definition invertcc_spec : iProp Σ :=
    (∀ (t : val) (T : G A) (iter : val),
      represents t T -∗
        isIter t T ⊥ CT iter -∗
          EWP invertcc (λ: "f", iter "f" t)%V .{| CT |} {{ k,
            isSeq t T ⊥ CT k [] }})%I.

End specification.


(* ========================================================================== *)
(** * Verification. *)

Section verification.

  (* ------------------------------------------------------------------------ *)
  (** Ghost Theory. *)

  Section ghost_theory.
    Context {A : Type}.

    (* We use ghost variables with contents in the CMRA [Auth(Ex(List A))]. *)
    Context `{!inG Σ (excl_authR (leibnizO (list A)))}.

    (* The assertion [own γ (●E Ys)] states that the handler
       has seen the elements [Ys]. *)
    Definition handlerView γ Ys : iProp Σ :=
      own γ (●E (Ys : ofe_car (leibnizO (list A)))).
    (* The assertion [own γ (◯E Xs)] states that [iter]
       has seen the elements [Xs]. *)
    Definition iterView γ Xs : iProp Σ :=
      own γ (◯E (Xs : ofe_car (leibnizO (list A)))).

    (* Create a new ghost cell from this CMRA. *)
    (* In the verification of [invert], the ghost variable [γ]
       initially holds the empty list. *)
    Lemma new_cell Zs : ⊢ (|==> ∃ γ, handlerView γ Zs ∗ iterView γ Zs)%I.
    Proof.
      iMod (own_alloc ((●E (Zs : ofe_car (leibnizO (list A)))) ⋅
                       (◯E (Zs : ofe_car (leibnizO (list A)))))) as (γ) "[??]";
      [ apply excl_auth_valid | eauto with iFrame ]; done.
    Qed.

    (* Handler and [iter]'s views are in agreement. *)
    Lemma confront_views γ Ys Xs :
      handlerView γ Ys -∗ iterView γ Xs -∗ ⌜ Xs = Ys ⌝.
    Proof.
      iIntros "Hγ● Hγ◯".
      by iDestruct (own_valid_2 with "Hγ● Hγ◯") as %?%excl_auth_agree_L.
    Qed.

    (* With the ownership of both views, one can update the contents of [γ]. *)
    Lemma update_cell γ Zs Ys Xs :
      handlerView γ Ys -∗ iterView γ Xs ==∗ handlerView γ Zs  ∗ iterView γ Zs.
    Proof.
      iIntros "Hγ● Hγ◯".
      iMod (own_update_2 _ _ _ (●E (Zs : ofe_car (leibnizO (list A))) ⋅
                                ◯E (Zs : ofe_car (leibnizO (list A))))
        with "Hγ● Hγ◯") as "[$$]";
      [ apply excl_auth_update |]; done.
    Qed.

  End ghost_theory.


  (* ------------------------------------------------------------------------ *)
  (** Verification of [invert]. *)

  Section invert_correct.
    Context `{!heapGS Σ}.
    Context  {G : Type → Type} `{DataStructure Σ G, Iterable G}
             {A : Type}        `{Representable Σ A}.
    Context `{!inG Σ (excl_authR (leibnizO (list A)))}.

    (* This protocol describes the effects performed by [yield]. *)
    Definition Ψ_yield T (iterView : list A → iProp Σ) : iEff Σ :=
      (>> (x : val) Xs X >>
        !x   {{ iterView  Xs              ∗
                represents x X            ∗
                ⌜ permitted T (Xs ++ [X]) ⌝ }};
        ?#() {{ iterView (Xs ++ [X])      ∗
                represents x X              }} @ OS).

    (* The [yield] handler is correct. *)
    Lemma yield_handler_correct t T γ (Ys : list A) :
      handlerView γ Ys -∗
        deep_handler ⊤
         (* Handlee's one-shot protocol:  *)
           (Ψ_yield T (iterView γ))
         (* Handlee's multi-shot protocol:  *)
           ⊥
         (* Handlee's postcondition:  *)
           (λ _, represents t T ∗ ∃ (Xs : list A),
              iterView γ Xs ∗ ⌜ complete T Xs ⌝)

         (* Effect branch. *)
           (λ: "x" "k", sCons "x" "k")%V
         (* Return branch. *)
           (λ: <>, sNil)%V

         (* Handler's one-shot and multi-shot protocols: *)
           ⊥ ⊥
         (* Handler's postcondition: *)
           (λ h, isHead t T ⊥ ⊥ h Ys).
    Proof.
      iLöb as "IH" forall (Ys γ).
      rewrite !deep_handler_unfold /deep_handler_eq.
      iIntros "HhandlerView". iSplit; [|iSplit].
      - iIntros (v) "HΦ".
        iDestruct "HΦ" as "[Hrepr [%Xs [HiterView %Hcomplete]]]".
        iDestruct (confront_views with "HhandlerView HiterView") as "<-".
        unfold sNil. ewp_pure_steps. by iFrame.
      - iIntros (u k) "Hhandler".
        rewrite /(Ψ_yield T (iterView γ)).
        rewrite (upcl_tele' [tele _ _ _] [tele]) //=.
        iDestruct "Hhandler"
          as (x Xs X) "(<- & [HiterView [Hrepr %Hpermitted]] & Hk)".
        iApply fupd_ewp.
        iDestruct (confront_views with "HhandlerView HiterView") as %<-.
        iMod (update_cell _ (Xs ++ [X]) with "HhandlerView HiterView")
          as "[HhandlerView HiterView]".
        iModIntro.
        iSpecialize ("Hk" with "[HiterView Hrepr]"). { by iFrame. }
        unfold sCons. ewp_pure_steps. iExists X. iSplit; [done|]. iNext.
        rewrite !isSeq_unfold /isSeq_pre.
        iSpecialize ("IH" with "HhandlerView").
        by iApply ("Hk" with "IH").
      - iIntros (u k) "HFalse". by rewrite upcl_bottom.
    Qed.

    (* [invert] is correct. *)
    Lemma invert_correct : ⊢ invert_spec.
    Proof.
      iIntros (t T iter) "Hrepr Hiter". unfold invert.
      iApply fupd_ewp.
      iMod (new_cell []) as (γ) "[HhandlerView HiterView]".
      iModIntro. ewp_pure_steps.
      rewrite !isSeq_unfold isSeq_eq /isSeq_pre.
      ewp_pure_steps.
      iApply (ewp_deep_try_with with "[Hiter Hrepr HiterView]").
      - ewp_pure_steps.
        iApply ("Hiter" $! (Ψ_yield T (iterView γ)) _ (iterView γ)
          with "[] Hrepr HiterView").
        iModIntro. iIntros (Xs X x) "%Hpermitted HiterView Hrepr".
        ewp_pure_steps. iApply ewp_do_os. rewrite /Ψ_yield.
        rewrite (upcl_tele' [tele _ _ _] [tele]) //=.
        iExists x, Xs, X. iFrame. iSplit; [|iSplit]; try done.
        by iIntros "[$$]".
      - rewrite -isSeq_eq -isHead_unfold.
        by iApply (yield_handler_correct t T with "HhandlerView").
    Qed.

  End invert_correct.


  (* ------------------------------------------------------------------------ *)
  (** Verification of [invertcc]. *)

  Section invertcc_correct.
    Context `{!heapGS Σ}.
    Context  {G : Type → Type} `{DataStructure Σ G, Iterable G}
             {A : Type}        `{Representable Σ A}.

    (* [invertcc] is correct. *)
    Lemma invertcc_correct : ⊢ invertcc_spec.
    Proof.
      iIntros (t T iter) "Hrepr Hiter". unfold invertcc.
      ewp_pure_steps.
      rewrite !isSeq_unfold isSeq_eq /isSeq_pre.
      ewp_pure_steps.
      iApply ewp_callcc.
      iIntros (k) "Hk". simpl.
      iApply (ewp_bind' (AppRCtx _)). done.
      iApply ewp_alloc.
      iIntros "!>" (r) "Hr !>". simpl.
      ewp_pure_steps.
      set I : list A → iProp Σ := (λ Xs,
        ∃ (k : val),
          r ↦ k ∗ isCont k (λ h, isHead t T ⊥ CT h Xs))%I.
      iApply (ewp_pers_mono with "[Hiter Hrepr Hr Hk]").
      ewp_pure_steps.
      iApply ("Hiter" $! _ I with "[] Hrepr"); [|
      by iExists k; iFrame; rewrite -isSeq_eq ].
      - iIntros "!#" (Xs X x) "%Hpermitted [%kc [Hr #Hkc]] Hrepr".
        ewp_pure_steps.
        iApply ewp_callcc.
        iIntros (kp) "#Hkp". simpl.
        ewp_pure_steps. ewp_bind_rule.
        iApply (ewp_load with "Hr").
        iIntros "!> Hr !>". simpl.
        iApply (ewp_throw with "[Hrepr Hr] Hkc").
        simpl. iExists X. iSplit; [done|]. iNext.
        rewrite !isSeq_unfold /isSeq_pre.
        ewp_pure_steps.
        iApply ewp_callcc.
        iIntros (kc') "#Hkc'". simpl.
        ewp_bind_rule.
        iApply (ewp_store with "Hr").
        iIntros "!> Hr !>". simpl.
        ewp_pure_steps.
        iApply (ewp_throw with "[Hr Hrepr] Hkp"). simpl.
        iFrame. iExists kc'. by iFrame.
      - iIntros "!#" (v) "[Hrepr [%Xs [[%kc [Hr #Hkc]] #Hcomplete]]] !>". simpl.
        ewp_pure_steps. ewp_bind_rule.
        iApply (ewp_load with "Hr").
        iIntros "!> Hr !>". simpl.
        iApply (ewp_throw with "[Hrepr Hr] Hkc").
        by iFrame.
    Qed.

  End invertcc_correct.

End verification.
