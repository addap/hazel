(* list_lib.v *)

(* This file introduces a simple API exposing operations for manipulating
   lists. This API is exploited to implement a scheduler
   [asynchronous_computation.v]. *)

From stdpp Require Import list.
From iris.proofmode Require Import base tactics classes.
From program_logic Require Import reasoning_rules.


(* ========================================================================== *)
(** * List Interface. *)

Class ListLib Σ `{!heapGS Σ} := {
  list_nil  : val;
  list_cons : val;
  list_iter : val;

  is_list :
    val → list val → iProp Σ;

  list_nil_spec E Ψ1 Ψ2 :
    ⊢ EWP list_nil #() @ E <| Ψ1 |> {| Ψ2 |} {{ l, is_list l [] }};

  list_cons_spec E Ψ1 Ψ2 (x : val) l xs :
    is_list l xs -∗
      EWP list_cons x l @ E <| Ψ1 |> {| Ψ2 |} {{ l', is_list l' (x :: xs) }};

  (* The specification of [list_iter] disallows multi-shot effects.
     If multi-shot effects were allowed, then the representation
     predicate [is_list] would have to be persistent (otherwise,
     there would be no way to argue that the list has not been
     compromised after multiple resumptions of the suspended iteration). *)
  list_iter_spec E
    (I : list val → iProp Σ) 
    (Ψ : iEff Σ)
    (f l : val) (xs : list val) :

    □ (∀ us u vs, ⌜ us ++ (u :: vs) = xs ⌝ →
        I us -∗
          EWP f u @ E <| Ψ |> {{ _, I (us ++ [u]) }})

    -∗

    is_list l xs -∗
      I [] -∗
        EWP list_iter f l @ E <| Ψ |> {{ _, is_list l xs ∗ I xs }};
}.


(* ========================================================================== *)
(** * Model. *)

(* We prove that the logical interface [ListLib] is inhabited; that is, it
   admits at least one implementation. *)

Section ListLibModel.
  Context `{!heapGS Σ}.

  (* ------------------------------------------------------------------------ *)
  (** Implementation. *)

  (* A list of values can be encoded as a single value. *)
  Fixpoint list_encoding' (us : list val) : val :=
    match us with
    | [] =>
        InjLV #()
    | u :: us =>
        InjRV (u, list_encoding' us)%V
    end.

  (* A value [l] _is the list_ [us] if it is the encoding of [us]. *)
  Definition is_list' l us : iProp Σ := ⌜ l = list_encoding' us ⌝.

  (* This representation predicate is persistent. *)
  Instance is_list_persistent l us : Persistent (is_list' l us).
  Proof. by rewrite /is_list'; apply _. Qed.

  (* List operations. *)
  Definition list_nil'  : val := (λ: <>, InjLV #())%V.
  Definition list_cons' : val := (λ: "u" "us", InjR ("u", "us"))%V.
  Definition list_iter' : val := (λ: "f",
    rec: "iter" "l" :=
      match: "l" with
        InjL <> =>
          #()
      | InjR "args" =>
          let: "u" := Fst "args" in
          let: "l" := Snd "args" in
          "f" "u";; "iter" "l"
      end
  )%V.


  (* ------------------------------------------------------------------------ *)
  (** Verification. *)

  Lemma list_nil_spec' E Ψ1 Ψ2 :
    ⊢ EWP list_nil' #() @ E <| Ψ1 |> {| Ψ2 |} {{ l, is_list' l [] }}.
  Proof. by unfold list_nil'; ewp_pure_steps. Qed.

  Lemma list_cons_spec' E Ψ1 Ψ2 (x : val) l xs :
    is_list' l xs -∗
      EWP list_cons' x l @ E <| Ψ1 |> {| Ψ2 |} {{ l', is_list' l' (x :: xs) }}.
  Proof. by iIntros "->"; unfold list_cons'; ewp_pure_steps. Qed.

  Lemma list_iter_spec' E
    (I : list val → iProp Σ) 
    (Ψ : iEff Σ)
    (f l : val) (xs : list val) :

    □ (∀ us u vs, ⌜ us ++ (u :: vs) = xs ⌝ →
        I us -∗
          EWP f u @ E <| Ψ |> {{ _, I (us ++ [u]) }})

    -∗

    is_list' l xs -∗
      I [] -∗
        EWP list_iter' f l @ E <| Ψ |> {{ _, is_list' l xs ∗ I xs }}.
  Proof.
    iIntros "#Hf #Hl HI". unfold list_iter'.
    do 3 ewp_value_or_step.
    (* Instead of strengthening the statement before apply induction,
       we apply the induction principle to the statement as is, but
       we generalize over the loop invariant [I]. Later, we specialize
       the induction hypothesis with the loop invariant [J vs = I (x :: vs)],
       where [x] is the head of [xs] in the inductive case. *)
    iInduction xs as [|x xs] "IH" forall (l I);
    iDestruct "Hl" as "->"; ewp_pure_steps; [by iFrame|].
    ewp_bind_rule. simpl.
    iApply (ewp_mono with "[HI]"); [
    by iApply ("Hf" $! [] x xs with "[//] HI")|].
    iIntros (v) "HI !>". simpl.
    do 3 ewp_value_or_step.
    set J : list val → iProp Σ := λ vs, I (x :: vs).
    iApply (ewp_mono with "[HI]").
    - iApply ("IH" $! (list_encoding' xs) J); try done.
      iIntros "!#" (us u vs) "%Heq HJ".
      by iApply ("Hf" $! (x :: us) u vs); [rewrite -Heq|].
    - by iIntros (_) "[_ $] !>".
  Qed.


  (* ------------------------------------------------------------------------ *)
  (** Instantiating the [ListLib] Interface. *)

  Program Instance ListLib_valid : ListLib Σ := {
    list_nil       := list_nil'; 
    list_cons      := list_cons';
    is_list        := is_list';
    list_iter      := list_iter';
    list_nil_spec  := list_nil_spec';
    list_cons_spec := list_cons_spec';
    list_iter_spec := list_iter_spec'
  }.

End ListLibModel.
