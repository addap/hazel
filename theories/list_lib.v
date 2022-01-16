From stdpp              Require Import list.
From iris.proofmode     Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
From hazel              Require Import notation weakestpre cascade.

Class ListLib Σ `{!irisGS eff_lang Σ} := {
  list_nil  : val;
  list_cons : val;
  list_iter : val;

  is_list :
    val → list val → iProp Σ;

  list_nil_spec E :
    ⊢ EWP list_nil #() @ E {{ l, is_list l [] }};

  list_cons_spec E (l x : val) (xs : list val) :
    ▷ is_list l xs -∗
      EWP list_cons x l @ E {{ l', is_list l' (x :: xs) }};

  list_eff_iter_spec E
  (I : list val → iProp Σ) 
  (Ψ : iEff Σ)
  (l f : val) (xs : list val) :
    □ (∀ us v vs, ⌜ us ++ (v :: vs) = xs ⌝ →
       I (v :: vs) -∗ EWP f v @ E <| Ψ |> {{ _, I vs }}) -∗
    ▷ is_list l xs -∗
      ▷ I xs -∗
        EWP list_iter f l @ E <| Ψ |> {{ _, is_list l xs ∗ I [] }};
}.


Section DerivedLaws.

Context `{H: ListLib Σ}.

Lemma list_iter_spec' E I (l f : val) (xs : list val) :
  □ (∀ us v vs, ⌜ us ++ (v :: vs) = xs ⌝ →
    I (v :: vs) -∗ EWP f v @ E {{ _, I vs }}) -∗
  ▷ is_list l xs -∗
    ▷ I xs -∗
      EWP list_iter f l @ E {{ _, is_list l xs ∗ I [] }}.
Proof.
  iIntros "#f_spec Hlist HI".
  iApply ewp_mono; [|
  iApply (list_eff_iter_spec _ I ⊥%ieff with "[f_spec] Hlist HI") ].
  - by iIntros (?) "[$ $]".
  - iModIntro. iIntros (us v vs <-) "HI".
    by iSpecialize ("f_spec" $! us with "[//] HI").
Qed.

Lemma list_iter_spec E I (l f : val) (xs : list val) :
  □ (∀ us u vs, ⌜ (us ++ [u]) ++ vs = xs ⌝ →
    I us -∗ EWP f u @ E {{ _, I (us ++ [u]) }}) -∗
  ▷ is_list l xs -∗
    ▷ I [] -∗
      EWP list_iter f l @ E {{ _, is_list l xs ∗ I xs }}.
Proof.
  iIntros "#f_spec Hlist HI".
  iApply ewp_mono; [|
  iApply (list_iter_spec' _ (λ vs, I (take ((length xs) - (length vs)) xs))
    with "[f_spec] Hlist [HI]") ].
  - simpl. rewrite Nat.sub_0_r firstn_all. by auto.
  - iIntros (us v vs <-).
    rewrite (_ : length (us ++ v :: vs) - length (v :: vs) = length us); [|
    rewrite app_length; by lia ].
    rewrite (_ : length (us ++ v :: vs) - length vs = length (us ++ [v])); [|
    rewrite app_length app_length //=; by lia ].
    rewrite take_app cons_middle app_assoc take_app.
    iModIntro. iIntros "HI". by iApply ("f_spec" with "[//] HI").
  - by rewrite Nat.sub_diag firstn_O.
Qed.

End DerivedLaws.


Section ListLibModel.

Context `{!irisGS eff_lang Σ}.

Fixpoint list_encoding' (us : list val) : val :=
  match us with [] => InjLV #() | u :: us => InjRV (u, list_encoding' us) end.

Definition is_list' l us : iProp Σ := ⌜ l = list_encoding' us ⌝.
Instance is_list_persistent l us : Persistent (is_list' l us).
Proof. rewrite /is_list'. apply _. Qed.

Lemma is_list_nil : ⊢ is_list' (InjLV #()) [].
Proof. by iPureIntro. Qed.
Lemma is_list_cons l u us : is_list' l us -∗ is_list' (InjRV (u, l)) (u :: us).
Proof. iIntros "->". by iPureIntro. Qed.

Definition list_nil'  : val := λ: <>, InjLV #().
Definition list_cons' : val := λ: "u" "us", InjR ("u", "us").

Definition list_iter' : val := λ: "f",
  rec: "iter" "l" :=
    match: "l" with
      InjL <> => #()
    | InjR "p"=> "f" (Fst "p");; "iter" (Snd "p")
    end.

Lemma list_nil_spec' E :
  ⊢ EWP list_nil' #() @ E {{ l, is_list' l [] }}.
Proof.
  iApply ewp_pure_step. apply pure_prim_step_beta.
  by iApply ewp_value.
Qed.

Lemma list_cons_spec' E (l x : val) (xs : list val) :
  ▷ is_list' l xs -∗
    EWP list_cons' x l @ E {{ l', is_list' l' (x :: xs) }}.
Proof.
  iIntros "Hl".
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply (Ectxi_ewp_bind InjRCtx). done.
  iApply ewp_pure_step. apply pure_prim_step_pair.
  iApply ewp_value.
  iApply ewp_pure_step'. apply pure_prim_step_InjR.
  iApply ewp_value. iNext. by iApply is_list_cons.
Qed.

Lemma list_eff_iter_spec' E
  (I : list val → iProp Σ) 
  (Ψ : iEff Σ)
  (l f : val) (xs : list val) :
    □ (∀ us v vs, ⌜ us ++ (v :: vs) = xs ⌝ →
       I (v :: vs) -∗ EWP f v @ E <| Ψ |> {{ _, I vs }}) -∗
    ▷ is_list' l xs -∗
      ▷ I xs -∗
        EWP list_iter' f l @ E <| Ψ |> {{ _, is_list' l xs ∗ I [] }}.
Proof.
  iIntros "#f_spec #Hl HI".
  iApply (Ectxi_ewp_bind (AppLCtx _)). done.
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_pure_step. apply pure_prim_step_rec.
  iApply ewp_value.
  iInduction xs as [|x xs] "IH" forall (l).
  - iApply ewp_pure_step'. apply pure_prim_step_beta. simpl.
    iNext. iDestruct "Hl" as "->". simpl.
    iApply ewp_pure_step. apply pure_prim_step_case_InjL.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value.
    iApply ewp_pure_step'. apply pure_prim_step_beta.
    iApply ewp_value. by iFrame.
  - iApply ewp_pure_step'. apply pure_prim_step_beta. simpl.
    iNext. iDestruct "Hl" as "->". simpl.
    iApply ewp_pure_step. apply pure_prim_step_case_InjR.
    iApply (Ectxi_ewp_bind (AppLCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_rec.
    iApply ewp_value. simpl.
    iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
    iApply (Ectxi_ewp_bind (AppRCtx _)). done.
    iApply (Ectxi_ewp_bind (AppRCtx _)). done.
    iApply ewp_pure_step. apply pure_prim_step_Fst.
    iApply ewp_value. simpl.
    iApply (ewp_strong_mono E with "[HI]"). done.
    * by iApply ("f_spec" $! [] x xs).
    * by iApply iEff_le_refl.
    * iIntros (v) "HI". iModIntro. (*fold is_list'.*)
      iSpecialize ("IH" $! (list_encoding' xs) with "[f_spec] [//] HI").
      { iModIntro. iIntros (us w ws HH) "HI".
        iApply ("f_spec" $! (x :: us) w ws with "[] HI").
        iPureIntro. by rewrite <- HH.
      }
      iApply (Ectxi_ewp_bind (AppLCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_rec.
      iApply ewp_value. simpl.
      iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
      iApply (Ectxi_ewp_bind (AppRCtx _)). done.
      iApply ewp_pure_step. apply pure_prim_step_Snd.
      iApply ewp_value. simpl.
      iApply (ewp_mono with "IH").
      iIntros (_) "[Hl HI]". by iFrame.
Qed.

Program Instance ListLib_valid : ListLib Σ := {
  list_nil           := list_nil'; 
  list_cons          := list_cons';
  is_list            := is_list';
  list_iter          := list_iter';
  list_nil_spec      := list_nil_spec';
  list_cons_spec     := list_cons_spec';
  list_eff_iter_spec := list_eff_iter_spec'
}.

End ListLibModel.


Section IterLibModel.

Context `{!irisGS eff_lang Σ}.

Context (l : val) (xs : list val).

Definition iter : val := λ: "f", list_iter' "f" l.

Definition permitted us : iProp Σ := ∃ vs, ⌜ us ++ vs = xs ⌝.
Definition complete  us : iProp Σ := ⌜ us = xs ⌝.

Local Definition S  : iProp Σ := is_list' l xs.
Local Definition S' : iProp Σ := True.

Lemma iter_spec E (I : list val → iProp Σ)
                  (Ψ : iEff Σ) (f : val) :
  □ (∀ us u, permitted (us ++ [u]) -∗
     S' -∗
       I us -∗
         EWP f u @ E <| Ψ |> {{ _, S' ∗ I (us ++ [u]) }}) -∗
  S -∗
    I [] -∗
      EWP iter f @ E <| Ψ |> {{ _, ∃ xs, S ∗ I xs ∗ complete xs }}.
Proof.
  unfold iter, permitted, complete, S, S'.
  iIntros "#f_spec Hl HI".
  iApply ewp_pure_step. apply pure_prim_step_beta. simpl.
  iApply ewp_mono; [|
  iApply (list_eff_iter_spec' _
         (λ vs, I (take ((length xs) - (length vs)) xs))
    with "[] Hl [HI]") ].
  - simpl. rewrite Nat.sub_0_r firstn_all.
    iIntros (_) "[Hl HI]". iExists xs. by iFrame.
  - iModIntro. iIntros (us v vs <-).
    rewrite (_ : length (us ++ v :: vs) - length (v :: vs) = length us); [|
    rewrite app_length; by lia ].
    rewrite (_ : length (us ++ v :: vs) - length vs = length (us ++ [v])); [|
    rewrite app_length app_length //=; by lia ].
    rewrite take_app cons_middle app_assoc take_app.
    iIntros "HI".
    iApply ewp_mono; [| iApply ("f_spec" with "[] [//] HI") ].
    { by iIntros (_) "[_ HI]". }
    { by iExists vs. }
  - by rewrite Nat.sub_diag firstn_O.
Qed.

Program Instance IterLib_valid : IterLib Σ := {
  iter      := iter;
  permitted := permitted;
  complete  := complete;
  S         := S;
  S'        := S';
  iter_spec := iter_spec
}.

End IterLibModel.
