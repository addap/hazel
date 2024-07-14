(* neutral_contexts.v *)

(* This file introduces the notion of _neutral contexts_, which can be
   succinctly described as evaluation context without handler frames.
   This notion is useful in the statement of the [Bind Rule] of the program
   logic we shall derive for [eff_lang] in the file
   [program_logic/weakest_precondition.v].
*)

From language Require Import syntax semantics.

(* ========================================================================== *)
(** * Definition of Neutral Contexts. *)

Class NeutralFrame (f : frame) := {
  neutral_frame m v k σ :
    head_step (fill_frame f (Eff m v k)) σ (Eff m v (f :: k)) σ []
}.
Class NeutralEctx (k : ectx) := { neutral_ectx : Forall NeutralFrame k }.


(* ========================================================================== *)
(** * Instances of Neutral Contexts. *)

#[export]
Instance EmptyCtx_neutral : NeutralEctx [].
Proof. by constructor. Qed.
#[export]
Instance ConsCtx_neutral f k :
  NeutralFrame f → NeutralEctx k → NeutralEctx (f :: k).
Proof. constructor. by apply Forall_cons; split; [|apply H0]. Qed.
Lemma ConsCtx_neutral_inv f k : NeutralEctx (f :: k) → NeutralEctx k.
Proof. inversion 1. by inversion neutral_ectx0. Qed.
Lemma ConsCtx_neutral_inv' f k : NeutralEctx (f :: k) → NeutralFrame f.
Proof. inversion 1. by inversion neutral_ectx0. Qed.

#[export]
Instance AppLCtx_neutral v2 : NeutralFrame (AppLCtx v2).
Proof. constructor => m v k σ. by apply AppLEffS. Qed.
#[export]
Instance AppRCtx_neutral e1 : NeutralFrame (AppRCtx e1).
Proof. constructor => m v k σ. by apply AppREffS. Qed.
#[export]
Instance DoCtx_neutral m : NeutralFrame (DoCtx m).
Proof. constructor => m' v k σ. by apply DoEffS. Qed.
#[export]
Instance UnOpCtx_neutral op : NeutralFrame (UnOpCtx op).
Proof. constructor => m v k σ. by apply UnOpEffS. Qed.
#[export]
Instance BinOpLCtx_neutral op v2 : NeutralFrame (BinOpLCtx op v2).
Proof. constructor => m v k σ. by apply BinOpLEffS. Qed.
#[export]
Instance BinOpRCtx_neutral op e1 : NeutralFrame (BinOpRCtx op e1).
Proof. constructor => m v k σ. by apply BinOpREffS. Qed.
#[export]
Instance IfCtx_neutral e1 e2 : NeutralFrame (IfCtx e1 e2).
Proof. constructor => m v k σ. by apply IfEffS. Qed.
#[export]
Instance PairLCtx_neutral v2 : NeutralFrame (PairLCtx v2).
Proof. constructor => m v k σ. by apply PairLEffS. Qed.
#[export]
Instance PairRCtx_neutral e1 : NeutralFrame (PairRCtx e1).
Proof. constructor => m v k σ. by apply PairREffS. Qed.
#[export]
Instance FstCtx_neutral : NeutralFrame FstCtx.
Proof. constructor => m v k σ. by apply FstEffS. Qed.
#[export]
Instance SndCtx_neutral : NeutralFrame SndCtx.
Proof. constructor => m v k σ. by apply SndEffS. Qed.
#[export]
Instance InjLCtx_neutral : NeutralFrame InjLCtx.
Proof. constructor => m v k σ. by apply InjLEffS. Qed.
#[export]
Instance InjRCtx_neutral : NeutralFrame InjRCtx.
Proof. constructor => m v k σ. by apply InjREffS. Qed.
#[export]
Instance CaseCtx_neutral e1 e2 : NeutralFrame (CaseCtx e1 e2).
Proof. constructor => m v k σ. by apply CaseEffS. Qed.
#[export]
Instance AllocNLCtx_neutral v2 : NeutralFrame (AllocNLCtx v2).
Proof. constructor => m v k σ. by apply AllocNLEffS. Qed.
#[export]
Instance AllocNRCtx_neutral e1 : NeutralFrame (AllocNRCtx e1).
Proof. constructor => m v k σ. by apply AllocNREffS. Qed.
#[export]
Instance LoadCtx_neutral : NeutralFrame LoadCtx.
Proof. constructor => m v k σ. by apply LoadEffS. Qed.
#[export]
Instance StoreLCtx_neutral v2 : NeutralFrame (StoreLCtx v2).
Proof. constructor => m v k σ. by apply StoreLEffS. Qed.
#[export]
Instance StoreRCtx_neutral e1 : NeutralFrame (StoreRCtx e1).
Proof. constructor => m v k σ. by apply StoreREffS. Qed.
#[export]
Instance CmpXchgLCtx_neutral v2 v3 : NeutralFrame (CmpXchgLCtx v2 v3).
Proof. constructor => m v k σ. by apply CmpXchgLS. Qed.
#[export]
Instance CmpXchgMCtx_neutral e1 v2 : NeutralFrame (CmpXchgMCtx e1 v2).
Proof. constructor => m v k σ. by apply CmpXchgMS. Qed.
#[export]
Instance CmpXchgRCtx_neutral e1 e2 : NeutralFrame (CmpXchgRCtx e1 e2).
Proof. constructor => m v k σ. by apply CmpXchgRS. Qed.

Lemma TryWithCtx_not_neutral e2 e3 : ¬ NeutralFrame (TryWithCtx e2 e3).
Proof.
  intros ?. cut (head_step
    (TryWith (Eff MS (LitV LitUnit) []) e2 e3) {|heap:=∅|}
    (Eff MS (LitV LitUnit) [TryWithCtx e2 e3]) {|heap:=∅|} []);
  [inversion 1|apply H]; done.
Qed.
