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

Instance EmptyCtx_neutral : NeutralEctx [].
Proof. by constructor. Qed.
Instance ConsCtx_neutral f k :
  NeutralFrame f → NeutralEctx k → NeutralEctx (f :: k).
Proof. constructor. by apply Forall_cons; split; [|apply H0]. Qed.
Lemma ConsCtx_neutral_inv f k : NeutralEctx (f :: k) → NeutralEctx k.
Proof. inversion 1. by inversion neutral_ectx0. Qed.
Lemma ConsCtx_neutral_inv' f k : NeutralEctx (f :: k) → NeutralFrame f.
Proof. inversion 1. by inversion neutral_ectx0. Qed.

Instance AppLCtx_neutral v2 : NeutralFrame (AppLCtx v2).
Proof. constructor => m v k σ. by apply AppLEffS. Qed.
Instance AppRCtx_neutral e1 : NeutralFrame (AppRCtx e1).
Proof. constructor => m v k σ. by apply AppREffS. Qed.
Instance DoCtx_neutral m : NeutralFrame (DoCtx m).
Proof. constructor => m' v k σ. by apply DoEffS. Qed.
Instance UnOpCtx_neutral op : NeutralFrame (UnOpCtx op).
Proof. constructor => m v k σ. by apply UnOpEffS. Qed.
Instance BinOpLCtx_neutral op v2 : NeutralFrame (BinOpLCtx op v2).
Proof. constructor => m v k σ. by apply BinOpLEffS. Qed.
Instance BinOpRCtx_neutral op e1 : NeutralFrame (BinOpRCtx op e1).
Proof. constructor => m v k σ. by apply BinOpREffS. Qed.
Instance IfCtx_neutral e1 e2 : NeutralFrame (IfCtx e1 e2).
Proof. constructor => m v k σ. by apply IfEffS. Qed.
Instance PairLCtx_neutral v2 : NeutralFrame (PairLCtx v2).
Proof. constructor => m v k σ. by apply PairLEffS. Qed.
Instance PairRCtx_neutral e1 : NeutralFrame (PairRCtx e1).
Proof. constructor => m v k σ. by apply PairREffS. Qed.
Instance FstCtx_neutral : NeutralFrame FstCtx.
Proof. constructor => m v k σ. by apply FstEffS. Qed.
Instance SndCtx_neutral : NeutralFrame SndCtx.
Proof. constructor => m v k σ. by apply SndEffS. Qed.
Instance InjLCtx_neutral : NeutralFrame InjLCtx.
Proof. constructor => m v k σ. by apply InjLEffS. Qed.
Instance InjRCtx_neutral : NeutralFrame InjRCtx.
Proof. constructor => m v k σ. by apply InjREffS. Qed.
Instance CaseCtx_neutral e1 e2 : NeutralFrame (CaseCtx e1 e2).
Proof. constructor => m v k σ. by apply CaseEffS. Qed.
Instance AllocCtx_neutral : NeutralFrame AllocCtx.
Proof. constructor => m v k σ. by apply AllocEffS. Qed.
Instance LoadCtx_neutral : NeutralFrame LoadCtx.
Proof. constructor => m v k σ. by apply LoadEffS. Qed.
Instance StoreLCtx_neutral v2 : NeutralFrame (StoreLCtx v2).
Proof. constructor => m v k σ. by apply StoreLEffS. Qed.
Instance StoreRCtx_neutral e1 : NeutralFrame (StoreRCtx e1).
Proof. constructor => m v k σ. by apply StoreREffS. Qed.
Instance CmpXchgLCtx_neutral v2 v3 : NeutralFrame (CmpXchgLCtx v2 v3).
Proof. constructor => m v k σ. by apply CmpXchgLS. Qed.
Instance CmpXchgMCtx_neutral e1 v2 : NeutralFrame (CmpXchgMCtx e1 v2).
Proof. constructor => m v k σ. by apply CmpXchgMS. Qed.
Instance CmpXchgRCtx_neutral e1 e2 : NeutralFrame (CmpXchgRCtx e1 e2).
Proof. constructor => m v k σ. by apply CmpXchgRS. Qed.

Lemma TryWithCtx_not_neutral e2 e3 : ¬ NeutralFrame (TryWithCtx e2 e3).
Proof.
  intros ?. cut (head_step
    (TryWith (Eff MS (LitV LitUnit) []) e2 e3) {|heap:=∅|}
    (Eff MS (LitV LitUnit) [TryWithCtx e2 e3]) {|heap:=∅|} []);
  [inversion 1|apply H]; done.
Qed.
