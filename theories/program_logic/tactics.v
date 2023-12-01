(* tactics.v *)

(* In this file, we define simple tactics for manipulating a weakest
   precondition. In particular, we wish to automate two kinds of reasoning:
   the application of the bind rule and the application of the step rule.

   Because in this project we study more than one notion of weakest
   precondition, we try to achieve modularity with respect to the underlying
   definition of this notion. Therefore, we parameterize the core tactics with
   the lemma that proves either the bind rule or the step rule for the
   corresponding notion of weakest precondition.
*)

From iris.proofmode Require Import base tactics classes.
From language Require Import eff_lang.
From program_logic Require Export weakest_precondition basic_reasoning_rules.

(* ========================================================================== *)
(** Tactics. *)

(* -------------------------------------------------------------------------- *)

(* The tactic [reshape_expr] is a shameless copy of a homonym tactic in
   Tej Chajed's repository [iris-simp-lang].  *)
Ltac reshape_expr e tac :=
  let rec go k e :=
    match e with
    | Do ?m ?e              => add_item (DoCtx m) k e
    | App ?e (Val ?v)       => add_item (AppLCtx v) k e
    | App ?e1 ?e2           => add_item (AppRCtx e1) k e2
    | UnOp ?op ?e           => add_item (UnOpCtx op) k e
    | BinOp ?op ?e (Val ?v) => add_item (BinOpLCtx op v) k e
    | BinOp ?op ?e1 ?e2     => add_item (BinOpRCtx op e1) k e2
    | If ?e0 ?e1 ?e2        => add_item (IfCtx e1 e2) k e0
    | Pair ?e (Val ?v)      => add_item (PairLCtx v) k e
    | Pair ?e1 ?e2          => add_item (PairRCtx e1) k e2
    | Fst ?e                => add_item FstCtx k e
    | Snd ?e                => add_item SndCtx k e
    | InjL ?e               => add_item InjLCtx k e
    | InjR ?e               => add_item InjRCtx k e
    | Case ?e0 ?e1 ?e2      => add_item (CaseCtx e1 e2) k e0
    | Alloc ?e              => add_item AllocCtx k e
    | Load ?e               => add_item LoadCtx k e
    | Store ?e (Val ?v)     => add_item (StoreLCtx v) k e
    | Store ?e1 ?e2         => add_item (StoreRCtx e1) k e2

    | Val _                 => tac k e
    | Eff _ _ _             => tac k e
    | TryWith _ _ _         => tac k e
    | Var _                 => tac k e
    | Rec _ _ _             => tac k e
  end
  with add_item f k e := go (f :: k) e
  in go ([] : ectx) e.


(* The tactic [bind_rule_tac lemma e] computes an evaluation context [K]
   such that [e = K[e']] for some [e'], and applies [lemma] instantiated
   with [K]. This term [lemma] stands for the application of the bind rule
   of the corresponding weakest precondition.
*)
Ltac bind_rule_tac lemma e :=
  let reverse_ctx k :=
    let rec go acc k :=
      match k with
      | []       => acc
      | ?f :: ?k => go (f :: acc) k
      end
    in
    go ([] : ectx) k
  in

  let apply_bind_rule k :=
    match k with
    | []     => idtac
    | _ :: _ =>
       let k := reverse_ctx k in
       (lemma k); [done|]
    end
  in

  let tac k e :=
    match e with
    | Val ?v =>
       match k with
       | []      => idtac
       | _ :: ?k => apply_bind_rule k
       end
    | _ => apply_bind_rule k
    end
  in

  reshape_expr e tac.


(* The tactic [pure_step_tac lemma e] applies [lemma], which stands for the
   step rule of the corresponding weakest precondition. We assume that such
   lemma asks for a proof that [e] is related to an expression [e'] by a
   one-step reduction lemma. *)
Ltac pure_step_tac lemma e :=
  match e with
  | Val _ =>
     idtac
  | Do _ (Val _) =>
     idtac
  | TryWith (Val _) _ _ =>
     lemma; [apply pure_prim_step_TryWithVal|]
  | Rec _ _ _ =>
     lemma; [apply pure_prim_step_Rec|]
  | App (Val (RecV _ _ _)) (Val _) =>
     lemma; [apply pure_prim_step_beta|]
  | App (Val (KontV _)) (Val _) =>
     lemma; [apply pure_prim_step_Kont|]
  | UnOp _ _ =>
     lemma; [apply pure_prim_step_UnOp|]
  | BinOp _ _ _ =>
     lemma; [apply pure_prim_step_BinOp|]
  | If (Val (LitV (LitBool _))) _ _ =>
     lemma; [apply pure_prim_step_If|]
  | Pair (Val _) (Val _) =>
     lemma; [apply pure_prim_step_Pair|]
  | Fst (Val (PairV _ _)) =>
     lemma; [apply pure_prim_step_Fst|]
  | Snd (Val (PairV _ _)) =>
     lemma; [apply pure_prim_step_Snd|]
  | InjL (Val _) =>
     lemma; [apply pure_prim_step_InjL|]
  | InjR (Val _) =>
     lemma; [apply pure_prim_step_InjR|]
  | Case (Val (InjLV _)) _ _ =>
     lemma; [apply pure_prim_step_Case_InjL|]
  | Case (Val (InjRV _)) _ _ =>
     lemma; [apply pure_prim_step_Case_InjR|]
  end.


(** [EWP]-Specific Tactics. *)

Ltac match_ewp_goal lemma tac :=
  match goal with
  | [ |- @bi_emp_valid _                (ewp_def ?E ?e ?Ψ1 ?Ψ2 ?ϕ) ] => tac lemma e
  | [ |- @environments.envs_entails _ _ (ewp_def ?E ?e ?Ψ1 ?Ψ2 ?ϕ) ] => tac lemma e
  end.

(* Tactic for applying the lemma [ewp_pure_step']. *)
Ltac ewp_pure_step_lemma :=
  iApply ewp_pure_step_no_fork'.

(* Tactic for applying the lemma [ewp_bind]. *)
Ltac ewp_bind_rule_lemma k :=
  iApply (ewp_bind k).

(* The tactic [ewp_bind_rule]*)
Ltac ewp_bind_rule :=
  match_ewp_goal ewp_bind_rule_lemma bind_rule_tac.

(* The tactic [ewp_bind_rule]*)
Ltac ewp_pure_step :=
  match_ewp_goal ewp_pure_step_lemma pure_step_tac.

(* The tactic [ewp_value_or_step] either applies the reasoning rule
   for values ([ewp_value]) or applies the combination of the bind
   rule and the step rule. *)
Ltac ewp_value_or_step :=
  ((iApply ewp_value) || (ewp_bind_rule; ewp_pure_step));
  try iNext; simpl.

Ltac ewp_pure_steps :=
  repeat ewp_value_or_step.


(* -------------------------------------------------------------------------- *)
(** Tests. *)

From iris.program_logic Require Import weakestpre.

Section tests.
  Context `{!irisGS eff_lang Σ}.

  Goal forall Ψ, ⊢
    EWP
      (λ: <>, λ: <>, if: (#true && #false) then #() #() else #())%E #true #()
    <| Ψ |> {| Ψ |} {{ y, ⌜ y = #() ⌝ }}.
    iIntros (?). by ewp_pure_steps.
  Qed.

End tests.
