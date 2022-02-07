(* tactics.v *)

(* In this file, we define simple tactics for manipulating a weakest
   precondition. In particular we wish to automate two kinds of reasoning:
   the application of the bind rule, and the application of the step rule.

   Because in this project we study more than one notion of weakest
   precondition, we try to achieve modularity with respect to the underlying
   definition of this notion. Thus, we parameterize the core tactics with the
   lemma that proves either the bind rule or the step rule for the
   corresponding notion of weakest precondition.
*)

From iris.proofmode Require Import base tactics classes.
From hazel          Require Export weakestpre.

(** General Tactics. *)

(* The tactic [reshape_expr] is a shameless copy of a homonym tactic in
   Tej Chajed's [iris-simp-lang] GitHub repository.
 *)
Ltac reshape_expr e tac :=
  let rec go K e :=
    match e with
    | Do ?e                 => add_item DoCtx K e
    | App ?e (Val ?v)       => add_item (AppLCtx v) K e
    | App ?e1 ?e2           => add_item (AppRCtx e1) K e2
    | UnOp ?op ?e           => add_item (UnOpCtx op) K e
    | BinOp ?op ?e (Val ?v) => add_item (BinOpLCtx op v) K e
    | BinOp ?op ?e1 ?e2     => add_item (BinOpRCtx op e1) K e2
    | If ?e0 ?e1 ?e2        => add_item (IfCtx e1 e2) K e0
    | Pair ?e (Val ?v)      => add_item (PairLCtx v) K e
    | Pair ?e1 ?e2          => add_item (PairRCtx e1) K e2
    | Fst ?e                => add_item FstCtx K e
    | Snd ?e                => add_item SndCtx K e
    | InjL ?e               => add_item InjLCtx K e
    | InjR ?e               => add_item InjRCtx K e
    | Case ?e0 ?e1 ?e2      => add_item (CaseCtx e1 e2) K e0
    | Alloc ?e              => add_item AllocCtx K e
    | Load ?e               => add_item LoadCtx K e
    | Store ?e (Val ?v)     => add_item (StoreLCtx v) K e
    | Store ?e1 ?e2         => add_item (StoreRCtx e1) K e2

    | Val _                 => tac K e
    | Eff _ _               => tac K e
    | TryWith _ _ _         => tac K e
    | Var _                 => tac K e
    | Rec _ _ _             => tac K e
  end
  with add_item Ki K e := go (ConsCtx Ki K) e
  in go EmptyCtx e.


(* The tactic [bind_rule_tac lemma e] computes an evaluation context [K]
   such that [e = K[e']] for some [e'], and applies [lemma] instantiated
   with [K]. This term [lemma] stands for the application of the bind rule
   of the corresponding weakest precondition.
*)
Ltac bind_rule_tac lemma e :=
  let reverse_ctx K :=
    let rec go acc K :=
      match K with
      | EmptyCtx       => acc
      | ConsCtx ?Ki ?K => go (ConsCtx Ki acc) K
      end
    in
    go EmptyCtx K
  in

  let apply_bind_rule K :=
    match K with
    | EmptyCtx    => idtac
    | ConsCtx _ _ =>
       let K := reverse_ctx K in
       (lemma K); [done|]
    end
  in

  let tac K e :=
    match e with
    | Val ?v =>
       match K with
       | EmptyCtx      => idtac
       | ConsCtx  _ ?K => apply_bind_rule K
       end
    | _ => apply_bind_rule K
    end
  in

  reshape_expr e tac.


(* The tactic [pure_step_tac lemma e] applies [lemma], which stands for the
   step rule of the corresponding weakest precondition. We assume that such
   lemma asks for a proof that [e] is related to an expression [e'] by a
   one-step reduction lemma.
*)
Ltac pure_step_tac lemma e :=
  match e with
  | Val _ =>
     idtac
  | Do (Val _) =>
     lemma; [apply pure_prim_step_do|]
  | TryWith (Val _) _ _ =>
     lemma; [apply pure_prim_step_try_with_val|]
  | Rec _ _ _ =>
     lemma; [apply pure_prim_step_rec|]
  | App (Val (RecV _ _ _)) (Val _) =>
     lemma; [apply pure_prim_step_beta|]
  | UnOp _ _ =>
     lemma; [apply pure_prim_step_unop|]
  | BinOp _ _ _ =>
     lemma; [apply pure_prim_step_binop|]
  | If (Val (LitV (LitBool _))) _ _ =>
     lemma; [apply pure_prim_step_if|]
  | Pair (Val _) (Val _) =>
     lemma; [apply pure_prim_step_pair|]
  | Fst (Val (PairV _ _)) =>
     lemma; [apply pure_prim_step_Fst|]
  | Snd (Val (PairV _ _)) =>
     lemma; [apply pure_prim_step_Snd|]
  | InjL (Val _) =>
     lemma; [apply pure_prim_step_InjL|]
  | InjR (Val _) =>
     lemma; [apply pure_prim_step_InjR|]
  | Case (Val (InjLV _)) _ _ =>
     lemma; [apply pure_prim_step_case_InjL|]
  | Case (Val (InjRV _)) _ _ =>
     lemma; [apply pure_prim_step_case_InjR|]
  end.


(** [ewp]-Specific Tactics. *)

Ltac match_ewp_goal lemma tac :=
  match goal with
  | [ |- @bi_emp_valid _                (ewp_def ?E ?e ?Ψ ?ϕ) ] => tac lemma e
  | [ |- @environments.envs_entails _ _ (ewp_def ?E ?e ?Ψ ?ϕ) ] => tac lemma e
  end.

(* Tactic for applying the lemma [ewp_pure_step']. *)
Ltac ewp_pure_step_lemma :=
  iApply ewp_pure_step'.

(* Tactic for applying the lemma [ewp_bind]. *)
Ltac ewp_bind_rule_lemma K :=
  iApply (ewp_bind K).

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


(* Tests. *)

From iris.program_logic  Require Import weakestpre.
From hazel               Require Import notation.

Section tests.
  Context `{!irisGS eff_lang Σ}.

  Goal forall Ψ, ⊢
    EWP
      (λ: <>, λ: <>, if: (#true && #false) then #() #() else #())%E #() #()
    <| Ψ |> {{ y, ⌜ y = #() ⌝ }}.
    iIntros (?). by ewp_pure_steps.
  Qed.

End tests.
