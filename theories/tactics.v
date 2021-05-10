From iris.proofmode Require Import base tactics classes.
From hazel          Require Export weakestpre.


(* The tactic [reshape_expr] was taken from
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

Ltac match_ewp_goal tac :=
  match goal with
  | [ |- @bi_emp_valid _                (ewp_def ?E ?e ?Ψ ?ϕ) ] => tac E e Ψ ϕ
  | [ |- @environments.envs_entails _ _ (ewp_def ?E ?e ?Ψ ?ϕ) ] => tac E e Ψ ϕ
  end.

Ltac ewp_bind_rule_tac _ e _ _ :=
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
       iApply (ewp_bind    K); [done|]
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

Ltac ewp_pure_step_tac _ e _ _ :=
  match e with
  | Val _ =>
     iApply ewp_value
  | TryWith (Val _) _ _ =>
     iApply (ewp_pure_step'); [apply pure_prim_step_try_with_val|]
  | Rec _ _ _ =>
     iApply (ewp_pure_step'); [apply pure_prim_step_rec|]
  | App (Val (RecV _ _ _)) (Val _) =>
     iApply (ewp_pure_step'); [apply pure_prim_step_beta|]
  | UnOp _ _ =>
     iApply (ewp_pure_step'); [apply pure_prim_step_unop|]
  | BinOp _ _ _ =>
     iApply (ewp_pure_step'); [apply pure_prim_step_binop|]
  | If (Val (LitV (LitBool _))) _ _ =>
     iApply (ewp_pure_step'); [apply pure_prim_step_if|]
  | Pair (Val _) (Val _) =>
     iApply (ewp_pure_step'); [apply pure_prim_step_pair|]
  | Fst (Val (PairV _ _)) =>
     iApply (ewp_pure_step'); [apply pure_prim_step_Fst|]
  | Snd (Val (PairV _ _)) =>
     iApply (ewp_pure_step'); [apply pure_prim_step_Snd|]
  | InjL (Val _) =>
     iApply (ewp_pure_step'); [apply pure_prim_step_InjL|]
  | InjR (Val _) =>
     iApply (ewp_pure_step'); [apply pure_prim_step_InjR|]
  | Case (Val (InjLV _)) _ _ =>
     iApply (ewp_pure_step'); [apply pure_prim_step_case_InjL|]
  | Case (Val (InjRV _)) _ _ =>
     iApply (ewp_pure_step'); [apply pure_prim_step_case_InjR|]
  end.

Ltac ewp_bind_rule :=
  match_ewp_goal ewp_bind_rule_tac.

Ltac ewp_pure_step :=
  match_ewp_goal ewp_pure_step_tac.

Ltac ewp_pure_steps :=
  repeat (ewp_bind_rule; simpl;
          ewp_pure_step; try iNext; simpl).
