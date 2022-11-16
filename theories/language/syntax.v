(* syntax.v *)

(* This file introduces the syntax of [eff_lang], a simple programming
   language with support for many common programming features, such as
   first-class functions and dynamically allocated (higher-order)
   mutable state; and, what is its singularity, with support for effect
   handlers and (consequently) first-class continuations.

   First-class continuations come in two flavors: either multi-shot or
   one-shot. One-shot continuations can be invoked at most once, whereas
   multi-shot continuations can be invoked multiple times.

   The nature of the continuation (one-shot or multi-shot) is specified
   at the moment an effect is performed. Therefore, the effect construct
   includes one bit of information [m], a _mode_, to indicate whether the
   evaluation context up to its innermost handler must be captured as
   a multi-shot continuation or as a one-shot continuation.

   The semantics of [eff_lang] is defined in the file [semantics.v],
   but we anticipate that handlers follow a _shallow-handler semantics_:
   the captured continuation does *not* include a copy of the handler as
   its topmost frame; in other words, invoking a continuation does *not*
   reinstall the handler.
*)


From stdpp Require Export binders strings. (* Representation of binders. *)
From stdpp Require Export gmap. (* Representation of the heap. *)

From iris.algebra Require Export ofe. (* Sets >--> Discrete OFEs. *)
From iris.heap_lang Require Export locations. (* Domain of locations. *)

Set Default Proof Using "Type".

Delimit Scope expr_scope with E.
Delimit Scope val_scope  with V.


(* ========================================================================== *)
(** * Syntax Definition. *)

(* Definition of the syntax of expressions, values, frames, and
   evaluation contexts. *)

Section eff_lang.

  (* Base values of [eff_lang]. *)
  Inductive base_lit : Set :=
    | LitInt (n : Z)
    | LitBool (b : bool)
    | LitUnit
    | LitLoc (l : loc).

  (* Unary operations. *)
  Inductive un_op : Set :=
    | NegOp
    | MinusUnOp.

  (* Binary operations. *)
  Inductive bin_op : Set :=
    (* Arithmetic. *)
    | PlusOp | MinusOp | MultOp | QuotOp | RemOp
    (* Bitwise. *)
    | AndOp | OrOp | XorOp
    (* Shifts. *)
    | ShiftLOp | ShiftROp
    (* Comparison. *)
    | LeOp | LtOp | EqOp.

  (* Mode of capture. *)
  Inductive mode : Set :=
    (* One-shot. *)
    | OS
    (* Multi-shot. *)
    | MS.

  (* Expressions. *)
  Inductive expr :=
    (* Values. *)
    | Val (v : val)
    (* Effects. *)
    | Do (m : mode) (e : expr)
    | Eff (m : mode) (v : val) (k : list frame)
    | TryWith (e1 e2 e3 : expr)
    (* λ-calculus. *)
    | Var (x : string)
    | Rec (f x : binder) (e : expr)
    | App (e1 e2 : expr)
    (* Operations. *)
    | UnOp (op : un_op) (e : expr)
    | BinOp (op : bin_op) (e1 e2 : expr)
    (* Conditional. *)
    | If (e0 e1 e2 : expr)
    (* Products. *)
    | Pair (e1 e2 : expr)
    | Fst (e : expr)
    | Snd (e : expr)
    (* Sums. *)
    | InjL (e : expr)
    | InjR (e : expr)
    | Case (e0 e1 e2 : expr)
    (* Heap. *)
    | Alloc (e : expr)
    | Load (e : expr)
    | Store (e1 e2 : expr)

  (* Values. *)
  with val :=
    (* Base values. *)
    | LitV (l : base_lit)
    (* First-class functions. *)
    | RecV (f x : binder) (e : expr)
    (* Products. *)
    | PairV (v1 v2 : val)
    (* Sums. *)
    | InjLV (v : val)
    | InjRV (v : val)
    (* One-shot continuations. *)
    (* The location [l] stores a Boolean indicating
       whether the continuation has been called.
       It is used in file [semantics.v] to implement
       the one-shot policy. *)
    | ContV (k : list frame) (l : loc)
    (* Multi-shot continuations. *)
    | KontV (k : list frame)

  (* Frames. *)
  with frame :=
    (* Application. *)
    (* The following frames impose a right-to-left evaluation order. *)
    | AppLCtx (v2 : val)
    | AppRCtx (e1 : expr)
    (* Effects. *)
    | DoCtx (m : mode)
    | TryWithCtx (e2 e3 : expr)
    (* Unary operation. *)
    | UnOpCtx (op : un_op)
    (* Binary operation. *)
    | BinOpLCtx (op : bin_op) (v2 : val)
    | BinOpRCtx (op : bin_op) (e1 : expr)
    (* Conditional. *)
    | IfCtx (e1 e2 : expr)
    (* Products. *)
    | PairLCtx (v2 : val)
    | PairRCtx (e1 : expr)
    | FstCtx
    | SndCtx
     (* Sums. *)
    | InjLCtx
    | InjRCtx
    | CaseCtx (e1 e2 : expr)
    (* Heap. *)
    | AllocCtx
    | LoadCtx
    | StoreLCtx (v2 : val)
    | StoreRCtx (e1 : expr).

  (* Evaluation contexts. *)
  Definition ectx := list frame.

  (* Heaps. *)
  Record state : Type := { heap: gmap loc val }.

End eff_lang.


(* -------------------------------------------------------------------------- *)
(** Simple Definitions. *)

Notation of_val := Val (only parsing).
Definition to_val (e : expr) : option val :=
  match e with Val v => Some v | _ => None end.
Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.
Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? [=]. Qed.

Notation of_eff := Eff (only parsing).
Definition to_eff (e : expr) : option (mode * val * ectx) :=
  match e with Eff m v k => Some (m, v, k) | _ => None end.
Lemma of_to_eff e m v k : to_eff e = Some (m, v, k) → of_eff m v k = e.
Proof. destruct e=>//=. by intros [= <- <- <-]. Qed.
Lemma of_eff_inj m1 v1 k1 m2 v2 k2 :
  of_eff m1 v1 k1 = of_eff m2 v2 k2 → m1 = m2 ∧ v1 = v2 ∧ k1 = k2.
Proof. by intros [= -> -> ->]. Qed.


(* ========================================================================== *)
(** * Induction Principle. *)

(* The induction principle for [expr] auto-generated by Coq is not
   sufficiently strong, because [expr] is a _nested inductive type_:
   the constructor [Eff v k], for example, carries a list of frames
   [k], and a frame may carry an expression. Therefore, we derive
   custom induction principles for [expr], [val], [frame], and [ectx]. *)

Section induction_principle.
  Variables (P : expr  → Type)
            (Q : val   → Type)
            (R : frame → Type)
            (S : ectx  → Type).

  Hypothesis
  (* Expressions. *)
    (* Values. *)
    (Val_case : ∀ v, Q v → P (Val v))
    (* Effects. *)
    (Do_case : ∀ m e, P e → P (Do m e))
    (Eff_case : ∀ m v k, Q v → S k → P (Eff m v k))
    (TryWith_case : ∀ e1 e2 e3, P e1 → P e2 → P e3 → P (TryWith e1 e2 e3))
    (* λ-calculus. *)
    (Var_case : ∀ b, P (Var b))
    (Rec_case : ∀ f x e, P e → P (Rec f x e))
    (App_case : ∀ e1 e2, P e1 → P e2 → P (App e1 e2))
    (* Operations. *)
    (UnOp_case : ∀ op e, P e → P (UnOp op e))
    (BinOp_case : ∀ op e1 e2, P e1 → P e2 → P (BinOp op e1 e2))
    (* Conditional. *)
    (If_case : ∀ e1 e2 e3, P e1 → P e2 → P e3 → P (If e1 e2 e3))
    (* Products. *)
    (Pair_case : ∀ e1 e2, P e1 → P e2 → P (Pair e1 e2))
    (Fst_case : ∀ e, P e → P (Fst e))
    (Snd_case : ∀ e, P e → P (Snd e))
    (* Sums. *)
    (InjL_case : ∀ e, P e → P (InjL e))
    (InjR_case : ∀ e, P e → P (InjR e))
    (Case_case : ∀ e0 e1 e2, P e0 → P e1 → P e2 → P (Case e0 e1 e2))
    (* Heap. *)
    (Alloc_case : ∀ e, P e → P (Alloc e))
    (Load_case : ∀ e, P e → P (Load e))
    (Store_case : ∀ e1 e2, P e1 → P e2 → P (Store e1 e2))

  (* Values. *)
    (* Base values. *)
    (LitV_case : ∀ l, Q (LitV l))
    (* First-class functions. *)
    (RecV_case : ∀ f x e, P e → Q (RecV f x e))
    (* Products. *)
    (PairV_case : ∀ v1 v2, Q v1 → Q v2 → Q (PairV v1 v2))
    (* Sums. *)
    (InjLV_case : ∀ v, Q v → Q (InjLV v))
    (InjRV_case : ∀ v, Q v → Q (InjRV v))
    (* One-shot continuations. *)
    (ContV_case : ∀ k l, S k → Q (ContV k l))
    (* Multi-shot continuations. *)
    (KontV_case : ∀ k, S k → Q (KontV k))

  (* Frames. *)
    (* Application. *)
    (AppLCtx_case : ∀ v2, Q v2 → R (AppLCtx v2))
    (AppRCtx_case : ∀ e1, P e1 → R (AppRCtx e1))
    (* Effects. *)
    (DoCtx_case : ∀ m, R (DoCtx m))
    (TryWithCtx_case : ∀ e2 e3, P e2 → P e3 → R (TryWithCtx e2 e3))
    (* Unary operation. *)
    (UnOpCtx_case : ∀ op, R (UnOpCtx op))
    (* Binary operation. *)
    (BinOpLCtx_case : ∀ op v2, Q v2 → R (BinOpLCtx op v2))
    (BinOpRCtx_case : ∀ op e1, P e1 → R (BinOpRCtx op e1))
    (* Conditional. *)
    (IfCtx_case : ∀ e1 e2, P e1 → P e2 → R (IfCtx e1 e2))
    (* Products. *)
    (PairLCtx_case : ∀ v2, Q v2 → R (PairLCtx v2))
    (PairRCtx_case : ∀ e1, P e1 → R (PairRCtx e1))
    (FstCtx_case : R FstCtx)
    (SndCtx_case : R SndCtx)
    (* Sums. *)
    (InjLCtx_case : R InjLCtx)
    (InjRCtx_case : R InjRCtx)
    (CaseCtx_case : ∀ e1 e2, P e1 → P e2 → R (CaseCtx e1 e2))
    (* Heap. *)
    (AllocCtx_case : R AllocCtx)
    (LoadCtx_case : R LoadCtx)
    (StoreLCtx_case : ∀ v2, Q v2 → R (StoreLCtx v2))
    (StoreRCtx_case : ∀ e1, P e1 → R (StoreRCtx e1))

  (* Evaluation contexts. *)
    (EmptyCtx_case : S [])
    (ConsCtx_case : ∀ (f : frame) (k : ectx), R f → S k → S (f :: k)).

  Definition expr_ind_pre
    (expr_ind : ∀ e, P e)
    (val_ind : ∀ v, Q v)
    (frame_ind : ∀ f, R f) : ∀ e, P e := λ e,
    match e with
    | Val v =>
        Val_case v (val_ind v)
    | Do m e =>
        Do_case m e (expr_ind e)
    | Eff m v k =>
        Eff_case m v k (val_ind v) (
          (fix ectx_ind k {struct k} : S k :=
            match k with
            | [] => EmptyCtx_case
            | f :: k => ConsCtx_case f k (frame_ind f) (ectx_ind k)
          end) k)
    | TryWith e1 e2 e3 =>
        TryWith_case e1 e2 e3 (expr_ind e1) (expr_ind e2) (expr_ind e3)
    | Var b =>
        Var_case b
    | Rec f x e =>
        Rec_case f x e (expr_ind e)
    | App e1 e2 =>
        App_case e1 e2 (expr_ind e1) (expr_ind e2)
    | UnOp op e =>
        UnOp_case op e (expr_ind e)
    | BinOp op e1 e2 =>
        BinOp_case op e1 e2 (expr_ind e1) (expr_ind e2)
    | If e1 e2 e3 =>
        If_case e1 e2 e3 (expr_ind e1) (expr_ind e2) (expr_ind e3)
    | Pair e1 e2 =>
        Pair_case e1 e2 (expr_ind e1) (expr_ind e2)
    | Fst e =>
        Fst_case e (expr_ind e)
    | Snd e =>
        Snd_case e (expr_ind e)
    | InjL e =>
        InjL_case e (expr_ind e)
    | InjR e =>
        InjR_case e (expr_ind e)
    | Case e0 e1 e2 =>
        Case_case e0 e1 e2 (expr_ind e0) (expr_ind e1) (expr_ind e2)
    | Alloc e =>
        Alloc_case e (expr_ind e)
    | Load e =>
        Load_case e (expr_ind e)
    | Store e1 e2 =>
        Store_case e1 e2 (expr_ind e1) (expr_ind e2)
    end.

  Definition val_ind_pre
    (expr_ind  : ∀ e, P e)
    (val_ind : ∀ v, Q v)
    (frame_ind : ∀ f, R f) : ∀ v, Q v := λ v,
    match v with
    | LitV l =>
        LitV_case l
    | RecV f x e =>
        RecV_case f x e (expr_ind e)
    | PairV v1 v2 =>
        PairV_case v1 v2 (val_ind v1) (val_ind v2)
    | InjLV v =>
        InjLV_case v (val_ind v)
    | InjRV v =>
        InjRV_case v (val_ind v)
    | ContV k l =>
        ContV_case k l (
          (fix ectx_ind k {struct k} : S k :=
            match k with
            | [] => EmptyCtx_case
            | f :: k => ConsCtx_case f k (frame_ind f) (ectx_ind k)
          end) k)
    | KontV k =>
        KontV_case k (
          (fix ectx_ind k {struct k} : S k :=
            match k with
            | [] => EmptyCtx_case
            | f :: k => ConsCtx_case f k (frame_ind f) (ectx_ind k)
          end) k)
    end.

  Definition frame_ind_pre
    (expr_ind : ∀ e, P e)
    (val_ind : ∀ v, Q v) : ∀ f, R f := λ f,
    match f with
    | AppLCtx v2 =>
        AppLCtx_case v2 (val_ind v2)
    | AppRCtx e1 =>
        AppRCtx_case e1 (expr_ind e1)
    | DoCtx m =>
        DoCtx_case m
    | TryWithCtx e2 e3 =>
        TryWithCtx_case e2 e3 (expr_ind e2) (expr_ind e3)
    | UnOpCtx op =>
        UnOpCtx_case op
    | BinOpLCtx op v2 =>
        BinOpLCtx_case op v2 (val_ind v2)
    | BinOpRCtx op e1 =>
        BinOpRCtx_case op e1 (expr_ind e1)
    | IfCtx e1 e2 =>
        IfCtx_case e1 e2 (expr_ind e1) (expr_ind e2)
    | PairLCtx v2 =>
        PairLCtx_case v2 (val_ind v2)
    | PairRCtx e1 =>
        PairRCtx_case e1 (expr_ind e1)
    | FstCtx =>
        FstCtx_case
    | SndCtx =>
        SndCtx_case
    | InjLCtx =>
        InjLCtx_case
    | InjRCtx =>
        InjRCtx_case
    | CaseCtx e1 e2 =>
        CaseCtx_case e1 e2 (expr_ind e1) (expr_ind e2)
    | AllocCtx =>
        AllocCtx_case
    | LoadCtx =>
        LoadCtx_case
    | StoreLCtx v2 =>
        StoreLCtx_case v2 (val_ind v2)
    | StoreRCtx e1 =>
        StoreRCtx_case e1 (expr_ind e1)
    end.

  Definition ectx_ind_pre
    (frame_ind : ∀ f, R f)
    (ectx_ind : ∀ k, S k) : ∀ k, S k := λ k,
    match k with
    | [] => EmptyCtx_case
    | f :: k => ConsCtx_case f k (frame_ind f) (ectx_ind k)
    end.

  Definition expr_ind' : ∀ e, P e :=
    fix expr_ind e := expr_ind_pre expr_ind val_ind frame_ind e
    with val_ind v := val_ind_pre expr_ind val_ind frame_ind v
    with frame_ind f := frame_ind_pre expr_ind val_ind f
    for expr_ind.

  Definition val_ind' : ∀ v, Q v :=
    fix expr_ind e := expr_ind_pre expr_ind val_ind frame_ind e
    with val_ind v := val_ind_pre expr_ind val_ind frame_ind v
    with frame_ind f := frame_ind_pre expr_ind val_ind f
    for val_ind.

  Definition frame_ind' : ∀ f, R f :=
    fix expr_ind e := expr_ind_pre expr_ind val_ind frame_ind e
    with val_ind v := val_ind_pre expr_ind val_ind frame_ind v
    with frame_ind f := frame_ind_pre expr_ind val_ind f
    for frame_ind.

  Definition ectx_ind' : ∀ k, S k :=
    fix ectx_ind k := ectx_ind_pre frame_ind' ectx_ind k.

End induction_principle.


(* ========================================================================== *)
(** * Properties. *)

(* -------------------------------------------------------------------------- *)
(** Decidable Equality. *)

(* We prove that [expr], [val], [frame], and [ectx] have decidable equality. *)

Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Instance mode_dec : EqDecision mode.
Proof. solve_decision. Defined.

Section eq_decidable.

  Notation eq_dec :=
    (λ (A : Type), λ (x : A), ∀ y, Decision (x = y)) (only parsing).

  Notation P := (eq_dec  expr) (only parsing).
  Notation Q := (eq_dec   val) (only parsing).
  Notation R := (eq_dec frame) (only parsing).
  Notation S := (eq_dec  ectx) (only parsing).

  (* Expressions. *)
  Definition eq_dec_Val_case v (Hv : Q v) : P (Val v).
    refine (λ e',
      match e' with
      | Val v' => cast_if (Hv v')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_Do_case m e (He : P e) : P (Do m e).
    refine (λ e',
      match e' with
      | Do m' e' => cast_if_and (decide (m = m')) (He e')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_Eff_case m v k (Hv : Q v) (Hk : S k) : P (Eff m v k).
    refine (λ e',
      match e' with
      | Eff m' v' k' => cast_if_and3 (decide (m = m')) (Hv v') (Hk k')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_TryWith_case e1 e2 e3
    (He1: P e1) (He2 : P e2) (He3 : P e3) : P (TryWith e1 e2 e3).
    refine (λ e',
      match e' with
      | TryWith e1' e2' e3' => cast_if_and3 (He1 e1') (He2 e2') (He3 e3')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_Var_case x : P (Var x).
    refine (λ e',
      match e' with
      | Var x' => cast_if (decide (x = x'))
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_Rec_case f x e (He : P e) : P (Rec f x e).
    refine (λ e',
      match e' with
      | Rec f' x' e' => cast_if_and3 (decide (f = f')) (decide (x = x')) (He e')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_App_case e1 e2 (He1 : P e1) (He2 : P e2) : P (App e1 e2).
    refine (λ e',
      match e' with
      | App e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_UnOp_case op e (He : P e) : P (UnOp op e).
    refine (λ e',
      match e' with
      | UnOp op' e' => cast_if_and (decide (op = op')) (He e')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_BinOp_case op e1 e2
    (He1 : P e1) (He2 : P e2 ) : P (BinOp op e1 e2).
    refine (λ e',
      match e' with
      | BinOp op' e1' e2' => cast_if_and3 (decide (op = op')) (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_If_case e1 e2 e3
    (He1 : P e1) (He2 : P e2) (He3 : P e3) : P (If e1 e2 e3).
    refine (λ e',
      match e' with
      | If e1' e2' e3' => cast_if_and3 (He1 e1') (He2 e2') (He3 e3')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_Pair_case e1 e2
    (He1 : P e1) (He2 : P e2 ) : P (Pair e1 e2).
    refine (λ e',
      match e' with
      | Pair e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_Fst_case e (He : P e) : P (Fst e).
    refine (λ e',
      match e' with
      | Fst e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_Snd_case e (He : P e) : P (Snd e).
    refine (λ e',
      match e' with
      | Snd e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_InjL_case e (He : P e) : P (InjL e).
    refine (λ e',
      match e' with
      | InjL e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_InjR_case e (He : P e) : P (InjR e).
    refine (λ e',
      match e' with
      | InjR e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_Case_case e0 e1 e2
    (He0 : P e0) (He1 : P e1) (He2 : P e2) : P (Case e0 e1 e2).
    refine (λ e',
      match e' with
      | Case e0' e1' e2' => cast_if_and3 (He0 e0') (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_Alloc_case e (He : P e) : P (Alloc e).
    refine (λ e',
      match e' with
      | Alloc e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_Load_case e (He : P e) : P (Load e).
    refine (λ e',
      match e' with
      | Load e' => cast_if (He e')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_Store_case e1 e2
    (He1 : P e1) (He2 : P e2) : P (Store e1 e2).
    refine (λ e',
      match e' with
      | Store e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Qed.

  (* Values. *)
  Definition eq_dec_LitV_case l : Q (LitV l).
    refine (λ v',
      match v' with
      | LitV l' => cast_if (decide (l = l'))
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_RecV_case f x e (He : P e) : Q (RecV f x e).
    refine (λ v',
      match v' with
      | RecV f' x' e' => cast_if_and3 (decide (f = f')) (decide (x = x')) (He e')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_PairV_case v1 v2 (Hv1 : Q v1) (Hv2 : Q v2) : Q (PairV v1 v2).
    refine (λ v',
      match v' with
      | PairV v1' v2' => cast_if_and (Hv1 v1') (Hv2 v2')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_InjLV_case v (Hv : Q v) : Q (InjLV v).
    refine (λ v',
      match v' with
      | InjLV v' => cast_if (Hv v')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_InjRV_case v (Hv : Q v) : Q (InjRV v).
    refine (λ v',
      match v' with
      | InjRV v' => cast_if (Hv v')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_ContV_case k l (Hk : S k) : Q (ContV k l).
    refine (λ v',
      match v' with
      | ContV k' l' => cast_if_and (Hk k') (decide (l = l'))
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_KontV_case k (Hk : S k) : Q (KontV k).
    refine (λ v',
      match v' with
      | KontV k' => cast_if (Hk k')
      | _ => right _
      end); congruence.
  Qed.

  (* Frames. *)
  Definition eq_dec_AppLCtx_case v2 (Hv2 : Q v2) : R (AppLCtx v2).
    refine (λ f',
      match f' with
      | AppLCtx v2' => cast_if (Hv2 v2')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_AppRCtx_case e1 (He1 : P e1) : R (AppRCtx e1).
    refine (λ f',
      match f' with
      | AppRCtx e1' => cast_if (He1 e1')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_DoCtx_case m : R (DoCtx m).
    refine (λ f',
      match f' with
      | DoCtx m' => cast_if (decide (m = m'))
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_TryWithCtx_case e2 e3
    (He2 : P e2) (He3 : P e3) : R (TryWithCtx e2 e3).
    refine (λ f',
      match f' with
      | TryWithCtx e2' e3' => cast_if_and (He2 e2') (He3 e3')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_UnOpCtx_case op : R (UnOpCtx op).
    refine (λ f',
      match f' with
      | UnOpCtx op' => cast_if (decide (op = op'))
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_BinOpLCtx_case op v2 (Hv2 : Q v2) : R (BinOpLCtx op v2).
    refine (λ f',
      match f' with
      | BinOpLCtx op' v2' => cast_if_and (decide (op = op')) (Hv2 v2')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_BinOpRCtx_case op e1 (He1 : P e1) : R (BinOpRCtx op e1).
    refine (λ f',
      match f' with
      | BinOpRCtx op' e1' => cast_if_and (decide (op = op')) (He1 e1')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_IfCtx_case e1 e2 (He1 : P e1) (He2 : P e2) : R (IfCtx e1 e2).
    refine (λ f',
      match f' with
      | IfCtx e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_PairLCtx_case v2 (Hv2 : Q v2) : R (PairLCtx v2).
    refine (λ f',
      match f' with
      | PairLCtx v2' => cast_if (Hv2 v2')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_PairRCtx_case e1 (He1 : P e1) : R (PairRCtx e1).
    refine (λ f',
      match f' with
      | PairRCtx e1' => cast_if (He1 e1')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_FstCtx_case : R FstCtx.
    by refine (λ f', match f' with FstCtx => left _ | _ => right _ end). Qed.
  Definition eq_dec_SndCtx_case : R SndCtx.
    by refine (λ f', match f' with SndCtx => left _ | _ => right _ end). Qed.
  Definition eq_dec_InjLCtx_case : R InjLCtx.
    by refine (λ f', match f' with InjLCtx => left _ | _ => right _ end). Qed.
  Definition eq_dec_InjRCtx_case : R InjRCtx.
    by refine (λ f', match f' with InjRCtx => left _ | _ => right _ end). Qed.
  Definition eq_dec_CaseCtx_case e1 e2 (He1 : P e1) (He2 : P e2) : R (CaseCtx e1 e2).
    refine (λ f',
      match f' with
      | CaseCtx e1' e2' => cast_if_and (He1 e1') (He2 e2')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_AllocCtx_case : R AllocCtx.
    by refine (λ f', match f' with AllocCtx => left _ | _ => right _ end). Qed.
  Definition eq_dec_LoadCtx_case : R LoadCtx.
    by refine (λ f', match f' with LoadCtx => left _ | _ => right _ end). Qed.
  Definition eq_dec_StoreLCtx_case v2 (Hv2 : Q v2) : R (StoreLCtx v2).
    refine (λ f',
      match f' with
      | StoreLCtx v2' => cast_if (Hv2 v2')
      | _ => right _
      end); congruence.
  Qed.
  Definition eq_dec_StoreRCtx_case e1 (He1 : P e1) : R (StoreRCtx e1).
    refine (λ f',
      match f' with
      | StoreRCtx e1' => cast_if (He1 e1')
      | _ => right _
      end); congruence.
  Qed.

  (* Evaluation contexts. *)
  Definition eq_dec_EmptyCtx_case : S [].
    by refine (λ f', match f' with [] => left _ | _ => right _ end). Qed.
  Definition eq_dec_ConsCtx_case f k (Hf : R f) (Hk : S k) : S (f :: k).
    refine (λ f',
      match f' with
      | f' :: k' => cast_if_and (Hf f') (Hk k')
      | _ => right _
      end); congruence.
  Qed.

  Global Instance expr_eq_dec : EqDecision expr :=
    expr_ind' P Q R S
      eq_dec_Val_case
      eq_dec_Do_case
      eq_dec_Eff_case
      eq_dec_TryWith_case
      eq_dec_Var_case
      eq_dec_Rec_case
      eq_dec_App_case
      eq_dec_UnOp_case
      eq_dec_BinOp_case
      eq_dec_If_case
      eq_dec_Pair_case
      eq_dec_Fst_case
      eq_dec_Snd_case
      eq_dec_InjL_case
      eq_dec_InjR_case
      eq_dec_Case_case
      eq_dec_Alloc_case
      eq_dec_Load_case
      eq_dec_Store_case
      eq_dec_LitV_case
      eq_dec_RecV_case
      eq_dec_PairV_case
      eq_dec_InjLV_case
      eq_dec_InjRV_case
      eq_dec_ContV_case
      eq_dec_KontV_case
      eq_dec_AppLCtx_case
      eq_dec_AppRCtx_case
      eq_dec_DoCtx_case
      eq_dec_TryWithCtx_case
      eq_dec_UnOpCtx_case
      eq_dec_BinOpLCtx_case
      eq_dec_BinOpRCtx_case
      eq_dec_IfCtx_case
      eq_dec_PairLCtx_case
      eq_dec_PairRCtx_case
      eq_dec_FstCtx_case
      eq_dec_SndCtx_case
      eq_dec_InjLCtx_case
      eq_dec_InjRCtx_case
      eq_dec_CaseCtx_case
      eq_dec_AllocCtx_case
      eq_dec_LoadCtx_case
      eq_dec_StoreLCtx_case
      eq_dec_StoreRCtx_case
      eq_dec_EmptyCtx_case
      eq_dec_ConsCtx_case.

  Global Instance val_eq_dec : EqDecision val :=
    val_ind' P Q R S
      eq_dec_Val_case
      eq_dec_Do_case
      eq_dec_Eff_case
      eq_dec_TryWith_case
      eq_dec_Var_case
      eq_dec_Rec_case
      eq_dec_App_case
      eq_dec_UnOp_case
      eq_dec_BinOp_case
      eq_dec_If_case
      eq_dec_Pair_case
      eq_dec_Fst_case
      eq_dec_Snd_case
      eq_dec_InjL_case
      eq_dec_InjR_case
      eq_dec_Case_case
      eq_dec_Alloc_case
      eq_dec_Load_case
      eq_dec_Store_case
      eq_dec_LitV_case
      eq_dec_RecV_case
      eq_dec_PairV_case
      eq_dec_InjLV_case
      eq_dec_InjRV_case
      eq_dec_ContV_case
      eq_dec_KontV_case
      eq_dec_AppLCtx_case
      eq_dec_AppRCtx_case
      eq_dec_DoCtx_case
      eq_dec_TryWithCtx_case
      eq_dec_UnOpCtx_case
      eq_dec_BinOpLCtx_case
      eq_dec_BinOpRCtx_case
      eq_dec_IfCtx_case
      eq_dec_PairLCtx_case
      eq_dec_PairRCtx_case
      eq_dec_FstCtx_case
      eq_dec_SndCtx_case
      eq_dec_InjLCtx_case
      eq_dec_InjRCtx_case
      eq_dec_CaseCtx_case
      eq_dec_AllocCtx_case
      eq_dec_LoadCtx_case
      eq_dec_StoreLCtx_case
      eq_dec_StoreRCtx_case
      eq_dec_EmptyCtx_case
      eq_dec_ConsCtx_case.

  Global Instance frame_eq_dec : EqDecision frame :=
    frame_ind' P Q R S
      eq_dec_Val_case
      eq_dec_Do_case
      eq_dec_Eff_case
      eq_dec_TryWith_case
      eq_dec_Var_case
      eq_dec_Rec_case
      eq_dec_App_case
      eq_dec_UnOp_case
      eq_dec_BinOp_case
      eq_dec_If_case
      eq_dec_Pair_case
      eq_dec_Fst_case
      eq_dec_Snd_case
      eq_dec_InjL_case
      eq_dec_InjR_case
      eq_dec_Case_case
      eq_dec_Alloc_case
      eq_dec_Load_case
      eq_dec_Store_case
      eq_dec_LitV_case
      eq_dec_RecV_case
      eq_dec_PairV_case
      eq_dec_InjLV_case
      eq_dec_InjRV_case
      eq_dec_ContV_case
      eq_dec_KontV_case
      eq_dec_AppLCtx_case
      eq_dec_AppRCtx_case
      eq_dec_DoCtx_case
      eq_dec_TryWithCtx_case
      eq_dec_UnOpCtx_case
      eq_dec_BinOpLCtx_case
      eq_dec_BinOpRCtx_case
      eq_dec_IfCtx_case
      eq_dec_PairLCtx_case
      eq_dec_PairRCtx_case
      eq_dec_FstCtx_case
      eq_dec_SndCtx_case
      eq_dec_InjLCtx_case
      eq_dec_InjRCtx_case
      eq_dec_CaseCtx_case
      eq_dec_AllocCtx_case
      eq_dec_LoadCtx_case
      eq_dec_StoreLCtx_case
      eq_dec_StoreRCtx_case
      eq_dec_EmptyCtx_case
      eq_dec_ConsCtx_case.

  Global Instance ectx_eq_dec : EqDecision ectx :=
    ectx_ind' P Q R S
      eq_dec_Val_case
      eq_dec_Do_case
      eq_dec_Eff_case
      eq_dec_TryWith_case
      eq_dec_Var_case
      eq_dec_Rec_case
      eq_dec_App_case
      eq_dec_UnOp_case
      eq_dec_BinOp_case
      eq_dec_If_case
      eq_dec_Pair_case
      eq_dec_Fst_case
      eq_dec_Snd_case
      eq_dec_InjL_case
      eq_dec_InjR_case
      eq_dec_Case_case
      eq_dec_Alloc_case
      eq_dec_Load_case
      eq_dec_Store_case
      eq_dec_LitV_case
      eq_dec_RecV_case
      eq_dec_PairV_case
      eq_dec_InjLV_case
      eq_dec_InjRV_case
      eq_dec_ContV_case
      eq_dec_KontV_case
      eq_dec_AppLCtx_case
      eq_dec_AppRCtx_case
      eq_dec_DoCtx_case
      eq_dec_TryWithCtx_case
      eq_dec_UnOpCtx_case
      eq_dec_BinOpLCtx_case
      eq_dec_BinOpRCtx_case
      eq_dec_IfCtx_case
      eq_dec_PairLCtx_case
      eq_dec_PairRCtx_case
      eq_dec_FstCtx_case
      eq_dec_SndCtx_case
      eq_dec_InjLCtx_case
      eq_dec_InjRCtx_case
      eq_dec_CaseCtx_case
      eq_dec_AllocCtx_case
      eq_dec_LoadCtx_case
      eq_dec_StoreLCtx_case
      eq_dec_StoreRCtx_case
      eq_dec_EmptyCtx_case
      eq_dec_ConsCtx_case.

End eq_decidable.


(* -------------------------------------------------------------------------- *)
(** Countable. *)

(* We prove that [expr], [val], [frame] and [ectx] are _countable_.

   The concept of a _countable set_ A is formalized in the [stdpp] library
   by the type class [Countable A]. This type class asserts the existence
   of an injective function [f] from [A] to the set [positive], which is
   isomorphic to the set of integers.

   Our proof relies on _generic trees_. A generic tree of type [gen_tree A]
   is either a node indexed by an integer and carrying an arbitrary number
   of subtrees or a leaf carrying a term of type [A]. Generic trees are
   countable and they form a more natural target for the (injective) encoding
   of expressions of [eff_lang] than the set of integers. Theorem
   [inj_countable'] allows us to use this intermediate representation.
*)

Instance mode_countable : Countable mode.
Proof.
  refine (inj_countable'
    ((* Encoding. *) λ m,
       match m with OS => false | MS => true end)
    ((* Decoding. *) λ b,
       match b with false => OS | true => MS end) _);
  by intros [].
Qed.
Instance base_lit_countable : Countable base_lit.
Proof.
  refine (inj_countable'
    ((* Encoding: base_lit → (nat + bool) + (unit + loc). *) λ l,
       match l with
       | LitInt n  => inl (inl n)
       | LitBool b => inl (inr b)
       | LitUnit   => inr (inl ())
       | LitLoc l  => inr (inr l)
       end)
    ((* Decoding. *) λ l,
       match l with
       | inl (inl n)  => LitInt n
       | inl (inr b)  => LitBool b
       | inr (inl ()) => LitUnit
       | inr (inr l)  => LitLoc l
       end) _);
  by intros [].
Qed.
Instance un_op_finite : Countable un_op.
Proof.
  refine (inj_countable'
    ((* Encoding. *) λ op,
       match op with NegOp => 0 | MinusUnOp => 1 end)
    ((* Decoding. *) λ n,
       match n with 0 => NegOp | _ => MinusUnOp end) _);
  by intros [].
Qed.
Instance bin_op_countable : Countable bin_op.
Proof.
  refine (inj_countable'
    ((* Encoding: bin_op → nat. *) λ op,
       match op with
       | PlusOp   => 0
       | MinusOp  => 1
       | MultOp   => 2
       | QuotOp   => 3
       | RemOp    => 4
       | AndOp    => 5
       | OrOp     => 6
       | XorOp    => 7
       | ShiftLOp => 8
       | ShiftROp => 9
       | LeOp     => 10
       | LtOp     => 11
       | EqOp     => 12
       end)
    ((* Decoding. *) λ n,
       match n with
       | 0 => PlusOp
       | 1 => MinusOp
       | 2 => MultOp
       | 3 => QuotOp
       | 4 => RemOp
       | 5 => AndOp
       | 6 => OrOp
       | 7 => XorOp
       | 8 => ShiftLOp
       | 9 => ShiftROp
       | 10 => LeOp
       | 11 => LtOp
       | _  => EqOp
       end) _);
  by intros [].
Qed.

Section countable.

  (* The set of generic trees. *)
  Notation gtree :=
    (gen_tree (string + binder + un_op + bin_op + mode + base_lit + loc))
    (only parsing).

  Notation enc_loc l :=
    (GenLeaf (inr l)) (only parsing).
  Notation enc_base_lit l :=
    (GenLeaf (inl (inr l))) (only parsing).
  Notation enc_mode m :=
    (GenLeaf (inl (inl (inr m)))) (only parsing).
  Notation enc_bin_op op :=
    (GenLeaf (inl (inl (inl (inr op))))) (only parsing).
  Notation enc_un_op op :=
    (GenLeaf (inl (inl (inl (inl (inr op)))))) (only parsing).
  Notation enc_string s :=
    (GenLeaf (inl (inl (inl (inl (inl (inl s))))))) (only parsing).
  Notation enc_binder b :=
    (GenLeaf (inl (inl (inl (inl (inl (inr b))))))) (only parsing).

  (* Encoding. *)

  (* Expressions. *)
  Definition encode_Val (v : val) (gv : gtree) : gtree :=
    GenNode 0 [gv].
  Definition encode_Do m (e : expr) (ge : gtree) : gtree :=
    GenNode 1 [(enc_mode m); ge].
  Definition encode_Eff m (v : val) (k : ectx) (gv gk : gtree) : gtree :=
    GenNode 2 [(enc_mode m); gv; gk].
  Definition encode_TryWith (e1 e2 e3 : expr) (ge1 ge2 ge3 : gtree) : gtree :=
    GenNode 3 [ge1; ge2; ge3].
  Definition encode_Var x : gtree :=
    GenNode 4 [enc_string x].
  Definition encode_Rec f x (e : expr) (ge : gtree) : gtree :=
    GenNode 5 [enc_binder f; enc_binder x; ge].
  Definition encode_App (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 6 [ge1; ge2].
  Definition encode_UnOp op (e : expr) (ge : gtree) : gtree :=
    GenNode 7 [enc_un_op op; ge].
  Definition encode_BinOp op (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 8 [enc_bin_op op; ge1; ge2].
  Definition encode_If (e1 e2 e3 : expr) (ge1 ge2 ge3 : gtree) : gtree :=
    GenNode 9 [ge1; ge2; ge3].
  Definition encode_Pair (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 10 [ge1; ge2].
  Definition encode_Fst (e : expr) (ge : gtree) : gtree :=
    GenNode 11 [ge].
  Definition encode_Snd (e : expr) (ge : gtree) : gtree :=
    GenNode 12 [ge].
  Definition encode_InjL (e : expr) (ge : gtree) : gtree :=
    GenNode 13 [ge].
  Definition encode_InjR (e : expr) (ge : gtree) : gtree :=
    GenNode 14 [ge].
  Definition encode_Case (e0 e1 e2 : expr) (ge0 ge1 ge2 : gtree) : gtree :=
    GenNode 15 [ge0; ge1; ge2].
  Definition encode_Alloc (e : expr) (ge : gtree) : gtree :=
    GenNode 16 [ge].
  Definition encode_Load (e : expr) (ge : gtree) : gtree :=
    GenNode 17 [ge].
  Definition encode_Store (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 18 [ge1; ge2].

  (* Values. *)
  Definition encode_LitV l : gtree :=
    GenNode 0 [enc_base_lit l].
  Definition encode_RecV (f x : binder) (e : expr) (ge : gtree) : gtree :=
    GenNode 1 [enc_binder f; enc_binder x; ge].
  Definition encode_PairV (v1 v2 : val) (gv1 gv2 : gtree) : gtree :=
    GenNode 2 [gv1; gv2].
  Definition encode_InjLV (v : val) (gv : gtree) : gtree :=
    GenNode 3 [gv].
  Definition encode_InjRV (v : val) (gv : gtree) : gtree :=
    GenNode 4 [gv].
  Definition encode_ContV (k : ectx) l (gk : gtree) : gtree :=
    GenNode 5 [gk; enc_loc l].
  Definition encode_KontV (k : ectx) (gk : gtree) : gtree :=
    GenNode 6 [gk].

  (* Frames. *)
  Definition encode_AppLCtx (v2 : val) (gv2 : gtree) : gtree :=
    GenNode 0 [gv2].
  Definition encode_AppRCtx (e1 : expr) (ge1 : gtree) : gtree :=
    GenNode 1 [ge1].
  Definition encode_DoCtx m : gtree :=
    GenNode 2 [enc_mode m].
  Definition encode_TryWithCtx (e2 e3 : expr) (ge2 ge3 : gtree) : gtree :=
    GenNode 3 [ge2; ge3].
  Definition encode_UnOpCtx op : gtree :=
    GenNode 4 [enc_un_op op].
  Definition encode_BinOpLCtx op (v2 : val) (gv2 : gtree) : gtree :=
    GenNode 5 [enc_bin_op op; gv2].
  Definition encode_BinOpRCtx op (e1 : expr) (ge1 : gtree) : gtree :=
    GenNode 6 [enc_bin_op op; ge1].
  Definition encode_IfCtx (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 7 [ge1; ge2].
  Definition encode_PairLCtx (v2 : val) (gv2 : gtree) : gtree :=
    GenNode 8 [gv2].
  Definition encode_PairRCtx (e1 : expr) (ge1 : gtree) : gtree :=
    GenNode 9 [ge1].
  Definition encode_FstCtx : gtree :=
    GenNode 10 [].
  Definition encode_SndCtx : gtree :=
    GenNode 11 [].
  Definition encode_InjLCtx : gtree :=
    GenNode 12 [].
  Definition encode_InjRCtx : gtree :=
    GenNode 13 [].
  Definition encode_CaseCtx (e1 e2 : expr) (ge1 ge2 : gtree) : gtree :=
    GenNode 14 [ge1; ge2].
  Definition encode_AllocCtx : gtree :=
    GenNode 15 [].
  Definition encode_LoadCtx : gtree :=
    GenNode 16 [].
  Definition encode_StoreLCtx (v2 : val) (gv2 : gtree) : gtree :=
    GenNode 17 [gv2].
  Definition encode_StoreRCtx (e1 : expr) (ge1 : gtree) : gtree :=
    GenNode 18 [ge1].

  (* Evaluation contexts. *)
  Definition encode_EmptyCtx : gtree :=
    GenNode 0 [].
  Definition encode_ConsCtx (f : frame) (k : ectx) (gf gk : gtree) :=
    GenNode 1 [gf; gk].

  Definition encode_expr : expr → gtree :=
    expr_ind' _ _ _ _
      encode_Val
      encode_Do
      encode_Eff
      encode_TryWith
      encode_Var
      encode_Rec
      encode_App
      encode_UnOp
      encode_BinOp
      encode_If
      encode_Pair
      encode_Fst
      encode_Snd
      encode_InjL
      encode_InjR
      encode_Case
      encode_Alloc
      encode_Load
      encode_Store
      encode_LitV
      encode_RecV
      encode_PairV
      encode_InjLV
      encode_InjRV
      encode_ContV
      encode_KontV
      encode_AppLCtx
      encode_AppRCtx
      encode_DoCtx
      encode_TryWithCtx
      encode_UnOpCtx
      encode_BinOpLCtx
      encode_BinOpRCtx
      encode_IfCtx
      encode_PairLCtx
      encode_PairRCtx
      encode_FstCtx
      encode_SndCtx
      encode_InjLCtx
      encode_InjRCtx
      encode_CaseCtx
      encode_AllocCtx
      encode_LoadCtx
      encode_StoreLCtx
      encode_StoreRCtx
      encode_EmptyCtx
      encode_ConsCtx.

  Definition encode_val : val → gtree :=
    val_ind' _ _ _ _
      encode_Val
      encode_Do
      encode_Eff
      encode_TryWith
      encode_Var
      encode_Rec
      encode_App
      encode_UnOp
      encode_BinOp
      encode_If
      encode_Pair
      encode_Fst
      encode_Snd
      encode_InjL
      encode_InjR
      encode_Case
      encode_Alloc
      encode_Load
      encode_Store
      encode_LitV
      encode_RecV
      encode_PairV
      encode_InjLV
      encode_InjRV
      encode_ContV
      encode_KontV
      encode_AppLCtx
      encode_AppRCtx
      encode_DoCtx
      encode_TryWithCtx
      encode_UnOpCtx
      encode_BinOpLCtx
      encode_BinOpRCtx
      encode_IfCtx
      encode_PairLCtx
      encode_PairRCtx
      encode_FstCtx
      encode_SndCtx
      encode_InjLCtx
      encode_InjRCtx
      encode_CaseCtx
      encode_AllocCtx
      encode_LoadCtx
      encode_StoreLCtx
      encode_StoreRCtx
      encode_EmptyCtx
      encode_ConsCtx.

  Definition encode_frame : frame → gtree :=
    frame_ind' _ _ _ _
      encode_Val
      encode_Do
      encode_Eff
      encode_TryWith
      encode_Var
      encode_Rec
      encode_App
      encode_UnOp
      encode_BinOp
      encode_If
      encode_Pair
      encode_Fst
      encode_Snd
      encode_InjL
      encode_InjR
      encode_Case
      encode_Alloc
      encode_Load
      encode_Store
      encode_LitV
      encode_RecV
      encode_PairV
      encode_InjLV
      encode_InjRV
      encode_ContV
      encode_KontV
      encode_AppLCtx
      encode_AppRCtx
      encode_DoCtx
      encode_TryWithCtx
      encode_UnOpCtx
      encode_BinOpLCtx
      encode_BinOpRCtx
      encode_IfCtx
      encode_PairLCtx
      encode_PairRCtx
      encode_FstCtx
      encode_SndCtx
      encode_InjLCtx
      encode_InjRCtx
      encode_CaseCtx
      encode_AllocCtx
      encode_LoadCtx
      encode_StoreLCtx
      encode_StoreRCtx
      encode_EmptyCtx
      encode_ConsCtx.

  Definition encode_ectx : ectx → gtree :=
    ectx_ind' _ _ _ _
      encode_Val
      encode_Do
      encode_Eff
      encode_TryWith
      encode_Var
      encode_Rec
      encode_App
      encode_UnOp
      encode_BinOp
      encode_If
      encode_Pair
      encode_Fst
      encode_Snd
      encode_InjL
      encode_InjR
      encode_Case
      encode_Alloc
      encode_Load
      encode_Store
      encode_LitV
      encode_RecV
      encode_PairV
      encode_InjLV
      encode_InjRV
      encode_ContV
      encode_KontV
      encode_AppLCtx
      encode_AppRCtx
      encode_DoCtx
      encode_TryWithCtx
      encode_UnOpCtx
      encode_BinOpLCtx
      encode_BinOpRCtx
      encode_IfCtx
      encode_PairLCtx
      encode_PairRCtx
      encode_FstCtx
      encode_SndCtx
      encode_InjLCtx
      encode_InjRCtx
      encode_CaseCtx
      encode_AllocCtx
      encode_LoadCtx
      encode_StoreLCtx
      encode_StoreRCtx
      encode_EmptyCtx
      encode_ConsCtx.


  (** Decoding. *)

  Definition decode_expr_pre
    (decode_expr : gtree → expr)
    (decode_val  : gtree → val)
    (decode_ectx : gtree → ectx) : gtree → expr := λ ge,
    match ge with
    | GenNode 0 [gv] =>
        Val (decode_val gv)
    | GenNode 1 [enc_mode m; ge] =>
        Do m (decode_expr ge)
    | GenNode 2 [enc_mode m; gv; gk] =>
        Eff m (decode_val gv) (decode_ectx gk)
    | GenNode 3 [ge1; ge2; ge3] =>
        TryWith (decode_expr ge1) (decode_expr ge2) (decode_expr ge3)
    | GenNode 4 [enc_string x] =>
        Var x
    | GenNode 5 [enc_binder f; enc_binder x; ge] =>
        Rec f x (decode_expr ge)
    | GenNode 6 [ge1; ge2] =>
        App (decode_expr ge1) (decode_expr ge2)
    | GenNode 7 [enc_un_op op; ge] =>
        UnOp op (decode_expr ge)
    | GenNode 8 [enc_bin_op op; ge1; ge2] =>
        BinOp op (decode_expr ge1) (decode_expr ge2)
    | GenNode 9 [ge1; ge2; ge3] =>
        If (decode_expr ge1) (decode_expr ge2) (decode_expr ge3)
    | GenNode 10 [ge1; ge2] =>
        Pair (decode_expr ge1) (decode_expr ge2)
    | GenNode 11 [ge] =>
        Fst (decode_expr ge)
    | GenNode 12 [ge] =>
        Snd (decode_expr ge)
    | GenNode 13 [ge] =>
        InjL (decode_expr ge)
    | GenNode 14 [ge] =>
        InjR (decode_expr ge)
    | GenNode 15 [ge1; ge2; ge3] =>
        Case (decode_expr ge1) (decode_expr ge2) (decode_expr ge3)
    | GenNode 16 [ge] =>
        Alloc (decode_expr ge)
    | GenNode 17 [ge] =>
        Load (decode_expr ge)
    | GenNode 18 [ge1; ge2] =>
        Store (decode_expr ge1) (decode_expr ge2)
    | _ =>
        Val $ LitV $ LitUnit
    end.

  Definition decode_val_pre
    (decode_expr : gtree → expr)
    (decode_val  : gtree → val)
    (decode_ectx : gtree → ectx) : gtree → val := λ gv,
    match gv with
    | GenNode 0 [enc_base_lit l] =>
        LitV l
    | GenNode 1 [enc_binder f; enc_binder x; ge] =>
        RecV f x (decode_expr ge)
    | GenNode 2 [gv1; gv2] =>
        PairV (decode_val gv1) (decode_val gv2)
    | GenNode 3 [gv] =>
        InjLV (decode_val gv)
    | GenNode 4 [gv] =>
        InjRV (decode_val gv)
    | GenNode 5 [gk; enc_loc l] =>
        ContV (decode_ectx gk) l
    | GenNode 6 [gk] =>
        KontV (decode_ectx gk)
    | _ =>
        LitV $ LitUnit
    end.

  Definition decode_frame_pre
    (decode_expr : gtree → expr)
    (decode_val  : gtree → val) : gtree → frame := λ gf,
    match gf with
    | GenNode 0 [gv2] =>
        AppLCtx (decode_val gv2)
    | GenNode 1 [ge1] =>
        AppRCtx (decode_expr ge1)
    | GenNode 2 [enc_mode m] =>
        DoCtx m
    | GenNode 3 [ge2; ge3] =>
        TryWithCtx (decode_expr ge2) (decode_expr ge3)
    | GenNode 4 [enc_un_op op] =>
        UnOpCtx op
    | GenNode 5 [enc_bin_op op; gv2] =>
        BinOpLCtx op (decode_val gv2)
    | GenNode 6 [enc_bin_op op; ge1] =>
        BinOpRCtx op (decode_expr ge1)
    | GenNode 7 [ge2; ge3] =>
        IfCtx (decode_expr ge2) (decode_expr ge3)
    | GenNode 8 [gv2] =>
        PairLCtx (decode_val gv2)
    | GenNode 9 [ge1] =>
        PairRCtx (decode_expr ge1)
    | GenNode 10 [] =>
        FstCtx
    | GenNode 11 [] =>
        SndCtx
    | GenNode 12 [] =>
        InjLCtx
    | GenNode 13 [] =>
        InjRCtx
    | GenNode 14 [ge1; ge2] =>
        CaseCtx (decode_expr ge1) (decode_expr ge2)
    | GenNode 15 [] =>
        AllocCtx
    | GenNode 16 [] =>
        LoadCtx
    | GenNode 17 [gv2] =>
        StoreLCtx (decode_val gv2)
    | GenNode 18 [ge1] =>
        StoreRCtx (decode_expr ge1)
    | _ =>
        FstCtx
    end.

  Definition decode_ectx_pre
    (decode_frame : gtree → frame)
    (decode_ectx : gtree → ectx) : gtree → ectx := λ gk,
    match gk with
    | GenNode 0 [] =>
        []
    | GenNode 1 [gf; gk] =>
        (decode_frame gf) :: (decode_ectx gk)
    | _ => []
    end.

  Definition decode_expr :=
    fix decode_expr ge := decode_expr_pre decode_expr decode_val decode_ectx ge
    with decode_val gv := decode_val_pre decode_expr decode_val decode_ectx gv
    with decode_frame gf := decode_frame_pre decode_expr decode_val gf
    with decode_ectx gk := decode_ectx_pre decode_frame decode_ectx gk
    for decode_expr.

  Definition decode_val :=
    fix decode_expr ge := decode_expr_pre decode_expr decode_val decode_ectx ge
    with decode_val gv := decode_val_pre decode_expr decode_val decode_ectx gv
    with decode_frame gf := decode_frame_pre decode_expr decode_val gf
    with decode_ectx gk := decode_ectx_pre decode_frame decode_ectx gk
    for decode_val.

  Definition decode_frame :=
    fix decode_expr ge := decode_expr_pre decode_expr decode_val decode_ectx ge
    with decode_val gv := decode_val_pre decode_expr decode_val decode_ectx gv
    with decode_frame gf := decode_frame_pre decode_expr decode_val gf
    with decode_ectx gk := decode_ectx_pre decode_frame decode_ectx gk
    for decode_frame.

  Definition decode_ectx :=
    fix decode_expr ge := decode_expr_pre decode_expr decode_val decode_ectx ge
    with decode_val gv := decode_val_pre decode_expr decode_val decode_ectx gv
    with decode_frame gf := decode_frame_pre decode_expr decode_val gf
    with decode_ectx gk := decode_ectx_pre decode_frame decode_ectx gk
    for decode_ectx.

  Notation P := (λ e, decode_expr  (encode_expr  e) = e) (only parsing).
  Notation Q := (λ v, decode_val   (encode_val   v) = v) (only parsing).
  Notation R := (λ f, decode_frame (encode_frame f) = f) (only parsing).
  Notation S := (λ k, decode_ectx  (encode_ectx  k) = k) (only parsing).

  Global Instance expr_countable : Countable expr.
  Proof.
    refine (inj_countable' encode_expr decode_expr _).
    apply (expr_ind' P Q R S); repeat intros ?; simpl;
    repeat match goal with
    | [ H : _ = _ |- _ ] => rewrite H
    end; done.
  Qed.

  Global Instance val_countable : Countable val.
  Proof.
    refine (inj_countable'
      ((* Encoding. *) λ v,
         Val v)
      ((* Decoding. *) λ e,
         match e with Val v => v | _ => LitV LitUnit end) _);
    by intros [].
  Qed.

  Global Instance frame_countable : Countable frame.
  Proof.
    refine (inj_countable'
      ((* Encoding. *) λ f,
         KontV [f])
      ((* Decoding. *) λ v,
         match v with KontV [f] => f | _ => FstCtx end) _);
    by intros [].
  Qed.

  Global Instance ectx_countable : Countable ectx.
  Proof.
    refine (inj_countable'
      ((* Encoding. *) λ k,
         KontV k)
      ((* Decoding. *) λ v,
         match v with KontV k => k | _ => [] end) _);
    by intros [].
  Qed.

End countable.


(* -------------------------------------------------------------------------- *)
(** Inhabited. *)

Instance state_inhabited : Inhabited state := populate {| heap := inhabitant |}.
Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).
Instance frame_inhabited : Inhabited frame := populate FstCtx.
Instance ectx_inhabited : Inhabited ectx := populate inhabitant.


(* -------------------------------------------------------------------------- *)
(** OFEs. *)

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure exprO := leibnizO expr.
Canonical Structure valO := leibnizO val.
Canonical Structure frameO := leibnizO frame.
Canonical Structure ectxO := leibnizO ectx.
