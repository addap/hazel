From stdpp              Require Export binders strings.
From stdpp              Require Import gmap.
From iris.algebra       Require Export ofe.
From iris.program_logic Require Export language.
From iris.heap_lang     Require Export locations.
From hazel              Require Import lib.

Set Default Proof Using "Type".

(** eff_lang. A simple programming language with support for effect handlers. *)

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module eff_lang.
Open Scope Z_scope.

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool)
  | LitUnit | LitLoc (l : loc).
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp. (* Pointer offset *)

Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Effects *)
  | Do (e : expr)
  | Eff (v : val) (k : ectx)
  | TryWith (e1 e2 e3 : expr)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 e1 e2 : expr)
  (* Heap *)
  | Alloc (e : expr) (* initial value *)
  | Load (e : expr)
  | Store (e1 e2 : expr)

with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | ContV (k : ectx) (l : loc)

with ectx :=
  | EmptyCtx
  | ConsCtx (ki : ectx_item) (k : ectx)

with ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | DoCtx
  | TryWithCtx (e2 e3 : expr)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (v2 : val)
  | PairRCtx (e1 : expr)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 e2 : expr)
  | AllocCtx
  | LoadCtx
  | StoreLCtx (v2 : val)
  | StoreRCtx (e1 : expr).

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _     => None
  end.

Notation of_eff := Eff (only parsing).

Definition to_eff (e : expr) : option (val * ectx) :=
  match e with
  | Eff v k => Some (v, k)
  | _       => None
  end.

(** The state: heaps of vals. *)
Record state : Type := { heap: gmap loc val }.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Lemma of_to_eff e v k : to_eff e = Some (v, k) → of_eff v k = e.
Proof. destruct e=>//=. by intros [= <- <-]. Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? [=]. Qed.

Lemma of_eff_inj v1 k1 v2 k2 :
  of_eff v1 k1 = of_eff v2 k2 → v1 = v2 ∧ k1 = k2.
Proof. by intros [= -> ->]. Qed.

Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Instance expr_eq_dec : EqDecision expr.
Proof.
  refine (
    fix go_expr (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
      match e1, e2 with
      | Val v, Val v' => cast_if (decide (v = v'))
      | Var x, Var x' => cast_if (decide (x = x'))
      | Do e , Do  e' => cast_if (decide (e = e'))
      | Eff v k , Eff v' k' => cast_if_and (decide (v = v')) (decide (k = k'))
      | TryWith e1 e2 e3, TryWith e1' e2' e3' =>
         cast_if_and3 (decide (e1 = e1')) (decide (e2 = e2')) (decide (e3 = e3'))
      | Rec f x e, Rec f' x' e' =>
         cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
      | App e1 e2, App e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
      | BinOp o e1 e2, BinOp o' e1' e2' =>
         cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
      | If e0 e1 e2, If e0' e1' e2' =>
         cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
      | Pair e1 e2, Pair e1' e2' =>
         cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | Fst e, Fst e' => cast_if (decide (e = e'))
      | Snd e, Snd e' => cast_if (decide (e = e'))
      | InjL e, InjL e' => cast_if (decide (e = e'))
      | InjR e, InjR e' => cast_if (decide (e = e'))
      | Case e0 e1 e2, Case e0' e1' e2' =>
         cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
      | Alloc e, Alloc e' => cast_if (decide (e = e'))
      | Load e, Load e' => cast_if (decide (e = e'))
      | Store e1 e2, Store e1' e2' =>
         cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | _, _ => right _
      end
    
    with go_val (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
      match v1, v2 with
      | LitV l, LitV l' => cast_if (decide (l = l'))
      | RecV f x e, RecV f' x' e' =>
         cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
      | PairV e1 e2, PairV e1' e2' =>
         cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | InjLV e, InjLV e' => cast_if (decide (e = e'))
      | InjRV e, InjRV e' => cast_if (decide (e = e'))
      | ContV k l, ContV k' l' => cast_if_and (decide (k = k')) (decide (l = l'))
      | _, _ => right _
      end

    with go_ectx (k1 k2 : ectx) {struct k1} : Decision (k1 = k2) :=
      match k1, k2 with
      | EmptyCtx, EmptyCtx => left _
      | ConsCtx ki k, ConsCtx ki' k' =>
         cast_if_and (decide (ki = ki')) (decide (k = k'))
      | _, _ => right _
      end

    with go_ectx_item (ki1 ki2 : ectx_item) {struct ki1} : Decision (ki1 = ki2) :=
      match ki1, ki2 with
      | AppLCtx v2, AppLCtx v2' => cast_if (decide (v2 = v2'))
      | AppRCtx e1, AppRCtx e1' => cast_if (decide (e1 = e1'))
      | DoCtx, DoCtx => left _
      | TryWithCtx e2 e3, TryWithCtx e2' e3' =>
         cast_if_and (decide (e2 = e2')) (decide (e3 = e3'))
      | UnOpCtx op, UnOpCtx op' => cast_if (decide (op = op'))
      | BinOpLCtx op v2, BinOpLCtx op' v2' =>
         cast_if_and (decide (op = op')) (decide (v2 = v2'))
      | BinOpRCtx op e1, BinOpRCtx op' e1' =>
         cast_if_and (decide (op = op')) (decide (e1 = e1'))
      | IfCtx e1 e2, IfCtx e1' e2' =>
         cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | PairLCtx v2, PairLCtx v2' => cast_if (decide (v2 = v2'))
      | PairRCtx e1, PairRCtx e1' => cast_if (decide (e1 = e1'))
      | FstCtx, FstCtx => left _
      | SndCtx, SndCtx => left _
      | InjLCtx, InjLCtx => left _
      | InjRCtx, InjRCtx => left _
      | CaseCtx e1 e2, CaseCtx e1' e2' =>
         cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
      | AllocCtx, AllocCtx => left _
      | LoadCtx, LoadCtx => left _
      | StoreLCtx v2, StoreLCtx v2' => cast_if (decide (v2 = v2'))
      | StoreRCtx e1, StoreRCtx e1' => cast_if (decide (e1 = e1'))
      | _, _ => right _
      end

    for go_expr); try (
    clear go_expr go_val go_ectx go_ectx_item;
    abstract intuition congruence).
Defined.
Instance val_eq_dec : EqDecision val.
Proof.
  intros ??. case (expr_eq_dec (Val x) (Val y)).
  - intros [= ->]. by left.
  - right. by intros ->.
Qed.
Instance ectx_eq_dec : EqDecision ectx.
Proof.
  intros ??.
  case (val_eq_dec (ContV x inhabitant) (ContV y inhabitant)).
  - intros [= ->]. by left.
  - right. by intros ->.
Qed.
Instance ectx_item_eq_dec : EqDecision ectx_item.
Proof. solve_decision. Defined.

Instance base_lit_countable : Countable base_lit.
Proof.
 refine (inj_countable' (λ l, match l with
  | LitInt n => inl (inl n)
  | LitBool b => inl (inr b)
  | LitUnit => inr (inl ())
  | LitLoc l => inr (inr l)
  end) (λ l, match l with
  | inl (inl n) => LitInt n
  | inl (inr b) => LitBool b
  | inr (inl ()) => LitUnit
  | inr (inr l) => LitLoc l
  end) _); by intros [].
Qed.
Instance un_op_finite : Countable un_op.
Proof.
 refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 end)
  (λ n, match n with 0 => NegOp | _ => MinusUnOp end) _); by intros [].
Qed.
Instance bin_op_countable : Countable bin_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
  | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
  | LeOp => 10 | LtOp => 11 | EqOp => 12 | OffsetOp => 13
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | 12 => EqOp | _ => OffsetOp
  end) _); by intros [].
Qed.
Instance expr_countable : Countable expr.
Proof.
  set (enc :=
    fix go_expr e :=
      match e with
      | Val v => GenNode 0 [go_val v]
      | Var x => GenLeaf (inl (inl x))
      | Rec f x e =>
         GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go_expr e]
      | App e1 e2 => GenNode 2 [go_expr e1; go_expr e2]
      | UnOp op e => GenNode 3 [GenLeaf (inr (inr (inl op))); go_expr e]
      | BinOp op e1 e2 =>
         GenNode 4 [GenLeaf (inr (inr (inr op))); go_expr e1; go_expr e2]
      | If e0 e1 e2 => GenNode 5 [go_expr e0; go_expr e1; go_expr e2]
      | Pair e1 e2 => GenNode 6 [go_expr e1; go_expr e2]
      | Fst e => GenNode 7 [go_expr e]
      | Snd e => GenNode 8 [go_expr e]
      | InjL e => GenNode 9 [go_expr e]
      | InjR e => GenNode 10 [go_expr e]
      | Case e0 e1 e2 => GenNode 11 [go_expr e0; go_expr e1; go_expr e2]
      | Do e => GenNode 12 [go_expr e]
      | Eff v k => GenNode 13 [go_val v; go_ectx k]
      | Alloc e => GenNode 14 [go_expr e]
      | Load e => GenNode 15 [go_expr e]
      | Store e1 e2 => GenNode 16 [go_expr e1; go_expr e2]
      | TryWith e1 e2 e3 => GenNode 17 [go_expr e1; go_expr e2; go_expr e3]
      end

    with go_val v :=
      match v with
      | LitV l => GenLeaf (inr (inl l))
      | RecV f x e =>
         GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go_expr e]
      | PairV v1 v2 => GenNode 1 [go_val v1; go_val v2]
      | InjLV v => GenNode 2 [go_val v]
      | InjRV v => GenNode 3 [go_val v]
      | ContV k l => GenNode 4 [go_ectx k; GenLeaf (inr (inl (LitLoc l)))]
      end

    with go_ectx k :=
      match k with
      | EmptyCtx => GenNode 0 []
      | ConsCtx ki k => GenNode 1 [go_ectx_item ki; go_ectx k]
      end

    with go_ectx_item ki :=
      match ki with
      | AppLCtx v2 => GenNode 0 [go_val v2]
      | AppRCtx e1 => GenNode 1 [go_expr e1]
      | DoCtx =>  GenNode 2 []
      | TryWithCtx e2 e3 => GenNode 3 [go_expr e2; go_expr e3]
      | UnOpCtx op => GenNode 4 [GenLeaf (inr (inr (inl op)))]
      | BinOpLCtx op v2 => GenNode 5 [GenLeaf (inr (inr (inr op))); go_val v2]
      | BinOpRCtx op e1 => GenNode 6 [GenLeaf (inr (inr (inr op))); go_expr e1]
      | IfCtx e1 e2 => GenNode 7 [go_expr e1; go_expr e2]
      | PairLCtx v2 => GenNode 8 [go_val v2]
      | PairRCtx e1 => GenNode 9 [go_expr e1]
      | FstCtx => GenNode 10 []
      | SndCtx => GenNode 11 []
      | InjLCtx => GenNode 12 []
      | InjRCtx => GenNode 13 []
      | CaseCtx e1 e2 => GenNode 14 [go_expr e1; go_expr e2]
      | AllocCtx => GenNode 15 []
      | LoadCtx => GenNode 16 []
      | StoreLCtx v2 => GenNode 17 [go_val v2]
      | StoreRCtx e1 => GenNode 18 [go_expr e1]
      end

    for go_expr).

  set (dec :=
    fix go_expr e :=
      match e with
      | GenNode 0 [v] => Val (go_val v)
      | GenLeaf (inl (inl x)) => Var x
      | GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] =>
         Rec f x (go_expr e)
      | GenNode 2 [e1; e2] => App (go_expr e1) (go_expr e2)
      | GenNode 3 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go_expr e)
      | GenNode 4 [GenLeaf (inr (inr (inr op))); e1; e2] =>
         BinOp op (go_expr e1) (go_expr e2)
      | GenNode 5 [e0; e1; e2] => If (go_expr e0) (go_expr e1) (go_expr e2)
      | GenNode 6 [e1; e2] => Pair (go_expr e1) (go_expr e2)
      | GenNode 7 [e] => Fst (go_expr e)
      | GenNode 8 [e] => Snd (go_expr e)
      | GenNode 9 [e] => InjL (go_expr e)
      | GenNode 10 [e] => InjR (go_expr e)
      | GenNode 11 [e0; e1; e2] => Case (go_expr e0) (go_expr e1) (go_expr e2)
      | GenNode 12 [e] => Do (go_expr e)
      | GenNode 13 [v; k] => Eff (go_val v) (go_ectx k)
      | GenNode 14 [e] => Alloc (go_expr e)
      | GenNode 15 [e] => Load (go_expr e)
      | GenNode 16 [e1; e2] => Store (go_expr e1) (go_expr e2)
      | GenNode 17 [e1; e2; e3] => TryWith (go_expr e1) (go_expr e2) (go_expr e3)
      | _ => Var "dummy" (* dummy *)
      end

    with go_val v :=
      match v with
      | GenLeaf (inr (inl l)) => LitV l
      | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] =>
         RecV f x (go_expr e)
      | GenNode 1 [v1; v2] => PairV (go_val v1) (go_val v2)
      | GenNode 2 [v] => InjLV (go_val v)
      | GenNode 3 [v] => InjRV (go_val v)
      | GenNode 4 [k; GenLeaf (inr (inl (LitLoc l)))] => ContV (go_ectx k) l
      | _ => LitV LitUnit (* dummy *)
      end

    with go_ectx k :=
      match k with
      | GenNode 0 [] => EmptyCtx 
      | GenNode 1 [ki; k] => ConsCtx (go_ectx_item ki) (go_ectx k)
      | _ => EmptyCtx (* dummy *)
      end

    with go_ectx_item ki :=
      match ki with
      | GenNode 0 [v2] => AppLCtx (go_val v2)
      | GenNode 1 [e1] => AppRCtx (go_expr e1)
      | GenNode 2 [] => DoCtx
      | GenNode 3 [e2; e3] => TryWithCtx (go_expr e2) (go_expr e3)
      | GenNode 4 [GenLeaf (inr (inr (inl op)))] => UnOpCtx op
      | GenNode 5 [GenLeaf (inr (inr (inr op))); v2] => BinOpLCtx op (go_val v2)
      | GenNode 6 [GenLeaf (inr (inr (inr op))); e1] => BinOpRCtx op (go_expr e1)
      | GenNode 7 [e1; e2] => IfCtx (go_expr e1) (go_expr e2)
      | GenNode 8 [v2] => PairLCtx (go_val v2)
      | GenNode 9 [e1] => PairRCtx (go_expr e1)
      | GenNode 10 [] => FstCtx
      | GenNode 11 [] => SndCtx
      | GenNode 12 [] => InjLCtx
      | GenNode 13 [] => InjRCtx
      | GenNode 14 [e1; e2] => CaseCtx (go_expr e1) (go_expr e2)
      | GenNode 15 [] => AllocCtx
      | GenNode 16 [] => LoadCtx
      | GenNode 17 [v2] => StoreLCtx (go_val v2)
      | GenNode 18 [e1] => StoreRCtx (go_expr e1)
      | _ => FstCtx (* dummy *)
      end

   for go_expr).

  refine (inj_countable' enc dec _).
  refine (fix  go_expr      (e  : expr)      {struct e}  := _
          with go_val       (v  : val)       {struct v}  := _
          with go_ectx      (k  : ectx)      {struct k}  := _
          with go_ectx_item (ki : ectx_item) {struct ki} := _ for go_expr).
  - destruct e as [v| | | | | | | | | | | | | | | | | |]; simpl; f_equal;
     [exact (go_val v)|try done..]; exact (go_ectx k).
  - destruct v; by f_equal.
  - destruct k as [|ki k]; simpl; f_equal; try done; exact (go_ectx_item ki).
  - destruct ki; by f_equal.
Qed.
Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

Instance state_inhabited : Inhabited state := populate {| heap := inhabitant |}.
Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Instance ectx_inhabited : Inhabited ectx := populate EmptyCtx.
Instance ectx_item_inhabited : Inhabited ectx_item := populate FstCtx.
Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure ectxO := leibnizO ectx.
Canonical Structure ectx_itemO := leibnizO ectx_item.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

(** Contextual closure *)
Fixpoint fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | DoCtx => Do e
  | TryWithCtx e2 e3 => TryWith e e2 e3
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op v2 => BinOp op e (Val v2)
  | BinOpRCtx op e1 => BinOp op e1 e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx v2 => Pair e (Val v2)
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | AllocCtx => Alloc e
  | LoadCtx => Load e
  | StoreLCtx v2 => Store e (Val v2)
  | StoreRCtx e1 => Store e1 e
  end.

(** Contexts *)

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with EmptyCtx => e | ConsCtx Ki K => fill_item Ki (fill K e) end.

Fixpoint ectx_app (K K' : ectx) : ectx :=
  match K with EmptyCtx => K' | ConsCtx Ki K => ConsCtx Ki (ectx_app K K') end.

Lemma fill_ectx_app K K' e : fill (ectx_app K K') e = fill K (fill K' e).
Proof. induction K as [|Ki K]; [done|]; by simpl; rewrite IHK. Qed.

(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Do e => Do (subst x v e)
  | Eff _ _ => e
  | TryWith e1 e2 e3 =>
     TryWith (subst x v e1) (subst x v e2) (subst x v e3)
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
  | Alloc e => Alloc (subst x v e)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | QuotOp => Some $ LitInt (n1 `quot` n2)
  | RemOp => Some $ LitInt (n1 `rem` n2)
  | AndOp => Some $ LitInt (Z.land n1 n2)
  | OrOp => Some $ LitInt (Z.lor n1 n2)
  | XorOp => Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp => Some $ LitInt (n1 ≪ n2)
  | ShiftROp => Some $ LitInt (n1 ≫ n2)
  | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  | OffsetOp => None (* Pointer arithmetic *)
  end.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp => None (* Pointer arithmetic *)
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    Some $ LitV $ LitBool $ bool_decide (v1 = v2)
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l), LitV (LitInt off) => Some $ LitV $ LitLoc (l +ₗ off)
    | _, _ => None
    end.

Definition state_upd_heap (f: gmap loc val → gmap loc val) (σ: state) : state :=
  {| heap := f σ.(heap) |}.
Arguments state_upd_heap _ !_ /.

Inductive head_step : expr → state → expr → state → Prop :=
  (* Lambda. *)
  | RecS f x e σ :
     head_step (Rec f x e) σ (Val $ RecV f x e) σ
  (* Pair. *)
  | PairS v1 v2 σ :
     head_step (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ
  (* InjL. *)
  | InjLS v σ :
     head_step (InjL $ Val v) σ (Val $ InjLV v) σ
  (* InjR. *)
  | InjRS v σ :
     head_step (InjR $ Val v) σ (Val $ InjRV v) σ
  (* Beta reduction. *)
  | BetaS f x e1 v2 e' σ :
     e' = subst' x v2 (subst' f (RecV f x e1) e1) →
     head_step (App (Val $ RecV f x e1) (Val v2)) σ e' σ
  (* Continuation resumption. *)
  | ContS k l w e' σ :
     σ.(heap) !! l = Some (LitV $ LitBool true) →
     e' = fill k (Val w) →
     head_step (App (Val (ContV k l)) (Val w))                        σ
               e' (state_upd_heap <[l:=(LitV $ LitBool false)]> σ)
  (* UnOp. *)
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
     head_step (UnOp op (Val v)) σ (Val v') σ
  (* BinOp. *)
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
     head_step (BinOp op (Val v1) (Val v2)) σ (Val v') σ
  (* If. *)
  | IfTrueS e1 e2 σ :
     head_step (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ
  | IfFalseS e1 e2 σ :
     head_step (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ
  (* Fst. *)
  | FstS v1 v2 σ :
     head_step (Fst (Val $ PairV v1 v2)) σ (Val v1) σ
  (* Snd. *)
  | SndS v1 v2 σ :
     head_step (Snd (Val $ PairV v1 v2)) σ (Val v2) σ
  (* Case. *)
  | CaseLS v e1 e2 σ :
     head_step (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ
  | CaseRS v e1 e2 σ :
     head_step (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ
  (* Alloc. *)
  | AllocS v σ l :
     σ.(heap) !! l = None →
     head_step (Alloc (Val v))          σ
               (Val $ LitV $ LitLoc l) (state_upd_heap <[l:=v]> σ)
  (* Load. *)
  | LoadS l v σ :
     σ.(heap) !! l = Some v →
     head_step (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ
  (* Store. *)
  | StoreS l v σ :
     is_Some (σ.(heap) !! l) →
     head_step (Store (Val $ LitV $ LitLoc l) (Val v)) σ
               (Val $ LitV LitUnit) (state_upd_heap <[l:=v]> σ)
  (* Do. *)
  | DoS v σ :
     head_step (Do (Val v)) σ (Eff v EmptyCtx) σ
  (* TryWith. *)
  | TryWithEffS v k e2 e3 σ l :
     σ.(heap) !! l = None →
     head_step (TryWith (Eff v k) e2 e3)                    σ
               (App (App e2 (Val v)) (Val (ContV k l)))
               (state_upd_heap <[l:=(LitV $ LitBool true)]> σ)
  | TryWithRetS v e2 e3 σ :
     head_step (TryWith (Val v) e2 e3) σ (App e3 (Val v)) σ
  (* AppLCtx: [ eff v1 y.k ] v2 --> eff v1 y.(k v2). *)
  | AppLEffS v1 k v2 σ :
     head_step (App (Eff v1 k) (Val v2))         σ
               (Eff v1 (ConsCtx (AppLCtx v2) k)) σ
  (* AppRCtx:  e1 [ eff v2 y.k ] --> eff v2 y.(e1 k). *)
  | AppREffS e1 v1 k σ :
     head_step (App e1 (Eff v1 k))               σ
               (Eff v1 (ConsCtx (AppRCtx e1) k)) σ
  (* UnOpCtx: op [ eff v y.k ] --> eff v y.(op k). *)
  | UnOpEffS op v k σ :
     head_step (UnOp op (Eff v k))              σ
               (Eff v (ConsCtx (UnOpCtx op) k)) σ
  (* BinOpLCtx: op [ eff v1 y.k ] v2 --> eff v1 y.(op k v2). *)
  | BinOpLEffS op v1 k v2 σ :
     head_step (BinOp op (Eff v1 k) (Val v2))         σ
               (Eff v1 (ConsCtx (BinOpLCtx op v2) k)) σ
  (* BinOpRCtx: op e1 [ eff v2 y.k ] --> eff v2 y.(op e1 k). *)
  | BinOpREffS op e1 v2 k σ :
     head_step (BinOp op e1 (Eff v2 k))               σ
               (Eff v2 (ConsCtx (BinOpRCtx op e1) k)) σ
  (* IfCtx: If [ eff v y.k ] e1 e2 --> eff v y.(If k e1 e2). *)
  | IfEffS v k e1 e2 σ :
     head_step (If (Eff v k) e1 e2)              σ
               (Eff v (ConsCtx (IfCtx e1 e2) k)) σ
  (* PairLCtx: ([ eff v1 y.k ], v2) --> eff v1 y.(k, v2). *)
  | PairLEffS v1 k v2 σ :
     head_step (Pair (Eff v1 k) (Val v2))         σ
               (Eff v1 (ConsCtx (PairLCtx v2) k)) σ
  (* PairRCtx: (e1, [ eff v2 y.k ]) --> eff v2 y.(e1, k). *)
  | PairREffS e1 v2 k σ :
     head_step (Pair e1 (Eff v2 k))               σ
               (Eff v2 (ConsCtx (PairRCtx e1) k)) σ
  (* FstCtx: fst [ eff v y.k  ] --> eff v y.(fst k) . *)
  | FstEffS v k σ :
     head_step (Fst (Eff v k))            σ
               (Eff v (ConsCtx FstCtx k)) σ
  (* SndCtx: snd [ eff v y.k  ] --> eff v y.(snd k) . *)
  | SndEffS v k σ :
     head_step (Snd (Eff v k))            σ
               (Eff v (ConsCtx SndCtx k)) σ
  (* InjLCtx: InjL [ eff v y.k ] --> eff v y.(InjL k). *)
  | InjLEffS v k σ :
     head_step (InjL (Eff v k))            σ
               (Eff v (ConsCtx InjLCtx k)) σ
  (* InjRCtx: InjR [ eff v y.k ] --> eff v y.(InjR k). *)
  | InjREffS v k σ :
     head_step (InjR (Eff v k))            σ
               (Eff v (ConsCtx InjRCtx k)) σ
  (* CaseCtx: match [ eff v y.k ] with InjL => e1 | InjR => e2 end -->
              eff v y.(match  k   with InjL => e1 | InjR => e2 end). *)
  | CaseEffS v k e1 e2 σ :
     head_step (Case (Eff v k) e1 e2)              σ
               (Eff v (ConsCtx (CaseCtx e1 e2) k)) σ
  (* AllocCtx: ref [ eff v y.k ] --> eff v y.(ref k). *)
  | AllocEffS v k σ :
     head_step (Alloc (Eff v k))            σ
               (Eff v (ConsCtx AllocCtx k)) σ
  (* LoadCtx: ! [ eff v y.k ] --> eff v y.(! k). *)
  | LoadEffS v k σ :
     head_step (Load (Eff v k))            σ
               (Eff v (ConsCtx LoadCtx k)) σ
  (* StoreLCtx: [ eff v1 y.k ] := v2 --> eff v1 y.(k := v2). *)
  | StoreLEffS v1 k v2 σ :
     head_step (Store (Eff v1 k) (Val v2))         σ
               (Eff v1 (ConsCtx (StoreLCtx v2) k)) σ
  (* StoreRCtx: e1 := [ eff v2 y.k ] --> eff v2 y.(e1 := k). *)
  | StoreREffS e1 v2 k σ :
     head_step (Store e1 (Eff v2 k))               σ
               (Eff v2 (ConsCtx (StoreRCtx e1) k)) σ
  (* EffCtx: do [ eff v y.k ] --> eff v y.(do k). *)
  | DoEffS v k σ :
     head_step (Do (Eff v k))            σ
               (Eff v (ConsCtx DoCtx k)) σ.

Inductive prim_step (e1 : expr) (σ1 : state)
                    (e2 : expr) (σ2 : state) : Prop :=
  | Ectx_prim_step K e1' e2' :
     e1 = fill K e1' →
     e2 = fill K e2' →
     head_step e1' σ1 e2' σ2 →
     prim_step e1  σ1 e2  σ2.

Lemma Ectxi_prim_step Ki e1' e2' e1 σ1 e2 σ2 :
  e1 = fill_item Ki e1' →
  e2 = fill_item Ki e2' →
  head_step e1' σ1 e2' σ2 →
  prim_step e1  σ1 e2  σ2.
Proof.
  intros -> -> H.
  by apply (Ectx_prim_step _ _ _ _ (ConsCtx Ki EmptyCtx) e1' e2').
Qed.

Lemma Ectxi_prim_step' Ki e1' e2' e1 σ1 e2 σ2 :
  e1 = fill_item Ki e1' →
  e2 = fill_item Ki e2' →
  prim_step e1' σ1 e2' σ2 →
  prim_step e1  σ1 e2  σ2.
Proof.
  intros -> ->. inversion 1. simplify_eq.
  by apply (Ectx_prim_step _ _ _ _ (ConsCtx Ki K) e1'0 e2'0).
Qed.

Lemma Ectx_prim_step' K e1 σ1 e2 σ2 e1' e2' :
  e1 = fill K e1' →
  e2 = fill K e2' →
  prim_step e1' σ1 e2' σ2 →
  prim_step e1  σ1 e2  σ2.
Proof.
  intros -> ->. inversion 1. simplify_eq.
  apply (Ectx_prim_step _ _ _ _ (ectx_app K K0) e1'0 e2'0); eauto;
  by rewrite fill_ectx_app.
Qed.

Definition prim_step' e1 σ1 (obs : list unit) e2 σ2 (efs : list expr) :=
  match obs with _ :: _ => False | [] =>
    match efs with _ :: _ => False | [] => prim_step e1 σ1 e2 σ2 end
  end.

(** Basic properties about the language *)
Instance InjLV_inj : Inj (=) (=) InjLV.
Proof. intros ??. by inversion 1. Qed.
Instance InjRV_inj : Inj (=) (=) InjRV.
Proof. intros ??. by inversion 1. Qed.

Instance InjLV_dec_range : DecRange InjLV.
Proof. intros v. case v; try (right; by inversion 1); left; by exists v0. Qed.
Instance InjRV_dec_range : DecRange InjRV.
Proof. intros v. case v; try (right; by inversion 1); left; by exists v0. Qed.

Lemma InjLV_case v : {w | v = InjLV w} + {∀ w, v ≠ InjLV w}.
Proof. by apply dec_range. Qed.
Lemma InjRV_case v : {w | v = InjRV w} + {∀ w, v ≠ InjRV w}.
Proof. by apply dec_range. Qed.

Instance InjLV_marker : Marker InjLV.
Proof. split. { by apply InjLV_inj. } { by apply InjLV_dec_range. } Qed.
Instance InjRV_marker : Marker InjRV.
Proof. split. { by apply InjRV_inj. } { by apply InjRV_dec_range. } Qed.

Instance InjLV_InjRV_disj_range : DisjRange InjLV InjRV.
Proof. by intros ?. Qed.
Instance InjRV_InjLV_disj_range : DisjRange InjRV InjLV.
Proof. by intros ?. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e : to_val (fill_item Ki e) = None.
Proof. induction Ki; simplify_option_eq; eauto. Qed.

Lemma fill_item_eff Ki e : to_eff (fill_item Ki e) = None.
Proof. induction Ki; simplify_option_eq; eauto. Qed.

Lemma fill_val K e v : to_val (fill K e) = Some v → K = EmptyCtx ∧ e = Val v.
Proof.
  destruct K as [|Ki K].
  - intro H; by rewrite (of_to_val _ _ H).
  - destruct Ki; by naive_solver.
Qed.

Lemma fill_val' K e v : fill K e = Val v → K = EmptyCtx ∧ e = Val v.
Proof. intros ?; apply (fill_val _ e v). by rewrite H. Qed.

Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
Proof. induction K as [|Ki K]; eauto. intros ?; by apply fill_item_val. Qed.

Lemma fill_not_eff K e : to_eff e = None → to_eff (fill K e) = None.
Proof.
  induction K as [|Ki K]; eauto.
  induction Ki; simplify_option_eq; eauto.
Qed.

Lemma fill_eff K e v k : to_eff (fill K e) = Some (v, k) → K = EmptyCtx ∧ e = Eff v k.
Proof.
  destruct K as [|Ki K].
  - intros Heq. by rewrite (of_to_eff _ _ _ Heq).
  - by rewrite fill_item_eff.
Qed.

Lemma fill_eff' K e v k : fill K e = of_eff v k → K = EmptyCtx ∧ e = Eff v k.
Proof. intros Heq. apply fill_eff. by rewrite Heq. Qed.

Lemma val_head_stuck e1 σ1 e2 σ2 : head_step e1 σ1 e2 σ2 → to_val e1 = None.
Proof. destruct 1; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. revert Ki1. induction Ki2, Ki1; naive_solver eauto with f_equal. Qed.

Lemma alloc_fresh v σ :
  let l := fresh_locs (dom (gset loc) σ.(heap)) in
  head_step (Alloc (Val v))                                  σ
            (Val $ LitV $ LitLoc l) (state_upd_heap <[l:=v]> σ).
Proof.
  intros.
  apply AllocS.
  intros. apply (not_elem_of_dom (D := gset loc)).
  specialize (fresh_locs_fresh (dom _ (heap σ)) 0).
  rewrite loc_add_0. naive_solver.
Qed.

Lemma try_with_fresh h r v k σ :
 let l := fresh_locs (dom (gset loc) σ.(heap)) in
 head_step (TryWith (Eff v k) h r)                    σ
           (App (App h (Val v)) (Val (ContV k l)))
           (state_upd_heap <[l:=LitV $ LitBool true]> σ).
Proof.
  intros. apply TryWithEffS.
  intros. apply (not_elem_of_dom (D := gset loc)).
  specialize (fresh_locs_fresh (dom _ (heap σ)) 0).
  rewrite loc_add_0. naive_solver.
Qed.

Lemma eff_lang_mixin : LanguageMixin of_val to_val prim_step'.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val.
  unfold prim_step'.
  intros e σ obs e' σ' efs.
  case obs; [|done]; case efs; [|done].
  induction 1 as [K e1' e2' -> ? ?].
  case K as [|Ki K].
  - revert H0. apply val_head_stuck.
  - apply fill_item_val.
Qed.
End eff_lang.

(** Language *)

Canonical Structure eff_lang : language := Language eff_lang.eff_lang_mixin.

(* Prefer exn_lang names over ectx_language names. *)
Export eff_lang.

Lemma prim_step_to_val_is_head_step e σ1 w σ2 :
  prim_step e σ1 (Val w) σ2 → head_step e σ1 (Val w) σ2.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some w) as H3; first by rewrite -H2.
  apply fill_val in H3 as [-> ->]. subst e. done.
Qed.

(** If [e1] makes a head step to a value under some state [σ1] then any head
 step from [e1] under any other state [σ1'] must necessarily be to a value. *)
Lemma head_step_to_val e1 σ1 e2 σ2 σ1' e2' σ2' :
  head_step e1 σ1  e2  σ2  →
  head_step e1 σ1' e2' σ2' →
  is_Some (to_val e2) →
  is_Some (to_val e2').
Proof. destruct 1; inversion 1; try naive_solver. Qed.


(* Neutral Evaluation Contexts. *)

Inductive Forall_ectx (P : ectx_item → Prop) : ectx → Prop :=
  | Forall_EmptyCtx : Forall_ectx P EmptyCtx
  | Forall_ConsCtx ki k :
     P ki → Forall_ectx P k → Forall_ectx P (ConsCtx ki k).

Class NeutralEctxi (Ki : ectx_item) :=
  { neutral_ectxi v k σ :
      head_step (fill_item Ki (Eff v k)) σ
                (Eff v (ConsCtx Ki k))   σ
  }.

Class NeutralEctx (K : ectx) :=
  { neutral_ectx : Forall_ectx NeutralEctxi K }.

Instance EmptyCtx_neutral : NeutralEctx EmptyCtx.
Proof. constructor. by apply Forall_EmptyCtx. Qed.
Instance ConsCtx_neutral Ki K : NeutralEctxi Ki → NeutralEctx K → NeutralEctx (ConsCtx Ki K).
Proof. constructor. apply Forall_ConsCtx; [|apply H0]; done. Qed.
Lemma ConsCtx_neutral_inv Ki K : NeutralEctx (ConsCtx Ki K) → NeutralEctx K.
Proof. intro H. inversion H. by inversion neutral_ectx0. Qed.
Lemma ConsCtx_neutral_inv' Ki K : NeutralEctx (ConsCtx Ki K) → NeutralEctxi Ki.
Proof. intro H. inversion H. by inversion neutral_ectx0. Qed.

Instance AppLCtx_neutral v2 : NeutralEctxi (AppLCtx v2).
Proof. constructor => v k σ. by apply AppLEffS. Qed.
Instance AppRCtx_neutral e1 : NeutralEctxi (AppRCtx e1).
Proof. constructor => v k σ. by apply AppREffS. Qed.
Instance DoCtx_neutral : NeutralEctxi DoCtx.
Proof. constructor => v k σ. by apply DoEffS. Qed.
Instance UnOpCtx_neutral op : NeutralEctxi (UnOpCtx op).
Proof. constructor => v k σ. by apply UnOpEffS. Qed.
Instance BinOpLCtx_neutral op v2 : NeutralEctxi (BinOpLCtx op v2).
Proof. constructor => v k σ. by apply BinOpLEffS. Qed.
Instance BinOpRCtx_neutral op e1 : NeutralEctxi (BinOpRCtx op e1).
Proof. constructor => v k σ. by apply BinOpREffS. Qed.
Instance IfCtx_neutral e1 e2 : NeutralEctxi (IfCtx e1 e2).
Proof. constructor => v k σ. by apply IfEffS. Qed.
Instance PairLCtx_neutral v2 : NeutralEctxi (PairLCtx v2).
Proof. constructor => v k σ. by apply PairLEffS. Qed.
Instance PairRCtx_neutral e1 : NeutralEctxi (PairRCtx e1).
Proof. constructor => v k σ. by apply PairREffS. Qed.
Instance FstCtx_neutral : NeutralEctxi FstCtx.
Proof. constructor => v k σ. by apply FstEffS. Qed.
Instance SndCtx_neutral : NeutralEctxi SndCtx.
Proof. constructor => v k σ. by apply SndEffS. Qed.
Instance InjLCtx_neutral : NeutralEctxi InjLCtx.
Proof. constructor => v k σ. by apply InjLEffS. Qed.
Instance InjRCtx_neutral : NeutralEctxi InjRCtx.
Proof. constructor => v k σ. by apply InjREffS. Qed.
Instance CaseCtx_neutral e1 e2 : NeutralEctxi (CaseCtx e1 e2).
Proof. constructor => v k σ. by apply CaseEffS. Qed.
Instance AllocCtx_neutral : NeutralEctxi AllocCtx.
Proof. constructor => v k σ. by apply AllocEffS. Qed.
Instance LoadCtx_neutral : NeutralEctxi LoadCtx.
Proof. constructor => v k σ. by apply LoadEffS. Qed.
Instance StoreLCtx_neutral v2 : NeutralEctxi (StoreLCtx v2).
Proof. constructor => v k σ. by apply StoreLEffS. Qed.
Instance StoreRCtx_neutral e1 : NeutralEctxi (StoreRCtx e1).
Proof. constructor => v k σ. by apply StoreREffS. Qed.

Lemma TryWithCtx_non_neutral e2 e3 : ¬ NeutralEctxi (TryWithCtx e2 e3).
Proof.
  intros ?. cut (head_step
      (TryWith (Eff (LitV LitUnit) EmptyCtx) e2 e3)        {|heap:=∅|}
               (Eff (LitV LitUnit)
                    (ConsCtx (TryWithCtx e2 e3) EmptyCtx)) {|heap:=∅|});
  [inversion 1|apply H]; done.
Qed.


(** Reducible *)

Lemma reducible_fill_item_eff Ki `{NeutralEctxi Ki} v k σ :
  reducible (fill_item Ki (Eff v k)) σ.
Proof.
  unfold reducible. simpl. exists [], (Eff v (ConsCtx Ki k)), σ, [].
  apply (Ectx_prim_step _ _ _ _ EmptyCtx (fill_item Ki (Eff v k))
                                        (Eff v (ConsCtx Ki k))); eauto.
  by apply H.
Qed.

Lemma reducible_fill K e σ : reducible e σ → reducible (fill K e) σ.
Proof.
  unfold reducible; simpl; rewrite /prim_step'; simpl.
  destruct 1 as [obs [e' [σ' [efs Hstep]]]].
  case obs in Hstep; [|done]; case efs in Hstep; [|done].
  inversion Hstep. simplify_eq. exists [], (fill (ectx_app K K0) e2'), σ', [].
  apply (Ectx_prim_step _ _ _ _ (ectx_app K K0) e1' e2'); eauto.
  by rewrite fill_ectx_app.
Qed.

Lemma reducible_fill_item Ki e σ : reducible e σ → reducible (fill_item Ki e) σ.
Proof. by apply (reducible_fill (ConsCtx Ki EmptyCtx)). Qed.

Lemma eff_irreducible v k σ : irreducible (Eff v k) σ.
Proof.
  unfold irreducible; simpl. unfold prim_step'; simpl.
  intros obs ???.
  case obs; last auto. 
  case efs; last auto.
  inversion 1.
  destruct K as [|Ki K].
  - simpl in H0; simplify_eq. by inversion H2.
  - destruct Ki; try naive_solver.
Qed.

Lemma reducible_not_eff e σ : reducible e σ → to_eff e = None.
Proof.
  intros ?. case_eq (to_eff e);[|done]. destruct p as (v, k).
  intros ?. specialize (eff_irreducible v k σ).
  rewrite (of_to_eff _ _ _ H0). by rewrite <-not_reducible.
Qed.


(** Pure steps. *)

Record pure_prim_step (e1 e2 : expr) := {
  pure_prim_step_safe σ : prim_step e1 σ e2 σ;
  pure_prim_step_det σ1 e2' σ2 :
    prim_step e1 σ1 e2' σ2 → σ2 = σ1 ∧ e2' = e2
}.

Lemma pure_prim_step_imp_reducible e1 e2 :
  pure_prim_step e1 e2 → (∀ σ, reducible e1 σ).
Proof. intros Hstep ?. exists [], e2, σ, []. by apply Hstep. Qed.

Lemma pure_prim_stepI e1 e2 :
  (∀ σ, head_step e1 σ e2 σ) →
  (∀ σ1 e2' σ2, prim_step e1 σ1 e2' σ2 → σ2 = σ1 ∧ e2' = e2) →
  pure_prim_step e1 e2.
Proof.
  intros Hhead_step Hstep_det. constructor; auto.
  intros ?. apply (Ectx_prim_step _ _ _ _ EmptyCtx e1 e2); by eauto.
Qed.

Lemma pure_prim_stepI' e1 e2 :
  (∀ σ, head_step e1 σ e2 σ) →
  (∀ K e1', e1 = fill K e1' →
    (K = EmptyCtx) ∨ (∃ v, e1' = Val v)) →
  pure_prim_step e1 e2.
Proof.
  intros Hstep Hfill; apply pure_prim_stepI; auto.
  intros ???. inversion 1.
  case (Hfill _ _ H0) as [->|(v & ->)]; [|by inversion H2].
  simpl in H0, H1, H2. simplify_eq.
  specialize (Hstep σ1) as H3.
  inversion H2; simplify_eq; try naive_solver;
  inversion H3; simplify_eq; try naive_solver.
  - unfold state_upd_heap in H9. simpl in H9.
    rewrite lookup_insert in H9. done.
  - unfold state_upd_heap in H4. simpl in H4.
    rewrite lookup_insert in H4. done.
  - split; [|done]. destruct σ1 as [σ1].
    by rewrite /state_upd_heap /= insert_insert.
  - unfold state_upd_heap in H10. simpl in H10.
    rewrite lookup_insert in H10. done.
Qed.

Lemma val_not_pure v e : ¬ pure_prim_step (Val v) e.
Proof.
  intros Hstep.
  specialize (pure_prim_step_imp_reducible _ _ Hstep {|heap:=∅|}) as H.
  specialize (reducible_not_val (Val v) {|heap:=∅|} H); done.
Qed.

Lemma val_not_pure' v e e' : to_val e = Some v → ¬ pure_prim_step e e'.
Proof. intro H1; rewrite <- (of_to_val _ _ H1). by apply val_not_pure. Qed.

Lemma eff_not_pure v k e : ¬ pure_prim_step (Eff v k) e.
Proof.
  intros H0.
  specialize (pure_prim_step_imp_reducible _ _ H0 {|heap:=∅|}).
  specialize (eff_irreducible v k {|heap:=∅|}).
  by rewrite <-not_reducible.
Qed.

Lemma eff_not_pure' v k e e' : to_eff e = Some (v, k) → ¬ pure_prim_step e e'.
Proof. intro H1; rewrite <- (of_to_eff _ _ _ H1). by apply eff_not_pure. Qed.

Lemma pure_prim_step_beta f x e v :
  pure_prim_step ((App (Val $ RecV f x e) (Val v)))
                 (subst' x v (subst' f (RecV f x e) e)).
Proof.
  apply pure_prim_stepI'; [intros ?; by apply BetaS|].
  intros ??. destruct K as [|Ki K]; [intros _; by left|].
  intros Hfill; right.
  destruct Ki; try naive_solver. simpl in Hfill.
  - exists (RecV f x e). inversion Hfill.
    by destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->].
  - exists v. inversion Hfill.
    by destruct (fill_val' _ _ _ (eq_sym H1)) as [-> ->].
Qed.

Lemma pure_prim_step_rec f x e :
  pure_prim_step (Rec f x e) (Val $ RecV f x e).
Proof.
  apply pure_prim_stepI'; [intros ?; by apply RecS|].
  intros ??. destruct K as [|Ki K]; try destruct Ki; by naive_solver.
Qed.

Lemma pure_prim_step_InjL v :
  pure_prim_step (InjL $ Val v) (Val $ InjLV v).
Proof.
  apply pure_prim_stepI'; [intros ?; by apply InjLS|].
  intros ??. destruct K as [|Ki K]; try destruct Ki; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_InjR v :
  pure_prim_step (InjR $ Val v) (Val $ InjRV v).
Proof.
  apply pure_prim_stepI'; [intros ?; by apply InjRS|].
  intros ??. destruct K as [|Ki K]; try destruct Ki; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_case_InjL v e1 e2 :
  pure_prim_step (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof.
  apply pure_prim_stepI'; [intros ?; by apply CaseLS|].
  intros ??. destruct K as [|Ki K]; try destruct Ki; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_case_InjR v e1 e2 :
  pure_prim_step (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof.
  apply pure_prim_stepI'; [intros ?; by apply CaseRS|].
  intros ??. destruct K as [|Ki K]; try destruct Ki; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_if e1 e2 b :
  pure_prim_step (If (Val $ LitV $ LitBool b) e1 e2) (if b then e1 else e2).
Proof.
  apply pure_prim_stepI'; [
  intros ?; case b; [by apply IfTrueS|by apply IfFalseS]|].
  intros ??. destruct K as [|Ki K]; try destruct Ki; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_if_true e1 e2 :
  pure_prim_step (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. by apply pure_prim_step_if. Qed.

Lemma pure_prim_step_if_false e1 e2 :
  pure_prim_step (If (Val $ LitV $ LitBool false) e1 e2) e2.
Proof. by apply pure_prim_step_if. Qed.

Lemma pure_prim_step_pair v1 v2 :
  pure_prim_step (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof.
  apply pure_prim_stepI'; [intros ?; by apply PairS|].
  intros ??. destruct K as [|Ki K]; try destruct Ki; try naive_solver.
  - intros [=]; destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
  - intros [=]; destruct (fill_val' _ _ _ (eq_sym H1)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_Fst v1 v2 :
  pure_prim_step (Fst (Val $ PairV v1 v2)) (Val v1).
Proof.
  apply pure_prim_stepI'; [intros ?; by apply FstS|].
  intros ??. destruct K as [|Ki K]; try destruct Ki; try naive_solver.
  intros [=]; destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_Snd v1 v2 :
  pure_prim_step (Snd (Val $ PairV v1 v2)) (Val v2).
Proof.
  apply pure_prim_stepI'; [intros ?; by apply SndS|].
  intros ??. destruct K as [|Ki K]; try destruct Ki; try naive_solver.
  intros [=]; destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_try_with_val v e₂ e₃ :
  pure_prim_step (TryWith (Val v) e₂ e₃) (App e₃ (Val v)).
Proof.
  apply pure_prim_stepI'; [intros ?; by apply TryWithRetS|].
  intros ??. destruct K as [|Ki K]; try destruct Ki; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_do v :
  pure_prim_step (Do (Val v)) (Eff v EmptyCtx).
Proof.
  apply pure_prim_stepI'; [intros ?; by apply DoS|].
  intros ??. destruct K as [|Ki K]; try destruct Ki; try naive_solver.
  intros [=]. destruct (fill_val' _ _ _ (eq_sym H0)) as [-> ->]; by eauto.
Qed.

Lemma pure_prim_step_eff `{NeutralEctxi Ki} v k :
  pure_prim_step (fill_item Ki (Eff v k)) (Eff v (ConsCtx Ki k)).
Proof.
  apply pure_prim_stepI; [intros ?; by apply H|].
  intros ??.
  inversion 1. destruct K as [|Kj K].
  - simpl in H2, H3. simplify_eq.
    destruct Ki; simpl in H3; inversion H3; try naive_solver.
    by specialize (TryWithCtx_non_neutral e2 e3).
  - simpl in H0, H1. simplify_eq.
    cut ((fill K e1' = Eff v k) ∨ (∃ v', fill K e1' = Val v')).
    + destruct K as [|Kl K]; simpl.
      * case; [intros -> | destruct 1 as [v' ->]]; by inversion H3.
      * case; [| destruct 1 as [v' H4]; destruct Kl; by naive_solver].
        destruct K as [|Km K]; [| destruct Kl, Km; by naive_solver].
        simpl. destruct Kl; try naive_solver.
    + destruct Ki, Kj; simpl in H1; by naive_solver.
Qed.

Lemma Ectxi_prim_step_inv Ki e e₂ σ₁ σ₂ :
  to_val e = None →
  to_eff e = None →
  prim_step (fill_item Ki e) σ₁ e₂ σ₂ →
  ∃ e', prim_step e σ₁ e' σ₂ ∧ e₂ = fill_item Ki e'.
Proof.
  intros ?? Hstep.
  inversion Hstep. destruct K as [|Kj K].
  - simpl in H1, H2, H3; simplify_eq.
    destruct Ki; inversion H3; try naive_solver.
  - simpl in H1, H2; simplify_eq.
    assert (e = fill K e1' ∧ Ki = Kj) as [-> ->].
    { assert (∀ v, (e1' = Val v → False)).
      { intros v ->; by specialize (val_head_stuck _ _ _ _ H3). }
      destruct Ki, Kj; try naive_solver;
      try (simpl in H3; simplify_eq;
           by destruct K as [|Ki K]; try destruct Ki, K; try naive_solver).
    }
  exists (fill K e2'). split; [|done].
  by apply (Ectx_prim_step _ _ _ _ K e1' e2').
Qed.

Lemma Ectx_prim_step_inv K e e₂ σ₁ σ₂ :
  to_val e = None →
  to_eff e = None →
  prim_step (fill K e) σ₁ e₂ σ₂ →
  ∃ e', prim_step e σ₁ e' σ₂ ∧ e₂ = fill K e'.
Proof.
  intros ??. revert e₂. induction K as [|Ki K]; intro e₂.
  - simpl. intros Hstep. exists e₂. by split.
  - simpl. intros Hstep.
    destruct (Ectxi_prim_step_inv Ki _ _ _ _ (fill_not_val K _ H)
                                             (fill_not_eff K _ H0) Hstep)
      as [e' [He' ->]].
    destruct (IHK _ He') as [e'' [He'' ->]].
    by exists e''.
Qed.

Lemma pure_prim_step_fill_item Ki e e' :
  pure_prim_step e e' → pure_prim_step (fill_item Ki e) (fill_item Ki e').
Proof.
  constructor.
  - intros ?. by apply (Ectxi_prim_step' Ki e e'), H.
  - intros ??? Hstep.
    have not_val : to_val e = None.
    { by apply (reducible_not_val _ σ1),
               (pure_prim_step_imp_reducible _ e'). }
    have not_eff : to_eff e = None.
    { by apply (reducible_not_eff _ σ1),
               (pure_prim_step_imp_reducible _ e'). }
    destruct (Ectxi_prim_step_inv Ki e _ _ _ not_val not_eff Hstep) as [e'' [He'' ->]].
    by destruct (pure_prim_step_det _ _ H _ _ _ He'') as [-> ->].
Qed.

Lemma pure_prim_step_fill K e e' :
  pure_prim_step e e' → pure_prim_step (fill K e) (fill K e').
Proof.
  induction K as [|Ki K]; [done|].
  intros ?. simpl. apply pure_prim_step_fill_item.
  apply IHK; eauto.
Qed.

Lemma tc_pure_prim_step_fill K e e' :
  tc pure_prim_step e e' → tc pure_prim_step (fill K e) (fill K e').
Proof.
  induction 1.
  - apply tc_once.
    by apply pure_prim_step_fill.
  - apply (tc_l _ _ (fill K y)); [|done].
    by apply pure_prim_step_fill.
Qed.

Lemma rtc_pure_prim_step_fill K e e' :
  rtc pure_prim_step e e' → rtc pure_prim_step (fill K e) (fill K e').
Proof.
  induction 1; [done|].
  apply (rtc_l _ _ (fill K y)); [|done].
  by apply pure_prim_step_fill.
Qed.

Lemma tc_pure_prim_step_fill_item Ki e e' :
  tc pure_prim_step e e' → tc pure_prim_step (fill_item Ki e) (fill_item Ki e').
Proof. by apply (tc_pure_prim_step_fill (ConsCtx Ki EmptyCtx)). Qed.

Lemma rtc_pure_prim_step_fill_item Ki e e' :
  rtc pure_prim_step e e' → rtc pure_prim_step (fill_item Ki e) (fill_item Ki e').
Proof. by apply (rtc_pure_prim_step_fill (ConsCtx Ki EmptyCtx)). Qed.

Lemma reducible_fill_item_inv Ki e σ :
  to_val e = None →
  to_eff e = None →
  reducible (fill_item Ki e) σ →
  reducible e σ.
Proof.
  intros ??. unfold reducible; simpl; unfold prim_step'; simpl.
  intros [obs [e₂ [σ' [efs Hstep]]]].
  case obs in Hstep; [|done].
  case efs in Hstep; [|done].
  destruct (Ectxi_prim_step_inv _ _ _ _ _ H H0 Hstep) as [e' [Hstep' _]].
  by exists [], e', σ', [].
Qed.

Lemma rtc_pure_prim_step_eff `{NeutralEctx K} v k :
  rtc pure_prim_step (fill K (Eff v k)) (Eff v (ectx_app K k)).
Proof.
  induction K as [|Ki K].
  - done.
  - specialize (ConsCtx_neutral_inv' _ _ H) as Ki_neutral.
    specialize (ConsCtx_neutral_inv  _ _ H) as  K_neutral.
    apply (rtc_r _ (fill_item Ki (Eff v (ectx_app K k)))); simpl.
    + by apply rtc_pure_prim_step_fill_item; auto.
    + by apply pure_prim_step_eff.
Qed.
