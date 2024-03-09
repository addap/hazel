(* semantics.v *)

(* This file formalizes the small-step operational semantics of [eff_lang] as
   a binary relation on _configurations_, which are pairs of an expression [e]
   and a store [σ]. The semantics is mostly standard except for the constructs
   related to effects and handlers:

   (1) The construct [Eff m v k] formalizes the capture of the evaluation
       context in a small-step semantics. If [Eff m v k] evaluates under
       a frame [f] different from a handler, then [Eff m v k] reduces to
       [Eff m v (f :: k)] in one step. When [Eff m v k] "reaches a handler"
       (i.e., when the surrounding evaluation frame is a handler), the
       expression [TryWith (Eff m v k) h r] reduces to [h v (ContV k l)],
       (where [l] is a fresh memory location that points to [false]),
       if [m = OS]; otherwise this expression reduces to [h v (KontV k)].
       In sum, we have the following rules:

                    (f (Eff m v k) , σ) --> (Eff m v (f :: k) , σ)
         (TryWith (Eff OS v k) h r , σ) --> (h v (ContV k l) , σ[l ↦ false])
         (TryWith (Eff MS v k) h r , σ) --> (h v (KontV k l) , σ)

   (2) The construct [ContV k l] reduces to [fill k v] (the "filling of the
       context [k] with [v]") the first time it is applied to a value [v].
       To implement this one-shot restriction, the location [l] is updated
       to [true] after the first invocation. The construct [KontV k], on the
       other hand, always reduces to [fill k v] when applied to [v]. In sum,
       we have the following rules:

              (((ContV k l) v), σ[l ↦ false]) --> (fill k v, σ[l ↦ true])
                          (((KontV k) v), σ]) --> (fill k v, σ)

*)

From language Require Import syntax.

(* ========================================================================== *)
(** * Preliminary Definitions. *)

(* -------------------------------------------------------------------------- *)
(** Frames. *)

Definition fill_frame (f : frame) (e : expr) : expr :=
  match f with
  | AppLCtx v2 =>
      App e (of_val v2)
  | AppRCtx e1 =>
      App e1 e
  | DoCtx m =>
      Do m e
  | TryWithCtx e2 e3 =>
      TryWith e e2 e3
  | UnOpCtx op =>
      UnOp op e
  | BinOpLCtx op v2 =>
      BinOp op e (Val v2)
  | BinOpRCtx op e1 =>
      BinOp op e1 e
  | IfCtx e1 e2 =>
      If e e1 e2
  | PairLCtx v2 =>
      Pair e (Val v2)
  | PairRCtx e1 =>
      Pair e1 e
  | FstCtx =>
      Fst e
  | SndCtx =>
      Snd e
  | InjLCtx =>
      InjL e
  | InjRCtx =>
      InjR e
  | CaseCtx e1 e2 =>
      Case e e1 e2
  | AllocCtx =>
      Alloc e
  | LoadCtx =>
      Load e
  | StoreLCtx v2 =>
      Store e (Val v2)
  | StoreRCtx e1 =>
      Store e1 e
  | CmpXchgLCtx v1 v2 =>
      CmpXchg e (Val v1) (Val v2)
  | CmpXchgMCtx e1 v2 =>
      CmpXchg e1 e (Val v2) 
  | CmpXchgRCtx e1 e2 =>
      CmpXchg e1 e2 e 
  end.


(* -------------------------------------------------------------------------- *)
(** Properties of [fill_frame]. *)

Instance fill_frame_inj f : Inj (=) (=) (fill_frame f).
Proof. induction f; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_frame_val f e : to_val (fill_frame f e) = None.
Proof. induction f; simplify_option_eq; eauto. Qed.

Lemma fill_frame_eff f e : to_eff (fill_frame f e) = None.
Proof. induction f; simplify_option_eq; eauto. Qed.

Lemma fill_frame_no_val_inj f1 f2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
    fill_frame f1 e1 = fill_frame f2 e2 → f1 = f2.
Proof. revert f1. induction f2, f1; naive_solver eauto with f_equal. Qed.

(* -------------------------------------------------------------------------- *)
(** Contexts. *)

Fixpoint fill (k : ectx) (e : expr) : expr :=
  match k with [] => e | f :: k => fill_frame f (fill k e) end.


(* -------------------------------------------------------------------------- *)
(** Properties of [fill]. *)

Lemma fill_app k k' e : fill (k ++ k') e = fill k (fill k' e).
Proof. by induction k as [|f k]; simpl; [|rewrite IHk]. Qed.

Lemma fill_val k e v : to_val (fill k e) = Some v → k = [] ∧ e = Val v.
Proof.
  destruct k as [|f k].
  - by intro H; rewrite (of_to_val _ _ H).
  - by destruct f; naive_solver.
Qed.

Lemma fill_val' k e v : fill k e = Val v → k = [] ∧ e = Val v.
Proof. intros ?; apply (fill_val _ e v). by rewrite H. Qed.

Lemma fill_not_val k e : to_val e = None → to_val (fill k e) = None.
Proof. induction k as [|f k]; eauto. intros ?; by apply fill_frame_val. Qed.

Lemma fill_not_eff k e : to_eff e = None → to_eff (fill k e) = None.
Proof.
  induction k as [|f k]; eauto.
  induction f; simplify_option_eq; eauto.
Qed.

Lemma fill_eff k e m v k' :
  to_eff (fill k e) = Some (m, v, k') → k = [] ∧ e = Eff m v k'.
Proof.
  destruct k as [|f k].
  - intros Heq. by rewrite (of_to_eff _ _ _ _ Heq).
  - by rewrite fill_frame_eff.
Qed.

Lemma fill_eff' k e m v k' : fill k e = of_eff m v k' → k = [] ∧ e = Eff m v k'.
Proof. intros Heq. apply fill_eff. by rewrite Heq. Qed.


(* -------------------------------------------------------------------------- *)
(** Substitution. *)

Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Val _ =>
      e
  | Var y =>
      if decide (x = y) then Val v else Var y
  | Do m e =>
      Do m (subst x v e)
  | Eff _ _ _ =>
      e
  | TryWith e1 e2 e3 =>
      TryWith (subst x v e1) (subst x v e2) (subst x v e3)
  | Rec f y e =>
      Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 =>
      App (subst x v e1) (subst x v e2)
  | UnOp op e =>
      UnOp op (subst x v e)
  | BinOp op e1 e2 =>
      BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 =>
      If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 =>
      Pair (subst x v e1) (subst x v e2)
  | Fst e =>
      Fst (subst x v e)
  | Snd e =>
      Snd (subst x v e)
  | InjL e =>
      InjL (subst x v e)
  | InjR e =>
      InjR (subst x v e)
  | Case e0 e1 e2 =>
      Case (subst x v e0) (subst x v e1) (subst x v e2)
  | Alloc e =>
      Alloc (subst x v e)
  | Load e =>
      Load (subst x v e)
  | Store e1 e2 =>
      Store (subst x v e1) (subst x v e2)
  | CmpXchg e1 e2 e3 =>
      CmpXchg (subst x v e1) (subst x v e2) (subst x v e3)
  | Fork e =>
      Fork (subst x v e)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.


(* ========================================================================== *)
(** * Reduction Relation. *)

(* Semantics of unary operations. *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) =>
      Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) =>
  (* a.d. TODO what does that mean for integers? *)
      Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) =>
      Some $ LitV $ LitInt (- n)
  | _, _ =>
      None
  end.

(* Semantics of binary operations on integers. *)
Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp =>
      Some $ LitInt (n1 + n2)
  | MinusOp =>
      Some $ LitInt (n1 - n2)
  | MultOp =>
      Some $ LitInt (n1 * n2)
  | QuotOp =>
      Some $ LitInt (n1 `quot` n2)
  | RemOp =>
      Some $ LitInt (n1 `rem` n2)
  | AndOp =>
      Some $ LitInt (Z.land n1 n2)
  | OrOp =>
      Some $ LitInt (Z.lor n1 n2)
  | XorOp =>
      Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp =>
      Some $ LitInt (n1 ≪ n2)
  | ShiftROp =>
      Some $ LitInt (n1 ≫ n2)
  | LeOp =>
      Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp =>
      Some $ LitBool (bool_decide (n1 < n2))
  | EqOp =>
      Some $ LitBool (bool_decide (n1 = n2))
  end%Z.

(* Semantics of binary operations on Booleans. *)
Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp =>
      None (* Arithmetic *)
  | AndOp =>
      Some (LitBool (b1 && b2))
  | OrOp =>
      Some (LitBool (b1 || b2))
  | XorOp =>
      Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp =>
      None (* Shifts *)
  | LeOp | LtOp =>
      None (* Inequality *)
  | EqOp =>
      Some (LitBool (bool_decide (b1 = b2)))
  end.

(* Semantics of binary operations. *)
Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    Some $ LitV $ LitBool $ bool_decide (v1 = v2)
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) =>
        LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) =>
        LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l), LitV (LitInt off) =>
    (* a.d. TODO seems a bit weird that any binary operation except EqOp is treated as loc_add. *)
        Some $ LitV $ LitLoc (l +ₗ off)
    | _, _ =>
        None
    end.

(* Heap update. *)
Definition heap_upd (f : gmap loc val → gmap loc val) : state → state :=
  λ σ,  {| heap := f σ.(heap) |}.
Arguments heap_upd _ !_ /.

(* Heap-reduction relation. *)
Inductive head_step : expr → state → expr → state → list expr → Prop :=
  (* Lambda. *)
  | RecS f x e σ :
     head_step (Rec f x e) σ (Val $ RecV f x e) σ []
  (* Pair. *)
  | PairS v1 v2 σ :
     head_step (Pair (Val v1) (Val v2)) σ (Val $ PairV v1 v2) σ []
  (* InjL. *)
  | InjLS v σ :
     head_step (InjL $ Val v) σ (Val $ InjLV v) σ []
  (* InjR. *)
  | InjRS v σ :
     head_step (InjR $ Val v) σ (Val $ InjRV v) σ []
  (* Beta reduction. *)
  | BetaS f x e1 v2 e' σ :
     e' = subst' x v2 (subst' f (RecV f x e1) e1) →
       head_step (App (Val $ RecV f x e1) (Val v2)) σ e' σ []
  (* Invoking a one-shot continuation. *)
  | ContS k l w e' σ :
     σ.(heap) !! l = Some (LitV $ LitBool false) →
       e' = fill k (Val w) →
         head_step (App (Val (ContV k l)) (Val w))            σ
                    e' (heap_upd <[l:=(LitV $ LitBool true)]> σ) []
  (* Invoking a multi-shot continuation. *)
  | KontS k w e' σ :
     e' = fill k (Val w) →
       head_step (App (Val (KontV k)) (Val w)) σ e' σ []
  (* UnOp. *)
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
       head_step (UnOp op (Val v)) σ (Val v') σ []
  (* BinOp. *)
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
       head_step (BinOp op (Val v1) (Val v2)) σ (Val v') σ []
  (* If. *)
  | IfTrueS e1 e2 σ :
     head_step (If (Val $ LitV $ LitBool true) e1 e2) σ e1 σ []
  | IfFalseS e1 e2 σ :
     head_step (If (Val $ LitV $ LitBool false) e1 e2) σ e2 σ []
  (* Fst. *)
  | FstS v1 v2 σ :
     head_step (Fst (Val $ PairV v1 v2)) σ (Val v1) σ []
  (* Snd. *)
  | SndS v1 v2 σ :
     head_step (Snd (Val $ PairV v1 v2)) σ (Val v2) σ []
  (* Case. *)
  | CaseLS v e1 e2 σ :
     head_step (Case (Val $ InjLV v) e1 e2) σ (App e1 (Val v)) σ []
  | CaseRS v e1 e2 σ :
     head_step (Case (Val $ InjRV v) e1 e2) σ (App e2 (Val v)) σ []
  (* Alloc. *)
  | AllocS v σ l :
     σ.(heap) !! l = None →
       head_step (Alloc (Val v))                            σ
                 (Val $ LitV $ LitLoc l) (heap_upd <[l:=v]> σ) []
  (* Load. *)
  | LoadS l v σ :
     σ.(heap) !! l = Some v →
       head_step (Load (Val $ LitV $ LitLoc l)) σ (of_val v) σ []
  (* Store. *)
  | StoreS l v σ :
     is_Some (σ.(heap) !! l) →
       head_step (Store (Val $ LitV $ LitLoc l) (Val v)) σ
                 (Val $ LitV LitUnit) (heap_upd <[l:=v]> σ) []
  (* CmpXchg *)
  | CmpXchgS l v1 v2 vl σ b :
     σ.(heap) !! l = Some vl →
     (* Crucially, this compares the same way as [EqOp]! *)
     vals_compare_safe vl v1 →
     b = bool_decide (vl = v1) →
      head_step (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) σ
               (Val $ PairV vl (LitV $ LitBool b)) (if b then heap_upd <[l:=v2]> σ else σ)
               []
  (* Concurrency *)
  | ForkS e σ :
     head_step (Fork e) σ (Val $ LitV LitUnit) σ [e]   
  (* Do. *)
  | DoS m v σ :
     head_step (Do m (Val v)) σ (Eff m v []) σ []
  (* TryWithOS. *)
  | TryWithOSEffS v k e2 e3 σ l :
     σ.(heap) !! l = None →
       head_step (TryWith (Eff OS v k) e2 e3)            σ
                 (App (App e2 (Val v)) (Val (ContV k l)))
                 (heap_upd <[l:=(LitV $ LitBool false)]> σ) []
  (* TryWithMS. *)
  | TryWithMSEffS v k e2 e3 σ :
     head_step (TryWith (Eff MS v k) e2 e3)           σ
               (App (App e2 (Val v)) (Val (KontV k))) σ []
  (* TryWithRet. *)
  | TryWithRetS v e2 e3 σ :
     head_step (TryWith (Val v) e2 e3) σ (App e3 (Val v)) σ []
  (* AppLCtx. *)
  | AppLEffS m v1 k v2 σ :
     head_step (App (Eff m v1 k) (Val v2))    σ
               (Eff m v1 ((AppLCtx v2) :: k)) σ []
  (* AppRCtx. *)
  | AppREffS e1 m v1 k σ :
     head_step (App e1 (Eff m v1 k))          σ
               (Eff m v1 ((AppRCtx e1) :: k)) σ []
  (* UnOpCtx. *)
  | UnOpEffS op m v k σ :
     head_step (UnOp op (Eff m v k))         σ
               (Eff m v ((UnOpCtx op) :: k)) σ []
  (* BinOpLCtx. *)
  | BinOpLEffS op m v1 k v2 σ :
     head_step (BinOp op (Eff m v1 k) (Val v2))    σ
               (Eff m v1 ((BinOpLCtx op v2) :: k)) σ []
  (* BinOpRCtx. *)
  | BinOpREffS op e1 m v2 k σ :
     head_step (BinOp op e1 (Eff m v2 k))          σ
               (Eff m v2 ((BinOpRCtx op e1) :: k)) σ []
  (* IfCtx. *)
  | IfEffS m v k e1 e2 σ :
     head_step (If (Eff m v k) e1 e2)         σ
               (Eff m v ((IfCtx e1 e2) :: k)) σ []
  (* PairLCtx. *)
  | PairLEffS m v1 k v2 σ :
     head_step (Pair (Eff m v1 k) (Val v2))    σ
               (Eff m v1 ((PairLCtx v2) :: k)) σ []
  (* PairRCtx. *)
  | PairREffS e1 m v2 k σ :
     head_step (Pair e1 (Eff m v2 k))          σ
               (Eff m v2 ((PairRCtx e1) :: k)) σ []
  (* FstCtx. *)
  | FstEffS m v k σ :
     head_step (Fst (Eff m v k))       σ
               (Eff m v (FstCtx :: k)) σ []
  (* SndCtx. *)
  | SndEffS m v k σ :
     head_step (Snd (Eff m v k))       σ
               (Eff m v (SndCtx :: k)) σ []
  (* InjLCtx. *)
  | InjLEffS m v k σ :
     head_step (InjL (Eff m v k))       σ
               (Eff m v (InjLCtx :: k)) σ []
  (* InjRCtx. *)
  | InjREffS m v k σ :
     head_step (InjR (Eff m v k))       σ
               (Eff m v (InjRCtx :: k)) σ []
  (* CaseCtx. *)
  | CaseEffS m v k e1 e2 σ :
     head_step (Case (Eff m v k) e1 e2)         σ
               (Eff m v ((CaseCtx e1 e2) :: k)) σ []
  (* AllocCtx. *)
  | AllocEffS m v k σ :
     head_step (Alloc (Eff m v k))       σ
               (Eff m v (AllocCtx :: k)) σ []
  (* LoadCtx. *)
  | LoadEffS m v k σ :
     head_step (Load (Eff m v k))       σ
               (Eff m v (LoadCtx :: k)) σ []
  (* StoreLCtx. *)
  | StoreLEffS m v1 k v2 σ :
     head_step (Store (Eff m v1 k) (Val v2))    σ
               (Eff m v1 ((StoreLCtx v2) :: k)) σ []
  (* StoreRCtx. *)
  | StoreREffS m e1 v2 k σ :
     head_step (Store e1 (Eff m v2 k))          σ
               (Eff m v2 ((StoreRCtx e1) :: k)) σ []
  (* EffCtx. *)
  | DoEffS m m' v k σ :
     head_step (Do m (Eff m' v k))         σ
               (Eff m' v ((DoCtx m) :: k)) σ []
  (* CmpXchgLCtx *)
  | CmpXchgLS m v1 k v2 v3 σ :
     head_step (CmpXchg (Eff m v1 k) (Val v2) (Val v3)) σ
               (Eff m v1 ((CmpXchgLCtx v2 v3) :: k))    σ []
  | CmpXchgMS m e1 v2 k v3 σ :
     head_step (CmpXchg e1 (Eff m v2 k) (Val v3))       σ
               (Eff m v2 ((CmpXchgMCtx e1 v3) :: k))    σ []
  | CmpXchgRS m e1 e2 v3 k σ :
     head_step (CmpXchg e1 e2 (Eff m v3 k))             σ
               (Eff m v3 ((CmpXchgRCtx e1 e2) :: k))    σ [].

(* Reduction relation. *)
(* [prim_step] is the closure of the head-reduction
   relation [head_step] over evaluation contexts. *)
Inductive prim_step (e1 : expr) (σ1 : state) (e2 : expr) (σ2 : state) (efs : list expr) : Prop :=
  | Ectx_prim_step (k : ectx) (e1' e2' : expr) :
     e1 = fill k e1' →
       e2 = fill k e2' →
         head_step e1' σ1 e2' σ2 efs →
           prim_step e1  σ1 e2  σ2 efs.


(* -------------------------------------------------------------------------- *)
(** Properties of [head_step] and [prim_step]. *)

(* Closure of [head_step] over evaluation frames. *)
Lemma Ectxi_prim_step f e1' e2' e1 σ1 e2 σ2 efs :
  e1 = fill_frame f e1' →
    e2 = fill_frame f e2' →
      head_step e1' σ1 e2' σ2 efs →
        prim_step e1  σ1 e2  σ2 efs.
Proof.
  intros -> -> H.
  by apply (Ectx_prim_step _ _ _ _ _ [f] e1' e2').
Qed.

(* Closure of [prim_step] over evaluation frames. *)
Lemma Ectxi_prim_step' f e1' e2' e1 σ1 e2 σ2 efs :
  e1 = fill_frame f e1' →
    e2 = fill_frame f e2' →
      prim_step e1' σ1 e2' σ2 efs →
        prim_step e1  σ1 e2  σ2 efs.
Proof.
  intros -> ->. inversion 1. simplify_eq.
  by apply (Ectx_prim_step _ _ _ _ _ (f :: k) e1'0 e2'0).
Qed.

(* Closure of [prim_step] over evaluation contexts. *)
Lemma Ectx_prim_step' k e1 σ1 e2 σ2 e1' e2' efs :
  e1 = fill k e1' →
    e2 = fill k e2' →
      prim_step e1' σ1 e2' σ2 efs →
        prim_step e1  σ1 e2  σ2 efs.
Proof.
  intros -> ->. inversion 1. simplify_eq.
  apply (Ectx_prim_step _ _ _ _ _ (k ++ k0) e1'0 e2'0); eauto;
  by rewrite fill_app.
Qed.

(* If [e1] makes a head step to a value under some state [σ1],
   then any head step from [e1] under any other state [σ1']
   must necessarily be to a value. *)
Lemma head_step_to_val e1 σ1 e2 σ2 σ1' e2' σ2' efs :
  head_step e1 σ1  e2  σ2 efs →
    head_step e1 σ1' e2' σ2' efs →
      is_Some (to_val e2) →
        is_Some (to_val e2').
Proof. destruct 1; inversion 1; try naive_solver. Qed.

(* If [e1] can perform one step, then [e1] is not a value. *)
Lemma val_head_stuck e1 σ1 e2 σ2 efs : head_step e1 σ1 e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; eauto. Qed.

(* There is always a fresh location to be used by [Alloc v]. *)
Lemma alloc_fresh v σ :
  let l := fresh_locs (dom (gset loc) σ.(heap)) in
  head_step (Alloc (Val v))                            σ
            (Val $ LitV $ LitLoc l) (heap_upd <[l:=v]> σ) [].
Proof.
  intros.
  apply AllocS.
  intros. apply (not_elem_of_dom (D := gset loc)).
  specialize (fresh_locs_fresh (dom _ (heap σ)) 0).
  rewrite loc_add_0. naive_solver.
Qed.

(* There is always a fresh location to be used in the
   creation of a new one-shot continuation. *)
Lemma try_with_fresh h r v k σ :
 let l := fresh_locs (dom (gset loc) σ.(heap)) in
 head_step (TryWith (Eff OS v k) h r)           σ
           (App (App h (Val v)) (Val (ContV k l)))
           (heap_upd <[l:=LitV $ LitBool false]> σ) [].
Proof.
  intros. apply TryWithOSEffS.
  intros. apply (not_elem_of_dom (D := gset loc)).
  specialize (fresh_locs_fresh (dom _ (heap σ)) 0).
  rewrite loc_add_0. naive_solver.
Qed.

Lemma Ectxi_prim_step_inv f e e₂ σ₁ σ₂ efs :
  to_val e = None →
    to_eff e = None →
      prim_step (fill_frame f e) σ₁ e₂ σ₂ efs →
        ∃ e', prim_step e σ₁ e' σ₂ efs ∧ e₂ = fill_frame f e'.
Proof.
  intros ?? Hstep.
  inversion Hstep. destruct k as [|f' k].
  - simpl in H1, H2, H3; simplify_eq.
    destruct f; inversion H3; try naive_solver.
  - simpl in H1, H2; simplify_eq.
    assert (e = fill k e1' ∧ f = f') as [-> ->].
    { assert (∀ v, (e1' = Val v → False)).
      { intros v ->; by specialize (val_head_stuck _ _ _ _ _ H3). }
      destruct f, f'; try naive_solver;
      try (simpl in H3; simplify_eq;
           by destruct k as [|f K]; try destruct f, K; try naive_solver).
    }
  exists (fill k e2'). split; [|done].
  by apply (Ectx_prim_step _ _ _ _ _ k e1' e2').
Qed.

Lemma Ectx_prim_step_inv k e e₂ σ₁ σ₂ efs :
  to_val e = None →
    to_eff e = None →
      prim_step (fill k e) σ₁ e₂ σ₂ efs →
        ∃ e', prim_step e σ₁ e' σ₂ efs ∧ e₂ = fill k e'.
Proof.
  intros ??. revert e₂. induction k as [|f k]; intro e₂.
  - simpl. intros Hstep. exists e₂. by split.
  - simpl. intros Hstep.
    destruct (Ectxi_prim_step_inv f _ _ _ _ _ (fill_not_val k _ H)
                                              (fill_not_eff k _ H0) Hstep)
      as [e' [He' ->]].
    destruct (IHk _ He') as [e'' [He'' ->]].
    by exists e''.
Qed.
