(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * Expressions.v : pWHILE Expressions *)


Set Implicit Arguments.

Require Export Operators.
Require Export Memory.

(* move *)
 Fixpoint seqZ (start : Z) (len : nat) : list Z :=
   match len with
     | 0%nat => nil
     | S len0 => start :: seqZ (Zsucc start) len0
   end.

 Definition Z_support n1 n2 :=
   if Zle_bool n1 n2 then (seqZ n1 (Zabs_nat (Zsucc n2 - n1)))
     else 0%Z :: nil.

 Lemma seqZ_length : forall l s,
   length (seqZ s l) = l.
 Proof.
  induction l; simpl; auto.
 Qed.

 Lemma Z_support_not_nil : forall n1 n2,
   Z_support n1 n2  <> nil.
 Proof.
  intros; unfold Z_support.
  case_eq (Zle_bool n1 n2); intros.
  apply Zle_is_le_bool in H.
  intro Heq.
  apply f_equal with (f := (fun x => length x)) in Heq.
  simpl in Heq.
  rewrite seqZ_length in Heq.
  apply f_equal with (f := (fun x => Z_of_nat x)) in Heq.
  rewrite inj_Zabs_nat in Heq.
  simpl in Heq.
  assert (forall n, Zabs n = 0 -> n = 0)%Z.
  intros.
  destruct n; simpl in *; try discriminate; auto.
  apply H0 in Heq.
  omega.
  intro; discriminate.
 Qed.

(** * User-defined random sampling *)
Module Type USUPPORT (UT:UTYPE) (T:TYPE UT).

 Parameter usupport : T.type -> Type.

 Parameter eval : forall k t, usupport t -> list (T.interp k t).

 Parameter ceval : forall k t, usupport t -> list (T.interp k t) * nat.

 Parameter eval_usupport_nil : forall k t (s:usupport t), eval k s <> nil.

 Parameter ceval_spec : forall k t (s:usupport t), eval k s = fst (ceval k s).
 
 Parameter eqb : forall t1 t2, usupport t1 -> usupport t2 -> bool.
 
 Parameter eqb_spec_dep :  forall t1 (e1 : usupport t1) t2 (e2:usupport t2), 
  if eqb e1 e2 then eq_dep T.type usupport t1 e1 t2 e2 
  else ~eq_dep T.type usupport t1 e1 t2 e2.
   
 Parameter eqb_spec : forall t (e1 e2:usupport t),
  if eqb e1 e2 then e1 = e2 else e1 <> e2. 

End USUPPORT.


Module EmptySupport (UT:UTYPE) (T:TYPE UT) <: USUPPORT UT T.

 Definition usupport (t:T.type):Type := Empty_set.

 Definition eval k t (us: usupport t) : list (T.interp k t) :=
  match us return list (T.interp k t) with end.

 Definition ceval k t (us: usupport t) : list (T.interp k t) * nat :=
  match us return list (T.interp k t) * nat with end.

 Lemma eval_usupport_nil : forall k t (s:usupport t), eval k s <> nil.
 Proof.
  destruct s.
 Qed.

 Lemma ceval_spec : forall k t (s:usupport t), eval k s = fst (ceval k s).
 Proof.
  destruct s.
 Qed.

 Definition eqb t1 t2 (us1:usupport t1)(us2:usupport t2) := true.
 
 Lemma eqb_spec_dep :  forall t1 (e1 : usupport t1) t2 (e2:usupport t2), 
  if eqb e1 e2 then eq_dep T.type usupport t1 e1 t2 e2 
  else ~eq_dep T.type usupport t1 e1 t2 e2.
 Proof. 
  destruct e1.
 Qed.

 Lemma eqb_spec : forall t (e1 e2:usupport t),
  if eqb e1 e2 then e1 = e2 else e1 <> e2.  
 Proof. 
  destruct e1.
 Qed.

End EmptySupport.


Module Type EXPR (UT:UTYPE) (T:TYPE UT)
 (Var:VAR UT T) (Uop : UOP UT T) (O:OP UT T Uop)
 (US:USUPPORT UT T)
 (Mem: MEM UT T Var).
 
 (* Constants *)
 Inductive cexpr : T.type -> Type :=
 | Cbool :> bool -> cexpr T.Bool
 | Cnat :> nat -> cexpr T.Nat 
 | CZ :> Z -> cexpr T.Zt
 | Cnil : forall t, cexpr (T.List t)
 | Cnone : forall t, cexpr (T.Option t).
 
 (* Expressions *)
 Inductive expr : T.type -> Type :=
 | Ecte :> forall t, cexpr t -> expr t
 | Evar :> forall t, Var.var t -> expr t
 | Eop : forall op, dlist expr (O.targs op) -> expr (O.tres op)
 | Eexists : forall t, Var.var t -> expr T.Bool -> expr (T.List t) -> expr T.Bool
 | Eforall : forall t, Var.var t -> expr T.Bool -> expr (T.List t) -> expr T.Bool
 | Efind : forall t, Var.var t -> expr T.Bool -> expr (T.List t) -> expr t.
 
 Definition args := dlist expr.
 
 (* Induction principles *)
 Parameter expr_ind2 : forall (P : forall t, expr t -> Prop)
  (Pl : forall l, args l -> Prop),
  (forall t (c:cexpr t), P _ c) ->
  (forall t (v:Var.var t), P _ v) ->
  (forall op args, Pl (O.targs op) args -> P _ (Eop op args)) ->
  (forall t (v:Var.var t) e1 e2, P _ e1 -> P _ e2 -> P _ (Eexists v e1 e2)) ->
  (forall t (v:Var.var t) e1 e2, P _ e1 -> P _ e2 -> P _ (Eforall v e1 e2)) ->
  (forall t (v:Var.var t) e1 e2, P _ e1 -> P _ e2 -> P _ (Efind v e1 e2)) ->
  (Pl nil (dnil expr)) ->
  (forall t l e le, P t e -> Pl l le -> Pl (t::l) (dcons t e le)) ->
  forall t e, P t e.

 Parameter expr_ind_and :  forall (P : forall t, expr t -> Prop) 
  (Pl : forall l, args l -> Prop),
  (forall t (c:cexpr t), P _ c) ->
  (forall t (v:Var.var t), P _ v) ->
  (forall op args, Pl (O.targs op) args -> P _ (Eop op args)) ->
  (forall t (v:Var.var t) e1 e2, P _ e1 -> P _ e2 -> P _ (Eexists v e1 e2)) ->
  (forall t (v:Var.var t) e1 e2, P _ e1 -> P _ e2 -> P _ (Eforall v e1 e2)) ->
  (forall t (v:Var.var t) e1 e2, P _ e1 -> P _ e2 -> P _ (Efind v e1 e2)) ->
  (Pl nil (dnil expr)) ->
  (forall t l e le, P t e -> Pl l le -> Pl (t::l) (dcons t e le)) ->
  (forall t e, P t e) /\ (forall lt args, Pl lt args).
 
 Parameter ceqb : forall t1 t2, cexpr t1 -> cexpr t2 -> bool.

 Parameter ceqb_spec_dep : forall t1 (e1 : cexpr t1) t2 (e2:cexpr t2), 
  if ceqb e1 e2 then eq_dep T.type cexpr t1 e1 t2 e2 
  else ~eq_dep T.type cexpr t1 e1 t2 e2.
   
 Parameter ceqb_spec : forall t (e1 e2:cexpr t),
  if ceqb e1 e2 then e1 = e2 else e1 <> e2. 
  
 Parameter eqb : forall t1 t2, expr t1 -> expr t2 -> bool.

 Parameter eqb_spec_dep : forall t1 (e1 : expr t1) t2 (e2:expr t2), 
  if eqb e1 e2 then eq_dep T.type expr t1 e1 t2 e2 
  else ~eq_dep T.type expr t1 e1 t2 e2.
   
 Parameter eqb_spec : forall t (e1 e2:expr t),
  if eqb e1 e2 then e1 = e2 else e1 <> e2. 
 
 Parameter args_eqb : forall l1 l2,  args l1 -> args l2 -> bool.

 Parameter args_eqb_spec_dep : forall l1 (a1 : args l1) l2 (a2:args l2), 
  if args_eqb a1 a2 then eq_dep (list T.type) args l1 a1 l2 a2 
  else ~eq_dep (list T.type) args l1 a1 l2 a2.

 Parameter args_eqb_spec : forall l (a1 a2:args l),
  if args_eqb a1 a2 then a1 = a2 else a1 <> a2. 

 (* Dependant Equality *)
 Parameter eq_dep_eq : forall t (P:expr t->Type) (p:expr t) (x y:P p), 
  eq_dep (expr t) P p x p y -> x = y.
 
 Parameter UIP_refl : forall t (x:expr t) (p:x = x), p = refl_equal x.
 
 Parameter inj_pair2 : forall t (P:expr t -> Type) (p:expr t) (x y:P p),
  existT P p x = existT P p y -> x = y.


 Section EVAL.

  Variable k : nat.

  Definition eval_cexpr t (c:cexpr t) : T.interp k t :=
   match c in (cexpr t0) return T.interp k t0 with
   | Cbool b => b
   | Cnat n => n
   | CZ n => n
   | Cnil t => @nil (T.interp k t)
   | Cnone t => @None (T.interp k t)
   end.

  Definition ceval_cexpr t (c:cexpr t) : T.interp k t * nat :=
   match c in (cexpr t0) return T.interp k t0 * nat with
   | Cbool b => (b, S O)
   | Cnat n => (n, size_nat n)   
   | CZ n => (n, size_Z n)
   | Cnil t => (@nil (T.interp k t), S O)
   | Cnone t => (@None (T.interp k t), S O)
   end.

  Fixpoint eval_expr (t:T.type) (e:expr t) (m:Mem.t k) : T.interp k t :=
   match e in expr t0 return T.interp k t0 with
   | Ecte t c => eval_cexpr c
   | Evar t v => m v
   | Eop op la =>
     O.eval_op op (dmap (T.interp k) (fun t (e:expr t) => eval_expr e m) la)
   | Eexists t x e1 e2 =>
     List.existsb 
     (fun v => eval_expr e1 (Mem.upd m x v)) 
     (eval_expr e2 m)
   | Eforall t x e1 e2 =>
     List.forallb
     (fun v => eval_expr e1 (Mem.upd m x v))
     (eval_expr e2 m)
   | Efind t x e1 e2 => 
     find_default 
     (fun v => eval_expr e1 (Mem.upd m x v)) 
     (eval_expr e2 m) (T.default k t)
   end.

  Fixpoint ceval_expr (t:T.type) (e:expr t) (m:Mem.t k) : T.interp k t * nat :=
   match e in expr t0 return T.interp k t0 * nat with
   | Ecte t c => ceval_cexpr c
   | Evar t v => (m v, S O)
   | Eop op la =>
     let ca := dfold_right (fun t (e:expr t) c => snd (ceval_expr e m) + c)%nat 0%nat la in
     let (r, c) := O.ceval_op op (dmap (T.interp k) (fun t (e:expr t) => eval_expr e m) la) in
     (r, c + ca)%nat
   | Eexists t x e1 e2 =>
     let (l, n) := ceval_expr e2 m in
      cexistsb 
      (fun v => ceval_expr e1 (Mem.upd m x v)) 
      l n
   | Eforall t x e1 e2 =>
     let (l, n) := ceval_expr e2 m in
      cforallb
      (fun v => ceval_expr e1 (Mem.upd m x v))
      l n
   | Efind t x e1 e2 =>
     let (l, n) := ceval_expr e2 m in
      cfind_default
      (fun v => ceval_expr e1 (Mem.upd m x v))
      l n (T.default k t)
   end.

  Parameter ceval_expr_spec : forall t (e:expr t) m,
   eval_expr e m = fst (ceval_expr e m).

  Definition eval_args lt (a:args lt) (m:Mem.t k) := 
   dmap (T.interp k) (fun t (e:expr t) => eval_expr e m) a.

  Definition ceval_args lt (a:args lt) (m:Mem.t k) := 
   dmap (fun x => T.interp k x * nat)%type (fun t (e:expr t) => ceval_expr e m) a.
  
 End EVAL.

 (* Support for random sampling *)   
 Inductive support : T.type -> Type :=
 | Dbool : support T.Bool
 | Dnat : expr T.Nat -> support T.Nat
 | DZ : expr T.Zt -> expr T.Zt -> support T.Zt
 | Duser : forall t, US.usupport t -> support t
 | Dprod : forall t1 t2, support t1 -> support t2 -> support (T.Pair t1 t2).

 Fixpoint eval_support k t (s:support t) (m: Mem.t k) : list (T.interp k t) :=
  match s in support t0 return list (T.interp k t0) with
  | Dbool => true::false::nil
  | Dnat e => seq 0 (S (eval_expr e m))
  | DZ e1 e2 => Z_support (eval_expr e1 m) (eval_expr e2 m)
  | Duser t s => US.eval k s
  | Dprod t1 t2 s1 s2 => list_prod (eval_support s1 m) (eval_support s2 m)
  end.

 Fixpoint ceval_support k t (s:support t) (m: Mem.t k) : list (T.interp k t) * nat :=
  match s in support t0 return list (T.interp k t0) * nat with
  | Dbool => (true::false::nil, S O)
  | Dnat e => let (n, m) := ceval_expr e m in (seq 0 (S n), m)
  | DZ e1 e2 => 
    let (n1, m1) := ceval_expr e1 m in 
      let (n2, m2) := ceval_expr e2 m in 
        (Z_support n1 n2, plus m1 m2)
  | Duser t s => US.ceval k s
  | Dprod t1 t2 s1 s2 => 
    let (n1, m1) := ceval_support s1 m in
    let (n2, m2) := ceval_support s2 m in
      (list_prod n1 n2, mult m1 m2)
  end.

 Parameter eval_support_nil : forall k t (s:support t) (m:Mem.t k),
  eval_support s m <> nil.

 Parameter ceval_support_spec : forall k t (s:support t) m, 
  eval_support (k:=k) s m = fst (ceval_support (k:=k) s m).
 
 Parameter seqb : forall t1 t2, support t1 -> support t2 -> bool.

 Parameter seqb_spec_dep :  forall t1 (e1 : support t1) t2 (e2:support t2), 
  if seqb e1 e2 then eq_dep T.type support t1 e1 t2 e2 
  else ~eq_dep T.type support t1 e1 t2 e2.
   
 Parameter seqb_spec : forall t (e1 e2:support t),
  if seqb e1 e2 then e1 = e2 else e1 <> e2. 

 (* Usefull functions *) 
 Fixpoint tapp_expr (lt:list T.type) (tr:T.type) : Type:= 
  match lt with
  | nil => expr tr
  | cons t lt => expr t -> tapp_expr lt tr
  end.

 Fixpoint app_expr (lt:list T.type) (tr:T.type) 
  (args:args lt) : tapp_expr lt tr -> expr tr :=
  match args in dlist _ lt0 return tapp_expr lt0 tr -> expr tr with
  | dnil => fun e => e
  | dcons t lt e l => fun op => app_expr tr l (op e)
  end.

 Definition get_uop t (e:expr t) : option (sigT (fun op => args (Uop.targs op))) :=
  match e with
  | Eop op a =>
    match op as op0 
    return args (O.targs op0) -> option (sigT (fun op => args (Uop.targs op))) with
    | O.Ouser uop => fun args => Some (existT _ uop args)
    | _ => fun _ => None
    end a
  | _ => None
  end.

 Parameter get_uop_spec : forall t (e:expr t) op args, 
  get_uop e = Some (existT _ op args) -> 
  eq_dep T.type expr _ e _ (Eop (O.Ouser op) args).

End EXPR.


Module MakeExpr (UT:UTYPE) (T:TYPE UT) 
 (Var:VAR UT T) (Uop : UOP UT T) (O:OP UT T Uop)
 (US:USUPPORT UT T)
 (Mem: MEM UT T Var) <: EXPR UT T Var Uop O US Mem.

 (* Constants *)  
 Inductive cexpr : T.type -> Type :=
 | Cbool :> bool -> cexpr T.Bool
 | Cnat :> nat -> cexpr T.Nat
 | CZ :> Z -> cexpr T.Zt
 | Cnil : forall t, cexpr (T.List t)
 | Cnone : forall t, cexpr (T.Option t).

 (* Expressions *)
 Inductive expr : T.type -> Type :=
 | Ecte :> forall t, cexpr t -> expr t
 | Evar :> forall t (v:Var.var t), expr t
 | Eop : forall op, dlist expr (O.targs op) -> expr (O.tres op)
 | Eexists : forall t, Var.var t -> expr T.Bool -> expr (T.List t) -> expr T.Bool
 | Eforall : forall t, Var.var t -> expr T.Bool -> expr (T.List t) -> expr T.Bool
 | Efind : forall t, Var.var t -> expr T.Bool -> expr (T.List t) -> expr t.

 Definition args := dlist expr.

 (* Induction principles *)
 Lemma expr_ind2 : forall (P : forall t, expr t -> Prop)
  (Pl : forall l, args l -> Prop),
  (forall t (c:cexpr t), P _ c) ->
  (forall t (v:Var.var t), P _ v) ->
  (forall op args, Pl (O.targs op) args -> P _ (Eop op args)) ->
  (forall t (v:Var.var t) e1 e2, P _ e1 -> P _ e2 -> P _ (Eexists v e1 e2)) ->
  (forall t (v:Var.var t) e1 e2, P _ e1 -> P _ e2 -> P _ (Eforall v e1 e2)) ->
  (forall t (v:Var.var t) e1 e2, P _ e1 -> P _ e2 -> P _ (Efind v e1 e2)) ->
  (Pl nil (dnil expr)) ->
  (forall t l e le, P t e -> Pl l le -> Pl (t::l) (dcons t e le)) ->
  forall t e, P t e.
 Proof.
  intros P Pl Hc Hv Hop Hex Hfa Hfind Hnil Hcons.
  fix expr_ind2 2.
  destruct e.
  apply Hc.
  apply Hv.
  apply Hop.
  generalize (O.targs op) d; clear d op.
  induction d.
  apply Hnil.
  apply Hcons; auto.
  apply Hex; auto.
  apply Hfa; auto.
  apply Hfind; auto.
 Qed.

 Lemma expr_ind_and :  forall (P : forall t, expr t -> Prop)
  (Pl : forall l, args l -> Prop),
  (forall t (c:cexpr t), P _ c) ->
  (forall t (v:Var.var t), P _ v) ->
  (forall op args, Pl (O.targs op) args -> P _ (Eop op args)) ->
  (forall t (v:Var.var t) e1 e2, P _ e1 -> P _ e2 -> P _ (Eexists v e1 e2)) ->
  (forall t (v:Var.var t) e1 e2, P _ e1 -> P _ e2 -> P _ (Eforall v e1 e2)) ->
  (forall t (v:Var.var t) e1 e2, P _ e1 -> P _ e2 -> P _ (Efind v e1 e2)) ->
  (Pl nil (dnil expr)) ->
  (forall t l e le, P t e -> Pl l le -> Pl (t::l) (dcons t e le)) ->
  (forall t e, P t e) /\ (forall lt args, Pl lt args).
 Proof.
  split; intros.
  eapply expr_ind2; eauto.
  induction args0; auto.
  apply H6; auto.
  eapply expr_ind2; eauto.
 Qed.

 Definition ceqb (t1 t2:T.type) (c1:cexpr t1) (c2:cexpr t2) : bool :=
  match c1, c2 with
  | Cbool b1, Cbool b2 => Bool.eqb b1 b2
  | Cnat n1, Cnat n2 => nat_eqb n1 n2 
  | CZ n1, CZ n2 => Zeq_bool n1 n2
  | Cnil t1, Cnil t2 => T.eqb t1 t2
  | Cnone t1, Cnone t2 => T.eqb t1 t2
  | _, _ => false
  end.

 Lemma ceqb_spec_dep : forall t1 (e1 : cexpr t1) t2 (e2:cexpr t2), 
  if ceqb e1 e2 then eq_dep T.type cexpr t1 e1 t2 e2 
  else ~eq_dep T.type cexpr t1 e1 t2 e2.
 Proof.
  destruct e1; destruct e2; simpl; try (intro Heq; inversion Heq).
  case_eq (eqb b b0); intros.
  rewrite (eqb_eq b b0);[ constructor | rewrite H; simpl; trivial].
  intros Heq; inversion Heq; subst; rewrite eqb_reflx in H; discriminate.
  generalize (nat_eqb_spec n n0); destruct (nat_eqb n n0); intros; subst.
  constructor.
  intros Heq; apply H; assert (W:=T.eq_dep_eq Heq);
    inversion W; trivial.
  generalize (Zeq_bool_eq z z0); generalize (Zeq_bool_neq z z0); destruct (Zeq_bool z z0); intros.
  elim H0; trivial.
  intros Heq.
  inversion Heq.
  apply H; trivial.
  generalize (T.eqb_spec t t0); destruct (T.eqb t t0); intros; subst.
  constructor.
  intros Heq; apply H; inversion Heq; trivial.
  generalize (T.eqb_spec t t0); destruct (T.eqb t t0); intros; subst.
  constructor.
  intros Heq; apply H; inversion Heq; trivial.
 Qed.

 Lemma ceqb_spec : forall t (e1 e2:cexpr t), if ceqb e1 e2 then e1 = e2 else e1 <> e2. 
 Proof.
  intros t e1 e2; generalize (ceqb_spec_dep e1 e2);
   destruct (ceqb e1 e2); intros.
  apply (T.eq_dep_eq H).
  intros Heq; apply H; rewrite Heq; constructor.
 Qed.
 
 Fixpoint eqb (t1 t2:T.type) (e1:expr t1)(e2:expr t2) {struct e1} : bool :=
  match e1, e2 with
  | Ecte t1 c1, Ecte t2 c2 => ceqb c1 c2
  | Evar t1 v1, Evar t2 v2 => Var.veqb v1 v2
  | Eop op1 args1, Eop op2 args2 => 
    if O.eqb op1 op2 then dforall2 eqb args1 args2 else false
  | Eexists t1 v1 e11 e12, Eexists t2 v2 e21 e22 =>
    if Var.veqb v1 v2 then
      if eqb e11 e21 then eqb e12 e22 else false
    else false 
  | Eforall t1 v1 e11 e12, Eforall t2 v2 e21 e22 =>
    if Var.veqb v1 v2 then
     if eqb e11 e21 then eqb e12 e22 else false
    else false 
  | Efind t1 v1 e11 e12, Efind t2 v2 e21 e22 =>
    if Var.veqb v1 v2 then
     if eqb e11 e21 then eqb e12 e22 else false
    else false 
  | _, _ => false
  end.
 
 Lemma eqb_spec_dep : forall t1 (e1 : expr t1) t2 (e2:expr t2), 
  if eqb e1 e2 then eq_dep T.type expr t1 e1 t2 e2 
  else ~eq_dep T.type expr t1 e1 t2 e2.
 Proof.
  induction e1 using expr_ind2 with 
   (P := fun t1 (e1:expr t1) => forall t2 (e2:expr t2),
    if eqb e1 e2 then eq_dep T.type expr t1 e1 t2 e2 
     else ~eq_dep T.type expr t1 e1 t2 e2)
   (Pl := fun l1 (le1: dlist expr l1) =>
    forall l2 (le2:dlist expr l2),
     if dforall2 eqb le1 le2 then
      eq_dep (list T.type) (dlist expr) l1 le1 l2 le2
      else ~ eq_dep (list T.type) (dlist expr) l1 le1 l2 le2);
   match goal with
    |- forall (t2:T.type) (e2:expr t2), _ => 
     destruct e2; simpl; try (intros Heq; inversion Heq; fail) 
   | _ => idtac end.
  generalize (ceqb_spec_dep c c0); destruct (ceqb c c0); intros H.
  inversion H; subst; simpl; constructor.
  intros Heq; apply H; inversion Heq; simpl; constructor.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); intros; subst.
  inversion H; clear H; constructor.
  intros Heq; apply H; inversion Heq; trivial.
  generalize (O.eqb_spec op op0); destruct (O.eqb op op0); intros; subst.
  generalize (IHe1 _ d); destruct (dforall2 eqb args0 d); intros.
  rewrite (T.l_eq_dep_eq H); constructor.
  intros Heq; apply H; inversion Heq.
  rewrite (O.inj_pair2 H0); constructor.
  intros Heq; apply H; inversion Heq; trivial.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); intros; subst.
  inversion H; clear H; subst.
  rewrite (T.inj_pair2 H3); clear H2 H3.
  generalize (IHe1_1 _ e2_1); destruct (eqb e1_1 e2_1); intros.
  generalize (IHe1_2 _ e2_2); destruct (eqb e1_2 e2_2); intros.
  rewrite (T.eq_dep_eq H).
  rewrite (T.eq_dep_eq H0); constructor.
  intros Heq; assert (W:= T.eq_dep_eq Heq); apply H0; inversion W.
  rewrite (T.inj_pair2 H3); constructor.
  intros Heq; apply H; inversion Heq; constructor.
  intros Heq; apply H; inversion Heq; trivial.
  subst; rewrite (T.inj_pair2 H2); constructor.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); intros; subst.
  inversion H; clear H; subst.
  rewrite (T.inj_pair2 H3); clear H2 H3.
  generalize (IHe1_1 _ e2_1); destruct (eqb e1_1 e2_1); intros.
  generalize (IHe1_2 _ e2_2); destruct (eqb e1_2 e2_2); intros.
  rewrite (T.eq_dep_eq H).
  rewrite (T.eq_dep_eq H0); constructor.
  intros Heq; assert (W:= T.eq_dep_eq Heq); apply H0; inversion W.
  rewrite (T.inj_pair2 H3); constructor.
  intros Heq; apply H; inversion Heq; constructor.
  intros Heq; apply H; inversion Heq; trivial.
  subst; rewrite (T.inj_pair2 H2); constructor.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); intros; subst.
  inversion H; clear H; subst.
  rewrite (T.inj_pair2 H3); clear H2 H3.
  generalize (IHe1_1 _ e2_1); destruct (eqb e1_1 e2_1); intros.
  generalize (IHe1_2 _ e2_2); destruct (eqb e1_2 e2_2); intros.
  rewrite (T.eq_dep_eq H).
  rewrite (T.eq_dep_eq H0); constructor.
  intros Heq; assert (W:= T.eq_dep_eq Heq); apply H0; inversion W.
  rewrite (T.inj_pair2 H3); constructor.
  intros Heq; apply H; inversion Heq; constructor.
  intros Heq; apply H; inversion Heq; trivial.
  subst; rewrite (T.inj_pair2 H4); constructor.
  destruct le2; simpl; try (intros Heq; inversion Heq; fail).
  constructor.
  destruct le2; simpl; try (intros Heq; inversion Heq; fail).
  generalize (IHe1 _ e); destruct (eqb e1 e); intros.
  inversion H; subst.
  rewrite (T.inj_pair2 H3); simpl.
  generalize (IHe0 _ le2); destruct (dforall2 eqb le le2); intros.
  inversion H0; subst; simpl; constructor.
  intros Heq; apply H0; inversion Heq; simpl; constructor.
  intros Heq; apply H; inversion Heq; simpl; constructor.
 Qed.

 Lemma eqb_spec : forall t (e1 e2:expr t),
  if eqb e1 e2 then e1 = e2 else e1 <> e2. 
 Proof.
  intros t e1 e2; generalize (eqb_spec_dep e1 e2); destruct (eqb e1 e2);
   intros.
  apply (T.eq_dep_eq H).
  intros Heq; apply H; rewrite Heq; constructor.
 Qed.

 Definition args_eqb (l1 l2:list T.type) (a1:args l1) (a2: args l2) : bool :=
  dforall2 eqb a1 a2.

 Lemma args_eqb_spec_dep : forall l1 (a1 : args l1) l2 (a2:args l2), 
  if args_eqb a1 a2 then eq_dep (list T.type) args l1 a1 l2 a2 
  else ~eq_dep (list T.type) args l1 a1 l2 a2.
 Proof.
  induction a1; destruct a2; simpl; try (intro Heq; inversion Heq).
  constructor.
  generalize (eqb_spec_dep p e); destruct (eqb p e); intros.
  inversion H; subst; simpl.
  generalize (IHa1 _ a2); destruct (args_eqb a1 a2); intros.
  inversion H0; subst; simpl; constructor.
  intros Heq; apply H0; inversion Heq; subst; simpl; constructor.
  intros Heq; apply H; inversion Heq; subst; simpl; trivial.
 Qed.

 Lemma args_eqb_spec : forall l (a1 a2:args l),
  if args_eqb a1 a2 then a1 = a2 else a1 <> a2. 
 Proof.
  intros t e1 e2; generalize (args_eqb_spec_dep e1 e2);
   destruct (args_eqb e1 e2); intros.
  apply (T.l_eq_dep_eq H).
  intros Heq; apply H; rewrite Heq; constructor.
 Qed.

 
 Section EVAL.

  Variable k : nat.

  Definition eval_cexpr t (c:cexpr t) : T.interp k t :=
   match c in (cexpr t0) return T.interp k t0 with
   | Cbool b => b
   | Cnat n => n   
   | CZ n => n
   | Cnil t => @nil (T.interp k t)
   | Cnone t => @None (T.interp k t)
   end.

  Definition ceval_cexpr t (c:cexpr t) : T.interp k t * nat :=
   match c in (cexpr t0) return T.interp k t0 * nat with
   | Cbool b => (b, S O)
   | Cnat n => (n, size_nat n) 
   | CZ n => (n, size_Z n)
   | Cnil t => (@nil (T.interp k t), S O)
   | Cnone t => (@None (T.interp k t), S O)
   end.

  Fixpoint eval_expr (t:T.type) (e:expr t) (m:Mem.t k) : T.interp k t :=
   match e in expr t0 return T.interp k t0 with
   | Ecte t c => eval_cexpr c
   | Evar t v => m v
   | Eop op la =>
     O.eval_op op (dmap (T.interp k) (fun t (e:expr t) => eval_expr e m) la)
   | Eexists t x e1 e2 =>
     List.existsb 
     (fun v => eval_expr e1 (Mem.upd m x v)) 
     (eval_expr e2 m)
   | Eforall t x e1 e2 =>
     List.forallb
     (fun v => eval_expr e1 (Mem.upd m x v))
     (eval_expr e2 m)
   | Efind t x e1 e2 => 
     find_default 
     (fun v => eval_expr e1 (Mem.upd m x v)) 
     (eval_expr e2 m) (T.default k t)
   end.

 Fixpoint ceval_expr (t:T.type) (e:expr t) (m:Mem.t k) : T.interp k t * nat :=
   match e in expr t0 return T.interp k t0 * nat with
   | Ecte t c => ceval_cexpr c
   | Evar t v => (m v, S O)
   | Eop op la =>
     let ca := dfold_right (fun t (e:expr t) c => snd (ceval_expr e m) + c)%nat 0%nat la in
     let (r, c) := O.ceval_op op (dmap (T.interp k) (fun t (e:expr t) => eval_expr e m) la) in
     (r, c + ca)%nat
   | Eexists t x e1 e2 =>
     let (l, n) := ceval_expr e2 m in
      cexistsb 
      (fun v => ceval_expr e1 (Mem.upd m x v)) 
      l n
   | Eforall t x e1 e2 =>
     let (l, n) := ceval_expr e2 m in
      cforallb
      (fun v => ceval_expr e1 (Mem.upd m x v))
      l n
   | Efind t x e1 e2 =>
     let (l, n) := ceval_expr e2 m in
      cfind_default
      (fun v => ceval_expr e1 (Mem.upd m x v))
      l n (T.default k t)
   end.

  Lemma ceval_expr_spec : forall t (e:expr t) m,
   eval_expr e m = fst (ceval_expr e m).
  Proof.
   induction e; intros.
   case c; trivial.   
   trivial.  
   simpl.
  rewrite O.ceval_op_spec.
  match goal with |- fst ?x = _ => destruct x; trivial end.
   simpl; rewrite IHe2.
   case (ceval_expr e2 m); intros.
   apply existsb_cexistsb.
   intro; apply IHe1.
   simpl; rewrite IHe2.
   case (ceval_expr e2 m); intros.
   apply forallb_cforallb.
   intro; apply IHe1.
   simpl; rewrite IHe2.
   case (ceval_expr e2 m); intros.
   apply find_cfind_default.
   intro; apply IHe1.
  Qed.

  Definition eval_args lt (a:args lt) (m:Mem.t k) := 
   dmap (T.interp k) (fun t (e:expr t) => eval_expr e m) a.

  Definition ceval_args lt (a:args lt) (m:Mem.t k) := 
   dmap (fun x => T.interp k x * nat)%type (fun t (e:expr t) => ceval_expr e m) a.
  
 End EVAL.

 (* Support for random sampling *)   
 Inductive support : T.type -> Type :=
 | Dbool : support T.Bool
 | Dnat : expr T.Nat -> support T.Nat
 | DZ : expr T.Zt -> expr T.Zt -> support T.Zt
 | Duser : forall t, US.usupport t -> support t
 | Dprod : forall t1 t2, support t1 -> support t2 -> support (T.Pair t1 t2). 
  
 Fixpoint eval_support k t (s:support t) (m: Mem.t k) : list (T.interp k t) :=
  match s in support t0 return list (T.interp k t0) with
  | Dbool => true::false::nil
  | Dnat e => seq 0 (S (eval_expr e m))
  | DZ e1 e2 => Z_support (eval_expr e1 m) (eval_expr e2 m)
  | Duser t s => US.eval k s
  | Dprod t1 t2 s1 s2 => list_prod (eval_support s1 m) (eval_support s2 m)
  end.

 Fixpoint ceval_support k t (s:support t) (m: Mem.t k) : list (T.interp k t) * nat :=
  match s in support t0 return list (T.interp k t0) * nat with
  | Dbool => (true::false::nil, S O)
  | Dnat e => let (n, m) := ceval_expr e m in (seq 0 (S n), m)
  | DZ e1 e2 => 
    let (n1, m1) := ceval_expr e1 m in 
      let (n2, m2) := ceval_expr e2 m in 
        (Z_support n1 n2, plus m1 m2)
  | Duser t s => US.ceval k s
  | Dprod t1 t2 s1 s2 => 
    let (n1, m1) := ceval_support s1 m in
    let (n2, m2) := ceval_support s2 m in
      (list_prod n1 n2, mult m1 m2)
  end.

 Lemma eval_support_nil : forall k t (s:support t) (m:Mem.t k),
  eval_support s m <> nil.
 Proof.
  induction s; intros; try (intro; discriminate); simpl.
  apply Z_support_not_nil.
  exact (@US.eval_usupport_nil k t u).
  apply list_prod_nil; auto.
 Qed.

 Lemma ceval_support_spec : forall k t (s:support t) m, 
  eval_support (k:=k) s m = fst (ceval_support (k:=k) s m).
 Proof.
  intros k t s m.
  induction s; simpl; trivial.
  rewrite (ceval_expr_spec e m); case (ceval_expr e m); trivial.
  rewrite (ceval_expr_spec e m); case (ceval_expr e m); trivial.
  rewrite (ceval_expr_spec e0 m); case (ceval_expr e0 m); trivial.
  refine (US.ceval_spec _ _).
  rewrite IHs1, IHs2.
  destruct (ceval_support s1 m).
  destruct (ceval_support s2 m).
  simpl; trivial.
 Qed.

 Fixpoint seqb (t1 t2:T.type) (s1:support t1) (s2:support t2) : bool :=
  match s1, s2 with
  | Dbool, Dbool => true
  | Dnat e1, Dnat e2 => eqb e1 e2
  | DZ e1a e1b, DZ e2a e2b => eqb e1a e2a && eqb e1b e2b
  | Duser t1 u1, Duser t2 u2 => US.eqb u1 u2
  | Dprod t1_1 t2_1 s1_1 s2_1, Dprod t1_2 t2_2 s1_2 s2_2 => 
    andb (seqb s1_1 s1_2) (seqb s2_1 s2_2)
  | _, _ => false
  end.

 Lemma seqb_spec_dep :  forall t1 (e1 : support t1) t2 (e2:support t2), 
  if seqb e1 e2 then eq_dep T.type support t1 e1 t2 e2 
  else ~eq_dep T.type support t1 e1 t2 e2.
 Proof.
  induction e1; destruct e2; simpl; try (intro H; inversion H; fail).
  constructor.
  generalize (eqb_spec_dep e e0); destruct (eqb e e0); intros.
  inversion H; subst.
  rewrite (T.inj_pair2 H0); constructor.
  intro Heq; apply H; inversion Heq; constructor.
  generalize (eqb_spec_dep e e1); destruct (eqb e e1); intros;
    generalize (eqb_spec_dep e0 e2); destruct (eqb e0 e2); intros; simpl.
  inversion H; subst.
  inversion H0; subst.
  rewrite (T.inj_pair2 H1), (T.inj_pair2 H2); constructor.
  intro Heq; apply H0; inversion Heq; constructor.
  intro Heq; apply H; inversion Heq; constructor.
  intro Heq; apply H; inversion Heq; constructor.
  generalize (US.eqb_spec_dep u u0); destruct (US.eqb u u0); intros.
  inversion H; simpl; constructor.
  contradict H; inversion H; simpl; constructor.
  generalize (IHe1_1 t0 e2_1); generalize (IHe1_2 t3 e2_2).
  destruct (seqb e1_2 e2_2); destruct (seqb e1_1 e2_1); simpl; intros.
  destruct H; destruct H0; constructor.
  contradict H0; destruct H; inversion H0; constructor.
  contradict H0; destruct H; inversion H0; constructor.
  contradict H0; destruct H; inversion H0; constructor.
 Qed.

 Lemma seqb_spec : forall t (e1 e2:support t),
  if seqb e1 e2 then e1 = e2 else e1 <> e2. 
 Proof.
  intros t e1 e2; generalize (seqb_spec_dep e1 e2); destruct (seqb e1 e2); intros.
  apply (T.eq_dep_eq H).
  intros Heq; apply H; rewrite Heq; constructor.
 Qed.

 (* Dependant Equality *)
 Lemma eq_dec2 : forall t (p1 p2 : expr t), {p1 = p2} + {p1 <> p2}.
 Proof.
  intros t p1 p2; generalize (eqb_spec p1 p2); destruct (eqb p1 p2); auto. 
 Qed.
 
 Lemma eq_dep_eq : forall t (P:expr t->Type) (p:expr t) (x y:P p), 
  eq_dep (expr t) P p x p y -> x = y.
 Proof.
  intros t; apply (eq_rect_eq__eq_dep_eq (expr t) (eq_rect_eq_dec (@eq_dec2 t))).
 Qed.

 Lemma UIP_refl : forall t (x:expr t) (p:x = x), p = refl_equal x.
 Proof.
  intros t; apply (UIP__UIP_refl (expr t) (eq_dep_eq__UIP (expr t) (@eq_dep_eq t))).
 Qed.

 Lemma inj_pair2 : forall t (P:expr t -> Type) (p:expr t) (x y:P p),
  existT P p x = existT P p y -> x = y. 
 Proof.
  intros t; apply (eq_dep_eq__inj_pairT2 (expr t) (@eq_dep_eq t)).
 Qed.

 (* Usefull functions *) 
 Fixpoint tapp_expr (lt:list T.type) (tr:T.type) : Type:= 
  match lt with
  | nil => expr tr
  | cons t lt => expr t -> tapp_expr lt tr
  end.

 Fixpoint app_expr (lt:list T.type) (tr:T.type) 
  (args:args lt) : tapp_expr lt tr -> expr tr :=
  match args in dlist _ lt0 return tapp_expr lt0 tr -> expr tr with
  | dnil => fun e => e
  | dcons t lt e l => fun op => app_expr tr l (op e)
  end.

 Definition get_uop t (e:expr t) : option (sigT (fun op => args (Uop.targs op))) :=
  match e with
  | Eop op a =>
    match op as op0 
    return args (O.targs op0) -> option (sigT (fun op => args (Uop.targs op))) with
    | O.Ouser uop => fun args => Some (existT _ uop args)
    | _ => fun _ => None
    end a
  | _ => None
  end.

 Module UOdec <: DecidableType.

   Definition U := Uop.t.

   Lemma eq_dec : forall (t1 t2:U), sumbool (t1 = t2) (t1 <> t2).
   Proof.
    intros t1 t2.
    generalize (Uop.eqb_spec t1 t2); destruct (Uop.eqb t1 t2); auto.
   Qed.

 End UOdec.
 
 Module UopD := DecidableEqDepSet UOdec.

 Lemma get_uop_spec : forall t (e:expr t) op args, 
  get_uop e = Some (existT _ op args) -> 
  eq_dep T.type expr _ e _ (Eop (O.Ouser op) args).
 Proof.
  destruct e; simpl; try (intros; discriminate). 
  destruct op; simpl; intros; try discriminate.
  injection H; clear H; intros; subst.
  rewrite (UopD.inj_pair2 (fun x => args (Uop.targs x)) op d args0 H); trivial.
 Qed.

End MakeExpr.
