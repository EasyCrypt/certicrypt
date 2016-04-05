(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * Group.v : Theory of cyclic groups, including a module to add group elements 
  as a user-defined type in programs *)

Set Implicit Arguments.

Require Export BoolEquality.
Require Export CCMisc.
Require Import Types.
Require Import Operators.


Module Type CYCLIC_GROUP_WITH_ORDER.

 Parameter t : nat -> Type.

 (** Equality is decidable *)
 Parameter eqb : forall k, t k -> t k -> bool.
 Parameter eqb_spec : forall k (x y:t k), if eqb x y then x = y else x <> y.

 (** Group operations: inverse, product, power *)
 Parameter inv : forall k, t k -> t k.
 Parameter mul : forall k, t k -> t k -> t k.
 Parameter pow : forall k, t k -> nat -> t k.

 (** Generator *)
 Parameter g : forall k, t k.
 
 (** Identity element *)
 Definition e k := pow (g k) 0.

 (** Order **)
 Parameter o : forall (k : nat), nat.
 Parameter o_bouned : forall k, ((2^k < (o k) < 2^(k+1) )%nat).

 (** Specification *) 
 Parameter mul_comm : forall k (x y: t k), mul x y = mul y x.
 Parameter mul_assoc : forall k (x y z:t k), mul x (mul y z) = mul (mul x y) z.
 Parameter inv_spec : forall k (x:t k), mul x (inv x) = e k.
 Parameter mul_0_r : forall k (x:t k), mul x (e k) = x.

 Parameter pow_0 : forall k x, pow x 0 = e k.
 Parameter pow_S : forall k (x:t k) n, pow x (S n) = mul x (pow x n).

 Parameter cyclic_k : forall k, pow (g k) (o k) = e k.
 Parameter cyclic_k' : forall k n, pow (g k) n = e k -> exists n', (n = k*n')%nat.

(*
 Parameter cyclic_k' : forall n, (0 < n)%N -> (n < k)%N -> pow g n <> g0.
 Parameter g_gen : forall k (x:t k), exists n, x = pow (g k) n.
*)

 Parameter log : forall k, t k -> nat.
 Parameter log_lt : forall k (x:t k), (log x < (o k))%nat.
 Parameter log_spec : forall k (x:t k), x = pow (g k) (log x).

 Parameter cost_mul : forall k (x y:t k), nat.
 Parameter cost_pow : forall k (x:t k) (n:nat), nat.
 Parameter cost_inv : forall k (x:t k), nat.

 Parameter cost_mul_poly : polynomial.

 Parameter cost_mul_poly_spec : forall k (x y:t k),
  (@cost_mul k x y <= peval cost_mul_poly (pred (size_nat (2^k))))%nat.

 Parameter cost_pow_poly : polynomial.

 Parameter cost_pow_poly_spec : forall k (x:t k) (n:nat),
  (@cost_pow k x n <= peval cost_pow_poly (pred (size_nat (2^k))))%nat.

End CYCLIC_GROUP_WITH_ORDER.


Module CGO_Properties (CG:CYCLIC_GROUP_WITH_ORDER).

 Import CG.

 Lemma pow_e : forall k n, pow (e k) n = e k.
 Proof.
  induction n; intros.
  apply pow_0.
  rewrite pow_S, IHn, mul_0_r; trivial.
 Qed.

 Lemma mul_pow_plus : forall k (x:t k)n1 n2, 
  mul (pow x n1) (pow x n2) = pow x (n1 + n2).
 Proof.
  induction n1; intros; simpl.
  rewrite pow_0, mul_comm; apply mul_0_r.
  repeat rewrite pow_S; rewrite <- mul_assoc, IHn1; trivial.
 Qed.

 Lemma pow_mul_distr : forall k (x y : t k) n, 
  pow (mul x y) n = mul (pow x n) (pow y n).
 Proof.
  induction n; intros.
  repeat rewrite pow_0; rewrite mul_0_r; trivial.
  repeat rewrite pow_S.
  rewrite mul_assoc.
  rewrite (mul_comm  x (pow x n)).
  rewrite <- (mul_assoc (pow x n)).
  rewrite (mul_comm (pow x n)).
  repeat rewrite <- mul_assoc.
  rewrite IHn; trivial.
 Qed.

 Lemma pow_pow : forall k (x:t k)n1 n2, pow (pow x n1) n2 = pow x (n1 * n2).
 Proof.
  induction n1; intros.
  simpl; rewrite pow_0, pow_e; trivial.
  simpl; rewrite pow_S.
  rewrite <- mul_pow_plus, <- IHn1.
  apply pow_mul_distr.
 Qed.

 Lemma pow_periodic: forall k (x: t k) b n,
  pow x b = pow x (b + n * (o k)) .
 Proof.
  intros.
  rewrite <- mul_pow_plus.
  replace (pow x (n * (o k))) with (e k).
  rewrite mul_0_r; auto.
  rewrite (log_spec x), pow_pow.
  rewrite mult_assoc, mult_comm.
  rewrite <- pow_pow, cyclic_k, pow_e; auto. 
 Qed.

 Lemma pow_inj : forall (k a b:nat),
  (a < k)%nat ->
  (b < k)%nat ->
  (pow (g k) a = pow (g k) b) ->
  (a = b)%nat.
 Proof.
  induction a; intros.
  simpl in H1; symmetry in H1.
  rewrite pow_0 in H1; apply cyclic_k' in H1.
  destruct H1 as [i H1]; subst.
  destruct i; [ trivial |].
  rewrite mult_comm in H0; simpl in H0.
  rewrite <- plus_0_r in H0.
  apply plus_lt_reg_l in H0.
  elimtype False; apply (lt_n_O _ H0).
  
  destruct b.
  rewrite pow_0 in H1; apply cyclic_k' in H1.
  destruct H1 as [i H1].
  clear IHa H0.
  destruct i.
  omega.
  rewrite mult_comm in H1; simpl in H1.
  rewrite H1 in H; clear H1.
  rewrite <- plus_0_r in H.
  apply plus_lt_reg_l in H.
  elimtype False; apply (lt_n_O _ H).
 
  apply f_equal.
  apply IHa; clear IHa; [ omega | omega | ].
  repeat (rewrite pow_S in H1).
  rewrite <- mul_0_r with (x:=pow (g k) a), mul_comm.
  rewrite <- mul_0_r with (x:=pow (g k) b), mul_comm.
  rewrite <- inv_spec with (x:=g k).
  repeat rewrite mul_assoc.
  rewrite mul_comm with (x:=pow (g k) a).
  rewrite mul_comm with (x:=pow (g k) b).
  rewrite H1; trivial.
 Qed.


End CGO_Properties.

Inductive tG : Type := Tg.

Module MAKE_GROUP (CGK : CYCLIC_GROUP_WITH_ORDER).

(** * User-defined type module for cyclic groups *)
 Module Gt <: UTYPE.
 
 Module CGKP := CGO_Properties CGK.

 Definition t := tG. 
 Definition eqb ( _ _ :t) := true.

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  simpl; destruct x; destruct y; trivial.
 Qed.

 Definition eq_dec (x y:t) : {x = y} + {True} :=
  match x as x0 return {x0 = y} + {True} with
  | Tg =>
    match y as y0 return {Tg= y0} + {True} with 
    | Tg => left _ (refl_equal Tg) 
    end
  end.

 Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
 Proof.
  destruct x; destruct y; simpl; intros; discriminate.
 Qed.
 
 Definition interp k (_:t) := CGK.t k.

 Definition size k (_:t) (_:CGK.t k) := S k.
 
 Definition default k (t0:t) : interp k t0 := CGK.e k.

 Definition default_poly (t0:t) := pplus (pcst 1) pvar.

 Lemma size_positive : forall k (t0:t) x, (0 < @size k t0 x)%nat.
 Proof.
  intros k t0 x.  
  unfold size; auto with arith.
 Qed.

 Lemma default_poly_spec : forall k (t0:t), 
  (@size k t0 (default k t0) <= peval (default_poly t0) k)%nat.
 Proof.
  intros k t0.
  unfold default, default_poly, size.
  rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
 Qed.
 
 Definition i_eqb k t (g1 g2: interp k t) := CGK.eqb g1 g2.

 Lemma i_eqb_spec : forall k t (x y:interp k t), 
  if i_eqb x y then x = y else x <> y.
 Proof.
  intros; refine (CGK.eqb_spec _ _).
 Qed.

End Gt.


Inductive gop : Type :=
 | OGorder
 | OGen
 | OGmul
 | OGpow
 | OGinv.

(** * Module for user-defined cyclic group operators *)

Module Gop  (T:TYPE Gt) <: UOP Gt T.

 Definition t := gop.

 Definition eqb (o1 o2 : t) : bool :=
  match o1, o2 with
  | OGorder, OGorder
  | OGen, OGen
  | OGmul, OGmul 
  | OGpow, OGpow 
  | OGinv, OGinv => true
  | _, _ => false
  end.

 Lemma eqb_spec :  forall x y, if eqb x y then x = y else x <> y.
 Proof.
  destruct x; destruct y; simpl; trivial; intro; discriminate.
 Qed.

 Definition targs (op : t) : list T.type :=
  match op with
  | OGorder 
  | OGen => nil
  | OGmul => T.User Tg :: T.User Tg :: nil
  | OGpow => T.User Tg :: T.Nat :: nil
  | OGinv =>T.User Tg :: nil
  end.

 Definition tres (op: t) : T.type :=
  match op with
  | OGorder => T.Nat
  | _ => T.User Tg
  end.

 Open Scope nat_scope.

 Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
  match op as op0 return T.type_op k (targs op0) (tres op0) with
  | OGorder => @CGK.o k
  | OGen => @CGK.g k
  | OGmul => @CGK.mul k
  | OGpow => @CGK.pow k
  | OGinv => @CGK.inv k
  end.

 Implicit Arguments interp_op [k].

 Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
  match op as op0 return T.ctype_op k (targs op0) (tres op0) with
  | OGorder => (@CGK.o k, size_nat k)
  | OGen => (@CGK.g k, S O)
  | OGmul => fun x y => (@CGK.mul k x y, CGK.cost_mul x y)
  | OGpow => fun x n => (@CGK.pow k x n, CGK.cost_pow x n)
  | OGinv => fun x => (@CGK.inv k x, CGK.cost_inv x)
  end.

 Implicit Arguments cinterp_op [k].

 Definition eval_op k
  (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) :=
  @T.app_op k (targs op) (tres op) (interp_op op) args.

 Definition ceval_op k 
  (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) * nat :=
  @T.capp_op k (targs op) (tres op) (cinterp_op op) args.

 Lemma ceval_op_spec : forall k op args,
  @eval_op k op args = fst (@ceval_op k op args).
 Proof.
  intros k o args; destruct o; simpl in args;
   T.dlist_inversion args; subst; trivial.
 Qed.

End Gop.

End MAKE_GROUP.
