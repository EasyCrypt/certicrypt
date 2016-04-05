(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * SigmaGSP.v: Sigma GSP protocol *)

Require Import PrimeLib.
Require Import EasyCrypt.
Require Import ZArith.
Require Psatz.

Set Implicit Arguments.

Open Scope Z_scope.

(** TODO: Move somewhere else *)

Lemma seqZ_S : forall n a,
 seqZ a (S n) = seqZ a n ++ (a + Z_of_nat n) :: nil.
Proof.
 induction n; intros.
 rewrite Zplus_0_r; trivial.
 simpl seqZ.
 rewrite <-app_comm_cons; apply f_equal.
 replace (a + Z_of_nat (S n)) with (Zsucc a + Z_of_nat n).
 rewrite <-(IHn (Zsucc a)); trivial.
 rewrite Zplus_succ_comm, inj_S; trivial.
Qed.

Lemma seqZ_app : forall n1 n2 n a,
 (n = n1 + n2)%nat ->
 seqZ a n = seqZ a n1 ++ seqZ (a + Z_of_nat n1) n2.
Proof.
 induction n1; intros.
 replace n2 with n by omega.
 simpl; rewrite Zplus_0_r; trivial.
 rewrite IHn1 with (n2:=S n2); [ | omega].
 rewrite (seqZ_S _ a).
 rewrite <-app_assoc; simpl; apply f_equal, f_equal.
 rewrite Zplus_succ_r, <-inj_S; trivial.
Qed.

Lemma seqZ_app' : forall n1 n a,
 (n1 <= n)%nat ->
 seqZ a n = seqZ a n1 ++ seqZ (a + Z_of_nat n1) (n - n1).
Proof.
 intros; apply seqZ_app; omega.
Qed.

Lemma seqZ_Zsucc : forall n a, 
 seqZ (Zsucc a) n = map Zsucc (seqZ a n).
Proof.
 induction n; intros.
 trivial.
 simpl; apply f_equal, IHn.
Qed.   

Lemma seqZ_Zplus : forall b ,
 0 <= b -> 
 forall n a, seqZ (Zplus a b) n = map (Zplus b) (seqZ a n).
Proof.
 intros b Hpos.
 apply natlike_ind with 
  (P:=fun b => forall n a, seqZ (a + b) n = map (Zplus b) (seqZ a n)).
 intros; rewrite Zplus_0_r, map_id; trivial.
 intros; rewrite <-Zplus_succ_r, seqZ_Zsucc, H0, map_map.
 apply map_ext; auto with zarith.
 trivial.
Qed.   

Lemma finite_sum_le_const : forall (A:Type) (f:A -> U) L v,
 ((forall x, In x L -> f x <= v) -> finite_sum f L <= length L */ v)%tord.
Proof.
 intros.
 rewrite <-(@finite_sum_cte _ (fun _ => v)); trivial.
 apply finite_sum_le; trivial.
Qed.
(***)

Close Scope Z_scope.


(** A family of multiplicative finite groups *)
Module Type GROUP.

 Parameter t : nat -> Type.

 (** The group is finite and non-empty *)
 Parameter elems : forall k, list (t k).

 Parameter elems_full : forall k (x:t k), In x (elems k).
 Parameter elems_nodup : forall k, NoDup (elems k).

 (** Equality is decidable *)
 Parameter eqb : forall k, t k -> t k -> bool.
 Parameter eqb_spec : forall k (x y:t k), if eqb x y then x = y else x <> y.

 (** Identity element *)
 Parameter e : forall k, t k.

 (** Operations: product, inverse *)
 Parameter mul : forall k, t k -> t k -> t k. 
 Parameter inv : forall k, t k -> t k.

 (** Specification *) 
 Parameter mul_assoc : forall k (x y z:t k), mul x (mul y z) = mul (mul x y) z.
 Parameter mul_e_l : forall k (x:t k), mul (e k) x = x.
 Parameter mul_inv_l : forall k (x:t k), mul (inv x) x = e k.
 Parameter mul_comm : forall k (x y:t k), mul x y = mul y x.
 
 (* Power *)
 Fixpoint pow (k:nat) (x:t k) (n:nat) : t k :=
  match n with
  | O => e k
  | S n => mul x (pow x n)
  end.

 Fixpoint powZ (k:nat) (x:t k) (n:Z) {struct n}: t k :=
  match n with
  | Z0 => pow x 0
  | Zpos p => pow x (nat_of_P p)
  | Zneg p => inv (pow x (nat_of_P p))
  end.

 Parameter pow_order : forall k x, pow x (length (elems k)) = e k.

 (* Cost *)
 Parameter order_poly : polynomial.

 Parameter order_size_nat : forall k,
  size_nat (length (elems k)) < peval order_poly k.

 Parameter cost_mul : forall k (x y:t k), nat.
 Parameter cost_pow : forall k (x:t k) (n:Z), nat.
 Parameter cost_inv : forall k (x:t k), nat.

 Parameter cost_mul_poly : polynomial.
 Parameter cost_pow_poly : polynomial.
 Parameter cost_inv_poly : polynomial.

 Parameter cost_mul_poly_spec : forall k (x y:t k),
  cost_mul x y <= peval cost_mul_poly k.

 Parameter cost_pow_poly_spec : forall k (x:t k) (n:Z),
  cost_pow x n <= peval cost_pow_poly k.

 Parameter cost_inv_poly_spec : forall k (x:t k),
  cost_inv x <= peval cost_inv_poly k.

End GROUP.


(** * Derived properties of finite groups *)
Module Group_Properties (G:GROUP).

 Import G.

 Lemma elems_not_nil : forall k, elems k <> nil.
 Proof.
  intros k H.
  assert (X:=elems_full (e k)).
  rewrite H in X; trivial.
 Qed.

 Lemma eqb_refl : forall k (x:t k), eqb x x.
 Proof.
  intros k x.
  generalize (eqb_spec x x).
  case (eqb x x); [ | intro H; elim H]; trivial.
 Qed.

 Lemma mul_pow_plus : forall k (x:t k) n m,
  mul (pow x n) (pow x m) = pow x (n + m).
 Proof.
  induction n; intros; simpl.
  simpl; apply mul_e_l.
  simpl; rewrite <- mul_assoc, IHn; trivial.
 Qed.

 Lemma cancellation : forall k (x y z:t k), mul x y = mul x z -> y = z.
 Proof.
  intros.
  rewrite <- (mul_e_l y), <- (mul_e_l z).
  rewrite <- (mul_inv_l x), <- mul_assoc, <- mul_assoc, H; trivial.
 Qed.

 Lemma mul_e_r : forall k (x:t k), mul x (e k) = x.
 Proof.
  intros; rewrite mul_comm, mul_e_l; trivial.
 Qed.

 Lemma mul_inv_r : forall k (x:t k), mul x (inv x) = e k.
 Proof.
  intros; rewrite mul_comm, mul_inv_l; trivial.
 Qed.

 Lemma inv_mul : forall k (a b : t k), inv (mul a b) = mul (inv a) (inv b).
 Proof.
  intros.
  apply cancellation with (mul a b).
  rewrite mul_inv_r, (mul_comm a b), <- mul_assoc.
  rewrite (mul_assoc a (inv a)), mul_inv_r, mul_e_l, mul_inv_r; trivial.
 Qed.

 Lemma inv_e : forall k, inv (e k) = e k.
 Proof.
  intros.
  apply cancellation with (e k).
  rewrite mul_inv_r, mul_e_l; trivial.
 Qed.

 Lemma inv_inv : forall k (x:t k), inv (inv x) = x.
 Proof.
  intros.
  apply cancellation with (inv x).
  rewrite mul_inv_l, <- inv_mul, mul_inv_r.
  apply inv_e.
 Qed.

 Lemma pow_e : forall k n, pow (e k) n = e k.
 Proof.
  induction n; intros; simpl.
  trivial.
  rewrite mul_e_l; trivial.
 Qed.

 Lemma pow_mul_distr : forall k (x y:t k) n,
  pow (mul x y) n = mul (pow x n) (pow y n).
 Proof.
  induction n; intros.
  simpl; rewrite mul_e_r; trivial. 
  simpl; rewrite mul_assoc.
  rewrite (mul_comm x (pow x n)).
  rewrite <- (mul_assoc (pow x n)).
  rewrite (mul_comm (pow x n)).
  repeat rewrite <- mul_assoc.
  rewrite IHn; trivial.
 Qed.

 Lemma pow_pow : forall k (x:t k) n m, pow (pow x n) m = pow x (n * m).
 Proof.
  induction n; intros; simpl.
  rewrite pow_e; trivial.
  rewrite <- mul_pow_plus, <- IHn; apply pow_mul_distr.
 Qed.

 Lemma pow_inv : forall k (x:t k) n, pow (inv x) n = inv (pow x n).
 Proof.
  induction n; simpl.
  rewrite inv_e; trivial.
  rewrite IHn, inv_mul; trivial.
 Qed.

 Lemma pow_minus : forall k (x:t k) m n,
  n > m ->
  pow x (n - m) = mul (pow x n) (inv (pow x m)).
 Proof.
  intros.
  replace n with (m + (n - m)) by omega.
  rewrite <- mul_pow_plus, <- mul_assoc, mul_comm, <- mul_assoc.
  rewrite mul_inv_l, mul_e_r, minus_plus; trivial.
 Qed.

 Lemma mul_powZ_plus : forall k (x:t k) n m, 
  mul (powZ x n) (powZ x m) = powZ x (n + m).
 Proof.
  intros.
  case n; intros; simpl.
  apply mul_e_l.
  case m; intros; simpl.  
  apply mul_e_r.
  
  rewrite nat_of_P_plus_morphism; apply mul_pow_plus.   
  
  case_eq ((p ?= p0)%positive Eq); intro H; simpl.
  apply Pcompare_Eq_eq in H; rewrite H; rewrite mul_inv_r; trivial.
  
  apply ZC2 in H.
  rewrite nat_of_P_minus_morphism; trivial.
  rewrite pow_minus, mul_comm, inv_mul, inv_inv; trivial.
  apply nat_of_P_gt_Gt_compare_morphism in H; trivial.
  
  rewrite nat_of_P_minus_morphism; trivial.
  rewrite pow_minus; trivial.
  apply nat_of_P_gt_Gt_compare_morphism in H; trivial.
  
  case m; intros; simpl.  
  apply mul_e_r.
  
  case_eq ((p ?= p0)%positive Eq); intro H; simpl.
  apply Pcompare_Eq_eq in H; rewrite H; rewrite mul_inv_l; trivial.
  
  apply ZC2 in H.
  rewrite nat_of_P_minus_morphism; trivial.
  rewrite pow_minus, mul_comm; trivial.
  apply nat_of_P_gt_Gt_compare_morphism in H; trivial.
  
  rewrite nat_of_P_minus_morphism; trivial. 
  rewrite pow_minus, inv_mul, inv_inv; trivial.
  apply nat_of_P_gt_Gt_compare_morphism in H; trivial.
  
  rewrite nat_of_P_plus_morphism.
  rewrite <- inv_mul, mul_pow_plus; trivial.
 Qed.

 Lemma powZ_e : forall k n, powZ (e k) n = e k.
 Proof.
  induction n; simpl.
  trivial.
  apply pow_e.
  rewrite pow_e, inv_e; trivial.
 Qed. 

 Lemma powZ_mul_distr : forall k (x y:t k) n, 
  powZ (mul x y) n = mul (powZ x n) (powZ y n).
 Proof.
  destruct n; intros.
  simpl; rewrite mul_e_r; trivial.
  apply pow_mul_distr.
  simpl.
  rewrite <- inv_mul, pow_mul_distr; trivial.
 Qed.
  
 Lemma powZ_powZ : forall k (x:t k) n m, powZ (powZ x n) m = powZ x (n * m).
 Proof.
  induction n; intros; simpl.
  apply powZ_e.
  case m; intros; simpl.
   trivial.
   rewrite pow_pow, nat_of_P_mult_morphism; trivial. 
   rewrite pow_pow, nat_of_P_mult_morphism; trivial.
  case m; intros; simpl.
   trivial.
   rewrite pow_inv, pow_pow, nat_of_P_mult_morphism; trivial.
   rewrite pow_inv, pow_pow, inv_inv, nat_of_P_mult_morphism; trivial.
 Qed.

 Lemma powZ_pow : forall k (x:t k) n,
  powZ x (Z_of_nat n) = pow x n.
 Proof.
  induction n; simpl.
  trivial.
  rewrite nat_of_P_o_P_of_succ_nat_eq_succ; simpl; trivial.
 Qed.

 Lemma powZ_minus : forall k (x : t k) n,
   powZ x (- n) = inv (powZ x n).
 Proof.
   intros k x n;case n; simpl; trivial.
   rewrite inv_e; trivial.
   intro p; rewrite inv_inv; trivial.
 Qed.

 Lemma powZ_order : forall k (x:t k), powZ x (Z_of_nat (length (elems k))) = e k.
 Proof.
  intros; rewrite powZ_pow; apply pow_order.
 Qed.
 
 Lemma powZ_gcd : forall k (x:t k) (a:Z),
  powZ x a = e k ->
  powZ x (Zgcd a (Z_of_nat (length (elems k)))) = e k.
 Proof.
  intros.
  destruct (Zis_gcd_bezout a (Z_of_nat (length (elems k))) _ (Zgcd_is_gcd a _)).
  rewrite <-H0, <-mul_powZ_plus.
  rewrite Zmult_comm, <-powZ_powZ, H, powZ_e, mul_e_l.
  rewrite Zmult_comm, <-powZ_powZ, powZ_order, powZ_e; trivial.  
 Qed.
 
End Group_Properties.


Module Type PARAMETERS. 

 Declare Module H : GROUP.

 Parameter cplus : nat -> nat.

 Parameter cplus_pos : forall k, 0 < cplus k.

 Parameter cplus_poly : polynomial.

 Parameter size_nat_cplus : forall k, 
  size_nat (cplus k) <= peval cplus_poly k.

 Parameters _T _l : Z.

 Hypothesis l_pos : (0 < _l)%Z.

 Hypothesis T_pos : (0 <= _T)%Z.

 Parameter g : forall k, H.t k.

End PARAMETERS.


(* 
** Functor constructing a SigmaGSP protocol corresponding to an
** exponentiation homomorphism.
*)
Module SigmaGSP (Params:PARAMETERS).
 
 Import Params.

 (** We first extend the semantics with the needed types and operators *)
 Open Scope nat_scope.
 Unset Strict Implicit.

 (** Types for elements of [G], [H], and for challenges [C] *)
 Inductive ut_ : Type := H_t.

 (** * User-defined type module *)
 Module Ut <: UTYPE.

  Definition t := ut_.

  Definition eqb (t1 t2:t) :=
   match t1, t2 with
   | H_t, H_t => true
   end.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   simpl; destruct x; destruct y; simpl; trivial; discriminate.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {True}.
   destruct x; destruct y; (left; apply refl_equal) || (right; trivial).
  Defined.

  Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
  Proof.
   destruct x; destruct y; simpl; intros; discriminate.
  Qed.

  Definition interp k (t0:t) : Type := 
   match t0 with
   | H_t => H.t k
   end.

  Definition size k (t0:t) : interp k t0 -> nat := 
   match t0 with
   | H_t => fun _ => S (size_nat (length (H.elems k)))
   end.

  Definition default k (t0:t) : interp k t0 :=
   match t0 with
   | H_t => H.e k
   end. 

  Definition default_poly (t0:t) := H.order_poly.

  Lemma size_positive : forall k (t0:t) x, 0 < @size k t0 x.
  Proof.
   intros k t0 x; unfold size; destruct t0; auto with arith.
  Qed.

  Lemma default_poly_spec : forall k (t0:t), 
   @size k t0 (default k t0) <= peval (default_poly t0) k.
  Proof.
   intros k t0.
   unfold default, default_poly, size.
   destruct t0.
   apply H.order_size_nat.
  Qed.

  Definition i_eqb k t (x y:interp k t) :=
   match t return interp k t -> interp k t -> bool with
   | H_t => @H.eqb k
   end x y.

  Lemma i_eqb_spec : forall k t (x y:interp k t), 
   if i_eqb x y then x = y else x <> y.
  Proof.
   intros; destruct t0.
   refine (H.eqb_spec _ _).
  Qed.

 End Ut.


 Module T := MakeType Ut.

 Inductive uop_ : Type :=
 | Ocplus
 | OT 
 | Ol 
 | OH_mul 
 | OH_pow 
 | OH_inv
 | Ophi.

 Module Uop <: UOP Ut T.

  Definition t := uop_.
  
  Definition eqb (o1 o2:t) : bool :=
   match o1, o2 with
    | Ocplus, Ocplus
    | OT, OT
    | Ol, Ol
    | OH_mul, OH_mul 
    | OH_pow, OH_pow 
    | OH_inv, OH_inv
    | Ophi, Ophi => true
    | _, _ => false
   end.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   destruct x; destruct y; simpl; trivial; intro; discriminate.
  Qed.

  Definition targs (op:t) : list T.type :=
   match op with
    | Ocplus => nil
    | OT => nil
    | Ol => nil
    | OH_mul => T.User H_t :: T.User H_t :: nil
    | OH_pow => T.User H_t :: T.Zt :: nil
    | OH_inv => T.User H_t :: nil
    | Ophi => T.Zt :: nil
   end.

  Definition tres (op:t) : T.type :=
   match op with
    | Ocplus => T.Zt
    | OT => T.Zt
    | Ol => T.Zt
    | OH_mul => T.User H_t
    | OH_pow => T.User H_t
    | OH_inv => T.User H_t
    | Ophi => T.User H_t
   end.

  Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
   match op as op0 return T.type_op k (targs op0) (tres op0) with
    | Ocplus => Z_of_nat (cplus k)
    | OT => _T
    | Ol => _l
    | OH_mul => @H.mul k
    | OH_pow => @H.powZ k
    | OH_inv => @H.inv k
    | Ophi => @H.powZ k (g k) 
   end.

  Implicit Arguments interp_op [k].

  Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
   match op as op0 return T.ctype_op k (targs op0) (tres op0) with
    | Ocplus => (Z_of_nat (cplus k), 1)
    | OT => (_T, 1)
    | Ol => (_l, 1)
    | OH_mul => fun x y => (H.mul x y, H.cost_mul x y)
    | OH_pow => fun x y => (H.powZ x y, H.cost_pow x y)
    | OH_inv => fun x => (H.inv x, H.cost_inv x)
    | Ophi => fun x => (H.powZ (g k) x, H.cost_pow (g k) x) 
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

 End Uop.

 Module US := EmptySupport Ut T.

 Module Sem := MakeSem.Make Ut T Uop US.
 Module SemT := BaseProp.Make Sem.

 Module Entries.

  (** Semantics with optimizations *)
  Module SemO <: SEM_OPT.

   Module Sem := Sem.
   Export Sem.

   (** Notations *)
   Notation "x '++' y" := (E.Eop O.OZadd {x, y}).
   Notation "x '--' y" := (E.Eop O.OZsub {x, y}) (at level 40, left associativity).
   Notation "x '**' y" := (E.Eop O.OZmul {x, y}) (at level 36, left associativity).
   Notation "x '^^' y" := (E.Eop O.OZpow {x, y}) (at level 30).
   Notation "x '*' y" := (E.Eop (O.Ouser OH_mul) {x,y}).
   Notation "x '^' a" := (E.Eop (O.Ouser OH_pow) {x,a}).
   Notation "x '^-1'" := (E.Eop (O.Ouser OH_inv) {x}) (at level 30).
   Notation "c+" := (E.Eop (O.Ouser Ocplus) (dnil _)).
   Notation "'TT'" := (E.Eop (O.Ouser OT) (dnil _)).
   Notation "'l'" := (E.Eop (O.Ouser Ol) (dnil _)).
   Notation "'Phi' x" := (E.Eop (O.Ouser Ophi) {x}) (at level 25).

   Definition simpl_op (op:Uop.t) (la:E.args (Uop.targs op)) :
    E.expr (Uop.tres op) := E.Eop (O.Ouser op) la.

   Implicit Arguments simpl_op [].

   Lemma simpl_op_spec : forall k op args (m:Mem.t k),
    E.eval_expr (simpl_op op args) m = E.eval_expr (E.Eop (O.Ouser op) args) m.
   Proof.
    destruct op; simpl; trivial. 
   Qed.

  End SemO.

  Module BP := SemT.

  Module Uppt.

   Import SemO.
   Import BP.

   Implicit Arguments T.size [k t].

   (** PPT expression *)
   Definition PPT_expr (t:T.type) (e:E.expr t) 
    (F:polynomial -> polynomial) 
    (G:polynomial -> polynomial) : Prop :=
    forall k (m:Mem.t k) p,
     (forall t (x:Var.var t), 
      BP.Vset.mem x (BP.fv_expr e) -> T.size (m x) <= peval p k)  ->
     let (v,n) := E.ceval_expr e m in
      T.size v <= peval (F p) k /\
      n <= peval (G p) k.

   (** PPT support *)
   Definition PPT_support t (s:E.support t)
    (F:polynomial -> polynomial) 
    (G:polynomial -> polynomial) : Prop :=
    forall k (m:Mem.t k) p,
     (forall t (x:Var.var t), 
      BP.Vset.mem x (BP.fv_distr s) -> T.size (m x) <= peval p k)  ->
     let (xs,n) := E.ceval_support s m in
      (forall v, In v xs -> T.size v <= peval (F p) k) /\
      n <= peval (G p) k.

   Definition utsize : Ut.t -> nat := fun _ => 1.

   Definition utsize_default_poly : nat -> polynomial := fun _ => H.order_poly.

   Lemma utsize_default_poly_spec : forall r ut,
    utsize ut <= r -> 
    forall k, 
     Ut.size (t:=ut) (Ut.default k ut) <= peval (utsize_default_poly r) k.
   Proof.
    intros r ut _ k.
    case ut; simpl; unfold Ut.size, utsize_default_poly. 
    apply H.order_size_nat.
   Qed.

   Definition uop_poly (o:Uop.t) : bool :=
    match o with
    | Ocplus 
    | OT
    | Ol
    | OH_mul | OH_pow | OH_inv 
    | Ophi => true
    end.

   Lemma uop_poly_spec : forall o (la:dlist E.expr (O.targs (O.Ouser o))),
    uop_poly o ->
    (forall t (e:E.expr t), @DIn _ E.expr _ e _ la -> 
     exists F, exists G, PPT_expr e F G) ->
    exists F, exists G, PPT_expr (E.Eop (O.Ouser o) la) F G.
   Proof.
    intros o la H Hla.
    destruct o.

    (* Ocplus *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    exists (fun _ => cplus_poly). 
    exists (fun _ => 1).
    simpl; split.
    simpl.
    unfold size_Z; rewrite Zabs_nat_Z_of_nat.
    apply size_nat_cplus.
    rewrite pcst_spec; trivial.

    (* OT *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    exists (fun _ => size_Z _T). 
    exists (fun _ => 1).
    simpl; split.
    rewrite pcst_spec; trivial.
    rewrite pcst_spec; trivial.

    (* Ol *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    exists (fun _ => size_Z _l). 
    exists (fun _ => 1).
    simpl; split.
    rewrite pcst_spec; trivial.
    rewrite pcst_spec; trivial.

    (* OH_mul *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    destruct (Hla _ x0) as [F2 [G2 H2] ].
    right; left; trivial.
    exists (fun _ => pplus 1 H.order_poly).
    exists (fun p => pplus H.cost_mul_poly (pplus (G1 p) (G2 p))).
    intros k m p Hm; simpl; split.
    rewrite pplus_spec, pcst_spec; trivial.
    generalize (H.order_size_nat k); simpl; unfold Ut.size; omega.
    generalize (H1 k m p) (H2 k m p); clear H1 H2.
    case_eq (E.ceval_expr x m); simpl.
    case_eq (E.ceval_expr x0 m); simpl.
    intros i n Heqi i0 n0 Heqi0 Hi Hi0.
    destruct Hi.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].  
    unfold fv_expr; simpl.
    apply fv_expr_rec_subset.
    destruct Hi0.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x0); [ | trivial].  
    unfold fv_expr at 2; simpl.
    fold (fv_expr_extend x0 (fv_expr_rec Vset.empty x)).
    rewrite union_fv_expr_spec.
    apply VsetP.subset_union_l.
    rewrite plus_0_r, pplus_spec, pplus_spec; apply plus_le_compat; auto.
    apply H.cost_mul_poly_spec.
    apply plus_le_compat; trivial.

    (* OH_pow *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    destruct (Hla _ x0) as [F2 [G2 H2] ].
    right; left; trivial.
    exists (fun _ => pplus 1 H.order_poly).
    exists (fun p => pplus H.cost_pow_poly (pplus (G1 p) (G2 p))).
    intros k m p Hm; simpl; split.
    rewrite pplus_spec, pcst_spec.
    generalize (H.order_size_nat k); simpl; unfold Ut.size; omega.
    generalize (H1 k m p) (H2 k m p); clear H1 H2.
    case_eq (E.ceval_expr x m); simpl.
    case_eq (E.ceval_expr x0 m); simpl.
    intros i n Heqi i0 n0 Heqi0 Hi Hi0.
    destruct Hi.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].  
    unfold fv_expr; simpl.
    apply fv_expr_rec_subset.
    destruct Hi0.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x0); [ | trivial].
    unfold fv_expr at 2; simpl.
    fold (fv_expr_extend x0 (fv_expr_rec Vset.empty x)).
    rewrite union_fv_expr_spec.
    apply VsetP.subset_union_l.
    rewrite plus_0_r, pplus_spec, pplus_spec; apply plus_le_compat; auto.
    apply H.cost_pow_poly_spec.
    apply plus_le_compat; trivial.

    (* OG_inv *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    exists (fun _ => pplus 1 H.order_poly).
    exists (fun p => pplus H.cost_inv_poly (G1 p)).
    intros k m p Hm; simpl; split.
    rewrite pplus_spec, pcst_spec.
    generalize (H.order_size_nat k); simpl; unfold Ut.size; omega.
    generalize (H1 k m p); clear H1.
    case_eq (E.ceval_expr x m); simpl.
    intros y n Heqy Hy.
    destruct Hy.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].
    apply VsetP.subset_refl.
    rewrite plus_0_r, pplus_spec; apply plus_le_compat.
    apply H.cost_inv_poly_spec.
    trivial.

    (* Ophi *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    exists (fun _ => pplus 1 H.order_poly).
    exists (fun p => pplus H.cost_pow_poly (G1 p)).
    intros k m p Hm; simpl; split.
    rewrite pplus_spec, pcst_spec.
    generalize (H.order_size_nat k); simpl; unfold Ut.size; omega.
    generalize (H1 k m p); clear H1.
    case_eq (E.ceval_expr x m); simpl.
    intros y n Heqy Hy.
    destruct Hy.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].
    apply VsetP.subset_refl.
    rewrite plus_0_r, pplus_spec; apply plus_le_compat.
    apply H.cost_pow_poly_spec.
    trivial.
   Qed.
  
   Definition usupport_poly t (us:US.usupport t) : bool := true.

   Lemma usupport_poly_spec : forall t (us:US.usupport t),
    usupport_poly us ->
    exists F, exists G, PPT_support (E.Duser us) F G.
   Proof.
    destruct us.
   Qed.

  End Uppt.

 End Entries.


 Module Import Tactics := EasyCrypt.Make Entries.

  
 (** * The protocol *)
 Module Protocol.

  Definition xT     := T.User H_t.
  Definition wT     := T.Zt.
  Definition rT     := T.User H_t.
  Definition stateT := T.Zt.
  Definition cT     := T.Zt.
  Definition sT     := T.Zt.

  (** Knowledge relation *)
  Definition R k (x:T.interp k xT) (w:T.interp k wT) := 
   x = H.powZ (g k) w /\ (-_T <= w <= _T)%Z.

  Definition R' := R.

  Lemma R_dec : forall k (x:T.interp k xT) (w:T.interp k wT), 
   sumbool (R x w) (~R x w).
  Proof.
   intros; unfold R.
   generalize (H.eqb_spec x (H.powZ (g k) w)).
   case (H.eqb x (H.powZ (g k) w));
   case (Z_le_dec (-_T)%Z w);
   case (Z_le_dec w _T); intuition.
  Qed.

  Definition R'_dec := R_dec.

  (** Variables *)
  Notation x      := (Var.Lvar (T.User H_t) 1).
  Notation w      := (Var.Lvar T.Zt 2).
  Notation r      := (Var.Lvar (T.User H_t) 3). 
  Notation state  := (Var.Lvar T.Zt 4).
  Notation c      := (Var.Lvar T.Zt 5). 
  Notation s      := (Var.Lvar T.Zt 6).
  Notation b      := (Var.Lvar T.Bool 7).
  Notation rstate := (Var.Lvar (T.Pair (T.User H_t) T.Zt) 8).
  Notation rs     := (Var.Lvar (T.Pair (T.User H_t) T.Zt) 9).
  Notation x'     := (Var.Lvar (T.User H_t) 10).
  Notation w'     := (Var.Lvar T.Zt 11).
  Notation r'     := (Var.Lvar (T.User H_t) 12). 
  Notation state' := (Var.Lvar T.Zt 13). 
  Notation c'     := (Var.Lvar T.Zt 14). 
  Notation s'     := (Var.Lvar T.Zt 15).
  Notation c''    := (Var.Lvar T.Zt 16). 
  Notation s''    := (Var.Lvar T.Zt 17).
  Notation c1     := (Var.Lvar T.Zt 18). 
  Notation s1     := (Var.Lvar T.Zt 19).
  Notation c2     := (Var.Lvar T.Zt 20). 
  Notation s2     := (Var.Lvar T.Zt 21).
  Notation t      := (Var.Lvar T.Zt 22).
  Notation u'     := (Var.Lvar T.Zt 23).
  Notation y'     := (Var.Lvar (T.User H_t) 24).
  Notation yu     := (Var.Lvar (T.Pair xT T.Zt) 25).

  (** Procedures *)
  Notation P1 := (Proc.mkP 1 
   ((T.User H_t) :: T.Zt :: nil) 
   (T.Pair (T.User H_t) T.Zt)).
 
  Notation P2 := (Proc.mkP 2 
   ((T.User H_t) :: T.Zt :: T.Zt :: T.Zt :: nil) 
   T.Zt).

  Notation S  := (Proc.mkP 3 
   ((T.User H_t) :: T.Zt :: nil) 
   (T.Pair (T.User H_t) T.Zt)).
 
  Notation KE := (Proc.mkP 4 
   ((T.User H_t) :: (T.User H_t) :: T.Zt :: T.Zt :: T.Zt :: T.Zt :: nil) 
   (T.Pair (T.User H_t) T.Zt)).
  
  Definition P1_args := dcons _ x' (dcons _ w' (dnil Var.var)).
  Definition P1_body := 
   [ 
    t <$- [ (-2 ** TT ** c+ ** l)%Z,, (2 ** TT ** c+ ** l)%Z]
   ].
  Definition P1_re   := (Phi t | t).

  Definition P2_args := 
   dcons _ x' (dcons _ w' (dcons _ state' (dcons _ c' (dnil Var.var)))).
  Definition P2_body := [ s' <- state' ++ c' ** (w' ++ TT) ].
  Definition P2_re : E.expr T.Zt := s'.

  Definition V x r c s := 
   (Phi (s -- c ** TT) =?= r * x ^ c) &&
   ((-2 ** TT ** c+ ** l)%Z <=Z s) && 
   (s <=Z (2 ** TT ** c+ ** l ++ 2 ** TT ** (c+ -- 1)))%Z.

  Definition S_args  := dcons _ x' (dcons _ c' (dnil Var.var)).
  Definition S_body  := 
   [ 
    s' <$- [ (-2 ** TT ** c+ ** l ++ c' ** (TT ++ TT))%Z,, 
             ( 2 ** TT ** c+ ** l ++ c' ** (TT ++ TT))%Z ];
    r' <- Phi (s' -- c' ** TT) * (x' ^ c')^-1
   ].
  Definition S_re    := (r' | s').

  Definition KE_args := 
   dcons _ x' (dcons _ r' (dcons _ c' (dcons _ c'' (dcons _ s' (dcons _ s''
    (dnil Var.var)))))).

  Definition KE_body := 
   [ 
    u' <- ((s'' -- s') /Z (c'' -- c')) -- TT;
    y' <- Phi(u') * (x'^-1) 
   ].

  Definition KE_re : (E.expr (T.Pair (T.User H_t) T.Zt)) := (y' | u').

  Parameter _E : env.

  Section ENV.

   Let add_P1 E := add_decl E P1 P1_args (refl_equal _) P1_body P1_re.
   Let add_P2 E := add_decl E P2 P2_args (refl_equal _) P2_body P2_re.
   Let add_S  E := add_decl E S S_args (refl_equal _) S_body S_re.
   Let add_KE E := add_decl E KE KE_args (refl_equal _) KE_body KE_re.

   Definition E := add_KE (add_S (add_P1 (add_P2 _E))).

  End ENV.

  Parameter P1_i : info P1_args P1_body P1_re.
  Parameter P2_i : info P2_args P2_body P2_re.
  Parameter S_i  : info S_args S_body S_re.
  Parameter KE_i : info KE_args KE_body KE_re.
  
  Definition protocol := 
   [
    rstate <c- P1 with {x, w};
    r <- Efst rstate; state <- Esnd rstate;
    c <$- [0%Z ,, c+ -Z 1%Z];
    s <c- P2 with {x, w, state, c};
    b <- V x r c s
   ].

  Definition protocol' := 
   [
    rstate <c- P1 with {x, w};
    r <- Efst rstate; state <- Esnd rstate;
    s <c- P2 with {x, w, state, c}
   ]. 

  Definition simulation :=
   [
    rs <c- S with {x,c};
    r <- Efst rs;
    s <- Esnd rs
   ].

  Definition R1 : mem_rel := fun k (m1:Mem.t k) _ => R (m1 x) (m1 w).

  Definition iEE := 
   (add_refl_info_O KE (fv_expr KE_re) Vset.empty Vset.empty
   (add_refl_info_O S (fv_expr S_re) Vset.empty Vset.empty
   (add_refl_info_O P1 (fv_expr P1_re) Vset.empty Vset.empty
   (add_refl_info_O P2 (fv_expr P2_re) Vset.empty Vset.empty 
   (empty_info E E))))).

  Definition Inv := req_mem_rel {{x, w}} R1. 

  Lemma decMR_R1 : decMR R1.
  Proof.
   unfold decMR, R1, R; intros k m1 m2.
   apply R_dec.
  Qed.

  Hint Resolve decMR_R1.

  Module HP := Group_Properties H.
 
  Lemma H_eqb_correct : forall k (x y:H.t k), x = y <-> H.eqb x y.
  Proof.
   intros; generalize (H.eqb_spec x y).
   case (H.eqb x y); intros; intuition; discriminate. 
  Qed.

  Definition Uis_uniform (t:T.type) (d:US.usupport t) := true.

  Lemma Uis_uniform_correct : forall t (d:US.usupport t) k,
   Uis_uniform d = true -> NoDup (US.eval k d).
  Proof.
   destruct d.
  Qed.
  
  Definition Uis_full (t:T.type) (d:US.usupport t) := true.
  
  Lemma Uis_full_correct : forall t (d : US.usupport t) k,
   Uis_full d = true -> forall x, In x (US.eval k d).
  Proof.
   destruct d.
  Qed.

  Notation "'PHI' p" := (@Eapp (O.Ouser Ophi) (dcons _ p (dnil _))) (at level 30).
  Notation "'TTT'"   := (@Eapp (O.Ouser OT) (dnil _)) (at level 40). 
  Notation "'---' x" := (@Eapp O.OZopp (dcons _ x (dnil _))) (at level 20).

  Opaque Zmult.

  Lemma completeness : forall k (m:Mem.t k), 
   R (m x) (m w) -> Pr E protocol m (EP k b) == 1.
  Proof.
   intros. 
   transitivity (Pr E [ b <- true ] m (EP k b)).
   apply equiv_deno with 
    (ipred 
     (Pand (Peq (Evar x<1>) (PHI (Evar w<1>)))
           (Pand (Ple (--- TTT) (Evar w<1>)) (Ple (Evar w<1>) (TTT)))))
    (kreq_mem {{b}}).  
   inline_l iEE P1; sinline_l iEE P2.
   setoid_replace (kreq_mem {{b}}) with (ipred (preq_mem {{b}})).
   match goal with 
    |- equiv (ipred ?P) ?E ?c1 ?E ?c2 (ipred ?Q) => change (Equiv P E c1 E c2 Q)
   end.
   check_proof 
    (refl1_info (empty_info E E)) 
    (refl2_info (empty_info E E))
    Uis_uniform Uis_uniform_correct Uis_full Uis_full_correct
    (@Rwp_simpl E E 
     (@Rrand_disj E E t true 
      (@Rrand_disj E E c true 
       (@Rnil E E)))); clear; simpl_goal; repeat split.
   
   pose T_pos; pose l_pos; auto with zarith.

   pose (cplus_pos k); auto with zarith.

   intros; apply is_true_andb; split; [apply is_true_andb; split | ].

   apply H_eqb_correct.
   rewrite H, HP.powZ_powZ, HP.mul_powZ_plus; apply f_equal; ring.

   apply Zle_imp_le_bool; rewrite <-Zplus_0_r at 1; auto with zarith.
  
   apply Zle_imp_le_bool, Zplus_le_compat; [trivial | ].
   rewrite Zmult_comm; apply Zmult_le_compat; auto with zarith.

   unfold SemT.iffMR, SemT.implMR; split; apply preq_mem_correct.

   intros m1 m2 H0; unfold EP, charfun, restr, fone; simpl.
   rewrite (H0 _ b); trivial.
   unfold R in H; split; simpl; intuition.
   
   unfold Pr; rewrite deno_assign_elim.
   unfold charfun, EP, restr; simpl; mem_upd_simpl.
  Qed.

  Import Psatz.

  Definition epsilon (k:nat) : U := [1/]1+Peano.pred (Zabs_nat (_l)).

  Lemma epsilon_bound : forall k c w,
   (Zabs_nat c <= cplus k)%nat ->
   (-_T <= w <= _T)%Z ->
   Zabs_nat (2*c*(_T - w)) */ [1/]1+Zabs_nat(4*_T * Z_of_nat (cplus k) * _l)%Z <=
   epsilon k.
  Proof.
   intros; unfold epsilon.
   repeat rewrite Zabs_nat_mult.
   rewrite <-(Nmult_1 ([1/]1+Peano.pred _)); apply Nmult_Unth_le.
   rewrite mult_1_l, <-(S_pred _ O).
   apply le_S.
   assert (Zabs_nat(_T - w) <= Zabs_nat 2 * Zabs_nat _T)%nat.
   rewrite <-Zabs_nat_mult; apply Zabs_nat_le; auto with zarith.
   replace (Zabs_nat 4) with (Zabs_nat 2 * Zabs_nat 2)%nat by (compute; trivial).
   apply mult_le_compat; trivial.
   repeat rewrite <-mult_assoc.
   apply mult_le_compat; [trivial | ].
   rewrite mult_comm, mult_assoc.
   apply mult_le_compat; trivial.
   rewrite Zabs_nat_Z_of_nat; trivial.
   change O with (Zabs_nat 0%Z); apply Zabs_nat_lt; split; [apply Zle_refl | ].
   apply l_pos.
  Qed.

  Lemma SHVZK_aux :
   prg_SD (req_mem_rel {{x,w,c}} 
    (R1 /-\ (fun k m1 _ => 0 <= m1 c <= Z_of_nat (cplus k))))%Z 
   E 
   [
    t <$- [(-2)%Z ** TT ** c+ ** l,, 2%Z ** TT ** c+ ** l];
    r <- Phi t;
    s <- t ++ c ** (w ++ TT)
   ]
   E 
   [
    s <$- [(-2)%Z ** TT ** c+ ** l ++ c ** (TT ++ TT),,
              2%Z ** TT ** c+ ** l ++ c ** (TT ++ TT)];
    r <- Phi (s -- c ** TT) * (x ^ c)^-1
   ]
   (kreq_mem {{r,s}}) epsilon.
  Proof.
   Open Scope Z_scope.
   Opaque sum_dom deno.

   intros k f1 f2 Hf m1 m2 [Heq [ [Hx Hw] Hc] ].
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   rewrite Uabs_diff_sym.
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   simpl; unfold O.eval_op; simpl.   
   pose l_pos; pose T_pos.  
   replace 
    (-2 * _T * Z_of_nat (cplus k) * _l) with
    (-(2 * _T * Z_of_nat (cplus k) * _l)) by ring.
   unfold Z_support; rewrite 2 Zle_imp_le_bool; 
    [ | ring_simplify; auto with zarith | ring_simplify; auto with zarith].     
   rewrite <-(Heq _ c); trivial.
   set (A:=2 * _T * Z_of_nat (cplus k) * _l).
   set (c':=m1 c).
   set (w:=m1 w).
   ring_simplify (c' * (_T + _T)).
   replace (A + 1 - - A) with (2 * A + 1) by ring.
   rewrite 2 (sum_dom_finite 0%Z).
   repeat rewrite seqZ_length.
   match goal with
    |- context [Zabs_nat ?x] => ring_simplify x
   end.
   set (y:=[1/]1+Peano.pred (Zabs_nat (2 * A + 1))).
  
   rewrite Uabs_diff_morphism with
    (y:=finite_sum
     (fun a =>
      Umult y 
      (f2 (m2{!s <-- a!}
             {!r <-- H.mul (H.powZ (g k) (a-c'*_T)) (H.inv(H.powZ (m2 x) c'))!})))
     (seqZ (-A + 2 * c' * _T) (Zabs_nat (2 * A + 1))))
    (y0:=finite_sum
     (fun a => Umult y 
      (f1 (m1{!t <-- a!}{!r <-- H.powZ (g k) a!}{!s <-- a + c' * (w + _T)!})))
     (seqZ (-A) (Zabs_nat (2 * A + 1)))).
   replace 
    (-A + 2 * c' * _T) with 
    (-A + c' * (_T - w) + c' * (w + _T)) by ring.  
   rewrite seqZ_Zplus, finite_sum_map.
   rewrite (@seqZ_app' (Zabs_nat (c' * (_T - w))) _ (-A)).
   rewrite (@seqZ_app' (Zabs_nat (2 * A + 1 - c' * (_T - w)))).
   rewrite 2 finite_sum_app.
   repeat rewrite inj_Zabs_nat, Zabs_eq.
   apply Uabs_diff_le_intro.

   rewrite Uplus_assoc, Uplus_sym; apply Uplus_le_compat.

   (* First *)
   rewrite (@finite_sum_le_const _ _ _ y); [ | trivial].
   rewrite seqZ_length, <-Zabs_nat_Zminus.
   replace (2 * A + 1 - (2 * A + 1 - c' * (_T - w))) with (c' * (_T - w)) by ring.

   transitivity (epsilon k); [ | auto].
   rewrite <-epsilon_bound with (c:=c') (w:=w); trivial.
   apply Nmult_Unth_le; rewrite <-(S_pred _ O).
   apply mult_le_compat.
   apply Zabs_nat_le; unfold c', w; split; auto with zarith.
   
   rewrite <-Zabs_nat_Zsucc.
   apply Zabs_nat_le; split; auto with zarith.  
   unfold A; ring_simplify; apply Zle_refl.

   auto with zarith.

   change O with (Zabs_nat 0); apply Zabs_nat_lt; split;unfold A; auto with zarith.
   psatz Z.

   unfold c'; rewrite <-Zabs_nat_Z_of_nat; apply Zabs_nat_le; trivial.

   split; unfold A, c', w; psatz Z.

   (** Second *)
   rewrite Zabs_nat_Zminus.
   apply finite_sum_le; intros; Usimpl.
   apply Hf; simpl; unfold O.eval_op; simpl; mem_upd_simpl; intros t v Hin.
   assert (Vset.mem v {{r,s}}) by trivial.
   Vset_mem_inversion H0; clear Hin; subst; mem_upd_simpl.
   rewrite <-(Heq _ Protocol.x), Hx; trivial.
   rewrite HP.powZ_powZ, <-HP.powZ_minus, HP.mul_powZ_plus.
   apply f_equal; unfold w; ring.
   ring_simplify; trivial.

   split; unfold A, c', w; psatz Z.

  
   (** The other inequality *)  
   rewrite (Uplus_sym _ (finite_sum (fun v => y * f2 _) _))%U.
   rewrite Uplus_assoc; apply Uplus_le_compat.

   (* First *)
   rewrite (@finite_sum_le_const _ _ _ y); [ | trivial].
   rewrite seqZ_length.

   transitivity (epsilon k); [ | auto].
   rewrite <-epsilon_bound with (c:=c') (w:=w); trivial.
   apply Nmult_Unth_le; rewrite <-(S_pred _ O).
   apply mult_le_compat.
   apply Zabs_nat_le; unfold c', w; psatz Z.

   unfold A.
   rewrite <-Zabs_nat_Zsucc.
   apply Zabs_nat_le.
   split; auto with zarith.
   ring_simplify; apply Zle_refl.

   psatz Z.

   change O with (Zabs_nat 0).
   apply Zabs_nat_lt; split; unfold A; [auto with zarith | psatz Z].

   rewrite <-Zabs_nat_Z_of_nat; apply Zabs_nat_le; auto with zarith.

   (* Second *)
   rewrite Zabs_nat_Zminus.
   apply finite_sum_le; intros; Usimpl.
   apply Hf; simpl; unfold O.eval_op; simpl; mem_upd_simpl; intros t v Hin.
   assert (Vset.mem v {{r,s}}) by trivial.
   Vset_mem_inversion H0; clear Hin; subst; mem_upd_simpl.
   rewrite <-(Heq _ Protocol.x), Hx; trivial.
   rewrite HP.powZ_powZ, <-HP.powZ_minus, HP.mul_powZ_plus.
   apply f_equal; unfold w; ring.
   ring_simplify; trivial.

   unfold A, w, c'; psatz Z.
   
   unfold A, w, c'; psatz Z.

   unfold A, w, c'; psatz Z.

   apply Zabs_nat_le; unfold A, w, c'; psatz Z.

   apply Zabs_nat_le; unfold A, w, c'; psatz Z.

   unfold A, w, c'; psatz Z.

   (***)
   apply finite_sum_eq; intros; Usimpl.
   unfold c'; rewrite (Heq _ c); trivial.
   rewrite (@deno_assign_elim k).
   simpl; unfold O.eval_op; simpl; mem_upd_simpl.

   (***)
   apply finite_sum_eq; intros; Usimpl.
   rewrite (@deno_cons_elim k), Mlet_simpl, deno_assign_elim, deno_assign_elim.
   simpl; unfold O.eval_op; simpl; mem_upd_simpl.
  Qed.

  Close Scope Z_scope.

  Lemma SHVZK :
   prg_SD (req_mem_rel {{x,w,c}} 
    (R1 /-\ (fun k m1 _ => 0 <= m1 c <= Z_of_nat (cplus k))))%Z 
   E protocol' 
   E simulation
   (kreq_mem {{r,s}}) 
   epsilon.
  Proof.
   intros k f1 f2 Hf m1 m2 H.
   rewrite Uabs_diff_morphism with
    (y:=mu ([[ 
     [
      t <$- [(-2)%Z ** TT ** c+ ** l,, 2%Z ** TT ** c+ ** l];
      r <- Phi t;
      s <- t ++ c ** (w ++ TT)
     ] ]] E m1) f1)
    (y0:=mu ([[
     [
      s <$- [(-2)%Z ** TT ** c+ ** l ++ c ** (TT ++ TT),,
                2%Z ** TT ** c+ ** l ++ c ** (TT ++ TT)];
      r <- Phi (s -- c ** TT) * (x ^ c)^-1
     ] ]] E m2) f2).
   apply SHVZK_aux; trivial.
   
   apply equiv_deno with (kreq_mem {{x,w,c}}) (kreq_mem {{r,s}}).
   inline iEE P1; sinline iEE P2; eqobs_in.
   intros; transitivity (f2 m3); [ | symmetry]; auto.
   trivial.

   apply equiv_deno with (kreq_mem {{x,w,c}}) (kreq_mem {{r,s}}).
   sinline_l iEE Protocol.S; alloc_r s s'; ep iEE; swap iEE; eqobs_in.
   intros; transitivity (f1 m3); [symmetry | ]; auto.
   trivial.
  Qed.

  Definition pi : PPT_info E := 
   PPT_add_info (PPT_add_info (PPT_empty_info E) KE) Protocol.S.

  Lemma S_PPT : PPT_proc E Protocol.S.
  Proof.
   PPT_proc_tac pi.
  Qed.


  Section SOUNDNESS.  

   Close Scope positive_scope.
   Open Scope Z_scope.

   Variable k : nat.
   Variable m : Mem.t k.
 
   Hypothesis accepting_1 : E.eval_expr (V x r c1 s1) m = true.
   Hypothesis accepting_2 : E.eval_expr (V x r c2 s2) m = true.
   Hypothesis c_range_1 : 0 <= m c1 < Z_of_nat (cplus k).
   Hypothesis c_range_2 : 0 <= m c2 < Z_of_nat (cplus k).
   
   Hypothesis H_neq : m c1 < m c2.
 
   Hypothesis H_delta_c :
    ((m c2 - m c1) | (m s2 - m s1 - (m c2 - m c1) * _T)).

   Variables d d' : Z.

   Let n := Z_of_nat (length (H.elems k)).

   (* d = Prod_{x | prime x /\ x | order /\ x <= cplus} x *)

   Hypothesis Hd : n = d * d'.
   
   Hypothesis d_spec : forall k x,
    prime x -> (x | d') -> Z_of_nat (cplus k) < x.

   Definition RR k (x y:T.interp k xT) (u:T.interp k wT) :=
    H.mul y x = H.powZ (g k) u /\
    H.powZ y d = H.e k /\
    -4 * _T * Z_of_nat (cplus k) * _l - 2 * _T * (Z_of_nat (cplus k) - 1) - _T <= u /\
    u <= 4 * _T * Z_of_nat (cplus k) * _l + 2 * _T * (Z_of_nat (cplus k) - 1) - _T.

   Lemma RR_dec : forall k (x y:T.interp k xT) u, 
    sumbool (RR x y u) (~RR x y u).
   Proof.
    clear; unfold RR; intros.  
    generalize (H.eqb_spec (H.mul y x) (H.powZ (g k) u)).
    case (H.eqb (H.mul y x) (H.powZ (g k) u)); [ | intuition].
    generalize (H.eqb_spec (H.powZ y d) (H.e k)).  
    case (H.eqb (H.powZ y d) (H.e k)); [ | intuition].
    match goal with 
     |- context [ ?x <= ?y <= ?z ] => 
     case (Z_le_dec x y); case (Z_le_dec y z); intuition
    end.
   Qed.


   Let u := (m s2 - m s1) / (m c2 - m c1) - _T.
   Let y := H.mul (H.powZ (g k) u) (H.inv (m x)).
  
   Lemma soundness_aux : RR (m x) y u.
   Proof.
    generalize accepting_1, accepting_2.
    simpl; unfold O.eval_op; simpl; intros H1 H2.
    apply andb_prop in H1; destruct H1 as [H Hge1].
    apply andb_prop in H; destruct H as [Heq1 Hle1].
    apply andb_prop in H2; destruct H2 as [H Hge2].
    apply andb_prop in H; destruct H as [Heq2 Hle2].
    rewrite <-Zle_is_le_bool in Hle1, Hle2, Hge1, Hge2 |- .
    apply H_eqb_correct in Heq1.
    apply H_eqb_correct in Heq2.

    assert (H.mul y (m x) = H.powZ (g k) u).
    unfold y, u; rewrite <-H.mul_assoc, H.mul_inv_l, HP.mul_e_r; trivial.
  
    unfold RR; intros; repeat split.
   
    trivial.

    (**)
    assert (H.powZ y (m c2 - m c1) = H.e k).
    apply HP.cancellation with (H.powZ (m x) (m c2 - m c1)).
    rewrite <-HP.powZ_mul_distr, HP.mul_e_r.
    unfold Zminus at 2; rewrite <-HP.mul_powZ_plus.
    rewrite <-HP.mul_e_r, <-(HP.mul_inv_r (m r)).
    rewrite H.mul_assoc, (H.mul_comm _ (m r)), H.mul_assoc.
    rewrite <-Heq2, <-H.mul_assoc, HP.powZ_minus.
    rewrite <-HP.inv_mul, (H.mul_comm _ (m r)), <-Heq1.
    rewrite <-HP.powZ_minus, HP.mul_powZ_plus.
    replace (m s2 - m c2 * _T + - (m s1 - m c1 * _T)) with (u * (m c2 - m c1)).
    rewrite <-HP.powZ_powZ, H.mul_comm, H; trivial.

    replace 
     (m s2 - m c2 * _T + - (m s1 - m c1 * _T)) with
     ((m s2 - m s1) - (m c2 - m c1) * _T) by ring.
    set (A:=m s2 - m s1) in *. 
    set (B:=m c2 - m c1) in *.    
    unfold u.
    rewrite Zdivide_Zdiv_eq with (a:=B); [ | unfold B; psatz Z | trivial].
    rewrite Zmult_comm.
    apply f_equal.   
    unfold Zminus; rewrite <-Z_div_plus; [ | unfold B; psatz Z].
    replace (A + -_T * B) with (A + -(B * _T)) by ring; trivial.

    (* y ^ d = e *)
    assert (m c2 - m c1 <= Z_of_nat (cplus k)) by psatz Z.
    assert (0 < m c2 - m c1) by psatz Z.
    set (delta_c:=m c2 - m c1) in *.
    clear -H0 n H1 H2 d_spec Hd.
    assert (Zdivide (Zgcd delta_c n) d).

    assert (Zgcd delta_c n | d * d') by (rewrite <-Hd; apply Zgcd_div_r).
    rewrite Zmult_comm in H; apply Gauss in H; trivial.
    unfold rel_prime; apply Zis_gcd_intro; auto with zarith; intros.
    
    case (Z_lt_dec 1 (Zabs x)); intro.
    case (prime_dec (Zabs x)); intro Hx.

    generalize (@d_spec k (Zabs x) Hx (Zdivide_Zabs_inv_l _ _ H4)); intro.
    assert (Zabs x <= delta_c).
    apply Zdivide_le; auto with zarith.
    apply Zdivide_Zabs_inv_l in H3.
    apply Zdivide_trans with (1:=H3), Zgcd_div_l.
    exfalso; auto with zarith.

    apply not_prime_divide_prime in Hx; trivial.
    destruct Hx as [p [? [? ?] ] ].
    assert (p | d').
    apply Zdivide_trans with (1:=H6).
    apply Zdivide_Zabs_inv_l in H4; trivial.
    assert (p | delta_c).
    apply Zdivide_trans with (1:=H6); trivial.
    apply Zdivide_trans with (2:=Zgcd_div_l _ n); trivial.
    assert (p <= delta_c).
    apply Zdivide_le; auto with zarith.
    generalize (@d_spec k p H5 H8); intro.
    assert (p <= delta_c).
    apply Zdivide_le; auto with zarith.
    apply Zdivide_trans with (1:=H6).
    apply Zdivide_Zabs_inv_l in H3.
    apply Zdivide_trans with (1:=H3), Zgcd_div_l.
    exfalso; auto with zarith.

    apply Zdivide_Zabs_inv_l; trivial.
    generalize (@d_spec k p H5 H8); intro.
    assert (p <= delta_c).
    apply Zdivide_le; auto with zarith.
    exfalso; auto with zarith.
    
    assert (Zabs x <= 1) by auto with zarith.
    case (Z_eq_dec (Zabs x) 1); intro.
    apply Zdivide_Zabs_l; rewrite e; auto with zarith.
    assert (Zabs x = 0).
    generalize (Zabs_pos x); intro.
    auto with zarith.
    apply Zabs_0_inv in H6.
    destruct H4; rewrite H6, Zmult_0_r in H4.
    assert (n = 0).
    rewrite Hd, H4, Zmult_0_r; trivial.
    
    unfold n in H7.
    elim (@HP.elems_not_nil k).
    destruct (H.elems k); [trivial | discriminate].
       
    apply HP.powZ_gcd in H0.
    destruct H; rewrite H, Zmult_comm, <-HP.powZ_powZ.
    unfold n; rewrite H0, HP.powZ_e; trivial.

    (**)
    unfold u.
    apply Zle_plus_swap; ring_simplify.
    apply Zdiv_le_lower_bound; [auto with zarith | ].    
    psatz Z.

    (**)
    unfold u.
    apply Zle_plus_swap; ring_simplify.
    apply Zdiv_le_upper_bound; [auto with zarith | ].
    psatz Z.
   Qed.

   Close Scope Z_scope.

   Lemma soundness : 
    Pr E ((yu <c- KE with {x, r, c1, c2, s1, s2}) :: nil) m
    (fun m => if RR_dec (m x) (fst(m yu)) (snd(m yu)) then true else false) == 1. 
   Proof.
    transitivity (Pr E  
     ( (yu <- (Phi ((s2 -- s1 /Z c2 -- c1) -- TT) * x ^-1 | 
                    (s2 -- s1 /Z c2 -- c1) -- TT)) :: nil) m 
     (fun m => if RR_dec (m x) (fst (m yu)) (snd (m yu)) then true else false)).   
    apply EqObs_deno with {{x, r, c1, c2, s1, s2}} {{x, yu}}.
    sinline_l iEE KE; eqobs_in.
    
    intros; unfold charfun, restr.
    rewrite (H _ x), (H _ yu); trivial.
    trivial.

    unfold Pr; rewrite deno_assign_elim.
    unfold charfun, restr, fone.
    simpl E.eval_expr; unfold O.eval_op; simpl.
    mem_upd_simpl.
    match goal with
     |- context [RR_dec ?A ?B ?C] => case (RR_dec A B C) 
    end.
    trivial.

    intro HR; elim HR; clear HR.
    apply soundness_aux.
   Qed.

   Lemma KE_PPT : PPT_proc E KE.
   Proof.
    PPT_proc_tac pi.
   Qed.

  End SOUNDNESS.

 End Protocol.

End SigmaGSP.
