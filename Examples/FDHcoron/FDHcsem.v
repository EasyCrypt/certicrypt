(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * FDHcsem.v : Semantics with a cyclic group, a trapdoor permutation and 
    its inverse *)
Set Implicit Arguments.

Unset Strict Implicit.

Require Export PPT.
Require Export BuildTac.

Open Scope nat_scope.


Module Type CYCLIC_GROUP.

 Parameter t : nat -> Type.

 (** Generator *)
 Parameter g : forall k, t k.
 
 (** Identity element *)
 Parameter e : forall k, t k.

 (** Equality is decidable *)
 Parameter eqb : forall k, t k -> t k -> bool.
 Parameter eqb_spec : forall k (x y:t k), if eqb x y then x = y else x <> y.

 (** Operations: inverse, product, logarithm, power *)
 Parameter inv : forall k, t k -> t k.
 Parameter mul : forall k, t k -> t k -> t k.
 Parameter log : forall k, t k -> nat.

 Fixpoint pow (k:nat) (x:t k) (n:nat) : t k :=
  match n with
  | O => e k
  | S n => mul x (pow x n)
  end.

 (** Specification *) 
 Parameter mul_assoc : forall k (x y z:t k), mul x (mul y z) = mul (mul x y) z.
 Parameter mul_e_l : forall k (x:t k), mul (e k) x = x.
 Parameter mul_inv_l : forall k (x:t k), mul (inv x) x = e k.

 Parameter cyclic_1 : forall k, pow (g k) k = e k.
 Parameter cyclic_2 : forall k n, pow (g k) n = e k -> exists i, n = k * i.

 Parameter log_lt : forall k (x:t k), log x < k.
 Parameter log_spec : forall k (x:t k), x = pow (g k) (log x).

 (* Cost *)
 Parameter cost_mul : forall k (x y:t k), nat.
 Parameter cost_pow : forall k (x:t k) (n:nat), nat.
 Parameter cost_inv : forall k (x:t k), nat.

 Parameter cost_mul_poly : polynomial.
 Parameter cost_pow_poly : polynomial.
 Parameter cost_inv_poly : polynomial.

 Parameter cost_mul_poly_spec : forall k (x y:t k),
  @cost_mul k x y <= peval cost_mul_poly (pred (size_nat k)).

 Parameter cost_pow_poly_spec : forall k (x:t k) (n:nat),
  @cost_pow k x n <= peval cost_pow_poly (pred (size_nat k)).

 Parameter cost_inv_poly_spec : forall k (x:t k),
  @cost_inv k x <= peval cost_inv_poly (pred (size_nat k)).

End CYCLIC_GROUP.


Module CG_Properties (CG:CYCLIC_GROUP).

 Import CG.

 Lemma mul_pow_plus : forall k (x:t k) n m, 
  mul (pow x n) (pow x m) = pow x (n + m).
 Proof.
  induction n; intros; simpl.
  simpl; apply mul_e_l.
  simpl; rewrite <- mul_assoc, IHn; trivial.
 Qed.

 Lemma mul_comm : forall k (x y:t k), mul x y = mul y x.
 Proof.
  intros k x y.
  rewrite (log_spec x), (log_spec y).
  rewrite mul_pow_plus, plus_comm, <- mul_pow_plus; trivial.
 Qed.

 Lemma mul_e_r : forall k x, mul x (e k) = x.
 Proof.
  intros; rewrite mul_comm, mul_e_l; trivial.
 Qed.

 Lemma mul_inv_r : forall k x, mul x (inv x) = e k.
 Proof.
  intros; rewrite mul_comm, mul_inv_l; trivial.
 Qed.

 Lemma pow_e : forall k n, pow (e k) n = e k.
 Proof.
  induction n; intros.
  trivial.
  simpl; rewrite IHn, mul_e_r; trivial.
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
  induction n; intros.
  simpl; simpl; rewrite pow_e; trivial.
  simpl; rewrite <- mul_pow_plus, <- IHn.
  apply pow_mul_distr.
 Qed.

 Lemma pow_inj : forall k a b,
  a < k ->
  b < k ->
  pow (g k) a = pow (g k) b ->
  a = b.
 Proof.
  induction a; intros.
  simpl in H1; symmetry in H1; apply cyclic_2 in H1.
  destruct H1 as [i H1]; subst.
  destruct i; [ trivial |].
  rewrite mult_comm in H0; simpl in H0.
  rewrite <- plus_0_r in H0.
  apply plus_lt_reg_l in H0.
  elimtype False; apply (lt_n_O _ H0).
  
  destruct b.
  simpl (pow (g k) 0) in H1.
  apply cyclic_2 in H1.
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
  simpl in H1.
  rewrite <- mul_e_r with (x:=pow (g k) a).
  rewrite <- mul_e_r with (x:=pow (g k) b).
  rewrite <- mul_inv_r with (x:=g k).
  repeat rewrite mul_assoc.
  rewrite mul_comm with (x:=pow (g k) a).
  rewrite mul_comm with (x:=pow (g k) b).
  rewrite H1; trivial.
 Qed.

End CG_Properties.


Declare Module CG : CYCLIC_GROUP.

Module Type TRAPDOOR_PERM.

 (** * Trapdoor permutation and its inverse *)
 Parameter ap_f    : forall k (x:CG.t (2^k)), CG.t (2^k).
 Parameter ap_finv : forall k (x:CG.t (2^k)), CG.t (2^k).

 Parameter f_spec : forall k (x:CG.t (2^k)), ap_finv (ap_f x) = x.
 Parameter finv_spec : forall k (x:CG.t (2^k)), ap_f (ap_finv x) = x.

 Parameter f_homo : forall k (x y:CG.t (2^k)), 
  ap_f (CG.mul x y) = CG.mul (ap_f x) (ap_f y).

 Parameter cost_f : polynomial.
 Parameter cost_finv : nat -> nat.

 (* Maximum number of queries made to the signing oracle *)
 Parameter qS_poly : polynomial.

 (* Maximum number of queries made to the hash oracle *)
 Parameter qH_poly : polynomial.

 (* REMARK: qS <= qH *)

End TRAPDOOR_PERM. 


Declare Module TP : TRAPDOOR_PERM.

Module CGP := CG_Properties CG.

Inductive ut_ : Type := group.

(** * User-defined type module *)
Module Ut <: UTYPE.

 Definition t := ut_. 
 Definition eqb ( _ _ :t) := true.

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  simpl; destruct x; destruct y; trivial.
 Qed.

 Definition eq_dec (x y:t) : {x = y} + {True} :=
  match x as x0 return {x0 = y} + {True} with
  | group =>
    match y as y0 return {group = y0} + {True} with 
    | group => left _ (refl_equal group) 
    end
  end.

 Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
 Proof.
  destruct x; destruct y; simpl; intros; discriminate.
 Qed.
 
 Definition interp k (_:t) := CG.t (2^k).

 Definition size k (_:t) (_:CG.t (2^k)) := S k.
 
 Definition default k (t0:t) : interp k t0 := CG.e (2^k).

 Definition default_poly (t0:t) := pplus (pcst 1) pvar.

 Lemma size_positive : forall k (t0:t) x, 0 < @size k t0 x.
 Proof.
  intros k t0 x; unfold size; auto with arith.
 Qed.

 Lemma default_poly_spec : forall k (t0:t), 
  @size k t0 (default k t0) <= peval (default_poly t0) k.
 Proof.
  intros k t0.
  unfold default, default_poly, size.
  rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
 Qed.
 
 Definition i_eqb k t (g1 g2: interp k t) := CG.eqb g1 g2.

 Lemma i_eqb_spec : forall k t (x y:interp k t), 
  if i_eqb x y then x = y else x <> y.
 Proof.
  intros; refine (CG.eqb_spec _ _).
 Qed.

End Ut.


Fixpoint lfalse (n:nat) :=
 match n with
 | O => nil
 | S n => false :: lfalse n
 end.

Definition bool_support (k:nat) := true :: lfalse (peval TP.qS_poly k).

Definition group_support (k:nat) := 
 map (fun i => CG.pow (CG.g (2^k)) i) (seq 0 (2^k)).

Lemma group_support_notnil : forall k, group_support k <> nil.
Proof.
 induction k; simpl; intros.
 discriminate.
 unfold group_support; intro Heq.
 assert (In 0 (seq 0 (2 ^ (S k)))).
 apply le_In_seq; split; [ trivial | ].
 rewrite plus_0_r; apply pow_lt_0; auto.
 apply in_map with (f:=fun i : nat => CG.pow (CG.g (2 ^ S k)) i) in H.
 rewrite Heq in H; inversion H.
Qed.

Lemma group_support_full : forall k (x:CG.t (2^k)), In x (group_support k).
Proof.
 intros; rewrite (CG.log_spec x).
 assert (Hlt:=CG.log_lt x).
 unfold group_support.
 rewrite in_map_iff.
 exists (CG.log x); split.
 trivial.
 apply le_In_seq; auto with arith.
Qed.

Lemma group_support_NoDup : forall k n, 
 n <= k ->
 NoDup (map (fun i => CG.pow (CG.g k) i) (seq 0 n)).
Proof.
 intros k n Hlt; induction n.
 constructor.

 rewrite seq_S; simpl.
 rewrite map_app; apply NoDup_app.
 auto with arith.
 constructor.
 apply in_nil.
 constructor.

 intros x H1 H2.
 rewrite in_map_iff in H1.
 rewrite in_map_iff in H2.
 destruct H1 as [a [Ha1 Ha2] ].
 destruct H2 as [b [Hb1 Hb2] ].
 inversion Ha2; [ | trivial]; clear Ha2 IHn; subst.
 apply In_seq_le in Hb2; rewrite plus_0_r in Hb2.

 assert (b = a).
 apply CGP.pow_inj with k; [ omega | omega | trivial].
 omega.
Qed.

Module T := MakeType Ut.

Inductive usupport_ 
 (Ttype:Type) (Tuser:ut_ -> Ttype) (Tbool:Ttype) : Ttype -> Type :=
| Ugroup : usupport_ Tuser Tbool (Tuser group)
| Ubool_p : usupport_ Tuser Tbool Tbool.

Module Us <: USUPPORT Ut T.

 Definition usupport : T.type -> Type := usupport_ T.User T.Bool.

 Definition eval k t (s:usupport t) : list (T.interp k t) :=
  match s in usupport_ _ _ t0 return list (T.interp k t0) with
  | Ugroup => group_support k
  | Ubool_p => bool_support k
  end.

 Definition ceval k t (s:usupport t) : list (T.interp k t) * nat :=
  match s in usupport_ _ _ t0 return list (T.interp k t0) * nat with
  | Ugroup => (group_support k, S O)
  | Ubool_p => (bool_support k, S O)
  end.
 
 Lemma eval_usupport_nil : forall k t (s:usupport t), eval k s <> nil.
 Proof.
  intros; case s.
  apply group_support_notnil.
  discriminate.
 Qed.

 Lemma ceval_spec : forall k t (s:usupport t), eval k s = fst (ceval k s).
 Proof.
  intros k t s; case s; trivial.
 Qed.

 Definition eqb (t1 t2:T.type) (s1:usupport t1) (s2:usupport t2) : bool :=
  match s1, s2 with
  | Ugroup, Ugroup => true
  | Ubool_p, Ubool_p => true
  | _, _ => false
  end.

 Lemma eqb_spec_dep :  forall t1 (e1 : usupport t1) t2 (e2:usupport t2),
  if eqb e1 e2 then eq_dep T.type usupport t1 e1 t2 e2
  else ~eq_dep T.type usupport t1 e1 t2 e2.
 Proof.
  intros.
  case e1; case e2; simpl; try constructor; intro H; inversion H.
 Qed.

 Lemma eqb_spec : forall t (e1 e2:usupport t),
  if eqb e1 e2 then e1 = e2 else e1 <> e2.
 Proof.
  intros t e1 e2.
  generalize (eqb_spec_dep e1 e2).
  case (eqb e1 e2); intro H.
  apply T.eq_dep_eq; trivial.
  intro Heq; apply H; rewrite Heq; constructor.
 Qed.

End Us.


Module Entries.

 Export TP.

 Lemma f_inj : forall k (x y:CG.t (2^k)), ap_f x = ap_f y -> x = y.
 Proof.
  intros; rewrite <- (f_spec x), <- (f_spec y), H; trivial.
 Qed.

 Lemma f_inj_Veqb : forall k (x y:CG.t (2^k)), 
  CG.eqb (ap_f x) (ap_f y) = CG.eqb x y.
 Proof.
  intros.
  generalize (CG.eqb_spec x y); case (CG.eqb x y); intro H.
  generalize (CG.eqb_spec (ap_f x) (ap_f y)).
  case (CG.eqb (ap_f x) (ap_f y)); trivial.
  rewrite H; intro H0; elim H0; trivial.

  generalize (CG.eqb_spec (ap_f x) (ap_f y)).
  case (CG.eqb (ap_f x) (ap_f y)); trivial.
  intro H0; apply f_inj in H0; elim H; trivial.
 Qed.


 Inductive uop_ : Type :=
 | OGorder
 | OGen
 | OGmul
 | OGpow
 | OGinv
 | Of
 | Ofinv
 | OqS
 | OqH.

 Module Uop <: UOP Ut T.

  Definition t := uop_.
  
  Definition eqb (o1 o2 : t) : bool :=
   match o1, o2 with
   | OGorder, OGorder
   | OGen, OGen
   | OGmul, OGmul 
   | OGpow, OGpow 
   | OGinv, OGinv 
   | Of, Of 
   | Ofinv, Ofinv
   | OqS, OqS 
   | OqH, OqH => true
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
   | OGmul => T.User group :: T.User group :: nil
   | OGpow => T.User group :: T.Nat :: nil
   | OGinv => T.User group :: nil
   | Of => T.User group :: nil
   | Ofinv => T.User group :: nil
   | OqS => nil
   | OqH => nil
   end.
  
  Definition tres (op: t) : T.type :=
   match op with
   | OGorder => T.Nat
   | OGen => T.User group
   | OGmul => T.User group
   | OGpow => T.User group
   | OGinv => T.User group
   | Of => T.User group
   | Ofinv => T.User group
   | OqS => T.Nat
   | OqH => T.Nat
   end.
   
  Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
   match op as op0 return T.type_op k (targs op0) (tres op0) with
   | OGorder => 2^k
   | OGen => @CG.g (2^k)
   | OGmul => @CG.mul (2^k)
   | OGpow => @CG.pow (2^k)
   | OGinv => @CG.inv (2^k)
   | Of => @ap_f k
   | Ofinv => @ap_finv k
   | OqS => peval qS_poly k
   | OqH => peval qH_poly k
   end.

  Implicit Arguments interp_op [k].

  Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
   match op as op0 return T.ctype_op k (targs op0) (tres op0) with
   | OGorder => (2^k, 1)
   | OGen => (@CG.g (2^k), 1)
   | OGmul => fun x y => (@CG.mul (2^k) x y, CG.cost_mul x y)
   | OGpow => fun x n => (@CG.pow (2^k) x n, CG.cost_pow x n)
   | OGinv => fun x => (@CG.inv (2^k) x, CG.cost_inv x)
   | Of => fun x => (@ap_f k x, peval cost_f k)
   | Ofinv => fun x => (@ap_finv k x, cost_finv k)
   | OqS => (peval qS_poly k, 1)
   | OqH => (peval qH_poly k, 1)
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


 (** Semantics with optimizations *)
 Module SemO <: SEM_OPT.

  Module Sem := MakeSem.Make Ut T Uop Us.
  Export Sem.

  (* The trapdoor permutation and its inverse *)
  Notation f := (E.Eop (O.Ouser Of)).
  Notation finv := (E.Eop (O.Ouser Ofinv)).
  
  (* Group operation *)  
  Notation "x '|x|' y" := (E.Eop (O.Ouser OGmul) {x,y}) (at level 40).

  (* Group inverse *)  
  Notation "x '^-1'" := (E.Eop (O.Ouser OGinv) {x}) (at level 40).

  (* Maximum number of queries made to the hash oracle *)
  Notation "'qH'" := (E.Eop (O.Ouser OqH) (dnil E.expr)).

  (* Maximum number of queries made to the signing oracle *)
  Notation "'qS'" := (E.Eop (O.Ouser OqS) (dnil E.expr)).

  (* Supports *)
  Notation "'{0,1}_p'" := (E.Duser (Ubool_p T.User T.Bool)).
  Notation "'G_k'" := (E.Duser (Ugroup T.User T.Bool)).

  (* Some infinite type (bitstrings in the literature) *)
  Notation Msg := T.Nat.

  (** Simplifies [f (finv x)] to [x] *)
  Definition simpl_op (op : Uop.t) : E.args (Uop.targs op) -> 
   E.expr (Uop.tres op) :=
   match op as op0 return E.args (Uop.targs op0) -> E.expr (Uop.tres op0) with
   | Of => fun args => 
    E.app_expr (T.User group) args 
    (fun (e:E.expr (T.User group)) =>
     match E.get_uop e with
     | Some (existT uop args) =>
       match uop as uop0 
       return E.args (Uop.targs uop0) -> E.expr (T.User group) with
       | Ofinv =>
         fun args => 
          E.app_expr (T.User group) args (fun e1:E.expr (T.User group) => e1)
       | _ => fun _ => f {e}
       end args
     | None => f {e}
     end)
   | op => fun args => E.Eop (O.Ouser op) args
   end.

  Implicit Arguments simpl_op [].

  Lemma simpl_op_spec : forall k op args (m:Mem.t k),
   E.eval_expr (simpl_op op args) m = E.eval_expr (E.Eop (O.Ouser op) args) m.
  Proof.
   destruct op; simpl; trivial. 
   intros args m.
   intros;T.dlist_inversion args; rewrite Heq; simpl.
   generalize (E.get_uop_spec x); destruct (E.get_uop x); trivial.
   destruct s as (uop, args0).
   intros H; generalize (H uop args0 (refl_equal _)); clear H; simpl; intros.
   destruct uop; trivial.
   rewrite (T.eq_dep_eq H); clear H.
   clear Heq;T.dlist_inversion args0; rewrite Heq; simpl.
   symmetry; exact (finv_spec (E.eval_expr x0 m)).
  Qed.

 End SemO.

 Module BP := BaseProp.Make SemO.Sem.

 Module Uppt.

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
    let (l,n) := E.ceval_support s m in
     (forall v, In v l -> T.size v <= peval (F p) k) /\
     n <= peval (G p) k.

  Definition utsize : UT.t -> nat := fun _ => 1.

  Definition utsize_default_poly : nat -> polynomial :=
   fun _ => pplus (pcst 1) pvar.

  Lemma utsize_default_poly_spec : forall r ut,
   utsize ut <= r -> 
   forall k, 
    UT.size (t:=ut) (UT.default k ut) <= peval (utsize_default_poly r) k.
  Proof.
   intros r ut _ k.
   case ut; simpl.
   unfold UT.size, utsize_default_poly. 
   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.  
  Qed.

  Definition uop_poly (o:Uop.t) : bool :=
   match o with
   | OGorder | OGen | OGmul | OGpow | OGinv | Of | OqS | OqH => true
   | _ => false
   end.

  Lemma uop_poly_spec : forall o (la:dlist E.expr (O.targs (O.Ouser o))),
   uop_poly o ->
   (forall t (e:E.expr t), @DIn _ E.expr _ e _ la -> 
    exists F, exists G, PPT_expr e F G) ->
   exists F, exists G, PPT_expr (E.Eop (O.Ouser o) la) F G.
  Proof.
   intros o la H Hla.
   destruct o.

   (* OGorder *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   exists (fun _ => pplus 1 pvar). 
   exists (fun _ => 1).
   simpl; split.
   rewrite pplus_spec, pcst_spec, pvar_spec; rewrite size_nat_pow_2; trivial.
   rewrite pcst_spec; trivial.

   (* OGen *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   exists (fun _ => pplus 1 pvar).
   exists (fun _ => 1). 
   simpl; split.
   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
   rewrite pcst_spec; trivial.

   (* OGmul *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [G1 H1] ].
   left; trivial.
   destruct (Hla _ x0) as [F2 [G2 H2] ].
   right; left; trivial.
   exists (fun _ => pplus 1 pvar).
   exists (fun p => pplus CG.cost_mul_poly (pplus (G1 p) (G2 p))).
   intros k m p Hm; simpl; split.

   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
   rewrite pplus_spec, pplus_spec.
   apply plus_le_compat.
   apply le_trans with (peval CG.cost_mul_poly (pred (size_nat (2^k)))).
   apply CG.cost_mul_poly_spec.
   rewrite size_nat_pow_2; trivial.

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
   rewrite plus_0_r; apply plus_le_compat; auto.  

   (* OGpow *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [G1 H1] ].
   left; trivial.
   destruct (Hla _ x0) as [F2 [G2 H2] ].
   right; left; trivial.
   exists (fun _ => pplus 1 pvar).
   exists (fun p => pplus CG.cost_pow_poly (pplus (G1 p) (G2 p))).
   intros k m p Hm; simpl; split.

   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
   rewrite pplus_spec, pplus_spec.
   apply plus_le_compat.
   apply le_trans with (peval CG.cost_pow_poly (pred (size_nat (2^k)))).
   apply CG.cost_pow_poly_spec.
   rewrite size_nat_pow_2; trivial.

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
   rewrite plus_0_r; apply plus_le_compat; auto.  

   (* OGinv *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [G1 H1] ].
   left; trivial.
   exists (fun _ => pplus 1 pvar).
   exists (fun p => pplus CG.cost_inv_poly (G1 p)).
   intros k m p Hm; simpl; split.

   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
   rewrite pplus_spec.
   apply plus_le_compat.
   apply le_trans with (peval CG.cost_inv_poly (pred (size_nat (2^k)))).
   apply CG.cost_inv_poly_spec.
   rewrite size_nat_pow_2; trivial.

   generalize (H1 k m p); clear H1.
   case_eq (E.ceval_expr x m); simpl.
   intros y n Heqy Hy.
   destruct Hy.
   intros; apply Hm; simpl.
   apply Vset.subset_correct with (fv_expr x); [ | trivial].
   apply VsetP.subset_refl.
   rewrite plus_0_r; trivial.

   (* Of *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [G1 H1] ].
   left; trivial.
   exists (fun _ => pplus 1 pvar).
   exists (fun p => pplus (cost_f) (G1 p)). 
   simpl; split.
   unfold T.size, UT.size; rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
   rewrite pplus_spec; apply plus_le_compat; trivial.
   simpl.
   generalize (H1 k m p); clear H1.
   case_eq (E.ceval_expr x m); simpl.
   intros i n Heqi Hi.
   destruct Hi.
   intros; apply H0; simpl.
   apply Vset.subset_correct with (fv_expr x); [ | trivial].
   unfold fv_expr; simpl; auto with set.
   rewrite plus_0_r; trivial.

   (* Ofinv *)
   discriminate.

   (* OqS *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   exists (fun _ => pplus 1 qS_poly).
   exists (fun _ => pcst 1). 
   simpl; split.
   rewrite pplus_spec, pcst_spec; case (peval qS_poly k).
   trivial.
   intro n; apply le_trans with (S n); [apply size_nat_le | ]; auto with arith.
   rewrite pcst_spec; trivial.

   (* OqS *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   exists (fun _ => pplus 1 qH_poly).
   exists (fun _ => pcst 1). 
   simpl; split.
   rewrite pplus_spec, pcst_spec; case (peval qH_poly k).
   trivial.
   intro n; apply le_trans with (S n); [apply size_nat_le | ]; auto with arith.
   rewrite pcst_spec; trivial.
  Qed.

  Definition usupport_poly t (us:US.usupport t) : bool := true.

  Lemma usupport_poly_spec : forall t (us:US.usupport t),
   usupport_poly us ->
   exists F, exists G, PPT_support (E.Duser us) F G.
  Proof.
   intros t us; case us; intros _.

   exists (fun _ => pplus (pcst 1) pvar).
   exists (fun _ => pcst 1).
   intros k m p Hm.
   rewrite pplus_spec, pvar_spec, pcst_spec.
   rewrite (surjective_pairing 
    (E.ceval_support (E.Duser (Ugroup T.User T.Bool)) m)).
   split; trivial.

   exists (fun _ => pcst 1).
   exists (fun _ => pcst 1).
   intros k m p Hm.
   rewrite pcst_spec.
   split; trivial.
  Qed.

 End Uppt.

End Entries.

Module Tactics := BuildTac.Make Entries.
Export Tactics.
