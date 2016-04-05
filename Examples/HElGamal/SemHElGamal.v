(** * SemHElGamal.v : Language extension with cyclic group and bitstring types *)
 
Set Implicit Arguments.

Require Import PPT.
Require Export BuildTac.
Require Export Group.
Require Export Bitstrings.

Unset Strict Implicit.


Inductive Ut : Type := 
| Bitstring
| Group.

(** * User-defined type module *)
Module UT <: UTYPE.

 Definition t := Ut. 
 
 Definition eqb (x y:t) := 
  match x, y with
  | Bitstring, Bitstring => true
  | Group, Group => true
  | _, _ => false
  end.

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  intros x y; case x; case y; simpl; trivial; discriminate.
 Qed.

 Definition eq_dec (x y:t) : {x = y} + {True} :=
  match x as x0 return {x0 = y} + {True} with
  | Bitstring => 
    match y as y0 return {Bitstring = y0} + {True} with 
    | Bitstring => left _ (refl_equal _) 
    | _ => right _ I
    end
  | Group => 
    match y as y0 return {Group = y0} + {True} with 
    | Group => left _ (refl_equal _) 
    | _ => right _ I
    end
  end.

 Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
 Proof.
  intros x y; case x; case y; simpl; intros; discriminate.
 Qed.

 Definition interp k (t0:t) : Type := 
  match t0 with
  | Bitstring => Bvector k
  | Group => CGK.t (2^k)
  end.

 Definition size k (t0:t) (_:interp k t0) := S k.

 Definition default k (t0:t) : interp k t0 := 
  match t0 with
  | Bitstring => Bvect_false k
  | Group => CGK.g0 (2^k)
  end.

 Definition default_poly (t0:t) := pplus (pcst 1) pvar.

 Lemma size_positive : forall k t0 (x:interp k t0), (0 < size x)%nat.
 Proof.
  intros k t0 x.
  unfold size; auto with arith.
 Qed.

 Lemma default_poly_spec : forall k (t0:t),
  (size (default k t0) <= peval (default_poly t0) k)%nat.
 Proof.
  intros k t0.
  unfold size, default, default_poly.
  rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
 Qed.

 Definition i_eqb k t : interp k t -> interp k t -> bool := 
  match t with 
  | Bitstring => @Veqb k
  | Group => @CGK.eqb (2^k)
  end.

 Lemma i_eqb_spec : forall k t (x y:interp k t), 
  if i_eqb x y then x = y else x <> y.
 Proof.
  intros; unfold i_eqb.
  destruct t0.
  apply Veqb_spec.
  apply CGK.eqb_spec.
 Qed.

End UT.

Module T := MakeType UT.

Inductive usupport_ (Ttype : Type) (Tuser : Ut -> Ttype) : Ttype -> Type :=
| Usupport : usupport_ Tuser (Tuser Bitstring).

(** * User-defined random sampling for bitstrings *)
Module US <: USUPPORT UT T.

 Definition usupport := usupport_ T.User.

 Definition eval k t (s:usupport t) : list (T.interp k t) :=
  match s in usupport_ _ t0 return list (T.interp k t0) with
  | Usupport => bs_support k
  end.

 Definition ceval k t (s:usupport t) : list (T.interp k t) * nat :=
  match s in usupport_ _ t0 return list (T.interp k t0) * nat with
  | Usupport => (bs_support k, S O)
  end.

 Lemma eval_usupport_nil : forall k t (s:usupport t), eval k s <> nil.
 Proof.
  intros; case s; exact (@bs_support_not_nil k).
 Qed.

 Lemma ceval_spec : forall k t (s:usupport t), eval k s = fst (ceval k s).
 Proof.
  intros k t s; case s; trivial.
 Qed.

 Definition eqb (t1 t2:T.type) (s1:usupport t1) (s2:usupport t2) : bool :=
  match s1, s2 with
  | Usupport, Usupport => true
  end.

 Lemma eqb_spec_dep :  forall t1 (e1 : usupport t1) t2 (e2:usupport t2),
  if eqb e1 e2 then eq_dep T.type usupport t1 e1 t2 e2
  else ~eq_dep T.type usupport t1 e1 t2 e2.
 Proof.
  intros.
  case e1; case e2; simpl.
  constructor.
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

End US.

Open Scope nat_scope.

Module Type HASH_FAMILY.

 (* An arbitrary value *)
 Definition kmax := 100.

 Parameter Hash : forall k, nat -> CGK.t (2^k) -> Bvector k.

 Parameter cost_Hash : forall k, nat -> CGK.t (2^k) -> nat.

 Parameter cost_Hash_poly : polynomial.

 Parameter cost_Hash_poly_spec : forall k x y,
  @cost_Hash k x y <= peval cost_Hash_poly k.
 
End HASH_FAMILY.


(** Semantics with optimizations *)
Module Entries (HF:HASH_FAMILY). 

 Export HF.

 Inductive uop : Type :=
  | OGorder
  | OGen
  | OGmul
  | OGpow
  | OGinv
  | Oxor
  | Okmax
  | Ohash.

 (** * Module for user-defined operators *)
 Module Uop <: UOP UT T.

  Definition t := uop.

  Definition eqb (o1 o2 : t) : bool :=
   match o1, o2 with
   | OGorder, OGorder
   | OGen, OGen
   | OGmul, OGmul 
   | OGpow, OGpow 
   | OGinv, OGinv => true
   | Oxor, Oxor => true
   | Okmax, Okmax => true
   | Ohash, Ohash => true
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
   | OGmul => T.User Group :: T.User Group :: nil
   | OGpow => T.User Group :: T.Nat :: nil
   | OGinv => T.User Group :: nil
   | Oxor => T.User Bitstring :: T.User Bitstring :: nil
   | Okmax => nil
   | Ohash => T.Nat :: T.User Group :: nil
   end.

  Definition tres (op: t) : T.type :=
   match op with
   | OGorder => T.Nat
   | Oxor => T.User Bitstring
   | Okmax => T.Nat
   | Ohash => T.User Bitstring
   | _ => T.User Group
   end.

  Open Scope nat_scope.
 
  Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
   match op as op0 return T.type_op k (targs op0) (tres op0) with
   | OGorder => 2^k
   | OGen => @CGK.g (2^k)
   | OGmul => @CGK.mul (2^k)
   | OGpow => @CGK.pow (2^k)
   | OGinv => @CGK.inv (2^k)
   | Oxor => BVxor k
   | Okmax => kmax
   | Ohash => @Hash k
   end.

  Implicit Arguments interp_op [k].

  Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
   match op as op0 return T.ctype_op k (targs op0) (tres op0) with
   | OGorder => (2^k, size_nat (2^k))
   | OGen => (@CGK.g (2^k), S O)
   | OGmul => fun x y => (@CGK.mul (2^k) x y, CGK.cost_mul x y)
   | OGpow => fun x n => (@CGK.pow (2^k) x n, CGK.cost_pow x n)
   | OGinv => fun x => (@CGK.inv (2^k) x, CGK.cost_inv x)
   | Oxor => fun x y => (BVxor k x y, k)
   | Okmax => (kmax, size_nat kmax)
   | Ohash => fun x y => (@Hash k x y, cost_Hash x y)
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


 Module SemO <: SEM_OPT.

  Module Sem := MakeSem.Make UT T Uop US.
  Export Sem.

  Notation "x '^' y" := (E.Eop (O.Ouser OGpow) {x, y}).
  Notation "x '**' y" := (E.Eop (O.Ouser OGmul) {x , y}) 
   (at level 40, left associativity).
  Notation "x '|x|' y" := (E.Eop (O.Ouser Oxor) {x, y}) 
   (at level 50, left associativity).	
  Notation "'g'" := (E.Eop (O.Ouser OGen) (@dnil T.type E.expr)).
  Notation "'q'" := (E.Eop (O.Ouser OGorder) (@dnil T.type E.expr)).
  Notation "'{0,1}^k'" := (E.Duser (Usupport T.User)).
  Notation Hash := (E.Eop (O.Ouser Ohash)).
  Notation K := [0..kmax].

  (* Simplifies [(e1^e2)^e3] to [e1^(e2*e3)] *)
  Definition simpl_op (op : Uop.t) : 
   E.args (Uop.targs op) -> E.expr (Uop.tres op) :=
   match op as op0 return E.args (Uop.targs op0) -> E.expr (Uop.tres op0) with
   | OGpow => fun args =>
      E.app_expr (T.User Group) args 
      (fun (e:E.expr (T.User Group)) (e3:E.expr T.Nat) =>
        match E.get_uop e with
        | Some (existT uop args) =>
          match uop as uop0 
          return E.args (Uop.targs uop0) -> E.expr (T.User Group) with
          | OGpow => fun args =>
            E.app_expr (T.User Group) args 
             (fun (e1:E.expr (T.User Group)) (e2:E.expr T.Nat) => e1 ^ (e2 *! e3))
          | _ => fun _ => e ^ e3
          end args
       | None => e ^ e3
       end)
   | op => fun args => E.Eop (O.Ouser op) args
   end.

  Implicit Arguments simpl_op [].

  Lemma simpl_op_spec : forall k op args (m:Mem.t k),
   E.eval_expr (simpl_op op args) m = E.eval_expr (E.Eop (O.Ouser op) args) m.
  Proof.
   destruct op; simpl; trivial. 
   intros args;T.dlist_inversion args; rewrite Heq; intros; simpl.
   generalize (E.get_uop_spec x); destruct (E.get_uop x); trivial.
   destruct s as (uop0, args0).
   intros H; generalize (H uop0 args0 (refl_equal _)); clear H; simpl; intros.
   destruct uop0; trivial.
   rewrite (T.eq_dep_eq H); clear H.
   clear Heq;T.dlist_inversion args0; rewrite Heq.
   simpl; unfold O.eval_op; simpl. 
   rewrite CGKP.pow_pow; trivial.
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
   case ut; simpl;
   unfold UT.size, utsize_default_poly;
   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
  Qed.

  Definition uop_poly (o:Uop.t) : bool :=
   match o with
   | OGorder | OGen | OGmul | OGpow | Oxor | Okmax | Ohash => true
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
   exists (fun _ => pplus (pcst 1) pvar).
   exists (fun _ => pplus (pcst 1) pvar). 
   simpl; split.
   rewrite pplus_spec, pcst_spec, pvar_spec; rewrite size_nat_pow_2; trivial.
   simpl; rewrite plus_0_r.
   rewrite pplus_spec, pcst_spec, pvar_spec; rewrite size_nat_pow_2; trivial.

   (* OGen *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   exists (fun _ => pplus (pcst 1) pvar).
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
   exists (fun _ => pplus (pcst 1) pvar).
   exists (fun p => pplus CGK.cost_mul_poly (pplus (G1 p) (G2 p))).
   intros k m p Hm; simpl; split.

   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
   rewrite pplus_spec, pplus_spec.
   apply plus_le_compat.
   apply le_trans with (peval CGK.cost_mul_poly (pred (size_nat (2^k)))).
   apply CGK.cost_mul_poly_spec.
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
   exists (fun _ => pplus (pcst 1) pvar).
   exists (fun p => pplus CGK.cost_pow_poly (pplus (G1 p) (G2 p))).
   intros k m p Hm; simpl; split.

   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
   rewrite pplus_spec, pplus_spec.
   apply plus_le_compat.
   apply le_trans with (peval CGK.cost_pow_poly (pred (size_nat (2^k)))).
   apply CGK.cost_pow_poly_spec.
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
   rewrite Heq in Hla; discriminate.

   (* Oxor *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [G1 H1] ].
   left; trivial.
   destruct (Hla _ x0) as [F2 [G2 H2] ].
   right; left; trivial.
   exists (fun _ => pplus (pcst 1) pvar).
   exists (fun p => pplus (pplus (pcst 1) pvar) (pplus (G1 p) (G2 p))).
   simpl; split.
   rewrite pplus_spec, pcst_spec, pvar_spec.
   simpl; unfold UT.size; trivial.
   
   generalize (H1 k m p) (H2 k m p); clear H1 H2.
   simpl.
   case_eq (E.ceval_expr x m); simpl.
   case_eq (E.ceval_expr x0 m); simpl.
   intros i n Heqi i0 n0 Heqi0 Hi Hi0.
   destruct Hi.
   intros; apply H0; simpl.
   apply Vset.subset_correct with (fv_expr x); [ | trivial].  
   unfold fv_expr; simpl.
   apply fv_expr_rec_subset.
   destruct Hi0.
   intros; apply H0; simpl.
   apply Vset.subset_correct with (fv_expr x0); [ | trivial].  
   unfold fv_expr at 2; simpl.
   fold (fv_expr_extend x0 (fv_expr_rec Vset.empty x)).
   rewrite union_fv_expr_spec.
   apply VsetP.subset_union_l.
   
   rewrite pplus_spec, pplus_spec, pplus_spec,  pcst_spec, pvar_spec.    
   apply plus_le_compat; auto.  
   auto with arith.
   rewrite plus_0_r; apply plus_le_compat; trivial. 
   
   (* Okmax  *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   exists (fun _ => size_nat kmax).
   exists (fun _ => size_nat kmax).
   simpl; split.
   rewrite pcst_spec; trivial.
   rewrite pcst_spec; trivial.

   (* Ohash *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [G1 H1] ].
   left; trivial.
   destruct (Hla _ x0) as [F2 [G2 H2] ].
   right; left; trivial.
   exists (fun _ => pplus 1 pvar).
   exists (fun p => pplus cost_Hash_poly (pplus (G1 p) (G2 p))).
   intros k m p Hm; simpl; split.

   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.

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
   rewrite pplus_spec, pplus_spec.
   apply plus_le_compat; auto.
   apply cost_Hash_poly_spec.  
   simpl; rewrite plus_0_r; apply plus_le_compat; trivial.
  Qed.
   
  Definition usupport_poly t (us:US.usupport t) : bool :=
   match us with 
   | Usupport => true
   end. 

  Lemma usupport_poly_spec : forall t (us:US.usupport t),
   usupport_poly us ->
   exists F, exists G, PPT_support (E.Duser us) F G.
  Proof.
   intros t us; destruct us; intros _.
   exists (fun _ => pplus (pcst 1) pvar).
   exists (fun _ => pcst 1).
   intros k m p Hm.
   simpl; split.
   rewrite pplus_spec, pcst_spec, pvar_spec.
   intros; simpl; unfold UT.size; trivial.
   rewrite pcst_spec; trivial. 
  Qed.
 
 End Uppt.

End Entries.

Declare Module HF : HASH_FAMILY.

Module EntriesHF := Entries HF.

Module Tactics := BuildTac.Make EntriesHF.
Export Tactics.


Lemma opt_sampling : forall E (x y z:Var.var (T.User Bitstring)), 
 Var.mkV x <> y ->
 Var.mkV x <> z ->
 Var.mkV y <> z ->
 EqObs (Vset.singleton z)
 E [x <$- {0,1}^k; y <- x |x| z] 
 E [y <$- {0,1}^k; x <- y |x| z]
 (Vset.add x (Vset.add y (Vset.singleton z))).
Proof.
 intros E x y z Hxy Hxz Hyz.
 apply equiv_cons with
  ((kreq_mem (Vset.singleton z)) /-\ 
   fun k m1 m2 => m1 x = BVxor _ (m2 y) (m2 z)).

 eapply equiv_strengthen;
  [ | apply equiv_random_permut with 
   (f:=fun k (m1 m2:Mem.t k) v => BVxor _ (m2 z) v)].
 unfold kreq_mem, andR; split.

 apply PermutP_weaken with (fun v1 v2 => v1 = BVxor k v2 (m2 z)).
 intros; subst; apply BVxor_comm.

 apply PermutP_bs_support_xor.
 intros; rewrite <- (H _ z); [ | apply Vset.singleton_correct; trivial].
 split.
 
 intros ? ? Hn; Vset_mem_inversion Hn.
 rewrite <- Heq.  
 repeat (rewrite Mem.get_upd_diff; [ | trivial]).
 rewrite H; [ | apply Vset.singleton_correct]; trivial.

 repeat rewrite Mem.get_upd_same.
 rewrite Mem.get_upd_diff, BVxor_comm, H; trivial.
 apply Vset.singleton_correct; trivial.

 eapply equiv_strengthen; [ | apply equiv_assign].
 unfold upd_para, Meq, andR; intros k m1 m2 (H1, H2).
 simpl E.eval_expr; unfold O.eval_op; simpl T.app_op. 
 intros ? ? Hn; Vset_mem_inversion Hn.
 rewrite <- Heq, Mem.get_upd_diff, Mem.get_upd_same; trivial.
 auto.
 rewrite <- Heq0, Mem.get_upd_same, Mem.get_upd_diff, H2, (H1 _ z).
 rewrite BVxor_assoc, BVxor_nilpotent, BVxor_0_r; trivial.
 apply Vset.singleton_correct; trivial.
 trivial.
 rewrite <- Heq1.
 repeat (rewrite Mem.get_upd_diff; [ | auto]).
 rewrite H1; [ | apply Vset.singleton_correct]; trivial.
Qed.
