(** SigmaSem.v : Semantics for the AND and OR composition of Sigma protocols *)

Require Import Bitstrings.
Require Export BuildTac.

Set Implicit Arguments.
Unset Strict Implicit.


(** Some interpretation of types *)
Parameter U : nat -> Type.
Parameter U_default : forall k, U k.
Parameter U_eq_dec : forall k (u1 u2:U k), {u1 = u2} + {u1 <> u2}.

Inductive ut : Type := 
 | Bitstring
 | xT1 | wT1 | rT1 | stateT1 | cT1 | sT1 
 | xT2 | wT2 | rT2 | stateT2 | cT2 | sT2.

Module UT <: UTYPE.

 Definition t := ut.

 Scheme Equality for ut.

 Definition eqb := ut_beq.

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  destruct x; destruct y; simpl; trivial || discriminate.
 Qed.

 Definition eq_dec (x y:t) : {x = y} + {True}.
  destruct x; destruct y; (left; apply refl_equal) || (right; trivial).
 Defined.

 Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
 Proof.
  destruct x; destruct y; intros; try discriminate.
 Qed.

 Definition interp k (T:t) : Type := 
  match T with
   | Bitstring => Bvector k
   | _ => U k
  end.

 Definition size k (t0:t) (x:interp k t0) := 
  match t0 with
    | Bitstring => S k
   | _ => S 0
  end.

 Definition default k (t0:t) : interp k t0 :=
  match t0 with
  | Bitstring => Bvect_false k
  | _ => U_default k
  end.

 Definition default_poly (_:t) := pplus (pcst 1) pvar.

 Open Scope nat_scope.

 Lemma size_positive : forall k t0 (x:interp k t0), 0 < size x.
 Proof.
  destruct t0; intros; simpl; auto with arith.
 Qed.

 Lemma default_poly_spec : forall k (t0:t),
  size (default k t0) <= peval (default_poly t0) k.
 Proof.
  intro k; unfold default_poly; rewrite pplus_spec, pcst_spec, pvar_spec.
  destruct t0; auto with arith.
 Qed.

 Definition i_eqb k t0 : interp k t0 -> interp k t0 -> bool := 
  match t0 with 
   | Bitstring => @Veqb k
   | _ => fun u1 u2 => if U_eq_dec u1 u2 then true else false
  end.

 Lemma i_eqb_spec : forall k t0 (x y:interp k t0), 
  if i_eqb x y then x = y else x <> y.
 Proof.
  destruct t0; simpl; try (destruct x; destruct y; trivial);
   try (intros x y; case (U_eq_dec x y); trivial).
  apply Veqb_spec.
 Qed.  

End UT.

Module T := MakeType UT.


Inductive usupport_ (Ttype : Type) (Tuser : ut -> Ttype) : Ttype -> Type :=
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


Inductive uop (Utype:Type) : Type := 
 | Xor.

Module UOP <: UOP UT T.

 Definition t := uop UT.t.

 Scheme Equality for uop.

 Definition eqb := @uop_beq UT.t UT.eqb.

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  intros x y; case x; case y; simpl; trivial; intros; try discriminate;
  generalize (UT.eqb_spec t2 t0); case (UT.eqb t2 t0);
  generalize (UT.eqb_spec t3 t1); case (UT.eqb t3 t1); 
  intros; subst; simpl; trivial; intro Heq; injection Heq; auto.
 Qed.

 Definition targs (op:t) := 
  match op with
   | Xor => T.User Bitstring :: T.User Bitstring :: nil    
  end.

 Definition tres (op:t) := 
  match op with
   | Xor => T.User Bitstring
  end.

 Definition interp_op k (op:t) : T.type_op k (targs op) (tres op) :=
  match op as op0 return T.type_op k (targs op0) (tres op0) with
   | Xor => BVxor k
  end.

 Definition cinterp_op k (op : t) :T.ctype_op k (targs op) (tres op) :=
  match op as op0 return T.ctype_op k (targs op0) (tres op0) with
   | Xor => fun x y => (BVxor k x y, k)
  end.

 Definition eval_op k
  (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) :=
  @T.app_op k (targs op) (tres op) (interp_op k op) args.

 Definition ceval_op k 
  (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) * nat :=
  @T.capp_op k (targs op) (tres op) (cinterp_op k op) args.

 Lemma ceval_op_spec : forall k op args,
  @eval_op k op args = fst (@ceval_op k op args).
 Proof.
  intros k op args; destruct op; T.dlist_inversion args; subst; trivial.
 Qed.

End UOP.


(** * Semantics with simplification rules for xor *)
Module SemO <: SEM_OPT.
 
 Module Sem := MakeSem.Make UT T UOP US.  
 Export Sem.

 Notation "x (+) y" := (E.Eop (O.Ouser (@Xor _)) {x, y}) 
  (at level 50, left associativity).

 Definition simpl_op (op:Uop.t) : E.args (Uop.targs op) -> E.expr (Uop.tres op) :=
   match op as op0 return E.args (Uop.targs op0) -> E.expr (Uop.tres op0) with
   | Xor => fun args => E.app_expr _ args 
     (fun e1 e2 =>
      match E.get_uop e1 with
      | Some (existT uop args) =>
        match uop return E.args (Uop.targs uop) -> E.expr (T.User Bitstring) with
        | Xor => fun args =>
          E.app_expr _ args (fun e3 e4 => 
           if E.eqb e2 e4 then e3 else 
             if E.eqb e2 e3 then e4 else
               if E.eqb e3 e4 then e2 else e1 (+) e2)
        end args
      | None => 
        match E.get_uop e2 with
         | Some (existT uop args) =>
           match uop return E.args (Uop.targs uop) -> E.expr (T.User Bitstring) with
            | Xor => fun args =>
             E.app_expr _ args (fun e3 e4 => 
              if E.eqb e1 e4 then e3 else
                if E.eqb e1 e3 then e4 else
                  if E.eqb e3 e4 then e1 else e1 (+) e2)
           end args
         | None => e1 (+) e2
        end
      end)
   end.

 Implicit Arguments simpl_op []. 

 Lemma simpl_op_spec : forall k op args (m:Mem.t k),
  E.eval_expr (@simpl_op op args) m = E.eval_expr (E.Eop (O.Ouser op) args) m.
 Proof.
  destruct op; simpl; trivial.
 
  (* Xor *)
  intros args; T.dlist_inversion args; rewrite Heq; intros; simpl.
  generalize (E.get_uop_spec x); destruct (E.get_uop x); trivial;
  generalize (E.get_uop_spec x0); destruct (E.get_uop x0); trivial.

  destruct s as (uop1, args1); destruct s0 as (uop2, args2); trivial. 
  intros H2; generalize (H2 uop2 args2 (refl_equal _)); clear H2; simpl; intro H2.
  intros H1; generalize (H1 uop1 args1 (refl_equal _)); clear H1; simpl; intro H1.
  destruct uop1; trivial.
  rewrite (T.eq_dep_eq H1); clear H1.
  clear Heq; T.dlist_inversion args1; rewrite Heq; clear Heq.
  simpl; unfold O.eval_op; simpl.
  generalize (E.eqb_spec x0 x2); case (E.eqb x0 x2); intro H1.
  rewrite H1, BVxor_bij; trivial.
  generalize (E.eqb_spec x1 x2); case (E.eqb x1 x2); intro H3.
  generalize (E.eqb_spec x0 x1); case (E.eqb x0 x1); intro H4.
  subst.
  elim H1; trivial.
  rewrite H3, BVxor_nilpotent, BVxor_0_l; trivial.
  generalize (E.eqb_spec x0 x1); case (E.eqb x0 x1); intro H4.
  rewrite H4, BVxor_assoc, BVxor_comm, BVxor_bij; trivial.
  trivial.
  
  destruct s as (uop1, args1); trivial.
  intros _.
  intros H1; generalize (H1 uop1 args1 (refl_equal _)); clear H1; simpl; intro H1.
  destruct uop1; trivial.
  rewrite (T.eq_dep_eq H1); clear H1.
  clear Heq; T.dlist_inversion args1; rewrite Heq; clear Heq.
  simpl; unfold O.eval_op; simpl.
  generalize (E.eqb_spec x0 x2); case (E.eqb x0 x2); intro H1.
  rewrite H1; rewrite BVxor_bij; trivial.
  generalize (E.eqb_spec x1 x2); case (E.eqb x1 x2); intro H3.
  generalize (E.eqb_spec x0 x1); case (E.eqb x0 x1); intro H4.
  subst.
  elim H1; trivial.
  rewrite H3, BVxor_nilpotent, BVxor_0_l; trivial.
  generalize (E.eqb_spec x0 x1); case (E.eqb x0 x1); intro H4.
  rewrite H4, BVxor_assoc, BVxor_comm, BVxor_bij; trivial.
  trivial.

  destruct s as (uop1, args1); trivial.
  intros H1; generalize (H1 uop1 args1 (refl_equal _)); clear H1; simpl; intro H1.
  intros _.
  destruct uop1; trivial.
  rewrite (T.eq_dep_eq H1); clear H1.
  clear Heq; T.dlist_inversion args1; rewrite Heq; clear Heq.
  simpl; unfold O.eval_op; simpl.
  generalize (E.eqb_spec x x2); case (E.eqb x x2); intro H1.
  rewrite H1; rewrite BVxor_comm, BVxor_bij; trivial.
  generalize (E.eqb_spec x x1); case (E.eqb x x1); intro H3.
  rewrite H3, <- BVxor_assoc, BVxor_nilpotent, BVxor_0_l; trivial.
  generalize (E.eqb_spec x1 x2); case (E.eqb x1 x2); intro H4.
  rewrite H4, BVxor_nilpotent, BVxor_0_r; trivial.
  trivial.
 Qed.

End SemO.


Module SemT := BaseProp.Make SemO.Sem.


Module Uppt.
 
 Import SemT.

 Implicit Arguments T.size [k t].

 Open Scope nat_scope.

 (** PPT expression *)
 Definition PPT_expr (t:T.type) (e:E.expr t) 
  (F:polynomial -> polynomial) 
  (G:polynomial -> polynomial) : Prop :=
  forall k (m:Mem.t k) p,
   (forall t (x:Var.var t), 
    Vset.mem x (fv_expr e) -> T.size (m x) <= peval p k)  ->
   let (v,n) := E.ceval_expr e m in
    T.size v <= peval (F p) k /\
    n <= peval (G p) k.

 (** PPT support *)
 Definition PPT_support t (s:E.support t)
  (F:polynomial -> polynomial) 
  (G:polynomial -> polynomial) : Prop :=
  forall k (m:Mem.t k) p,
   (forall t (x:Var.var t), 
    Vset.mem x (fv_distr s) -> T.size (m x) <= peval p k)  ->
   let (l,n) := E.ceval_support s m in
    (forall v, In v l -> T.size v <= peval (F p) k) /\
    n <= peval (G p) k.

 Definition utsize : UT.t -> nat := fun _ => 1.

 Definition utsize_default_poly : nat -> polynomial :=
  fun _ => pplus (pcst 1) pvar.

 Lemma utsize_default_poly_spec : forall r t,
  utsize t <= r -> 
  forall k, UT.size (t:=t) (UT.default k t) <= peval (utsize_default_poly r) k.
 Proof.
  intros r t _ k.
  apply UT.default_poly_spec.    
 Qed.

 Definition uop_poly (o:Uop.t) : bool := true.

 Lemma uop_poly_spec : forall o (la:dlist E.expr (O.targs (O.Ouser o))),
  uop_poly o ->
  (forall t (e:E.expr t), @DIn _ E.expr _ e _ la -> 
   exists F, exists G, PPT_expr e F G) ->
  exists F, exists G, PPT_expr (E.Eop (O.Ouser o) la) F G.
 Proof.
  intros o la H Hla.
  destruct o; simpl.
  
  (* Xor *)    
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


Module Entries.

 Module SemO := SemO.

 Module BP := SemT.
 
 Module Uppt := Uppt.

End Entries.


Module Tactics := BuildTac.Make Entries.
Export Tactics.

Notation "'{0,1}^k'" := (E.Duser (Usupport T.User)).
Notation "x (+) y" := (E.Eop (O.Ouser (@Xor _)) {x, y}) 
 (at level 50, left associativity).


(** * An algebraic propery of xor *)
Section OPTIMISTIC_SAMPLING.

 Variables x y : Var.var (T.User Bitstring).
 Variable z : E.expr (T.User Bitstring).
 
 Hypothesis x_z  : Vset.mem x (fv_expr z) = false.
 Hypothesis y_z : Vset.mem y (fv_expr z) = false.
 Hypothesis x_y: Var.mkV x <> y.
 
 Lemma optimistic_sampling : forall E, 
  EqObs (fv_expr z)
  E [x <$- {0,1}^k; y <- x (+) z] 
  E [y <$- {0,1}^k; x <- y (+) z]
  (Vset.add x (Vset.add y (fv_expr z))).
 Proof.
  intros E'.
  apply equiv_cons with
   ((kreq_mem (fv_expr z)) /-\ 
   fun k m1 m2 => m1 x = E.eval_expr (y (+) z) m2).

  eapply equiv_strengthen;
  [ | apply equiv_random_permut with 
   (f:=fun k (m1 m2:Mem.t k) v => BVxor _ (E.eval_expr z m2) v)].
  unfold kreq_mem, andR; split.

  apply PermutP_weaken with (fun v1 v2 => v1 = BVxor _ v2 (E.eval_expr z m2)).
  intros; subst; apply BVxor_comm.

  apply PermutP_bs_support_xor.
  intros; split.
  apply req_mem_trans with m1.
  apply req_mem_sym; apply req_mem_upd_disjoint; trivial.
  apply req_mem_trans with m2; trivial.
  apply req_mem_upd_disjoint; trivial.

  rewrite Mem.get_upd_same, BVxor_comm.
  simpl; unfold O.eval_op; simpl.
  rewrite Mem.get_upd_same.
  assert (m2 =={fv_expr z} m2{!y <-- v!}).
  apply req_mem_upd_disjoint; trivial.
  rewrite depend_only_fv_expr_subset with (2:=H1).
  trivial.
  apply VsetP.subset_refl.

  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold upd_para, Meq, andR; intros k m1 m2 (H1, H2).
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op. 
  intros ? ? Hn.
  rewrite VsetP.add_spec in Hn. 
  rewrite VsetP.add_spec in Hn.
  decompose [or] Hn; clear Hn.
  inversion H; simpl. 
  rewrite Mem.get_upd_diff, Mem.get_upd_same; auto.
  inversion H0; simpl. 
  rewrite Mem.get_upd_same, Mem.get_upd_diff; auto.
  rewrite H2.
  simpl; unfold O.eval_op; simpl.
  
  rewrite BVxor_assoc.
  rewrite depend_only_fv_expr_subset with (2:=H1);
   [ | apply VsetP.subset_refl].
  rewrite BVxor_nilpotent, BVxor_0_r; trivial.
  repeat rewrite Mem.get_upd_diff.
  auto.
  intro Heq; rewrite <- Heq in H0; rewrite H0 in x_z; discriminate.
  intro Heq; rewrite <- Heq in H0; rewrite H0 in y_z; discriminate.
 Qed.

End OPTIMISTIC_SAMPLING.


(** Helper functions to build specification for procedures *)
Set Strict Implicit.
  
Section BUILD_REFL_INFO.
 
 Variables E1 : env.
 Variable t : T.type. 
 Variable f : Proc.proc t.
 Variable fi : info (proc_params E1 f) (proc_body E1 f) (proc_res E1 f).

 Definition basic_refl_info : proc_eq_refl_info E1 f.
 refine (@Build_proc_eq_refl_info E1 t f
  (Build_dproc_eq_refl_info 
   Vset.empty Vset.empty (Vset_of_var_decl (proc_params E1 f)) Vset.empty true) _).
 split; simpl; intros; try discriminate.
 apply fi.(info_lossless).
 apply VsetP.subset_refl.
 exists fi.(info_X); split.
 apply fi.(info_modify_local).
 
 rewrite VsetP.union_sym, VsetP.union_empty; apply fi.(info_modify).
 apply VsetP.subset_refl.
 exists (fv_expr (proc_res E1 f)); repeat split.
 apply fi.(info_re_local).
 rewrite VsetP.union_sym, VsetP.union_empty.
 apply fi.(info_eqobs).
 rewrite VsetP.union_sym, VsetP.union_empty, VsetP.union_sym, VsetP.union_empty.
 apply EqObs_e_fv_expr.
 Defined.

End BUILD_REFL_INFO.

Section BUILD_INV_INFO.

 Variables E1 E2 : env.
 Variable t : T.type. 
 Variable f : Proc.proc t. 
 Variable fi1 : info (proc_params E1 f) (proc_body E1 f) (proc_res E1 f).

 Hypothesis Hp : proc_params E1 f = proc_params E2 f.
 Hypothesis Hb : proc_body E1 f = proc_body E2 f.
 Hypothesis Hr : proc_res E1 f = proc_res E2 f.

 Definition add_basic_info (pii:eq_inv_info trueR E1 E2) : 
  eq_inv_info trueR E1 E2.       
 intros pii.
 set (fi2:=fi1); rewrite Hp, Hb, Hr in fi2.
 refine (@add_pii_info trueR E1 E2 t f _ pii).
 refine (Build_proc_eq_inv_info
  (dpii:=Build_dproc_eq_inv_info 
   (basic_refl_info E1 f fi1)
   (basic_refl_info E2 f fi2)  
   Vset.empty
   (Vset_of_var_decl (proc_params E1 f))
   Vset.empty) _).
 split; simpl; intros; try discriminate.
 apply VsetP.subset_refl.
 rewrite Hp; apply VsetP.subset_refl.
 exists (fv_expr (proc_res E1 f)); repeat split.
 apply fi1.(info_re_local).
 rewrite VsetP.union_sym, VsetP.union_empty.
 apply EqObs_equiv_trueR.
 rewrite <- Hb; apply fi1.(info_eqobs).
 rewrite Hr; intros k m1 m2 Heq.
 rewrite depend_only_fv_expr_subset with (2:=Heq); auto with set.
 Defined.

End BUILD_INV_INFO.

Implicit Arguments add_basic_info [t].
