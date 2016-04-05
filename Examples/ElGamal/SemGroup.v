(** * SemGroup.v : Language extension with a cyclic group type *)
 
Set Implicit Arguments.

Require Import PPT.
Require Export BuildTac.
Require Export Group2.

Module MAKE_SEM_GROUP (CGK : CYCLIC_GROUP_WITH_ORDER).

(** Semantics with optimizations *)
Module Entries. 

 Module MG := MAKE_GROUP CGK.
 Module CGKP := CGO_Properties CGK.

 Import MG.

 Module SemO <: SEM_OPT.

  Module T_ := MakeType Gt.

  Module Uop_ := Gop T_.

  Module US_ := EmptySupport Gt T_.

  Module Sem := MakeSem.Make Gt T_ Uop_ US_.
  Export Sem.

  Notation "x '^' y" := (E.Eop (O.Ouser OGpow) {x, y}).
  Notation "x '**' y" := (E.Eop (O.Ouser OGmul) {x , y}) 
   (at level 40, left associativity).
  Notation "'g'" := (E.Eop (O.Ouser OGen) (@dnil T.type E.expr)).
  Notation "'q'" := (E.Eop (O.Ouser OGorder) (@dnil T.type E.expr)).


  Definition simpl_op (op : Uop.t) : 
   E.args (Uop.targs op) -> E.expr (Uop.tres op) :=
   match op as op0 return E.args (Uop.targs op0) -> E.expr (Uop.tres op0) with
   | OGpow => fun args =>
      E.app_expr (T.User Tg) args 
      (fun (e:E.expr (T.User Tg)) (e3:E.expr T.Nat) =>
        match E.get_uop e with
        | Some (existT uop args) =>
          match uop as uop0 return E.args (Uop.targs uop0) -> E.expr (T.User Tg) with
          | OGpow => fun args =>
            E.app_expr (T.User Tg) args 
             (fun (e1:E.expr (T.User Tg)) (e2:E.expr T.Nat) => e1 ^ (e2 *! e3))
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
   destruct s as (uop, args0).
   intros H; generalize (H uop args0 (refl_equal _)); clear H; simpl; intros.
   destruct uop; trivial.
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

  Open Scope nat_scope.

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
   forall k, UT.size (t:=ut) (UT.default k ut) <= peval (utsize_default_poly r) k.
  Proof.
   intros r ut _ k.
   case ut; simpl.
   unfold UT.size, utsize_default_poly. 
   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.  
  Qed.

  Definition uop_poly (o:Uop.t) : bool :=
   match o with
   | OGen | OGmul | OGpow => true
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
   exists (fun _ => pplus (pcst 1) (pplus (pcst 1) pvar)).
   exists (fun _ => pplus (pcst 1) pvar). 
   simpl; split.
   rewrite pplus_spec, pplus_spec, pcst_spec, pvar_spec; simpl.
   rewrite <- size_nat_pow_2.
   apply size_nat_monotonic.
   assert (Hb := CGK.o_bouned k).
   apply lt_le_weak.
   replace (2 ^ S k) with (2 ^ (k + 1));[ omega | auto with zarith ].
   simpl; rewrite plus_0_r.
   rewrite pplus_spec, pcst_spec, pvar_spec.
   destruct (eq_nat_dec k 0); intros.
   subst; simpl; trivial.
   eapply le_trans; [ apply size_nat_le | ]; omega.   
   
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
  Qed.

  Definition usupport_poly t (us:US.usupport t) : bool := false.

  Lemma usupport_poly_spec : forall t (us:US.usupport t),
   usupport_poly us ->
   exists F, exists G, PPT_support (E.Duser us) F G.
  Proof.
   intros t us; case us.
  Qed.

 End Uppt.

End Entries.

Module Tactics := BuildTac.Make Entries.
Export Tactics.


Definition minus_mod (x m k:nat) :=
 match le_lt_dec m x with
 | left _ => (x - m) %nat
 | _ => (k - m + x)%nat
 end.

Lemma mult_uniform : 
 forall E (n:Var.var T.Nat) (x:Var.var (T.User Tg)) (e:E.expr (T.User Tg)) P,
  ~Vset.mem n (fv_expr e) ->
  equiv P
  E [n <$- [0..q-!1]; x <- g ^ n ** e]
  E [n <$- [0..q-!1]; x <- g ^ n] 
  (kreq_mem {{x}}).
Proof.
 intros E n x e P Hn.
 apply equiv_cons with 
  (fun k (m1 m2:Mem.t k) => 
   m1 n = minus_mod (m2 n) (CGK.log (E.eval_expr e m1)) (CGK.o k)).

 (* equiv_random_permut *)
 eapply equiv_strengthen; 
  [ | apply equiv_random_permut with 
     (f:=fun k (m1 m2:Mem.t k) v => minus_mod v (CGK.log (E.eval_expr e m1)) (CGK.o k))].
 red; intros; split.

 (* permut_support *)
 unfold permut_support.
 change (E.eval_support [0..q -! 1] m2) with (E.eval_support [0..q -! 1] m1).
 generalize (CGK.log (E.eval_expr e m1)) (CGK.log_lt (E.eval_expr e m1)).
 intros p; destruct (zerop p); intros; subst.
 
  (* p = 0 *) 
  apply PermutP_refl.
  intros a _; unfold minus_mod; destruct (le_lt_dec 0 a); omega.

  (* p > 0 *) 
  assert (Hs:forall (m:Mem.t k), E.eval_support [0..q-!1] m = seq 0 (CGK.o k)).
  simpl; unfold O.eval_op; simpl.
  destruct (CGK.o k)%nat; simpl.
  elimtype False; omega.
  rewrite <- minus_n_O; trivial.

  rewrite Hs.
  assert (Hle:(p <= CGK.o k)%nat) by auto with arith.
  assert (W:=@seq_PermutP (CGK.o k) p Hle).
  apply PermutP_weaken with (R2:=fun x y => y = x) in W; auto.
  apply PermutP_sym in W. 
  apply PermutP_trans with (2:=W).
  pattern (CGK.o k)%nat at 2; replace (CGK.o k)%nat with (((CGK.o k) - p) + p)%nat; auto with zarith.
  rewrite seq_append; apply PermutP_app.
  apply Permut_seq_R; unfold minus_mod; intros.
  destruct (le_lt_dec p (i + p)); omega.
  apply Permut_seq_R; unfold minus_mod; intros.
  destruct (le_lt_dec p (i + 0)); omega.

 (* precondition *)
 intros v Hv.
 rewrite Mem.get_upd_same, Mem.get_upd_same.
 assert (
  E.eval_expr e m1 = 
  E.eval_expr e (m1 {!n <-- minus_mod v (CGK.log (E.eval_expr e m1)) (CGK.o k)!})).
 apply EqObs_e_fv_expr.
 red; intros; rewrite Mem.get_upd_diff; trivial.
 intros Heq; rewrite <- Heq in H0; apply Hn; trivial.
 rewrite <- H0; trivial.

 (* assignment *)
 eapply equiv_strengthen; [ | apply equiv_assign].
 intros k m1 m2 H t w H0.
 Vset_mem_inversion H0; rewrite Heq.
 repeat rewrite Mem.get_upd_same.
 simpl; unfold O.eval_op, T.app_op, O.interp_op, Uop.interp_op.
 rewrite H.
 set (X:=E.eval_expr e m1).
 pattern X at 2; rewrite (CGK.log_spec X).
 generalize (m2 n) (CGK.log X) (CGK.log_lt X); intros n1 p Hlt.
 rewrite CGKP.mul_pow_plus.
 unfold minus_mod.
 destruct (le_lt_dec p n1).
 rewrite plus_comm, le_plus_minus_r; trivial.
 rewrite plus_comm; repeat rewrite plus_assoc.
 rewrite le_plus_minus_r; auto with arith.
 rewrite plus_comm, <- CGKP.mul_pow_plus, CGK.cyclic_k, CGK.mul_0_r; trivial.
Qed.

End MAKE_SEM_GROUP.
