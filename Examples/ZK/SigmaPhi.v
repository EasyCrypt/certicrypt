(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * SigmaPhi.v: Sigma Phi protocols *)

Require Import Sigma.
Require Export Homomorphism.
Require Import BuildTac.
Require Import LtIrrelevance.

Set Implicit Arguments.


(** * Functor constructing a Sigma-phi protocol corresponding to a
   special homomorphism. A valid challenge set must be given (it may
   be constructed using the functor in Homomorphism.v that minimizes
   the knowledge error).
*)
Module SigmaPhi (G H:GROUP) (HM:HOMOMORPHISM G H) (CS:CHALLENGE_SET G H HM).
 
 (** We first extend the semantics with the needed types and operators *)
 Open Scope nat_scope.
 Unset Strict Implicit.

 Module HMP := Homomorphism_Properties G H HM.
 Import HMP.
 Import CS.

 Definition Z_of_C k (x : {n:nat | n <= cplus k}) := Z_of_nat (projT1 x).

 (** Types for elements of [G], [H], and for challenges [C] *)
 Inductive ut_ : Type := 
 | G_t | H_t | C_t.

 (** * User-defined type module *)
 Module Ut <: UTYPE.

  Definition t := ut_.

  Definition eqb (t1 t2:t) := 
   match t1, t2 with
   | G_t, G_t 
   | H_t, H_t => true
   | C_t, C_t => true
   | _, _ => false
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

  Definition interp k (t0:t) := 
   match t0 with
   | G_t => G.t k
   | H_t => H.t k
   | C_t => {n : nat | n <= cplus k}
   end.

  Definition size k (t0:t) : interp k t0 -> nat := 
   match t0 with
   | G_t => fun _ => S (size_nat (length (G.elems k)))
   | H_t => fun _ => S (size_nat (length (H.elems k)))
   | C_t => fun x => size_nat (projT1 x)
   end.

 Definition default k (t0:t) : interp k t0 := 
   match t0 with
   | G_t => G.e k
   | H_t => H.e k
   | C_t => existT  _ O (le_O_n _)
   end.

  Definition default_poly (t0:t) := 
   pplus G.order_poly (pplus H.order_poly 1).

  Lemma size_positive : forall k (t0:t) x, 0 < @size k t0 x.
  Proof.
   intros k t0 x; unfold size; destruct t0; auto with arith.
   apply size_nat_positive.
  Qed.

  Lemma default_poly_spec : forall k (t0:t), 
   @size k t0 (default k t0) <= peval (default_poly t0) k.
  Proof.
   intros k t0.
   unfold default, default_poly, size.
   destruct t0.
   eapply le_trans; [apply G.order_size_nat | apply pplus_le_l].
   eapply le_trans; [ | apply pplus_le_r].
   eapply le_trans; [apply H.order_size_nat | apply pplus_le_l].
   eapply le_trans; [ | apply pplus_le_r].
   eapply le_trans; [ | apply pplus_le_r].
   rewrite pcst_spec; trivial.
   Qed.

  Definition i_eqb k t (x y:interp k t) :=
   match t return interp k t -> interp k t -> bool with
   | G_t => @G.eqb k
   | H_t => @H.eqb k
   | C_t => fun n m => nat_eqb (projT1 n) (projT1 m)
   end x y.

  Lemma i_eqb_spec : forall k t (x y:interp k t), 
   if i_eqb x y then x = y else x <> y.
  Proof.
   intros; destruct t0.
   refine (G.eqb_spec _ _).
   refine (H.eqb_spec _ _).
   destruct x; destruct y; simpl.
   case_eq (nat_eqb x x0).
   intro Heq; apply nat_eqb_true in Heq; subst.
   rewrite (le_eq l l0); trivial.
   intros Heq Heq1.
   rewrite <- not_is_true_false in Heq.
   elim Heq; injection Heq1; intro; subst; apply nat_eqb_refl.
  Qed.

 End Ut.


 Module T := MakeType Ut.


 Inductive uop_ : Type :=
 | OZ_of_C
 | OG_order
 | OG_mul | OG_pow | OG_inv
 | OH_mul | OH_pow | OH_inv
 | Ophi  
 | Ospecial_v 
 | Ospecial_u
 | Oeuclid.

 Module Uop <: UOP Ut T.

  Definition t := uop_.
  
  Definition eqb (o1 o2:t) : bool :=
   match o1, o2 with
    | OZ_of_C, OZ_of_C
    | OG_order, OG_order
    | OG_mul, OG_mul 
    | OG_pow, OG_pow 
    | OG_inv, OG_inv 
    | OH_mul, OH_mul 
    | OH_pow, OH_pow 
    | OH_inv, OH_inv 
    | Ophi, Ophi
    | Ospecial_v, Ospecial_v 
    | Ospecial_u, Ospecial_u  
    | Oeuclid, Oeuclid => true
    | _, _ => false
   end.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   destruct x; destruct y; simpl; trivial; intro; discriminate.
  Qed.

  Definition targs (op:t) : list T.type :=
   match op with
    | OZ_of_C => T.User C_t :: nil   
    | OG_order => nil
    | OG_mul => T.User G_t :: T.User G_t :: nil
    | OG_pow => T.User G_t :: T.Zt :: nil
    | OG_inv => T.User G_t :: nil
    | OH_mul => T.User H_t :: T.User H_t :: nil
    | OH_pow => T.User H_t :: T.Zt :: nil
    | OH_inv => T.User H_t :: nil
    | Ophi => T.User G_t :: nil 
    | Ospecial_v => nil 
    | Ospecial_u => T.User H_t :: nil
    | Oeuclid => T.Zt :: T.Zt :: nil
   end.

  Definition tres (op:t) : T.type :=
   match op with
    | OZ_of_C => T.Zt 
    | OG_order => T.Nat
    | OG_mul => T.User G_t
    | OG_pow => T.User G_t
    | OG_inv => T.User G_t
    | OH_mul => T.User H_t
    | OH_pow => T.User H_t
    | OH_inv => T.User H_t
    | Ophi => T.User H_t 
    | Ospecial_v => T.Zt 
    | Ospecial_u => T.User G_t
    | Oeuclid => T.Pair (T.Pair T.Zt T.Zt) T.Zt
   end.

  Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
   match op as op0 return T.type_op k (targs op0) (tres op0) with
    | OZ_of_C => @Z_of_C k
    | OG_order => length (G.elems k)
    | OG_mul => @G.mul k
    | OG_pow => @G.powZ k
    | OG_inv => @G.inv k
    | OH_mul => @H.mul k
    | OH_pow => @H.powZ k
    | OH_inv => @H.inv k
    | Ophi => @phi k 
    | Ospecial_v => special_v k
    | Ospecial_u => @special_u k
    | Oeuclid => eeuclid
   end.

  Implicit Arguments interp_op [k].

  Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
   match op as op0 return T.ctype_op k (targs op0) (tres op0) with
    | OZ_of_C => fun x => (Z_of_C x, 1) 
    | OG_order => (length (G.elems k), 1)
    | OG_mul => fun x y => (G.mul x y, G.cost_mul x y)
    | OG_pow => fun x y => (G.powZ x y, G.cost_pow x y)
    | OG_inv => fun x => (G.inv x, G.cost_inv x)
    | OH_mul => fun x y => (H.mul x y, H.cost_mul x y)
    | OH_pow => fun x y => (H.powZ x y, H.cost_pow x y)
    | OH_inv => fun x => (H.inv x, H.cost_inv x)
    | Ophi => fun x => (phi x, cost_phi x)   
    | Ospecial_v => (special_v k, cost_special_v k)
    | Ospecial_u => fun x => (special_u x, @cost_special_u k x)
    | Oeuclid => fun x y => (eeuclid x y, size_Z x * size_Z y)
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

 Inductive usupport_ (Ttype : Type) (Tuser : ut_ -> Ttype) : Ttype -> Type :=
 | Gsupport : usupport_ Tuser (Tuser G_t)
 | Csupport : usupport_ Tuser (Tuser C_t).

 (** * User-defined random sampling for elements in G *)
 Module US <: USUPPORT Ut T.

  Definition usupport := usupport_ T.User.

  Definition elems_aux n : list {x | x <= n} -> list {x | x <= S n} :=
   map (fun s : {x | x <= n} => 
    match s with 
     exist x H => exist (fun x => x <= S n) x (le_S x n H) 
    end).

  Fixpoint elems n : list {x | x <= n} :=
   match n return list {x | x <= n} with
   | O => (exist (fun x => x <= O) O (le_refl _)) :: nil
   | S n0 => exist (fun x => x <= S n0) (S n0) (le_refl _) :: elems_aux (elems n0)
   end.

  Definition eval k t (s:usupport t) : list (T.interp k t) :=
   match s in usupport_ _ t0 return list (T.interp k t0) with
   | Gsupport => G.elems k
   | Csupport => elems (cplus k)
   end.

  Definition ceval k t (s:usupport t) : list (T.interp k t) * nat :=
   match s in usupport_ _ t0 return list (T.interp k t0) * nat with
   | Gsupport => (G.elems k, S O)
   | Csupport => (elems (cplus k), S O)
   end.

  Lemma eval_usupport_nil : forall k t (s:usupport t), eval k s <> nil.
  Proof.
   intros; case s; simpl.
   apply G.elems_not_nil.
   destruct (cplus k); discriminate.
  Qed.

  Lemma ceval_spec : forall k t (s:usupport t), eval k s = fst (ceval k s).
  Proof.
   intros k t s; case s; trivial.
  Qed.

  Definition eqb (t1 t2:T.type) (s1:usupport t1) (s2:usupport t2) : bool :=
   match s1, s2 with
   | Gsupport, Gsupport => true
   | Csupport, Csupport => true
   | _, _ => false
   end.

  Lemma eqb_spec_dep :  forall t1 (e1 : usupport t1) t2 (e2:usupport t2),
   if eqb e1 e2 then eq_dep T.type usupport t1 e1 t2 e2
    else ~eq_dep T.type usupport t1 e1 t2 e2.
  Proof.
   intros; case e1; case e2; constructor || (intro H; inversion H).
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

 Module Sem := MakeSem.Make Ut T Uop US.
 Module SemT := BaseProp.Make Sem.

 Module Entries.

  (** Semantics with optimizations *)
  Module SemO <: SEM_OPT.

   Module Sem := Sem.
   Export Sem.

   (** Notations *)
   Notation "'N2Z' x " := (E.Eop (O.Ouser OZ_of_C) {x}) (at level 30).
   Notation "x '-Z-' y"  := (E.Eop O.OZsub {x, y}) (at level 50, left associativity).
   Notation "x '|+|' y" := (E.Eop (O.Ouser OG_mul) {x,y}) (at level 45).
   Notation "x '*' a" := (E.Eop (O.Ouser OG_pow) {x,a}).
   Notation "'--' x " := (E.Eop (O.Ouser OG_inv) {x}) (at level 30).
   Notation "x '|*|' y" := (E.Eop (O.Ouser OH_mul) {x,y}) (at level 45).
   Notation "x '^' a" := (E.Eop (O.Ouser OH_pow) {x,a}).
   Notation "x '^-1'" := (E.Eop (O.Ouser OH_inv) {x}) (at level 30).
   Notation q := (E.Eop (O.Ouser OG_order) (dnil _)).
   Notation Ephi := (E.Eop (O.Ouser Ophi)).
   Notation v := (E.Eop (O.Ouser Ospecial_v) (dnil _)).
   Notation "'u' x" := (E.Eop (O.Ouser Ospecial_u) {x}) (at level 50).
   Notation E_euclid := (E.Eop (O.Ouser Oeuclid)).
   Notation Gs := (E.Duser (Gsupport T.User)).   
   Notation C := (E.Duser (Csupport T.User)).   

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
     let (l,n) := E.ceval_support s m in
      (forall v, In v l -> T.size v <= peval (F p) k) /\
      n <= peval (G p) k.

   Definition utsize : Ut.t -> nat := fun _ => 1.

   Definition utsize_default_poly : nat -> polynomial :=
    fun _ => pplus G.order_poly (pplus H.order_poly 1).

   Lemma utsize_default_poly_spec : forall r ut,
    utsize ut <= r -> 
    forall k, 
     Ut.size (t:=ut) (Ut.default k ut) <= peval (utsize_default_poly r) k.
   Proof.
    intros r ut _ k.
    case ut; simpl; unfold Ut.size, utsize_default_poly. 
    eapply le_trans; [apply G.order_size_nat | apply pplus_le_l].
    eapply le_trans; [ | apply pplus_le_r].
    eapply le_trans; [apply H.order_size_nat | apply pplus_le_l].
    eapply le_trans; [ | apply pplus_le_r].
    eapply le_trans; [ | apply pplus_le_r].
    rewrite pcst_spec; trivial.  
   Qed.

   Definition uop_poly (o:Uop.t) : bool :=
    match o with
    | OZ_of_C
    | OG_order 
    | OG_mul | OG_pow | OG_inv
    | OH_mul | OH_pow | OH_inv 
    | Ophi 
    | Ospecial_v 
    | Ospecial_u
    | Oeuclid => true
    end.

   Lemma uop_poly_spec : forall o (la:dlist E.expr (O.targs (O.Ouser o))),
    uop_poly o ->
    (forall t (e:E.expr t), @DIn _ E.expr _ e _ la -> 
     exists F, exists G, PPT_expr e F G) ->
    exists F, exists G, PPT_expr (E.Eop (O.Ouser o) la) F G.
   Proof.
    intros o la H Hla.
    destruct o.

    (* OZ_of_C *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    exists (fun p => pplus 1 (F1 p)).
    exists (fun p => pplus 1 (G1 p)).
    intros k m p Hm.
    generalize (H1 k m p); clear H1.
    simpl; rewrite E.ceval_expr_spec.
    destruct (E.ceval_expr x m); simpl.
    intros [H1 H2]; intros.
    apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].
    apply VsetP.subset_refl.
    simpl; split.
    unfold size_Z, Z_of_C; rewrite Zabs_nat_Z_of_nat.
    rewrite pplus_spec, pcst_spec; omega.
    rewrite pplus_spec, pcst_spec, <- plus_n_O; omega.

    (* OG_order *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    exists (fun _ => pplus 1 G.order_poly). 
    exists (fun _ => 1).
    simpl; split.
    rewrite pplus_spec, pcst_spec.
    generalize (G.order_size_nat k); simpl; omega.
    rewrite pcst_spec; trivial.

    (* OG_mul *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    destruct (Hla _ x0) as [F2 [G2 H2] ].
    right; left; trivial.
    exists (fun _ => pplus 1 G.order_poly).
    exists (fun p => pplus G.cost_mul_poly (pplus (G1 p) (G2 p))).
    intros k m p Hm; simpl; split.

    rewrite pplus_spec, pcst_spec; trivial.
    generalize (G.order_size_nat k); simpl; unfold Ut.size; omega.

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
    apply G.cost_mul_poly_spec.
    apply plus_le_compat; trivial.

    (* OG_pow *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    destruct (Hla _ x0) as [F2 [G2 H2] ].
    right; left; trivial.
    exists (fun _ => pplus 1 G.order_poly).
    exists (fun p => pplus G.cost_pow_poly (pplus (G1 p) (G2 p))).
    intros k m p Hm; simpl; split.

    rewrite pplus_spec, pcst_spec.
    generalize (G.order_size_nat k); simpl; unfold Ut.size; omega.

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
    apply G.cost_pow_poly_spec.
    apply plus_le_compat; trivial.

    (* OG_inv *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    exists (fun _ => pplus 1 G.order_poly).
    exists (fun p => pplus G.cost_inv_poly (G1 p)).
    intros k m p Hm; simpl; split.

    rewrite pplus_spec, pcst_spec.
    generalize (G.order_size_nat k); simpl; unfold Ut.size; omega.

    generalize (H1 k m p); clear H1.
    case_eq (E.ceval_expr x m); simpl.
    intros y n Heqy Hy.
    destruct Hy.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].
    apply VsetP.subset_refl.
    rewrite plus_0_r, pplus_spec; apply plus_le_compat.
    apply G.cost_inv_poly_spec.
    trivial.

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
    exists (fun p => pplus cost_phi_poly (G1 p)). 
    simpl; split.
    unfold T.size, Ut.size; rewrite pplus_spec, pcst_spec.
    generalize (H.order_size_nat k); omega.
    generalize (H1 k m p); clear H1.
    case_eq (E.ceval_expr x m); simpl.
    intros i n Heqi Hi.
    destruct Hi.
    intros; apply H0; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].
    unfold fv_expr; simpl; auto with set.
    rewrite pplus_spec; apply plus_le_compat.
    apply cost_phi_poly_spec.
    rewrite Heqi, plus_0_r; trivial.

    (* Ospecial_v *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    exists (fun _ => special_v_poly).
    exists (fun _ => cost_special_v_poly).
    simpl; split.
    apply size_nat_special_v.
    rewrite plus_0_r; apply cost_special_v_poly_spec.

    (* Ospecial_u *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    exists (fun _ => G.order_poly).
    exists (fun p => pplus cost_special_u_poly (G1 p)).
    intros k m p Hm; simpl; split.
    apply G.order_size_nat.
    simpl; rewrite plus_0_r, pplus_spec.
    apply plus_le_compat.
    apply cost_special_u_poly_spec.
    generalize (H1 k m p); clear H1.
    case_eq (E.ceval_expr x m); simpl.
    intros y n Heqy Hy.
    destruct Hy.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].
    apply VsetP.subset_refl.
    trivial.
   
    (* Oeuclid *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    destruct (Hla _ x0) as [F2 [G2 H2] ].
    right; left; trivial.
    exists (fun p => pplus 2 (pplus (pplus (pplus (F1 p) (F2 p)) (pplus (F1 p) (F2 p))) (pplus (F1 p) (F2 p)))).
    exists (fun p => pplus (pmult (F1 p) (F2 p)) (pplus (G1 p) (G2 p))).
    intros k m p Hm.
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
    repeat rewrite E.ceval_expr_spec; rewrite Heqi, Heqi0; clear Heqi Heqi0.
    simpl; split.
    
    repeat rewrite pplus_spec; rewrite pcst_spec.
    match goal with |- S (S ?X) <= _ => change (S (S X)) with (2 + X) end.
    apply plus_le_compat; [ trivial | ].
    destruct (eeuclid_bound i0 i (Zabs i0 + Zabs i)).
    rewrite <- (Zplus_0_r (Zabs i0)) at 1; apply Zplus_le_compat_l; apply Zabs_pos.
    rewrite <- (Zplus_0_l (Zabs i)) at 1; apply Zplus_le_compat_r; apply Zabs_pos.
    apply plus_le_compat.
    apply plus_le_compat.
    apply le_trans with (size_nat (Zabs_nat i0 + Zabs_nat i)).
    apply size_nat_monotonic.
    apply inj_le_rev; rewrite inj_plus; repeat rewrite inj_Zabs_nat; trivial.
    eapply le_trans; [ apply size_nat_plus | unfold size_Z in H0, H2; omega].
    apply le_trans with (size_nat (Zabs_nat i0 + Zabs_nat i)).
    apply size_nat_monotonic.
    apply inj_le_rev; rewrite inj_plus; repeat rewrite inj_Zabs_nat; trivial.
    eapply le_trans; [ apply size_nat_plus | unfold size_Z in H0, H2; omega].

    assert (He:=eeuclid_spec i0 i).
    destruct (eeuclid i0 i) as ((u',v),d); simpl.
    destruct (He u' v d (refl_equal _)) as [Hd [Hgcd _] ]; subst.
    case (Z_eq_dec i0 0); intro Hi0.
    case (Z_eq_dec i 0); intro Hi.
    subst.
    rewrite Zmult_0_r, Zmult_0_r; simpl; omega.

    destruct Hgcd.
    apply Zdivide_bounds in H7; [ | trivial].
    apply le_trans with (size_Z i).
    apply size_nat_monotonic.
    repeat rewrite <- inj_Zabs_nat in H7; omega.
    repeat rewrite <- inj_Zabs_nat in H7; omega.

    destruct Hgcd.
    apply Zdivide_bounds in H6; [ | trivial].
    apply le_trans with (size_Z i0).
    apply size_nat_monotonic.
    repeat rewrite <- inj_Zabs_nat in H6; omega.
    repeat rewrite <- inj_Zabs_nat in H6; omega.

    rewrite plus_0_r, pplus_spec, pplus_spec, pmult_spec.
    apply plus_le_compat; [ apply mult_le_compat | ]; omega.
   Qed.
  
   Definition usupport_poly t (us:US.usupport t) : bool := true.

   Lemma usupport_poly_spec : forall t (us:US.usupport t),
    usupport_poly us ->
    exists F, exists G, PPT_support (E.Duser us) F G.
   Proof.
    intros t us; case us; intros _.
    exists (fun _ => pplus (pcst 1) G.order_poly).
    exists (fun _ => pcst 1).
    intros k m p Hm.
    simpl; split.
    rewrite pplus_spec, pcst_spec.
    intros; apply le_S; apply G.order_size_nat.
    rewrite pcst_spec; trivial. 
  
    exists (fun _ => cplus_poly).
    exists (fun _ => pcst 1).
    intros k m p Hm.
    simpl; split.
    intros; eapply le_trans; [ | apply size_nat_cplus].
    apply size_nat_monotonic; destruct v; trivial.
    rewrite pcst_spec; trivial.
   Qed.

  End Uppt.

 End Entries.


 Module Tactics := BuildTac.Make Entries.
 Export Tactics.
  
 Section FACTS.
    
  Variables E1 E2 : env.
  Variables x y : Var.var (T.User G_t).
  Variable z : E.expr (T.User G_t).
  Variable P : mem_rel.
  
  Hypothesis x_z : Vset.mem x (fv_expr z) = false.
    
  Lemma G_plus_pad : 
   equiv P
   E1 [x <$- Gs; y <- x |+| z]
   E2 [x <$- Gs; y <- x] 
   (kreq_mem {{y}}).
  Proof. 
   apply equiv_cons with 
    (fun k (m1 m2:Mem.t k) => m1 x = G.mul (m2 x) (G.inv (E.eval_expr z m1))).

   (* equiv_random_permut *)
   eapply equiv_strengthen; 
    [ | apply equiv_random_permut with 
       (f:=fun k (m1 m2:Mem.t k) v => G.mul v (G.inv (E.eval_expr z m1)))].
   red; intros; split.

   (* permut_support *)
   unfold permut_support.
   apply PermutP_NoDup with (fun v => G.mul v (E.eval_expr z m1)); intros.
   apply G.elems_nodup.
   apply G.elems_nodup.
   rewrite <- G.mul_assoc, GP.mul_inv_r, GP.mul_e_r; trivial.
   rewrite <- G.mul_assoc, G.mul_inv_l, GP.mul_e_r; trivial.
   apply G.elems_full.
   apply G.elems_full.

   (* precondition *)
   intros v Hv.
   mem_upd_simpl.
   assert (
    E.eval_expr z m1 = 
    E.eval_expr z (m1 {!x <-- G.mul v (G.inv (E.eval_expr z m1))!})).
   apply EqObs_e_fv_expr.
   red; intros.
   rewrite Mem.get_upd_diff; trivial.
   intros Heq; rewrite <- Heq, x_z in H0; discriminate.
   rewrite <- H0; trivial.

   (* assignment *)
   eapply equiv_strengthen; [ | apply equiv_assign].
   intros k m1 m2 H t w H0.
   Vset_mem_inversion H0; rewrite Heq.
   mem_upd_simpl.
   simpl; unfold O.eval_op; simpl; rewrite H.
   rewrite <- G.mul_assoc, G.mul_inv_l, GP.mul_e_r; trivial.
  Qed.

 End FACTS.


 (** * The protocol *)
 Module Protocol : SIGMA N Sem BP.

  Import N.

  Definition xT     := T.User H_t.
  Definition wT     := T.User G_t.
  Definition rT     := T.User H_t.
  Definition stateT := T.User G_t.
  Definition cT     := T.User C_t.
  Definition sT     := T.User G_t.

  (** Knowledge relation *)
  Definition R k (x:T.interp k (T.User H_t)) (w:T.interp k (T.User G_t)) := 
   x = phi w.

  Definition R' := R.

  Lemma R_dec : forall k (x:T.interp k (T.User H_t)) (w:T.interp k (T.User G_t)), 
   sumbool (R x w) (~R x w).
  Proof.
   intros; unfold R.
   generalize (H.eqb_spec x (phi w)).
   case (H.eqb x (phi w)); auto.
  Qed.

  Definition R'_dec := R_dec.

  (** Variables *)
  Notation x      := (Var.Lvar (T.User H_t) 1).
  Notation w      := (Var.Lvar (T.User G_t) 2).
  Notation r      := (Var.Lvar (T.User H_t) 3). 
  Notation state  := (Var.Lvar (T.User G_t) 4). 
  Notation c      := (Var.Lvar (T.User C_t) 5). 
  Notation s      := (Var.Lvar (T.User G_t) 6).
  Notation b      := (Var.Lvar T.Bool 7).
  Notation rstate := (Var.Lvar (T.Pair (T.User H_t) (T.User G_t)) 8).
  Notation rs     := (Var.Lvar (T.Pair (T.User H_t) (T.User G_t)) 9).
  Notation x'     := (Var.Lvar (T.User H_t) 10).
  Notation w'     := (Var.Lvar (T.User G_t) 11).
  Notation r'     := (Var.Lvar (T.User H_t) 12). 
  Notation state' := (Var.Lvar (T.User G_t) 13). 
  Notation c'     := (Var.Lvar (T.User C_t) 14). 
  Notation s'     := (Var.Lvar (T.User G_t) 15).
  Notation c''    := (Var.Lvar (T.User C_t) 16). 
  Notation s''    := (Var.Lvar (T.User G_t) 17).
  Notation c1     := (Var.Lvar (T.User C_t) 18). 
  Notation s1     := (Var.Lvar (T.User G_t) 19).
  Notation c2     := (Var.Lvar (T.User C_t) 20). 
  Notation s2     := (Var.Lvar (T.User G_t) 21).
  Notation y'     := (Var.Lvar (T.User G_t) 22).
  Notation abd    := (Var.Lvar (T.Pair (T.Pair T.Zt T.Zt) T.Zt) 23).
  Notation a      := (Var.Lvar T.Zt 24).
  Notation b'     := (Var.Lvar T.Zt 25).

  (** Procedures *)
  Notation P1 := (Proc.mkP 1 
   ((T.User H_t) :: (T.User G_t) :: nil) 
   (T.Pair (T.User H_t) (T.User G_t))).
 
  Notation P2 := (Proc.mkP 2 
   ((T.User H_t) :: (T.User G_t) :: (T.User G_t) :: (T.User C_t) :: nil) 
   (T.User G_t)).
 
  Notation V1 := (Proc.mkP 3 
   ((T.User H_t) :: (T.User H_t) :: nil) 
   (T.User C_t)).
 
  Notation V2 := (Proc.mkP 4 
   ((T.User H_t) :: (T.User H_t) :: (T.User C_t) :: (T.User G_t) :: nil) 
   T.Bool).

  Notation S  := (Proc.mkP 5 
   ((T.User H_t) :: (T.User C_t) :: nil) 
   (T.Pair (T.User H_t) (T.User G_t))).
 
  Notation KE := (Proc.mkP 6 
   ((T.User H_t) :: (T.User H_t) :: (T.User C_t) :: (T.User C_t) :: (T.User G_t) :: (T.User G_t) :: nil) 
   (T.User G_t)).

  
  Definition P1_args := dcons _ x' (dcons _ w' (dnil Var.var)).
  Definition P1_body := [ y' <$- Gs ].
  Definition P1_re   := (Ephi {y'} | y').

  Definition P2_args := 
   dcons _ x' (dcons _ w' (dcons _ state' (dcons _ c' (dnil Var.var)))).
  Definition P2_body := [ s' <- state' |+| (w' * (N2Z c')) ].
  Definition P2_re : E.expr (T.User G_t) := s'.

  Definition V1_args := dcons _ x' (dcons _ r' (dnil Var.var)).
  Definition V1_body := [ c' <$- C ].
  Definition V1_re : E.expr (T.User C_t) := c'.

  Definition V2_args := 
   dcons _ x' (dcons _ r' (dcons _ c' (dcons _ s' (dnil Var.var)))).
  Definition V2_body := nil:cmd.
  Definition V2_re   := Ephi {s'} =?= r' |*| x' ^ (N2Z c').

  Definition S_args := dcons _ x' (dcons _ c' (dnil Var.var)).
  Definition S_body := [ s' <$- Gs; r' <- Ephi {s'} |*| (x' ^ (N2Z c') )^-1 ].
  Definition S_re   := (r' | s').

  Definition KE_args := 
   dcons _ x' (dcons _ r' (dcons _ c' (dcons _ c'' (dcons _ s' (dcons _ s''
    (dnil Var.var)))))). 

  Definition KE_body := 
   [
    abd <- E_euclid {N2Z c' -Z- N2Z c'', v};
    a <- Efst (Efst abd);  
    b' <- Esnd (Efst abd);
    w' <- (s' |+| -- s'') * a |+| (u x') * b'
   ].

  Definition KE_re : (E.expr (T.User G_t)) := w'.

  Parameter _E : env.

  Section ENV.

   Let add_P1 E := add_decl E P1 P1_args (refl_equal _) P1_body P1_re.
   Let add_P2 E := add_decl E P2 P2_args (refl_equal _) P2_body P2_re.
   Let add_V1 E := add_decl E V1 V1_args (refl_equal _) V1_body V1_re.
   Let add_V2 E := add_decl E V2 V2_args (refl_equal _) V2_body V2_re.
   Let add_S  E := add_decl E S S_args (refl_equal _) S_body S_re.
   Let add_KE E := add_decl E KE KE_args (refl_equal _) KE_body KE_re.

   Definition E := add_KE (add_S (add_P1 (add_P2 (add_V1 (add_V2 _E))))).

  End ENV.

  Parameter P1_i : info P1_args P1_body P1_re.
  Parameter P2_i : info P2_args P2_body P2_re.
  Parameter V1_i : info V1_args V1_body V1_re.
  Parameter V2_i : info V2_args V2_body V2_re.
  Parameter S_i  : info S_args S_body S_re.
  Parameter KE_i : info KE_args KE_body KE_re.
  
  Definition protocol := 
   [
    rstate <c- P1 with {x, w};
    r <- Efst rstate; state <- Esnd rstate;
    c <c- V1 with {x, r};
    s <c- P2 with {x, w, state, c};
    b <c- V2 with {x, r, c, s}
   ].

  Definition protocol' := 
   [
    rstate <c- P1 with {x, w};
    r <- Efst rstate; state <- Esnd rstate;
    s <c- P2 with {x, w, state, c};
    b <c- V2 with {x, r, c, s}
   ]. 

  Definition simulation :=
   [
    rs <c- S with {x,c};
    r <- Efst rs;
    s <- Esnd rs
   ].

  Definition R1 : mem_rel := fun k (m1:Mem.t k) _ => R (m1 x) (m1 w).

  Definition iEE := 
   add_refl_info_O S (fv_expr S_re) Vset.empty Vset.empty
   (add_refl_info_O P1 (fv_expr P1_re) Vset.empty Vset.empty
   (add_refl_info_O P2 (fv_expr P2_re) Vset.empty Vset.empty 
   (add_refl_info_O V1 (fv_expr V1_re) Vset.empty Vset.empty
   (add_refl_info_O V2 (fv_expr V2_re) Vset.empty Vset.empty
   (empty_info E E))))).

  Definition Inv := req_mem_rel {{x, w}} R1. 

  Lemma decMR_R1 : decMR R1.
  Proof.
   unfold decMR, R1, R; intros k m1 m2.
   simpl; unfold O.eval_op; simpl.
   generalize (T.i_eqb_spec k xT (m1 x) (phi (m1 w))).
   destruct (T.i_eqb k xT (m1 x) (phi (m1 w))); intro; [left | right]; apply H.
  Qed.

  Hint Resolve decMR_R1.  

  Lemma completeness : forall k (m:Mem.t k), 
   R (m x) (m w) -> Pr E protocol m (EP k b) == 1%U.
  Proof.
   unfold protocol; intros. 
   transitivity (Pr E [ b <- true ] m (EP k b)).
   apply equiv_deno with (P := Inv) (Q := kreq_mem {{b}}).
   unfold Inv.
   inline_l iEE P1.
   inline_l iEE V1.
   inline_l iEE P2.
   inline_l iEE V2.
   ep iEE; deadcode iEE.
   ep_eq_l x (Ephi {w}).  
   unfold req_mem_rel, andR,kreq_mem, E.eval_expr.
   simpl; unfold O.eval_op; simpl.
   intros k0 m1 m2 [H1 H2]; exact H2.
   apply equiv_strengthen with (kreq_mem Vset.empty).
   intros; unfold kreq_mem; trivial.

   apply EqObs_trans with E
    [
      y' <$- Gs;
      c <$- C;
      b <- true
    ].
   eqobs_hd.
   ep_eq_l (Ephi {y' |+| w * (N2Z c) }) (Ephi {y'} |*| Ephi {w} ^ (N2Z c) ).
   intros; simpl; unfold O.eval_op; simpl.
   rewrite phi_homo, phi_powZ; trivial.
   eqobs_in.
   deadcode; eqobs_in.
   intros m1 m2 H0; unfold EP, charfun, restr, fone; simpl.
   rewrite (H0 _ b); trivial.
   unfold Inv, R ; split; [ apply req_mem_refl | ].
   simpl in H; unfold O.eval_op in H; simpl in H; exact H.
   unfold Pr; rewrite deno_assign_elim; simpl.
   unfold charfun, EP, restr; simpl.
   mem_upd_simpl.
  Qed.

  Lemma SHVZK :
   equiv (req_mem_rel {{x, w, c}} R1)
   E protocol'
   E simulation
   (kreq_mem {{r, c, s}}).
  Proof.
   unfold protocol', simulation, Inv.

   inline_r iEE S.
   inline_l iEE P1.
   inline_l iEE V1.
   sinline_l iEE P2.

   alloc_r s' s.
   ep; deadcode.

   ep_eq_r x (Ephi {w}).
   unfold EP2, E.eval_expr; simpl; unfold O.eval_op; simpl; intros k m1 m2 [H1 H2].
   rewrite <- (H1 _ x), <- (H1 _ w) ;trivial.
   apply equiv_strengthen with (kreq_mem {{x, w, c}}).
   intros k m1 m2 [H1 H2]; exact H1.

   apply EqObs_trans with E
    [
      s <$- Gs;
      y' <- s |+| --(w * (N2Z c));
      s <- y' |+| w * (N2Z c);
      r <- Ephi {y'}
    ].
   swap.
   eqobs_tl.
   alloc_l y' s.
   union_mod.
   apply EqObs_sym; apply G_plus_pad; trivial.

   ep; deadcode.
   eqobs_hd.
   ep_eq_l ((s |+| --(w * (N2Z c) )) |+| w * (N2Z c)) s.
   intros; simpl; unfold O.eval_op; simpl.
   rewrite <- G.mul_assoc, G.mul_inv_l, GP.mul_e_r; trivial.
   deadcode.
   ep_eq_l (Ephi {s |+| --(w * (N2Z c) )}) (Ephi {s} |*| (Ephi {w} ^ (N2Z c) ) ^-1).
   intros; simpl; unfold O.eval_op; simpl.
   rewrite phi_homo, phi_inv, phi_powZ; trivial.
   eqobs_in.
  Qed.

  Definition pi : PPT_info E := 
   PPT_add_info (PPT_add_info (PPT_empty_info E) KE) S.

  Lemma S_PPT : PPT_proc E S.
  Proof.
   PPT_proc_tac pi.
  Qed.

  Section SOUNDNESS.  

   Close Scope positive_scope.
   Close Scope nat_scope.

   Variable k : nat.
   Variable m : Mem.t k.

   Hypothesis H_neq : m c1 <> m c2.
   Hypothesis accepting_1 : Pr E [b <c- V2 with {x, r, c1, s1} ] m (EP k b) == 1.
   Hypothesis accepting_2 : Pr E [b <c- V2 with {x, r, c2, s2} ] m (EP k b) == 1.

   Lemma H1 : phi (m s1)  = H.mul (m r) (H.pow (m x) (projT1 (m c1))).
   Proof.
    assert (Pr E [b <- (Ephi {s1}  =?= r |*| x ^ N2Z c1)] m (EP k b) == 1).
    rewrite <- accepting_1.
    apply EqObs_deno with {{x, r, c1, s1}} {{b}}.
    sinline_r iEE V2; eqobs_in iEE.
    intros; unfold charfun, restr, EP. 
    rewrite (depend_only_fv_expr b H); trivial.
    trivial.
    generalize H; unfold Pr.
    rewrite deno_assign_elim.
    unfold charfun, restr, EP, fone.
    simpl E.eval_expr; unfold O.eval_op; simpl.
    rewrite Mem.get_upd_same.
    unfold Z_of_C; rewrite HP.powZ_pow.
    generalize (H.eqb_spec (phi (m s1)) (H.mul (m r) (H.pow (m x) (projT1 (m c1))))).
    case (H.eqb (phi (m s1)) (H.mul (m r) (H.pow (m x) (projT1 (m c1))))).
    trivial.
    intros; elim Udiff_0_1; trivial.
   Qed.

   Lemma H2 : phi (m s2)  = H.mul (m r) (H.pow (m x) (projT1 (m c2))).
   Proof.
    assert (Pr E [b <- (Ephi {s2}  =?= r |*| x ^ N2Z c2)] m (EP k b) == 1).
    rewrite <- accepting_2.
    apply EqObs_deno with {{x, r, c2, s2}} {{b}}.
    sinline_r iEE V2; eqobs_in iEE.
    intros; unfold charfun, restr, EP. 
    rewrite (depend_only_fv_expr b H); trivial.
    trivial.
    generalize H; unfold Pr.
    rewrite deno_assign_elim.
    unfold charfun, restr, EP, fone.
    simpl E.eval_expr; unfold O.eval_op; simpl.
    rewrite Mem.get_upd_same.
    unfold Z_of_C; rewrite HP.powZ_pow.
    generalize (H.eqb_spec (phi (m s2)) (H.mul (m r) (H.pow (m x) (projT1 (m c2))))).
    case (H.eqb (phi (m s2)) (H.mul (m r) (H.pow (m x) (projT1 (m c2))))).
    trivial.
    intros; elim Udiff_0_1; trivial.
   Qed.

   Open Scope Z_scope.

   Lemma soundness_aux :
    phi (G.mul (m s1) (G.inv (m s2))) = 
    H.powZ (m x) (Z_of_C (m c1) - Z_of_C (m c2)).
   Proof.
    rewrite phi_homo, phi_inv, H1, H2.
    rewrite HP.inv_mul, H.mul_assoc, <- (H.mul_comm (H.inv (m r))).
    rewrite H.mul_assoc, H.mul_inv_l, H.mul_e_l; trivial.
    apply HP.cancellation with (H.powZ (m x) (Z_of_C (m c2))).
    rewrite HP.mul_powZ_plus, Zplus_minus.
    unfold Z_of_C; repeat rewrite HP.powZ_pow.
    rewrite H.mul_assoc, H.mul_comm, H.mul_assoc. 
    rewrite H.mul_inv_l, H.mul_e_l; trivial.
   Qed.

   Close Scope Z_scope.

   Lemma KE_correct : 
    Pr E [w <c- KE with {x, r, c1, c2, s1, s2} ] m
     (fun m => if R'_dec (m x) (m w) then true else false) == 1. 
   Proof.
    transitivity (Pr E  
     [ w <- (s1 |+| --s2) * Efst (Efst (E_euclid {N2Z c1 -Z- N2Z c2, v})) |+|
            (u x) * (Esnd (Efst (E_euclid {N2Z c1 -Z- N2Z c2, v}))) ] m 
     (fun m => if R'_dec (m x) (m w) then true else false)).
    apply EqObs_deno with {{x, r, c1, c2, s1, s2}} {{x, w}}.
    inline_l iEE V2.
    sinline_l iEE KE; eqobs_in iEE.
    intros; unfold charfun, restr.
    rewrite (H _ x), (H _ w); trivial.
    trivial.

    unfold Pr; rewrite deno_assign_elim.
    unfold charfun, restr, fone.
    simpl E.eval_expr; unfold O.eval_op; simpl.
    mem_upd_simpl.

    match goal with
     |- context [R'_dec ?A ?B] => case (R'_dec A B) 
    end.
    trivial.
    intro HR; elim HR; unfold R.
    assert (Hprime : rel_prime (Z_of_C (m c1) - Z_of_C (m c2)) (special_v k)).
    assert (projT1 (m c1) <= cplus k)%nat by (destruct (m c1); trivial).
    assert (projT1 (m c2) <= cplus k)%nat by (destruct (m c2); trivial).
    assert (Hneq:projT1 (m c1) <> projT1 (m c2)).    
     destruct (m c1); destruct (m c2); simpl. 
     intro Heq; elim H_neq.
     generalize l l0; rewrite Heq; intros; rewrite (le_eq l1 l2); trivial.
    unfold Z_of_C; apply Zdivide_lt_rel_prime.
    intros p Hp Hdiv; generalize (cplus_spec Hp Hdiv).
    omega.
    omega.

    generalize (eeuclid_spec (Z_of_C (m c1) - Z_of_C (m c2)) (special_v k)).
    destruct (eeuclid (Z_of_C (m c1) - Z_of_C (m c2)) (special_v k)).
    intro Heuclid.
    rewrite phi_homo, phi_powZ, phi_powZ, phi_special.
    rewrite soundness_aux. 
    unfold Z_of_C; simpl.
    rewrite HP.powZ_powZ, HP.powZ_powZ, HP.mul_powZ_plus.
    simpl.
    rewrite Zmult_comm, (Zmult_comm (special_v k)).  
    destruct (Heuclid (fst p) (snd p) z)%Z as [H3 [H4 Hpos] ].
    destruct p; trivial.
    unfold Z_of_C in H3; rewrite H3.
    destruct (Zis_gcd_unique _ _ _ _ Hprime H4). 
    rewrite <- H.
    simpl; rewrite HP.mul_e_r; trivial.
    elimtype False; omega.
   Qed.

   Lemma KE_PPT : PPT_proc E KE.
   Proof.
    PPT_proc_tac pi.
   Qed.

  End SOUNDNESS.

 End Protocol.

End SigmaPhi.


(** Usage example:

Declare Module G1 : GROUP.
Declare Module H1 : GROUP.
Declare Module G2 : GROUP.
Declare Module H2 : GROUP.
Declare Module HM1 : HOMOMORPHISM G1 H1.
Declare Module HM2 : HOMOMORPHISM G2 H2.

Module GG := Group_Prod G1 G2.
Module HH := Group_Prod H1 H2.
Module HM := Homomorphism_Prod G1 H1 G2 H2 HM1 HM2.
Module CS := Largest_Challenge_Set GG HH HM.

Module S := SigmaPhi GG HH HM CS.
*)
