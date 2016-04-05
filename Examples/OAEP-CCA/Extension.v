(** * Extension.v : An user-defined extension to pWHILE, including
operators corresponding to a permutation and its inverse *)

Require Export PPT.
Require Export BuildTac2.
Require Import Bitstrings.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope nat_scope.


Module Type TRAPDOOR_PERM.

 Parameter k0 : nat -> nat.
 Parameter k1 : nat -> nat.
 Parameter n  : nat -> nat.

 Parameter k_spec : forall k, k = n k + k0 k + k1 k.
 
 (** * Trapdoor permutation and its inverse *)

 Definition Bvectork k := 
  ((Bvector (n k) *  Bvector (k1 k)) * Bvector (k0 k))%type.

 Parameter f : forall k, Bvectork k -> Bvectork k.

 Parameter finv : forall k, Bvectork k -> Bvectork k.

 Parameter f_spec : forall k (x:Bvectork k), finv (f x) = x.

 Parameter finv_spec : forall k (y:Bvectork k), f (finv y) = y.

 Parameter cost_f : polynomial.
 Parameter cost_finv : nat -> nat.

 (** Maximum number of queries made to the G oracle *)
 Parameter qG_poly : polynomial.

 (** Maximum number of queries made to the H oracle *)
 Parameter qH_poly : polynomial.

 (** Maximum number of queries made to the decryption oracle *)
 Parameter qD_poly : polynomial.

End TRAPDOOR_PERM.


Module Entries (TP:TRAPDOOR_PERM).

 Inductive ut_ : Type := 
 | Bitstring_n
 | Bitstring_k0
 | Bitstring_k1.

 (** * User-defined type module *)
 Module Ut <: UTYPE.

  Definition t := ut_. 

  Definition eqb (t1 t2 :t) := 
   match t1, t2 with 
   | Bitstring_n,   Bitstring_n   => true
   | Bitstring_k0,  Bitstring_k0  => true
   | Bitstring_k1,  Bitstring_k1  => true
   | _, _ => false
   end.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   simpl; destruct x; destruct y; simpl;
    trivial; discriminate.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {True} :=
   match x as x0 return {x0 = y} + {True} with
   | Bitstring_n =>
     match y as y0 return {Bitstring_n = y0} + {True} with 
     | Bitstring_n => left _ (refl_equal _) 
     | _ => right _ I
     end
   | Bitstring_k0 =>
     match y as y0 return {Bitstring_k0 = y0} + {True} with 
     | Bitstring_k0 => left _ (refl_equal _) 
     | _ => right _ I
     end
   | Bitstring_k1 =>
     match y as y0 return {Bitstring_k1 = y0} + {True} with 
     | Bitstring_k1 => left _ (refl_equal _) 
     | _ => right _ I
     end
   end.

  Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
  Proof.
   destruct x; destruct y; simpl; intros; discriminate.
  Qed.

  Import TP.

  Definition len k (t0:t) := 
   match t0 with
   | Bitstring_n   => n k
   | Bitstring_k0  => k0 k
   | Bitstring_k1  => k1 k
   end.

  Definition interp k (t0:t) := 
   Bvector (len k t0).

  Definition size k (t0:t) (_:interp k t0) := 
   S (len k t0).

  Definition default k (t0:t) : interp k t0 := 
   Bvect_false (len k t0).

  Definition default_poly (t0:t) := 
   pplus (pcst 1) pvar.

  Lemma size_positive : forall k (t0:t) x, 0 < @size k t0 x.
  Proof.
   intros k t0 x; unfold size; auto with arith.
  Qed.

  Lemma len_le : forall k t0, len k t0 <= k.
  Proof.
   intros k; assert (W:=k_spec k); destruct t0; simpl; omega.
  Qed.

  Lemma default_poly_spec : forall k (t0:t), 
   @size k t0 (default k t0) <= peval (default_poly t0) k.
  Proof.
   intros k t0.
   unfold size, default, default_poly.
   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
   simpl; apply le_n_S; apply len_le.
  Qed.

  Definition i_eqb k t (x1 x2:interp k t) := Veqb x1 x2.

  Lemma i_eqb_spec : forall k t (x y:interp k t), 
   if i_eqb x y then x = y else x <> y.
  Proof.
   intros; refine (Veqb_spec _ _).
  Qed.

 End Ut.

 Module T := MakeType Ut.


 Inductive usupport_ (Ut:Type) (Ttype:Type) (Tuser:Ut -> Ttype): Ttype -> Type :=
 | Usupport : forall t, usupport_ Tuser (Tuser t).

 Module US <: USUPPORT Ut T.

  Definition usupport := usupport_ T.User.

  Definition eval k t (s:usupport t) : list (T.interp k t) :=
   match s in usupport_ _ t0 return list (T.interp k t0) with
   | Usupport bst => bs_support (Ut.len k bst)
   end.

  Definition ceval k t (s:usupport t) : list (T.interp k t) * nat :=
   (eval k s, 1%nat).

  Lemma eval_usupport_nil : forall k t (s:usupport t), eval k s <> nil.
  Proof.
   destruct s; refine (@bs_support_not_nil _).
  Qed.

  Lemma ceval_spec : forall k t (s:usupport t), eval k s = fst (ceval k s).
  Proof. 
   trivial. 
  Qed.

  Definition eqb (t1 t2:T.type) (s1:usupport t1) (s2:usupport t2) : bool :=
   T.eqb t1 t2.

  Lemma eqb_spec_dep : forall t1 (e1 : usupport t1) t2 (e2:usupport t2),
   if eqb e1 e2 then eq_dep T.type usupport t1 e1 t2 e2
   else ~eq_dep T.type usupport t1 e1 t2 e2.
  Proof.
   intros.
   destruct e1; destruct e2; unfold eqb.
   generalize (T.eqb_spec (T.User t) (T.User t0));
    destruct (T.eqb (T.User t) (T.User t0)); intros.
   injection H; clear H; intros; subst; trivial.
   intros Heq; apply H; inversion Heq; trivial.
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


 Inductive Uop : Type :=
 | Oapp_f : Uop
 | Oapp_f_inv : Uop
 | OqG : Uop
 | OqH : Uop
 | OqD : Uop 
 | Oxor : Ut.t -> Uop
 | Ozero : Uop
 | Oone : Uop.

 Module UOp <: UOP Ut T.

  Definition t := Uop.

  Definition eqb (o1 o2:t) : bool := 
   match o1, o2 with
   | Oapp_f, Oapp_f
   | Oapp_f_inv, Oapp_f_inv
   | OqG, OqG
   | OqH, OqH 
   | OqD, OqD
   | Ozero, Ozero => true
   | Oone, Oone => true
   | Oxor t1, Oxor t2 => Ut.eqb t1 t2 
   | _, _ => false
   end.

   Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
   Proof.
    intros x y; case x; case y; simpl; trivial; intros;
    try (intro; discriminate).
    generalize (Ut.eqb_spec t1 t0); destruct (Ut.eqb t1 t0); intros.
    rewrite H; trivial.
    intro H1; apply H; inversion H1; trivial.
   Qed.

   Definition Tnk1 := T.Pair (T.User Bitstring_n) (T.User Bitstring_k1).
   Definition Tk := T.Pair Tnk1 (T.User Bitstring_k0).

   Definition targs (op:t) : list T.type :=
    match op with
    | Oapp_f => Tk :: nil
    | Oapp_f_inv => Tk :: nil
    | OqG | OqH | OqD | Ozero | Oone => nil
    | Oxor t => T.User t :: T.User t :: nil
    end.

   Definition tres (op:t) : T.type :=
    match op with 
    | Oapp_f => Tk
    | Oapp_f_inv => Tk
    | OqG | OqH | OqD => T.Nat
    | Ozero => T.User Bitstring_k1
    | Oone => T.User Bitstring_n
    | Oxor t => T.User t
    end.

   Import TP.

   Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
    match op as op0 return T.type_op k (targs op0) (tres op0) with 
    | Oapp_f => @f k
    | Oapp_f_inv => @finv k
    | OqG => peval qG_poly k
    | OqH => peval qH_poly k
    | OqD => peval qD_poly k
    | Oxor t => BVxor (Ut.len k t)
    | Ozero => Bvect_false (k1 k)
    | Oone => Bvect_true (n k)
    end.

   Implicit Arguments interp_op [k].

   Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
    match op as op0 return T.ctype_op k (targs op0) (tres op0) with
    | Oapp_f => fun v => (@f k v, peval cost_f k)
    | Oapp_f_inv => fun v => (@finv k v, cost_finv k)
    | OqG => (peval qG_poly k, 1)
    | OqH => (peval qH_poly k, 1)
    | OqD => (peval qD_poly k, 1)
    | Oxor t => fun v1 v2 => (BVxor (Ut.len k t) v1 v2, Ut.len k t)
    | Ozero => (Bvect_false (k1 k), 1)
    | Oone => (Bvect_true (n k), 1)
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
    T.dlist_inversion args; rewrite Heq; trivial.
   Qed.

 End UOp.

 Export TP.

 (** Semantics with optimizations *)
 Module SemO <: SEM_OPT.

  Module Sem := MakeSem.Make Ut T UOp US.
  Import Sem.

  (* The trapdoor permutation and its inverse *)
  Notation "'{0,1}^k0'" := (E.Duser (Usupport T.User Bitstring_k0)).
  Notation "'{0,1}^n'" := (E.Duser (Usupport T.User Bitstring_n)).
  Notation "'{0,1}^k1'" := (E.Duser (Usupport T.User Bitstring_k1)).

  Notation " x '|x|' y " := (E.Eop (O.Ouser (Oxor _)) {x, y}) (at level 50, left associativity).
  Notation "'ap_f' x" := (E.Eop (O.Ouser Oapp_f) {x}) (at level 40).
  Notation "'ap_finv' x" := (E.Eop (O.Ouser Oapp_f_inv) {x}) (at level 40).
  Notation "'qG'" := (E.Eop (O.Ouser OqG) (dnil _)).
  Notation "'qH'" := (E.Eop (O.Ouser OqH) (dnil _)).   
  Notation "'qD'" := (E.Eop (O.Ouser OqD) (dnil _)).
  Notation zero_k1 := (E.Eop (O.Ouser Ozero) (dnil _)).
  Notation one_n := (E.Eop (O.Ouser Oone) (dnil _)).
 
  Definition simpl_op (op:Uop.t) (args:E.args (Uop.targs op)) :=
   E.Eop (O.Ouser op) args.

  Implicit Arguments simpl_op [].

  Lemma simpl_op_spec : forall k op args (m:Mem.t k),
   E.eval_expr (simpl_op op args) m = E.eval_expr (E.Eop (O.Ouser op) args) m.
  Proof. 
   trivial.
  Qed.

 End SemO.
  
 Module BP := BaseProp.Make SemO.Sem.
  
 Module Uppt.

  Import BP.
  Import SemO.
   
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
    forall k, UT.size (UT.default k ut) <= peval (utsize_default_poly r) k.
   Proof.
    intros r ut _ k.
    simpl.
    unfold UT.default, UT.size, utsize_default_poly. 
    rewrite pplus_spec, pcst_spec, pvar_spec; trivial. 
    simpl; apply le_n_S; apply Ut.len_le.
   Qed.

   Definition uop_poly (o:Uop.t) : bool := 
    match o with 
    | Oapp_f_inv => false 
    | _ => true 
    end.

   Lemma uop_poly_spec : forall o (la:dlist E.expr (O.targs (O.Ouser o))),
    uop_poly o ->
    (forall t (e:E.expr t), @DIn _ E.expr _ e _ la -> 
     exists F, exists G, PPT_expr e F G) ->
    exists F, exists G, PPT_expr (E.Eop (O.Ouser o) la) F G.
   Proof.
    intros o la H Hla.
    destruct o; simpl.

    (* Oapp_f *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    exists (fun _ => pplus (pcst 5) pvar).
    exists (fun p => pplus (cost_f) (G1 p)). 
    simpl; split.
    unfold T.size, UT.size, UOp.Tk, UOp.Tnk1; rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
    simpl;assert (W:= k_spec k);omega.
    simpl; rewrite pplus_spec.
    generalize (H1 k m p); clear H1.
    case_eq (E.ceval_expr x m); simpl.
    intros i n0 Heqi Hi.
    destruct Hi.
    intros; apply H0; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].
    unfold fv_expr; simpl; auto with set.
    rewrite plus_0_r; trivial.
    omega.

    discriminate H.

    (* OqG *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    exists (fun _ => pplus (pcst 1) qG_poly).
    exists (fun _ => pcst 1). 
    simpl; split.
    rewrite pplus_spec, pcst_spec; case (peval qG_poly k).
    trivial.
    intro n0; apply le_trans with (S n0); [apply size_nat_le | ]; auto with arith.
    rewrite pcst_spec; trivial.

    (* OqH *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    exists (fun _ => pplus (pcst 1) qH_poly).
    exists (fun _ => pcst 1). 
    simpl; split.
    rewrite pplus_spec, pcst_spec; case (peval qH_poly k).
    trivial.
    intro n0; apply le_trans with (S n0); [apply size_nat_le | ]; auto with arith.
    rewrite pcst_spec; trivial.

    (* OqD *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    exists (fun _ => pplus (pcst 1) qD_poly).
    exists (fun _ => pcst 1). 
    simpl; split.
    rewrite pplus_spec, pcst_spec; case (peval qD_poly k).
    trivial.
    intro n0; apply le_trans with (S n0); [apply size_nat_le | ]; auto with arith.
    rewrite pcst_spec; trivial.

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
    exact (UT.default_poly_spec k t).

    generalize (H1 k m p) (H2 k m p); clear H1 H2.
    simpl.
    case_eq (E.ceval_expr x m); simpl.
    case_eq (E.ceval_expr x0 m); simpl.
    intros i n1 Heqi i0 n0 Heqi0 Hi Hi0.
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
    apply le_trans with k.
    exact (Ut.len_le k t).
    auto with arith.
    rewrite plus_0_r; apply plus_le_compat; trivial.
 
    (* Ozero *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    exists (fun _ => pplus (pcst 1) pvar).
    exists (fun _ => pcst 1). 
    simpl; split.
    rewrite pplus_spec, pcst_spec.
    trivial.
    rewrite pvar_spec.
    unfold T.size, Ut.size; simpl.
    apply le_n_S.
    rewrite k_spec; omega.
    rewrite pcst_spec; trivial.

    (* Oone *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    exists (fun _ => pplus (pcst 1) pvar).
    exists (fun _ => pcst 1). 
    simpl; split.
    rewrite pplus_spec, pcst_spec.
    trivial.
    rewrite pvar_spec.
    unfold T.size, Ut.size; simpl.
    apply le_n_S.
    rewrite k_spec; omega.
    rewrite pcst_spec; trivial.
   Qed.

   Definition usupport_poly t (us:US.usupport t) : bool :=
    match us with 
    | Usupport _ => true
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
    intros; exact (UT.default_poly_spec k t).
    rewrite pcst_spec; trivial. 
   Qed.

 End Uppt.

End Entries.

Declare Module TP : TRAPDOOR_PERM.
Module Ent := Entries TP.

Module Tactics := BuildTac2.Make Ent.
Export Tactics.
