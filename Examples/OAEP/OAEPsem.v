(** * OAEPsem.v : Semantics with bitstrings of length [k], [p] and [k-p] *)

Set Implicit Arguments.

Require Export PPT.
Require Export BuildTac.
Require Export Bitstrings.

Open Scope nat_scope.


Inductive Bt : Type := 
| BS_kmp (* length = S (k - p) *)
| BS_p   (* length = p *)
| BS_k.  (* length = S k *)

Module Type OAEP_ENTRIES.

 Parameter k_p : nat -> nat.
 Parameter k_kmp : nat -> nat.
 Parameter k_kmp_p : forall k, (S k = S (k_kmp k) + k_p k)%nat.

 Definition K k := S (k_kmp k) + k_p k.

 (** * Trapdoor permutation and its inverse *)
 Parameter f     : forall k (x:Bvector (K k)), Bvector (K k).
 Parameter f_inv : forall k (x:Bvector (K k)), Bvector (K k).

 Parameter cost_f : polynomial.
 Parameter cost_f_inv :  nat -> nat.
 Parameter f_spec : forall k (x:Bvector (K k)), f_inv (f x) = x.

 Parameter f_inv_spec : forall k (x:Bvector (K k)), f (f_inv x) = x.

 (** Numbers of queries to G and H oracles *)
 Parameter qG_poly qH_poly : polynomial.

End OAEP_ENTRIES.


Module Make (ENT:OAEP_ENTRIES).

 Export ENT.

 Lemma p_lt_k : forall k, (k_p k < S k)%nat.
 Proof.
  intros.
  generalize (k_kmp_p k); omega.   
 Qed.

 Lemma f_inj : forall k x y, @f k x = f y -> x = y.
 Proof.
  intros.
  rewrite <- (f_spec x), <- (f_spec y), H; trivial.
 Qed.

 (** * User-defined type module for bitstrings *)
 Module UT <: UTYPE.

  Definition t := Bt. 

  Definition eqb (x y:t) := 
   match x, y with
   | BS_kmp, BS_kmp | BS_p, BS_p | BS_k, BS_k => true
   | _, _ => false
   end.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   intros x y; case x; case y; simpl; trivial;
   intro; discriminate.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {True} :=
   match x as x0 return {x0 = y} + {True} with
   | BS_kmp=> 
     match y as y0 return {BS_kmp= y0} + {True} with 
     | BS_kmp=> left _ (refl_equal _) 
     | _ => right _ I
     end
   | BS_p=> 
     match y as y0 return {BS_p= y0} + {True} with 
     | BS_p=> left _ (refl_equal _) 
     | _ => right _ I
     end
   | BS_k=> 
     match y as y0 return {BS_k= y0} + {True} with 
     | BS_k=> left _ (refl_equal _) 
     | _ => right _ I
     end
   end.

  Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
  Proof.
   intros x y; case x; case y; simpl; intros; discriminate.
  Qed.

  Definition length k (t0:t) : nat := 
   match t0 with
   | BS_kmp => S (k_kmp k)
   | BS_p => k_p k
   | BS_k => (S (k_kmp k) + k_p k)%nat
   end.

  Definition interp k (t0:t) := Bvector (length k t0).

  Definition size k t0 (b:interp k t0) := S (length k t0).

  Definition default k (t0:t) : interp k t0 := Bvect_false (length k t0).

  Definition default_poly (t0:t) := pplus (pcst 2) pvar.

  Lemma size_positive : forall k t0 (x:interp k t0), (0 < size x)%nat.
  Proof.
   intros k t0 x.
   unfold size; auto with arith.
  Qed.

  Lemma length_le : forall k t0, (length k t0 <= S k)%nat.
  Proof.
   intros k; assert (W:= k_kmp_p k); destruct t0; simpl; omega.
  Qed.

  Lemma default_poly_spec : forall k (t0:t),
   (size (default k t0) <= peval (default_poly t0) k)%nat.
  Proof.
   intros k t0.
   unfold size, default, default_poly.
   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
   simpl; apply le_n_S; apply length_le.
  Qed.

  Definition i_eqb k t (x1 x2:interp k t) : bool := Veqb x1 x2.

  Lemma i_eqb_spec : forall k t (x y:interp k t), 
   if i_eqb x y then x = y else x <> y.
  Proof.
   intros k t0 x y; exact (Veqb_spec x y).
  Qed.

 End UT.

 Module T := MakeType UT.

 Inductive usupport_  (Ttype : Type) (Tuser : Bt -> Ttype): Ttype -> Type :=
 | Usupport : forall t, usupport_ Tuser (Tuser t).

 (** * User-defined random sampling for bitstrings *)
 Module US <: USUPPORT UT T.

  Definition usupport := usupport_ T.User.

  Definition eval k t (s:usupport t) : list (T.interp k t) :=
   match s in usupport_ _ t0 return list (T.interp k t0) with
   | Usupport bst => bs_support (UT.length k bst)
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

  Lemma eqb_spec_dep :  forall t1 (e1 : usupport t1) t2 (e2:usupport t2),
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


 Inductive Bop : Type :=
 | Oxor_bs : UT.t -> Bop
 | Oappend_bs : Bop
 | Oapp_f : Bop
 | Oapp_f_inv : Bop
 | OqG : Bop
 | OqH : Bop.

 (** * Module for user-defined bitstring operators *)
 Module Uop <: UOP UT T.

  Definition t := Bop.

  Definition eqb (o1 o2 : t) : bool := 
   match o1, o2 with
   | Oxor_bs t1, Oxor_bs t2 => UT.eqb t1 t2
   | Oappend_bs, Oappend_bs 
   | Oapp_f, Oapp_f
   | Oapp_f_inv, Oapp_f_inv
   | OqG, OqG
   | OqH, OqH => true
   | _, _ => false
   end.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   intros x y; case x; case y; simpl; trivial; intros;
   try (intro; discriminate).
   generalize (UT.eqb_spec t1 t0); destruct(UT.eqb t1 t0); intros.
   rewrite H; trivial.
   intro H1; apply H; inversion H1; trivial.
  Qed.

  Definition targs (op : t) : list T.type :=
   match op with
   | Oxor_bs t => T.User t :: T.User t :: nil
   | Oappend_bs => T.User BS_kmp :: T.User BS_p :: nil
   | Oapp_f => T.User BS_k :: nil
   | Oapp_f_inv => T.User BS_k :: nil
   | OqG | OqH => nil
   end.

  Definition tres (op: t) : T.type :=
   match op with 
   | Oxor_bs t => T.User t
   | Oappend_bs | Oapp_f | Oapp_f_inv => T.User BS_k
   | OqG | OqH => T.Nat
   end.

  Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
   match op as op0 return T.type_op k (targs op0) (tres op0) with 
   | Oxor_bs t => BVxor (UT.length k t)
   | Oappend_bs => Vextend bool (UT.length k BS_kmp) (UT.length k BS_p)
   | Oapp_f => @f k
   | Oapp_f_inv => @f_inv k
   | OqG => peval qG_poly k
   | OqH => peval qH_poly k
   end.

  Implicit Arguments interp_op [k].

  Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
   match op as op0 return T.ctype_op k (targs op0) (tres op0) with
   | Oxor_bs t => 
     fun x1 x2 => 
      (BVxor (UT.length k t) x1 x2, UT.length k t)
   | Oappend_bs => 
     fun x1 x2 =>
      (Vextend bool (UT.length k BS_kmp) (UT.length k BS_p) x1 x2,
       UT.length k BS_k)
   | Oapp_f =>fun x => (@f k x, peval cost_f k)
   | Oapp_f_inv => fun x => (@f_inv k x, cost_f_inv k)
   | OqG => (peval qG_poly k, 1)
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
   T.dlist_inversion args; rewrite Heq; trivial.
  Qed.

 End Uop.


 (** Semantics with optimizations *)
 Module Entries. 

  Module SemO <: SEM_OPT.

   Module Sem := MakeSem.Make UT T Uop US.
   Export Sem.

   Notation "'{0,1}^k'" := (E.Duser (Usupport T.User BS_k)).
   Notation "'{0,1}^k-p'" := (E.Duser (Usupport T.User BS_kmp)).
   Notation "'{0,1}^p'" := (E.Duser (Usupport T.User BS_p)).
  
   Notation " x '|x|' y " := (E.Eop (O.Ouser (Oxor_bs _)) {x, y}) (at level 50, left associativity).
   Notation " x '@' y " := (E.Eop (O.Ouser Oappend_bs) {x, y}).
   Notation "'apply_f' x" := (E.Eop (O.Ouser Oapp_f) {x}) (at level 40).
   Notation "'apply_finv' x" := (E.Eop (O.Ouser Oapp_f_inv) {x}) (at level 40).
   Notation "'qG'" := (E.Eop (O.Ouser OqG) (dnil _)).
   Notation "'qH'" := (E.Eop (O.Ouser OqH) (dnil _)).

   (** Simplifies [f (finv x)] to [x] *)
   Definition simpl_op (op : Uop.t) (args : E.args (Uop.targs op)) :=
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
    fun _ => pplus (pcst 2) pvar.

   Lemma utsize_default_poly_spec : forall r ut,
    utsize ut <= r -> 
    forall k, UT.size (UT.default k ut) <= peval (utsize_default_poly r) k.
   Proof.
    intros r ut _ k.
    simpl.
    unfold UT.default, UT.size, utsize_default_poly. 
    rewrite pplus_spec, pcst_spec, pvar_spec; trivial. 
    simpl; apply le_n_S; apply UT.length_le.
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

    (* Oxor *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    destruct (Hla _ x0) as [F2 [G2 H2] ].
    right; left; trivial.
    exists (fun _ => pplus (pcst 2) pvar).
    exists (fun p => pplus (pplus (pcst 1) pvar) (pplus (G1 p) (G2 p))).
    simpl; split.
    exact (UT.default_poly_spec k t).

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
    exact (UT.length_le k t).
    rewrite plus_0_r; apply plus_le_compat; trivial.
 
    (* Oappend *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    destruct (Hla _ x0) as [F2 [G2 H2] ].
    right; left; trivial.
    exists (fun _ => pplus (pcst 2) pvar).
    exists (fun p => pplus (pplus (pcst 1) pvar) (pplus (G1 p) (G2 p))).
    simpl; split.
    exact (UT.default_poly_spec k BS_k).

    rewrite pplus_spec, pplus_spec, pplus_spec,  pcst_spec, pvar_spec.    
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

    apply le_n_S.
    apply plus_le_compat; auto.  
    apply le_S_n; rewrite (k_kmp_p k); trivial. 
    rewrite plus_0_r; apply plus_le_compat; trivial.

    (* Oapp_f *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    exists (fun _ => pplus (pcst 2) pvar).
    exists (fun p => pplus (cost_f) (G1 p)). 
    simpl; split.
    unfold T.size, UT.size; rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
    apply le_n_S.
    exact (UT.length_le k BS_k).

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

    discriminate H.

    (* OqG *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    exists (fun _ => pplus (pcst 1) qG_poly).
    exists (fun _ => pcst 1). 
    simpl; split.
    rewrite pplus_spec, pcst_spec; case (peval qG_poly k).
    trivial.
    intro n; apply le_trans with (S n); [apply size_nat_le | ]; auto with arith.
    rewrite pcst_spec; trivial.

    (* OqH *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    exists (fun _ => pplus (pcst 1) qH_poly).
    exists (fun _ => pcst 1). 
    simpl; split.
    rewrite pplus_spec, pcst_spec; case (peval qH_poly k).
    trivial.
    intro n; apply le_trans with (S n); [apply size_nat_le | ]; auto with arith.
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
    exists (fun _ => pplus (pcst 2) pvar).
    exists (fun _ => pcst 1).
    intros k m p Hm.
    simpl; split.
    intros; exact (UT.default_poly_spec k t).
    rewrite pcst_spec; trivial. 
   Qed.

  End Uppt.

 End Entries.

 Module Tactics := BuildTac.Make Entries.
 Export Tactics.

End Make.
