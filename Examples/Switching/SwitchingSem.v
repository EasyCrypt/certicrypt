(** * SwitchingSem.v : Semantics with bitstrings of length [k] *)

Set Implicit Arguments.

Require Import PPT.
Require Export BuildTac.
Require Export Bitstrings.


Module Type SwEntries.

 Parameter q_poly : polynomial.

End SwEntries.


Inductive Bt : Type := BS_k. 

Inductive uop : Set := Oq.


Module Make (SWE:SwEntries).

 Export SWE.

 (** * User-defined type module for bitstrings *)
 Module UT <: UTYPE.

  Definition t := Bt. 

  Definition eqb (x y:t) := true.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   intros x y; case x; case y; simpl; trivial.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {True} :=
   match x as x0 return {x0 = y} + {True} with
   | BS_k=> 
     match y as y0 return {BS_k= y0} + {True} with 
     | BS_k=> left _ (refl_equal _) 
     end
   end.

  Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
  Proof.
   intros x y; case x; case y; simpl; intros; discriminate.
  Qed.

  Definition length k (t0:t) : nat := 
   match t0 with
   | BS_k => k 
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

  Lemma length_le : forall k t0, (length k t0 <= k)%nat.
  Proof.
   intros k; destruct t0; simpl; omega.
  Qed.

  Lemma default_poly_spec : forall k (t0:t),
   (size (default k t0) <= (default_poly t0) k)%nat.
  Proof.
   intros k t0.
   unfold size, default, default_poly.
   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
   simpl; apply le_n_S.
   assert (W:=length_le k t0); auto with arith.
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
   destruct t; destruct t0; trivial.
   elim H; destruct t; destruct t0; trivial.
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

 (** * Module for user-defined bitstring operators *)
 Module Uop (T:TYPE UT) <: UOP UT T.

  Definition t := uop.

  Definition eqb (o1 o2 : t) : bool := true.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   intros; destruct x; destruct y; simpl; trivial.
  Qed.

  Definition targs (op : t) : list T.type :=nil.

  Definition tres (op: t) : T.type :=
   match op with 
   | Oq => T.Nat 
   end.

  Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
   match op as op0 return T.type_op k (targs op0) (tres op0) with 
   | Oq => q_poly k 
   end.

  Implicit Arguments interp_op [k].

  Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
   match op as op0 return T.ctype_op k (targs op0) (tres op0) with
   | Oq => (q_poly k, 1%nat)
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
   
   Module Uop_ := Uop T.

   Module Sem := MakeSem.Make UT T Uop_ US.
   Export Sem.

   Notation "'{0,1}^k'" := (E.Duser (Usupport T.User BS_k)).
   Notation q := (E.Eop (O.Ouser Oq) (dnil _)).

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

   Open Scope nat_scope.

   (** PPT expression *)
   Definition PPT_expr (t:T.type) (e:E.expr t) 
   (F:polynomial -> polynomial) 
   (G:polynomial -> polynomial) : Prop :=
   forall k (m:Mem.t k) (p:polynomial),
    (forall t (x:Var.var t), 
     BP.Vset.mem x (BP.fv_expr e) -> T.size (m x) <= p k)  ->
    let (v,n) := E.ceval_expr e m in
     T.size v <= (F p) k /\
     n <= (G p) k.

   (** PPT support *)
   Definition PPT_support t (s:E.support t)
   (F:polynomial -> polynomial) 
   (G:polynomial -> polynomial) : Prop :=
   forall k (m:Mem.t k) (p:polynomial),
    (forall t (x:Var.var t), 
     BP.Vset.mem x (BP.fv_distr s) -> T.size (m x) <= p k)  ->
    let (l,n) := E.ceval_support s m in
     (forall v, In v l -> T.size v <= (F p) k) /\
     n <= (G p) k.

   Definition utsize : UT.t -> nat := fun _ => 1.

   Definition utsize_default_poly : nat -> polynomial :=
    fun _ => pplus (pcst 2) pvar.

   Lemma utsize_default_poly_spec : forall r ut,
    utsize ut <= r -> 
    forall k, UT.size (UT.default k ut) <= (utsize_default_poly r) k.
   Proof.
    intros r ut _ k.
    simpl.
    unfold UT.default, UT.size, utsize_default_poly. 
    rewrite pplus_spec, pcst_spec, pvar_spec; trivial. 
    simpl; apply le_n_S.
    assert (W:= UT.length_le k ut); auto with arith.
   Qed.

   Definition uop_poly (o:Uop.t) : bool := true.

   Lemma uop_poly_spec : forall o (la:dlist E.expr (O.targs (O.Ouser o))),
    uop_poly o ->
    (forall t (e:E.expr t), @DIn _ E.expr _ e _ la -> 
     exists F, exists G, PPT_expr e F G) ->
    exists F, exists G, PPT_expr (E.Eop (O.Ouser o) la) F G.
   Proof.
    intros; destruct o.
    T.dlist_inversion la.
    rewrite Heq in H0 |- *.
    exists (fun _ => pplus (pcst 1) q_poly).
    exists (fun _ => pcst 1).   
    simpl; split.
    rewrite pplus_spec, pcst_spec.
    simpl; destruct (q_poly k).
    simpl; trivial.
    assert (W:= @size_nat_le (S n)); omega.
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


Declare Module SWE : SwEntries.
Module Sem := Make SWE.
Export Sem.

Notation "'Elength' p" := (E.Eop (O.Olength _) { p }) (at level 0).
Notation "x '<!' y" := (E.Eop O.Olt {x, y})%nat (at level 50).
Notation "'Ehd' p" := (E.Eop (O.Ohd _) { p }) (at level 0).
Notation "'Etl' p" := (E.Eop (O.Otl _) { p }) (at level 0).
Notation "'Enth' p" := (E.Eop (O.Onth _) { p }) (at level 0).
Notation "l1 '|++|' l2" := (E.Eop (O.Oappend _) { l1, l2 }) (right associativity, at level 60).
