(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * FDHsem.v : Semantics with bitstrings, a trapdoor permutation and its inverse *)

Set Implicit Arguments.

Require Export PPT.
Require Export BuildTac.
Require Export Bitstrings.


Inductive Bt : Type := 
| Bitstring.

(** * User-defined type module for bitstrings *)
Module UT <: UTYPE.

 Definition t := Bt. 

 Definition eqb (_ _:t) := true.

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  intros x y; case x; case y; simpl; trivial.
 Qed.

 Definition eq_dec (x y:t) : {x = y} + {True} :=
  match x as x0 return {x0 = y} + {True} with
  | Bitstring => 
    match y as y0 return {Bitstring= y0} + {True} with 
     Bitstring => left _ (refl_equal _) 
    end
  end.

 Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
 Proof.
  intros x y; case x; case y; simpl; intros; discriminate.
 Qed.
 
 Definition interp k (_:t) := Bvector k.

 Definition size k (t0:t) (_:interp k t0) := S k.

 Definition default k (t0:t) : interp k t0 := Bvect_false k.

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

 Definition i_eqb k t (x1 x2:interp k t) : bool := Veqb x1 x2.

 Lemma i_eqb_spec : forall k t (x y:interp k t), 
  if i_eqb x y then x = y else x <> y.
 Proof.
  intros; unfold i_eqb; refine (Veqb_spec _ _).
 Qed.

End UT.

Module T := MakeType UT.

Inductive usupport_ (Ttype : Type) (Tuser : Bt -> Ttype) : Ttype -> Type :=
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


Module Type TRAPDOOR_PERM.

 (** * Trapdoor permutation and its inverse *)
 Parameter ap_f    : forall k (x:Bvector k), Bvector k.
 Parameter ap_finv : forall k (x:Bvector k), Bvector k.

 Parameter cost_f : polynomial.
 Parameter cost_finv : nat -> nat.

 Parameter f_perm :  forall k, PermutP (@eq _) (bs_support k) (map (@ap_f k) (bs_support k)).
 Parameter f_spec : forall k (x:Bvector k), x = ap_finv (ap_f x).

 (* Maximum number of queries made to the hash oracle, minus one *)
 Parameter q_poly : polynomial.

End TRAPDOOR_PERM. 


Module Entries (TDP:TRAPDOOR_PERM).

 Export TDP.

 Lemma finv_spec : forall k (x:Bvector k), x = ap_f (ap_finv x).
 Proof.
  intros; symmetry; apply f_inv_spec_bs.
  apply f_perm.
  intro v; symmetry; apply (f_spec v).
 Qed.

 Lemma f_inj : forall k (x y:Bvector k), ap_f x = ap_f y -> x = y.
 Proof.
  intros.
  rewrite (f_spec x), (f_spec y), H; trivial.
 Qed.

 Lemma f_inj_Veqb : forall k (x y:Bvector k), Veqb (ap_f x) (ap_f y) = Veqb x y.
 Proof.
  intros.
  case_eq (Veqb x y); intro H1.
  apply Veqb_true in H1; rewrite H1; apply Veqb_refl.
  case_eq (Veqb (ap_f x) (ap_f y)); intro H2.
  apply Veqb_true in H2; apply f_inj in H2.
  rewrite <- H1, H2; symmetry; apply Veqb_refl.
  trivial.
 Qed.


 Inductive perm_op : Type :=
  | Oq
  | Of
  | Ofinv.

 (** Add [f] and [finv] and [q] as operators in the language *)
 Module Uop <: UOP UT T.

 Definition t := perm_op.
 
 Definition eqb (o1 o2:t) : bool :=
  match o1, o2 with
  | Of, Of | Ofinv, Ofinv | Oq, Oq => true
  | _, _ => false
  end.

 Lemma eqb_spec :  forall x y, if eqb x y then x = y else x <> y.
 Proof.
  intros x y; case x; case y; simpl; trivial; intro; discriminate.
 Qed.

 Definition targs (o:t) : list T.type :=
  match o with 
  | Oq => nil
  | Of | Ofinv => T.User Bitstring :: nil
  end.

 Definition tres (o:t) := 
  match o with 
  | Oq => T.Nat
  | _ => T.User Bitstring
  end.
 
 Definition interp_op k op : T.type_op k (targs op) (tres op) :=
  match op as o return T.type_op k (targs o) (tres o) with
  | Oq => peval q_poly k
  | Of => @ap_f k
  | Ofinv => @ap_finv k
  end.

 Definition cinterp_op k op : T.ctype_op k (targs op) (tres op) :=
  match op as o return T.ctype_op k (targs o) (tres o) with
  | Oq => (peval q_poly k, 1%nat)
  | Of => fun x => (@ap_f k x, peval cost_f k)
  | Ofinv => fun x => (@ap_finv k x, cost_finv k)
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
  intros k o; case o; intro args; simpl in args;
  T.dlist_inversion args; rewrite Heq; trivial.
 Qed.

 Implicit Arguments interp_op [k].
 Implicit Arguments cinterp_op [k].

 End Uop.


 (** Semantics with optimizations *)
 Module SemO <: SEM_OPT.

  Module Sem := MakeSem.Make UT T Uop US.
  Export Sem.
  
  (* Bottom *)
  Notation "'bottom'" := (E.Eop (O.Ohd _) {Nil (T.User Bitstring) }) (at level 50).

  (* The trapdoor permutation and its inverse *)
  Notation "'apply_f' x" := (E.Eop (O.Ouser Of) {x}) (at level 40).
  Notation "'apply_finv' y" := (E.Eop (O.Ouser Ofinv) {y}) (at level 40).

  (* Maximum number of queries to the hash oracle, minus one *)
  Notation "'q'" := (E.Eop (O.Ouser Oq) (dnil E.expr)).

  (* Uniform sampling of bitstrings of fixed length (the security parameter) *)
  Notation "'{0,1}^k'" := (E.Duser (Usupport T.User)).

  (* Some infinite type (bitstrings in the literature) *)
  Notation Msg := T.Nat.


  (** Simplifies [f (finv x)] to [x] *)
  Definition simpl_op (op : Uop.t) : E.args (Uop.targs op) -> 
   E.expr (Uop.tres op) :=
   match op as op0 return E.args (Uop.targs op0) -> E.expr (Uop.tres op0) with
   | Of => fun args => 
    E.app_expr (T.User Bitstring) args 
    (fun (e:E.expr (T.User Bitstring)) =>
     match E.get_uop e with
     | Some (existT uop args) =>
       match uop as uop0 
       return E.args (Uop.targs uop0) -> E.expr (T.User Bitstring) with
       | Ofinv =>
         fun args => 
          E.app_expr (T.User Bitstring) args (fun e1:E.expr (T.User Bitstring) => e1)
       | _ => fun _ => apply_f e
       end args
     | None => apply_f e
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
   exact (finv_spec (E.eval_expr x0 m)).
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
   forall k, UT.size (UT.default k ut) <= peval (utsize_default_poly r) k.
  Proof.
   intros r ut _ k.
   case ut; simpl.
   unfold UT.size, utsize_default_poly. 
   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.  
  Qed.

  Definition uop_poly (o:Uop.t) : bool :=
   match o with
   | Of | Oq => true
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

   (* Oq *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   exists (fun _ => pplus (pcst 1) q_poly).
   exists (fun _ => pcst 1). 
   simpl; split.
   rewrite pplus_spec, pcst_spec; case (peval q_poly k).
   trivial.
   intro n; apply le_trans with (S n); [apply size_nat_le | ]; auto with arith.
   rewrite pcst_spec; trivial.

   (* Of *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [G1 H1] ].
   left; trivial.
   exists (fun _ => pplus (pcst 1) pvar).
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

   discriminate.
  Qed.

  Definition usupport_poly t (us:US.usupport t) : bool :=
   match us with 
   | Dbitstring => true
   end. 

  Lemma usupport_poly_spec : forall t (us:US.usupport t),
   usupport_poly us ->
   exists F, exists G, PPT_support (E.Duser us) F G.
  Proof.
   intros t us; case us; intros _.
   exists (fun _ => pplus (pcst 1) pvar).
   exists (fun _ => pcst 1).
   intros k m p Hm.
   simpl; split.
   intros; unfold UT.size; rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
   rewrite pcst_spec; trivial. 
  Qed.

 End Uppt.

End Entries.


Declare Module TDP : TRAPDOOR_PERM.

Module Entries_TDP := Entries TDP.

Module Tactics := BuildTac.Make Entries_TDP.
Export Tactics.
