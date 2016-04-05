(** * ClawFree.v: Sigma protocols based on families of claw-free
 permutations *)

Require Import Sigma.
Require Import Bitstrings.
Require Import BuildTac.

Set Implicit Arguments.


(** A module type for families of claw-free trapdoor permutations *)
Module Type ClawFreeParameters.

 (* Domain, and space of public and secret keys *)
 Parameter D PK SK : nat -> Set.
 Parameter D_size : nat -> nat. 
 Parameter D_size_poly : polynomial.
 Parameter D_size_poly_spec : forall k, D_size k < peval D_size_poly k.
 
 Parameter D_elems : forall k, list (D k).
 Parameter D_elems_not_nil : forall k, D_elems k <> nil.
 Parameter D_elems_full : forall k (x:D k), In x (D_elems k).
 Parameter D_elems_nodup : forall k, NoDup (D_elems k).
 Parameter D_default : forall k, D k.
 Parameter D_eqb : forall k, D k -> D k -> bool.
 Parameter D_eqb_spec : forall k (x y:D k), if D_eqb x y then x = y else x <> y.

 Parameter PK_default : forall k, PK k.
 Parameter PK_eqb : forall k, PK k -> PK k -> bool.
 Parameter PK_eqb_spec : forall k (x y:PK k), if PK_eqb x y then x = y else x <> y.
 Parameter PK_size : nat -> nat.
 Parameter PK_size_poly : polynomial.
 Parameter PK_size_poly_spec : forall k, PK_size k < peval PK_size_poly k.
 
 Parameter SK_default : forall k, SK k.
 Parameter SK_eqb : forall k, SK k -> SK k -> bool.
 Parameter SK_eqb_spec : forall k (x y:SK k), if SK_eqb x y then x = y else x <> y.
 Parameter SK_size : nat -> nat.
 Parameter SK_size_poly : polynomial.
 Parameter SK_size_poly_spec : forall k, SK_size k < peval SK_size_poly k.
 
 (** Challenges -- bitstrings *)
 Parameter bs_size : nat -> nat.
 Parameter bs_size_poly : polynomial.
 Parameter bs_size_poly_spec : forall k, bs_size k < peval bs_size_poly k.
 
 (** The pair of permutations and their respective inverses *)
 Parameter f0    : forall k, PK k -> D k -> D k.
 Parameter f1    : forall k, PK k -> D k -> D k.
 Parameter f0inv : forall k, SK k -> D k -> D k.
 Parameter f1inv : forall k, SK k -> D k -> D k.
 
 Parameter cost_f0    : forall k (pk:PK k) (x:D k), nat.
 Parameter cost_f0inv : forall k (sk:SK k) (x:D k), nat.
 Parameter cost_f1    : forall k (pk:PK k) (x:D k), nat.
 Parameter cost_f1inv : forall k (sk:SK k) (x:D k), nat.
 
 Parameter cost_f0_poly    : polynomial.
 Parameter cost_f0inv_poly : polynomial.
 Parameter cost_f1_poly    : polynomial.
 Parameter cost_f1inv_poly : polynomial.
 
 Parameter cost_f0_poly_spec : forall k (pk:PK k) (x:D k),
  (cost_f0 pk x <= peval cost_f0_poly k) %nat.
 
 Parameter cost_f0inv_poly_spec : forall k (sk:SK k) (x:D k),
  (cost_f0inv sk x <= peval cost_f0inv_poly k) %nat.
 
 Parameter cost_f1_poly_spec : forall k (pk:PK k) (x:D k),
  (cost_f1 pk x <= peval cost_f1_poly k) %nat.
 
 Parameter cost_f1inv_poly_spec : forall k (sk:SK k) (x:D k),
  (cost_f1inv sk x <= peval cost_f1inv_poly k)%nat.

 (** The relation characterizing key pairs *) 
 Parameter R : forall k, PK k -> SK k -> Prop.
 Parameter R_dec : forall k (pk:PK k) (sk:SK k), {R pk sk} + {~R pk sk }.

 Parameter f0_spec    : forall k (sk:SK k) (pk:PK k), 
  R pk sk -> forall (x:D k), f0inv sk (f0 pk x) = x.
 Parameter f0inv_spec : forall k (sk:SK k) (pk:PK k), 
  R pk sk -> forall (x:D k), f0 pk (f0inv sk x) = x.
 Parameter f1_spec    : forall k (sk:SK k) (pk:PK k), 
  R pk sk -> forall (x : D k), f1inv sk (f1 pk x) = x.
 Parameter f1inv_spec : forall k (sk:SK k) (pk:PK k), 
  R pk sk -> forall (x:D k), f1 pk (f1inv sk x) = x.

End ClawFreeParameters.


(** Derived properties of families of claw-free trapdoor permutations *)
Module ClawFreeProperties (CFP:ClawFreeParameters).

 Import CFP.

 Lemma inj_f0 : forall k (x:PK k) (y:SK k) (a b:D k), 
  R x y -> f0 x a = f0 x b -> a = b.
 Proof.
  intros.
  rewrite <- (f0_spec H a), <- (f0_spec H b), H0; trivial.
 Qed.

 Lemma inj_f1 : forall k (x:PK k) (y:SK k) (a b:D k), 
  R x y -> f1 x a = f1 x b -> a = b.
 Proof.
  intros.   
  rewrite <- (f1_spec H a), <- (f1_spec H b), H0; trivial.
 Qed.

 (* Definition of [f_comp] *)
 Fixpoint vector_to_list (A:Set)(n:nat)(v:vector A n){struct v} : list A := 
  match v with 
  | Vnil => nil 
  | Vcons a p tl => cons a (@vector_to_list A p tl) 
  end.
 
 Definition f_comp_list k (pk:PK k) c (x:D k) : D k :=
  fold_right (fun (b:bool) acc => if b then f0 pk acc else f1 pk acc) x c.

 Definition f_comp k t (pk:PK k) (c:Bvector t) (x:D k) : D k := 
  f_comp_list pk (vector_to_list c) x.

 Definition finv_comp_list k (sk:SK k) c (x:D k) : D k :=
  fold_left (fun acc (b:bool) => if b then f0inv sk acc else f1inv sk acc) c x.
 
 Definition finv_comp k t (sk:SK k) (c:Bvector t) (x:D k) : D k := 
  finv_comp_list sk (vector_to_list c) x.
 
 Lemma simpl_f_comp : forall k t (sk:SK k) (pk:PK k) (x:D k) bv,
  R pk sk -> @f_comp k t pk bv (finv_comp sk bv x) = x.
 Proof.
  intros k t sk pk x bv HR.
  unfold f_comp, finv_comp, f_comp_list, finv_comp_list.
  rewrite <- fold_left_rev_right.
  rewrite <- fold_right_rev_left.
  induction (rev (vector_to_list bv)); simpl; trivial.
  case a; [rewrite f0inv_spec | rewrite f1inv_spec]; trivial.
 Qed.

 Lemma simpl_finv_comp : forall k t (sk:SK k) (pk:PK k) (x:D k) bv,
  R pk sk -> @finv_comp k t sk bv (f_comp pk bv x) = x.
 Proof.  
  intros k t sk pk x l HR.
  unfold f_comp, finv_comp, f_comp_list, finv_comp_list.
  induction (vector_to_list l); simpl; trivial.
  case a;[rewrite f0_spec | rewrite f1_spec]; trivial.
 Qed.

 Definition find_collision : forall k t (x:PK k) 
  (c c':Bvector (S t)) (s s':D k), (D k * D k).
 intros k t x c c' s s'.

 induction t.
 inversion_clear c.
 case_eq a; intro.
 exact (s, s').
 exact (s', s).

 inversion_clear c.
 inversion_clear c'.
 case_eq (eqb a a0); intro.
 apply (IHt H H0).
 
 case a.
 exact (f_comp x H s, f_comp x H0 s'). 
 exact (f_comp x H0 s', f_comp x H s).
 Defined.

 Lemma find_collision_spec : forall k t (x:PK k) 
  (w:SK k) (c c':Bvector (S t)) (s s':D k),
   R x w ->
   c <> c' ->
   @f_comp k (S t) x c s =  @f_comp k (S t) x c' s' -> 
   let claw := find_collision x c c' s s' in f0 x (fst claw) = f1 x (snd claw).
 Proof.
  intros k t x y c c' s s' Hr Hdiff.
  
  rewrite (VSn_eq bool _ c), (VSn_eq bool _ c').
  intro; simpl.
  
  induction t; simpl.
  (* 0 *)
  unfold f_comp, f_comp_list in H.
  simpl in H.   
  assert (Vhead bool 0 c <> Vhead bool 0 c').
  intro.
  rewrite (VSn_eq _ _ c), (VSn_eq _ _ c'), H0, (V0_eq _ _), 
   (V0_eq _ (Vtail _ _ _)) in Hdiff.
  apply Hdiff; trivial.
  generalize H0 H.
  rewrite (V0_eq _ (Vtail bool 0 c)), (V0_eq _ (Vtail bool 0 c')).
  case (Vhead bool 0 c); intro.
  rewrite (not_true_is_false (Vhead bool 0 c')); auto.
  rewrite (not_false_is_true (Vhead bool 0 c')); auto.

  (* S n *)
  generalize (eqb_spec (Vhead bool (Datatypes.S t) c) (Vhead bool (Datatypes.S t) c')).
  case (eqb (Vhead bool (Datatypes.S t) c) (Vhead bool (Datatypes.S t) c')); intro; simpl.

  rewrite H0 in H.
  rewrite (VSn_eq _ t (Vtail bool _ c)), (VSn_eq _ t (Vtail bool _ c')).
  apply IHt.
  intro.
  rewrite (VSn_eq bool (Datatypes.S t) c), (VSn_eq bool (Datatypes.S t) c') in Hdiff.
  rewrite H0, H1 in Hdiff.
  elim Hdiff; trivial.   
  rewrite <- (VSn_eq _ t (Vtail bool _ c)), <- (VSn_eq _ t (Vtail bool _ c')).
  generalize H.
  unfold f_comp; simpl.
  case (Vhead bool (Datatypes.S t) c'); intros.
  apply (inj_f0 Hr) in H1; trivial.
  apply (inj_f1 Hr) in H1; trivial.

  generalize H.
  unfold f_comp ; simpl.
  case_eq (Vhead bool (Datatypes.S t) c); simpl; intros.

  rewrite (not_true_is_false (Vhead bool _ c')) in H2; trivial.
  intro; rewrite H1, H3 in H0.
  apply H0; trivial.

  rewrite (not_false_is_true (Vhead bool _ c')) in H2.
  rewrite H2; trivial.
  intro H3; rewrite H1, H3 in H0.
  apply H0; trivial.
 Qed.

End ClawFreeProperties.


(** * Functor constructing a Sigma protocol from a family of trapdoor
   permutations.
*)
Module ClawFree (CFP:ClawFreeParameters).

 Open Scope nat_scope.
 Unset Strict Implicit.

 Module CFProp := ClawFreeProperties CFP.

 Import CFP.
 Import CFProp.

 (** We first extend the semantics with the needed types and operators *)
 Inductive ut_ : Type := 
 | D_t
 | PK_t
 | SK_t
 | Bitstring.

 (** * User-defined type module *)
 Module Ut <: UTYPE.

  Definition t := ut_.

  Definition eqb (t1 t2:t) := 
   match t1, t2 with
   | D_t, D_t
   | PK_t, PK_t
   | SK_t, SK_t
   | Bitstring, Bitstring => true
   | _, _ => false
   end.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   simpl; destruct x; destruct y; simpl; trivial; discriminate.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {True} :=
   match x as x0 return {x0 = y} + {True} with
   | D_t =>
     match y as y0 return {D_t = y0} + {True} with 
     | D_t => left _ (refl_equal D_t) 
     | _ => right _ I
     end
   | PK_t =>
     match y as y0 return {PK_t = y0} + {True} with 
     | PK_t => left _ (refl_equal PK_t) 
     | _ => right _ I
     end
   | SK_t =>
     match y as y0 return {SK_t = y0} + {True} with 
     | SK_t => left _ (refl_equal SK_t) 
     | _ => right _ I
     end
   |  Bitstring =>
     match y as y0 return {Bitstring = y0} + {True} with 
     | Bitstring => left _ (refl_equal Bitstring) 
     | _ => right _ I
     end      
   end.

  Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
  Proof.
   destruct x; destruct y; simpl; intros; discriminate.
  Qed.

  Definition interp k (t0:t) := 
   match t0 with
   | D_t  =>  D k  
   | PK_t =>  PK k  
   | SK_t =>  SK k
   | Bitstring => Bvector (S (bs_size k))
   end.
  
  Definition size k (t0:t) (_:interp k t0) := 
   match t0 with
   | D_t  => S (D_size k)
   | PK_t => S (PK_size k)
   | SK_t => S (SK_size k)
   | Bitstring => (S (bs_size k))
   end.
  
  Definition default k (t0:t) : interp k t0 := 
   match t0 with
   | D_t => D_default k
   | PK_t => PK_default k
   | SK_t => SK_default k
   | Bitstring => Bvect_false (S (bs_size k))
   end.

  Definition default_poly (t0:t) := pplus D_size_poly (pplus bs_size_poly (pplus PK_size_poly SK_size_poly)).

  Lemma size_positive : forall k (t0:t) x, 0 < @size k t0 x.
  Proof.
   intros k t0 x; unfold size; destruct t0; auto with arith.
  Qed.

  Lemma default_poly_spec : forall k (t0:t), 
   @size k t0 (default k t0) <= peval (default_poly t0) k.
  Proof.
   intros k t0.
   unfold default, default_poly, size.
   repeat rewrite pplus_spec.
   destruct t0.
   eapply le_trans; [apply D_size_poly_spec | omega ].
   eapply le_trans; [apply PK_size_poly_spec | omega ].
   eapply le_trans; [apply SK_size_poly_spec | omega ].
   eapply le_trans; [apply bs_size_poly_spec | omega ].
  Qed.

  Definition i_eqb k t (x y:interp k t) :=
   match t return interp k t -> interp k t -> bool with
   | D_t => @D_eqb k
   | PK_t => @PK_eqb k   
   | SK_t => @SK_eqb k
   | Bitstring => @Veqb (S (bs_size k))
   end x y.

  Lemma i_eqb_spec : forall k t (x y:interp k t), 
   if i_eqb x y then x = y else x <> y.
  Proof.
   intros; destruct t0.
   refine (D_eqb_spec _ _).
   refine (PK_eqb_spec _ _).
   refine (SK_eqb_spec _ _).
   apply Veqb_spec.
  Qed.

 End Ut.

 Module T := MakeType Ut.

 Inductive uop_ : Type :=
 | Of0 | Of1
 | Of_comp 
 | Ofinv_comp 
 | Ofind_collision.

 Module Uop <: UOP Ut T.

  Definition t := uop_.
  
  Definition eqb (o1 o2:t) : bool :=
   match o1, o2 with
    | Of0, Of0
    | Of1, Of1
    | Of_comp, Of_comp 
    | Ofinv_comp, Ofinv_comp 
    | Ofind_collision, Ofind_collision => true
    | _, _ => false
   end.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   destruct x; destruct y; simpl; trivial; intro; discriminate.
  Qed.

  Definition targs (op:t) : list T.type :=
   match op with
    | Of0 => T.User PK_t :: T.User D_t :: nil
    | Of1 => T.User PK_t :: T.User D_t :: nil
    | Of_comp => T.User PK_t :: T.User Bitstring :: T.User D_t :: nil
    | Ofinv_comp => T.User SK_t :: T.User Bitstring :: T.User D_t :: nil 
    | Ofind_collision => T.User PK_t :: T.User Bitstring :: 
                         T.User Bitstring :: T.User D_t :: T.User D_t :: nil
   end.

  Definition tres (op:t) : T.type :=
   match op with
    | Of0 => T.User D_t
    | Of1 => T.User D_t
    | Of_comp => T.User D_t
    | Ofinv_comp => T.User D_t
    | Ofind_collision => T.Pair (T.User D_t) (T.User D_t)
   end.

  Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
   match op as op0 return T.type_op k (targs op0) (tres op0) with
    | Of0 => @f0 k
    | Of1 => @f1 k
    | Of_comp => @f_comp k (S (bs_size k))
    | Ofinv_comp => @finv_comp k (S (bs_size k))
    | Ofind_collision => @find_collision k (bs_size k)
   end.

  Implicit Arguments interp_op [k].

  Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
   match op as op0 return T.ctype_op k (targs op0) (tres op0) with
    | Of0 => fun pk x => (f0 pk x, cost_f0 pk x)
    | Of1 => fun pk x => (f1 pk x, cost_f1 pk x)
    | Of_comp => fun pk c x => 
       (f_comp pk c x, (bs_size k) * (cost_f0 pk x + cost_f1 pk x))
    | Ofinv_comp => fun sk c x => 
       (finv_comp sk c x, (bs_size k) * (cost_f0inv sk x  + cost_f1inv sk x)) 
    | Ofind_collision => fun pk c c' s s' => 
       (@find_collision k (bs_size k) pk c c' s s', 
        (bs_size k) * (cost_f0 pk s + cost_f1 pk s'))
   end.

  Implicit Arguments cinterp_op [k].

  Definition eval_op k
   (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) :=
   @T.app_op k (targs op) (tres op) (interp_op op) args.

  Definition ceval_op k (op:t) 
   (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) * nat :=
   @T.capp_op k (targs op) (tres op) (cinterp_op op) args.

  Lemma ceval_op_spec : forall k op args,
   @eval_op k op args = fst (@ceval_op k op args).
  Proof.
   intros k o args; destruct o; simpl in args;
    T.dlist_inversion args; subst; trivial.
  Qed.

 End Uop.

 Inductive usupport_ (Ttype : Type) (Tuser:ut_ -> Ttype) : Ttype -> Type := 
 | Usupport : usupport_ Tuser (Tuser Bitstring) 
 | Dsupport : usupport_ Tuser (Tuser D_t).

 (** * User-defined random sampling for elements in G *)
 Module US <: USUPPORT Ut T.

  Definition usupport := usupport_ T.User.

  Definition eval k t (s:usupport t) : list (T.interp k t) :=
   match s in usupport_ _ t0 return list (T.interp k t0) with  
   | Usupport => bs_support _ 
   | Dsupport => D_elems k
   end.

  Definition ceval k t (s:usupport t) : list (T.interp k t) * nat :=
   match s in usupport_ _ t0 return list (T.interp k t0) * nat with  
   | Usupport => (bs_support _, S O) 
   | Dsupport => (D_elems k, S O)
   end.

  Lemma eval_usupport_nil : forall k t (s:usupport t), eval k s <> nil.
  Proof.
   intros; case s; simpl.  
   exact (@bs_support_not_nil _).
   apply D_elems_not_nil.
  Qed.

  Lemma ceval_spec : forall k t (s:usupport t), eval k s = fst (ceval k s).
  Proof.
   intros k t s; case s; trivial.
  Qed.

  Definition eqb (t1 t2:T.type) (s1:usupport t1) (s2:usupport t2) : bool :=
   match s1, s2 with  
   | Usupport, Usupport => true
   | Dsupport, Dsupport => true  
   | _ , _ => false
   end.

  Lemma eqb_spec_dep :  forall t1 (e1:usupport t1) t2 (e2:usupport t2),
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

 End US.

 Module Sem := MakeSem.Make Ut T Uop US.
 Module SemT := BaseProp.Make Sem.

 Module Entries.

  Module SemO <: SEM_OPT.

   Module Sem := Sem.
   Export Sem.

   (** Notations *)
   Notation fcomp       := (E.Eop (O.Ouser Of_comp)).
   Notation finvcomp    := (E.Eop (O.Ouser Ofinv_comp)). 
   Notation find_col    := (E.Eop (O.Ouser Ofind_collision)).
   Notation f_0         := (E.Eop (O.Ouser Of0)).
   Notation f_1         := (E.Eop (O.Ouser Of1)).
   Notation "'{0,1}^k'" := (E.Duser (Usupport T.User)).
   Notation Dfs         := (E.Duser (Dsupport T.User)).   

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
    fun _ => pplus D_size_poly 
              (pplus bs_size_poly (pplus PK_size_poly SK_size_poly)).

   Lemma utsize_default_poly_spec : forall r ut,
    utsize ut <= r -> 
    forall k, 
     Ut.size (t:=ut) (Ut.default k ut) <= peval (utsize_default_poly r) k.
   Proof.  
    intros r ut _ k.
    unfold Ut.size, utsize_default_poly. 
    repeat rewrite pplus_spec.
    case ut; simpl. 
    eapply le_trans; [apply D_size_poly_spec | omega ].
    eapply le_trans; [apply PK_size_poly_spec | omega ].
    eapply le_trans; [apply SK_size_poly_spec | omega ].
    eapply le_trans; [apply bs_size_poly_spec | omega ].
   Qed.

   Definition uop_poly (o:Uop.t) : bool := true.

   Lemma sub_fv_expr_1 : 
    forall (t:ClawFree.T.type) (e:E.expr t) (s:SemT.Vset.t),
     SemT.fv_expr_rec SemT.Vset.empty e [<=] (SemT.fv_expr_rec s e).
   Proof.
    intros.
    fold (fv_expr_extend e s).
    rewrite union_fv_expr_spec.
    apply VsetP.subset_union_l.     
   Qed.

   Lemma sub_fv_expr_2 : 
    forall (t t':ClawFree.T.type) (e:E.expr t) (e':E.expr t') (s:SemT.Vset.t),
     SemT.fv_expr_rec SemT.Vset.empty e[<=] s -> 
     SemT.fv_expr_rec SemT.Vset.empty e[<=] SemT.fv_expr_rec s e'.
   Proof.
    intros.
    fold (fv_expr_extend e' s).
    rewrite union_fv_expr_spec.
    rewrite H.
    apply VsetP.subset_union_r.
   Qed.     

   Ltac prove_fv_expr_subset :=
    match goal with
      | |- SemT.fv_expr_rec SemT.Vset.empty ?e[<=] (SemT.fv_expr_rec ?s ?e) =>
        apply sub_fv_expr_1; prove_fv_expr_subset
      | |-  SemT.fv_expr_rec SemT.Vset.empty ?e[<=] (SemT.fv_expr_rec ?s ?e') =>
        apply sub_fv_expr_2; prove_fv_expr_subset
    end.
   
   Lemma uop_poly_spec : forall o (la:dlist E.expr (O.targs (O.Ouser o))),
    uop_poly o ->
    (forall t (e:E.expr t), @DIn _ E.expr _ e _ la -> 
     exists F, exists G, PPT_expr e F G) ->
    exists F, exists G, PPT_expr (E.Eop (O.Ouser o) la) F G.
   Proof.
    intros o la H Hla.
    destruct o. 

    (* Of0 *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    destruct (Hla _ x0) as [F2 [G2 H2] ].
    right; left; trivial.
    exists (fun p => D_size_poly).
    exists (fun p => pplus (cost_f0_poly) (pplus (G1 p) (G2 p))).
    intros k m p Hm; simpl; split.
    apply D_size_poly_spec.
    generalize (H1 k m p) (H2 k m p); clear H1 H2.
    case_eq (E.ceval_expr x m); simpl.
    case_eq (E.ceval_expr x0 m); simpl.   
    intros i n Heqi i0 n0 Heqi0 Hi Hi0.
    destruct Hi.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].
    unfold fv_expr; simpl; prove_fv_expr_subset.
    destruct Hi0.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x0); [ | trivial].
    unfold fv_expr; simpl; prove_fv_expr_subset.
    rewrite pplus_spec, pplus_spec; apply plus_le_compat; trivial.
    apply cost_f0_poly_spec.
    omega.

    (* Of1 *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    destruct (Hla _ x0) as [F2 [G2 H2] ].
    right; left; trivial.
    exists (fun p => D_size_poly).
    exists (fun p => pplus (cost_f1_poly) (pplus (G1 p) (G2 p))).
    intros k m p Hm; simpl; split.
    apply D_size_poly_spec.
    generalize (H1 k m p) (H2 k m p); clear H1 H2.
    case_eq (E.ceval_expr x m); simpl.
    case_eq (E.ceval_expr x0 m); simpl.   
    intros i n Heqi i0 n0 Heqi0 Hi Hi0.
    destruct Hi.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].
    unfold fv_expr; simpl; prove_fv_expr_subset.
    destruct Hi0.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x0); [ | trivial].
    unfold fv_expr; simpl; prove_fv_expr_subset.
    rewrite pplus_spec, pplus_spec; apply plus_le_compat; trivial.
    apply cost_f1_poly_spec.
    omega.

    (* Of_comp *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    destruct (Hla _ x0) as [F2 [G2 H2] ].
    right; left; trivial.
    destruct (Hla _ x1) as [F3 [G3 H3] ].
    right; right; left; trivial.
    exists (fun p => D_size_poly).
    exists (fun p => pplus (pplus (G1 p) 
     (pplus (G2 p) (G3 p))) 
     (pmult bs_size_poly (pplus (cost_f0_poly) (cost_f1_poly)))).
    intros k m p Hm; simpl; split.
    apply D_size_poly_spec.
    generalize (H1 k m p) (H2 k m p) (H3 k m p); clear H1 H2 H3.
    case_eq (E.ceval_expr x m); simpl.
    case_eq (E.ceval_expr x0 m); simpl.    
    case_eq (E.ceval_expr x1 m); simpl.    
    intros i n Heqi i0 n0 Heqi0 i1 n1 Heqi1 Hi Hi0 Hi1.
    destruct Hi.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].
    unfold fv_expr; simpl.
    prove_fv_expr_subset.
    destruct Hi0.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x0); [ | trivial].
    unfold fv_expr; simpl.  
    prove_fv_expr_subset.
    destruct Hi1.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x1); [ | trivial].
    unfold fv_expr; simpl.
    prove_fv_expr_subset.
    rewrite pplus_spec, pplus_spec, pmult_spec, pplus_spec, pplus_spec.
    rewrite (plus_comm).
    apply plus_le_compat.
    omega.
    apply mult_le_compat.
    apply lt_le_weak.
    apply bs_size_poly_spec.
    apply plus_le_compat.
    apply cost_f0_poly_spec.
    apply cost_f1_poly_spec.
    
    (* Ofinv_comp *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    destruct (Hla _ x0) as [F2 [G2 H2] ].
    right; left; trivial.
    destruct (Hla _ x1) as [F3 [G3 H3] ].
    right; right; left; trivial.
    exists (fun p => D_size_poly).
    exists (fun p => pplus (pplus (G1 p) 
     (pplus (G2 p) (G3 p))) 
     (pmult bs_size_poly (pplus (cost_f0inv_poly) (cost_f1inv_poly)))).
    intros k m p Hm; simpl; split.
    apply D_size_poly_spec.
    generalize (H1 k m p) (H2 k m p) (H3 k m p); clear H1 H2 H3.
    case_eq (E.ceval_expr x m); simpl.
    case_eq (E.ceval_expr x0 m); simpl.    
    case_eq (E.ceval_expr x1 m); simpl.    
    intros i n Heqi i0 n0 Heqi0 i1 n1 Heqi1 Hi Hi0 Hi1.
    destruct Hi.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].
    unfold fv_expr; simpl.
    prove_fv_expr_subset.
    destruct Hi0.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x0); [ | trivial].
    unfold fv_expr; simpl.
    prove_fv_expr_subset.
    destruct Hi1.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x1); [ | trivial].
    unfold fv_expr; simpl.
    prove_fv_expr_subset.
    rewrite pplus_spec, pplus_spec, pmult_spec, pplus_spec, pplus_spec.
    rewrite (plus_comm).
    apply plus_le_compat.
    omega.
    apply mult_le_compat.
    apply lt_le_weak.
    apply bs_size_poly_spec.
    apply plus_le_compat.
    apply cost_f0inv_poly_spec.
    apply cost_f1inv_poly_spec.

    (* find_col *)
    T.dlist_inversion la.
    rewrite Heq in Hla |- *.
    destruct (Hla _ x) as [F1 [G1 H1] ].
    left; trivial.
    destruct (Hla _ x0) as [F2 [G2 H2] ].
    right; left; trivial.
    destruct (Hla _ x1) as [F3 [G3 H3] ].
    right; right; left; trivial.
    destruct (Hla _ x2) as [F4 [G4 H4] ].
    right; right; right; left; trivial.
    destruct (Hla _ x3) as [F5 [G5 H5] ].
    right; right; right; right; left; trivial.
    exists (fun p => pplus 1 (pplus D_size_poly (pplus 1 D_size_poly))).
    exists (fun p => pplus (G1 p) 
     (pplus (G2 p) (pplus (G3 p) (pplus (G4 p) (pplus (G5 p) 
      (pmult bs_size_poly (pplus (cost_f0_poly) (cost_f1_poly)))))))).
    intros k m p Hm; simpl; split.
    repeat rewrite pplus_spec; repeat rewrite pcst_spec.
    apply le_trans with (S (S (D_size k)) + S (S (D_size k))).
    omega.
    apply le_trans with ((1 + peval D_size_poly k) + (1 + peval D_size_poly k)).
    apply plus_le_compat.
    apply le_n_S.
    apply D_size_poly_spec.
    apply le_n_S.
    apply D_size_poly_spec.
    omega.
    generalize (H1 k m p) (H2 k m p) (H3 k m p) (H4 k m p) (H5 k m p); 
     clear H1 H2 H3 H4 H5.
    case_eq (E.ceval_expr x m); simpl.
    case_eq (E.ceval_expr x0 m); simpl.
    case_eq (E.ceval_expr x1 m); simpl.    
    case_eq (E.ceval_expr x2 m); simpl.
    case_eq (E.ceval_expr x3 m); simpl.
    intros.    
    destruct H5.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x); [ | trivial].
    unfold fv_expr; simpl; prove_fv_expr_subset.
    destruct H6.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x0); [ | trivial].
    unfold fv_expr; simpl; prove_fv_expr_subset.
    destruct H7.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x1); [ | trivial].
    unfold fv_expr; simpl; prove_fv_expr_subset.
    destruct H8.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x2); [ | trivial].
    unfold fv_expr; simpl; prove_fv_expr_subset.
    destruct H9.
    intros; apply Hm; simpl.
    apply Vset.subset_correct with (fv_expr x3); [ | trivial].
    unfold fv_expr; simpl; prove_fv_expr_subset.
    repeat rewrite pplus_spec; rewrite pmult_spec; repeat rewrite pplus_spec.
    rewrite (plus_comm).
    repeat (rewrite plus_assoc).
    apply plus_le_compat.
    omega.
    apply mult_le_compat.
    apply lt_le_weak.
    apply bs_size_poly_spec.
    apply plus_le_compat.
    apply cost_f0_poly_spec.
    apply cost_f1_poly_spec.
   Qed.
    
   Definition usupport_poly t (us:US.usupport t):bool := true.

   Lemma usupport_poly_spec : forall t (us:US.usupport t),
    usupport_poly us ->
    exists F, exists G, PPT_support (E.Duser us) F G.
   Proof.
    intros t us; case us; intros _.   
    exists (fun _ => bs_size_poly).
    exists (fun _ => pcst 1).
    intros k m p Hm.
    simpl; split; intros.
    apply bs_size_poly_spec.
    rewrite pcst_spec; trivial.
   
    exists (fun _ => D_size_poly).
    exists (fun _ => pcst 1).
    intros k m p Hm.
    simpl; split; intros.
    apply D_size_poly_spec.
    rewrite pcst_spec; trivial.
   Qed.

  End Uppt.

 End Entries.

 Module Tactics := BuildTac.Make Entries.
 Export Tactics.


 (** * The protocol *)
 Module Protocol.

  Import N.

  (** Knowledge relation *)
  Definition R k (x:T.interp k (T.User PK_t)) (w:T.interp k (T.User SK_t)) := 
   R x w.
 
  (** Variables *)
  Notation x      := (Var.Lvar (T.User PK_t) 1).
  Notation w      := (Var.Lvar (T.User SK_t) 2).
  Notation r      := (Var.Lvar (T.User D_t) 3). 
  Notation state  := (Var.Lvar (T.User D_t) 4). 
  Notation c      := (Var.Lvar (T.User Bitstring) 5). 
  Notation s      := (Var.Lvar (T.User D_t) 6).
  Notation rstate := (Var.Lvar (T.Pair (T.User D_t) (T.User D_t)) 7).
  Notation rs     := (Var.Lvar (T.Pair (T.User D_t) (T.User D_t)) 8).
  Notation b      := (Var.Lvar T.Bool 9).
  Notation x'     := (Var.Lvar (T.User PK_t) 10).
  Notation w'     := (Var.Lvar (T.User SK_t) 11).
  Notation k'     := (Var.Lvar (T.User D_t) 12).
  Notation c'     := (Var.Lvar (T.User Bitstring) 13).
  Notation s'     := (Var.Lvar (T.User D_t) 14).
  Notation r'     := (Var.Lvar (T.User D_t) 15).
  Notation y'     := (Var.Lvar (T.User D_t) 16).
  Notation c1     := (Var.Lvar (T.User Bitstring) 20).
  Notation c2     := (Var.Lvar (T.User Bitstring) 21).
  Notation s1     := (Var.Lvar (T.User D_t) 22).
  Notation s2     := (Var.Lvar (T.User D_t) 23).
  Notation pc     := (Var.Lvar (T.Pair (T.User D_t) (T.User D_t)) 24).
  Notation lx     := (Var.Lvar (T.User PK_t) 25).
  Notation lr     := (Var.Lvar (T.User D_t) 26).
  Notation lc1    := (Var.Lvar (T.User Bitstring) 27).
  Notation lc2    := (Var.Lvar (T.User Bitstring) 28).
  Notation ls1    := (Var.Lvar (T.User D_t) 29).
  Notation ls2    := (Var.Lvar (T.User D_t) 30).
  Notation lpc    := (Var.Lvar (T.Pair (T.User D_t) (T.User D_t)) 31).
  Notation claw1  := (Var.Lvar (T.User D_t) 32).
  Notation claw2  := (Var.Lvar (T.User D_t) 33).

  (** Procedures *)
  Notation P1 := (Proc.mkP 1 
   ((T.User PK_t) :: (T.User SK_t) :: nil) 
   (T.Pair (T.User D_t) (T.User D_t))).
  
  Notation P2 := (Proc.mkP 2 
   ((T.User PK_t) :: (T.User SK_t) :: (T.User D_t) ::  (T.User Bitstring) :: nil) 
   (T.User D_t)).
  
  Notation V1 := (Proc.mkP 3 
   ((T.User PK_t) :: (T.User D_t) :: nil) 
   (T.User Bitstring)).
  
  Notation V2 := (Proc.mkP 4 
   ((T.User PK_t) :: (T.User D_t) :: (T.User Bitstring) :: (T.User D_t) :: nil) 
   T.Bool).
  
  Notation S  := (Proc.mkP 5 
   ((T.User PK_t) :: (T.User Bitstring) :: nil) 
   (T.Pair (T.User D_t)(T.User D_t))).

  Notation CE := (Proc.mkP 6 
   ((T.User PK_t) :: (T.User Bitstring) :: (T.User Bitstring) :: (T.User D_t) ::  (T.User D_t) :: nil)
   (T.Pair (T.User D_t) (T.User D_t))).
   
 
  Definition P1_args : var_decl (Proc.targs P1) := 
   dcons _ x' (dcons _ w' (dnil _)).
  
  Definition P1_body : cmd := [ y' <$- Dfs ].
  
  Definition P1_re : E.expr (T.Pair (T.User D_t) (T.User D_t)) := (y' | y').
  

  Definition P2_args : var_decl (Proc.targs P2) := 
   dcons _ x' (dcons _ w' (dcons _ k' (dcons _ c' (dnil _)))).
  
  Definition P2_body : cmd := [ s' <- finvcomp {w', c', k'} ].

  Definition P2_re : E.expr (T.User D_t) := s'.


  Definition V1_args : var_decl (Proc.targs V1) := 
   dcons _ x' (dcons _ r' (dnil _)).
 
  Definition V1_body : cmd := [ c' <$- {0,1}^k ].
  
  Definition V1_re : E.expr (T.User Bitstring) := c'.


  Definition V2_args : var_decl (Proc.targs V2) := 
   dcons _ x' (dcons _ r' (dcons _ c' (dcons _ s' (dnil _)))).

  Definition V2_body : cmd := nil.
  
  Definition V2_re : E.expr T.Bool := fcomp {x', c', s'} =?= r'.

 
  Definition S_args : var_decl (Proc.targs S) :=  dcons _ x' (dcons _ c' (dnil _)).

  Definition S_body : cmd :=
   [
    s' <$- Dfs;
    r' <- fcomp {x', c', s'}
   ].
  
  Definition S_re : E.expr (T.Pair (T.User D_t) (T.User D_t)) := (r' | s').


  Definition CE_args : var_decl (Proc.targs CE) := 
   dcons _ lx (dcons _ lc1 (dcons _ lc2 (dcons _ ls1 (dcons _ ls2 (dnil _))))).
  
  Definition CE_body := [ lpc <- find_col {lx, lc1, lc2, ls1, ls2} ].
  
  Definition CE_re : E.expr (T.Pair (T.User D_t) (T.User D_t)) := lpc.
  
  Parameter _E : env.

  Section ENV.  

   Let add_P1 E := add_decl E P1 P1_args (refl_equal _) P1_body P1_re.
   Let add_P2 E := add_decl E P2 P2_args (refl_equal _) P2_body P2_re.
   Let add_V1 E := add_decl E V1 V1_args (refl_equal _) V1_body V1_re.
   Let add_V2 E := add_decl E V2 V2_args (refl_equal _) V2_body V2_re.
   Let add_S  E := add_decl E S S_args   (refl_equal _) S_body S_re.
   Let add_CE E := add_decl E CE CE_args (refl_equal _) CE_body CE_re.

   Definition E := add_CE (add_S (add_P1 (add_P2 (add_V1 (add_V2 _E))))).

  End ENV.

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
   add_refl_info_O CE (fv_expr CE_re) Vset.empty Vset.empty
   (add_refl_info_O S (fv_expr S_re) Vset.empty Vset.empty
   (add_refl_info_O P1 (fv_expr P1_re) Vset.empty Vset.empty
   (add_refl_info_O P2 (fv_expr P2_re) Vset.empty Vset.empty 
   (add_refl_info_O V1 (fv_expr V1_re) Vset.empty Vset.empty
   (add_refl_info_O V2 (fv_expr V2_re) Vset.empty Vset.empty
   (empty_info E E)))))).

  Lemma decMR_R1 : decMR R1.
  Proof.
   unfold decMR, R1, R; intros.
   apply R_dec.
  Qed.

  Hint Resolve decMR_R1.

  Lemma completeness : forall k (m:Mem.t k),  
   R (m x) (m w) -> Pr E protocol m (EP k b) == 1%U.
  Proof.
   unfold protocol; intros.
   transitivity (Pr E [ b <- true ] m (EP k b)).
   apply equiv_deno with (req_mem_rel {{x, w}} R1) (kreq_mem {{b}}).
   clear.
   inline_l iEE P1.
   inline_l iEE V1.
   inline_l iEE P2.
   sinline_l iEE V2.

   equiv_trans E [ y' <$- Dfs; c <$- {0,1}^k; b <- true ].
   apply refl_supMR_req_mem_rel with {{x, w}} Vset.empty.
   unfold R1; intros k' m1 m2 m1' m2' Hreq _ HR.
   rewrite <- (Hreq _ w), <- (Hreq _ x); trivial.
   vm_compute; trivial.

   apply equiv_cons with  (req_mem_rel {{x, w}} R1).
   eqobsrel_tail; unfold R1, implMR; simpl; intros.
   mem_upd_simpl.
   destruct H; trivial.

   apply equiv_cons with  (req_mem_rel {{x, w}} R1).
   eqobsrel_tail; unfold R1, implMR; simpl; intros.
   mem_upd_simpl.
   destruct H; trivial.

   ep_eq_l ((fcomp {x, c, finvcomp {w, c, y'} } =?= y')) true.
   intros; simpl E.eval_expr; unfold O.eval_op; simpl.
   rewrite simpl_f_comp.
   generalize (D_eqb_spec (m1 y') (m1 y')).
   case (D_eqb (m1 y') (m1 y')); intuition.
   destruct H; trivial.

   rewrite (implMR_trueR R1); eqobs_in.

   rewrite (implMR_trueR R1); deadcode; eqobs_in.

   intros; unfold charfun, restr, EP; simpl.  
   rewrite (H0 _ b); trivial.
   split; trivial.

   unfold Pr; rewrite deno_assign_elim; simpl.
   unfold charfun, EP, restr; simpl; rewrite Mem.get_upd_same; trivial.
  Qed.

  Lemma SHVZK : equiv 
   (req_mem_rel {{x, w, c}} R1)
   E protocol'
   E simulation
   (kreq_mem {{r, c, s}}).
  Proof.
   unfold protocol, simulation.
   inline_r iEE S.
   inline_l iEE P1.
   inline_l iEE V1.
   sinline_l iEE P2.
   alloc_l s s'.
   eqobs_tl.
   alloc_l y' r.
   ep; deadcode iEE.

   apply equiv_cons with 
    (fun k (m1 m2:Mem.t k) => finv_comp (m1 w) (m1 c) (m1 r) = m2 s' /\ 
      m1 c = m2 c /\ (R (m1 x) (m1 w)) /\ m1 x = m2 x).
   eapply equiv_strengthen;
    [ | apply equiv_random_permut
        with (f:=fun k (m1 m2:Mem.t k) (v:T.interp k (T.User D_t)) => f_comp (m1  x) (m1 c) v)].
   intros; split.
   apply PermutP_NoDup with (finv_comp (m1 w) (m1 c)); intros.
   apply D_elems_nodup.
   apply D_elems_nodup.
   apply simpl_f_comp; destruct H; trivial.
   apply simpl_finv_comp; destruct H; trivial.
   apply D_elems_full.
   apply D_elems_full.

   intros; mem_upd_simpl.
   destruct H; split.
   apply simpl_finv_comp; trivial.
   split.
   rewrite (H _ c); trivial.
   split; [ trivial | ].
   rewrite (H _ x); trivial.

   eapply equiv_strengthen; [ | apply equiv_assign ].
   unfold upd_para; intros k m1 m2 [H1 [ H2 [ H3 H4 ] ] ].
   simpl; unfold O.eval_op; simpl.
   intros ? x Hin.
   assert (Vset.mem x {{s', r, c}}) by trivial.
   Vset_mem_inversion H; subst; mem_upd_simpl.
   trivial.
   rewrite <- H1, H2, <- H4, simpl_f_comp; trivial.
  Qed.

  Definition pi : PPT_info E := 
   PPT_add_info (PPT_add_info (PPT_empty_info E) S) CE.

  Lemma S_PPT : PPT_proc E S.
  Proof.
   PPT_proc_tac pi.
  Qed.
  
  Section COLLISION_INTRACTABILITY.

   Close Scope positive_scope.
   Close Scope nat_scope.

   Variable k : nat.
   Variable m : Mem.t k.

   Hypothesis H_neq : m c1 <> m c2.
   Hypothesis H_R : R (m x) (m w).
   Hypothesis accepting_1 : f_comp (m x) (m c1) (m s1) = (m r).
   Hypothesis accepting_2 : f_comp (m x) (m c2) (m s2) = (m r).

   Lemma CE_correct : 
    Pr E [pc <c- CE with {x, c1, c2, s1, s2} ] m 
     (EP k (f_0{x,(Efst pc)} =?= f_1{x,(Esnd pc)})) == 1.
   Proof.
    transitivity (Pr E  
     [ pc <- find_col {x, c1, c2, s1, s2} ] m (EP k (f_0 {x,(Efst pc)} =?= f_1 {x,(Esnd pc)}))).
    apply EqObs_deno with {{x, r, c1, c2, s1, s2}} {{x, pc}}.
    sinline_l iEE CE.
    eqobs_in iEE.
    intros; unfold charfun, restr, EP.
    simpl E.eval_expr; unfold O.eval_op; simpl. 
    rewrite (H _ x), (H _ pc); trivial.
    trivial.

    unfold Pr; rewrite deno_assign_elim.
    unfold charfun, restr, fone, EP.
    simpl E.eval_expr; unfold O.eval_op; simpl. 
    mem_upd_simpl.
    
    rewrite (find_collision_spec _ _ H_R).
    assert (forall x:D k, D_eqb x x = true).
    intros; generalize (D_eqb_spec x x).
    case (D_eqb x x); [ | intro H ; elim H]; trivial.
    rewrite H; trivial.
    trivial.

    rewrite accepting_1, accepting_2; trivial.
   Qed.

   Lemma CE_PPT : PPT_proc E CE.
   Proof.
    PPT_proc_tac pi.
   Qed.

  End COLLISION_INTRACTABILITY.

 End Protocol.

End ClawFree.
