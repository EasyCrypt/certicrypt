(** * Variables.v: Variable and procedure names *)


Set Implicit Arguments.

Require Export ZArith.
Require Export Types.


(** * Variable names *)
Module Type VAR (UT:UTYPE) (T:TYPE UT).

 Inductive var : T.type -> Type :=
 | Gvar : forall t, positive -> var t
 | Lvar : forall t, positive -> var t.
 
 Inductive bvar : Type :=
 | mkV :> forall t, var t -> bvar.

 Definition btype (bv:bvar) : T.type :=
  let (t, _) := bv in t.

 Definition bname (bv:bvar) : var (btype bv) :=
  match bv as bv0 return var (btype bv0) with
  | mkV t v => v
  end.

 Coercion bname : bvar >-> var.

 Parameter veqb : forall t1 t2, var t1 -> var t2 -> bool.

 Parameter veqb_spec_dep : forall t1 (e1:var t1) t2 (e2:var t2), 
  if veqb e1 e2 then eq_dep T.type var t1 e1 t2 e2 
   else ~eq_dep T.type var t1 e1 t2 e2.
   
 Parameter veqb_spec : forall t (e1 e2:var t),
  if veqb e1 e2 then e1 = e2 else e1 <> e2.

 Parameter veq_dec : forall t (e1 e2:var t), {e1 = e2} + {e1 <> e2}.

 Definition t := bvar.
 
 Parameter eqb : t -> t -> bool.
 
 Parameter eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Parameter eq_dec : forall (x y:t), {x = y} + {x <> y}.
 
 Definition vis_global t (x:var t) := 
  match x with
  | Gvar _ _ => true
  | _ => false
  end.

 (* REMARK: maybe we gain something if we define this directly, 
    I guess we use this intensively when applying tactics *) 
 Definition vis_local t (x:var t) := negb (vis_global x).
  
 Definition is_global (x:t) := vis_global x.
 Definition is_local (x:t) := negb (is_global x).
 
 Parameter global_local : forall v, is_global v <-> ~is_local v.

 Parameter vis_local_local : forall t (x:var t), vis_local x = is_local x.
 
 (* Dependant equality *)
 Parameter eq_dep_eq :
  forall (P:t->Type) (p:t) (x y:P p), eq_dep t P p x p y -> x = y.
 
 Parameter UIP_refl : forall (x:t) (p:x = x), p = refl_equal x.
 
 Parameter inj_pair2 : forall (P:t -> Type) (p:t) (x y:P p),
  existT P p x = existT P p y -> x = y.

End VAR.


Module MakeVar (UT:UTYPE) (T:TYPE UT) <: VAR UT T.

 Inductive var : T.type -> Type :=
 | Gvar : forall t, positive -> var t
 | Lvar : forall t, positive -> var t.
 
 Inductive bvar : Type :=
  | mkV :> forall t, var t -> bvar.

 Definition btype (bv:bvar) : T.type :=
  let (t, _) := bv in t.

 Definition bname (bv:bvar) : var (btype bv) :=
  match bv as bv0 return var (btype bv0) with
  | mkV t v => v
  end.

 Definition veqb t1 t2 (x:var t1) (y:var t2) : bool :=
  if T.eqb t1 t2 then 
   match x, y with
   | Gvar _ nx, Gvar _ ny => PosEq.eqb nx ny
   | Lvar _ nx, Lvar _ ny => PosEq.eqb nx ny
   | _, _ => false
   end
  else false.
 
 Lemma veqb_spec_dep : forall t1 (e1 : var t1) t2 (e2:var t2), 
  if veqb e1 e2 then eq_dep T.type var t1 e1 t2 e2 
   else ~eq_dep T.type var t1 e1 t2 e2.
 Proof.
  intros t1 x t2 y; unfold veqb.
  generalize (T.eqb_spec t1 t2); case (T.eqb t1 t2); intro; subst.
  destruct x; destruct y.
  generalize (PosEq.eqb_spec p p0); case (PosEq.eqb p p0); intro; subst.
  constructor.
  intro H0; assert (W:=T.eq_dep_eq H0); injection W; trivial.
  intro H0; assert (W:=T.eq_dep_eq H0); discriminate.
  intro H0; assert (W:=T.eq_dep_eq H0); discriminate.
  generalize (PosEq.eqb_spec p p0); case (PosEq.eqb p p0); intro; subst.
  constructor.
  intro H0; assert (W:=T.eq_dep_eq H0); injection W; trivial.
  intro H0; elim H; case H0; trivial.
 Qed.

 Lemma veqb_spec : forall t (e1 e2:var t),
  if veqb e1 e2 then e1 = e2 else e1 <> e2.   
 Proof.
  intros t x y; generalize (veqb_spec_dep x y); case (veqb x y); intros.
  apply (T.eq_dep_eq H).
  intro H0; apply H; rewrite H0; constructor.
 Qed.

 Lemma veq_dec : forall t (e1 e2:var t), {e1 = e2} + {e1 <> e2}.
 Proof. 
  intros t x y; generalize (veqb_spec x y); case (veqb x y); intro; auto.
 Qed.

 Definition t := bvar.
  
 Definition eqb (x y: t) : bool := veqb (bname x) (bname y).
 
 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  intros (tx,x) (ty,y); unfold eqb; simpl.
  generalize (veqb_spec_dep x y); case (veqb x y); intros.
  case H; trivial.
  intro H0; injection H0; intros H1 H2; clear H0; subst.    
  apply H; rewrite (T.inj_pair2 H1); constructor.
 Qed.

 Lemma eq_dec : forall (x y:t), {x = y} + {x <> y}.
 Proof.
  intros x y; generalize (eqb_spec x y); destruct (eqb x y); auto.
 Qed.
 
 Definition vis_global t (x:var t) := 
  match x with
  | Gvar _ _ => true
  | _ => false
  end.

 Definition vis_local t (x:var t) := negb (vis_global x).

 Definition is_global x := vis_global (bname x).
 Definition is_local x := negb (is_global x).

 Lemma global_local : forall v, is_global v <-> ~is_local v.
 Proof.  
  intros (tx, x); destruct x; unfold is_local, is_global; split; simpl; intro; trivialb.
 Qed.
 
 Lemma vis_local_local : forall t (x:var t), vis_local x = is_local x.
 Proof. 
  trivial. 
 Qed.

 (* Dependant equality *) 
 Module VBdec <: DecidableType.

  Definition U := t.
  Definition eq_dec := eq_dec.

 End VBdec.
 
 Include DecidableEqDepSet VBdec.

End MakeVar.


(** * Procedure names *)
Module Type PROC (UT:UTYPE) (T:TYPE UT).

 Inductive proc : T.type -> Type :=
 | mkP : forall (pname:positive) (targs:list T.type) (tres:T.type), proc tres.
 
 Parameter eqb : forall t1 t2, proc t1 -> proc t2 -> bool.
 
 Parameter eqb_spec_dep : forall t1 (p1 : proc t1) t2 (p2:proc t2), 
  if eqb p1 p2 then eq_dep T.type proc t1 p1 t2 p2 
   else ~eq_dep T.type proc t1 p1 t2 p2.
 
 Parameter eqb_spec : forall t (p1 p2:proc t),
  if eqb p1 p2 then p1 = p2 else p1 <> p2. 
 
 Parameter eq_dec : forall t (x y:proc t), {x = y} + {True}.
 Parameter eq_dec_r : forall t (x y:proc t) i, eq_dec x y = right _ i -> x <> y.
 
 Definition targs t (p:proc t) : list T.type := 
  let (_, l, _) := p in l.

 (* Dependant Equality *)
 Parameter eq_dep_eq : forall t (P:proc t->Type) (p:proc t) (x y:P p), 
  eq_dep (proc t) P p x p y -> x = y.
 
 Parameter UIP_refl : forall t (x:proc t) (p:x = x), p = refl_equal x.
 
 Parameter inj_pair2 :forall t (P:proc t -> Type) (p:proc t) (x y:P p),
  existT P p x = existT P p y -> x = y.

End PROC.


Module MakeProc (UT:UTYPE) (T:TYPE UT) <: PROC UT T.

 Inductive proc : T.type -> Type :=
 | mkP : forall (pname:positive) (targs:list T.type) (tres:T.type), proc tres.
 
 Definition eqb t1 t2 (x : proc t1) (y : proc t2) : bool :=
  let (xn, xa, xr) := x in
   let (yn, ya, yr) := y in
    if PosEq.eqb xn yn then
     if T.eqb xr yr then eqb_list T.eqb xa ya
     else false
    else false.
 
 Lemma eqb_spec_dep : forall t1 (p1 : proc t1) t2 (p2:proc t2),
  if eqb p1 p2 then eq_dep T.type proc t1 p1 t2 p2 
   else ~eq_dep T.type proc t1 p1 t2 p2.
 Proof.
  intros t1 (xn,xa,xr) t2 (yn,ya,yr); simpl.
  generalize (PosEq.eqb_spec xn yn); case (PosEq.eqb xn yn); intro; subst. 
  generalize (T.eqb_spec xr yr); case (T.eqb xr yr); intro; subst.
  generalize (eqb_list_spec T.eqb T.eqb_spec xa ya);
   case (eqb_list T.eqb xa ya); intro; subst.
  constructor.
  intro H0; assert (W:=T.eq_dep_eq H0); injection W; trivial.   
  intro H0; apply H; case H0; trivial.
  generalize (T.eqb_spec xr yr); case (T.eqb xr yr); intro; subst.
  intro H0; assert (W:=T.eq_dep_eq H0); injection W; trivial.   
  intro H1; apply H0; case H1; trivial.
 Qed.
  
 Lemma eqb_spec : forall t (p1 p2:proc t),
  if eqb p1 p2 then p1 = p2 else p1 <> p2. 
 Proof.
  intros; generalize (eqb_spec_dep p1 p2); case (eqb p1 p2); intros.
  apply (T.eq_dep_eq H).
  intro H0; apply H; rewrite H0; constructor.
 Qed.

 Fixpoint pos_eq_dec (x y : positive){struct x} : {x = y} + {True} :=
  match x as x0 return {x0 = y} + {True} with
  | xH =>
   match y as y0 return {xH = y0}+{True} with
   | xH => left _ (refl_equal xH)
   | _ => right _ I
   end
  | xO x =>
   match y as y0 return {xO x = y0}+{True} with
   | xO y => 
    match pos_eq_dec x y with 
    | left H => 
     match H in (_ = y0) return {xO x = xO y0}+{True} with
     | refl_equal => left _ (refl_equal (xO x))
     end
    | _ => right _ I
    end
   | _ => right _ I
   end
  | xI x =>
   match y as y0 return {xI x = y0}+{True} with
   | xI y => 
    match pos_eq_dec x y with 
    | left H => 
     match H in (_ = y0) return {xI x = xI y0}+{True} with
     | refl_equal => left _ (refl_equal (xI x))
     end
    | _ => right _ I
    end
   | _ => right _ I
   end
  end. 

 Lemma pos_eq_dec_r : forall x y i, pos_eq_dec x y = right _ i -> x <> y.
 Proof.
  induction x; destruct y; intro i; try (intros; intro; discriminate); simpl.
  generalize (IHx y); destruct (pos_eq_dec x y).
  case e; intros; discriminate.
  case t; case i; intros; intro.
  apply (H I); trivial; injection H1; trivial.
  generalize (IHx y); destruct (pos_eq_dec x y).
  case e; intros; discriminate.
  case t; case i; intros; intro.
  apply (H I); trivial; injection H1; trivial.
 Qed.

 Definition eq_dec t (x y:proc t) : {x = y} + {True} :=
  match x as x0 in (proc xr) return  forall (y:proc xr), {x0 = y} + {True} with
  | mkP xn xa xr =>
   fun (y:proc xr) =>
    match y as y0 in (proc yr) return { mkP xn xa yr = y0}+{True} with
    | mkP yn ya yr =>
     match pos_eq_dec xn yn with
     | left H =>
      match H in (_ = y0) return {mkP xn xa yr=mkP y0 ya yr}+{True} with
      | refl_equal =>
       match eq_dec_list T.eq_dec xa ya with
       | left H => 
        match H in (_ = y0) return {mkP xn xa yr=mkP xn y0 yr}+{True} with
        | refl_equal =>left _ (refl_equal (mkP xn xa yr))
        end
       | _ => right _ I
       end
      end
     | _ => right _ I
     end
    end
  end y.

 Lemma eq_dec_r : forall t (x y:proc t) i, eq_dec x y = right _ i -> x <> y.
 Proof.
  destruct x; destruct y; simpl; intros i.
  generalize (@pos_eq_dec_r pname pname0); case (pos_eq_dec pname pname0); intro e.
  case e.
  generalize (@eq_dec_list_r _ T.eq_dec T.eq_dec_r targs targs0);
   case (eq_dec_list T.eq_dec targs targs0); intro e0.
  case e0.
  intros; discriminate.
  intros; intro.
  apply (H e0); trivial; injection H2; trivial.
  intros; intro.
  apply (H e); trivial; inversion H1; trivial.
 Qed.

 Definition targs t (p:proc t) : list T.type := let (_, l, _) := p in l.

 (* Dependant Equality *)
 Lemma eq_dec2 : forall t (p1 p2 : proc t), {p1 = p2} + {p1 <> p2}.
 Proof.
  intros t p1 p2; generalize (eqb_spec p1 p2); case (eqb p1 p2); auto. 
 Qed.
 
 Lemma eq_dep_eq : forall t (P:proc t->Type) (p:proc t) (x y:P p), 
  eq_dep (proc t) P p x p y -> x = y.
 Proof.
  intros t; apply (eq_rect_eq__eq_dep_eq (proc t) (eq_rect_eq_dec (@eq_dec2 t))).
 Qed.

 Lemma UIP_refl : forall t (x:proc t) (p:x = x), p = refl_equal x.
 Proof.
  intros t; apply (UIP__UIP_refl (proc t) (eq_dep_eq__UIP (proc t) (@eq_dep_eq t))).
 Qed.

 Lemma inj_pair2 : forall t (P:proc t -> Type) (p:proc t) (x y:P p),
  existT P p x = existT P p y -> x = y. 
 Proof.
  intros t; apply (eq_dep_eq__inj_pairT2 (proc t) (@eq_dep_eq t)).
 Qed.

End MakeProc.
