(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * BoolEquality.v : Reflection of [bool] into [Prop].
   Modules and functors for types with boolean and decidable equality *)

Set Implicit Arguments.
Global Unset Automatic Introduction.
Global Set Automatic Coercions Import.

Require Export Bool.
Require Export Setoid.
Require Import List.
Require Import BinPos Ndec.

Definition is_true b := b = true.
Definition notb b := b = false.
Definition impb b1 b2 := negb b1 || b2 .

(* Coercion from [bool] to [Prop], enables reflection *)
Coercion is_true : bool >-> Sortclass.

Lemma fold_is_true : forall b, is_true b -> b = true.
 trivial.
Qed.

Lemma iff_eq : forall b1 b2:bool, (b1 <-> b2) <-> b1 = b2.
Proof.
 unfold is_true,iff; intros b1 b2; destruct b1; destruct b2; intuition. 
Qed.

Lemma true_false_elim : forall (A:Type), notb true -> A.
Proof.
 intros; discriminate.
Qed.

Lemma false_true_elim : forall (A:Type), false -> A.
Proof. 
 intros; discriminate.
Qed.

Lemma is_true_true : is_true true.
Proof refl_equal true.

Lemma notb_false : notb false.
Proof refl_equal false.

Lemma is_true_andb : forall b1 b2:bool, b1 && b2 <-> (b1 /\ b2).
Proof.
 unfold andb, is_true; destruct b1; destruct b2; simpl; tauto.
Qed.

Lemma is_true_orb : forall b1 b2:bool, b1 || b2 <-> (b1 \/ b2).
Proof.
 unfold orb, is_true; destruct b1; destruct b2; simpl; tauto.
Qed.

Lemma is_true_negb : forall b, negb b <-> ~ b.
Proof.
 unfold notb, is_true; destruct b; simpl; try tauto.
 split; intros H; [discriminate | elim H; trivial].
 split; intros; [discriminate | trivial].
Qed.

Lemma is_true_negb_false : forall b, negb b <-> b = false.
Proof.
 unfold is_true; destruct b; split; simpl; trivial;
 intros; discriminate.
Qed.

Lemma not_is_true_false : forall (b:bool), (~ b) <-> b = false.
Proof.
 intros; rewrite <- is_true_negb.
 apply is_true_negb_false.
Qed.

Lemma is_true_impb : forall b1 b2:bool, impb b1 b2 <-> (b1 -> b2).
Proof.
 unfold impb, is_true; destruct b1; destruct b2; simpl; tauto.
Qed.

Lemma impb_true_r : forall b, impb b true = true.
Proof.
  destruct b; trivial.
Qed.

Lemma is_true_existsb : forall A (f:A -> bool) (l:list A),
 existsb f l <-> (exists x, In x l /\ f x).
Proof.
 unfold is_true; apply existsb_exists.
Qed.

Lemma is_true_forallb : forall A (f:A -> bool) (l:list A),
 forallb f l <-> (forall x, In x l -> f x).
Proof.
 unfold is_true; apply forallb_forall.
Qed.

Hint Rewrite is_true_impb is_true_andb is_true_orb is_true_negb 
 is_true_existsb is_true_forallb : Ris_true.

Ltac bprop := autorewrite with Ris_true.


Lemma if_and : forall (b1 b2:bool), b1 && b2 -> b1 /\ b2.
Proof. 
 destruct b1; intros. 
 split; trivial. 
 exact (refl_equal true).
 apply false_true_elim; trivial.
Qed.

Lemma if_or : forall (b1 b2:bool), b1 || b2 -> b1 \/ b2.
Proof. 
 destruct b1; intros; auto.
Qed.

Lemma if_notb : forall (b:bool), ~ b -> notb b.
Proof.
 unfold notb; destruct b; intros; trivial. 
 elim H; exact (refl_equal true). 
Qed.

Hint Resolve is_true_true notb_false.

Ltac simplb :=
 simpl;
 repeat progress 
 (match goal with
  | H : is_true false -> _ |- _ => clear H
  | H : is_true true -> _ |- _ => 
   let HH := fresh "H" in assert (HH:=H is_true_true); clear H; rename HH into H
  | H : is_true (true && ?b) |- _  => change (is_true b) in H
  | H : is_true (false || ?b) |- _ => change (is_true b) in H
  | H : is_true (?b1 && ?b2) |- _ => destruct (if_and _ _ H); clear H
  | H : is_true (?b1 || ?b2) |- _ => 
   let HH := fresh "H" in 
    assert (HH:=if_or _ _ H); clear H; rename HH into H
  | |- is_true (true && ?b) => change (is_true b)
  | |- is_true (false || ?b) => change (is_true b)
  | H : is_true ?b |- context [ ?b ]  => rewrite H
  | H : is_true ?b, H0 : context [ ?b ] |- _ => rewrite H in H0 
  | H : ~ is_true ?b, H0 : context [ ?b ] |- _ => rewrite (if_notb H) in H0 
  | H : ~ is_true ?b |- context [ ?b ] => rewrite (if_notb H) 
  | H : ?b = true |- context [ ?b ] => rewrite H
  | H : true = ?b |- context [ ?b ] => rewrite <- H
  | H : ?b = true, H0 : context [ ?b ] |- _ => rewrite H in H0
  | H : true = ?b, H0 : context [ ?b ] |- _ => rewrite H in H0  
  | H : ?b = false |- context [ ?b ] => rewrite H
  | H : false = ?b |- context [ ?b ] => rewrite <- H
  | H : ?b = false, H0 : context [ ?b ] |- _ => rewrite H in H0
  | H : false = ?b, H0 : context [ ?b ] |- _ => rewrite H in H0
 end; simpl).

Ltac trivialb := 
 try
 (simplb;
 match goal with 
  | |- is_true true => exact (refl_equal true)
  | |- true = true => exact (refl_equal true)
  | |- notb false => exact (refl_equal false)
  | |- ~ (is_true false) => 
   let H:=fresh "H" in intro; apply (false_true_elim False H)
  | |- false = false => exact (refl_equal false) 
  | H : is_true false |- ?G => apply (false_true_elim G H)
  | H : ~ is_true true |- _ => elim H; trivial
  | H : false = true |- ?G => apply (false_true_elim G H)
  | H : notb true |- ?G  => apply (true_false_elim G H)
  | H : true = false |- ?G => apply (true_false_elim G H)
  | H : False |- _  => elim H
  | H : ~ ?A, H0:?A |- _ => elim (H H0)
  | H : _ /\ _ |- _  => destruct H
  | H : is_true true |- _ => clear H; trivialb
  | H : true = true |- _ => clear H; trivialb
  | _ => trivial
 end).

Ltac autob := trivialb; auto.
Ltac eautob := trivialb; eauto.

Lemma is_true_dec : forall (b:bool), b \/ ~b.
Proof.
 intros [|]; [|right]; autob.
Qed.

Lemma False_false : False <-> false.
Proof. 
 split; intros; trivialb. 
Qed.

Lemma True_true : True <-> true.
Proof. 
 split; intros; trivialb.
Qed.


(** Reflective predicate [forallb] over lists *)
Section FORALLB. 
 
 Variable A : Type.
 Variable P : A -> bool.

 Fixpoint forallb (l:list A) {struct l} : bool := 
  match l with 
   | nil => true
   | a::l => if P a then forallb l else false
  end.

 Lemma forallb_app : forall l1 l2,
  forallb (l1++l2) = if forallb l1 then forallb l2 else false.
 Proof.
  induction l1; trivial.
  simpl; intros l2.
  rewrite IHl1; case (P a); trivial.
 Qed.  

End FORALLB.


(** Boolean equality on lists of elements from a type equipped with 
    boolean equality *) 
Section EQ_LIST.

 Variable t : Type.
 Variable eq : t -> t -> Prop.
 Variable eqb : t -> t -> bool.

 Parameter eq_dec : forall x y, {eq x y} + {~ eq x y}.

 (* Inductively defined equality *)
 Inductive eq_list : list t -> list t -> Prop :=
  | eq_list_nil : eq_list nil nil
  | eq_list_cons : forall x y l l', 
     eq x y -> eq_list l l' -> eq_list (x::l) (y::l').

 (* An [In] predicate parametrized by an equality relation *)
 Inductive InA (x:t) : list t -> Prop :=
  | InA_cons_hd : forall y l, eq x y -> InA x (y :: l)
  | InA_cons_tl : forall y l, InA x l -> InA x (y :: l).

 Lemma InA_dec : forall x l, InA x l \/ ~InA x l.
 Proof.
  induction l.
  right; intros H; inversion H.
  case (eq_dec x a); intro.
  left; constructor; trivial.
  destruct IHl. 
  left; constructor 2; trivial.
  right; intros H1; inversion H1; subst; clear H1; auto.
 Qed.

 Lemma InA_spec : forall x l, InA x l <-> exists y, eq x y /\ In y l.
 Proof.
  induction l; split; intro.
  inversion H.
  firstorder.
  inversion H; firstorder.
  firstorder; subst. 
  constructor; trivial.
  constructor 2; apply H1 with x0; split; trivial.
 Qed.

 Fixpoint eqb_list (l1 l2: list t) {struct l1} :=
  match l1, l2 with
   | nil, nil => true
   | x::l1', y::l2' => 
     if eqb x y then eqb_list l1' l2' else false
   | _, _ => false
  end.
  
End EQ_LIST.

Hint Constructors InA eq_list.


(** Type equipped with both logical and boolean equality *)
Module Type EQDEC.

 Parameter t : Type.
 Parameter eq : t -> t -> Prop.
 Parameter eqb : t -> t -> bool.

 Parameter eqb_spec : forall x y, if eqb x y then eq x y else ~ eq x y.
 Parameter eq_refl : forall x, eq x x.
 Parameter eq_sym : forall x y, eq x y -> eq y x.
 Parameter eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
 
 Add Relation t eq 
  reflexivity proved by eq_refl
  symmetry proved by eq_sym
  transitivity proved by eq_trans as eq_setoid.

 Hint Immediate eq_refl eq_sym.
 Hint Resolve eq_trans.

End EQDEC.


(** Functor extending [EQDEC] *)
Module MkEqDec_Theory (E:EQDEC).

 Import E.

 Hint Immediate eq_sym.
 Hint Resolve eq_refl eq_trans.

 Lemma eq_dec : forall x y, {eq x y} + {~ eq x y}.
 Proof.
  intros x y.
  generalize (eqb_spec x y); case (eqb x y); auto.
 Qed.

 Lemma eq_eqb_l : forall x y, eq x y -> eqb x y.
 Proof.
  intros x y; assert (W:=E.eqb_spec x y); intro; 
   destruct (eqb x y); autob.
 Qed.

 Lemma eq_eqb_r : forall x y, eqb x y -> eq x y.
 Proof.
  intros x y; assert (W:=E.eqb_spec x y); intro; 
   destruct (eqb x y); autob.
 Qed.

 Hint Resolve eq_eqb_l eq_eqb_r.

 Lemma eq_eqb : forall x y, eq x y <-> eqb x y.
 Proof. 
  split; auto. 
 Qed.

 Lemma neq_neqb_l : forall x y, ~ eq x y -> ~ eqb x y.
 Proof.
  intros x y H H0; rewrite eq_eqb in H; auto.
 Qed.

 Lemma neq_neqb_r : forall x y, ~ eqb x y -> ~ eq x y.
 Proof.
  intros x y H H0; rewrite eq_eqb in H0; auto.
 Qed.

 Hint Resolve neq_neqb_l neq_neqb_r.

 Lemma neq_neqb : forall x y, ~ eq x y <-> ~ eqb x y.
 Proof. 
  split; auto. 
 Qed.

 Lemma eqb_refl : forall x, eqb x x.
 Proof. 
  intro; rewrite <- eq_eqb; auto. 
 Qed.

 (* TODO: Think about changing the conclusion to [eqb x y = eqb y x] *)
 Lemma eqb_sym : forall x y, eqb x y -> eqb y x.
 Proof.  
  intros x y; repeat rewrite <- eq_eqb; auto.
 Qed.
 
 Lemma eqb_trans : forall x y z, eqb x y -> eqb y z -> eqb x z.
 Proof.
  intros x y z; repeat rewrite <- eq_eqb; eauto.
 Qed.

 Hint Resolve eqb_refl eqb_trans.
 Hint Immediate eqb_sym.

 Definition eq_list := eq_list eq.
 Definition eqb_list := eqb_list eqb.

 Hint Unfold eq_list eqb_list.

 Lemma eqb_list_spec : forall l l', 
  if eqb_list l l' then eq_list l l' else ~ eq_list l l'.
 Proof.
  induction l; destruct l'; autob.
  intro; inversion H.
  intro; inversion H.
  generalize (eqb_spec a t0); generalize (IHl l'). 
  case (eqb a t0); case (eqb_list l l'); intros; simpl.
  constructor; trivial.
  intro W; inversion_clear W; trivialb.
  intro W; inversion_clear W; trivialb.
  intro W; inversion_clear W; trivialb.
 Qed.

 Lemma eq_list_refl : forall l, eq_list l l.
 Proof.
  induction l; auto.
 Qed.

 Lemma eq_list_sym : forall l1 l2, eq_list l1 l2 -> eq_list l2 l1.
 Proof.
  induction l1; destruct l2; trivial.
  intro W; inversion W.
  intro W; inversion W.
  intro W; inversion W; auto.
  constructor; auto.
  apply IHl1; trivial.
 Qed.

 Lemma eq_list_trans : forall l1 l2 l3,
  eq_list l1 l2 -> eq_list l2 l3 -> eq_list l1 l3.
 Proof.
  induction l1; destruct l2; destruct l3; intros; auto.
  inversion H.
  inversion H.
  inversion H0.
  inversion H; inversion H0.
  constructor; eauto.
  eapply IHl1; eauto.
 Qed.

 Lemma eqb_list_refl : forall l:list t, eqb_list l l.   
 Proof.
  intro l.
  generalize (eqb_list_spec l l).
  case (eqb_list l l).
  trivial.
  intro H; elim H; apply eq_list_refl.
 Qed.

 Add Relation (list t) eq_list 
  reflexivity proved by eq_list_refl
  symmetry proved by eq_list_sym
  transitivity proved by eq_list_trans as eq_list_setoid.

(* REMARK: it seems this is not so useful
 Add Morphism eqb : eqb_morphism.
 Proof.
  intros.
  case_eq (eqb x1 x0); intros.
  symmetry.
  change (eqb x2 x3); rewrite <- eq_eqb.
  transitivity x1; auto.
  change (eqb x1 x0) in H1; rewrite <- eq_eqb in H1.
  transitivity x0; auto.
  case_eq (eqb x2 x3); intros; auto.
  rewrite <- H1.
  change (eqb x1 x0); rewrite <- eq_eqb.
  transitivity x2; auto.
  change (eqb x2 x3) in H2; rewrite <- eq_eqb in H2.
  transitivity x3; auto.
 Qed.
*)

End MkEqDec_Theory.


(** Type equipped with a boolean function that decides Leibniz equality *)
Module Type EQBOOL_LEIBNIZ.

  Parameter t : Type.
  Parameter eqb : t -> t -> bool.

  Parameter eqb_spec : forall x y, if eqb x y then x = y else x <> y.

End EQBOOL_LEIBNIZ.


(** Functor constructing a [EQDEC] module for a type equipped
    with a boolean function that decides Leibniz equality *)
Module MkEqBool_Leibniz (E:EQBOOL_LEIBNIZ) <: EQDEC
 with Definition t := E.t
 with Definition eq := @eq E.t
 with Definition eqb := E.eqb.

 Definition t := E.t.
 Definition eq := @eq E.t.
 Definition eqb := E.eqb.

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof E.eqb_spec.

 Lemma eq_refl : forall x:t, x = x.
 Proof. 
  trivial. 
 Qed.

 Lemma eq_sym : forall x y:t, x = y -> y = x.
 Proof. 
  auto. 
 Qed.

 Lemma eq_trans : forall x y z:t, x = y -> y = z -> x = z.
 Proof. 
  intros; transitivity y; trivial. 
 Qed.

 Add Relation t eq 
  reflexivity proved by eq_refl
  symmetry proved by eq_sym
  transitivity proved by eq_trans as eq_setoid.

End MkEqBool_Leibniz. 


(** Functor extending [EQBOOL_LEIBNIZ] *)
Module MkEqBool_Leibniz_Theory (E:EQBOOL_LEIBNIZ).
 
 Module Edec:= MkEqBool_Leibniz E.
 Module EP := MkEqDec_Theory Edec.
 
 Lemma eq_dec : forall x y:E.t, {x = y} + {x <> y}.
 Proof EP.eq_dec.

 Lemma eq_eqb_l : forall x y, x = y -> E.eqb x y.
 Proof EP.eq_eqb_l.

 Lemma eq_eqb_r : forall x y, E.eqb x y -> x = y.
 Proof EP.eq_eqb_r.

 Hint Resolve eq_eqb_l eq_eqb_r.

 Lemma eq_eqb : forall x y, x = y <-> E.eqb x y.
 Proof EP.eq_eqb.

 Lemma neq_neqb_l : forall x y, x <> y -> ~ E.eqb x y.
 Proof EP.neq_neqb_l.

 Lemma neq_neqb_r : forall x y, ~ E.eqb x y -> x <> y.
 Proof EP.neq_neqb_r.

 Hint Resolve neq_neqb_l neq_neqb_r.

 Lemma neq_neqb : forall x y, x <> y <-> ~ E.eqb x y.
 Proof EP.neq_neqb. 

 Lemma eqb_refl : forall x, E.eqb x x.
 Proof EP.eqb_refl.

 Lemma eqb_sym : forall x y, E.eqb x y -> E.eqb y x.
 Proof EP.eqb_sym.
 
 Lemma eqb_trans : forall x y z, E.eqb x y -> E.eqb y z -> E.eqb x z.
 Proof EP.eqb_trans.

 Definition eqb_list := eqb_list E.eqb.

 Hint Unfold eqb_list.

 Lemma eqb_list_spec : forall l l', 
  if eqb_list l l' then l = l' else l <> l'.
 Proof.
  induction l; destruct l'; trivialb; try discriminate.
  generalize (E.eqb_spec a t); generalize (IHl l'). 
  case (E.eqb a t); case (eqb_list l l'); intros; subst.
  trivial.
  intro W; injection W; trivial.
  intro W; injection W; trivial.
  intro W; injection W; trivial.
 Qed.

End MkEqBool_Leibniz_Theory.


(** Type equipped with boolean equality *)
Module Type EQBOOL.

 Parameter t : Type.
 Parameter eqb : t -> t -> bool.

 Parameter eqb_refl : forall x, eqb x x.
 Parameter eqb_sym : forall x y, eqb x y -> eqb y x.
 Parameter eqb_trans : forall x y z, eqb x y -> eqb y z -> eqb x z.

 (* REMARK: the boolean relation [eqb] coerced to a logical relation may be
    declared as a setoid relation *)

End EQBOOL.

(** Functor constructing a [EQDEC] module from a type equipped only with 
    boolean equality *)
Module MkEqBool (E:EQBOOL) <: EQDEC
 with Definition t := E.t
 with Definition eqb := E.eqb.

 Definition t := E.t.
 Definition eq : t -> t -> Prop := E.eqb.
 Definition eqb := E.eqb.
 
 Lemma eqb_spec : forall x y, if eqb x y then eq x y else ~ eq x y.
  intros; unfold eq, eqb; destruct (E.eqb x y); autob.
 Qed.

 Lemma eq_refl : forall x, eq x x. 
 Proof E.eqb_refl.

 Lemma eq_sym : forall x y, eq x y -> eq y x.
 Proof E.eqb_sym.
 
 Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
 Proof E.eqb_trans.

 Add Relation t eq 
  reflexivity proved by eq_refl
  symmetry proved by eq_sym
  transitivity proved by eq_trans as eq_setoid.

End MkEqBool. 


(** A functor thtat constructs a sum type equipped with decidable Leibniz 
    equality from two types equipped with decidable Leibniz equality *)
Module MkEqBoolLeibniz_Sum (E1 E2:EQBOOL_LEIBNIZ) <: EQBOOL_LEIBNIZ.
 
 Definition t := (E1.t + E2.t)%type.

 Definition eqb e1 e2 :=
  match e1, e2 with
  | inl x, inl y => E1.eqb x y
  | inr x, inr y => E2.eqb x y
  | _, _ => false
  end.

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  destruct x; destruct y; simpl; try (intro; discriminate).
  assert (W:=E1.eqb_spec t0 t1); destruct (E1.eqb t0 t1).
  subst; trivial. 
  intro H; apply W; inversion H; trivial.
  assert (W:=E2.eqb_spec t0 t1); destruct (E2.eqb t0 t1).
  subst; trivial.
  intro H; apply W; inversion H; trivial.
 Qed.

End MkEqBoolLeibniz_Sum.


(** A functor thtat constructs a sum type equipped with boolean equality 
    from two types equipped with boolean equality *)
Module MkEqBool_Sum (E1 E2 : EQBOOL) <: EQBOOL 
  with Definition t := (E1.t + E2.t)%type.

 Definition t := (E1.t + E2.t)%type.

 Definition eqb e1 e2 :=
  match e1, e2 with
  | inl x, inl y => E1.eqb x y
  | inr x, inr y => E2.eqb x y
  | _, _ => false
  end.

 Lemma eqb_refl : forall x, eqb x x.
 Proof.
  destruct x; simpl; auto using E1.eqb_refl, E2.eqb_refl.
 Qed.

 Lemma eqb_sym : forall x y, eqb x y -> eqb y x.
 Proof.
  destruct x; destruct y; simpl; auto using E1.eqb_sym, E2.eqb_sym.
 Qed.

 Lemma eqb_trans : forall x y z, eqb x y -> eqb y z -> eqb x z.
 Proof.
  destruct x; destruct y; simpl; intros; trivialb; destruct z; trivialb;
   eauto using E1.eqb_trans, E2.eqb_trans.
 Qed.

End MkEqBool_Sum.


(** An instance of [EQBOOL_LEIBNIZ] for positive numbers *)
Module PosEq <: EQBOOL_LEIBNIZ.

 Definition t := positive.

 Definition eqb := Peqb.

 Definition eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  intros; case_eq (eqb x y); intros.
  apply Pcompare_Eq_eq. 
  apply Peqb_Pcompare; trivial.
  intros Heq; subst. 
  rewrite Pcompare_Peqb in H.
  discriminate.
  apply Pcompare_refl.
 Qed.

End PosEq.

Module PosEqP := MkEqBool_Leibniz_Theory PosEq.

(** Instance of [EQBOOL_LEIBNIZ] for the sum type [positive + positive] *)
Module SumPosEq := MkEqBoolLeibniz_Sum PosEq PosEq.
Module SumPosEqP := MkEqBool_Leibniz_Theory SumPosEq.
