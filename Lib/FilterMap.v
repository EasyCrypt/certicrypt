(** FilterMap.v : Dependent filter and map *)

Require Import List.
Require Import BoolEquality.
Require Export EqdepFacts.
Require Export Eqdep_dec.
Require Import Arith.

Set Implicit Arguments.


Fixpoint filter_map (A B:Type) 
 (P:A -> bool) (f:forall a, P a -> B) (l:list A) {struct l} : list B :=
 match l with
  | nil => nil
  | a :: l' =>
   (if P a as b return P a = b -> list B 
    then fun H:P a => f a H :: filter_map P f l'
    else fun _ => filter_map P f l') 
   (refl_equal (P a))    
 end.

Lemma UIP_bool : UIP_ bool.
Proof.
 apply eq_dep_eq__UIP; red.
 apply eq_dep_eq_dec.
 intros [ | ] [ | ]; auto.
 right; discriminate.
Qed. 

Lemma In_filter_map : forall (A B:Type) (P:A -> bool) (f:forall a, P a -> B) 
 (l:list A) (a:A) (H:P a) (Hin:In a l),
 In (f a H) (filter_map P f l).
Proof.
 induction l; intros; destruct Hin; simpl; subst.
 unfold is_true in *.
 generalize (f a0); destruct (P a0); intros.
 rewrite (UIP_bool H (refl_equal true)).
 constructor; trivial.
 discriminate.
 generalize (f a); destruct (P a); intros.
 constructor 2; auto.
 auto.
Qed. 

Lemma filter_map_In : forall (A B:Type) (P:A -> bool) (f:forall a, P a -> B) 
 (l:list A) b,
 In b (filter_map P f l) ->
 exists a, exists H, b = f a H /\ In a l.
Proof.
 induction l; simpl; intros b H.
 elim H.

 case_eq (P a); intro Ha.
 assert (In b (f a Ha :: filter_map P f l)).
 generalize (f a) H; clear H; destruct (P a); [ | discriminate].
 rewrite (UIP_bool Ha (refl_equal true)); trivial.

 destruct (in_inv H0).
 exists a; exists Ha; auto.

 destruct (IHl _ H1) as [a0 Ha0].
 exists a0; destruct Ha0 as [Ha0 [H2 H3] ]; exists Ha0; auto.

 generalize (f a) H; clear H; destruct (P a); [discriminate | ].
 intros.
 destruct (IHl _ H) as [a0 Ha0].
 exists a0; destruct Ha0 as [Ha0 [H2 H3] ]; exists Ha0; auto.
Qed. 

Lemma filter_map_app : forall (A B:Type) (P:A -> bool) (f:forall a, P a -> B) 
 (l1 l2:list A), 
 filter_map P f (l1 ++ l2) = filter_map P f l1 ++ filter_map P f l2.
Proof.
 induction l1; simpl.
 trivial.
 generalize (f a); destruct (P a); intros.
 rewrite IHl1; trivial.
 trivial.
Qed.

Lemma filter_map_length : forall (A B:Type) (P:A -> bool) (f:forall a, P a -> B) 
 (l:list A), 
 (length (filter_map P f l) <= length l)%nat.
Proof.
 induction l; simpl.
 trivial.
 generalize (f a); destruct (P a); intros; simpl.
 apply le_n_S; trivial.
 apply le_S; trivial.
Qed.


Hint Constructors NoDup.

Lemma NoDup_filter_map_inj : forall (A B:Type) (P:A -> bool) (f:forall a, P a -> B),
 (forall x y H1 H2, f x H1 = f y H2 -> x = y) -> 
 forall l, NoDup l -> NoDup (filter_map P f l).
Proof.
 induction l; simpl; intros.
 constructor.

 inversion_clear H0.
 generalize (f a) (H a); destruct (P a); intros.
 constructor.
 intro Hin.
 apply filter_map_In in Hin; destruct Hin as [a0 [Ha0 [H3 H4] ] ].
 assert (In a l) by (rewrite (H0 a0 _ Ha0 H3); trivial).
 auto.
 auto.
 auto.
Qed.
