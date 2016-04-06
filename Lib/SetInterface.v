(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * SetInterface.v : An abstract interface for sets
   and an implementation using lists *)

Set Implicit Arguments.

Require Export BoolEquality.
Require Export List.


(** Abstract interface for sets of elements of a type equipped 
    with boolean equality *)
Module Type SET.

 Declare Module E : EQDEC.
 Export E.

 Parameter t : Type. 

 (** Boolean equality *)
 Parameter eqb : t -> t -> bool.
 Definition eq : t -> t -> Prop := eqb.

 (** The empty set *)
 Parameter empty : t.

 (** [mem x s] tests whether [x] belongs to the set [s] *) 
 Parameter mem : E.t -> t -> bool.

 (** [add x s] returns a set containing all elements of [s], plus [x]. 
     If [x] was already in [s], [s] is returned unchanged. *)
 Parameter add : E.t -> t -> t.

 (** [singleton x] returns the one-element set containing only [x] *)
 Parameter singleton : E.t -> t.

 (** [remove x s] returns a set containing all elements of [s], except [x]. 
     If [x] was not in [s], [s] is returned unchanged *)
 Parameter remove : E.t -> t -> t.

 (** Set union *)
 Parameter union : t -> t -> t.

 (** Set intersection *)
 Parameter inter : t -> t -> t.

 (** Set difference *)
 Parameter diff : t -> t -> t.

 (** [subset s1 s2] tests whether the set [s1] is a subset of the set [s2] *)
 Parameter subsetb : t -> t -> bool.
 Definition subset: t -> t -> Prop := subsetb.

 (** Lists the elements of the set in some unspecified order *)
 Parameter elements : t -> list E.t.

 (** [fold f s] a computes (f xN ... (f x2 (f x1 a))...), 
     where [x1 ... xN] is the result of [elements s] *)
 Parameter fold : forall A : Type, (E.t -> A -> A) -> t -> A -> A.

 Parameter filter : (E.t -> bool) -> t -> t.

 Parameter forallb : (E.t -> bool) -> t -> bool.

 Notation "s [=] t" := (eq s t) (at level 70, no associativity).
 Notation "s [<=] t" := (subset s t) (at level 70, no associativity).
 Notation "s '[=?]' t" := (eqb s t) (at level 70, no associativity).
 Notation "s '[<=?]' t" := (subsetb s t) (at level 70, no associativity).

 Definition disjoint s1 s2 := eqb (inter s1 s2) empty.
 
 Hint Unfold disjoint.


 (** * Specification *)
 
 (** Specification of [subset] *)
 Parameter subset_correct : forall s1 s2, 
  s1 [<=] s2 -> (forall x, mem x s1 -> mem x s2).

 Parameter subset_complete : forall s1 s2, 
  (forall x, mem x s1 -> mem x s2) -> s1 [<=] s2.

 (** Specification of [eq] *)
 Parameter eq_correct_l : forall s1 s2,
  s1 [=] s2 -> s1 [<=] s2.
 
 Parameter eq_correct_r : forall s1 s2,
  s1 [=] s2 -> s2 [<=] s1.

 Parameter eq_complete : forall s1 s2,
  s1 [<=] s2 -> s2 [<=] s1 -> s1 [=] s2.


 (** Specification of [empty] *)
 Parameter empty_spec : forall x, ~mem x empty.


 (** Specification of [mem] *)
 Parameter mem_correct : forall x y s,
  E.eq x y -> mem x s -> mem y s.

 
 (** Specification of [add] *)
 Parameter add_correct : forall x y s,
  E.eq x y -> mem y (add x s).
 
 Parameter add_complete : forall x y s,
  mem y s -> mem y (add x s).

 Parameter add_inversion : forall x y s,
  ~E.eq x y -> mem y (add x s) -> mem y s.


 (** Specification of [singleton] *)
 Parameter singleton_correct : forall x y,
  E.eq x y -> mem y (singleton x).

 Parameter singleton_complete : forall x y,
  mem y (singleton x) -> E.eq x y.


 (** Specification of [remove] *)
 Parameter remove_correct : forall x y s,
  E.eq x y -> ~mem x (remove y s).

 Parameter remove_complete : forall x y s,
  ~E.eq x y -> mem y s -> mem y (remove x s).

 Parameter remove_inversion : forall x y s,
  mem y (remove x s) -> mem y s.


 (** Specification of [union] *)
 Parameter union_correct : forall s1 s2 x,
  mem x (union s1 s2) -> (mem x s1 \/ mem x s2).

 Parameter union_complete_l : forall s1 s2 x, 
  mem x s1 -> mem x (union s1 s2).

 Parameter union_complete_r : forall s1 s2 x, 
  mem x s2 -> mem x (union s1 s2).


 (** Specification of [inter] *)
 Parameter inter_correct_l : forall s1 s2 x,
  mem x (inter s1 s2) -> mem x s1.

 Parameter inter_correct_r : forall s1 s2 x,
  mem x (inter s1 s2) -> mem x s2.

 Parameter inter_complete : forall s1 s2 x,
  mem x s1 -> mem x s2 -> mem x (inter s1 s2).


 (** Specification of [diff] *)
 Parameter diff_correct_l : forall s1 s2 x, 
  mem x (diff s1 s2) -> mem x s1.

 Parameter diff_correct_r : forall s1 s2 x, 
  mem x (diff s1 s2) -> ~mem x s2.

 Parameter diff_complete : forall s1 s2 x, 
  mem x s1 -> ~mem x s2 -> mem x (diff s1 s2).


 (** Specification of [fold] *)
 Parameter fold_spec : forall A (f:E.t -> A -> A) i s,
  fold f s i = fold_left (fun a x => f x a) (elements s) i.

 (* Alternatively,
 Parameter fold_spec : forall A (f:E.t -> A -> A) i s,
  fold f s i = fold_right f i (elements s). *)

 (** Specification of [forallb] *)
 Parameter forallb_correct : forall f, (forall x y, E.eq x y -> f x = f y) ->
   forall s, forallb f s -> forall x, mem x s -> f x.
 
 Parameter forallb_complete : forall (f:E.t->bool),
   (forall x y, E.eq x y -> f x = f y) ->
   forall s, (forall x, mem x s -> f x) -> forallb f s.

 (** Specification of [elements] *)
 Parameter elements_correct : forall s x, 
  mem x s -> InA E.eq x (elements s).

 Parameter elements_complete : forall s x, 
  InA E.eq x (elements s) -> mem x s.

 (** Specification of filter *)
 Parameter filter_correct : forall (f:E.t->bool) x s,
  (forall x y, E.eq x y -> f x = f y) -> mem x (filter f s) -> mem x s /\ f x.
 
 Parameter filter_complete : forall (f:E.t->bool) x s,
  (forall x y, E.eq x y -> f x = f y) ->
  mem x s -> f x -> mem x (filter f s).

End SET.


(** Functor extending [SET] *)
Module MkSet_Theory (S:SET).

 Export S.

 Module ET := MkEqDec_Theory E.


 Lemma subset_iff : forall s1 s2, 
  s1 [<=] s2 <-> (forall x, mem x s1 -> mem x s2).
 Proof.
  split; [apply subset_correct | apply subset_complete].
 Qed.

 Lemma subset_refl : forall s, s [<=] s.
 Proof.
  auto using subset_complete.
 Qed.

 Lemma subset_trans : forall s s0 s1, 
  s [<=] s0 -> s0 [<=] s1 -> s [<=] s1.
 Proof.
  intros s s0 s1; repeat rewrite subset_iff; firstorder.
 Qed.

 Add Relation t subset 
   reflexivity proved by subset_refl
   transitivity proved by subset_trans
   as subset_relation.
 
 Lemma eq_refl : forall s, s [=] s. 
 Proof. 
  auto using subset_refl, eq_complete.
 Qed.

 Lemma eq_sym : forall s1 s2, 
  s1 [=] s2 -> s2 [=] s1.
 Proof.
  intros; apply eq_complete.
  apply eq_correct_r; trivial.
  apply eq_correct_l; trivial.
 Qed.

 Lemma eq_trans : forall s1 s2 s3,
  s1 [=] s2 -> s2 [=] s3 -> s1 [=] s3.
 Proof.
  intros; apply eq_complete.
  apply subset_trans with s2; apply eq_correct_l; trivial.
  apply subset_trans with s2; apply eq_correct_r; trivial.
 Qed.
 
 Add Relation t eq 
  reflexivity proved by eq_refl
  symmetry proved by eq_sym
  transitivity proved by eq_trans as eq_setoid.

 Add Morphism eqb 
  with signature eq ==> eq ==> (@Logic.eq bool)
  as eqb_morphism.
 Proof.
  intros s1 s2 H s3 s4 H0.
  case_eq (s1 [=?] s3); intros.
  change (s1 [=] s3) in H1.
  symmetry; change (s2 [=] s4).
  transitivity s1.
  symmetry; trivial.
  transitivity s3; auto.
  case_eq (s2 [=?] s4); auto; intros.
  rewrite <- H1; change (s2 [=] s4) in H2.
  change (s1 [=] s3).
  transitivity s2; auto.
  transitivity s4; auto.
  symmetry; trivial.
 Qed.
  
 Add Morphism subsetb 
  with signature eq ==> eq ==> (@Logic.eq bool) 
  as subsetb_morphism.
 Proof. 
  intros s1 s2 H s3 s4 H0.
  case_eq (s1 [<=?] s3); case_eq (s2 [<=?] s4); intros; trivial.

  assert (L:=eq_correct_r H); assert (R:=eq_correct_l H0).
  elim H1.
  symmetry; apply fold_is_true.
  eapply subset_trans; eauto.
  eapply subset_trans; eauto.
  trivialb.

  assert (L:=eq_correct_r H0); assert (R:=eq_correct_l H).
  elim H2.
  apply fold_is_true.
  eapply subset_trans; eauto.
  eapply subset_trans; eauto.
 Qed.

 Add Morphism subset 
  with signature eq ==> eq ==> iff
  as subset_morphism.
 Proof. 
  intros; unfold subset.
  rewrite iff_eq.
  apply subsetb_morphism; trivial.
 Qed.

 Lemma eq_spec : forall s1 s2, 
  s1 [=] s2 <-> (s1 [<=] s2 /\ s2 [<=] s1).
 Proof.
  split; intros.
  auto using eq_correct_l, eq_correct_r.
  apply eq_complete; autob.
 Qed.

 Lemma eqb_eq : forall s1 s2,
  eqb s1 s2 -> s1 [=] s2.
 Proof.
  trivial.
 Qed.

 Add Morphism mem 
  with signature E.eq ==> eq ==> (@Logic.eq bool)
  as mem_morphism.
 Proof.
  intros x y H s1 s2 H0.
  destruct (eq_spec s1 s2).
  destruct (H1 H0); clear H0 H1 H2.
  rewrite <- iff_eq.
  split; eauto using mem_correct, subset_correct.
 Qed.  

 Lemma mem_diff : forall s x y, ~mem x s -> mem y s -> ~E.eq x y.
 Proof.
  intros s x y H H0.
  case (ET.eq_dec x y); intro; trivial.
  rewrite e in H; trivialb.
 Qed.

 Lemma mem_dec : forall x s, {mem x s} + {~mem x s}.
 Proof.
  intros x s; case_eq (mem x s); intro; [left | right]; trivialb.
 Qed.

  
 Add Morphism add 
  with signature E.eq ==> eq ==> eq
  as add_morphism.  
 Proof.
  intros x y H s1 s2 H0. 
  apply eq_complete; apply subset_complete; intros.
  case (ET.eq_dec x0 y); intro.
  apply add_correct; auto.
  apply add_complete.
  rewrite <- H0; rewrite <- H in n.
  apply add_inversion with x; auto. 
  case (ET.eq_dec x0 x); intro.
  apply add_correct; auto.
  apply add_complete.
  rewrite H0; rewrite H in n.
  apply add_inversion with y; auto.
 Qed.
 
 Lemma add_spec : forall a s x, 
  mem x (add a s) <-> (E.eq a x \/ mem x s).
 Proof. 
  split; intros.
  case (ET.eq_dec a x); intro.
  left; trivial.
  right; apply (add_inversion n H).
  destruct H; [apply add_correct | apply add_complete]; trivial.
 Qed.

 Lemma subset_empty : forall s, empty [<=] s.
 Proof.
  intros; apply subset_complete.
  intros; elim (empty_spec H). 
 Qed.

 Lemma subset_add : forall a s, s [<=] (add a s).
 Proof.
  intros; apply subset_complete. 
  intros; apply add_complete; auto.
 Qed.

 Lemma add_idem : forall x s,
  mem x s -> (add x s) [=] s.
 Proof.
  intros x s H; apply eq_complete.
  apply subset_complete; intros y Hy.
  case (ET.eq_dec x y); intro.
  rewrite <- e; trivial.
  apply add_inversion with x; trivial.
  apply subset_add.
 Qed.

 Add Morphism singleton 
  with signature E.eq ==> eq 
  as singleton_morphism.
 Proof.
  intros.
  unfold eq; apply eq_complete; apply subset_complete; intros.
  apply singleton_correct.
  rewrite <- H.
  apply singleton_complete; trivial.
  apply singleton_correct.
  rewrite H.
  apply singleton_complete; trivial.
 Qed.

 Lemma singleton_mem_diff : forall x y, 
  ~E.eq x y -> ~mem y (singleton x).
 Proof.
  intros x y H; case_eq (mem y (singleton x)); intros; autob.
  elim H; apply singleton_complete; trivialb.
 Qed.

 Lemma mem_singleton_diff : forall x y, 
  ~mem y (singleton x) -> ~E.eq x y.
 Proof.
  intros x y H H0. 
  rewrite H0 in H.
  elim H; apply singleton_correct; trivial.
 Qed.

 Add Morphism remove 
  with signature E.eq ==> eq ==> eq 
  as remove_morphism.
 Proof.
  intros x y H s1 s2 H0.
  apply eq_complete; apply subset_complete; intros.
  apply remove_complete.
  rewrite <- H.
  intro H2; elim (remove_correct (E.eq_sym H2) H1).
  rewrite <- H0; apply remove_inversion with x; trivial.
  apply remove_complete.
  rewrite H.
  intro H2; elim (remove_correct (E.eq_sym H2) H1).
  rewrite H0; apply remove_inversion with y; trivial.
 Qed.

 Lemma remove_spec : forall x y s, 
  mem y (remove x s) <-> (mem y s /\ ~E.eq x y).
 Proof. 
  repeat split; intros.
  apply remove_inversion with x; trivial.
  intro H0; elim (remove_correct (E.eq_sym H0) H).
  apply remove_complete; destruct H; auto.
 Qed.

 Lemma subset_remove : forall x s, (remove x s) [<=] s.
 Proof.
  intros; apply subset_complete; intros.
  apply remove_inversion with x; trivial.
 Qed.

 Lemma remove_idem : forall x s,
  ~mem x s -> (remove x s) [=] s.
 Proof.
  intros x s H; apply eq_complete.
  apply subset_remove.
  apply subset_complete; intros y Hy.
  case (ET.eq_dec x y); intro e.
  rewrite e in H; trivialb.
  apply remove_complete; trivial.
 Qed.

 Add Morphism union 
  with signature eq ==> eq ==> eq 
  as union_morphism.
 Proof.
  intros; apply eq_complete; apply subset_complete; intros. 
  destruct (union_correct H1).
  apply union_complete_l; rewrite <- H; trivial.
  apply union_complete_r; rewrite <- H0; trivial.
  destruct (union_correct H1).
  apply union_complete_l; rewrite H; trivial.
  apply union_complete_r; rewrite H0; trivial.
 Qed.

 Lemma union_spec : forall s1 s2 x, 
  mem x (union s1 s2) <-> (mem x s1 \/ mem x s2).
 Proof. 
  split. 
  apply union_correct.
  destruct 1; auto using union_complete_l, union_complete_r.
 Qed.

 Lemma union_sym : forall s1 s2, union s1 s2 [=] union s2 s1.
 Proof.
  intros; rewrite eq_spec; split; apply subset_complete; intros x H;
   rewrite union_spec in *; destruct H; auto.
 Qed.

 Lemma union_empty : forall s, union empty s [=] s.
 Proof.
  intros; apply eq_complete; apply subset_complete; intros.
  destruct (union_correct H); trivial.
  elim (empty_spec H0).
  apply union_complete_r; trivial.
 Qed.
 
 Lemma subset_union_l : forall s1 s2, s1 [<=] (union s1 s2).
 Proof.
  intros; apply subset_complete; intros.
  apply union_complete_l; auto.
 Qed.

 Lemma subset_union_r : forall s1 s2, s2 [<=] (union s1 s2).
 Proof.
  intros; apply subset_complete; intros.
  apply union_complete_r; auto.
 Qed.

 Lemma union_assoc : forall s1 s2 s3, union (union s1 s2) s3 [=] union s1 (union s2 s3).
 Proof.
  intros; rewrite eq_spec; split; apply subset_complete; intro x;
  repeat rewrite union_spec; tauto.
 Qed.

 Lemma subset_union : forall s1 s2, s1 [<=] s2 -> union s1 s2 [=] s2.
 Proof.
  intros s1 s2; rewrite eq_spec; repeat rewrite subset_iff;
  split; intros; rewrite union_spec in *; intuition.
 Qed.

 Lemma union_idem : forall s, union s s [=] s.
 Proof.
  intros; apply eq_complete; rewrite subset_iff; intros;
  rewrite union_spec in *; intuition.
 Qed.

 Lemma subset_union_ctxt : forall s1 s1' s2 s2', 
   s1 [<=] s1' -> s2 [<=] s2' -> union s1 s2 [<=] union s1' s2'.
 Proof.
  intros s1 s1' s2 s2'; repeat rewrite subset_iff; intros.
  rewrite union_spec in *; intuition.
 Qed.

 Lemma union_subset : forall s1 s2 s3,
  s1 [<=] s3 ->
  s2 [<=] s3 ->
  union s1 s2 [<=] s3.   
 Proof.
  intros; rewrite <- (union_idem s3).
  apply subset_union_ctxt; trivial.
 Qed.

 Add Morphism inter 
  with signature eq ==> eq ==> eq
  as inter_morphism.
 Proof.
  intros s1 s2 H s3 s4 H0.
  apply eq_complete; apply subset_complete; intros. 
  apply inter_complete.
  rewrite <- H; apply inter_correct_l with s3; trivial.
  rewrite <- H0; apply inter_correct_r with s1; trivial.
  apply inter_complete.
  rewrite H; apply inter_correct_l with s4; trivial.
  rewrite H0; apply inter_correct_r with s2; trivial.
 Qed.

 Lemma inter_spec : forall s1 s2 x,
  mem x (inter s1 s2) <-> (mem x s1 /\ mem x s2).
 Proof. 
  repeat split; intros.
  apply inter_correct_l with s2; trivial.
  apply inter_correct_r with s1; trivial.
  apply inter_complete; autob.
 Qed.
 
 Lemma inter_sym : forall s1 s2, inter s1 s2 [=] inter s2 s1.
 Proof.
  intros s1 s2; apply eq_complete; apply subset_complete; 
   eauto using inter_complete, inter_correct_l, inter_correct_r.
 Qed.

 Lemma subset_inter_l : forall s1 s2, (inter s1 s2) [<=] s1.
 Proof.
  intros; apply subset_complete; intros.
  apply inter_correct_l with s2; trivial.
 Qed.

 Lemma subset_inter_r : forall s1 s2, (inter s1 s2) [<=] s2.
 Proof.
  intros; apply subset_complete; intros.
  apply inter_correct_r with s1; trivial.
 Qed.

 Lemma subset_inter : forall s1 s2, 
  s1 [<=] s2 -> inter s1 s2 [=] s1.
 Proof.
  intros.
  apply eq_complete; apply subset_complete; intros.
  eauto using inter_correct_l.
  eauto using inter_complete, subset_correct.
 Qed.

 Lemma inter_idem : forall s, inter s s [=] s.
 Proof.
  intros; rewrite subset_inter.  
  apply eq_refl.
  apply subset_refl.
 Qed.
 	 
 Add Morphism diff 
  with signature eq ==> eq ==> eq
  as diff_morphism.
 Proof.
  intros s1 s2 H s3 s4 H0.
  apply eq_complete; apply subset_complete; intros. 
  apply diff_complete.
  rewrite <- H; apply diff_correct_l with s3; trivial.
  rewrite <- H0; apply diff_correct_r with s1; trivial.
  apply diff_complete.
  rewrite H; apply diff_correct_l with s4; trivial.
  rewrite H0; apply diff_correct_r with s2; trivial.
 Qed.

 Lemma diff_spec : forall s1 s2 x, 
  mem x (diff s1 s2) <-> (mem x s1 /\ ~mem x s2).
 Proof. 
  repeat split; intros.
  apply diff_correct_l with s2; trivial. 
  apply diff_correct_r with s1; trivial.
  apply diff_complete; autob.
 Qed.

 Lemma subset_diff : forall s1 s2, (diff s1 s2) [<=] s1. 
 Proof.
  intros; apply subset_complete; intros.
  apply diff_correct_l with s2; trivial.
 Qed.

 Lemma remove_diff : forall x s, 
  remove x s [=] diff s (singleton x).
 Proof.
  intros; rewrite eq_spec; split; apply subset_complete; intros.
  apply diff_complete.
  eauto using remove_inversion.
  intro H0.
  assert (W:=singleton_complete H0).
  exact (remove_correct (E.eq_sym W) H).
  eauto using remove_complete, mem_singleton_diff, diff_correct_r, 
   diff_correct_l.
 Qed.

 Lemma union_diff_assoc : forall s1 s2 s3, union (diff s1 s3) (diff s2 s3) [=] diff (union s1 s2) s3.
 Proof.
   intros; rewrite eq_spec; split; apply subset_complete; intros;
   repeat (rewrite union_spec in * ||  rewrite diff_spec in * ); tauto.
 Qed.

 Lemma union_diff : forall s1 s2, union (diff s1 s2) s2 [=] union s1 s2.
 Proof.
  intros; rewrite eq_spec; split; apply subset_complete; intros;
   repeat (rewrite union_spec in * ||  rewrite diff_spec in * ); intuition.
  destruct (mem x s2); auto.
  left; split; auto.
  intros; autob.
 Qed.

 (* To declare [elements] and [fold] as morphisms it is necessary to declare 
    equality on lists up to permutation as a relation first (as done in the 
    Coq standard library)*) 

 Lemma elements_empty : elements empty = nil.
 Proof.
  generalize (@elements_complete empty).
  destruct (elements empty); trivial.
  intros; assert (mem t0 empty) by auto.
  elim (empty_spec H0).
 Qed.

 Lemma mem_fold_add_inversion : forall l s x, 
  mem x (fold_left (fun s y => add y s) l s) ->
  InA E.eq x l \/ mem x s.
 Proof.
  induction l; simpl; intros.
  auto.
  case (ET.eq_dec a x); intro.
  auto.
  assert (InA E.eq x l \/ mem x (add a s)).
  apply IHl; trivial.
  destruct H0; auto.
  right; apply (add_inversion n H0).
 Qed.  

 Lemma mem_fold_add_r : forall l s x, 
  mem x s -> mem x (fold_left (fun s y => add y s) l s).
 Proof.
  induction l; simpl; intros.
  trivial.
  auto using add_complete.
 Qed.  

 Lemma mem_fold_add_l : forall s1 s2 x, 
  mem x s1 -> mem x (fold add s1 s2).
 Proof.
  intros s1 s2 x H; rewrite fold_spec; generalize s2; clear s2.
  assert (W:=elements_correct H).
  induction (elements s1); intros; simpl; inversion_clear W.
  auto using mem_fold_add_r, add_correct.
  auto.
 Qed.

 Lemma union_fold : forall s1 s2,
  union s1 s2 [=] fold add s1 s2.
 Proof.
  intros; apply eq_complete; apply subset_complete; intros.
  destruct (union_correct H).
  auto using mem_fold_add_l.
  rewrite fold_spec; auto using mem_fold_add_r.
  rewrite fold_spec in H.
  destruct (mem_fold_add_inversion _ _ H);
   auto using union_complete_l, union_complete_r, elements_complete.
 Qed.  

 Lemma diff_le_compat : forall s1 s2 s1' s2',
     s1 [<=] s1' -> s2' [<=] s2 ->
     diff s1 s2 [<=] diff s1' s2'.
 Proof.
  intros s1 s2 s1' s2'; repeat rewrite subset_iff; intros H H0 x;
  repeat rewrite diff_spec; intuition.
 Qed.

 Hint Resolve subset_complete eq_correct_l eq_correct_r
  eq_complete add_correct add_complete
  singleton_correct singleton_complete remove_correct remove_complete
  union_complete_l union_complete_r inter_correct_l inter_correct_r 
  diff_correct_l diff_correct_r elements_correct
  subset_refl subset_trans eq_refl eq_trans
  subset_empty singleton_mem_diff mem_singleton_diff diff_le_compat: set.
 
 Hint Immediate subset_correct eq_complete mem_correct
  empty_spec union_correct inter_complete diff_complete 
  elements_complete eq_sym subset_empty subset_add subset_remove 
  subset_union_l subset_union_r subset_inter_l subset_inter_r 
  subset_diff remove_diff : set.

 Lemma empty_union : forall s1 s2,
   union s1 s2 [=] empty ->
   s1 [=] empty /\ s2 [=] empty.
 Proof.
  intros; apply eq_spec in H; destruct H.
  split; apply eq_spec; split; auto with set;
  eapply subset_trans; eauto; auto with set.
 Qed.

 Lemma inter_remove_comm : forall x s1 s2, 
  inter (remove x s1) s2 [=] remove x (inter s1 s2).
 Proof.
  intros; apply eq_complete; apply subset_complete; intro;
   rewrite remove_spec; repeat rewrite inter_spec; 
   try rewrite remove_spec; tauto.
 Qed.
  
 Lemma add_remove : forall x s, add x (remove x s) [=] add x s.
 Proof.
  intros; apply eq_complete; apply subset_complete; intro;
   repeat rewrite add_spec; rewrite remove_spec; try tauto.
  assert (W:=E.eqb_spec x x0); destruct (E.eqb x x0); tauto.
 Qed.

 Lemma add_union_comm : forall x s1 s2, 
  add x (union s1 s2) [=] union (add x s1) s2.
 Proof.
   intros; apply eq_complete; apply subset_complete; intro;
    repeat (rewrite union_spec || rewrite add_spec); tauto.
 Qed.

 Lemma add_union_swap : forall x s1 s2, 
  union (add x s1) s2 [=] union s1 (add x s2).
 Proof.
  intros x s1 s2; rewrite (union_sym s1); repeat rewrite <- add_union_comm;
   rewrite union_sym; apply eq_refl.
 Qed.

 Lemma inter_union_comm : forall s1 s2 s3, 
  inter s1 (union s2 s3) [=] union (inter s1 s2) (inter s1 s3).
 Proof.
  intros; apply eq_complete; apply subset_complete; intro;
   repeat (rewrite union_spec || rewrite inter_spec); tauto.
 Qed.

 Lemma union_inter_comm : forall s1 s2 s3,
  union (inter s1 s2) s3 [=] 
  inter (union s1 s3) (union s2 s3).
 Proof.
  intros; apply eq_complete; apply subset_complete; intro;
   repeat (rewrite union_spec || rewrite inter_spec); tauto.
 Qed.

 Lemma empty_dec : forall s, s[=] empty \/ exists x, mem x s.
 Proof.
  intros s; case_eq (elements s); intros.
  left; apply eq_complete; auto with set.
  apply subset_complete; intros.
  assert (U:=elements_correct H0); rewrite H in U; inversion U.
  right; exists t0; apply elements_complete. 
  rewrite H; constructor; trivial. 
 Qed.

 Lemma subset_remove_ctxt : forall x s1 s2, 
  s1 [<=] s2 -> remove x s1 [<=] remove x s2.
 Proof.
  intros x s1 s2; repeat rewrite subset_iff; intros.
  rewrite remove_spec in *; intuition.
 Qed.

 Lemma subset_inter_ctxt : forall s1 s1' s2 s2', 
   s1 [<=] s1' -> s2 [<=] s2' -> inter s1 s2 [<=] inter s1' s2'.
 Proof.
  intros s1 s1' s2 s2'; repeat rewrite subset_iff; intros.
  rewrite inter_spec in *; intuition.
 Qed.

 Lemma subset_add_ctxt : forall x s1 s2,
   s1 [<=] s2 -> (add x s1) [<=] (add x s2).
 Proof.
  intros x s1 s2; repeat rewrite subset_iff; intros.
  rewrite add_spec in *; intuition.
 Qed.

 Lemma disjoint_sym : forall s1 s2, disjoint s1 s2 -> disjoint s2 s1.
 Proof.
  unfold disjoint; intros; rewrite inter_sym; trivial.
 Qed.

 Lemma disjoint_subset_l : forall X Y Z,
  X [<=] Y ->
  disjoint Y Z ->
  disjoint X Z.
 Proof.
  unfold disjoint; intros X Y Z Hsub Heq.
  apply eq_complete; auto with set.
  change (inter Y Z [=] empty) in Heq.
  rewrite <- Heq.
  apply subset_inter_ctxt; auto with set.
 Qed.
 
 Lemma disjoint_mem_not_mem : forall s1 s2,
  disjoint s1 s2 -> forall x, mem x s1 -> ~mem x s2.
 Proof.
  unfold disjoint; intros s1 s2 H x H1 H2.
  assert (mem x (inter s1 s2)) by auto using inter_complete.
  change (inter s1 s2 [=] empty) in H.
  rewrite H in H0; elim (empty_spec H0).
 Qed.

 Lemma disjoint_complete : forall X1 X2, 
      (forall x, mem x X1 -> ~mem x X2) -> disjoint X1 X2.
 Proof.
  unfold disjoint; intros.
  change ((inter X1 X2) [=] empty).
  apply eq_complete; apply subset_complete; intros.
  rewrite inter_spec in H0; destruct H0.
  elim (H _ H0 H1).
  elim (empty_spec H0).
 Qed.

 Lemma filter_union : forall s f,
  (forall x y, E.eq x y -> f x = f y) ->
  s [=] union (filter f s) (filter (fun x => negb (f x)) s).
 Proof.
  intros s f Hf.
  assert (Hnf: forall x y, E.eq x y -> negb (f x) = negb (f y)) by
   (intros y z Heq; rewrite (Hf _ _ Heq); trivial).
  
  apply eq_complete.
  apply subset_complete; intros x Hx.
  case_eq (f x); intro H.
  apply union_complete_l; apply filter_complete; trivial.
  apply union_complete_r; apply filter_complete; trivialb.

  apply subset_complete; intros x Hx.
  destruct (union_correct Hx). 
  destruct (filter_correct Hf H); trivial.
  destruct (filter_correct Hnf H); trivial.
 Qed.

 Lemma filter_subset : forall s f,
  (forall x y, E.eq x y -> f x = f y) ->
  (filter f s) [<=] s.
 Proof.
  intros s f Hf; apply subset_complete; intros x Hx.
  generalize (filter_correct Hf Hx); intuition.
 Qed.

End MkSet_Theory.


(** A concrete implementation of [SET] using lists *)
Module MkListSet (X:EQDEC) <: SET.

 Module E := X.
 Module ET := MkEqDec_Theory X.

 Definition t := list X.t.

 Definition empty : t := nil.

 Definition singleton (x:X.t) : t := x::nil.

 Fixpoint mem (x:X.t) (s:t) {struct s} : bool :=
  match s with
   | nil => false
   | y :: s' => if X.eqb x y then true else mem x s'
  end.
 
 Fixpoint add (x:X.t) (s:t) {struct s} : t :=
  match s with
   | nil => x::nil
   | y :: s' => if X.eqb x y then y :: s' else y :: add x s'
  end.
 
 Fixpoint remove (x:X.t) (s:t) {struct s} : t :=
  match s with
   | nil => nil
   | y::s' => if X.eqb x y then remove x s' else y::remove x s'
  end.

 Fixpoint inter (s1 s2:t) {struct s1} : t :=
  match s1 with
   | nil => nil
   | y :: s1' => if mem y s2 then y :: inter s1' s2 else inter s1' s2
  end.

 Fixpoint union (s1 s2:t) {struct s1} : t :=
  match s1 with
   | nil => s2
   | y :: s1' =>  union s1' (add y s2)
  end.

 Fixpoint diff (s1 s2:t) {struct s2} : t :=
  match s2 with
   | nil => s1
   | x :: s2' => remove x (diff s1 s2')
  end.

 Fixpoint subsetb (s1 s2:t) {struct s1} : bool :=
  match s1 with
   | nil => true
   | x :: s1' => if mem x s2 then subsetb s1' s2 else false
  end.

 Definition filter : (E.t -> bool) -> t -> t := @List.filter E.t.

 Definition eqb (s1 s2:t) : bool :=
  if subsetb s1 s2 then subsetb s2 s1 else false.


 Definition subset : t -> t -> Prop := subsetb.

 Definition eq : t -> t -> Prop := eqb.

 Definition elements (s:t) : list E.t := s.

 Definition fold (A:Type) (f:X.t -> A -> A) (s:t) (i:A) := 
  fold_left (fun a x => f x a) s i. 

 Definition forallb (f:X.t ->bool) := 
  Eval cbv beta delta [List.forallb andb ifb] in List.forallb f.

 Notation "s [=] t" := (eq s t) (at level 70, no associativity).
 Notation "s [<=] t" := (subset s t) (at level 70, no associativity).
 Notation "s '[=?]' t" := (eqb s t) (at level 70, no associativity).
 Notation "s '[<=?]' t" := (subsetb s t) (at level 70, no associativity).

 Definition disjoint s1 s2 := eqb (inter s1 s2) empty.


 (** * Specification *)

 (** Specification of [mem] *)
 Lemma mem_correct : forall x y s,
  X.eq x y -> mem x s -> mem y s.
 Proof.
  induction s; trivial. 
  simpl; intros.
  case (ET.eq_dec x a); intro.
  assert (X.eqb y a) by eauto.
  trivialb.

  rewrite H in n.
  assert (~X.eqb x a) by eauto.
  rewrite ET.neq_neqb in n.
  autob.
 Qed.


 (** Specification of [subset] *)
 Lemma subset_correct : forall s1 s2, 
  s1 [<=] s2 -> (forall x, mem x s1 -> mem x s2).
 Proof.
  unfold subset; induction s1; simpl; intros; autob.
  case_eq (mem a s2); intro.
  case_eq (X.eqb x a); intro.
  apply mem_correct with a; auto. 
  rewrite H1 in H; rewrite H2 in H0; autob.
  rewrite H1 in H; trivialb.
 Qed.

 Lemma subset_complete : forall s1 s2, 
  (forall x, mem x s1 -> mem x s2) -> s1 [<=] s2.
 Proof.
  unfold subset; induction s1; simpl; intros; autob.
  assert (W:=H a).
  assert (X.eqb a a) by auto.
  simplb.
  apply IHs1; intros.
  apply H; intros.
  case (X.eqb x a); trivialb.
 Qed.  


 (** Specification of [eqb] *)
 Lemma eq_correct_l : forall s1 s2,
  s1 [=] s2 -> s1 [<=] s2.
 Proof.
  intros s1 s2; unfold eq, eqb, subset.
  case (s1 [<=?] s2); trivial.
 Qed.
 
 Lemma eq_correct_r : forall s1 s2,
  s1 [=] s2 -> s2 [<=] s1.
 Proof.
  intros s1 s2; unfold eq, eqb, subset.
  case (s2 [<=?] s1); case (s1 [<=?] s2); trivial.
 Qed.

 Lemma eq_complete : forall s1 s2,
  s1 [<=] s2 -> s2 [<=] s1 -> s1 [=] s2.
 Proof.
  unfold eq, eqb, subset; intros; trivialb.
 Qed.


 (** Specification of [empty] *)
 Lemma empty_spec : forall x, ~mem x empty.
 Proof.
  intros x; unfold empty; trivialb.
 Qed.

 
 (** Specification of [add] *)
 Lemma add_correct : forall x y s,
  X.eq x y -> mem y (add x s).
 Proof.
  induction s; simpl; intros.
  assert (X.eqb y x) by auto; trivialb.

  case (ET.eq_dec x a); intro.
  assert (X.eqb x a) by auto; assert (X.eqb y a) by eauto; trivialb; simpl; 
   trivialb.
  assert (~X.eqb y a) by eauto; rewrite ET.eq_eqb in n.
  rewrite (if_notb n); simpl.
  rewrite (if_notb H0); auto.
 Qed.
  
 
 Lemma add_complete : forall x y s,
  mem y s -> mem y (add x s).
 Proof.
  induction s; simpl; intros.
  trivialb.
  case (X.eqb x a); simpl; destruct (X.eqb y a); autob.
 Qed.

 Lemma add_inversion : forall x y s,
  ~X.eq x y -> mem y (add x s) -> mem y s.
 Proof.
  induction s; simpl; intros.
  assert (~X.eqb y x) by auto.
  rewrite (if_notb H1) in H0; trivialb.
  destruct (X.eqb x a); simpl in H0; destruct (X.eqb y a); autob.
 Qed.


 (** Specification of [singleton] *)
 Lemma singleton_correct : forall x y,
  X.eq x y -> mem y (singleton x).
 Proof.
  intros; simpl.
  assert (X.eqb y x) by auto; trivialb.
 Qed.

 Lemma singleton_complete : forall x y,
  mem y (singleton x) -> X.eq x y.
 Proof.
  simpl; intros.
  symmetry.
  apply ET.eq_eqb_r; destruct (X.eqb y x); trivial.
 Qed.


 (** Specification of [remove] *)
 Lemma remove_correct : forall x y s,
  X.eq x y -> ~mem x (remove y s).
 Proof.
  induction s; intros.
  trivialb.
  simpl; case (ET.eq_dec y a); intro.
  assert (X.eqb y a) by auto.
  autob.
  assert (~X.eq x a) by eauto.
  rewrite ET.eq_eqb in n; rewrite ET.eq_eqb in H0.
  rewrite (if_notb n); simpl.
  rewrite (if_notb H0); auto.
 Qed.

 Lemma remove_complete : forall x y s,
  ~X.eq x y -> mem y s -> mem y (remove x s).
 Proof.
  induction s; intros.
  trivial.
  simpl in H0 |- *.   
  case (ET.eq_dec x a); intro.  
  assert (~X.eqb y a) by eauto.
  assert (X.eqb x a) by auto.
  autob.

  assert (~X.eqb x a) by auto.
  simplb; destruct (X.eqb y a); auto.
 Qed.

 Lemma remove_inversion : forall x y s,
  mem y (remove x s) -> mem y s.
 Proof.
  induction s; intros.
  trivial.
  simpl in H |- *.
  case (ET.eq_dec y a); intro.
  assert (X.eqb y a) by auto.
  trivialb.

  assert (~X.eqb y a) by auto.
  simplb.
  case (ET.eq_dec x a); intro.
  assert (X.eqb x a) by auto.
  trivialb.

  assert (~X.eqb x a) by auto.
  simplb; simpl in H; trivialb.
 Qed.
  

 (** Specification of [union] *)
 Lemma union_correct : forall s1 s2 x,
  mem x (union s1 s2) -> (mem x s1 \/ mem x s2).
 Proof.
  induction s1; simpl; intros; auto.
  destruct (IHs1 (add a s2) x H).
  left; rewrite H0; destruct (X.eqb x a); trivial.
  case (ET.eq_dec a x); intro.
  assert (X.eqb x a) by auto; autob.
  right; apply add_inversion with a; trivial.
 Qed.

 Lemma union_complete : forall s1 s2 x, 
  mem x s1 \/ mem x s2 -> mem x (union s1 s2).
 Proof.
  induction s1; simpl; intros s2 x H.
  destruct H; autob.

  apply IHs1; simpl.
  case (ET.eq_dec x a); intro.
  assert (X.eqb x a) by auto. 
  right; auto using add_correct.
 
  destruct H; auto using add_complete.
  assert (~X.eqb x a) by auto; trivialb.
  auto.
 Qed.

 Lemma union_complete_l : forall s1 s2 x, 
  mem x s1 -> mem x (union s1 s2).
 Proof.
  auto using union_complete.
 Qed.

 Lemma union_complete_r : forall s1 s2 x, 
  mem x s2 -> mem x (union s1 s2).
 Proof.
  auto using union_complete.
 Qed.


 (** Specification of [inter] *)
 Lemma inter_correct_l : forall s1 s2 x,
  mem x (inter s1 s2) -> mem x s1.
 Proof.
  induction s1; intros.
  trivial.

  simpl in *.
  case_eq (X.eqb x a); intro; trivial.
  case_eq (mem a s2); intro; simplb.
  simpl in H; eautob.
  eauto.
 Qed.  
  
 Lemma inter_correct_r : forall s1 s2 x,
  mem x (inter s1 s2) -> mem x s2.
 Proof.
  induction s1; simpl; intros.
  trivialb.
  case_eq (mem a s2); intro; simplb; simpl in H.
  case (ET.eq_dec x a); intro.
  apply mem_correct with a; auto.
  assert (~X.eqb x a) by auto; simplb; auto.
  auto.
 Qed.

 Lemma inter_complete : forall s1 s2 x,
  mem x s1 -> mem x s2 -> mem x (inter s1 s2).
 Proof.
  induction s1; simpl; intros.
  trivialb.

  case_eq (X.eqb x a); intro.
  case_eq (mem a s2); intro; trivialb.
  assert (~mem a s2) by autob.
  assert (X.eq x a) by auto.
  elim H; eauto using mem_correct.

  case (mem a s2); autob.
 Qed.


 (** Specification of [diff] *)
 Lemma diff_correct_l : forall s1 s2 x, 
  mem x (diff s1 s2) -> mem x s1.
 Proof.
  induction s2; simpl; intros.
  trivial.
  eauto using remove_inversion.
 Qed.

 Lemma diff_correct_r : forall s1 s2 x, 
  mem x (diff s1 s2) -> ~mem x s2.
 Proof.
  induction s2; simpl; intros.
  trivialb.

  case (ET.eq_dec x a); intro; simplb.
  assert (X.eqb x a) by auto; simplb.
  elim (remove_correct (diff s1 s2) e); auto.
  assert (~X.eqb x a) by auto; simplb.
  eauto using remove_inversion.
 Qed.

 Lemma diff_complete : forall s1 s2 x, 
  mem x s1 -> ~mem x s2 -> mem x (diff s1 s2).
 Proof.
  induction s2; simpl; intros.
  trivial.
  case (ET.eq_dec x a); intro.
  assert (X.eqb x a) by auto; trivialb.
  assert (~X.eqb x a) by auto; simplb.
  apply remove_complete; auto.
 Qed.  


 (** Specification of [fold] *)
 Lemma fold_spec : forall A (f:X.t -> A -> A) i s,
  fold f s i = fold_left (fun x a => f a x) (elements s) i.
 Proof.
  trivial.
 Qed.

 (* Alternatively,
 Parameter fold_spec : forall A (f:E.t -> A -> A) i s,
  fold f s i = fold_right f i (elements s). *)


 (** Specification of [elements] *)
 Lemma elements_correct : forall s x, 
  mem x s -> InA X.eq x (elements s).
 Proof.
  induction s; unfold elements; simpl; intros.
  trivialb.  
  case (ET.eq_dec x a); intro.
  constructor; trivial.
  rewrite ET.eq_eqb in n; simplb.
  constructor 2; auto.
 Qed.

 Lemma elements_complete : forall s x, 
  InA X.eq x (elements s) -> mem x s.
 Proof.
  induction s; unfold elements; simpl; intros.
  inversion H.  
  inversion H.
  rewrite ET.eq_eqb in H1; trivialb.
  destruct (X.eqb x a); auto.
 Qed.

 Lemma filter_correct : forall (f:E.t->bool) x s, 
  (forall x y, E.eq x y -> f x = f y) -> mem x (filter f s) -> mem x s /\ f x.
 Proof.
  intros.
  assert (W:=elements_correct _ _ H0).
  rewrite (InA_spec _ ET.eq_dec) in W; destruct W as (y,(W1,W2)).
  unfold filter, elements in W2; rewrite filter_In in W2.
  destruct W2; rewrite (H _ _ W1); split; trivial.
  apply elements_complete.
  rewrite (InA_spec _ ET.eq_dec).
  exists y; auto.
 Qed.

 Lemma filter_complete : forall (f:E.t -> bool) x s, 
  (forall x y, E.eq x y -> f x = f y) ->
  mem x s -> f x -> mem x (filter f s).
 Proof.
  intros.
  assert (W:=elements_correct _ _ H0).
  rewrite (InA_spec _ ET.eq_dec) in W; destruct W as (y, (W1,W2)).
  assert (In y s /\ f y).
  rewrite <- (H _ _ W1); auto.
  unfold filter, is_true in H2; rewrite <- filter_In in H2.
  apply elements_complete.
  rewrite (InA_spec _ ET.eq_dec); exists y; auto.
 Qed.

 Lemma forallb_correct : forall f, (forall x y, X.eq x y -> f x = f y) ->
  forall s, forallb f s -> forall x, mem x s -> f x.
 Proof.
  induction s; simpl; intros; autob.
  assert (W:= X.eqb_spec x a); destruct (X.eqb x a).
  rewrite (H x a W).
  destruct (f a); trivialb.
  destruct (f a); trivialb; auto.
 Qed. 

 Lemma forallb_complete : forall (f:E.t -> bool), 
  (forall x y, X.eq x y -> f x = f y) ->
  forall s, (forall x, mem x s -> f x) -> forallb f s.
 Proof.
  induction s; simpl; intros; auto.
  assert (W:= H0 a).
  assert (Heq:= X.eqb_spec a a); destruct (X.eqb a a).
  rewrite W; auto. 
  apply IHs; intros; apply H0.
  destruct (X.eqb x a); auto.
  elim Heq; apply X.eq_refl.
 Qed.

End MkListSet.
