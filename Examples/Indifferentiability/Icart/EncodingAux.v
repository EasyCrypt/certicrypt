(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

Require Import List.
Require Import Arith.
Require Import Permutation.
Require Import Omega.

Set Implicit Arguments.

Section ListAux.

 Variable A : Type.

 Variable eqb : forall (a b : A), {a = b} + {a <> b}.

 Fixpoint is_in x l : bool :=
  match l with
   | nil => false
   | a :: l' => if eqb x a then true else is_in x l'
  end.

 Lemma is_in_correct : forall x l,
  is_in x l = true -> In x l.
 Proof.
  induction l; simpl; intros.
  discriminate.
  destruct (eqb x a); auto.
 Qed.

 Lemma is_in_correct_conv : forall x l,
  is_in x l = false -> ~ In x l.
 Proof.
  induction l; simpl; intros; auto.
  destruct (eqb x a).
  discriminate.
  intros [H1 | H2].
  elim n; auto.
  apply IHl; trivial.
 Qed.

 Fixpoint nodup l :=
  match l with
   | nil => nil
   | a :: l' => if is_in a l' then nodup l' else a :: nodup l'
  end.

 Lemma nodup_in : forall l x, In x l -> In x (nodup l).
 Proof.
  induction l; simpl; intros; trivial.
  case_eq (is_in a l); intros; auto.
  apply is_in_correct in H0.
  destruct H; subst; auto.
  apply is_in_correct_conv in H0.
  destruct H; subst; simpl; auto.
 Qed.

 Lemma nodup_in_rev : forall l x, In x (nodup l) -> In x l.
 Proof.
  induction l; simpl; intros; trivial.
  case_eq (is_in a l); intros; rewrite H0 in H.
  apply is_in_correct in H0; auto.
  apply is_in_correct_conv in H0.
  destruct H; subst; auto.
 Qed.

 Lemma Nodup_nodup : forall l,
   NoDup (nodup l).
 Proof.
  induction l; simpl; auto.
  constructor.
  case_eq (is_in a l); intros; auto.
  apply is_in_correct_conv in H.
  constructor; trivial.
  intro H'; elim H.
  apply nodup_in_rev; trivial.
 Qed.

 Lemma nodup_fix : forall l,
  NoDup l -> nodup l = l.
 Proof.
  induction l; simpl; auto; intros.
  case_eq (is_in a l); intros.
  apply is_in_correct in H0.
  inversion H; subst.
  elim H3; trivial.
  rewrite IHl; auto.
  inversion H; trivial.
 Qed.

 Lemma permutation_cons_inv : forall a (l:list A),
  In a l -> exists l1, permutation (a :: l1) l.
 Proof.
  induction l; intros.
  elim H.
  simpl in H; destruct H.
  subst; exists l; apply permutation_refl.
  destruct (IHl H) as [l2 H0].
  exists (a0 :: l2).
  apply permutation_trans with (a0 :: a :: l2).
  apply permutation_swap.
  constructor; trivial.
 Qed.

 Lemma incl_permutation: forall (l1 l2 : list A),
  NoDup l1 -> incl l1 l2 -> exists l3, permutation l2 (l1 ++ l3).
 Proof.
  induction l1.
  intro l2; exists l2; apply permutation_refl.
  intros l2 H H0.
  destruct (permutation_cons_inv a l2) as [l3 H1].
  intuition.
  destruct (IHl1 l3) as [l4 H2].
  inversion H; trivial.
  intros b Hb.
  assert (In b (a :: l3)).
  apply permutation_sym in H1.
  apply (permutation_in _ b) in H1; intuition.
  simpl in H2; destruct H2; [ | trivial].
  subst; inversion_clear H; intuition.
  exists l4; simpl.
  apply permutation_trans with (a :: l3).
  apply permutation_sym; trivial.
  constructor; trivial.
 Qed.

 Lemma length_surj : forall (l1 l2 : list A),
  NoDup l1 -> incl l1 l2 ->
  length l1 <= length l2.
 Proof.
  intros.
  destruct (incl_permutation H H0).
  rewrite (permutation_length _ _  _ H1).
  rewrite app_length.
  omega.
 Qed.

 Lemma In_nodup : forall x l, In x l -> In x (nodup l).
 Proof.
  induction l; simpl.
  intros.
  apply H.
  intros.
  destruct H; subst.
  case_eq (is_in x l); intros.
  apply is_in_correct in H; auto.
  simpl; auto.
  case_eq (is_in a l); intros.
  apply is_in_correct in H0; auto.
  apply is_in_correct_conv in H0.
  simpl; auto.
 Qed.

 Lemma incl_nodup : forall l1 l2, incl l1 l2 -> incl (nodup l1) l2.
 Proof.
  induction l1; simpl; intros; auto.
  case_eq (is_in a l1); intros.
  apply IHl1.
  apply is_in_correct in H0.
  red; intros.
  apply H.
  simpl; auto.
  apply is_in_correct_conv in H0.
  red; intros.
  simpl in H1; destruct H1.
  apply H.
  simpl; auto.
  apply IHl1; trivial.
  red; intros; apply H.
  simpl; auto.
 Qed.

End ListAux.


Section ListAux_f.
 
 Variable A B : Type.
 
 Variable Aeqb : forall (a b : A), {a = b} + {a <> b}.
 Variable Beqb : forall (a b : B), {a = b} + {a <> b}.
 
 Variable f : A -> B.
 Variable finv : B -> list A.
 
 Hypothesis finv_nodup : forall b, NoDup (finv b).
 
 Hypothesis f_spec : forall a b, In a (finv b) <-> f a = b.
 
 Variable size : nat.
 Hypothesis size_finv : forall x, length (finv x) <= size.

 Lemma length_surj_mult : forall (la : list A),
  NoDup la -> 
  length la <= length (nodup Beqb (map f la)) * size.
 Proof.
  intros.
  apply le_trans with (length (flat_map finv (nodup Beqb (map f la)))).
  apply length_surj; auto.
    
  red; intros.
  eapply in_flat_map.
  apply f_spec; trivial.    
  apply In_nodup.
  apply in_map; trivial.
  
  apply le_trans with 
   (fold_right (fun x sum => sum + length (finv x)) 0 (nodup Beqb (map f la))).
  
  induction la; simpl; auto.
  case_eq (is_in Beqb (f a) (map f la)); intros; simpl.
  apply IHla.
  inversion H; auto.
  rewrite plus_comm.
  rewrite app_length.
  apply plus_le_compat; auto.
  apply IHla.
  inversion H; auto.
  
  induction la; simpl; auto.
  case_eq (is_in Beqb (f a) (map f la)); intros; simpl.
  apply IHla.
  inversion H; auto.
  rewrite plus_comm.
  apply plus_le_compat; auto.
  apply IHla.
  inversion H; auto.
 Qed.
 
 Lemma map_incl : forall A B (f : A -> B) l1 l2,
  incl l1 l2 -> incl (map f l1) (map f l2).
 Proof.
  red; intros.
  rewrite in_map_iff.
  rewrite in_map_iff in H0.
  destruct H0.
  exists x.
  split; [ | apply H]; tauto.
 Qed.

 Lemma NoDup_intro : forall l : _ A,
  (forall l1 x l2 l3, l = l1 ++ x :: l2 ++ x :: l3 -> False) ->
  NoDup l.
 Proof.
  induction l ; simpl.
  intros ; constructor.
  intros.
  constructor.
  intro Habs.
  destruct (In_split _ _ Habs).
  destruct H0.
  subst.
  exact (H (@nil _) _ _ _ (refl_equal _)).
  apply IHl.
  intros.
  subst.
  exact (H (_ :: _) _ _ _ (refl_equal _)).
 Qed.

 Lemma NoDup_app_recip : forall l,
  (forall l1 l2, l = l1 ++ l2 -> forall x : A, In x l1 -> In x l2 -> False) ->
  NoDup l.
 Proof.
  intros.
  apply NoDup_intro.
  intros ? ? ? ?.
  change (x :: l2 ++ x :: l3) with ((x :: l2) ++ x :: l3).
  rewrite <- app_ass.
  intros.
  subst.
  eapply H.
  reflexivity.
  apply in_or_app.
  right.
  simpl.
  left.
  reflexivity.
  auto.
  simpl; auto.
 Qed.
 
 Lemma NoDup_app_intro : forall (A : Type) (l1 : _ A),
  NoDup l1 ->
  forall l2, NoDup l2 ->
   (forall x, In x l1 -> In x l2 -> False) ->
   NoDup (l1 ++ l2).
 Proof.
  induction 1; subst; simpl.
  tauto.
  intros.
  constructor.
  intro.
  destruct (in_app_or _ _ _ H3).
  contradiction.
  eauto.
  eauto.
 Qed.

 Lemma fold_right_incl_eq : forall (la : list A) (lb : list B),
  NoDup la -> NoDup lb -> 
  (forall a, In a la) ->
  (forall b, In b lb) ->
  length la = fold_right (fun b r => length (finv b) + r) 0 lb.
 Proof.
  intros la lb Hincl_b Hincl_a Hla_full Hlb_full.
  transitivity (length (flat_map finv lb)).
  2:clear; induction lb; simpl; auto.
  2:rewrite app_length; omega.

  apply le_antisym.
  apply length_surj; auto.
  red; intros.
  eapply in_flat_map.
  apply f_spec; trivial.
  auto.

  apply length_surj; auto.
  clear Hlb_full.
  induction lb; simpl.
  constructor.
  apply NoDup_app_intro; auto.
  apply IHlb.
  inversion Hincl_a; auto.
  intros.
  apply f_spec in H.
  subst.
  apply List.in_flat_map in H0.
  destruct H0 as [x2 [H1 H2] ].
  apply f_spec in H2.
  subst.
  inversion Hincl_a.
  subst.
  apply H2; trivial.
  red.
  auto.
 Qed.

End ListAux_f.
