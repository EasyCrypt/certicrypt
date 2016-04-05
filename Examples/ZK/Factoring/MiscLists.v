(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** This file contains some definitions, lemmas and tactics that
    are missing from the Lists section of the Coq standard library.

    N.B. Lemmas [four_to_one_inv], [Splitable4_nodup] and [NoDup_Splitable4_map]
    are currently admitted.
    However, their proofs shoup be similar to the ones of
    [two_to_one_inv], [Splitable_nodup] and [NoDup_Splitable_map].
 *)

Require Import Classical Setoid Omega Lists.List.
Require Import MiscLogic.
Require Import Permutation.

Lemma in_app: forall A (l m : list A) a, In a (l ++ m) <-> In a l \/ In a m.
Proof.
auto with *.
Qed.

Lemma all_in_neq : forall A (l:list A) a, (forall b, In b l -> a <> b) -> ~In a l.
Proof.
induction l as [ | a l IHl].
tauto.
simpl.
intros b H1.
apply and_not_or.
split.
generalize (H1 b).
tauto.
apply IHl.
intros c Hc.
apply H1.
tauto.
Qed.

Lemma fold_left_eqf :
  forall A B C (f g:A->B)(h:C->B->C) l (b:C),
  (forall a, In a l -> f a = g a) ->
  fold_left (fun res a => h res (f a)) l b =
  fold_left (fun res a => h res (g a)) l b.
Proof.
intros A B C f g h l.
induction l as [ | a l IHl].
reflexivity.
simpl.
intros b H.
rewrite IHl.
cutrewrite (f a = g a).
reflexivity.
auto.
auto.
Qed.

Lemma fold_left_op : 
  forall A B op (f:A->B) l b1 b2,
  (forall x y z, op (op x y) z = op x (op y z)) ->
  op b1 (fold_left (fun res a => op res (f a)) l b2) =
  fold_left (fun res a => op res (f a)) l (op b1 b2).
Proof.
intros A B op f l b1 b2 assoc.
revert b1 b2.
induction l as [ | a l IHl].
reflexivity.
simpl.
intros b1 b2.
rewrite assoc.
apply IHl.
Qed.

Lemma Permutation_fold_left :
  forall A B op (f:A->B) l l' (b:B),
  (forall x y z, op (op x y) z = op x (op y z)) ->
  (forall x y, op x y = op y x) ->
  Permutation l l' ->
  fold_left (fun res a => op res (f a)) l b =
  fold_left (fun res a => op res (f a)) l' b.
Proof.
intros A B op f l l' b assoc comm H.
revert b.
induction H; intro b; simpl.
reflexivity.
trivial.
congruence.
congruence.
Qed.

Lemma fold_left_app_same :
  forall A B op (f:A->B) l (b:B),
  (forall x y z, op (op x y) z = op x (op y z)) ->
  (forall x y, op x y = op y x) ->
  fold_left (fun res a => op res (f a)) (l++l) b =
  fold_left (fun res a => op (op res (f a)) (f a)) l b.
Proof.
intros A B op f l b assoc comm.
revert b.
induction l as [ | a l IHl]; intros b; simpl.
reflexivity.
rewrite Permutation_fold_left with (l':=a :: l++l).
apply IHl.
exact assoc.
exact comm.
apply Permutation_sym.
apply Permutation_cons_app.
apply Permutation_refl.
Qed.

Lemma fold_left_all :
  forall A B op (f:A->B) l (b:B),
  (forall x y z, op (op x y) z = op x (op y z)) ->
  (forall x y, op x y = op y x) ->
  (forall x, op b x = x) ->
  (forall x y, op x y = b -> x = b) ->
  (fold_left (fun res a => op res (f a)) l b = b <-> forall a, In a l -> f a = b).
Proof.
intros A B op f l b assoc comm neutral_left no_inv.
induction l as [ | a l IHl]; simpl.
tauto.
rewrite comm.
rewrite <- fold_left_op.
split.

intros H1 x [H2 | H2].
subst x.
apply no_inv in H1.
assumption.
rewrite comm in H1.
apply no_inv in H1.
rewrite IHl in H1.
apply H1.
assumption.

intro H.
assert (forall a, In a l -> f a = b) as H0.
auto.
rewrite <- IHl in H0.
rewrite H0.
rewrite H.
apply neutral_left.
tauto.
assumption.
Qed.

Lemma fold_left_double :
  forall A B op (f:A->B) l (b:B),
  (forall x y z, op (op x y) z = op x (op y z)) ->
  (forall x y, op x y = op y x) ->
  fold_left (fun res a => op (op res (f a)) (f a)) l b =
  (fold_left (fun res a => op res (f a)) l
    (fold_left (fun res a => op res (f a)) l b)).
Proof.
intros A B op f l b assoc comm.
revert b.
induction l as [ | a l IHl].
reflexivity.
intro b.
simpl.
rewrite IHl.
symmetry.
rewrite comm.
rewrite fold_left_op.
congruence.
assumption.
Qed.

Lemma fold_left_strength :
  forall A1 A2 B op (f:A1->A2->B) l a1 (b:B),
  fold_left
    (fun res a => op res (f (fst a) (snd a))) (List.map (fun a2 => (a1, a2)) l) b =
  fold_left
    (fun res a2 => op res (f a1 a2)) l b.
Proof.
intros A1 A2 B op f l.
induction l as [ | a2 l IHl].
reflexivity.
intros a1 b.
simpl.
apply IHl.
Qed.
   
Lemma In_seq :
  forall n start len, In n (seq start len) <-> start <= n < start+len.
Proof.
intros n start len.
revert n start.
induction len as [ | m IHlen]; simpl.
auto with *.
intros n start.
split.
intros [H | H].
omega.
rewrite IHlen in H.
omega.
intro H.
generalize (eq_nat_dec start n).
intros [H0 | H0].
tauto.
cut (S start <= n < S start + m).
clear H H0.
intro H.
rewrite <- IHlen in H.
tauto.
omega.
Qed.

Lemma length_map_cons :
  forall A (a:A)(l:list A)(ll:list (list A))(len:nat),
  (forall l, In l ll -> length l = len) -> In l (List.map (cons a) ll) ->
  length l = S len.
Proof.
destruct l as [ | a' l'].
intros.
contradict H0.
clear H.
induction ll as [ | l l1 IHl1].
tauto.
simpl.
intro H0.
destruct H0 as [H0 | H0].
discriminate H0.
intuition.
simpl.
intros.
rewrite H.
reflexivity.
induction ll as [ | l ll' IHll'].
tauto.
simpl in *.
destruct H0 as [H0 | H0].
left.
injection H0.
trivial.
right.
auto.
Qed.

Lemma NoDup_map :
  forall A B (f:A->B)(l:list A),
  (forall x y, In x l -> In y l -> f x = f y -> x=y) -> NoDup l -> NoDup (map f l).
Proof.
intros A B f l Hf Hl.
induction l as [ | a l IH].
constructor.
simpl in *.
inversion_clear Hl.
constructor.
contradict H.
rewrite in_map_iff in H.
destruct H as [b [H1 H2] ].
cutrewrite (a=b).
assumption.
apply Hf.
tauto.
tauto.
congruence.
apply IH.
auto.
assumption.
Qed.

Lemma map_NoDup : forall A B (f:A->B)(l:list A), NoDup (map f l) -> NoDup l.
Proof.
intros A B f l H.
induction l as [ | a l IHl].
constructor.
simpl in H.
constructor.
cut (~In (f a) (map f l)).
intro Hin.
contradict Hin.
apply in_map.
assumption.
inversion H.
assumption.
apply IHl.
inversion H.
assumption.
Qed.

Lemma NoDup_seq : forall start len, NoDup (seq start len).
Proof.
intros start len.
revert start.
induction len as [ | n IHn]; simpl; intro start.
constructor.
constructor.
rewrite In_seq.
omega.
apply IHn.
Qed.

Lemma NoDup_app :
  forall A (l1 l2:list A),
  NoDup l1 -> NoDup l2 ->
  (forall x, In x l1 -> ~In x l2) -> (forall x, In x l2 -> ~In x l1) ->
  NoDup (l1++l2).
Proof.
induction l1 as [ | a1 l1 IHl1].
trivial.
simpl.
intros l2 H1 H2 H3 H4.
constructor.
intro H.
apply in_app_or in H.
destruct H as [H | H].
inversion H1.
contradiction.
destruct (H4 _ H).
tauto.
apply IHl1.
inversion H1.
assumption.
assumption.
auto.
intros x H.
generalize (H4 _ H).
tauto.
Qed.

Lemma app_NoDup :
  forall A (l1 l2:list A),
  NoDup (l1++l2) ->
  NoDup l1 /\ NoDup l2 /\
  (forall x, In x l1 -> ~In x l2) /\ (forall x, In x l2 -> ~In x l1).
Proof.
intros A l1.
induction l1 as [ | a1 l1 IHl1]; simpl; intros l2 H.
split.
constructor.
tauto.
assert (~In a1 (l1++l2) /\ NoDup (l1++l2)) as [H1 H2].
inversion H.
tauto.
destruct (IHl1 _ H2) as (H3 & H4 & H5 & H6).
split.
constructor.
auto with *.
assumption.
split.
assumption.
split.
intros x [H7 | H7].
subst x.
auto with *.
auto.
intros x H7.
contradict H1.
destruct H1 as [H1 | H1].
subst x.
auto with *.
apply H5 in H1.
contradiction.
Qed.

Lemma NoDup_list_prod :
  forall A B (l1:list A)(l2:list B),
  NoDup l1 -> NoDup l2 -> NoDup (list_prod l1 l2).
Proof.
induction l1 as [ | a l1 IHl1]; simpl.
constructor.
intros l2 H1 H2.
cut (~In a l1 /\ NoDup l1).
clear H1.
intros [H3 H1].
apply NoDup_app.
apply NoDup_map.
congruence.
assumption.
apply IHl1.
assumption.
assumption.
intros [x y] H.
rewrite in_map_iff in H.
destruct H as [b [H4 H5] ].
injection H4.
clear H4.
intros H6 H7.
subst x.
subst y.
rewrite in_prod_iff.
tauto.
intros [x y] H.
rewrite in_map_iff.
contradict H.
destruct H as [b [H4 H5] ].
injection H4.
clear H4.
intros H6 H7.
subst x.
subst y.
rewrite in_prod_iff.
tauto.
inversion H1.
tauto.
Qed.

Lemma In_split2 :
  forall A (l:list A) x1 x2, x1<>x2 -> In x1 l -> In x2 l ->
  exists l0, exists l1, exists l2,
  l = l0 ++ (x1 :: l1) ++ (x2 :: l2) \/
  l = l0 ++ (x2 :: l1) ++ (x1 :: l2).
Proof.
intros A l x1 x2 H0 H1 H2.
destruct (In_split x1 l H1) as (l1 & l2 & H3).
assert (In x2 l1 \/ In x2 l2) as H4.
subst l.
apply in_app_or in H2.
destruct H2 as [H2 | H2].
tauto.
right.
simpl in H2.
tauto.
destruct H4 as [H4 | H4].

destruct (In_split x2 l1 H4) as (l11 & l12 & H5).
exists l11.
exists l12.
exists l2.
right.
subst l l1.
auto with *.

destruct (In_split x2 l2 H4) as (l21 & l22 & H5).
exists l1.
exists l21.
exists l22.
left.
subst l l2.
reflexivity.
Qed.

Definition two_to_one {A B}(f:A->B)(l:list A) : Prop :=
  forall y, In y (List.map f l) -> exists x1, exists x2, In x1 l /\ In x2 l /\
  x1<>x2 /\ y = f x1 /\ y = f x2 /\
  (forall x, In x l -> y = f x -> (x=x1 \/ x=x2)).

Definition four_to_one {A B}(f:A->B)(l:list A) : Prop :=
  forall y, In y (List.map f l) ->
  exists x1, exists x2, exists x3, exists x4, In x1 l /\ In x2 l /\
    x1<>x2 /\ x1<>x3 /\ x1<>x4 /\ x2<>x3 /\ x2<>x4 /\ x3<>x4 /\
    y = f x1 /\ y = f x2 /\ y = f x3 /\ y = f x4 /\
    (forall x, In x l -> y = f x -> (x=x1 \/ x=x2 \/ x=x3 \/ x=x4)).

Lemma two_to_one_inv :
  forall A B (f:A->B)(x1 x2:A)(l1 l2:list A),
  NoDup (x1::l1++x2::l2) ->
  x1<>x2 -> f x1 = f x2 -> two_to_one f (x1 :: l1 ++ x2 :: l2) ->
  two_to_one f (l1++l2).
Proof.
intros A B f x1 x2 l1 l2 Hnod Hneq Heq H2to1 y Hy.
assert (~In x1 l1 /\ ~In x1 l2 /\ ~In x2 l1 /\ ~In x2 l2 /\ NoDup l1 /\ NoDup l2)
  as (Hnod1 & Hnod2 & Hnod3 & Hnod4 & Hnod5 & Hnod6).
assert (~In x1 (l1++x2::l2) /\ NoDup (l1++x2::l2)) as [Hnod1 Hnod2].
inversion Hnod.
tauto.
clear Hnod.
split.
auto with *.
split.
contradict Hnod1.
auto with *.
split.
apply NoDup_remove_2 in Hnod2.
auto with *.
split.
apply NoDup_remove_2 in Hnod2.
auto with *.
apply NoDup_remove_1 in Hnod2.
apply app_NoDup in Hnod2.
tauto.

rewrite map_app in Hy.
apply in_app_or in Hy.
destruct (H2to1 y) as (x1' & x2' & [H1 | H1] & [H2 | H2] & H3 & H4 & H5 & H6);
clear H2to1.
simpl.
right.
rewrite map_app.
apply in_or_app.
simpl.
tauto.


congruence.


fold (In x2' (l1++x2::l2)) in H2.
subst x1'.
assert (x2=x1 \/ x2=x2') as [H7 | H7].
apply H6.
auto with *.
congruence.
congruence.
subst x2'.
destruct Hy as [Hy | Hy].

rewrite in_map_iff in Hy.
destruct Hy as (x & Hx1 & Hx2).
assert (x=x1 \/ x=x2) as [H7 | H7].
apply H6.
auto with *.
congruence.
subst x.
contradiction.
congruence.

rewrite in_map_iff in Hy.
destruct Hy as (x & Hx1 & Hx2).
assert (x=x1 \/ x=x2) as [H7 | H7].
apply H6.
auto with *.
congruence.
subst x.
contradiction.
congruence.



fold (In x1' (l1++x2::l2)) in H1.
subst x2'.
assert (x2=x1' \/ x2=x1) as [H7 | H7].
apply H6.
auto with *.
congruence.
subst x1'.
destruct Hy as [Hy | Hy].

rewrite in_map_iff in Hy.
destruct Hy as (x & Hx1 & Hx2).
assert (x=x2 \/ x=x1) as [H7 | H7].
apply H6.
auto with *.
congruence.
congruence.
subst x.
contradiction.

rewrite in_map_iff in Hy.
destruct Hy as (x & Hx1 & Hx2).
assert (x=x2 \/ x=x1) as [H7 | H7].
apply H6.
auto with *.
congruence.
congruence.
congruence.
congruence.

fold (In x1' (l1 ++ x2 :: l2)) in H1.
fold (In x2' (l1 ++ x2 :: l2)) in H2.
apply in_app_or in H1.
apply in_app_or in H2.
simpl in H1, H2.
destruct H1 as [H1 | [H1 | H1] ].
exists x1'.
destruct H2 as [H2 | [H2 | H2] ].
exists x2'.
split.
auto with *.
split.
auto with *.
split.
assumption.
split.
assumption.
split.
assumption.
intros x H7 H8.
apply H6.
apply in_app_or in H7.
simpl.
right.
apply in_or_app.
simpl.
tauto.
assumption.
subst x2'.
assert (x1=x1' \/ x1=x2) as [H7 | H7].
apply H6.
auto with *.
congruence.
congruence.
contradiction.
exists x2'.
split.
auto with *.
split.
auto with *.
split.
assumption.
split.
assumption.
split.
assumption.
intros x H7 H8.
apply H6.
apply in_app_or in H7.
simpl.
right.
apply in_or_app.
simpl.
tauto.
assumption.
subst x1'.
assert (x1=x2 \/ x1=x2') as [H7 | H7].
apply H6.
auto with *.
congruence.
contradiction.
subst x2'.
tauto.
destruct H2 as [H2 | [H2 | H2] ].
exists x1'.
exists x2'.
split.
auto with *.
split.
auto with *.
split.
assumption.
split.
assumption.
split.
assumption.
intros x H7 H8.
apply H6.
apply in_app_or in H7.
simpl.
right.
apply in_or_app.
simpl.
tauto.
assumption.
subst x2'.
assert (x1=x1' \/ x1=x2) as [H7 | H7].
apply H6.
auto with *.
congruence.
congruence.
contradiction.
exists x1'.
exists x2'.
split.
auto with *.
split.
auto with *.
split.
assumption.
split.
assumption.
split.
assumption.
intros x H7 H8.
apply H6.
apply in_app_or in H7.
simpl.
right.
apply in_or_app.
simpl.
tauto.
assumption.
Qed.

Lemma four_to_one_inv :
  forall A B (f:A->B)(x1 x2 x3 x4:A)(l1 l2 l3 l4:list A),
  NoDup (x1::l1++x2::l2++x3::l3++x4::l4) ->
  x1<>x2 -> x1<>x3 -> x1<>x4 -> x2<>x3 -> x2<>x4 -> x3<>x4 ->
  f x1 = f x2 -> f x2 = f x3 -> f x3 = f x4 ->
  four_to_one f (x1::l1++x2::l2++x3::l3++x4::l4) ->
  four_to_one f (l1++l2).
Proof.
Admitted.

Definition inl {A} (eq_A_dec : forall a1 a2:A, {a1=a2}+{a1<>a2})(a:A)(l:list A) :
  bool :=
  if In_dec eq_A_dec a l then true else false. 

Definition Finite (A:Type) : Prop :=
  exists l, forall a:A, In a l.

Section NoDup.

Variable A:Type.

Variable eq_A_dec : forall a1 a2:A, {a1=a2}+{a1<>a2}.

Fixpoint nodup
  (l:list A) {struct l} :
  list A :=
  match l with
  | nil => nil
  | a :: l =>
      let l' := nodup l in
      if In_dec eq_A_dec a l' then l' else a :: l'
  end.

Lemma NoDup_nodup : forall l, NoDup (nodup l).
Proof.
induction l as [ | a l IHl]; simpl.
constructor.
destruct (In_dec eq_A_dec a (nodup l)) as [H | H].
assumption.
constructor; assumption.
Qed.

Lemma incl_nodup : forall l, (incl l (nodup l)).
Proof.
unfold incl.
induction l as [ | a l IHl]; simpl.
contradiction.
intros a' [H | H]; destruct (In_dec eq_A_dec a (nodup l)); simpl.
congruence.
tauto.
auto.
auto.
Qed.

Lemma In_nodup : forall a l, In a (nodup l) <-> In a l.
Proof.
intros a l.
induction l as [ | a' l IHl]; simpl.

reflexivity.

destruct (In_dec eq_A_dec a' (nodup l)) as [H | H].
rewrite IHl.
split.
tauto.
intros [H1 | H1].
subst a'.
tauto.
assumption.
simpl.
tauto.
Qed.

Lemma Permutation_nodup :
  forall l l', Permutation l l' -> Permutation (nodup l) (nodup l').
Proof.
intros l l' Hperm.
induction Hperm; simpl.

apply Permutation_refl.

destruct (In_dec eq_A_dec x (nodup l)) as [H1 | H1];
destruct (In_dec eq_A_dec x (nodup l')) as [H2 | H2].
assumption.
contradict H2.
apply Permutation_in with (nodup l).
assumption.
assumption.
contradict H1.
apply Permutation_in with (nodup l').
apply Permutation_sym.
assumption.
assumption.
apply perm_skip.
assumption.

(repeat
  match goal with
  | |- context [In_dec ?eq_dec ?x ?l] => destruct (In_dec eq_dec x l)
  end
); simpl in *; try contradiction; try apply Permutation_refl;
(repeat
  match goal with
  | H:_ \/ _ |- _ => destruct H as [H | H]
  end
); try subst x; try contradiction; try apply Permutation_refl; try tauto.
apply perm_swap.

eapply Permutation_trans.
eassumption.
assumption.
Qed.

Inductive Splitable : list A -> Prop :=
| splitable_nil : Splitable nil
| splitable_cons :
    forall a l l1 l2,
    Permutation l (l1++a::l2) -> ~In a l1 -> ~In a l2 -> Splitable (l1++l2) ->
    Splitable (a::l).

Inductive Splitable4 : list A -> Prop :=
| splitable4_nil : Splitable4 nil
| splitable4_cons :
    forall a l l1 l2 l3 l4,
    Permutation l (l1++a::l2++a::l3++a::l4) ->
    ~In a l1 -> ~In a l2 -> ~In a l3 -> ~In a l4 -> Splitable4 (l1++l2++l3++l4) ->
    Splitable4 (a::l).

Lemma Splitable_nodup :
  forall l,
  Splitable l -> Permutation (nodup l ++ nodup l) l.
Proof.
intros l Hl.
induction Hl as  [ | a l l1 l2 H1 H2 H3 H4 IH].

apply Permutation_refl.

simpl.
destruct (In_dec eq_A_dec a (nodup l)) as [H6 | H6].

apply perm_skip with (x:=a) in H1.
apply Permutation_sym.
eapply Permutation_trans.
eexact H1.
apply Permutation_trans with ((a::a::nil)++(l1++l2)).
apply perm_skip.
apply Permutation_sym.
apply Permutation_cons_app.
apply Permutation_refl.
eapply Permutation_trans.
apply Permutation_app.
apply Permutation_refl.
apply Permutation_sym.
eexact IH.
apply Permutation_trans with ((a :: nodup (l1++l2)) ++ (a :: nodup (l1++l2))).
apply perm_skip.
apply Permutation_cons_app.
apply Permutation_refl.
assert (Permutation (a :: nodup (l1 ++ l2)) (nodup l)).
apply perm_trans with (nodup (l1++a::l2)).
apply perm_trans with (nodup (a::l1++l2)).
simpl.
destruct (In_dec eq_A_dec a (nodup (l1 ++ l2))) as [H7 | H7].
rewrite In_nodup in H7.
apply in_app_or in H7.
tauto.
apply Permutation_refl.
apply Permutation_nodup.
apply Permutation_cons_app.
apply Permutation_refl.
apply Permutation_nodup.
apply Permutation_sym.
apply Permutation_cons_inv with a.
assumption.
apply Permutation_app.
assumption.
assumption.

contradict H6.
apply Permutation_in with (nodup (l1++a::l2)).
apply Permutation_nodup.
apply Permutation_sym.
assumption.
apply incl_nodup.
auto with *.
Qed.

Lemma Splitable4_nodup :
  forall l,
  Splitable4 l -> Permutation (nodup l ++ nodup l ++ nodup l ++ nodup l) l.
Proof.
intros l Hl.
induction Hl as  [ | a l l1 l2 l3 l4 H1 H2 H3 H4 H5 H6 IH].

apply Permutation_refl.

simpl.
destruct (In_dec eq_A_dec a (nodup l)) as [H9 | H9].

apply perm_skip with (x:=a) in H1.
apply Permutation_sym.
eapply Permutation_trans.
eexact H1.
apply Permutation_trans with ((a::a::a::a::nil)++(l1++l2++l3++l4)).
apply perm_skip.
apply Permutation_sym.
apply Permutation_cons_app.

eapply Permutation_trans.
apply Permutation_cons_app.
apply Permutation_cons_app.
instantiate (2:=l1++l2).
instantiate (1:=l3++l4).
rewrite app_ass.
apply Permutation_refl.
eapply Permutation_trans.
apply Permutation_app.
apply Permutation_refl.
apply Permutation_cons_app.
change (a::l3++l4) with ((a::l3)++l4).
apply Permutation_refl.
rewrite app_ass.
apply Permutation_refl.

eapply Permutation_trans.
apply Permutation_app.
apply Permutation_refl.
apply Permutation_sym.
eexact IH.
apply Permutation_nodup in H1.
simpl in H1.
destruct (In_dec eq_A_dec a (nodup l)) as [_ | ?]; [idtac | contradiction].
destruct (In_dec eq_A_dec a (nodup (l1 ++ a :: l2 ++ a :: l3 ++ a :: l4)))
  as [_ | H].
apply Permutation_sym.
eapply Permutation_trans.
apply Permutation_app.
apply H1.
apply Permutation_app.
apply H1.
apply Permutation_app.
apply H1.
apply H1.
apply Permutation_sym.
simpl.
apply Permutation_trans with (
  a :: nodup (l1++l2++l3++l4) ++
  a :: nodup (l1++l2++l3++l4) ++
  a :: nodup (l1++l2++l3++l4) ++
  a :: nodup (l1++l2++l3++l4)
).
admit.
assert (
  Permutation (a :: nodup (l1++l2++l3++l4)) (nodup (l1++a::l2++a::l3++a::l4))
).
admit.
change (
  a :: nodup (l1++l2++l3++l4) ++
  a :: nodup (l1++l2++l3++l4) ++
  a :: nodup (l1++l2++l3++l4) ++
  a :: nodup (l1++l2++l3++l4)
) with (
  (a :: nodup (l1++l2++l3++l4)) ++
  (a :: nodup (l1++l2++l3++l4)) ++
  (a :: nodup (l1++l2++l3++l4)) ++
  (a :: nodup (l1++l2++l3++l4))
).
apply Permutation_app.
assumption.
apply Permutation_app.
assumption.
apply Permutation_app.
assumption.
assumption.

contradict H.
rewrite In_nodup.
auto with *.

contradict H9.
apply Permutation_in with (nodup (l1++a::l2++a::l3++a::l4)).
apply Permutation_nodup.
apply Permutation_sym.
assumption.
apply incl_nodup.
auto with *.
Qed.

Lemma NoDup_Splitable_map :
  forall B (f:B->A) l,
  NoDup l ->
  two_to_one f l ->
  Splitable (List.map f l).
Proof.
intros B f l.
pattern l.
apply well_founded_ind with (R := fun l1 l2 => List.length l1 < List.length l2).
apply well_founded_lt_compat with (f:=List.length (A:=B)).
trivial.
clear l.
intros l IHl Hnod H2to1.
destruct l as [ | b l].

apply splitable_nil.

simpl.
assert (~In b l /\ NoDup l) as [Hnod1 Hnod2].
inversion Hnod.
tauto.
clear Hnod.

destruct (H2to1 (f b)) as (x1 & x2 & [H3 | H3] & [H4 | H4] & H5 & H6 & H7 & H8).
simpl.
tauto.


congruence.


fold (In x2 l) in H4.
subst b.
destruct (In_split _ _ H4) as (l1 & l2 & H9).
apply splitable_cons with (l1:=List.map f l1) (l2:=List.map f l2).
rewrite H7, H9.
rewrite map_app.
apply Permutation_refl.

rewrite in_map_iff.
intros [x [Hx1 Hx2] ].
apply H8 in H6.
apply H8 in H7.
symmetry in Hx1.
apply H8 in Hx1.
destruct H6 as [H6 | H6];
destruct H7 as [H7 | H7];
destruct Hx1 as [Hx1 | Hx1];
try contradiction; try congruence.
subst x l; auto with *.
subst x.
apply In_split in Hx2.
destruct Hx2 as (l11 & l12 & Hx2).
subst l1.
subst l.
apply NoDup_remove_2 in Hnod2.
contradict Hnod2.
auto with *.
subst l.
auto with *.
auto with *.
auto with *.

rewrite in_map_iff.
intros [x [Hx1 Hx2] ].
apply H8 in H6.
apply H8 in H7.
symmetry in Hx1.
apply H8 in Hx1.
destruct H6 as [H6 | H6];
destruct H7 as [H7 | H7];
destruct Hx1 as [Hx1 | Hx1];
try contradiction; try congruence.
subst x l; auto with *.
subst x.
apply In_split in Hx2.
destruct Hx2 as (l11 & l12 & Hx2).
subst l2.
subst l.
apply NoDup_remove_2 in Hnod2.
contradict Hnod2.
auto with *.
subst l.
auto with *.
auto with *.
auto with *.

rewrite <- map_app.
apply IHl.
rewrite H9.
rewrite app_length.
simpl.
rewrite app_length.
auto with arith.
apply NoDup_remove_1 with x2.
congruence.

apply two_to_one_inv with x1 x2.
constructor.
congruence.
congruence.
assumption.
assumption.
rewrite <- H9.
assumption.


rename H3 into H4', H4 into H3.
rename H4' into H4.
rename H6 into H7', H7 into H6.
rename H7' into H7.
rename x1 into x2', x2 into x1.
rename x2' into x2. 
assert (forall x : B, In x (b :: l) -> f b = f x -> x = x1 \/ x = x2) as H8'.
intros x H9 H10.
generalize (H8 x H9 H10).
tauto.
clear H8.
rename H8' into H8.
assert (x1<>x2) as H5'.
congruence.
clear H5.
rename H5' into H5.

fold (In x2 l) in H4.
subst b.
destruct (In_split _ _ H4) as (l1 & l2 & H9).
apply splitable_cons with (l1:=List.map f l1) (l2:=List.map f l2).
rewrite H7, H9.
rewrite map_app.
apply Permutation_refl.

rewrite in_map_iff.
intros [x [Hx1 Hx2] ].
apply H8 in H6.
apply H8 in H7.
symmetry in Hx1.
apply H8 in Hx1.
destruct H6 as [H6 | H6];
destruct H7 as [H7 | H7];
destruct Hx1 as [Hx1 | Hx1];
try contradiction; try congruence.
subst x l; auto with *.
subst x.
apply In_split in Hx2.
destruct Hx2 as (l11 & l12 & Hx2).
subst l1.
subst l.
apply NoDup_remove_2 in Hnod2.
contradict Hnod2.
auto with *.
subst l.
auto with *.
auto with *.
auto with *.

rewrite in_map_iff.
intros [x [Hx1 Hx2] ].
apply H8 in H6.
apply H8 in H7.
symmetry in Hx1.
apply H8 in Hx1.
destruct H6 as [H6 | H6];
destruct H7 as [H7 | H7];
destruct Hx1 as [Hx1 | Hx1];
try contradiction; try congruence.
subst x l; auto with *.
subst x.
apply In_split in Hx2.
destruct Hx2 as (l11 & l12 & Hx2).
subst l2.
subst l.
apply NoDup_remove_2 in Hnod2.
contradict Hnod2.
auto with *.
subst l.
auto with *.
auto with *.
auto with *.

rewrite <- map_app.
apply IHl.
rewrite H9.
rewrite app_length.
simpl.
rewrite app_length.
auto with arith.
apply NoDup_remove_1 with x2.
congruence.

apply two_to_one_inv with x1 x2.
constructor.
congruence.
congruence.
assumption.
assumption.
rewrite <- H9.
assumption.


fold (In x1 l) in H3.
fold (In x2 l) in H4.
assert (f b = f b) as H9.
reflexivity.
apply H8 in H6.
apply H8 in H7.
apply H8 in H9.
destruct H6 as [H6 | H6];
destruct H7 as [H7 | H7];
destruct H9 as [H9 | H9];
try contradiction; try congruence.
auto with *.
auto with *.
auto with *.
Qed.

Lemma NoDup_Splitable4_map :
  forall B (f:B->A) l,
  NoDup l ->
  four_to_one f l ->
  Splitable4 (List.map f l).
Proof.
Admitted.

Lemma incl_length_le :
  forall (l1 l2:list A), NoDup l1 -> incl l1 l2 -> length l1 <= length l2.
Proof.
intros l1 l2 Hnod.
revert l2.
induction Hnod as [ | n l1 H1 H2 IH].
auto with arith.
simpl.
intros l2 Hincl.
assert (exists l3, exists l4, l2 = l3++n::l4) as [l3 [l4 Hsplit] ].
apply In_split.
auto with *.
subst l2.
assert (incl l1 (l3++l4)).
intros a H.
unfold incl in Hincl.
simpl in Hincl.
destruct (eq_A_dec a n) as [Heq | Hneq].
congruence.
apply in_or_app.
assert (In a (l3++n::l4)).
auto.
apply in_app_or in H0.
destruct H0 as [H0 | [H0 | H0] ].
tauto.
congruence.
tauto.
replace (length (l3++n::l4)) with (S (length (l3++l4))).
apply le_n_S.
apply IH.
assumption.
do 2 rewrite app_length.
simpl.
trivial.
Qed.

Lemma Finite_to_list : Finite A -> exists l:list A, NoDup l /\ forall a:A, In a l.
Proof.
intros [l Hfin].
exists (nodup l).
split.
apply NoDup_nodup.
intro a.
apply incl_nodup.
trivial.
Qed.

End NoDup.

Lemma NoDup_length_le :
  forall n l, NoDup l -> (forall m, In m l -> m < n) -> length l <= n.
Proof.
intros n l Hnod H.
replace n with (length (seq 0 n)).
apply incl_length_le.
exact eq_nat_dec.
assumption.
intros m Hm.
rewrite In_seq.
auto with arith.
apply seq_length.
Qed.

Lemma Permutation_In :
  forall A x (l1 l2:list A), Permutation l1 l2 -> (In x l1 <-> In x l2).
Proof.
induction l1 as [ | a l1 IH].

intros l2 H.
cutrewrite (l2 = nil).
reflexivity.
apply Permutation_nil.
assumption.

intros l2 H.
induction H.
reflexivity.
simpl.
tauto.
simpl.
tauto.
tauto.
Qed.

Lemma NoDup_swap : forall A l (x y:A), NoDup (y::x::l) <-> NoDup (x::y::l).
Proof.
induction l as [ | z l IH].

split; intro H; inversion H; constructor.
firstorder.
constructor.
tauto.
constructor.
firstorder.
constructor.
tauto.
constructor.

split; intro H; inversion H; constructor; simpl in *.
contradict H2.
destruct H2 as [H2 | [H2 | H2] ].
auto.
subst z.
inversion H3.
contradict H5.
auto with *.
inversion H3.
contradict H6.
auto with *.
constructor.
tauto.
inversion H3.
assumption.
contradict H2.
destruct H2 as [H2 | [H2 | H2] ].
auto.
subst z.
inversion H3.
contradict H5.
auto with *.
inversion H3.
contradict H6.
auto with *.
constructor.
tauto.
inversion H3.
assumption.
Qed.

Lemma Permutation_NoDup :
  forall A (l1 l2:list A), Permutation l1 l2 -> (NoDup l1 <-> NoDup l2).
Proof.
destruct l1 as [ | a l1].

intros l2 H.
cutrewrite (l2 = nil).
reflexivity.
apply Permutation_nil.
assumption.

intros l2 H.
induction H.
reflexivity.
simpl.
split; intro H0; constructor.
rewrite <- (Permutation_In _ x _ _ H).
inversion H0.
assumption.
rewrite <- IHPermutation.
inversion H0.
assumption.
rewrite (Permutation_In _ x _ _ H).
inversion H0.
assumption.
rewrite IHPermutation.
inversion H0.
assumption.
apply NoDup_swap.
tauto.
Qed.

Lemma Permutation_app_In_r :
  forall A (eq_A_dec:forall x y:A, {x=y}+{x<>y}) l1 l2 l (x:A),
  Permutation (l1++l2) l -> In x l -> ~In x l1 -> In x l2.
Proof.
intros A eq_A_dec l1 l2.
revert l1.
induction l2 as [ | x l2 IH]; simpl; intros l1 l y H1 H2 H3.
cutrewrite (l1++nil = l1) in H1.
rewrite (Permutation_In _ y _ _ H1) in H3.
contradiction.
auto with *.
apply perm_trans with (l:=(x::l1)++l2) in H1.
destruct (eq_A_dec x y) as [Heq | Hneq].
tauto.
right.
eapply IH.
eassumption.
assumption.
simpl.
tauto.
simpl.
apply Permutation_cons_app.
apply Permutation_refl.
Qed.

Fixpoint duplicate {A} (a:A)(n:nat) {struct n} : list A :=
  match n with
  | O => nil
  | S n' => a :: duplicate a n'
  end.

Lemma duplicate_length : forall A (a:A)(n:nat), length (duplicate a n) = n.
Proof.
induction n as [ | n IHn].
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Lemma nth_tail : forall A n (l:list A) d, nth n (tail l) d = nth (S n) l d.
Proof.
intros A n l d.
destruct l as [ | a l].
destruct n as [ | n].
reflexivity.
reflexivity.
reflexivity.
Qed.

Fixpoint update_nth {A:Type}(n:nat)(a:A)(l:list A)(d:A) {struct n} : list A :=
  match n with
  | O => a :: tail l
  | S n' => hd d l :: update_nth n' a (tail l) d
  end.

Lemma nth_update_nth_eq : forall A i (x d d':A) l, nth i (update_nth i x l d') d = x.
Proof.
induction i as [ | i' IH].
reflexivity.
intros x d d' l.
simpl.
apply IH.
Qed.

Lemma nth_update_nth_neq :
  forall A i1 i2 (x d:A) l, i1<>i2 -> nth i1 (update_nth i2 x l d) d = nth i1 l d.
Proof.
induction i1 as [ | i1 IH1].
destruct i2 as [ | i2].
tauto.
destruct l as [ | a l].
reflexivity.
reflexivity.
destruct i2 as [ | i2].
simpl.
intros  _ d l _.
apply nth_tail.
simpl.
intros x d l H.
rewrite IH1.
apply nth_tail.
congruence.
Qed.

Lemma firstn_nil : forall A n, firstn n nil = (nil:list A).
Proof.
destruct n.
reflexivity.
reflexivity.
Qed.

Lemma skipn_nil : forall A n, skipn n nil = (nil:list A).
Proof.
destruct n.
reflexivity.
reflexivity.
Qed.

Lemma firstn_cons :
  forall A (a:A) l n, firstn (S n) (a::l) = a :: firstn n l.
Proof.
destruct n.
reflexivity.
reflexivity.
Qed.

Lemma skipn_cons :
  forall A (a:A) l n, skipn (S n) (a::l) = skipn n l.
Proof.
destruct n.
reflexivity.
reflexivity.
Qed.

Lemma nth_skipn :
  forall A m n l (default:A),
  nth n (skipn m l) default = nth (m+n) l default.
Proof.
induction m as [ | m IH].
reflexivity.
intros n l default.
destruct l as [ | l].
rewrite skipn_nil.
rewrite nth_overflow.
rewrite nth_overflow.
reflexivity.
auto with arith.
auto with arith.
rewrite skipn_cons.
apply IH.
Qed.

Lemma fold_left_firstn_S :
  forall A B f len l (a0:A) (default:B),
  (len < length l)%nat ->
  fold_left f (firstn (S len) l) a0 =
  f (fold_left f (firstn len l) a0) (nth len l default).
Proof.
intros A B f len.
induction len as [ | len IH]; intros l a0 default H; destruct l as [ | a l].
contradict H.
auto with arith.
reflexivity.
contradict H.
auto with arith.
do 2 rewrite firstn_cons.
simpl (nth (S len) (a :: l) default).
simpl (fold_left f (a :: firstn len l) a0).
rewrite <- IH.
reflexivity.
auto with arith.
Qed.

Lemma length_firstn_le :
  forall A n (l:list A),
  (n <= length l)%nat -> length (firstn n l) = n.
Proof.
induction n as [ | n IH].
reflexivity.
intros l H.
destruct l as [ | a l].
auto with arith.
rewrite firstn_cons.
simpl.
auto with arith.
Qed.

Lemma length_skipn_le :
  forall A n (l:list A),
  (n <= length l)%nat -> length (skipn n l) = (length l - n)%nat.
Proof.
induction n as [ | n IH].
auto with arith.
intros l H.
destruct l as [ | a l].
reflexivity.
rewrite skipn_cons.
simpl.
apply IH.
auto with arith.
Qed.

Definition Incl {A:Type}(l1 l2:list A) : Prop :=
  exists l, Permutation (l1 ++ l) l2.

Lemma Incl_app_left : forall (A:Type)(l1 l2:list A), Incl l1 (l1 ++ l2).
Proof.
intros A l1 l2.
exists l2.
apply Permutation_refl.
Qed.

Lemma Incl_app_right : forall (A:Type)(l1 l2:list A), Incl l2 (l1 ++ l2).
Proof.
intros A l1 l2.
exists l1.
apply Permutation_app_swap.
Qed.

Definition listNE (A:Type) : Type := {l:list A | l<>nil}.

Coercion list_from_listNE {A:Type} (l:listNE A) : list A :=
  proj1_sig l.

Lemma cons_ne : forall A (a:A) l, a::l <> nil.
Proof.
congruence.
Qed.

Definition consNE {A} (a:A)(l:list A) : listNE A :=
  exist _ (a::l) (cons_ne _ a l).

Definition seqNE (start len:nat) : listNE nat :=
  match len with
  | 0 => exist _ (start::nil) (cons_ne _ start nil)
  | S len' => consNE start (List.seq (S start) len')
  end.

Lemma In_seqNE :
  forall n start len,
  len <>0 -> (In n (seqNE start len) <-> start <= n < start+len).
Proof.
unfold seqNE.
intros n start [ | len].
tauto.
intros _.
rewrite <- In_seq.
reflexivity.
Qed.

Lemma NoDup_seqNE : forall start len, NoDup (seqNE start len).
Proof.
unfold seqNE.
intros start len.
destruct len as [ | n]; simpl.
constructor.
tauto.
constructor.
constructor.
rewrite In_seq.
omega.
apply NoDup_seq.
Qed.

Lemma appNE_spec : forall A (l:listNE A)(l':list A), l++l'<>nil.
Proof.
intros A [l Hl] l'.
simpl.
destruct l as [ | x l].
tauto.
discriminate.
Qed.

Definition appNE {A} (l:listNE A)(l':list A) : listNE A :=
  exist _ (l++l') (appNE_spec A l l').

Infix "++NE" := appNE (right associativity, at level 60) : list_scope.

Lemma appNE_ass : forall A (l m n:listNE A), (l ++NE m) ++NE n = l ++NE m ++NE n.
Proof.
intros A l m n.
unfold appNE.
simpl.
apply subset_eq_compatT.
apply app_ass.
Qed.

Program Definition mapNE {A B}(f:A->B)(l:listNE A) : listNE B :=
  List.map f l.
Next Obligation.
destruct l as [ [ | a l] Hl].
congruence.
discriminate.
Qed.

Section NoDup2.

Variable A:Type.

Variable eq_A_dec : forall a1 a2:A, {a1=a2}+{a1<>a2}.

Lemma Finite_to_listNE :
  inhabited A -> Finite A -> exists l:listNE A, NoDup l /\ forall a:A, In a l.
Proof.
intros [a] Hfin.
destruct (Finite_to_list A eq_A_dec Hfin) as [l [H1 H2] ].
assert (l <> nil) as Hl.
destruct l as [ | b l].
generalize (H2 a).
contradiction.
discriminate.
exists (exist _ l Hl).
simpl.
tauto.
Qed.

End NoDup2.
