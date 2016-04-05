(*
 * Copyright 2007-9 David Nowak, RCIS, AIST, Japan
 * All rights reserved
 *)

(** This file contains some definitions, lemmas and tactics that
    are missing from the Arith section of the Coq standard library.
 *)

Require Import Classical Epsilon Arith Even Div2 Omega.
Require Import MiscLogic.

Lemma double_minus: forall n m : nat, double (n - m) = double n - double m.
Proof.
induction n as [ | n IH].
reflexivity.
destruct m as [ | m].
reflexivity.
simpl.
rewrite IH.
unfold double.
omega.
Qed.

Lemma even_even_minus: forall n m : nat, even n -> even m -> even (n - m).
Proof.
intros n m Hn Hm.
destruct (even_2n _ Hm) as [m' Hm'].
destruct (even_2n _ Hn) as [n' Hn'].
subst m.
subst n.
rewrite <- double_minus.
cutrewrite (double (n'-m')= 2*(n'-m'))%nat.
auto with arith.
unfold double.
omega.
Qed.

Lemma odd_even_minus: forall n m : nat, odd n -> odd m -> even (n - m).
Proof.
intros n m Hn Hm.
destruct (odd_S2n _ Hm) as [m' Hm'].
destruct (odd_S2n _ Hn) as [n' Hn'].
subst m.
subst n.
simpl.
rewrite <- double_minus.
cutrewrite (double (n'-m')= 2*(n'-m'))%nat.
auto with arith.
unfold double.
omega.
Qed.

Definition IsLeast (P:nat->Prop)(n:nat) : Prop :=
  P n /\ forall m, m<n -> ~P m.

Definition least (P:nat->Prop) : nat :=
  iota (inhabits 0) (IsLeast P).

Lemma least_exists : forall (P:nat->Prop), (exists n, P n) -> exists! m, IsLeast P m.
Proof.
intros P H.
apply NNPP.
contradict H.
apply all_not_not_ex.
apply well_founded_ind with (R:=lt).
auto with arith.
intros n H0.
contradict H.
exists n.
unfold IsLeast.
split.
tauto.
intros m [H1 H2].
generalize (H0 m).
generalize (H2 n).
clear H0 H2.
intros H2 H0.
destruct (lt_eq_lt_dec m n) as [ [H3 | H3] | H3].
tauto.
congruence.
tauto.
Qed.

Lemma least_unique :
  forall n (P:nat -> Prop), P n -> n < least P -> n = least P.
Proof.
intros n P H.
unfold least.
apply iota_ind.
apply least_exists.
exists n.
assumption.
unfold IsLeast.
intros m [H1 H2] H3.
generalize (H2 n).
tauto.
Qed.
