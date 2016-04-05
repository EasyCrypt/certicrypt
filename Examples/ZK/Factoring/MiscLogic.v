(*
 * Copyright 2007-9 David Nowak, RCIS, AIST, Japan
 * All rights reserved
 *)

(** This file contains some definitions, lemmas and tactics that
    are missing from the Logic section of the Coq standard library.
 *)

Require Import ProofIrrelevance.
Require Import Epsilon.

Lemma subset_eq_compatT :
    forall (U:Type) (P:U->Prop) (x y:U) (p:P x) (q:P y),
      x = y -> exist P x p = exist P y q.
  Proof.
    intros.
    rewrite proof_irrelevance with (p1:=q) (p2:=eq_rect x P p y H).
    elim H using eq_indd.
    reflexivity.
  Qed.

Theorem epsilon_ind :
  forall A (i:A)(P:A->Prop)(Q:A->Prop),
  (exists a:A, P a) -> (forall a : A, P a -> Q a) -> (Q (epsilon (inhabits i) P)).
Proof.
intros A i P Q [a H1] H2.
apply H2.
apply epsilon_spec.
exists a.
assumption.
Qed.

Theorem iota_ind :
  forall A (i:A)(P:A->Prop)(Q:A->Prop),
    (exists! a, P a) -> (forall a : A, P a -> Q a) -> (Q (iota (inhabits i) P)).
Proof.
intros A i P Q [a [H1 H2] ] H3.
apply H3.
apply iota_spec.
exists a.
split; assumption.
Qed.
