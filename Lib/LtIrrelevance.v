(** LtIrrelevance.v : Proof irrelevance of [le] and [lt] *)

Require Export Eqdep_dec.
Require Import Arith.

Set Implicit Arguments.

Scheme le_rec := Induction for le Sort Prop.

Lemma le_inversion : forall (x y:nat) (P:le x y),
 (exists H:x = y, P = eq_rect x (le x) (le_n x) y H) \/
 (exists y', exists R:S y' = y, exists H:le x y',
   P = eq_rect (S y') (le x) (le_S x y' H) y R).
Proof.
 intros x y P.
 case P.
 left.
 exists (refl_equal x); auto.
 intros m H.
 right.
 exists m.
 exists (refl_equal (S m)).
 exists H; auto.
Qed.

Lemma le_eq : forall (x y:nat) (p1 p2:x <= y), p1 = p2.
Proof.
 intros x y p1.
 elim p1 using le_rec.
 intros p2.
 destruct (le_inversion p2) as [(x0,H0)|(x0,(x1,(x2,_)))].
 rewrite H0.
 rewrite <- eq_rect_eq_dec; auto with *.
 subst.
 absurd (S x0 <= x0); auto with arith.

 intros.
 destruct (le_inversion p2) as [(x0,H0)|(x0,(x1,(x2,H0)))].
 absurd (S m <= m); auto with arith.
 rewrite <- x0.
 assumption.

 injection x1; intros; subst.
 rewrite (H x2).
 rewrite <- eq_rect_eq_dec; auto with *. 
Qed.

Lemma lt_eq : forall x y (H1 H2: x < y), H1 = H2.
Proof.
 intros.
 hnf in *.
 rewrite (le_eq H1 H2).
 reflexivity.
Qed.
