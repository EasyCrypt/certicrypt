(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** This file contains an adaptation of Fermat's little theorem from
    the Pocklington library.
 *)

Require Import ZArith Znumtheory.

Require Import exp.
Require Import modulo.
Require Import divides.
Require Import prime.
Require Import fermat.

Local Open Scope Z_scope.

Lemma Exp_eq : forall a n, 0 <= n -> Exp a (Zabs_nat n) = a^n.
Proof.
intros a n Hn.
pattern n.
apply natlike_ind.
reflexivity.
clear n Hn.
intros n Hn IH.
rewrite Zabs_nat_Zsucc.
simpl.
rewrite IH.
unfold Zsucc.
rewrite Zpower_exp.
ring.
omega.
discriminate.
assumption.
assumption.
Qed.

Lemma from_Mod : forall a b n, 0 <= n -> Mod a b (Zabs_nat n) -> a mod n = b mod n.
Proof.
unfold Mod.
intros a b n Hn [q H].
subst a.
rewrite Zmult_comm.
rewrite inj_Zabs_nat.
rewrite Zabs_eq.
apply Z_mod_plus_full.
assumption.
Qed.

Lemma from_Divides : forall n a, 0 <= a -> Divides n (Zabs_nat a) -> (Z_of_nat n | a). 
Proof.
unfold Divides.
intros n a Ha [q H].
apply Zdivide_intro with (Z_of_nat q).
rewrite <- inj_mult.
rewrite mult_comm.
rewrite <- H.
rewrite inj_Zabs_nat.
rewrite Zabs_eq.
reflexivity.
assumption.
Qed.

Lemma to_Prime : forall p, prime p -> Prime (Zabs_nat p).
Proof.
unfold Prime.
intros p H1.
split.
change 1%nat with (Zabs_nat 1).
apply Zabs_nat_lt.
destruct H1.
omega.
intros q H2.
apply from_Divides in H2.
apply prime_divisors in H2.
destruct H2 as [H2 | [H2 | [H2 | H2] ] ].
omega.
omega.
right.
rewrite <- H2.
rewrite Zabs_nat_Z_of_nat.
reflexivity.
generalize (Zle_0_nat q).
rewrite H2.
destruct H1.
omega.
assumption.
destruct H1.
omega.
Qed.

Theorem little_fermat :
  forall a p, prime p -> rel_prime a p -> (a ^ (p-1)) mod p = 1 mod p.
Proof.
intros a p H1 H2.
apply from_Mod.
destruct H1.
omega.
rewrite <- Exp_eq.
rewrite Zabs_nat_Zminus.
change (Zabs_nat 1) with 1%nat.
rewrite <- pred_of_minus.
apply flt.
apply to_Prime.
assumption.
intro H3.
apply from_Mod in H3.
apply rel_prime_mod in H2.
rewrite H3 in H2.
apply rel_prime_mod_rev in H2.
revert H2.
apply not_rel_prime_0.
destruct H1.
assumption.
destruct H1.
omega.
destruct H1.
omega.
destruct H1.
omega.
destruct H1.
omega.
destruct H1.
omega.
Qed.
