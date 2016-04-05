(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** This file contains some definitions, lemmas and tactics that
    are missing from the ZArith section of the Coq standard library.
 *)

Require Import Classical.
Require Import Even ZArith Znumtheory.

Open Local Scope Z_scope.

Lemma Zbetween_dec : forall a b x:Z, {a <= x < b}+{~(a <= x < b)}.
Proof.
intros a b x.
destruct (Z_le_dec a x) as [H1 | H1].
destruct (Z_lt_dec x b) as [H2 | H2].
left.
tauto.
right.
tauto.
right.
tauto.
Qed.

Lemma Z_eq_mod_ex : forall x y n, n<>0 -> (x mod n = y mod n <-> exists k, x = y 
+ k*n).
Proof.
intros x y n Hn.
split.
unfold Zmod.
generalize (Z_div_mod_full x n Hn).
generalize (Z_div_mod_full y n Hn).
destruct (Zdiv_eucl x n) as [qx rx].
destruct (Zdiv_eucl y n) as [qy ry].
unfold Remainder.
intros [H1 H2] [H3 H4] H.
subst x.
subst y.
subst ry.
exists (qx - qy).
ring.
intros [k H].
subst x.
apply Z_mod_plus_full.
Qed.

Lemma even_odd_Zabs_nat :
  forall n,
  0<=n -> (even (Zabs_nat n) <-> Zeven n) /\  (odd (Zabs_nat n) <-> Zodd n).
Proof.
intros n Hn.
pattern n.
apply natlike_ind.
split.
auto with *.
split; simpl; intro H.
inversion H.
contradiction.
clear n Hn.
intros n Hn [IH1 IH2].
unfold Zsucc.
rewrite Zabs_nat_Zplus.
change (Zabs_nat 1) with 1%nat.
split; split; intro H.
apply Zeven_Sn.
rewrite <- IH2.
apply even_plus_odd_inv_l with (m:=1%nat).
assumption.
auto with arith.
rewrite plus_comm.
apply even_S.
rewrite IH2.
replace n with (n+1-1)%Z.
apply Zodd_pred.
assumption.
ring.
apply Zodd_Sn.
rewrite <- IH1.
apply odd_plus_even_inv_l with (m:=1%nat).
assumption.
auto with arith.
rewrite plus_comm.
apply odd_S.
rewrite IH1.
replace n with (n+1-1).
apply Zeven_pred.
assumption.
ring.
assumption.
discriminate.
assumption.
Qed.

Lemma even_Zabs_nat : forall n, 0<=n -> (even (Zabs_nat n) <-> Zeven n).
Proof.
intros n Hn.
generalize (even_odd_Zabs_nat n Hn).
tauto.
Qed.

Lemma odd_Zabs_nat : forall n, 0<=n -> (odd (Zabs_nat n) <-> Zodd n).
Proof.
intros n Hn.
generalize (even_odd_Zabs_nat n Hn).
tauto.
Qed.

Lemma Zminus_mod_prime_0 :
  forall a b p,
  prime p -> 0 <= a < p -> 0 <= b < p -> (a-b) mod p = 0 -> a mod p = b mod p.
Proof.
intros a b p Hp Ha Hb H.
destruct (Z_le_gt_dec b a) as [H0 | H0].
rewrite Zmod_small.
rewrite Zmod_small.
rewrite Zmod_small in H.
omega.
omega.
assumption.
assumption.
cutrewrite (a-b = - (b-a)) in H.
rewrite Z_mod_nz_opp_full in H.
rewrite Zmod_small in H.
cutrewrite (b = p+a).
omega.
omega.
omega.
apply Zrel_prime_neq_mod_0.
destruct Hp.
assumption.
apply rel_prime_le_prime.
assumption.
omega.
ring.
Qed.

Lemma Zplus_mod_prime_0 :
  forall a b p,
  prime p -> 0 <= a < p -> 0 <= b < p -> (a+b) mod p = 0 -> a mod p = (-b) mod p.
Proof.
intros a b p Hp Ha Hb H.
destruct (Z_eq_dec b 0) as [H0 | H0].
subst b.
rewrite (Zmod_small (-0)).
simpl.
rewrite <- H.
f_equal.
ring.
assumption.
cutrewrite (a+b = a - (-b)) in H.
rewrite Zminus_mod in H.
rewrite Z_mod_nz_opp_full in H.
rewrite (Zmod_small a) in H.
rewrite (Zmod_small b) in H.
cut (0 <= p-b < p).
clear H0.
intro H0.
rewrite (Zminus_mod_prime_0 _ _ _ Hp Ha H0 H).
cutrewrite (p-b = -b + 1*p).
apply Z_mod_plus_full.
ring.
omega.
assumption.
assumption.
apply Zrel_prime_neq_mod_0.
destruct Hp.
assumption.
apply rel_prime_le_prime.
assumption.
omega.
ring.
Qed.

Lemma Zmult_mod_prime_0 :
  forall a b p, prime p -> (a*b) mod p = 0 -> a mod p = 0 \/ b mod p = 0.
Proof.
intros a b p Hp H.
apply NNPP.
contradict H.
apply not_or_and in H.
destruct H as [H1 H2].
apply Zrel_prime_neq_mod_0.
destruct Hp.
assumption.
apply rel_prime_sym.
apply rel_prime_mult.
apply prime_rel_prime.
assumption.
contradict H1.
apply Zdivide_mod; trivial.
apply prime_rel_prime.
assumption.
contradict H2.
apply Zdivide_mod; trivial.
Qed.

Lemma Zequal_square_mod :
  forall a b p, prime p -> 0 <= a < p -> 0 <= b < p ->
  (a * a mod p = b * b mod p <-> a mod p = b mod p \/ a mod p = -b mod p).
Proof.
intros a b p Hp Ha Hb.
split.
intro H.
cut (((a*a) mod p - (b*b) mod p) mod p = 0).
clear H.
intro H.
rewrite <- Zminus_mod in H.
cutrewrite (a*a - b*b = (a-b) * (a+b))%Z in H.
apply Zmult_mod_prime_0 in H.
destruct H as [H | H].
left.
apply Zminus_mod_prime_0.
assumption.
assumption.
assumption.
assumption.
right.
apply Zplus_mod_prime_0.
assumption.
assumption.
assumption.
assumption.
assumption.
ring.
rewrite <- (Zmod_small 0 p).
f_equal.
omega.
omega.
rewrite (Zmult_mod a).
rewrite (Zmult_mod b).
intros [H | H]; rewrite H.
reflexivity.
rewrite <- Zmult_mod.
rewrite <- Zmult_mod.
f_equal.
ring.
Qed.

Lemma Zeven_plus_odd_inv_l_even_plus_even_inv_l :
  forall n m, n>=0 -> (Zodd (n + m) -> Zeven m -> Zodd n) /\ (Zeven (n + m) -> Zeven m -> Zeven n).
Proof.
intros n m Hn.
revert m.
pattern n.
apply natlike_rec.
simpl.
intro m.
split.
intros H1 H2.
generalize (Zodd_not_Zeven _ H1).
contradiction.
trivial.
clear n Hn.
intros n Hn IH m.
split; intros H1 H2.
apply Zodd_Sn.
destruct (IH m) as [IH1 IH2].
apply IH2.
cutrewrite (n + m = Zpred (Zsucc n + m)).
apply Zeven_pred.
assumption.
unfold Zpred.
ring.
assumption.
apply Zeven_Sn.
destruct (IH m) as [IH1 IH2].
apply IH1.
cutrewrite (n + m = Zpred (Zsucc n + m)).
apply Zodd_pred.
assumption.
unfold Zpred.
ring.
assumption.
omega.
Qed.

Lemma Zeven_plus_odd_inv_l :
  forall n m, n>=0 -> Zodd (n + m) -> Zeven m -> Zodd n.
Proof.
intros n m H H1 H2.
destruct (Zeven_plus_odd_inv_l_even_plus_even_inv_l _ m H).
tauto.
Qed.

Lemma Zeven_plus_even_inv_l :
  forall n m, n>=0 -> Zeven (n + m) -> Zeven m -> Zeven n.
Proof.
intros n m H H1 H2.
destruct (Zeven_plus_odd_inv_l_even_plus_even_inv_l _ m H).
tauto.
Qed.

Lemma Zodd_plus_even_inv_l_odd_plus_odd_inv_l :
  forall n m,
  n>=0 ->
  (Zodd (n + m) -> Zodd m -> Zeven n) /\ (Zeven (n + m) -> Zodd m -> Zodd n).
Proof.
intros n m Hn.
revert m.
pattern n.
apply natlike_rec.
simpl.
intro m.
split.
trivial.
intros H1 H2.
generalize (Zodd_not_Zeven _ H2).
contradiction.
clear n Hn.
intros n Hn IH m.
split; intros H1 H2.
apply Zeven_Sn.
destruct (IH m) as [IH1 IH2].
apply IH2.
cutrewrite (n + m = Zpred (Zsucc n + m)).
apply Zeven_pred.
assumption.
unfold Zpred.
ring.
assumption.
apply Zodd_Sn.
destruct (IH m) as [IH1 IH2].
apply IH1.
cutrewrite (n + m = Zpred (Zsucc n + m)).
apply Zodd_pred.
assumption.
unfold Zpred.
ring.
assumption.
omega.
Qed.

Lemma Zodd_plus_even_inv_l :
  forall n m, n>=0 -> Zodd (n + m) -> Zodd m -> Zeven n.
Proof.
intros n m H H1 H2.
destruct (Zodd_plus_even_inv_l_odd_plus_odd_inv_l _ m H).
tauto.
Qed.

Lemma Zodd_plus_odd_inv_l :
  forall n m, n>=0 -> Zeven (n + m) -> Zodd m -> Zodd n.
Proof.
intros n m H H1 H2.
destruct (Zodd_plus_even_inv_l_odd_plus_odd_inv_l _ m H).
tauto.
Qed.

Lemma Zodd_minus_Zeven : forall m n, n <= m -> Zodd m -> Zodd n -> Zeven (m-n).
Proof.
intros m n H1 H2 H3.
apply Zodd_plus_even_inv_l with (m:=n).
omega.
cutrewrite (m-n+n=m).
assumption.
ring.
assumption.
Qed.

Lemma Zodd_Zeven_minus_Zodd : forall m n, n<=m -> Zodd m -> Zeven n -> Zodd (m-n).
Proof.
intros m n H1 H2 H3.
apply Zeven_plus_odd_inv_l with (m:=n).
omega.
cutrewrite (m-n+n = m).
assumption.
ring.
assumption.
Qed.

Lemma Zdiv2_pos : forall a, 1 < a -> 0 < Zdiv2 a.
Proof.
intros a Ha.
repeat
  match goal with
  | x:Z |- _ => destruct x; simpl; try reflexivity; try ring; try (contradict Ha; progress auto with zarith)
  end.
destruct p.
assumption.
assumption.
assumption.
destruct p.
assumption.
assumption.
discriminate.
Qed.

Lemma Zdiv2_double : forall a, Zdiv2 (2 * a) = a.
Proof.
destruct a.
reflexivity.
reflexivity.
reflexivity.
Qed.

Lemma Zdiv2_S_double : forall a, a>=0 -> Zdiv2 (Zsucc (2 * a)) = a.
Proof.
destruct a.
reflexivity.
reflexivity.
intro H.
contradict H.
auto.
Qed.

Lemma Zdiv2_ge : forall a b, a >= b -> b >= 0 -> Zdiv2 a >= Zdiv2 b.
Proof.
intros a b H Hb.
cut (a>=0).
intro Ha.
destruct (Zeven_odd_dec a) as [H1 | H1];
destruct (Zeven_odd_dec b) as [H2 | H2].
generalize (Zeven_div2 _ H1).
generalize (Zeven_div2 _ H2).
omega.
generalize (Zeven_div2 _ H1).
generalize (Zodd_div2 _ Hb H2).
omega.
generalize (Zodd_div2 _ Ha H1).
generalize (Zeven_div2 _ H2).
omega.
generalize (Zodd_div2 _ Ha H1).
generalize (Zodd_div2 _ Hb H2).
omega.
omega.
Qed.

Lemma Zdiv2_le : forall a b, a <= b -> a >= 0 -> Zdiv2 a <= Zdiv2 b.
Proof.
intros a b H Ha.
cut (b>=0).
intro Hb.
destruct (Zeven_odd_dec a) as [H1 | H1];
destruct (Zeven_odd_dec b) as [H2 | H2].
generalize (Zeven_div2 _ H1).
generalize (Zeven_div2 _ H2).
omega.
generalize (Zeven_div2 _ H1).
generalize (Zodd_div2 _ Hb H2).
omega.
generalize (Zodd_div2 _ Ha H1).
generalize (Zeven_div2 _ H2).
omega.
generalize (Zodd_div2 _ Ha H1).
generalize (Zodd_div2 _ Hb H2).
omega.
omega.
Qed.

Lemma Zdiv2_minus_even_r : forall a b, a>=b -> b>=0 -> Zeven b -> Zdiv2 (a-b) = Zdiv2 a - Zdiv2 b.
Proof.
intros a b H H' Hb.
destruct (Zeven_odd_dec a) as [Ha | Ha].
rewrite (Zeven_div2 _ Ha) at 1.
rewrite (Zeven_div2 _ Hb) at 1.
rewrite <- Zmult_minus_distr_l.
apply Zdiv2_double.
cut (a>=0).
intro H''.
rewrite (Zodd_div2 _ H'' Ha) at 1.
rewrite (Zeven_div2 _ Hb) at 1.
rewrite Zplus_comm.
cutrewrite (1 + 2 * Zdiv2 a - 2 * Zdiv2 b = Zsucc (2 * Zdiv2 a - 2 * Zdiv2 b)).
rewrite <- Zmult_minus_distr_l.
apply Zdiv2_S_double.
cut (Zdiv2 a >= Zdiv2 b).
omega.
apply Zdiv2_ge.
assumption.
assumption.
ring.
omega.
Qed.

Lemma blum_odd : forall n:Z, 0<=n -> n mod 4 = 3 mod 4 -> Zodd (Zdiv2 (n-1)).
Proof.
intros n Hn.
pattern n.
apply Zlt_0_rec.
clear n Hn.
intros n IH H1 H2.
destruct (Z_lt_dec n 4) as [H0 | H0].
destruct (Z_eq_dec n 0) as [H3 | H3].
subst n.
discriminate.
destruct (Z_eq_dec n 1) as [H4 | H4].
subst n.
discriminate.
destruct (Z_eq_dec n 2) as [H5 | H5].
subst n.
discriminate.
cut (n=3).
intro H6.
subst n.
change True.
trivial.
omega.
destruct (Z_eq_dec n 4) as [H6 | H6].
rewrite H6.
simpl.
trivial.
cut (Zodd (Zdiv2 (n-4-1))).
intro H.
apply Zeven_plus_odd_inv_l with (-2).
cut (1 < n-1).
intro H3.
generalize (Zdiv2_pos _ H3).
omega.
omega.
cutrewrite (Zdiv2 (n-1) + -2 = Zdiv2 (n-4-1)).
assumption.
cutrewrite (n-4-1 = (n-1) - 4).
symmetry.
rewrite Zdiv2_minus_even_r.
reflexivity.
omega.
discriminate.
auto with zarith.
ring.
auto with zarith.
apply IH.
omega.
rewrite Zminus_mod.
rewrite Z_mod_same.
rewrite Zminus_0_r.
rewrite Zmod_mod.
assumption.
omega.
assumption.
Qed.

Lemma Z_opp_one_power_parity :
  forall a, 0<=a -> (Zodd a -> (-1)^a = -1) /\ (Zeven a -> (-1)^a = 1).
Proof.
intros a Ha.
pattern a.
apply natlike_rec2.
split.
contradiction.
reflexivity.
clear a Ha.
intros a H0 [H1 H2].
unfold Zsucc.
rewrite Zpower_exp.
split; intro H.
rewrite H2.
reflexivity.
cutrewrite (a = a +1-1).
apply Zeven_pred.
assumption.
ring.
rewrite H1.
reflexivity.
cutrewrite (a = a +1-1).
apply Zodd_pred.
assumption.
ring.
omega.
discriminate.
assumption.
Qed.

Lemma Z_opp_one_power_odd : forall a, 0<=a -> Zodd a -> (-1)^a = -1.
Proof.
intros a Ha.
generalize (Z_opp_one_power_parity _ Ha).
tauto.
Qed.

Lemma Zodd_prime_gt_2 : forall p, prime p -> Zodd p -> p>2.
Proof.
intros p p_prime p_odd.
destruct p_prime as [H1 _].
cut (p>=0).
intro H2.
generalize (Zodd_div2 _ H2 p_odd).
omega.
omega.
Qed.

Lemma Z_divide_le : forall a b, b>0 -> (a|b) -> a<= b.
Proof.
intros a b H1 H2.
destruct H2 as [c H2].
rewrite H2.
cut (a<0 \/ a>=0).
intros [H3 | H3].
omega.
cut (c*a>0).
intro H4.
pattern a at 1.
replace a with (1*a)%Z.
apply Zmult_le_compat_r.
cut (a=0 \/ a>0).
intros [H5 | H5].
rewrite H5 in H4.
omega.
cut (c>0).
omega.
apply Zmult_gt_0_reg_l with a.
trivial.
cutrewrite (a*c=c*a)%Z.
trivial.
ring.
omega.
omega.
ring.
congruence.
omega.
Qed.

Lemma Z_rel_prime_not_divide : forall a b, 1<b -> rel_prime a b -> ~(b|a).
Proof.
intros a b H0 H1.
destruct H1 as [_ _ H1].
intro H2.
cut (b|b).
intro H3.
generalize (H1 _ H2 H3).
intro H4.
cut (1>0).
intro H5.
generalize (Z_divide_le _ _ H5 H4).
omega.
omega.
apply Zdivide_refl.
Qed.

Lemma square_mod_1 :
  forall a b,
  prime b -> (a^2 mod b = 1 mod b <-> a mod b = 1 mod b \/ a mod b = -1 mod b).
Proof.
intros a b H.
cut (1<b).
intro Hp.
rewrite <- Zmod_mod.
rewrite <- (Zmod_mod a).
rewrite <- Zequal_square_mod.
cutrewrite (a^2 = a*a).
rewrite Zmult_mod.
rewrite Zmod_mod.
tauto.
ring.
assumption.
apply Z_mod_lt.
omega.
omega.
destruct H.
assumption.
Qed.

Section CRT.

Variables m n : Z.

Hypothesis rel_primality : rel_prime m n.

Lemma chinese : forall a b, {x:Z | x mod m = a mod m /\ x mod n = b mod n}.
Proof.
intros a b.
destruct (euclid m n) as [u v d H1 H2].
exists (a * (d * v * n) + b * (d * u * m)).
destruct (Zis_gcd_unique _ _ _ _ rel_primality H2) as [H | H].
rewrite <- H in *.
rewrite Zmult_1_l.
rewrite Zmult_1_l.
split.
rewrite Zmult_assoc.
rewrite Zmult_assoc.
rewrite Z_mod_plus_full.
rewrite <- Zmult_assoc.
cutrewrite (v*n = 1 - u*m).
cutrewrite (a*(1-u*m) = a + (-a*u*m)).
apply Z_mod_plus_full.
ring.
omega.
rewrite Zplus_comm.
rewrite Zmult_assoc.
rewrite Zmult_assoc.
rewrite Z_mod_plus_full.
rewrite <- Zmult_assoc.
cutrewrite (u*m = 1 - v*n).
cutrewrite (b*(1-v*n) = b + (-b*v*n)).
apply Z_mod_plus_full.
ring.
omega.
cut (d=-1).
clear H.
intro H.
rewrite H in *.
cutrewrite (-1 * u = -u).
cutrewrite (-1 * v = -v).
split.
rewrite Zmult_assoc.
rewrite Zmult_assoc.
rewrite Z_mod_plus_full.
rewrite <- Zmult_assoc.
cutrewrite (-v*n = 1 - -u*m).
cutrewrite (a*(1- -u*m) = a + (a * u *m)).
apply Z_mod_plus_full.
ring.
transitivity (- (v*n)).
ring.
transitivity (1 + u*m).
omega.
ring.
rewrite Zplus_comm.
rewrite Zmult_assoc.
rewrite Zmult_assoc.
rewrite Z_mod_plus_full.
rewrite <- Zmult_assoc.
cutrewrite (-u*m = 1 - -v*n).
cutrewrite (b*(1- -v*n) = b + b*v*n).
apply Z_mod_plus_full.
ring.
transitivity (- (u*m)).
ring.
transitivity (1 + v*n).
omega.
ring.
reflexivity.
reflexivity.
omega.
Qed.

Hypothesis m_neq_0 : m <> 0.

Hypothesis n_neq_0 : n <> 0.

Lemma chinese_unique_modulo :
  forall a b x, x mod m = a mod m -> x mod n = b mod n ->
  x mod (m*n) = (proj1_sig (chinese a b)) mod (m*n).
Proof.
intros a b x Ha Hb.
destruct (chinese a b) as [x' [H1 H2] ].
simpl.
rewrite <- Ha in H1.
rewrite <- Hb in H2.
clear Ha Hb.
rewrite Z_eq_mod_ex in H1.
rewrite Z_eq_mod_ex in H2.
symmetry.
rewrite Z_eq_mod_ex.
destruct H1 as [k1 H1].
destruct H2 as [k2 H2].
generalize (rel_prime_bezout _ _ rel_primality).
intros [u v H].
cut (k1 * m = k2 * n).
intro H0.
cut (u * (k1 * m) + k1 * v * n = k1).
cut (k2 * u * m + v * (k2 * n) = k2).
intros H3 H4.
rewrite <- H0 in H3.
rewrite H0 in H4.
cut (k2 = m * (k2 * u + k1 * v)).
cut (k1 = n * (k2 * u + k1 * v)).
clear H3 H4.
intros H3 H4.
rewrite H3 in H1.
clear H2 H3 H4.
exists (k2*u + k1*v).
rewrite (Zmult_comm m n).
rewrite Zmult_assoc.
rewrite (Zmult_comm (k2*u + k1*v) n).
assumption.
rewrite Zmult_plus_distr_r.
rewrite Zmult_assoc.
rewrite Zmult_comm.
rewrite (Zmult_comm n k2).
rewrite (Zmult_comm n).
congruence.
rewrite Zmult_plus_distr_r.
rewrite (Zmult_comm m).
rewrite Zmult_assoc.
rewrite (Zmult_comm (m*k1)).
rewrite (Zmult_comm m k1).
congruence.
transitivity (k2 * (u*m) + k2 * (v*n)).
ring.
rewrite <- Zmult_plus_distr_r.
rewrite H.
ring.
transitivity (k1 * (u*m) + k1 * (v*n)).
ring.
rewrite <- Zmult_plus_distr_r.
rewrite H.
ring.
omega.
intro H.
generalize (Zmult_integral _ _ H).
tauto.
assumption.
assumption.
Qed.

End CRT.
