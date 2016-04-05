(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** This file contains some notions on integers modulo n.
    In particular it provides Legendre and Jacobi symbols.

    N.B. Lemma [prime_cyclic] is currently admitted.
 *)
Add LoadPath "./Pocklington".
Require Import ProofIrrelevance Classical.
Require Import Epsilon Recdef Even Div2 ZArith Znumtheory Zpow_facts Coq.Lists.List.
Require Import MiscLogic MiscArith MiscZArith MiscLists.
Require Import Group2 LittleFermat.
Require Import Permutation.

Open Local Scope group_scope.

Section Zstar1.

Variable n : Z.

Hypothesis n_gt_1 : 1 < n.

Definition carrier : Set := { x:Z | 0 <= x < n /\ rel_prime x n }.

Definition eq_dec : forall x y : carrier, {x=y}+{x<>y}.
Proof.
intros [x [Hx1 Hx2 ] ] [y [Hy1 Hy2] ].
destruct (Z_eq_dec x y) as [H | H].
left.
apply subset_eq_compat.
assumption.
right.
congruence.
Defined.

Lemma neutral_spec : 0 <= 1 < n /\ rel_prime 1 n.
Proof.
split.
omega.
unfold rel_prime.
apply Zis_gcd_sym.
apply Zis_gcd_1.
Qed.

Definition neutral : carrier :=
  exist _ 1 neutral_spec.

Lemma mult_spec :
  forall x y:carrier,
  0 <= (proj1_sig x * proj1_sig y) mod n < n /\
  rel_prime ((proj1_sig x * proj1_sig y) mod n) n.
Proof.
intros [x [Hx1 Hx2 ] ] [y [Hy1 Hy2] ].
simpl.
split.
apply Z_mod_lt.
omega.
apply rel_prime_mod.
omega.
unfold rel_prime.
apply Zis_gcd_sym.
apply rel_prime_mult; unfold rel_prime; apply Zis_gcd_sym; assumption.
Qed.

Definition mult (x y:carrier) : carrier :=
  exist _ ((proj1_sig x * proj1_sig y) mod n) (mult_spec x y).

Lemma inv_spec :
  forall x:carrier, 
  0 <= (let (y, H, d, _, _) := euclid (proj1_sig x) n in (d * y) mod n) < n /\
  rel_prime (let (y, H, d, _, _) := euclid (proj1_sig x) n in (d * y) mod n) n.
Proof.
intros [x [Hx1 Hx2] ].
simpl.
destruct (euclid x n) as [u v d H1 H2].
split.
apply Z_mod_lt.
omega.
apply rel_prime_mod.
omega.
apply Zis_gcd_uniqueness_apart_sign with (d:=d) in Hx2.
destruct Hx2 as [H | H]; rewrite H in *; clear H.
rewrite Zmult_1_l.
apply bezout_rel_prime.
econstructor.
instantiate (1:=v).
instantiate (1:=x).
rewrite Zmult_comm.
assumption.
cutrewrite ( -(1) * u = (-u))%Z.
apply bezout_rel_prime.

econstructor.
instantiate (1:=-v).
instantiate (1:=x).
cutrewrite (x * -u + -v * n = - (u * x + v * n)).
omega.
ring.
reflexivity.
assumption.
Qed.

Definition inv (x:carrier) : carrier :=
  exist _ (let (y,_,d,_,_) := euclid (proj1_sig x) n in (d*y) mod n) (inv_spec x).

Lemma mult_comm : forall x y, mult x y = mult y x.
Proof.
intros [x [Hx1 Hx2] ] [y [Hy1 Hy2] ].
apply subset_eq_compat.
rewrite Zmult_comm.
reflexivity.
Qed.

Lemma neutral_left : forall x, mult neutral x = x.
Proof.
intros [x [Hx1 Hx2] ].
apply subset_eq_compat.
rewrite Zmult_1_l.
apply Zmod_small.
assumption.
Qed.

Lemma neutral_right : forall x, mult x neutral = x.
Proof.
intro a.
rewrite mult_comm.
apply neutral_left.
Qed.

Lemma inv_left : forall x, mult (inv x) x = neutral.
Proof.
intros [x [Hx1 Hx2] ].
apply subset_eq_compat.
simpl.
destruct (euclid x n) as [u v d H1 H2].
apply Zis_gcd_uniqueness_apart_sign with (d:=d) in Hx2.
destruct Hx2 as [H | H]; rewrite H in *; clear H.

rewrite Zmult_1_l.
cut ((u*x + v*n) mod n = 1 mod n).
rewrite Zplus_mod.
rewrite Zmult_mod.
rewrite (Zmult_mod v n).
cutrewrite (n mod n = 0).
cutrewrite (v mod n * 0 = 0)%Z.
cutrewrite (0 mod n = 0).
cutrewrite (x mod n = x).
cutrewrite ((u mod n * x) mod n + 0 = (u mod n * x) mod n).
cutrewrite (((u mod n * x) mod n) mod n = (u mod n * x) mod n).
intro H3.
rewrite H3.
apply Zmod_small.
omega.
apply Zmod_small.
apply Z_mod_lt.
omega.
ring.
apply Zmod_small.
assumption.
reflexivity.
ring.
apply Z_mod_same.
omega.
f_equal.
assumption.

cutrewrite (- (1) * u = -u)%Z.
cut (((-u)*x + (-v)*n) mod n = 1 mod n).
rewrite Zplus_mod.
rewrite Zmult_mod.
rewrite (Zmult_mod (-v) n).
cutrewrite (n mod n = 0).
cutrewrite ((-v) mod n * 0 = 0)%Z.
cutrewrite (0 mod n = 0).
cutrewrite (x mod n = x).
cutrewrite (((-u) mod n * x) mod n + 0 = ((-u) mod n * x) mod n).
cutrewrite ((((-u) mod n * x) mod n) mod n = ((-u) mod n * x) mod n).
intro H3.
rewrite H3.
apply Zmod_small.
omega.
apply Zmod_small.
apply Z_mod_lt.
omega.
ring.
apply Zmod_small.
assumption.
reflexivity.
ring.
apply Z_mod_same.
omega.
f_equal.
transitivity (- (u*x + v*n)).
ring.
omega.
reflexivity.

assumption.
Qed.

Lemma inv_right : forall x, mult x (inv x) = neutral.
Proof.
intro x.
rewrite mult_comm.
apply inv_left.
Qed.


Lemma associative : forall x y z, mult x (mult y z) = mult (mult x y) z.
Proof.
intros [x [Hx1 Hx2 ] ] [y [Hy1 Hy2] ] [z [Hz1 Hz2] ].
apply subset_eq_compat.
simpl.
rewrite (Zmult_mod y z).
rewrite <- (Zmod_small _ _ Hx1).
rewrite <- Zmult_mod.
rewrite Zmult_assoc.
rewrite (Zmod_small _ _ Hx1).
rewrite (Zmod_small _ _ Hy1).
rewrite (Zmod_small _ _ Hz1).
rewrite Zmult_mod.
rewrite (Zmod_small _ _ Hz1).
reflexivity.
Qed.

Definition Zstar :=
  Build_Group
    carrier eq_dec neutral mult inv
    neutral_left neutral_right inv_left inv_right associative.

Definition parity (x:Zstar) : bool :=
  if Zodd_dec (proj1_sig x) then true else false.

Lemma opp_spec :
  forall x:Zstar,
  0 <= (- (proj1_sig x)) mod n < n /\ rel_prime ((- (proj1_sig x)) mod n) n.
Proof.
intros [x [Hx1 Hx2] ].
simpl.
split.
apply Z_mod_lt.
omega.
apply rel_prime_mod.
omega.
unfold rel_prime.
apply Zis_gcd_minus.
apply Zis_gcd_sym.
cutrewrite (- -x =  x).
assumption.
ring.
Qed.

Definition opp (x:Zstar) : Zstar :=
  exist _ ((- (proj1_sig x)) mod n) (opp_spec x).

Lemma mult_opp : forall a b, opp a * opp b = a * b.
Proof.
intros a b.
unfold opp.
simpl.
apply subset_eq_compat.
simpl.
rewrite <- Zmult_mod.
f_equal.
ring.
Qed.

Lemma eq_opp : forall x y, opp x = y -> x = opp y.
Proof.
intros [x [Hx1 Hx2] ] [y [Hy1 Hy2] ].
unfold opp.
simpl.
intro H.
apply subset_eq_compat.
injection H.
clear H.
intro H.
rewrite <- H.
clear H.
rewrite (Z_mod_nz_opp_full x).
cutrewrite (- (n - x mod n) = x mod n - n).
rewrite Zminus_mod.
rewrite Z_mod_same_full.
rewrite Zmod_mod.
rewrite Zmod_small.
rewrite Zmod_small.
ring.
assumption.
rewrite Zmod_small.
omega.
assumption.
ring.
apply Zrel_prime_neq_mod_0.
assumption.
assumption.
Qed.

Lemma opp_opp : forall  x, opp (opp x) = x.
Proof.
intro x.
symmetry.
apply eq_opp.
reflexivity.
Qed.

Lemma opp_mult_l : forall x y, opp (x * y) = opp x * y.
Proof.
intros [x [H1 H2] ] [y [H3 H4] ].
simpl.
apply subset_eq_compat.
simpl.
rewrite <- (Zmod_small y n H3) at 2.
rewrite <- Zmult_mod.
cutrewrite (-x * y = -(x*y))%Z.
rewrite Z_mod_nz_opp_full.
rewrite Z_mod_nz_opp_full.
rewrite Zmod_mod.
reflexivity.
apply Zrel_prime_neq_mod_0.
assumption.
apply rel_prime_sym.
apply rel_prime_mult.
apply rel_prime_sym.
assumption.
apply rel_prime_sym.
assumption.
apply Zrel_prime_neq_mod_0.
assumption.
apply rel_prime_mod.
omega.
apply rel_prime_sym.
apply rel_prime_mult.
apply rel_prime_sym.
assumption.
apply rel_prime_sym.
assumption.
ring.
Qed.

Lemma parity_opp : Zodd n -> forall x, parity (opp x) <> parity x.
Proof.
intros H [x [H1 H2] ].
unfold parity.
simpl.
rewrite Z_mod_nz_opp_full.
rewrite Zmod_small.
destruct (Zodd_dec (n - x)) as [H3 | H3];
destruct (Zodd_dec x) as [H4 | H4].
contradict H3.
clear H3.
apply Zeven_not_Zodd.
apply Zodd_minus_Zeven.
omega.
assumption.
assumption.
discriminate.
discriminate.
contradict H3.
clear H3.
assert (Zeven x).
destruct (Zeven_odd_dec x) as [H3 | H3].
assumption.
contradiction.
apply Zodd_Zeven_minus_Zodd.
omega.
assumption.
assumption.
assumption.
apply Zrel_prime_neq_mod_0.
assumption.
assumption.
Qed.

Function Zstar_list_from (x:Z) {measure (fun x => Zabs_nat (n-x)) x} :
  list Zstar :=
  match Zbetween_dec 0 n x with
  | left H1 =>
      match rel_prime_dec x n with
      | left H2 => exist _ x (conj H1 H2) :: Zstar_list_from (Zsucc x)
      | _ => Zstar_list_from (Zsucc x)
      end
  | _ => nil
  end.
intros x H1 _ _ _.
apply Zabs_nat_lt.
omega.
intros x H1 _ _ _.
apply Zabs_nat_lt.
omega.
Qed.

Definition Zstar_list : list Zstar :=
  Zstar_list_from 0.

Lemma Zstar_list_from_complete :
  forall (x:Zstar) y, 0 <= y <= proj1_sig x -> In x (Zstar_list_from y).
Proof.
intros [x [Hx1 Hx2] ] y Hy.
functional induction Zstar_list_from y; simpl in *.
cut (x = x0 \/ x >= Zsucc x0).
intros [H0 | H0].
left.
apply subset_eq_compat.
congruence.
right.
apply IHl.
omega.
omega.
apply IHl.
cut (x<>x0).
omega.
intro H0.
rewrite <- H0 in y.
destruct (rel_prime_dec x n) as [H2 | H2].
assumption.
contradiction.
destruct (Zbetween_dec 0 n x0) as [H0 | H0].
assumption.
omega.
Qed.

Lemma Zstar_list_spec : forall x, In x Zstar_list.
Proof.
intros [x [Hx1 Hx2] ].
apply Zstar_list_from_complete.
simpl.
omega.
Qed.

Lemma Zstar_list_from_le :
  forall x y, In y (Zstar_list_from x) -> x <= proj1_sig y.
Proof.
intro x.
functional induction Zstar_list_from x; simpl in *.
intros y [H | H].
rewrite <- H.
simpl.
omega.
generalize (IHl _ H).
omega.
destruct (rel_prime_dec x n) as [H | H].
contradiction.
intros z Hz.
generalize (IHl z Hz).
omega.
contradiction.
Qed.

Lemma NoDup_Zstar_list_from : forall x, NoDup (Zstar_list_from x).
Proof.
intro x.
functional induction Zstar_list_from x; simpl in *.
constructor.
intro H.
generalize (Zstar_list_from_le _ _ H).
simpl.
omega.
assumption.
assumption.
constructor.
Qed.

Lemma NoDup_Zstar_list : NoDup Zstar_list.
Proof.
apply NoDup_Zstar_list_from.
Qed.

Lemma finite : Finite Zstar.
Proof.
exists Zstar_list.
exact Zstar_list_spec.
Qed.

Lemma Zstar_list_ne : Zstar_list <> nil.
Proof.
assert (In neutral Zstar_list).

apply Zstar_list_spec.

destruct Zstar_list.
contradiction.
discriminate.
Qed.

Definition Zstar_listNE : listNE Zstar :=
  exist _ Zstar_list Zstar_list_ne.

Hypothesis n_prime : prime n.

Lemma equal_square_prime : forall x y, x * x = y * y <-> x = y \/ x = opp y.
Proof.
unfold opp.
intros [x [Hx1 Hx2] ] [y [Hy1 Hy2] ].
simpl.
split.

intro H.
injection H.
clear H.
intro H.
apply Zequal_square_mod in H; trivial.
destruct H as [H | H].
left.
apply subset_eq_compat.
rewrite Zmod_small in H, H.
assumption.
assumption.
assumption.
right.
apply 
subset_eq_compat.
rewrite Zmod_small in H.
assumption.
assumption.

intros [H | H]; injection H; clear H; intro H; apply subset_eq_compat; simpl.
congruence.
subst x.
rewrite <- Zmult_mod.
f_equal.
ring.
Qed.

Lemma power_nat_power_spec :
  forall (x:Zstar) m,
  0 <= (proj1_sig x ^ Z_of_nat m) mod n < n /\
  rel_prime ((proj1_sig x ^ Z_of_nat m) mod n) n.
Proof.
intros [x [Hx1 Hx2] ].
simpl.
split.
apply Z_mod_lt.
omega.
apply rel_prime_mod.
omega.
destruct m as [ | m].
apply rel_prime_1.
apply rel_prime_sym.
apply rel_prime_Zpower_r.
change 0 with (Z_of_nat 0%nat).
apply inj_lt.
omega.
apply rel_prime_sym.
assumption.
Qed.

Lemma power_nat_power :
  forall (x:Zstar) m,
  x ^ m = exist _ ((proj1_sig x ^ (Z_of_nat m)) mod n)%Z (power_nat_power_spec x m).
Proof.
intros [x [Hx1 Hx2] ] m.
induction m as [ | m IHm]; simpl in *.
apply subset_eq_compat.
rewrite Zmod_small.
reflexivity.
omega.
apply subset_eq_compat.
simpl.
injection IHm.
clear IHm.
intro IHm.
rewrite IHm.
simpl.
rewrite Zpower_pos_nat.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
rewrite Zpower_nat_Zpower.
change (S m) with (1+m)%nat.
rewrite Zpower_nat_is_exp.
symmetry.
rewrite <- Zmult_mod_idemp_r.
f_equal.
f_equal.
unfold Zpower_nat.
simpl.
rewrite Zmult_1_r.
reflexivity.
rewrite Zabs_nat_Z_of_nat.
reflexivity.
omega.
Qed.

Lemma power_power_nat :
  forall (x:Zstar) m, (proj1_sig x ^ Z_of_nat m)%Z mod n = proj1_sig (x^m).
Proof.
intros [x [Hx1 Hx2] ] m.
simpl.
rewrite power_nat_power.
simpl.
pattern (Z_of_nat m).
apply natlike_ind.
reflexivity.
reflexivity.
omega.
Qed.

Lemma Zstar_fermat :
  forall x, x ^ Zabs_nat (n - 1) = (neutral:Group2.carrier Zstar).
Proof.
intro x.
rewrite power_nat_power.
simpl.
apply subset_eq_compat.
rewrite inj_Zabs_nat.
rewrite Zabs_eq.
rewrite little_fermat.
apply Zmod_small.
omega.
assumption.
destruct x as [x [Hx1 Hx2] ].
assumption.
omega.
Qed.

Lemma Zstar_list_from_length :
  forall m, 0 < m < n -> length (Zstar_list_from m) = Zabs_nat (n-m).
Proof.
intros m Hm.
functional induction Zstar_list_from m; simpl in *.
destruct (Z_eq_dec x (n-1)) as [Hx | Hx].
rewrite Hx.
cutrewrite (Zsucc (n-1) = n).
cut (forall m, m=n -> length (Zstar_list_from m) = 0)%nat.
intro Hlen.
rewrite Hlen.
change 1%nat with (Zabs_nat 1).
f_equal.
ring.
reflexivity.
intro m.
functional induction Zstar_list_from m; simpl in *.
omega.
omega.
reflexivity.
ring.
rewrite IHl.
rewrite Zabs_nat_Zminus.
rewrite Zabs_nat_Zsucc.
rewrite (Zabs_nat_Zminus x).
cut (Zabs_nat x < Zabs_nat n)%nat.
omega.
apply Zabs_nat_lt.
assumption.
omega.
omega.
omega.
omega.
destruct (rel_prime_dec x n) as [Hx | Hx].
contradiction.
contradict Hx.
apply rel_prime_sym.
apply prime_rel_prime.
assumption.
intro Hpx.
cut (n<=x).
omega.
apply Zdivide_le.
omega.
tauto.
assumption.
destruct (Zbetween_dec 0 n x).
contradiction.
omega.
Qed.

Lemma Zstar_list_length : length Zstar_list = Zabs_nat (n-1).
Proof.
unfold Zstar_list.
cutrewrite (Zstar_list_from 0 = Zstar_list_from 1).
apply Zstar_list_from_length.
omega.
cut (forall x, x=0 -> Zstar_list_from x = Zstar_list_from 1).
auto.
intro x.
functional induction (Zstar_list_from x).
intro Hx.
subst x.
absurd (rel_prime 0 n).
apply not_rel_prime_0.
assumption.
assumption.
intro Hx.
subst x.
reflexivity.
intro Hx.
subst x.
destruct (Zbetween_dec 0 n 0) as [Hx | Hx].
contradiction.
contradict Hx.
omega.
Qed.

Lemma prime_cyclic : Cyclic Zstar.
Proof.
generalize n_prime.
admit.
Qed.

Lemma order_Zstar_prime : order Zstar = Zabs_nat (n-1).
Proof.
unfold order, to_list.
apply epsilon_ind.
apply Finite_to_listNE.
apply eq_dec.
exact (inhabits neutral).
exact finite.
intros [l Hnil] [Hnod Hin].
simpl in *.
transitivity (length Zstar_list).
apply Permutation_length.
apply NoDup_Permutation.
assumption.
apply NoDup_Zstar_list.
intro x.
split; intro H.
apply Zstar_list_spec.
apply Hin.
apply Zstar_list_length.
Qed.

Definition generator_exists : {g:Zstar | Generator _ g}.
Proof.
apply constructive_indefinite_description.
apply prime_cyclic.
Qed.

Definition generator : Zstar :=
  proj1_sig generator_exists.

Lemma is_generator : Generator Zstar generator.
Proof.
exact (proj2_sig generator_exists).
Qed.

Lemma opp_2 : forall x:Zstar, opp x = x <-> n=2.
Proof.
cut (n>0).
intro Hn.
intros [x [Hx1 Hx2] ].
unfold opp.
simpl.
split; intro H.
injection H.
clear H.
intro H.
cut ((x + x) mod n = 0).
clear H.
intro H.
apply Zmod_divide in H.
cutrewrite (x+x = 2*x)%Z in H.
generalize (prime_mult _ n_prime _ _ H).
clear H.
intros [H | H].
apply prime_div_prime.
assumption.
constructor.
omega.
intros m Hm.
cutrewrite (m=1).
apply rel_prime_1.
omega.
assumption.
contradict H.
apply Z_rel_prime_not_divide.
destruct n_prime as [H _].
omega.
assumption.
ring.
omega.
rewrite <- Zplus_mod_idemp_l.
pattern x at 2.
rewrite <- H.
rewrite <- Zplus_mod.
cutrewrite (x + -x = 0).
reflexivity.
ring.
apply subset_eq_compat.
cut (n |2*x).
clear H.
intro H.
cut ((x+x) mod n = 0).
clear H.
intro H.
cut (n<>0).
intro Hp'.
rewrite Zmod_divides in H.
destruct H as [k H].
symmetry.
apply Zmod_unique with (-k).
assumption.
cut (0 = n * -k + (x+x)).
rewrite H.
omega.
cutrewrite (n * -k = - (n*k))%Z.
omega.
ring.
assumption.
omega.
cutrewrite (x+x = 2*x)%Z.
apply Zdivide_mod.
assumption.
ring.
rewrite H.
apply Zdivide_factor_r.
destruct n_prime.
omega.
Qed.

Hypothesis n_odd : Zodd n.

Lemma neq_opp_prime : forall x, opp x <> x.
Proof.
intro x.
rewrite opp_2.
assert (n>2).
apply Zodd_prime_gt_2.
assumption.
assumption.
omega.
Qed.

Lemma legendre_spec :
  forall x, ~(n|x) -> 0 <= x mod n < n /\ rel_prime (x mod n) n.
Proof.
intros x H.
destruct n_prime as [H1 H2].
split.
apply Z_mod_lt.
omega.
apply H2.
assert (n > 0) as Hn.
omega.
generalize (Z_mod_lt x n Hn).
cut (x mod n <> 0).
omega.
intro H'.
apply H.
apply Zmod_divide.
omega.
assumption.
Qed.

Definition legendre (x:Z) : Z :=
  match Zdivide_dec n x with
  | left _ => 0
  | right H =>
      if qr_dec _ finite (exist _ (x mod n) (legendre_spec x H)) then 1 else -1
  end.

Lemma legendre_1 : legendre 1 = 1.
Proof.
unfold legendre.
destruct (Zdivide_dec n 1) as [H | H].
apply Zdivide_1 in H.
omega.
match goal with
| |- context [qr_dec _ _ ?x] => destruct (qr_dec _ finite x) as [H0 | H0]
end.
reflexivity.
contradict H0.
exists neutral.
rewrite neutral_left.
simpl.
apply subset_eq_compat.
rewrite Zmod_small.
reflexivity.
omega.
Qed.

Lemma legendre_plus_qr :
  forall x:Zstar, legendre (proj1_sig x) = 1 <-> QuadraticResidue x.
Proof.
intros [x [Hx1 Hx2] ].
simpl.
unfold legendre.
destruct (Zdivide_dec n x) as [H1 | H1].

assert (x=0 \/ 0<x) as [Hx | Hx].
omega.
subst x.
contradict Hx2.
apply not_rel_prime_0.
assumption.
apply Zdivide_le with (a:=n) in Hx.
contradict Hx.
omega.
omega.
assumption.

match goal with
| |- context [qr_dec _ _ ?x] => destruct (qr_dec _ finite x) as [ [y H2] | H2]
end.
split.
intros _.
exists y.
rewrite H2.
simpl.
apply subset_eq_compat.
apply Zmod_small.
assumption.
reflexivity.

split.
congruence.
intros [y Hy].
contradict H2.
exists y.
rewrite Hy.
simpl.
apply subset_eq_compat.
rewrite Zmod_small.
reflexivity.
assumption.
Qed.

Lemma legendre_minus_qnr :
  forall x:Zstar, legendre (proj1_sig x) = -1 <-> ~QuadraticResidue x.
Proof.
intros [x [Hx1 Hx2] ].
simpl.
unfold legendre.
destruct (Zdivide_dec n x) as [H1 | H1].

split.
congruence.
assert (x=0 \/ 0<x) as [Hx | Hx].
omega.
subst x.
contradict Hx2.
apply not_rel_prime_0.
assumption.
apply Zdivide_le with (a:=n) in Hx.
contradict Hx.
omega.
omega.
assumption.

match goal with
| |- context [qr_dec _ _ ?x] => destruct (qr_dec _ finite x) as [ [y H2] | H2]
end.
split.
congruence.
intros H.
contradict H.
exists y.
rewrite H2.
simpl.
apply subset_eq_compat.
apply Zmod_small.
assumption.

split.
intros _.
contradict H2.
destruct H2 as [y H2].
exists y.
rewrite H2.
simpl.
apply subset_eq_compat.
rewrite Zmod_small.
reflexivity.
assumption.
reflexivity.
Qed.

Lemma legendre_mod : forall x, legendre (x mod n) = legendre x.
Proof.
intro x.
unfold legendre.
destruct (Zdivide_dec n (x mod n)) as [H1 | H1];
destruct (Zdivide_dec n x) as [H2 | H2].
reflexivity.
contradict H2.
apply Zmod_divide.
omega.
rewrite <- Zmod_mod.
apply Zdivide_mod.
assumption.
contradict H1.
apply Zmod_divide.
omega.
rewrite Zmod_mod.
apply Zdivide_mod.
assumption.
destruct (
  qr_dec Zstar finite (exist _ ((x mod n) mod n) (legendre_spec (x mod n) H1))
) as [ [y H3] | H3];
destruct (
  qr_dec Zstar finite (exist _ (x mod n) (legendre_spec x H2))
) as [ [z H4] | H4].
reflexivity.
contradict H4.
exists y.
simpl.
apply subset_eq_compat.
injection H3.
clear H3.
intro H3.
rewrite H3.
apply Zmod_mod.
contradict H3.
exists z.
simpl.
apply subset_eq_compat.
injection H4.
clear H4.
intro H4.
rewrite H4.
symmetry.
apply Zmod_mod.
reflexivity.
Qed.

Lemma legendre_mult_Zstar_prime :
  forall x y:Zstar,
  legendre (proj1_sig (x*y)) =
  (legendre (proj1_sig x) * legendre (proj1_sig y))%Z.
Proof.
intros x y.
destruct (qr_dec _ finite x) as [Hx | Hx];
destruct (qr_dec _ finite y) as [Hy | Hy].
cut (QuadraticResidue (x * y)).
intro H.
rewrite <- legendre_plus_qr in Hx.
rewrite <- legendre_plus_qr in Hy.
rewrite <- legendre_plus_qr in H.
rewrite Hx.
rewrite Hy.
rewrite H.
reflexivity.
apply qr_qr_mult_qr.
exact mult_comm.
assumption.
assumption.
cut (~QuadraticResidue (x * y)).
intro H.
rewrite <- legendre_plus_qr in Hx.
rewrite <- legendre_minus_qnr in Hy.
rewrite <- legendre_minus_qnr in H.
rewrite Hx.
rewrite Hy.
rewrite H.
reflexivity.
rewrite mult_comm.
apply qnr_qr_mult_qnr.
exact mult_comm.
assumption.
assumption.
cut (~QuadraticResidue (x * y)).
intro H.
rewrite <- legendre_minus_qnr in Hx.
rewrite <- legendre_plus_qr in Hy.
rewrite <- legendre_minus_qnr in H.
rewrite Hx.
rewrite Hy.
rewrite H.
reflexivity.
apply qnr_qr_mult_qnr.
exact mult_comm.
assumption.
assumption.
cut (QuadraticResidue (x * y)).
intro H.
rewrite <- legendre_minus_qnr in Hx.
rewrite <- legendre_minus_qnr in Hy.
rewrite <- legendre_plus_qr in H.
rewrite Hx.
rewrite Hy.
rewrite H.
reflexivity.
apply qnr_qnr_mult_qr with (g:=generator).
exact finite.
exact is_generator.
rewrite order_Zstar_prime.
rewrite even_Zabs_nat.
apply Zeven_pred.
assumption.
omega.
assumption.
assumption.
Qed.

Lemma Zstar_from_not_divide_spec :
  forall x, ~(n|x) -> 0 <= x mod n < n /\ rel_prime (x mod n) n.
Proof.
intros x H.
split.
apply Z_mod_lt.
omega.
destruct n_prime as [H1 H2].
apply H2.
assert (0 <= x mod n < n).
apply Z_mod_lt.
omega.
assert (x mod n <>0).
contradict H.
apply Zmod_divide.
omega.
assumption.
omega.
Qed.

Definition Zstar_from_not_divide (x:Z)(H:~(n|x)) : Zstar :=
  exist _ (x mod n) (Zstar_from_not_divide_spec _ H).

Lemma legendre_mult_mod :
  forall x y,
  ~(n|x) -> ~(n|y) ->
  legendre ((x*y) mod n) = (legendre (x mod n) * legendre (y mod n))%Z.
Proof.
intros x y Hx Hy.
change (x mod n) with (proj1_sig (Zstar_from_not_divide _ Hx)).
change (y mod n) with (proj1_sig (Zstar_from_not_divide _ Hy)).
rewrite <- legendre_mult_Zstar_prime.
simpl.
f_equal.
apply Zmult_mod.
Qed.

Lemma legendre_mult : forall x y, legendre (x*y) = (legendre x * legendre y)%Z.
Proof.
intros x y.
destruct (Zdivide_dec n x) as [Hx | Hx].
unfold legendre.
destruct (Zdivide_dec n x) as [Hx' | Hx'].
destruct (Zdivide_dec n (x * y)) as [H | H].
reflexivity.
contradict H.
apply Zdivide_mult_l.
assumption.
contradiction.
destruct (Zdivide_dec n y) as [Hy | Hy].
unfold legendre.
destruct (Zdivide_dec n y) as [Hy' | Hy'].
destruct (Zdivide_dec n (x * y)) as [H | H].
ring.
contradict H.
apply Zdivide_mult_r.
assumption.
contradiction.
rewrite <- (legendre_mod (x*y)).
rewrite <- (legendre_mod x).
rewrite <- (legendre_mod y).
apply legendre_mult_mod.
assumption.
assumption.
Qed.

Lemma legendre_formula : forall x, (legendre x) mod n = x^(Zdiv2 (n-1)) mod n.
Proof.
assert (0 < Zdiv2 (n-1)) as Hdiv2.
apply Zdiv2_pos.
assert (n=2 \/ 2<n) as [H | H].
omega.
subst n.
contradiction.
omega.

intro x.
unfold legendre.
destruct (Zdivide_dec n x) as [H1 | H1].

rewrite Zmod_small.
symmetry.
apply Zdivide_mod.
inversion H1 as [q Hn].
subst x.
rewrite Zmult_power.
apply Zdivide_mult_r.
apply Zpower_divide.
assumption.
congruence.
omega.
destruct (qr_dec Zstar finite (exist _ (x mod n) (legendre_spec x H1)))
  as [ [y H2] | H2].

injection H2.
clear H2.
intro H2.
rewrite Zpower_mod.
rewrite <- H2.
rewrite Zmult_mod.
rewrite <- Zpower_mod.
rewrite Zmult_power.
rewrite <- Zpower_exp.
cutrewrite (Zdiv2 (n-1) + Zdiv2 (n-1) = 2 * Zdiv2 (n-1))%Z.
rewrite <- Zeven_div2.
rewrite little_fermat.
reflexivity.
assumption.
destruct y as [y [Hy1 Hy2] ].
simpl.
simpl in H2.
apply rel_prime_mod.
omega.
assumption.
apply Zeven_pred.
assumption.
ring.
omega.
omega.
congruence.
omega.
omega.

destruct (is_generator (exist _ (x mod n) (legendre_spec x H1))) as [m Hm].
rewrite Hm in H2.
rewrite qr_even in H2.
rewrite power_nat_power in Hm.
injection Hm.
clear Hm.
intro Hm.
rewrite Zpower_mod.
rewrite Hm.
clear Hm.
assert (odd m) as Hodd.
generalize (even_or_odd m).
tauto.
clear H2.
apply odd_S2n in Hodd.
destruct Hodd as [p Hp].
subst m.
rewrite power_power_nat.
rewrite power_nat_power.
change (
  -1 mod n =
  ((proj1_sig generator) ^ Z_of_nat (S (double p)) mod n) ^ Zdiv2 (n - 1) mod n
).
rewrite inj_S.
rewrite <- Zpower_mod.
rewrite <- Zpower_mult.
rewrite Zmult_succ_l.
rewrite Zpower_exp.
unfold double.
rewrite inj_plus.
rewrite Zplus_diag_eq_mult_2.
rewrite <- Zmult_assoc.
rewrite <- Zeven_div2.
rewrite Zpower_mult.
rewrite Zmult_mod.
rewrite little_fermat.
rewrite (Zmod_small 1).
rewrite Zmult_1_l.
rewrite Zmod_mod.
assert (
  proj1_sig generator ^ Zdiv2 (n - 1) mod n = 1 mod n \/
  proj1_sig generator ^ Zdiv2 (n - 1) mod n = -1 mod n
) as [H | H].
rewrite <- square_mod_1.
rewrite <- Zpower_mult.
rewrite Zmult_comm.
rewrite <- Zeven_div2.
apply little_fermat.
assumption.
destruct generator.
simpl.
tauto.
apply Zeven_pred.
assumption.
congruence.
discriminate.
assumption.
contradict H.
generalize (order_eq_order' Zstar finite generator is_generator).
rewrite order_Zstar_prime.
unfold order', least, IsLeast.
apply iota_ind.
apply least_exists.
apply neutral_reachable.
exact finite.
exact is_generator.
intros ord [ [H2 H3] H4] H5.
assert (Zabs_nat (Zdiv2 (n-1)) < ord)%nat.
rewrite <- H5.
apply Zabs_nat_lt.
split.
congruence.
assert (Zdiv2 (n-1) <= n-1).
rewrite <- (Zdiv2_double (n-1)) at 2.
apply Zdiv2_le.
omega.
omega.
assert (Zdiv2 (n-1) <> n-1).
rewrite (Zeven_div2 (n-1)) at 2.
omega.
apply Zeven_pred.
assumption.
omega.
generalize (H4 _ H).
intro H6.
contradict H6.
split.
change 0%nat with (Zabs_nat 0).
apply Zabs_nat_lt.
omega.
rewrite power_nat_power.
simpl.
apply subset_eq_compat.
rewrite inj_Zabs_nat.
rewrite Zabs_eq.
rewrite H6.
apply Zmod_small.
omega.
congruence.
congruence.
omega.
assumption.
destruct generator.
simpl.
rewrite <- (Zpower_1_r n).
apply rel_prime_Zpower.
omega.
discriminate.
tauto.
omega.
omega.
apply Zeven_pred.
assumption.
rewrite <- (Zmult_0_l 0).
apply Zmult_ge_compat.
omega.
omega.
discriminate.
discriminate.
omega.
omega.
congruence.
omega.
omega.
exact finite.
exact is_generator.
rewrite order_Zstar_prime.
rewrite even_Zabs_nat.
apply Zeven_pred.
assumption.
omega.
Qed.

Hypothesis n_blum : n mod 4 = 3 mod 4.

Lemma qnr_opp_neutral : ~QuadraticResidue (opp neutral).
Proof.
rewrite <- legendre_plus_qr.
simpl.
intro H.
cut (legendre (-1 mod n) mod n = 1).
clear H.
rewrite legendre_formula.
rewrite <- Zpower_mod.
cut (0<=n).
intro H.
generalize (blum_odd _ H n_blum).
clear H.
intro H.
rewrite Z_opp_one_power_odd.
clear H.
intro H.
cut (n=2).
cut (n>2).
omega.
apply Zodd_prime_gt_2.
assumption.
assumption.
rewrite <- (opp_2 neutral).
unfold opp, neutral.
simpl.
apply subset_eq_compat.
assumption.
cut (1<n-1).
intro H0.
generalize (Zdiv2_pos _ H0).
congruence.
cut (n>2).
omega.
apply Zodd_prime_gt_2.
assumption.
assumption.
assumption.
omega.
omega.
rewrite Zmod_small.
assumption.
rewrite H.
omega.
Qed.

Lemma legendre_opp_1 : legendre (-1) = -1.
Proof.
unfold legendre.
destruct (Zdivide_dec n (-1)) as [H | H].
apply (Zdivide_opp_r_rev n 1) in H.
apply Zdivide_1 in H.
omega.
cutrewrite (exist _ (-1 mod n) (legendre_spec (-1) H) = opp neutral).
destruct (
  qr_dec Zstar finite (opp neutral)
) as [H0 | _].
contradict H0.
apply qnr_opp_neutral.
reflexivity.
apply subset_eq_compat.
reflexivity.
Qed.

Lemma legendre_opp : forall x, legendre (- x) = - legendre x.
Proof.
intro x.
change (-x) with ((-1) * x)%Z.
rewrite legendre_mult.
rewrite legendre_opp_1.
reflexivity.
Qed.

Lemma qr_opp_prime : forall x, QuadraticResidue (opp x) <-> ~QuadraticResidue x.
Proof.
intro x.
rewrite <- legendre_plus_qr.
rewrite <- legendre_minus_qnr.
simpl.
rewrite legendre_mod.
rewrite legendre_opp.
omega.
Qed.

Lemma unique_squareroot_exists_prime :
  forall x, QuadraticResidue x -> exists! y:Zstar, QuadraticResidue y /\ y*y = x.
Proof.
intros x [y Hy1].
destruct (qr_dec Zstar finite y) as [Hy2 | Hy2].
exists y.
split.
tauto.
intros z [Hz2 Hz1].
rewrite <- Hz1 in Hy1.
rewrite (equal_square_prime y z) in Hy1.
destruct Hy1 as [Hy1 | Hy1].
assumption.
subst y.
contradict Hz2.
rewrite <- qr_opp_prime.
assumption.
exists (opp y).
split.
rewrite qr_opp_prime.
rewrite mult_opp.
tauto.
intros z [Hz2 Hz1].
rewrite <- Hz1 in Hy1.
rewrite (equal_square_prime y z) in Hy1.
destruct Hy1 as [Hy1 | Hy1].
subst y.
contradiction.
symmetry.
apply eq_opp.
congruence.
Qed.

End Zstar1.

Section Zstar2.

Variable p q : Z.

Hypothesis distinct : p<>q.

Hypothesis p_prime : prime p.

Hypothesis q_prime : prime q.

Hypothesis p_odd : Zodd p.

Hypothesis q_odd : Zodd q.

Lemma p_gt_1 : 1<p.
Proof.
destruct p_prime as [Hp _].
assumption.
Qed.

Lemma q_gt_1 : 1<q.
Proof.
destruct q_prime as [Hq _].
assumption.
Qed.

Lemma pq_gt_1 : 1 < p*q.
Proof.
destruct p_prime.
destruct q_prime.
assert (p*1 < p*q).
apply Zmult_lt_compat_l.
omega.
assumption.
omega.
Qed.

Lemma rel_primality : rel_prime p q.
Proof.
apply prime_rel_prime.
assumption.
intro H.
apply prime_div_prime in H.
contradiction.
assumption.
assumption.
Qed.

Lemma fst_spec :
  forall x:Zstar (p*q) pq_gt_1,
  0 <= proj1_sig x mod p < p /\ rel_prime (proj1_sig x mod p) p.
Proof.
intros [x [Hx1 Hx2] ].
simpl.
split.
apply Z_mod_lt.
destruct p_prime as [Hp _].
omega.
apply rel_prime_mod.
destruct p_prime as [Hp _].
omega.
apply rel_prime_sym.
apply rel_prime_div with (p:=(p*q)%Z).
apply rel_prime_sym.
assumption.
auto with zarith.
Qed.

Definition fst (x:Zstar (p*q) pq_gt_1) : Zstar p p_gt_1 :=
  exist _ (proj1_sig x mod p) (fst_spec x).

Lemma snd_spec :
  forall x:Zstar (p*q) pq_gt_1,
  0 <= proj1_sig x mod q < q /\ rel_prime (proj1_sig x mod q) q.
Proof.
intros [x [Hx1 Hx2] ].
simpl.
split.
apply Z_mod_lt.
destruct q_prime as [Hq _].
omega.
apply rel_prime_mod.
destruct q_prime as [Hq _].
omega.
apply rel_prime_sym.
apply rel_prime_div with (p:=(p*q)%Z).
apply rel_prime_sym.
assumption.
auto with zarith.
Qed.

Definition snd (x:Zstar (p*q) pq_gt_1) : Zstar q q_gt_1 :=
  exist _ (proj1_sig x mod q) (snd_spec x).

Lemma pair_spec :
  forall (x:Zstar p p_gt_1)(y:Zstar q q_gt_1),
  0 <= proj1_sig (chinese p q rel_primality (proj1_sig x) (proj1_sig y))
    mod (p*q) < p * q /\
  rel_prime
    (proj1_sig (chinese p q rel_primality (proj1_sig x) (proj1_sig y)) mod (p*q))
    (p * q).
Proof.
intros [x [Hx1 Hx2] ] [y [Hy1 Hy2] ].
simpl.
split.
apply Z_mod_lt.
auto with zarith.
apply rel_prime_mod.
apply Zgt_lt.
auto with zarith.
destruct (chinese p q rel_primality x y) as [z [Hz1 Hz2] ].
simpl.
apply rel_prime_mult.
apply rel_prime_mod_rev.
omega.
rewrite Hz1.
apply rel_prime_mod.
omega.
assumption.
apply rel_prime_mod_rev.
omega.
rewrite Hz2.
apply rel_prime_mod.
omega.
assumption.
Qed.

Definition pair (x:Zstar p p_gt_1)(y:Zstar q q_gt_1) : Zstar (p*q) pq_gt_1 :=
  exist _
    (proj1_sig (chinese p q rel_primality (proj1_sig x) (proj1_sig y)) mod (p*q))
    (pair_spec x y).

Lemma pair_inj : forall x1 x2 y1 y2, pair x1 x2 = pair y1 y2 -> x1=y1 /\ x2=y2.
Proof.
intros [x1 [Hx11 Hx12] ] [x2 [Hx21 Hx22] ] [y1 [Hy11 Hy12] ] [y2 [Hy21 Hy22] ] H.
injection H.
clear H.
intro H.
destruct (chinese p q rel_primality x1 x2) as [x [Hx1 Hx2] ].
destruct (chinese p q rel_primality y1 y2) as [y [Hy1 Hy2] ].
simpl in H.
split; simpl; apply subset_eq_compat.
rewrite <- (Zmod_small x1 p).
rewrite <- (Zmod_small y1 p).
rewrite <- Hx1, <-Hy1.
rewrite Zmod_div_mod with (m:=(p*q)%Z).
symmetry.
rewrite Zmod_div_mod with (m:=(p*q)%Z).
congruence.
omega.
rewrite <- (Zmult_0_l 0).
apply Zmult_lt_compat.
omega.
omega.
auto with zarith.
omega.
rewrite <- (Zmult_0_l 0).
apply Zmult_lt_compat.
omega.
omega.
auto with zarith.
assumption.
assumption.
rewrite <- (Zmod_small x2 q).
rewrite <- (Zmod_small y2 q).
rewrite <- Hx2, <-Hy2.
rewrite Zmod_div_mod with (m:=(p*q)%Z).
symmetry.
rewrite Zmod_div_mod with (m:=(p*q)%Z).
congruence.
omega.
rewrite <- (Zmult_0_l 0).
apply Zmult_lt_compat.
omega.
omega.
auto with zarith.
omega.
rewrite <- (Zmult_0_l 0).
apply Zmult_lt_compat.
omega.
omega.
auto with zarith.
assumption.
assumption.
Qed.

Lemma fst_pair : forall (x:Zstar p p_gt_1)(y:Zstar q q_gt_1), fst (pair x y) = x.
Proof.
intros [x [Hx1 Hx2] ] [y [Hy1 Hy2] ].
simpl.
apply subset_eq_compat.
simpl.
destruct (chinese p q rel_primality x y) as [z [Hz1 Hz2] ].
simpl.
rewrite <- Zmod_div_mod.
rewrite Hz1.
apply Zmod_small.
assumption.
omega.
apply Zgt_lt.
auto with zarith.
auto with zarith.
Qed.

Lemma snd_pair : forall (x:Zstar p p_gt_1)(y:Zstar q q_gt_1), snd (pair x y) = y.
Proof.
intros [x [Hx1 Hx2] ] [y [Hy1 Hy2] ].
simpl.
apply subset_eq_compat.
simpl.
destruct (chinese p q rel_primality x y) as [z [Hz1 Hz2] ].
simpl.
rewrite <- Zmod_div_mod.
rewrite Hz2.
apply Zmod_small.
assumption.
omega.
apply Zgt_lt.
auto with zarith.
auto with zarith.
Qed.

Lemma pair_fst_snd : forall x:Zstar (p*q) pq_gt_1, pair (fst x) (snd x) = x.
Proof.
intros [x [Hx1 Hx2] ].
simpl.
apply subset_eq_compat.
simpl.
rewrite <- chinese_unique_modulo with (x:=x).
apply Zmod_small.
assumption.
destruct p_prime as [Hp _].
omega.
destruct q_prime as [Hq _].
omega.
apply Zmod_div_mod.
destruct p_prime as [Hp _].
omega.
destruct p_prime as [Hp _].
omega.
auto with zarith.
apply Zmod_div_mod.
destruct q_prime as [Hq _].
omega.
destruct q_prime as [Hq _].
omega.
auto with zarith.
Qed.

Lemma fst_opp : forall x, fst (opp _ _ x) = opp _ _ (fst x).
Proof.
intros [x [Hx1 Hx2] ].
simpl.
apply subset_eq_compat.
simpl.
rewrite Z_mod_nz_opp_full.
rewrite Zminus_mod.
rewrite <- Zmod_div_mod.
rewrite Zminus_mod.
rewrite Zmult_comm.
rewrite Z_mod_mult.
rewrite Zmod_0_l.
rewrite (Zmod_small (x mod p)).
reflexivity.
apply Z_mod_lt.
destruct p_prime.
omega.
destruct p_prime.
omega.
omega.
auto with zarith.
apply Zrel_prime_neq_mod_0.
change 1 with (1*1)%Z.
apply Zmult_lt_compat.
destruct p_prime.
omega.
destruct q_prime.
omega.
assumption.
Qed.

Lemma snd_opp : forall x, snd (opp _ _ x) = opp _ _ (snd x).
Proof.
intros [x [Hx1 Hx2] ].
simpl.
apply subset_eq_compat.
simpl.
rewrite Z_mod_nz_opp_full.
rewrite Zminus_mod.
rewrite <- Zmod_div_mod.
rewrite Zminus_mod.
rewrite Z_mod_mult.
rewrite Zmod_0_l.
rewrite (Zmod_small (x mod q)).
reflexivity.
apply Z_mod_lt.
destruct q_prime.
omega.
destruct q_prime.
omega.
omega.
auto with zarith.
apply Zrel_prime_neq_mod_0.
change 1 with (1*1)%Z.
apply Zmult_lt_compat.
destruct p_prime.
omega.
destruct q_prime.
omega.
assumption.
Qed.

Lemma opp_pair : forall x y, opp _ _ (pair x y) = pair (opp _ _ x) (opp _ _ y).
Proof.
intros x y.
rewrite <- (fst_pair x y) at 2.
rewrite <- (snd_pair x y) at 3.
rewrite <- fst_opp.
rewrite <- snd_opp.
rewrite pair_fst_snd.
reflexivity.
Qed.

Lemma fst_mult :
  forall x y:Zstar (p*q) pq_gt_1, fst (x * y) = fst x * fst y.
Proof.
intros [x [Hx1 Hx2] ] [y [Hy1 Hy2] ].
simpl.
apply subset_eq_compat.
simpl.
rewrite <- Zmod_div_mod.
apply Zmult_mod.
destruct p_prime.
omega.
omega.
auto with zarith.
Qed.

Lemma snd_mult :
  forall x y:Zstar (p*q) pq_gt_1, snd (x * y) = snd x * snd y.
Proof.
intros [x [Hx1 Hx2] ] [y [Hy1 Hy2] ].
simpl.
apply subset_eq_compat.
simpl.
rewrite <- Zmod_div_mod.
apply Zmult_mod.
destruct q_prime.
omega.
omega.
auto with zarith.
Qed.

Lemma mult_pair :
  forall x1 y1 x2 y2, pair x1 y1 * pair x2 y2 = pair (x1 * x2) (y1 * y2). 
Proof.
intros [x1 [Hx11 Hx12] ] [y1 [Hy11 Hy12] ] [x2 [Hx21 Hx22] ] [y2 [Hy21 Hy22] ].
simpl.
apply subset_eq_compat.
simpl.
apply chinese_unique_modulo.
omega.
omega.

destruct (chinese p q rel_primality x1 y1) as [c1 [Hc11 Hc12] ].
destruct (chinese p q rel_primality x2 y2) as [c2 [Hc21 Hc22] ].
simpl.
rewrite Zmult_mod.
rewrite <- Zmod_div_mod.
rewrite <- Zmod_div_mod.
rewrite Hc11, Hc21.
rewrite <- Zmult_mod.
symmetry.
rewrite Zmod_small.
reflexivity.
apply Z_mod_lt.
omega.
omega.
change 0 with (0 * q)%Z.
apply Zmult_lt_compat_r.
omega.
omega.
auto with zarith.
omega.
change 0 with (0 * q)%Z.
apply Zmult_lt_compat_r.
omega.
omega.
auto with zarith.

destruct (chinese p q rel_primality x1 y1) as [c1 [Hc11 Hc12] ].
destruct (chinese p q rel_primality x2 y2) as [c2 [Hc21 Hc22] ].
simpl.
rewrite Zmult_mod.
rewrite <- Zmod_div_mod.
rewrite <- Zmod_div_mod.
rewrite Hc12, Hc22.
rewrite <- Zmult_mod.
symmetry.
rewrite Zmod_small.
reflexivity.
apply Z_mod_lt.
omega.
omega.
change 0 with (0 * q)%Z.
apply Zmult_lt_compat_r.
omega.
omega.
auto with zarith.
omega.
change 0 with (0 * q)%Z.
apply Zmult_lt_compat_r.
omega.
omega.
auto with zarith.
Qed.

Lemma fst_inv : forall x, fst (/ x) = / fst x.
Proof.
intro x.
apply mult_right_inj with (c:=fst x).
rewrite Group2.inv_left.
rewrite <- fst_mult.
rewrite Group2.inv_left.
simpl.
apply subset_eq_compat.
apply Zmod_small.
destruct p_prime.
omega.
Qed.

Lemma snd_inv : forall x, snd (/ x) = / snd x.
Proof.
intro x.
apply mult_right_inj with (c:=snd x).
rewrite Group2.inv_left.
rewrite <- snd_mult.
rewrite Group2.inv_left.
simpl.
apply subset_eq_compat.
apply Zmod_small.
destruct q_prime.
omega.
Qed.

Lemma neq_opp : forall x:Zstar (p*q) pq_gt_1, opp _ _ x <> x.
Proof.
intro x.
rewrite <- (pair_fst_snd x).
rewrite opp_pair.
intro H.
apply pair_inj in H as [H _].
contradict H.
apply neq_opp_prime.
assumption.
assumption.
Qed.

Lemma legendre_fst :
  forall x:Zstar (p*q) pq_gt_1,
  legendre p p_gt_1 p_prime (proj1_sig (fst x)) =
  legendre p p_gt_1 p_prime (proj1_sig x).
Proof.
intros [x [Hx1 Hx2] ].
simpl.
unfold legendre.
destruct (Zdivide_dec p x) as [H1 | H1];
destruct (Zdivide_dec p (x mod p)) as [H2 | H2].
reflexivity.

contradict H2.
apply Zdivide_mod in H1.
rewrite H1.
auto with zarith.

assert (0 <= x mod p < p) as [H3 H4].
apply Z_mod_lt.
destruct p_prime as [Hp _].
omega.
assert (x mod p = 0 \/ 0 < x mod p) as [H5 | H5].
omega.
apply Zmod_divide in H5.
contradiction.
destruct p_prime as [Hp _].
omega.
apply Zdivide_le in H2.
omega.
destruct p_prime.
omega.
assumption.

match goal with
| |- context [qr_dec _ ?fin ?x] =>
    destruct (qr_dec _ fin x) as [ [y H3] | H3]
end;
match goal with
| |- context [qr_dec _ ?fin ?x] =>
    destruct (qr_dec _ fin x) as [ [y' H4] | H4]
end.
reflexivity.
contradict H4.
exists y.
rewrite H3.
simpl.
apply subset_eq_compat.
apply Zmod_mod.
contradict H3.
exists y'.
rewrite H4.
simpl.
apply subset_eq_compat.
rewrite Zmod_mod.
reflexivity.
reflexivity.
Qed.

Lemma legendre_snd :
  forall x:Zstar (p*q) pq_gt_1,
  legendre q q_gt_1 q_prime (proj1_sig (snd x)) =
  legendre q q_gt_1 q_prime (proj1_sig x).
Proof.
intros [x [Hx1 Hx2] ].
simpl.
unfold legendre.
destruct (Zdivide_dec q x) as [H1 | H1];
destruct (Zdivide_dec q (x mod q)) as [H2 | H2].
reflexivity.

contradict H2.
apply Zdivide_mod in H1.
rewrite H1.
auto with zarith.

assert (0 <= x mod q < q) as [H3 H4].
apply Z_mod_lt.
destruct q_prime as [Hq _].
omega.
assert (x mod q = 0 \/ 0 < x mod q) as [H5 | H5].
omega.
apply Zmod_divide in H5.
contradiction.
destruct q_prime as [Hq _].
omega.
apply Zdivide_le in H2.
omega.
destruct q_prime.
omega.
assumption.

match goal with
| |- context [qr_dec _ ?fin ?x] =>
    destruct (qr_dec _ fin x) as [ [y H3] | H3]
end;
match goal with
| |- context [qr_dec _ ?fin ?x] =>
    destruct (qr_dec _ fin x) as [ [y' H4] | H4]
end.
reflexivity.
contradict H4.
exists y.
rewrite H3.
simpl.
apply subset_eq_compat.
apply Zmod_mod.
contradict H3.
exists y'.
rewrite H4.
simpl.
apply subset_eq_compat.
rewrite Zmod_mod.
reflexivity.
reflexivity.
Qed.

Lemma qr_pair :
  forall (x:Zstar p p_gt_1)(y:Zstar q q_gt_1),
  QuadraticResidue (pair x y) <-> QuadraticResidue x /\ QuadraticResidue y.
Proof.
intros x y.
split.

intros [z Hz].
split.

exists (fst z).
destruct x as [x [Hx1 Hx2] ].
destruct z as [z [Hz1 Hz2] ].
simpl in *.
apply subset_eq_compat.
simpl.
injection Hz.
clear Hz.
intro Hz.
rewrite <- Zmult_mod.
rewrite Zmod_div_mod with (m:=(p*q)%Z).
rewrite Hz.
clear Hz.
destruct (chinese p q rel_primality x (proj1_sig y)) as [w [Hw1 Hw2] ].
simpl.
rewrite <- Zmod_div_mod.
rewrite Hw1.
apply Zmod_small.
assumption.
omega.
omega.
auto with zarith.
omega.
omega.
auto with zarith.

exists (snd z).
destruct y as [y [Hy1 Hy2] ].
destruct z as [z [Hz1 Hz2] ].
simpl in *.
apply subset_eq_compat.
simpl.
injection Hz.
clear Hz.
intro Hz.
rewrite <- Zmult_mod.
rewrite Zmod_div_mod with (m:=(p*q)%Z).
rewrite Hz.
clear Hz.
destruct (chinese p q rel_primality (proj1_sig x) y) as [w [Hw1 Hw2] ].
simpl.
rewrite <- Zmod_div_mod.
rewrite Hw2.
apply Zmod_small.
assumption.
omega.
omega.
auto with zarith.
omega.
omega.
auto with zarith.

intros [ [x' Hx] [y' Hy] ].
exists (pair x' y').
subst x y.
simpl.
apply subset_eq_compat.
simpl.
destruct x' as [x [Hx1 Hx2] ].
destruct y' as [y [Hy1 Hy2] ].
simpl.
destruct (chinese p q rel_primality x y) as [z [Hz1 Hz2] ].
simpl.
apply chinese_unique_modulo.
omega.
omega.
rewrite Zmod_div_mod with (m:=(p*q)%Z).
rewrite <- Zmult_mod.
rewrite <- Zmod_div_mod.
rewrite Zmod_mod.
rewrite Zmult_mod.
rewrite Hz1.
symmetry.
apply Zmult_mod.
omega.
apply Zgt_lt.
auto with zarith.
auto with zarith.
omega.
apply Zgt_lt.
auto with zarith.
auto with zarith.
rewrite Zmod_div_mod with (m:=(p*q)%Z).
rewrite <- Zmult_mod.
rewrite <- Zmod_div_mod.
rewrite Zmod_mod.
rewrite Zmult_mod.
rewrite Hz2.
symmetry.
apply Zmult_mod.
omega.
apply Zgt_lt.
auto with zarith.
auto with zarith.
omega.
apply Zgt_lt.
auto with zarith.
auto with zarith.
Qed.

Lemma qr_prod_Permutation :
  Permutation
    (qr_list (Zstar (p*q) pq_gt_1) (finite _ _))
    (List.map (fun x => pair (Datatypes.fst x) (Datatypes.snd x))
      (list_prod
        (qr_list (Zstar p p_gt_1) (finite _ _))
        (qr_list (Zstar q q_gt_1) (finite _ _)))).
Proof.
apply NoDup_Permutation.
apply NoDup_qr_list.
apply NoDup_map.
intros [x1 x2] [y1 y2].
do 2 rewrite in_prod_iff.
simpl.
intros [Hx1 Hx2] [Hy1 Hy2] H.
assert (x1 = y1).
rewrite <- fst_pair with (x:=x1)(y:=x2).
rewrite <- fst_pair with (x:=y1)(y:=y2).
congruence.
assert (x2 = y2).
rewrite <- snd_pair with (x:=x1)(y:=x2).
rewrite <- snd_pair with (x:=y1)(y:=y2).
congruence.
congruence.
apply NoDup_list_prod.
apply NoDup_qr_list.
apply NoDup_qr_list.
intro x.
rewrite qr_list_spec.
rewrite in_map_iff.
rewrite <- pair_fst_snd with x.
rewrite qr_pair.
split.
exists (fst x, snd x).
simpl.
split.
reflexivity.
rewrite in_prod_iff.
rewrite (qr_list_spec (Zstar p p_gt_1)).
rewrite (qr_list_spec (Zstar q q_gt_1)).
assumption.
intros [ [x1 x2] [H1 H2] ].
simpl in H1.
rewrite pair_fst_snd in H1.
subst x.
rewrite in_prod_iff in H2.
rewrite (qr_list_spec (Zstar p p_gt_1)) in H2.
rewrite (qr_list_spec (Zstar q q_gt_1)) in H2.
rewrite fst_pair.
rewrite snd_pair.
assumption.
Qed.

Lemma Zstar_list_Permutation :
  Permutation
    (Zstar_list (p*q) pq_gt_1)
    (List.map (fun x => pair (Datatypes.fst x) (Datatypes.snd x))
      (list_prod
        (Zstar_list p p_gt_1)
        (Zstar_list q q_gt_1))).
Proof.
apply NoDup_Permutation.
apply NoDup_Zstar_list.
apply NoDup_map.
intros [x1 x2] [y1 y2].
do 2 rewrite in_prod_iff.
simpl.
intros [Hx1 Hx2] [Hy1 Hy2] H.
assert (x1 = y1).
rewrite <- fst_pair with (x:=x1)(y:=x2).
rewrite <- fst_pair with (x:=y1)(y:=y2).
congruence.
assert (x2 = y2).
rewrite <- snd_pair with (x:=x1)(y:=x2).
rewrite <- snd_pair with (x:=y1)(y:=y2).
congruence.
congruence.
apply NoDup_list_prod.
apply NoDup_Zstar_list.
apply NoDup_Zstar_list.
intro x.
split.
intro H.
rewrite in_map_iff.
rewrite <- pair_fst_snd with x.
exists (fst x, snd x).
simpl.
split.
reflexivity.
rewrite in_prod_iff.
split.
apply (@Zstar_list_spec p p_gt_1 (fst x)).
apply (@Zstar_list_spec q q_gt_1 (snd x)).
intro H.
apply (@Zstar_list_spec (p*q) pq_gt_1 x).
Qed.

Lemma length_Zstar_list :
  length (Zstar_list (p*q) pq_gt_1) =
  (length (Zstar_list p p_gt_1) *
   length (Zstar_list q q_gt_1))%nat.
Proof.
rewrite (Permutation_length Zstar_list_Permutation).
rewrite map_length.
apply prod_length.
Qed.

Lemma length_qr_list :
  length (qr_list (Zstar (p*q) pq_gt_1) (finite _ _)) =
  (length (qr_list (Zstar p p_gt_1) (finite _ _)) *
   length (qr_list (Zstar q q_gt_1) (finite _ _)))%nat.
Proof.
rewrite (Permutation_length qr_prod_Permutation).
rewrite map_length.
apply prod_length.
Qed.

Definition jacobi (x:Z) : Z :=
  (legendre p p_gt_1 p_prime x * legendre q q_gt_1 q_prime x)%Z.

Lemma jacobi_1 : jacobi 1 = 1.
Proof.
unfold jacobi.
rewrite legendre_1.
rewrite legendre_1.
reflexivity.
Qed.

Lemma jacobi_mod : forall x, jacobi (x mod (p*q)) = jacobi x.
Proof.
intro x.
unfold jacobi.
rewrite <- (legendre_mod p).
rewrite <- (legendre_mod q).
rewrite <- Zmod_div_mod.
rewrite <- Zmod_div_mod.
rewrite legendre_mod.
rewrite legendre_mod.
reflexivity.
destruct q_prime.
omega.
rewrite <- (Zmult_0_l 0).
apply Zmult_lt_compat.
destruct p_prime.
omega.
destruct q_prime.
omega.
auto with zarith.
destruct p_prime.
omega.
rewrite <- (Zmult_0_l 0).
apply Zmult_lt_compat.
destruct p_prime.
omega.
destruct q_prime.
omega.
auto with zarith.
Qed.

Lemma qr_jacobi_plus_qr :
  forall x,
  QuadraticResidue (fst x) -> jacobi (proj1_sig x) = 1 ->
  QuadraticResidue (snd x).
Proof.
intros x Hqr Hjac.
unfold jacobi in Hjac.
rewrite <- legendre_plus_qr in Hqr.
rewrite legendre_fst in Hqr.
rewrite Hqr in Hjac.
rewrite Zmult_1_l in Hjac.
rewrite <- legendre_plus_qr.
rewrite legendre_snd.
assumption.
Qed.

Lemma jacobi_plus :
  forall x : Zstar (p*q) pq_gt_1,
  jacobi (proj1_sig x) = 1 <->
  ( QuadraticResidue (fst x) /\  QuadraticResidue (snd x)) \/
  (~QuadraticResidue (fst x) /\ ~QuadraticResidue (snd x)).
Proof.
intro x.
unfold jacobi.
rewrite <- (legendre_plus_qr _ _ p_prime).
rewrite <- (legendre_plus_qr _ _ q_prime).
rewrite legendre_fst.
rewrite legendre_snd.
split.
intro H.
generalize H.
intro H'.
apply Zmult_1_inversion_l in H'.
destruct H' as [H' | H']; rewrite H' in *; omega.
intros [ [H1 H2] | [H1 H2] ].
rewrite H1.
omega.
rewrite <- legendre_fst in H1.
rewrite <- legendre_snd in H2.
rewrite legendre_plus_qr in H1, H2.
rewrite <- (legendre_minus_qnr _ _ p_prime) in H1.
rewrite <- (legendre_minus_qnr _ _ q_prime) in H2.
rewrite legendre_fst in H1.
rewrite legendre_snd in H2.
rewrite H1.
omega.
Qed.

Lemma qnr_plus_qr_mult_qnr_plus :
  forall x y : Zstar (p*q) pq_gt_1,
  ~QuadraticResidue x -> jacobi (proj1_sig x) = 1 ->
  QuadraticResidue y ->
  ~QuadraticResidue (x*y) /\ jacobi (proj1_sig (x*y)) = 1.
Proof.
intros x y.
do 2 rewrite jacobi_plus.
pattern x at 1 6.
rewrite <- (pair_fst_snd x).
pattern y at 1 2.
rewrite <- (pair_fst_snd y).
rewrite mult_pair.
do 3 rewrite qr_pair.
intros H1 [ [H2 H3] | [H2 H3] ] [H4 H5].
tauto.
rewrite fst_mult, snd_mult.
split.
intros [H6 H7].
contradict H6.
apply qnr_qr_mult_qnr.
simpl.
apply mult_comm.
assumption.
assumption.
right.
split.
apply qnr_qr_mult_qnr.
simpl.
apply mult_comm.
assumption.
assumption.
apply qnr_qr_mult_qnr.
simpl.
apply mult_comm.
assumption.
assumption.
Qed.

Lemma qnr_plus_qnr_plus_mult_qr :
  forall x y : Zstar (p*q) pq_gt_1,
  ~QuadraticResidue x -> jacobi (proj1_sig x) = 1 ->
  ~QuadraticResidue y -> jacobi (proj1_sig y) = 1 ->
  QuadraticResidue (x * y).
Proof.
intros x y.
do 2 rewrite jacobi_plus.
pattern x at 1 6.
rewrite <- (pair_fst_snd x).
pattern y at 1 6.
rewrite <- (pair_fst_snd y).
do 2 rewrite qr_pair.
intros H1 [ [H2 H3] | [H2 H3] ] H4 [ [H5 H6] | [H5 H6] ].
tauto.
tauto.
tauto.
rewrite mult_pair.
rewrite qr_pair.
split.

apply qnr_qnr_mult_qr with (g:=generator p p_gt_1 p_prime).
apply finite.
apply is_generator.
rewrite order_Zstar_prime.
rewrite even_Zabs_nat.
apply Zeven_pred.
assumption.
destruct p_prime.
omega.
assumption.
assumption.
assumption.

apply qnr_qnr_mult_qr with (g:=generator q q_gt_1 q_prime).
apply finite.
apply is_generator.
rewrite order_Zstar_prime.
rewrite even_Zabs_nat.
apply Zeven_pred.
assumption.
destruct q_prime.
omega.
assumption.
assumption.
assumption.
Qed.

Fixpoint jacobi_plus_list_gen (l:list (Zstar (p*q) pq_gt_1)) :
  list (Zstar (p*q) pq_gt_1) :=
  match l with
  | nil => nil
  | x :: l' =>
      if Z_eq_dec (jacobi (proj1_sig x)) 1 then
        x :: jacobi_plus_list_gen l'
      else
        jacobi_plus_list_gen l'
  end.

Definition jacobi_plus_list : list (Zstar (p*q) pq_gt_1) :=
  jacobi_plus_list_gen (Zstar_list (p*q) pq_gt_1).

Lemma jacobi_plus_list_gen_incl : forall l, incl (jacobi_plus_list_gen l) l.
Proof.
induction l as [ | y l IHl]; simpl.
congruence.
destruct (Z_eq_dec (jacobi (proj1_sig y)) 1) as [H | H].
auto with *.
auto with *.
Qed.

Lemma NoDup_jacobi_plus_list_gen :
  forall l, NoDup l -> NoDup (jacobi_plus_list_gen l).
Proof.
induction l as [ | x l IHl].
constructor.
simpl.
intro H.
cut (~In x l /\ NoDup l).
clear H.
intros [H1 H2].
destruct (Z_eq_dec (jacobi (proj1_sig x)) 1) as [H | H].
apply NoDup_cons.
contradict H1.
apply jacobi_plus_list_gen_incl.
assumption.
tauto.
tauto.
inversion H.
tauto.
Qed.

Lemma NoDup_jacobi_plus_list : NoDup jacobi_plus_list.
Proof.
apply NoDup_jacobi_plus_list_gen.
apply NoDup_Zstar_list.
Qed.

Lemma jacobi_plus_list_gen_spec :
  forall x l,
  In x (jacobi_plus_list_gen l) <-> In x l /\ jacobi (proj1_sig x) = 1.
Proof.
intro x.
induction l as [ | y l IH]; simpl.
tauto.
destruct (Z_eq_dec (jacobi (proj1_sig y)) 1) as [H | H].
simpl.
split.
intros [H0 | H0].
split.
tauto.
congruence.
tauto.
tauto.
split.
tauto.
intros [ [H1 | H1] H2].
congruence.
tauto.
Qed.

Lemma jacobi_plus_list_spec :
  forall x, In x jacobi_plus_list <-> jacobi (proj1_sig x) = 1.
Proof.
intro x.
unfold jacobi_plus_list.
rewrite jacobi_plus_list_gen_spec.
split.
tauto.
split.
apply Zstar_list_spec.
assumption.
Qed.

Lemma jacobi_plus_list_ne : jacobi_plus_list <> nil.
Proof.
assert (In (neutral (p*q) pq_gt_1) jacobi_plus_list).

rewrite jacobi_plus_list_spec.
apply jacobi_1.

destruct jacobi_plus_list.
contradiction.
congruence.
Qed.

Definition jacobi_plus_listNE : listNE (Zstar (p*q) pq_gt_1) :=
  exist _ jacobi_plus_list jacobi_plus_list_ne.

Definition qnr_plus_list : list (Zstar (p*q) pq_gt_1) :=
  qnr_list_gen _ (finite _ _) jacobi_plus_list.

Lemma NoDup_qnr_plus_list : NoDup qnr_plus_list.
Proof.
apply NoDup_qnr_list_gen.
apply NoDup_jacobi_plus_list.
Qed.

Lemma qnr_plus_list_spec :
  forall x,
  In x qnr_plus_list <-> ~QuadraticResidue x /\ jacobi (proj1_sig x) = 1.
Proof.
intro x.
unfold qnr_plus_list.
rewrite qnr_list_gen_spec.
rewrite jacobi_plus_list_spec.
reflexivity.
Qed.

Lemma qnr_plus_permutation :
  Permutation
    qnr_plus_list
    (List.map
      (fun x => pair (Datatypes.fst x) (Datatypes.snd x))
      (list_prod
        (qnr_list (Zstar p p_gt_1) (finite _ _))
        (qnr_list (Zstar q q_gt_1) (finite _ _)))).
Proof.
apply NoDup_Permutation.
apply NoDup_qnr_plus_list.
apply NoDup_map.
intros [x1 x2] [y1 y2].
do 2 rewrite in_prod_iff.
simpl.
intros [Hx1 Hx2] [Hy1 Hy2] H.
assert (x1 = y1).
rewrite <- fst_pair with (x:=x1)(y:=x2).
rewrite <- fst_pair with (x:=y1)(y:=y2).
congruence.
assert (x2 = y2).
rewrite <- snd_pair with (x:=x1)(y:=x2).
rewrite <- snd_pair with (x:=y1)(y:=y2).
congruence.
congruence.
apply NoDup_list_prod; apply NoDup_qnr_list.
intro x.
rewrite qnr_plus_list_spec.
rewrite in_map_iff.
rewrite jacobi_plus.
split.
intros [H1 [ [H2 H3] | [H2 H3] ] ].
rewrite <- pair_fst_snd with (x:=x) in H1.
rewrite qr_pair in H1.
tauto.
exists (fst x, snd x).
split.
apply pair_fst_snd.
rewrite in_prod_iff.
do 2 rewrite qnr_list_spec.
tauto.
intros [ [y1 y2] [H1 H2] ].
simpl in H1.
rewrite in_prod_iff in H2.
do 2 rewrite qnr_list_spec in H2.
subst x.
split.
rewrite qr_pair.
tauto.
rewrite fst_pair, snd_pair.
tauto.
Qed.

Lemma length_qnr_plus_list :
  length qnr_plus_list =
  (length (qnr_list (Zstar p p_gt_1) (finite _ _)) *
   length (qnr_list (Zstar q q_gt_1) (finite _ _)))%nat.
Proof.
rewrite (Permutation_length qnr_plus_permutation).
rewrite map_length.
apply prod_length.
Qed.

Lemma length_qr_qnr_plus :
  length (qr_list (Zstar (p*q) pq_gt_1) (finite _ _)) =
  length qnr_plus_list.
Proof.
rewrite length_qr_list.
rewrite length_qnr_plus_list.
rewrite length_qr_qnr_list with (g:=generator p p_gt_1 p_prime).
rewrite length_qr_qnr_list with (g:=generator q q_gt_1 q_prime).
reflexivity.
apply is_generator.
rewrite order_Zstar_prime.
rewrite even_Zabs_nat.
apply Zeven_pred.
assumption.
destruct q_prime.
omega.
assumption.
apply is_generator.
rewrite order_Zstar_prime.
rewrite even_Zabs_nat.
apply Zeven_pred.
assumption.
destruct p_prime.
omega.
assumption.
Qed.

Lemma qnr_plus_list_ne : qnr_plus_list <> nil.
Proof.
generalize (qr_list_ne (Zstar (p*q) pq_gt_1) (finite _ _)), length_qr_qnr_plus.
intros H1 H2.
destruct qr_list as [ | x qrl].
tauto.
destruct qnr_plus_list as [ | y qnrpl].
discriminate.
discriminate.
Qed.

Definition qnr_plus_listNE : listNE (Zstar (p*q) pq_gt_1) :=
  exist _ qnr_plus_list qnr_plus_list_ne.

Lemma Permutation_qr_square_Zstar :
  Permutation
    (qr_list (Zstar (p*q) pq_gt_1) (finite _ _) ++
     qr_list (Zstar (p*q) pq_gt_1) (finite _ _) ++
     qr_list (Zstar (p*q) pq_gt_1) (finite _ _) ++
     qr_list (Zstar (p*q) pq_gt_1) (finite _ _))
    (List.map (fun x => x*x) (Zstar_list (p*q) pq_gt_1)).
Proof.
remember
  (nodup _ (eq_dec (p*q)) (List.map (fun x => x*x) (Zstar_list (p*q) pq_gt_1)))
  as l.
apply Permutation_trans with (l++l++l++l).
assert (
  Permutation (qr_list (Zstar (p * q) pq_gt_1) (finite (p * q) pq_gt_1)) l
).
subst l.
apply NoDup_Permutation.
apply NoDup_qr_list.
apply NoDup_nodup.
intro x.
rewrite qr_list_spec.
rewrite In_nodup.
rewrite in_map_iff.
split.

intros [y Hx].
subst x.
destruct (In_dec (eq_dec (p*q)) y (Zstar_list (p * q) pq_gt_1)) as [H | H].
exists y.
tauto.
contradict H.
apply (Zstar_list_spec (p*q) pq_gt_1).

intros (y & H & _).
exists y.
assumption.

rewrite <- app_ass.
rewrite <- (app_ass l).
apply Permutation_app;
apply Permutation_app;
assumption.

subst l.
apply Splitable4_nodup.
apply NoDup_Splitable4_map.
apply NoDup_Zstar_list.
intro y.
rewrite in_map_iff.
intros (x & H1 & _).
exists (opp _ _ x).
exists (pair (opp _ _ (fst x)) (snd x)).
exists (pair (fst x) (opp _ _ (snd x))).
exists x.
split.
apply Zstar_list_spec.
split.
apply Zstar_list_spec.
split.
rewrite <- (pair_fst_snd x) at 1.
rewrite opp_pair.
intro H.
apply pair_inj in H as [_ H3].
revert H3.
apply neq_opp_prime.
assumption.
assumption.
split.
rewrite <- (pair_fst_snd x) at 1.
rewrite opp_pair.
intro H.
apply pair_inj in H as [H3 _].
revert H3.
apply neq_opp_prime.
assumption.
assumption.
split.
apply neq_opp.
split.
intro H.
apply pair_inj in H as [H3 _].
revert H3.
apply neq_opp_prime.
assumption.
assumption.
split.
rewrite <- (pair_fst_snd x) at 3.
intro H.
apply pair_inj in H as [H3 _].
revert H3.
apply neq_opp_prime.
assumption.
assumption.
split.
rewrite <- (pair_fst_snd x) at 3.
intro H.
apply pair_inj in H as [_ H3].
revert H3.
apply neq_opp_prime.
assumption.
assumption.
split.
rewrite mult_opp.
congruence.
split.
rewrite <- H1.
rewrite <- (pair_fst_snd x) at 1 2.
do 2 rewrite mult_pair.
rewrite mult_opp.
reflexivity.
split.
rewrite mult_pair.
rewrite mult_opp.
rewrite <- mult_pair.
rewrite pair_fst_snd.
congruence.
split.
congruence.
intros x' _ Hx'.
subst y.
rewrite <- (pair_fst_snd x) in Hx'.
rewrite <- (pair_fst_snd x') in Hx'.
do 2 rewrite mult_pair in Hx'.
apply pair_inj in Hx' as [Hx'1 Hx'2].
rewrite equal_square_prime in Hx'1, Hx'2.
destruct Hx'1 as [Hx'1 | Hx'1]; destruct Hx'2 as [Hx'2 | Hx'2];
rewrite <- (pair_fst_snd x) at 1 6; rewrite <- (pair_fst_snd x');
rewrite Hx'1, Hx'2.
tauto.
rewrite opp_opp.
tauto.
rewrite opp_opp.
tauto.
rewrite opp_pair.
do 2 rewrite opp_opp.
tauto.
assumption.
assumption.
Qed.

Lemma Permutation_qnr_plus_mult_qr :
  forall y:Zstar (p*q) pq_gt_1,
  ~QuadraticResidue y -> jacobi (proj1_sig y) = 1 ->
  Permutation
    qnr_plus_list
    (List.map (fun x => y*x) (qr_list (Zstar (p*q) pq_gt_1) (finite _ _))).
Proof.
intros y Hy1 Hy2.
apply NoDup_Permutation.
apply NoDup_qnr_plus_list.
apply NoDup_map.
intros x1 x2 Hx1 Hx2 H.
apply mult_left_inj with (c:=y).
assumption.
apply NoDup_qr_list.
intro x.
rewrite qnr_plus_list_spec.
rewrite in_map_iff.
split.

intros [H1 H2].
exists (/ y * x).
rewrite qr_list_spec.
split.
rewrite Group2.associative.
rewrite Group2.inv_right.
apply Group2.neutral_left.
apply qnr_plus_qnr_plus_mult_qr.
rewrite qr_inv.
rewrite inv_inv.
assumption.
rewrite jacobi_plus in Hy2 |- *.
rewrite fst_inv, snd_inv.
do 2 rewrite <- qr_inv.
assumption.
assumption.
assumption.

intros [z [Hz1 Hz2] ].
rewrite qr_list_spec in Hz2.
subst x.
apply qnr_plus_qr_mult_qnr_plus.
assumption.
assumption.
assumption.
Qed.

Lemma Permutation_jacobi_plus_qr_qnr_plus :
  Permutation
    jacobi_plus_list
    (qr_list _ (finite _ _) ++ qnr_plus_list).
Proof.
apply NoDup_Permutation.
apply NoDup_jacobi_plus_list.
apply NoDup_app.
apply NoDup_qr_list.
apply NoDup_qnr_plus_list.
intro x.
rewrite qr_list_spec, qnr_plus_list_spec.
tauto.
intro x.
rewrite qr_list_spec, qnr_plus_list_spec.
tauto.
intro x.
rewrite jacobi_plus_list_spec, in_app, qr_list_spec, qnr_plus_list_spec.
pattern x at 2 3.
rewrite <- (pair_fst_snd x).
rewrite qr_pair.
rewrite jacobi_plus.
tauto.
Qed.

Hypothesis p_blum : p mod 4 = 3 mod 4.

Hypothesis q_blum : q mod 4 = 3 mod 4.

Lemma qr_opp :
  forall x:Zstar (p*q) pq_gt_1,
  QuadraticResidue (opp _ _ x) <->
  ~QuadraticResidue x /\ jacobi (proj1_sig x) = 1.
Proof.
intro x.
rewrite <- (pair_fst_snd (opp _ _ x)), qr_pair, fst_opp, snd_opp.
rewrite qr_opp_prime.
rewrite qr_opp_prime.
rewrite jacobi_plus.
pattern x at 3.
rewrite <- (pair_fst_snd x), qr_pair.
tauto.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
Qed.

Lemma jacobi_opp : forall x, jacobi (-x) = jacobi x.
Proof.
intro x.
unfold jacobi.
rewrite legendre_opp.
rewrite legendre_opp.
ring.
assumption.
assumption.
assumption.
assumption.
Qed.

Lemma equal_square :
  forall x y:Zstar (p*q) pq_gt_1,
  jacobi (proj1_sig x) = 1 -> jacobi (proj1_sig y) = 1 ->
  (x * x = y * y <-> x = y \/ x = opp _ _ y).
Proof.
intros x y Hx Hy.
rewrite jacobi_plus in Hx, Hy.
rewrite <- (pair_fst_snd x), <- (pair_fst_snd y).
do 2 rewrite mult_pair.
rewrite opp_pair.
split.

intro H.
apply pair_inj in H as [H1 H2].
rewrite equal_square_prime in H1, H2.
destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
left.
congruence.

rewrite H1, H2 in Hx.
rewrite qr_opp_prime in Hx.
tauto.
assumption.
assumption.
assumption.

rewrite H1, H2 in Hx.
rewrite qr_opp_prime in Hx.
tauto.
assumption.
assumption.
assumption.

right.
congruence.
assumption.
assumption.

do 2 rewrite <- mult_pair.
intros [H | H].
congruence.
apply pair_inj in H as [H1 H2].
rewrite H1, H2.
rewrite <- opp_pair.
apply mult_opp.
Qed.

Lemma qr_equal_square :
  forall x y:Zstar (p*q) pq_gt_1,
  QuadraticResidue x -> QuadraticResidue y -> x * x = y * y -> x = y.
Proof.
intros x y Hx Hy H.
rewrite equal_square in H.
destruct H as [H | H].
assumption.
rewrite H in Hx.
rewrite qr_opp in Hx.
tauto.
rewrite jacobi_plus.
left.
rewrite <- (pair_fst_snd x), qr_pair in Hx.
assumption.
rewrite jacobi_plus.
left.
rewrite <- (pair_fst_snd y), qr_pair in Hy.
assumption.
Qed.

Lemma unique_squareroot_exists :
  forall x,
  QuadraticResidue x ->
  exists! y:Zstar (p*q) pq_gt_1, QuadraticResidue y /\ y*y = x.
Proof.
intros x Hx.
rewrite <- pair_fst_snd in Hx.
rewrite qr_pair in Hx.
destruct Hx as [Hx1 Hx2].
destruct (
  unique_squareroot_exists_prime p p_gt_1 p_prime p_odd p_blum (fst x) Hx1
) as [y1 [ [Hy11 Hy12] Hy13] ].
destruct (
  unique_squareroot_exists_prime q q_gt_1 q_prime q_odd q_blum (snd x) Hx2
) as [y2 [ [Hy21 Hy22] Hy23] ].
exists (pair y1 y2).
split.
split.
rewrite qr_pair.
tauto.
rewrite mult_pair.
rewrite Hy12, Hy22.
apply pair_fst_snd.
intros y [Hy1 Hy2].
rewrite <- (pair_fst_snd y) in Hy1 |- *.
rewrite qr_pair in Hy1.
f_equal.
apply Hy13.
split.
tauto.
rewrite <- fst_mult.
congruence.
apply Hy23.
split.
tauto.
rewrite <- snd_mult.
congruence.
Qed.

Definition squareroot (x:Zstar (p*q) pq_gt_1) : Zstar (p*q) pq_gt_1 :=
  iota
    (inhabits (neutral (p*q) pq_gt_1))
    (fun y:Zstar (p*q) pq_gt_1 => QuadraticResidue y  /\  y*y = x).

Lemma QuadraticResidue_squareroot :
  forall x, QuadraticResidue x -> QuadraticResidue (squareroot x).
Proof.
intros x Hx.
unfold squareroot.
apply iota_ind.
apply unique_squareroot_exists.
assumption.
tauto.
Qed.

Theorem squareroot_square :
  forall x, QuadraticResidue x -> squareroot (x * x) = x.
Proof.
intros x [y Hx].
unfold squareroot.
apply iota_ind.
apply unique_squareroot_exists.
exists x.
reflexivity.
intros z [Hz1 Hz2].
apply qr_equal_square.
assumption.
exists y.
assumption.
assumption.
Qed.

Lemma square_squareroot :
  forall x, QuadraticResidue x -> squareroot x * squareroot x = x.
Proof.
intros x Hx.
unfold squareroot.
apply iota_ind.
apply unique_squareroot_exists.
assumption.
tauto.
Qed.

Lemma opp_squareroot_square :
  forall x:Zstar _ _,
  ~QuadraticResidue x ->
  jacobi (proj1_sig x) = 1 -> opp _ _ (squareroot (x*x)) = x.
Proof.
intros x H1 H2.
symmetry.
apply eq_opp.
rewrite <- mult_opp.
symmetry.
apply squareroot_square.
rewrite qr_opp.
tauto.
Qed.

Lemma qr_Permutation :
  Permutation
    (qr_list (Zstar (p * q) pq_gt_1) (finite (p * q) pq_gt_1))
    (List.map
      (fun x => x * x)
      (qr_list (Zstar (p * q) pq_gt_1) (finite (p * q) pq_gt_1))).
Proof.
apply NoDup_Permutation.
apply NoDup_qr_list.
apply NoDup_map.
intros x y Hx Hy H.
apply qr_equal_square.
rewrite <- qr_list_spec.
eassumption.
rewrite <- qr_list_spec.
eassumption.
assumption.
apply NoDup_qr_list.
intro x.
rewrite in_map_iff.
rewrite qr_list_spec.
split.

intro Hx.
exists (squareroot x).
split.
apply square_squareroot.
assumption.
rewrite qr_list_spec.
apply QuadraticResidue_squareroot.
assumption.

intros [y [H1 H2] ].
exists y.
assumption.
Qed.

Lemma Permutation_qr_square_jacobi_plus :
  Permutation
    (qr_list (Zstar (p*q) pq_gt_1) (finite _ _) ++
     qr_list (Zstar (p*q) pq_gt_1) (finite _ _))
    (List.map (fun x => x*x) jacobi_plus_list).
Proof.
remember (nodup _ (eq_dec (p*q)) (List.map (fun x => x*x) jacobi_plus_list)) as l.
apply Permutation_trans with (l++l).
assert (
  Permutation (qr_list (Zstar (p * q) pq_gt_1) (finite (p * q) pq_gt_1)) l
).
subst l.
apply NoDup_Permutation.
apply NoDup_qr_list.
apply NoDup_nodup.
intro x.
rewrite qr_list_spec.
rewrite In_nodup.
rewrite in_map_iff.
split.

intros [y Hx].
subst x.
destruct (In_dec (eq_dec (p*q)) y jacobi_plus_list) as [H | H].
exists y.
tauto.
rewrite <- (pair_fst_snd y).
exists (pair (fst y) (opp _ _ (snd y))).
split.
do 2 rewrite mult_pair.
f_equal.
apply mult_opp.
rewrite jacobi_plus_list_spec, jacobi_plus in H |- *.
rewrite fst_pair, snd_pair, qr_opp_prime.
apply not_or_and in H.
destruct H as [H1 H2].
apply not_and_or in H1.
apply not_and_or in H2.
apply NNPP.
tauto.
assumption.
assumption.
assumption.

intros (y & H & _).
exists y.
assumption.

apply Permutation_app.
assumption.
assumption.
subst l.

apply Splitable_nodup.
apply NoDup_Splitable_map.
apply NoDup_jacobi_plus_list.
intro y.
rewrite in_map_iff.
intros (x & H1 & H2).
exists (opp _ _ x).
exists x.
split.
rewrite jacobi_plus_list_spec.
simpl.
rewrite jacobi_mod.
rewrite jacobi_opp.
rewrite jacobi_plus_list_spec in H2.
assumption.
split.
assumption.
split.
apply neq_opp.
split.
rewrite mult_opp.
congruence.
split.
congruence.
intros x' H3 Hx'.
subst y.
rewrite jacobi_plus_list_spec in H2, H3.
rewrite equal_square in Hx'.
destruct Hx' as [Hx' | Hx'].
auto.
left.
apply eq_opp.
congruence.
assumption.
assumption.
Qed.

Lemma parity_squareroot_square :
  forall x:Zstar _ _, jacobi (proj1_sig x) = 1 -> (
    QuadraticResidue x <->
    parity _ _ x = parity _ _ (squareroot (x * x))
  ).
Proof.
intros x Hx.
split; intro H.
rewrite squareroot_square.
reflexivity.
assumption.
apply NNPP.
contradict H.
cut (opp _ _ (squareroot (x*x)) = x).
intro H1.
rewrite <- H1 at 1.
apply parity_opp.
apply Zodd_mult_Zodd; assumption.
apply opp_squareroot_square.
assumption.
assumption.
Qed.

End Zstar2.

