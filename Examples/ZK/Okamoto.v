(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * Okamoto.v : Okamoto protocol *)

Require Import SigmaPhi.
Require Import FilterMap.
Require Import LtIrrelevance.
Require Import Schnorr.

Set Implicit Arguments.


Module Type OKAMOTO_PARAMETERS.

 Open Scope Z_scope.

 Parameters p q g g' : nat -> Z.

 Parameter p_prime : forall k, prime (p k).

 Parameter q_prime : forall k, prime (q k).

 Parameter q_divides_pred_p : forall k, (q k | p k - 1).

 Parameter p_poly : polynomial.

 Parameter p_poly_spec : forall k, (size_Z (p k) < peval p_poly k)%nat.

 Parameter g_range : forall k, 1 < g k < p k.

 Parameter g'_range : forall k, 1 < g' k < p k.

 Parameter g_order : forall k, g k ^ q k mod p k = 1.

 Parameter g'_order : forall k, g' k ^ q k mod p k = 1.

End OKAMOTO_PARAMETERS.


Module Okamoto_Homomorphism (OP:OKAMOTO_PARAMETERS).

 Module SPP := Schnorr_Parameters_Properties OP.
 Import SPP.
 Import OP.

 Module G1 := Schnorr_G OP.
 Module G2 := Schnorr_G OP.
 Module G := Group_Prod G1 G2.

 Module H := Schnorr_H OP.
 Module HP := Group_Properties H.
 Import HP.
 
 Open Scope nat_scope.

 Definition g1 k : H.t k.
  intro k.
  refine (exist _ (Zabs_nat (OP.g k)) _).
  destruct (OP.g_range k).
  apply <- H.P_prop; split.
  change 0%nat with (Zabs_nat 0).
  split; apply Zabs_nat_lt; auto with zarith.
  rewrite inj_Zabs_nat, Zabs_eq, OP.g_order; auto with zarith.
 Defined.

 Definition g2 k : H.t k.
  intro k.
  refine (exist _ (Zabs_nat (OP.g' k)) _).
  destruct (OP.g'_range k).
  apply <- H.P_prop; split.
  change 0%nat with (Zabs_nat 0).
  split; apply Zabs_nat_lt; auto with zarith.
  rewrite inj_Zabs_nat, Zabs_eq, OP.g'_order; auto with zarith.
 Defined.

 Definition phi k (x:G.t k) : H.t k :=
  match x with
   | (exist a _, exist a' _) => H.mul (H.pow (g1 k) a) (H.pow (g2 k) a') 
  end.

 Definition cost_phi k (x:G.t k) :=
  match x with
   | (exist a _,exist a' _) => H.cost_pow (g1 k) (Z_of_nat a) * H.cost_pow (g2 k) (Z_of_nat a )
  end.

 Definition cost_phi_poly : polynomial := pmult H.cost_pow_poly H.cost_pow_poly.

 Lemma cost_phi_poly_spec : forall k (x:G.t k),
  cost_phi x <= peval cost_phi_poly k.
 Proof.
  intros k ((a1,H1),(a2,H2)); unfold cost_phi, cost_phi_poly.
  rewrite pmult_spec.
  apply mult_le_compat; apply H.cost_pow_poly_spec.
 Qed.

 Lemma Hpow_simpl : forall k a H n, 
  exists H1, 
   H.pow (exist (H.P k) a H) n = exist (H.P k) (Zabs_nat (Z_of_nat (a^n) mod p k)) H1. 
 Proof.
  intro k.
  assert (Hp:=prime_ge_2 _ (p_prime k)).
  induction n; intros.
  simpl; rewrite Zmod_1_l.
  exists (proj2_sig (H.e k)); trivial.
  auto with zarith.

  change (S n) with (1 + n).
  destruct IHn.
  rewrite <- mul_pow_plus, H0; clear H0; simpl.
  match goal with 
   |- context [exist _ _ ?H] => generalize H
  end.  
  rewrite mult_1_r, inj_mult, inj_mult.
  repeat (rewrite Zabs_nat_Z_of_nat || rewrite inj_Zabs_nat || fail).
  rewrite Zabs_eq, Zabs_eq, Zmult_mod_idemp_l, Zmult_mod_idemp_r.
  intros H1; exists H1; trivial.
  generalize (Z_mod_lt (Z_of_nat (a ^ n)) (p k)); auto with zarith.
  generalize (Z_mod_lt (Z_of_nat a) (p k)); auto with zarith.
 Qed.

 Lemma cyclic : forall k x, H.pow x (Zabs_nat (q k)) = H.e k.
 Proof.
  intros.
  assert (Hin:=H.elems_full x).
  unfold H.elems in Hin.
  apply filter_map_In in Hin.
  destruct Hin as [a [H [Heq _] ] ]; subst.
  destruct (Hpow_simpl _ a H (Zabs_nat (q k))).
  rewrite H0; generalize x; clear x H0.
  rewrite H.P_prop in H; destruct H as [Hlt Heq].
  assert (a = Zabs_nat (Z_of_nat a)) by (symmetry; apply Zabs_nat_Z_of_nat).
  rewrite H, Zpower_pow_nat, Heq.
  change (Zabs_nat 1) with 1; intro.
  rewrite (H.eq_P _ _ x (proj2_sig (H.e k))); trivial.
  auto with zarith.
  generalize (prime_ge_2 _ (q_prime k)); auto with zarith.
 Qed.

 Lemma phi_homo : forall k (x y:G.t k), 
  phi (G.mul x y) = H.mul (phi x) (phi y).
 Proof.
  intros k ((x1,Hx1),(x2,Hx2)) ((y1,Hy1),(y2,Hy2)); unfold phi; simpl.
 
  rewrite H.mul_assoc, <- (H.mul_assoc (H.pow (g1 k) x1) (H.pow (g2 k) x2) (H.pow (g1 k) y1)).
  rewrite (H.mul_comm (H.pow (g2 k) x2) (H.pow (g1 k) y1)).
  rewrite H.mul_assoc, HP.mul_pow_plus, <- H.mul_assoc, HP.mul_pow_plus.
  case (le_gt_dec (Zabs_nat (q k)) (x1 + y1));
  case (le_gt_dec (Zabs_nat (q k)) (x2 + y2));
  intros; trivial.

  assert (x1 + y1 = x1 + y1 - Zabs_nat (q k) + Zabs_nat (q k)) by omega.
  assert (x2 + y2 = x2 + y2 - Zabs_nat (q k) + Zabs_nat (q k)) by omega.
  rewrite H, H0 at 2.
  rewrite <- (HP.mul_pow_plus (g2 k) (x2 + y2 - Zabs_nat (q k)) (Zabs_nat (q k))), cyclic, HP.mul_e_r; trivial.
  rewrite <- (HP.mul_pow_plus (g1 k) (x1 + y1 - Zabs_nat (q k)) (Zabs_nat (q k))), cyclic, HP.mul_e_r; trivial.

  assert (x1 + y1 = x1 + y1 - Zabs_nat (q k) + Zabs_nat (q k)) by omega.
  rewrite H at 2.
  rewrite <- (HP.mul_pow_plus (g1 k) (x1 + y1 - Zabs_nat (q k)) (Zabs_nat (q k))), cyclic, HP.mul_e_r; trivial.
 
  assert (x2 + y2 = x2 + y2 - Zabs_nat (q k) + Zabs_nat (q k)) by omega.
  rewrite H at 2.
  rewrite <- (HP.mul_pow_plus (g2 k) (x2 + y2 - Zabs_nat (q k)) (Zabs_nat (q k))), cyclic, HP.mul_e_r; trivial.
 Qed.

 (* [phi] is a special homomorphism *)
 Definition special_v k := Z_of_nat (Zabs_nat (OP.q k)).
  
 Lemma special_v_spec : forall k, special_v k <> 0%Z.
 Proof.
  intro k; unfold special_v.
  generalize (q_pos k); auto with zarith.
 Qed.
 
 Definition special_v_poly : polynomial := OP.p_poly.

 Lemma size_nat_special_v : forall k, 
  size_nat (Zabs_nat (special_v k)) <= peval special_v_poly k. 
 Proof.
  intro k; unfold special_v, special_v_poly.
  apply lt_le_weak.
  rewrite Zabs_nat_Z_of_nat.
  apply q_size.
 Qed.
 
 Definition cost_special_v (k:nat) := 1.

 Definition cost_special_v_poly : polynomial := 1.

 Lemma cost_special_v_poly_spec : forall k, 
  cost_special_v k <= peval cost_special_v_poly k. 
 Proof.
  intro k; unfold cost_special_v_poly; rewrite pcst_spec; trivial.
 Qed.

 Definition special_u k (x:H.t k) : G.t k := G.e k.
 
 Definition cost_special_u k (x:H.t k) := 1. 

 Definition cost_special_u_poly : polynomial := 1.

 Lemma cost_special_u_poly_spec : forall k (x:H.t k), 
  cost_special_u x <= peval cost_special_u_poly k. 
 Proof.
  intro k; unfold cost_special_u_poly; rewrite pcst_spec; trivial.
 Qed.

 Lemma phi_special : forall k (y:H.t k), 
  phi (special_u y) = H.powZ y (special_v k).
 Proof.
  intros; unfold special_u, special_v.
  rewrite powZ_pow, cyclic.
  unfold G.e, phi, G1.e, G2.e.
  rewrite <- pow_mul_distr; trivial.
 Qed.

End Okamoto_Homomorphism.


(** Instantiation *)
Declare Module SP : OKAMOTO_PARAMETERS.

Module HM := Okamoto_Homomorphism SP.
Module CS := Largest_Challenge_Set HM.G HM.H HM.

Module S := SigmaPhi.SigmaPhi HM.G HM.H HM CS.
