(** * FiatShamir.v: Fiat Shamir protocol *)

Require Import SigmaPhi.
Require Import FilterMap.
Require Import LtIrrelevance.
Require Import PrimeLib.
Require Import GuillouQuisquater.

Set Implicit Arguments.


Module Type FIAT_SHAMIR_PARAMETERS (ZnP : Z_nZ_PARAMETERS).

 Import ZnP.

 Open Scope Z_scope.

 Parameters p q : nat -> Z.

 Parameter p_prime : forall k, prime (p k).

 Parameter q_prime : forall k, prime (q k).

 Parameter pq_distinct : forall k, (p k) <> (q k). 

 Parameter rsa_modulus : forall k,  (n k) = (p k) * (q k).
 
End FIAT_SHAMIR_PARAMETERS.


Module Fiat_Shamir_Homomorphism 
 (ZnP:Z_nZ_PARAMETERS) (FSP:FIAT_SHAMIR_PARAMETERS ZnP).
  
 Import FSP.

 Module G := Z_nZ ZnP.
 Module H := G.

 Module GP := Group_Properties H.
 Import GP.
 Module HP := Group_Properties G.
 Import HP.

 Open Scope nat_scope.

 Definition phi k (x:G.t k) : (H.t k) := H.powZ x 2.

 Definition cost_phi k (x:G.t k) := (G.cost_pow x 2)%nat.

 Definition cost_phi_poly : polynomial := G.cost_pow_poly.

 Lemma cost_phi_poly_spec : forall k (x:G.t k),
  @cost_phi k x <= peval cost_phi_poly k.
 Proof.
  intros k (a,b); unfold cost_phi, cost_phi_poly; simpl.
  apply G.cost_pow_poly_spec.
 Qed.

 Lemma phi_homo : forall k (x y:G.t k), 
  phi (G.mul x y) = H.mul (phi x) (phi y).
 Proof.
  intros k x y; unfold phi; simpl.
  repeat rewrite GP.mul_e_r.
  rewrite (G.mul_comm x y) at 1.
  repeat rewrite G.mul_assoc.
  rewrite (G.mul_comm y x), (G.mul_comm (G.mul x y) x), G.mul_assoc.
  trivial.
 Qed.

 (* [phi] is a special homomorphism *)
 Definition special_v (k : nat) := 2%Z.
  
 Lemma special_v_spec : forall k, special_v k <> 0%Z.
 Proof.
  intro k; unfold special_v.
  omega.
 Qed.
 
 Definition special_v_poly : polynomial := pcst 2.

 Lemma size_nat_special_v : forall k, 
  size_nat (Zabs_nat (special_v k)) <= peval special_v_poly k. 
 Proof.
  intro k; unfold special_v, special_v_poly.
  rewrite pcst_spec; simpl; omega.
 Qed.
 
 Definition cost_special_v (k:nat) := 1.

 Definition cost_special_v_poly : polynomial := 1.

 Lemma cost_special_v_poly_spec : forall k, 
  cost_special_v k <= peval cost_special_v_poly k. 
 Proof.
  intro k; unfold cost_special_v_poly; rewrite pcst_spec; trivial.
 Qed.

 Definition special_u k (x:H.t k) : G.t k := x.
 
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
  intros; simpl; unfold special_v, special_u, phi.
  trivial.
 Qed.

End Fiat_Shamir_Homomorphism.


(** Instantiation *)
Declare Module ZnP : Z_nZ_PARAMETERS.
Declare Module GQP : FIAT_SHAMIR_PARAMETERS ZnP.

Module HM := Fiat_Shamir_Homomorphism ZnP GQP.
Module CS := Largest_Challenge_Set HM.G HM.H HM.

Module S := SigmaPhi.SigmaPhi HM.G HM.H HM CS.
