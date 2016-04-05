(** * PreimageEq.v : Proof of equality of preimages under two homomorphisms *)

Require Export SigmaPhi.

Set Implicit Arguments.


(** Constraints on the special homomorphisms: values [u_1(x_1)] and
   [u_2(x_2)] must be some constant independent of [x_1] and [x_2],
   and the special exponent [v] must be the same for both
   homomorphisms.
*)
Module Type EP_CONSTRAINTS (G H1 H2:GROUP) 
 (HM1:HOMOMORPHISM G H1) (HM2:HOMOMORPHISM G H2).

 Parameter special_u_same : forall k (x1:H1.t k) (x2:H2.t k), 
  HM1.special_u x1 = HM2.special_u x2.

 Parameter special_v_same : HM1.special_v = HM2.special_v.

End EP_CONSTRAINTS.


(** The special homomorphism used to prove equality of the preimages
  of a pair of elements in [H1 * H2]
*)
Module EP_Homomorphism (G  H1 H2:GROUP) 
 (HM1:HOMOMORPHISM G H1) (HM2:HOMOMORPHISM G H2)
 (EPC:EP_CONSTRAINTS G H1 H2 HM1 HM2).

 Import EPC.
  
 Module H := Group_Prod H1 H2.

 Module HP1 := Homomorphism_Properties G H1 HM1.
 Module HP2 := Homomorphism_Properties G H2 HM2.

 Definition phi k : G.t k -> H.t k := fun x => (HM1.phi x, HM2.phi x).
 
 Definition cost_phi k (x:G.t k) := 1 + (HM1.cost_phi x + HM2.cost_phi x).
 
 Definition cost_phi_poly := pplus 1 (pplus HM1.cost_phi_poly HM2.cost_phi_poly).
 
 Lemma cost_phi_poly_spec : forall k (x:G.t k),
  cost_phi x <= peval cost_phi_poly k.
 Proof.
  intros; unfold cost_phi, cost_phi_poly.
  rewrite pplus_spec, pplus_spec, pcst_spec.
  apply plus_le_compat; [ trivial | ].
  apply plus_le_compat;
   [ apply HM1.cost_phi_poly_spec | apply HM2.cost_phi_poly_spec ].
 Qed.

 Lemma phi_homo : forall k (x y:G.t k), 
  phi (G.mul x y) = H.mul (phi x) (phi y).
 Proof.
  intros; unfold phi, H.mul; simpl.
  rewrite HM1.phi_homo, HM2.phi_homo; trivial.
 Qed.

 (* [phi] is a special homomorphism *)
 Definition special_v k := HM1.special_v k.

 Lemma special_v_spec : forall k, special_v k <> 0%Z.
 Proof.
  apply HM1.special_v_spec.
 Qed.

 Definition special_v_poly := HM1.special_v_poly.

 Lemma size_nat_special_v : forall k,
  size_nat (Zabs_nat (special_v k)) <= peval special_v_poly k. 
 Proof.
  apply HM1.size_nat_special_v.
 Qed.

 Definition cost_special_v k := HM1.cost_special_v k.

 Definition cost_special_v_poly := HM1.cost_special_v_poly.
 
 Lemma cost_special_v_poly_spec : forall k, 
  cost_special_v k <= peval cost_special_v_poly k. 
 Proof.
  apply HM1.cost_special_v_poly_spec.
 Qed.
 
 Definition special_u k : H.t k -> G.t k := fun x => HM1.special_u (fst x).

 Definition cost_special_u k (x:H.t k) := HM1.cost_special_u (fst x).

 Definition cost_special_u_poly := HM1.cost_special_u_poly.

 Lemma cost_special_u_poly_spec : forall k (x:H.t k), 
  cost_special_u x <= peval cost_special_u_poly k.
 Proof.
  intros; apply HM1.cost_special_u_poly_spec.
 Qed.

 Lemma phi_special : forall k (x:H.t k), 
  phi (special_u x) = H.powZ x (special_v k).
 Proof.
  intros k (x1, x2).
  unfold phi, special_u, special_v.
  rewrite H.powZ_equiv; simpl.
  rewrite HM1.phi_special.
  rewrite (special_u_same x1 x2), special_v_same.
  rewrite HM2.phi_special.
  trivial.
 Qed.

End EP_Homomorphism.
