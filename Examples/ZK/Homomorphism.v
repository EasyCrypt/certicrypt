(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * Homomorphism.v : Module types of groups and special homomorphisms *)

Require Export PrimeLib.
Require Export Types.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope nat_scope.


(** A family of multiplicative abelian finite groups *)
Module Type GROUP.

 Parameter t : nat -> Type.

 (** The group is finite and non-empty *)
 Parameter elems : forall k, list (t k).
 (* TODO : this parameter is not needed (e is in the group) *)
 Parameter elems_not_nil : forall k, elems k <> nil.
 Parameter elems_full : forall k (x:t k), In x (elems k).
 Parameter elems_nodup : forall k, NoDup (elems k).

 (** Equality is decidable *)
 Parameter eqb : forall k, t k -> t k -> bool.
 Parameter eqb_spec : forall k (x y:t k), if eqb x y then x = y else x <> y.

 (** Identity element *)
 Parameter e : forall k, t k.

 (** Operations: product, inverse *)
 Parameter mul : forall k, t k -> t k -> t k. 
 Parameter inv : forall k, t k -> t k.

 (** Specification *) 
 Parameter mul_assoc : forall k (x y z:t k), mul x (mul y z) = mul (mul x y) z.
 Parameter mul_e_l : forall k (x:t k), mul (e k) x = x.
 Parameter mul_inv_l : forall k (x:t k), mul (inv x) x = e k.
 Parameter mul_comm : forall k (x y:t k), mul x y = mul y x.
 
 (* Power *)
 Fixpoint pow (k:nat) (x:t k) (n:nat) : t k :=
  match n with
  | O => e k
  | S n => mul x (pow x n)
  end.

 Fixpoint powZ (k:nat) (x:t k) (n:Z) {struct n}: t k :=
  match n with
  | Z0 => pow x 0
  | Zpos p => pow x (nat_of_P p)
  | Zneg p => inv (pow x (nat_of_P p))
  end.

 (* Cost *)
 Parameter order_poly : polynomial.

 Parameter order_size_nat : forall k,
  size_nat (length (elems k)) < peval order_poly k.

 Parameter cost_mul : forall k (x y:t k), nat.
 Parameter cost_pow : forall k (x:t k) (n:Z), nat.
 Parameter cost_inv : forall k (x:t k), nat.

 Parameter cost_mul_poly : polynomial.
 Parameter cost_pow_poly : polynomial.
 Parameter cost_inv_poly : polynomial.

 Parameter cost_mul_poly_spec : forall k (x y:t k),
  cost_mul x y <= peval cost_mul_poly k.

 Parameter cost_pow_poly_spec : forall k (x:t k) (n:Z),
  cost_pow x n <= peval cost_pow_poly k.

 Parameter cost_inv_poly_spec : forall k (x:t k),
  cost_inv x <= peval cost_inv_poly k.

End GROUP.


(** Module type for special homomorphisms *)
Module Type HOMOMORPHISM (G H:GROUP).

 Parameter phi : forall k, G.t k -> H.t k.

 Parameter cost_phi : forall k (x:G.t k), nat.

 Parameter cost_phi_poly : polynomial.

 Parameter cost_phi_poly_spec : forall k (x:G.t k),
  cost_phi x <= peval cost_phi_poly k.

 Parameter phi_homo : forall k (x y:G.t k), 
  phi (G.mul x y) = H.mul (phi x) (phi y).

 (* [phi] is a special homomorphism *)
 Parameter special_v : nat -> Z.

 Parameter special_v_spec : forall k, special_v k <> 0%Z.
 
 Parameter special_v_poly : polynomial.

 Parameter size_nat_special_v : forall k, 
  size_nat (Zabs_nat (special_v k)) <= peval special_v_poly k. 
 
 Parameter cost_special_v : nat -> nat.

 Parameter cost_special_v_poly : polynomial.

 Parameter cost_special_v_poly_spec : forall k, 
  cost_special_v k <= peval cost_special_v_poly k. 

 Parameter special_u : forall k, H.t k -> G.t k.

 Parameter cost_special_u : forall k (x:H.t k), nat. 

 Parameter cost_special_u_poly : polynomial.

 Parameter cost_special_u_poly_spec : forall k (x:H.t k), 
  cost_special_u x <= peval cost_special_u_poly k. 

 Parameter phi_special : forall k (x:H.t k), 
  phi (special_u x) = H.powZ x (special_v k).

End HOMOMORPHISM.


(** Module type for the challenge set of a Sigma-phi protocol *)
Module Type CHALLENGE_SET (G H:GROUP) (HM:HOMOMORPHISM G H).

 (** Challenge set : {0,..,c+} *) 
 Parameter cplus : nat -> nat.

 Parameter cplus_poly : polynomial.

 Parameter size_nat_cplus : forall k, 
  size_nat (cplus k) <= peval cplus_poly k. 

 Parameter cplus_spec : forall k p,
  prime p -> ( (p | HM.special_v k) -> Z_of_nat (cplus k) < p)%Z.

End CHALLENGE_SET.


(** * Derived properties of abelian groups *)
Module Group_Properties (G:GROUP).

 Import G.

 Lemma eqb_refl : forall k (x:t k), eqb x x.
 Proof.
  intros k x.
  generalize (eqb_spec x x).
  case (eqb x x); [ | intro H; elim H]; trivial.
 Qed.

 Lemma mul_pow_plus : forall k (x:t k) n m,
  mul (pow x n) (pow x m) = pow x (n + m).
 Proof.
  induction n; intros; simpl.
  simpl; apply mul_e_l.
  simpl; rewrite <- mul_assoc, IHn; trivial.
 Qed.

 Lemma cancellation : forall k (x y z:t k), mul x y = mul x z -> y = z.
 Proof.
  intros.
  rewrite <- (mul_e_l y), <- (mul_e_l z).
  rewrite <- (mul_inv_l x), <- mul_assoc, <- mul_assoc, H; trivial.
 Qed.

 Lemma mul_e_r : forall k (x:t k), mul x (e k) = x.
 Proof.
  intros; rewrite mul_comm, mul_e_l; trivial.
 Qed.

 Lemma mul_inv_r : forall k (x:t k), mul x (inv x) = e k.
 Proof.
  intros; rewrite mul_comm, mul_inv_l; trivial.
 Qed.

 Lemma inv_mul : forall k (a b : t k), inv (mul a b) = mul (inv a) (inv b).
 Proof.
  intros.
  apply cancellation with (mul a b).
  rewrite mul_inv_r, (mul_comm a b), <- mul_assoc.
  rewrite (mul_assoc a (inv a)), mul_inv_r, mul_e_l, mul_inv_r; trivial.
 Qed.

 Lemma inv_e : forall k, inv (e k) = e k.
 Proof.
  intros.
  apply cancellation with (e k).
  rewrite mul_inv_r, mul_e_l; trivial.
 Qed.

 Lemma inv_inv : forall k (x:t k), inv (inv x) = x.
 Proof.
  intros.
  apply cancellation with (inv x).
  rewrite mul_inv_l, <- inv_mul, mul_inv_r.
  apply inv_e.
 Qed.

 Lemma pow_e : forall k n, pow (e k) n = e k.
 Proof.
  induction n; intros; simpl.
  trivial.
  rewrite mul_e_l; trivial.
 Qed.

 Lemma pow_mul_distr : forall k (x y:t k) n,
  pow (mul x y) n = mul (pow x n) (pow y n).
 Proof.
  induction n; intros.
  simpl; rewrite mul_e_r; trivial. 
  simpl; rewrite mul_assoc.
  rewrite (mul_comm x (pow x n)).
  rewrite <- (mul_assoc (pow x n)).
  rewrite (mul_comm (pow x n)).
  repeat rewrite <- mul_assoc.
  rewrite IHn; trivial.
 Qed.

 Lemma pow_pow : forall k (x:t k) n m, pow (pow x n) m = pow x (n * m).
 Proof.
  induction n; intros; simpl.
  rewrite pow_e; trivial.
  rewrite <- mul_pow_plus, <- IHn; apply pow_mul_distr.
 Qed.

 Lemma pow_inv : forall k (x:t k) n, pow (inv x) n = inv (pow x n).
 Proof.
  induction n; simpl.
  rewrite inv_e; trivial.
  rewrite IHn, inv_mul; trivial.
 Qed.

 Lemma pow_minus : forall k (x:t k) m n,
  n > m ->
  pow x (n - m) = mul (pow x n) (inv (pow x m)).
 Proof.
  intros.
  replace n with (m + (n - m)) by omega.
  rewrite <- mul_pow_plus, <- mul_assoc, mul_comm, <- mul_assoc.
  rewrite mul_inv_l, mul_e_r, minus_plus; trivial.
 Qed.

 Lemma mul_powZ_plus : forall k (x:t k) n m, 
  mul (powZ x n) (powZ x m) = powZ x (n + m).
 Proof.
  intros.
  case n; intros; simpl.
   apply mul_e_l.
   case m; intros; simpl.  
    apply mul_e_r.

    rewrite nat_of_P_plus_morphism; apply mul_pow_plus.   

    case_eq ((p ?= p0)%positive Eq); intro H; simpl.
     apply Pcompare_Eq_eq in H; rewrite H; rewrite mul_inv_r; trivial.

     apply ZC2 in H.
     rewrite nat_of_P_minus_morphism; trivial.
     rewrite pow_minus, mul_comm, inv_mul, inv_inv; trivial.
     apply nat_of_P_gt_Gt_compare_morphism in H; trivial.

     rewrite nat_of_P_minus_morphism; trivial.
     rewrite pow_minus; trivial.
     apply nat_of_P_gt_Gt_compare_morphism in H; trivial.

   case m; intros; simpl.  
    apply mul_e_r.

    case_eq ((p ?= p0)%positive Eq); intro H; simpl.
     apply Pcompare_Eq_eq in H; rewrite H; rewrite mul_inv_l; trivial.

     apply ZC2 in H.
     rewrite nat_of_P_minus_morphism; trivial.
     rewrite pow_minus, mul_comm; trivial.
     apply nat_of_P_gt_Gt_compare_morphism in H; trivial.

     rewrite nat_of_P_minus_morphism; trivial. 
     rewrite pow_minus, inv_mul, inv_inv; trivial.
     apply nat_of_P_gt_Gt_compare_morphism in H; trivial.
     
   rewrite nat_of_P_plus_morphism.
   rewrite <- inv_mul, mul_pow_plus; trivial.
 Qed.

 Lemma powZ_e : forall k n, powZ (e k) n = e k.
 Proof.
  induction n; simpl.
  trivial.
  apply pow_e.
  rewrite pow_e, inv_e; trivial.
 Qed. 

 Lemma powZ_mul_distr : forall k (x y:t k) n, 
  powZ (mul x y) n = mul (powZ x n) (powZ y n).
 Proof.
  destruct n; intros.
  simpl; rewrite mul_e_r; trivial.
  apply pow_mul_distr.
  simpl.
  rewrite <- inv_mul, pow_mul_distr; trivial.
 Qed.
  
 Lemma powZ_powZ : forall k (x:t k) n m, powZ (powZ x n) m = powZ x (n * m).
 Proof.
  induction n; intros; simpl.
  apply powZ_e.
  case m; intros; simpl.
   trivial.
   rewrite pow_pow, nat_of_P_mult_morphism; trivial. 
   rewrite pow_pow, nat_of_P_mult_morphism; trivial.
  case m; intros; simpl.
   trivial.
   rewrite pow_inv, pow_pow, nat_of_P_mult_morphism; trivial.
   rewrite pow_inv, pow_pow, inv_inv, nat_of_P_mult_morphism; trivial.
 Qed.

 Lemma powZ_pow : forall k (x:t k) n,
  powZ x (Z_of_nat n) = pow x n.
 Proof.
  induction n; simpl.
  trivial.
  rewrite nat_of_P_o_P_of_succ_nat_eq_succ; simpl; trivial.
 Qed.

 Lemma powZ_minus : forall k (x : t k) n,
   powZ x (- n) = inv (powZ x n).
 Proof.
   intros k x n;case n; simpl; trivial.
   rewrite inv_e; trivial.
   intro p; rewrite inv_inv; trivial.
 Qed.

End Group_Properties.


(** Derived properties of special homomorphisms *)
Module Homomorphism_Properties (G H:GROUP) (HM:HOMOMORPHISM G H).  

 Module GP := Group_Properties G.
 Module HP := Group_Properties H.
 Export GP HP.
 Export HM.
 
 Lemma phi_e : forall k,
  phi (@G.e k) = H.e k.
 Proof.
  intros.
  apply HP.cancellation with (phi (G.e k)).
  rewrite <- phi_homo, G.mul_e_l, HP.mul_e_r; trivial.
 Qed.

 Lemma phi_inv : forall k (x:G.t k),
  phi (G.inv x) = H.inv (phi x).
 Proof.
  intros.
  apply HP.cancellation with (phi x).
  rewrite <- phi_homo, HP.mul_inv_r, GP.mul_inv_r.
  apply phi_e.
 Qed.

 Lemma phi_pow : forall k (x:G.t k) a,
  phi (G.pow x a) = H.pow (phi x) a.
 Proof.
  induction a; simpl.
  apply phi_e.
  rewrite <- IHa, phi_homo; trivial.
 Qed.

 Lemma phi_powZ : forall k (x:G.t k) a,
  phi (G.powZ x a) = H.powZ (phi x) a.
 Proof.
  induction a; simpl.
  apply phi_e.
  apply phi_pow.
  rewrite phi_inv, phi_pow; trivial.
 Qed.

End Homomorphism_Properties.


(** Direct product of two groups *)
Module Group_Prod (G1 G2:GROUP) <: GROUP.
 
 Definition t k := (G1.t k * G2.t k)%type.
 
 Definition elems k := list_prod (G1.elems k) (G2.elems k).

 Lemma elems_not_nil : forall k, elems k <> nil.
 Proof.
  unfold elems; intros k H.
  apply (f_equal (@length _)) in H.
  rewrite prod_length in H.
  destruct (mult_is_O _ _ H).
  apply (G1.elems_not_nil (length_nil _ H0)).
  apply (G2.elems_not_nil (length_nil _ H0)).
 Qed.

 Lemma elems_full : forall k (x:t k), In x (elems k).
 Proof.
  intros k x; unfold elems; elim x; intros a b.
  apply in_prod.
  exact (G1.elems_full a).   
  exact (G2.elems_full b).   
 Qed.

 Lemma elems_nodup : forall k, NoDup (elems k).
 Proof.
  intros k; unfold elems.
  apply NoDup_list_prod.
  exact (G1.elems_nodup k).
  exact (G2.elems_nodup k).
 Qed.

 Definition eqb k (x y:t k) : bool := 
  andb (G1.eqb (fst x) (fst y)) (G2.eqb (snd x) (snd y)).
 
 Lemma eqb_spec : forall k (x y: t k), if eqb  x y then x = y else x <> y.
 Proof.
  intros k (x1,y1) (x2,y2).
  unfold eqb; simpl.
  generalize (G1.eqb_spec x1 x2).
  generalize (G2.eqb_spec y1 y2).
  case (G1.eqb x1 x2); simpl.
  case (G2.eqb y1 y2); simpl.
  intros; subst; trivial.
  intros; injection; auto.
  intros; injection; auto.
 Qed.

 Definition e k := (G1.e k, G2.e k). 

 Definition inv k (x:t k) := (G1.inv (fst x), G2.inv (snd x)).

 Definition mul k (x y:t k) := (G1.mul (fst x) (fst y), G2.mul (snd x) (snd y)).
 
 Lemma mul_assoc : forall k (x y z:t k), mul x (mul y z) = mul (mul x y) z.
 Proof.
  intros k x y z; unfold mul; simpl.
  rewrite G1.mul_assoc, G2.mul_assoc; trivial.
 Qed.
 
 Lemma mul_e_l : forall k (x:t k), mul (e k) x = x.
 Proof.
  destruct x.
  intros; unfold mul; rewrite G1.mul_e_l, G2.mul_e_l; trivial.
 Qed.
 
 Lemma mul_inv_l : forall k (x:t k), mul (inv x) x = e k.
 Proof.
  destruct x.
  intros; unfold mul; simpl; rewrite G1.mul_inv_l, G2.mul_inv_l; trivial.
 Qed.

 Lemma mul_comm : forall k (x y:t k), mul x y = mul y x.
 Proof.
  intros.
  unfold mul; rewrite G1.mul_comm, G2.mul_comm; trivial.
 Qed.

 Fixpoint pow (k:nat) (x:t k) (n:nat) : t k :=
  match n with
  | O => e k
  | S n => mul x (pow x n)
  end.

 Fixpoint powZ (k:nat) (x:t k) (n:Z) {struct n}: t k :=
  match n with
  | Z0 => pow x 0
  | Zpos p => pow x (nat_of_P p)
  | Zneg p => inv (pow x (nat_of_P p))
  end.

 Lemma pow_equiv: forall k (x:t k) n, 
  pow x n = (G1.pow (fst x) n , G2.pow (snd x) n).
 Proof.
  induction n; simpl.
  trivial.
  rewrite IHn; trivial.
 Qed.

 Lemma powZ_equiv: forall k (x:t k) n, 
  powZ x n = (G1.powZ (fst x) n , G2.powZ (snd x) n).
 Proof.
  destruct n; simpl.
  trivial.
  apply pow_equiv.
  rewrite pow_equiv; trivial.
 Qed.

 Definition order_poly := pplus G1.order_poly G2.order_poly.

 Lemma order_size_nat : forall k,
  size_nat (length (elems k)) < peval order_poly k.
 Proof.
  intros k; unfold order_poly, elems.
  rewrite pplus_spec, prod_length.
  apply le_lt_trans with 
   (size_nat (length (G1.elems k)) + size_nat (length (G2.elems k))).
  apply size_nat_mult.
  apply plus_lt_compat.
  exact (G1.order_size_nat k).
  exact (G2.order_size_nat k).
 Qed.

 Definition cost_mul k (x y:t k) := 
  G1.cost_mul (fst x) (fst y) + G2.cost_mul (snd x) (snd y).

 Definition cost_pow k (x:t k) (n:Z) := 
  G1.cost_pow (fst x) n + G2.cost_pow (snd x) n.

 Definition cost_inv k (x:t k) :=
  G1.cost_inv (fst x) + G2.cost_inv (snd x).

 Definition cost_mul_poly := pplus G1.cost_mul_poly G2.cost_mul_poly.
 Definition cost_pow_poly := pplus G1.cost_pow_poly G2.cost_pow_poly.
 Definition cost_inv_poly := pplus G1.cost_inv_poly G2.cost_inv_poly.

 Lemma cost_mul_poly_spec : forall k (x y:t k),
  cost_mul x y <= peval cost_mul_poly k.
 Proof.
  intros k x y; unfold cost_mul, cost_mul_poly.
  rewrite pplus_spec.
  apply plus_le_compat.
  exact (G1.cost_mul_poly_spec (fst x) (fst y)).
  exact (G2.cost_mul_poly_spec (snd x) (snd y)).
 Qed.
  
 Lemma cost_pow_poly_spec : forall k (x:t k) (n:Z),
  cost_pow x n <= peval cost_pow_poly k.
 Proof.
  intros k x n; unfold cost_pow, cost_pow_poly.
  rewrite pplus_spec.
  apply plus_le_compat.
  exact (G1.cost_pow_poly_spec (fst x) n).
  exact (G2.cost_pow_poly_spec (snd x) n).
 Qed.
  
 Lemma cost_inv_poly_spec : forall k (x:t k),
  cost_inv x <= peval cost_inv_poly k.
 Proof.
  intros k x; unfold cost_inv, cost_inv_poly.
  rewrite pplus_spec.
  apply plus_le_compat.
  exact (G1.cost_inv_poly_spec (fst x)).
  exact (G2.cost_inv_poly_spec (snd x)).
 Qed.

End Group_Prod.


(** Direct product of two special homomorphisms *)
Module Homomorphism_Prod (G1 H1 G2 H2:GROUP) 
 (HM1:HOMOMORPHISM G1 H1) (HM2:HOMOMORPHISM G2 H2).
  
 Module GG := Group_Prod G1 G2.
 Module HH := Group_Prod H1 H2.

 Module HP1 := Homomorphism_Properties G1 H1 HM1.
 Module HP2 := Homomorphism_Properties G2 H2 HM2.

 Definition phi k : GG.t k -> HH.t k :=
  fun a => let (x, y) := a in (HM1.phi x, HM2.phi y).
 
 Definition cost_phi k (x:GG.t k) := HM1.cost_phi (fst x) + HM2.cost_phi (snd x).
 
 Definition cost_phi_poly := pplus HM1.cost_phi_poly HM2.cost_phi_poly.
 
 Lemma cost_phi_poly_spec : forall k (x:GG.t k),
  cost_phi x <= peval cost_phi_poly k.
 Proof.
  intros k x; unfold cost_phi, cost_phi_poly.
  rewrite pplus_spec.
  apply plus_le_compat.
  exact (HM1.cost_phi_poly_spec (fst x)).
  exact (HM2.cost_phi_poly_spec (snd x)).
 Qed.

 Lemma phi_homo : forall k (x y:GG.t k), 
  phi (GG.mul x y) = HH.mul (phi x) (phi y).
 Proof.
  destruct x; destruct y; simpl.
  rewrite HM1.phi_homo, HM2.phi_homo; trivial.
 Qed.

 (* [phi] is a special homomorphism *)
 Definition special_v k := Zlcm (HM1.special_v k) (HM2.special_v k).

 Lemma special_v_spec : forall k, special_v k <> 0%Z.
 Proof.
  intro k; apply Zlcm_neq_0.
  exact (@HM1.special_v_spec k).
  exact (@HM2.special_v_spec k).  
 Qed.

 Definition special_v_poly := pplus HM1.special_v_poly HM2.special_v_poly.

 Lemma size_nat_special_v : forall k,
  size_nat (Zabs_nat (special_v k)) <= peval special_v_poly k. 
 Proof.
  intro; unfold special_v, special_v_poly.
  rewrite pplus_spec.
  assert (H1:=HM1.size_nat_special_v k).
  assert (H2:=HM2.size_nat_special_v k).
  assert (H3:=@HM1.special_v_spec k).
  assert (H4:=@HM2.special_v_spec k).

  apply le_trans with 
   (size_nat (Zabs_nat (Zabs ((HM1.special_v k) * (HM2.special_v k))))).
  apply size_nat_monotonic.
  apply Zabs_nat_le; split.
  apply Zlcm_is_pos.
  apply Zdivide_le.
  apply Zlcm_is_pos.
  apply Zle_lt.
  apply Zabs_neq_0.
  apply Zmult_neq_0; trivial.
  apply Zabs_pos.
  rewrite Zlcm_gcd.
  apply Zdivide_factor_l.
  
  rewrite Zabs_Zmult.
  rewrite Zabs_nat_mult.
  repeat rewrite Zabs_nat_Zabs.
  apply le_trans with 
   (size_nat (Zabs_nat (HM1.special_v k)) + size_nat (Zabs_nat (HM2.special_v k))).
  apply size_nat_mult.
  apply plus_le_compat; trivial.
 Qed.
 
 Definition cost_special_v k := HM1.cost_special_v k + HM2.cost_special_v k.

 Definition cost_special_v_poly := 
  pplus HM1.cost_special_v_poly HM2.cost_special_v_poly .
 
 Lemma cost_special_v_poly_spec : forall k, 
  cost_special_v k <= peval cost_special_v_poly k. 
 Proof.
  intro; unfold cost_special_v, cost_special_v_poly.
  rewrite pplus_spec.
  apply plus_le_compat.
  exact (HM1.cost_special_v_poly_spec k).  
  exact (HM2.cost_special_v_poly_spec k).
 Qed.
 
 Definition special_u k : HH.t k -> GG.t k :=
  fun x => let (x1, x2) := x in 
   let v1 := HM1.special_v k in
   let v2 := HM2.special_v k in
   let v := special_v k in
   let y1 := G1.powZ (HM1.special_u x1) (v / v1) in
   let y2 := G2.powZ (HM2.special_u x2) (v / v2) in  (y1, y2).

 Definition cost_special_u k (x:HH.t k) := 
  HM1.cost_special_u (fst x) + HM2.cost_special_u (snd x).

 Definition cost_special_u_poly := 
  pplus HM1.cost_special_u_poly HM2.cost_special_u_poly.

 Lemma cost_special_u_poly_spec : forall k (x:HH.t k), 
  cost_special_u x <= peval cost_special_u_poly k.
 Proof.
  intros; unfold cost_special_u, cost_special_u_poly.
  rewrite pplus_spec.
  apply plus_le_compat.
  exact (HM1.cost_special_u_poly_spec (fst x)).
  exact (HM2.cost_special_u_poly_spec (snd x)).
 Qed.

 Lemma phi_special : forall k (x:HH.t k), 
  phi (special_u x) = HH.powZ x (special_v k).
 Proof.
  destruct x; simpl.
  rewrite HP1.phi_powZ, HP2.phi_powZ, HM1.phi_special, HM2.phi_special.
  rewrite HP1.HP.powZ_powZ, HP2.HP.powZ_powZ.
  rewrite <- Zdivide_Zdiv_eq_full, <- Zdivide_Zdiv_eq_full; trivial.
  rewrite HH.powZ_equiv; simpl; trivial.
  apply HM2.special_v_spec.
  apply Zlcm_div_r.
  apply HM1.special_v_spec.
  apply Zlcm_div_l.
 Qed.

End Homomorphism_Prod.


(** Largest challenge set for a Sigma-phi protocol *)
Module Largest_Challenge_Set (G H:GROUP) (HM:HOMOMORPHISM G H) : CHALLENGE_SET G H HM.

 Import HM.
 Open Scope Z_scope.

 Definition cplus k := 
  if Z_eq_dec (Zabs (special_v k)) 1
   then 1%nat
   else Zabs_nat (smallest_prime_divisor (Zabs (special_v k)) - 1).

 Definition cplus_poly := special_v_poly.

 Lemma size_nat_cplus : forall k, 
  (size_nat (cplus k) <= peval cplus_poly k)%nat.
 Proof.
  intro k.
  eapply le_trans; [ | apply size_nat_special_v].  
  apply size_nat_monotonic.

  assert (Hv:=@special_v_spec k).
  unfold cplus.
  case (Z_eq_dec (Zabs (special_v k)) 1); intro Heq.
  rewrite <- (Zabs_nat_Zabs (special_v k)), Heq; trivial.
  
  assert (H:1 < Zabs (special_v k)).
  apply Zabs_neq_0 in Hv.
  generalize (Zabs_pos (special_v k)); omega.

  destruct (smallest_prime_divisor_spec _ H) as [H0 [H1 _] ].  
  set (p:=smallest_prime_divisor (Zabs (special_v k))) in *.
  assert (Hle:0 <= p) by (apply prime_ge_2 in H0; omega).

  unfold cplus; fold p.
  apply Zdivide_le in H1; [ | omega | omega].
  rewrite <- (Zabs_nat_Zabs (special_v k)).
  apply prime_ge_2 in H0.
  apply Zabs_nat_le; omega.
 Qed.

 Lemma cplus_spec : forall k p,
  prime p -> ( (p | special_v k) -> Z_of_nat (cplus k) < p)%Z.
 Proof.
  intros k p' H H0.
  assert (Hv:=@special_v_spec k).
  unfold cplus.
  case (Z_eq_dec (Zabs (special_v k)) 1); intro Heq.
  destruct (Zabs_spec (special_v k)) as [ [H1 H2] | [H1 H2] ].
  rewrite Heq in H2.
  rewrite <- H2 in H0.
  apply prime_ge_2 in H.
  apply Zdivide_le in H0; omega.

  rewrite Heq in H2.
  apply (f_equal Zopp) in H2.
  rewrite Zopp_involutive in H2.
  rewrite <- H2 in H0.
  apply Zdivide_opp_r_rev in H0.
  apply prime_ge_2 in H.
  apply Zdivide_le in H0; omega.
  
  assert (H1:1 < Zabs (special_v k)).
  apply Zabs_neq_0 in Hv.
  generalize (Zabs_pos (special_v k)); omega.
  
  unfold cplus.  
  destruct (smallest_prime_divisor_spec _ H1).
  set (p:=smallest_prime_divisor (Zabs (special_v k))) in *.
 
  apply prime_ge_2 in H2.
  apply Zlt_le_trans with p.
  rewrite inj_Zabs_nat.
  rewrite Zabs_eq; omega.

  apply H3.
  trivial.
  apply Zdivide_trans with (special_v k); [trivial | apply Zabs_div]. 
 Qed.  

End Largest_Challenge_Set.
