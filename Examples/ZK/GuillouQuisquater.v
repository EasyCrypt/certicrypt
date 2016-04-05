(** * GuillouQuisquater.v : Guillou-Quisquater protocol *)

Require Import SigmaPhi.
Require Import FilterMap.
Require Import LtIrrelevance.
Require Import PrimeLib.

Set Implicit Arguments.


Module Type Z_nZ_PARAMETERS.

 Open Scope Z_scope.

 Parameters n : nat -> Z.

 Parameter n_pos : forall k, 1 < (n k).
 
 Parameter n_poly : polynomial.
 
 Parameter n_poly_spec : forall k, (size_Z (n k) < peval n_poly k)%nat.
 
End Z_nZ_PARAMETERS.


Module Z_nZ_PROPERTIES (P : Z_nZ_PARAMETERS).

  Import P.
  
  Lemma n_pos' : forall k, (1 < Zabs_nat (n k))%nat.
  Proof.
   intros.
   change 1%nat with (Zabs_nat 1%Z).
   apply Zabs_nat_lt.
   split;[ omega | ].
   apply n_pos.
  Qed.

End Z_nZ_PROPERTIES.


Module Z_nZ (P: Z_nZ_PARAMETERS) <: GROUP.

 Module P' := Z_nZ_PROPERTIES P.
 Import P.
 Import P'.

 Definition P k x : bool :=
  Zle_bool 0 x && negb (Zle_bool (n k) x) && Zeq_bool (Zgcd x (n k)) 1.

 Lemma eq_P : forall k x (H1:P k x) (H2:P k x), H1 = H2.
 Proof.
  intros.
  apply eq_proofs_unicity.
  intros a b; case (bool_dec a b); auto.
 Qed.

 Lemma P_prop : forall k x, P k x <->
  (0 <= x < n k) /\ rel_prime x (n k).
 Proof.
  unfold P; split; intros.

  apply andb_prop in H; destruct H.  
  apply andb_prop in H; destruct H.  
  split.
  split.

  apply Zle_bool_imp_le; trivial.
  generalize (Zle_cases (n k) x).
  apply -> is_true_negb_false in H1.
  rewrite H1.
  omega.

  apply Zeq_is_eq_bool in H0.
  apply Zgcd_1_rel_prime in H0.
  trivial.

  destruct H.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply Zle_imp_le_bool; omega.
  apply eq_true_not_negb.
  intro.
  apply Zle_bool_imp_le in H1.
  omega.
    
  apply -> Zeq_is_eq_bool.
  apply <- Zgcd_1_rel_prime.
  trivial.
 Qed.

 Definition t k := {x | P k x}.

 Definition elems k : list (t k) := 
  filter_map (P k) (@exist _ _) (map (fun x => Z_of_nat x) 
   (seq 0 (Zabs_nat (n k)))).

 Lemma elems_not_nil : forall k, elems k <> nil.
 Proof.
  intro k; unfold elems.

  assert (Hn := n_pos k).  
  assert (Hn' := n_pos' k).  
  assert (P k 1).
  unfold P.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  trivial.
  apply fold_is_true.
  rewrite is_true_negb_false.
  apply not_true_is_false; intro.
  apply Zle_bool_imp_le in H.
  omega.
    
  apply -> Zeq_is_eq_bool.
  apply <- Zgcd_1_rel_prime.
  apply rel_prime_1.
  
  induction (Zabs_nat (n k));[ omega | ].

  assert (In 1 (map (fun x : nat => Z_of_nat x) (seq 0 (S n0)))).
  change 1 with (Z_of_nat (Zabs_nat 1)).
  apply in_map.
  apply le_In_seq.
  split; [ omega | ].
  apply le_trans with 2%nat; [ trivial | ].
  rewrite <- plus_n_O; trivial.

  intro Heq.
  apply In_filter_map with (A:=Z) (f:=@exist _ _) (H:=H) in H0.
  rewrite Heq in H0.
  inversion H0.
 Qed.

 Lemma elems_full : forall k (x:t k), In x (elems k).
 Proof.
  intros k (x,H).
  apply In_filter_map.  
  replace x with (Z_of_nat (Zabs_nat x)). 
  apply in_map.
  apply le_In_seq.
  apply andb_prop in H; destruct H.
  apply andb_prop in H; destruct H.
  apply Zle_bool_imp_le in H.
  split.
  change 0%nat with (Zabs_nat (Z_of_nat 0)).
  apply Zabs_nat_le; simpl; omega.
  simpl.
  rewrite <- plus_n_O.
  apply Zabs_nat_lt.
  apply is_true_negb_false in H1.
  generalize (Zle_cases (n k) x).
  rewrite H1; omega.

  apply P_prop in H.
  rewrite inj_Zabs_nat, Zabs_eq; trivial.
  omega.
 Qed.

 Lemma elems_nodup : forall k, NoDup (elems k).
 Proof.
  intro k; unfold elems.
  apply NoDup_filter_map_inj.
  intros x y ? ? H; inversion H; trivial.
  apply NoDup_map_inj.
  intros; apply inj_eq_rev; trivial.
  apply NoDup_seq.
 Qed.


 (** Equality is decidable *)
 Definition eqb k (x y:t k) :=
  match x, y with
   | exist n _, exist m _ => Zeq_bool n m
  end.

 Lemma eqb_spec : forall k (x y:t k), if eqb x y then x = y else x <> y.
 Proof.
  intros k (a,Ha) (b,Hb).
  unfold eqb.
  generalize (Zeq_bool_eq a b); generalize (Zeq_bool_neq a b).
  case (Zeq_bool a b); intros.
  assert (a = b) by (apply H0; trivial).
  subst; rewrite (eq_P _ _ Hb Ha); trivial.
  assert (a <> b) by (apply H; trivial).
  intro H2; elim H1; injection H2; trivial.
 Qed.

 (** Identity element *)
 Definition e k : t k.
 intro k.
 refine (exist _ 1 _).
 apply <- P_prop; split.
 split; [omega | apply n_pos].
 apply rel_prime_1.
 Defined. 

 (** Operations: product, inverse *)

 Definition mul : forall k, t k -> t k -> t k. 
  intros k (a,Ha) (b,Hb).
  assert (Hpos := n_pos k).
  refine (exist _ ( (a * b) mod n k) _)%Z.
  apply P_prop in Ha; destruct Ha as [[ Ha1 Ha2 ] Ha3 ].  
  apply P_prop in Hb; destruct Hb as [[ Hb1 Hb2 ] Hb3 ].
  apply <- P_prop; split.
  apply Z_mod_lt.
  omega. 
  apply rel_prime_mod.
  omega.
  apply rel_prime_sym.
  apply rel_prime_mult; apply rel_prime_sym; trivial.
 Defined.


 Definition inv : forall k, t k -> t k.
  intros k (a,Ha).
  assert (Hn := n_pos k).
  refine 
   (exist (P k) ((fst (fst (eeuclid a (n k)))) mod (n k)) _).
  
  apply P_prop in Ha; destruct Ha as [[Hlt1 Hlt2] Hrel_prime].
  apply <- P_prop.
  
  destruct (eeuclid_bound a (n k) (Zabs (n k))) as [H2 H3].
  repeat rewrite Zabs_eq; omega.
  apply Zle_refl.
 
  assert (H1:=eeuclid_spec a (n k)).
  assert (Hgcd:Zis_gcd a (n k) 1).
  apply Zgcd_1_rel_prime in Hrel_prime.
  rewrite <- Hrel_prime.
  apply Zgcd_is_gcd.

  destruct (eeuclid a (n k)) as ((u, v), d); simpl in *.
  destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.
  case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
  subst.

  split.
  apply Z_mod_lt.  
  omega.

  apply rel_prime_mod.
  omega.
  apply bezout_rel_prime.
  econstructor.
  instantiate (1:=v).
  instantiate (1:=a).
  rewrite Zmult_comm; trivial.
 Defined.

 (** Specification *) 
 Lemma mul_assoc : forall k (x y z:t k), mul x (mul y z) = mul (mul x y) z.
 Proof.
  intros k (a,Ha) (b,Hb) (c,Hc); unfold mul.
  match goal with
   |- exist _ ?a ?Ha = exist _ ?b ?Hb => 
    generalize Ha Hb; assert (H:a = b)
  end.
  rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
  rewrite Zmult_assoc; trivial.
  rewrite H; intros p1 p2; rewrite (eq_P _ _ p1 p2); trivial.
 Qed.

 Lemma mul_e_l : forall k (x:t k), mul (e k) x = x.
 Proof.
  intros k (a,Ha); unfold mul, e.
  match goal with
   |- exist _ ?a ?Ha = exist _ ?b ?Hb => 
    generalize Hb Ha; assert (H:a = b)
  end.
  rewrite P_prop in Ha; destruct Ha as [[H1 H2] H3].
  rewrite Zmult_1_l, Zmod_small; trivial.
  omega.
  rewrite H; intros p1 p2; rewrite (eq_P _ _ p1 p2); trivial.
 Qed.

 Lemma mul_inv_l : forall k (x:t k), mul (inv x) x = e k.
 Proof.
  intros k (a,Ha); unfold mul, inv, e.
  match goal with
   |- exist _ ?a ?Ha = exist _ ?b ?Hb => 
    generalize Ha Hb; assert (H:a = b);
     [ | rewrite H; intros p1 p2; rewrite (eq_P _ _ p1 p2); trivial]
  end.

  apply P_prop in Ha; destruct Ha as [[Hlt1 Hlt2] Hrp].
  destruct (eeuclid_bound a (n k) (Zabs (n k))) as [H2 H3].  
  repeat rewrite Zabs_eq; omega.
  apply Zle_refl.
  
  assert (H1:=eeuclid_spec a (n k)).
  assert (Hp:=n_pos k).

  assert (Hgcd:Zis_gcd a (n k) 1).
  apply  Zgcd_1_rel_prime in Hrp.
  rewrite <- Hrp.
  apply Zgcd_is_gcd.

  destruct (eeuclid a (n k)) as ((u, v), d); simpl in *.
  destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.
  case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
  clear H5 H6 Hgcd; subst.

  rewrite <- Zmod_1_l with (n k); [ | auto with zarith].

  rewrite <- H, Z_mod_plus_full; trivial.
  rewrite Zmult_mod_idemp_l; trivial.
 Qed.

 Lemma mul_comm : forall k (x y:t k), mul x y = mul y x.
 Proof.
  intros k (a,Ha) (b,Hb); unfold mul.
  match goal with
   |- exist _ ?a ?Ha = exist _ ?b ?Hb => 
    generalize Ha Hb; assert (H:a = b)
  end.
  rewrite Zmult_comm; trivial.
  rewrite H; intros p1 p2; rewrite (eq_P _ _ p1 p2); trivial.
 Qed.
 
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
 Open Scope nat_scope.

 Definition order_poly : polynomial := n_poly.

 Lemma order_size_nat : forall k,
  size_nat (length (elems k)) < peval order_poly k.
 Proof.
  intro k.
  apply le_lt_trans with (2:=n_poly_spec k).
  apply size_nat_monotonic.
  eapply le_trans; [apply filter_map_length | ].
  rewrite map_length, seq_length; apply le_refl.
 Qed.

 Definition cost_mul k (x y:t k) : nat := size_Z (proj1_sig y).

 Definition cost_pow k (x:t k) (m:Z) : nat :=
  size_Z (proj1_sig x) * (size_Z (n k)).

 Definition cost_inv k (x:t k) : nat := size_Z (proj1_sig x) * size_Z (n k).

 Definition cost_mul_poly : polynomial := n_poly. 
 Definition cost_pow_poly : polynomial := pmult n_poly n_poly.
 Definition cost_inv_poly : polynomial := pmult n_poly n_poly.

 Lemma cost_mul_poly_spec : forall k (x y:t k),
  cost_mul x y <= peval cost_mul_poly k.
 Proof.
  intros k x (b,Hb).
  unfold cost_mul; simpl.
  apply P_prop in Hb; decompose [and] Hb; clear Hb.
  apply le_trans with (size_Z (n k)).
  apply size_nat_monotonic; apply lt_le_weak; trivial.
  apply Zabs_nat_lt; omega.
  apply lt_le_weak; apply n_poly_spec.
 Qed.

 Lemma cost_pow_poly_spec : forall k (x:t k) (m:Z),
  cost_pow x m <= peval cost_pow_poly k.
 Proof.
  intros k (a,Ha) m.
  unfold cost_pow, cost_pow_poly; simpl.
  rewrite pmult_spec.
  apply P_prop in Ha; decompose [and] Ha; clear Ha.
  apply mult_le_compat.
  apply le_trans with (size_Z (n k)).
  apply size_nat_monotonic; apply lt_le_weak; trivial.
  apply Zabs_nat_lt; omega.
  apply lt_le_weak; apply n_poly_spec.
  apply lt_le_weak; apply n_poly_spec.
 Qed.

 Lemma cost_inv_poly_spec : forall k (x:t k),
  cost_inv x <= peval cost_inv_poly k.
 Proof.
  intros k (a,Ha).
  unfold cost_inv, cost_inv_poly; simpl.
  rewrite pmult_spec.
  apply P_prop in Ha; decompose [and] Ha; clear Ha.
  apply mult_le_compat.
  apply le_trans with (size_Z (n k)).
  apply size_nat_monotonic; apply lt_le_weak; trivial.
  apply Zabs_nat_lt; omega.  
  apply lt_le_weak; apply n_poly_spec.
  apply lt_le_weak; apply n_poly_spec.
 Qed.

End Z_nZ.


Module Type GUILLOU_QUISQUATER_PARAMETERS (ZnP : Z_nZ_PARAMETERS).

 Import ZnP.

 Open Scope Z_scope.

 Parameters p q e : nat -> Z.

 Parameter p_prime : forall k, prime (p k).

 Parameter q_prime : forall k, prime (q k).

 Parameter pq_distinct : forall k, (p k) <> (q k). 
 
 Parameter rsa_modulus : forall k,  (n k) = (p k) * (q k).

 Parameter rsa_exponent : forall k, rel_prime (e k) ((p k - 1) * (q k - 1)).

 Parameter e_poly : polynomial.

 Parameter e_poly_spec : forall k, (size_Z (e k) < peval e_poly k)%nat.
 
End GUILLOU_QUISQUATER_PARAMETERS.


Module Guillou_Quisquater_Parameters_Properties 
 (ZnP:Z_nZ_PARAMETERS) (SP:GUILLOU_QUISQUATER_PARAMETERS ZnP).

 Import SP.
 Import ZnP.
 
 Lemma n_pos : forall k, (0 < Zabs_nat (n k))%nat.
 Proof.
  intro k.
  assert (Hp:=n_pos k).
  change 0%nat with (Zabs_nat 0).  
  apply Zabs_nat_lt.
  omega.
 Qed.

End Guillou_Quisquater_Parameters_Properties.


Module Guillou_Quisquater_Homomorphism 
 (ZnP:Z_nZ_PARAMETERS) (GQP:GUILLOU_QUISQUATER_PARAMETERS ZnP).

 Import GQP.

 Module G := (Z_nZ ZnP).
 Module H := G.

 Module HP := Group_Properties H.
 Import HP.

 Module GQPP :=  Guillou_Quisquater_Parameters_Properties ZnP GQP.
 Import GQPP.
 
 Open Scope nat_scope.

 Definition phi k (x:G.t k) : (H.t k) := H.powZ x (GQP.e k).

 Definition cost_phi k (x:G.t k) := 
   (G.cost_pow x (GQP.e k) * (size_Z (GQP.e k)))%nat.

 Definition cost_phi_poly : polynomial := pmult G.cost_pow_poly e_poly.

 Lemma cost_phi_poly_spec : forall k (x:G.t k),
  @cost_phi k x <= peval cost_phi_poly k.
 Proof.
  intros k (a,b); unfold cost_phi, cost_phi_poly; simpl.
  rewrite pmult_spec.
  apply mult_le_compat.
  apply G.cost_pow_poly_spec.
  apply lt_le_weak.
  apply e_poly_spec.
 Qed.

 Lemma phi_homo : forall k (x y:G.t k), 
  phi (G.mul x y) = H.mul (phi x) (phi y).
 Proof.
  intros k x y; unfold phi; simpl.
  rewrite HP.powZ_mul_distr.
  trivial.
 Qed.

 (* [phi] is a special homomorphism *)
 Definition special_v k := (e k).
  
 Lemma special_v_spec : forall k, special_v k <> 0%Z.
 Proof.
  intro k; unfold special_v.
  intro Heq.
  generalize (rsa_exponent k).
  intros.
  rewrite Heq in H.
  generalize (not_rel_prime_0 ((p k - 1) * (q k - 1))).
  intros.
  destruct H0;[ | trivial].
  assert (Hq :=prime_ge_2 _ (q_prime k)).
  assert (Hp :=prime_ge_2 _ (p_prime k)).
  assert (Hpq := @pq_distinct k).
  apply Zle_lt_trans with ((1 * 1)%Z);[ omega | ].
  destruct (Z_dec (p k) (q k)).
  destruct s.
  apply Zmult_lt_compat2; split; omega.
  rewrite (Zmult_comm (p k - 1) (q k - 1)).
  apply Zmult_lt_compat2; split; omega.
  elimtype False; omega.
 Qed.
 
 Definition special_v_poly : polynomial := e_poly.

 Lemma size_nat_special_v : forall k, 
  size_nat (Zabs_nat (special_v k)) <= peval special_v_poly k. 
 Proof.
  intro k; unfold special_v.
  apply lt_le_weak.
  apply e_poly_spec.
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

End Guillou_Quisquater_Homomorphism.


(** Instantiation *)
Declare Module ZnP : Z_nZ_PARAMETERS.
Declare Module GQP : GUILLOU_QUISQUATER_PARAMETERS ZnP.

Module HM := Guillou_Quisquater_Homomorphism ZnP GQP.
Module CS := Largest_Challenge_Set HM.G HM.H HM.

Module S := SigmaPhi.SigmaPhi HM.G HM.H HM CS.
