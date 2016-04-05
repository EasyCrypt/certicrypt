(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** FFS.v : Feige Fiat Shamir protocol *)

Require Import SigmaPhi.
Require Import FilterMap.
Require Import PrimeLib.

Set Implicit Arguments.


Module Type ZnZ_PARAMETERS.

 Open Scope Z_scope.

 Parameter n : nat -> Z.

 Parameter n_pos : forall k, 1 < n k.
 
 Parameter n_poly : polynomial.
 
 Parameter n_poly_spec : forall k, (size_Z (n k) < peval n_poly k)%nat.
 
End ZnZ_PARAMETERS.


(** The multiplicative group of integers module an integer n,
    i.e. the integers in {1,..,n-1} relative prime to n.
    This is noted as Zn/Z or sometimes Zn^* 
*)
Module ZnZ (P:ZnZ_PARAMETERS) <: GROUP.

 Import P.

 (* We ask just for 0 <= x to ease the proofs, 
    but note that 0 is never relative prime to n *)
 Definition P k (x:Z) : bool :=
  Zle_bool 0 x && Zlt_bool x (n k) && Zeq_bool (Zgcd x (n k)) 1.

 Lemma eq_P : forall k x (H1 H2:P k x), H1 = H2.
 Proof.
  intros; apply eq_proofs_unicity.
  intros a b; case (bool_dec a b); auto.
 Qed.

 Lemma P_prop : forall k x, P k x <-> 0 <= x < n k /\ Zis_gcd x (n k) 1.
 Proof.
  unfold P; split; intros.

  apply andb_prop in H; destruct H.  
  apply andb_prop in H; destruct H.  
  split.
  split.
  apply Zle_bool_imp_le; trivial.
  apply <- Zlt_is_lt_bool; trivial.
  apply Zeq_is_eq_bool in H0; rewrite <- H0; apply Zgcd_is_gcd.

  decompose [and] H.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply Zle_imp_le_bool; trivial.
  apply -> Zlt_is_lt_bool; trivial.    
  apply -> Zeq_is_eq_bool; apply Zis_gcd_gcd; auto with zarith.
 Qed.

 Definition t k := {x : Z | P k x}.

 Definition elems k : list (t k) := 
  filter_map (P k) (@exist _ _) (map (fun x => Z_of_nat x) 
   (seq 0 (Zabs_nat (n k)))).

 Lemma elems_not_nil : forall k, elems k <> nil.
 Proof.
  intro k; unfold elems.

  assert (Hn := n_pos k).  
  assert (P k 1).
  unfold P.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  trivial.
  apply -> Zlt_is_lt_bool; trivial.    
  apply -> Zeq_is_eq_bool; apply <- Zgcd_1_rel_prime; apply rel_prime_1.
 
  assert (H0:0 <= 1 < n k) by omega.
  apply Zabs_nat_lt in H0.
  induction (Zabs_nat (n k)).
  elimtype False; omega.

  assert (In 1 (map (fun x : nat => Z_of_nat x) (seq 0 (S n0)))).
  change 1 with (Z_of_nat (Zabs_nat 1)).
  apply in_map.
  apply le_In_seq.
  split; [ omega | ].
  apply le_trans with 2%nat; [ trivial | ].
  rewrite <- plus_n_O; trivial.

  intro Heq.
  apply In_filter_map with (A:=Z) (f:=@exist _ _) (H:=H) in H1.
  rewrite Heq in H1; inversion H1.
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
  rewrite <- plus_n_O.
  apply Zabs_nat_lt.
  split.
  omega.
  apply <- Zlt_is_lt_bool; trivial.    

  apply P_prop in H.
  rewrite inj_Zabs_nat, Zabs_eq; trivial.
  omega.
 Qed.

 Lemma elems_nodup : forall k, NoDup (elems k).
 Proof.
  intro k; unfold elems.
  apply NoDup_filter_map_inj.
  intros x y H1 H2 H; injection H; trivial.
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
  exists ((a * b) mod n k).
  apply P_prop in Ha; destruct Ha as [[ Ha1 Ha2 ] Ha3 ].  
  apply P_prop in Hb; destruct Hb as [[ Hb1 Hb2 ] Hb3 ].
  apply <- P_prop; split.
  apply Z_mod_lt; omega.
  apply rel_prime_mod.
  omega.
  apply rel_prime_sym; apply rel_prime_mult; apply rel_prime_sym; trivial.
 Defined.

 Definition inv : forall k, t k -> t k.
  intros k (a,Ha).
  assert (Hn := n_pos k).
  exists ((fst (fst (eeuclid a (n k)))) mod (n k)).  
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
  apply Z_mod_lt; omega.

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

End ZnZ.


Module Type FFS_PARAMETERS.

 Declare Module P : ZnZ_PARAMETERS. 

 Export P.

 Parameters p q : nat -> Z.

 Parameter p_prime : forall k, prime (p k).

 Parameter q_prime : forall k, prime (q k).

 Parameter p_blum : forall k, p k mod 4 = 3.
  
 Parameter q_blum : forall k, q k mod 4 = 3.

 Parameter pq_distinct : forall k, p k <> q k. 

 Parameter rsa_modulus : forall k, n k = p k * q k.
 
End FFS_PARAMETERS.


Module FFS_G (FFSP:FFS_PARAMETERS) <: GROUP.

 Import FFSP.

 Module G := ZnZ P.
 
 Module GP := Group_Properties G.
 Import GP.

 Definition t k := (bool * G.t k)%type.

 Definition elems k : list (t k) := 
  map (fun x => (true,x)) (G.elems k) ++
  map (fun x => (false,x)) (G.elems k).

 Lemma map_nil : forall A B (f:A -> B) (l:list A), map f l = nil -> l = nil.
 Proof.
  destruct l; [trivial | intro; discriminate].
 Qed.

 Lemma elems_not_nil : forall k, elems k <> nil.
 Proof.
  intro k; unfold elems.
  intro H; apply app_eq_nil in H.
  destruct H as [H _].
  apply map_nil in H.  
  elim (@G.elems_not_nil k H).
 Qed.
  
 Lemma elems_full : forall k (x:t k), In x (elems k).
 Proof.
  intros k (b,x).
  apply in_or_app.
  case b; [left | right]; apply in_map; apply G.elems_full.
 Qed.

 Lemma elems_nodup : forall k, NoDup (elems k).
 Proof.
  intro k.
  apply NoDup_app.
  apply NoDup_map_inj.
  intros x y _ _ H; injection H; trivial.
  apply G.elems_nodup.
  apply NoDup_map_inj.
  intros x y _ _ H; injection H; trivial.
  apply G.elems_nodup.

  intros (b,x) Hf Ht.
  apply in_map_iff in Ht; destruct Ht as [(b1,x1) [Ht _]].
  apply in_map_iff in Hf; destruct Hf as [(b2,x2) [Hf _]].
  injection Ht; injection Hf.
  intros; subst; discriminate. 
 Qed.


 (** Equality is decidable *)
 Definition eqb k (x y:t k) :=
  match x, y with
   | (b1,x), (b2,y) => Bool.eqb b1 b2 && G.eqb x y
  end.

 Lemma eqb_spec : forall k (x y:t k), if eqb x y then x = y else x <> y.
 Proof.
  intros k (b1,x) (b2,y).
  unfold eqb.
  generalize (G.eqb_spec x y).
  generalize (Bool.eqb_eq b1 b2).
  case b1; case b2; simpl; intros; try discriminate;
  destruct (G.eqb x y); simpl.
  rewrite H0; trivial.
  intro Heq; injection Heq; intros; auto.
  rewrite H0; trivial.
  intro Heq; injection Heq; intros; auto.
 Qed.

 (** Identity element *)
 Definition e k : t k := (true, G.e k).

 (** Operations: product, inverse *)

 Definition mul k (x y:t k) : t k :=
  match x, y with
  | (true,x),  (true,y)  => (true, G.mul x y)
  | (false,x), (false,y) => (true, G.mul x y)
  | (_,x), (_,y) => (false, G.mul x y)
  end.
 
 Definition inv k (x:t k) : t k := 
  match x with 
  | (true,x)  => (true, G.inv x)
  | (false,x) => (false, G.inv x)
  end.


 (** Specification *) 
 Lemma mul_assoc : forall k (x y z:t k), mul x (mul y z) = mul (mul x y) z.
 Proof.
  intros k (b1,x) (b2,y) (b3,z); unfold mul.
  case b1; case b2; case b3;
  rewrite G.mul_assoc; trivial.
 Qed.

 Lemma mul_e_l : forall k (x:t k), mul (e k) x = x.
 Proof.
  intros k (b,x); unfold mul, e.
  case b; rewrite G.mul_e_l; trivial.  
 Qed.

 Lemma mul_inv_l : forall k (x:t k), mul (inv x) x = e k.
 Proof.
  intros k (b,x); unfold mul, inv, e.
  case b; rewrite G.mul_inv_l; trivial.
 Qed.

 Lemma mul_comm : forall k (x y:t k), mul x y = mul y x.
 Proof.
  intros k (b1,x) (b2,y); unfold mul.
  case b1; case b2; rewrite G.mul_comm; trivial.
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

 Definition order_poly : polynomial := pplus 1 n_poly.

 Lemma order_size_nat : forall k,
  size_nat (length (elems k)) < peval order_poly k. 
 Proof.
  intro k.
  unfold elems.
  rewrite app_length, map_length, map_length.
  
  unfold order_poly; rewrite pplus_spec, pcst_spec.
  eapply le_lt_trans.
  apply size_nat_plus_max; trivial.
  apply lt_n_S; apply G.order_size_nat.
 Qed.

 Definition cost_mul k (x y:t k) : nat := G.cost_mul (snd x) (snd y).

 Definition cost_pow k (x:t k) (m:Z) : nat := G.cost_pow (snd x) m.

 Definition cost_inv k (x:t k) : nat := G.cost_inv (snd x).

 Definition cost_mul_poly : polynomial := n_poly. 
 Definition cost_pow_poly : polynomial := pmult n_poly n_poly.
 Definition cost_inv_poly : polynomial := pmult n_poly n_poly.

 Lemma cost_mul_poly_spec : forall k (x y:t k),
  cost_mul x y <= peval cost_mul_poly k.
 Proof.
  destruct x; destruct y.
  apply G.cost_mul_poly_spec.
 Qed.

 Lemma cost_pow_poly_spec : forall k (x:t k) (m:Z),
  cost_pow x m <= peval cost_pow_poly k.
 Proof.
  destruct x.
  apply G.cost_pow_poly_spec.
 Qed.

 Lemma cost_inv_poly_spec : forall k (x:t k),
  cost_inv x <= peval cost_inv_poly k.
 Proof.
  destruct x.
  apply G.cost_inv_poly_spec.
 Qed.

End FFS_G.


Module FFS_Homomorphism (FFSP:FFS_PARAMETERS).

 Module G := FFS_G FFSP.
 Module H := G.G.
 
 Import FFSP. 

 Open Scope nat_scope.

 Definition minusone k : H.t k.
  intro k.
  exists (Zpred (n k)).
  assert (Hn := n_pos k).
  apply <- H.P_prop; split.
  split.
  apply Zgt_0_le_0_pred; auto with zarith.
  apply Zlt_pred.

  constructor.
  apply Zone_divide.
  apply Zone_divide.
  intros.
  replace 1%Z with (n k - Zpred (n k))%Z.
  apply Zdivide_minus_l; trivial.  
  unfold Zpred; auto with zarith.
 Defined.

 Lemma minusone_square : forall k, H.mul (minusone k) (minusone k) = H.e k.
 Proof.
  intro k.  
  unfold G.G.mul, G.G.e, minusone.
  match goal with
   |- exist _ ?a ?Ha = exist _ ?b ?Hb => 
    generalize Ha Hb; assert (H:a = b)
  end.  
  unfold Zpred.
  replace  ((n k + -1) * (n k + -1))%Z with 
           (1 + (n k - 2) * n k)%Z by ring.
  rewrite Z_mod_plus_full.
  apply Zmod_1_l.
  apply n_pos.
  rewrite H; intros p1 p2; rewrite (G.G.eq_P _ _ p1 p2); trivial.
 Qed.  

 Definition phi k (x:G.t k) : (H.t k) := 
  match x with
  | (true,x)  => H.mul x x
  | (false,x) => H.mul (minusone k) (H.mul x x)
  end.

 Definition cost_phi k (x:G.t k) := 3 * G.cost_mul x x.

 Definition cost_phi_poly : polynomial := pmult 3 G.cost_mul_poly.

 Lemma cost_phi_poly_spec : forall k (x:G.t k),
  @cost_phi k x <= peval cost_phi_poly k.
 Proof.
  intros k x; unfold cost_phi, cost_phi_poly.
  rewrite pmult_spec, pcst_spec.  
  apply mult_le_compat_l.
  apply G.cost_mul_poly_spec.
 Qed.

 Lemma phi_homo : forall k (x y:G.t k), 
  phi (G.mul x y) = H.mul (phi x) (phi y).
 Proof.
  intros k (b1,x) (b2,y); unfold phi.
  unfold G.mul.
 
  assert (G.G.mul (G.G.mul x y) (G.G.mul x y) = 
          G.G.mul (G.G.mul x x) (G.G.mul y y)).
  rewrite G.G.mul_assoc, (G.G.mul_comm _ x).
  repeat rewrite <- G.G.mul_assoc.
  trivial.

  case b1; case b2.
  trivial.

  rewrite H.
  rewrite (G.G.mul_assoc _ (minusone k)).
  rewrite (G.G.mul_comm _ (minusone k)).
  rewrite G.G.mul_assoc.
  trivial.

  rewrite H.
  rewrite (G.G.mul_assoc (minusone k)).
  trivial.
  
  rewrite H.
  rewrite (G.G.mul_assoc _ (minusone k)).
  rewrite (G.G.mul_comm _ (minusone k)).
  rewrite (G.G.mul_assoc _ (minusone k)).
  rewrite minusone_square.
  rewrite G.G.mul_e_l.
  trivial.
 Qed.

 (* [phi] is a special homomorphism *)
 Definition special_v (k:nat) := 2%Z.
  
 Lemma special_v_spec : forall k, special_v k <> 0%Z.
 Proof.
  intro k; unfold special_v; omega.
 Qed.
 
 Definition special_v_poly : polynomial := 2.

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

 Definition special_u k (x:H.t k) : G.t k := (true,x).
 
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
  rewrite (G.G.mul_comm _ (G.G.e k)).
  rewrite G.G.mul_e_l.
  trivial.
 Qed.

End FFS_Homomorphism.


(** Instantiation *)
Declare Module FFSP : FFS_PARAMETERS.

Module HM := FFS_Homomorphism FFSP.
Module CS := Largest_Challenge_Set HM.G HM.H HM.

Module S := SigmaPhi.SigmaPhi HM.G HM.H HM CS.
