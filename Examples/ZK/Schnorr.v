(* Schnorr.v : Schnorr protocol *)

Require Import SigmaPhi.
Require Import FilterMap.
Require Import LtIrrelevance.

Set Implicit Arguments.


Module Type SCHNORR_PARAMETERS.

 Open Scope Z_scope.

 Parameters p q g : nat -> Z.

 Parameter p_prime : forall k, prime (p k).

 Parameter q_prime : forall k, prime (q k).

 Parameter q_divides_pred_p : forall k, (q k | p k - 1).

 Parameter p_poly : polynomial.

 Parameter p_poly_spec : forall k, (size_Z (p k) < peval p_poly k)%nat.

 Parameter g_range : forall k, 1 < g k < p k.

 Parameter g_order : forall k, g k ^ q k mod p k = 1.
 
End SCHNORR_PARAMETERS.


Module Schnorr_Parameters_Properties (SP:SCHNORR_PARAMETERS).

 Export SP.

 Lemma q_pos : forall k, (0 < Zabs_nat (q k))%nat.
 Proof.
  intro k.
  assert (H:=prime_ge_2 _ (q_prime k)).
  change 0%nat with (Zabs_nat 0).  
  apply Zabs_nat_lt.
  auto with zarith.
 Qed.

 Lemma q_range : forall k, 2 <= q k < p k.
 Proof.
  intro k.
  assert (Hq:=prime_ge_2 _ (q_prime k)).
  assert (Hp:=prime_ge_2 _ (p_prime k)).
  assert (H:=q_divides_pred_p k).
  apply Zdivide_le in H; auto with zarith.
 Qed.

 Lemma q_size : forall k, (size_Z (q k) < peval p_poly k)%nat.
 Proof.
  intro k.
  apply le_lt_trans with (2:=p_poly_spec k).
  apply size_nat_monotonic.
  apply Zabs_nat_le.
  generalize (q_range k).  
  auto with zarith.
 Qed.

End Schnorr_Parameters_Properties.


(** The Zq group *)
Module Schnorr_G (SP:SCHNORR_PARAMETERS) <: GROUP.

 Module SPP := Schnorr_Parameters_Properties SP.
 Import SPP.

 Open Scope nat_scope.

 Definition t k := {x : nat | x < Zabs_nat (q k)}.
 
 (** The group is finite and non-empty *)
 
 Definition elems_aux n : list {x | x < n} -> list {x | x < S n} :=
  map (fun s : {x | x < n} => 
   match s with 
    exist x H => exist (fun x => x < S n) x (le_S (S x) n H) 
   end).

 Fixpoint elems' n : list {x | x < n} :=
  match n return list {x | x < n} with
  | O => nil
  | S n0 => exist (fun x => x < S n0) n0 (le_n (S n0)) :: elems_aux (elems' n0)
  end.

 Definition elems k := elems' (Zabs_nat (q k)).

 Lemma elems_not_nil : forall k, elems k <> nil.
 Proof.
  intro k; unfold elems, elems'.
  assert (Hq:=q_pos k).
  induction (Zabs_nat (q k)).
  omega.
  discriminate.
 Qed.

 Lemma elems_full : forall k (x:t k), In x (elems k).
 Proof.
  unfold elems, elems', t; intro k.
  induction (Zabs_nat (q k)); destruct x.
  elimtype False; omega.
  inversion l; subst.
   constructor.
   rewrite (lt_eq l (le_n (S n))); trivial.
  
   constructor 2.
   rewrite (lt_eq l (le_S (S x) n H0)); clear l.
   assert (H:=IHn (exist _ x H0)); clear IHn.
   apply in_map with (f:=
    (fun s : {x | x < n} => 
     match s with 
      exist x H => exist (fun x => x < S n) x (le_S (S x) n H) 
     end)) in H.
   trivial.
 Qed.

 Lemma elems_nodup : forall k, NoDup (elems k).
 Proof.
  intro k; unfold elems, elems'.
  induction (Zabs_nat (q k)); constructor.

  clear IHn; intro.
  unfold elems_aux in H.
  rewrite in_map_iff in H; destruct H as [x [H0 H1] ]; destruct x.
  injection H0; intro; subst; clear H0.
  omega.

  apply NoDup_map_inj with (2:=IHn).
  intros x y _ _ H; destruct x; destruct y; inversion H; subst.
  rewrite (lt_eq l l0); trivial. 
 Qed.


 (** Equality is decidable *)
 Definition eqb k (x y:t k) :=
  match x, y with
   | exist n _, exist m _ => nat_eqb n m
  end.

 Lemma eqb_spec : forall k (x y:t k), if eqb x y then x = y else x <> y.
 Proof.
  intros k (a,Ha) (b,Hb).
  unfold eqb.
  generalize (nat_eqb_spec a b); case (nat_eqb a b); intro Heq.
  subst; rewrite (lt_eq Hb Ha); trivial.
  intro H; elim Heq; injection H; trivial. 
 Qed.

 (** Identity element *)
 Definition e k : t k := exist _ 0 (q_pos k).

 (** Operations: product, inverse *)
 Definition mul : forall k, t k -> t k -> t k. 
  intros k (a,Ha) (b,Hb).
  case (le_gt_dec (Zabs_nat (q k)) (a + b)); intro Hlt.  
   exists (a + b - (Zabs_nat (q k))); auto with *.
   exists (a + b); exact Hlt.
 Defined.  

 Definition inv : forall k, t k -> t k.
  intros k (a,Ha).
  case (eq_nat_dec a 0); intro Heq.
  exists 0; apply q_pos.  
  exists (Zabs_nat (q k) - a); auto with *.
 Defined.

 (** Specification *)

 Ltac prove_mul_eq :=
  repeat match goal with 
   |- context [le_gt_dec ?x ?y] => case (le_gt_dec x y)
   | _ => intros; 
     (elimtype False; omega) ||
     match goal with
      |- exist _ ?a ?Ha = exist _ ?b ?Hb => 
        generalize Ha Hb; assert (H:a = b) by omega; rewrite H;
        intros p1 p2; rewrite (lt_eq p1 p2); trivial
     end
  end.  

 Lemma mul_assoc : forall k (x y z:t k), mul x (mul y z) = mul (mul x y) z.
 Proof.
  intros k (a,Ha) (b,Hb) (c,Hc); unfold mul.  
  prove_mul_eq.
 Qed.

 Lemma mul_e_l : forall k (x:t k), mul (e k) x = x.
 Proof.
  intros k (a,Ha); unfold e, mul.
  prove_mul_eq.
 Qed.

 Lemma mul_inv_l : forall k (x:t k), mul (inv x) x = e k.
 Proof.
  intros k (a,Ha); unfold e, mul, inv.
  case (eq_nat_dec a 0); intro; subst; prove_mul_eq.
 Qed.

 Lemma mul_comm : forall k (x y:t k), mul x y = mul y x.
 Proof.
  intros k (a,Ha) (b,Hb); unfold mul.
  prove_mul_eq.
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
 Definition order_poly : polynomial := p_poly.

 Lemma order_size_nat : forall k,
  size_nat (length (elems k)) < peval order_poly k.
 Proof.
  intro k.
  replace (length (elems k)) with (Zabs_nat (q k)).
  apply q_size.
  unfold elems; induction (Zabs_nat (q k)).
  trivial.  
  rewrite IHn at 1.
  simpl; unfold elems_aux; rewrite map_length; trivial.  
 Qed.

 Definition cost_mul k (x y:t k) : nat := size_nat (proj1_sig y).

 Definition cost_pow k (x:t k) (n:Z) : nat :=
  size_nat (proj1_sig x) * (size_Z (q k)).

 Definition cost_inv k (x:t k) : nat := size_nat (proj1_sig x).

 Definition cost_mul_poly : polynomial := p_poly. 
 Definition cost_pow_poly : polynomial := pmult p_poly p_poly.
 Definition cost_inv_poly : polynomial := p_poly.

 Lemma cost_mul_poly_spec : forall k (x y:t k),
  cost_mul x y <= peval cost_mul_poly k.
 Proof.
  intros k x (b,Hb).
  unfold cost_mul; simpl.
  apply le_trans with (size_Z (q k)).
  apply size_nat_monotonic; apply lt_le_weak; trivial.
  apply lt_le_weak; apply q_size.
 Qed.

 Lemma cost_pow_poly_spec : forall k (x:t k) (n:Z),
  cost_pow x n <= peval cost_pow_poly k.
 Proof.
  intros k (a,Ha) n.
  unfold cost_pow, cost_pow_poly; simpl.
  rewrite pmult_spec.
  apply mult_le_compat.
  apply le_trans with (size_Z (q k)).
  apply size_nat_monotonic; apply lt_le_weak; trivial.
  apply lt_le_weak; apply q_size.
  apply lt_le_weak; apply q_size.
 Qed.

 Lemma cost_inv_poly_spec : forall k (x:t k),
  cost_inv x <= peval cost_inv_poly k.
 Proof.
  intros k (a,Ha).
  unfold cost_inv; simpl.
  apply le_trans with (size_Z (q k)).
  apply size_nat_monotonic; apply lt_le_weak; trivial.
  apply lt_le_weak; apply q_size.
 Qed.

End Schnorr_G.


(** An Schnorr group *)
Module Schnorr_H (SP:SCHNORR_PARAMETERS) <: GROUP. 

 Module SPP := Schnorr_Parameters_Properties SP.
 Import SPP.

 Definition P k x : bool :=
  leb 1 x && negb (leb (Zabs_nat (p k)) x) && Zeq_bool (Z_of_nat x^q k mod p k) 1.

 Lemma eq_P : forall k x (H1:P k x) (H2:P k x), H1 = H2.
 Proof.
  intros.
  apply eq_proofs_unicity.
  intros a b; case (bool_dec a b); auto.
 Qed.

 Lemma P_prop : forall k x, P k x <->
  (0 < x < Zabs_nat (p k))%nat /\
  Z_of_nat x ^ q k mod p k = 1.
 Proof.
  unfold P; split; intros.

  apply andb_prop in H; destruct H.
  apply andb_prop in H; destruct H; split.
  
  fold (is_true (negb (leb (Zabs_nat (p k)) x))) in H1.
  rewrite is_true_negb_false in H1.
  apply leb_complete_conv in H1.
  apply leb_complete in H.
  auto with zarith.
  rewrite Zeq_is_eq_bool; trivial.

  destruct H.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply leb_correct; auto with zarith.
  apply <- is_true_negb_false.
  apply leb_correct_conv; auto with zarith.
  rewrite <- Zeq_is_eq_bool; trivial.
 Qed.

 Definition t k := {x | P k x}.
  
 Definition elems k : list (t k) := 
  filter_map (P k) (@exist _ _) (seq 0 (Zabs_nat (p k))).

 Lemma elems_not_nil : forall k, elems k <> nil.
 Proof.
  intro k; unfold elems.

  assert (Hq:(2 <= Zabs_nat (p k))%nat).
  change 2%nat with (Zabs_nat 2).
  apply Zabs_nat_le; auto using prime_ge_2, p_prime with zarith.

  assert (Hg:(1 < Zabs_nat (g k) < Zabs_nat (p k))%nat).
  destruct (g_range k).
  change 1%nat with (Zabs_nat 1).
  split; apply Zabs_nat_lt; auto with zarith.

  assert (P k (Zabs_nat (g k))).
  unfold P.
  destruct (g_range k).
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply leb_correct; auto with zarith.
  apply fold_is_true.
  rewrite is_true_negb_false.
  rewrite leb_correct_conv; trivial.
  auto with zarith.
  rewrite <- Zeq_is_eq_bool.
  rewrite inj_Zabs_nat, Zabs_eq, g_order; auto with zarith.
  
  induction (Zabs_nat (p k)); [ omega | ].
  
  assert (In (Zabs_nat (g k)) (seq 0 (S n))).
  apply le_In_seq; auto with zarith.

  intro Heq.
  apply In_filter_map with (A:=nat) (f:=@exist _ _) (H:=H) in H0.
  rewrite Heq in H0.
  inversion H0.
 Qed.

 Lemma elems_full : forall k (x:t k), In x (elems k).
 Proof.
  intros k (x,H).
  apply In_filter_map.
  apply le_In_seq.
  apply andb_prop in H; destruct H.
  apply andb_prop in H; destruct H.
  apply is_true_negb_false in H1. 
  apply leb_complete_conv in H1.
  auto with zarith.
 Qed.

 Lemma elems_nodup : forall k, NoDup (elems k).
 Proof.
  intro k; unfold elems.
  apply NoDup_filter_map_inj.
  intros x y H1 H2 H; injection H; trivial.
  apply NoDup_seq.
 Qed.


 (** Equality is decidable *)
 Definition eqb k (x y:t k) :=
  match x, y with
   | exist n _, exist m _ => nat_eqb n m
  end.

 Lemma eqb_spec : forall k (x y:t k), if eqb x y then x = y else x <> y.
 Proof.
  intros k (a,Ha) (b,Hb).
  unfold eqb.
  generalize (nat_eqb_spec a b); case (nat_eqb a b); intro Heq.
  subst; rewrite (eq_P _ _ Hb Ha); trivial.
  intro H; elim Heq; injection H; trivial. 
 Qed.

 (** Identity element *)
 Definition e k : t k.
 intro k.
 refine (exist _ 1%nat _).
 apply <- P_prop; split.
 change 1%nat with (Zabs_nat 1).
 assert (Hp:=prime_ge_2 _ (p_prime k)).
 split; auto.
 apply Zabs_nat_lt; auto with zarith.

 simpl; rewrite Zpower_1.
 apply Zmod_1_l.
 generalize (prime_ge_2 _ (p_prime k)); auto with zarith.
 generalize (prime_ge_2 _ (q_prime k)); auto with zarith.
 Defined. 

 (** Operations: product, inverse *)

 Definition mul : forall k, t k -> t k -> t k. 
  intros k (a,Ha) (b,Hb).
  assert (Hp:=prime_ge_2 _ (p_prime k)).
  assert (Hq:=prime_ge_2 _ (q_prime k)).
  refine (exist _ (Zabs_nat (Z_of_nat (a * b) mod p k)) _)%Z.
  apply P_prop in Ha; destruct Ha as [Ha1 Ha2].
  apply P_prop in Hb; destruct Hb as [Hb1 Hb2].
  apply <- P_prop; split.
  split.
  
  apply neq_O_lt.
  intro Heq.
  apply f_equal with (f:=fun x => (Z_of_nat x ^ q k) mod p k) in Heq.
  rewrite inj_Zabs_nat in Heq.
  simpl in Heq.
  rewrite Zabs_eq in Heq.  
  rewrite Zmod_power in Heq.
  rewrite inj_mult in Heq. 
  rewrite Zmult_power_distr in Heq.
  rewrite Zmult_mod in Heq.
  rewrite Ha2, Hb2 in Heq.
  rewrite Zmod_1_l in Heq; [ | auto with zarith].
  rewrite Zpower_0 in Heq; [ | auto with zarith].  
  discriminate Heq.

  generalize (Z_mod_lt (Z_of_nat (a * b)) (p k)); auto with zarith.

  apply Zabs_nat_lt.
  apply Z_mod_lt; auto with zarith.
 
  rewrite inj_Zabs_nat, Zabs_eq.
  rewrite Zmod_power, inj_mult, Zmult_power_distr, Zmult_mod, Ha2, Hb2.
  apply Zmod_1_l; auto with zarith.

  generalize (Z_mod_lt (Z_of_nat (a * b)) (p k)); auto with zarith.
 Defined. 

 Definition inv : forall k, t k -> t k.
  intros k (a,Ha).
  refine 
   (exist (P k)
    (if Z_le_dec 0 (fst (fst (eeuclid (Z_of_nat a) (p k))))
     then Zabs_nat (fst (fst (eeuclid (Z_of_nat a) (p k)))) 
     else Zabs_nat (fst (fst (eeuclid (Z_of_nat a) (p k))) + p k)) _).

  apply P_prop in Ha; destruct Ha as [Hlt Hmod].

  destruct (eeuclid_bound (Z_of_nat a) (p k) (Zabs (p k))) as [H2 H3].

  rewrite <- inj_Zabs_nat.
  rewrite <- inj_Zabs_nat.
  apply inj_le.
  rewrite Zabs_nat_Z_of_nat; auto with zarith.
  apply Zle_refl.

  assert (H1:=eeuclid_spec (Z_of_nat a) (p k)).
  assert (Hp:=prime_ge_2 _ (p_prime k)).
  assert (Hq:=prime_ge_2 _ (q_prime k)).

  assert (Hgcd:Zis_gcd (Z_of_nat a) (p k) 1).
   apply Zis_gcd_prime.
   apply p_prime.
   auto with zarith.
   destruct Hlt.
   apply inj_lt in H0.
   split.
   auto with zarith.
   rewrite inj_Zabs_nat, Zabs_eq in H0; auto with zarith.

  destruct (eeuclid (Z_of_nat a) (p k)) as ((u, v), d); simpl in *.
  destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.
  case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
  apply <- P_prop.
  case (Z_le_dec 0 u); intro Hu; clear H5 H6 Hgcd; subst.

  assert (Hneq:u <> p k).
  intro Heq; subst.
  rewrite Zmult_comm, <- Zmult_plus_distr_l, Zmult_comm in H.
  apply Zmult_1_inversion_l in H; auto with zarith.

  split.
  split.
  apply neq_O_lt; intro Heq.
  apply f_equal with (f:=Z_of_nat) in Heq.
  rewrite inj_Zabs_nat, Zabs_eq in Heq; trivial.
  simpl in Heq.
  rewrite <- Heq, Zmult_0_l, Zplus_0_l in H.
  generalize (prime_ge_2 _ (p_prime k)).
  case (Zmult_1_inversion_l _ _ H); intros; subst; auto with zarith.

  apply Zabs_nat_lt; rewrite Zabs_eq, Zabs_eq in H2; auto with zarith.
  
  rewrite inj_Zabs_nat, Zabs_eq; [ | trivial].
  apply f_equal with (f:=fun x => (x mod (p k)) ^ (q k) mod (p k)) in H.
  rewrite Zmod_1_l, Z_mod_plus_full in H; [ | auto with zarith].
  rewrite Zmod_power, Zmult_power_distr in H.
  rewrite Zmult_mod, Hmod, Zmult_1_r, Zmod_mod, Zpower_1 in H; [ | auto with zarith].
  rewrite Zmod_1_l in H; auto with zarith.

  assert (Hneq:- u <> p k).
  intro Heq; rewrite <- Heq in H.
  rewrite Zmult_comm, <- Zmult_opp_comm, <- Zmult_plus_distr_l, Zmult_comm in H.
  apply Zmult_1_inversion_l in H; auto with zarith.

  assert (-p k < u < p k).
  split; [ | auto with zarith]. 
  rewrite Zabs_non_eq in H2; [ | auto with zarith].
  rewrite Zabs_eq in H2; auto with zarith. 
   
  split.
  split.
  assert (0 < u + p k) by omega.
  apply inj_lt_rev.
  rewrite inj_Zabs_nat, Zabs_eq; auto with zarith.
  apply Zabs_nat_lt; omega.

  rewrite inj_Zabs_nat, Zabs_eq; [ | auto with zarith].
  apply f_equal with (f:=fun x => (x mod (p k)) ^ (q k) mod (p k)) in H.
  rewrite Zmod_1_l, Z_mod_plus_full in H; [ | auto with zarith].
  rewrite Zmod_power, Zmult_power_distr in H.
  rewrite Zmult_mod, Hmod, Zmult_1_r, Zmod_mod, Zpower_1 in H; [ | auto with zarith].
  rewrite Zmod_1_l in H; auto with zarith.
  rewrite <- Zmod_power.
  
  rewrite <- (Zmult_1_l (p k)) at 1.
  rewrite Z_mod_plus.
  rewrite Zmod_power; trivial.
  auto with zarith.
 Defined.


 (** Specification *) 
 Lemma mul_assoc : forall k (x y z:t k), mul x (mul y z) = mul (mul x y) z.
 Proof.
  intros k (a,Ha) (b,Hb) (c,Hc); unfold mul.
  match goal with
   |- exist _ ?a ?Ha = exist _ ?b ?Hb => 
    generalize Ha Hb; assert (H:a = b)
  end.
  apply f_equal.
  rewrite <- (Zabs_nat_Z_of_nat a).
  rewrite <- (Zabs_nat_Z_of_nat c).
  repeat rewrite <- Zabs_nat_mult.
  repeat rewrite Zabs_nat_Z_of_nat.
  repeat rewrite inj_Zabs_nat.
  repeat (rewrite Zabs_eq; [ | apply Zmult_le_0_compat]).
  rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r.
  repeat rewrite inj_mult.
  rewrite Zmult_assoc; trivial.

  generalize (Z_mod_lt (Z_of_nat (a * b)) (p k)).
  generalize (prime_ge_2 _ (p_prime k)).
  auto with zarith.
  auto with zarith.

  auto with zarith.
  generalize (Z_mod_lt (Z_of_nat (b * c)) (p k)).
  generalize (prime_ge_2 _ (p_prime k)).
  auto with zarith.

  rewrite H; intros p1 p2; rewrite (eq_P _ _ p1 p2); trivial.
 Qed.

 Lemma mul_e_l : forall k (x:t k), mul (e k) x = x.
 Proof.
  intros k (a,Ha); unfold mul, e.
  match goal with
   |- exist _ ?a ?Ha = exist _ ?b ?Hb => 
    generalize Hb Ha; assert (H:a = b)
  end.
  rewrite P_prop in Ha; destruct Ha as [ [_ Ha] _].
  rewrite mult_1_l, Zmod_small, Zabs_nat_Z_of_nat; trivial.
  split.
  auto with zarith.
  apply inj_lt in Ha.
  rewrite inj_Zabs_nat in Ha.
  rewrite <- Zabs_eq; trivial.
  generalize (prime_ge_2 _ (p_prime k)); auto with zarith.

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

  apply P_prop in Ha; destruct Ha as [Hlt Hmod].
  destruct (eeuclid_bound (Z_of_nat a) (p k) (Zabs (p k))) as [H2 H3].
  rewrite <- inj_Zabs_nat.
  rewrite <- inj_Zabs_nat.
  apply inj_le.
  rewrite Zabs_nat_Z_of_nat; auto with zarith.
  apply Zle_refl.

  assert (H1:=eeuclid_spec (Z_of_nat a) (p k)).
  assert (Hp:=prime_ge_2 _ (p_prime k)).
  assert (Hq:=prime_ge_2 _ (q_prime k)).

  assert (Hgcd:Zis_gcd (Z_of_nat a) (p k) 1).
   apply Zis_gcd_prime.
   apply p_prime.
   auto with zarith.
   destruct Hlt.
   apply inj_lt in H0.
   split.
   auto with zarith.
   rewrite inj_Zabs_nat, Zabs_eq in H0; auto with zarith.

  destruct (eeuclid (Z_of_nat a) (p k)) as ((u, v), d); simpl in *.
  destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.
  case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
  clear H5 H6 Hgcd; subst.

  change 1%nat with (Zabs_nat 1).
  rewrite <- Zmod_1_l with (p k); [ | auto with zarith].
  apply f_equal.
  case (Z_le_dec 0 u); intro Hu.

  rewrite <- H, Z_mod_plus_full, inj_mult, inj_Zabs_nat, Zabs_eq; trivial.

  assert (Hneq:- u <> p k).
  intro Heq; rewrite <- Heq in H.
  rewrite Zmult_comm, <- Zmult_opp_comm, <- Zmult_plus_distr_l, Zmult_comm in H.
  apply Zmult_1_inversion_l in H; auto with zarith.

  assert (-p k < u < p k).
  split; [ | auto with zarith]. 
  rewrite Zabs_non_eq in H2; [ | auto with zarith].
  rewrite Zabs_eq in H2; auto with zarith. 

  rewrite <- H, Z_mod_plus_full, Zmult_mod, inj_mult, Zmult_mod, inj_Zabs_nat. 
  rewrite <- (Zmult_1_l (p k)) at 1.
  rewrite Zabs_eq; [ | auto with zarith].
  rewrite Z_mod_plus_full; trivial.
 Qed.

 Lemma mul_comm : forall k (x y:t k), mul x y = mul y x.
 Proof.
  intros k (a,Ha) (b,Hb); unfold mul.
  match goal with
   |- exist _ ?a ?Ha = exist _ ?b ?Hb => 
    generalize Ha Hb; assert (H:a = b)
  end.
  rewrite mult_comm; trivial.
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

 Definition order_poly : polynomial := p_poly.

 Lemma order_size_nat : forall k,
  size_nat (length (elems k)) < peval order_poly k.
 Proof.
  intro k.
  apply le_lt_trans with (2:=p_poly_spec k).
  apply size_nat_monotonic.
  eapply le_trans; [apply filter_map_length | ].
  rewrite seq_length; apply le_refl.
 Qed.

 Definition cost_mul k (x y:t k) : nat := size_nat (proj1_sig y).

 Definition cost_pow k (x:t k) (n:Z) : nat :=
  size_nat (proj1_sig x) * (size_Z (q k)).

 Definition cost_inv k (x:t k) : nat := size_nat (proj1_sig x) * size_Z (p k).

 Definition cost_mul_poly : polynomial := p_poly. 
 Definition cost_pow_poly : polynomial := pmult p_poly p_poly.
 Definition cost_inv_poly : polynomial := pmult p_poly p_poly.

 Lemma cost_mul_poly_spec : forall k (x y:t k),
  cost_mul x y <= peval cost_mul_poly k.
 Proof.
  intros k x (b,Hb).
  unfold cost_mul; simpl.
  apply P_prop in Hb; decompose [and] Hb; clear Hb.
  apply le_trans with (size_Z (p k)).
  apply size_nat_monotonic; apply lt_le_weak; trivial.
  apply lt_le_weak; apply p_poly_spec.
 Qed.

 Lemma cost_pow_poly_spec : forall k (x:t k) (n:Z),
  cost_pow x n <= peval cost_pow_poly k.
 Proof.
  intros k (a,Ha) n.
  unfold cost_pow, cost_pow_poly; simpl.
  rewrite pmult_spec.
  apply P_prop in Ha; decompose [and] Ha; clear Ha.
  apply mult_le_compat.
  apply le_trans with (size_Z (p k)).
  apply size_nat_monotonic; apply lt_le_weak; trivial.
  apply lt_le_weak; apply p_poly_spec.
  apply lt_le_weak; apply q_size.
 Qed.

 Lemma cost_inv_poly_spec : forall k (x:t k),
  cost_inv x <= peval cost_inv_poly k.
 Proof.
  intros k (a,Ha).
  unfold cost_inv, cost_inv_poly; simpl.
  rewrite pmult_spec.
  apply P_prop in Ha; decompose [and] Ha; clear Ha.
  apply mult_le_compat.
  apply le_trans with (size_Z (p k)).
  apply size_nat_monotonic; apply lt_le_weak; trivial.
  apply lt_le_weak; apply p_poly_spec.
  apply lt_le_weak; apply p_poly_spec.
 Qed.

End Schnorr_H.


Module Type SCHNORR_GROUPS (SP:SCHNORR_PARAMETERS).

 Module G := Schnorr_G SP.
 Module H := Schnorr_H SP.

End SCHNORR_GROUPS.

 
Module Schnorr_Homomorphism (SP:SCHNORR_PARAMETERS) (GH:SCHNORR_GROUPS SP) <: HOMOMORPHISM GH.G GH.H.

 Module SPP := Schnorr_Parameters_Properties SP.
 Import SPP.
 
 Import GH.

 Module HP := Group_Properties H.
 Import HP.
 
 Open Scope nat_scope.

 Definition g k : H.t k.
  intro k.
  refine (exist _ (Zabs_nat (g k)) _).
  destruct (g_range k).
  apply <- H.P_prop; split.
  change 0%nat with (Zabs_nat 0).
  split; apply Zabs_nat_lt; auto with zarith.
  rewrite inj_Zabs_nat, Zabs_eq, g_order; auto with zarith.
 Defined.
 
 Definition phi k (x:G.t k) : H.t k :=
  match x with
   | exist a _ => H.pow (g k) a
  end.

 Definition cost_phi k (x:G.t k) :=
  match x with
   | exist a _ => H.cost_pow (g k) (Z_of_nat a)
  end.

 Definition cost_phi_poly : polynomial := H.cost_pow_poly.

 Lemma cost_phi_poly_spec : forall k (x:G.t k),
  cost_phi x <= peval cost_phi_poly k.
 Proof.
  intros k (a,Ha); apply H.cost_pow_poly_spec.
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

 Lemma cyclic_1 : forall k x, H.pow x (Zabs_nat (q k)) = H.e k.
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
  intros k (a,Ha) (b,Hb); unfold phi; simpl.
  rewrite HP.mul_pow_plus.
  case (le_gt_dec (Zabs_nat (q k)) (a + b)).
  intros.
  assert (a + b = a + b - Zabs_nat (q k) + Zabs_nat (q k)) by omega.
  rewrite H at 2.
  rewrite <- HP.mul_pow_plus, cyclic_1, HP.mul_e_r; trivial.
  trivial.
 Qed.  


 (* [phi] is a special homomorphism *)
 Definition special_v k := Z_of_nat (Zabs_nat (q k)).
  
 Lemma special_v_spec : forall k, special_v k <> 0%Z.
 Proof.
  intro k; unfold special_v.
  generalize (q_pos k); auto with zarith.
 Qed.
 
 Definition special_v_poly : polynomial := p_poly.

 Lemma size_nat_special_v : forall k, 
  size_nat (Zabs_nat (special_v k)) <= peval special_v_poly k. 
 Proof.
  intro k; unfold special_v.
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
  intros; simpl; unfold special_v.  
  rewrite HP.powZ_pow.
  symmetry; apply cyclic_1.
 Qed.

End Schnorr_Homomorphism.


(** Instantition *)
Declare Module SP : SCHNORR_PARAMETERS.

Module GH : SCHNORR_GROUPS SP.

 Module G := Schnorr_G SP.
 Module H := Schnorr_H SP.

End GH.

Module HM := Schnorr_Homomorphism SP GH.
Module CS := Largest_Challenge_Set GH.G GH.H HM.

Module S := SigmaPhi.SigmaPhi GH.G GH.H HM CS.
