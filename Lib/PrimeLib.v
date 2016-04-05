(** * PrimeLib.v : Extension to the library of Coq about integers *)

Require Import CCMisc.
Require Export Znumtheory.
Require Import Arith Even Div2.
Require Import Arith.Euclid.

(** Zdivide *)

Lemma Zle_lt : forall a, a <> 0 -> 0 <= a -> 0 < a.
Proof.
 intros; omega.
Qed.

Lemma Zdivide_Zdiv_eq_full : forall a b, 
 a <> 0 -> (a | b) -> b = a * (b / a).
Proof.   
 intros.
 apply Z_div_exact_full_2; trivial.
 destruct H0; rewrite H0.
 apply Z_div_exact_full_1.
 rewrite Z_div_mult_full; trivial.
 rewrite Zmult_comm; trivial.
Qed.

Lemma bezout_identity : forall a b,
 Zis_gcd a b 1 ->
 exists x, exists y, x * a + y * b = 1.
Proof.
 intros.
 apply Zis_gcd_bezout in H; inversion H as [u' v].
 exists u'; exists v; trivial.
Qed.

Lemma not_prime_divide_prime : forall n, 
 1 < n -> ~ prime n -> exists p, prime p /\ (p | n) /\ 1 < p < n.
Proof.
 intros n Hn; generalize Hn.
 pattern n; apply Z_lt_induction.
 clear n Hn; intros n Rec H H1.
 case (not_prime_divide n); auto.
 intros n1 [ [H3 H4] H5].
 case (prime_dec n1); intros H6.
 exists n1; split; trivial.
 split; [ | split]; trivial.
 apply Rec in H6; trivial; try omega.
 elim H6; intros n0 [Hp [Hpn1 Hlt] ]. 
 exists n0; split; auto with zarith.
 split.
 apply Zdivide_trans with n1; trivial.
 auto with zarith.
 auto with zarith.
Qed.
  
Lemma lt_minus_one_divide_prime : forall n, 
 n < -1 -> exists p, prime p /\ (p | n).
Proof.
 intros n Hn.
 case (prime_dec (-n)); intro Hprime.
 exists (- n); split; trivial.
 apply Zdivide_opp_l; apply Zdivide_refl.
 elim (@not_prime_divide_prime (-n)); trivial; try omega.
 intros p' [Hp' [ Hdiv' Hlt ] ].
 exists p'; split; trivial.
 apply Zdivide_opp_r_rev; trivial.
Qed.

Lemma Zdivide_prime : forall n, 
 n <> -1 -> n <> 0 -> n <> 1 -> ~ prime n -> exists p, prime p /\ (p | n).
Proof.
 intros n Hnm1 Hn0 Hn1 Hpn.
 case (Z_lt_dec n 0); intro.
 apply lt_minus_one_divide_prime; omega.
 destruct (not_prime_divide_prime n); trivial.
 omega.
 destruct H as [H1 [ H2 H3] ].
 exists x.
 split; trivial.
Qed.

Lemma Zdivide_lt_rel_prime : forall a b,
 (forall p, prime p -> (p | b) ->  -p < a < p) ->
 a <> 0 ->
 Zis_gcd a b 1.
Proof.
 intros a b Hp Ha.
 assert (Hpos:= Zgcd_is_pos a b).
 destruct (Z_dec a 0) as [ [ H3 | H4] | H5].    
     
 assert (H0: (Zgcd a b | -a)) by (apply Zdivide_opp_r; case (Zgcd_is_gcd a b); auto).
 assert (H1: (Zgcd a b | -b)) by (apply Zdivide_opp_r; case (Zgcd_is_gcd a b); auto).    
 apply Zdivide_le in H0; try omega.
 case (prime_dec (Zgcd a b)); intros Hz.
 apply Hp in Hz.
 elimtype False; omega.
 apply Zdivide_opp_r_rev; trivial.     
 elim (Z_eq_dec (Zgcd a b) 0); intros Hz0.
 apply Zgcd_inv_0_l in Hz0.
 elimtype False; omega.
 elim (Z_eq_dec (Zgcd a b) 1); intros Hz1.
 rewrite <- Hz1; apply Zgcd_is_gcd.         
 apply Zdivide_prime in Hz; trivial; try omega.
 elim Hz; intros p2 [Hp2 Hdiv2]; clear Hz.
 apply Zdivide_opp_r_rev in H1.
 apply Hp in Hp2; trivial.
 apply Zdivide_le in Hdiv2; try omega.
 elimtype False; omega.
 apply Zdivide_trans with (Zgcd a b); trivial.

 assert (H0: (Zgcd a b | a)) by (case (Zgcd_is_gcd a b); auto).
 assert (H1: (Zgcd a b | b)) by (case (Zgcd_is_gcd a b); auto).
 apply Zdivide_le in H0; try omega.
 case (prime_dec (Zgcd a b)); intros Hz.
 apply Hp in Hz; trivial.
 elimtype False; omega.
 elim (Z_eq_dec (Zgcd a b) 0); intros Hz0.
 apply Zgcd_inv_0_l in Hz0.
 elimtype False; omega.
 elim (Z_eq_dec (Zgcd a b) 1); intros Hz1.
 rewrite <- Hz1; apply Zgcd_is_gcd.    
 apply Zdivide_prime in Hz; trivial; try omega.
 elim Hz; intros p2 [Hp2 Hdiv2]; clear Hz.
 assert (Hb := Zdivide_trans p2 (Zgcd a b) b Hdiv2 H1).
 apply Hp in Hp2; trivial.
 apply Zdivide_le in Hdiv2; try omega.
 elimtype False; omega.
    
 elimtype False; omega.
Qed.


(** Zmult *)

Lemma Zmult_neq_0 : forall x y, x <> 0 -> y <> 0 -> x * y <> 0.
Proof.
 firstorder using Zmult_integral.
Qed.
 
(** Zdiv *)

Lemma Zdiv_pos : forall a b : Z, 0 <= b -> 0 <= a -> 0 <= a / b.
Proof.
 intros.
 case (Z_eq_dec b 0); intro Hb.
 rewrite Hb, Zdiv_0_r; apply Zle_refl.
 apply Z_div_pos; omega.
Qed.

Lemma Zdiv_neq_0 : forall a b, 0 < b <= a -> a / b <> 0.
Proof.
 intros.
 generalize (Zdiv_le_lower_bound a b 1).
 intros Hlt Heq; rewrite Heq in Hlt; apply Hlt; try omega; trivial.
Qed.

(** Zpower *)

Lemma Zmod_power : forall a b n, (a mod b) ^ n mod b = a ^ n mod b.
Proof.
 destruct n; [trivial | | trivial].
 simpl; repeat rewrite Zpower_pos_nat.
 induction (nat_of_P p).
 trivial.
 unfold Zpower_nat in *; simpl.
 rewrite Zmult_mod_idemp_l, Zmult_mod, IHn, <- Zmult_mod; trivial.
Qed.

Lemma Zmult_power_distr : forall a b n, (a * b) ^ n = a ^ n * b ^ n.
Proof.
 destruct n; trivial.
 simpl; repeat rewrite Zpower_pos_nat.
 induction (nat_of_P p).   
 trivial.
 unfold Zpower_nat in *; simpl.
 rewrite IHn; ring.
Qed.

Lemma Zpower_0 : forall n, 0 < n -> 0 ^ n = 0.
Proof.
 intros; destruct n.
 auto with zarith.
 simpl; rewrite Zpower_pos_nat.
 rewrite Zpos_eq_Z_of_nat_o_nat_of_P in H.
 induction (nat_of_P p).
 simpl in H; auto with zarith.
 trivial.
 auto with zarith.
Qed.

Lemma Zpower_1 : forall n, 0 <= n -> 1 ^ n = 1.
Proof.
 intros; destruct n.
 trivial.
 simpl; rewrite Zpower_pos_nat.
 induction (nat_of_P p).
 trivial.
 change (S n) with (1 + n)%nat.
 unfold Zpower_nat in *.
 rewrite iter_nat_plus, IHn; trivial.
 elim H; trivial.
Qed.

Lemma Zpower_pow_nat : forall (a b:Z),
 0 <= a -> 
 0 <= b ->
 Z_of_nat (Zabs_nat a ^ Zabs_nat b) = a ^ b.
Proof.
 destruct b; intros; [trivial | simpl | elim H0; trivial].  
 rewrite Zpower_pos_nat.
 clear H0; induction (nat_of_P p).
 trivial.
 simpl; rewrite inj_mult, IHn, inj_Zabs_nat, Zabs_eq; trivial.
Qed.

(** Zgcd *)

Lemma Zgcd_sym : forall a b, Zgcd a b = Zgcd b a.
Proof.
 intros a b.
 apply Zis_gcd_gcd.
 apply Zgcd_is_pos.
 apply Zis_gcd_sym.
 apply Zgcd_is_gcd.
Qed.

Lemma Zgcd_div_l : forall a b, (Zgcd a b | a).
Proof.
 intros a b; destruct (Zgcd_is_gcd a b); trivial.
Qed.

Lemma Zgcd_div_r : forall a b, (Zgcd a b | b).
Proof.
 intros a b; rewrite Zgcd_sym.
 apply Zgcd_div_l.
Qed.

Lemma Zgcd_0_r : forall a, Zgcd 0 a = Zabs a.
Proof.
 intro; simpl; trivial.
Qed.

Lemma Zgcd_0_l : forall a, Zgcd a 0 = Zabs a.
Proof.
 intros; rewrite Zgcd_sym; simpl; trivial.
Qed.

Lemma Zgcd_neq_0 : forall a b, a <> 0 -> b <> 0 -> Zgcd a b <> 0.
Proof.
 intros a b Ha Hb Heq.
 apply Zgcd_inv_0_l in Heq.
 subst a; elim Ha; trivial.
Qed.

Lemma Zgcd_assoc : forall a b c, Zgcd a (Zgcd b c) = Zgcd (Zgcd a b) c.
Proof.
 intros.
 apply Zis_gcd_gcd.
 apply Zgcd_is_pos.
 constructor;
 eauto using Zdivide_Zgcd, Zdivide_trans, Zgcd_div_l, Zgcd_div_r.
Qed.

Lemma Zis_gcd_prime : forall p n, 
 prime p -> n <> 0 -> -p < n < p -> Zis_gcd n p 1.
Proof.
 intros. 
 case (Z_lt_dec n 0); intro Hdec.
 apply Zis_gcd_minus.
 apply bezout_rel_prime.
 apply rel_prime_bezout.
 apply rel_prime_sym.
 apply rel_prime_le_prime; trivial.
 omega.
    
 apply bezout_rel_prime.
 apply rel_prime_bezout.
 apply rel_prime_le_prime; trivial.
 omega.
Qed.
 

(** Zabs *)

Lemma Zabs_div : forall a, (a | Zabs a).
Proof.
 intros a; case a; simpl.
 apply Zdivide_0.
 intro; apply Zdivide_refl.
 intro; rewrite <- Zopp_neg.
 apply Zdivide_opp_r.
 apply Zdivide_refl.
Qed.

Lemma Zabs_div_inv : forall a, (Zabs a | a).
Proof.
 intros.
 apply Zdivide_Zabs_inv_l.
 apply Zdivide_refl.
Qed.

Lemma Zabs_nat_Zabs : forall a, Zabs_nat (Zabs a) = Zabs_nat a.
Proof.
 intro a; case a; simpl; trivial.
Qed.

Lemma Zabs_neq_0 : forall x, x <> 0 -> Zabs x <> 0.
Proof.
 intro x; case x; intros.
 elim H; trivial.
 simpl; trivial.
 simpl.
 intro Heq; rewrite <- Zopp_neg in Heq.
 rewrite <- Heq in H.
 elim H; omega.
Qed.

Lemma Zabs_0_inv : forall n,
 Zabs n = 0%Z -> n = 0%Z.
Proof.
 intros; destruct n; simpl; trivial.
 rewrite <- H; discriminate.
Qed. 
 

(** Zlcm *)

Definition Zlcm a b := Zabs (a * b) / Zgcd a b.

Lemma Zlcm_gcd : forall a b, Zabs (a * b) = Zgcd a b * Zlcm a b.
Proof.
 intros; unfold Zlcm.
 case (Z_eq_dec (Zgcd a b) 0); intro H.
 rewrite H; simpl.
 apply Zgcd_inv_0_l in H.
 rewrite H; trivial.
 apply Zdivide_Zdiv_eq_full; [ trivial | ].
 apply Zdivide_trans with (a * b).
 apply Zdivide_mult_l; apply Zgcd_div_l.
 apply Zabs_div.
Qed. 

Lemma Zlcm_sym : forall a b, Zlcm a b = Zlcm b a.
Proof.
 intros; unfold Zlcm.
 rewrite Zgcd_sym, Zmult_comm; trivial.
Qed.

Lemma Zlcm_div_mult : forall a b, (Zlcm a b | a * b).
Proof.
 intros a b.
 apply Zdivide_trans with (Zabs (a * b)).
 rewrite Zlcm_gcd.
 apply Zdivide_factor_l.
 apply Zabs_div_inv.
Qed.

Lemma Zis_gcd_lcm : forall n a b, 
 Zis_gcd n a 1 ->
 Zis_gcd n b 1 ->
 Zis_gcd n (Zlcm a b) 1.
Proof.
 intros n a b Ha Hb.
 apply Zis_gcd_gcd in Ha; try omega.
 apply Zis_gcd_gcd in Hb; try omega.
 destruct (Zgcd_1_rel_prime n a) as [Hrp_a _].
 destruct (Zgcd_1_rel_prime n b) as [Hrp_b _].
 apply Hrp_a in Ha.
 apply Hrp_b in Hb.
 clear Hrp_a Hrp_b.
 assert (Hab := rel_prime_mult n a b Ha Hb).
 
 apply rel_prime_sym.
 apply rel_prime_div with (a * b); trivial.
 apply rel_prime_sym; trivial.
 apply Zlcm_div_mult.
Qed.

Lemma Zdivide_lt_rel_prime_lcm : forall n a b,
 (forall p, prime p -> (p | a) -> -p < n < p) ->
 (forall p, prime p -> (p | b) -> -p < n < p) ->
 n <> 0 ->
 Zis_gcd n (Zlcm a b) 1.
Proof.
 intros n a b Hpa Hpb Hn.
 assert (Ha := Zdivide_lt_rel_prime n a Hpa Hn).
 assert (Hb := Zdivide_lt_rel_prime n b Hpb Hn).
 apply Zis_gcd_lcm; trivial.
Qed.

Lemma Zlcm_div_l : forall a b, (a | Zlcm a b).
Proof.
 intros; unfold Zlcm.
 case (Z_eq_dec (Zgcd a b) 0); intro Hgcd.
 rewrite Hgcd, Zdiv_0_r; apply Zdivide_0.

 apply Zdivide_Zabs_l.
 apply Zdivide_intro with (Zabs b / Zgcd a b).
 rewrite Zabs_Zmult, (Zmult_comm _ (Zabs a)).
 apply Zdivide_Zdiv_eq_2.
 generalize (Zgcd_is_pos a b); omega.
 apply Zdivide_trans with b; [apply Zgcd_div_r | apply Zabs_div].
Qed.

Lemma Zlcm_div_r : forall a b, (b | Zlcm a b).
Proof.
 intros.
 rewrite Zlcm_sym.
 apply Zlcm_div_l.
Qed.

Lemma Zlcm_is_pos : forall a b, 0 <= Zlcm a b.
Proof.
 intros; unfold Zlcm.
 apply Zdiv_pos.
 apply Zgcd_is_pos.
 apply Zabs_pos.
Qed. 
 
Lemma Zlcm_neq_0 : forall a b, a <> 0 -> b <> 0 -> Zlcm a b <> 0.
Proof.
 intros; unfold Zlcm.

 assert (H1:0 < Zgcd a b).
 generalize (Zgcd_is_pos a b) (Zgcd_neq_0 a b); omega.

 assert (H2:0 < Zabs (a * b)).
 generalize (Zabs_pos (a * b)) (Zabs_neq_0 (a * b)) (Zmult_neq_0 a b); omega.

 apply Zdiv_neq_0; split.
 trivial.
 apply Zdivide_le.
 apply Zlt_le_weak; trivial.
 trivial.
 rewrite Zabs_Zmult.
 apply Zdivide_mult_l.
 apply Zdivide_trans with a.
 apply Zgcd_div_l.
 apply Zabs_div.
Qed.

Lemma Zdivide_lcm_prime :
 forall p a b, prime p -> (p | Zlcm a b) -> (p | a) \/ (p | b).
Proof.
 intros p a b Hp Hdiv.
 apply (prime_mult p Hp).
 apply Zdivide_trans with (Zabs (a * b)).
 rewrite Zlcm_gcd.   
 apply Zdivide_mult_r; trivial.
 apply Zabs_div_inv.
Qed.


(** Smallest prime divisor *)

Definition primeb (a:Z) : bool := if prime_dec a then true else false.

Lemma primeb_spec : forall a, primeb a = true <-> prime a.
Proof.
 unfold primeb; intro a; split; case (prime_dec a).
 trivial.
 intros; discriminate.
 trivial.
 intuition.
Qed.

Definition Zdivideb (a b:Z) : bool := if Zdivide_dec a b then true else false.

Lemma Zdivideb_spec : forall a b, Zdivideb a b = true <-> Zdivide a b.
Proof.
 unfold Zdivideb; intro a; split; case (Zdivide_dec a b).
 trivial.
 intros; discriminate.
 trivial.
 intuition.
Qed.

Definition smallest_prime_divisor (a:Z) :=
 match filter (fun b => primeb (Z_of_nat b) && Zdivideb (Z_of_nat b) a) 
              (seq 2 (Zabs_nat a))
 with
  | nil    => 1 + a
  | p :: _ => Z_of_nat p
 end.

Lemma smallest_prime_divisor_spec : forall (a:Z),
 1 < a ->
 let p := smallest_prime_divisor a in
  prime p /\
  (p | a) /\
  forall p', prime p' -> (p' | a) -> p <= p'.
Proof.
 intro a; unfold smallest_prime_divisor.
 case_eq (filter 
  (fun b => primeb (Z_of_nat b) && Zdivideb (Z_of_nat b) a) (seq 2 (Zabs_nat a))).

 (* No smallest prime divisor, absurd *)
 intros Heq Hlt.
 case (prime_dec a); intro Ha.

  (* If [a] is prime, [a] must be in the list *)
  assert (Hin:In (Zabs_nat a) nil).
   rewrite <- Heq, filter_In; split.
   apply le_In_seq; split; [ | omega].
   change 2%nat with (Zabs_nat 2).
   apply Zabs_nat_le; omega.
   rewrite inj_Zabs_nat.
   rewrite Zabs_eq; [ | omega].
   apply andb_true_intro; split.
    apply <- primeb_spec; trivial.
    apply <- Zdivideb_spec; apply Zdivide_refl.  
  inversion Hin.

  (* If [a] is composite, it has a prime divisor that must be in the list *)
  apply (not_prime_divide_prime a Hlt) in Ha.
  destruct Ha as [p [H0 [H1 H2] ] ].
  assert (Hin:In (Zabs_nat p) nil).
   rewrite <- Heq, filter_In; split.
   apply le_In_seq; split.
   change 2%nat with (Zabs_nat 2).
   apply Zabs_nat_le; omega.
   assert (H3:0 <= p <= a) by omega.
   apply Zabs_nat_le in H3; omega.
   rewrite inj_Zabs_nat.
   rewrite Zabs_eq; [ | omega].
   apply andb_true_intro; split.
    apply <- primeb_spec; trivial.
    apply <- Zdivideb_spec; trivial.
  inversion Hin.

 (* [p] is the smallest prime divisor *)
 intros p l Heq Hlt.
 assert (Hin:In p (p::l)) by intuition.
 rewrite <- Heq, filter_In, andb_true_iff in Hin.
 destruct Hin as [_ [H0 H1] ].
 split; [ | split].
  apply -> primeb_spec; trivial.
  apply -> Zdivideb_spec; trivial.

  (* Any other prime divisor [p'] has to be in the list *)
  intros p' H2 H3.
  assert (H4:=prime_ge_2 _ H2).
  assert (H5:p' <= a) by (apply Zdivide_le; [omega | omega | trivial]).
  assert (Hin:In (Zabs_nat p') (p::l)).
  rewrite <- Heq, filter_In; split.
  apply le_In_seq; split.
   change 2%nat with (Zabs_nat 2).
   apply Zabs_nat_le; omega.
   assert (H6:0 <= p' <= a) by omega.
   apply Zabs_nat_le in H6; omega.
   rewrite inj_Zabs_nat.
   rewrite Zabs_eq; [ | omega].
   apply andb_true_intro; split.
    apply <- primeb_spec; trivial.
    apply <- Zdivideb_spec; trivial.
  induction Hin.
  rewrite H, inj_Zabs_nat, Zabs_eq; omega.
  
  (* Since [p'] is in the list and the list is ordered, [p <= p'] *)
  assert (Hs:sort lt (p :: l)).
   rewrite <- Heq.
   apply sorted_filter.
   unfold transitive; intros; eauto with arith.
   apply sorted_seq.

  replace p' with (Zabs p') by (apply Zabs_eq; omega).  
  rewrite <- inj_Zabs_nat; apply inj_le.

  apply sort_inv in Hs; destruct Hs as [Hs Hl].
  clear -H Hs Hl; induction l.
  inversion H.
  induction H.
  apply lelistA_inv in Hl; intuition.

  apply (IHl H).
  apply sort_inv in Hs; intuition.
  apply lelistA_inv in Hl.
  apply sort_inv in Hs; intuition.
  clear -Hl H1.
  induction l; constructor.
  apply lelistA_inv in H1; omega.
Qed.


(** Extended Euclidean Algorithm *)

Ltac Z_eq_dec_tac x :=
 let H := fresh "H" in
  case (Z_dec 0 x); intro H; [ elim H; clear H; intro H | ].


Inductive Euclid : Z -> Z -> Z -> Z -> Z -> Prop :=
| EuclidEq: forall a,
             0 < a -> 
             Euclid a a 1 0 a
| EuclidGt: forall a b u v d, 
             0 <= b < a -> 
             Euclid (a - b) b u v d ->
             Euclid a b u (v - u) d
| EuclidLt: forall a b u v d, 
             Euclid a b u v d -> 
             Euclid b a v u d.

Hint Constructors Euclid.

Lemma Euclid_bezout : forall a b u v d, 
 Euclid a b u v d -> u * a + v * b = d.
Proof.
 induction 1; try rewrite <- IHEuclid; ring.
Qed.

Lemma Euclid_gcd : forall a b u v d, 
 Euclid a b u v d -> Zis_gcd a b d.
Proof.
 induction 1; auto with zarith.
 apply Zis_gcd_refl.
 apply Zis_gcd_for_euclid with 1; rewrite Zmult_1_l; auto.
 apply Zis_gcd_sym; auto.
Qed.

Lemma Euclid_bound : forall a b u v d, 
 Euclid a b u v d -> Zabs u <= Zabs b /\ Zabs v <= Zabs a.
Proof.
 induction 1; auto with zarith.
 repeat rewrite Zabs_eq; auto with zarith.
 split; intuition.
 apply Zle_trans with (Zabs u + Zabs v).
 replace (v - u) with ((-u) + v); try ring.
 rewrite <- (Zabs_Zopp u).
 apply Zabs_triangle.
 rewrite (Zabs_eq a) in * |- *; auto with zarith.
 rewrite (Zabs_eq b) in * |- *; auto with zarith.
 rewrite (Zabs_eq (a - b)) in * |- *; auto with zarith.
Qed.


(** Chinese Remainder Theorem *)

Lemma chinese : forall m n a b, 
 rel_prime m n -> {x:Z | x mod m = a mod m /\ x mod n = b mod n}.
Proof.
 intros m n a b Hmn.
 destruct (euclid m n) as [u v d H1 H2].
 exists (a * (d * v * n) + b * (d * u * m)).
 destruct (Zis_gcd_unique _ _ _ _ Hmn H2) as [H | H]. 
 rewrite <- H in *.
 rewrite Zmult_1_l, Zmult_1_l.
 split.
 rewrite Zmult_assoc, Zmult_assoc.
 rewrite Z_mod_plus_full.
 rewrite <- Zmult_assoc.
 cutrewrite (v*n = 1 - u*m); [ | omega].
 cutrewrite (a*(1-u*m) = a + (-a*u*m)); [ | ring].
 apply Z_mod_plus_full.
 rewrite Zplus_comm, Zmult_assoc, Zmult_assoc, Z_mod_plus_full, <- Zmult_assoc.
 cutrewrite (u*m = 1 - v*n); [ | omega].
 cutrewrite (b*(1-v*n) = b + (-b*v*n)); [ | ring ].
 apply Z_mod_plus_full.
 cut (d=-1); [ | omega ].
 clear H; intro H.
 rewrite H in *.
 cutrewrite (-1 * u = -u);[ | trivial].
 cutrewrite (-1 * v = -v);[ | trivial].
 split.
 rewrite Zmult_assoc, Zmult_assoc, Z_mod_plus_full, <- Zmult_assoc.
 cutrewrite (-v*n = 1 - -u*m).
 cutrewrite (a*(1- -u*m) = a + (a * u *m));[ | ring ].
 apply Z_mod_plus_full.
 transitivity (- (v*n)); [ring | ].
 transitivity (1 + u*m); [omega | ring ].
 rewrite Zplus_comm, Zmult_assoc, Zmult_assoc, Z_mod_plus_full, <- Zmult_assoc.
 cutrewrite (-u*m = 1 - -v*n).
 cutrewrite (b*(1- -v*n) = b + b*v*n);[ | ring].
 apply Z_mod_plus_full.
 transitivity (- (u*m)); [ ring | ].
 transitivity (1 + v*n); [ omega | ring].
Qed.

(* The algorithm, assuming [0 < b <= a] *)
Definition euclid : forall a b, 
 0 < b <= a -> 
 {uvd: Z * Z * Z | let (uv,d) := uvd in let (u,v) := uv in Euclid a b u v d /\ 0 <= d}.
 intros a b Hab; generalize b Hab; pattern a.
 apply Zlt_0_rec; [ | omega]; clear a b Hab; intros a Hrec Ha b Hb.

 case (Z_eq_dec a b); intros Hab.
 exists (1, 0, a); subst; intuition.

 case (Z_le_gt_dec (a - b) b); intros Habb.
 assert (HH:0 <= b < a) by auto with zarith.
 assert (HH1:0 < a - b <= b) by auto with zarith.
 destruct (Hrec _ HH _ HH1) as (((u,v),d), Hd).
 exists (v, u - v, d); intuition.

 assert (HH:0 <= a - b < a) by auto with zarith. 
 assert (HH1:0 < b <= a - b) by auto with zarith.
 destruct (Hrec _ HH _ HH1) as (((u,v),d), Hd).
 exists (u, v - u, d); intuition.
Defined.

(* The general algorithm *)
Definition eeuclid (a b: Z) : Z * Z * Z.
 intros a b.
 Z_eq_dec_tac a.
 Z_eq_dec_tac b.

 case (Z_le_gt_dec b a); intro Hab.
 destruct (euclid a b) as [((u,v),d) [H1 H2] ]; [auto with zarith | exact (u,v,d)].
 destruct (euclid b a) as [((u,v),d) [H1 H2] ]; [auto with zarith | exact (v,u,d)].
  
 case (Z_le_gt_dec (-b) a); intro Hab.
 destruct (euclid a (-b)) as [((u,v),d) [H1 H2] ]; [auto with zarith | exact (u,-v,d)].
 destruct (euclid (-b) a) as [((u,v),d) [H1 H2] ]; [auto with zarith | exact (v,-u,d)].

 exact (1, 0, a).
 
 Z_eq_dec_tac b.
 case (Z_le_gt_dec (-a) b); intro Hab.
 destruct (euclid b (-a)) as [((u,v),d) [H1 H2] ]; [auto with zarith | exact (-v,u,d)].
 destruct (euclid (-a) b) as [((u,v),d) [H1 H2] ]; [auto with zarith | exact (-u,v,d)].

 case (Z_le_gt_dec (-b) (-a)); intro Hab.
 destruct (euclid (-a) (-b)) as [((u,v),d) [H1 H2] ]; [auto with zarith | exact (-u,-v,d)].
 destruct (euclid (-b) (-a)) as [((u,v),d) [H1 H2] ]; [auto with zarith | exact (-v,-u,d)].
 
 exact (-1, 0, -a).

 Z_eq_dec_tac b. 
 exact (0, 1, b).
 exact (0, -1, -b).
 exact (0, 0, 0).
Defined.

Lemma eeuclid_spec : forall (a b u v d:Z),
 eeuclid a b = (u, v, d) -> 
 u * a + v * b = d /\ Zis_gcd a b d /\ 0 <= d.
Proof.
 intros a b u v d; unfold eeuclid.
 Z_eq_dec_tac a.
 Z_eq_dec_tac b; simpl.

 case (Z_le_gt_dec b a); intro Hab;
 match goal with 
  |- context [euclid ?a ?b ?H] =>
      let H1 := fresh "H" in
       destruct (euclid a b H) as [((u',v'),d') [H1 ?] ]; simpl;
       injection 1; intros; subst; split
 end. 
 apply Euclid_bezout; trivial.
 apply Euclid_gcd in H1; auto.
 apply Euclid_bezout in H1; rewrite Zplus_comm; trivial.
 apply Euclid_gcd in H1; apply Zis_gcd_sym in H1; auto.

 case (Z_le_gt_dec (-b) a); intro Hab;
 match goal with 
  |- context [euclid ?a ?b ?H] =>
      let H1 := fresh "H" in
       destruct (euclid a b H) as [((u',v'),d') [H1 ?] ]; simpl;
       injection 1; intros; subst; split
 end.
 apply Euclid_bezout in H1; rewrite <- H1; ring.
 apply Euclid_gcd in H1; apply Zis_gcd_minus in H1; apply Zis_gcd_sym in H1; auto.
 apply Euclid_bezout in H1; rewrite <- H1; ring.
 apply Euclid_gcd in H1; apply Zis_gcd_sym in H1; apply Zis_gcd_minus in H1; 
  apply Zis_gcd_sym in H1; auto.

 intro H1; injection H1; clear H1; intros; subst; auto with zarith.

 Z_eq_dec_tac b; simpl.
 case (Z_le_gt_dec (-a) b); intro Hab;
 match goal with 
  |- context [euclid ?a ?b ?H] =>
      let H1 := fresh "H" in
       destruct (euclid a b H) as [((u',v'),d') [H1 ?] ]; simpl;
       injection 1; intros; subst; split
 end.
 apply Euclid_bezout in H1; rewrite <- H1; ring.
 apply Euclid_gcd in H1; apply Zis_gcd_minus in H1; auto.
 apply Euclid_bezout in H1; rewrite <- H1; ring.
 apply Euclid_gcd in H1; apply Zis_gcd_sym in H1; apply Zis_gcd_minus in H1; auto.

 case (Z_le_gt_dec (-b) (-a)); intro Hab;
 match goal with 
  |- context [euclid ?a ?b ?H] =>
      let H1 := fresh "H" in
       destruct (euclid a b H) as [((u',v'),d') [H1 ?] ]; simpl;
       injection 1; intros; subst; split
 end.
 apply Euclid_bezout in H1; rewrite <- H1; ring.
 apply Euclid_gcd in H1; apply Zis_gcd_minus in H1; apply Zis_gcd_minus in H1; auto.

 apply Euclid_bezout in H1; rewrite <- H1; ring.
 apply Euclid_gcd in H1; apply Zis_gcd_minus in H1; apply Zis_gcd_minus in H1; 
  apply Zis_gcd_sym in H1; auto.

 intro H1; injection H1; clear H1; intros; subst; auto with zarith.

 Z_eq_dec_tac b; intro H1; injection H1; clear H1; intros; subst; auto with zarith.
Qed.

Lemma euclid_bound : forall a b (H:0 < b <= a),
 match euclid a b H with
 | exist (u,v,d) He => Zabs u <= Zabs b /\ Zabs v <= Zabs a
 end.
Proof.
 intros a b H.
 generalize (let uvd := proj1_sig (euclid a b H) in
  Euclid_bound a b (fst (fst uvd)) (snd (fst uvd)) (snd uvd)).
 destruct (euclid a b H) as [((u,v),d) [H1 H2]]; auto.
Qed.

Lemma eeuclid_bound : forall (a b n:Z),
 Zabs a <= n ->
 Zabs b <= n ->
 Zabs (fst (fst (eeuclid a b))) <= n /\
 Zabs (snd (fst (eeuclid a b))) <= n.
Proof.
 intros a b n Ha Hb; unfold eeuclid.
 Z_eq_dec_tac a.
 Z_eq_dec_tac b; simpl.

 case (Z_le_gt_dec b a); intro Hab;
 match goal with 
  |- context [euclid ?a ?b ?H] =>
     assert (H1:=euclid_bound a b H);
     destruct (euclid a b H) as [((u,v),d) [? ?] ]; simpl;
     auto with zarith
 end.

 case (Z_le_gt_dec (-b) a); intro Hab;
 match goal with 
  |- context [euclid ?a ?b ?H] =>
     assert (H1:=euclid_bound a b H);
     destruct (euclid a b H) as [((u,v),d) [? ?] ]; simpl
 end.
 rewrite Zabs_Zopp.
 rewrite (Zabs_eq (-b)) in H1; rewrite Zabs_non_eq in Hb; auto with zarith.
 rewrite Zabs_Zopp.
 rewrite (Zabs_eq (-b)) in H1; rewrite Zabs_non_eq in Hb; auto with zarith.

 rewrite Zabs_eq in Ha; auto with zarith.

 Z_eq_dec_tac b; simpl.
 case (Z_le_gt_dec (-a) b); intro Hab;
 match goal with 
  |- context [euclid ?a ?b ?H] =>
     assert (H1:=euclid_bound a b H);
     destruct (euclid a b H) as [((u,v),d) [? ?] ]; simpl
 end.
 rewrite Zabs_Zopp.
 rewrite (Zabs_eq (-a)) in H1; rewrite Zabs_non_eq in Ha; auto with zarith.
 rewrite Zabs_Zopp.
 rewrite (Zabs_eq (-a)) in H1; rewrite Zabs_non_eq in Ha; auto with zarith.

 case (Z_le_gt_dec (-b) (-a)); intro Hab;
 match goal with 
  |- context [euclid ?a ?b ?H] =>
     assert (H1:=euclid_bound a b H);
     destruct (euclid a b H) as [((u,v),d) [? ?] ]; simpl
 end.
 rewrite Zabs_Zopp, Zabs_Zopp.
 rewrite (Zabs_eq (-a)) in H1; rewrite Zabs_non_eq in Ha;
 rewrite (Zabs_eq (-b)) in H1; rewrite Zabs_non_eq in Hb; auto with zarith.
 rewrite Zabs_Zopp, Zabs_Zopp.
 rewrite (Zabs_eq (-a)) in H1; rewrite Zabs_non_eq in Ha; 
 rewrite (Zabs_eq (-b)) in H1; rewrite Zabs_non_eq in Hb; auto with zarith.

 rewrite Zabs_non_eq in Ha; auto with zarith.

 Z_eq_dec_tac b; simpl.
 rewrite Zabs_eq in Hb; auto with zarith.
 rewrite Zabs_non_eq in Hb; auto with zarith.
 rewrite Zabs_eq in Ha; auto with zarith.
Qed.

Lemma even_of_Zeven : forall x, 0 <= x -> even (Zabs_nat x) -> Zeven x.
Proof.
 intros x Hx H.
 destruct (even_2n (Zabs_nat x) H) as [d Hd].
 rewrite <- Zabs_eq, <- inj_Zabs_nat, Hd.
 unfold double.
 cutrewrite (d + d = 2 * d)%nat.
 rewrite inj_mult.
 change (Zeven (2 * Z_of_nat d)).
 apply Zeven_2p.
 omega.
 trivial.
Qed.

Lemma Zeven_of_even : forall x, Zeven (Z_of_nat x) -> even x.
Proof.
 intros x H.
 destruct (Zeven_ex (Z_of_nat x) H) as [d Hd].
 rewrite <- Zabs_nat_Z_of_nat, Hd, Zabs_nat_mult.
 change (even (2 * Zabs_nat d)).
 auto with arith.
Qed.

Lemma Zeven_minus : forall x y, Zeven x -> Zeven y -> Zeven (x - y).
Proof.
 intros x y Hx Hy.
 destruct (Zeven_ex x Hx) as [x' Hx'].
 destruct (Zeven_ex y Hy) as [y' Hy'].  
 subst.
 cutrewrite (2 * x' - 2 * y' = 2 * (x' - y')).
 apply Zeven_2p.
 omega.
Qed.

Lemma rel_prime_minus_1 : forall x, rel_prime (-1) x.
Proof.
 intro x.
 apply bezout_rel_prime.
 apply Zis_gcd_bezout.
 apply Zis_gcd_minus.
 simpl.
 apply Zis_gcd_1.
Qed.

Lemma Zpower_nat_Zpower x m : Zpower x (Z_of_nat m) = Zpower_nat x m.
Proof.
 intros; unfold Zpower_nat; induction m.
 simpl; trivial.
 cutrewrite (x ^ Z_of_nat (S m) = x * x ^ Z_of_nat m).
 simpl; rewrite <- IHm; trivial.
 cutrewrite (S m = m + 1)%nat;[ | ring].
 rewrite inj_plus, Zpower_exp; simpl.
 unfold Zpower_pos; simpl.
 ring.
 generalize (Zle_0_nat m); omega.
 omega.
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

Lemma Zdiv_Zdiv2 a : a >= 0 -> Zdiv2 a = Zdiv a 2.
Proof.
 intros a Ha.
 destruct (Zeven_odd_dec a) as [H1 | H1].
 
 apply Zeven_div2 in H1.
 rewrite H1 at 2.
 rewrite Zmult_comm.
 rewrite Z_div_mult_full; trivial.
 omega.
 
 destruct (Zodd_ex _ H1).
 rewrite H.
 cutrewrite (2 * x + 1 = Zsucc (2 * x)).
 rewrite <- (Zdiv_unique (Zsucc (2 * x)) 2 x 1).
 rewrite Zdiv2_S_double.
 trivial.
 omega.
 omega.
 auto.
 auto.
Qed.

Lemma Zlt_is_not_lt_bool: forall n m : Z, n >= m <-> Zlt_bool n m = false.
Proof.
 intros; split; intros.
 apply not_true_is_false.
 intro Heq.
 apply Zlt_is_lt_bool in Heq.
 omega.
 generalize (Zlt_cases n m).
 rewrite H.
 trivial.
Qed.

Lemma Zle_is_not_le_bool: forall n m : Z, n > m <-> Zle_bool n m = false.
Proof.
 intros; split; intros.
 apply not_true_is_false.
 intro Heq.
 apply Zle_is_le_bool in Heq.
 omega.
 generalize (Zle_cases n m).
 rewrite H.
 trivial.
Qed.

Lemma Zle_lt_2 a b : a <= b -> a <> b -> a < b.
Proof.
 intros; omega.
Qed.

Lemma Zmod_ex a b c (W : b <> 0) : a mod b = c -> a = b * (a / b) + c.
Proof.
 intros.
 rewrite <- H.
 apply Z_div_mod_eq_full; trivial.
Qed.

Lemma Zopp_Zminus x : - x = (-1) * x.
Proof.
 intros; ring.
Qed.

Lemma Zdiv2_small : forall a n: Z, 
 0 < Zdiv2 a -> Zdiv2 a < n < a -> a - n <= Zdiv2 a.
Proof.
 intros.
 destruct (Zeven_odd_dec a) as [H1 | H1].
 apply Zeven_div2 in H1; omega.
 destruct (Zodd_ex _ H1).
 assert (Zdiv2 a = x).
 rewrite H2.
 cutrewrite (2 * x + 1 = Zsucc (2 * x)).
 rewrite Zdiv2_S_double.
 trivial.
 omega.
 unfold Zsucc; trivial.
 omega.
Qed. 

Lemma Zdiv2_small_mod a n (W : Zodd a) (W' : a >= 0) (W'' : n mod a <> 0) : 
 - n mod a <= Zdiv2 a -> Zdiv2 a < n mod a.
Proof.
 intros.
 rewrite Z_mod_nz_opp_full in H.
 apply Zlt_0_minus_lt.
 apply Zle_left in H.
 ring_simplify in H.
 apply Zle_lt_trans with (Zdiv2 a - a + n mod a); trivial.
 cutrewrite (Zdiv2 a - a + n mod a =  n mod a + ( Zdiv2 a - a )); [ | ring ].
 cutrewrite (n mod a - Zdiv2 a = n mod a + - Zdiv2 a).
 apply Zplus_lt_compat_l.
 apply Zlt_0_minus_lt.
 rewrite (Zodd_div2 a) at 3.
 ring_simplify.
 omega.
 trivial.
 trivial.
 ring.
 trivial.
Qed.

Lemma Zdiv2_small_mod_bis a n (W : Zodd a) (W' : a >= 0) (W'' : n mod a <> 0): 
 - n mod a < Zdiv2 a -> Zdiv2 a < n mod a.
Proof.
 intros.
 rewrite Z_mod_nz_opp_full in H.
 apply Zlt_0_minus_lt.
 apply Zlt_left in H.
 ring_simplify in H.
 apply Zle_lt_trans with ( Zdiv2 a - a + n mod a - 1); trivial.
 cutrewrite (Zdiv2 a - a + n mod a - 1 = n mod a + ( Zdiv2 a - a - 1 )); [ | ring ].
 cutrewrite (n mod a - Zdiv2 a = n mod a + - Zdiv2 a).
 apply Zplus_lt_compat_l.
 apply Zlt_0_minus_lt.
 rewrite (Zodd_div2 a) at 3.
 ring_simplify.
 omega.
 trivial.
 trivial.
 ring.
 trivial.
Qed.

Lemma Zdiv2_small_mod_bis_rev a n (W : Zodd a) (W' : a >= 0) (W'' : n mod a <> 0) :
 - n mod a > Zdiv2 a -> Zdiv2 a >= n mod a.
Proof.
 intros.
 rewrite Z_mod_nz_opp_full in H.
 apply Zle_ge.
 apply Zgt_lt in H.
 apply Zle_0_minus_le.
 apply Zlt_left in H.
 ring_simplify in H.
 apply Zle_trans with ( a - n mod a - Zdiv2 a - 1); trivial.
 apply Zle_0_minus_le.
 rewrite (Zodd_div2 a) at 3.
 ring_simplify.
 omega.
 trivial.
 trivial.
 trivial.
Qed.

Lemma Zeven_mod n : n mod 2 = 0 -> Zeven n.
Proof.
 intros.
 apply Zmod_divide in H.
 inversion H; subst.
 rewrite Zmult_comm.
 apply Zeven_2p.
 omega.
Qed.
 
Lemma Zmod_opp_diff_0 n m : n mod m <> 0 -> - n mod m <> 0.
Proof.
 intros.
 intro Heq; apply H; clear H.
 apply Z_mod_zero_opp_full in Heq.
 rewrite Zopp_involutive in Heq.
 trivial.
Qed.

Lemma Zmod_pos x n (W : 0 < n): 0 <= x mod n.
Proof.
 intros; generalize (Z_mod_lt x n); omega.
Qed.

Lemma Zmod_bound x n (W : 0 < n): x mod n < n.
Proof.
 intros; generalize (Z_mod_lt x n); omega.
Qed.

Lemma not_Zle_lt: forall n m : Z, ~ n <= m -> m < n.
Proof.
 intros; omega.
Qed.

Lemma not_Zlt_le: forall n m : Z, ~ n < m -> m <= n.
Proof.
 intros; omega.
Qed.

Lemma mod_mult_0 : forall p a b : Z,
 prime p -> (a * b) mod p = 0 -> a mod p = 0 \/ b mod p = 0.
Proof.
 intros.
 apply Zmod_divide_minus in H0.
 rewrite Zminus_0_r in H0.  
 apply prime_mult in H0; [ | trivial].
 destruct H0; apply Zdivide_mod in H0; auto.
 apply prime_ge_2 in H; omega.
Qed.


(** Multiplicative inverse modulo *)

Definition Zinv_mod (a q:Z) := 
 let (p,_) := eeuclid a q in let (u,_) := p in u mod q.

Lemma Zinv_mod_spec : forall (a q:Z), 
 1 < q -> Zis_gcd a q 1 -> (a * Zinv_mod a q) mod q = 1.
Proof.
 intros a q Hlt H; unfold Zinv_mod.
 generalize (eeuclid_spec a q).
 destruct (eeuclid a q) as ((u, v), d).
 intro H0; destruct (H0 u v d (refl_equal _)) as [Heq [Hgcd Hle] ].
 destruct (Zis_gcd_unique a q d 1 Hgcd H); [ | exfalso; omega].
 rewrite Zmult_mod_idemp_r.
 rewrite <- (Z_mod_plus_full _ v), Zmult_comm, Heq, H1, Zmod_1_l; trivial.
Qed.

Lemma Zinv_mod_bound : forall (a q:Z), 
 0 < q -> 0 <= Zinv_mod a q < q.
Proof.
 intros a q Hlt; unfold Zinv_mod.
 destruct (eeuclid a q) as ((u, v), d).
 split; [apply Zmod_pos | apply Z_mod_lt]; omega.
Qed.


(** nmod *)

Definition nmod a b := Zabs_nat (Zmod (Z_of_nat a) (Z_of_nat b)).

Close Scope Z_scope.

Infix "mod" := nmod.

Lemma mod_unique: forall a b p r, 
 0 <= r < b ->
 a = b * p + r -> r = a mod b.
Proof.
 intros; unfold nmod.
 apply inj_eq_rev.
 rewrite inj_Zabs_nat, Zabs_eq.
 apply Zmod_unique with (Z_of_nat p).
 omega.
 rewrite <- inj_mult, <- inj_plus; apply inj_eq; trivial.
 apply Zmod_pos; omega.
Qed.

Lemma mod_0_l: forall a, 0 mod a = 0.
Proof.
 destruct a; simpl; auto.
Qed.

Lemma mod_0_r: forall a, a mod 0 = 0.
Proof.
 destruct a; simpl; auto.
Qed.

Lemma mod_1_l: forall a, 1 < a -> 1 mod a = 1.
Proof.
 intros; symmetry; apply mod_unique with 0; auto with zarith.
Qed.

Lemma mod_1_r: forall a, a mod 1 = 0.
Proof.
 intros; symmetry; apply mod_unique with a; auto with zarith.
Qed.

Lemma mod_same : forall a, a mod a = 0.
Proof.
 intros.
 destruct (zerop a) as [H | H].
 rewrite H, mod_0_r; trivial.
 symmetry; apply mod_unique with 1; omega.
Qed.

Lemma mod_mult : forall a b,
 (a * b) mod b = 0.
Proof.
 intros.
 destruct (zerop b) as [H | H].
 rewrite H, mod_0_r; trivial.
 symmetry; apply mod_unique with a.
 auto with arith.
 rewrite mult_comm, plus_0_r; trivial.
Qed.

Lemma mod_small : forall a n,
 0 <= a < n -> a mod n = a.
Proof.
 intros; symmetry; apply mod_unique with 0; auto with zarith.
Qed.

Lemma mult_mod : forall a b n,
 (a * b) mod n = a mod n * (b mod n) mod n.
Proof.
 intros.
 destruct (zerop n) as [H | H].
 subst; rewrite mod_0_r, mod_0_r; trivial.
 unfold nmod.
 rewrite inj_mult, Zmult_mod.
 rewrite <- Zabs_nat_mult, inj_Zabs_nat, Zabs_eq; trivial.
 apply Zmult_le_0_compat; apply Zmod_pos; omega.
Qed.

Lemma mult_mod_idemp_r : forall a b n, 
 (b * (a mod n)) mod n = (b * a) mod n.
Proof.
 intros; unfold nmod.
 destruct (zerop n) as [H | H].
 rewrite H, Zmod_0_r, Zmod_0_r; trivial.
 rewrite inj_mult, inj_Zabs_nat, Zabs_eq.
 rewrite Zmult_mod_idemp_r, inj_mult; trivial.
 apply Zmod_pos; omega.
Qed.

Lemma mod_lt : forall a b,
 0 < b ->  0 <= a mod b < b.
Proof.
 intros; unfold nmod. 
 split.
 apply inj_le_rev.
 rewrite inj_Zabs_nat, Zabs_eq; apply Zmod_pos; omega.
 apply inj_lt_rev.
 rewrite inj_Zabs_nat, Zabs_eq.
 apply Zmod_bound.
 omega.
 apply Zmod_pos; omega.
Qed.

Lemma mod_mod : forall a p,
 a mod p mod p = a mod p.
Proof.
 intros; destruct (zerop p) as [H | H].
 subst; rewrite mod_0_r, mod_0_r; trivial.
 rewrite mod_small; trivial.
 apply mod_lt; trivial.
Qed.

Lemma mod_plus : forall a b n, (a + b) mod n = ((a mod n) + (b mod n)) mod n.
Proof.
 intros; destruct (zerop n) as [Hn | Hn].
 subst; rewrite mod_0_r; rewrite mod_0_r; trivial.
 destruct (quotient _ Hn a) as (qa, (ra,(H1a,H2a))); rewrite mult_comm in H1a.
 destruct (quotient _ Hn b) as (qb, (rb,(H1b,H2b))); rewrite mult_comm in H1b.
 destruct (quotient _ Hn (ra + rb)) as (qr, (r,(H1r,H2r))); rewrite mult_comm in H1r.
 rewrite <-(mod_unique a n qa ra), <-(mod_unique b n qb rb); auto with arith.
 rewrite <-(mod_unique (ra + rb) n qr r); auto with arith.    
 symmetry; apply mod_unique with (qa + qb + qr).
 auto with arith.
 subst; transitivity (n * qa + n * qb + (ra + rb)); [ ring | ].
 rewrite H1r; ring.
 Qed.

Definition inv_mod (q a:nat) := Zabs_nat (Zinv_mod (Z_of_nat a) (Z_of_nat q)).

Lemma inv_mod_prime : forall a p,
 prime (Z_of_nat p) ->
 0 < a < p ->
 (a * inv_mod p a) mod p = 1.
Proof.
 intros.
 unfold inv_mod, nmod.
 rewrite inj_mult, inj_Zabs_nat, Zabs_eq.
 rewrite Zinv_mod_spec; trivial.
 apply prime_ge_2 in H; omega.
 apply Zis_gcd_prime; trivial; omega.
 
 unfold Zinv_mod.
 destruct (eeuclid (Z_of_nat a) (Z_of_nat p)).
 destruct p0.
 apply Zmod_pos.
 apply prime_ge_2 in H; omega.
Qed.

Lemma inv_mod_neq_0 : forall a p,
 (1 < Z_of_nat p)%Z ->
 Zis_gcd (Z_of_nat a) (Z_of_nat p) 1 ->
 0 < a ->
 inv_mod p a <> 0.
Proof.
 unfold inv_mod; intros a p Hp Hgcd Hlt Heq.
 generalize (Zinv_mod_spec _ _ Hp Hgcd).
 change 0 with (Zabs_nat (Z_of_nat 0)) in Heq.
 apply inj_eq in Heq.
 simpl in Heq; rewrite inj_Zabs_nat in Heq.
 apply Zabs_0_inv in Heq.
 rewrite Heq, Zmult_0_r, Zmod_0_l; intro; discriminate.
Qed.

Lemma inv_mod_bound: forall n p,
  0 < p  ->
  inv_mod p n < p.
Proof.
  unfold inv_mod; intros.
  rewrite <-(Zabs_nat_Z_of_nat p); apply Zabs_nat_lt.
  rewrite Zabs_nat_Z_of_nat; apply Zinv_mod_bound. 
  apply (inj_lt 0 p H).
Qed.


