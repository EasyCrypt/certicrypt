(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** ClawFreeFactoring.v: An instantce of a Sigma-protocol based on
   claw-free trapdoor permutations.
*)

Add LoadPath "..".
Add LoadPath "Pocklington".

Require Import Homomorphism.
Require Import ClawFree.
Require Import ZArith Arith Even Div2.
Require Import Euclid.
Require Import LtIrrelevance.
Require Import FilterMap.
Require Import Program.
Require Import Zpow_facts.
Require Import LittleFermat.
Require Import Epsilon.
Require Import Zstar.
Require Import PrimeLib.

Set Implicit Arguments.

Open Scope Z_scope.

Module Type PARAMETERS.

 Parameters p q : nat -> Z.

 Parameter distinct : forall k, p k <> q k.

 Parameter p_prime : forall k, prime (p k).

 Parameter q_prime : forall k, prime (q k). 

 Parameter p_blum_8 : forall k, (p k) mod 8 = 3.

 Parameter q_blum_8 : forall k, (q k) mod 8 = 7.

 Parameter p_neq_3 : forall k, p k <> 3.
  
 Parameter p_poly : polynomial.
 
 Parameter p_poly_spec : forall k, (size_Z (p k) < peval p_poly k)%nat.
 
 Parameter q_poly : polynomial.
 
 Parameter q_poly_spec : forall k, (size_Z (q k) < peval q_poly k)%nat.

End PARAMETERS.


Module Dn (DP:PARAMETERS) <: GROUP.

 Import DP.

 Lemma not_Zeven_Zodd : forall p, ~Zeven p -> Zodd p.
 Proof.
  intros; case (Zeven_odd_dec p0); firstorder.
 Qed.

 Lemma prime_gt_2_Zodd : forall p : Z, prime p -> p > 2 -> Zodd p.
 Proof.
  intros.
  apply not_Zeven_Zodd.
  intro H1.
  apply Zeven_ex in H1.
  destruct H.
  assert (rel_prime 2 p0) by (apply H2; omega).
  destruct H1.
  subst; contradict H3; clear.
  intros H; unfold rel_prime in H.
  assert (Zis_gcd (2 * 1) (2 * x) (2 * 1)).
  apply Zis_gcd_mult.
  apply Zis_gcd_sym; apply Zis_gcd_1.
  change (2 * 1) with 2 in H0.
  generalize (Zis_gcd_unique _ _ _ _ H H0); intro; omega.
 Qed.

 Lemma p_odd : forall k, Zodd (p k).
 Proof.
  intros.
  apply prime_gt_2_Zodd.
  apply p_prime.
  assert (H:=p_blum_8 k).
  assert (H0:=prime_ge_2 _ (p_prime k)). 
  assert (3 <= p k).
  rewrite <- H; apply Zmod_le; omega.
  omega.
 Qed.
 
 Lemma q_odd : forall k, Zodd (q k).
 Proof.
  intros.
  apply prime_gt_2_Zodd.
  apply q_prime.
  assert (H:=q_blum_8 k).
  assert (H0:=prime_ge_2 _ (q_prime k)). 
  assert (7 <= q k).
  rewrite <- H; apply Zmod_le; omega.
  omega. 
 Qed.

 Lemma lt_p_4 : forall k, 4 < p k.
 Proof.
  intros. 
  assert (H:=p_blum_8 k).
  assert (H0:=prime_ge_2 _ (p_prime k)). 
  assert (3 <= p k).
  rewrite <- H; apply Zmod_le; omega.
  assert (p k <> 4).
  intro Heq.
  assert (prime 4).
  rewrite <- Heq; apply p_prime.
  destruct H2.
  assert (rel_prime 2 4).
  apply H3; omega.
  unfold rel_prime in H4.
  apply Zis_gcd_gcd in H4; simpl in H4.
  discriminate.
  omega.
  generalize (@p_neq_3 k); intro.
  omega.
 Qed.

 Lemma lt_q_4 : forall k, 4 < q k.
 Proof.
  intros. 
  assert (H:=q_blum_8 k).
  assert (H0:=prime_ge_2 _ (q_prime k)). 
  assert (7 <= q k).
  rewrite <- H; apply Zmod_le; omega.
  omega.
 Qed.

 Lemma p_blum : forall k, (p k) mod 4 = 3.
 Proof.
  intros.
  rewrite (Zmod_div_mod 4 8).
  rewrite p_blum_8; compute; trivial.
  omega.
  omega.
  change 8 with (4 * 2); auto with zarith.
 Qed.

 Lemma q_blum : forall k, (q k) mod 4 = 3.
 Proof.
  intros.
  rewrite (Zmod_div_mod 4 8).
  rewrite q_blum_8; compute; trivial.
  omega.
  omega.
  change 8 with (4 * 2); auto with zarith.
 Qed.

 Lemma p_diff_2 k : p k <> 2.
 Proof.
  intros k H.
  generalize (p_blum k); intro Hmod.
  rewrite H in Hmod.
  compute in Hmod.
  omega.
 Qed.

 Lemma q_diff_2 k : q k <> 2.
 Proof.
  intros k H.
  generalize (q_blum k); intro Hmod.
  rewrite H in Hmod.
  compute in Hmod.
  omega.
 Qed.

 Lemma rel_prime_p_q : forall k, rel_prime (p k) (q k).
 Proof.
  intro k.
  apply prime_rel_prime.
  apply p_prime.
  intro H.
  apply prime_div_prime in H.
  apply (distinct H).
  apply p_prime.
  apply q_prime.
 Qed.

 Lemma p_blum_mod_0 k : (p k + 1) mod 4 = 0.
 Proof.
  intros.
  generalize (p_blum k); intros.
  rewrite Zplus_mod.
  rewrite H; compute; trivial.
 Qed.
 
 Lemma q_blum_mod_0 k : (q k + 1) mod 4 = 0.
 Proof.
  intros.
  generalize (q_blum k); intros.
  rewrite Zplus_mod.
  rewrite H; compute; trivial.
 Qed.

 Lemma Zeven_q k : Zeven ((q k + 1) / 4).
 Proof.
  intros k.
 
  assert (Hmod : (4 | (q k) + 1)).
  apply Zmod_divide; [ omega | ].
  rewrite Zplus_mod.
  rewrite q_blum; compute; trivial.
  
  assert (Hmod' : (8 | (q k) + 1)).
  apply Zmod_divide; [ omega | ].
  rewrite Zplus_mod.
  rewrite q_blum_8; compute; trivial.
  
  apply Zeven_mod.
  apply Z_div_exact_full_1.
  inversion Hmod.
  
  rewrite H in Hmod'.
  inversion Hmod'.

  rewrite H.
  rewrite H0 at 2.
  rewrite Zdiv_Zdiv; try omega.
  change (4 * 2) with 8.
  repeat rewrite Zdivide_Zdiv_eq_2; try omega; auto with zarith.
  repeat rewrite Z_div_same_full; try omega.
 Qed.

 Definition jacobi k x := jacobi (p k) (q k) (p_prime k) (q_prime k) x.

 Definition P k (x : carrier (p k * q k)): bool := 
  Zeq_bool (jacobi k (proj1_sig x)) 1 && 
  Zlt_bool 0 (proj1_sig x) && 
  Zle_bool (proj1_sig x) (Zdiv2 (p k * q k)).

 Lemma eq_P : forall k (x : carrier (p k * q k)) (H1:P k x) (H2:P k x), H1 = H2.
 Proof.
  intros.
  apply eq_proofs_unicity.
  intros a b; case (bool_dec a b); auto.
 Qed.

 Lemma P_prop : forall k (x : carrier (p k * q k)), 
  P k x <-> jacobi k (proj1_sig x) = 1 /\ 0 < (proj1_sig x) <= Zdiv2 (p k * q k).
 Proof. 
  intros k x.
  unfold P; split; intros.
  
  apply andb_prop in H; destruct H.  
  apply andb_prop in H; destruct H.  
  split.
  apply Zeq_is_eq_bool in H; trivial.
  split.
  
  apply <- Zlt_is_lt_bool; trivial.
  apply <- Zle_is_le_bool; trivial.
  
  destruct H.
  apply andb_true_intro; split.
  apply andb_true_intro; split.
  apply -> Zeq_is_eq_bool; trivial.
  apply -> Zlt_is_lt_bool; omega.
  apply -> Zle_is_le_bool; omega.
 Qed.

 Definition t k : Set := 
  @sigT (carrier (p k * q k)) (fun x : carrier (p k * q k) => is_true (@P k x)).

 Definition elems k : list (t k) := 
  filter_map (@P k) (@existT _ _) 
  (Zstar_list (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))).

 Definition e_nowak k := neutral (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).

 Lemma P_e : forall k, P k (e_nowak k).
 Proof.
  intros.
  apply <- P_prop.
  unfold jacobi.
  split.
  apply jacobi_1.
  simpl; split;[ omega | ].
  rewrite Zdiv_Zdiv2.
  change 1 with (1 * 1).
  assert (Hp_diff := @p_diff_2 k).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hp_prime := @p_prime k).
  assert (Hq_prime := @q_prime k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  apply Zle_trans with (2 * 2 / 2).
  simpl.
  cutrewrite (4 / 2 = 2).
  omega.
  compute; trivial.
  apply Z_div_le.
  omega.
  apply Zmult_le_compat; omega.
  generalize (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)); omega.  
 Qed.

 Lemma elems_not_nil : forall k, elems k <> nil.
 Proof.
  intro k; unfold elems.
  
  assert (In (e_nowak k) (Zstar_list (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))).
  apply (Zstar_list_spec (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))  (e_nowak k)).
  
  intro Heq.
  apply In_filter_map with (f:=@existT _ _) (H:=P_e k) in H.
  rewrite Heq in H.
  inversion H.
 Qed.

 Lemma elems_full : forall k (x:t k), In x (elems k).
 Proof.
  intros k (x,H).
  apply In_filter_map.
  apply (Zstar_list_spec (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) x).
 Qed.

 Lemma elems_nodup : forall k, NoDup (elems k).
 Proof.
  intro k; unfold elems.
  apply NoDup_filter_map_inj.
  intros x y H1 H2 H; injection H; trivial.
  apply (NoDup_Zstar_list (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))).
 Qed.

 Definition eqb k (x y:t k) : bool :=
  match x, y with
   | existT (exist n _) _, existT (exist m _) _ => Zeq_bool n m
  end.

 Lemma eqb_spec : forall k (x y:t k), if eqb x y then x = y else x <> y.
 Proof.
  intros k ((a,Ha),Ha') ((b,Hb),Hb'); unfold eqb.
  case_eq (Zeq_bool a b); intros.
  apply subsetT_eq_compat.
  apply subset_eq_compat.
  apply Zeq_bool_eq; trivial.
  
  intro Heq.
  injection Heq.
  apply Zeq_bool_neq; trivial.
 Qed.

 Definition e k : t k.
 intros k.
 refine (exist _ (e_nowak k) _).
 apply P_e.
 Defined.

 Lemma P_mul_1 k a b : P k a -> P k b ->
  proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) a b) <= Zdiv2 (p k * q k) ->
  P k (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) a b).
 Proof.
  intros k a b Ha Hb H; simpl in *.
  
  assert (Hp_diff := @p_diff_2 k).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hp_prime := @p_prime k).
  assert (Hq_prime := @q_prime k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  assert (Hpq_lt_1 := Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
  
  apply <- P_prop.
  apply -> P_prop in Ha.
  apply -> P_prop in Hb.
  destruct Ha.
  destruct Hb.
  split.
  unfold jacobi in *.
  simpl; rewrite jacobi_mod.
  unfold Zstar.jacobi in *.
  repeat rewrite legendre_mult.
  ring [H0 H2].
  apply q_odd.
  apply p_odd.
  
  destruct a as [a [Ha1 Ha2]]; destruct b as [b [Hb1 Hb2]]; simpl in *;split; [ | trivial].
  
  apply Zle_lt.
  intro Heq.
  apply Zmod_divide in Heq.
  assert (rel_prime (a * b) (p k * q k)).
  apply rel_prime_sym;apply rel_prime_mult; apply rel_prime_sym; trivial.
  apply MiscZArith.Z_rel_prime_not_divide in H4.
  apply H4; trivial.
  omega.
  omega.
  apply Zmod_pos.
  omega.
 Qed.
 
 Lemma P_mul_2 k a b : 
  P k a -> 
  P k b -> 
  ~ proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) a b) <= Zdiv2 (p k * q k) ->
  P k (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) a b)).
Proof.
  intros k a b Ha Hb H; simpl in *.
  
  assert (Hp_diff := @p_diff_2 k).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hp_prime := @p_prime k).
  assert (Hq_prime := @q_prime k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  assert (Hpq_lt_1 := Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
  
  apply <- P_prop.
  apply -> P_prop in Ha.
  apply -> P_prop in Hb.
  destruct Ha.
  destruct Hb.
  split.
  unfold jacobi in *.
  unfold Zstar.jacobi in *.
  rewrite <- (legendre_fst (p k) (q k) (p_prime k) (q_prime k)).
  rewrite <- (legendre_snd (p k) (q k) (p_prime k) (q_prime k)).
  rewrite fst_opp, snd_opp; simpl in *.
  repeat rewrite legendre_mod; repeat rewrite legendre_opp.
  assert (forall x y, x * y = - x * - y) by (intros; ring).
  rewrite <- H4.
  repeat rewrite <- Zmod_div_mod; try omega.
  repeat rewrite legendre_mod.
  repeat rewrite legendre_mult.
  ring [H0 H2].
  apply q_odd.
  apply p_odd.
  apply Zdivide_factor_l.
  apply Zdivide_factor_r.
  apply q_odd.
  apply q_blum.
  apply p_odd.
  apply p_blum.

  simpl in *.
  destruct a as [a [Ha1 Ha2]]; destruct b as [b [Hb1 Hb2]]; simpl in *.

  assert (((a * b) mod (p k * q k)) mod (p k * q k) <> 0).
  intro Heq.
  rewrite Zmod_mod in Heq.
  apply Zmod_divide in Heq.
  assert (rel_prime (a * b) (p k * q k)).
  apply rel_prime_sym;apply rel_prime_mult; apply rel_prime_sym; trivial.
  apply MiscZArith.Z_rel_prime_not_divide in H4.
  apply H4; trivial.
  omega.
  omega.

  split; [ | trivial].
  
  apply Zle_lt.
  intro Heq.
  apply Z_mod_zero_opp_full in Heq.
  rewrite Zopp_involutive in Heq.
  omega.
  apply Zmod_pos.
  omega.
  
  rewrite Z_mod_nz_opp_full.
  rewrite Zmod_mod.
  apply Zdiv2_small.
  omega.
  split.
  omega.
  generalize (Z_mod_lt (a * b) (p k * q k)); omega.
  trivial.
 Qed.

 Definition mul : forall k, t k -> t k -> t k.
 intros k (a ,Ha) (b,Hb).  
 assert (Hpq_lt_1 := Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
 case_eq (Z_le_dec (proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) a b)) (Zdiv2 (p k * q k))); intros H _.
 refine (exist _ (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) a b) (P_mul_1 _ _ _ Ha Hb H)).
 refine (exist _ (opp _ (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) a b)) (P_mul_2 _ _ _ Ha Hb H)).
 Defined.

 Definition sqr k (x : t k) := mul x x.
 
 Lemma mult_1 x y : x * y = 1 <-> (x = 1 /\ y = 1) \/ (x = -1 /\ y = -1).
 Proof.
  intros; split; intros.
  generalize H.
  apply Zmult_1_inversion_l in H.
  destruct H;[left | right]; subst; split;omega.
  destruct H as [ [Ha1 Ha2] | [Ha1 Ha2] ]; subst; ring.
 Qed.
  
 Lemma mult_group2mult : forall n (x y: carrier n) (W : 1 < n), 
  mult n W x y = Group2.mult (Zstar n W) x y.
 Proof.
  auto.
 Qed.

 Lemma neutral_group2neutral : forall n (W : 1 < n),
  neutral n W = Group2.neutral (Zstar n W).
 Proof.
  auto.
 Qed.

 Lemma opp_mult_opp k x y : mult (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) x y = 
  opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (mult (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) x) y).
 Proof.
  intros.
  rewrite (mult_comm _ _ (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) x)), (mult_comm _ _ x y).
  repeat rewrite mult_group2mult.
  rewrite opp_mult_l, mult_opp; trivial.
 Qed.

 Lemma opp_mult_mult k x y z : opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (mult (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) x (mult (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) y z)) =
  mult (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (mult (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) x y)) z.
 Proof.
  intros.
  rewrite associative.
  repeat rewrite mult_group2mult.
  rewrite opp_mult_l; trivial.
 Qed.
 
 Lemma mult_opp_mult k x y z : mult (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) x (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (mult (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) y z)) =
  opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (mult (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (mult (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) x y) z).
 Proof.
  intros.
  rewrite <- associative.
  generalize (mult (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) y z); intros yz.
  rewrite (mult_comm _ _ x yz).
  repeat rewrite mult_group2mult.
  rewrite opp_mult_l.
  repeat rewrite <- mult_group2mult.
  rewrite mult_comm.
  trivial.
 Qed.

 (*  Specification *)
 Lemma mul_assoc : forall k (x y z:t k), mul x (mul y z) = mul (mul x y) z.
 Proof.
  intros k ((x,Hx'), Hx) ((y,Hy'), Hy) ((z,Hz'), Hz); unfold mul; simpl in *.
  
  assert (Hp_diff := @p_diff_2 k).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hp_prime := @p_prime k).
  assert (Hq_prime := @q_prime k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  assert (Hpq_lt_1 := Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
  assert (Zodd (p k * q k)).
  apply Zodd_mult_Zodd;[ apply p_odd | apply q_odd ].

  case ( Z_le_dec ((y * z) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros H1.
    case ( Z_le_dec ((x * ((y * z) mod (p k * q k))) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros H2.
      case ( Z_le_dec ((x * y) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros H3.
        case ( Z_le_dec (((x * y) mod (p k * q k) * z) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros H4.
          apply subsetT_eq_compat.
          apply associative.
          
          elimtype False.
          rewrite Zmult_mod_idemp_l in H4.
          rewrite Zmult_mod_idemp_r in H2.
          rewrite Zmult_assoc in H2; omega.

        case (Z_le_dec ((- ((x * y) mod (p k * q k)) mod (p k * q k) * z) mod (p k * q k)) (Zdiv2 (p k * q k))); intros H4.
          elimtype False.
          rewrite Zmult_mod_idemp_r in H2.
          rewrite Zopp_Zminus in H4.
          rewrite Zmult_mod_idemp_r in H4.
          rewrite Zmult_mod_idemp_l in H4.
          cutrewrite (-1 * (x * y) * z = - (x * (y * z))) in H4;[ | ring ].
          apply Zdiv2_small_mod in H4.
          omega.
          trivial.
          omega.
          intro Heq.
          apply Zmod_divide in Heq.
          assert (rel_prime (x * (y * z)) (p k * q k)).
          apply rel_prime_sym;apply rel_prime_mult; apply rel_prime_sym; trivial.
          apply P_prop in Hx; simpl in Hx; tauto.
          apply P_prop in Hy; simpl in Hy.
          apply P_prop in Hz; simpl in Hz.
          apply rel_prime_sym;apply rel_prime_mult; apply rel_prime_sym; trivial; tauto.
          apply MiscZArith.Z_rel_prime_not_divide in H0.
          apply H0; trivial.
          omega.
          omega.
          
          apply subsetT_eq_compat.
          rewrite <- opp_mult_opp, associative; trivial.

      case ( Z_le_dec ((x * y) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros H3.

        case ( Z_le_dec (((x * y) mod (p k * q k) * z) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros H4.
          elimtype False.
          rewrite Zmult_mod_idemp_r in H2.
          rewrite Zmult_mod_idemp_l in H4.
          rewrite Zmult_assoc in H2; omega.
          
          apply subsetT_eq_compat.
          rewrite <- associative; trivial.
            
        case (Z_le_dec ((- ((x * y) mod (p k * q k)) mod (p k * q k) * z) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros H4.
          apply subsetT_eq_compat.
          rewrite opp_mult_mult; trivial.
          
          elimtype False.
          rewrite Zmult_mod_idemp_r in H2.
          rewrite Zopp_Zminus in H4.
          rewrite Zmult_mod_idemp_r in H4.
          rewrite Zmult_mod_idemp_l in H4.
          cutrewrite (-1 * (x * y) * z = - (x * (y * z))) in H4;[ | ring ].
          apply H4.
          rewrite Z_mod_nz_opp_full.
          apply Zdiv2_small.
          apply MiscZArith.Zdiv2_pos.
          omega.
          split.
          omega.
          generalize (Z_mod_lt ((x * (y * z))) (p k * q k)).
          omega.
          intro Heq.
          apply Zmod_divide in Heq.
          assert (rel_prime (x * (y * z)) (p k * q k)).
          apply rel_prime_sym;apply rel_prime_mult; apply rel_prime_sym; trivial.
          apply P_prop in Hx; simpl in Hx; tauto.
          apply P_prop in Hy; simpl in Hy.
          apply P_prop in Hz; simpl in Hz.
          apply rel_prime_sym;apply rel_prime_mult; apply rel_prime_sym; trivial; tauto.
          apply MiscZArith.Z_rel_prime_not_divide in H0.
          apply H0; trivial.
          omega.
          omega.
      
    case (Z_le_dec ((x * (- ((y * z) mod (p k * q k)) mod (p k * q k))) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intro H2.
      case ( Z_le_dec ((x * y) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros H3.
        case ( Z_le_dec (((x * y) mod (p k * q k) * z) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros H4.
          elimtype False.
          rewrite Zmult_mod_idemp_r in H2.
          rewrite Zopp_Zminus in H2.
          rewrite Zmult_assoc in H2.
          rewrite Zmult_mod_idemp_r in H2.
          rewrite Zmult_mod_idemp_l in H4.
          cutrewrite (x * -1 * (y * z) = - (x * y * z)) in H2;[ | ring ].
          apply Zdiv2_small_mod in H2.
          omega.
          trivial.
          omega.
          intro Heq.
          apply Zmod_divide in Heq.
          assert (rel_prime (x * y * z) (p k * q k)).
          apply rel_prime_sym;apply rel_prime_mult; apply rel_prime_sym.
          apply P_prop in Hx; simpl in Hx.
          apply P_prop in Hy; simpl in Hy.
          apply rel_prime_sym;apply rel_prime_mult; apply rel_prime_sym; trivial; tauto.
          apply P_prop in Hz; simpl in Hz; tauto.
          apply MiscZArith.Z_rel_prime_not_divide in H0.
          apply H0; trivial.
          omega.
          omega.
        
          apply subsetT_eq_compat.
          rewrite mult_opp_mult; trivial.
              
        case ( Z_le_dec ((- ((x * y) mod (p k * q k)) mod (p k * q k) * z) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros H4.
          apply subsetT_eq_compat.
          rewrite mult_opp_mult.
          rewrite <- opp_mult_mult.
          rewrite associative; trivial.

          elimtype False.
          rewrite Zmult_mod_idemp_r in H2.
          rewrite Zopp_Zminus in H2.
          rewrite Zmult_assoc in H2.
          rewrite Zmult_mod_idemp_r in H2.
          rewrite Zopp_Zminus in H4.
          rewrite Zmult_mod_idemp_r in H4.
          rewrite Zmult_mod_idemp_l in H4.
          cutrewrite (x * -1 * (y * z) = - (x * y * z)) in H2;[ | ring ].
          cutrewrite (-1 * (x * y) * z = - (x * y * z)) in H4;[ | ring ].
          apply H4; trivial.

      case ( Z_le_dec ((x * y) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros H3.
        case ( Z_le_dec (((x * y) mod (p k * q k) * z) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros H4.
          apply subsetT_eq_compat.
          rewrite <- associative.
          repeat rewrite mult_group2mult.
          rewrite opp_mult_l, mult_opp; trivial.

          elimtype False.
          rewrite Zmult_mod_idemp_r in H2.
          rewrite Zopp_Zminus in H2.
          rewrite Zmult_assoc in H2.
          rewrite Zmult_mod_idemp_r in H2.
          rewrite Zmult_mod_idemp_l in H4.
          cutrewrite (x * -1 * (y * z) = - (x * y * z)) in H2;[ | ring ].
          apply Znot_le_gt in H2.
          apply Znot_le_gt in H4.
          apply Zdiv2_small_mod_bis_rev in H2; trivial.
          omega.
          omega.
          intro Heq.
          apply Zmod_divide in Heq.
          assert (rel_prime (x * y * z) (p k * q k)).
          apply rel_prime_sym;apply rel_prime_mult; apply rel_prime_sym; trivial.
          apply P_prop in Hx; simpl in Hx.
          apply P_prop in Hy; simpl in Hy.
          apply rel_prime_sym;apply rel_prime_mult; apply rel_prime_sym; trivial; tauto.
          apply P_prop in Hz; simpl in Hz; tauto.
          apply MiscZArith.Z_rel_prime_not_divide in H0.
          apply H0; trivial.
          omega.
          omega.
        
        case ( Z_le_dec ((- ((x * y) mod (p k * q k)) mod (p k * q k) * z) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intro H4.
          elimtype False.
          rewrite Zmult_mod_idemp_r in H2.
          rewrite Zopp_Zminus in H2.
          rewrite Zmult_assoc in H2.
          rewrite Zmult_mod_idemp_r in H2.
          rewrite Zopp_Zminus in H4.
          rewrite Zmult_mod_idemp_r in H4.
          rewrite Zmult_mod_idemp_l in H4.
          cutrewrite (x * -1 * (y * z) = - (x * y * z)) in H2;[ | ring ].
          cutrewrite (-1 * (x * y) * z = - (x * y * z)) in H4;[ | ring ].
          apply H2; trivial.
        
          apply subsetT_eq_compat.
          apply f_equal.
          rewrite mult_opp_mult, <- opp_mult_mult, <- associative; trivial.
 Qed.


 Lemma mul_e_l : forall k (x:t k), mul (e k) x = x.
 Proof.
  intros; unfold mul, e, e_nowak.
  destruct x.
  unfold sigT_of_sig.
  case ( Z_le_dec (proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
   (neutral (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x)) (Zdiv2 (p k * q k)) ); intros.
  apply subsetT_eq_compat.
  apply (Group2.neutral_left (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))).
  elimtype False.
  rewrite (Group2.neutral_left (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))) in n.
  apply -> P_prop in i.
  omega.
 Qed.

 Lemma mul_comm : forall k (x y:t k), mul x y = mul y x.
 Proof.
  intros; unfold mul.
  destruct x.
  destruct y; simpl.
  unfold sigT_of_sig.
  destruct x; destruct x0; simpl.
  case ( Z_le_dec ((x * x0) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros.
  case ( Z_le_dec ((x0 * x) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros.
  apply subsetT_eq_compat.
  rewrite mult_comm; trivial.
  elimtype False; rewrite Zmult_comm in n ; omega.
  case ( Z_le_dec ((x0 * x) mod (p k * q k)) (Zdiv2 (p k * q k))); simpl; intros.
  elimtype False; rewrite Zmult_comm in n ; omega.
  apply subsetT_eq_compat.
  rewrite mult_comm; trivial.
 Qed.

 (* Power *)
 Fixpoint pow (k:nat) (x:t k) (n:nat) : t k :=
  match n with
  | O => e k
  | S n => mul x (pow x n)
  end.

 Definition inv_carrier n (x:carrier n) : carrier n.
 intros n (a, Ha).
 exists ((Datatypes.fst (Datatypes.fst (eeuclid a n)) mod n)).  
 destruct Ha as [[Hlt1 Hlt2] Hrel_prime].
 
 destruct (eeuclid_bound a n (Zabs n)) as [H2 H3].
 repeat rewrite Zabs_eq; omega.
 apply Zle_refl.
 
 assert (H1:=eeuclid_spec a n).
 assert (Hgcd:Zis_gcd a n 1).
 apply Zgcd_1_rel_prime in Hrel_prime.
 rewrite <- Hrel_prime.
 apply Zgcd_is_gcd.
 
 destruct (eeuclid a n) as ((u, v), d); simpl in *.
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

 Lemma inv_carrier_mul_inv_l : forall n x (W : 1 < n),
  Group2.mult (Zstar n W) (inv_carrier x) x =  neutral n W.
 Proof.
  intros n (a,Ha) W; unfold inv_carrier, Group2.mult, Zstar,  mult.
  apply subset_eq_compat; simpl.
  
  destruct Ha as [[Hlt1 Hlt2] Hrp].
  destruct (eeuclid_bound a n (Zabs n)) as [H2 H3].  
  repeat rewrite Zabs_eq; omega.
  apply Zle_refl.
  
  assert (H1:=eeuclid_spec a n).
  
  assert (Hgcd:Zis_gcd a n 1).
  apply  Zgcd_1_rel_prime in Hrp.
  rewrite <- Hrp.
  apply Zgcd_is_gcd.
  
  destruct (eeuclid a n) as ((u, v), d); simpl in *.
  destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.
  case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
  clear H5 H6 Hgcd; subst.
  
  rewrite <- Zmod_1_l with n; [ | auto with zarith].

  rewrite <- H, Z_mod_plus_full; trivial.
  rewrite Zmult_mod_idemp_l; trivial.
 Qed.

 Lemma inv_carrier_mul : forall n x y (W : 1 < n), 
  mult n W (inv_carrier x) (inv_carrier y) = (inv_carrier (mult n W x y)).
 Proof.
  intros n x y W.
  repeat rewrite mult_group2mult.
  apply (Group2.mult_left_inj (Zstar n W) _ _ (Group2.mult (Zstar n W) x y)).
  repeat rewrite <- mult_group2mult.
  rewrite (mult_comm _ _ (Group2.mult (Zstar n W) x y) (inv_carrier (mult n W x y))).
  rewrite (mult_comm _ _ x y) at 1.
  rewrite associative.
  rewrite <- (associative _ _ y x).
  rewrite (mult_comm _ _ x _) at 1.
  repeat rewrite mult_group2mult.  
  rewrite (inv_carrier_mul_inv_l (Group2.mult (Zstar n W) x y)).
  rewrite (inv_carrier_mul_inv_l x).
  rewrite Group2.neutral_right.
  repeat rewrite <- mult_group2mult.
  rewrite mult_comm.
  repeat rewrite mult_group2mult.
  rewrite (inv_carrier_mul_inv_l ).
  trivial.
 Qed.

 Lemma inv_carrier_fst : forall k a,  inv_carrier (fst (p k) (q k) (p_prime k) (q_prime k) a) =
  fst (p k) (q k) (p_prime k) (q_prime k) (inv_carrier a).
 Proof.
  intros.
  apply (Group2.mult_right_inj _ _ _ (fst (p k) (q k) (p_prime k) (q_prime k) a)).
  rewrite inv_carrier_mul_inv_l.
  rewrite <- fst_mult.
  rewrite inv_carrier_mul_inv_l.
  unfold neutral, fst; simpl.
  apply subset_eq_compat.
  rewrite Zmod_small; trivial.
  destruct (p_prime k); omega.
 Qed.
 
 Lemma inv_carrier_snd : forall k a,  inv_carrier (snd (p k) (q k) (p_prime k) (q_prime k) a) =
  snd (p k) (q k) (p_prime k) (q_prime k) (inv_carrier a).
 Proof.
  intros.
  apply (Group2.mult_right_inj _ _ _ (snd (p k) (q k) (p_prime k) (q_prime k) a)).
  rewrite inv_carrier_mul_inv_l.
  rewrite <- snd_mult.
  rewrite inv_carrier_mul_inv_l.
  unfold neutral, snd; simpl.
  apply subset_eq_compat.
  rewrite Zmod_small; trivial.
  destruct (q_prime k); omega.
 Qed.

 Lemma inv_carrier_inv_carrier : forall n (a : carrier n) (W : 1 < n) , inv_carrier (inv_carrier a) = a.
 Proof.
  intros.
  apply (Group2.mult_right_inj (Zstar n W) _ _ (inv_carrier a)).
  rewrite inv_carrier_mul_inv_l.
  repeat rewrite <- mult_group2mult.
  rewrite mult_comm.
  repeat rewrite mult_group2mult.
  rewrite inv_carrier_mul_inv_l.
  trivial.
 Qed.
  
 Definition inv : forall k, t k -> t k.
 intros k (a, Ha).
 case_eq (Z_le_dec (proj1_sig (inv_carrier a)) (Zdiv2 (p k * q k))); intros Heq _.

 refine (exist _ (inv_carrier a) _).
 apply P_prop in Ha.
 destruct Ha as [Ha1 Ha3].
 apply <- P_prop.
 unfold jacobi in *.
 unfold Zstar.jacobi in *.
 simpl.
 
 apply mult_1 in Ha1.
 destruct Ha1 as [ [Ha1 Ha2] | [Ha1 Ha2] ].
 split.
 apply <- mult_1.
 rewrite <- (legendre_fst (p k) (q k) (p_prime k) (q_prime k)) in Ha1.
 rewrite <- (legendre_snd (p k) (q k) (p_prime k) (q_prime k)) in Ha2.
 apply (legendre_plus_qr (p k) (p_gt_1 (p k) (p_prime k)) (p_prime k) _) in Ha1.
 apply (legendre_plus_qr (q k) (q_gt_1 (q k) (q_prime k)) (q_prime k) _) in Ha2.
 
 left; split.
 
 rewrite <- (legendre_fst _ _ _ (q_prime k)).
 apply <- (legendre_plus_qr (p k) (p_gt_1 (p k) (p_prime k)) (p_prime k) ((fst (p k) (q k) (p_prime k) (q_prime k)
  (inv_carrier a)))).
 destruct Ha1.
 exists (inv_carrier x).
 rewrite <- mult_group2mult, inv_carrier_mul, mult_group2mult, H, inv_carrier_fst; trivial.
 
 rewrite <- (legendre_snd _ _ (p_prime k) (q_prime k)).
 apply <- (legendre_plus_qr (q k) (q_gt_1 (q k) (q_prime k)) (q_prime k) ((snd (p k) (q k) (p_prime k) (q_prime k)
  (inv_carrier a)))).
 destruct Ha2.
 exists (inv_carrier x).
 rewrite <- mult_group2mult, inv_carrier_mul, mult_group2mult, H, inv_carrier_snd; trivial.
 
 split; trivial.
 
 destruct a as [x [Ha Hrp]]; simpl in *.
 destruct (eeuclid_bound x (p k * q k) (Zabs (p k * q k))) as [H2 H3].  
 repeat rewrite Zabs_eq; omega.
 apply Zle_refl.
 
 assert (H1:=eeuclid_spec x (p k * q k)).
 
 destruct (eeuclid x (p k * q k)) as ((u, v), d); simpl in *.
 destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.
 
 assert (Hgcd:Zis_gcd x (p k * q k) 1).
 apply  Zgcd_1_rel_prime in Hrp.
 rewrite <- Hrp.
 apply Zgcd_is_gcd.
 case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
 clear H5 H6 Hgcd; subst.
 
 assert (rel_prime u (p k * q k)).
 apply bezout_rel_prime.
 econstructor.
 instantiate (1:=v).
 instantiate (1:=x).
 rewrite Zmult_comm; trivial.
 
 apply Zle_lt.
 intro Hmod.
 apply Zmod_divide in Hmod.
 apply MiscZArith.Z_rel_prime_not_divide in H0.
 apply H0; trivial.
 omega.
 omega.
 apply Zmod_pos; omega.
 
 split.
 
 apply <- mult_1.
 rewrite <- (legendre_fst (p k) (q k) (p_prime k) (q_prime k)) in Ha1.
 rewrite <- (legendre_snd (p k) (q k) (p_prime k) (q_prime k)) in Ha2.
 apply (legendre_minus_qnr (p k) (p_gt_1 (p k) (p_prime k)) (p_prime k) _) in Ha1.
 apply (legendre_minus_qnr (q k) (q_gt_1 (q k) (q_prime k)) (q_prime k) _) in Ha2.
 
 right; split.
 
 rewrite <- (legendre_fst _ _ _ (q_prime k)).
 apply <- (legendre_minus_qnr (p k) (p_gt_1 (p k) (p_prime k)) (p_prime k) ((fst (p k) (q k) (p_prime k) (q_prime k)
  (inv_carrier a)))).
 intro H; apply Ha1.
 destruct H.
 exists (inv_carrier x).
 rewrite <- mult_group2mult, inv_carrier_mul, mult_group2mult, H, inv_carrier_fst, inv_carrier_inv_carrier; trivial.
 apply (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
 
 rewrite <- (legendre_snd _ _ (p_prime k) (q_prime k)).
 apply <- (legendre_minus_qnr (q k) (q_gt_1 (q k) (q_prime k)) (q_prime k) ((snd (p k) (q k) (p_prime k) (q_prime k)
  (inv_carrier a)))).
 intro H; apply Ha2.
 destruct H.
 exists (inv_carrier x).
 rewrite <- mult_group2mult, inv_carrier_mul, mult_group2mult, H, inv_carrier_snd, inv_carrier_inv_carrier; trivial.
 apply (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
 
 split; trivial.
 
 destruct a as [x [Ha Hrp]]; simpl in *.
 destruct (eeuclid_bound x (p k * q k) (Zabs (p k * q k))) as [H2 H3].  
 repeat rewrite Zabs_eq; omega.
 apply Zle_refl.
 
 assert (H1:=eeuclid_spec x (p k * q k)).
  
 destruct (eeuclid x (p k * q k)) as ((u, v), d); simpl in *.
 destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.
 
 assert (Hgcd:Zis_gcd x (p k * q k) 1).
 apply  Zgcd_1_rel_prime in Hrp.
 rewrite <- Hrp.
 apply Zgcd_is_gcd.
 case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
 clear H5 H6 Hgcd; subst.
 
 assert (rel_prime u (p k * q k)).
 apply bezout_rel_prime.
 econstructor.
 instantiate (1:=v).
 instantiate (1:=x).
 rewrite Zmult_comm; trivial.
 
 apply Zle_lt.
 intro Hmod.
 apply Zmod_divide in Hmod.
 apply MiscZArith.Z_rel_prime_not_divide in H0.
 apply H0; trivial.
 omega.
 omega.
 apply Zmod_pos; omega.
 
 refine (exist _ (opp _ (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (inv_carrier a)) _).
 apply P_prop in Ha.
 destruct a as [a [Halt Hrp]].
 apply <- P_prop.
 unfold jacobi in *.
 unfold Zstar.jacobi in *.
 destruct Ha as [Ha Hale].
 
 assert (H1:=eeuclid_spec a (p k * q k)).
 
 apply mult_1 in Ha.
 destruct Ha as [ [Ha1 Ha2] | [Ha1 Ha2] ].

 split.
 apply <- mult_1.
 rewrite <- (legendre_fst (p k) (q k) (p_prime k) (q_prime k)) in Ha1.
 rewrite <- (legendre_snd (p k) (q k) (p_prime k) (q_prime k)) in Ha2.
 apply (legendre_plus_qr (p k) (p_gt_1 (p k) (p_prime k)) (p_prime k) _) in Ha1.
 apply (legendre_plus_qr (q k) (q_gt_1 (q k) (q_prime k)) (q_prime k) _) in Ha2.
 
 right; split.
 
 rewrite <- (legendre_fst _ _ _ (q_prime k)).
 apply <- (legendre_minus_qnr (p k) (p_gt_1 (p k) (p_prime k)) (p_prime k) 
   ((fst (p k) (q k) (p_prime k) (q_prime k)
    (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (inv_carrier (exist (fun x : Z =>
     0 <= x < p k * q k /\ rel_prime x (p k * q k)) a (conj Halt Hrp))))))).
 destruct Ha1.
 rewrite fst_opp, <- inv_carrier_fst,  <- H, qr_opp_prime.
 intro Hw.
 apply Hw.
 exists (inv_carrier x).
 repeat rewrite <- mult_group2mult.
 rewrite inv_carrier_mul; trivial.
 apply p_prime.
 apply p_odd.
 apply p_blum.
 
 rewrite <- (legendre_snd _ _ (p_prime k) (q_prime k)).
 apply <- (legendre_minus_qnr (q k) (q_gt_1 (q k) (q_prime k)) (q_prime k) 
  ((snd (p k) (q k) (p_prime k) (q_prime k)
   (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (inv_carrier (exist (fun x : Z =>
    0 <= x < p k * q k /\ rel_prime x (p k * q k)) a (conj Halt Hrp))))))).
 
 destruct Ha2.
 rewrite snd_opp, <- inv_carrier_snd,  <- H, qr_opp_prime.
 intro Hw.
 apply Hw.
 exists (inv_carrier x).
 repeat rewrite <- mult_group2mult.
 rewrite inv_carrier_mul; trivial.
 apply q_prime.
 apply q_odd.
 apply q_blum.
  
 split; trivial.
 
 destruct (eeuclid_bound a (p k * q k) (Zabs (p k * q k))) as [H2 H3].  
 repeat rewrite Zabs_eq; omega.
 apply Zle_refl.
  
 assert (He:=eeuclid_spec a (p k * q k)).
 unfold inv_carrier; simpl.
 
 destruct (eeuclid a (p k * q k)) as ((u, v), d); simpl in *.
 destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.
 
 assert (Hgcd:Zis_gcd a (p k * q k) 1).
 apply  Zgcd_1_rel_prime in Hrp.
 rewrite <- Hrp.
 apply Zgcd_is_gcd.
 case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
 clear H5 H6 Hgcd; subst.
 
 assert (rel_prime u (p k * q k)).
 apply bezout_rel_prime.
 econstructor.
 instantiate (1:=v).
 instantiate (1:=a).
 rewrite Zmult_comm; trivial.
 
 apply Zle_lt.
 intro Hmod.
 apply Zmod_divide in Hmod.
 apply rel_prime_mod in H0.
 apply MiscZArith.Z_rel_prime_not_divide in H0.
 apply Zdivide_opp_r_rev in Hmod.
 apply H0; trivial.
 omega.
 omega.
 generalize (Z_mod_lt u (p k * q k)); omega.
 destruct (Z_mod_lt (- (u mod (p k * q k))) (p k * q k)); omega.
 
 simpl in *.
 rewrite Z_mod_nz_opp_full.
 apply Zdiv2_small.
 omega.
 split.
 rewrite Zmod_mod.
 omega.
 destruct (Z_mod_lt ((Datatypes.fst (Datatypes.fst (eeuclid a (p k * q k))) mod (p k * q k)) ) (p k * q k)); omega.
 
 destruct (eeuclid_bound a (p k * q k) (Zabs (p k * q k))) as [H2 H3].  
 repeat rewrite Zabs_eq; omega.
 apply Zle_refl.
 
 assert (He:=eeuclid_spec a (p k * q k)).
 unfold inv_carrier; simpl.
 
 destruct (eeuclid a (p k * q k)) as ((u, v), d); simpl in *.
 destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.
 
 assert (Hgcd:Zis_gcd a (p k * q k) 1).
 apply  Zgcd_1_rel_prime in Hrp.
 rewrite <- Hrp.
 apply Zgcd_is_gcd.
 case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
 clear H5 H6 Hgcd; subst.
 
 assert (rel_prime u (p k * q k)).
 apply bezout_rel_prime.
 econstructor.
 instantiate (1:=v).
 instantiate (1:=a).
 rewrite Zmult_comm; trivial.
 
 intro Hmod.
 apply Zmod_divide in Hmod.
 apply rel_prime_mod in H0.
 apply MiscZArith.Z_rel_prime_not_divide in H0.
 apply H0; trivial.
 omega.
 omega.
 omega.
 
 split.
 apply <- mult_1.
 rewrite <- (legendre_fst (p k) (q k) (p_prime k) (q_prime k)) in Ha1.
 rewrite <- (legendre_snd (p k) (q k) (p_prime k) (q_prime k)) in Ha2.
 apply (legendre_minus_qnr (p k) (p_gt_1 (p k) (p_prime k)) (p_prime k) _) in Ha1.
 apply (legendre_minus_qnr (q k) (q_gt_1 (q k) (q_prime k)) (q_prime k) _) in Ha2.
 
 left; split.
 
 rewrite <- (legendre_fst _ _ (p_prime k) (q_prime k)).
 apply <- (legendre_plus_qr (p k) (p_gt_1 (p k) (p_prime k)) (p_prime k) 
  ((fst (p k) (q k) (p_prime k) (q_prime k)
   (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (inv_carrier (exist (fun x : Z =>
    0 <= x < p k * q k /\ rel_prime x (p k * q k)) a (conj Halt Hrp))))))).
 rewrite fst_opp, <- inv_carrier_fst.
 rewrite qr_opp_prime.
 intro H.
 apply Ha1.
 destruct H.
 exists (inv_carrier x).
 rewrite <- mult_group2mult, inv_carrier_mul, mult_group2mult.
 rewrite <- (inv_carrier_inv_carrier ( fst (p k) (q k) (p_prime k) (q_prime k)
  (exist (fun x0 : Z => 0 <= x0 < p k * q k /\ rel_prime x0 (p k * q k)) a (conj Halt Hrp)))).
 apply f_equal; trivial.
 apply (p_gt_1 (p k) (p_prime k)).
 apply p_prime.
 apply p_odd.
 apply p_blum.
 
 rewrite <- (legendre_snd _ _ (p_prime k) (q_prime k)).
 apply <- (legendre_plus_qr (q k) (q_gt_1 (q k) (q_prime k)) (q_prime k) 
  ((snd (p k) (q k) (p_prime k) (q_prime k)
   (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (inv_carrier (exist (fun x : Z =>
    0 <= x < p k * q k /\ rel_prime x (p k * q k)) a (conj Halt Hrp))))))).
 rewrite snd_opp, <- inv_carrier_snd.
 rewrite qr_opp_prime.
 intro H.
 apply Ha2.
 destruct H.
 exists (inv_carrier x).
 rewrite <- mult_group2mult, inv_carrier_mul, mult_group2mult.
 rewrite <- (inv_carrier_inv_carrier ( snd (p k) (q k) (p_prime k) (q_prime k)
  (exist (fun x0 : Z => 0 <= x0 < p k * q k /\ rel_prime x0 (p k * q k)) a (conj Halt Hrp)))).
 apply f_equal; trivial.
 apply (q_gt_1 (q k) (q_prime k)).
 apply q_prime.
 apply q_odd.
 apply q_blum.
 
 split; trivial.
 
 destruct (eeuclid_bound a (p k * q k) (Zabs (p k * q k))) as [H2 H3].  
 repeat rewrite Zabs_eq; omega.
 apply Zle_refl.
 
 assert (He:=eeuclid_spec a (p k * q k)).
 unfold inv_carrier; simpl.
 
 destruct (eeuclid a (p k * q k)) as ((u, v), d); simpl in *.
 destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.
 
 assert (Hgcd:Zis_gcd a (p k * q k) 1).
 apply  Zgcd_1_rel_prime in Hrp.
 rewrite <- Hrp.
 apply Zgcd_is_gcd.
 case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
 clear H5 H6 Hgcd; subst.
 
 assert (rel_prime u (p k * q k)).
 apply bezout_rel_prime.
 econstructor.
 instantiate (1:=v).
 instantiate (1:=a).
 rewrite Zmult_comm; trivial.
 
 apply Zle_lt.
 intro Hmod.
 apply Zmod_divide in Hmod.
 apply rel_prime_mod in H0.
 apply MiscZArith.Z_rel_prime_not_divide in H0.
 apply Zdivide_opp_r_rev in Hmod.
 apply H0; trivial.
 omega.
 omega.
 generalize (Z_mod_lt u (p k * q k)); omega.
 destruct (Z_mod_lt (- (u mod (p k * q k))) (p k * q k)); omega.
 
 simpl in *.
 rewrite Z_mod_nz_opp_full.
 apply Zdiv2_small.
 omega.
 split.
 rewrite Zmod_mod.
 omega.
 destruct (Z_mod_lt ((Datatypes.fst (Datatypes.fst (eeuclid a (p k * q k))) mod (p k * q k)) ) (p k * q k)); omega.
 
 destruct (eeuclid_bound a (p k * q k) (Zabs (p k * q k))) as [H2 H3].  
 repeat rewrite Zabs_eq; omega.
 apply Zle_refl.
 
 assert (He:=eeuclid_spec a (p k * q k)).
 unfold inv_carrier; simpl.

 destruct (eeuclid a (p k * q k)) as ((u, v), d); simpl in *.
 destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.
 
 assert (Hgcd:Zis_gcd a (p k * q k) 1).
 apply  Zgcd_1_rel_prime in Hrp.
 rewrite <- Hrp.
 apply Zgcd_is_gcd.
 case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
 clear H5 H6 Hgcd; subst.
 
 assert (rel_prime u (p k * q k)).
 apply bezout_rel_prime.
 econstructor.
 instantiate (1:=v).
 instantiate (1:=a).
 rewrite Zmult_comm; trivial.
 
 intro Hmod.
 apply Zmod_divide in Hmod.
 apply rel_prime_mod in H0.
 apply MiscZArith.Z_rel_prime_not_divide in H0.
 apply H0; trivial.
 omega.
 omega.
 omega.
 Defined.

 Lemma mul_inv_l : forall k (x:t k), mul (inv x) x = e k.
 Proof.
  intros k (x, Hx).
  unfold mul, inv, e.
  case (Z_le_dec (proj1_sig (inv_carrier x)) (Zdiv2 (p k * q k)) ); intros.
  unfold sigT_of_sig.
  case (Z_le_dec (proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) (inv_carrier x) x)) (Zdiv2 (p k * q k))); intros.
  apply subsetT_eq_compat.
  rewrite inv_carrier_mul_inv_l; auto.
  elimtype False.
  simpl in *.
  apply n.
  destruct x.
  apply P_prop in Hx; simpl in *.

  destruct a as [Ha Hrp]; simpl in *.
  destruct (eeuclid_bound x (p k * q k) (Zabs (p k * q k))) as [H2 H3].  
  repeat rewrite Zabs_eq; omega.
  apply Zle_refl.

  assert (H1:=eeuclid_spec x (p k * q k)).

  destruct (eeuclid x (p k * q k)) as ((u, v), d); simpl in *.
  destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.

  assert (Hgcd:Zis_gcd x (p k * q k) 1).
  apply  Zgcd_1_rel_prime in Hrp.
  rewrite <- Hrp.
  apply Zgcd_is_gcd.
  case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
  clear H5 H6 Hgcd; subst.
  trivial.

  rewrite Zmult_mod_idemp_l.
  rewrite <- (Zplus_0_r (u * x)).
  rewrite Zplus_mod.
  rewrite <- (Z_mod_mult v (p k * q k)).
  rewrite Zmod_mod.
  rewrite <- Zplus_mod.
  rewrite H.
  rewrite Zmod_small.
  omega.
  omega.

  unfold sigT_of_sig.
  case ( Z_le_dec
       (proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
            (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (inv_carrier x)) x))
       (Zdiv2 (p k * q k))); intros.
  2: apply subsetT_eq_compat.
  2: rewrite opp_mult_l, opp_opp, inv_carrier_mul_inv_l; auto.

  elimtype False.
  simpl in *.
  destruct x.
  apply P_prop in Hx; simpl in *.

  destruct a as [Ha Hrp]; simpl in *.
  destruct (eeuclid_bound x (p k * q k) (Zabs (p k * q k))) as [H2 H3].  
  repeat rewrite Zabs_eq; omega.
  apply Zle_refl.

  assert (H1:=eeuclid_spec x (p k * q k)).

  destruct (eeuclid x (p k * q k)) as ((u, v), d); simpl in *.
  destruct (H1 u v d) as [H4 [H5 H6] ]; [ trivial | ]; clear H1.

  assert (Hgcd:Zis_gcd x (p k * q k) 1).
  apply  Zgcd_1_rel_prime in Hrp.
  rewrite <- Hrp.
  apply Zgcd_is_gcd.
  case (Zis_gcd_unique _ _ _ _ H5 Hgcd); intro; [ | rewrite H in H6; elim H6; trivial].
  clear H5 H6 Hgcd; subst.
  trivial.

  rewrite Zmult_mod_idemp_l in z.
  cutrewrite (- (u mod (p k * q k)) * x = (u mod (p k * q k)) * - x) in z ;[ | ring].
  rewrite Zmult_mod_idemp_l in z.
  cutrewrite (u * - x = - ( u * x)) in z;[ | ring ].
  apply Zdiv2_small_mod in z.
  apply Zlt_gt in z.
  rewrite <- (Zplus_0_r (u * x)) in z.
  rewrite Zplus_mod in z.
  rewrite <- (Z_mod_mult v (p k * q k)) in z.
  rewrite Zmod_mod in z.
  rewrite <- Zplus_mod in z.
  rewrite H in z.
  rewrite Zmod_small in z.
  omega.
  omega.
  apply Zodd_mult_Zodd.
  apply p_odd.
  apply q_odd.
  omega.
  intro Heq. 
  rewrite <- (Zplus_0_r (u * x mod (p k * q k))) in Heq.
  rewrite <- (Z_mod_mult v (p k * q k)) in Heq at 1.
  apply f_equal with (f:=fun x => x mod (p k * q k)) in Heq.
  rewrite <- Zplus_mod, H in Heq.
  rewrite Zmod_0_l in Heq.
  rewrite Zmod_small in Heq.
  discriminate.
  omega.
 Qed.

 Definition div k (x y:t k) : t k := mul x (inv y).
  
 Fixpoint powZ (k:nat) (x:t k) (n:Z) {struct n}: t k :=
  match n with
  | Z0 => pow x 0
  | Zpos p => pow x (nat_of_P p)
  | Zneg p => inv (pow x (nat_of_P p))
  end.
 
 Lemma pow_S: forall k n (x : t k), pow x (S n) = mul x (pow x n).
 Proof.
  intros; simpl; trivial.
 Qed.

 Lemma pow_0 : forall k (x : t k), pow x 0 = e k.
 Proof.
  intros; simpl; trivial.
 Qed.

 Lemma mul_pow_plus : forall k (x:t k) n m,
  mul (pow x n) (pow x m) = pow x (n + m).
 Proof.
  induction n; intros.
  rewrite pow_0,  mul_e_l; trivial.
  rewrite pow_S.
  rewrite <- mul_assoc, IHn; trivial.
 Qed.

 Lemma pow_e : forall k n, pow (e k) n = e k.
 Proof.
  induction n; intros.
  trivial.
  rewrite pow_S, IHn.
  rewrite mul_e_l; trivial.
 Qed.

 Lemma sqr_eq_pow_2 k (x : t k) : sqr x = pow x 2.
  Proof.
   intros; unfold sqr; simpl.
   rewrite (mul_comm _ (e k)), mul_e_l; trivial.
  Qed.

 Lemma pow_mul_distr : forall k (x y:t k) n,
  pow (mul x y) n = mul (pow x n) (pow y n).
 Proof.
  induction n; intros.
  repeat rewrite pow_0.
  rewrite mul_e_l; trivial.
  repeat rewrite pow_S.
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

 Lemma lt_n n (n_prime : prime n)(Hmod : (4 | n + 1)) : 0 <= (n + 1) / 4.
 Proof.
  intros.
  assert (Hp_ge_2 := prime_ge_2 _ n_prime).
  apply Zmult_lt_0_le_reg_r with 4; simpl.
  omega.
  rewrite Zmult_comm.
  rewrite <- Zdivide_Zdiv_eq.
  omega.
  omega.
  trivial.
 Qed.

 Lemma power_2  n (W : 1 < n) (x : Zstar n W):
  (Group2.mult (Zstar n W) x x = Group2.power_nat (Zstar n W) x (Zabs_nat 2)).
 Proof.
  intros; simpl.
  rewrite (neutral_right n W); trivial.
 Qed.
 
 Definition sqrt_n n (W : 1 < n) (x : Zstar n W) : Zstar n W := 
  Group2.power_nat _ x (Zabs_nat ((n + 1) / 4)).
 
 Lemma sqrt_square_qr n (W : 1 < n) (x : Zstar n W) (n_blum : n mod 4 = 3) (n_prime : prime n) (n_odd : Zodd n):
  Group2.QuadraticResidue x -> sqrt_n (Group2.mult _ x x) = x.
 Proof.
  intros; unfold sqrt_n.
  
  assert (Hmod : (4 | n + 1)).
  apply Zmod_divide; [ omega | ].
  rewrite Zplus_mod.
  rewrite n_blum; compute; trivial.
  
  assert (lt_n := lt_n n_prime Hmod).
  rewrite power_2.
  
  destruct H as [y H].
  
  rewrite <- H.
  rewrite power_2.
  
  repeat rewrite <- Group2.power_nat_mult.
  repeat rewrite <- Zabs_nat_mult.
  rewrite <- Group2.neutral_right.
  rewrite <- neutral_group2neutral.
  rewrite <- (Zstar_fermat n W n_prime y).
  rewrite <- Group2.power_nat_plus.
  rewrite <- (Group2.power_nat_1 (Zstar n W) y) at 2.
  rewrite <- Group2.power_nat_mult.
  apply f_equal.
  repeat rewrite <- Zabs_nat_Zplus; try omega.
  rewrite mult_1_l.
  cutrewrite (2 * (2 * ((n + 1) / 4)) =  4 * (n - 1 + 2) / 4).
  rewrite Zdivide_Zdiv_eq_2; try omega.
  rewrite <- Zdivide_Zdiv_eq; try omega.
  apply f_equal; ring.
  ring_simplify; trivial.
  ring_simplify; trivial.
  cutrewrite (n - 1 + 2 = n + 1);[ | ring ].
  rewrite Zdivide_Zdiv_eq_2; trivial; try omega.
 Qed.
 
 Lemma sqrt_square_qnr n (W : 1 < n) (x : Zstar n W) (n_blum : n mod 4 = 3) (n_prime : prime n) (n_odd : Zodd n):
  ~Group2.QuadraticResidue x -> sqrt_n (Group2.mult _ x x) = opp _ _ x.
 Proof.
  intros; unfold sqrt_n.
  
  assert (Hmod : (4 | n + 1)).
  apply Zmod_divide; [ omega | ].
  rewrite Zplus_mod.
  rewrite n_blum; compute; trivial.
  
  assert (lt_n := lt_n n_prime Hmod).
  rewrite power_2.
  
  set (g := generator n W n_prime).
  assert (gig := is_generator n W n_prime).
  
  apply qr_opp_prime in H; trivial.
  destruct H as [y H].
  rewrite <- power_2.
  rewrite <- mult_opp.
  rewrite power_2.
  rewrite <- H.
  
  rewrite power_2.
  
  repeat rewrite <- Group2.power_nat_mult.
  repeat rewrite <- Zabs_nat_mult.
  rewrite <- Group2.neutral_right.
  rewrite <- neutral_group2neutral.
  rewrite <- (Zstar_fermat n W n_prime y).
  rewrite <- Group2.power_nat_plus.
  rewrite <- (Group2.power_nat_1 (Zstar n W) y) at 2.
  rewrite <- Group2.power_nat_mult.
  apply f_equal.
  repeat rewrite <- Zabs_nat_Zplus; try omega.
  rewrite mult_1_l.
  cutrewrite (2 * (2 * ((n + 1) / 4)) =  4 * (n - 1 + 2) / 4).
  rewrite Zdivide_Zdiv_eq_2; try omega.
  rewrite <- Zdivide_Zdiv_eq; try omega.
  apply f_equal; ring.
  ring_simplify; trivial.
  ring_simplify; trivial.
  cutrewrite (n - 1 + 2 = n + 1);[ | ring ].
  rewrite Zdivide_Zdiv_eq_2; trivial; try omega.
 Qed.
 
 Lemma sqrt_mult  n (W : 1 < n) (x y: Zstar n W) (n_blum : n mod 4 = 3) (n_prime : prime n):
  Group2.mult _ (sqrt_n x) (sqrt_n y) = sqrt_n (Group2.mult _ x y).
 Proof.
  intros; unfold sqrt_n.
  induction (Zabs_nat ((n + 1) / 4)).
  simpl.
  rewrite neutral_right; trivial.
  simpl in *.
  rewrite <- IHn0.
  unfold mult.
  apply subset_eq_compat; simpl.
  repeat rewrite <- Zmult_mod.
  apply (f_equal (fun x => x mod n)); ring.
 Qed.
 
 Lemma sqrt_inj_qr  n (W : 1 < n) (n_prime : prime n) (n_blum : n mod 4 = 3) (n_odd : Zodd n) (x y: Zstar n W):
  Group2.QuadraticResidue x /\ Group2.QuadraticResidue y -> sqrt_n x = sqrt_n y -> x = y.
 Proof.
  intros ? ? ? ? ? ? ? [H1 H2] ?.
  apply sqrt_square_qr in H1; trivial.
  apply sqrt_square_qr in H2; trivial.
  rewrite <- H1, <- H2, <- sqrt_mult, <- sqrt_mult, H ; trivial.
 Qed.

 Lemma sqrt_inj_qnr  n (W : 1 < n) (n_prime : prime n) (n_blum : n mod 4 = 3) (n_odd : Zodd n) (x y: Zstar n W):
   ~ Group2.QuadraticResidue x /\ ~ Group2.QuadraticResidue y -> sqrt_n x = sqrt_n y -> x = y.
 Proof.
  intros ? ? ? ? ? ? ? [H1 H2] ?.
  apply sqrt_square_qnr in H1; trivial.
  apply sqrt_square_qnr in H2; trivial.
  rewrite <- (opp_opp _ _ x),  <- (opp_opp _ _ y).
  rewrite <- H1, <- H2, <- sqrt_mult, <- sqrt_mult, H; trivial.
 Qed.

 Lemma sqrt_qr n (W : 1 < n) (n_prime : prime n) (n_blum : n mod 4 = 3) (n_odd : Zodd n)
   (x : Zstar n W) : Group2.QuadraticResidue x -> Group2.QuadraticResidue (sqrt_n x).
 Proof.
  intros.
  apply sqrt_square_qr in H; trivial.
  rewrite <- sqrt_mult in H; trivial.
  rewrite <- H.
  rewrite <- sqrt_mult; trivial.
  exists (sqrt_n (sqrt_n x)); trivial.
 Qed.

 Lemma sqrt_qnr n (W : 1 < n) (n_prime : prime n) (n_blum : n mod 4 = 3) (n_odd : Zodd n)
   (x : Zstar n W) : ~ Group2.QuadraticResidue x -> Group2.QuadraticResidue (sqrt_n (opp _ _ x)).
 Proof.
  intros.
  apply sqrt_square_qnr in H; trivial.
  rewrite <- sqrt_mult in H; trivial.
  rewrite <- H.
  rewrite <- sqrt_mult; trivial.
  exists (sqrt_n (sqrt_n x)); trivial.
 Qed.
 
 Lemma sqrt_opp_even  n (W : 1 < n) (n_prime : prime n) (n_blum : n mod 4 = 3) (n_odd : Zodd n) (x : Zstar n W) : 
   Zeven ((n + 1) / 4) -> sqrt_n (opp _ _ x) = sqrt_n x.
 Proof.
  intros; unfold sqrt_n.
  destruct (Zeven_ex _ H).
  rewrite H0.
  rewrite Zabs_nat_mult.
  repeat rewrite Group2.power_nat_mult.
  repeat rewrite <- power_2.
  rewrite mult_opp; trivial.
 Qed.

 Lemma sqrt_opp_odd  n (W : 1 < n) (n_prime : prime n) (n_blum : n mod 4 = 3) (n_odd : Zodd n) (x : Zstar n W) : 
   Zodd ((n + 1) / 4) -> sqrt_n (opp _ _ x) = opp _ _ (sqrt_n x).
 Proof.
  intros; unfold sqrt_n.
  assert (Hmod : (4 | n + 1)).
  apply Zmod_divide; [ omega | ].
  rewrite Zplus_mod.
  rewrite n_blum; compute; trivial.  
  destruct (Zodd_ex _ H).
  rewrite H0.
  rewrite Zabs_nat_Zplus, Zabs_nat_mult.
  repeat rewrite Group2.power_nat_plus.
  repeat rewrite Group2.power_nat_mult.
  repeat rewrite <- power_2.
  rewrite mult_opp; trivial.
  apply eq_opp.
  rewrite <- mult_group2mult.
  rewrite mult_comm.
  rewrite mult_group2mult.
  rewrite opp_mult_l.
  repeat rewrite Group2.power_nat_1.
  rewrite opp_opp.
  simpl.
  rewrite mult_comm.
  trivial.
  generalize (lt_n n_prime Hmod); omega.
  omega.
 Qed.

 Definition sqrt1 k x := (pair (p k) (q k) (@distinct k) (p_prime k) (q_prime k) 
  (sqrt_n (fst _ _ (p_prime k) (q_prime k) x)) 
  (sqrt_n (snd _ _ (p_prime k) (q_prime k) x))).

 Definition sqrt2 k x := (pair (p k) (q k) (@distinct k) (p_prime k) (q_prime k) 
  (sqrt_n (opp _ _ (fst _ _ (p_prime k) (q_prime k) x))) 
  (sqrt_n (snd _ _ (p_prime k) (q_prime k) x))).

 Definition sqrt3 k x := (pair (p k) (q k) (@distinct k) (p_prime k) (q_prime k) 
  (sqrt_n (fst _ _ (p_prime k) (q_prime k) x))
  (sqrt_n (opp _ _ (snd _ _ (p_prime k) (q_prime k) x))))
. 
 Definition sqrt4 k x := (pair (p k) (q k) (@distinct k) (p_prime k) (q_prime k) 
  (sqrt_n (fst _ _ (p_prime k) (q_prime k) (opp _ _ x)))
  (sqrt_n (snd _ _ (p_prime k) (q_prime k) (opp _ _ x)))).

 Lemma sqrt1_mult  k x y : Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) (sqrt1 x) (sqrt1 y) = 
  sqrt1 (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x y).
 Proof.
  intros.
  unfold sqrt1.
  rewrite  fst_mult, snd_mult.
  repeat rewrite <- sqrt_mult; trivial.
  set (x1 :=  (sqrt_n (fst (p k) (q k) (p_prime k) (q_prime k) x))).
  set (x2 :=  (sqrt_n (snd (p k) (q k) (p_prime k) (q_prime k) x))).
  set (y1 :=  (sqrt_n (fst (p k) (q k) (p_prime k) (q_prime k) y))).
  set (y2 :=  (sqrt_n (snd (p k) (q k) (p_prime k) (q_prime k) y))).
  rewrite (mult_pair (p k) (q k) (@distinct k) (p_prime k) (q_prime k) x1 x2 y1 y2).
  trivial.
  apply q_blum.
  apply q_prime.
  apply p_blum.
  apply p_prime.
 Qed.

 Lemma sqrt1_opp_sqrt4 k x : @sqrt1 k x = sqrt4 (opp _ _ x).
 Proof.
  intros; unfold sqrt1, sqrt4.
  rewrite opp_opp.
  trivial.
 Qed.

 Lemma sqrt4_opp_sqrt1 k x : @sqrt4 k x = sqrt1 (opp _ _ x).
 Proof.
  intros; unfold sqrt1, sqrt4; trivial.
 Qed.

 Lemma sqrt4_mult  k x y : Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) (sqrt4 x) (sqrt4 y) = 
   sqrt4 (opp _ _ (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x y)).
 Proof.
  intros.
  repeat rewrite sqrt4_opp_sqrt1.
  rewrite sqrt1_mult.
  rewrite mult_opp.
  rewrite opp_opp.
  trivial.
 Qed.

 Lemma sqrt1_sqrt4 k x y : Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) (@sqrt1 k x) (sqrt4 y) =
   sqrt4 (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x y).
 Proof.
  intros.
  rewrite <- (opp_opp _ _ (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x y)).
  rewrite sqrt1_opp_sqrt4, sqrt4_mult.
  apply f_equal.
  rewrite opp_opp, opp_mult_l, opp_opp; trivial.
 Qed.

 Ltac simpl_legendre := 
  try (apply <- legendre_plus_qr); try (apply <- legendre_minus_qnr).

 Lemma sqrt1_spec k x (Hx : P k x)
  (Hqr_fst : Group2.QuadraticResidue
   (fst (p k) (q k) (p_prime k) (q_prime k) x))
  (Hqr_snd : Group2.QuadraticResidue
   (snd (p k) (q k) (p_prime k) (q_prime k) x))
  (Hsqrt1 : proj1_sig (sqrt1 x) <= Zdiv2 (p k * q k)) : 
  P k (sqrt1 x).
 Proof.
  intros.
  assert (Hp_prime := p_prime k).
  assert (Hq_prime := q_prime k).
  assert (Hp_blum := p_blum k).
  assert (Hq_blum := q_blum k).
  assert (Hp_odd := p_odd k).
  assert (Hq_odd := q_odd k).
  assert (Hp_diff := @p_diff_2 k).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  assert (Hpq_lt_1 := Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
  unfold sqrt1 in *.
  apply <- P_prop.
  apply P_prop in Hx.
  unfold jacobi in *.
  destruct Hx as [Hx1 Hlt].
  split.
  apply jacobi_plus in Hx1.
  destruct Hx1 as [ [Hx1 Hx2] | [Hx1 Hx2] ]. 
  apply sqrt_qr in Hx1; trivial.
  apply sqrt_qr in Hx2; trivial.
  apply <- mult_1.
  left; split. 
  rewrite <- (legendre_fst _ _ _ (q_prime k)).
  simpl_legendre.
  rewrite fst_pair; trivial.
  rewrite <- (legendre_snd _ _ (p_prime k) (q_prime k)).
  simpl_legendre.
  rewrite snd_pair; trivial.
  elim Hx1; trivial.
  split; trivial.
  generalize (pair_spec (p k) (q k) (@distinct k) (p_prime k) (q_prime k)  
    (sqrt_n (fst (p k) (q k) (p_prime k) (q_prime k) x))
    (sqrt_n (snd (p k) (q k) (p_prime k) (q_prime k) x))).
  simpl.
  unfold  fst, snd, sqrt_n.
  repeat rewrite power_nat_power; simpl.
  destruct x; simpl in *.
  intros [Hle_lt Hrp].
  apply Zle_lt.
  rewrite <- Zmod_mod.
  intro Hmod.
  apply Zmod_divide in Hmod.
  apply MiscZArith.Z_rel_prime_not_divide in Hrp.
  apply Hrp; trivial.
  omega.
  omega.
  omega.
 Qed.

 Lemma opp_sqrt1_spec k x (Hx : P k x)
  (Hqr_fst : Group2.QuadraticResidue
   (fst (p k) (q k) (p_prime k) (q_prime k) x))
  (Hqr_snd : Group2.QuadraticResidue
   (snd (p k) (q k) (p_prime k) (q_prime k) x))
  (Hsqrt1 :  ~ proj1_sig (sqrt1 x) <= Zdiv2 (p k * q k)) : 
  P k (opp _ _ (sqrt1 x)).
 Proof.
  intros.
  assert (Hp_prime := p_prime k).
  assert (Hq_prime := q_prime k).
  assert (Hp_blum := p_blum k).
  assert (Hq_blum := q_blum k).
  assert (Hp_odd := p_odd k).
  assert (Hq_odd := q_odd k).
  assert (Hp_diff := @p_diff_2 k).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  assert (Hpq_lt_1 := Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
  unfold sqrt1 in *.
  apply <- P_prop.
  apply P_prop in Hx.
  unfold jacobi in *.
  destruct Hx as [Hx1 Hlt].
  split.
  apply jacobi_plus in Hx1.
  destruct Hx1 as [ [Hx1 Hx2] | [Hx1 Hx2] ]. 
  apply sqrt_qr in Hx1; trivial.
  apply sqrt_qr in Hx2; trivial.
  apply <- mult_1.
  right; split. 
  rewrite <- (legendre_fst _ _ _ (q_prime k)).
  simpl_legendre.
  rewrite fst_opp.
  apply -> qr_opp_prime; trivial.
  rewrite opp_opp.
  rewrite fst_pair; trivial. 
  rewrite <- (legendre_snd _ _ (p_prime k) (q_prime k)).
  simpl_legendre.
  rewrite snd_opp.
  apply -> qr_opp_prime; trivial.
  rewrite opp_opp.
  rewrite snd_pair; trivial.
  elim Hx1; trivial.
  generalize (pair_spec (p k) (q k) (@distinct k) (p_prime k) (q_prime k)  
    (sqrt_n (fst (p k) (q k) (p_prime k) (q_prime k) x))
    (sqrt_n (snd (p k) (q k) (p_prime k) (q_prime k) x))).
  intros [Hle_lt Hrp].
  simpl.
  unfold  fst, snd, sqrt_n in *.
  split.  
  repeat rewrite power_nat_power in * ; simpl in *.
  destruct x; simpl in *.
  apply Zle_lt.
  apply Zmod_opp_diff_0.
  intro Hmod.
  apply Zmod_divide in Hmod.
  apply MiscZArith.Z_rel_prime_not_divide in Hrp.
  apply Hrp; trivial.
  simpl.
  omega.
  omega.
  apply Zmod_pos; omega.
  simpl.
  rewrite Z_mod_nz_opp_full.
  rewrite Zmod_mod.
  apply Zdiv2_small.
  omega.
  split.
  unfold pair in Hsqrt1; simpl in Hsqrt1; omega.
  apply Zmod_bound; omega.
  intro Hmod.
  apply Zmod_divide in Hmod.
  apply MiscZArith.Z_rel_prime_not_divide in Hrp.
  apply Hrp; trivial.
  omega.
  omega.
 Qed.

 Lemma sqrt2_spec k x (Hx : P k x)
  (Hqr_fst : Group2.QuadraticResidue
   (fst (p k) (q k) (p_prime k) (q_prime k) x))
  (Hqr_snd : ~Group2.QuadraticResidue
   (snd (p k) (q k) (p_prime k) (q_prime k) x)) : 
  P k (sqrt2 x).
 Proof.
  intros.
  unfold sqrt2 in *.
  apply <- P_prop.
  apply P_prop in Hx.
  unfold jacobi in *.
  destruct Hx as [Hx1 Hlt].
  apply jacobi_plus in Hx1.
  destruct Hx1 as [ [Hx1 Hx2] | [Hx1 Hx2] ]. 
  elim Hqr_snd; trivial.
  elim Hx1; trivial.
 Qed.

 Lemma sqrt3_spec k x (Hx : P k x)
  (Hqr_fst : ~Group2.QuadraticResidue
   (fst (p k) (q k) (p_prime k) (q_prime k) x))
  (Hqr_snd : Group2.QuadraticResidue
   (snd (p k) (q k) (p_prime k) (q_prime k) x)) : 
  P k (sqrt3 x).
 Proof.
  intros.
  unfold sqrt3 in *.
  apply <- P_prop.
  apply P_prop in Hx.
  unfold jacobi in *.
  destruct Hx as [Hx1 Hlt].
  apply jacobi_plus in Hx1.
  destruct Hx1 as [ [Hx1 Hx2] | [Hx1 Hx2] ]. 
  elim Hqr_fst; trivial.
  elim Hx2; trivial.
 Qed.
 
 Lemma sqrt4_spec k x (Hx : P k x)
  (Hqr_fst : ~Group2.QuadraticResidue
   (fst (p k) (q k) (p_prime k) (q_prime k) x))
  (Hqr_snd : ~Group2.QuadraticResidue
   (snd (p k) (q k) (p_prime k) (q_prime k) x))
  (Hsqrt4 : proj1_sig (sqrt4 x) <= Zdiv2 (p k * q k)) : 
  P k (sqrt4 x).
 Proof.
  intros.
  assert (Hp_prime := p_prime k).
  assert (Hq_prime := q_prime k).
  assert (Hp_blum := p_blum k).
  assert (Hq_blum := q_blum k).
  assert (Hp_odd := p_odd k).
  assert (Hq_odd := q_odd k).
  assert (Hp_diff := @p_diff_2 k).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  assert (Hpq_lt_1 := Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
  unfold sqrt4 in *.
  apply <- P_prop.
  apply P_prop in Hx.
  unfold jacobi in *.
  destruct Hx as [Hx1 Hlt].
  split.
  apply jacobi_plus in Hx1.
  destruct Hx1 as [ [Hx1 Hx2] | [Hx1 Hx2] ]. 
  elim Hqr_snd; trivial.
  clear Hqr_fst Hqr_snd.

  apply sqrt_qnr in Hx1; trivial.
  apply sqrt_qnr in Hx2; trivial.
  apply <- mult_1.
  left ; split.
  rewrite <- (legendre_fst _ _ _ (q_prime k)).
  simpl_legendre.
  rewrite fst_pair, fst_opp; trivial.
  rewrite <- (legendre_snd _ _ (p_prime k) (q_prime k)).
  simpl_legendre.
  rewrite snd_pair, snd_opp; trivial.
  generalize (pair_spec (p k) (q k) (@distinct k) (p_prime k) (q_prime k)  
    (sqrt_n (fst (p k) (q k) (p_prime k) (q_prime k) (opp _ _ x)))
    (sqrt_n (snd (p k) (q k) (p_prime k) (q_prime k) (opp _ _ x)))). 
  intros [Hle_lt Hrp].
  simpl.
  unfold  fst, snd, sqrt_n in *.
  split.  
  repeat rewrite power_nat_power in * ; simpl in *.
  destruct x; simpl in *.
  apply Zle_lt.
  rewrite <- Zmod_mod.
  intro Hmod.
  apply Zmod_divide in Hmod.
  apply MiscZArith.Z_rel_prime_not_divide in Hrp.
  apply Hrp; trivial.
  omega.
  omega.
  apply Zmod_pos; omega.
  generalize Hsqrt4; simpl; trivial.
 Qed.
 
 Lemma opp_sqrt4_spec k x (Hx : P k x)
  (Hqr_fst : ~Group2.QuadraticResidue
   (fst (p k) (q k) (p_prime k) (q_prime k) x))
  (Hqr_snd : ~Group2.QuadraticResidue
   (snd (p k) (q k) (p_prime k) (q_prime k) x))
  (Hsqrt4 : ~proj1_sig (sqrt4 x) <= Zdiv2 (p k * q k)) : 
  P k (opp _ _ (sqrt4 x)).
 Proof.
  intros.
  assert (Hp_prime := p_prime k).
  assert (Hq_prime := q_prime k).
  assert (Hp_blum := p_blum k).
  assert (Hq_blum := q_blum k).
  assert (Hp_odd := p_odd k).
  assert (Hq_odd := q_odd k).
  assert (Hp_diff := @p_diff_2 k).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  assert (Hpq_lt_1 := Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
  unfold sqrt4 in *.
  apply <- P_prop.
  apply P_prop in Hx.
  unfold jacobi in *.
  destruct Hx as [Hx1 Hlt].
  split.
  apply jacobi_plus in Hx1.
  destruct Hx1 as [ [Hx1 Hx2] | [Hx1 Hx2] ].
  elim Hqr_fst; trivial.
  clear Hqr_fst Hqr_snd.
  apply sqrt_qnr in Hx1; trivial.
  apply sqrt_qnr in Hx2; trivial.
  apply <- mult_1.
  right; split.
  rewrite <- (legendre_fst _ _ _ (q_prime k)).
  simpl_legendre.
  rewrite fst_opp.
  apply -> qr_opp_prime; trivial.
  rewrite opp_opp.
  rewrite fst_pair, fst_opp; trivial.
  rewrite <- (legendre_snd _ _ (p_prime k) (q_prime k)).
  simpl_legendre.
  rewrite snd_opp.
  apply -> qr_opp_prime; trivial.
  rewrite opp_opp.
  rewrite snd_pair, snd_opp; trivial.
  generalize (pair_spec (p k) (q k) (@distinct k) (p_prime k) (q_prime k)
    (sqrt_n (fst (p k) (q k) (p_prime k) (q_prime k) (opp _ _ x)))
    (sqrt_n (snd (p k) (q k) (p_prime k) (q_prime k) (opp _ _ x)))).
  intros [Hle_lt Hrp].
  simpl.
  unfold  fst, snd, sqrt_n in *.
  split.
  repeat rewrite power_nat_power in * ; simpl in *.
  destruct x; simpl in *.
  apply Zle_lt.
  rewrite <- Zmod_mod.
  rewrite Zmod_mod.
  apply Zmod_opp_diff_0.
  intro Hmod.
  apply Zmod_divide in Hmod.
  apply MiscZArith.Z_rel_prime_not_divide in Hrp.
  apply Hrp; trivial.
  omega.
  omega.
  apply Zmod_pos; omega.
  rewrite Z_mod_nz_opp_full.
  rewrite Zmod_mod.
  apply Zdiv2_small.
  omega.
  split.
  generalize Hsqrt4; simpl; intros; omega.
  apply Zmod_bound; omega.
  intro Hmod.
  apply Zmod_divide in Hmod.
  apply MiscZArith.Z_rel_prime_not_divide in Hrp.
  apply Hrp; trivial.
  omega.
  omega.
 Qed.

 Definition sqrt k (x : t k) : t k.
 intros k (x,Hx).
 case_eq ( Group2.qr_dec (Zstar (p k) (p_gt_1 (p k) (p_prime k))) 
   (Zstar.finite (p k) (p_gt_1 (p k) (p_prime k))) (fst (p k) (q k) (p_prime k) (q_prime k) x)); intros Hqr_fst _.
 case_eq ( Group2.qr_dec (Zstar (q k) (q_gt_1 (q k) (q_prime k))) 
   (Zstar.finite (q k) (q_gt_1 (q k) (q_prime k))) (snd (p k) (q k) (p_prime k) (q_prime k) x)); intros Hqr_snd _.
 case_eq (Z_le_dec (proj1_sig (sqrt1 x)) (Zdiv2 (p k * q k))); intros Hsqrt1 _.
 refine (exist _ (sqrt1 x) (@sqrt1_spec k x Hx Hqr_fst Hqr_snd Hsqrt1)).
 refine (exist _ (opp _ _ (sqrt1 x)) (@opp_sqrt1_spec k x Hx Hqr_fst Hqr_snd Hsqrt1)).
 refine (exist _ (sqrt2 x) (@sqrt2_spec k x Hx Hqr_fst Hqr_snd)).
 case_eq ( Group2.qr_dec (Zstar (q k) (q_gt_1 (q k) (q_prime k))) 
   (Zstar.finite (q k) (q_gt_1 (q k) (q_prime k))) (snd (p k) (q k) (p_prime k) (q_prime k) x)); intros Hqr_snd _.
 refine (exist _ (sqrt3 x) (@sqrt3_spec k x Hx Hqr_fst Hqr_snd)).
 case_eq (Z_le_dec (proj1_sig (sqrt4 x)) (Zdiv2 (p k * q k))); intros Hsqrt4 _. 
 refine (exist _ (sqrt4 x) (@sqrt4_spec k x Hx Hqr_fst Hqr_snd Hsqrt4)).
 refine (exist _ (opp _ _ (sqrt4 x)) (@opp_sqrt4_spec k x Hx Hqr_fst Hqr_snd Hsqrt4)).
 Defined.

 Lemma mul_sqrt k (x : t k) : mul (sqrt x) (sqrt x) = x.
 Proof.
  intros k (x,Hx).
  
  assert (Hp_prime := p_prime k).
  assert (Hq_prime := q_prime k).
  assert (Hp_blum := p_blum k).
  assert (Hq_blum := q_blum k).
  assert (Hp_odd := p_odd k).
  assert (Hq_odd := q_odd k).
  assert (Hp_diff := @p_diff_2 k).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  assert (Hpq_lt_1 := Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
  
  unfold mul, sqrt.
  case (Group2.qr_dec (Zstar (p k) (p_gt_1 (p k) (p_prime k)))
   (Zstar.finite (p k) (p_gt_1 (p k) (p_prime k)))
   (fst (p k) (q k) (p_prime k) (q_prime k) x)); intros.
  case (Group2.qr_dec (Zstar (q k) (q_gt_1 (q k) (q_prime k)))
   (Zstar.finite (q k) (q_gt_1 (q k) (q_prime k)))
   (snd (p k) (q k) (p_prime k) (q_prime k) x)); intros.
  case (Z_le_dec (proj1_sig (sqrt1 x)) (Zdiv2 (p k * q k))); intros.
  unfold sigT_of_sig.
  case (Z_le_dec (proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) (sqrt1 x) (sqrt1 x)))
   (Zdiv2 (p k * q k)));intros.
  apply subsetT_eq_compat.
  unfold sqrt1.
  rewrite mult_pair, sqrt_mult, sqrt_square_qr, sqrt_mult, sqrt_square_qr, pair_fst_snd; trivial.
  unfold sqrt1 in *; elim n.
  rewrite mult_pair, sqrt_mult, sqrt_square_qr, sqrt_mult, sqrt_square_qr, pair_fst_snd; trivial.
  apply P_prop in Hx; omega.
  
  unfold sigT_of_sig.
  case ( Z_le_dec (proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
   (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (sqrt1 x))
   (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (sqrt1 x)))) (Zdiv2 (p k * q k))); intros.
  apply subsetT_eq_compat.
  unfold sqrt1.
  rewrite mult_opp, mult_pair, sqrt_mult, sqrt_square_qr, sqrt_mult, sqrt_square_qr, pair_fst_snd; trivial.
  unfold sqrt1 in *; elim n0.
  rewrite mult_opp, mult_pair, sqrt_mult, sqrt_square_qr, sqrt_mult, sqrt_square_qr, pair_fst_snd; trivial.
  apply P_prop in Hx; omega.

  elimtype False.
  apply P_prop in Hx.
  unfold jacobi in *.
  destruct Hx as [Hx1 _].
  apply jacobi_plus in Hx1.
  destruct Hx1 as [ [Hx1 Hx2] | [Hx1 Hx2] ]. 
  elim n; trivial.
  elim Hx1; trivial.
  
  case (Group2.qr_dec (Zstar (q k) (q_gt_1 (q k) (q_prime k)))
   (Zstar.finite (q k) (q_gt_1 (q k) (q_prime k)))
   (snd (p k) (q k) (p_prime k) (q_prime k) x)); intros.
  elimtype False.
  apply P_prop in Hx.
  unfold jacobi in *.
  destruct Hx as [Hx1 _].
  apply jacobi_plus in Hx1.
  destruct Hx1 as [ [Hx1 Hx2] | [Hx1 Hx2] ]. 
  elim n; trivial.
  elim Hx2; trivial.
  
  case (Z_le_dec (proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) (sqrt4 x) (sqrt4 x)))
   (Zdiv2 (p k * q k)));intros.
  unfold sqrt4 in *.
  elimtype False.
  apply P_prop in Hx.
  assert (Zdiv2 (p k * q k) < `x).
  generalize z.
  unfold sqrt4.
  rewrite mult_pair, sqrt_mult, sqrt_square_qr, sqrt_mult, sqrt_square_qr, pair_fst_snd; trivial; simpl.
  destruct x as [x [Hlt Hrp] ]; simpl in *.
  intros.
  apply Zdiv2_small_mod in z0.
  rewrite Zmod_small in z0; omega.
  apply Zodd_mult_Zodd; trivial.
  omega.
  intro Heq.
  apply Zmod_divide in Heq.
  clear n n0 z Hx.
  apply MiscZArith.Z_rel_prime_not_divide in Hrp.
  apply Hrp; trivial.
  omega.
  omega.
  rewrite snd_opp.
  apply <- qr_opp_prime; trivial.
  rewrite fst_opp.
  apply <- qr_opp_prime; trivial.
  omega.

  case (Z_le_dec (proj1_sig (sqrt4 x)) (Zdiv2 (p k * q k))); intros; unfold sigT_of_sig.
  case (Z_le_dec (proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) (sqrt4 x) (sqrt4 x)))
   (Zdiv2 (p k * q k)));intros.
  elimtype False; omega.

  apply subsetT_eq_compat.
  unfold sqrt4.
  rewrite mult_pair, sqrt_mult, sqrt_mult; trivial.
  rewrite fst_opp, snd_opp, mult_opp, mult_opp, sqrt_square_qnr, sqrt_square_qnr; trivial.
  rewrite opp_pair, opp_opp, opp_opp, pair_fst_snd; trivial.
  rewrite <- mult_opp in n1.

  case (Z_le_dec (proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
   (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (sqrt4 x))
   (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (sqrt4 x)))) (Zdiv2 (p k * q k))); intros.
  elimtype False; omega.
  apply subsetT_eq_compat.
  unfold sqrt4.
  rewrite mult_opp.
  rewrite mult_pair, sqrt_mult, sqrt_mult; trivial.
  rewrite fst_opp, snd_opp, mult_opp, mult_opp, sqrt_square_qnr, sqrt_square_qnr; trivial.
  rewrite opp_pair, opp_opp, opp_opp, pair_fst_snd; trivial.
 Qed.

 Lemma group2_comm : forall n (W : 1 < n) (a b : Zstar n W),
  Group2.mult (Zstar n W) a b = Group2.mult (Zstar n W) b a.
 Proof.
  intros.
  repeat rewrite <- mult_group2mult.
  rewrite mult_comm; trivial.
 Qed.
 
 Lemma sqrt_mul k (x : t k) : sqrt (mul x x) = x.
 Proof.
  intros k (x,Hx).
  
  assert (Hp_prime := p_prime k).
  assert (Hq_prime := q_prime k).
  assert (Hp_blum := p_blum k).
  assert (Hq_blum := q_blum k).
  assert (Hp_odd := p_odd k).
  assert (Hq_odd := q_odd k).
  assert (Hp_diff := @p_diff_2 k).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  assert (Hpq_lt_1 := Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
  unfold mul, sqrt.
  
  case (Group2.qr_dec (Zstar (p k) (p_gt_1 (p k) (p_prime k)))
   (Zstar.finite (p k) (p_gt_1 (p k) (p_prime k)))
   (fst (p k) (q k) (p_prime k) (q_prime k) x)); intros.
  case (Group2.qr_dec (Zstar (q k) (q_gt_1 (q k) (q_prime k)))
   (Zstar.finite (q k) (q_gt_1 (q k) (q_prime k)))
   (snd (p k) (q k) (p_prime k) (q_prime k) x)); intros.

  case ( Z_le_dec (proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x))
   (Zdiv2 (p k * q k))); intros.
  unfold sigT_of_sig.
  case (Group2.qr_dec (Zstar (p k) (p_gt_1 (p k) (p_prime k)))
   (Zstar.finite (p k) (p_gt_1 (p k) (p_prime k)))
   (fst (p k) (q k) (p_prime k) (q_prime k)
    (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x))); intros.
  case (Group2.qr_dec (Zstar (q k) (q_gt_1 (q k) (q_prime k)))
   (Zstar.finite (q k) (q_gt_1 (q k) (q_prime k)))
   (snd (p k) (q k) (p_prime k) (q_prime k)
    (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x))); intros.
  case (Z_le_dec (proj1_sig (sqrt1 (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x)))
   (Zdiv2 (p k * q k))); intros.
  apply subsetT_eq_compat.
  unfold sqrt1.
  rewrite fst_mult, snd_mult, sqrt_square_qr, sqrt_square_qr, pair_fst_snd; trivial.
  elimtype False.
  unfold sqrt1 in n.
  rewrite fst_mult, snd_mult, sqrt_square_qr, sqrt_square_qr, pair_fst_snd in n ; trivial.
  apply P_prop in Hx; omega.
  elim n.
  rewrite snd_mult.
  apply Group2.qr_qr_mult_qr; trivial.
  apply group2_comm.
  elim n.
  rewrite fst_mult.
  apply Group2.qr_qr_mult_qr; trivial.
  apply group2_comm.
  unfold sigT_of_sig.
  case (Group2.qr_dec (Zstar (p k) (p_gt_1 (p k) (p_prime k)))
   (Zstar.finite (p k) (p_gt_1 (p k) (p_prime k)))
   (fst (p k) (q k) (p_prime k) (q_prime k)
    (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
     (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x)))); intros.
  elimtype False.
  rewrite fst_opp in q2.
  apply qr_opp_prime in q2; trivial.
  elim q2.
  rewrite fst_mult.
  apply Group2.qr_qr_mult_qr; trivial.
  apply group2_comm.
  case (Group2.qr_dec (Zstar (q k) (q_gt_1 (q k) (q_prime k)))
   (Zstar.finite (q k) (q_gt_1 (q k) (q_prime k)))
   (snd (p k) (q k) (p_prime k) (q_prime k)
    (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
     (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x)))); intros.
  elimtype False.
  rewrite snd_opp in q2.
  apply qr_opp_prime in q2; trivial.
  elim q2.
  rewrite snd_mult.
  apply Group2.qr_qr_mult_qr; trivial.
  apply group2_comm.
  case ( Z_le_dec (proj1_sig (sqrt4
   (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x))))
  (Zdiv2 (p k * q k))); intros.
  apply subsetT_eq_compat.
  unfold sqrt4.
  rewrite opp_opp, fst_mult, snd_mult, sqrt_square_qr, sqrt_square_qr, pair_fst_snd; trivial.
  unfold sqrt4 in n2.
  elimtype False.
  rewrite opp_opp, fst_mult, snd_mult, sqrt_square_qr, sqrt_square_qr, pair_fst_snd in n2; trivial.
  apply P_prop in Hx; omega.

  elimtype False.
  apply P_prop in Hx.
  destruct Hx as [Hx _].
  apply jacobi_plus in Hx.
  destruct Hx as [ [Hx1 Hx2] | [Hx1 Hx2] ]. 
  elim n; trivial.
  elim Hx1; trivial.

  case (Group2.qr_dec (Zstar (q k) (q_gt_1 (q k) (q_prime k)))
   (Zstar.finite (q k) (q_gt_1 (q k) (q_prime k)))
   (snd (p k) (q k) (p_prime k) (q_prime k) x)); intros.

  elimtype False.
  apply P_prop in Hx.
  destruct Hx as [Hx _].
  apply jacobi_plus in Hx.
  destruct Hx as [ [Hx1 Hx2] | [Hx1 Hx2] ]. 
  elim n; trivial.
  elim Hx2; trivial.

  case ( Z_le_dec (proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x))
   (Zdiv2 (p k * q k))); intros.
  unfold sigT_of_sig.
  case (Group2.qr_dec (Zstar (p k) (p_gt_1 (p k) (p_prime k)))
   (Zstar.finite (p k) (p_gt_1 (p k) (p_prime k)))
   (fst (p k) (q k) (p_prime k) (q_prime k)
    (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x))); intros.
  case (Group2.qr_dec (Zstar (q k) (q_gt_1 (q k) (q_prime k)))
   (Zstar.finite (q k) (q_gt_1 (q k) (q_prime k)))
   (snd (p k) (q k) (p_prime k) (q_prime k)
    (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x))); intros.
  case (Z_le_dec (proj1_sig (sqrt1 (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x)))
   (Zdiv2 (p k * q k))); intros.
  elimtype False.
  unfold sqrt1 in z0.
  rewrite  fst_mult, snd_mult, sqrt_square_qnr, sqrt_square_qnr, <- opp_pair, pair_fst_snd in z0; trivial.
  simpl in z0.
  apply Zdiv2_small_mod in z0.
  rewrite Zmod_small in z0.
  apply P_prop in Hx; omega.
  destruct x; simpl in *; omega. 
  apply Zodd_mult_Zodd; trivial.
  omega.
  intro Heq.
  destruct x as [x [Hx1 Hrp]]; simpl in *.
  apply Zmod_divide in Heq.
  clear q0 Hx n n0 q1.
  apply MiscZArith.Z_rel_prime_not_divide in Hrp.
  apply Hrp; trivial.
  omega.
  omega.
  apply subsetT_eq_compat.
  unfold sqrt1.
  rewrite  fst_mult, snd_mult, sqrt_square_qnr, sqrt_square_qnr, <- opp_pair, pair_fst_snd, opp_opp ; trivial.
  elim n1.
  rewrite snd_mult.
  apply (Group2.qnr_qnr_mult_qr (Zstar (q k) (q_gt_1 (q k) (q_prime k))) (Zstar.finite (q k) (q_gt_1 (q k) (q_prime k)))
   (generator (q k) (q_gt_1 (q k) (q_prime k)) Hq_prime) ); trivial.
  apply is_generator.
  rewrite order_Zstar_prime; trivial.
  rewrite MiscZArith.even_Zabs_nat.
  apply Zeven_pred; trivial.
  omega.
  elim n1.
  rewrite fst_mult.
  apply (Group2.qnr_qnr_mult_qr (Zstar (p k) (p_gt_1 (p k) (p_prime k))) (Zstar.finite (p k) (p_gt_1 (p k) (p_prime k)))
   (generator (p k) (p_gt_1 (p k) (p_prime k)) Hp_prime) ); trivial.
  apply is_generator.
  rewrite order_Zstar_prime; trivial.
  rewrite MiscZArith.even_Zabs_nat.
  apply Zeven_pred; trivial.
  omega.

  unfold sigT_of_sig.
  case (Group2.qr_dec (Zstar (p k) (p_gt_1 (p k) (p_prime k)))
   (Zstar.finite (p k) (p_gt_1 (p k) (p_prime k)))
   (fst (p k) (q k) (p_prime k) (q_prime k)
    (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
     (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x)))); intros.
  elimtype False.
  rewrite fst_opp in q0.
  apply qr_opp_prime in q0; trivial.
  elim q0.
  rewrite fst_mult.
  apply (Group2.qnr_qnr_mult_qr (Zstar (p k) (p_gt_1 (p k) (p_prime k))) (Zstar.finite (p k) (p_gt_1 (p k) (p_prime k)))
   (generator (p k) (p_gt_1 (p k) (p_prime k)) Hp_prime) ); trivial.
  apply is_generator.
  rewrite order_Zstar_prime; trivial.
  rewrite MiscZArith.even_Zabs_nat.
  apply Zeven_pred; trivial.
  omega.
  case (Group2.qr_dec (Zstar (q k) (q_gt_1 (q k) (q_prime k)))
   (Zstar.finite (q k) (q_gt_1 (q k) (q_prime k)))
   (snd (p k) (q k) (p_prime k) (q_prime k)
    (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
     (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x)))); intros.
  elimtype False.
  rewrite snd_opp in q0.
  apply qr_opp_prime in q0; trivial.
  elim q0.
  rewrite snd_mult.
  apply (Group2.qnr_qnr_mult_qr (Zstar (q k) (q_gt_1 (q k) (q_prime k))) (Zstar.finite (q k) (q_gt_1 (q k) (q_prime k)))
   (generator (q k) (q_gt_1 (q k) (q_prime k)) Hq_prime) ); trivial.
  apply is_generator.
  rewrite order_Zstar_prime; trivial.
  rewrite MiscZArith.even_Zabs_nat.
  apply Zeven_pred; trivial.
  omega.
  case ( Z_le_dec (proj1_sig (sqrt4
   (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x x))))
  (Zdiv2 (p k * q k))); intros.
  elimtype False.
  unfold sqrt4 in z.
  rewrite opp_opp, fst_mult, snd_mult, sqrt_square_qnr, sqrt_square_qnr, <- opp_pair, pair_fst_snd in z; trivial. 
  simpl in z.
  apply Zdiv2_small_mod in z.
  rewrite Zmod_small in z.
  apply P_prop in Hx; omega.
  destruct x; simpl in *; omega. 
  apply Zodd_mult_Zodd; trivial.
  omega.
  intro Heq.
  destruct x as [x [Hx1 Hrp]]; simpl in *.
  apply Zmod_divide in Heq.
  clear Hx n n0 n2 n3.
  apply MiscZArith.Z_rel_prime_not_divide in Hrp.
  apply Hrp; trivial.
  omega.
  omega.
  apply subsetT_eq_compat.
  unfold sqrt4.
  rewrite opp_opp, fst_mult, snd_mult, sqrt_square_qnr, sqrt_square_qnr, <- opp_pair, pair_fst_snd, opp_opp ; trivial.
 Qed.

 Lemma opp_mult_r : forall (n : Z) (n_gt_1 : 1 < n) (x y : Zstar n n_gt_1),
  opp n n_gt_1 (Group2.mult (Zstar n n_gt_1) x y) =
  Group2.mult (Zstar n n_gt_1) x (opp n n_gt_1 y).
 Proof.
  intros.
  pattern (Group2.mult (Zstar n n_gt_1) x (opp n n_gt_1 y)).
  rewrite <- mult_opp.
  rewrite opp_opp.
  apply opp_mult_l.
 Qed.

 Lemma opp_contradic k (x : carrier (p k * q k)) : 
  proj1_sig (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) x) <= Zdiv2 (p k * q k) -> 
   proj1_sig x <= Zdiv2 (p k * q k) -> False.
 Proof.
  intros k (x, (Hx1, Hx2) ) H1 H2.
  simpl in *. 
  apply Zdiv2_small_mod in H1.
  rewrite Zmod_small in H1.
  omega.
  omega.
  apply Zodd_mult_Zodd;[ apply p_odd | apply q_odd ].
  omega.
  intro Heq.
  apply Zmod_divide in Heq.
  apply MiscZArith.Z_rel_prime_not_divide in Hx2.
  apply Hx2; trivial.
  apply pq_gt_1.
  apply p_prime.
  apply q_prime.
  omega.
 Qed.

 Lemma not_opp_contradic k (x : carrier (p k * q k)) : 
  ~ proj1_sig (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) x) <= Zdiv2 (p k * q k) -> 
  ~ proj1_sig x <= Zdiv2 (p k * q k) -> False.
 Proof.
  intros k (x, (Hx1, Hx2) ) H1 H2.
  simpl in *.
  apply not_Zle_lt in H1.  
  apply not_Zle_lt in H2.
  apply Zlt_gt in H1.
  apply Zdiv2_small_mod_bis_rev in H1.
  rewrite Zmod_small in H1.
  omega.
  omega.
  apply Zodd_mult_Zodd;[ apply p_odd | apply q_odd ].
  omega.
  intro Heq.
  apply Zmod_divide in Heq.
  apply MiscZArith.Z_rel_prime_not_divide in Hx2.
  apply Hx2; trivial.
  apply pq_gt_1.
  apply p_prime.
  apply q_prime.
  omega.
 Qed.

 Lemma qnr_opp_prime: forall (n : Z) (n_gt_1 : 1 < n),
  prime n -> Zodd n -> n mod 4 = 3 mod 4 ->
  forall x : Zstar n n_gt_1,
   ~ Group2.QuadraticResidue (opp n n_gt_1 x) <-> Group2.QuadraticResidue x.
 Proof.
  intros; split; intros.
  apply qr_opp_prime in H2; trivial.
  rewrite opp_opp in H2; trivial.
  apply -> qr_opp_prime; trivial.
  rewrite opp_opp; trivial.
 Qed.
  
 Lemma mul_sqrt_mul : forall k (x y : t k), mul (sqrt x) (sqrt y) = sqrt (mul x y).
 Proof.
  intros k (x,Hx) (y,Hy).

  assert (Hp_prime := p_prime k).
  assert (Hq_prime := q_prime k).
  assert (Hp_blum := p_blum k).
  assert (Hq_blum := q_blum k).
  assert (Hp_odd := p_odd k).
  assert (Hq_odd := q_odd k).
  assert (Hp_diff := @p_diff_2 k).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  assert (Hpq_lt_1 := Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
  unfold mul, sqrt, sigT_of_sig.

  assert (even (Group2.order (Zstar (q k) (q_gt_1 (q k) (q_prime k))))).
  rewrite order_Zstar_prime; trivial.
  rewrite MiscZArith.even_Zabs_nat.
  apply Zeven_pred; trivial.
  omega.
  
  assert (even (Group2.order (Zstar (p k) (p_gt_1 (p k) (p_prime k))))).
  rewrite order_Zstar_prime; trivial.
  rewrite MiscZArith.even_Zabs_nat.
  apply Zeven_pred; trivial.
  omega.
   
  repeat match goal with |- context [match ?x with left _ => _ | right _ => _ end] => case x;intros end;
  (*simpl cases*)
  try (apply subsetT_eq_compat); trivial;
  try (apply f_equal); trivial;
  try (rewrite sqrt1_sqrt4 in * ); trivial;
  try (rewrite sqrt1_mult in * ); trivial;
  try (rewrite <- sqrt1_opp_sqrt4 in * );  trivial;
  try (rewrite <- sqrt4_opp_sqrt1 in * ); trivial;
  try (rewrite <- opp_mult_r); trivial;
  try (rewrite sqrt1_mult); trivial;
  try (rewrite opp_opp);   trivial;
  try (apply f_equal); trivial;
  try (rewrite sqrt1_sqrt4 in * ); trivial;
  try (rewrite sqrt1_mult in * );  trivial;
  try (rewrite <- sqrt1_opp_sqrt4 in * );  trivial;
  try (rewrite <- sqrt4_opp_sqrt1 in * ); trivial;
  try (rewrite <- opp_mult_r); trivial;
  try (rewrite sqrt1_mult); trivial;
  try (rewrite opp_opp); trivial;
  try (rewrite <- sqrt1_mult, opp_mult_l); trivial;
  try (rewrite <- sqrt1_mult, opp_mult_l, opp_opp); trivial;
  try (rewrite opp_opp); trivial;
  try (rewrite <- sqrt1_mult, opp_mult_l); trivial;
  try (rewrite <- sqrt1_mult, opp_mult_l, opp_opp); trivial;
  try (rewrite sqrt1_mult in * ); trivial;
  try (rewrite <- opp_mult_l, sqrt1_sqrt4); trivial;
  try (rewrite <- opp_mult_l, sqrt1_sqrt4, opp_opp); trivial;
  try (rewrite opp_opp); trivial;
  try (rewrite group2_comm, sqrt1_sqrt4, group2_comm); trivial;
  try (rewrite sqrt4_mult, <- sqrt1_opp_sqrt4); trivial;
  try (elimtype False; omega);
  try (rewrite <- opp_mult_l, group2_comm, sqrt1_sqrt4, group2_comm, opp_opp); trivial;
  try (rewrite <- opp_mult_l, sqrt4_mult,<- sqrt1_opp_sqrt4, <- opp_mult_l, sqrt1_mult); trivial;
  try (rewrite <- opp_mult_l, group2_comm, sqrt1_sqrt4, group2_comm); trivial;


  (* hypothesis simplification *)
  try (match goal with [H : proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) ?x)
    (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) ?y)) <= Zdiv2 (p k * q k) |- _ ] =>
  rewrite mult_opp in H end);
  try (match goal with [H : ~ proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) ?x)
    (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) ?y)) <= Zdiv2 (p k * q k) |- _ ] =>
  rewrite mult_opp in H end);
  try (match goal with [H : ~ proj1_sig (sqrt4 (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
    (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) _ _))) <= Zdiv2 (p k * q k)
  |- _ ]  => rewrite <- sqrt1_opp_sqrt4 in H end);
  try (match goal with [H : proj1_sig (sqrt4 (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
    (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) _ _))) <= Zdiv2 (p k * q k)
  |- _ ]  => rewrite <- sqrt1_opp_sqrt4 in H end);
  try (match goal with [H : proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (?f1 _) (opp (p k * q k)
      (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (?f2 _))) <= Zdiv2 (p k * q k) |- _ ] =>
  rewrite <- opp_mult_r in H; (rewrite sqrt1_mult in H || rewrite sqrt1_sqrt4 in H) end);
  try (match goal with [H : ~ proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (?f1 _) (opp (p k * q k)
      (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (?f2 _))) <= Zdiv2 (p k * q k) |- _ ] =>
  rewrite <- opp_mult_r in H; (rewrite sqrt1_mult in H || rewrite sqrt1_sqrt4 in H) end);
  try (match goal with [H : proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (opp (p k * q k)
      (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (?f2 _)) (?f1 _)) <= Zdiv2 (p k * q k) |- _ ] =>
  rewrite <- opp_mult_l in H; (rewrite sqrt1_mult in H || rewrite sqrt1_sqrt4 in H) end);
  try (match goal with [H : ~ proj1_sig (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (opp (p k * q k)
      (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (?f2 _)) (?f1 _)) <= Zdiv2 (p k * q k) |- _ ] =>
  rewrite <- opp_mult_l in H; (rewrite sqrt1_mult in H || rewrite sqrt1_sqrt4 in H) end);
  try (match goal with [ H: ~ Group2.QuadraticResidue
   (?f (p k) (q k) (p_prime k) (q_prime k)
     (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
       (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x y))) |- _] =>
 (rewrite fst_opp in H || rewrite snd_opp in H) ; apply qnr_opp_prime in H; trivial
  end);
  try (match goal with [H : proj1_sig (Group2.mult
    (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (sqrt1 ?x) (sqrt1 ?y)) <= Zdiv2 (p k * q k) |- _] => rewrite sqrt1_mult in H end);
  try (match goal with [H : ~ proj1_sig (Group2.mult
    (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (sqrt1 ?x) (sqrt1 ?y)) <= Zdiv2 (p k * q k) |- _] => rewrite sqrt1_mult in H end);
 try (match goal with [H:proj1_sig (Group2.mult
            (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
            (opp (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
               (sqrt4 ?x)) (sqrt4 ?y)) <= Zdiv2 (p k * q k) |- _] =>
 rewrite <- opp_mult_l, sqrt4_mult, <- sqrt1_opp_sqrt4 in H end);

  (* qr contradiction*)
  try (match goal with [H : ~ Group2.QuadraticResidue
    (snd (p k) (q k) (p_prime k) (q_prime k)
      (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) _ _)) |- _ ]  =>
  try (elim H; rewrite snd_mult; apply Group2.qr_qr_mult_qr; trivial; apply group2_comm) end);
  try (match goal with [H : ~ Group2.QuadraticResidue
    (fst (p k) (q k) (p_prime k) (q_prime k)
      (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) _ _)) |- _ ]  =>
  try (elim H; rewrite fst_mult; apply Group2.qr_qr_mult_qr; trivial; apply group2_comm) end);
  try (match goal with [H :Group2.QuadraticResidue
          (fst (p k) (q k) (p_prime k) (q_prime k)
             (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
                (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) _ _ ))) |- _ ]  =>
  elimtype False; rewrite fst_opp in H; apply qr_opp_prime in H; trivial; elim H; rewrite fst_mult;
  apply Group2.qr_qr_mult_qr; trivial; apply group2_comm end);
  try (match goal with [H :Group2.QuadraticResidue
          (snd (p k) (q k) (p_prime k) (q_prime k)
             (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
                (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) _ _ ))) |- _ ]  =>
  elimtype False; rewrite snd_opp in H; apply qr_opp_prime in H; trivial; elim H; rewrite snd_mult;
  apply Group2.qr_qr_mult_qr; trivial; apply group2_comm end);
  try (match goal with
  [H1 : Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k) ?y) |- _ ] =>
  match goal with [H2 : ~ Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k) y) |- _ ] =>
    elimtype False; apply P_prop in Hy; destruct Hy as [Hj _];
    apply jacobi_plus in Hj; tauto
  end end);
  try (match goal with
  [H1 : Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k) ?y) |- _ ] =>
  match goal with [H2 : ~ Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k) y) |- _ ] =>
    elimtype False; apply P_prop in Hx; destruct Hx as [Hj _];
    apply jacobi_plus in Hj; tauto
  end end);
  try (match goal with
  [H1 : ~Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k) ?y) |- _ ] =>
  match goal with [H2 : Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k) y) |- _ ] =>
    elimtype False; apply P_prop in Hy; destruct Hy as [Hj _];
    apply jacobi_plus in Hj; tauto
  end end);
  try (match goal with
  [H1 : ~Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k) ?y) |- _ ] =>
  match goal with [H2 : Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k) y) |- _ ] =>
    elimtype False; apply P_prop in Hx; destruct Hx as [Hj _];
    apply jacobi_plus in Hj; tauto
  end end);
  try (match goal with
  [H1 : ~ Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k) ?x) |- _ ] =>
  match goal with [H2 : Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k) ?y) |- _ ] =>
    match goal with [H3 : Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k)
        (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x y))
   |- _ ] =>
    elimtype False;
    elim (Group2.qnr_qr_mult_qnr _ (@group2_comm (q k) (q_gt_1 (q k) (q_prime k)))
      (snd (p k) (q k) (p_prime k) (q_prime k) x) (snd (p k) (q k) (p_prime k) (q_prime k) y) H1 H2);
    rewrite <- snd_mult; trivial
    end end end);
 try (match goal with
  [H1 : ~ Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k) ?x) |- _ ] =>
  match goal with [H2 : Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k) ?y) |- _ ] =>
    match goal with [H3 : Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k)
        (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x y))
   |- _ ] =>
    elimtype False;
    elim (Group2.qnr_qr_mult_qnr _ (@group2_comm (p k) (p_gt_1 (p k) (p_prime k)))
      (fst (p k) (q k) (p_prime k) (q_prime k) x) (fst (p k) (q k) (p_prime k) (q_prime k) y) H1 H2);
    rewrite <- fst_mult; trivial
    end end end);
  try (match goal with
    [H1 : Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k) ?x) |- _ ] =>
    match goal with [H2 : ~ Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k) ?y) |- _ ] =>
      match goal with [H3 : Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k)
        (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x y))
      |- _ ] =>
      elimtype False;
      elim (Group2.qnr_qr_mult_qnr _ (@group2_comm (p k) (p_gt_1 (p k) (p_prime k)))
        (fst (p k) (q k) (p_prime k) (q_prime k) y) (fst (p k) (q k) (p_prime k) (q_prime k) x) H2 H1);
      rewrite <- fst_mult; rewrite group2_comm; trivial
      end end end);
  try (match goal with
    [H1 : Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k) ?x) |- _ ] =>
    match goal with [H2 : ~ Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k) ?y) |- _ ] =>
      match goal with [H3 : Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k)
        (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x y))
      |- _ ] =>
      elimtype False;
      elim (Group2.qnr_qr_mult_qnr _ (@group2_comm (q k) (q_gt_1 (q k) (q_prime k)))
        (snd (p k) (q k) (p_prime k) (q_prime k) y) (snd (p k) (q k) (p_prime k) (q_prime k) x) H2 H1);
      rewrite <- snd_mult; rewrite group2_comm; trivial
      end end end);
  try (match goal with [H : ~ proj1_sig (sqrt4 (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
    (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) _ _))) <= Zdiv2 (p k * q k)
  |- _ ]  => rewrite <- sqrt1_opp_sqrt4 in H end);
  try (match goal with [H : proj1_sig (sqrt4 (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
    (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) _ _))) <= Zdiv2 (p k * q k)
  |- _ ]  => rewrite <- sqrt1_opp_sqrt4 in H end);
  try (match goal with [H : proj1_sig (Group2.mult
    (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (sqrt1 ?x) (sqrt4 ?y)) <= Zdiv2 (p k * q k) |- _] =>
  rewrite sqrt1_sqrt4 in H end);
  try (match goal with [H : ~ proj1_sig (Group2.mult
    (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (sqrt1 ?x) (sqrt4 ?y)) <= Zdiv2 (p k * q k) |- _] =>
  rewrite sqrt1_sqrt4 in H end);
  try (match goal with [H : proj1_sig (Group2.mult
    (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (sqrt4 ?x) (sqrt1 ?y)) <= Zdiv2 (p k * q k) |- _] =>
  rewrite group2_comm, sqrt1_sqrt4, group2_comm in H end);
  try (match goal with [H : ~ proj1_sig (Group2.mult
    (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (sqrt4 ?x) (sqrt1 ?y)) <= Zdiv2 (p k * q k) |- _] =>
  rewrite group2_comm, sqrt1_sqrt4, group2_comm in H end);
  try (match goal with [H : proj1_sig (Group2.mult
   (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
   (sqrt4 ?x)
   (opp (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
     (sqrt1 ?y))) <= Zdiv2 (p k * q k) |- _] => rewrite <- opp_mult_r,group2_comm,sqrt1_sqrt4,group2_comm in H end);
  try (match goal with [H : ~ proj1_sig (Group2.mult
   (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
   (sqrt4 ?x)
   (opp (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
     (sqrt1 ?y))) <= Zdiv2 (p k * q k) |- _] => rewrite <- opp_mult_r,group2_comm,sqrt1_sqrt4,group2_comm in H end);
  try (match goal with
         [H : proj1_sig (Group2.mult
           (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
           (sqrt4 ?x) (sqrt4 ?y)) <=
         Zdiv2 (p k * q k) |- _] => rewrite sqrt4_mult, <- sqrt1_opp_sqrt4 in H end);
  try (match goal with
         [H : ~ proj1_sig (Group2.mult
           (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
           (sqrt4 ?x) (sqrt4 ?y)) <=
         Zdiv2 (p k * q k) |- _] => rewrite sqrt4_mult, <- sqrt1_opp_sqrt4 in H end);
  try (match goal with
         [H : proj1_sig (Group2.mult
           (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
           (sqrt4 ?x) (opp (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (sqrt4 ?y))) <=
         Zdiv2 (p k * q k) |- _] =>
         rewrite <- opp_mult_r , sqrt4_mult, <- sqrt1_opp_sqrt4 in H end);
  try (match goal with
         [H : ~ proj1_sig (Group2.mult
           (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
           (sqrt4 ?x) (opp (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) (sqrt4 ?y))) <=
         Zdiv2 (p k * q k) |- _] =>
         rewrite <- opp_mult_r , sqrt4_mult, <- sqrt1_opp_sqrt4 in H end);
  try (match goal with [H : proj1_sig (Group2.mult
    (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (sqrt4 ?x) (sqrt4 ?y)) <= Zdiv2 (p k * q k) |- _] =>
  rewrite sqrt4_mult, <- sqrt1_opp_sqrt4 in H end);
  try (match goal with [H : proj1_sig (Group2.mult
    (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (sqrt4 ?x) (sqrt4 ?y)) <= Zdiv2 (p k * q k) |- _] =>
  rewrite sqrt4_mult, <- sqrt1_opp_sqrt4 in H end);
  try (match goal with [H : Group2.QuadraticResidue
    (fst (p k) (q k) (p_prime k) (q_prime k)
      (opp (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
        (Group2.mult (Zstar (p k * q k)
          (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) ?x ?y))) |- _] =>
  rewrite fst_opp in H; apply qr_opp_prime in H; trivial end);
  try (match goal with [H : Group2.QuadraticResidue
    (snd (p k) (q k) (p_prime k) (q_prime k)
      (opp (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
        (Group2.mult (Zstar (p k * q k)
          (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) ?x ?y))) |- _] =>
  rewrite snd_opp in H; apply qr_opp_prime in H; trivial end);
  try (match goal with [H: proj1_sig (Group2.mult
    (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (opp (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
      (sqrt4 ?x)) (sqrt1 ?y)) <= Zdiv2 (p k * q k) |- _] =>
  rewrite <- opp_mult_l, group2_comm, sqrt1_sqrt4, group2_comm  in H end);
  try (match goal with [H: ~ proj1_sig (Group2.mult
    (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (opp (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
      (sqrt4 ?x)) (sqrt1 ?y)) <= Zdiv2 (p k * q k) |- _] =>
  rewrite <- opp_mult_l, group2_comm, sqrt1_sqrt4, group2_comm  in H end);
  try (match goal with [H: ~ proj1_sig (Group2.mult
    (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (opp (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
      (sqrt4 ?x)) (sqrt1 ?y)) <= Zdiv2 (p k * q k) |- _] =>
  rewrite  <- opp_mult_l, group2_comm, sqrt4_mult, <- sqrt1_opp_sqrt4  in H end);
  try (match goal with
  [H1 : ~ Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k) ?x) |- _ ] =>
  match goal with [H2 : ~Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k) ?y) |- _ ] =>
    match goal with [H3 : ~Group2.QuadraticResidue (snd (p k) (q k) (p_prime k) (q_prime k)
        (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x y))
   |- _ ] =>
    elim H3;
      rewrite snd_mult;
        apply (Group2.qnr_qnr_mult_qr (Zstar (q k) (q_gt_1 (q k) (q_prime k))) (finite (q k) (q_gt_1 (q k) (q_prime k)))
          (generator (q k) (q_gt_1 (q k) (q_prime k)) Hq_prime) ); [ apply is_generator  | | | ]; trivial
    end end end);
  try (match goal with
  [H1 : ~ Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k) ?x) |- _ ] =>
  match goal with [H2 : ~Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k) ?y) |- _ ] =>
    match goal with [H3 : ~Group2.QuadraticResidue (fst (p k) (q k) (p_prime k) (q_prime k)
        (Group2.mult (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))) x y))
   |- _ ] =>
    elim H3;
      rewrite fst_mult;
        apply (Group2.qnr_qnr_mult_qr (Zstar (p k) (p_gt_1 (p k) (p_prime k))) (finite (p k) (p_gt_1 (p k) (p_prime k)))
          (generator (p k) (p_gt_1 (p k) (p_prime k)) Hp_prime) ); [ apply is_generator  | | | ]; trivial
    end end end);
  try (match goal with [H: proj1_sig (Group2.mult
    (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (opp (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
      (sqrt4 ?x)) (sqrt1 ?y)) <= Zdiv2 (p k * q k) |- _] =>
  rewrite <- opp_mult_l, group2_comm, sqrt1_sqrt4, group2_comm  in H end);
  try (match goal with [H: ~ proj1_sig (Group2.mult
    (Zstar (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)))
    (opp (p k * q k) (pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))
      (sqrt4 ?x)) (sqrt1 ?y)) <= Zdiv2 (p k * q k) |- _] =>
  rewrite <- opp_mult_l, group2_comm, sqrt1_sqrt4, group2_comm  in H end);
  try (elimtype False; omega);

  (* contradiction *)
  try (match goal with
  [H1 : proj1_sig (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) ?x) <= Zdiv2 (p k * q k) |- _ ]  =>
  match goal with [H2 : proj1_sig x <= Zdiv2 (p k * q k) |- _ ] =>  elim (@opp_contradic _ _ H1 H2) end end);

  try (match goal with
  [H1 : ~proj1_sig (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) ?x) <= Zdiv2 (p k * q k) |- _ ]  =>
  match goal with [H2 : ~proj1_sig x <= Zdiv2 (p k * q k) |- _ ] =>  elim (@not_opp_contradic _ _ H1 H2) end end);

  try (match goal with [H1 : ~ ?x <= Zdiv2 (p k * q k) |- _ ]  =>
    match goal with [H2 : x <= Zdiv2 (p k * q k) |- _ ] => elim H1; trivial end end);
  try (elimtype False; omega).

  rewrite <- opp_mult_l, group2_comm, sqrt4_mult,group2_comm, <- sqrt1_opp_sqrt4 in n4.
  try (match goal with
  [H1 : proj1_sig (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) ?x) <= Zdiv2 (p k * q k) |- _ ]  =>
  match goal with [H2 : proj1_sig x <= Zdiv2 (p k * q k) |- _ ] =>  elim (@opp_contradic _ _ H1 H2) end end);

  try (match goal with
  [H1 : ~proj1_sig (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) ?x) <= Zdiv2 (p k * q k) |- _ ]  =>
  match goal with [H2 : ~proj1_sig x <= Zdiv2 (p k * q k) |- _ ] =>  elim (@not_opp_contradic _ _ H1 H2) end end);

  try (match goal with [H1 : ~ ?x <= Zdiv2 (p k * q k) |- _ ]  =>
    match goal with [H2 : x <= Zdiv2 (p k * q k) |- _ ] => elim H1; trivial end end);
  try (elimtype False; omega).

  rewrite <- opp_mult_l, group2_comm, sqrt4_mult,group2_comm, <- sqrt1_opp_sqrt4 in n4.
  try (match goal with
  [H1 : proj1_sig (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) ?x) <= Zdiv2 (p k * q k) |- _ ]  =>
  match goal with [H2 : proj1_sig x <= Zdiv2 (p k * q k) |- _ ] =>  elim (@opp_contradic _ _ H1 H2) end end);

  try (match goal with
  [H1 : ~proj1_sig (opp (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)) ?x) <= Zdiv2 (p k * q k) |- _ ]  =>
  match goal with [H2 : ~proj1_sig x <= Zdiv2 (p k * q k) |- _ ] =>  elim (@not_opp_contradic _ _ H1 H2) end end);

  try (match goal with [H1 : ~ ?x <= Zdiv2 (p k * q k) |- _ ]  =>
    match goal with [H2 : x <= Zdiv2 (p k * q k) |- _ ] => elim H1; trivial end end);
  try (elimtype False; omega).
 Qed.

 Definition order (k : nat) : nat := 
  Group2.order (Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k))).

 Close Scope Z_scope.

 Definition cost_mul k (x y:t k) : nat := size_Z (proj1_sig (proj1_sig y)).

 Definition cost_pow k (x:t k) (m:Z) : nat :=
  size_Z (proj1_sig (proj1_sig x)) * (size_Z (p k * q k)).

 Definition cost_inv k (x:t k) : nat := 
  size_Z (proj1_sig (proj1_sig x)) * (size_Z (p k * q k)).

 Definition cost_sqrt k (x:t k) : nat := (cost_pow x (p k)) + (cost_pow x (q k)).

 Definition cost_mul_poly  := pplus p_poly q_poly. 
 Definition cost_pow_poly  := pmult (pplus p_poly q_poly) (pplus p_poly q_poly).
 Definition cost_inv_poly  := pmult (pplus p_poly q_poly) (pplus p_poly q_poly).
 Definition cost_sqrt_poly := pplus cost_pow_poly cost_pow_poly.

 Lemma size_Z_mult x y : size_Z (x * y) <= size_Z x + size_Z y.
 Proof.
  intros; unfold size_Z.
  rewrite Zabs_nat_mult.
  apply size_nat_mult.
 Qed. 

 Lemma cost_mul_poly_spec : forall k (x y:t k),
  cost_mul x y <= peval cost_mul_poly k.
 Proof.
  intros k x ((b,Hb'),Hb).
  unfold cost_mul; simpl.
  apply P_prop in Hb; decompose [and] Hb; clear Hb.
  apply le_trans with (size_Z (p k * q k)).
  apply size_nat_monotonic; apply lt_le_weak; trivial.
  apply Zabs_nat_lt; omega.
  unfold cost_mul_poly.
  rewrite pplus_spec.
  eapply le_trans.
  apply size_Z_mult.
  apply plus_le_compat.
  apply lt_le_weak; apply p_poly_spec.
  apply lt_le_weak; apply q_poly_spec.
 Qed.

 Lemma cost_pow_poly_spec : forall k (x:t k) (m:Z),
  cost_pow x m <= peval cost_pow_poly k.
 Proof.
  intros k ((a,Ha'),Ha) m.
  unfold cost_pow, cost_pow_poly; simpl.
  rewrite pmult_spec.
  apply P_prop in Ha; decompose [and] Ha; clear Ha.
  apply mult_le_compat.
  apply le_trans with (size_Z (p k * q k)).
  apply size_nat_monotonic; apply lt_le_weak; trivial.
  apply Zabs_nat_lt; omega.
  eapply le_trans.
  apply size_Z_mult.
  rewrite pplus_spec.
  apply plus_le_compat.
  apply lt_le_weak; apply p_poly_spec.
  apply lt_le_weak; apply q_poly_spec.
  rewrite pplus_spec.
  eapply le_trans.
  apply size_Z_mult.
  apply plus_le_compat.
  apply lt_le_weak; apply p_poly_spec.
  apply lt_le_weak; apply q_poly_spec.
 Qed.

 Lemma cost_inv_poly_spec : forall k (x:t k),
  cost_inv x <= peval cost_inv_poly k.
 Proof.
  intros k ((a,Ha'),Ha).
  unfold cost_inv, cost_inv_poly; simpl.
  rewrite pmult_spec.
  apply P_prop in Ha; decompose [and] Ha; clear Ha.
  apply mult_le_compat.
  apply le_trans with (size_Z (p k * q k)).
  apply size_nat_monotonic; apply lt_le_weak; trivial.
  apply Zabs_nat_lt; omega.
  eapply le_trans.
  apply size_Z_mult.
  rewrite pplus_spec.
  apply plus_le_compat.
  apply lt_le_weak; apply p_poly_spec.
  apply lt_le_weak; apply q_poly_spec.
  rewrite pplus_spec.
  eapply le_trans.
  apply size_Z_mult.
  apply plus_le_compat.
  apply lt_le_weak; apply p_poly_spec.
  apply lt_le_weak; apply q_poly_spec.
 Qed.

 Lemma cost_sqrt_poly_spec : forall k (x:t k),
  cost_sqrt x <= peval cost_sqrt_poly k.
 Proof.
  intros k x.
  unfold cost_sqrt, cost_sqrt_poly; simpl.
  rewrite pplus_spec.
  apply plus_le_compat.
  apply cost_pow_poly_spec.
  apply cost_pow_poly_spec.
 Qed.

 Definition order_poly := pplus p_poly q_poly.
  
 Lemma order_size_nat : forall k,
  size_nat (length (elems k)) < peval order_poly k.
 Proof.
  intro k.
  assert (Hp_prime := p_prime k).
  assert (Hq_prime := q_prime k).
  assert (Hp_blum := p_blum k).
  assert (Hq_blum := q_blum k).
  assert (Hp_odd := p_odd k).
  assert (Hq_odd := q_odd k).
  assert (Hp_diff := @p_diff_2 k).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  assert (Hpq_lt_1 := Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).
  unfold mul, sqrt, sigT_of_sig.

  eapply le_lt_trans.
  apply size_nat_monotonic.
  unfold elems.
  apply filter_map_length.
  generalize (length_Zstar_list (p k) (q k) (@distinct k) (p_prime k) (q_prime k)); intros.
  unfold Group2.carrier in H.
  unfold Zstar in H.
  rewrite H.
  generalize (Zstar_list_length (p k) (p_gt_1 (p k) (p_prime k)) (p_prime k)); intros.
  unfold Group2.carrier in H0.
  unfold Zstar in H0.
  rewrite H0.
  generalize (Zstar_list_length (q k) (q_gt_1 (q k) (q_prime k)) (q_prime k)); intros.
  unfold Group2.carrier in H1.
  unfold Zstar in H1.
  rewrite H1.
  unfold order_poly.
  rewrite pplus_spec.
  rewrite <- Zabs_nat_mult.
  apply le_lt_trans with (size_Z (p k * q k)).
  unfold size_Z.
  apply size_nat_monotonic.
  apply Zabs_nat_le.
  split.
  auto with zarith.
  ring_simplify.
  auto with zarith.
  apply le_lt_trans with (size_Z (p k) + size_Z (q k)).
  apply size_Z_mult.
  apply plus_lt_compat.
  apply p_poly_spec.
  apply q_poly_spec.
 Qed.
 
 Open Scope Z_scope.

 Definition Dp (k : nat) := (Zstar (p k) (p_gt_1 (p k) (p_prime k))).
 Definition Dq (k : nat) := (Zstar (q k) (q_gt_1 (q k) (q_prime k))).
 Definition D (k : nat) := Zstar (p k * q k) (Zstar.pq_gt_1 (p k) (q k) (p_prime k) (q_prime k)).

 Definition two_Dp k : Dp k.
  intro.
  refine (exist _ 2%Z _).
  assert (Hp_diff := @p_diff_2 k).
  assert (Hp_prime := @p_prime k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  split;[ split; [omega | ] | ].
  omega.
  apply rel_prime_le_prime; trivial;  omega.
 Defined.

 Definition two_Dq k : Dq k.
  intro.
  refine (exist _ 2%Z _).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hq_prime := @q_prime k).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  split;[ split; [omega | ] | ].
  omega.
  apply rel_prime_le_prime; trivial;  omega.
 Defined.

 Definition two_D k : D k.
  intro.
  refine (exist _ 2%Z _).
  assert (Hp_diff := @p_diff_2 k).
  assert (Hp_prime := @p_prime k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hq_prime := @q_prime k).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  split;[ split; [omega | ] | ].
  apply Zlt_trans with (p k).
  omega.
  rewrite <- (Zmult_1_r (p k)) at 1.
  apply Zmult_gt_0_lt_compat_l; omega.
  apply rel_prime_mult; apply rel_prime_le_prime; trivial;  omega.
 Defined.

 Definition four_D k : D k.
  intro.
  refine (exist _ 4%Z _).
  assert (Hp_diff := @p_diff_2 k).
  assert (Hp_prime := @p_prime k).
  assert (Hp_ge_2 := prime_ge_2 _ Hp_prime).
  assert (Hq_diff := @q_diff_2 k).
  assert (Hq_prime := @q_prime k).
  assert (Hq_ge_2 := prime_ge_2 _ Hq_prime).
  assert (Hdistinct := @distinct k).
  change 4 with (2 * 2).
  split;[ split; [omega | ] | ].
  assert (2 * 2 <= p k * q k).
  apply Zmult_le_compat; omega.
  assert (2 * 2 <> p k * q k).
  intro Heq.
  apply Zdivide_intro in Heq.
  apply prime_mult in Heq; trivial.
  destruct Heq;
  apply prime_div_prime in H0; trivial; try omega; apply prime_2.
  omega.
  apply rel_prime_mult; apply rel_prime_sym ;apply rel_prime_mult; apply prime_rel_prime; trivial; 
    intro Heq; apply prime_div_prime in Heq; trivial; try omega; apply prime_2.
 Defined.
    
 Lemma legendre_p_4 : forall k, 
  legendre (p k) (p_gt_1 (p k) (p_prime k)) (p_prime k) 4 = 1.
 Proof.
  intro k.
  assert (4 = proj1_sig (Group2.mult _ (two_Dp k) (two_Dp k))).
  simpl.
  rewrite Zmod_small; trivial.
  generalize (lt_p_4 k); omega.
  rewrite H.
  apply <- legendre_plus_qr.
  exists (two_Dp k).
  simpl; trivial.
 Qed.

 Lemma legendre_q_4 : forall k, 
  legendre (q k) (q_gt_1 (q k) (q_prime k)) (q_prime k) 4 = 1.
 Proof.
  intro k.
  assert (4 = proj1_sig (Group2.mult _ (two_Dq k) (two_Dq k))).
  simpl.
  rewrite Zmod_small; trivial.
  generalize (lt_q_4 k); omega.
  rewrite H.
  apply <- legendre_plus_qr.
  exists (two_Dq k).
  simpl; trivial.
 Qed.
    
 Definition four : forall k, t k.
  intro k.
  refine (exist _ (four_D k) _).
  apply <- P_prop.
  unfold jacobi, Zstar.jacobi; simpl.
  rewrite legendre_p_4, legendre_q_4.
  split;[ ring | ].
  split;[ omega | ].
  generalize (lt_p_4 k); intros.
  generalize (lt_q_4 k); intros.
  replace 4 with (Zdiv2 (4 * 2)).
  apply MiscZArith.Zdiv2_le.
  apply Zmult_le_compat; omega.
  omega.
  simpl; trivial.
 Defined.

End Dn.


Module Type CHALLENGE.
 
 Parameter size : nat -> nat.
 Parameter size_poly : polynomial.
 Parameter size_poly_spec : forall k, (size k < peval size_poly k)%nat.

End CHALLENGE.


Module ClawFreeFactoring (DP:PARAMETERS) (BS:CHALLENGE) : ClawFreeParameters.
  
 Module _Dn := Dn DP.
 Import _Dn.
 Import DP.

 Definition D      := t.
 Definition PK     := D.
 Definition SK k   := (D k * D k)%type.
 Definition D_size := fun k => size_nat (length (elems k)).

 Definition D_size_poly := order_poly.

 Lemma D_size_poly_spec : forall k, (D_size k < peval D_size_poly k)%nat.
 Proof.
   exact order_size_nat. 
 Qed.
  
 Definition D_elems := elems.
 
 Lemma D_elems_not_nil k : D_elems k <> nil.
 Proof.
  exact elems_not_nil.
 Qed.

 Lemma D_elems_full k (x:D k) : In x (D_elems k).
 Proof.
  exact elems_full.
 Qed.
 
 Lemma D_elems_nodup : forall k, NoDup (D_elems k).
 Proof.
  exact elems_nodup.
 Qed.

 Definition D_default := e.
 Definition D_eqb := eqb.
 
 Lemma D_eqb_spec : forall k (x y:D k), if D_eqb x y then x = y else x <> y.
 Proof.
  exact eqb_spec.
 Qed.
  
 Definition PK_default   := D_default.
 Definition PK_eqb       := D_eqb.
 Definition PK_eqb_spec  := D_eqb_spec.
 Definition PK_size      := D_size.
 Definition PK_size_poly := D_size_poly.
 Definition PK_size_poly_spec := D_size_poly_spec.

 Definition SK_default k := (D_default k, D_default k).
 Definition SK_eqb k (x y: SK k) := 
  D_eqb (Datatypes.fst x) (Datatypes.fst y) && 
  D_eqb (Datatypes.snd x) (Datatypes.snd y).

 Lemma SK_eqb_spec : forall k (x y:SK k), if SK_eqb x y then x = y else x <> y.
 Proof.
  intros k (x1, x2) (y1, y2).
  unfold SK_eqb; simpl.
  generalize (D_eqb_spec x1 y1).
  generalize (D_eqb_spec x2 y2).
  case (D_eqb x2 y2); case (D_eqb x1 y1); intros; simpl; subst; trivial.
  contradict H0; injection H0; auto.
  contradict H; injection H; auto.
  contradict H; injection H; auto.
Qed.

Close Scope Z_scope.
 
 Definition SK_size k    := D_size k + D_size k.
 Definition SK_size_poly := pplus D_size_poly D_size_poly.

 Lemma SK_size_poly_spec : forall k : nat, SK_size k < SK_size_poly k.
 Proof.
  intros; unfold SK_size, SK_size_poly.
  rewrite pplus_spec.
  generalize (D_size_poly_spec k); intros.
  omega.
 Qed.
 
 Definition bs_size := BS.size.
 Definition bs_size_poly := BS.size_poly.
 Definition bs_size_poly_spec := BS.size_poly_spec.

 Definition f0 k (pk:PK k) (x:D k) : D k := sqr x.
 Definition f1 k (pk:PK k) (x:D k) : D k := mul (@four k) (sqr x).

 Definition f0inv k (sk:SK k) (x:D k) : D k := sqrt x.
 Definition f1inv k (sk:SK k) (x:D k) : D k := sqrt (div x (four k)).

 Definition cost_f0 k (pk:PK k) (x:D k) := cost_mul x x.
 Definition cost_f1 k (pk:PK k) (x:D k) := cost_mul x x + cost_mul (four k) (mul x x).

 Definition cost_f0inv k (sk:SK k) (x:D k) := cost_sqrt x.
 Definition cost_f1inv k (sk:SK k) (x:D k) := cost_sqrt (div x (four k)) + cost_inv (four k) + cost_mul x (inv (four k)).

 Definition cost_f0_poly    := cost_mul_poly.
 Definition cost_f1_poly    := pplus cost_mul_poly cost_mul_poly.
 Definition cost_f0inv_poly := cost_sqrt_poly.
 Definition cost_f1inv_poly := 
  pplus (pplus cost_sqrt_poly cost_inv_poly) cost_mul_poly.

 Lemma cost_f0_poly_spec : forall k (pk:PK k) (x:D k),
  cost_f0 pk x <= peval cost_f0_poly k.
 Proof.
  intros; apply cost_mul_poly_spec.
 Qed.

 Lemma cost_f1_poly_spec : forall k (pk:PK k) (x:D k),
  cost_f1 pk x <= peval cost_f1_poly k.
 Proof.
  intros; unfold cost_f1, cost_f1_poly.
  rewrite pplus_spec.
  apply plus_le_compat.
  apply cost_mul_poly_spec.
  apply cost_mul_poly_spec.
 Qed.

 Lemma cost_f0inv_poly_spec : forall k (sk:SK k) (x:D k),
  cost_f0inv sk x <= peval cost_f0inv_poly k.
 Proof.
  intros; apply cost_sqrt_poly_spec.
 Qed.

 Lemma cost_f1inv_poly_spec : forall k (sk:SK k) (x:D k),
  cost_f1inv sk x <= peval cost_f1inv_poly k.
 Proof.
  intros; unfold cost_f1inv, cost_f1inv_poly.
  repeat rewrite pplus_spec.
  apply plus_le_compat.
  apply plus_le_compat.
  apply cost_sqrt_poly_spec.
  apply cost_inv_poly_spec.
  apply cost_mul_poly_spec.
 Qed.

 Definition R k (pk:PK k) (sk:SK k) : Prop :=
  mul (Datatypes.fst sk) (Datatypes.snd sk) = pk.

 Lemma R_dec : forall k (pk:PK k) (sk:SK k), {R pk sk} + {~R pk sk }.
 Proof.
  intros; unfold R. 
  match goal with 
  |- sumbool (?x = ?y) _ => 
   generalize (D_eqb_spec x y); case (D_eqb x y); intro; tauto
  end.  
 Qed.
 
 Lemma f0_spec    : forall k (sk:SK k) (pk:PK k), 
  R pk sk -> forall (x:D k), f0inv sk (f0 pk x) = x.
 Proof.
  intros; unfold f0, f0inv, sqr.
  apply sqrt_mul.
 Qed.

 Lemma f0inv_spec : forall k (sk:SK k) (pk:PK k), 
  R pk sk -> forall (x:D k), f0 pk (f0inv sk x) = x.
 Proof.
  intros; unfold f0, f0inv, sqr.
  apply mul_sqrt.
 Qed.
 
 Lemma f1_spec    : forall k (sk:SK k) (pk:PK k), 
  R pk sk -> forall (x:D k), f1inv sk (f1 pk x) = x.
 Proof.
  intros; unfold f1, f1inv, div, sqr.
  rewrite (mul_comm (four k)), <- mul_assoc, (mul_comm (four k)),
   mul_inv_l, (mul_comm (mul x x)), mul_e_l, sqrt_mul; trivial.
 Qed.

 Lemma f1inv_spec : forall k (sk:SK k) (pk:PK k), 
  R pk sk -> forall (x:D k), f1 pk (f1inv sk x) = x.
 Proof.
  intros; unfold f1, f1inv, div, sqr.
  rewrite mul_sqrt, mul_assoc, (mul_comm _ x), <- mul_assoc, 
   (mul_comm (four k)), mul_inv_l, mul_comm, mul_e_l; trivial.
 Qed.

End ClawFreeFactoring.


(** Instantiation *)
Declare Module DP : PARAMETERS.
Declare Module BS : CHALLENGE.

Module CFP := ClawFreeFactoring DP BS.

Module S := ClawFree.ClawFree CFP.
