(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

Require Import SMain.
Require Import Field_tac.
Require Import Program.
Require Import EGroup.
Require Import FGroup.
Require Import UList.
Require Import Arith.
Require Import Znumtheory.
Require Import ZAux.
Require Import FilterMap.
Require Import Znumtheory.
Require Import SMain.
Require Import Ring.
Require Import PrimeLib.
Require Import Padding.
Require Import EC.
Require Import EncodingAux.
Require Import RO.

Set Implicit Arguments.

Module Type SOLVE_DEGREE_4 (A : FIELD).
 
 Parameter solve_degree_4 : forall k (a b c d e : A.t k), list (A.t k).
 
 Notation "x + y" := (A.kplus x y).
 Notation "x * y" := (A.kmul x y). 
 
 Parameter solve_degree_4_correct : forall k (a b c d e sol : A.t k), 
  In sol (solve_degree_4 a b c d e) <-> 
  (fun x => a * x*x*x*x + b * x*x*x + c * x*x + d * x + e) sol = A.kO k.
 
 Parameter solve_degree_4_size : forall k (a b c d e : A.t k), 
  (length (solve_degree_4 a b c d e) <= 4)%nat.

 Parameter solve_degree_4_NoDup : forall k (a b c d e : A.t k),
  NoDup (solve_degree_4 a b c d e).

End SOLVE_DEGREE_4.

Declare Module F : FIELD 
 with Definition order_mod1 := fun (_:nat) => 3%Z
 with Definition order_mod2 := fun (_:nat) => 2%Z.
 
Declare Module CP : CURVE_PROPERTIES F.

Declare Module S4 : SOLVE_DEGREE_4 F.

Module EC_GROUP <: CFG  := (EC.EC F CP).

Module PAD := Padding.Padding EC_GROUP.

Module IcartEncoding <: ENCODING F PAD.B.

 Import F CP S4.

 Section ENC.
  
  Variable k : nat.
  
  Add Field Kfield : (@K_field k) (abstract).
  
  Notation "x + y" := (kplus x y).
  Notation "x * y" := (kmul x y). 
  Notation "x - y" := (ksub x y).
  Notation "- x" := (kopp x).
  Notation "/ x" := (kinv x). 
  Notation "x / y" := (kdiv x y).
  Notation "0" := (kO k).
  Notation "1" := (kI k).
  Notation "2" := (1+1).
  Notation "3" := (1+1+1).
  Notation "4" := (2*2).
  Notation "5" := (4+1).
  Notation "6" := (2*3).
  Notation "8" := (2*2*2).
  Notation "16" := (2*2*2*2).
  Notation "20" := (4*5).
  Notation "27" := (3*3*3).
  Notation "256" := (2*2*2*2*2*2*2*2).
  
  Notation "x ^ n" := (kpow x n).
  
  Lemma kpow_S : forall (x:t k) n, x ^ (S n) = x * (x ^ n).
  Proof.
   intros; simpl; trivial.
  Qed.

  Lemma kpow_kplus : forall (x:t k) n m, ((x ^ n) * (x ^ m) = x ^ (n + m)).
  Proof.
   intros x n m.
   induction m; simpl.
   rewrite plus_0_r; field.
   rewrite <- plus_n_Sm, kpow_S, <- IHm; field.
  Qed.
    
  Lemma kpow_pow : forall x n1 n2, kpow (@kpow k x n1) n2 = kpow x (n1 * n2).
  Proof.
   intros x n1 n2.
   induction n2.
   rewrite mult_0_r; simpl; trivial.
   rewrite mult_succ_r, <- kpow_kplus; simpl.
   rewrite IHn2; field.
  Qed.
    
  Lemma kpow_kplus_n : forall (x y:t k) n, (x ^ n) * (y ^ n) = (x * y) ^ n.
  Proof.
   intros x y n.
   induction n; simpl.
   ring.
   rewrite <- IHn; ring.
  Qed.
 
  Definition sqr (x : t k) : t k := x * x.
    
  Definition cube (x : t k) : t k := x * x * x.
  
  Definition pow4 (x : t k) : t k := x * x * x * x.
  
  Lemma cube_pow (x : t k) : cube x = kpow x 3%nat.
  Proof.
   intros; unfold cube; simpl; ring.
  Qed.
  
  Lemma cube_plus a b : 
   cube (a + b) = (cube a) + 3 * a*a * b + 3 * b*b * a + (cube b).
  Proof.
   intros a b; unfold cube; ring.
  Qed.
  
  Lemma cube_minus a b : 
   cube (a - b) = (cube a) - 3 * a*a * b + 3 * b*b * a - (cube b).
  Proof.
   intros a b; unfold cube; ring.
  Qed.
        
  Definition cube_root (x : t k) : t k :=
   kpow x (Zabs_nat ((2 * (orderZ k) - 1) / 3)).
  
  Lemma order_pos : (0 < orderZ k)%Z.
  Proof.
   change 0%Z with (Z_of_nat 0).
   apply inj_lt.       
   generalize (@elems_notnil k).
   destruct (elems k); intros; simpl.
   elim H; trivial.
   omega.
  Qed.

  Lemma cube_root_spec : forall x, cube_root (cube x) = x.
  Proof.
   intros x; unfold cube_root.
   assert (Ho := order_pos).
   rewrite cube_pow, kpow_pow.
   change 3%nat with (Zabs_nat 3).
   rewrite <- Zabs_nat_mult, <- Zdivide_Zdiv_eq;[ | omega | ].
   cutrewrite (2 * orderZ k - 1 = 1 + (orderZ k - 1) + (orderZ k - 1))%Z;[ | ring].
   repeat rewrite Zabs_nat_Zplus; try omega.
   repeat rewrite <- kpow_kplus; simpl.
   cutrewrite (Zabs_nat (orderZ k - 1) = (order k - 1)%nat ).
   repeat rewrite fermat; ring.
   rewrite Zabs_nat_Zminus.
   unfold orderZ; rewrite Zabs_nat_Z_of_nat; auto.
   omega.
   apply Zmod_divide; [ omega | ].
   rewrite <- Zminus_mod_idemp_l, Zmult_comm, <- Zmult_mod_idemp_l, order_mod.
   vm_compute; trivial.
  Qed.

  Lemma cube_spec : forall x, cube (cube_root x) = x.
  Proof.
   intros x; unfold cube_root.
   rewrite cube_pow, kpow_pow, mult_comm, <- kpow_pow, <- cube_pow.  
   apply cube_root_spec.
  Qed.

  Lemma cube_root_mul x y : cube_root x * cube_root y = cube_root (x * y).
  Proof.
   intros x y; unfold cube_root.
   rewrite kpow_kplus_n; trivial.
  Qed. 
    
  Lemma diff_opp_0 x : x <> 0 -> -x <> 0.
  Proof.
   intros x H1 Heq.
   apply H1.
   apply (f_equal (fun x => kopp x)) in Heq.
   cutrewrite (- - x = x) in Heq; [ | ring ].
   ring [Heq].
  Qed.
    
  Lemma mult_inj x y z : z <> 0 ->  x * z = y * z -> x = y.
  Proof.
   intros x y z Hz H.
   apply (f_equal (fun x => x / z)) in H.
   cutrewrite (x = x * z / z).
   rewrite H.
   field; trivial.
   field; trivial.
  Qed.
  
  Lemma diff_1_0 : 1 <> 0.
  Proof.
   generalize (K_field k); intros.
   inversion H; trivial.
  Qed.
  
  Lemma diff_1_2_0 : 1 + 2 <> 0.
  Proof.
   cutrewrite (1 + 2 = 3).
   apply diff_3_0.
   ring.
  Qed.
    
  Lemma diff_3_0' : 1 + 1 + 1 <> 0.
  Proof.
   apply diff_3_0.
  Qed.
  
  Lemma diff_4_0 : 4 <> 0.
  Proof.
   apply diff_mul_0; apply diff_2_0.  
  Qed.
  
  Lemma diff_6_0 : 2 * (1 + 2) <> 0.
  Proof.
   apply diff_mul_0.
   apply diff_2_0.
   apply diff_1_2_0.
  Qed.
  
  Lemma diff_8_0 : 8 <> 0.
  Proof.
   apply diff_mul_0.
   apply diff_4_0.
   apply diff_2_0.
  Qed.
  
  Lemma diff_27_0 : 1 + 2 * (1 + 2 * (2 * (1 + 2))) <> 0.
  Proof.
   cutrewrite (1 + 2 * (1 + 2 * (2 * (1 + 2))) = 3 * 3 * 3).
   apply diff_mul_0.
   apply diff_mul_0.
   apply diff_3_0.
   apply diff_3_0.
   apply diff_3_0.
   ring.
  Qed.
    
  Hint Resolve diff_1_2_0 diff_1_0 diff_2_0 diff_3_0 diff_3_0' 
   diff_4_0 diff_6_0 diff_27_0 diff_8_0 diff_opp_0.

  Lemma is_zero_eq_false : forall x, is_zero x = false <-> x <> 0.
  Proof.
   generalize (EC_GROUP.ECB.Eth k); intros.
   inversion H; trivial.
   split; intro He.
   intro Heq.
   apply is_zero_correct in Heq.
   rewrite He in Heq; discriminate.
   apply not_true_is_false.
   intro Heq.
   apply is_zero_correct in Heq.
   subst.
   elim He; trivial.
  Qed.
  
  Lemma mult_sqr (x y : t k) : x = y \/ x = -y -> x * x = y * y.
  Proof.
   intros x y [H | H]; subst; ring.
  Qed.
  
  Lemma eqb_dec : forall (x y : F.t k), {x = y} + {x <> y}.
  Proof.
   intros.
   generalize (eqb_spec x y).
   case (eqb x y); auto.
  Qed.
    
  Definition f_def : F.t k -> PAD.B.t k.
   intro u.
  
   destruct (eqb_dec u 0).

   destruct (eqb_dec (A k) 0).

   pose (x := cube_root (- B k )).

   (* if A = 0 then f(0) = ( (-b)^(1/3), 0). cf (mail with Thomas Icart) *)
   refine (curve_elt (kI k) (@kplus k) (@kmul k) (A k) (B k) x 0 _).
   symmetry; unfold SMain.pow.
   rewrite e0.
   ring_simplify.
   cutrewrite (x * x * x = cube x); auto.
   unfold x.
   rewrite cube_spec.
   ring.
   
   (* A <> 0 (Icart's paper)  *)
   exact (PAD.B.default k).
    
   pose (v := kdiv ((3 * A k) - (u*u*u*u)) (6 * u)).
   pose (x := cube_root ((v * v) - B k - ((u ^ 6) / 27)) + ( (u^2) / 3)).
   pose (y := (u * x) + v).    
   refine (curve_elt (kI k) (@kplus k) (@kmul k) (A k) (B k) x y _).
   symmetry; unfold SMain.pow.
   ring_simplify.    
   assert (x = cube_root (v * v - B k - u ^ 6 / 27) + u ^ 2 / 3) by trivial.    
   apply (f_equal cube) in H.
   assert (cube (x - ((u*u) / 3)) = (v*v) - B k - (u^6)/27).
   rewrite cube_minus, H, cube_plus, cube_spec; clear H; unfold x.
   generalize (v * v - B k - u ^ 6 / 27); intro.
   rewrite <- (cube_spec t0) at 1 8; unfold cube.
   cutrewrite (u ^ 2 = u * u); [ | unfold kpow]; ring.    
   assert (cube x = u * u * x * x - ((u * u * u * u) / 3) * x + (- B k + v * v)).
   cutrewrite <- (cube (x - u * u / 3) + u ^ 6 / 27  = - B k + v * v);
    [ | ring [H0] ].
   rewrite cube_minus; set (n1 := 1); unfold kpow, cube; field; auto.    
   cutrewrite (u * u * u * u / 3 = A k - 2 * u * v) in H1.
   unfold y; unfold cube in H1; ring [H1].
   unfold v; set (n1 := 1); field.    
   split;[  | split ]; auto.
   apply diff_2_0.
  Defined.  

  Lemma Feqb : forall a b : t k, {a = b} + {a <> b}.
  Proof.
   intros.
   generalize (eqb_spec a b).
   case (eqb a b); intros; auto.
  Qed. 
  
  Lemma Geqb : forall a b : PAD.B.t k, {a = b} + {a <> b}.
  Proof.
   intros.
   generalize (PAD.B.eqb_spec _ a b).
   case (PAD.B.eqb _ a b); intros; auto.
  Qed. 
  
  Definition Im_f := nodup Geqb (map f_def (elems k)).
  
  Lemma NoDup_Im_f : NoDup Im_f.
  Proof.
   apply Nodup_nodup.
  Qed.
  
  Definition finv_def : (PAD.B.t k) -> list (F.t k).
   intros p.
  
   destruct p.
   destruct (eqb_dec (A k) 0).
   exact nil.
   exact [0].
   
   destruct (eqb_dec (A k) 0).
   refine (solve_degree_4 0 1 0 (- x * 6) (6 * y)). (* cf. Icart's suggestion *)
   refine (solve_degree_4 1 0 (- x * 6) (6 * y) (- A k * 3)).
  Defined.
 
  Definition finv_len : nat := 4%nat.
  
  Parameter cost_f : F.t k -> nat.
  
  Parameter cost_f_poly : polynomial.
  
  Parameter cost_f_poly_spec : forall (x:F.t k),
   (cost_f x <= peval cost_f_poly k)%nat.
  
  Parameter cost_finv : PAD.B.t k -> nat.
  
  Parameter cost_finv_poly : polynomial.
  
  Parameter cost_finv_poly_spec : forall (x:PAD.B.t k),
   (cost_finv x <= peval cost_finv_poly k)%nat.
  
  Definition finv_len_poly := pcst 4.
  
  Lemma finv_len_poly_spec : finv_len <= finv_len_poly k.
  Proof.
   unfold finv_len, finv_len_poly.
   rewrite pcst_spec; auto.
  Qed.
  
  Ltac elim_if :=
   match goal with
    |- context [if ?a then ?b else ?c] => case_eq a; intros
   end.
  
  Lemma finv_len_spec : forall x, length (finv_def x) <= finv_len.
  Proof.
   unfold finv_def, finv_len; intros.
   destruct x; repeat elim_if; simpl; auto;
    apply solve_degree_4_size.
  Qed.

  Lemma finv_len_not_0 : 0 < finv_len.
  Proof.
   unfold finv_len; auto.
  Qed.

 End ENC.

End IcartEncoding.

Require Import ssreflect.

Module Icart_PI <: POLYNOMIALLY_INVERTIBLE_ENCODING F PAD.B IcartEncoding.
 
 Import IcartEncoding CP F.

 Section PI.

  Variable k : nat.

  Add Field Kfield : (@K_field k) (abstract).
  
  Notation "x + y" := (kplus x y).
  Notation "x * y" := (kmul x y). 
  Notation "x - y" := (ksub x y).
  Notation "- x" := (kopp x).
  Notation "/ x" := (kinv x). 
  Notation "x / y" := (kdiv x y).
  Notation "0" := (kO k).
  Notation "1" := (kI k).
  Notation "2" := (1+1).
  Notation "3" := (1+1+1).
  Notation "4" := (2*2).
  Notation "5" := (4+1).
  Notation "6" := (2*3).
  Notation "8" := (2*2*2).
  Notation "16" := (2*2*2*2).
  Notation "20" := (4*5).
  Notation "27" := (3*3*3).
  Notation "256" := (2*2*2*2*2*2*2*2).
  
  Notation "x ^ n" := (kpow x n).
  
  Lemma finv_NoDup : forall (x:PAD.B.t k), NoDup (finv_def x).
  Proof.
   intros; unfold finv_def.
   destruct x.
   destruct (eqb_dec (CP.A k) (F.kO k)); auto.
   destruct (eqb_dec (CP.A k) (F.kO k));
    apply S4.solve_degree_4_NoDup.
  Qed.

  Hint Resolve diff_1_2_0 diff_1_0 diff_2_0 diff_3_0 diff_3_0' 
   diff_4_0 diff_6_0 diff_27_0 diff_8_0 diff_opp_0.

  Lemma finv_spec1 : forall (g : PAD.B.t k) (u : F.t k),
   In u (finv_def g) -> f_def u = g.
  Proof.
   intros g u; unfold finv_def, f_def.
   (* case_eq ( p_in g Im_f ); intros Hpin. *)
   destruct g; simpl; intros.
   (** inf *)
   destruct (eqb_dec (A k) 0); simpl in *.
   elim H.
   destruct H.
   subst.
   destruct (eqb_dec 0 0); intros.
   auto.
   elim n0; trivial.
   elim H.


   (** (x,y) *)
   unfold SMain.pow in e.
   destruct (eqb_dec (A k) 0).
   (*** A = 0 *)
   apply S4.solve_degree_4_correct in H.
   destruct (eqb_dec u 0); intros.
   (**** u = 0 *)
   rewrite e1 in H.
   ring_simplify in H.
   assert (y = 0).
   rewrite e0 in e.
   cutrewrite (2 * (1 + 2) * y = y * (2 * (1 + 2))) in H;[ | ring ].
   cutrewrite (0 = 0 * (2 * (1 + 2))) in H.
   apply mult_inj in H; auto.
   ring.
   apply (curve_elt_irr (EC_GROUP.ECB.Eth k)).
   rewrite H0 e0 in e.
   cutrewrite (- B k = x * x * x).
   apply cube_root_spec.
   cutrewrite (x * x * x = - (0 * 0) + x * x * x);[ | ring].
   rewrite e; ring.
   auto.

   (**** u <> 0 *)
   ring_simplify in H.
   assert (u * u * u - x * 6 * u + 6 * y = 0).
   rewrite <- H; ring.
   clear H.
 
   assert (u * u * u / 6 = x * u - y).
   cutrewrite (u * u * u = u * u * u - 0);[ | ring ].
   rewrite <- H0; field; auto.

   assert (B k = y * y - x * x * x).
   rewrite e e0; ring.
  
   pose (v := - (u * u * u / 6)).
   assert (y = u * x + v).
   unfold v.
   rewrite H.
   ring.

   assert (v * v - B k - u ^ 6 / 27 = cube (x - u * u / 3)).
   cutrewrite <- (u * u * x * x + 2 * u * v * x + v * v = y * y) in e.
   rewrite e0 in e.
   ring_simplify in e.
   
   assert ((x * x * x + B k) - u * u * x * x  - 2 * u * v * x - v * v = 0).
   rewrite <- e; ring.
   clear e.
 
   assert (x * x * x - u * u * x * x + (- (2 * u * v)) * x + B k - v * v = 0).
   rewrite <- H3; ring.
   clear H3.

   rewrite cube_minus.
   assert (  v * v - B k = cube x - 3 * x * x * (u * u / 3) + 3 * (u * u / 3) * (u * u / 3) * x ).
   cutrewrite (v * v = v * v + 0);[ | ring ].
   rewrite <- H4.
   unfold v.
   ring_simplify.
   unfold cube; field; auto.
   rewrite H3.
   unfold cube.
   simpl; field; auto.
   rewrite H2; ring.
   
   simpl in H3.

   assert ( cube_root
     ((3 * 0 - u * u * u * u) / (6 * u) * ((3 * 0 - u * u * u * u) / (6 * u)) -
      B k - u * (u * (u * (u * (u * (u * 1))))) / 27) = x - u * (u * 1) / 3).
   apply (f_equal (@cube_root k)) in H3.
   rewrite cube_root_spec in H3.
   cutrewrite ( x - u * (u * 1) / 3 = x - u * u / 3 );[ | field; auto ].
   rewrite <- H3.
   f_equal.
   unfold v; field; auto.

   apply (curve_elt_irr (EC_GROUP.ECB.Eth k)).
   rewrite e0 H4.
   field; auto.
   rewrite e0 H4 H2.
   unfold v.
   field; auto.

   (*** A <> 0 *)
   apply S4.solve_degree_4_correct in H.
   destruct (eqb_dec u 0); intros.
   (**** u = 0 *)
   rewrite e0 in H.
   ring_simplify in H.
   cutrewrite (0 = 0 * (A k)) in H.
   apply mult_inj in H; trivial.
   assert (- (1 + 2) <> 0).
   apply diff_opp_0; auto.
   elim H0; trivial.
   ring.
   (**** u <> 0 *)
   ring_simplify in H.
   assert (u * u * u * u - x * 6 * u * u + 6 * y * u - A k * 3 = 0).
   rewrite <- H; ring.
   clear H.
   pose (v := kdiv ((3 * A k ) - (u * u * u * u)) (6 * u)).
   assert (y = u * x + v).
   unfold v.
   assert (3 * A k = u * u * u * u - x * 6 * u * u + 6 * y * u).
   cutrewrite (3 * A k = 3 * A k + 0);[ | ring ].
   rewrite <- H0; field.
   rewrite H; field.
   split; auto.
   assert (v * v - B k - u ^ 6 / 27 = cube (x - u * u / 3)).
   generalize e; intro He.
   cutrewrite <- (u * u * x * x + 2 * u * v * x + v * v = y * y) in He.
   assert ((x*(x*x) + A k * x + B k) - u * u * x * x  - 2 * u * v * x - v * v = 0).
   rewrite <- He; ring.
   clear He.
   assert (x * x * x - u * u * x * x + (A k - 2 * u * v) * x + B k - v * v = 0).
   rewrite <- H1; ring.
   clear H1.
   cutrewrite (A k - 2 * u * v = u * u * u * u / 3) in H2.
   cutrewrite (v * v = v * v + 0);[ | ring ].
   rewrite <- H2.
   unfold cube; simpl; field; auto.
   unfold v; field; auto.
   rewrite H; field.
   simpl in H1.
   apply (curve_elt_irr (EC_GROUP.ECB.Eth k)).
   fold v.
   rewrite H1 cube_root_spec.
   simpl; field; auto.
   fold v.
   rewrite H1 cube_root_spec.
   rewrite H.
   simpl; field; auto.
  Qed.

  Lemma finv_spec2 : forall (g : PAD.B.t k) (u : F.t k),
   f_def u = g -> In u (finv_def g).
  Proof.
   intros g u; unfold finv_def, f_def; intros.
   destruct (eqb_dec u 0); destruct (eqb_dec (A k) 0); 
    destruct g; try discriminate.
   apply S4.solve_degree_4_correct.
   injection H; intros; subst; ring.
   subst; simpl; auto.
   apply S4.solve_degree_4_correct.
   injection H; intros; subst; clear H.
   rewrite e; field; auto.
   injection H; intros; subst; clear H.
   apply S4.solve_degree_4_correct.
   field; auto.
  Qed.
  
  Lemma finv_spec : forall (g : PAD.B.t k) (u : F.t k),
   In u (finv_def g) <-> f_def u = g.
  Proof.
   intros; split.
   apply finv_spec1.
   apply finv_spec2.
  Qed.
   
  Lemma finv_len_group : (length (F.elems k) <= length (PAD.B.elems k) * finv_len).
  Proof.
   apply le_trans with 
    (length (nodup (@Geqb k) (map (@f_def k) (elems k))) * finv_len)%nat.
   apply length_surj_mult with (finv := @finv_def k).
   intros; apply finv_spec.
   intros; apply finv_len_spec.
   apply elems_NoDup.
   apply mult_le_compat_r.
   apply le_trans with (length (PAD.B.elems k)).
   apply length_surj.
   apply Nodup_nodup.
   red; intros.
   apply PAD.B.elems_full.
   auto.
  Qed.

 End PI.

End Icart_PI.

