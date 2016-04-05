(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * DiffieHellman.v : An instance of the protocol for proving
 equality of preimages under two special homomorphisms, that proves
 well-formedness of Diffie-Hellman triples *)

Require Import PreimageEq.
Require Import LtIrrelevance.

Set Implicit Arguments.


(** Parameters *)
Module Type DH_PARAMETERS.

 (** A group [H] of prime order [q] with a generator [g] *)
 Declare Module H : GROUP.

 Parameter q : nat -> Z.

 Parameter q_prime : forall k, prime (q k).

 Parameter q_order : forall k, length (H.elems k) = Zabs_nat (q k).

 Parameter g : forall k, H.t k.

 Parameter g_gen : forall k (x:H.t k), exists a, x = H.pow (g k) a.

 Parameter g_order : forall k, H.pow (g k) (Zabs_nat (q k)) = H.e k.
 
 (** The exponent of the second component of the DH triple *)
 Parameter b : nat -> nat. 

End DH_PARAMETERS.


(** The homomorphism, obtained as a composition of homomorphisms
   [phi_1 : Zq -> H, phi_1(x) = g^x] and
   [phi_2 : Zq -> H, phi_2(x) = g^(x.b)]
*)
Module DH_Homomorphism (DHP:DH_PARAMETERS).

 Import DHP.
 
 Lemma q_pos : forall k, 0 < Zabs_nat (q k).
 Proof.
  intro k.
  assert (H:=prime_ge_2 _ (q_prime k)).
  change 0 with (Zabs_nat 0).  
  apply Zabs_nat_lt.
  auto with zarith.
 Qed.

 
 (** The Zq group *)
 Module Zq <: GROUP.

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
   assert (0 < Zabs_nat (q k)).
   change 0%nat with (Zabs_nat 0).  
   apply Zabs_nat_lt.
   generalize (prime_ge_2 _ (q_prime k)).
   auto with zarith.
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
   intros k (n,Hn) (m,Hm).
   unfold eqb.
   generalize (nat_eqb_spec n m); case (nat_eqb n m); intro Heq.
   subst; rewrite (lt_eq Hm Hn); trivial.
   intro H; elim Heq; injection H; trivial. 
  Qed.

  (** Identity element *)
  Definition e k : t k := exist _ 0 (q_pos k).

  (** Operations: product, inverse *)
  Definition mul : forall k, t k -> t k -> t k. 
   intros k (n,Hn) (m,Hm).
   case (le_gt_dec (Zabs_nat (q k)) (n + m)); intro Hlt.  
   exists (n + m - (Zabs_nat (q k))); auto with *.
   exists (n + m); exact Hlt.
  Defined.  

  Definition inv : forall k, t k -> t k.
   intros k (n,Hn).
   case (eq_nat_dec n 0); intro Heq.
   exists 0; apply q_pos.  
   exists (Zabs_nat (q k) - n); auto with *.
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
   intros k (n,Hn) (m,Hm) (p,Hp); unfold mul.  
   prove_mul_eq.
  Qed.

  Lemma mul_e_l : forall k (x:t k), mul (e k) x = x.
  Proof.
   intros k (n,Hn); unfold e, mul.
   prove_mul_eq.
  Qed.

  Lemma mul_inv_l : forall k (x:t k), mul (inv x) x = e k.
  Proof.
   intros k (n,Hn); unfold e, mul, inv.
   case (eq_nat_dec n 0); intro; subst; prove_mul_eq.
  Qed.

  Lemma mul_comm : forall k (x y:t k), mul x y = mul y x.
  Proof.
   intros k (n,Hn) (m,Hm); unfold mul.
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
  Definition order_poly : polynomial := H.order_poly.

  Lemma order_size_nat : forall k,
   size_nat (length (elems k)) < peval order_poly k.
  Proof.
   intro k.
   replace (length (elems k)) with (Zabs_nat (q k)).
   rewrite <- q_order.
   apply H.order_size_nat.
   unfold elems; induction (Zabs_nat (q k)).
   trivial.  
   rewrite IHn at 1.
   simpl; unfold elems_aux; rewrite map_length; trivial.  
  Qed.

  Definition cost_mul k (x y:t k) : nat := size_nat (proj1_sig y).

  Definition cost_pow k (x:t k) (n:Z) : nat :=
   size_nat (proj1_sig x) * (size_Z (q k)).

  Definition cost_inv k (x:t k) : nat := size_nat (proj1_sig x).

  Definition cost_mul_poly : polynomial := H.order_poly. 
  Definition cost_pow_poly : polynomial := pmult H.order_poly H.order_poly.
  Definition cost_inv_poly : polynomial := H.order_poly.

  Lemma cost_mul_poly_spec : forall k (x y:t k),
   cost_mul x y <= peval cost_mul_poly k.
  Proof.
   intros k x (n,Hn).
   unfold cost_mul; simpl.
   apply le_trans with (size_Z (q k)).
   apply size_nat_monotonic; apply lt_le_weak; trivial.
   unfold size_Z.
   rewrite <- q_order.
   apply le_Sn_le.
   apply H.order_size_nat. 
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
   unfold size_Z; rewrite <- q_order.
   apply le_Sn_le; apply H.order_size_nat.
   unfold size_Z; rewrite <- q_order. 
   apply le_Sn_le; apply H.order_size_nat.
  Qed.

  Lemma cost_inv_poly_spec : forall k (x:t k),
   cost_inv x <= peval cost_inv_poly k.
  Proof.
   intros k (a,Ha).
   unfold cost_inv; simpl.
   apply le_trans with (size_Z (q k)).
   apply size_nat_monotonic; apply lt_le_weak; trivial.
   unfold size_Z; rewrite <- q_order. 
   apply le_Sn_le; apply H.order_size_nat.
  Qed.

 End Zq.


 Module HP := Group_Properties H.
 Import HP.


 Module HM1 <: HOMOMORPHISM Zq H.

  Open Scope nat_scope.
 
  Definition phi k (x:Zq.t k) : H.t k :=
   match x with
    exist a _ => H.pow (g k) a
   end.

  Definition cost_phi k (x:Zq.t k) :=
   match x with
    | exist a _ => H.cost_pow (g k) (Z_of_nat a)
   end.

  Definition cost_phi_poly : polynomial := H.cost_pow_poly.

  Lemma cost_phi_poly_spec : forall k (x:Zq.t k),
   cost_phi x <= peval cost_phi_poly k.
  Proof.
   intros k (a,Ha); apply H.cost_pow_poly_spec.
  Qed.

  Lemma phi_homo : forall k (x y:Zq.t k), 
   phi (Zq.mul x y) = H.mul (phi x) (phi y).
  Proof.
   intros k (n,Hn) (m,Hm); unfold phi; simpl.
   rewrite HP.mul_pow_plus.
   case (le_gt_dec (Zabs_nat (q k)) (n + m)).
   intros.
   assert (H:n + m = n + m - Zabs_nat (q k) + Zabs_nat (q k)) by omega. 
   rewrite H at 2.
   rewrite <- HP.mul_pow_plus, g_order, mul_e_r; trivial.
   trivial.
  Qed.

  (* [phi] is a special homomorphism *)
  Definition special_v k := q k.

  Lemma special_v_spec : forall k, special_v k <> 0%Z.
  Proof.
   intro k; unfold special_v.
   generalize (prime_ge_2 _ (q_prime k)).
   auto with zarith.
  Qed.

  Definition special_v_poly : polynomial := H.order_poly.

  Lemma size_nat_special_v : forall k, 
   size_nat (Zabs_nat (special_v k)) <= peval special_v_poly k. 
  Proof.
   intro k; unfold special_v.
   apply lt_le_weak.
   rewrite <- q_order. 
   apply H.order_size_nat.
  Qed.

  Definition cost_special_v (k:nat) := 1.

  Definition cost_special_v_poly : polynomial := 1.

  Lemma cost_special_v_poly_spec : forall k, 
   cost_special_v k <= peval cost_special_v_poly k. 
  Proof.
   intro k; unfold cost_special_v_poly; rewrite pcst_spec; trivial.
  Qed.

  Definition special_u k (x:H.t k) : Zq.t k := Zq.e k.

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
   replace (q k) with (Z_of_nat (Zabs_nat (q k))).
   rewrite HP.powZ_pow.
   destruct (g_gen y) as [a Heq]; rewrite Heq.
   rewrite HP.pow_pow, mult_comm, <- HP.pow_pow.
   rewrite g_order, pow_e; trivial.
   rewrite inj_Zabs_nat, Zabs_eq; trivial.
   generalize (prime_ge_2 _ (q_prime k)).
   auto with zarith.
  Qed.

 End HM1.


 Module HM2 <: HOMOMORPHISM Zq H.

  Open Scope nat_scope.
 
  Definition phi k (x:Zq.t k) : H.t k :=
   match x with
    exist a _ => H.pow (g k) (a * b k)
   end.

  Definition cost_phi k (x:Zq.t k) :=
   match x with
    | exist a _ => H.cost_pow (g k) (Z_of_nat (a * b k))
   end.

  Definition cost_phi_poly : polynomial := H.cost_pow_poly.

  Lemma cost_phi_poly_spec : forall k (x:Zq.t k),
   cost_phi x <= peval cost_phi_poly k.
  Proof.
   intros k (a,Ha); apply H.cost_pow_poly_spec.
  Qed.
  
  Lemma phi_homo : forall k (x y:Zq.t k), 
   phi (Zq.mul x y) = H.mul (phi x) (phi y).
  Proof.
   intros k (a,Ha) (c,Hc); unfold phi; simpl.
   rewrite HP.mul_pow_plus.
   case (le_gt_dec (Zabs_nat (q k)) (a + c)).
   intros.
   replace (a * (b k) + c * (b k)) with
    ((a + c) * (b k) - Zabs_nat (q k) * (b k) + Zabs_nat (q k) * (b k)).
   rewrite mult_minus_distr_r.
   rewrite <- HP.mul_pow_plus, <- pow_pow, g_order, pow_e, mul_e_r; trivial.
   rewrite plus_comm.
   rewrite le_plus_minus_r; [ring | ].
   apply mult_le_compat_r; omega.

   rewrite mult_plus_distr_r; trivial.
  Qed.


  (* [phi] is a special homomorphism *)
  Definition special_v k := q k.

  Lemma special_v_spec : forall k, special_v k <> 0%Z.
  Proof.
   intro k; unfold special_v.
   generalize (prime_ge_2 _ (q_prime k)).
   auto with zarith.
  Qed.

  Definition special_v_poly : polynomial := H.order_poly.

  Lemma size_nat_special_v : forall k, 
   size_nat (Zabs_nat (special_v k)) <= peval special_v_poly k. 
  Proof.
   intro k; unfold special_v.
   apply lt_le_weak.
   rewrite <- q_order. 
   apply H.order_size_nat.
  Qed.

  Definition cost_special_v (k:nat) := 1.

  Definition cost_special_v_poly : polynomial := 1.

  Lemma cost_special_v_poly_spec : forall k, 
   cost_special_v k <= peval cost_special_v_poly k. 
  Proof.
   intro k; unfold cost_special_v_poly; rewrite pcst_spec; trivial.
  Qed.

  Definition special_u k (x:H.t k) : Zq.t k := Zq.e k.

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
   replace (q k) with (Z_of_nat (Zabs_nat (q k))).
   rewrite HP.powZ_pow.
   destruct (g_gen y) as [a Heq]; rewrite Heq.

   rewrite HP.pow_pow, mult_comm, <- HP.pow_pow.
   rewrite g_order, pow_e; trivial.
   rewrite inj_Zabs_nat, Zabs_eq; trivial.
   generalize (prime_ge_2 _ (q_prime k)).
   auto with zarith.
  Qed.

 End HM2.


 Module EPC_DH : EP_CONSTRAINTS Zq H H HM1 HM2.
 
  Lemma special_u_same : forall k (x1 x2:H.t k), 
   HM1.special_u x1 = HM2.special_u x2.
  Proof.
   trivial.
  Qed.
 
  Lemma special_v_same : HM1.special_v = HM2.special_v.
  Proof.
   trivial.
  Qed.

 End EPC_DH.


 Module HM := EP_Homomorphism Zq H H HM1 HM2 EPC_DH.

End DH_Homomorphism.


(** Instantiation with a challenge set of maximal size *)
Declare Module DHP : DH_PARAMETERS.

Module DHH := DH_Homomorphism DHP.
 
Module CS := Largest_Challenge_Set DHH.Zq DHH.HM.H DHH.HM.

Module S := SigmaPhi.SigmaPhi DHH.Zq DHH.HM.H DHH.HM CS.
