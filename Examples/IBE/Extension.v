(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * Extension.v : Semantics with bitstrings and a bilinear map between 
   two groups of prime order. *)

Require Export BuildTac.
Require Export PPT.
Require Export Bitstrings.
Require Export PrimeLib.
Require Import Arith.Euclid.

Set Implicit Arguments.
Unset Strict Implicit.


Module Type GROUP.

 Parameter t : nat -> Type.

 (** Equality is decidable *)
 Parameter eqb : forall k, t k -> t k -> bool.
 Parameter eqb_spec : forall k (x y:t k), if eqb x y then x = y else x <> y.

 (** Identity element *)
 Parameter e : forall k, t k.

 (** Group operations: inverse, product *)
 Parameter inv : forall k, t k -> t k.
 Parameter mul : forall k, t k -> t k -> t k.

 Fixpoint pow k (x:t k) n : t k :=
  match n with
  | O => e k
  | S n => mul x (pow x n)
  end.
 
 (** Specification *) 
 Parameter mul_assoc : forall k (x y z:t k), mul x (mul y z) = mul (mul x y) z.
 Parameter mul_inv_l : forall k (x:t k), mul (inv x) x = e k.
 Parameter mul_inv_r : forall k (x:t k), mul x (inv x) = e k.
 Parameter mul_e_l : forall k (x:t k), mul (e k) x = x.
 Parameter mul_e_r : forall k (x:t k), mul x (e k) = x.

 Parameter cost_mul : forall k (x y:t k), nat.
 Parameter cost_inv : forall k (x:t k), nat.
 Parameter cost_pow : forall k (x:t k) (n:nat), nat.

 Parameter cost_mul_poly : polynomial.
 Parameter cost_inv_poly : polynomial.
 Parameter cost_pow_poly : polynomial.

 Parameter cost_mul_poly_spec : forall k (x y:t k),
  cost_mul x y <= cost_mul_poly k.
 Parameter cost_inv_poly_spec : forall k (x:t k),
  cost_inv x <= cost_inv_poly k.
 Parameter cost_pow_poly_spec : forall k (x:t k) (n:nat),
  cost_pow x n <= cost_pow_poly k.

 Lemma mul_cancel_l : forall k (x y z:t k),
  mul x y = mul x z -> y = z.
 Proof.
  intros k x y z H.
  generalize (f_equal (mul (inv x)) H).
  repeat rewrite mul_assoc, mul_inv_l, mul_e_l; trivial.
 Qed.

 Lemma mul_cancel_r : forall k (x y z:t k),
  mul x z = mul y z -> x = y.
 Proof.
  intros k x y z H.
  generalize (f_equal (fun x => mul x (inv z)) H).
  repeat rewrite <- mul_assoc, mul_inv_r, mul_e_r; trivial.
 Qed.

 Lemma inv_inv : forall k (x:t k),
  inv (inv x) = x.
 Proof.
  intros k x.
  apply mul_cancel_l with (inv x).
  rewrite mul_inv_r, mul_inv_l; trivial.
 Qed.

 Lemma inv_unique_l : forall k (x y:t k),
  mul x y = e k ->
  x = inv y.
 Proof.
  intros.  
  apply mul_cancel_r with y.
  rewrite H, mul_inv_l; trivial.
 Qed.

 Lemma inv_unique_r : forall k (x y:t k),
  mul x y = e k ->
  y = inv x.
 Proof.
  intros.  
  apply mul_cancel_l with x.
  rewrite H, mul_inv_r; trivial.
 Qed.

 Lemma inv_mul : forall k (x y:t k), inv (mul x y) = mul (inv y) (inv x).
 Proof.
  intros k x y.
  symmetry; apply inv_unique_r.
  rewrite mul_assoc, <-(mul_assoc x y), mul_inv_r, mul_e_r, mul_inv_r; trivial.
 Qed.

 Lemma eqb_refl : forall k (x:t k), eqb x x.
 Proof.
  intros k x; generalize (eqb_spec x x).
  case (eqb x x); [ | intro H; elim H]; trivial.
 Qed.

 Lemma eqb_true : forall k (x y:t k), eqb x y = true <-> x = y.
 Proof.
  intros k x y; split.
  generalize (eqb_spec x y); case (eqb x y).
  trivial.
  intros; discriminate.
  intro; rewrite H; apply eqb_refl.
 Qed.

End GROUP.


Module Type CYCLIC_GROUP.

 Include GROUP.

 (** Generator *)
 Parameter g : forall k, t k.

 (** Logarithm *)
 Parameter log: forall k, t k -> nat.
 Parameter log_spec : forall k (x:t k), x = pow (g k) (log x).
 Parameter cost_log: forall k (x:t k), nat. 


 Lemma mul_pow_plus : forall k (x:t k) n1 n2,
   mul (pow x n1) (pow x n2) = pow x (n1 + n2).
 Proof.
  induction n1; intros; simpl.
  rewrite mul_e_l; trivial.
  rewrite <- mul_assoc, IHn1; trivial.
 Qed.

 Lemma mul_comm : forall k (x y:t k), mul x y = mul y x.
 Proof.
  intros k x y.
  rewrite (log_spec x), (log_spec y).
  rewrite mul_pow_plus, mul_pow_plus, plus_comm; trivial.
 Qed.

 Lemma pow_mul : forall k n (x y:t k),
  pow (mul x y) n = mul (pow x n) (pow y n).
 Proof.
  induction n; intros; simpl.
  rewrite mul_e_r; trivial.
  rewrite IHn, mul_assoc, mul_assoc.
  cutrewrite (mul (mul x y) (pow x n) = mul (mul x (pow x n)) y); trivial.
  rewrite <- mul_assoc, <- mul_assoc, (mul_comm y); trivial.
 Qed.

 Lemma inv_pow : forall n k (x:t k), inv (pow x n) = pow (inv x) n.
 Proof.
  induction n; intros; simpl.
  symmetry; apply inv_unique_l; rewrite mul_e_l; trivial.
  rewrite inv_mul, IHn, mul_comm; trivial.
 Qed.

 Lemma pow_e : forall k n, pow (e k) n = e k.
 Proof.
  induction n; intros.
  trivial.
  simpl; rewrite IHn, mul_e_r; trivial.
 Qed.

 Lemma pow_pow : forall k (x:t k) n1 n2, pow (pow x n1) n2 = pow x (n1 * n2).
 Proof.
  induction n1; intros; simpl.
  rewrite pow_e; trivial.
  rewrite <- mul_pow_plus, <- IHn1.
  apply pow_mul.
 Qed.

End CYCLIC_GROUP.


Module Type FINITE_CYCLIC_GROUP.

 Include CYCLIC_GROUP.

 (** Order *)
 Parameter order : nat -> nat.
 Parameter order_neq_0: forall k, 0 < order k.

 Parameter log_lt : forall k (x:t k), (log x < order k)%nat.
 Parameter cyclic_inj: forall k n, 
   e k = pow (g k) n -> 
   n < order k ->
   n = 0.
 

 (** The group is finite and non-empty *)
 Definition elems k := map (pow (g k)) (seq 0 (order k)).

 Parameter elems_full : forall k (x:t k), In x (elems k).
 Parameter elems_nodup : forall k, NoDup (elems k).


 Lemma elems_not_nil : forall k, elems k <> nil.
 Proof.
  intros k H.
  assert (In (e k) nil).
  rewrite <- H; apply (elems_full (e k)).
  elim H0.
 Qed.
 
 Lemma order_positive : forall k, 0 < order k.
 Proof.
  intro k; apply neq_0_lt; intro H.
  apply (@elems_not_nil k).  
  unfold elems.
  rewrite <- H; trivial.
 Qed.

 Lemma pow_g_order : forall k,
  pow (g k) (order k) = e k.
 Proof.
  intros.
  assert (H:=elems_full (pow (g k) (order k))).
  assert (Hn:=elems_nodup k).
  unfold elems in H, Hn.
  apply in_map_iff in H.
  destruct H as [n [H0 H1] ].
  apply In_seq_le in H1.
  rewrite plus_0_r in H1.
 
  destruct (order k) as [ | m].
  exfalso; omega.
 
  destruct n.
  rewrite <- H0; trivial.

  simpl in H0.
  assert (pow (g k) n = pow (g k) m).
  apply mul_cancel_l with (g k); trivial.

  rewrite seq_S in Hn.
  rewrite map_app in Hn.
  apply NoDup_remove_2 in Hn.
  elim Hn.
  rewrite plus_0_l.
  rewrite <- H.

  rewrite app_nil_r.
  apply in_map_iff.
  exists n; split; [ trivial | ].
  apply le_In_seq; omega.
 Qed.

 Lemma pow_order : forall k (x:t k),
  pow x (order k) = e k.
 Proof.
  intros.
  assert (H:=elems_full x).
  assert (Hn:=elems_nodup k).
  unfold elems in H, Hn.
  apply in_map_iff in H.
  destruct H as [n [H0 H1] ].
  apply In_seq_le in H1.
  rewrite plus_0_r in H1.
  rewrite <- H0, pow_pow, mult_comm, <- pow_pow, pow_g_order, pow_e; trivial.
 Qed.

 Lemma pow_periodic : forall k b a (x:t k),
  pow x (a + b * order k) = pow x a.
 Proof.
  induction b; intros; simpl.
  rewrite plus_0_r; trivial.
  rewrite (plus_comm (order k)), plus_assoc.
  rewrite <- mul_pow_plus, IHb, pow_order, mul_e_r; trivial.
 Qed.

 Lemma pow_mod : forall k (x:t k) a, 
  pow x a = pow x (nmod a (order k)).
 Proof.
  intros.
  assert (Ho:=order_positive k).  
  assert (a = nmod a (order k) + 
   Zabs_nat ((Z_of_nat a) / Z_of_nat (order k))%Z * order k).
  unfold nmod; rewrite mult_comm, plus_comm.
  rewrite <- (Zabs_nat_Z_of_nat (order k)) at 1.
  rewrite <- Zabs_nat_mult, <- Zabs_nat_Zplus.
  rewrite <- Z_div_mod_eq, Zabs_nat_Z_of_nat; trivial.
  auto with zarith.
  apply Zmult_le_0_compat.
  auto with zarith.
  apply Zdiv_pos; auto with zarith.
  apply Zmod_pos; auto with zarith. 
  rewrite H at 1; apply pow_periodic.
 Qed.

 Lemma pow_inj : forall (k a b:nat),
  (a < order k)%nat ->
  (b < order k)%nat ->
  (pow (g k) a = pow (g k) b) ->
  (a = b)%nat.
 Proof.
  intros.
  destruct (gt_eq_gt_dec a b) as [ [Hab | Hab] | Hab]; [ | trivial | ].
    assert (b = a + (b - a)) by omega.
    rewrite H2, <-mul_pow_plus in H1.
    rewrite <-(mul_e_r (pow (g k) a)) in H1 at 1.
    apply mul_cancel_l in H1; apply cyclic_inj in H1.
      exfalso; omega.
      omega.
    assert (a = b + (a - b)) by omega.
    rewrite H2, <-mul_pow_plus in H1.
    rewrite <-(mul_e_r (pow (g k) b)) in H1 at 2.
    apply mul_cancel_l in H1; apply eq_sym in H1; apply cyclic_inj in H1.
      exfalso; omega.
      omega.
 Qed.
    
 Lemma log_mul: forall k (x y:t k), log (mul x y) =  (log x + log y) mod (order k).
 Proof.
  intros.
  apply pow_inj with k.
    apply log_lt.
    apply (mod_lt _ _ (order_neq_0 _)).
  rewrite <-log_spec, <-pow_mod, <-mul_pow_plus, <-log_spec, <-log_spec; trivial.
 Qed.

 Lemma log_e: forall k, log (e k) = 0.
 Proof.
  intros.
  apply pow_inj with k.
    apply log_lt.
    apply order_neq_0.
    rewrite <-log_spec; trivial.
 Qed.
    
 Lemma log_pow: forall k n (x:t k), log (pow x n) = (n * log x) mod (order k). 
 Proof.
  induction n; intros; simpl.
    rewrite mod_0_l, log_e; trivial.
    rewrite log_mul, IHn.
    rewrite mod_plus, (mod_plus (log x) (n * log x)), mod_mod; trivial.
 Qed.

 Lemma log_g: forall k, 
  1 < order k ->
  log (g k) = 1.
 Proof.
  intros.
  apply pow_inj with k.
   apply log_lt.
   assumption.
   rewrite <-log_spec; simpl; rewrite mul_e_r; trivial.
 Qed.


End  FINITE_CYCLIC_GROUP.


(** Bilinear map from [G1] onto [G2] *)
Module Type BILINEAR_MAP (G1 G2:CYCLIC_GROUP).

 Parameter bmap : forall k, G1.t k -> G1.t k -> G2.t k.

 (* Bilinearity *)
 Parameter bilinear : forall k (x1 x2:G1.t k) (a b:nat),
  bmap (G1.pow x1 a) (G1.pow x2 b) = G2.pow (bmap x1 x2) (a * b).

 (* Cost *)
 Parameter cost_bmap : polynomial.

End BILINEAR_MAP.


(** Parametrical bounds on number of queries to oracles *)
Module Type PARAMETERS.

 Declare Module G1 : FINITE_CYCLIC_GROUP.
 Declare Module G2 : FINITE_CYCLIC_GROUP.
 Declare Module BM : BILINEAR_MAP G1 G2.
 Export BM.

 Parameter q : nat -> nat.

 Parameter q_prime : forall k, prime (Z_of_nat (q k)).

 Parameter q_size_poly : polynomial.

 Parameter q_size : forall k, size_nat (q k) <= q_size_poly k.

 Parameter G1_order : G1.order = q.

 Parameter G2_order : G2.order = q.

 (* Maximum number of queries made to oracle H1.
    This includes indirect calls generated by calls to the extraction
    oracle: [qEX_poly k < qH1_poly k] *) 
 Parameter qH1_poly : polynomial.

 (* Maximum number of queries made to oracle H2 *)
 Parameter qH2_poly : polynomial.
 
 (* Number of queries made to the extraction oracle *)
 Parameter qEX_poly : polynomial.
 
End PARAMETERS.


Module Entries (Par:PARAMETERS).

 Import Par.


 Inductive ut_ : Type := 
 | G1
 | G2
 | Bitstring.

 (** * User-defined type module *)
 Module Ut <: UTYPE.

  Definition t := ut_. 

  Definition eqb (t1 t2:t) := 
    match t1, t2 with
    | G1, G1 
    | G2, G2
    | Bitstring, Bitstring => true
    | _, _ => false
    end.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   intros; destruct x; destruct y; simpl; (trivial||discriminate).
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {True} := 
   match x as u return ({u = y} + {True}) with
    | G1 =>
     match y as u return ({G1 = u} + {True}) with
      | G1 => left _ (refl_equal G1)
      | G2 => right _ I
      | Bitstring => right _ I
     end
    | G2 =>
     match y as u return ({G2 = u} + {True}) with
      | G1 => right _ I
      | G2 => left _ (refl_equal G2)
      | Bitstring => right _ I
     end
    | Bitstring =>
     match y as u return ({Bitstring = u} + {True}) with
      | G1 => right _ I
      | G2 => right _ I
      | Bitstring => left _ (refl_equal Bitstring)
     end
   end.

  Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
  Proof.
   destruct x; destruct y; simpl; intros; discriminate.
  Qed.

  Definition interp k (x:t) : Type :=
   match x with
    | G1 => G1.t k
    | G2 => G2.t k
    | Bitstring => Bvector k
   end.

  Definition size k (x:t) (_: interp k x) : nat := 
   match x with 
    | G1 => size_nat (q k)
    | G2 => size_nat (q k)
    | Bitstring => S k
   end. 

  Definition default k (x:t) : interp k x :=
   match x with
    | G1 => G1.e k
    | G2 => G2.e k
    | Bitstring => Bvect_false k
   end.

  Definition default_poly (x:t) := 
   match x with
    | G1 => q_size_poly 
    | G2 => q_size_poly
    | Bitstring => pplus 1 pvar
   end.

  Lemma size_positive: forall k (x:t) r, 0 < @size k x r.
  Proof.
   intros k x r; destruct x; unfold size.
   apply size_nat_positive.
   apply size_nat_positive.
   auto with arith.
  Qed.

  Lemma default_poly_spec: forall k t,
   @size k t (default k t) <= default_poly t k.
  Proof.
   intros k t0; destruct t0; unfold default, default_poly, size.
   apply q_size.
   apply q_size.
   rewrite pplus_spec, pcst_spec, pvar_spec; trivial.
  Qed.

  Definition i_eqb k (x:t) : interp k x -> interp k x -> bool :=
   match x as x0 return interp k x0 -> interp k x0 -> bool with
    | G1 => @G1.eqb k
    | G2 => @G2.eqb k
    | Bitstring => @Veqb k  
   end.

  Lemma i_eqb_spec : forall k t (x y:interp k t), 
   if i_eqb x y then x = y else x <> y.
  Proof.
   intros; destruct t0; simpl.
   apply G1.eqb_spec.
   apply G2.eqb_spec.
   apply Veqb_spec.
  Qed.

 End Ut.

 Module T := MakeType Ut.

 Definition bool_support (k:nat) := true :: lfalse (qEX_poly k).

 Definition Zq_support (k:nat) := seq 1 (pred (q k)).

 Lemma Zq_support_notnil : forall k, Zq_support k <> nil.
 Proof.
  intros k H.
  assert (In 1 (Zq_support k)).
  unfold Zq_support.
  apply le_In_seq.
  generalize (prime_ge_2 _ (q_prime k)); omega.
  rewrite H in H0; elim H0.
 Qed.

 Definition G1_support (k:nat) := map (G1.pow (G1.g k)) (seq 1 (pred (q k))).

 Lemma G1_support_notnil : forall k, G1_support k <> nil.
 Proof.
  intros k H.
  assert (In (G1.g k) (G1_support k)).
  unfold G1_support.
  apply in_map_iff.
  exists 1; split.
  simpl; rewrite G1.mul_e_r; trivial.
  apply le_In_seq.
  generalize (prime_ge_2 _ (q_prime k)); omega.
  rewrite H in H0; elim H0.
 Qed.

 Inductive usupport_ 
  (Ttype:Type) (Tuser:ut_ -> Ttype) (Tbool:Ttype) (Tnat:Ttype) : Ttype -> Type :=
 | Ubool_p : usupport_ Tuser Tbool Tnat Tbool 
 | UBitstring : usupport_ Tuser Tbool Tnat (Tuser Bitstring) 
 | UZq :  usupport_ Tuser Tbool Tnat Tnat 
 | UG1 :  usupport_ Tuser Tbool Tnat (Tuser G1).


 Module Us <: USUPPORT Ut T.

  Definition usupport : T.type -> Type := usupport_ T.User T.Bool T.Nat.

  Definition eval k t (s:usupport t) : list (T.interp k t) :=
   match s in usupport_ _ _ _ t0 return list (T.interp k t0) with
    | Ubool_p => bool_support k
    | UBitstring => bs_support k  
    | UZq => Zq_support k
    | UG1 => G1_support k
   end.

  Definition ceval k t (s:usupport t) : list (T.interp k t) * nat :=
   match s in usupport_ _ _ _ t0 return list (T.interp k t0) * nat with
    | Ubool_p => (bool_support k, S O)
    | UBitstring => (bs_support k, k)
    | UZq => (Zq_support k, size_nat (q k))
    | UG1 => (G1_support k, size_nat (q k))
   end.

  Lemma eval_usupport_nil : forall k t (s:usupport t), eval k s <> nil.
  Proof.
   intros; case s.
   discriminate.
   exact (@bs_support_not_nil k).
   exact (@Zq_support_notnil k).
   exact (@G1_support_notnil k).
  Qed.

  Lemma ceval_spec : forall k t (s:usupport t), eval k s = fst (ceval k s).
  Proof.
   intros k t s; case s; trivial.
  Qed.

  Definition eqb (t1 t2:T.type) (s1:usupport t1) (s2:usupport t2) : bool :=
   match s1, s2 with
    | UZq, UZq
    | UBitstring, UBitstring
    | Ubool_p, Ubool_p 
    | UG1, UG1 => true
    | _, _ => false
   end.

  Lemma eqb_spec_dep :  forall t1 (e1 : usupport t1) t2 (e2:usupport t2),
   if eqb e1 e2 then eq_dep T.type usupport t1 e1 t2 e2
   else ~eq_dep T.type usupport t1 e1 t2 e2.
  Proof.
   intros.
   case e1; case e2; simpl; try constructor; intro H; inversion H.
  Qed.

  Lemma eqb_spec : forall t (e1 e2:usupport t),
   if eqb e1 e2 then e1 = e2 else e1 <> e2.
  Proof.
   intros t e1 e2.
   generalize (eqb_spec_dep e1 e2).
   case (eqb e1 e2); intro H.
   apply T.eq_dep_eq; trivial.
   intro Heq; apply H; rewrite Heq; constructor.
  Qed.

 End Us.

 Export BM.

 Inductive uop_ : Type :=
 | OqH1
 | OqH2
 | OqEX
 | Oq
 | Oinvq
 | Omodq
 | Olog
 | Omul1
 | Opow1
 | Oinv1
 | Omul2
 | Opow2
 | Oe
 | Obot
 | Oxor.

 Module Uop <: UOP Ut T.

  Definition t := uop_.
  
  Definition eqb (o1 o2:t) : bool :=
   match o1, o2 with
    | OqH1, OqH1 
    | OqH2, OqH2 
    | OqEX, OqEX 
    | Oq, Oq
    | Oinvq, Oinvq
    | Omodq, Omodq
    | Olog, Olog
    | Omul1, Omul1 
    | Opow1, Opow1 
    | Oinv1, Oinv1 
    | Omul2, Omul2 
    | Opow2, Opow2 
    | Oe, Oe
    | Oxor, Oxor => true
    | Obot, Obot => true
    | _, _ => false
   end.

  Lemma eqb_spec :  forall x y, if eqb x y then x = y else x <> y.
  Proof.
   destruct x; destruct y; simpl; trivial; intro; discriminate.
  Qed.
  
  Definition targs (op : t) : list T.type :=
   match op with
    | OqH1 => nil
    | OqH2 => nil
    | OqEX => nil
    | Oq => nil
    | Oinvq => T.Nat :: nil
    | Omodq => T.Nat :: nil
    | Olog =>  T.User G1 :: nil
    | Omul1 => T.User G1 :: T.User G1 :: nil
    | Opow1 => T.User G1 :: T.Nat :: nil
    | Oinv1 => T.User G1 :: nil
    | Omul2 => T.User G2 :: T.User G2 :: nil
    | Opow2 => T.User G2 :: T.Nat :: nil
    | Oe => T.User G1 :: T.User G1 :: nil  
    | Obot => nil
    | Oxor => T.User Bitstring :: T.User Bitstring :: nil
   end.
  
  Definition tres (op: t) : T.type :=
   match op with
    | OqH1 => T.Nat
    | OqH2 => T.Nat
    | OqEX => T.Nat
    | Oq => T.Nat 
    | Oinvq => T.Nat
    | Omodq => T.Nat   
    | Olog => T.Nat
    | Omul1 => T.User G1 
    | Opow1 => T.User G1
    | Oinv1 => T.User G1
    | Omul2 => T.User G2
    | Opow2 => T.User G2
    | Oe => T.User G2
    | Obot => T.User Bitstring      
    | Oxor => T.User Bitstring  
   end.

 Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
   match op as op0 return T.type_op k (targs op0) (tres op0) with
    | OqH1   => qH1_poly k 
    | OqH2   => qH2_poly k
    | OqEX   => qEX_poly k
    | Oq     => q k
    | Oinvq  => inv_mod (q k)  
    | Omodq  => fun n => n mod (q k)
    | Olog   => @G1.log k 
    | Omul1  => @G1.mul k
    | Opow1  => @G1.pow k
    | Oinv1  => @G1.inv k
    | Omul2  => @G2.mul k
    | Opow2  => @G2.pow k
    | Oe     => @BM.bmap k
    | Obot   => Bvect_false k
    | Oxor   => BVxor k
   end.

  Implicit Arguments interp_op [k].

  Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
   match op as op0 return T.ctype_op k (targs op0) (tres op0) with
    | OqH1 => (qH1_poly k, 1)
    | OqH2 => (qH2_poly k, 1)
    | OqEX => (qEX_poly k, 1)
    | Oq => (q k, 1)
    | Oinvq => fun x => (inv_mod (q k) x, size_nat (q k))
    | Omodq => fun x => (x mod (q k), size_nat (q k)) 
    | Olog => fun x => (@G1.log k x, G1.cost_log x)
    | Omul1 => fun x y => (@G1.mul k x y, G1.cost_mul x y)
    | Oinv1 => fun x => (@G1.inv k x, G1.cost_inv x)
    | Opow1 => fun x n => (@G1.pow k x n, G1.cost_pow x n)
    | Omul2 => fun x y => (@G2.mul k x y, G2.cost_mul x y)
    | Opow2 => fun x n => (@G2.pow k x n, G2.cost_pow x n)
    | Oe => fun x1 x2 => (@bmap k x1 x2, cost_bmap k)
    | Obot => (Bvect_false k, 1)
    | Oxor => fun x y => (BVxor k x y, k)  
   end.

  Implicit Arguments cinterp_op [k].

  Definition eval_op k
   (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) :=
   @T.app_op k (targs op) (tres op) (interp_op op) args.

  Definition ceval_op k 
   (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) * nat :=
   @T.capp_op k (targs op) (tres op) (cinterp_op op) args.

  Lemma ceval_op_spec : forall k op args,
   @eval_op k op args = fst (@ceval_op k op args).
  Proof.
   intros k o args; destruct o; simpl in args;
    T.dlist_inversion args; subst; trivial.
  Qed.

 End Uop.

 (** Semantics with optimizations *)
 Module SemO <: SEM_OPT.

  Module Sem := MakeSem.Make Ut T Uop Us.
  Export Sem.

  (* Maximum number of queries made to hash oracle H1 *)
  Notation "'qH1'" := (E.Eop (O.Ouser OqH1) (dnil E.expr)).

  (* Maximum number of queries made to hash oracle H2 *)
  Notation "'qH2'" := (E.Eop (O.Ouser OqH2) (dnil E.expr)).
 
  (* Number of queries made to the extraction oracle *)
  Notation "'qEX'" := (E.Eop (O.Ouser OqEX) (dnil E.expr)).

  (* Order of the groups *)
  Notation "'q'" := (E.Eop (O.Ouser Oq) (dnil E.expr)).

  (* Multiplicative inverse modulo [q] *)
  Notation "x '^-1'" := (E.Eop (O.Ouser Oinvq) {x}) (at level 50).

  (* Modulo [q] *)  
  Notation "x 'mod_q'" := (E.Eop (O.Ouser Omodq) {x}) (at level 52).

  (* G1's operation *)  
  Notation "x '|+|' y" := (E.Eop (O.Ouser Omul1) {x,y}) (at level 40).
   
  (* G1's power *)
  Notation "n '|.|' x" := (E.Eop (O.Ouser Opow1) {x, n}) (at level 40).

  (* G1's natural logarithm *)
  Notation "'log' x" := (E.Eop (O.Ouser Olog) {x}) (at level 50).

  (* G1's inverse *)
  Notation "'{-}' x" := (E.Eop (O.Ouser Oinv1) {x}) (at level 50).

  (* G2's operation *)  
  Notation "x '|*|' y" := (E.Eop (O.Ouser Omul2) {x,y}) (at level 40).
  
  (* G2's power *)
  Notation "x '|^|' n" := (E.Eop (O.Ouser Opow2) {x, n}) (at level 40).

  (* Bilinear map application *)
  Notation "'e' '(' x ',' y ')' " := (E.Eop (O.Ouser Oe) {x, y}) (at level 30).

  (* Xor *)
  Notation "x '|x|' y" := (E.Eop (O.Ouser Oxor) {x, y}) (at level 50, left associativity).	

  (* Bottom *)
  Notation bottom := (E.Eop (O.Ouser Obot) (dnil E.expr)).

  (* Abbreviation *)
  Notation "x '<<' y '!<!' z" := 
   (E.Eop O.Oand {(E.Eop O.Olt {x, y}), (E.Eop O.Olt {y, z})}) (at level 50).
  

  (* Supports *)
  Notation "'{0,1}_p'" := (E.Duser (Ubool_p T.User T.Bool T.Nat)).
  Notation "'{0,1}^k'" := (E.Duser (UBitstring T.User T.Bool T.Nat)).
  Notation "'[1..q-1]'" := (E.Duser (UZq T.User T.Bool T.Nat)).
  Notation "'G1o'" := (E.Duser (UG1 T.User T.Bool T.Nat)).

  (* Normalizes application of the bilinear map and powers in both groups *)
  Definition simpl_op (op:Uop.t) : E.args (Uop.targs op) -> E.expr (Uop.tres op) :=
   match op as op0 return E.args (Uop.targs op0) -> E.expr (Uop.tres op0) with
   | Opow1 => fun args =>
      E.app_expr (T.User G1) args 
      (fun (ex:E.expr (T.User G1)) (e3:E.expr T.Nat) =>
        match E.get_uop ex with
        | Some (existT uop args) =>
          match uop as uop0 
          return E.args (Uop.targs uop0) -> E.expr (T.User G1) with
          | Opow1 => fun args =>
            E.app_expr (T.User G1) args 
             (fun (e1:E.expr (T.User G1)) (e2:E.expr T.Nat) => (e2 *! e3) |.| e1)
          | _ => fun _ => e3 |.| ex
          end args
       | None => e3 |.| ex
       end)

   | Opow2 => fun args =>
      E.app_expr (T.User G2) args 
      (fun (ex:E.expr (T.User G2)) (e3:E.expr T.Nat) =>
        match E.get_uop ex with
        | Some (existT uop' args') =>
          match uop' as uop'0 
          return E.args (Uop.targs uop'0) -> E.expr (T.User G2) with
          | Opow2 => fun args'' =>
            E.app_expr (T.User G2) args''
             (fun (e1:E.expr (T.User G2)) (e2:E.expr T.Nat) => e1 |^| (e2 *! e3))
          | _ => fun _ => ex |^| e3
          end args'
        | None => ex |^| e3
      end)

   | Oe => fun args =>
      E.app_expr _ args 
      (fun (e1:E.expr (T.User G1)) (e2:E.expr (T.User G1)) =>
        match E.get_uop e1 with
        | Some (existT uop' args') =>
          match uop' as uop'0 
          return E.args (Uop.targs uop'0) -> E.expr (T.User G2) with
          | Opow1 => fun args'' =>
            E.app_expr _ args''
             ( fun (P:E.expr (T.User G1)) (a:E.expr T.Nat) => 
               match E.get_uop e2 with
                 | Some (existT uop'' args'') =>
                   match uop'' as uop''0 
                   return E.args (Uop.targs uop''0) -> E.expr (T.User G2) with
                   | Opow1 => fun args''' =>
                   E.app_expr _ args'''
                   (fun (Q:E.expr (T.User G1)) (b:E.expr T.Nat) => e(P,Q) |^| (a *! b)) (* e(aP, bQ) *)
                   | _ => fun _ => e(P,e2) |^| a    (* e(aP, e2) *)
                   end args''
                 | None => e(P,e2) |^| a  (* e(aP, e2) *)  
               end    
             )
          | _ => fun _ => e(e1,e2) (* e(e1, e2) *)  
          end args'
        | None => 
            match E.get_uop e2 with
            | Some (existT uop'' args'') =>
              match uop'' as uop''0 
              return E.args (Uop.targs uop''0) -> E.expr (T.User G2) with
              | Opow1 => fun args''' =>
                 E.app_expr _ args'''
                 (fun (Q:E.expr (T.User G1)) (b:E.expr T.Nat) => e(e1,Q) |^| b) (* e(e1, bQ) *)
              | _ => fun _ => e(e1,e2)    (* e(e1, e2) *)
              end args''
            | None => e(e1,e2)  (* e(e1, e2) *)  
            end    
       end)

   | op => fun args => E.Eop (O.Ouser op) args
  end.

  Implicit Arguments simpl_op [].

  Lemma simpl_op_spec : forall k op args (m:Mem.t k),
   E.eval_expr (simpl_op op args) m = E.eval_expr (E.Eop (O.Ouser op) args) m.
  Proof.
   destruct op; simpl; trivial. 

   intros args;T.dlist_inversion args; rewrite Heq; intros; simpl.
   generalize (E.get_uop_spec x); destruct (E.get_uop x); trivial.
   destruct s as (uop0, args0).
   intros H; generalize (H uop0 args0 (refl_equal _)); clear H; simpl; intros.
   destruct uop0; trivial.
   rewrite (T.eq_dep_eq H); clear H.
   clear Heq;T.dlist_inversion args0; rewrite Heq.
   simpl; unfold O.eval_op; simpl. 
   rewrite G1.pow_pow; trivial.

   intros args;T.dlist_inversion args; rewrite Heq; intros; simpl.
   generalize (E.get_uop_spec x); destruct (E.get_uop x); trivial.
   destruct s as (uop0, args0).
   intros H; generalize (H uop0 args0 (refl_equal _)); clear H; simpl; intros.
   destruct uop0; trivial.
   rewrite (T.eq_dep_eq H); clear H.
   clear Heq;T.dlist_inversion args0; rewrite Heq.
   simpl; unfold O.eval_op; simpl. 
   rewrite G2.pow_pow; trivial.

   assert (pow_1 : forall k (m:Mem.t k) (x:E.expr (T.User G1)), 
    (E.eval_expr x m) = (G1.pow (E.eval_expr x m) 1)) by
   (intros; simpl; rewrite G1.mul_e_r; trivial).
   intros args;T.dlist_inversion args; rewrite Heq; intros; simpl.
   generalize (E.get_uop_spec x); destruct (E.get_uop x); trivial.
   destruct s as (uop, args0).
   intros H; generalize (H uop args0 (refl_equal _)); clear H; simpl; intros.
   destruct uop; trivial.
   T.dlist_inversion args0; rewrite Heq0; simpl.
   generalize (E.get_uop_spec x0); destruct (E.get_uop x0).
   destruct s as (uop, args1).
   intros H1; generalize (H1 uop args1 (refl_equal _)); clear H1; simpl; intros.
   destruct uop; rewrite (T.eq_dep_eq H), Heq0; simpl; unfold O.eval_op; simpl;
    try (pattern (E.eval_expr x0 m) at 2;
     rewrite (pow_1 k m x0),(BM.bilinear  _ _ _ 1), mult_1_r; trivial).
   T.dlist_inversion args1; rewrite  (T.eq_dep_eq H0), Heq1. 
   simpl; unfold O.eval_op; simpl.
   rewrite (BM.bilinear  _ _ _ _); trivial.
   intros _ ; rewrite (T.eq_dep_eq H), Heq0.
   simpl; unfold O.eval_op; simpl.
   pattern (E.eval_expr x0 m) at 2;
    rewrite (pow_1 k m x0),(BM.bilinear  _ _ _ 1), mult_1_r; trivial.
   intros _; generalize (E.get_uop_spec x0); destruct (E.get_uop x0).
   destruct s as (uop, args1).
   intros H1; generalize (H1 uop args1 (refl_equal _)); clear H1; simpl; intros.
   destruct uop; simpl; unfold O.eval_op; simpl; trivial.
   T.dlist_inversion args1; rewrite (T.eq_dep_eq H), Heq0.
   simpl; unfold O.eval_op; simpl.
   pattern (E.eval_expr x m) at 2;
    rewrite (pow_1 k m x),(BM.bilinear  _ _ 1 _ ), mult_1_l; trivial.
   intros; trivial.
  Qed.

 End SemO.

 Module BP := BaseProp.Make SemO.Sem.

 Module Uppt.

  Import BP.
  
  Implicit Arguments T.size [k t].

  (** PPT expression *)
  Definition PPT_expr (t:T.type) (e:E.expr t) 
   (F:polynomial -> polynomial) 
   (G:polynomial -> polynomial) : Prop :=
   forall k (m:Mem.t k) (p:polynomial),
    (forall t (x:Var.var t), 
     BP.Vset.mem x (BP.fv_expr e) -> T.size (m x) <= p k)  ->
    let (v,n) := E.ceval_expr e m in
     T.size v <= (F p) k /\
     n <= (G p) k.

  (** PPT support *)
  Definition PPT_support t (s:E.support t)
   (F:polynomial -> polynomial) 
   (G:polynomial -> polynomial) : Prop :=
   forall k (m:Mem.t k) (p:polynomial),
    (forall t (x:Var.var t), 
     BP.Vset.mem x (BP.fv_distr s) -> T.size (m x) <= p k)  ->
    let (l,n) := E.ceval_support s m in
     (forall v, In v l -> T.size v <= (F p) k) /\
     n <= (G p) k.

  Definition utsize (x:UT.t) : nat := 1.

  Definition utsize_default_poly : nat -> polynomial :=
   fun _ => pplus (pplus 2 pvar) q_size_poly.

  Lemma utsize_default_poly_spec : forall r ut,
   utsize ut <= r -> 
   forall k, UT.size (t:=ut) (UT.default k ut) <= (utsize_default_poly r) k.
  Proof.
   intros r ut _ k.
   generalize (q_size k).
   case ut; simpl; unfold UT.size, utsize_default_poly;
   rewrite pplus_spec, pplus_spec, pcst_spec, pvar_spec; omega.
  Qed.

  Definition uop_poly (o:Uop.t) : bool :=
    match o with 
      | Olog => false
      | _ => true
    end.

  Lemma uop_poly_spec : forall o (la:dlist E.expr (O.targs (O.Ouser o))),
   uop_poly o ->
   (forall t (e:E.expr t), @DIn _ E.expr _ e _ la -> 
    exists F, exists G, PPT_expr e F G) ->
   exists F, exists G, PPT_expr (E.Eop (O.Ouser o) la) F G.
  Proof.
   intros o la H Hla.
   destruct o.

   (* OqH1 *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   exists (fun _ => pplus 1 qH1_poly).
   exists (fun _ => 1). 
   simpl; split.
   rewrite pplus_spec, pcst_spec; case (qH1_poly k).
   trivial.
   intro n; apply le_trans with (S n); [apply size_nat_le | ]; auto with arith.
   rewrite pcst_spec; trivial.

   (* OqH2 *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   exists (fun _ => pplus 1 qH2_poly).
   exists (fun _ => 1). 
   simpl; split.
   rewrite pplus_spec, pcst_spec; case (qH2_poly k).
   trivial.
   intro n; apply le_trans with (S n); [apply size_nat_le | ]; auto with arith.
   rewrite pcst_spec; trivial.

   (* OqEX *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   exists (fun _ => pplus 1 qEX_poly).
   exists (fun _ => 1). 
   simpl; split.
   rewrite pplus_spec, pcst_spec; case (qEX_poly k).
   trivial.
   intro n; apply le_trans with (S n); [apply size_nat_le | ]; auto with arith.
   rewrite pcst_spec; trivial.

   (* OGorder *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   exists (fun _ => q_size_poly). 
   exists (fun _ => 1).
   simpl; split.
   apply q_size.
   rewrite pcst_spec; trivial.

   (* Oinvq *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F [I H1] ].
   left; trivial.
   exists (fun _ => q_size_poly). 
   exists (fun p => pplus q_size_poly (I p)).
   simpl; split.
   simpl; unfold O.eval_op; simpl.
   apply le_trans with (size_nat (q k)); [ | apply q_size].
   apply size_nat_monotonic.
   apply lt_le_weak; unfold inv_mod.
   assert (Hq:(0 < Z_of_nat (q k))%Z).
   generalize (prime_ge_2 _ (q_prime k)); omega.
   destruct (Zinv_mod_bound (Z_of_nat (E.eval_expr x m)) _ Hq).
   apply inj_lt_rev; rewrite inj_Zabs_nat, Zabs_eq; trivial.

   rewrite pplus_spec; apply plus_le_compat.
   apply q_size.
   simpl; rewrite plus_0_r.
   generalize (H1 k m p); clear H1.
   case_eq (E.ceval_expr x m); simpl.
   intros i n Heqi Hi.
   destruct Hi.
   intros; apply H0; simpl.
   auto with set.
   trivial.

   (* Omodq *)
   admit.

   (* Olog *)
   discriminate.

   (* Omul1 *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [I1 H1] ].
   left; trivial.
   destruct (Hla _ x0) as [F2 [I2 H2] ].
   right; left; trivial.
   exists (fun _ => q_size_poly).
   exists (fun p => pplus G1.cost_mul_poly (pplus (I1 p) (I2 p))).
   intros k m p Hm; simpl; split.
   apply q_size.
   rewrite pplus_spec, pplus_spec.
   apply plus_le_compat.
   eapply le_trans ; [ apply G1.cost_mul_poly_spec | trivial].
 
   generalize (H1 k m p) (H2 k m p); clear H1 H2.
   case_eq (E.ceval_expr x m); simpl.
   case_eq (E.ceval_expr x0 m); simpl.
   intros i n Heqi i0 n0 Heqi0 Hi Hi0.
   destruct Hi.
   intros; apply Hm; simpl.
   apply Vset.subset_correct with (fv_expr x); [ | trivial].  
   unfold fv_expr; simpl.
   apply fv_expr_rec_subset.
   destruct Hi0.
   intros; apply Hm; simpl.
   apply Vset.subset_correct with (fv_expr x0); [ | trivial].  
   unfold fv_expr at 2; simpl.
   fold (fv_expr_extend x0 (fv_expr_rec Vset.empty x)).
   rewrite union_fv_expr_spec.
   apply VsetP.subset_union_l.
   rewrite plus_0_r; apply plus_le_compat; auto.  

   (* Opow1 *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [I1 H1] ].
   left; trivial.
   destruct (Hla _ x0) as [F2 [I2 H2] ].
   right; left; trivial.
   exists (fun _ => q_size_poly).
   exists (fun p => pplus G1.cost_pow_poly (pplus (I1 p) (I2 p))).
   intros k m p Hm; simpl; split.
   apply q_size.
   rewrite pplus_spec, pplus_spec.
   apply plus_le_compat.
   apply G1.cost_pow_poly_spec.

   rewrite plus_0_r.
   generalize (H1 k m p) (H2 k m p); clear H1 H2.
   case_eq (E.ceval_expr x m); simpl.
   case_eq (E.ceval_expr x0 m); simpl.
   intros i n Heqi i0 n0 Heqi0 Hi Hi0.
   destruct Hi.
   intros; apply Hm; simpl.
   apply Vset.subset_correct with (fv_expr x); [ | trivial].  
   unfold fv_expr; simpl.
   apply fv_expr_rec_subset.
   destruct Hi0.
   intros; apply Hm; simpl.
   apply Vset.subset_correct with (fv_expr x0); [ | trivial].  
   unfold fv_expr at 2; simpl.
   fold (fv_expr_extend x0 (fv_expr_rec Vset.empty x)).
   rewrite union_fv_expr_spec.
   apply VsetP.subset_union_l.
   apply plus_le_compat; trivial.  

   (* Oinv1 *)
   admit.

   (* Omul2 *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [I1 H1] ].
   left; trivial.
   destruct (Hla _ x0) as [F2 [I2 H2] ].
   right; left; trivial.
   exists (fun _ => q_size_poly).
   exists (fun p => pplus G2.cost_mul_poly (pplus (I1 p) (I2 p))).
   intros k m p Hm; simpl; split.
   apply q_size.
   rewrite pplus_spec, pplus_spec.
   apply plus_le_compat.
   eapply le_trans ; [ apply G2.cost_mul_poly_spec | trivial].
 
   generalize (H1 k m p) (H2 k m p); clear H1 H2.
   case_eq (E.ceval_expr x m); simpl.
   case_eq (E.ceval_expr x0 m); simpl.
   intros i n Heqi i0 n0 Heqi0 Hi Hi0.
   destruct Hi.
   intros; apply Hm; simpl.
   apply Vset.subset_correct with (fv_expr x); [ | trivial].  
   unfold fv_expr; simpl.
   apply fv_expr_rec_subset.
   destruct Hi0.
   intros; apply Hm; simpl.
   apply Vset.subset_correct with (fv_expr x0); [ | trivial].  
   unfold fv_expr at 2; simpl.
   fold (fv_expr_extend x0 (fv_expr_rec Vset.empty x)).
   rewrite union_fv_expr_spec.
   apply VsetP.subset_union_l.
   rewrite plus_0_r; apply plus_le_compat; auto.  

   (* Opow2 *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [I1 H1] ].
   left; trivial.
   destruct (Hla _ x0) as [F2 [I2 H2] ].
   right; left; trivial.
   exists (fun _ => q_size_poly).
   exists (fun p => pplus G2.cost_pow_poly (pplus (I1 p) (I2 p))).
   intros k m p Hm; simpl; split.
   apply q_size.
   rewrite pplus_spec, pplus_spec.
   apply plus_le_compat.
   apply G2.cost_pow_poly_spec.

   rewrite plus_0_r.
   generalize (H1 k m p) (H2 k m p); clear H1 H2.
   case_eq (E.ceval_expr x m); simpl.
   case_eq (E.ceval_expr x0 m); simpl.
   intros i n Heqi i0 n0 Heqi0 Hi Hi0.
   destruct Hi.
   intros; apply Hm; simpl.
   apply Vset.subset_correct with (fv_expr x); [ | trivial].  
   unfold fv_expr; simpl.
   apply fv_expr_rec_subset.
   destruct Hi0.
   intros; apply Hm; simpl.
   apply Vset.subset_correct with (fv_expr x0); [ | trivial].  
   unfold fv_expr at 2; simpl.
   fold (fv_expr_extend x0 (fv_expr_rec Vset.empty x)).
   rewrite union_fv_expr_spec.
   apply VsetP.subset_union_l.
   apply plus_le_compat; trivial.  

   (* Oe *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [I1 H1] ].
   left; trivial.
   destruct (Hla _ x0) as [F2 [I2 H2] ].
   right; left; trivial.
   exists (fun _ => q_size_poly).
   exists (fun p => pplus cost_bmap (pplus (I1 p) (I2 p))).
   intros k m p Hm; simpl; split.
   apply q_size.
   rewrite pplus_spec, pplus_spec.
   repeat (apply plus_le_compat); [trivial | | rewrite plus_0_r].

   generalize (H1 k m p); clear H1.
   case_eq (E.ceval_expr x m); simpl.
   intros i n Heqi Hi.
   destruct Hi.
   intros; apply Hm; simpl.
   apply Vset.subset_correct with (fv_expr x); [ | trivial].
   unfold fv_expr; simpl.
   apply fv_expr_rec_subset.
   trivial.

   generalize (H2 k m p); clear H2.
   case_eq (E.ceval_expr x0 m); simpl.
   intros i n Heqi Hi.
   destruct Hi.
   intros; apply Hm; simpl.
   apply Vset.subset_correct with (fv_expr x0); [ | trivial].
   unfold fv_expr at 2; simpl.
   fold (fv_expr_extend x0 (fv_expr_rec Vset.empty x)).
   rewrite union_fv_expr_spec.
   apply VsetP.subset_union_l.
   trivial.
  
   (* Obot *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   exists (fun _ => pplus 1 pvar).
   exists (fun _ => 1). 
   simpl; split.
   rewrite pplus_spec, pvar_spec, pcst_spec; simpl; trivial.
   rewrite pcst_spec; trivial.
   
   (* Oxor *)
   T.dlist_inversion la.
   rewrite Heq in Hla |- *.
   destruct (Hla _ x) as [F1 [I1 H1] ].
   left; trivial.
   destruct (Hla _ x0) as [F2 [I2 H2] ].
   right; left; trivial.
   exists (fun _ => pplus 1 pvar).
   exists (fun p => pplus (pplus 1 pvar) (pplus (I1 p) (I2 p))).
   simpl; split.
   rewrite pplus_spec, pcst_spec, pvar_spec.
   simpl; unfold UT.size; trivial.
   
   generalize (H1 k m p) (H2 k m p); clear H1 H2.
   simpl.
   case_eq (E.ceval_expr x m); simpl.
   case_eq (E.ceval_expr x0 m); simpl.
   intros i n Heqi i0 n0 Heqi0 Hi Hi0.
   destruct Hi.
   intros; apply H0; simpl.
   apply Vset.subset_correct with (fv_expr x); [ | trivial].  
   unfold fv_expr; simpl.
   apply fv_expr_rec_subset.
   destruct Hi0.
   intros; apply H0; simpl.
   apply Vset.subset_correct with (fv_expr x0); [ | trivial].  
   unfold fv_expr at 2; simpl.
   fold (fv_expr_extend x0 (fv_expr_rec Vset.empty x)).
   rewrite union_fv_expr_spec.
   apply VsetP.subset_union_l.
   
   rewrite pplus_spec, pplus_spec, pplus_spec, pcst_spec, pvar_spec.    
   apply plus_le_compat; auto.  
   auto with arith.
   rewrite plus_0_r; apply plus_le_compat; trivial. 
  Qed.

  Definition usupport_poly t (us:US.usupport t) : bool := true.

  Lemma usupport_poly_spec : forall t (us:US.usupport t),
   usupport_poly us ->
   exists F, exists G, PPT_support (E.Duser us) F G.
  Proof.
   intros t us; case us; intros _.

   (** {0,1} *)
   exists (fun _ => 1).
   exists (fun _ => 1).
   intros k m p Hm.
   rewrite pcst_spec.
   split; trivial.

   (** {0,1}^k *)
   exists (fun _ => pplus 1 pvar).
   exists (fun _ => pvar).
   intros k m p Hm.
   split.
   intros; rewrite pplus_spec, pvar_spec, pcst_spec; trivial.
   rewrite pvar_spec; trivial.
   
   (** Zq *)
   exists (fun _ => q_size_poly).
   exists (fun _ => q_size_poly).
   intros k m p Hm.
   split; [ | apply q_size].
   intros v H.
    destruct (In_seq_le _ _ _ H) as [_ Hv]; clear H.
    rewrite plus_comm in Hv; unfold plus in Hv; rewrite <- (S_pred _ 0) in Hv.
    apply le_trans with (size_nat (q k)).
    apply size_nat_monotonic; auto with arith.
    apply q_size.
    generalize (prime_ge_2 _ (q_prime k)); omega.

   (** G1^* *)
   exists (fun _ => q_size_poly).
   exists (fun _ => q_size_poly).
   intros k m p Hm.
   split; intros; apply q_size.
  Qed.

 End Uppt.

End Entries.


Declare Module Par : PARAMETERS.
Module Ent := Entries Par.

Module Tactics := BuildTac.Make Ent.
Export Tactics.

Export Par.

(** TODO: move this somewhere else *)
Lemma expr_eval_lt : forall k (m:Mem.t k) (e1 e2:E.expr T.Nat),
 E.eval_expr e1 m < E.eval_expr e2 m <->
 E.eval_expr (e1 <! e2) m.
Proof.
 intros; simpl; unfold O.eval_op; simpl; split; intro.
 apply leb_correct; omega.
 apply leb_complete in H; omega.
Qed.

Lemma in_dom_In : forall A B (x:E.expr A) (L:Var.var (T.List (T.Pair A B)))
 k (m:Mem.t k),
 E.eval_expr (x in_dom L) m ->
 In (E.eval_expr x m, E.eval_expr (L[{x}]) m) (m L). 
Proof.
 simpl; unfold O.eval_op; simpl; intros.
 rewrite is_true_existsb in H.
 destruct H as [(x',y) [Hin Heq] ].
 induction (m L) as [ | xy L0 ].
 inversion Hin.
 simpl in *; destruct xy as (x0, y0); destruct Hin.
 injection H; intros; subst; clear H.
 rewrite is_true_Ti_eqb in Heq; subst.
 unfold O.assoc; simpl; rewrite Ti_eqb_refl; auto.
 rewrite is_true_Ti_eqb in Heq; subst.
 unfold O.assoc; simpl.
 case_eq (T.i_eqb k A (E.eval_expr x m) x0); intro H0.
 left; simpl.
 fold (is_true (T.i_eqb k A (E.eval_expr x m) x0)) in H0.
 rewrite is_true_Ti_eqb in H0; subst; trivial.
 auto.
Qed.

Lemma In_in_dom : forall A B k (m:Mem.t k) (x:E.expr A) (y:T.interp k B) 
 (L:Var.var (T.List (T.Pair A B))),
 In (E.eval_expr x m, y) (m L) -> 
 E.eval_expr (x in_dom L) m.
Proof.
 intros; unfold E.eval_expr, O.eval_op; simpl.
 bprop.
 exists (E.eval_expr x m, y); split.
 assumption.
 rewrite is_true_Ti_eqb; trivial.
Qed.

Lemma req_mem_upd_notin : forall k (m1 m2:Mem.t k) t1 t2 (v1: Var.var t1) (v2: Var.var t2) e1 e2 X, 
 req_mem X m1 m2 ->
 ~Vset.mem v1 X ->
 ~Vset.mem v2 X ->
 req_mem X (m1 {!v1 <-- e1!}) (m2 {!v2 <-- e2!}).
Proof.
 intros; intros t0 x Hx.
 repeat rewrite Mem.get_upd_diff.
 apply H; trivial.
 intro Heq; elim H1; rewrite Heq; trivial.
 intro Heq; elim H0; rewrite Heq; trivial.
Qed.

Lemma req_mem_upd_notin_l : forall k (m1 m2:Mem.t k) t (v1:Var.var t) e1 X, 
 req_mem X m1 m2 ->
 ~Vset.mem v1 X ->
 req_mem X (m1 {!v1 <-- e1!}) m2.
Proof.
 intros; intros t0 x Hx.
 repeat rewrite Mem.get_upd_diff.
 apply H; trivial.
 intro Heq; elim H0; rewrite Heq; trivial.
Qed.

Lemma req_mem_upd_notin_r : forall k (m1 m2:Mem.t k) t (v2:Var.var t) e2 X, 
 req_mem X m1 m2 ->
 ~Vset.mem v2 X ->
 req_mem X m1 (m2 {!v2 <-- e2!}).
Proof.
 intros; intros t0 x Hx.
 repeat rewrite Mem.get_upd_diff.
 apply H; trivial.
 intro Heq; elim H0; rewrite Heq; trivial.
Qed.

Open Scope U_scope.

Lemma finite_lfalse : forall (x:Var.var T.Bool) k (m:Mem.t k) f' (N n:nat),
 (n <= N)%nat ->
 finite_sum (fun a : bool => [1/]1+N * f' (m{!x <-- a!})) (lfalse n) == 
 (n */ [1/]1+N) * f' (m{!x <-- false!}).
Proof.
 induction n; simpl; intros.
 auto.
 match goal with 
  |- ?X == ?Y => 
   change Y with (((Datatypes.S n) */ [1/]1+N) * f' (m{!x <-- false!}))
 end.
 rewrite Nmult_S, Udistr_plus_right.
 apply Uplus_eq_compat; trivial.
 apply IHn; auto with arith.
 apply Uinv_le_perm_right.
 apply Nmult_le_n_Unth; auto with arith.
Qed.

Lemma deno_sample_p : forall (x:Var.var T.Bool) k (m:Mem.t k) E f',
 mu ([[ [x <$-{0,1}_p] ]] E m) f' ==
 [1/]1+peval qEX_poly k       * (f' (m{!x <-- true!})) + 
 [1-] [1/]1+peval qEX_poly k  * (f' (m{!x <-- false!})). 
Proof.
 intros; rewrite deno_random_elim.
 change 
  (mu (sum_support (T.default k T.Bool) (E.eval_support {0,1}_p m))
   (fun v => f' (m {!x <-- v!}))) 
  with 
   (sum_dom (T.default k T.Bool) (E.eval_support {0,1}_p m)
    (fun v => f' (m {!x <-- v!}))).
 rewrite sum_dom_finite; simpl; rewrite length_lfalse.
 apply Uplus_eq_compat; trivial.
 rewrite <- Nmult_n_Unth.
 apply finite_lfalse; auto with arith.
Qed.

Lemma mu_range_and : forall A (d:Distr A) (P Q:A -o> boolO),
 mu d (fone _) == 1 ->
 range P d -> 
 range Q d ->
 range (P [&&] Q) d.
Proof.
 intros; apply mu_range.
 rewrite <- (mu_range_strenghten _ Q H0).
 transitivity (mu d (fone _)); [ | trivial].
 apply range_mu; trivial. 
Qed.

Lemma charfun_and_elim : forall (A:Type) (P Q:A -o> boolO) (a:A),
 charfun (P[&&]Q) a == charfun P a * charfun Q a.
Proof.
 intros.
 fold (Fmult (charfun P) (charfun Q) a).
 apply ford_eq_elim.
 refine (charfun_and _ _).
Qed.

Lemma charfun_compat_pointwise : forall (A:Type) (F G:A -o> boolO) (x:A),
 F x == G x -> charfun F x == charfun G x.
Proof.
 intros.
 unfold charfun, restr, fone.
 rewrite (Oeq_eq_bool H); trivial.
Qed.

Close Scope U_scope.
Close Scope bool_scope.

Lemma EP2_and_elim : forall x y: E.expr (T.Bool),
 implMR (EP2 (x && y)) ((EP2 x) /-\ (EP2 y)). 
Proof.
 unfold EP2; simpl; unfold O.eval_op; simpl.
 intros x y k m1 m2 H.
 unfold is_true in H; rewrite andb_true_iff in H; destruct H.
 split; assumption.
Qed.


Ltac expr_simpl := 
 unfold EP1, EP2, notR, andR, orR, impR, E.eval_expr; simpl; 
 unfold O.eval_op; simpl; mem_upd_simpl.

Ltac bool_tauto :=
 match goal with
  | |- _ -> _ => red_antecedent
  | |- (@Oeq boolO) _ _ => red_eq_LHS; red_eq_RHS
  | |- (@Oeq (tcpo U)) (charfun _) (charfun _) => apply charfun_eq_compat; bool_tauto
  | |- _ => idtac
 end with 
 red_antecedent :=
 match goal with
  | |- is_true true -> _   => intros _; bool_tauto 
  | |- is_true false -> _  => intro; discriminate 
  | |- is_true (?exp) -> _ => case_expr exp; bool_tauto
  | |- if ?exp then _ else _ -> _  => (case_expr exp); bool_tauto
  | |- _ -> _ => idtac
 end  with
 red_eq_LHS :=
 match goal with
  | |- (@Oeq boolO) true  _  => idtac
  | |- (@Oeq boolO) false _  => idtac
  | |- (@Oeq boolO) ?e1   _  => case_expr e1; red_eq_LHS
  | |- _ => idtac
 end  with
 red_eq_RHS := 
 match goal with
  | |- (@Oeq boolO) _  true   => try trivial
  | |- (@Oeq boolO) _  false  => try trivial
  | |- (@Oeq boolO) _  ?e2    => case_expr e2; red_eq_RHS
  | |- _ => idtac
 end  with
 case_expr e' :=
 match e' with
  | true => idtac
  | false => idtac
  | (@E.eval_expr _ T.Bool (E.Eop O.Oimp {?exp1, ?exp2}) ?m) => 
   change (@E.eval_expr _ T.Bool (exp1 ==> exp2) m) with
    (impb (@E.eval_expr _ T.Bool exp1 m) (@E.eval_expr _ T.Bool exp2 m)); unfold impb, negb, orb
  | (@E.eval_expr _  T.Bool (E.Eop O.Onot {?exp}) ?m) =>
   change (@E.eval_expr _ T.Bool (E.Eop O.Onot {exp}) m) with 
    (negb (@E.eval_expr _ T.Bool exp m)); unfold negb
  | (@E.eval_expr _ T.Bool ?exp ?m) => case (@E.eval_expr _ T.Bool exp m)  
  | impb ?e1 ?e2 => unfold impb, negb, orb
  | negb ?exp => unfold negb
  | if ?exp then ?e1 else ?e2 => (case_expr exp) 
  | _ => idtac
 end.

Ltac rewrite_req_mem_l Hrm :=
 unfold kreq_mem in Hrm;
  match type of Hrm with
   | req_mem _ ?m1 ?m2 =>
    unfold andP, negP, andb, negb, EP; unfold charfun, restr, fone; unfold EP1, EP2;
     repeat (rewrite (@depend_only_fv_expr T.Bool _ _  m1 m2);
      [| apply req_mem_weaken with (2:= Hrm); unfold Vset.subset; trivial]); 
     trivial
   | _ => idtac
  end.

Ltac rewrite_req_mem_r Hrm :=
 unfold kreq_mem in Hrm;
  match type of Hrm with
   | req_mem _ ?m1 ?m2 =>
    unfold andP, negP, andb, negb, EP; unfold charfun, restr, fone; unfold EP1, EP2;
     repeat (rewrite <-(@depend_only_fv_expr T.Bool _ _  m1 m2);
      [| apply req_mem_weaken with (2:= Hrm); unfold Vset.subset; trivial]); 
     trivial
   | _ => idtac
  end.

Ltac bool_tauto_l Hrm :=
 let H := fresh "Haux" in
  match goal with
   | |- _ -> charfun ?F1 ?m1 == charfun ?F2 ?m2 => 
    intro H; transitivity (charfun F1 m2);
     [ 
      rewrite_req_mem_l Hrm
      | 
       apply charfun_compat_pointwise; 
     unfold EP1, EP2 in H;
      repeat (rewrite (@depend_only_fv_expr T.Bool _ _  m1 m2) in H;
       [| apply req_mem_weaken with (2:=Hrm); unfold Vset.subset; trivial]);   
      generalize H; clear H; unfold EP, andP, andb, negP, negb;  bool_tauto  
     ]
  end.

Ltac bool_tauto_r Hrm :=
 let H := fresh "Haux" in
  match goal with
   | |- _ -> charfun ?F1 ?m1 == charfun ?F2 ?m2 => 
    intro H; transitivity (charfun F2 m1);
   [ 
    apply charfun_compat_pointwise; 
     unfold EP1, EP2 in H;
      repeat (rewrite (@depend_only_fv_expr T.Bool _ _  m2 m1) in H;
       [| apply req_mem_weaken with (2:= req_mem_sym Hrm); unfold Vset.subset; trivial]); 
     generalize H; clear H; unfold EP, andP, andb, negP, negb; bool_tauto
    |
     rewrite_req_mem_r Hrm
   ] 
  end.

(***)

Section PRIME_PROPERTIES.

 Variables p : nat.
 Variable prime_p : prime (Z_of_nat p). 

 Lemma p_bound : 1 < p.
 Proof.
  apply prime_ge_2 in prime_p; omega.
 Qed.

 Lemma inv_mod_neq_0_prime: forall n, 
  0 < n < p ->
  inv_mod p n <> 0.
 Proof.
  intros n [Hl Hu]; refine (inv_mod_neq_0 _ _ _ _ Hl).
    apply (inj_lt _ _ (p_bound)).  
    apply (Zis_gcd_prime _ _ prime_p).
      apply (inj_neq n 0); apply not_eq_sym; apply (lt_0_neq _ Hl).
      split; [ omega | apply (inj_lt _ _ Hu) ].
 Qed.

 Variable a : nat.
 Variable a_bound : 0 < a < p.

 Lemma mod_mult_neq_0_prime: forall b, 0 < b < p ->
   (a * b) mod p <> 0. 
 Proof.
  intros b Hb.
  unfold nmod; change 0 with (Zabs_nat (Z_of_nat 0)); injection; intros _.
  apply inj_eq in H; simpl in H; rewrite inj_Zabs_nat in H; apply Zabs_0_inv in H.
  elim (Zrel_prime_neq_mod_0 (Z_of_nat (a * b)) (Z_of_nat p)); trivial.
    apply (inj_lt 1 p p_bound).
    apply rel_prime_sym; rewrite inj_mult; apply rel_prime_mult. 
      apply rel_prime_sym; apply (rel_prime_le_prime _ _ prime_p); omega.
      apply rel_prime_sym; apply (rel_prime_le_prime _ _ prime_p); omega.
 Qed.

 Lemma Permut_Mod_Prime :
  PermutP (fun v1 v2 => v1 = nmod (a * v2) p) 
  (seq 1 (pred p)) 
  (seq 1 (pred p)).
 Proof.
  apply PermutP_NoDup with 
   (f_inv := fun z => nmod (inv_mod p a * z) p).
  apply NoDup_seq.
  apply NoDup_seq.

  intros x H.
  rewrite mult_mod_idemp_r, mult_assoc, mult_mod, inv_mod_prime, mult_1_l; trivial.
  rewrite mod_mod; apply mod_small.
  apply In_seq_le in H; omega.
  
  intros x H.
  apply In_seq_le in H.
  rewrite mult_mod_idemp_r, mult_assoc, mult_mod, (mult_comm _ a).
  rewrite inv_mod_prime, mult_1_l, mod_mod, mod_small; trivial.
  omega.

  intros x H.
  apply In_seq_le in H.
  destruct (@mod_lt (a * x) p).
  omega.
  apply le_In_seq; split; [ | omega].
  assert ((a * x) mod p <> 0).
  intro Heq.
  unfold nmod in Heq.
  apply inj_eq in Heq.
  rewrite inj_Zabs_nat in Heq.
  rewrite Zabs_eq in Heq.
  rewrite inj_mult in Heq.
  apply mod_mult_0 in Heq; trivial.
  destruct Heq as [H2 | H2]; (apply Z_div_exact_2 in H2; [ | omega]).
  rewrite Zdiv_small in H2; omega.
  rewrite Zdiv_small in H2; omega.
  apply Zabs_0_inv in Heq.
  rewrite Heq; omega.
  omega.

  intros x H.
  apply In_seq_le in H.
  destruct (@mod_lt (inv_mod p a * x) p).
  omega.
  apply le_In_seq; split; [ | omega ].
  assert ((inv_mod p a * x) mod p <> 0).
  intro Heq.
  unfold nmod in Heq.
  apply inj_eq in Heq.
  rewrite inj_Zabs_nat in Heq.
  rewrite Zabs_eq in Heq.
  rewrite inj_mult in Heq.
  apply mod_mult_0 in Heq; trivial.
  destruct Heq as [H2 | H2]; (apply Z_div_exact_2 in H2; [ | omega]).
 
  rewrite Zdiv_small, Zmult_0_r in H2.
  elim (@inv_mod_neq_0 a p).
  omega.
  apply Zis_gcd_prime.
  trivial.
  omega.
  omega.
  omega.
  apply inj_eq_rev.
  trivial.
  
  destruct (@Zinv_mod_bound (Z_of_nat a) (Z_of_nat p)).
  omega.
  unfold inv_mod.
  rewrite inj_Zabs_nat.
  rewrite Zabs_eq.
  omega.
  omega.
  
  rewrite Zdiv_small in H2; omega.
  apply Zabs_0_inv in Heq.
  rewrite Heq; omega.
  omega.
 Qed.

End PRIME_PROPERTIES.


 Lemma equiv_random_permut_gen : forall (Q:mem_rel) E1 E2 t1 t2 
  (x1:Var.var t1) (x2:Var.var t2)
  (f:forall k, Mem.t k -> Mem.t k -> T.interp k t2 -> T.interp k t1) 
  (d1:E.support t1) (d2:E.support t2),
  equiv ((permut_support f d1 d2) /-\ 
   (fun k m1 m2 => 
    forall v, In v (E.eval_support d2 m2) -> 
     Q k (m1{!x1 <-- f k m1 m2 v!}) (m2{!x2 <-- v!})))
  E1 [x1 <$- d1] E2 [x2<$-d2] Q.
 Proof.
  unfold equiv; intros.
  exists (fun m1 m2 =>
   Mlet (([[ [x2 <$- d2] ]]) E2 m2)
   (fun m => 
    Munit (m1{! x1 <-- f k m1 m2 (m x2) !}, m))); intros.
  destruct H; constructor; intros.
  rewrite Mlet_simpl, deno_random_elim, deno_random_elim.
  change  (fun x0 : T.interp k t2 =>
   mu
   (Munit
    (m1 {!x1 <-- f k m1 m2 ((m2 {!x2 <-- x0!}) x2)!}, m2 {!x2 <-- x0!}))
   (fun x : Mem.t k * Mem.t k => f0 (fst x))) with
  (fun x0 : T.interp k t2 =>f0 (m1 {!x1 <-- f k m1 m2 ((m2 {!x2 <-- x0!}) x2)!})).
  symmetry.
  refine (@sum_dom_permut_eq (T.interp k t1) (T.interp k t2)
    (T.default k t1) (T.default k t2)
   (E.eval_support d1 m1) (E.eval_support d2 m2) 
   (fun x0 : T.interp k t1 => f0 (m1 {!x1 <-- x0!}))
   (fun x0 : T.interp k t2 =>
    f0 (m1 {!x1 <-- f k m1 m2 ((m2 {!x2 <-- x0!}) x2)!})) _ ).
  red in H.
  generalize (E.eval_support d1 m1) (E.eval_support d2 m2) H; clear H H0.
  induction 1; constructor; subst; trivial.
  rewrite Mem.get_upd_same; trivial.
  rewrite Mlet_simpl, deno_random_elim, deno_random_elim; trivial.
  rewrite deno_random.
  unfold range; intros.
  repeat rewrite Mlet_simpl.
  change (0 == sum_dom (T.default k t2) (E.eval_support d2 m2)
   (fun x : T.interp k t2 => 
    f0 (m1 {!x1 <-- f k m1 m2 (m2 {!x2 <-- x!} x2)!}, m2 {!x2 <-- x!}))).
  rewrite sum_dom_finite.
  generalize (E.eval_support d2 m2) 
   (Unth (pred (length (E.eval_support d2 m2)))) H0.
  induction l; simpl; intros; trivial.
  rewrite <- IHl; auto.
  rewrite <- H1; auto.
  red; simpl.
  rewrite Mem.get_upd_same; auto.
 Qed.

  Lemma fv_expr_andb: forall (e1 e2:E.expr T.Bool),
    fv_expr (e1 && e2) [=] Vset.union (fv_expr e1) (fv_expr e2).
  Proof.
   unfold fv_expr; intros; simpl.
   fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).   
   rewrite union_fv_expr_spec.
   apply VsetP.union_sym.
  Qed.

 Ltac Vset_mem_inversion2 :=
 fun H =>
  match type of H with
  | is_true (Vset.mem _ Vset.empty) =>
      discriminate H
  | is_true (Vset.mem ?x (Vset.singleton ?y)) =>
      change (is_true (Vset.mem x {{y}})) in H; Vset_mem_inversion H
  | is_true (Vset.mem ?x (Vset.add ?y ?X)) =>
      let H1 := fresh "H" in
      let Heq := fresh "Heq" in
      generalize (Var.eqb_spec y x); case_eq (Var.eqb y x); intros _ H1;
        [ try discriminate; try auto| pose proof (Vset.add_inversion _ H1 H) 
          as Heq; Vset_mem_inversion2 Heq  ]; clear H 
  end.


Section SAMPLING_FACTS.

 Lemma opt_sampling : forall E (x y z:Var.var (T.User Bitstring)), 
  Var.mkV x <> y ->
  Var.mkV x <> z ->
  Var.mkV y <> z ->
  EqObs {{z}}
  E [x <$- {0,1}^k; y <- x |x| z] 
  E [y <$- {0,1}^k; x <- y |x| z]
  {{x,y,z}}.
 Proof.
  intros E x y z Hxy Hxz Hyz.
  apply equiv_cons with
   (kreq_mem {{z}} /-\ fun k m1 m2 => m1 x = BVxor _ (m2 y) (m2 z)).

  eapply equiv_strengthen; [ | apply equiv_random_permut with 
   (f:=fun k (m1 m2:Mem.t k) v => BVxor _ (m2 z) v)].
  unfold kreq_mem, andR; split.

  apply PermutP_weaken with (fun v1 v2 => v1 = BVxor k v2 (m2 z)).
  intros; subst; apply BVxor_comm.
  apply PermutP_bs_support_xor.
  
  intros; rewrite <- (H _ z); [ | auto with set].
  split.

  intros ? ? Hn; Vset_mem_inversion Hn.
  rewrite <- Heq.
  repeat (rewrite Mem.get_upd_diff; [ | trivial]).
  rewrite H; [ | auto with set]; trivial.

  repeat rewrite Mem.get_upd_same.
  rewrite Mem.get_upd_diff, BVxor_comm, H; trivial.
  auto with set.

  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold upd_para, Meq, andR; intros k m1 m2 (H1, H2).
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op. 
  intros ? ? Hn; Vset_mem_inversion Hn.
  rewrite <- Heq, Mem.get_upd_diff, Mem.get_upd_same; trivial.
  auto.
  rewrite <- Heq0, Mem.get_upd_same, Mem.get_upd_diff, H2, (H1 _ z).
  rewrite BVxor_assoc, BVxor_nilpotent, BVxor_0_r; trivial.
  auto with set.  
  trivial.
  rewrite <- Heq1.
  repeat (rewrite Mem.get_upd_diff; [ | trivial]).
  rewrite H1; [ | auto with set]; trivial.
 Qed.


 Lemma Zq_padding  : forall E1 E2
  (x y:Var.var T.Nat) (u:E.expr T.Nat),
  Var.mkV x <> Var.mkV y ->
  ~ Vset.mem x (fv_expr u) ->
  ~ Vset.mem y (fv_expr u) ->
  equiv
  (req_mem_rel (fv_expr u) (EP2 (0 << u !<! q))) 
  E1 [ x <$- [1..q-1]; y <- (u *! x) mod_q ]
  E2 [ y <$- [1..q-1]; x <- (u^-1 *! y) mod_q]
  (kreq_mem (Vset.union (fv_expr u) {{x,y}})).
 Proof.
  intros E1 E2 x y u Hxy Hxu Hyu.
  apply equiv_cons with 
   (req_mem_rel (fv_expr u) ((EP2 (0 << u !<! q)) /-\
     (fun k m1 m2 => m2 y = E.eval_expr ((u *! x) mod_q) m1 /\
       m1 x = E.eval_expr ((u^-1 *! y) mod_q) m2))).

  eapply equiv_strengthen; [ | apply equiv_random_permut with 
   (f:=fun k (m1 m2:Mem.t k) n => ((E.eval_expr (u^-1) m1) * n) mod (Par.q k)) ].
  intros k m1 m2 [H1 H2]; repeat split.

    unfold permut_support; apply (Permut_Mod_Prime (q_prime _)).
    change (0 < inv_mod (Par.q k) (E.eval_expr u m1) < (Par.q k)); 
        rewrite  (depend_only_fv_expr u H1); split. 
    apply neq_0_lt; apply not_eq_sym; apply (inv_mod_neq_0_prime (q_prime _)).
    apply EP2_and_elim in H2; destruct H2 as [H21 H22]; unfold EP2 in *; rewrite <-eval_lt in *; auto.
    apply inv_mod_bound; generalize (p_bound (q_prime k)); auto with arith.

    apply req_mem_upd_notin; trivial.

    unfold EP2; rewrite (@depend_only_fv_expr T.Bool _  _ (m2 {!y <-- v!}) m2); trivial.
    apply req_mem_upd_notin_l.
    exact (req_mem_refl (fv_expr (0 << u !<! q)) m2).
    intro H'; elim Hyu; apply Vset.subset_correct with (2:=H').
    rewrite (fv_expr_andb (0 <! u) (u <! q)),
      VsetP.union_idem; auto with set.

    set (m' := (m1 {!x <-- (E.eval_expr (u ^-1) m1 * v) mod (Par.q k)!})).
    change (m2 {!y <-- v!} y = (E.eval_expr u m' * 
      (m1 {!x <-- ((inv_mod (Par.q k) (E.eval_expr u m1)) * v) mod (Par.q k)!}) x) mod (Par.q k)).
    rewrite Mem.get_upd_same, Mem.get_upd_same, (@depend_only_fv_expr T.Nat  u  _ m' m1); [ | 
      refine (req_mem_upd_notin_l _ (req_mem_refl _ _) Hxu) ].
    apply EP2_and_elim in H2; destruct H2 as [H21 H22]; unfold EP2 in *; rewrite <-eval_lt in *.    
    rewrite <-(@mod_small (E.eval_expr u m1) (Par.q k)) at 1; [ rewrite <-mult_mod | ].
    rewrite mult_assoc, mult_mod, inv_mod_prime, mult_1_l, mod_mod.
    symmetry; apply mod_small; apply In_seq_le in H; omega.
    apply q_prime.
    rewrite (depend_only_fv_expr u H1); auto.
    rewrite (depend_only_fv_expr u H1); auto with arith.


    mem_upd_simpl; expr_simpl; change ( (inv_mod (Par.q k) (@E.eval_expr k T.Nat u m1) * v) 
      mod (Par.q k) = (inv_mod (Par.q k) (@E.eval_expr k T.Nat u (m2 {!y <-- v!})) * v) mod (Par.q k)). 
    rewrite (@depend_only_fv_expr T.Nat  u  _ (m2 {!y <-- v!}) m1); trivial.
    apply req_mem_trans with m2.
       refine (req_mem_upd_notin_l _ (req_mem_refl _ _) Hyu).
       apply (req_mem_sym H1).

  eapply equiv_strengthen; [ | apply equiv_assign ].
  intros k m1 m2 [H1 [H2 [H3 H4] ] ]; unfold upd_para.
  apply req_mem_union.
    apply (req_mem_upd_notin _ _ H1 Hyu Hxu).
    intros t z Hz.
    Vset_mem_inversion Hz; subst.
    rewrite Mem.get_upd_same, (Mem.get_upd_diff _ _ (not_eq_sym Hxy)); assumption.
    rewrite Mem.get_upd_same, (Mem.get_upd_diff _ _ Hxy); symmetry; assumption.
 Qed.

 Lemma G1_padding : forall E1 E2
  (P R:Var.var (T.User G1)) (x y:Var.var (T.Nat)),
  Var.mkV R <> Var.mkV P ->
  Var.mkV y <> Var.mkV x ->
 equiv
  (req_mem_rel {{R,y}}
    (EP2 (0 << y !<! q) /-\ EP1 (!(log R =?= 0%nat))))
  E1 [ P <$- G1o; x <- (y^-1 *! ((log P) *! ((log R)^-1))) mod_q ]
  E2 [ x <$- [1..q-1]; P <- (y *! x) |.| R ]
  (kreq_mem (Vset.union {{R, y}} {{P,x}})).
 Proof.
  intros.
  apply equiv_cons with 
   (req_mem_rel  {{R,y}}  
     (EP2 (0 << y !<! q) /-\ EP1 (0%nat <! log R)  /-\
     (fun k m1 m2 => m2 x = E.eval_expr ((y^-1 *! ((log P) *! ((log R)^-1))) mod_q) m1 /\
       m1 P = E.eval_expr ( (y *! x) |.| R) m2))).
  
  eapply equiv_strengthen; [ | eapply equiv_random_permut_gen with 
   (f:=fun k (m1 m2:Mem.t k) (n:nat) => E.eval_expr ( (y *! n) |.| R) m1) ].
  intros k m1 m2 [HS [HI1 HI2] ].
  assert (H'': negb (nat_eqb (E.eval_expr (log R) m1) (0%nat))) by
      apply HI2; clear HI2; rename H'' into HI2. 
  split; [ | split; [ | split; [ | split; [ | split] ] ] ].

    (* 1st *)
    change (EP2 (0 << y !<! q) k m1 m2) in HI1; apply EP2_and_elim in HI1; 
      destruct HI1 as [H11 H12]; unfold EP2 in *; rewrite <-eval_lt in *.
    simpl; unfold O.eval_op; simpl.
    unfold permut_support; simpl; unfold G1_support, Zq_support.
    apply PermutP_sym; rewrite <-PermutP_map; apply PermutP_sym.
    apply PermutP_weaken with (fun b a => b =  
      ((E.eval_expr y m1 * (G1.log (E.eval_expr R m1))) mod (Par.q k) * a) mod (Par.q k)).
    set (v1:=E.eval_expr y m1); set (v2:=E.eval_expr R m1); intros a b Ha Hb Hab.
    rewrite (f_equal (G1.pow (G1.g k)) Hab).
    transitivity (G1.pow (G1.g k) (((G1.log v2) * (v1 * b)) mod (Par.q k))).
      apply f_equal; rewrite (mult_mod v1), mult_mod, mod_mod, <-(mod_mod b), 
        <-mult_mod, (mult_comm (v1 mod _)), <-mult_assoc, mult_mod, mod_mod, 
        <-(mod_mod ((v1 mod _ * _))), <-(mod_mod (G1.log v2)), 
        <-mult_mod, <-(mult_mod v1 b), <-mult_mod; trivial.
      rewrite <-G1_order, <-G1.pow_mod, <-G1.pow_pow, <-G1.log_spec; trivial.
    assert (Haux: 0 < (E.eval_expr y m1 * G1.log (E.eval_expr R m1)) mod (Par.q k) < (Par.q k)).
      split.
        apply neq_0_lt; apply not_eq_sym; apply mod_mult_neq_0_prime.
          apply q_prime.
          rewrite (@depend_only_fv_expr _ y _ m1 m2); [ split; trivial |
            apply req_mem_weaken with (2:=HS); auto with set ].
          split.
            change (0 < E.eval_expr (log R) m1); apply neq_0_lt; intro H'.
            rewrite <-H', nat_eqb_refl in HI2; discriminate.
            rewrite <-G1_order; apply G1.log_lt.
        apply mod_lt; rewrite <-G1_order; apply G1.order_neq_0.
    apply Permut_Mod_Prime; [ apply q_prime | apply Haux ].

    (* 2nd *)
    apply req_mem_upd_notin; trivial;
      intros H'; Vset_mem_inversion2 H'.

    (* 3rd *)
    unfold EP2 in *.
    rewrite (@depend_only_fv_expr _ (0 << y !<! q) _ _ m2); [ trivial |
      apply (req_mem_upd_notin_l _ (req_mem_refl _ _))  ].
    intro H'.
    apply Vset.subset_correct with (s2:=Vset.singleton y) in H'.
    apply Vset.singleton_complete in H'; 
    injection H'; intro H2; apply T.inj_pairT2 in H2;
      elim H0; subst; auto.
    rewrite (fv_expr_andb (0 <! y) (y <! q)),
      VsetP.union_idem; auto with set.

    (* 4th *)
    unfold EP1.
    rewrite (@depend_only_fv_expr _ (0 <! (log R)) _ _ m1). 
    Focus 2.
      refine (req_mem_upd_notin_l _ (req_mem_refl (fv_expr (0 <! (log R))) m1) _). 
      intro H'.
      apply Vset.subset_correct with (s2:=Vset.singleton R) in H';
        [ | apply VsetP.subset_refl ].
      apply Vset.singleton_complete in H';
        injection H'; intro H2; apply T.inj_pairT2 in H2;
          elim H; subst; auto.
    apply (leb_correct (0+1) (E.eval_expr (log R) m1)); simpl plus;
    cut (0 <> E.eval_expr (log R) m1); [ omega | intro H' ].
    rewrite <-H', nat_eqb_refl in HI2; discriminate.

    (* 5th *)
    apply In_seq_le in H1.
    change (EP2 (0 << y !<! q) k m1 m2) in HI1; apply EP2_and_elim in HI1; 
      destruct HI1 as [H11 H12]; unfold EP2 in *; rewrite <-eval_lt in *.
    simpl; unfold O.eval_op; simpl; mem_upd_simpl.
    rewrite (@Mem.get_upd_diff _ m1); [ | auto using not_eq_sym  ].
    rewrite G1.log_pow, G1_order, mult_mod.
    match goal with |- _ = (_ * ?X) mod _ => replace X with ((E.eval_expr y m1 * v) mod (Par.q k)) end.
    rewrite <-mult_mod, mult_comm, <-(mult_comm v), <-mult_assoc, 
      mult_mod,inv_mod_prime, mult_1_r, mod_mod.
      symmetry; apply mod_small; omega.
      apply q_prime.
      rewrite (HS _ y); [ split; trivial | apply Vset.add_complete;
        apply Vset.add_correct;  apply VarP.Edec.eq_refl ].
    assert (Haux: 0 < G1.log (m1 R) < (Par.q k)).
      split.
        change (0 < E.eval_expr (log R) m1); apply neq_0_lt; intro H'.
        rewrite <-H', nat_eqb_refl in HI2; discriminate.
        rewrite <-G1_order; apply G1.log_lt.
    rewrite (mult_mod (_ * _) (G1.log (m1 R))),  <-(mod_small (inv_mod _ (G1.log _)) (Par.q k)), 
      <-mult_mod, (mod_small  (G1.log (m1 R))), <-mult_assoc; try split; try auto with arith.
    rewrite (mult_mod _ (_ * _)), mod_mod, inv_mod_prime, mult_1_r, mod_mod; trivial.
      apply q_prime.
      apply (proj2 Haux).
      apply inv_mod_bound; rewrite <-G1_order; apply G1.order_neq_0.

    (* 6th *)
    mem_upd_simpl; simpl; unfold O.eval_op; simpl; mem_upd_simpl.
    rewrite (HS _ R); [ | auto with set ].
    rewrite (HS _ y); [ | apply Vset.add_complete;
        apply Vset.add_correct;  apply VarP.Edec.eq_refl ].
    rewrite (@Mem.get_upd_diff _ m2); auto using not_eq_sym.
 
  eapply equiv_strengthen; [ | apply equiv_assign ].
  intros k m1 m2 [H1 [_ [_ [H2 H3] ] ] ]; unfold upd_para.
  apply req_mem_union.
    apply req_mem_upd_notin; trivial.
      intros H'; Vset_mem_inversion2 H'.
      intros H'; Vset_mem_inversion2 H'.
    intros t z Hz.
    Vset_mem_inversion Hz.
    rewrite <-Heq, Mem.get_upd_diff, Mem.get_upd_same; trivial; discriminate.
    rewrite <-Heq0, Mem.get_upd_same, Mem.get_upd_diff; [ symmetry; trivial |
      discriminate].
  Qed.
  
End SAMPLING_FACTS.


Section PR_RANDOM_DOM.
 
 Variable c : cmd.
 Variable t1 : T.type.
 Variable t2 : T.type.

 Variable expr : E.expr t1.
 Variable n : nat -> nat.

 Variable i : Var.var T.Nat.
 Variable x : Var.var t1.
 Variable L : Var.var (T.List (T.Pair t1 t2)).
 
 Variable E : env.
 
 Hypothesis fv_x : ~Vset.mem x (fv_expr expr).
 Hypothesis fv_i : ~Vset.mem i (fv_expr expr).

 Let c' := c ++ [ i <$- [0..Elen L]; x <- Efst (Enth {i, L}) ].

 Close Scope nat_scope.
 Open Scope U_scope.

 Lemma Pr_random_dom : forall k (m:Mem.t k),
  ([1/]1+pred (n k)) * Pr E c m (EP k (Elen L <! (n k)) [&&] EP k (expr in_dom L)) <=
  Pr E c' m (EP k (x =?= expr)).
 Proof.
  intros; unfold Pr, c'.
  rewrite <- (mu_stable_mult _ _ _), deno_app_elim.
  apply mu_monotonic; intro m'.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  unfold charfun, restr, EP, andP, andb, fone, fmult.
  case_eq (@E.eval_expr _ T.Bool (Elen L <! n k) m');
   case_eq (@E.eval_expr _ T.Bool (expr in_dom L) m'); Usimpl; trivial.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  intros Hin Hlen.
  apply leb_complete in Hlen; simpl in Hlen.
  apply is_true_existsb in Hin; destruct Hin as [a [Hin Heq] ].
  simpl in Hin.
  destruct (In_nth_inv _ (T.default k (T.Pair t1 t2)) _ Hin) as [j [Hlt Hnth] ].  
  rewrite <- (@sum_support_in _ _ j).
  simpl; rewrite seq_length; unfold O.eval_op; simpl.
  apply Unth_anti_mon; omega.  
  apply le_In_seq; simpl; unfold O.eval_op; simpl in Hlt |- *; auto with arith.
 
  rewrite deno_assign_elim.
  rewrite Mem.get_upd_same.
  simpl; unfold O.eval_op; simpl; mem_upd_simpl.
  rewrite (@depend_only_fv_expr _ _ _ _ m').
  apply is_true_Ti_eqb in Heq; rewrite Heq, Hnth, Ti_eqb_refl; trivial.

  intros ? y Hy.
  repeat rewrite Mem.get_upd_diff; trivial.
  intro H; rewrite H in fv_i; tauto.
  intro H; rewrite H in fv_x; tauto.
 Qed.

End PR_RANDOM_DOM.
