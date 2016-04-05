(** * Bitstrings.v : Bitstring type and operators *)

Require Export Bvector.
Require Export EqdepFacts.
Require Export Eqdep_dec.
Require Export Peano_dec.
Require Export BaseDef.
Require Export List.
Require Export Types.

Set Implicit Arguments.

(* Boolean equality on [Bvector k] *)
Fixpoint Veqb k (v1 v2:Bvector k) : bool :=
 match k as k0 return Bvector k0 -> Bvector k0 -> bool with
 | O => fun _ _ => true
 | S k0 => fun x1 x2 =>
   if Bool.eqb (Blow k0 x1) (Blow k0 x2) then
    Veqb (Bhigh k0 x1) (Bhigh k0 x2)
    else false
 end v1 v2.

Lemma Veqb_spec : forall k (v1 v2:Bvector k),
 if Veqb v1 v2 then v1 = v2 else v1 <> v2.
Proof.
 induction k; simpl; intros.
 rewrite (V0_eq bool v1), (V0_eq bool v2); trivial.
 rewrite (VSn_eq bool k v1); rewrite (VSn_eq bool k v2); simpl.
 case_eq (Bool.eqb (Vhead bool k v1) (Vhead bool k v2)).
 generalize (IHk (Vtail bool k v1) (Vtail bool k v2));
  destruct Veqb; intros.
 rewrite H, (eqb_prop _ _ H0); trivial.
 intro Heq; injection Heq; intros.
 apply H; apply (inj_pair2_eq_dec _ eq_nat_dec _ _ _ _ H1).
 intros H Heq; injection Heq; intros.
 rewrite H1 in H; rewrite eqb_reflx in H; discriminate.
Qed.

Lemma Veqb_sym : forall k (x y:Bvector k), Veqb x y = Veqb y x.
Proof.
 induction k; simpl; intros.
 trivial.
 rewrite eqb_sym; rewrite IHk; trivial.
Qed. 

Lemma Veqb_refl : forall k (x:Bvector k), Veqb x x.
Proof.
 induction k; simpl; intros.
 trivial.
 rewrite eqb_reflx; trivial.
Qed.

Lemma Veqb_true : forall k (x y:Bvector k), Veqb x y = true -> x = y.
Proof.
 intros; generalize (Veqb_spec x y); rewrite H; trivial.
Qed.


(** Support for uniform bitstring distribution *)
Fixpoint bs_support (k:nat) : list (Bvector k) :=
 match k as k0 return list (Bvector k0) with
 | O => Vnil bool :: nil
 | S k => 
   let l := bs_support k in
   map (Vcons bool false k) l ++
   map (Vcons bool true k) l 
 end.

Lemma bs_support_not_nil : forall k, bs_support k <> nil.
Proof.
 induction k; simpl.
 intro; discriminate.
 destruct (bs_support k).
 elim IHk; trivial.
 intro; discriminate.
Qed.

Lemma bs_length_add : forall k p, 
 length (bs_support (k + p)) = (length (bs_support k) * length (bs_support p))%nat.
Proof.
 induction k; simpl; intros.
 ring.
 repeat (rewrite app_length || rewrite map_length || rewrite IHk).
 fold Bvector; ring.
Qed.
  
Opaque Vextend.

Lemma bs_support_sum : forall k p f,
 mu (sum_support (Bvect_false (k+p)) (bs_support (k+p))) f ==
 mu (sum_support (Bvect_false k) (bs_support k))
 (fun v1 => mu (sum_support (Bvect_false p) (bs_support p))
  (fun v2 => f (Vextend bool k p v1 v2))).
Proof.
 intros; apply Oeq_trans with
  (finite_sum 
   (fun v1 => finite_sum 
    (fun a  => [1/]1+pred (length (bs_support (k+p))) * f (Vextend bool k p v1 a)) 
    (bs_support p)) (bs_support k)).
 change  (mu (sum_support (Bvect_false (k + p)) (bs_support (k + p))) f) with
  (sum_dom (Bvect_false (k + p)) (bs_support (k + p)) f).
 rewrite sum_dom_finite.
 fold (Bvector (k+p)); generalize k p (length (bs_support (k + p))) f; clear k p f.
 induction k; simpl; intros.
 Usimpl; apply finite_sum_Perm.
 apply PermutP_refl; intros; trivial.
 repeat rewrite finite_sum_app.
 repeat rewrite finite_sum_map.
 repeat rewrite IHk; trivial.
 change 
  (mu (sum_support (Bvect_false k) (bs_support k))
   (fun v1 : vector bool k =>
    mu (sum_support (Bvect_false p) (bs_support p))
    (fun v2 : vector bool p => f (Vextend bool k p v1 v2)))) with
  (sum_dom (Bvect_false k) (bs_support k)
   (fun v1 : vector bool k =>
    sum_dom (Bvect_false p) (bs_support p)
    (fun v2 : vector bool p => f (Vextend bool k p v1 v2)))).
 rewrite sum_dom_finite.
 apply finite_sum_Perm; apply PermutP_refl. intros v1 _.
 rewrite <- (sum_dom_stable_mult (Bvect_false p) (bs_support p) ([1/]1+pred (length (bs_support k)))).
 unfold fmult; rewrite sum_dom_finite.
 apply finite_sum_Perm; apply PermutP_refl; intros v2 _.
 rewrite Umult_assoc, Unth_prod.
 apply Umult_eq_compat_left.
 fold Bvector; rewrite <- (S_pred (length (bs_support p)) 0).
 rewrite <- (S_pred (length (bs_support k)) 0).
 rewrite mult_comm, bs_length_add; trivial.
 generalize (@bs_support_not_nil k); destruct (bs_support k); simpl; intros; auto with arith.
 elim H; trivial.
 generalize (@bs_support_not_nil p); destruct (bs_support p); simpl; intros; auto with arith.
 elim H; trivial.
Qed.

Lemma full_support : forall k (bs:Bvector k), In bs (bs_support k).
Proof.
 induction bs.
 left; trivial.
 simpl; apply in_or_app.
 destruct a;[right | left]; rewrite in_map_iff; exists bs; auto.
Qed.

Lemma bs_support_NoDup : forall k, NoDup (bs_support k).
Proof.
 induction k; simpl.
 constructor.
 intro; simpl; trivial. 
 constructor.
 apply NoDup_app.
 apply NoDup_map_inj; intros; trivial.
 change (Vtail _ _ (Vcons bool false k x) = Vtail _ _ (Vcons bool false k y)).
 rewrite H1; trivial.
 apply NoDup_map_inj; intros; trivial.
 change (Vtail _ _ (Vcons bool true k x) = Vtail _ _ (Vcons bool true k y)).
 rewrite H1; trivial.
 intros; intro.
 rewrite in_map_iff in H, H0.
 destruct H as (y1, (Heq1, _)); destruct H0 as (y2, (Heq2, _)); subst.
 inversion Heq2.
Qed.

Section FINV_SPEC.

 Variables (T : Type) (f f_inv : T -> T) (d : list T).

 Hypothesis f_perm :  PermutP (@eq _) d (map f d).

 Hypothesis f_spec : forall x, f_inv (f x) = x.

 Lemma f_inv_spec : forall x, In x d -> f (f_inv x) = x.
 Proof.
  intros. 
  assert (In x (map f d)).
  apply PermutP_In with (d1:=d); trivial.
  rewrite in_map_iff in H0. 
  destruct H0 as [y [Hy _] ].
  rewrite <- Hy, f_spec; trivial.
 Qed.

End FINV_SPEC.

Section FINV_SPEC_BS. 
 
 Variables (k : nat) (f f_inv : Bvector k -> Bvector k).

 Hypothesis f_perm : PermutP (@eq _) (bs_support k) (map f (bs_support k)).
 
 Hypothesis f_spec : forall x, f_inv (f x) = x.

 Lemma f_inv_spec_bs : forall x, f (f_inv x) = x.
 Proof.
  intros; apply f_inv_spec with (1:= f_perm); trivial.
  apply full_support.
 Qed.

End FINV_SPEC_BS. 


(* Lemmas about [BVxor] *) 
Lemma BVxor_comm : forall n v1 v2, BVxor n v1 v2 = BVxor n v2 v1.
Proof.
 intros; rewrite <- Ndigits.N2Bv_Bv2N, Ndigits.Nxor_BVxor, Ndigits.Nxor_comm.
 rewrite <- Ndigits.Nxor_BVxor, Ndigits.N2Bv_Bv2N; trivial.
Qed.

Lemma BVxor_assoc : forall n v1 v2 v3, BVxor n (BVxor n v1 v2) v3 = BVxor n v1 (BVxor n v2 v3).
Proof.
 intros; do 2 rewrite <- Ndigits.N2Bv_Bv2N, Ndigits.Nxor_BVxor.
 rewrite <- Ndigits.Nxor_assoc.
 do 2 rewrite <- Ndigits.Nxor_BVxor, Ndigits.N2Bv_Bv2N; trivial.
Qed.

Lemma Bv2N_Bvect_false : forall n, Ndigits.Bv2N _ (Bvect_false n) = N0.
Proof.
 induction n; simpl; trivial.
 unfold Bvect_false in IHn.
 rewrite IHn; trivial.
Qed.

Lemma BVxor_nilpotent : forall n v, BVxor n v v = Bvect_false n.
Proof.
 intros.
 rewrite <- Ndigits.N2Bv_Bv2N; symmetry; rewrite <- Ndigits.N2Bv_Bv2N, Ndigits.Nxor_BVxor.
 rewrite Ndigits.Nxor_nilpotent,Bv2N_Bvect_false; trivial.
Qed.

Lemma BVxor_0_l : forall n v, BVxor n (Bvect_false n) v = v.
Proof.
 intros; symmetry; rewrite <- Ndigits.N2Bv_Bv2N, Ndigits.Nxor_BVxor.
 rewrite Bv2N_Bvect_false,Ndigits.Nxor_neutral_left.
 symmetry; apply Ndigits.N2Bv_Bv2N.
Qed.

Lemma BVxor_0_r : forall n v, BVxor n v (Bvect_false n) = v.
Proof.
 intros; symmetry; rewrite <- Ndigits.N2Bv_Bv2N, Ndigits.Nxor_BVxor.
 rewrite Bv2N_Bvect_false,Ndigits.Nxor_neutral_right.
 symmetry; apply Ndigits.N2Bv_Bv2N.
Qed.

Lemma BVxor_bij : forall n (v x : vector bool n), BVxor n (BVxor n x v) v = x.
Proof.
 intros; rewrite BVxor_assoc, BVxor_nilpotent, BVxor_0_r; trivial.
Qed.

Lemma bs_support_length : forall k, length (bs_support k) = (2 ^ k)%nat.
Proof.
 induction k; simpl; trivial.
 rewrite app_length, map_length, map_length.
 unfold Bvector in *; rewrite IHk; ring.
Qed.

Lemma bs_support_pow : forall k,
 [1/]1+pred (length (bs_support k)) == [1/2]^k.
Proof.
 intros; rewrite bs_support_length.
 symmetry; apply Unth_pow.
Qed.

Lemma Pr_bs_support : forall k (default v:Bvector k) f,
 (forall x, x <> v -> f v x == 0) ->
 f v v == 1 ->
 mu (sum_support default (bs_support k)) (f v) == [1/2]^k.
Proof.
 Opaque sum_dom.
 intros; simpl.
 rewrite (sum_dom_finite default (bs_support k) (f v)).
 rewrite (@finite_sum_full _ v).
 rewrite H0; Usimpl; apply bs_support_pow.
 intros; rewrite H; auto. 
 apply full_support.
 apply bs_support_NoDup.
Qed.


Module NatDec.

 Definition U := nat.
 
 Lemma eq_dec : forall x y:U, {x = y} + {x <> y}.
 Proof. 
  unfold U; auto with arith. 
 Qed.

End NatDec.


Module NatEqDep := DecidableEqDep NatDec.

(** Lemmas about [Vextend] (concatenation of bitstrings) *)
Transparent Vextend.

Lemma Vextend_inj : forall n p (v1 v2 : vector bool n) (w1 w2 : vector bool p),
 Vextend bool n p v1 w1 = Vextend bool n p v2 w2 ->
 v1 = v2 /\ w1 = w2.
Proof.
 induction n; intros p v1 v2 w1 w2.
 rewrite (V0_eq bool v1), (V0_eq bool v2); simpl; auto.
 rewrite (VSn_eq bool n v1), (VSn_eq bool n v2); simpl; intros.
 injection H; clear H; intros.
 rewrite H0.
 destruct (IHn p (Vtail bool n v1)(Vtail bool n v2) w1 w2).
 rewrite (NatEqDep.inj_pairT2 _ _ _ _ H); trivial.
 rewrite H1, H2; auto.
Qed.

Lemma PermutP_bs_support_xor : forall n v, 
 PermutP (fun v1 v2 => v1 = BVxor n v2 v) (bs_support n) (bs_support n).
Proof.
 intros; apply PermutP_NoDup with (f_inv := fun v2 => BVxor n v2 v); intros.
 apply bs_support_NoDup.
 apply bs_support_NoDup.
 apply BVxor_bij.
 apply BVxor_bij.
 apply full_support.
 apply full_support.
Qed.

Opaque BVxor Vextend bs_support. 
