(** * Types.v : Standard types and user-defined types *)

Set Implicit Arguments.

Require Export BaseDef.
Require Export Dlist.
Require Export CCMisc.


Open Scope nat_scope.

(** Polynomials *)
Module Type POLYNOMIALS.

 Parameter polynomial : Type.

 Parameter pcst :> nat -> polynomial.
 Parameter pvar : polynomial.
 Parameter pplus : polynomial -> polynomial -> polynomial.
 Parameter pmult : polynomial -> polynomial -> polynomial.
 Parameter pcomp : polynomial -> polynomial -> polynomial.

 Parameter peval : polynomial -> nat -> nat.

 Coercion peval : polynomial >-> Funclass.

 Parameter pcst_spec : forall k n, peval (pcst k) n = k.
 
 Parameter pvar_spec : forall n, peval pvar n = n.

 Parameter pplus_spec : forall p1 p2 n, 
  peval (pplus p1 p2) n = peval p1 n + peval p2 n.

 Parameter pmult_spec : forall p1 p2 n, 
    peval (pmult p1 p2) n = peval p1 n * peval p2 n.

 Parameter pcomp_spec : forall (p q : polynomial) n,
   peval (pcomp p q) n = peval p (peval q n).

 Parameter polynomial_bounded :
  forall p, exists k, forall n, 2 <= n -> peval p n <= n ^ k.

 Parameter peval_monotonic : forall (p : polynomial) n1 n2,
   n1 <= n2 -> p n1 <= p n2.

End POLYNOMIALS.

Module Poly : POLYNOMIALS.

 Definition polynomial : Type := list (nat * nat).

 Definition pcst (c:nat) : polynomial := (c,0) :: nil.

 Definition pvar : polynomial := (1,1) :: nil. 

 Fixpoint mplus (c:nat) (k:nat) (p:polynomial) {struct p} : polynomial :=
  match p with
  | nil => (c,k) :: nil
  | (c',k') :: p' =>
   match nat_eqb k k' with
   | true => (c + c', k) :: p'
   | false => (c', k') :: mplus c k p'
   end
  end.
 
 Fixpoint pplus (p1 p2:polynomial) {struct p1} : polynomial :=
  match p1 with
  | nil => p2
  | (c,k) :: p' => mplus c k (pplus p' p2)
  end.

 Fixpoint mmult (c:nat) (k:nat) (p:polynomial) {struct p} : polynomial :=
  match p with
  | nil => nil
  | (c', k') :: p' => (c*c', k + k') :: mmult c k p'
  end.

 Fixpoint pmult (p1 p2:polynomial) {struct p1} : polynomial :=
  match p1 with
  | nil => nil
  | (c,k)::p => pplus (mmult c k p2) (pmult p p2)
  end.
  
 Fixpoint ppow (p : polynomial) (n : nat) {struct n} : polynomial :=
   match n with
     | 0 => pcst 1
     | S n' => pmult p (ppow p n')
   end.

 Fixpoint pcomp (p q : polynomial) : polynomial :=
   match p with
     | nil => nil
     | (c,k)::p' => pplus (pmult (pcst c) (ppow q k)) (pcomp p' q) 
   end.

 Fixpoint peval (p:polynomial) (n:nat) {struct p} : nat :=
  match p with
  | nil => 0
  | (c,k) :: p' => c * n ^ k + peval p' n
  end.

 Lemma pcst_spec : forall k n, peval (pcst k) n = k.
 Proof.
  intros; simpl; ring.
 Qed.
 
 Lemma pvar_spec : forall n, peval pvar n = n.
 Proof.
  intros; simpl; ring.
 Qed.

 Lemma peval_mplus : forall c k p n,
  peval (mplus c k p) n = c * n ^ k + peval p n.
 Proof.
  induction p; simpl.
  intros; ring.
  intros; destruct a.
  case_eq (nat_eqb k n1); intro Heq.
  rewrite (nat_eqb_true Heq); simpl; ring.
  simpl; rewrite IHp; ring.
 Qed.

 Lemma pplus_spec : forall p1 p2 n, 
  peval (pplus p1 p2) n = peval p1 n + peval p2 n.
 Proof.
  induction p1; simpl.
  trivial.
  intros; destruct a; rewrite peval_mplus, IHp1; simpl; ring.
 Qed.

 Lemma peval_mmult : forall c k p n,
   peval (mmult c k p) n = (c*n^k)*peval p n.
 Proof.
  induction p; simpl; intros.
  ring.
  destruct a; simpl.
  rewrite IHp, <- pow_mult_plus; ring.
 Qed.

 Lemma pmult_spec : forall p1 p2 n,
   peval (pmult p1 p2) n = peval p1 n * peval p2 n.
 Proof.
  induction p1; simpl; intros.
  trivial.
  destruct a.
  rewrite pplus_spec, peval_mmult, IHp1; ring.
 Qed.

 Lemma ppow_spec : forall p k n,
   peval (ppow p k) n = (peval p n) ^ k.
 Proof.
  induction k; simpl; intros; trivial.
  rewrite pmult_spec, IHk; trivial.
 Qed.

 Lemma pcomp_spec : forall (p q : polynomial) n,
   peval (pcomp p q) n = peval p (peval q n).
 Proof.
   induction p; simpl; intros; trivial.
   destruct a as (c, k).
   rewrite pplus_spec, pplus_spec, peval_mmult, ppow_spec, IHp; simpl; ring.
 Qed.

 Lemma polynomial_bounded :
  forall p, exists k, forall n, 2 <= n -> peval p n <= n ^ k.
 Proof.
  induction p; intros; simpl.
  exists 0; intros; simpl; auto.

  destruct a as (c, k0).
  destruct IHp as [k Hle].
  destruct (pow_2_le c) as [kc Hc].
  exists (S (Max.max (kc + k0) k)); intros n Hn.
  apply le_trans with (2 ^ kc * n ^ k0 + n ^ k).
  apply plus_le_compat; [ | auto].
  apply mult_le_compat; trivial.
  
  apply le_trans with (n ^ kc * n ^ k0 + n ^ k).
  apply plus_le_compat; [ | trivial].
  apply mult_le_compat; [ | trivial].
  apply pow_monotone_1; trivial.

  apply le_trans with (2 * n ^ (Max.max (kc + k0) k)).
  apply le_trans with (n ^ Max.max (kc + k0) k + n ^ Max.max (kc + k0) k).
  rewrite pow_mult_plus.
  apply plus_le_compat.
  apply pow_monotone_2; auto with arith.
  apply pow_monotone_2; auto with arith.
  omega.
  apply mult_le_compat; trivial.  
 Qed.

 Lemma peval_monotonic : forall (p : polynomial) n1 n2,
   n1 <= n2 -> peval p n1 <= peval p n2.
 Proof.
  induction p; simpl; intros; auto.
  destruct a.
  apply plus_le_compat; auto.
  apply mult_le_compat; auto.
  apply pow_monotone_1; trivial.
 Qed.

End Poly.

Export Poly.

Lemma pplus_assoc : forall p q r k,
 peval (pplus (pplus p q) r) k = peval (pplus p (pplus q r)) k.
Proof.
 intros p q r k.
 rewrite (pplus_spec (pplus p q) r).
 rewrite (pplus_spec p q).
 rewrite <- plus_assoc.
 repeat rewrite <- pplus_spec; trivial.
Qed.

Lemma pplus_comm : forall p q k,
 peval (pplus p q) k = peval (pplus q p) k.
Proof.
 intros p q k.
 rewrite pplus_spec.
 rewrite plus_comm.
 rewrite <- pplus_spec; trivial.
Qed.
 
Lemma pplus_le_l : forall p1 p2 n, peval p1 n <= peval (pplus p1 p2) n.
Proof.
 intros; rewrite pplus_spec; auto with arith.
Qed.

Lemma pplus_le_r : forall p1 p2 n, peval p2 n <= peval (pplus p1 p2) n.
Proof.
 intros; rewrite pplus_spec; auto with arith.
Qed.

(** [size_nat] definition *)

Fixpoint log_inf (p:positive) : nat :=
 match p with
 | xH => O
 | xO q => S (log_inf q)
 | xI q => S (log_inf q)
 end.

Fixpoint log_sup (p:positive) : nat :=
 match p with
 | xH => O
 | xO q => S (log_sup q)
 | xI q => S (S (log_inf q))
 end.

Lemma log_inf_monotonic : forall (p q:positive), (p <= q)%positive ->
 log_inf p <= log_inf q.
Proof.
 unfold Ple; induction p; destruct q; simpl; intros; auto using le_n_S with arith.
 apply le_n_S; apply IHp; intro; apply H.
 case_eq ((p ?= q)%positive Gt); intros; trivial.
 destruct (Pcompare_not_Eq p q).
 elim (H2 H1).
 apply Pcompare_Gt_Lt in H1; rewrite H1 in H0; trivial.
 elim H; trivial.
 apply le_n_S; apply IHp; intro; apply H.
 rewrite <- Pcompare_eq_Gt; trivial.
 elim H; trivial.
Qed.

Lemma log_sup_inf_monotonic :forall p q, 
 (p ?= q)%positive Eq = Lt ->
 S (log_inf p) <= log_sup q.
Proof.
 induction p; destruct q; simpl; intros H; try discriminate H; auto with arith.
 apply le_n_S; apply le_n_S; apply log_inf_monotonic; unfold Ple; rewrite H; intro; discriminate.
 apply le_n_S; apply IHp.
 rewrite Pcompare_eq_Lt; trivial.
 apply le_n_S; apply le_n_S; apply log_inf_monotonic; unfold Ple.
 apply Pcompare_Lt_Lt in H; destruct H.
 rewrite H; intro; discriminate.
 rewrite H, Pcompare_refl; intro; discriminate.
Qed.

Lemma log_inf_le_log_sup : forall p, log_inf p <= log_sup p.
Proof.
 induction p; intros; simpl; auto with arith.
Qed.

Lemma log_sup_le_Slog_inf : forall p, log_sup p <= S (log_inf p).
Proof.
 induction p; intros; simpl; auto with arith.
Qed.

Lemma log_sup_monotonic : forall (p q:positive), (p <= q)%positive ->
 log_sup p <= log_sup q.
Proof.
 unfold Ple; induction p; destruct q; simpl; intros; 
  auto using le_n_S, log_inf_monotonic with arith.
 apply le_n_S.
 case_eq ((p ?= q)%positive Gt); intros Heq; rewrite Heq in H.
 destruct (Pcompare_not_Eq p q).
 elim (H0 Heq).
 rewrite <- Pcompare_eq_Lt in Heq.
 apply log_sup_inf_monotonic; trivial.
 elim H; trivial.
 elim H; trivial.
 apply le_n_S.
 apply le_trans with (2:= log_sup_le_Slog_inf q); auto with arith.
 apply IHp; intro; apply H; rewrite <- Pcompare_eq_Gt; trivial.
 elim H; trivial.
Qed.

Definition size_nat (n:nat) : nat := 
 match n with
 | O => S O
 | _ => log_sup (P_of_succ_nat n)
 end.

Lemma size_nat_double : forall n, 
 0 < n -> size_nat (2 * n) = S (size_nat n).
Proof.
 intros n Hn.
 destruct n; simpl; auto with arith.
 clear; rewrite plus_0_r, <- plus_n_Sm; simpl.
 rewrite ZL3.
 induction (P_of_succ_nat n); simpl.
 apply eq_S; rewrite <- IHp; trivial.
 trivial.
 trivial.
Qed.

Lemma size_nat_monotonic : forall n p,
 n <= p -> 
 size_nat n <= size_nat p.
Proof.
 intros n p; case n; case p; intros.
 trivial.
 simpl.
 apply le_trans with (log_sup (P_of_succ_nat (S O))).
 trivial.
 apply log_sup_monotonic.
 simpl; intro.
 apply nat_of_P_gt_Gt_compare_morphism in H0.
 rewrite nat_of_P_succ_morphism, nat_of_P_o_P_of_succ_nat_eq_succ in H0.
 unfold nat_of_P in H0; simpl in H0; omega.
 omega.
 simpl; apply log_sup_monotonic; intro.
 apply nat_of_P_gt_Gt_compare_morphism in H0.
 repeat rewrite nat_of_P_succ_morphism, nat_of_P_o_P_of_succ_nat_eq_succ in H0; omega.
Qed.

Lemma size_nat_positive : forall n, 0 < size_nat n.
Proof.
 induction n.
 auto.
 apply lt_le_trans with (size_nat n).
 trivial.
 apply size_nat_monotonic; apply le_S; trivial.
Qed.

Lemma size_nat_plus_max : forall n m, n <= m -> size_nat (n + m) <= S (size_nat m).
Proof.
 intros; apply le_trans with (size_nat (2 * m)).
 apply size_nat_monotonic; omega.
 destruct m.
 simpl; auto with arith.
 rewrite size_nat_double; auto with arith.
Qed.

Lemma size_nat_plus : forall n m, size_nat (n + m) <= size_nat n + size_nat m.
Proof.
 intros n m.
 destruct (le_lt_dec n m).
 apply le_trans with (1 := size_nat_plus_max l).
 assert (W:= size_nat_positive n); omega.
 assert (m <= n) by omega; clear l.
 rewrite plus_comm, (plus_comm (size_nat n)).
 apply le_trans with (1 := size_nat_plus_max H).
 assert (W:= size_nat_positive m); omega.
Qed.

Fixpoint Ppow2 (n:nat) := match n with O => xH | S n => xO (Ppow2 n) end.

Lemma Ppow2_lt_compat : forall n m, n < m -> (Ppow2 n < Ppow2 m)%positive.
Proof.
 induction n; destruct m; simpl; intros.
 elimtype False; omega.
 red; trivial.
 elimtype False; omega.
 refine (IHn _ _); omega.
Qed.

Lemma Ppow2_monotonic : forall n m, n <= m -> (Ppow2 n <= Ppow2 m)%positive.
Proof.
 induction n; destruct m; simpl; intros.
 discriminate.
 discriminate.
 elimtype False; omega.
 refine (IHn _ _); omega.
Qed.

Lemma log_inf_pow : forall n, (Ppow2 (log_inf n) <= n < Ppow2 (S (log_inf n)))%positive.
Proof.
 induction n.
 destruct IHn; split.
 unfold Ple in *; simpl; intro; apply H.
 apply Pcompare_Lt_Gt; trivial.
 change ((n ?= (Ppow2 (log_inf n~1)))%positive Gt = Lt).
 rewrite <- Pcompare_eq_Lt; exact H0.
 exact IHn.
 unfold Ple, Plt; simpl; split;[discriminate | trivial].
Qed.

Lemma log_sup_inf : forall p, log_sup p = log_inf p \/ log_sup p = S (log_inf p).
Proof.
 intros p; assert (W:= log_inf_le_log_sup p); assert (W':= log_sup_le_Slog_inf p).
 omega.
Qed.

Lemma log_pow_eq : forall n, log_sup n = log_inf n -> n = Ppow2 (log_sup n).
Proof.
 induction n; simpl; intros.
 elimtype False; omega.
 rewrite <- IHn; trivial.
 injection H; trivial.
 trivial.
Qed.

Lemma log_sup_pow : forall n, log_sup (Ppow2 n) = n.
Proof.
 induction n; simpl; trivial.
 rewrite IHn; trivial.
Qed.

Lemma log_pow : forall n, (n <= Ppow2 (log_sup n))%positive.
Proof.
 intros.
 assert (W:=log_inf_pow n).
 destruct (log_sup_inf n).
 rewrite <- (log_pow_eq _ H); intro H0; rewrite Pcompare_refl in H0; discriminate H0.
 destruct W.
 unfold Ple, Plt in *; rewrite H, H1; discriminate.
Qed.

Lemma nat_of_P_le_morphism : forall p q, Ple p q -> nat_of_P p <= nat_of_P q.
Proof.
 intros.
 assert (~ nat_of_P p > nat_of_P q);[ | omega].
 intro. 
 apply nat_of_P_gt_Gt_compare_complement_morphism in H0.
 apply (H H0).
Qed.

Lemma nat_of_P_le_complement_morphism : forall p q, nat_of_P p <= nat_of_P q -> Ple p q.
Proof.
 intros.
 intro.
 apply nat_of_P_gt_Gt_compare_morphism in H0; omega.
Qed.
 
Lemma Ppow2_mult_add : forall n m, (Ppow2 n * Ppow2 m = Ppow2 (n + m))%positive.
Proof.
 induction n; simpl; intros; trivial.
 rewrite IHn; trivial.
Qed.

Lemma log_sup_mult : forall n m, log_sup (n * m) <= log_sup n + log_sup m.
Proof.
 intros.
 apply le_trans with (log_sup (Ppow2 (log_sup n) * Ppow2 (log_sup m))).
 apply log_sup_monotonic.
 apply nat_of_P_le_complement_morphism.
 repeat rewrite nat_of_P_mult_morphism.
 apply mult_le_compat; apply nat_of_P_le_morphism; apply log_pow.
 rewrite Ppow2_mult_add, log_sup_pow; trivial.
Qed.

Lemma size_nat_mult : forall n m, size_nat (n * m) <= size_nat n + size_nat m.
Proof.
 intros n m.
 destruct n.
 simpl; auto with arith.
 destruct m.
 rewrite mult_0_r, plus_comm; simpl; auto with arith. 
 unfold size_nat.
 change (log_sup (P_of_succ_nat (S n * S m)) <=
   log_sup (P_of_succ_nat (S n)) + log_sup (P_of_succ_nat (S m))).
 apply le_trans with (log_sup (P_of_succ_nat (S n) * P_of_succ_nat (S m))).
 apply log_sup_monotonic; intro.
 apply nat_of_P_gt_Gt_compare_morphism in H.
 rewrite nat_of_P_mult_morphism in H.
 repeat rewrite nat_of_P_o_P_of_succ_nat_eq_succ in H.
 ring_simplify in H; omega.
 apply log_sup_mult.
Qed.

Lemma log_sup_le : forall p, log_sup (Psucc p) <= S (log_sup p).
Proof.
 induction p; simpl.
 apply le_trans with (S (S (log_sup p))).
 apply le_n_S; trivial.
 apply le_n_S; apply le_n_S; apply log_sup_le_Slog_inf.
 apply le_n_S; apply le_n_S; apply log_inf_le_log_sup.
 trivial.
Qed.

Lemma log_sup_le_S : forall p,
 log_sup p <= log_sup (Psucc p).
Proof.
 destruct p; simpl.
 apply le_n_S.
 induction p; simpl.
 apply le_n_S; trivial.
 trivial.
 trivial.
 apply le_n_S; apply log_sup_le_Slog_inf.
 apply le_S; trivial.
Qed.

Lemma log_sup_monotonic_P_of : forall p n,
 n <= p ->
 log_sup (P_of_succ_nat n) <= log_sup (P_of_succ_nat p).
Proof.
 induction p; intros n Hn; inversion_clear Hn.
 trivial.
 trivial.
 apply le_trans with (log_sup (P_of_succ_nat p)).
 apply IHp; trivial.
 simpl; apply log_sup_le_S.
Qed.

Lemma size_nat_le : forall n, 
 0 < n -> size_nat n <= n.
Proof.
 intro n; case n.
 intro Hn; trivial.  
 intros n0 _.
 unfold size_nat.
 induction (S n0).
 trivial.
 simpl.
 apply le_trans with (S (log_sup (P_of_succ_nat n1))).
 apply log_sup_le.
 apply le_n_S; trivial.
Qed.

Lemma size_nat_pow_2 : forall n, size_nat (2^n) = S n.
Proof.
 induction n.
 trivial.
 change (2 ^ (S n)) with (2 * 2 ^ n).
 rewrite size_nat_double.
 rewrite IHn; trivial.
 apply pow_lt_0; auto.
Qed.

(* REMARK: should add 1 to account for the sign *)
Definition size_Z (n:Z) : nat := size_nat (Zabs_nat n).

Lemma size_Z_positive : forall n, 0 < size_Z n.
Proof.
 unfold size_Z.
 intros.
 apply size_nat_positive.
Qed.


Section EQLIST.

 Variables (A:Type) (eqb : A -> A -> bool).

 Hypothesis eqb_spec : forall x y, if eqb x y then x = y else x <> y.

 Lemma eqb_list_spec : forall x y, if eqb_list eqb x y then x = y else x <> y.
 Proof.
  induction x; destruct y; simpl; trivial; try (intro; discriminate).
  generalize (eqb_spec a a0); destruct (eqb a a0); intros; subst.
  generalize (IHx y); destruct (eqb_list eqb x y); intros; subst; trivial.
  intros H1; apply H; inversion H1; trivial.
  intros H1; apply H; inversion H1; trivial.
 Qed.

 Hypothesis Aeq_dec : forall x y:A, {x = y} + {True}.
 Hypothesis Aeq_dec_r : forall x y i, Aeq_dec x y = right _ i -> x <> y.

 Fixpoint eq_dec_list (l1 l2 : list A) {struct l1} : {l1 = l2} + {True} :=
  match l1 as l1_0 return {l1_0 = l2} + {True} with
   | nil =>
    match l2 as l2_0 return {nil = l2_0} + {True} with
     | nil => left _ (refl_equal nil)
     | _ => right _ I
    end
   | a1::l1 => 
    match l2 as l2_0 return {a1::l1 = l2_0} + {True} with
     | nil => right _ I
     | a2::l2 =>
      match Aeq_dec a1 a2 with
       | left H =>
        match H in (_ = y0) return {a1::l1 = y0::l2} + {True} with
         | refl_equal =>
          match eq_dec_list l1 l2 with
           | left H =>
            match H in (_ = y0) return {a1::l1 = a1::y0} + {True} with
             | refl_equal => left _ (refl_equal (a1::l1))
            end
           | _ => right _ I
          end
        end
       | _ => right _ I
      end
    end
  end.

 Lemma eq_dec_list_r : forall x y i, eq_dec_list x y = right _ i -> x <> y.
 Proof.
  induction x; destruct y; simpl; intro i; try (intros; intro; discriminate).
  generalize (@Aeq_dec_r a a0); destruct (Aeq_dec a a0).
  case e.
  generalize (IHx y); destruct (eq_dec_list x y).
  case e0.
  intros; discriminate.
  case t; case i; intros; intro.
  apply (H I); trivial; inversion H2; trivial. 
  case t; case i; intros; intro.
  apply (H I); trivial; inversion H1; trivial.
 Qed.

End EQLIST.


(** * User-defined types *)
Module Type UTYPE.

 Parameter t : Type. 
 Parameter eqb : t -> t -> bool. 
 Parameter eqb_spec : forall x y, if eqb x y then x = y else x <> y.

 Parameter eq_dec : forall (x y:t), {x = y} + {True}.

 Parameter eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
 
 Parameter interp : nat -> t -> Type.

 Parameter size : forall k t, interp k t -> nat.

 Parameter default : forall k t, interp k t.

 Parameter default_poly : t -> polynomial.

 Parameter size_positive : forall k t (x:interp k t), 0 < size x.

 Parameter default_poly_spec : forall k t,
  size (default k t) <= peval (default_poly t) k.

 Parameter i_eqb : forall k t, interp k t -> interp k t -> bool.
 Parameter i_eqb_spec : forall k t (x y:interp k t), 
  if i_eqb x y then x = y else x <> y.

End UTYPE.


Module EmptyType <: UTYPE.

 Inductive t_ := .

 Definition t := t_.

 Definition eqb : t -> t -> bool := fun _ _ => true.

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  destruct x.
 Qed.

 Lemma eq_dec : forall (x y:t), {x = y} + {True}.
 Proof.
  destruct x.
 Qed.

 Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
 Proof.
  destruct x.
 Qed.

 Definition interp : nat -> t -> Type := fun _ _ => Datatypes.unit.

 Definition size : forall k t, interp k t -> nat := fun _ _ _ => O.

 Definition default : forall k t, interp k t := fun _ _ => tt.
 
 Definition i_eqb : forall k t, interp k t -> interp k t -> bool := 
  fun _ _ _ _  => true.

 Definition default_poly : t -> polynomial := fun _ => pcst O.

 Lemma size_positive :  forall k t (x:interp k t), 0 < size x.
 Proof.
  intros k t0; elim t0.
 Qed.

 Lemma default_poly_spec : forall k t,
  size (default k t) <= peval (default_poly t) k.
 Proof.
  intros k t0; elim t0.
 Qed.

 Lemma i_eqb_spec : forall k t (x y:interp k t),
  if i_eqb x y then x = y else x <> y.
 Proof.
  intros k t0 x y; case x; case y.
  simpl; trivial.
 Qed.

End EmptyType.


(** * Types *)
Module Type TYPE (UT:UTYPE).

 Inductive type : Type :=
 | User (ut:UT.t)
 | Unit  
 | Nat
 | Zt
 | Bool
 | List (t:type)
 | Pair (t1 t2:type)
 | Sum (t1 t2:type)
 | Option (t:type).

 Parameter eqb : type -> type -> bool.
 Parameter eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 
 Parameter eq_dec : forall (x y:type), {x = y} + {True}.
 Parameter eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.

 Section INTERP.

  Variable k:nat.

  Fixpoint interp (t : type) : Type :=
   match t with
    | User ut => UT.interp k ut
    | Unit => Datatypes.unit
    | Nat => nat
    | Zt => Z
    | Bool => bool
    | List t => list (interp t)
    | Pair t1 t2 => (interp t1 * interp t2)%type
    | Sum t1 t2 => (interp t1 + interp t2)%type
    | Option t => option (interp t) 
   end.
  
  Fixpoint type_op (dom:list type) (codom:type) {struct dom} : Type :=
   match dom with
    | nil => interp codom 
    | t1 :: dom => interp t1 -> type_op dom codom 
   end.

  Fixpoint ctype_op (dom:list type) (codom:type) {struct dom} : Type :=
   match dom with
    | nil => (interp codom * nat)%type 
    | t1 :: dom => interp t1 -> ctype_op dom codom 
   end.

  Fixpoint app_op (dom:list type) (codom:type) (op:type_op dom codom)
   (args:dlist interp dom) {struct args} : interp codom :=
   match args in (dlist _ dom0) return type_op dom0 codom -> interp codom with
   | dnil => fun (op:interp codom) => op
   | dcons t1 dom v args =>
     fun (op:type_op (t1::dom) codom) => app_op codom (op v) args
   end op.

  Fixpoint capp_op (dom:list type) (codom:type) (op:ctype_op dom codom)
   (args:dlist interp dom) {struct args} : interp codom * nat :=
   match args in (dlist _ dom0) return ctype_op dom0 codom -> interp codom * nat with
   | dnil => fun (op:interp codom * nat) => op
   | dcons t1 dom v args =>
     fun (op:ctype_op (t1::dom) codom) => capp_op codom (op v) args
   end op.

  Fixpoint default (t:type) {struct t} : interp t :=
   match t as t0 return interp t0 with
    | User ut => UT.default k ut
    | Unit => tt
    | Nat => 0%nat
    | Zt => 0%Z
    | Bool => false
    | List t1 => @nil (interp t1)
    | Pair t1 t2 => (default t1, default t2)
    | Sum t1 t2 => inl _ (default t1)
    | Option t => None
   end.

  Fixpoint default_poly (t:type) : polynomial :=
   match t with
    | User ut => UT.default_poly ut
    | Unit => 1
    | Nat => 1   
    | Zt => 1
    | Bool => 1
    | List _ => 1
    | Pair t1 t2 => pplus 1 (pplus (default_poly t1) (default_poly t2))
    | Sum t1 t2 => pplus 1 (default_poly t1)
    | Option t => 1
   end.

  Fixpoint size (t:type) {struct t} : interp t -> nat :=
   match t as t0 return interp t0 -> nat with
    | User ut => fun v => UT.size v
    | Unit => fun _ => 1
    | Nat => size_nat    
    | Zt => size_Z
    | Bool => fun _ => S O
    | List t1 => fun l => List.fold_right (fun v n => S (size t1 v + n)) 1 l
    | Pair t1 t2 => fun p => S (size t1 (fst p) + size t2 (snd p))%nat
    | Sum t1 t2 => fun s => 
       S (match s with inl x => size t1 x | inr y => size t2 y end)   
    | Option t => fun o => 
       match o with None => 1 | Some x => S (size t x) end 
   end.

 End INTERP.

 Parameter size_positive : forall k t (x:interp k t), 0 < size k t x.

 Parameter default_poly_spec : forall k t,
  size k t (default k t) <= peval (default_poly t) k.
 
 Parameter i_eqb : forall k t, interp k t -> interp k t -> bool.
 Parameter i_eqb_spec : forall k t (x y:interp k t), 
  if i_eqb k t x y then x = y else x <> y.

 (* Dependant equality *)
 Parameter eq_dep_eq : forall (P:type->Type) (p:type) (x y:P p), 
  eq_dep type P p x p y -> x = y.
 
 Parameter UIP_refl : forall (x:type) (p:x = x), p = refl_equal x.

 Parameter inj_pair2 : forall (P:type -> Type) (p:type) (x y:P p),
  existT P p x = existT P p y -> x = y.

 Parameter l_eq_dep_eq : forall (P : list type -> Type) 
  (p : list type) (x y : P p),
  eq_dep (list type) P p x p y -> x = y.

 Parameter l_inj_pair2 : forall (P : list type -> Type) 
  (p : list type) (x y : P p),
  existT P p x = existT P p y -> x = y.

 Parameter l_UIP_refl : forall (x : list type) (p : x = x), p = refl_equal x.


 Ltac dlist_inversion_aux l Heq :=
  let H := fresh "H" in
  let l1 := fresh "l" in
   match type of l with
   | dlist _ nil =>
     rewrite (l_eq_dep_eq (dlist_nil l)) in Heq
   | dlist _ (_::_) =>
     destruct (dlist_cons l) as [? [l1 H] ];
     rewrite (l_eq_dep_eq H) in Heq;
     clear H; dlist_inversion_aux l1 Heq; clear l1
   | _ => fail 1 "dlist_inversion : Unexpected type"
   end.

 Ltac dlist_inversion l :=
  let l' := fresh "l" in
  let Heq := fresh "Heq" in
   pose (l' := l);
   assert (Heq : l' = l) by (vm_cast_no_check (refl_equal l'));
   vm_compute in l;
   dlist_inversion_aux l Heq;
   unfold l' in Heq; clear l'.

End TYPE.


Module MakeType (UT:UTYPE) <: TYPE UT.

 Inductive type : Type :=
 | User (ut:UT.t)
 | Unit
 | Nat
 | Zt
 | Bool
 | List (t:type)
 | Pair (t1 t2:type)
 | Sum (t1 t2:type)
 | Option (t:type).

 Fixpoint eqb (x y : type) {struct x} : bool :=
  match x, y with
   | User ut1, User ut2 => UT.eqb ut1 ut2
   | Unit, Unit => true
   | Nat, Nat => true  
   | Zt, Zt => true 
   | Bool, Bool => true
   | List t1, List t2 => eqb t1 t2
   | Pair x1 x2, Pair y1 y2 => if eqb x1 y1 then eqb x2 y2 else false
   | Sum x1 x2, Sum y1 y2 => if eqb x1 y1 then eqb x2 y2 else false
   | Option x, Option y => eqb x y
   | _, _ => false
  end.

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  induction x; destruct y; simpl; intros; trivial; try (intro; discriminate).
  generalize (UT.eqb_spec ut ut0); destruct (UT.eqb ut ut0);
   intros; subst; trivial.
  intro H1; apply H; inversion H1; trivial.
  generalize (IHx y); destruct (eqb x y); intros; subst; trivial.
  intro H1; apply H; inversion H1; trivial.
  generalize (IHx1 y1); destruct (eqb x1 y1); intros; subst.
  generalize (IHx2 y2); destruct (eqb x2 y2); intros; subst; trivial.
  intro H1; apply H; inversion H1; trivial.   
  intro H1; apply H; inversion H1; trivial.   
  generalize (IHx1 y1); destruct (eqb x1 y1); intros; subst.
  generalize (IHx2 y2); destruct (eqb x2 y2); intros; subst; trivial.
  intro H1; apply H; inversion H1; trivial.   
  intro H1; apply H; inversion H1; trivial.   
  generalize (IHx y); destruct (eqb x y); intros; subst; trivial.
  intro H1; apply H; inversion H1; trivial.
 Qed.

 Definition eq_dec (x y:type) : {x = y} + {True}.
  induction x; destruct y;
  match goal with 
  | |- {?X _ _ = ?X _ _} + {True} => idtac
  | |- {?X _ = ?X _} + {True} => idtac
  | |- {?X = ?X} + {True} => left; apply refl_equal
  | _ => right; trivial
  end.
  case (UT.eq_dec ut ut0).
  intro Heq; rewrite Heq; left; trivial.
  right; trivial.  
  
  case (IHx y).
  intro Heq; rewrite Heq; left; trivial.
  right; trivial.

  case (IHx1 y1).
  intro Heq1; rewrite Heq1.
  case (IHx2 y2).
  intro Heq2; rewrite Heq2; left; trivial.     
  right; trivial.
  right; trivial.

  case (IHx1 y1).
  intro Heq1; rewrite Heq1.
  case (IHx2 y2).
  intro Heq2; rewrite Heq2; left; trivial.     
  right; trivial.
  right; trivial.

  case (IHx y).
  intro Heq; rewrite Heq; left; trivial.
  right; trivial.
 Defined.  
 
 Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
 Proof.
  induction x; destruct y; intros i; simpl; try (intros; intro; discriminate).
  case_eq (UT.eq_dec ut ut0); intros.
  clear H; generalize H0; case e; intros; discriminate.
  clear H0; assert (H0 := UT.eq_dec_r H).
  intros Heq; apply H0; inversion Heq; trivial.
  generalize (IHx y); destruct (eq_dec x y); intros; try discriminate.
  clear H; generalize H0; case e; intros; discriminate.
  generalize H; clear H; case t; intros.
  intros Heq; apply (H i); trivial; inversion Heq; trivial.
  case i; trivial.
  generalize (IHx1 y1); destruct (eq_dec x1 y1).
  case e.
  generalize (IHx2 y2); destruct (eq_dec x2 y2).
  case e0.
  intros; discriminate.
  case t; intros; intro.
  apply (H i); trivial; inversion H2; trivial.
  case i; trivial.
  case t; intros; intro.
  apply (H i); trivial; inversion H1; trivial.
  case i; trivial.
  generalize (IHx1 y1); destruct (eq_dec x1 y1).
  case e.
  generalize (IHx2 y2); destruct (eq_dec x2 y2).
  case e0.
  intros; discriminate.
  case t; intros; intro.
  apply (H i); trivial; inversion H2; trivial.
  case i; trivial.
  case t; intros; intro.
  apply (H i); trivial; inversion H1; trivial.
  case i; trivial.
  generalize (IHx y); destruct (eq_dec x y); intros; try discriminate.
  clear H; generalize H0; case e; intros; discriminate.
  generalize H; clear H; case t; intros.
  intros Heq; apply (H i); trivial; inversion Heq; trivial.
  case i; trivial.
 Qed.

 Section INTERP.

  Variable k:nat.

  Fixpoint interp (t : type) : Type :=
   match t with
    | User ut => UT.interp k ut
    | Unit => Datatypes.unit
    | Nat => nat
    | Zt => Z
    | Bool => bool
    | List t => list (interp t)
    | Pair t1 t2 => (interp t1 * interp t2)%type
    | Sum t1 t2 => (interp t1 + interp t2)%type
    | Option t => option (interp t) 
   end.
  
  Fixpoint type_op (dom:list type) (codom:type) {struct dom} : Type :=
   match dom with
    | nil => interp codom
    | t1 :: dom => interp t1 -> type_op dom codom 
   end.

  Fixpoint ctype_op (dom:list type) (codom:type) {struct dom} : Type :=
   match dom with
    | nil => (interp codom * nat)%type 
    | t1 :: dom => interp t1 -> ctype_op dom codom 
   end.

  Fixpoint app_op (dom:list type) (codom:type) (op:type_op dom codom)
   (args:dlist interp dom) {struct args} : interp codom :=
   match args in (dlist _ dom0) return type_op dom0 codom -> interp codom with
   | dnil => fun (op:interp codom) => op
   | dcons t1 dom v args =>
     fun (op:type_op (t1::dom) codom) => app_op codom (op v) args
   end op.

  Fixpoint capp_op (dom:list type) (codom:type) (op:ctype_op dom codom)
   (args:dlist interp dom) {struct args} : interp codom * nat :=
   match args in (dlist _ dom0) return ctype_op dom0 codom -> interp codom * nat with
   | dnil => fun (op:interp codom * nat) => op
   | dcons t1 dom v args =>
     fun (op:ctype_op (t1::dom) codom) => capp_op codom (op v) args
   end op.

  Fixpoint default (t:type) {struct t} : interp t :=
   match t as t0 return interp t0 with
    | User ut => UT.default k ut
    | Unit => tt
    | Nat => 0%nat
    | Zt => 0%Z
    | Bool => false
    | List t1 => @nil (interp t1)
    | Pair t1 t2 => (default t1, default t2)
    | Sum t1 t2 => inl _ (default t1)
    | Option t => None
   end.

  Fixpoint default_poly (t:type) : polynomial :=
   match t with
    | User ut => UT.default_poly ut
    | Unit => 1   
    | Nat => 1   
    | Zt => 1
    | Bool => 1
    | List _ => 1
    | Pair t1 t2 => pplus 1 (pplus (default_poly t1) (default_poly t2))
    | Sum t1 t2 => pplus 1 (default_poly t1)
    | Option t => 1
   end.

  Fixpoint size (t:type) {struct t} : interp t -> nat :=
   match t as t0 return interp t0 -> nat with
    | User ut => fun v => UT.size v
    | Unit  => fun _ => 1
    | Nat => size_nat    
    | Zt => size_Z
    | Bool => fun _ => S O
    | List t1 => fun l => List.fold_right (fun v n => S (size t1 v + n)) 1 l
    | Pair t1 t2 => fun p => S (size t1 (fst p) + size t2 (snd p))%nat
    | Sum t1 t2 => fun s => 
       S (match s with inl x => size t1 x | inr y => size t2 y end)   
    | Option t => fun o => 
       match o with None => 1 | Some x => S (size t x) end 
   end.
  
  Fixpoint i_eqb (t:type) {struct t} : interp t -> interp t -> bool :=
   match t as t0 return interp t0 -> interp t0 -> bool with
    | User ut => @UT.i_eqb k ut
    | Unit => fun _ _ => true
    | Nat => nat_eqb
    | Zt => Zeq_bool
    | Bool => Bool.eqb 
    | List t1 => eqb_list (i_eqb t1) 
    | Pair t1 t2 => 
      fun (v1 v2:interp t1 * interp t2) =>
       if i_eqb t1 (fst v1) (fst v2) then i_eqb t2 (snd v1) (snd v2) else false
    | Sum t1 t2 =>
      fun (v1 v2:interp t1 + interp t2) =>
       match v1, v2 with
       | inl x1, inl x2 => i_eqb t1 x1 x2
       | inr y1, inr y2 => i_eqb t2 y1 y2 
       | _, _ => false
       end
    | Option t =>
       fun v1 v2 =>
        match v1, v2 with 
        | None, None => true
        | Some x1, Some x2 => i_eqb t x1 x2
        | _, _ => false
        end 
   end. 

  Lemma i_eqb_spec : forall t (x y:interp t), 
   if i_eqb t x y then x = y else x <> y.
  Proof.
   induction t; simpl; intros.
   apply UT.i_eqb_spec.
   destruct x; destruct y; trivial.
   apply nat_eqb_spec.
   case_eq (Zeq_bool x y); intros.
   apply Zeq_bool_eq; exact H.
   apply Zeq_bool_neq; exact H.
   case_eq (Bool.eqb x y); intros.
   apply eqb_prop; trivial.
   intro; subst; rewrite eqb_reflx in H; discriminate.
   apply eqb_list_spec; auto.
   generalize (IHt1 (fst x) (fst y)); destruct (i_eqb t1 (fst x) (fst y));
    intros; subst.
   generalize (IHt2 (snd x) (snd y)); destruct (i_eqb t2 (snd x) (snd y));
    intros; subst; trivial.
   destruct x; destruct y; simpl in H, H0; subst; trivial.
   intro H1; apply H0; inversion H1; trivial.
   intro H1; apply H; inversion H1; trivial.

   destruct x as [x1 | y1]; destruct y as [x2 | y2].
   generalize (IHt1 x1 x2); destruct (i_eqb t1 x1 x2).
   intro; subst; trivial.   
   intros H0 H1; apply H0; injection H1; trivial.
   discriminate.
   discriminate.
   generalize (IHt2 y1 y2); destruct (i_eqb t2 y1 y2).
   intro; subst; trivial.   
   intros H0 H1; apply H0; injection H1; trivial.
   
   destruct x; destruct y.  
   generalize (IHt i i0); case (i_eqb t i i0). 
   intro; subst; trivial. 
   intros H0 H1; apply H0; injection H1; trivial.
   discriminate.
   discriminate.  
   trivial.
  Qed.

 End INTERP.

 Lemma size_positive :  forall k t (x:interp k t), 0 < size k t x.
 Proof.
  intros k t x.
  destruct t; simpl.
  apply UT.size_positive.
  auto.
  apply size_nat_positive.
  apply size_Z_positive.
  auto.
  induction x; simpl; auto with arith.
  auto with arith.
  auto with arith.
  case x; auto with arith.
 Qed.

 Lemma default_poly_spec : forall k t,
  size k t (default k t) <= peval (default_poly t) k.
 Proof.
  intros k t.
  induction t.
  simpl; apply UT.default_poly_spec.
  simpl; rewrite pcst_spec; trivial.
  simpl; rewrite pcst_spec; trivial.
  simpl; rewrite pcst_spec; trivial.
  simpl; rewrite pcst_spec; trivial.  
  simpl; rewrite pcst_spec; trivial.
  simpl; rewrite pplus_spec, pcst_spec, pplus_spec; simpl.
  apply le_n_S; apply plus_le_compat; trivial.
  simpl; rewrite pplus_spec, pcst_spec.
  apply le_n_S; trivial.
  simpl; rewrite pcst_spec; trivial.
 Qed.

 (** Dependant equality *) 
 Module Tdec <: DecidableType.

  Definition U := type.

  Lemma eq_dec : forall (t1 t2:type), {t1 = t2} + {t1 <> t2}.
  Proof.
   intros t1 t2; generalize (eqb_spec t1 t2); destruct (eqb t1 t2); auto.
  Qed.

 End Tdec.

 Include DecidableEqDepSet Tdec.
 

 Module LTdec <: DecidableType.

  Definition U := list type.

  Lemma eq_dec : forall (l1 l2:list type), {l1 = l2} + {l1 <> l2}.
  Proof.
   intros l1 l2; generalize (eqb_list_spec eqb eqb_spec l1 l2).
   destruct (eqb_list eqb l1 l2); auto.
  Qed.

 End LTdec.
 
 Module LTeqdep := DecidableEqDepSet LTdec.

 Lemma l_eq_dep_eq : forall (P : list type -> Type) (p : list type) (x y : P p),
  eq_dep (list type) P p x p y -> x = y.
 Proof LTeqdep.eq_dep_eq.
 
 Lemma l_inj_pair2 : forall (P : list type -> Type) (p : list type) (x y : P p),
  existT P p x = existT P p y -> x = y.
 Proof LTeqdep.inj_pair2.
 
 Lemma l_UIP_refl : forall (x : list type) (p : x = x), p = refl_equal x.
 Proof LTeqdep.UIP_refl.


 Ltac dlist_inversion_aux l Heq :=
  let H := fresh "H" in
  let l1 := fresh "l" in
   match type of l with
   | dlist _ nil =>
     rewrite (l_eq_dep_eq (dlist_nil l)) in Heq
   | dlist _ (_::_) =>
     destruct (dlist_cons l) as [? [l1 H] ];
     rewrite (l_eq_dep_eq H) in Heq;
     clear H; dlist_inversion_aux l1 Heq; clear l1
   | _ => fail 1 "dlist_inversion : Unexpected type"
   end.

 Ltac dlist_inversion l :=
  let l' := fresh "l" in
  let Heq := fresh "Heq" in
   pose (l' := l);
   assert (Heq : l' = l) by (vm_cast_no_check (refl_equal l'));
   vm_compute in l;
   dlist_inversion_aux l Heq;
   unfold l' in Heq; clear l'.

End MakeType.

Close Scope nat_scope.
