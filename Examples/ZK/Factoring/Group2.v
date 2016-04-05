(*
 * Copyright 2007-9 David Nowak, RCIS, AIST, Japan
 * All rights reserved
 *)

(** This file provides cyclic groups and their properties.
 *)

Require Import Classical FunctionalExtensionality.
Require Import Bool Arith Even Div2 Euclid Max Epsilon Coq.Lists.List.
Require Import MiscLogic MiscArith MiscLists.
Require Import Permutation.

Open Local Scope bool_scope.

Record Group : Type := {
  carrier :> Type ;
  eq_dec : forall a b:carrier, {a=b}+{a<>b} ;
  neutral : carrier ;
  mult : carrier -> carrier -> carrier ;
  inv : carrier -> carrier ;
  neutral_left : forall a, mult neutral a = a;
  neutral_right : forall a, mult a neutral = a;
  inv_left : forall a, mult (inv a) a = neutral;
  inv_right : forall a, mult a (inv a) = neutral;
  associative : forall a b c, mult a (mult b c) = mult (mult a b) c
}.

Definition T : Type :=
  Group.

Notation "a * b" :=
  (mult _ a b) : group_scope.

Notation "/ a" :=
  (inv _ a) : group_scope.

Open Local Scope group_scope.

Section Group.

Variable G : T.

Definition equal (a b:G) : bool :=
  if eq_dec _ a b then true else false.

Lemma equal_complete : forall a b, a=b -> equal a b = true.
Proof.
intros a b H.
unfold equal.
destruct (eq_dec _ a b).
reflexivity.
contradiction.
Qed.

Fixpoint power_nat (a:G)(n:nat) {struct n} : G :=
  match n with
  | O => neutral G
  | S n' => a * power_nat a n'
  end.

Notation "a ^ n" :=
  (power_nat a n) : group_scope.

Lemma neutral_power_nat : forall n, neutral G ^ n = neutral G.
Proof.
induction n as [ | n IHn].
reflexivity.
simpl.
rewrite IHn.
apply neutral_left.
Qed.

Lemma power_nat_1 : forall (a:G), a^1 = a.
Proof.
intro a.
simpl.
apply neutral_right.
Qed.

Lemma power_nat_plus : forall (a:G) m n,  a^(m+n) = a^m * a^n.
Proof.
intros a m.
induction m as [ | m IHm]; simpl; intro n.
rewrite neutral_left.
reflexivity.
rewrite IHm.
apply associative.
Qed.

Lemma power_nat_mult : forall (a:G) m n,  a^(m*n) = (a^m)^n.
Proof.
intros a m n.
revert m.
induction n as [ | n IHn]; simpl; intro m.
rewrite mult_0_r.
reflexivity.
rewrite <- IHn.
rewrite <- power_nat_plus.
f_equal.
ring.
Qed.

Lemma power_nat_comm : forall (a:G) m n, (a^m)^n = (a^n)^m.
Proof.
intro a.
induction m as [ | m IHm]; simpl; intro n.
apply neutral_power_nat.
rewrite <- (power_nat_1 a) at 1.
rewrite <- power_nat_plus.
do 2 rewrite <- power_nat_mult.
rewrite <- power_nat_plus.
f_equal.
ring.
Qed.

Lemma inv_inv : forall a:G, / / a = a.
Proof.
intro a.
transitivity (// a * /a * a).
rewrite <- associative.
rewrite inv_left.
rewrite neutral_right.
reflexivity.
cut (// a * /a = a * /a).
intro H.
rewrite H.
rewrite inv_right.
apply neutral_left.
rewrite inv_right.
apply inv_left.
Qed.

Lemma transpose_left : forall a b c:G, / b * a = c ->  a = b * c.
Proof.
intros a b c H.
rewrite <- H.
rewrite associative.
rewrite inv_right.
rewrite neutral_left.
reflexivity.
Qed.

Lemma transpose_right : forall a b c:G, a * / b = c ->  a = c * b.
Proof.
intros a b c H.
rewrite <- H.
rewrite <- associative.
rewrite inv_left.
rewrite neutral_right.
reflexivity.
Qed.

Lemma inv_mult : forall a b:G, / (a*b) = / b * / a.
Proof.
intros a b.
symmetry.
rewrite <- neutral_left.
apply transpose_right.
rewrite inv_inv.
rewrite <- associative.
rewrite (associative _ (/ a)).
rewrite inv_left.
rewrite neutral_left.
apply inv_left.
Qed.

Lemma power_nat_minus : forall (a:G) m n,  n<=m -> a^(m-n) = a^m * / (a^n).
Proof.
intros a m n H.
apply transpose_right.
rewrite inv_inv.
rewrite <- power_nat_plus.
auto with zarith.
Qed.

Lemma mult_left_inj : forall (a b c:G), c*a = c*b -> a=b.
Proof.
intros a b c H.
rewrite <- neutral_left.
rewrite <- (inv_left _ c).
rewrite <- associative.
apply transpose_left.
rewrite inv_inv.
assumption.
Qed.

Lemma mult_right_inj : forall (a b c:G), a*c = b*c -> a=b.
Proof.
intros a b c H.
rewrite <- neutral_right.
rewrite <- (inv_left _ (/ c)).
rewrite associative.
apply transpose_right.
rewrite inv_inv.
assumption.
Qed.

Lemma no_neutral_neq :
  forall a,
  (forall n, n>0 -> a^n <> neutral G) -> (forall n p, n<p -> a^n <> a^p).
Proof.
intros a H1 n p H2.
cut (a^(p-n) <> neutral G).
intro H.
contradict H.
rewrite power_nat_minus.
rewrite H.
apply inv_right.
omega.
auto with zarith.
Qed.

Definition QuadraticResidue (a:G) : Prop :=
  exists b, b * b = a.

Lemma qr_inv : forall a, QuadraticResidue a <-> QuadraticResidue (/ a).
Proof.
intro a.
split.
intros [b Hb].
exists (/ b).
rewrite <- inv_mult.
congruence.
intros [b Hb].
exists (/ b).
rewrite <- inv_mult.
rewrite Hb.
apply inv_inv.
Qed.

Section QuadraticResidue.

Hypothesis commutative : forall (a b:G), a*b = b*a.

Lemma qr_qr_mult_qr :
  forall a b, QuadraticResidue a -> QuadraticResidue b -> QuadraticResidue (a*b).
Proof.
intros a b [a' Ha] [b' Hb].
exists (a' * b').
rewrite <- associative.
rewrite (commutative a' b').
rewrite (associative _ b').
rewrite Hb.
rewrite (commutative b).
rewrite associative.
rewrite Ha.
reflexivity.
Qed.

Lemma qnr_qr_mult_qnr :
  forall a b,
  ~QuadraticResidue a -> QuadraticResidue b -> ~QuadraticResidue (a*b).
Proof.
intros a b Hqnr Hqr.
contradict Hqnr.
destruct Hqr as [b' Hb'].
destruct Hqnr as [c Hc].
exists (c * / b').
rewrite <- associative.
rewrite (commutative c (/ b')).
rewrite (associative _ (/ b')).
rewrite commutative.
rewrite <- inv_mult.
rewrite Hb'.
rewrite <- associative.
rewrite Hc.
rewrite commutative.
rewrite <- associative.
rewrite inv_right.
apply neutral_right.
Qed.

End QuadraticResidue.

Hypothesis finite : Finite G.

Definition to_list : listNE G :=
  epsilon
    (A := listNE G)
    (inhabits (exist _ (neutral G :: nil) (cons_ne _ (neutral G) nil)))
    (fun l => NoDup l /\ forall a:G, In a l).

Lemma NoDup_to_list : NoDup to_list.
Proof.
unfold to_list.
apply epsilon_ind.
apply Finite_to_listNE.
exact (eq_dec G).
exact (inhabits (neutral G)).
assumption.
tauto.
Qed.

Lemma In_to_list : forall a, In a to_list.
Proof.
intro a.
unfold to_list.
apply epsilon_ind.
apply Finite_to_listNE.
exact (eq_dec G).
exact (inhabits (neutral G)).
assumption.
intros l [_ H].
trivial.
Qed.

Definition order : nat :=
  length to_list.

Lemma order_gt_0 : order > O.
Proof.
unfold order, to_list.
apply epsilon_ind.
apply Finite_to_listNE.
apply eq_dec.
exact (inhabits (neutral G)).
assumption.
intros [l Hl] _.
simpl.
destruct l as [ | a l].
tauto.
simpl.
omega.
Qed.

Definition qr_dec : forall a, {QuadraticResidue a}+{~QuadraticResidue a}.
Proof.
intro a.
case_eq (fold_left (fun res b => res || (equal (b*b) a)) to_list false);
unfold equal; intro H.

left.
generalize (eq_true_false_abs _ H).
clear H.
intro H.
rewrite fold_left_all in H.
apply not_all_ex_not in H.
destruct H as [b H].
destruct (eq_dec G (b*b) a) as [H0 | H0].
exists b.
assumption.
tauto.
auto with bool.
auto with bool.
reflexivity.
intros x y H0.
destruct x.
assumption.
reflexivity.

right.
rewrite fold_left_all in H.
contradict H.
destruct H as [b H].
apply ex_not_not_all.
exists b.
intro H0.
generalize (H0 (In_to_list b)).
destruct (eq_dec G (b*b) a) as [H1 | H1].
discriminate.
contradiction.
auto with bool.
auto with bool.
reflexivity.
intros x y H0.
destruct x.
assumption.
reflexivity.
Qed.

Definition quadratic_residuosity (x:G) : bool :=
  if qr_dec x then true else false.

Fixpoint qr_list_gen (l:list G) : list G :=
  match l with
  | nil => nil
  | a :: l' =>
      if qr_dec a then a :: qr_list_gen l' else qr_list_gen l'
  end.

Definition qr_list : list G :=
  qr_list_gen to_list.

Lemma qr_list_gen_incl : forall l, incl (qr_list_gen l) l.
Proof.
induction l as [ | a l IH]; simpl.
congruence.
destruct (qr_dec a) as [_ | _].
auto with *.
auto with *.
Qed.

Lemma NoDup_qr_list_gen : forall l, NoDup l -> NoDup (qr_list_gen l).
Proof.
induction l as [ | a l IHl].
trivial.
simpl.
intro H.
destruct (qr_dec a) as [_ | _].
constructor.
contradict H.
apply qr_list_gen_incl in H.
intro H0.
inversion H0.
contradiction.
apply IHl.
inversion H.
assumption.
apply IHl.
inversion H.
assumption.
Qed.

Lemma NoDup_qr_list : NoDup qr_list.
Proof.
apply NoDup_qr_list_gen.
apply NoDup_to_list.
Qed.

Lemma qr_list_gen_spec :
  forall a l, In a (qr_list_gen l) <-> QuadraticResidue a /\ In a l.
Proof.
induction l as [ | b l IHl]; simpl.
tauto.
destruct (qr_dec b) as [H | H].
simpl.
rewrite IHl.
split.
intros [H0 | H0].
subst b.
tauto.
tauto.
tauto.
rewrite IHl.
split.
tauto.
intros [H1 [H2 | H2] ].
congruence.
tauto.
Qed.

Lemma qr_list_spec : forall a, In a qr_list <-> QuadraticResidue a.
Proof.
intro a.
unfold qr_list.
rewrite qr_list_gen_spec.
split.
tauto.
intro H.
split.
assumption.
apply In_to_list.
Qed.

Lemma qr_list_ne : qr_list <> nil.
Proof.
assert (In (neutral G) qr_list).

rewrite qr_list_spec.
exists (neutral G).
apply neutral_left.

destruct qr_list.
contradiction.
discriminate.
Qed.

Definition qr_listNE : listNE G :=
  exist _ qr_list qr_list_ne.

Fixpoint qnr_list_gen (l:list G) : list G :=
  match l with
  | nil => nil
  | a :: l' =>
      if qr_dec a then qnr_list_gen l' else a :: qnr_list_gen l'
  end.

Definition qnr_list : list G :=
  qnr_list_gen to_list.

Lemma qnr_list_gen_incl : forall l, incl (qnr_list_gen l) l.
Proof.
induction l as [ | a l IHl]; simpl.
congruence.
destruct (qr_dec a) as [_ | _].
auto with *.
auto with *.
Qed.

Lemma NoDup_qnr_list_gen : forall l, NoDup l -> NoDup (qnr_list_gen l).
Proof.
induction l as [ | a l IHl].
trivial.
simpl.
intro H.
destruct (qr_dec a) as [_ | _].
apply IHl.
inversion H.
assumption.
constructor.
contradict H.
apply qnr_list_gen_incl in H.
intro H0.
inversion H0.
contradiction.
apply IHl.
inversion H.
assumption.
Qed.

Lemma NoDup_qnr_list : NoDup qnr_list.
Proof.
apply NoDup_qnr_list_gen.
apply NoDup_to_list.
Qed.

Lemma qnr_list_gen_spec :
  forall a l, In a (qnr_list_gen l) <-> ~QuadraticResidue a /\ In a l.
Proof.
induction l as [ | b l IHl].
tauto.
simpl.
destruct (qr_dec b) as [H | H].
split.
tauto.
intros [H1 [H2 | H2] ].
congruence.
tauto.
simpl.
split.
intros [H1 | H1].
split.
congruence.
tauto.
tauto.
tauto.
Qed.

Lemma qnr_list_spec :
  forall a, In a qnr_list <-> ~QuadraticResidue a.
Proof.
intro a.
unfold qnr_list.
rewrite qnr_list_gen_spec.
split.
tauto.
intro H.
split.
assumption.
apply In_to_list.
Qed.

Lemma mult_Permutation :
  forall b,
  Permutation to_list (map (fun a : G => a * b) to_list).
Proof.
unfold to_list.
apply epsilon_ind.
apply Finite_to_listNE.
apply eq_dec.
exact (inhabits (neutral G)).
assumption.
intros [l Hl] [Hnod Hin] b.
simpl in *.
apply NoDup_Permutation.
assumption.
apply NoDup_map.
intros a1 a2 H1 H2 Hg.
apply mult_right_inj with b.
assumption.
assumption.
intro c.
rewrite in_map_iff.
split; intro H.
exists (c * / b).
split.
rewrite <- associative.
rewrite inv_left.
apply neutral_right.
apply Hin.
apply Hin.
Qed.

Definition Generator (g:G) : Prop :=
  forall a:G, exists n:nat, a = g^n.

Definition Cyclic : Prop :=
  exists g:G, Generator g.

Hypothesis cyclic : Cyclic.

Lemma commutative : forall (a b:G), a*b = b*a.
Proof.
intros a b.
destruct cyclic as [g is_generator].
destruct (is_generator a) as [m Ha].
destruct (is_generator b) as [n Hb].
subst a b.
do 2 rewrite <- power_nat_plus.
auto with arith.
Qed.

Variable g : G.

Hypothesis is_generator : Generator g.

Definition log (a:G) : nat :=
  epsilon (inhabits O) (fun n => a = g ^ n).

Lemma power_nat_log : forall a, g^(log a) = a.
Proof.
intro a.
unfold log.
apply epsilon_ind.
trivial.
congruence.
Qed.

Lemma power_nat_log_mult :  forall a b, g ^ log (a*b) = g ^ log a * g ^ log b.
Proof.
unfold log.
intros a b.
apply epsilon_ind.
apply is_generator.
apply epsilon_ind.
apply is_generator.
apply epsilon_ind.
apply is_generator.
congruence.
Qed.

Lemma log_inj : forall a b, log a = log b -> a=b.
Proof.
intros a b.
unfold log.
apply epsilon_ind.
apply is_generator.
apply epsilon_ind.
apply is_generator.
congruence.
Qed.

Lemma neutral_reachable : exists n, n>0 /\ g^n = neutral G.
Proof.
apply NNPP.
contradict finite.
generalize (not_ex_all_not _ _ finite).
clear finite.
intro H.
assert (forall n p, n<p -> g^n <> g^p) as H0.
apply no_neutral_neq.
intros n Hn.
generalize (H n).
tauto.
clear H.
apply all_not_not_ex.
intro l.
apply ex_not_not_all.
exists (g ^ S (fold_left (fun res a => max res a) (List.map log l) 0)).
apply all_in_neq.
intros b Hb.
rewrite <- (power_nat_log b).
apply sym_not_eq.
apply H0.
induction l as [ | a l IHl].
contradiction.
simpl.
cut (log a = max (log a) 0).
intro Hmax.
destruct Hb as [Hb | Hb].
subst b.
rewrite Hmax at 2.
rewrite <- fold_left_op.
auto with arith.
intros m n p.
rewrite max_assoc.
reflexivity.
generalize (IHl Hb).
clear IHl Hb.
intro H.
rewrite Hmax.
rewrite <- fold_left_op.
apply le_lt_n_Sm.
apply lt_n_Sm_le in H.
eapply le_trans.
eexact H.
apply le_max_r.
intros m n p.
rewrite max_assoc.
reflexivity.
rewrite max_comm.
reflexivity.
Qed.

Definition order' : nat :=
  least (fun n => n>0 /\ g^n = neutral G).

Lemma power_nat_inj' :
  forall m n, m < order' -> n < order' -> g^m = g^n -> m = n.
Proof.
intros m n Hm Hn H.
destruct (lt_eq_lt_dec m n) as [ [Hmn | Hmn] | Hmn].

assert (n-m>0 /\ g^(n-m) = neutral G) as Hminus.
split.
omega.
rewrite power_nat_minus.
symmetry.
apply transpose_right.
rewrite inv_inv.
rewrite neutral_left.
assumption.
omega.
assert (0 < n-m < order') as [H1 H2].
omega.
unfold order' in H2.
generalize (least_unique (n-m) _ Hminus H2).
omega.

assumption.

assert (m-n>0 /\ g^(m-n) = neutral G) as Hminus.
split.
omega.
rewrite power_nat_minus.
symmetry.
apply transpose_right.
rewrite inv_inv.
rewrite neutral_left.
congruence.
omega.
assert (0 < m-n < order') as [H1 H2].
omega.
unfold order' in H2.
generalize (least_unique (m-n) _ Hminus H2).
omega.
Qed.

Lemma lt_not_in : forall l, length l < order' -> exists n, ~In (g^n) l.
Proof.
unfold order', least.
apply iota_ind.
apply least_exists.
apply neutral_reachable.
intros n [ [H1 H2] H3] l Hlen.
apply NNPP.
contradict Hlen.
apply le_not_lt.
generalize (not_ex_all_not _ _ Hlen).
clear Hlen.
intro Hlen.
replace n with (length (seq 0 n)).
replace (length l) with
  (length (List.map (fun a => proj1_sig (modulo n H1 (log a))) l)).
apply incl_length_le.
exact eq_nat_dec.
apply NoDup_seq.
intros i Hi.
replace i with ((fun a => proj1_sig (modulo n H1 (log a))) (g^i)).
change (proj1_sig (modulo n H1 (log (g ^ i)))) with
  ((fun a => proj1_sig (modulo n H1 (log a))) (g^i)).
apply in_map.
apply NNPP.
apply Hlen.
destruct (modulo n H1 (log (g ^ i))) as [r [q [H4 H5] ] ].
simpl.
rewrite In_seq in Hi.
simpl in Hi.
destruct Hi as [Hi1 Hi2].
cut (g^i = g^(q*n+r)).
intro H.
cut (order' = n).
intro Hord'.
apply power_nat_inj'.
omega.
congruence.
rewrite H.
rewrite power_nat_plus.
rewrite power_nat_mult.
rewrite power_nat_comm.
rewrite H2.
rewrite neutral_power_nat.
rewrite neutral_left.
reflexivity.
unfold order', least.
apply iota_ind.
apply least_exists.
apply neutral_reachable.
intros m [ [H6 H7] H8].
apply NNPP.
intro H0.
cut (m<n \/ n<m).
clear H0.
intros [H0 | H0].
generalize (H3 m).
tauto.
generalize (H8 n).
tauto.
omega.
rewrite <- H4.
rewrite power_nat_log.
reflexivity.
apply map_length.
apply seq_length.
Qed.

Lemma order_not_lt_order' : ~ order < order'.
Proof.
unfold order, order', to_list, least, IsLeast.
apply epsilon_ind.
apply Finite_to_listNE.
apply eq_dec.
exact (inhabits (neutral G)).
assumption.
apply iota_ind.
apply least_exists.
apply neutral_reachable.
intros n [ [Hn1 Hn2] Hn3] [l Hl] [Hnod Hin] Hlen.
simpl in *.
generalize (Hin (g ^ least (fun n => ~In (g^n) l))).
apply all_in_neq.
intros b Hb.
unfold least.
apply iota_ind.
apply least_exists.
apply lt_not_in.
cutrewrite (order' = n).
assumption.
unfold order', least.
apply iota_ind.
apply least_exists.
apply neutral_reachable.
intros n' [ [Hn'1 Hn'2] Hn'3].
apply NNPP.
intro H.
cut (n'<n \/ n<n').
clear H.
intros [H | H].
generalize (Hn3 _ H).
tauto.
generalize (Hn'3 _ H).
tauto.
omega.
unfold IsLeast.
intros m [Hm1 Hm2].
congruence.
Qed.

Lemma order_not_gt_order' : ~ order > order'.
Proof.
unfold order, order', to_list, least, IsLeast.
apply epsilon_ind.
apply Finite_to_listNE.
apply eq_dec.
exact (inhabits (neutral G)).
assumption.
apply iota_ind.
apply least_exists.
apply neutral_reachable.
intros n [ [Hn1 Hn2] Hn3] [l Hl] [Hnod Hin] Hlen.
simpl in *.
apply NoDup_map with (f := fun a => g ^ log a) in Hnod.
replace
  (fun a => g ^ log a) with (fun a => g ^ proj1_sig (modulo n Hn1 (log a))) in
  Hnod.
rewrite <- map_map with (B:=nat) in Hnod.
apply map_NoDup in Hnod.
contradict Hlen.
apply le_not_gt.
erewrite <- map_length.
apply NoDup_length_le.
eexact Hnod.
intros m Hm.
rewrite in_map_iff in Hm.
destruct Hm as [a [Ha1 Ha2] ].
subst m.
destruct (modulo n Hn1 (log a)) as [r [q [Hmod1 Hmod2] ] ].
assumption.
extensionality a.
destruct (modulo n Hn1 (log a)) as [r [q [Hmod1 Hmod2] ] ].
simpl.
rewrite Hmod1.
rewrite power_nat_plus.
rewrite mult_comm.
rewrite power_nat_mult.
rewrite Hn2.
rewrite neutral_power_nat.
rewrite neutral_left.
reflexivity.
intros a b _ _ H.
do 2 rewrite power_nat_log in H.
assumption.
Qed.

Lemma order_eq_order' : order = order'.
Proof.
apply NNPP.
intro H.
assert (order < order' \/ order > order') as H0.
omega.
clear H.
destruct H0 as [H | H].
apply order_not_lt_order'.
assumption.
apply order_not_gt_order'.
assumption.
Qed.

Lemma power_nat_inj :
  forall m n, m < order -> n < order -> g^m = g^n -> m = n.
Proof.
rewrite order_eq_order'.
exact power_nat_inj'.
Qed.

Lemma generator_to_order : g ^ order = neutral G.
Proof.
rewrite order_eq_order'.
unfold order', least.
apply iota_ind.
apply least_exists.
apply neutral_reachable.
unfold IsLeast.
tauto.
Qed.

Lemma inv_minus : forall n, n <= order -> / (g^n) = g ^ (order - n).
Proof.
intros n H.
rewrite power_nat_minus.
rewrite generator_to_order.
rewrite neutral_left.
reflexivity.
assumption.
Qed.

Lemma finite_generator : forall a:G, exists n:nat, n < order /\ a = g^n.
Proof.
intro a.
destruct (is_generator a) as [n Ha].
destruct (modulo order order_gt_0 n) as [r [q [H1 H2] ] ].
exists r.
split.
omega.
subst n a.
rewrite power_nat_plus.
rewrite power_nat_mult.
rewrite power_nat_comm.
rewrite generator_to_order.
rewrite neutral_power_nat.
apply neutral_left.
Qed.

Lemma even_log_square : forall a, even order -> even (log (a*a)).
Proof.
intros a Heven.
unfold log.
apply epsilon_ind.
apply is_generator.
intros n Hn.
rewrite <- (power_nat_log a) in Hn.
rewrite <- power_nat_plus in Hn.
destruct (modulo order order_gt_0 (log a + log a)) as [r1 [q1 [H1 H2] ] ]. 
destruct (modulo order order_gt_0 n) as [r2 [q2 [H3 H4] ] ]. 
rewrite H1 in Hn.
rewrite H3 in Hn.
assert (g^r1 = g^r2).
transitivity (g^(q1*order+r1)).
rewrite power_nat_plus.
rewrite power_nat_mult.
rewrite power_nat_comm.
rewrite generator_to_order.
rewrite neutral_power_nat.
rewrite neutral_left.
reflexivity.
transitivity (g^(q2*order+r2)).
assumption.
rewrite power_nat_plus.
rewrite power_nat_mult.
rewrite power_nat_comm.
rewrite generator_to_order.
rewrite neutral_power_nat.
apply neutral_left.
apply power_nat_inj in H.
subst n.
subst r2.
apply even_even_plus.
apply even_mult_r.
assumption.
cutrewrite (r1 = log a + log a - q1 * order).
apply even_even_minus.
cutrewrite (log a + log a = 2 * log a)%nat.
auto with arith.
ring.
auto with arith.
omega.
assumption.
assumption.
Qed.

Lemma power_nat_Permutation :
  Permutation
    to_list (map (fun x : nat => g ^ x) (seqNE 0 order)).
Proof.
unfold to_list.
apply epsilon_ind.
apply Finite_to_listNE.
apply eq_dec.
exact (inhabits (neutral G)).
assumption.
intros [l Hl] [Hnod Hin].
simpl in *.
unfold order, to_list.
apply epsilon_ind.
apply Finite_to_listNE.
apply eq_dec.
exact (inhabits (neutral G)).
assumption.
intros [l' Hl'] [Hnod' Hin'].
simpl in *.
apply NoDup_Permutation.
assumption.
apply NoDup_map.
intros x y Hx Hy Hg.
apply power_nat_inj.
unfold order.
rewrite In_seqNE in Hx.
cutrewrite (length to_list = length l').
tauto.
apply Permutation_length.
apply NoDup_Permutation.
apply NoDup_to_list.
assumption.
intro a.
split; intro H.
apply Hin'.
apply In_to_list.
destruct l' as [ | a' l'].
tauto.
discriminate.
unfold order.
rewrite In_seqNE in Hy.
cutrewrite (length to_list = length l').
tauto.
apply Permutation_length.
apply NoDup_Permutation.
apply NoDup_to_list.
assumption.
intro a.
split; intro H.
apply Hin'.
apply In_to_list.
destruct l' as [ | a' l'].
tauto.
discriminate.
assumption.
apply NoDup_seqNE.
intro x.
rewrite in_map_iff.
split; intro H.
destruct (finite_generator x) as [n [ Hx Hx0] ].
exists n.
split.
congruence.
rewrite In_seqNE.
split.
omega.
simpl.
cutrewrite (length l' = order).
assumption.
unfold order.
unfold to_list.
apply epsilon_ind.
exists (exist _ l' Hl').
tauto.
intros [l'' Hl''] [Hnod'' Hin''].
simpl in *.
apply Permutation_length.
apply NoDup_Permutation.
assumption.
assumption.
auto with *.
destruct l' as [ | a' l'].
tauto.
discriminate.
trivial.
Qed.

Hypothesis even_order : even order.

Lemma qr_even : forall n, (QuadraticResidue (g^n) <-> even n).
Proof.
intro n.
split.

intros [a Ha].
destruct (is_generator a) as [m Hm].
subst a.
rewrite <- power_nat_plus in Ha.
destruct (modulo order order_gt_0 (m + m)) as [r1 [q1 [H1 H2] ] ]. 
destruct (modulo order order_gt_0 n) as [r2 [q2 [H3 H4] ] ]. 
rewrite H1, H3 in Ha.
assert (g^r1 = g^r2).
transitivity (g^(q1*order+r1)).
rewrite power_nat_plus.
rewrite power_nat_mult.
rewrite power_nat_comm.
rewrite generator_to_order.
rewrite neutral_power_nat.
rewrite neutral_left.
reflexivity.
transitivity (g^(q2*order+r2)).
assumption.
rewrite power_nat_plus.
rewrite power_nat_mult.
rewrite power_nat_comm.
rewrite generator_to_order.
rewrite neutral_power_nat.
apply neutral_left.
apply power_nat_inj in H.
subst n.
subst r2.
apply even_even_plus.
apply even_mult_r.
assumption.
cutrewrite (r1 = m + m - q1 * order).
apply even_even_minus.
cutrewrite (m + m = 2 * m)%nat.
auto with arith.
ring.
auto with arith.
omega.
assumption.
assumption.

intro H.
apply even_2n in H.
destruct H as [m Hm].
exists (g^m).
rewrite <- power_nat_plus.
subst n.
reflexivity.
Qed.

Lemma qnr_qnr_mult_qr :
  forall a b,
  ~QuadraticResidue a -> ~QuadraticResidue b -> QuadraticResidue (a*b).
Proof.
intros a b.
destruct (is_generator a) as [m Ha].
destruct (is_generator b) as [n Hb].
subst a b.
rewrite <- power_nat_plus.
do 3 rewrite qr_even.
intros Hm Hn.
apply odd_even_plus.
generalize (even_or_odd m).
tauto.
generalize (even_or_odd n).
tauto.
Qed.

Lemma qr_qnr_Permutation :
  Permutation qr_list (List.map (fun a => g * a) qnr_list).
Proof.
apply NoDup_Permutation.
apply NoDup_qr_list.
apply NoDup_map.
intros x y Hx Hy H.
rewrite <- neutral_left.
rewrite <- inv_left with (a:=g).
rewrite <- associative.
apply transpose_left.
simpl in *.
rewrite <- H.
rewrite inv_inv.
reflexivity.
apply NoDup_qnr_list.
intro a.
rewrite in_map_iff.
rewrite qr_list_spec.
split.

intro H.
case_eq (log a).
intro Hlog.
exists (/ g).
rewrite qnr_list_spec.
split.
rewrite <- (power_nat_log a).
rewrite Hlog.
apply inv_right.
rewrite <- (power_nat_1 g).
rewrite inv_minus.
rewrite qr_even.
intro H1.
apply not_even_and_odd with (n:=(order-1)%nat).
assumption.
assert (odd (order - 1 + 1)) as H2.
apply odd_plus_r.
assumption.
auto with arith.
contradict H2.
intro H2.
apply not_even_and_odd with (n:=order).
assumption.
cutrewrite (order = order - 1 + 1).
assumption.
generalize order_gt_0.
omega.
generalize order_gt_0.
trivial.
intros m Hlog.
exists (g ^ m).
rewrite qnr_list_spec.
split.
rewrite <- (power_nat_log a).
rewrite Hlog.
reflexivity.
rewrite <- (power_nat_log a) in H.
rewrite Hlog in H.
rewrite qr_even in H.
rewrite qr_even.
intro H'.
apply not_even_and_odd with (n:=m).
assumption.
apply even_plus_odd_inv_r with (n:=1%nat).
assumption.
auto with arith.

intros [b [H1 H2] ].
rewrite qnr_list_spec in H2.
rewrite <- H1.
revert H2.
rewrite <- (power_nat_log b).
change (g * g ^ log b) with (g ^ S (log b)).
rewrite qr_even.
rewrite qr_even.
intro H2.
apply even_S.
destruct (even_or_odd (log b)).
contradiction.
assumption.
Qed.

Lemma length_qr_qnr_list : length qr_list = length qnr_list.
Proof.
rewrite (Permutation_length qr_qnr_Permutation).
apply map_length.
Qed.

End Group.

Notation "a ^ n" :=
  (power_nat _ a n) : group_scope.

Implicit Arguments QuadraticResidue [G].
