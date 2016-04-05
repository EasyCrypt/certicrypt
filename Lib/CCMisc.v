(** * CCMisc.v: Extensions to the Coq Standard Library *)

Set Implicit Arguments.

Require Import Bool.
Require Export BoolEquality.
Require Export List.
Require Import Heap.
Require Export Sorting.
Require Export Permutation.
Require Export NArith.
Require Export Ndec.
Require Export ZArith.
Require Export Arith.

Open Scope nat_scope.

(* List *)
Definition is_nil (A:Type) (l:list A) : bool :=
 match l with
  | nil => true
  | _ => false
 end.

Lemma find_In : forall (A:Type) (f:A -> bool) l a, 
 find f l = Some a -> In a l /\ f a.
Proof.
 induction l; simpl; intro; try (intros; discriminate).
 case_eq (f a); intros.
 inversion H0; subst; auto. 
 destruct (IHl _ H0); intuition. 
Qed. 

Lemma find_notIn : forall (A:Type) (f:A -> bool) l, 
 find f l = None -> 
 forall a, In a l -> f a = false.
Proof.
 induction l; simpl; intros.
 elim H0. 
 destruct H0; subst.
 destruct (f a0); try discriminate; trivial.
 destruct (f a); try discriminate; auto.
Qed.

Lemma length_nil : forall A (l:list A), length l = O -> l = nil.
Proof.
 destruct l; intros; [trivial | discriminate].
Qed.

Lemma fold_right_rev_left: forall (A B:Type) (f:B -> A -> B) (l:list A) (i:B),
 fold_left f (rev l) i = fold_right (fun (x:A) (y:B) => f y x) i l.
Proof.
 intros.   
 induction l; simpl; trivial.
 rewrite fold_left_app, IHl; simpl; trivial.
Qed.

Fixpoint lfalse (n:nat) :=
 match n with
  | O => nil
  | S n => false :: lfalse n
 end.

Lemma length_lfalse : forall n, length (lfalse n) = n.
Proof.
 induction n; simpl; intros; trivial.
 rewrite IHn; trivial.
Qed.

Lemma list_prod_nil t1 t2 (l1 : list t1) (l2 : list t2) : 
  l1 <> nil -> l2 <> nil -> list_prod l1 l2 <> nil.
Proof.
 intros t1 t2 l1 l2 H1 H2 H.
 assert (length (list_prod l1 l2) = 0%nat).
 rewrite H; trivial.
 rewrite prod_length in H0.
 apply mult_is_O in H0; destruct H0;
   apply length_nil in H0; subst; tauto.
Qed.

Hint Constructors NoDup.

Lemma NoDup_dec: forall A,
 (forall x y:A, sumbool (x = y) (x <> y)) ->
 forall l:list A, sumbool (NoDup l) (~ NoDup l).
Proof.
 intros A eq_dec; induction l.
 left; constructor.
 destruct (in_dec eq_dec a l).
 right; intro H; inversion_clear H; tauto.
 destruct IHl.
 left; constructor; assumption.
 right; intro H; inversion_clear H; tauto.
Qed.

Lemma NoDup_snd : forall A B (l:list (A * B)),
 NoDup (map (@snd _ _) l) ->
 forall a1 a2 b,
  In (a1,b) l ->
  In (a2,b) l ->
  a1 = a2.
Proof.
 induction l; simpl; intros.
 elim H1.
 inversion_clear H.
 destruct H0; destruct H1; subst.
 injection H0; trivial.
 apply (in_map (@snd _ _)) in H0; tauto.
 apply (in_map (@snd _ _)) in H; tauto.
 apply IHl with b; trivial.
Qed.

Lemma NoDup_map_inj : forall A B (f:A -> B) l,
 (forall x y, In x l -> In y l -> f x = f y -> x = y) -> 
 NoDup l -> 
 NoDup (map f l).
Proof.
 clear.
 induction l; simpl; intros; constructor.
 intro H1; apply in_map_iff in H1.
 destruct H1 as [y [H3 H4] ].
 apply H in H3; [ | right; trivial | left; trivial].
 inversion_clear H0; subst; tauto.
 apply IHl.
 intros; apply H; auto.
 inversion H0; trivial.
Qed.

Lemma NoDup_app : forall A (l1 l2:list A), 
 NoDup l1 -> 
 NoDup l2 ->
 (forall x, In x l2 -> ~In x l1) ->
 NoDup (l1 ++ l2).
Proof.
 induction l1; simpl; intros; trivial.
 inversion_clear H.
 constructor; auto.
 intro H4; apply in_app_or in H4; destruct H4; auto.
 elim (H1 a); auto.
 apply IHl1; auto.
 firstorder.
Qed.

Lemma NoDup_app_inv : forall A (l1 l2:list A),
 NoDup (l1 ++ l2) -> NoDup l1 /\ NoDup l2.
Proof.
 induction l1; simpl; intros. 
 split; [constructor | trivial].
 inversion_clear H.
 destruct (IHl1 _ H1); split; [ constructor; trivial | trivial].
 intro; apply H0; apply in_or_app; auto.
Qed.

Lemma NoDup_rev : forall A (l:list A),
 NoDup l ->
 NoDup (rev l).
Proof. 
 induction l; intros.
 constructor.
 inversion_clear H.
 simpl; apply NoDup_app.
 auto.
 auto.
 intros x Hx Hin.
 apply In_rev in Hin.
 destruct Hx; subst; auto.
Qed.

Lemma NoDup_list_prod : forall A B (l1:list A) (l2:list B), 
 NoDup l1 -> NoDup l2 -> NoDup (list_prod l1 l2).
Proof.
 induction l1.
 constructor.

 intros; simpl.
 apply NoDup_app.
 apply NoDup_map_inj; trivial.
 intros ? ? _ _ H3; injection H3; trivial.
 apply IHl1; trivial.
 inversion H; trivial.
 
 intros (x,y) H3 Hin.
 apply in_prod_iff in H3; destruct H3.
 apply in_map_iff in Hin; destruct Hin as [x' [? ?] ].
 injection H3; intros; subst.
 contradict H; intro; inversion H; subst.
 absurd (In x l1); trivial.
Qed.

Lemma Permutation_NoDup : forall A (l l': list A), 
 Permutation l l' -> NoDup l -> NoDup l'.
Proof.
 induction 1; intros; trivial.
 inversion_clear H0; constructor; auto.
 intro; apply H1.
 apply Permutation_in with l'; trivial. 
 apply Permutation_sym; trivial.
 inversion_clear H.
 inversion_clear H1.
 simpl in H0; constructor.
 simpl; intros [H1 | H1]; auto.
 constructor; auto.
 auto.
Qed.

Lemma NoDup_app_comm: forall A (l1 l2 :list A),
 NoDup (l1 ++ l2) -> NoDup (l2 ++ l1).
Proof.
 intros.
 refine (@Permutation_NoDup _ (l1 ++ l2) _ _ H).
 apply Permutation_app_swap.
Qed.

Lemma NoDup_app_cons_r : forall A (l l' : list A) (x':A), 
 NoDup (l ++ x'::l') ->
 NoDup l /\ NoDup l' /\ not (In x' l) /\ not (In x' l').
Proof.
 intros.
 destruct (NoDup_app_inv _ _ H) as [H1 H2].
 inversion_clear H2.
 repeat split; try assumption.
 apply NoDup_app_comm in H.
 rewrite <- app_comm_cons in H.
 inversion_clear H; clear H4.
 intro H4; elim H2.
 apply in_or_app; auto.
Qed.

Lemma Sorted_le_lt : forall l,
 NoDup l ->
 Sorted le l ->
 Sorted lt l.
Proof.
 induction l; intros.
 trivial.
 constructor.
 inversion_clear H0; subst.
 apply IHl in H1; trivial.
 inversion H; trivial. 
 inversion H0; subst.
 apply IHl in H3; trivial.
 inversion H; subst.
 destruct l.
 trivial.
 constructor.
 assert (a <> n).
 intro; subst; elim H5; simpl; auto.
 inversion H4; subst; omega.
 inversion H; trivial.
Qed.

Lemma Forall2_eq : forall A (l1 l2:list A), Forall2 eq l1 l2 -> l1 = l2.
Proof.
 intros; induction H; subst; trivial.
Qed.

Lemma Sorted_lt_NoDup : forall l,
 NoDup l ->
 exists l', Sorted lt l' /\ Permutation l l'.
Proof.
 intros.
 destruct (treesort nat le eq le_ge_dec eq_nat_dec le_trans l) as (l',H0,H1).
 apply PermutSetoid.permutation_Permutation in H1.
 destruct H1 as [l1 [ ? ? ] ].
 apply Forall2_eq in H2; subst.
 exists l'; split; trivial.
 apply Permutation_NoDup in H1; trivial.
 apply Sorted_le_lt; trivial.
 apply eq_equivalence.
Qed.

Lemma nth_cons : forall A (l:list A) a b n i,
 Compare_dec.leb (S n) i ->
 nth (i - S n) l b = nth (i - n) (a :: l) b.
Proof.
 intros.
 change (b :: l) with (b :: nil ++ l).
 rewrite (app_nth2 (a :: nil) l); [ | apply leb_complete in H; simpl; omega].
 simpl; replace (i - S n) with (i - n - 1) by omega; trivial.
Qed.

Lemma nth_app : forall A (l:list A) a b, 
 nth (length l) (l ++ a :: nil) b = a.
Proof.
 intros; rewrite app_nth2, minus_diag; auto.
Qed.

Lemma In_nth_inv : forall A (a b:A) l,
 In a l ->
 exists n, (n < length l)%nat /\ a = nth n l b.
Proof.
 induction l; destruct 1.
 subst; exists O; split; simpl; auto with arith.
 destruct (IHl H) as [j [? ?] ]; exists (S j); split.
 simpl; omega.
 trivial.
Qed.


Fixpoint cexistsb (A:Type) (f:A->bool*nat) (l:list A) (n:nat) {struct l} : 
 bool * nat :=
 match l with
  | nil => (false, n)
  | a::l0 => let (b, n0) := f a in 
    if b then (true, n + n0) else cexistsb f l0 (n + n0)
 end.

Lemma existsb_cexistsb : forall A f g,
 (forall x, f x = fst (g x)) ->
 forall (l:list A) n, existsb f l = fst (cexistsb g l n).
Proof.
 intros A f g Hfg; induction l.
 trivial.
 simpl; generalize (Hfg a).
 case (f a); case (g a); intros b n H n0; simpl in H; rewrite <- H; trivial.
Qed.

Lemma existsb_app : forall A (f:A -> bool) l1 l2,
 existsb f (l1 ++ l2) = orb (existsb f l1) (existsb f l2).
Proof.
 induction l1; simpl; intros; trivial.
 rewrite IHl1, orb_assoc; trivial.
Qed.

Fixpoint cforallb (A:Type)(f:A->bool*nat)(l:list A)(n:nat) {struct l} : bool * nat :=
 match l with
 | nil => (true, n)
 | a::l0 => let (b, n0) := f a in 
  if b then cforallb f l0 (n + n0) else (false, n + n0)
 end.

Lemma forallb_cforallb : forall A f g,
 (forall x, f x = fst (g x)) ->
 forall (l:list A) n, forallb f l = fst (cforallb g l n).
Proof.
 intros A f g Hfg; induction l.
 trivial.
 simpl; generalize (Hfg a).
 case (f a); case (g a); intros b n H n0; simpl in H; rewrite <- H; trivial.
Qed.

Definition find_default (A:Type) (f:A->bool) l default :=
  match List.find f l with
  | Some a => a
  | None => default
  end.

Fixpoint cfind (A:Type) (f:A->bool*nat) l n {struct l} : option A * nat :=
  match l with
  | nil => (None, n) 
  | a :: tl => let (b, n0) := f a in
    if b then (Some a, n + n0) else cfind f tl (n + n0)
  end.

Definition cfind_default (A:Type) (f:A->bool*nat) l n default :=
  match cfind f l n with
  | (Some a, n0) => (a, n0)
  | (None, n0) => (default, n0)
  end.

Lemma find_cfind : forall A f g,
 (forall x, f x = fst (g x)) ->
 forall (l:list A) n, find f l = fst (cfind g l n).
Proof.
 intros A f g Hfg; induction l.
 trivial.
 simpl; generalize (Hfg a).
 case (f a); case (g a); intros b n H n0; simpl in H; rewrite <- H; trivial.
Qed.

Lemma find_cfind_default : forall A f g default,
 (forall x, f x = fst (g x)) ->
 forall (l:list A) n, find_default f l default = fst (cfind_default g l n default).
Proof.
 unfold find_default, cfind_default; intros.
 rewrite (find_cfind f g H l n).
 destruct (cfind g l n).
 destruct o; trivial.
Qed.

Section FOLD.

  Definition opt_app (A B:Type) (f : A -> option B) (a:option A) : option B :=
   match a with
   | Some a => f a
   | None => None
   end.

  Variable A B : Type.
  Variable f : A -> B -> option A.

  Fixpoint fold_left_opt  (l : list B) (a0 : A) {struct l} : option A :=
   match l with
   | nil => Some a0
   | b :: t => opt_app (fold_left_opt t) (f a0 b)
   end.

  Definition spec_opt (P:A->Prop) (a:option A) : Prop :=
   match a with
   | Some a => P a
   | None => True
   end.

End FOLD.

(* Nat *)
Fixpoint pow (n m:nat) {struct m} : nat :=
 match m with
 | O => S O
 | S m' => n * (pow n m')
 end.

Infix "^" := pow : nat_scope.

Definition pow_N (n m:N) : N :=
 Nnat.N_of_nat (pow (Nnat.nat_of_N n) (Nnat.nat_of_N m)). 

Lemma pow_lt_0 : forall n c, 0 < n -> 0 < n ^ c.
Proof.
 intros; induction c.
 auto.
 apply lt_le_trans with (1:=IHc).
 rewrite <- (mult_1_l (n ^ c)).
 simpl pow; apply mult_le_compat_r; trivial.
Qed.

Lemma pow_2_le : forall c, exists k, c <= 2 ^ k.
Proof.
 induction c; intros.
 exists 0; simpl; auto.
 destruct IHc as [k Hle].
 exists (S k).
 apply le_trans with (1 + (2 ^ k)).
 apply le_n_S; trivial.
 simpl pow; rewrite plus_0_r.
 apply plus_le_compat.
 apply pow_lt_0; auto.
 trivial.
Qed.

Lemma pow_monotone_1 : forall k n m, n <= m -> n ^ k <= m ^ k.
Proof.
 induction k; intros; simpl.
 trivial.
 apply mult_le_compat; auto.
Qed. 

Lemma pow_monotone_2 : forall k1 k2 n, 0 < n -> k1 <= k2 -> n ^ k1 <= n ^ k2.
Proof.
 induction k1; intros; simpl.
 apply le_trans with (1 ^ k2).
 apply pow_lt_0; auto.
 apply pow_monotone_1; trivial.
 inversion H0; subst.
 trivial.
 simpl; apply mult_le_compat.
 trivial.
 apply IHk1.
 trivial.
 auto with arith.
Qed. 

Lemma pow_mult_plus : forall k1 k2 n, n ^ k1 * n ^ k2 = n ^ (k1 + k2).
Proof.
 induction k1; destruct k2; simpl; intros.
 trivial.
 ring.
 rewrite plus_0_r, mult_1_r; trivial.
 rewrite <- plus_n_Sm.
 simpl; rewrite <- IHk1; ring.
Qed.  


Definition Nminus n1 n2 :=
 match n1, n2 with
 | N0, _ => N0
 | _, N0 =>  n1
 | Npos p1, Npos p2 => 
   match Pminus_mask p1 p2 with
   | IsPos p1 => Npos p1
   | _ => N0
   end
 end.


(* REMARK: There exist a [beq_nat] in EqNat *)
Fixpoint nat_eqb (n1 n2:nat) {struct n1} : bool :=
 match n1, n2 with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S n1, S n2 => nat_eqb n1 n2
 end.

Lemma nat_eqb_spec : forall n1 n2, if nat_eqb n1 n2 then n1 = n2 else n1 <> n2.
Proof.
 induction n1; destruct n2; simpl; trivial; try (intro; discriminate).
 generalize (IHn1 n2); destruct (nat_eqb n1 n2); auto.
Qed.

Lemma nat_eqb_true : forall n1 n2, nat_eqb n1 n2 = true -> n1 = n2.
Proof.
 induction n1; destruct n2; simpl; trivial; try (intro; discriminate).
 auto.
Qed.

Implicit Arguments nat_eqb_true [n1 n2].

Lemma nat_eqb_refl : forall n, nat_eqb n n = true.
Proof.
 induction n; trivial.
Qed.

Lemma nat_eqb_sym : forall n m, nat_eqb n m = nat_eqb m n.
Proof.
 induction n; destruct m; simpl; trivial.
Qed.

Lemma nat_eqb_trans: forall (n m p: nat), 
 nat_eqb n m -> nat_eqb m p -> nat_eqb n p.
Proof.
 intros.
 apply nat_eqb_true in H.
 apply nat_eqb_true in H0.
 subst; apply nat_eqb_refl. 
Qed.

Lemma eqb_sym : forall x y, eqb x y = eqb y x.
Proof.
 intros; case x; case y; trivial.
Qed.

Lemma eqb_spec : forall (x y:bool), if eqb x y then x = y else x <> y.
Proof.
 intros.
 case_eq (eqb x y).
 apply eqb_prop.
 intros H1 H2; subst.
 rewrite eqb_reflx in H1.
 inversion H1.
Qed.

Definition eq_dec_nat (n m:nat) : sumbool (n = m) True :=
 match eq_nat_dec n m with
  | left i => left _ i
  | right _ => right _ I
 end.

Lemma eq_dec_nat_r : forall n m i, eq_dec_nat n m = right _ i -> n <> m.
Proof.
 intros n m; simpl; intro i.
 unfold eq_dec_nat; case (eq_nat_dec n m); intros.
 discriminate.
 trivial.
Qed.


(* Sum of the first [p] natural numbers *)

Fixpoint sum_k_p (k p:nat) {struct p} : nat :=
 if Compare_dec.leb k p then 
  match p with
   | O => O
   | S p' => sum_k_p k p' + p
  end
  else 0.

Lemma sum_k_p_plus : forall p1 p2 p3,
 p1 <= p2 -> 
 p2 <= p3 ->
 sum_k_p p1 p2 + sum_k_p (S p2) p3 = sum_k_p p1 p3.
Proof.
 induction p3; simpl; intros.
 assert (W:p2 = 0) by omega; rewrite W, plus_0_r; trivial.      
 assert (W:p1 <= S p3) by apply le_trans with (1:=H) (2:=H0).
 rewrite (leb_correct _ _ W).
 case_eq (Compare_dec.leb p2 p3); intros.
 rewrite plus_assoc, IHp3; auto using leb_complete.
 apply leb_complete_conv in H1.
 assert (W1:p2 = S p3) by omega; rewrite plus_0_r, W1; simpl.
 rewrite (leb_correct _ _ W); trivial.
Qed.

Lemma sum_k_p_lt : forall k p, p < k -> sum_k_p k p = 0.
Proof.
 destruct p; simpl; intros.
 destruct (Compare_dec.leb k 0); trivial.
 rewrite leb_correct_conv; auto with arith.
Qed.

Lemma sum_k_p_eq : forall k, sum_k_p k k = k.
Proof.
 destruct k; trivial.
 simpl.
 rewrite leb_correct; auto with arith.
 rewrite sum_k_p_lt; auto with arith.
Qed.

Lemma sum_Sk_p : forall k p, 
 k <= p ->
 sum_k_p k p = k + sum_k_p (S k) p.
Proof.
 intros k p H; destruct (le_lt_dec (S k) p).
 assert (W:k <= S k) by auto with arith.
 rewrite <- (@sum_k_p_plus k k p); trivial.
 rewrite sum_k_p_eq; trivial.
 assert (W: k = p) by omega.
 rewrite (sum_k_p_lt l), plus_0_r, W; apply sum_k_p_eq.
Qed.

Lemma sum_k_Sp : forall k p,
 k <= S p ->
 sum_k_p k (S p) = sum_k_p k p + S p.
Proof.
 intros; simpl; rewrite leb_correct; trivial.
Qed.

Lemma sum_0_n : forall n, 2 * sum_k_p 0 n = n * (n + 1).
Proof.
 induction n; trivial.
 rewrite sum_k_Sp; [ | auto with arith].
 rewrite mult_plus_distr_l, IHn; ring.
Qed.


(* New Datatypes *)

Inductive triple (A B C:Type) : Type :=
| Triple : A -> B -> C -> triple A B C.

Inductive quadruple (A B C D:Type) : Type :=
| Quad : A -> B -> C -> D -> quadruple A B C D.



Section PERMUTATION.

 Variables A B : Type.
 Variable  P : A -> B -> Prop. 

 Inductive PermutP : list A -> list B -> Prop :=
 | permP_nil : PermutP nil nil
 | permP_swap : forall x x' l l1' l2',
    P x x' -> PermutP l (l1' ++ l2') -> PermutP (x :: l) (l1' ++ x' :: l2').

 Lemma PermutP_length : forall l1 l2, 
  PermutP l1 l2 -> length l1 = length l2.
 Proof.
  induction 1; simpl; intros; trivial.
  rewrite IHPermutP; repeat rewrite app_length; simpl; auto with arith.
 Qed.

 Lemma PermutP_app : forall l1 l1', 
  PermutP l1 l1' -> 
  forall l2 l2', 
   PermutP l2 l2' -> PermutP (l1++l2) (l1'++l2').
 Proof.
  induction 1; intros; simpl; trivial.
  rewrite app_ass; simpl; constructor; trivial.
  rewrite <- app_ass; auto.
 Qed.

 Lemma PermutP_cons : forall a b la lb, 
  P a b -> 
  PermutP la lb ->
  PermutP (a::la) (b::lb).
 Proof.
  intros; change (b::lb) with (nil++b::lb); constructor; trivial.
 Qed.
   
 Lemma PermutP_cons_r_inv : forall x l1 l2, 
  PermutP l1 (x::l2) ->
  exists x', exists l, exists l', 
   l1 = l ++ x' :: l' /\ 
   P x' x /\ 
   PermutP (l++l') l2.
 Proof.
  induction l1; intros l2 H; inversion H; clear H; subst.
  destruct l1'; simpl in *.
  injection H2; clear H2; intros; subst.
  exists a; exists nil; exists l1; repeat split; trivial. 
  injection H2; clear H2; intros; subst.
  destruct (IHl1 _ H4) as (x'' , (l, (l', (W1,(W2,W3))))); clear H4; subst.
  exists x''; exists (a::l); exists l'; repeat split; trivial.
  simpl; constructor; trivial. 
 Qed. 

 Lemma PermutP_cons_r : forall a b l l' l2, 
  PermutP (l++l') l2 ->
  P a b ->
  PermutP (l ++ a :: l') (b::l2).
 Proof.
  induction l; simpl; intros l' l2 H Hp.
  apply PermutP_cons; trivial.
  inversion H; clear H; subst.
  change (b :: l1' ++ x' :: l2') with ((b :: l1') ++ x' :: l2'); 
   constructor; simpl; auto.
 Qed.

 Lemma PermutP_app_cons_inv : forall x l2 l1 l3,
  PermutP (l1 ++ x :: l2) l3 -> 
  exists l4, exists l5, exists x', 
   l3 = l4 ++ (x'::l5) /\ 
   P x x' /\ 
   PermutP (l1++l2) (l4++l5) .
 Proof.
  induction l1; simpl; intros.
  inversion H.
  exists l1'; exists l2'; exists x'; auto.
  inversion H; clear H; subst.
  destruct (IHl1 _ H4) as (l4, (l5, (x'', (Heq, (HP, HPr))))).
  clear IHl1 H4. 
  generalize l1' l2' l1 l2 l4 l5 Heq HPr.
  clear HPr Heq l1' l2' l4 l5 l1 l2.
  induction l1'; simpl; intros.
  rewrite Heq; exists (x'::l4); exists l5; exists x''; repeat split; trivial.
  simpl; apply PermutP_cons; trivial.
  destruct l4; simpl in Heq; injection Heq; clear Heq; intros; subst; simpl in *.
  exists nil; exists (l1' ++ x' :: l2'); exists x''; repeat split; trivial.
  simpl; constructor; trivial.
  destruct (PermutP_cons_r_inv HPr) as (b', (l6, (l7, (W1,(W2,W3))))).
  destruct (IHl1' _ _ _ _ _ H W3) as (l8, (l9, (y, (W4, (W5,W6))))).
  rewrite W4, W1.
  exists (b::l8); exists l9; exists y; repeat split; trivial.
  simpl; inversion W6; clear W6; subst.
  change (b :: l1'0 ++ x'0 :: l2'0) with ((b:: l1'0) ++ x'0 :: l2'0).
  constructor; trivial.
  simpl; apply PermutP_cons_r; trivial.
 Qed.

End PERMUTATION.


Section PERMUTATION_PROP.
 
 Lemma PermutP_trans : forall (A B:Type) (P:A -> B -> Prop) l1 l2, 
  PermutP P l1 l2 ->
  forall l3, PermutP (@eq _) l2 l3 -> PermutP P l1 l3.
 Proof.
  induction 1; simpl; intros.
  inversion H; constructor. 
  destruct (PermutP_app_cons_inv (B:= B) (P:= @eq B) _ _ _ H1) as
   (l4, (l5, (x'', (W1, (W2, W3))))); clear H1; subst.
  constructor; auto.
 Qed.


 Lemma PermutP_refl : forall A (R:A -> A -> Prop) (l:list A),
  (forall x, In x l -> R x x) ->
  PermutP R l l.
 Proof.
  induction l; intros.
  constructor.
  apply PermutP_cons.
  apply H; apply in_eq.
  apply IHl; intros x Hx; exact (H x (in_cons  a _ _  Hx)). 
 Qed.

 Lemma PermutP_sym : forall A B R (la:list A) (lb:list B), 
  PermutP (fun b a => R a b) lb la ->
  PermutP R la lb.
 Proof.
  induction 1. 
  constructor.
  apply PermutP_cons_r; trivial.
 Qed.

 Lemma PermutP_eq : forall A (l:list A), PermutP (@eq A) l l.
 Proof.
  induction l. 
  constructor.
  apply PermutP_cons; trivial.
 Qed.

 Lemma PermutP_app_comm : forall A (l1 l2:list A), 
  PermutP (@eq _) (l1++l2) (l2++l1).
 Proof.
  induction l1; simpl; intros.
  rewrite <- app_nil_end; apply PermutP_refl; unfold reflexive; trivial.
  constructor; trivial.
 Qed.

 Lemma PermutP_In : forall (A:Type) (d1 d2:list A) (x:A), 
  PermutP (@eq _) d1 d2 -> In x d1 -> In x d2.
 Proof.
  intros A d1 d2 x Hperm. 
  induction Hperm.
  tauto.
  intro Hx; simpl in Hx; destruct Hx as [Hx | Hx].
  rewrite <- Hx; rewrite H. 
  apply in_or_app; right; simpl; tauto.
  apply in_or_app.
  destruct (@in_app_or _ _ _ _ (IHHperm Hx)).
  left; assumption.
  right; simpl; right; assumption.
 Qed.

 Lemma PermutP_rev : forall (A:Type) (l:list A), 
  PermutP (@eq _) l (rev l).
 Proof.
  induction l; simpl; try constructor; auto.
  rewrite <- app_nil_end; trivial.
 Qed.

 Lemma PermutP_map : forall A B C (R:A -> C -> Prop) (f:B -> C) la lb,
  PermutP (fun a b => R a (f b)) la lb <->
  PermutP R la (map f lb).
 Proof.
  intros A B C R f la lb; split.
  induction 1; simpl.
  constructor.
  rewrite map_app; simpl; constructor; trivial.
  rewrite <- map_app; trivial.
  generalize la; clear la.
  induction lb; intros la H; simpl in H; inversion H; subst.
  constructor.
  destruct l1'; discriminate. 
  destruct (PermutP_cons_r_inv H) as [b [lla [llb [W1 [W2 W3] ] ] ] ]; subst.
  rewrite W1.
  apply PermutP_sym; constructor; trivial.
  apply PermutP_sym; auto.
 Qed.

 Lemma PermutP_weaken : forall A B (R1 R2:A -> B -> Prop) la lb,
  (forall a b, In a la -> In b lb -> R1 a b -> R2 a b) -> 
  PermutP R1 la lb -> PermutP R2 la lb.
 Proof.
  induction la; intros.
  (* base case *)
  inversion H0; constructor.
  (* inductive case *)
  induction lb; inversion H0; subst.
  elim (app_cons_not_nil l1' l2' x' (eq_sym H3)).
  apply permP_swap.
  apply H; auto using in_eq.
  rewrite <-H3; apply in_or_app; right; apply in_eq.
  apply IHla. 
  intros; apply H; auto using in_cons, in_eq.
  rewrite <-H3; destruct (in_app_or _ _ _  H2); 
  auto using in_or_app, in_cons.
  trivial.
 Qed.
 
 Lemma Permut_seq_R : forall (R:nat -> nat -> Prop) k a b, 
  (forall i, 0 <= i < k -> R (i + a) (i + b)) -> 
  PermutP R (seq a k) (seq b k).
 Proof.
  induction k; simpl; intros.
  constructor.
  apply PermutP_cons.
  refine (H 0 _); auto with arith.
  apply IHk; intros.
  repeat rewrite <- plus_n_Sm.
  refine (H (S i) _); omega.
 Qed.

 Lemma PermutP_seq_shift : forall n i1 i2 g ,
  PermutP (fun v1 v2 => v1 = g v2) (seq (S i1)  n) (seq (S i2) n) ->
  PermutP (fun v1 v2 => S v1 = g (S v2)) (seq i1 n) (seq i2 n).
 Proof.
  intros. 
  rewrite (PermutP_map (fun v1 v2 => S v1 = g v2) S).
  apply PermutP_sym.
  apply PermutP_weaken with (fun v1 v2 => g v1 = S v2); [ auto | ].
  rewrite (PermutP_map (fun v1 v2 => g v1 = v2) S).
  rewrite seq_shift, seq_shift.
  apply PermutP_sym.
  apply PermutP_weaken with (fun v1 v2 => v1 = g v2); auto.
 Qed.

End PERMUTATION_PROP.

Section PERMUTP_BIJECTION.

 Variable T : Type.

 Variables f f_inv : T -> T.

 Lemma PermutP_NoDup : forall (l1:list T) (l2:list T),
  NoDup l1 ->
  NoDup l2 ->
  (forall x, In x l1 -> f (f_inv x) = x) ->
  (forall x, In x l2 -> f_inv (f x) = x) ->
  (forall x, In x l2 -> In (f x) l1) ->
  (forall x, In x l1 -> In (f_inv x) l2) ->
  PermutP (fun v1 v2 => v1 = f v2) l1 l2.
 Proof.
  induction l1; intros l2 H H0 f_inv_spec f_spec H1 H2.
  destruct l2.
  constructor.
  elim (H1 t); simpl; auto.
  destruct (In_split (f_inv a) l2) as (hd, (tl, H3)).
  apply H2; simpl; auto.
  
  subst; constructor.
  rewrite f_inv_spec; simpl; auto.

  inversion_clear H.
  apply IHl1; clear IHl1; trivial; intros.
  apply NoDup_remove_1 with (f_inv a); trivial.
  intros; apply f_inv_spec; simpl; auto.
  intros; apply f_spec.
  apply in_app_or in H; destruct H; apply in_or_app; simpl; auto.
 
  assert (In (f x) (a::l1)).
   apply H1; apply in_app_or in H; apply in_or_app; simpl; destruct H; auto.
  simpl in H5; destruct H5; trivial.
  elim (@NoDup_remove_2 _ _ _ _ H0); rewrite H5; rewrite f_spec; trivial.
  apply in_app_or in H.
  apply in_or_app; simpl; destruct H; auto.
  
  assert (H6:In (f_inv x) (hd ++ f_inv a :: tl)) by (apply H2; simpl; auto).
  apply in_or_app.
  destruct (in_app_or _ _ _ H6).
  auto.
  destruct H5; [ | auto].
  elim H3; clear H3. 

  apply (f_equal f) in H5.
  rewrite f_inv_spec in H5; [ | simpl; auto].
  rewrite H5, f_inv_spec; simpl; auto.
 Qed.

End PERMUTP_BIJECTION.


(** Sequences *)

Lemma seq_append : forall k1 k2 n, 
 seq n (k1 + k2) = seq n k1 ++ seq (n + k1) k2.
Proof.
 induction k1; simpl; intros.
 rewrite plus_0_r; trivial.
 rewrite <- plus_n_Sm, IHk1; trivial.
Qed.

Lemma seq_S : forall m n,
 seq n (S m) = seq n m ++ (n + m :: nil).
Proof.
 induction m; intros.
 rewrite plus_0_r; trivial.
 change (S (S m)) with (1 + (S m)).
 rewrite seq_append, IHm. 
 replace (seq n (S m)) with (seq n 1 ++ seq (n + 1) m)
  by (rewrite IHm, <- seq_append, IHm; trivial).
 rewrite app_ass, <- plus_assoc; trivial.
Qed.

Lemma le_In_seq : forall n m i,
 m <= i < n + m ->
 In i (seq m n).
Proof.
 induction n; intros m i [Hge Hle].
 elimtype False; omega.

 case (le_lt_or_eq _ _ Hle); clear Hle; intro.
 change (S n) with (1 + n).
 rewrite seq_append.
 apply in_or_app.
 case (le_lt_or_eq _ _ Hge); clear Hge; intro.
 right.
 rewrite plus_comm.
 change (1 + m) with (S m).
 rewrite <- seq_shift.
 destruct i; [elim (lt_n_O _ H0) | ].
 apply in_map; apply IHn; omega.

 simpl; auto.

 simpl in H; injection H; intro.
 clear H Hge; subst.
 destruct n.
 simpl; auto.

 simpl plus.
 change (S (S n)) with (1 + (S n)).
 rewrite seq_append.
 rewrite (plus_comm m 1).
 change (1 + m) with (S m).
 rewrite <- seq_shift.
 apply in_or_app.

 right; simpl plus.
 apply in_map.
 apply IHn; omega.
Qed.

Lemma In_seq_le : forall n m i, 
 In i (seq m n) ->
 m <= i < n + m.
Proof.
 induction n; intros m i Hi.
 elim Hi.
 simpl in Hi.
 case Hi; clear Hi; intro Hi.
 rewrite <- Hi; omega.
 rewrite <- seq_shift in Hi.
 rewrite in_map_iff in Hi.
 destruct Hi as [i0 [H1 H2] ].
 rewrite <- H1.
 generalize (IHn _ _ H2); omega.
Qed.

Lemma seq_PermutP : forall k p, 
 p <= k ->
 PermutP (@eq _) (seq 0 k) (seq p (k - p) ++ seq 0 p).
Proof.
 intros k p H.
 pattern k at 1; replace k with (p + (k - p)); auto with arith.
 rewrite seq_append, plus_0_l.
 apply PermutP_app_comm.
Qed.


(** Sorted lists *)

Definition monotone (A B:Type) (R1:A -> A -> Prop) (R2:B -> B -> Prop) (f:A -> B) :=
 forall a1 a2, R1 a1 a2 -> R2 (f a1) (f a2).

Hint Unfold monotone.

Lemma sorted_map : forall (A B:Type) (R1:A -> A -> Prop) (R2:B -> B -> Prop) (f:A -> B) 
 (l:list A), 
 monotone R1 R2 f ->
 sort R1 l ->
 sort R2 (map f l).
Proof.
 induction l; intros; simpl.
 constructor.
 apply sort_inv in H0.
 constructor.
 firstorder.
 induction l; constructor.
 apply H.
 destruct H0 as [? H1].
 apply lelistA_inv in H1; trivial.
Qed.

Lemma lelistA_filter : forall (A:Type) (R:A -> A -> Prop) (P:A -> bool) 
 (a:A) (l:list A),
 transitive A R ->
 sort R l ->
 lelistA R a l ->
 lelistA R a (filter P l).
Proof.
 induction l; intros.
 constructor.
 apply sort_inv in H0.
 apply lelistA_inv in H1.
 simpl; case (P a0).
 constructor; trivial.
 apply IHl.
 trivial.
 firstorder.
 destruct l.  
 constructor.
 destruct H0.
 apply lelistA_inv in H2.
 constructor.
 apply H with a0; trivial.
Qed.  

Lemma sorted_filter : forall (A:Type) (R:A -> A -> Prop) (P:A -> bool) 
 (l:list A), 
 transitive A R ->
 sort R l ->
 sort R (filter P l).
Proof.
 induction l; intros.
 constructor.
 apply sort_inv in H0; simpl; firstorder.
 case (P a); [ | trivial].
 constructor; trivial.
 apply lelistA_filter; trivial.
Qed.

Lemma sorted_cons : forall l a,
 sort lt l ->
 (forall b, In b l -> a < b) ->
 sort lt (a :: l).
Proof.
 induction l; intros; constructor.
 trivial.
 constructor.
 trivial.
 constructor.
 apply H0.
 apply in_eq.
Qed.

Lemma sorted_seq : forall n a, sort lt (seq a n).
Proof.
 induction n; simpl; intros.
 constructor.
 apply sorted_cons.
 trivial.
 intros.
 apply In_seq_le in H.
 omega.
Qed.

Lemma NoDup_seq : forall a b, NoDup (seq a b).
Proof.
 induction b.
 constructor.
 rewrite seq_S.
 apply NoDup_app with (1:=IHb).
 constructor; [intro H; elim H | constructor].
 intros x [H | H] Hin.
 subst; apply In_seq_le in Hin; omega.
 elim H.
Qed.

Lemma eqb_spec_beg A (a_beq : A -> A -> bool):
  (forall x : A,
    (fun x0 : A => forall y : A, a_beq x0 y = true -> x0 = y) x) ->
  (forall x : A,
    (fun x0 : A => forall y : A, x0 = y -> a_beq x0 y = true) x) ->
  (forall (x y : A), if a_beq x y then x = y else x <> y).
Proof.
 intros.
 case_eq (a_beq x y); intros.
 apply H; trivial.
 intro.
 rewrite (H0 x y H2) in H1.
 discriminate.
Qed.
