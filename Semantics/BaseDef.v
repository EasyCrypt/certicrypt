(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * BaseDef.v: Extensions to the standard library and the library of 
   Paulin & Audebaud *)

Set Implicit Arguments.

Require Import Bool.
Require Import List.
Require Export Relations.
Require Export Cover.
Require Export Prelude.
Require Import BoolEquality.
Require Import Even Div2 Wf_nat.
Require Import CCMisc.
Require Export Coq.Program.Basics.

Declare Module Univ : Universe.

Module CP := CoverFun Univ.

Export Univ CP RP PP MP UP.

Close Scope nat_scope.
Open Scope U_scope.

(* TODO: remove this once added to ALEA *)
Lemma Unth_prod : forall n m, [1/]1+n * [1/]1+m == [1/]1+(pred (S n * S m)).
Proof.
 intros; apply Unth_eq; simpl.
 rewrite plus_Nmult_distr.
 rewrite Nmult_Umult_assoc_right; auto.
 rewrite Nmult_n_Unth.
 rewrite Nmult_mult_assoc.
 rewrite Nmult_Unth_simpl_right.
 rewrite Nmult_n_Unth; auto.
Qed.

Lemma Unth_pow : forall n c, ([1/]1+n) ^ c == [1/]1+pred ((S n) ^ c).
Proof.
 induction c.
 simpl; auto.
 simpl; rewrite IHc, Unth_prod.
 replace 
  (S n * S (pred ((S n) ^ c)))%nat with
  ((S n) ^ c + n * (S n) ^ c)%nat; trivial.
 change 
  (S n * S (pred ((S n) ^ c)))%nat with 
  ((S (pred ((S n) ^ c))) + n * S (pred ((S n) ^ c)))%nat.
 rewrite <- (S_pred ((S n) ^ c) 0); trivial.
 apply pow_lt_0; auto with arith.
Qed.

Lemma Unth_le_pow : forall n c, (0 < c)%nat -> ([1/]1+n) ^ c <= [1/]1+n ^ c.
Proof.
 intros n c Hle; apply Ole_trans with ([1/]1+pred ((S n) ^ c)).
 rewrite Unth_pow; trivial.
 apply Unth_anti_mon.
 induction c.
 inversion Hle.
 simpl in IHc |- *.
 destruct c.
 simpl; trivial.
 apply le_trans with (n * ((S n) ^ (S c)))%nat.
 apply mult_le_compat_l.
 apply le_trans with (pred ((S n) ^ (S c)))%nat; auto with arith.
 rewrite pred_of_minus.
 assert (0 < (S n) ^ (S c))%nat by (apply pow_lt_0; auto with arith).
 omega.
Qed.

Lemma mu_fone_0 : forall A d, 
 0 == mu d (fone A) -> 
 forall f, 0 == mu d f.
Proof.
 intros; apply Ole_antisym.
 trivial.
 rewrite H; apply mu_monotonic; intro; trivial.
Qed. 

Hint Resolve mu_fone_0.

Lemma mu_fone_0_eq : forall A d, 
 0 == mu d (fone A) -> forall f g, mu d f == mu d g.
Proof.
 intros; apply Oeq_trans with (0:U); [symmetry |]; apply mu_fone_0; trivial.
Qed.

Lemma mu_0 : forall A (d:Distr A), mu d (fun _ => 0) == 0.
Proof.
 intros; rewrite (mu_cte d 0); trivial.
Qed.


 (** [Uabs_diff a b] corresponds to [|a - b|] in the interval [[0,1]].
     When [~a == b], one of the subtractions in the sum will underflow and the 
     other one will correspond to the absolute value of the subtraction *)
 Definition Uabs_diff (a b:U) := (a - b) + (b - a).

 Add Morphism Uabs_diff 
 with signature Oeq (O:=U) ==> Oeq (O:=U) ==> Oeq (O:=U) 
 as Uabs_diff_morphism.
 Proof.
  unfold Uabs_diff; intros.
  rewrite H; rewrite H0; auto.
 Qed.

 Lemma Uabs_diff_sym : forall x y, Uabs_diff x y == Uabs_diff y x.
 Proof. 
  unfold Uabs_diff; intros; trivial. 
 Qed.

 Lemma Uabs_diff_compat_eq : forall x, Uabs_diff x x == 0.
 Proof.
  unfold Uabs_diff; intros.
  rewrite Uminus_le_zero; auto.
 Qed.

 Lemma Uabs_diff_compat_le : forall x y, x <= y -> Uabs_diff x y == y - x.
 Proof.
  unfold Uabs_diff; intros.
  rewrite Uminus_le_zero ; trivial.
 Qed.

 Lemma Uabs_diff_zero : forall x y,  Uabs_diff x y == 0 <-> x==y.
 Proof.
  unfold Uabs_diff; split; intros H.
  apply (Ueq_orc x y); [auto|auto|].
  intro H'.
  apply (Ule_total x y); [auto|intro H''|intro H''].
    absurd (0 == x - y + (y - x))%U.
      rewrite Uplus_sym.
      apply Uplus_neq_zero_left.
      apply Uminus_lt_non_zero.
      apply Ule_diff_lt; assumption.
      apply Oeq_sym in H; assumption.
    absurd (0 == x - y + (y - x))%U.
      apply Uplus_neq_zero_left.
      apply Uminus_lt_non_zero.
      apply Ule_diff_lt; [assumption|auto].
      apply Oeq_sym in H; assumption.

  rewrite H, Uminus_eq; auto.
 Qed.

 Section UMINUS_TRIANGLE_INEQ.

  Variables a b c : U.
  Hypothesis hyp : a<=b.

  (* c <= a <= b *)
  Lemma Uminus_triangle_ineq1 : 
   c <= a ->
   b - a <= (a - c) + (b - c).
  Proof.
   intros; apply Ole_trans with (b - c); auto.
  Qed.

  (* a <= c <= b *)
  Lemma Uminus_triangle_ineq2 : 
   a <= c ->
   c <= b ->
   b - a <= (c - a) + (b - c).
  Proof.
   intros; assert ((c-a) <= c).
   apply Uplus_le_perm_left; trivial.
   rewrite Uplus_sym.
   rewrite <- (Uminus_assoc_right _ _ _ H0 H1).
   rewrite (Uminus_assoc_right _ _ _ (Ole_refl c) H).
   rewrite (Uminus_le_zero _ _ (Ole_refl c)); Usimpl; trivial.
  Qed.
  
  (* a <= b <= c *)
  Lemma Uminus_triangle_ineq3 :
   b <= c ->
   b - a <= c - a + (c - b).
  Proof.
   intros; apply Ole_trans with (c-a).
   apply Uminus_le_compat_left; trivial.
   apply Ule_plus_right.
  Qed.

  Lemma Uabs_diff_triangle_ineq_simpl : 
   Uabs_diff a b <= Uabs_diff a c + Uabs_diff c b.
  Proof.
   unfold Uabs_diff.
   rewrite (Uminus_le_zero _ _ hyp).
   apply (Ule_total a c); trivial;
    intros H; rewrite (Uminus_le_zero _ _ H); 
    repeat (rewrite Uplus_zero_left); repeat (rewrite Uplus_zero_right).
   apply (Ule_total c b); trivial; intros H0; rewrite (Uminus_le_zero _ _ H0);
    repeat (rewrite Uplus_zero_left); repeat (rewrite Uplus_zero_right).
   apply Uminus_triangle_ineq2; assumption.
   apply Uminus_triangle_ineq3; assumption.
   assert (c<=b) by (apply Ole_trans with a; trivial).
   rewrite (Uminus_le_zero _ _ H0); rewrite Uplus_zero_left.
   apply Uminus_triangle_ineq1; assumption.
  Qed.

  Lemma Uplus_minus_le : forall x y z, (x + y) - z <= x + (y - z).
  Proof.
   intros.
   apply (Ule_total y z); trivial; intros.
   auto.
   apply (Ule_total y ([1-] x)); trivial; intros.
   rewrite <- Uplus_minus_assoc_right; trivial.
   apply Uplus_le_perm_left.
   rewrite (Uplus_sym z), <- Uplus_assoc.
   rewrite Uminus_plus_simpl; trivial.
  Qed.

  Lemma Uabs_diff_plus_aux : forall f1 f2 g1 g2,
   f1 + g1 <= f2 + g2 ->
   Uabs_diff (f1 + g1) (f2 + g2) <= Uabs_diff f1 f2 + Uabs_diff g1 g2.
  Proof.
   intros; rewrite Uabs_diff_compat_le; trivial.
   rewrite <- Uminus_assoc_left, Uplus_sym.
   transitivity (g2 + (f2 - f1) - g1).
   apply Uminus_le_compat; auto using Uplus_minus_le.
   rewrite Uplus_sym.
   transitivity (f2 - f1 + (g2 - g1)).
   apply Uplus_minus_le.
   unfold Uabs_diff; auto.
  Qed.

  Lemma Uabs_diff_plus : forall f1 f2 g1 g2, 
    Uabs_diff (f1 + g1) (f2 + g2) <= Uabs_diff f1 f2 + Uabs_diff g1 g2.
  Proof.
   intros; apply (Ule_total (f1 + g1) (f2 + g2)); trivial; intros.
   apply Uabs_diff_plus_aux; trivial.
   intros; rewrite Uabs_diff_sym, (Uabs_diff_sym f1),(Uabs_diff_sym g1).
   apply Uabs_diff_plus_aux; trivial.
  Qed.

  Lemma Uabs_diff_mult : forall c f g, 
   Uabs_diff (c * f) (c * g) == c * Uabs_diff f g.
  Proof.
   intros; apply (Ule_total f g); trivial; intros.
   repeat rewrite Uabs_diff_compat_le; auto.
   rewrite Uabs_diff_sym, (Uabs_diff_sym f).
   repeat rewrite Uabs_diff_compat_le; auto.
  Qed.

 End UMINUS_TRIANGLE_INEQ.

 (** [ |a-b| <= |a-c| + |b-c| ] *)
 Lemma Uabs_diff_triangle_ineq : forall a b c, 
  Uabs_diff a b <= Uabs_diff a c + Uabs_diff c b.
 Proof.
  intros; apply (Ule_total a b); trivial.
  apply Uabs_diff_triangle_ineq_simpl; trivial.
  rewrite Uplus_sym.
  rewrite Uabs_diff_sym.
  rewrite (Uabs_diff_sym c).
  rewrite (Uabs_diff_sym a).
  apply Uabs_diff_triangle_ineq_simpl; trivial.
 Qed.

 Definition fabs_diff (A:Type) (f h : MF A) : MF A := 
               fun x =>  Uabs_diff (f x) (h x). 
 Implicit Arguments fabs_diff [A].

 Lemma fabs_diff_eq_compat: forall (A:Type) (f1 h1 f2 h2: MF A),
   f1 == f2 -> h1 == h2 ->
   fabs_diff f1 h1 == fabs_diff f2 h2.
 Proof.
   unfold fabs_diff; intros.
   refine (ford_eq_intro _); intro a.
   rewrite (ford_eq_elim H a), (ford_eq_elim H0 a); trivial.
 Qed.

 Lemma Uabs_diff_mu_compat : forall (A:Type) (f' g':A-o>U) (d: Distr A),
   Uabs_diff (mu d f') (mu d g') <= mu d (fabs_diff f' g').
 Proof.
  intros.
  rewrite (@mu_stable_plus _ d (fminus f' g') (fminus g' f')).
  apply Uplus_le_compat; apply mu_stable_le_minus.
    intros x.
    apply (Ule_total (f' x) (g' x)); [auto| |].
      intro H'; rewrite (Uminus_le_zero _ _ H'); trivial.
      intro H'; apply Uinv_le_perm_right; rewrite (Uminus_le_zero _ _ H'); trivial.
 Qed.

(** ** Predicate operators *)

Lemma Bool_leb_refl : forall b, Bool.leb b b.
Proof. 
 destruct b; trivial; simpl; trivial. 
Qed.

Lemma Bool_leb_trans : forall x y z, Bool.leb x y -> Bool.leb y z -> Bool.leb x z.
Proof. 
 destruct x; simpl; intros; subst; trivial.
Qed.

Definition boolO := mk_ord Bool_leb_refl Bool_leb_trans.

Lemma Oeq_eq_bool : forall (b1 b2:boolO), b1 == b2 -> b1 = b2.
Proof.
 intros b1 b2 (H1, H2); destruct b1; simpl in *; auto.
 destruct b2; trivial.
Qed.
 
Lemma Bool_le_true : forall b, Bool.leb b true.
Proof. 
 destruct b; simpl; trivial. 
Qed.

Hint Resolve Bool_le_true Bool_leb_refl.


Section PREDICATES.

 Variable A : Type.

 Variables P Q : A -o> boolO.

 Definition andP : A -o> boolO := fun x:A => andb (P x) (Q x).

 Definition orP : A -o> boolO := fun x:A => orb (P x) (Q x).

 Definition implP : A -o> boolO := fun x:A => implb (P x) (Q x).

 Definition negP : A -o> boolO := fun x:A => negb (P x).

 Definition falseP : A -o> boolO := fun _:A => false.

 Definition trueP : A -o> boolO := fun _:A => true.

 Definition disjoint := forall x:A, P x && Q x = false.

End PREDICATES.

Infix "[||]" := orP (right associativity, at level 30).
Infix "[&&]" := andP (right associativity, at level 30).
Infix "[=>]" := implP (right associativity, at level 30).

Add Parametric Morphism A : (orP (A:=A)) 
 with signature 
  (Ole (o:=A -o> boolO)) ++> (Ole (o:=A -o> boolO)) ++> (Ole (o:=A -o> boolO))
 as orP_le_compat.
Proof.
 unfold orP; intros P Q Hle P0 Q0 Hle0 a.
 assert (W:=Hle a); assert (W0:=Hle0 a).
 destruct (P a); simpl in W |- *.
 rewrite W; trivial. 
 destruct (Q a); simpl in W0 |- *; trivial.
Qed.

Add Parametric Morphism A : (orP (A:=A))
 with signature (Oeq (O:=A -o> boolO)) ==> (Oeq (O:=A -o> boolO)) ==> (Oeq (O:=A -o> boolO))
 as orP_eq_compat.
Proof.
 intros P Q [H1 H2] P0 Q0 [H3 H4]; split; apply orP_le_compat; trivial.
Qed.

Add Parametric Morphism A : (andP (A:=A))
 with signature (Ole (o:=A -o> boolO)) ++> (Ole (o:=A -o> boolO)) ++> (Ole (o:=A -o> boolO))
 as andP_le_compat.
Proof.
 unfold andP; intros P Q H P0 Q0 H0 a.
 assert (W:=H a); assert (W0:=H0 a).
 destruct (P a); simpl in W |- *; trivial.
 rewrite W; trivial.
Qed.

Add Parametric Morphism A : (andP (A:=A))
 with signature (Oeq (O:=A -o> boolO)) ==> (Oeq (O:=A -o> boolO)) ==> (Oeq (O:=A -o> boolO))
 as andP_eq_compat.
Proof.
 intros P Q [H1 H2] P0 Q0 [H3 H4]; split; apply andP_le_compat; trivial.
Qed.

Add Parametric Morphism A : (implP (A:=A))
 with signature (Ole (o:=A -o> boolO)) --> (Ole (o:=A -o> boolO)) ++> (Ole (o:=A -o> boolO))
 as implP_le_compat.
Proof.
 unfold implP; intros P Q H P0 Q0 H0 a.
 assert (W:=H a); assert (W0:=H0 a).
 destruct (Q a); simpl in W |- *; trivial.
 rewrite W; simpl; trivial.
Qed.

Add Parametric Morphism A : (implP (A:=A)) 
 with signature (Oeq (O:=A -o> boolO)) ==> (Oeq (O:=A -o> boolO)) ==> (Oeq (O:=A -o> boolO))
 as implP_eq_compat.
Proof.
 intros P Q [H1 H2] P0 Q0 [H3 H4]; split; apply implP_le_compat; trivial.
Qed.

Add Parametric Morphism A : (negP (A:=A)) 
 with signature (Ole (o:=A -o> boolO)) --> (Ole (o:=A -o> boolO))
 as negP_le_compat.
Proof.
 unfold negP; intros P Q H a.
 assert (W:=H a); destruct (Q a); simpl; trivial.
 rewrite W; trivial.
Qed.

Add Parametric Morphism A : (negP (A:=A))
 with signature (Oeq (O:=A -o> boolO)) ==> (Oeq (O:=A -o> boolO))
 as negP_eq_compat.
Proof.
 intros P Q [H1 H2]; split; apply negP_le_compat; trivial.
Qed.


Section PRED_PROP.

 Variable A : Type.

 Variables P Q R : A -o> boolO.

 Lemma andP_comm : (P [&&] Q) == Q [&&] P.
 Proof.
  apply ford_eq_intro; intros x; unfold andP, andb.
  case (P x); case (Q x); trivial.
 Qed.

 Lemma andP_assoc : (P [&&] Q) [&&] R == P [&&] (Q [&&] R).
 Proof.
  apply ford_eq_intro; intro x; unfold andP, andb.
  case (P x); case (Q x); case (R x); trivial.
 Qed.

 Lemma andP_orP_distrib_r : P [&&] (Q  [||] R) == (P [&&] Q) [||] (P [&&] R).
 Proof.
  apply ford_eq_intro; intro x; unfold andP, orP.
  rewrite andb_orb_distrib_r; trivial.
 Qed.

 Lemma orP_andP_distrib_r : P [||] (Q [&&] R) == (P [||] Q) [&&] (P [||] R).
 Proof.
  apply ford_eq_intro; intro x; unfold andP, orP.
  rewrite orb_andb_distrib_r; trivial.
 Qed.

 Lemma proj1_BP : P [&&] Q <= P.
 Proof.
  intro; unfold andP.
  destruct (P x); simpl; trivial.
 Qed.

 Lemma proj2_BP : P [&&] Q <= Q.
 Proof.
  intro; unfold andP.
  destruct (P x); simpl; auto.
 Qed.

 Lemma negP_involutive : negP (negP P) == P.
 Proof.
  apply ford_eq_intro; intro x; unfold negP; rewrite negb_involutive; trivial.
 Qed.

 Lemma orP_neg : P [||] negP P == @trueP _.
 Proof.
  apply ford_eq_intro; intro x; unfold negP, orP, trueP; destruct (P x); trivial.
 Qed.

 Lemma disjoint_negP : disjoint P (negP P).
 Proof.
  red; unfold negP; intros; apply andb_negb_r.
 Qed.

 Lemma andP_true_l : (@trueP _) [&&] P == P.
 Proof. 
  intros; apply ford_eq_intro; trivial. 
 Qed.

 Lemma andP_true_r : P [&&] (@trueP _) == P.
 Proof. 
  intros; apply ford_eq_intro; intros; unfold andP, trueP;
  rewrite (andb_true_r (P n)); trivial.
 Qed.
 
End PRED_PROP.


(** ** Restriction of distributions *) 

Definition restr A (P:A -o> boolO) (f:A -O-> U) : A -O-> U := 
 fun a => if P a then f a else 0.

Definition charfun A (P:A -o> boolO) : A -O-> U := restr P (fone _).

Add Parametric Morphism A : (restr (A:=A)) 
 with signature (Ole (o:=A -o> boolO)) ++> (Ole (o:=A -O-> U)) ++> (Ole (o:=A -O-> U))
 as restr_le_compat.
Proof.
 intros P Q H f g H0 a.
 unfold restr; simpl.
 assert (W:=H a); destruct (P a); trivial.
 rewrite W; trivial.
Qed.

Add Parametric Morphism A : (restr (A:=A)) 
 with signature (Oeq (O:=A -o> boolO)) ==> (Oeq (O:=A -O-> U)) ==> (Oeq (O:=A -O-> U)) 
 as restr_eq_compat.
Proof.
 intros P Q [H1 H2] f g [H3 H4]; split; apply restr_le_compat; trivial.
Qed.

Add Parametric Morphism A : (charfun (A:=A)) 
 with signature (Ole (o:=A -o> boolO)) ++> (Ole (o:=A -O-> U))
 as charfun_le_compat.
Proof.
 intros; unfold charfun; apply restr_le_compat; trivial.
Qed.

Add Parametric Morphism A : (charfun (A:=A))
 with signature (Oeq (O:=A -o> boolO)) ==> (Oeq (O:=A -O-> U)) 
 as charfun_eq_compat.
Proof.
 intros; unfold charfun; apply restr_eq_compat; trivial.
Qed.

Definition Fmult A (f1 f2:A -o> U) : A -o> U := fun a => f1 a * f2 a.

Add Parametric Morphism A : (Fmult (A:=A))
 with signature Ole (o:=A -o> U) ++> Ole (o:=A -o> U) ++> Ole (o:=A -o> U)
 as Fmult_le_compat.
Proof.
 intros f g H f0 g0 H0 a; unfold Fmult; apply Umult_le_compat; trivial.
Qed.

Add Parametric Morphism A : (Fmult (A:=A)) 
 with signature Oeq (O:=A -o> U) ==> Oeq (O:=A -o> U) ==> Oeq (O:=A -o> U)
 as Fmult_eq_compat.
Proof.
 intros f g H f0 g0 H0; unfold Fmult.
 apply ford_eq_intro; intro a.
 apply Umult_eq_compat; apply ford_eq_elim; trivial.
Qed.

Lemma restr_and : forall (A:Type) (P Q:A -o> boolO) f, 
 restr (P [&&] Q) f == restr P (restr Q f).
Proof.
 intros; refine (ford_eq_intro _); intro a.
 unfold restr, andP; case (P a); trivial.
Qed.

Lemma restr_or : forall (A:Type) (P Q :A -o> boolO) f, 
 restr (P [||] Q) f == fplus (restr P f) (restr (negP P) (restr Q f)).
Proof.
 intros; refine (ford_eq_intro _); intro a.
 unfold restr, orP, negP, fplus; case (P a); auto.
Qed.

Lemma restr_or_le : forall (A:Type) (P Q:A -o> boolO) f, 
 restr (P [||] Q) f <= fplus (restr P f) (restr Q f).
Proof.
 intros; rewrite restr_or.
 intro a; unfold fplus, restr, negP; case (P a); auto.
Qed.

Lemma disjoint_restr_or : forall (A:Type) (P Q:A -o> boolO),
 disjoint P Q -> 
 forall f, restr (P [||] Q) f == fplus (restr P f) (restr Q f).
Proof.
 intros; rewrite restr_or. 
 refine (ford_eq_intro _); intro a.
 assert (W:=H a); unfold fplus, restr, negP.
 destruct (P a); [ | trivial].
 destruct (Q a); [discriminate | trivial].
Qed.

Lemma restr_true : forall A f, restr (@trueP A) f == f.
Proof.
 intros; refine (ford_eq_intro _); intro a; trivial.
Qed.

Lemma restr_split : forall A (P:A -o> boolO) f,
 f == fplus (restr P f) (restr (negP P) f).
Proof.
 intros; rewrite <- disjoint_restr_or. 
 rewrite orP_neg, restr_true; trivial.
 apply disjoint_negP.
Qed.

Lemma restr_impl : forall (A:Type) (P Q:A -o> boolO) f,
 restr (P [=>] Q) f == fplus (restr (negP P) f) (restr P (restr Q f)).
Proof.
 intros; refine (ford_eq_intro _); intro a.
 unfold restr, implP, negP, fplus; intros.
 destruct (P a); simpl; auto.
Qed. 

Lemma restr_neg : forall (A:Type) (P:A -o> boolO) f, 
 restr (negP P) f  == fminus f (restr P f).
Proof.
 intros; refine (ford_eq_intro _); intro a.
 unfold negP, restr, fminus; intros.
 destruct (P a); simpl; auto.
Qed.

Lemma charfun_neg : forall (A:Type) (P:A -o> boolO), 
 charfun (negP P) == finv (charfun P).
Proof.
 unfold charfun; intros.
 rewrite (restr_neg P (fone _)).
 refine (ford_eq_intro _); intro a; unfold fminus, finv; auto.
Qed.

Lemma restr_charfun : forall (A:Type) (P Q:A -o> boolO), 
 restr P (charfun Q) == Fmult (charfun P) (charfun Q).
Proof.
 intros; refine (ford_eq_intro _); intro a.
 unfold charfun, restr, Fmult; intros; case (P a); auto.
Qed.

Lemma charfun_and : forall (A:Type) (P Q:A -o> boolO), 
 charfun (P [&&] Q) == Fmult (charfun P) (charfun Q).
Proof.
 intros; unfold charfun at 1.
 rewrite restr_and; fold (charfun Q); rewrite restr_charfun; trivial.
Qed.

Lemma restr_charfun_and : forall (A:Type) (P Q:A -o> boolO), 
 restr P (charfun Q) == charfun (P [&&] Q).
Proof.
 intros; unfold charfun at 1; rewrite <- restr_and; trivial.
Qed.

Lemma charfun_or : forall (A:Type) (P Q:A -o> boolO), 
 charfun (P [||] Q) == fplus (charfun P) (Fmult (finv (charfun P)) (charfun Q)).
Proof.
 unfold charfun at 1; intros; rewrite restr_or.
 fold (charfun P) (charfun Q).
 rewrite restr_charfun; rewrite charfun_neg; trivial.
Qed.

Lemma charfun_or_le : forall (A:Type) (P Q:A -o> boolO), 
 charfun (P [||] Q) <= fplus (charfun P) (charfun Q). 
Proof.
 intros; unfold charfun; apply restr_or_le.
Qed.

Lemma disjoint_fplusok_restr : forall (A:Type) (P Q:A -o> boolO) (f:A -O-> U),
 disjoint P Q ->
 fplusok (restr P f) (restr Q f).
Proof.
 unfold fplusok; intros.
 simpl; apply ford_le_intro; intro a.
 unfold restr, finv.
 generalize (H a); unfold andP.
 case (P a); case (Q a); intros; try discriminate; auto.
Qed.

Lemma disjoint_fplusok_charfun : forall (A:Type) (P Q:A -o> boolO),
 disjoint P Q ->
 fplusok (charfun P) (charfun Q).
Proof.
 unfold charfun; intros; apply disjoint_fplusok_restr; trivial.
Qed.

Lemma disjoint_charfun : forall (A:Type) (P Q:A -o> boolO), 
 disjoint P Q -> 
 Fmult (finv (charfun P)) (charfun Q) == charfun Q.  
Proof.
 intros; apply ford_eq_intro; intro a.
 unfold charfun, restr, finv, Fmult.
 assert (W:=H a); destruct (Q a); [ | auto].
 destruct (P a); [discriminate W | auto].
Qed.
  
Lemma disjoint_charfun_or : forall (A:Type) (P Q:A -o> boolO), 
 disjoint P Q ->
 charfun (P [||] Q) == fplus (charfun P) (charfun Q). 
Proof.
 intros; rewrite charfun_or.
 rewrite disjoint_charfun; trivial.
Qed.

Lemma charfun_impl : forall  (A:Type) (P Q:A -o> boolO),
 charfun (P [=>] Q) == fplus (finv (charfun P)) (Fmult (charfun P) (charfun Q)).
Proof.
 unfold charfun at 1; intros; rewrite restr_impl; rewrite <- restr_and.
 fold (charfun (negP P)) (charfun (P [&&] Q)); rewrite charfun_neg, charfun_and; trivial.
Qed.

Lemma charfun_and_impl : forall (A:Type) (P Q:A -o> boolO),
 charfun (P [&&] P [=>] Q) == charfun (P [&&] Q).
Proof.
 intros; rewrite charfun_and, charfun_and, charfun_impl.
 simpl; apply ford_eq_intro; unfold Fmult, fplus, finv, charfun, restr, fone.
 intro a; destruct (P a); repeat Usimpl; auto.
Qed.

Section PROBABILITY.
  
 Variable A : Type.

 Variable d : Distr A.

 Variables P Q R: A -o> boolO.

 Definition distr0 : Distr A.
  exists (@fmon_cte (A -O-> U) U 0); intro x; intros; auto.
 Defined.

 Definition drestr := Mlet d (fun a => if P a then Munit a else distr0).

 Lemma mu_drestr : forall f, mu drestr f == mu d (restr P f).
 Proof.
  unfold drestr, restr; intros; rewrite Mlet_simpl.
  apply mu_stable_eq.
  simpl; apply ford_eq_intro; intros n.
  destruct (P n); trivial. 
 Qed.

 Lemma distr_OR_restr : forall f, 
  mu d (restr (P [||] Q) f) <=
  mu d (fplus (restr P f) (restr Q f)). 
 Proof.
  intros; apply mu_monotonic; apply restr_or_le.
 Qed.

 Lemma distr_OR_charfun :  
  mu d (charfun (P [||] Q)) <=
  mu d (charfun P) + mu d (charfun Q). 
 Proof.
  intros; eapply Ole_trans;[ | apply mu_le_plus].
  apply mu_monotonic.
  apply charfun_or_le.
 Qed. 

 Lemma distr_OR_restr_disj : forall f,
  disjoint P Q ->
  mu d (restr (P [||] Q) f) ==
  mu d (restr P f) + mu d (restr Q f). 
 Proof.
  intros f H; rewrite <- (mu_stable_plus d (disjoint_fplusok_restr f H)).
  apply mu_stable_eq.
  apply disjoint_restr_or; trivial.
 Qed.

 Lemma distr_OR_charfun_disj : 
  disjoint P Q ->
  mu d (charfun (P [||] Q)) ==
  mu d (charfun P) + mu d (charfun Q). 
 Proof.
  unfold charfun; intros; apply distr_OR_restr_disj; trivial.
 Qed.

 Lemma mu_neg_restr : forall f, 
  mu d (restr (negP P) f)  ==
  mu d f - mu d (restr P f).
 Proof.
  intros; rewrite <- stable_minus_distr; [ | auto | auto | ].
  apply mu_stable_eq; apply restr_neg.  
  intro a; unfold restr; case (P a); trivial.
 Qed.

 Lemma mu_neg_charfun : 
  mu d (charfun (negP P)) == mu d (fone _) - mu d (charfun P).
 Proof.
  unfold charfun; apply mu_neg_restr. 
 Qed. 

 Lemma mu_impl_charfun : 
  mu d (charfun (P [=>] Q))  ==
  mu d (fone _) - mu d (charfun P) + mu d (Fmult (charfun P) (charfun Q)).
 Proof.
  apply Oeq_trans with 
   (mu d (fplus (finv (charfun P)) (Fmult (charfun P) (charfun Q)))).
  apply mu_stable_eq; apply charfun_impl.
  rewrite (@mu_stable_plus _ d (finv (charfun P))).
  rewrite mu_inv_minus; trivial.
  unfold fplusok, finv, Fmult; intro; auto.
 Qed.

 Lemma mu_range_strenghten : 
  range P d ->
  mu d (charfun Q) == mu d (charfun (P [&&] Q)).
 Proof.
  intros Hd.
  apply (range_eq Hd); intros a Ha.
  unfold andP, charfun, restr; rewrite Ha; trivial.
 Qed.

 Lemma mu_range_restr : forall (A:Type) (d:Distr A) (P:A -> bool),
  range P d ->
  forall f, mu d f == mu d (restr P f). 
 Proof.
  intros; apply range_eq with (1:=H); intros.
  unfold restr; rewrite H0; trivial.
 Qed.

 Lemma mu_restr_split : forall f,
  mu d f == mu d (restr P f) + mu d (restr (negP P) f).
 Proof.
  intros; transitivity (mu d (fplus (restr P f) (restr (negP P) f))).
  apply mu_stable_eq; apply restr_split.
  apply mu_stable_plus; apply disjoint_fplusok_restr; apply disjoint_negP.
 Qed.

 Lemma mu_restr_fplus : forall f g,
  mu d (restr P (fplus f g)) == mu d (fplus (restr P f) (restr P g)).
 Proof.
  intros; apply mu_stable_eq.
  refine (ford_eq_intro _); intro x.
  intros; unfold restr, fplus; case (P x); Usimpl; trivial.
 Qed.

 Lemma mu_restr_cte : forall k,
  mu d (restr P (fcte _ k)) == k * mu d (restr P (fone _)).
 Proof.
  intros.
  rewrite <- (@mu_stable_mult _ _ _).
  apply mu_stable_eq.
  refine (ford_eq_intro _); intro x.
  unfold restr, fmult, fcte, fone; case (P x); Usimpl; trivial.
 Qed.


End PROBABILITY.


Lemma charfun_range : forall A (d:Distr A) (P:A -o> boolO),
 mu d (charfun P) == mu d (fone _) ->
 range P d.
Proof.
 red; intros.
 transitivity (mu d (restr (P [||] negP P) f)).
 rewrite distr_OR_restr_disj. 
 transitivity (mu d (fun _ => 0) +  0).
 rewrite mu_0; auto.
 apply Uplus_eq_compat.
 apply mu_stable_eq; simpl; apply ford_eq_intro; intros.
 unfold restr; assert (W:= H0 n); destruct (P n); auto.
 split; trivial. 
 transitivity (mu d (charfun (negP P))).
 apply mu_monotonic; unfold charfun; intro; apply restr_le_compat; auto.
 rewrite mu_neg_charfun, H; auto.
 apply disjoint_negP.
 apply mu_stable_eq; simpl; apply ford_eq_intro; unfold restr, orP, negP.
 intro n; destruct (P n); trivial.
Qed.


Definition feq (A:Type) (O:ord) (f1 f2:A -> O) := forall x, f1 x == f2 x.

Implicit Arguments feq [A O].

Infix "===" := feq (at level 70).

Lemma feq_refl : forall (A:Type) (O:ord) (f:A -> O), f === f.
Proof. 
 unfold feq; trivial.
Qed.

Lemma feq_sym : forall (A:Type) (O:ord) (f1 f2:A -> O), f1 === f2 -> f2 === f1.
Proof.
 unfold feq; intros; symmetry; trivial.
Qed.

Lemma feq_trans : forall  (A:Type) (O:ord) (f1 f2 f3:A -> O), 
 f1 === f2 -> f2 === f3 -> f1 === f3.
Proof.
 unfold feq; intros; transitivity (f2 x); trivial.
Qed.

Add Parametric Relation A (O:ord) : (A -> O) (@feq A O)
 reflexivity proved by (@feq_refl A O)
 symmetry proved by (@feq_sym A O)
 transitivity proved by (@feq_trans A O)
 as feq_rel.

Add Parametric Morphism A B : (Mlet (A:=A) (B:=B))
 with signature Oeq (O:=Distr A) ==> (@feq A (Distr B)) ==> Oeq (O:=Distr B)
 as Mlet_morph. 
Proof.
 intros; apply Mlet_eq_compat; trivial.
 apply ford_eq_intro; trivial.
Qed.

Hint Immediate feq_refl.

Add Parametric Morphism A : (drestr (A:=A))
 with signature Oeq (O:=Distr A) ==> Oeq (O:=A -o> boolO) ==> Oeq (O:=Distr A)
 as drestr_morph.
Proof.
 intros d1 d2 H f g H0; unfold drestr.
 apply Mlet_morph; trivial.
 intro a; rewrite (Oeq_eq_bool (ford_eq_elim H0 a)); trivial.
Qed.

Hint Resolve mu_fone_0_eq mu_0.


Section FINITE.

 Variable A : Type.

 Definition finite_sum (f:A -> U) (l:list A) :=
  List.fold_right (fun a res => f a + res) 0 l.

 Lemma finite_sum_app : forall f l1 l2, 
  finite_sum f (l1 ++ l2) == finite_sum f l1 + finite_sum f l2.
 Proof.
  induction l1; simpl; intros; trivial.
  auto.
  rewrite IHl1; auto.
 Qed.

 Lemma finite_sum_cons : forall f a l, 
  finite_sum f (a::l) == f a + finite_sum f l.
 Proof.
  trivial.
 Qed.

 Lemma finite_sum_In : forall f l a,
  In a l ->
  f a <= finite_sum f l.
 Proof.
  intros f l a H; induction l.
  elim H.
  simpl in H; case H; clear H; intro H.
  rewrite H; simpl; trivial.
  eapply Ole_trans; [ apply IHl; trivial | ].
  simpl; trivial.
 Qed.

 Lemma finite_sum_mult_le : forall f k l,
  k * finite_sum f l <= finite_sum (fmult k f) l.
 Proof.
  induction l; simpl.
  trivial.
  rewrite <- IHl; apply Udistr_plus_left_le.
 Qed.

End FINITE.

Lemma finite_sum_le : forall (A:Type) (f1 f2:A -o> U) l,
 (forall x, In x l -> (f1 x <= f2 x)%tord) ->
 (finite_sum f1 l <= finite_sum f2 l)%tord.
Proof.
 induction l; simpl; trivial; intros.
 apply Uplus_le_compat; auto.
Qed.
 
Lemma finite_sum_eq : forall (A:Type) (f1 f2 : A-o>U) l,
 (forall x, In x l -> (f1 x == f2 x)%tord) ->
 (finite_sum f1 l == finite_sum f2 l)%tord.
Proof.
 induction l; simpl; trivial; intros.
 apply Uplus_eq_compat; auto.
Qed.


Lemma finite_sum_notIn : forall (A:Type) (v:A) (f:A->U),
 (forall x, x <> v -> f x == 0) ->
 forall l, ~In v l -> finite_sum f l == 0.
Proof.
 induction l; simpl; intros;[trivial | ].
 rewrite H; firstorder.
Qed.

Lemma finite_sum_notIn2 : forall (A:Type) (f:A -> U) l,
 (forall x, In x l -> f x == 0) ->
 finite_sum f l == 0.
Proof.
 induction l; simpl; intros;[trivial | ].
 rewrite H; firstorder.
Qed.

Lemma finite_sum_cte : forall (A:Type) (f:A -> U) l (v : U),
 (forall x, In x l -> f x == v) ->
 finite_sum f l == (length l) */ v.
Proof.
 induction l; simpl; trivial; intros.
 rewrite IHl.
 rewrite H.
 destruct (length l).
 Usimpl; trivial.
 trivial.
 auto.
 intros; apply H.
 auto.
Qed.

Lemma finite_sum_mult : forall (A:Type) (f:A -> nat) (v:U) (l:list A),
 finite_sum (fun a => f a */ v) l == 
 fold_right (fun a r => (f a + r)%nat) 0%nat l */ v.
Proof.
 induction l; simpl; intros; auto.
 rewrite IHl.
 rewrite <- plus_Nmult_distr; auto.
Qed.

Lemma finite_sum_full : forall (A:Type) (v:A) (f:A->U),
 (forall x, x <> v -> f x == 0) ->
 forall l,
  In v l ->
  NoDup l ->
  finite_sum f l == f v.
Proof.
 intros.
 destruct (In_split _ _ H0) as (l1, (l2, Heq)); subst.
 assert (W:= NoDup_remove_2 _ _ _ H1).
 rewrite finite_sum_app; simpl.
 repeat rewrite (@finite_sum_notIn _ v); auto.
 Usimpl; auto.
 intro; apply W; apply in_or_app; auto.
 intro; apply W; apply in_or_app; auto.
Qed.

Lemma finite_sum_Perm : forall A B f1 f2 (l1:list A) (l2:list B), 
 PermutP (fun x1 x2 => @Oeq U (f1 x1) (f2 x2)) l1 l2 ->
 finite_sum f1 l1 == finite_sum f2 l2.
Proof.
 induction 1; simpl; trivial.
 rewrite H, IHPermutP, finite_sum_app, finite_sum_app, finite_sum_cons; auto.
Qed. 

Lemma finite_sum_Permutation : forall A (f:A -> U) l1 l2,
 PermutP (@eq _) l1 l2 ->
 finite_sum f l1 == finite_sum f l2.
Proof.
 intros; apply finite_sum_Perm.
 induction H; constructor; subst; auto.
Qed.

Lemma finite_sum_map : forall A B (F:A -> B) f l,
 finite_sum f (map F l) == finite_sum (fun v => f (F v)) l.
Proof.
 intros; apply finite_sum_Perm.
 apply PermutP_sym; rewrite <- PermutP_map. 
 apply PermutP_refl; intros; trivial.
Qed.

Lemma finite_sum_rev : forall A (f:A -> U) l, 
 finite_sum f l == finite_sum f (rev l).
Proof.
 intros; apply finite_sum_Permutation.
 apply PermutP_rev.
Qed.
 
Section SUMDOM.

 Variable A : Type.

 Variable default : A.

 Definition nth_dom (dom:list A) : (A -o> U) -m> (natO -o> U).
 intros dom.
 refine (@mk_fmono (A -o> U) (natO -o> U)
  (fun f n => [1/]1+pred (length dom) * f (nth n dom default)) _).
 unfold monotonic; intros; auto.
 Defined.

 Definition sum_dom (dom:list A) : M A := 
  (UP.Sigma <_> (length dom)) @ (nth_dom dom).

 (* TODO: Make [sum_dom] more efficient (without using [Sigma]), e.g.

 Section SUMAUX.

  Variable A : Type.
  Variable f : (A -o> U).
  Variable p : U.

  Fixpoint sumaux (l:list A) {struct l} : U :=
   match l with
    | nil => 0
    | a::l' => p * f a + sumaux l' 
   end.

 End SUMAUX.
 
 Definition sum_dom (l:list A) : M A.
  intro l.
  exists (fun (f:A-O->U) => sumaux f ([1/]1+pred (length l)) l). 
  red; intros.  
  apply sumaux_le_compat; trivial.
 Defined.
 *)

 Lemma comp_fold_right : forall def f f' (l:list A),
  (forall n, (n < length l)%nat -> f n = f' (nth (length l - S n) l def)) ->
  comp Uplus 0 f (length l) = fold_right (fun a res => f' a + res) 0 l.
 Proof.
  induction l; simpl; intros; trivial.
  rewrite IHl.
  rewrite (H (length l)); auto with arith.
  rewrite <- minus_n_n; trivial.
  intros; rewrite H; auto with arith.
  case_eq (length l - n)%nat; intros.
  elimtype False; omega.
  replace n0 with (length l - S n)%nat; trivial; omega.
 Qed.

 Lemma sigma_finite_sum : forall f l,
  sigma (fun k => f (nth k l default)) (length l) ==
  finite_sum f l.
 Proof.
  simpl; intros.
  rewrite finite_sum_rev.
  unfold finite_sum; intros.
  pattern (length l); rewrite <- rev_length.
  rewrite (comp_fold_right default 
   (fun n : nat => f (nth n l default))
   (fun a => f a)); trivial.
  intros; rewrite rev_nth.
  replace (length l - S (length (rev l) - S n))%nat with n; trivial.
  rewrite rev_length in *; omega.
  rewrite rev_length in *; omega.
 Qed.

 Lemma sum_dom_finite : forall dom f, 
  sum_dom dom f ==
  finite_sum (fun a => [1/]1+(pred (length dom)) * f a) dom.
 Proof.
  unfold sum_dom; simpl; intros.
  refine (sigma_finite_sum (fun a : A => [1/]1+pred (length dom) * f a) dom).
 Qed.

 Opaque sigma.

 Lemma sum_dom_stable_inv : forall l, stable_inv (sum_dom l).
 Proof.
  unfold stable_inv; destruct l; intros. 
  trivial.
  simpl; rewrite sigma_inv. 
  trivial.
  simpl length; auto.
 Qed.

 Lemma sum_dom_stable_plus : forall l, stable_plus (sum_dom l).
 Proof.
  unfold stable_plus; simpl; destruct l; intros.
  simpl; auto.
  simpl length; simpl pred.
  transitivity 
   (sigma 
    (fplus 
     (fun n => [1/]1+length l * f (nth n (a :: l) default))
     (fun n => [1/]1+length l * g (nth n (a :: l) default)))
    (S (length l))).
  apply sigma_eq_compat; intros; unfold fplus.
  rewrite Udistr_plus_left; [ | refine (H _)]; trivial.
  unfold fplus; apply sigma_plus.
 Qed.
 
 Lemma sum_dom_stable_mult : forall l, stable_mult (sum_dom l).
 Proof.
  unfold stable_mult; simpl; destruct l; intros; auto.
  rewrite <- sigma_mult.  
  apply sigma_eq_compat; intros; unfold fmult; auto.
  unfold retract; intros.
  transitivity ([1/]1+length l); trivial.
  transitivity ([1-] sigma (fun n => [1/]1+length l) k0).
  exact (fnth_retract (length l) _ H).
  apply Uinv_le_compat; apply sigma_le_compat; auto.
 Qed.
 
 Lemma sum_dom_continuous: forall l, continuous (sum_dom l).
 Proof.
  unfold continuous, sum_dom; intros.
  assert (X:=sigma_continuous1 ((nth_dom l) @ h) (length l)).
  match type of X with ?x1 <= ?x2 =>
   transitivity x1; [ | transitivity x2; [exact X | ] ]
  end; trivial.
  simpl; apply sigma_le_compat; intros.
  rewrite <- lub_eq_mult; apply lub_le_compat; auto.
 Qed.

 Lemma sum_dom_zero : forall l P f,
  (forall a, In a l -> P a) -> 
  (forall a, P a -> f a == 0) ->
  sum_dom l f == 0.
 Proof.
  induction l; intros P f Hl Hf.
  trivial.
  simpl; apply sigma_zero; intros k Hk.
  rewrite Hf; [auto | ].
  apply Hl; destruct k.
  simpl; auto.
  right; apply nth_In; auto with arith.
 Qed.

 Definition sum_support (dom:list A) : Distr A :=
  @Build_distr A
  (sum_dom dom) 
  (sum_dom_stable_inv dom)
  (sum_dom_stable_plus dom)
  (sum_dom_stable_mult dom)
  (sum_dom_continuous dom).

 Lemma sum_support_lossless : forall l, 
  l <> nil -> 
  mu (sum_support l) (fun _ => 1) == 1. 
 Proof.
  unfold sum_support, sum_dom; intros; simpl.
  destruct l.  
  elim H; trivial.
  intros; transitivity (sigma (fun _ => [1/]1+length l) (S (length l))); auto.
 Qed.

 Lemma sum_support_const : forall k l,
  l <> nil ->
  mu (sum_support l) (fun _ => k) == k.
 Proof.
  intros; refine (mu_cte_eq _ _ _).
  apply sum_support_lossless; trivial.
 Qed.

 Lemma sum_support_stable_eq : forall dom f g,
  (forall v, In v dom -> f v == g v) -> 
  mu (sum_support dom) f == mu (sum_support dom) g.
 Proof.
  intros dom f g Heq; simpl.
  apply sigma_eq_compat; intros k H.
  apply Umult_eq_compat_right; apply Heq.
  apply nth_In; trivial.
 Qed.

 Lemma sum_support_in : forall a f l,
  In a l ->
  f a == 1 ->
  [1/]1+pred (length l) <= mu (sum_support l) f.
 Proof.
  intros; rewrite (sum_dom_finite l f).
  transitivity ([1/]1+pred (length l) * f a); [rewrite H0; auto | ].
  rewrite <- (finite_sum_mult_le f ([1/]1+pred (length l))).
  Usimpl; apply finite_sum_In; trivial.
 Qed.
 
End SUMDOM.

 Lemma sum_dom_permut_eq : forall (B1 B2 : Type) (def1:B1) (def2:B2) 
  (dom1:list B1) (dom2:list B2) (f1:B1->U) (f2:B2->U),
  PermutP (fun x1 x2 => @Oeq U (f1 x1) (f2 x2)) dom1 dom2 ->
  sum_dom def1 dom1 f1 == sum_dom def2 dom2 f2.
 Proof.
  intros; repeat rewrite sum_dom_finite.
  apply finite_sum_Perm.
  rewrite (PermutP_length H).
  eapply PermutP_weaken  with (2:= H).
  intros a b _ _ Heq; rewrite Heq; trivial.
 Qed.


(*** Remove This Defined in Prog *) 
(** * Properties of the product of two distributions *)

(* TODO: This should be part of ALEA *)

Add Parametric Morphism A B : (prod_distr (A:=A) (B:=B))
 with signature Oeq (O:=Distr A) ==> Oeq (O:=Distr B) ==> Oeq (O:=Distr (A * B))
 as prod_distr_morphism.
Proof.
 intros; unfold prod_distr.
 apply Mlet_morph; trivial.
 intro; apply Mlet_morph; simpl; auto.
Qed.

Lemma continuous2_prod_distr : forall A B,
 continuous2 (D1:=cDistr A) (D2:=cDistr B) (D3:=cDistr (A * B)) (Prod_distr A B).
Proof.
 red; intros.
 assert (H:Prod_distr A B (lub (c:=cDistr A) f) (lub (c:=cDistr B) g) == 
           prod_distr (lub (c:=cDistr A) f) (lub (c:=cDistr B) g)).
 rewrite Prod_distr_simpl; trivial.
 rewrite H; unfold prod_distr.
 transitivity
  (Mlet (lub f)
   (lub (c:=A -O-> cDistr (A*B)) 
    (ford_shift (fun x1 => (MLet B (A*B) @ g) <_> (fun x2 => Munit (x1,x2)))))).
  apply (Mlet_le_compat (A:=A) (B:=A*B)); auto.
  rewrite Mlet_lub_le.
  apply lub_le_compat; auto.
Qed.

Lemma lub_prod_distr : forall A B (F1:natO -m> cDistr A) (F2:natO -m> cDistr B),
 prod_distr (lub F1) (lub F2) == 
 lub (c:=cDistr (A*B)) ((Prod_distr A B @2 F1) F2).
Proof.
 intros A B; exact (lub_cont2_comp2_eq (@continuous2_prod_distr A B)).
Qed.


Section PROD_COMM.

 Definition prod_comm (A B : Type) (d1:Distr A) (d2:Distr B) :=
  prod_distr d2 d1 == Mlet (prod_distr d1 d2) (fun p => Munit (snd p, fst p)). 

 Lemma prod_comm_distr0 : forall A B (d:Distr B),
  prod_comm (distr0 A) d.
 Proof.
  unfold prod_comm, prod_distr; intros.
  apply eq_distr_intro; intro; simpl.
  apply (@mu_0 B).
 Qed.

 Lemma prod_comm_Munit : forall A B (a:A) (d:Distr B),
  prod_comm (Munit a) d.
 Proof.
  unfold prod_comm, prod_distr; intros.
  apply eq_distr_intro; trivial.
 Qed.

 Opaque sigma.

 Lemma prod_comm_sum_support : forall A B (a:A) (l:list A) (d:Distr B),
  prod_comm (sum_support a l) d.
 Proof.
  unfold prod_comm, prod_distr; intros.
  apply eq_distr_intro; simpl; intros.
  assert (length l <= S (pred (length l)))%nat.
  destruct l; auto with arith.
  generalize (pred (length l)) H; clear H.
  induction (length l); intros.
  rewrite sigma_0.
  transitivity (mu d (fun _ => 0)).
  apply (mu_stable_eq d).
  simpl; apply ford_eq_intro; intro; rewrite sigma_0; trivial.
  apply mu_0.
  rewrite sigma_S; simpl pred.  
  transitivity (mu d 
   (fplus (fmult ([1/]1+n0) (fun x => f (x, nth n l a)))
          (fun x => sigma (fun n1 => [1/]1+n0 * f (x, nth n1 l a)) n))).
  apply (mu_stable_eq d).
  simpl; apply ford_eq_intro; simpl; intro.
  rewrite sigma_S; trivial.
  assert (X:=mu_stable_plus d); unfold stable_plus in X; rewrite X; clear X.
  apply Uplus_eq_compat.
  apply (mu_stable_mult d).
  rewrite IHn; auto with arith.
  unfold fplusok, finv; intro; simpl.
  refine (@retractS (fun n1 : nat => [1/]1+n0 * f (x, nth n1 l a)) n _).
  apply retract_unif; intros.
  rewrite <- (Umult_one_right ([1/]1+n)).
  apply Umult_le_compat; auto with arith.
 Qed.

 Lemma sum_support_comm : forall A B (d:distr B) a (l:list A) f,
  mu (sum_support a l) (fun x => mu d (fun y => f y x)) ==
  mu d (fun y => mu (sum_support a l) (fun x => f y x)).
 Proof.
  intros A B d a l f.  
  generalize (eq_distr_elim (prod_comm_sum_support a l d) (fun p => f (fst p) (snd p))).
  repeat rewrite Mlet_simpl; intro; symmetry; trivial.
 Qed.

 Add Parametric Morphism A B : (prod_comm (A:=A) (B:=B))
  with signature Oeq (O:=Distr A) ==> Oeq (O:=Distr B) ==> iff 
  as prod_comm_morphism_aux.
 Proof.
  intros d1 d2 H d3 d4 H0; unfold prod_comm.
  rewrite H; rewrite H0; split; trivial.
 Qed. 

 Lemma prod_comm_sym : forall A B (d1:Distr A) (d2:Distr B),
  prod_comm d1 d2 -> prod_comm d2 d1.
 Proof.
  unfold prod_comm; intros.
  rewrite H; apply eq_distr_intro; trivial.
 Qed.

End PROD_COMM.


Add Parametric Morphism A B : (prod_comm (A:=A) (B:=B))
 with signature Oeq (O:=Distr A) ==> Oeq (O:=Distr B) ==> iff 
 as prod_comm_morphism.
Proof.
 intros d1 d2 H d3 d4 H0; unfold prod_comm.
 rewrite H; rewrite H0; split; trivial.
Qed. 

Lemma prod_distr_Mlet_l : forall (A B C:Type) (d1:Distr A) (d2:Distr C) (F:A -> Distr B),
 prod_distr (Mlet d1 F) d2 == Mlet d1 (fun x => prod_distr (F x) d2).
Proof.
 intros; apply eq_distr_intro; trivial.
Qed.

Lemma prod_distr_Mlet_r : forall (A B C:Type)(d1:Distr A) (d2:Distr C) (F:A -> Distr B),
 prod_comm d1 d2 ->
 prod_distr d2 (Mlet d1 F) == Mlet d1 (fun x => prod_distr d2 (F x)).
Proof.
 intros; apply eq_distr_intro; simpl; intros.
 exact (eq_distr_elim H (fun p =>  mu (F (snd p)) (fun x1 => f ((fst p), x1)))).
Qed.

Lemma prod_distr_Mlet2 : forall (A B A' B' : Type) (d1:Distr A) (d2:Distr A') 
 (F1:A -> Distr B) (F2:A' -> Distr B'),
 (forall x, prod_comm (F1 x) d2) ->
 prod_distr (Mlet d1 F1) (Mlet d2 F2) ==
 Mlet (prod_distr d1 d2) (fun p => prod_distr (F1 (fst p)) (F2 (snd p))).
Proof.
 intros; rewrite prod_distr_Mlet_l.
 assert (H0:(fun x => prod_distr (F1 x) (Mlet d2 F2)) ===
            (fun x => Mlet d2 (fun y => prod_distr (F1 x) (F2 y)))).
 intro; apply prod_distr_Mlet_r; apply prod_comm_sym; trivial.
 rewrite H0; apply eq_distr_intro; trivial.
Qed.

Lemma prod_comm_Mlet : forall (A B C : Type) (d1:Distr A) (d2:Distr C) (F:A -> Distr B),
 prod_comm d1 d2 ->
 (forall x, prod_comm (F x) d2) ->
 prod_comm (Mlet d1 F) d2.
Proof.
 intros; unfold prod_comm.
 rewrite prod_distr_Mlet_l; rewrite prod_distr_Mlet_r; trivial.
 rewrite Mcomp; apply Mlet_morph; trivial.
Qed.

Lemma prod_comm_drestr : forall (A B:Type) (f:A -> bool) (dA:distr A) (d:Distr B),
 prod_comm dA d ->
 prod_comm (drestr dA f) d.
Proof.
 unfold drestr; intros.
 apply prod_comm_Mlet; trivial.
 intro a; destruct (f a).
 apply prod_comm_Munit.
 apply prod_comm_distr0.
Qed.

Lemma prod_comm_Mlet2 : forall (A B A' B' : Type) (d1:Distr A) (d2:Distr A') 
 (F1:A -> Distr B) (F2:A' -> Distr B'),
 prod_comm d1 d2 ->
 (forall x, prod_comm (F1 x) d2) ->
 (forall x, prod_comm (F2 x) d1) ->
 (forall x y, prod_comm (F1 x) (F2 y)) ->
 prod_comm (Mlet d1 F1) (Mlet d2 F2).
Proof.
 intros; apply prod_comm_Mlet; intros; apply prod_comm_sym; apply prod_comm_Mlet.
 apply prod_comm_sym; trivial.
 trivial.
 apply prod_comm_sym; trivial.
 intro; apply prod_comm_sym; trivial.
Qed.

Lemma prod_comm_lub : forall A B (f:natO -m> cDistr A) (d:cDistr B),
 (forall n, prod_comm (f n) d) ->
 prod_comm (lub f) d.
Proof.
 intros; rewrite <- (lub_cte d).
 unfold prod_comm.
 do 2 rewrite lub_prod_distr.
 apply eq_distr_intro; intro g; simpl.
 apply lub_eq_compat; simpl.
 refine (@ford_eq_intro _ _ _ _ _); intro; simpl.
 apply (eq_distr_elim (H n) g). 
Qed.

Lemma finite_sum_prod (A1 A2 : Type) k1 k2 l1 l2 (f : (A1 * A2) -> U) :
 ((length l1) <= k1)%nat -> ((length l2) <= k2)%nat ->  (0 < k1)%nat  -> (0 < k2)%nat ->
 finite_sum (fun a : (A1 * A2) => [1/]1+pred (k1*k2) * f a) (list_prod l1 l2) ==
 finite_sum
 (fun a : A1 => [1/]1+pred k1 * finite_sum (fun a0 : A2 => [1/]1+pred k2 * (f (a,a0))) l2) l1.
Proof.
 induction l1; simpl in *; intros; trivial.
 rewrite finite_sum_app, finite_sum_map; simpl; auto.
 rewrite IHl1; try omega; try apply H1.
 apply Uplus_eq_compat_left.
 generalize H0; clear H0 IHl1.
 induction l2; simpl in *; intros; auto.
 rewrite IHl2; try omega.
 rewrite Udistr_plus_left, Umult_assoc, Unth_prod.
 rewrite <- (S_pred k1 0%nat), <- (S_pred k2 0%nat) ; trivial; try split; try omega.
 transitivity ([1/]1+pred k2); auto.
 transitivity ([1-] finite_sum (fun a1 : A2 => [1/]1+pred k2) l2).  
 rewrite <- (sigma_finite_sum a0), Unth_prop_sigma.
 apply Uinv_le_compat.
 apply sigma_incr; omega.
 apply Uinv_le_compat.
 repeat rewrite <- (sigma_finite_sum a0).
 apply sigma_le_compat; intros; auto.
Qed.

Section RANGE.

 Variable A:Type.
 Variable P: A -> Prop. 

 Lemma distr0_range : forall (d:Distr A), 
  0 == mu d (fone A) -> range P d.
 Proof.
  red; auto.
 Qed.

 Lemma lub_range : forall (F:natO -m> cDistr A),
  (forall n, range P (F n)) -> range P (lub F).
 Proof.
  red; intros.
  transitivity (lub (fmon_cte natO (O2:=U) 0)).
  symmetry; apply lub_cte. 
  simpl; apply lub_eq_compat.
  refine (ford_eq_intro _).
  intro; simpl; apply H; trivial.
 Qed.

 Lemma range_stable_eq : forall (d1 d2:Distr A), 
  d1 == d2 -> range P d1 -> range P d2.
 Proof.
  unfold range; intros.  
  rewrite <- (eq_distr_elim H); auto.
 Qed.

End RANGE.

Hint Immediate distr0_range.

Lemma range_True : forall A (d:Distr A), range (fun _ => True) d.
Proof.
 unfold range; intros.
 transitivity (mu d (fun _ => 0)).
 symmetry; apply mu_0.
 apply mu_stable_eq.
 refine (ford_eq_intro _); auto.
Qed.

Lemma range_weaken : forall (A:Type) (P1 P2:A -> Prop),
 (forall x, P1 x -> P2 x) ->  forall d, range P1 d -> range P2 d.
Proof.
 unfold range; intros; auto.
Qed.

Definition Fimp (A:Type) (P1 P2:A -> Prop) := forall a, P1 a -> P2 a.

Lemma Fimp_trans : forall (A:Type) (P1 P2 P3:A -> Prop), 
 Fimp P1 P2 -> Fimp P2 P3 -> Fimp P1 P3.
Proof. 
 unfold Fimp; auto.
Qed.

Lemma Fimp_refl :  forall (A:Type) (P:A -> Prop), Fimp P P.
Proof. 
 unfold Fimp; trivial.
Qed. 

Add Parametric Relation A : (A -> Prop) (Fimp (A:=A))
 reflexivity proved by (@Fimp_refl A)
 transitivity proved by (@Fimp_trans A)
 as Fimp_rel.

Add Parametric Morphism A : (range (A:=A))
 with signature Fimp (A:=A) --> Oeq (O:=Distr A) ==> inverse impl 
 as range_morph2.
Proof.
 unfold Basics.flip, impl, Fimp; intros P Q H d1 d2 H0 H1.
 apply range_weaken with Q; trivial.
 apply range_stable_eq with d2; auto.
Qed.

Lemma range_Munit: forall (A B:Type) (P: A -> B -> Prop) x y,
  P x y -> range (fun xy => P (fst xy) (snd xy)) (Munit (x,y)).
Proof.
 intros A B P x y Hxy f Hf.
 refine (Hf (x,y) Hxy).
Qed.

Lemma range_Mlet: forall (A B:Type) (P:A -> Prop) (Q:B -> Prop)
 (d:Distr A) (F:A -> Distr B),
 range P d ->
 (forall x, P x -> range Q (F x)) ->
 range Q (Mlet d F).
Proof.
 unfold range; intros; simpl; auto.
Qed.

Lemma mu_range : forall A (P:A -> bool) (d:Distr A), 
 mu d (fun a => if P a then 1 else 0) == 1 ->
 range P d.
Proof.
 intros A P d H f Hf.
 apply Ole_antisym; [trivial | ].
 rewrite <- Uinv_one, <- (Uinv_eq_compat H).
 eapply Ole_trans; [ | apply mu_stable_inv].
 apply mu_le_compat; trivial.
 apply ford_le_intro; intro.
 unfold finv; case_eq (P n); intro.
 rewrite <- Hf; trivial.
 rewrite Uinv_zero; trivial.
Qed.

Lemma range_mu : forall A (P:A -> bool) (d:Distr A), 
 range P d ->
 mu d (fun a => if P a then 1 else 0) == mu d (fone _).
Proof.
 intros A P d H.
 apply range_eq with P.
 exact H.
 intros a Ha; rewrite Ha; trivial.
Qed.

Lemma range_strengthen : forall A (d:Distr A) (P Q:A -o> boolO),
 mu d (fone _) == 1%U ->
 range P d -> 
 range Q d ->
 range (P [&&] Q) d.
Proof.
 intros; apply mu_range.
 rewrite <- (mu_range_strenghten _ Q H0).
 transitivity (mu d (fone _)); [ | trivial].
 apply range_mu; trivial. 
Qed.


(** * Lift of a relation to a product distribution *)
Section RELATIONS.

 Variable A B:Type.

 Variable P Q: A -> B -> Prop.

 Hypothesis Pdec : forall x y, {P x y} + {~P x y}.

 Definition prodP := fun xy => P (fst xy) (snd xy).

 Definition caract2 p:= if Pdec (fst p) (snd p) then 1 else 0.
 
 Definition Fimp2 := forall x y, P x y -> Q x y.

End RELATIONS.


Lemma Fimp2_trans : forall (A B:Type) (P1 P2 P3:A -> B -> Prop),
 Fimp2 P1 P2 -> Fimp2 P2 P3 -> Fimp2 P1 P3.
Proof. 
 unfold Fimp2; auto. 
Qed.

Lemma Fimp2_refl :  forall (A B:Type) (P:A -> B -> Prop), Fimp2 P P.
Proof. 
 unfold Fimp2; trivial.
Qed.

Add Parametric Relation A B : (A -> B -> Prop) (Fimp2 (A:=A) (B:=B))
 reflexivity proved by (@Fimp2_refl A B)
 transitivity proved by (@Fimp2_trans A B)
 as Fimp2_rel.

(** Lifting a relation [R] to a product distribution [d].
    There shall exist two distributions [d1] and [d2] s.t. the projections
    of [d] coincide with each of them respectively, and [R] covers the whole
    support of [d].
*)
Record lift (A B:Type) (R:A -> B -> Prop) (d:Distr (A * B)) 
 (d1:Distr A) (d2:Distr B) : Type := {
  l_fst : forall f, mu d (fun x => f (fst x)) == mu d1 f;
  l_snd : forall f, mu d (fun x => f (snd x)) == mu d2 f;
  l_range : range (prodP R) d
}.

Lemma distr0_lift : forall A B (R:A -> B -> Prop), 
 lift R (distr0 _) (distr0 _) (distr0 _).
Proof.
 intros; constructor; trivial.
 apply distr0_range; trivial.
Qed.

Lemma lift_True : forall (A B:Type) (d1:Distr A) (d2:Distr B),
 mu d1 (fone _) == 1 ->
 mu d2 (fone _) == 1 ->
 lift (fun _ _ => True) (prod_distr d1 d2) d1 d2.
Proof.
 intros A B d1 d2.
 constructor; simpl; intros.
 apply (mu_stable_eq d1); simpl; apply ford_eq_intro; intros.
 change (fun _ => f n) with (fcte B (f n)).
 rewrite (mu_cte d2 (f n)), H0; trivial.
 change (mu d1 (fcte _ (mu d2 (fun b => f b))) == mu d2 f).
 rewrite (mu_cte d1), H, Umult_one_right; trivial.
 apply mu_stable_eq; trivial.
 refine (ford_eq_intro _); trivial.
 unfold prodP; apply range_True.
Qed.

Lemma lift_mu : forall (A B:Type) (R:A -> B -> Prop) (d1:Distr A) (d2:Distr B) d,
 lift R d d1 d2 ->
 forall f h,
  (forall a b, R a b -> f a == h b) -> mu d1 f == mu d2 h.
Proof.
 intros A B R d1 d2 d H f h Heq.
 destruct H as [H1 H2 H3].
 rewrite <- H1, <- H2.
 apply range_eq with (1:=H3); auto.
Qed.

Lemma lift_weaken : forall A B (P Q:A -> B -> Prop), 
 (forall x y, P x y -> Q x y) ->
 forall d d1 d2, lift P d d1 d2 -> lift Q d d1 d2.
Proof.
 intros A B P Q H d d1 d2 (Hfst, Hsnd, Hsupp).
 constructor; trivial.
 apply range_weaken with (prodP P); trivial.
 unfold prodP; auto.
Qed.

Lemma lift_eq_refl : forall A (d:distr A), 
 lift (@eq A) (Mlet d (fun x => Munit (x,x))) d d.
Proof.
 intros; constructor; intros.
 simpl; apply (mu_stable_eq d); refine (ford_eq_intro _); trivial.
 simpl; apply (mu_stable_eq d); refine (ford_eq_intro _); trivial.
 red; simpl; intros.
 transitivity (mu d (fzero A)).
 auto.
 apply (mu_stable_eq d); refine (ford_eq_intro _).
 intros; rewrite <- H; trivial.
 unfold prodP; trivial.
Qed.

Lemma lift_refl : forall (A:Type) (R:relation A),
 reflexive A R -> forall d, lift R (Mlet d (fun x => Munit (x,x))) d d.
Proof.
 intros A R R_refl d.
 apply lift_weaken with eq; [intros; subst; apply R_refl | ].
 unfold prod_distr; simpl.
 apply lift_eq_refl.
Qed.

Lemma lift_unit : forall A B (a:A) (b:B) (R:A -> B -> Prop), 
 R a b -> lift R (Munit (a,b)) (Munit a) (Munit b).
Proof.
 intros; constructor; trivial.
 unfold range; intros; rewrite Munit_eq; auto. 
Qed.

Lemma lift_Mlet : forall A1 A2 B1 B2 
 (R1:A1 -> B1 -> Prop) (R2:A2 -> B2 -> Prop) d d1 d2 F F1 F2,
 lift R1 d d1 d2 ->
 (forall x y, R1 x y -> lift R2 (F (x,y)) (F1 x) (F2 y)) ->
 lift R2 (Mlet d F) (Mlet d1 F1) (Mlet d2 F2).
Proof.
 intros; constructor; intros; simpl.
 rewrite <- H.(l_fst). 
 apply (range_eq H.(l_range)).
 intros (x,y) H1; apply (H0 _ _ H1).(l_fst). 
 rewrite <- H.(l_snd).
 apply (range_eq H.(l_range)).
 intros (x,y) H1; apply (H0 _ _ H1).(l_snd). 
 apply range_Mlet with (1:=H.(l_range)).
 intros (x,y) H1; apply (H0 _ _ H1).(l_range).
Qed.

Lemma lift_cond : forall A B (R:A -> B -> Prop) b dt dt1 dt2 df df1 df2,
 (b = true  -> lift R dt dt1 dt2) ->
 (b = false -> lift R df df1 df2) ->
 lift R (if b then dt else df) (if b then dt1 else df1) (if b then dt2 else df2).
Proof.
 destruct b; auto. 
Qed.

Lemma lift_stable_eq : forall A B (R:A -> B -> Prop) 
 (d d' : Distr (A*B)) (d1 d1':Distr A) (d2 d2':Distr B),
 d == d' -> 
 d1 == d1' -> 
 d2 == d2' -> 
 lift R d d1 d2 -> lift R d' d1' d2'.
Proof.
 intros A B R d d' d1 d1' d2 d2' Heq Heq1 Heq2 (Hfst, Hsnd, Hrange).
 constructor; intros.
 transitivity (mu d1 f); [rewrite <- Hfst | ]; auto. 
 transitivity (mu d2 f); [rewrite <- Hsnd | ]; auto. 
 apply range_stable_eq with (1:=Heq); trivial.
Qed.

Lemma lift_sym : forall A (R:A -> A -> Prop) (d:distr (A * A)) 
 (d1:Distr A) (d2:Distr A), 
 lift R d d1 d2 ->
 lift (transp _ R) (Mlet d (fun p => Munit (snd p, fst p))) d2 d1.
Proof.
 intros A R d d1 d2 (Hfst, Hsnd, Hrange).
 constructor; intros; [ | | unfold range]; simpl; auto.
Qed.

Add Parametric Morphism A B : (lift (A:=A) (B:=B))
 with signature Fimp2 (A:=A) (B:=B) --> 
  Oeq (O:=Distr (A * B)) ==> Oeq (O:=Distr A) ==> Oeq (O:=Distr B) ==> inverse impl
 as lift_morph.
Proof.
 unfold impl, Fimp2; intros R1 R2 H d1 d2 H0 d3 d4 H1 d5 d6 H2 H3.
 apply lift_weaken with R2; trivial.
 apply lift_stable_eq with d2 d4 d6; auto.
Qed.


Section LIFT_LUB.

 Variables A B : Type.
 Variable R : A -> B -> Prop.
 Variable F : natO -m> cDistr (A * B). 
 Variable F1 : natO -m> cDistr A.
 Variable F2 : natO -m> cDistr B.

 Hypothesis liftn : forall n, lift R (F n) (F1 n) (F2 n).

 Lemma lift_lub : lift R (lub F) (lub F1) (lub F2).
 Proof.
  constructor; intros; simpl.
  apply lub_eq_compat.
  refine (ford_eq_intro _); intro; simpl; apply (liftn n).(l_fst).
  apply lub_eq_compat.
  refine (ford_eq_intro _); intro; simpl; apply (liftn n).(l_snd).
  unfold range; intros.
  transitivity (lub (fmon_cte natO (O2:=U) 0)).
  symmetry; apply lub_cte.
  simpl; apply lub_eq_compat.
  refine (ford_eq_intro _); intro; simpl.
  apply (liftn n).(l_range); trivial.
 Qed.

End LIFT_LUB.


Section DISCRETE.
 
 Variable A : Type.

 Section In_class.

   Variable R : A -> A -> Prop.
   Variable uR : A -> MF A.
   Hypothesis cover_uR : forall a, cover (R a) (uR a).
   Hypothesis R_trans : transitive A R.
   Hypothesis R_sym : symmetric A R.
   Hypothesis R_refl : reflexive A R.

   Variable points : nat -> A.

   (* [not_first_repr k] decide if [points k] is not the first point in is class,
      in that case [points k] is not the representant of the class *)
   Definition not_first_repr k := sigma (fun i => uR (points k) (points i)) k.

   Lemma cover_not_first_repr :  
    cover (fun k => exc (fun k0 => (k0 < k)%nat /\ R (points k) (points k0))) not_first_repr.
   Proof.
    red; split; intros.
    apply H;[auto | intros k0 (H1, H2)].
    apply Ole_trans with (2:= sigma_le (fun i : nat => uR (points x) (points i)) H1).
    rewrite (cover_eq_one _ (cover_uR (points x)) H2); trivial.
    unfold not_first_repr; rewrite sigma_zero; trivial; intros.
    apply (cover_elim (cover_uR (points x)) (points k)); [auto | | ];
    intros [H4 H5]; trivial.
    elim H; apply exc_intro with k; auto.
  Qed.

  (* [in_classes a] decides in [a] is in relation with one element of [points] *)
  Definition in_classes a := serie (fun k => uR a (points k)).

  Definition In_classes a := exc (fun k => R a (points k)).

  Lemma cover_in_classes : cover In_classes in_classes.
  Proof.
   unfold In_classes; red; split; intros.
   apply H;[auto | intros k H1].
   apply Ole_trans with (2:=serie_le (fun k : nat => uR x (points k)) k).
   rewrite (cover_eq_one _ (cover_uR x) H1); trivial.
   unfold in_classes; rewrite serie_zero; trivial.
   intros k; apply (cover_elim (cover_uR x) (points k)); [auto | | ]; intros [H4 H5]; trivial.
    elim H; apply exc_intro with k; trivial.
  Qed.

  (* [in_class a k] decides in [a] is in relation with [points k] and
     [points k] is the representant of it class *)
  Definition in_class a k := 
     [1-] (not_first_repr k) * uR (points k) a.

  Definition In_class a k :=
     R (points k) a /\
     (forall k0, (k0 < k)%nat -> ~R (points k) (points k0)).
  
  Lemma cover_in_class : forall a, cover (In_class a) (in_class a).
  Proof.
   unfold in_class, In_class;split;intros.
   destruct H.
   rewrite (cover_eq_one _ (cover_uR (points x)) H); Usimpl.
   rewrite (cover_eq_zero _ cover_not_first_repr);[auto| ].
   intros Hex;apply Hex;[auto | intros].
   destruct H1;apply (H0 x0);trivial.
   apply (cover_elim (cover_uR (points x)) a);[auto | | ];intros [H1 H2].
   rewrite H2;trivial.
   apply (cover_elim cover_not_first_repr x);[auto | | ];intros [H3 H4].
   elim H;split;trivial.
   red;intros;apply H3.
   apply exc_intro with k0;auto.
   rewrite H4;Usimpl;auto.
  Qed.

  Lemma in_class_wretract : forall x, wretract (in_class x).
  Proof.
   red; intros.
   apply (cover_elim (cover_in_class x) k);[auto | | ];intros [H H0];
   rewrite H0;[auto | ].
   rewrite sigma_zero; [auto | intros].
   destruct H;apply (cover_eq_zero _ (cover_in_class x)).
   intros (H3, H4).
   elim (H2 _ H1).
   eapply R_trans;eauto.
  Qed.
 
  Lemma in_classes_refl : forall k, in_classes (points k) == 1.
  Proof.
   intros k; apply (cover_eq_one _ cover_in_classes).
   red; intros; apply exc_intro with k; trivial.
  Qed.

  Lemma cover_serie_in_class : cover (fun a => exc (In_class a)) (fun a => serie (in_class a)).
  Proof.
   split; intros.
   apply H;[auto | intros k H1].
   apply Ole_trans with (2:=serie_le (in_class x) k).
   rewrite (cover_eq_one _ (cover_in_class x) H1); trivial.
   rewrite serie_zero; trivial.
   intros k; apply (cover_elim (cover_in_class x) k); [auto | | ]; intros [H4 H5]; trivial.
   elim H; apply exc_intro with k; trivial.
  Qed.

  Lemma in_classes_in_class : forall a, 
     in_classes a == serie (in_class a).
  Proof.
   intros a; apply (cover_elim cover_in_classes a); [ auto | | ]; intros [H1 H2].
   rewrite H2; symmetry; apply serie_zero; intros.
   apply (cover_elim (cover_in_class a) k);[auto | | ];intros (H3, H4);rewrite H4;trivial.
   elim H1;destruct H3;apply exc_intro with k;auto.
   rewrite H2;split;trivial.
   assert (exc (In_class a)).
     apply H1;[auto | ].
     induction x using Wf_nat.lt_wf_ind; intros.
     apply (cover_elim cover_not_first_repr x); [ auto | | ]; intros [H3 H4].
     apply exc_intro with x; split;auto.
     red;intros;elim H3.
     apply exc_intro with k0;auto.
     apply H3;[auto | ].
     intros m (H5, H6);apply (H m);eauto.
   assert (W:= cover_eq_one a cover_serie_in_class H);simpl in W;rewrite W.
   trivial.
  Qed.

  Variable d : Distr A.

  Definition Discrete := range In_classes d.

  Definition coeff k := ([1-] (not_first_repr k)) * mu d (uR (points k)).

  Lemma mu_discrete : Discrete -> forall f, 
    (forall x y, R x y -> f x == f y) ->
    mu d f == discrete coeff points f.
  Proof.
   intros Hdiscr f Hf; rewrite discrete_simpl.
   unfold coeff.
   transitivity (serie (fun k => mu d (fun a => f a * (in_class a k)))).
   rewrite <- mu_serie_eq.
   unfold serie_fun.
   transitivity (mu d (fun a : A => in_classes a * f a)).
   apply range_cover with (P:= In_classes); trivial.
   apply cover_in_classes.
   apply mu_stable_eq; simpl; apply ford_eq_intro; intro a.
   rewrite Umult_sym, serie_mult; [ | apply in_class_wretract].
   Usimpl; apply in_classes_in_class.
   intros; apply wretract_le with (2:=in_class_wretract x); auto. 
   apply serie_eq_compat; intros.
   assert (W:= mu_stable_mult d (f (points k) * [1-] not_first_repr k )).
   rewrite Umult_sym, Umult_assoc, <- W.
   apply mu_stable_eq; simpl; apply ford_eq_intro; intros; unfold fmult.
   unfold in_class;rewrite Umult_assoc.
   apply (cover_elim (cover_uR (points k)) n); [auto | | ]; intros [H5 H6].
   rewrite H6; repeat Usimpl; trivial.
   rewrite (Hf _ _ H5);trivial.
  Qed. 

 End In_class.

 Variable carA : A -> MF A.

 Hypothesis carA_prop : forall a, cover (@eq A a) (carA a).

 Record is_Discrete (d:Distr A) : Type := mkDiscr {
  D_points : nat -> A;
  D_Discr : Discrete (@eq A) D_points d
 }.
  
 Lemma is_Discrete_eq_compat: forall (d1 d2:Distr A),
   d2 == d1 ->
   is_Discrete d2 ->
   is_Discrete d1.
 Proof.
  intros d1 d3 Hd [p H].
  apply mkDiscr with p.
  refine (range_stable_eq Hd H).
 Qed.

 Lemma mu_is_Discrete : forall d (D:is_Discrete d),
  forall f, mu d f == discrete (coeff carA D.(D_points) d) (D.(D_points)) f.
 Proof.
  intros; apply mu_discrete with (@eq A);auto.
  apply eq_Transitive.
  apply eq_Symmetric.
  apply D_Discr.
  intros;subst;trivial.
 Qed.

 

 Section Class1.

   Variable R : A -> A -> Prop.
   Variable uR : A -> MF A.
   Hypothesis cover_uR : forall a, cover (R a) (uR a).
   Hypothesis R_trans : transitive A R.
   Hypothesis R_sym : symmetric A R.
   Hypothesis R_refl : reflexive A R.

   Lemma mu_is_Discrete_R :
     forall d (D:is_Discrete d) f,
     mu d f == serie (fun k => mu (distr_mult (fun a => in_class uR (D_points D) a k) d) f).
     unfold distr_mult;simpl;intros.
     assert (W:= mu_serie_eq d (fun k x => in_class uR (@D_points d D) x k * f x));simpl in W.
     rewrite <- W;clear W.
     repeat rewrite (mu_is_Discrete D).
     unfold discrete;simpl;apply serie_eq_compat;intros k.
     apply Umult_eq_compat;[trivial | ].
     unfold serie_fun;simpl.
     transitivity (f (@D_points d D k) * 1);[auto | ].
     transitivity 
       (f (@D_points d D k) * serie (in_class uR (@D_points d D) (@D_points d D k))).
     apply Umult_eq_compat;[trivial | ].
     symmetry; rewrite <- (in_classes_in_class (R:=R)); auto.
     apply in_classes_refl with R; trivial.
     rewrite <- serie_mult.
     apply serie_eq_compat;auto.
     apply in_class_wretract with R;auto.
     intros; apply wretract_le with (2:=in_class_wretract uR cover_uR R_trans R_sym (@D_points d D) x); auto.
   Qed.

 End Class1.

 Lemma is_Discrete_Munit : forall a, is_Discrete (Munit a). 
 Proof.
  intros a; apply mkDiscr with (D_points := fun _ => a).
  red; red; intros.
  refine (H a _).
  red; apply exc_intro with O; trivial.
 Qed.

 Lemma bij_n_nxn_aux : forall k, 
  (0 < k)%nat ->
  sigT (fun i:nat => {j : nat | k = (exp2 i * (2 * j + 1))%nat}).
 Proof.
  induction k using lt_wf_rec; intros.
  destruct (even_odd_dec k).
  destruct (H (div2 k)) as (i, (j, Heq)).
  apply lt_div2; auto with arith.
  inversion e.
  rewrite <- H1 in H0; inversion H0.
  inversion H1; simpl; auto with arith.
  exists (S i)%nat; exists j.
  rewrite (even_double _ e).
  rewrite Heq; unfold double; simpl exp2; ring.
  exists O; exists (div2 k).
  apply trans_eq with (1:= odd_double _ o).
  unfold double; simpl exp2; ring.
 Qed.

 Definition bij_n_nxn k :=
  match @bij_n_nxn_aux (S k) (lt_O_Sn k) with
  | existT i (exist j _) => (i, j)
  end.

 Lemma mult_eq_reg_l : forall n m p, 
  (0 < p -> p * n = p * m -> n = m)%nat.
 Proof.
  intros.
  destruct p;[inversion H | ].
  apply le_antisym;
   apply mult_S_le_reg_l with p; rewrite H0; trivial.
 Qed.
 
 Lemma even_exp2 : forall n, even (exp2 (S n)).
 Proof.
  induction n; simpl.
  repeat constructor.
  apply even_even_plus.
  exact IHn.
  rewrite plus_0_r; exact IHn.
 Qed.

 Lemma odd_2p1 : forall n, odd (2 * n + 1).
 Proof.
  intros; apply odd_plus_r;[ apply even_mult_l | ];
   repeat constructor.
 Qed.
 
 Lemma bij_surj : forall i j, exists k, 
  bij_n_nxn k = (i, j).
 Proof.
  intros i j.
  exists (exp2 i * (2 * j + 1) - 1)%nat.
  unfold bij_n_nxn.
  destruct (bij_n_nxn_aux (lt_O_Sn (exp2 i * (2 * j + 1) - 1))) as (i', (j', H)).
  assert (exp2 i * (2 * j + 1) = exp2 i' * (2 * j' + 1))%nat .
  rewrite <- H.
  assert (0 < exp2 i * (2 * j + 1))%nat; [ | omega].
  apply le_lt_trans with (O * (2 * j + 1))%nat; trivial.
  apply mult_lt_compat_r.
  apply exp2_pos.
  rewrite plus_comm; simpl; auto with arith.
  clear H.
  generalize i j i' j' H0; clear H0 i j i' j'.
  induction i; destruct i'; intros.
  apply mult_eq_reg_l in H0; [ | apply exp2_pos].
  rewrite plus_comm, (plus_comm (2 * j')) in H0.
  apply plus_reg_l in H0; apply mult_eq_reg_l in H0.
  rewrite H0; trivial.
  auto with arith.
  elimtype False.
  apply not_even_and_odd with (exp2 0 * (2 * j + 1))%nat.
  rewrite H0.
  apply even_mult_l; apply even_exp2.
  simpl exp2; rewrite mult_1_l; apply odd_2p1.
  elimtype False.
  apply not_even_and_odd with (exp2 0 * (2 * j' + 1))%nat.
  rewrite <- H0.
  apply even_mult_l; apply even_exp2.
  simpl exp2; rewrite mult_1_l; apply odd_2p1.
  assert (forall k, exp2 (S k) = 2 * exp2 k)%nat by trivial.
  repeat rewrite H, <- mult_assoc in H0.
  apply mult_eq_reg_l in H0; [ | auto with arith].
  assert (W:= IHi _ _ _ H0); injection W; intros; subst; trivial.
 Qed.
  
 Lemma is_Discrete_lub : forall (F:natO -m> cDistr A),
  (forall n, is_Discrete (F n)) ->
  is_Discrete (lub F).
 Proof.
  intros F DF; apply mkDiscr with 
   (D_points := 
    (fun k => let (i, j) := bij_n_nxn k in D_points (DF i) j)).     
  red; apply lub_range.
  intros.
  apply range_weaken with (2 := D_Discr (DF n)).
  intros.
  apply H;[ unfold In_classes; trivial | intros j Hj].
  destruct (bij_surj n j) as (k, Heq).
  red; apply exc_intro with k; rewrite Heq; trivial.
 Qed.

 Lemma is_Discrete_sum_support : forall a l, is_Discrete (sum_support a l).
 Proof.
  intros.
  apply mkDiscr with (D_points:=fun k => nth k l a).    
  red; intros.
  red; intros.
  change (0 == sum_dom a l f).
  symmetry; apply sum_dom_zero with (In_classes (@eq A) (fun k : nat => nth k l a)).
  clear H; induction l; simpl; intros a1 H; destruct H.
  red; apply exc_intro with O; auto.
  apply (IHl _ H);[ unfold In_classes; trivial | intros k Hk].
  red; apply exc_intro with (S k); auto.
  intros; symmetry; auto.
 Qed.

End DISCRETE.

 
Lemma is_Discrete_Mlet : forall (A B:Type) (d:Distr A) (F:A -> Distr B) 
 (Dd : is_Discrete d),
 (forall a, (* In_points Dd.(D_points) a -> *) is_Discrete (F a)) ->
 is_Discrete (Mlet d F).
Proof.
 intros A B d f Dd DF.
 apply mkDiscr with (D_points := 
  fun k => let (i, j) := bij_n_nxn k in D_points (DF (D_points Dd i)) j).
 red.
 apply range_Mlet with (P := In_classes (@eq A) (D_points Dd)).
 exact Dd.(D_Discr).
 intros.
 set (DFx:=DF x). 
 apply range_weaken with (2:=D_Discr DFx).
 intros.
 apply H;[ unfold In_classes; trivial | intros i Hi].
 apply H0;[ unfold In_classes; trivial | intros j Hj].
 destruct (bij_surj i j) as (k, Heq).
 red; apply exc_intro with k.
 rewrite Heq.
 rewrite Hj, <- Hi; trivial.
Qed.


Section LIFT_TRANS.
 
 Variables A B C : Type.
 Variable carB : B -> MF B.

 Hypothesis carB_prop : forall a, cover (fun x => a = x) (carB a).
 
 Variable P : A -> B -> Prop.
 Variable Q : B -> C -> Prop.
 Variable R : A -> C -> Prop.

 Hypothesis P_Q_R : forall x y z, P x y -> Q y z -> R x z.

 Variable d  : Distr (A*B).
 Variable d' : Distr (B*C). 
 Variable d1 : Distr A.
 Variable d2 : Distr B.
 Variable d3 : Distr C.

 Variable Hd : lift P d  d1 d2.
 Variable Hd': lift Q d' d2 d3.

 Definition dfst (b : B) : distr (B*C) := distr_mult (fun q => carB b (fst q)) d'.
 
 Definition dsnd (b : B) : distr (A*B) := distr_mult (fun q => carB b (snd q)) d.

 Lemma dfst_simpl : forall b f, 
  mu (dfst b) f = mu d' (fun q => carB b (fst q) * f q).
 Proof. 
  trivial.
 Qed.

 Lemma dfst_le : forall b, mu (dfst b) (fone (B * C)) <= mu d2 (carB b).
 Proof.
  intro; rewrite dfst_simpl.
  apply Ole_trans with (mu d' (fun q => carB b (fst q))); [auto | ].
  rewrite Hd'.(l_fst); trivial.
 Qed.

 Lemma dsnd_simpl : forall b f, 
  mu (dsnd b) f = mu d (fun q => carB b (snd q) * f q).
 Proof. 
  trivial.
 Qed.

 Lemma dsnd_le : forall b, mu (dsnd b) (fone (A * B)) <= mu d2 (carB b).
 Proof.
  intro; rewrite dsnd_simpl.
  apply Ole_trans with (mu d (fun q => carB b (snd q))); [auto | ].
  rewrite Hd.(l_snd); trivial.
 Qed.

 Hint Resolve dfst_le dsnd_le.

 Definition d_restr : B -> distr (A*B) := 
  fun b => distr_div (mu d2 (carB b)) (dsnd b) (dsnd_le b) .

 Definition d'_restr : B -> distr (B*C) := 
  fun b => distr_div (mu d2 (carB b)) (dfst b) (dfst_le b).

 Lemma d_restr_simpl : forall b f, 
  mu (d_restr b) f = mu d (fun q => carB b (snd q) * f q) / mu d2 (carB b).
 Proof. 
  trivial.
 Qed.

 Lemma d'_restr_simpl : forall b f, 
  mu (d'_restr b) f = mu d' (fun q => carB b (fst q) * f q) / mu d2 (carB b).
 Proof. 
  trivial.
 Qed.

 Definition dd' : distr (A * C) := 
  Mlet d2 (fun b => 
   Mlet (d_restr b) (fun p => 
    Mlet (d'_restr b) (fun q => Munit (fst p, snd q)))).

 Lemma dd'_range : range (prodP R) dd'.
 Proof.
  red; intros.
  unfold dd'; simpl.
  transitivity (mu d2 (fzero B)); [auto | ].
  apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intro x; unfold fzero.
  apply (Ueq_orc 0 (mu d2 (carB x))); auto; intros.
  apply Oeq_sym; apply Udiv_by_zero; auto.
  apply Oeq_sym; apply Udiv_zero_eq; auto.
  apply Hd.(l_range); intros.
  apply (cover_elim (carB_prop x) (snd x0)); auto; intros [H4 H5].
  rewrite H5; auto.
  rewrite H5; Usimpl.
  apply Oeq_sym; apply Udiv_zero_eq; auto.
  apply Hd'.(l_range); intros.
  destruct x1; destruct x0; simpl.
  simpl in H4; subst x.
  apply (cover_elim (carB_prop b0) b); auto; intros [H6 H7].
  rewrite H7; auto.
  rewrite <- H; auto.
  subst b0; red; apply P_Q_R with b; trivial.
 Qed.


 Section HYPO.

  Hypothesis hyp_d1_d : forall f:A -> U,
   mu d1 f == 
   mu d2 (fun b => mu d (fun p => carB b (snd p) * f (fst p)) / mu d2 (carB b)).

  Lemma dd'_fst : forall f : A -> U, mu dd' (fun p => f (fst p)) == mu d1 f.
  Proof.
   intros; simpl.
   apply Oeq_trans with 
    (mu d2 (fun a =>
     (mu d (fun ab => carB a (snd ab) * 
      (mu d2 (fun b => carB a b * f (fst ab)) / mu d2 (carB a))) 
     / mu d2 (carB a)))).
   apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intros b; simpl.
   apply Udiv_eq_compat_left.
   apply (mu_stable_eq d); simpl; apply ford_eq_intro; intros; simpl; Usimpl.
   apply Udiv_eq_compat_left.
   apply (Hd'.(l_fst) (fun x => carB b x * f (fst n))).
   apply Oeq_trans with 
    (mu d2 
     (fun b => mu d (fun ab => carB b (snd ab) * f (fst ab)) / mu d2 (carB b))).
   apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intros b; simpl.
   apply (Ueq_orc 0 (mu d2 (carB b))); auto; intros.
   repeat (rewrite Udiv_by_zero; auto).
   apply Udiv_eq_compat_left.
   apply (mu_stable_eq d); simpl; apply ford_eq_intro; intros (a,b'); simpl.
   Usimpl.
   apply Oeq_trans with (f a * mu d2 (carB b) / mu d2 (carB b)).
   apply Udiv_eq_compat_left.
   rewrite <- (mu_stable_mult d2 (f a) (carB b)).
   apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intros; unfold fmult; auto.
   rewrite Umult_div_assoc; auto.
   apply Oeq_sym; apply hyp_d1_d.
  Qed.

  Hypothesis hyp_d3_d' : forall f:C -> U,
   mu d3 f == 
   mu d2 (fun b => mu d' (fun p => carB b (fst p) * f (snd p)) / mu d2 (carB b)).

  Lemma dd'_snd : forall f : C -> U, mu dd' (fun p => f (snd p)) == mu d3 f.
  Proof.
   intros; simpl.
   apply Oeq_trans with 
    (mu d2 (fun b =>
     (mu d2 (fun b' => carB b b' * 
      (mu d' (fun bc => carB b (fst bc) * f (snd bc)) / mu d2 (carB b)))
     / mu d2 (carB b)))).
   apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intros b; simpl.
   apply Udiv_eq_compat_left.
   apply (Hd.(l_snd) (fun b' =>
    carB b b' *
    (mu d' (fun bc => carB b (fst bc) * f (snd bc)) / mu d2 (carB b)))).  
   apply Oeq_trans with 
    (mu d2 (fun b =>
     (mu d' (fun bc => carB b (fst bc) * f (snd bc)) / mu d2 (carB b)))).
   apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intros b; simpl.
   apply (Ueq_orc 0 (mu d2 (carB b))); auto; intros.
   repeat (rewrite Udiv_by_zero; auto).
   apply Udiv_eq_compat_left.
   apply Oeq_trans with 
    ((mu d' (fun bc => carB b (fst bc) * f (snd bc)) / mu d2 (carB b))
     * (mu d2 (carB b))).
   rewrite <- (mu_stable_mult d2 
    (mu d' (fun bc => carB b (fst bc) * f (snd bc)) / mu d2 (carB b))
    (carB b)).
   apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intros; unfold fmult; auto.
   apply Udiv_mult; auto.
   apply Ole_trans with (mu (dfst b) (fone (B*C))); auto.
   apply Oeq_sym; apply hyp_d3_d'.
  Qed.

  Lemma lift_trans : lift R dd' d1 d3.
  Proof.
   constructor.
   apply dd'_fst.
   apply dd'_snd.
   apply dd'_range.
  Qed.

 End HYPO.


 Section DISCRETE.

  Variable D2 : is_Discrete d2.

  Let p := D2.(D_points).


  Let c := coeff carB D2.(D_points) d2.
 
  Lemma cp_retract : forall x, 
   wretract (fun k : nat => c k / c k * carB (p k) x).
  Proof.
   unfold wretract; intros.
   apply (Ueq_orc 0 (c k)); [auto | | ]; intros.
   rewrite Udiv_by_zero; trivial; repeat Usimpl; auto.
   apply (cover_elim (carB_prop (p k)) x); [auto | | ]; intros [H4 H5].
   rewrite H5; repeat Usimpl; auto.
   rewrite sigma_zero; [ auto | intros].
   apply (cover_elim (carB_prop (p k0)) x); [auto | | ]; intros [H2 H3].
   rewrite H3; repeat Usimpl; auto.
   elim H; unfold c, coeff.
   set (P1:=fun k => exc (fun k0 => (k0 < k)%nat /\ p k = p k0)).
   rewrite (@cover_eq_one _ P1 _ k (cover_not_first_repr (@eq B) carB carB_prop (D_points D2))).
   Usimpl; auto.
   red; apply exc_intro with k0; split; trivial.
   rewrite H2; trivial.
  Qed.
 
  Definition in_d2 b := serie (fun k : nat => c k / c k * carB (p k) b).
  
  Lemma in_d2_dec : forall b, orc (in_d2 b == 0) (in_d2 b == 1).
  Proof.
   intros; apply orc_intro; intros.
   elim H.
   unfold in_d2.
   apply serie_zero.
   intros k; apply (Ueq_orc (c k / c k * carB (p k) b) 0); auto; intros.
   elim H0; split; trivial.
   transitivity (c k / c k * carB (p k) b).
   apply (Ueq_orc (c k)  0); auto; intros.
   elim H1; rewrite H2, Udiv_by_zero; auto.
   apply (cover_elim (carB_prop (p k)) b); [auto | | ]; intros [H4 H5].
   elim H1; rewrite H5; auto.
   rewrite H5, Udiv_refl; auto.
   exact (serie_le (fun k0 : nat => c k0 / c k0 * carB (p k0) b) k).
  Qed.

  Lemma in_d2_p : forall k, ~c k == 0 -> in_d2 (p k) == 1.
  Proof.
   intros; unfold in_d2; split; trivial.
   transitivity (c k / c k * carB (p k) (p k)).
   rewrite Udiv_refl; [ auto | ].
   rewrite (cover_eq_one _ (carB_prop (p k)) (refl_equal (p k))).
   auto.
   auto.
   exact (serie_le (fun k0 : nat => c k0 / c k0 * carB (p k0) (p k)) k).
  Qed.

  Lemma lift_discr_fst : forall f : A -> U,
   mu d1 f ==
   mu d2 (fun b : B =>
    mu d (fun p : A * B => carB b (snd p) * f (fst p)) / mu d2 (carB b)).
  Proof.
   intros; rewrite (mu_is_Discrete carB carB_prop D2).
   rewrite discrete_simpl.
   transitivity (serie (fun k =>
    mu d (fun p0 => (c k / c k) * carB (p k) (snd p0) * f (fst p0)))).
   rewrite <- mu_serie_eq.

   2:intro x; apply wretract_le with (2:=cp_retract (snd x)); auto.

   unfold serie_fun; rewrite <- Hd.(l_fst).
   apply range_eq with (P:=fun x => in_d2 (snd x) == 1).
   unfold range; intros; split; auto.
   transitivity (mu d (fun p => [1-] (in_d2 (snd p)))).
   apply (mu_monotonic d); intro x.
   apply (in_d2_dec (snd x)); [auto | | ]; intros H0; [rewrite H0 | rewrite <- H]; auto.
   rewrite (Hd.(l_snd) (fun x => [1-] in_d2 x)).
   rewrite (mu_is_Discrete carB carB_prop D2), discrete_simpl.
   rewrite serie_zero; [auto | intros].
   fold (c k).
   apply (Ueq_orc (c k) 0); [auto | | ]; intros.
   rewrite H0; auto.
   fold p; rewrite in_d2_p; [ Usimpl | ]; auto.
   intros.
   transitivity (serie (fun k => f (fst a) * (c k / c k * carB (p k) (snd a)))).
   rewrite serie_mult.   
   rewrite H; auto.
   apply cp_retract.
   apply serie_eq_compat; auto.
   apply serie_eq_compat; intros.
   set (g:=fun p0 => c k / c k * carB (p k) (snd p0) * f (fst p0)).
   apply (Ueq_orc (c k) 0); [auto | | ]; intros.
   fold c; rewrite H; Usimpl.
   rewrite <- (mu_0 d).
   apply (mu_stable_eq d).
   simpl; apply ford_eq_intro; intros; unfold g; rewrite Udiv_by_zero; [Usimpl | ]; auto.
   unfold c in H; unfold coeff in *.
   apply (cover_elim (cover_not_first_repr (@eq B) carB carB_prop (D_points D2)) k);
    [ auto | | ]; intros (H1, H2).
   generalize H; clear H; rewrite H2; repeat Usimpl; intros.
   rewrite Umult_sym, Udiv_mult; [auto | | ].
   apply mu_stable_eq; unfold g; simpl; apply ford_eq_intro; intros.
   rewrite Udiv_refl; auto.
   unfold c; rewrite H2; Usimpl; auto.
   auto.
   apply Ole_trans with (2:=dsnd_le (p k)).
   rewrite dsnd_simpl.
   apply (mu_monotonic d); intro; unfold fone; auto.
   elim H; rewrite H2;Usimpl; auto.
  Qed.
 
 End DISCRETE.

End LIFT_TRANS.


Section LIFT_TRANS_DISCR.

 Variables A B C : Type.
 Variable carB : B -> MF B.
 
 Hypothesis carB_prop : forall a, cover (fun x => a = x) (carB a).

 Variable P : A -> B -> Prop.
 Variable Q : B -> C -> Prop.
 Variable R : A -> C -> Prop.

 Hypothesis P_Q_R : forall x y z, P x y -> Q y z -> R x z.

 Variable d  : Distr (A * B).
 Variable d' : Distr (B * C). 
 Variable d1 : Distr A.
 Variable d2 : Distr B.
 Variable d3 : Distr C.

 Variable Hd : lift P d  d1 d2.
 Variable Hd': lift Q d' d2 d3.

 Lemma lift_trans_discr : is_Discrete d2 -> lift R (dd' carB Hd Hd') d1 d3.
 Proof.
  intros D2.
  apply lift_trans; auto; intros.
  eapply lift_discr_fst; eauto.
  assert (lift (fun c b => Q b c) (Mlet d' (fun p => Munit (snd p, fst p))) d3 d2).
   constructor; intros; simpl.
   apply Hd'.(l_snd).
   apply Hd'.(l_fst).
   unfold range; intros; simpl; apply Hd'.(l_range).
   intros (b1,c1) H1; apply H; exact H1.
  rewrite (lift_discr_fst carB carB_prop H D2); trivial.
 Qed.
 
End LIFT_TRANS_DISCR.


Lemma lift_eq_trans_l : forall A B (R:A -> B -> Prop) d d1 d1' d' d2,
 lift (@eq _) d d1 d1' ->
 lift R d' d1' d2 ->
 lift R d' d1  d2.
Proof.
 intros; constructor.
 intros; assert (mu d1 f == mu d1' f).
 rewrite <- H.(l_fst); rewrite <- H.(l_snd).
 apply range_eq with (1:= H.(l_range)).
 intros a H1; rewrite H1; trivial.
 rewrite H1; apply H0.(l_fst).
 apply H0.(l_snd).
 apply H0.(l_range).
Qed.

Lemma lift_eq_trans_r : forall A B (R:A -> B -> Prop) d d1 d' d2 d2',
 lift (@eq _) d d2 d2' ->
 lift R d' d1 d2' ->
 lift R d' d1 d2.
Proof.
 intros; constructor.
 apply H0.(l_fst).
 intros; assert (mu d2 f == mu d2' f).
 rewrite <- H.(l_fst); rewrite  <- H.(l_snd).
 apply range_eq with (1:=H.(l_range)).
 intros a H1; rewrite H1; trivial.
 rewrite H1; apply H0.(l_snd).
 apply H0.(l_range).
Qed.


(** Definition of negligible function *)

Definition negligible (f:nat -> U) := 
 forall c, exists n0, forall n, (n0 <= n)%nat -> f n <= ([1/]1+n) ^ c.

Lemma negligible_0 : negligible (fun _ => 0).
Proof.
 unfold negligible.
 intro; exists 0%nat; auto.
Qed.

Lemma negligible_eq_stable : forall f g,
 f === g -> negligible f -> negligible g.
Proof.
 unfold negligible; intros.
 destruct (H0 c) as (n0, H1); clear H0.
 exists n0; intros.
 rewrite <- (H n); auto.
Qed.

Lemma negligible_le_stable : 
 forall f g, (forall n, f n <= g n) -> negligible g -> negligible f.
Proof.
 unfold negligible; intros.
 destruct (H0 c) as (n0, H1); exists n0.
 intros n H2; apply Ole_trans with (2:= H1 n H2); auto.
Qed.

Lemma negligible_plus_stable : forall f g,
 negligible f -> negligible g -> negligible (fun n => f n + g n).
Proof.
 unfold negligible; intros.
 destruct c.
  (* case 0 *)
 simpl; exists 0%nat; auto.
 
  (* case S *)
 destruct (H (Datatypes.S (Datatypes.S c))) as (nf, Hf).
 destruct (H0 (Datatypes.S (Datatypes.S c))) as (ng, Hg).
 assert (exists max, (nf <= max)%nat /\ (ng <= max)%nat).
 destruct (le_lt_dec nf ng);[ exists ng | exists nf] ; auto with arith.
 destruct H1 as (Smax, (Hfm, Hgm)).
 exists (Datatypes.S Smax); intros.
 apply Ole_trans with 
  (UP.Uexp ([1/]1+n)(Datatypes.S (Datatypes.S c)) + 
   UP.Uexp ([1/]1+n) (Datatypes.S(Datatypes.S c))).
 apply UP.Uplus_le_compat; auto with zarith.
 simpl.
 change ([1/]1+n * UP.Uexp ([1/]1+n) c) with 
  (UP.Uexp ([1/]1+n) (Datatypes.S c)).
 apply Ole_trans with
  ([1/]1+1 * UP.Uexp ([1/]1+n) (Datatypes.S c) + 
   [1/]1+1 * UP.Uexp ([1/]1+n)  (Datatypes.S c)).
 apply UP.Uplus_le_compat; apply Umult_le_compat; auto;
  apply UP.Unth_anti_mon; auto with zarith.
 rewrite <- UP.Udistr_plus_left.
 apply UP.half_twice_le.
 apply UP.le_half_inv.
 apply Ole_trans with ([1/]1+n).
 auto.
 apply UP.Unth_anti_mon; auto; omega.
Qed.

Lemma negligible_mult_stable : forall c f,
 negligible f -> negligible (fun n => c * f n).
Proof.
 unfold negligible; intros.
 destruct (H c0) as (n0, H1); exists n0; intros.
 transitivity (f n); auto.
Qed.

Lemma negligible_mult_poly : forall a f,
 negligible (fun k => f k * ([1/]1+k) ^ a) ->
 negligible f.
Proof.
 unfold negligible; intros a f H c.
 destruct (H (c + a))%nat as [n0 H1]; clear H. 
 exists n0; intros n Hle.
 generalize (H1 n Hle); clear.
 induction a.
 repeat Usimpl; rewrite plus_0_r; trivial.
 rewrite <- plus_n_Sm; simpl.
 rewrite Umult_assoc, Umult_sym, Umult_assoc,  Umult_sym.
 rewrite (Umult_sym (([1/]1+n) ^ a)).
 intro H; apply IHa; clear IHa.
 apply Umult_le_simpl_left with ([1/]1+n); trivial.
Qed.

Lemma negligible_le : forall f g : nat -> U,
 (exists n0, forall n, (n0 <= n)%nat -> f n <= g n) -> 
 negligible g -> negligible f.
Proof.
 intros f g [n0 Hle] Hg c.
 destruct (Hg c) as [n1 H].
 exists (Max.max n0 n1); intros.
 transitivity (g n).
 apply Hle.
 apply le_trans with (2:=H0); apply Max.le_max_l.
 apply H.
 apply le_trans with (2:=H0); apply Max.le_max_r.
Qed.


 Definition rcomp (A B C:Type) (P: A -> B -> Prop) (Q: B -> C -> Prop) : A -> C -> Prop :=
  fun a c => exists b, P a b /\ Q b c.
  
 Lemma PER_r : forall (A: Type) (R:relation A) x1 x2, 
   @PER _ R ->
   R x1 x2 ->
   R x2 x2.
 Proof.
  intros A R x1 x2  [Hsym Htrans] H.
  exact (Htrans _ _ _ (Hsym _ _ H) H).
 Qed.


 Lemma PER_l : forall (A: Type) (R:relation A) x1 x2, 
   @PER _ R ->
   R x1 x2 ->
   R x1 x1.
 Proof.
  intros A R x1 x2  [Hsym Htrans] H.
  unfold transitive in Htrans.
  exact (Htrans _ _ _ H (Hsym _ _ H)).
 Qed.

 Lemma rcomp_PER : forall  (A:Type) (R : relation A),
  @PER _ R -> same_relation _ R (rcomp R R). 
 Proof.
  unfold rcomp; split; intros.
   intros x1 x2 Hx; exists x2; split.
     assumption.
     apply (PER_r _ _ H Hx).
   intros x1 x2 [x [H1 H2] ].  
   destruct H. apply (PER_Transitive _ _ _ H1 H2).
 Qed.
 
 Hint Unfold same_relation inclusion.

 Lemma same_relation_refl : forall (A:Type) (R: relation A), same_relation _ R R.
 Proof.
  split; intros; auto.
 Qed.

 Lemma same_relation_sym : forall (A:Type) (R S: relation A), 
   same_relation _ R S -> same_relation _ S R.
 Proof.
  intros A R S [? ?]; split; assumption.
 Qed.


 Add Parametric Relation (A:Type) : (relation A) (@same_relation A)
   reflexivity proved by (@same_relation_refl A)
   symmetry proved by (@same_relation_sym A)
 as same_rel_rel.
