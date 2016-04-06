(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Export BoolEquality.
Require Export CCMisc.  
Require Import BaseDef. 
Require Import Arith Even Div2.
Require Export RelationClasses.

Open Scope U_scope. 
Open Scope O_scope.

Hint Resolve Uabs_diff_compat_eq.


(* ***********  Boolean comparison in [U] *********** *)
 Variable Uleb : U -> U -> bool.
 Hypothesis Uleb_spec : forall (x y: U), 
    if Uleb x y then (x <= y) else ~(x <= y). 

 Lemma Uleb_correct : forall (x y: U), 
    Uleb x y -> (x <= y).
 Proof.
  intros; generalize (Uleb_spec x y).
  rewrite H; trivial.
 Qed.

 Lemma Uleb_complete : forall (x y: U), 
   Uleb x y = false -> (y < x).
 Proof.
  intros x y.
  generalize (Uleb_spec x y). 
  case (Uleb x y).
    intros _ H; discriminate H.
    intros H _; auto.
 Qed.
(* ************************************************** *)


(* *************** SOME AUXILIARY STUFF *************** *)


 Lemma Uminus_plus_aux: forall a b c d,
  d <= c ->
  a <= [1-] c ->
  a - b <= (a+c) - (b+d).
 Proof.
  intros.
  rewrite (Uplus_sym b d), <-Uminus_assoc_left.
  apply Uminus_le_compat; [|trivial].
  rewrite <-Uplus_minus_assoc_right;
  [|apply Uinv_le_perm_right|]; trivial.
 Qed.

 Lemma  fminus_fplus_simpl : forall (A:Type) (f h:A -o> U), 
   h <= f ->
   f == fplus h (fminus f h).
 Proof.
  intros.
  apply ford_eq_intro; intro.
  unfold fplus, fminus.
  rewrite Uplus_sym, Uminus_plus_simpl; trivial.
 Qed. 

 Lemma Uabs_diff_plus_bound: forall a b c d E,
   c <= a ->
   b <= d ->
   Uabs_diff a c <= E ->
   Uabs_diff d b <= E ->
   Uabs_diff (a+b) (c+d) <= E.
 Proof.
   intros a b c d E Hca Hbd HacE HdbE.
   apply (Ule_total (a+b) (c+d)); trivial; intro H.
    (* case [a+b <= c+d] *)
    rewrite Uabs_diff_compat_le; trivial.
    rewrite <- Uminus_assoc_left, Uplus_minus_perm_le.
    rewrite (Uminus_le_zero _ _ Hca), Uplus_zero_left.
    rewrite <- HdbE; apply Ule_plus_right.
    (* case [a+b >= c+d] *)
    rewrite Uabs_diff_sym, Uabs_diff_compat_le; trivial.
    rewrite <- Uminus_assoc_left, Uplus_minus_perm_le, Uplus_minus_le.
    rewrite (Uminus_le_zero _ _ Hbd),Uplus_zero_right.
    rewrite <- HacE; apply Ule_plus_right.
 Qed.

 
 Lemma PER_Oeq : forall (A:Type), @PER (A -o> U) (@Oeq (A -o> U) ).
 Proof.
  intros; constructor.
    refine (@Oeq_sym (A-o>U)).
    refine (@Oeq_trans (A-o>U)).
 Qed.


 Definition relTr (A B :Type) (F : A -o> Distr B) (R : relation (A -o> U)) : relation (B -o> U) :=
   fun f g => R (fun x : A => (mu (F x)) f) (fun x : A => (mu (F x)) g). 

 Lemma even_2n : forall n, even (2*n).
 Proof.
  intro n.
  apply even_mult_l.
  repeat constructor.
 Qed.

 Lemma odd_S2n : forall n, odd (S(2*n)).
 Proof.
  intro n.
  constructor.
  apply even_2n.
 Qed.


(* 
  parity_split f g (2m) = f m
  parity_split f g (2m+1) = g m
*)   
 Definition parity_split := fun (A:Type) (f g : nat -> A) n  =>
   match (even_odd_dec n) with
   | left x => f (div2 n)
   | right x => g (div2 (pred n)) 
   end.


(* Given two discrete disctribution over [A], restate them in terms
   of the same enumearion of [A]'s elements *)
Section SamePoints.

 Variable A : Type.
 Variable AeqU : A -> A -O-> U.
 Hypothesis cover_uR: forall a : A, cover (eq a) (AeqU a).

 Variable d1 d2 : Distr A.
 Hypothesis is_Discr_d1 : is_Discrete d1.
 Hypothesis is_Discr_d2 : is_Discrete d2.

 Definition p1 := D_points is_Discr_d1.
 Definition p2 := D_points is_Discr_d2.
 Definition D1 := D_Discr is_Discr_d1.
 Definition D2 := D_Discr is_Discr_d2.

 Definition c1 : nat -> U := parity_split (coeff AeqU p1 d1) (fzero _).
 Definition c2 : nat -> U := parity_split (fzero _) (coeff AeqU p2 d2).
 Definition p  : nat -> A := parity_split p1 p2.

 Lemma disc_eqpoint_l : Discrete (@eq A) p d1.
 Proof.
  apply range_weaken with (2:=D1); fold p1.
  unfold In_classes; intros x Hx.
  unfold p, parity_split.
  unfold exc in *. 
  intros P HP H.
  apply (Hx _ HP).
  intros n Hn.
  generalize (H (2*n)%nat).
  elim (even_odd_dec (2*n)%nat); intro Hn'.
     rewrite div2_double.
     exact (fun n => n Hn).
     elimtype False; refine (not_even_and_odd _ (even_2n _) Hn').
 Qed.

 Lemma disc_eqpoint_r : Discrete (@eq A) p d2.
 Proof.
  apply range_weaken with (2:=D2); fold p2.
  unfold In_classes; intros x Hx.
  unfold p, parity_split.
  unfold exc in *. 
  intros P HP H.
  apply (Hx _ HP).
  intros n Hn.
  generalize (H (S(2*n))).
  elim (even_odd_dec (S(2*n))); intro Hn'.
     elimtype False; refine (not_even_and_odd _ Hn' (odd_S2n _)).
     rewrite <-pred_Sn, div2_double; exact (fun n => n Hn).
 Qed.

 End SamePoints.

(* ******************************************************** *)




(********************************************************************)
(* *************** RELATIONAL STATISTICAL DISTANCE  *************** *)
(********************************************************************)

 Definition RSD (A:Type) (R : relation _) (d1 d2:Distr A) (ep:U) := 
   forall (f g: A -o> U),
   R f g -> 
   Uabs_diff (mu d1 f) (mu d2 g) <= ep.


 Lemma RSD_eq_distr_compat: forall (A:Type) R (d1 d2 d3 d4:Distr A) (ep:U),
   d1 == d3 ->
   d2 == d4 ->
   RSD R d3 d4 ep ->
   RSD R d1 d2 ep.
 Proof.
  unfold RSD; intros.
  rewrite (eq_distr_elim H), (eq_distr_elim H0).
  apply (H1 _ _ H2).
 Qed.


 Lemma RSD_weaken: forall (A:Type) (R R' : relation _) (d1 d2:Distr A) (ep ep':U),
   inclusion _ R R' ->
   ep' <= ep ->
   RSD R' d1 d2 ep' ->
   RSD R d1 d2 ep.
 Proof.
  unfold RSD; intros. 
  rewrite <-H0.
  apply (H1 _ _ (H _ _ H2)).
 Qed.


 Add Parametric Morphism (A:Type) : (@RSD A) 
   with signature (@inclusion _) ==> (@Oeq (Distr A)) ==> (@Oeq (Distr A))
    ==> (@Ole (tcpo U)) --> Basics.flip impl as RSD_impl_le_compat_mor.
 Proof.
  intros R R' HR d1 d3 H31 d2 d4 H24 ep ep' Hep H.
  apply RSD_eq_distr_compat with (1:=H31) (2:=H24).
  refine (RSD_weaken _ HR Hep H). 
 Qed.


 Add Parametric Morphism (A:Type) : (@RSD A) 
   with signature (@same_relation _) ==> (@Oeq (Distr A)) ==> (@Oeq (Distr A))
    ==> (@Oeq (tcpo U)) ==> Basics.flip impl as RSD_eq_compat_mor.
 Proof.
  intros R R' [HR _] d1 d3 H31 d2 d4 H24 ep ep' [_ Hep] H.
  apply RSD_eq_distr_compat with (1:=H31) (2:=H24).
  refine (RSD_weaken _ HR Hep H). 
 Qed.

 Lemma RSD_one : forall (A:Type) (d1 d2:Distr A) (R : relation _),
  RSD R d1 d2 1.
 Proof.
  unfold RSD; intros; trivial.
 Qed.


 Lemma RSD_tranp: forall (A:Type) (d1 d2:Distr A) (R : relation _) (ep:U),
   RSD R d1 d2 ep -> RSD (transp _ R) d2 d1 ep.
 Proof.
  unfold RSD; intros.
  rewrite Uabs_diff_sym.
  apply (H _ _ H0).
 Qed.


 Lemma RSD_sym: forall (A:Type) (d1 d2:Distr A) (R : relation _) (ep:U),
   symmetric _ R ->
   RSD R d2 d1 ep -> 
   RSD R d1 d2 ep.
 Proof.
  intros.
  apply RSD_tranp. 
  apply RSD_weaken with R ep; trivial.
  intros f g; apply H.
 Qed.


 Lemma RSD_null: forall (A:Type) (d1 d2:Distr A) (R : relation _),
   RSD R d1 d2 0 <-> 
   (forall f g, R f g  -> mu d1 f == mu d2 g).
 Proof.
  split; [ | unfold RSD ]; intros.
    rewrite <-Uabs_diff_zero; apply Ule_zero_eq; auto.
    rewrite (H _ _ H0), Uabs_diff_compat_eq; trivial.
 Qed.


 Lemma RSD_trans : forall (A:Type) R1 R2 (d1 d2 d3:Distr A) (ep1 ep2:U),
   RSD R1 d1 d2 ep1 -> 
   RSD R2 d2 d3 ep2 -> 
   RSD (rcomp R1 R2) d1 d3 (ep1+ep2) .
 Proof.
  unfold RSD; intros.
  destruct H1 as [h [Hh1 Hh2] ].
  rewrite (Uabs_diff_triangle_ineq _ _  (mu d2 h)).
  apply Uplus_le_compat; [ apply (H _ _ Hh1) |  apply (H0 _ _ Hh2) ].
 Qed.


 Lemma RSD_Mlet : forall (A:Type) R (d1 d2 :Distr A) (B: Type) (F:A -> Distr B) (ep:U),
   RSD R d1 d2 ep  -> 
   RSD (relTr F R) (Mlet d1 F) (Mlet d2 F) ep.
 Proof.
  unfold RSD; intros.
  repeat rewrite Mlet_simpl.
  apply (H _ _ H0).
 Qed.


 Lemma RSD_Mlet' : forall (A:Type) (d :Distr A) (B: Type) (F G : A -> Distr B) (S : relation (B -o> U)) (ep:U),
 (forall f g, S f g ->
   mu d (fabs_diff (fun a => mu (F a) f) (fun a => mu (G a) g)) <= ep) ->
   RSD S (Mlet d F) (Mlet d G) ep. 
 Proof.
  unfold RSD; intros.
  repeat rewrite Mlet_simpl.
  rewrite Uabs_diff_mu_compat.
  auto.
 Qed.




(********************************************************************)
(* *************** CLASSICAL STATISTICAL DISTANCE  *************** *)
(********************************************************************)

Hint Unfold symmetric reflexive inclusion.

(* Statistical distance w.r.t {0,1}-valued functions *)
 Definition SD (A:Type) (d1 d2:Distr A) (ep:U)  := 
   forall (P : A -o> boolO), 
     (Uabs_diff (mu d1 (charfun P)) (mu d2 (charfun P))) <= ep.

(* Statistical distance w.r.t [0,1]-valued functions *)
 Definition GSD (A:Type) (d1 d2:Distr A) (ep:U)  := 
  RSD (@Oeq _) d1 d2 ep.


 Lemma GSD_sym : forall (ep:U) (A:Type) (d1 d2:Distr A) ,
   GSD d1 d2 ep -> GSD  d2 d1 ep.
 Proof.
  intros.
  refine (RSD_sym _ H); auto.
 Qed.

 Lemma GSD_trans : forall (A:Type) (d1 d2 d3:Distr A) (ep ep':U),
   GSD  d1 d2 ep -> GSD d2 d3 ep' -> GSD d1 d3 (ep+ep') .
 Proof.
  intros;  unfold GSD.
  rewrite (@rcomp_PER (A -o> U) _ (PER_Oeq A)).
  apply RSD_trans with (1:=H) (2:=H0).
 Qed.


 Lemma GSD_eq_distr_compat : forall (A:Type) (d1 d2 d3 d4:Distr A) (ep:U),
   GSD d1 d2 ep -> d3 == d1 -> d4==d2 -> GSD d3 d4 ep.
 Proof.
  intros.
  refine (RSD_eq_distr_compat H0 H1 H).
 Qed.

 Lemma GSD_weaken : forall (A:Type) (d1 d2:Distr A) (ep ep':U),
   GSD d1 d2 ep' -> ep' <= ep -> GSD d1 d2 ep.
 Proof.
  intros.
  refine (RSD_weaken _ _ H0 H); auto.
 Qed.

 Add Parametric Morphism (A:Type) : (@GSD A) 
   with signature (@Oeq (Distr A)) ==> (@Oeq (Distr A)) ==> (@Ole (tcpo U)) --> Basics.flip impl 
 as GSD_le_eq_compat_mor.
 Proof.
  intros  d3 d1 H31 d4 d2 H24 ep' ep Hep H.
  refine (GSD_weaken _ _ Hep). 
  refine (GSD_eq_distr_compat H H31 H24).
 Qed.

 Add Parametric Morphism (A:Type) : (@GSD A) 
   with signature (@eq (Distr A)) ==> (@eq (Distr A)) ==> ((Oeq (O:=U))) --> impl 
  as GSD_eq_compat_mor.
 Proof.
  unfold impl; intros. 
  refine (GSD_weaken _ H0 (Oeq_le_sym H)). 
 Qed.


 Lemma GSD_NonDeg : forall (A:Type) (d1 d2:Distr A),
   GSD d1 d2 0 <-> d1 == d2.
 Proof.
  split; intro H.
    apply eq_distr_intro; intro f.
    apply (proj1 (RSD_null _ _ _) H); trivial.
    intros a1 a2 Ha. 
    rewrite (mu_stable_eq d1 _ _ Ha), (eq_distr_elim H).
    rewrite Uabs_diff_compat_eq; trivial.
 Qed.


 Lemma GSD_refl_0 : forall (A:Type) (d:Distr A),
   GSD d d 0.
 Proof.
  intros; rewrite GSD_NonDeg; trivial.
 Qed.


 Lemma GSD_refl : forall (ep:U) (A:Type) (d:Distr A),
   GSD d d ep.
 Proof.
  intros.
  rewrite <-(Upos ep).
  apply GSD_refl_0.
 Qed.


 Lemma GSD_Mlet : forall (A:Type) (d1 d2 :Distr A) (B: Type) (F:A -> Distr B) (ep:U),
   GSD d1 d2 ep  -> 
   GSD (Mlet d1 F) (Mlet d2 F) ep.
 Proof.
  unfold GSD; intros.
  apply RSD_weaken with (relTr F (@Oeq _)) ep; trivial.
    unfold relTr, inclusion; intros;
    refine (ford_eq_intro (fun a => mu_stable_eq (F a) _ _ H0)).
    apply (RSD_Mlet _ H).
 Qed.


 Theorem SD_le_GSD : forall (A:Type) (d1 d2 :Distr A) (ep:U),
   GSD d1 d2 ep -> SD d1 d2 ep.
 Proof.
  intros A d1 d2 ep H f.
  apply H; trivial.
 Qed.


(* For discrete distributions, it holds that [GSD <= SD]. The 
   converse (trivially) holds for any pair of distributions *)
Section Discrete_distr.

 Variable A : Type.
 Variable AeqU : A -> A -O-> U.
 Hypothesis cover_uR: forall a : A, cover (eq a) (AeqU a).

 Variable d1 d2 : Distr A.
 Hypothesis d1_discr : is_Discrete d1.
 Hypothesis d2_discr : is_Discrete d2.

 Definition  R : A -> boolO := 
   fun a => Uleb (mu d2 (AeqU a)) (mu d1 (AeqU a)).
 
 Definition p' := p d1_discr d2_discr.

 Lemma discrete1 : Discrete (@eq A) p' d1.
 Proof.  apply disc_eqpoint_l. Qed.

 Lemma discrete2 : Discrete (@eq A) p' d2.
 Proof. apply disc_eqpoint_r. Qed.


 Lemma nul_in_R : forall (f:A-o>U),
   (forall a, R a -> f a == 0) -> mu d1 f <= mu d2 f.
 Proof.
  intros.
  rewrite (mu_restr_split d1 R f).
  transitivity  ((mu d1 (fzero _)) + mu d1 (restr (negP R) f)).
    apply Uplus_le_compat_left.
    apply mu_monotonic.
      refine (ford_le_intro _); intro a.
      unfold restr, fzero; generalize (H a).
      case (R a); auto.
  rewrite mu_zero, Uplus_zero_left.
  transitivity (mu d2 (restr (negP R) f)).
    rewrite (mu_discrete AeqU cover_uR (@eq_Transitive A)(@eq_Symmetric A) discrete1);
      [ | intros x y Heq; rewrite Heq; trivial ].
    rewrite (mu_discrete AeqU cover_uR (@eq_Transitive A)(@eq_Symmetric A) discrete2);
      [ | intros x y Heq; rewrite Heq; trivial ].
    unfold coeff; simpl.
    apply serie_le_compat; intro k.
    repeat rewrite <-Umult_assoc; apply Umult_le_compat_right.
    unfold restr, negP, negb, R.
    generalize (@Uleb_complete (mu d2 (AeqU (p' k)))(mu d1 (AeqU (p' k)))). 
    case_eq (Uleb (mu d2 (AeqU (p' k))) (mu d1 (AeqU (p' k)))).
      intros; Usimpl; trivial.
      intros _ H'; Usimpl.
      apply Ult_le; apply H'; trivial.
  apply mu_monotonic.
    refine (ford_le_intro _); intro a.
    unfold restr; case ((negP R) a); auto.
  Qed.  


 Lemma nul_in_notR : forall (f:A-o>U),
   (forall a, (negP R) a -> f a == 0) -> mu d2 f <= mu d1 f.
 Proof.
  intros.
  rewrite (mu_restr_split d2 R f).
  transitivity  ((mu d2 (restr R f)) + (mu d2 (fzero _))).
    apply Uplus_le_compat_right.
    apply mu_monotonic.
      refine (ford_le_intro _); intro a.
      unfold restr, fzero; generalize (H a).
      case ((negP R) a); auto.
  rewrite mu_zero, Uplus_zero_right.
  transitivity (mu d1 (restr R f)).
    rewrite (mu_discrete AeqU cover_uR (@eq_Transitive A)(@eq_Symmetric A) discrete1);
      [ | intros x y Heq; rewrite Heq; trivial ].
    rewrite (mu_discrete AeqU cover_uR (@eq_Transitive A)(@eq_Symmetric A) discrete2);
      [ | intros x y Heq; rewrite Heq; trivial ].
    unfold coeff; simpl.
    apply serie_le_compat; intro k.
    repeat rewrite <-Umult_assoc; apply Umult_le_compat_right.
    unfold restr, R.
    case_eq (Uleb (mu d2 (AeqU (p' k))) (mu d1 (AeqU (p' k)))); intro H'; Usimpl.
      apply Uleb_correct; apply H'; trivial.
      trivial.
  apply mu_monotonic.
    refine (ford_le_intro _); intro a.
    unfold restr; case (R a); auto.
  Qed.  


 Lemma monot_Uabsdiff_notR: forall (f h :A-o>U),
   h <= f ->
   (forall a, (negP R) a -> f a == 0 /\ h a == 0) ->
   Uabs_diff (mu d1 h)  (mu d2 h) <= Uabs_diff (mu d1 f) (mu d2 f).
 Proof.
  intros f h H1 H2.
  assert (H' : fplusok h (fminus f h)) by 
    (apply (@ford_le_intro _ _ h);unfold fplusok, fminus, finv; auto).
  repeat rewrite (range_eq (range_True _) _ _  
    (fun a _ => (ford_eq_elim  (fminus_fplus_simpl H1)) a)).
  rewrite (@mu_stable_plus _ d2 h (fminus f h)); [|exact H'].
  rewrite (@mu_stable_plus _ d1 h (fminus f h)); [|exact H'].

  assert (H_1 : mu d2 (fminus f h) <= mu d1 (fminus f h)).
   apply nul_in_notR.
   intros a Ha; destruct (H2 a Ha) as [Hfa Hha]; clear H2.
   unfold fminus; rewrite Hfa, Hha; trivial.
  assert (H_2 : mu d2 h <= mu d1 h).
   apply nul_in_notR; intros a Ha; destruct (H2 a Ha) as [_ ?]; assumption.
  rewrite Uabs_diff_sym, (Uabs_diff_compat_le (mu d2 h) (mu d1 h)); 
  [| exact H_2].
  rewrite  Uabs_diff_sym, (Uabs_diff_compat_le 
    (mu d2 h + mu d2 (fminus f h)) (mu d1 h + mu d1 (fminus f h)));
    [ | apply Uplus_le_compat; [exact H_2|exact H_1] ].

  apply  Uminus_plus_aux.
   apply nul_in_notR.
   intros a Ha; destruct (H2 a Ha) as [Hfa Hha]; clear H2.
   unfold fminus; rewrite Hfa, Hha; trivial.
   apply mu_fplusok; exact H'.
 Qed.


 Lemma monot_Uabsdiff_R: forall (f h :A-o>U),
   h <= f ->
   (forall a, R a -> f a == 0 /\ h a == 0) ->
    Uabs_diff (mu d2 h)  (mu d1 h) <= Uabs_diff (mu d1 f) (mu d2 f).
 Proof.
  intros f h H1 H2.
  assert (H' : fplusok h (fminus f h)) by 
    (apply (@ford_le_intro _ _ h);unfold fplusok, fminus, finv; auto).
  repeat rewrite (range_eq (range_True _) _ _  
    (fun a _ => (ford_eq_elim  (fminus_fplus_simpl H1)) a)).
  rewrite (@mu_stable_plus _ d2 h (fminus f h)); [|exact H'].
  rewrite (@mu_stable_plus _ d1 h (fminus f h)); [|exact H'].

  assert (H_1 : mu d1 (fminus f h) <= mu d2 (fminus f h)).
   apply nul_in_R.
   intros a Ha; destruct (H2 a Ha) as [Hfa Hha]; clear H2.
   unfold fminus; rewrite Hfa, Hha; trivial.
  assert (H_2 : mu d1 h <= mu d2 h).
   apply nul_in_R; intros a Ha; destruct (H2 a Ha) as [_ ?]; assumption.
  rewrite Uabs_diff_sym, (Uabs_diff_compat_le (mu d1 h) (mu d2 h)); [| exact H_2].
  rewrite (Uabs_diff_compat_le 
    (mu d1 h + mu d1 (fminus f h)) (mu d2 h + mu d2 (fminus f h)));
    [ | apply Uplus_le_compat; [exact H_2|exact H_1] ].

  apply  Uminus_plus_aux.
   apply nul_in_R.
   intros a Ha; destruct (H2 a Ha) as [Hfa Hha]; clear H2.
   unfold fminus; rewrite Hfa, Hha; trivial.
   apply mu_fplusok; exact H'.
 Qed.


 Lemma GSD_le_SD: forall (ep:U),
   SD d1 d2 ep -> GSD d1 d2 ep.
 Proof.
  intros ep HSD f g H.  
  rewrite <-(mu_stable_eq d2 _ _ H).
  rewrite (mu_restr_split d1 R f), (mu_restr_split d2 R f).
  apply Uabs_diff_plus_bound.
   apply nul_in_notR; unfold restr, negP; intro a.
   case (R a); intros; [discriminate H0 | trivial].
   apply nul_in_R; unfold restr, negP, negb; intro a.
   case (R a); intros; [trivial | discriminate H0 ].
   transitivity (Uabs_diff (mu d1 (restr R (@fone A))) (mu d2 (restr R (@fone A)))).
    apply monot_Uabsdiff_notR.
     apply restr_le_compat; auto.
     unfold negP, negb, restr; intros a. 
     case (R a); intros; [discriminate H0 | split; trivial].
    apply HSD.
   transitivity (Uabs_diff (mu d1 (restr (negP R) (@fone A))) (mu d2 (restr (negP R) (@fone A)))).
    apply monot_Uabsdiff_R.
     apply restr_le_compat; auto.
     unfold negP, negb, restr; intros a. 
     case (R a); intros; [split; trivial |discriminate H0].
    apply HSD. 
 Qed.


End Discrete_distr.
