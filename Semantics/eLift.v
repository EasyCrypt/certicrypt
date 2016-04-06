(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* Should move this to BeseDef.v *)
Require Export BaseDef.
Require Import Classical.

Set Implicit Arguments.


(* ************************ SOME AUXILIARY STUFF ************************ *)

 Lemma Distr_split: forall (A:Type) (d:Distr A) (P:A->bool) (vt vf:U),
   mu d (fun a => if P a then vt else vf) ==
   vt * mu d (charfun P) +  vf * mu d (charfun (negP P)).
 Proof.
  intros.
  apply Oeq_trans with (mu d (fplus 
    (fmult vt (charfun P)) (fmult vf (charfun (negP P))))).
    unfold fplus, fmult, charfun, negP, negb, restr, fone. 
    apply (mu_stable_eq d); refine (ford_eq_intro _); intro a.
    case (P a); repeat Usimpl; trivial.
    rewrite (mu_stable_plus d (f:=(fmult vt (charfun P)))
      (g:=(fmult vf (charfun (negP P))))).
    rewrite (mu_stable_mult d vt (charfun P)), 
      (mu_stable_mult d  vf (charfun (negP P))); trivial.
    apply fplusok_le_compat with (charfun P) (charfun (negP P)).
      apply (disjoint_fplusok_charfun (disjoint_negP P)).
      apply fle_fmult.
      apply fle_fmult.
 Qed.

 Definition d_inv (A B: Type) (d:distr (A*B)) := 
   Mlet d (fun p => Munit (snd p, fst p)).

 Lemma d_inv_fst: forall (A B:Type) (d:distr (A*B)) g, 
   mu d (fun ab => g (snd ab)) == mu (d_inv d) (fun ba => g (fst ba)).
 Proof. intros; trivial. Qed.

 Lemma d_inv_snd: forall (A B:Type) (d:distr (A*B)) f, 
   mu d (fun ab => f (fst ab)) == mu (d_inv d) (fun ba => f (snd ba)).
 Proof. intros; trivial. Qed.

 Lemma cover_neg: forall (A:Type) (P:set A) (caracP: MF A),
  cover P caracP ->
  cover (fun a => ~ P a) (finv caracP).
 Proof.
  intros A P caracP H a.
  split; intro Ha; unfold finv.
    rewrite (cover_eq_zero _ H Ha); auto.
    rewrite (cover_eq_one _ H (NNPP _ Ha)); auto.
 Qed.

 Lemma cover_eq_prod: forall (A B:Type) (P: A -> MF A) (Q: B -> MF B),
  (forall a, cover (eq a) (P a)) ->
  (forall b, cover (eq b) (Q b)) ->
  forall ab:A*B, 
    cover (eq ab) (fun ab' => P (fst ab) (fst ab') * Q (snd ab) (snd ab')).
 Proof.
  intros A B P Q HP HQ ab.
  apply cover_equiv_stable with (inter (fun ab':A*B => eq (fst ab') (fst ab))
    (fun ab':A*B => eq (snd ab') (snd ab))).
    unfold Sets.equiv, inter; split.
      intros [H1 H2].
      destruct ab; destruct x; simpl in *; rewrite H1, H2; trivial.
      intros H1.
      destruct ab; destruct x; simpl; injection H1; auto.
    apply cover_inter_mult.
      intros ab'; split; intros.
        apply (cover_eq_one _ (HP (fst ab)) (eq_sym H)).
        apply (cover_eq_zero _ (HP (fst ab)) (not_eq_sym H)).
      intros ab'; split; intros.
        apply (cover_eq_one _ (HQ (snd ab)) (eq_sym H)).
        apply (cover_eq_zero _ (HQ (snd ab)) (not_eq_sym H)).
 Qed.

 Lemma mu_stable_plus_range: forall (A:Type) (d:Distr A) R,
   range R d ->
   forall f g,
   (forall a, R a ->  g a <= [1-] f a) ->
   mu d (fplus f g) == mu d f + mu d g.
 Proof.
  intros; split.
    auto.
    transitivity (mu d (fminus (fplus f g) g) + mu d g).
      Usimpl.
      apply range_le with (1:=H).
      intros a Ha; unfold fminus, fplus.
      rewrite Uplus_minus_simpl_right; auto.
      rewrite <-(@mu_stable_plus _ d _ _); unfold fminus, fplus.
        apply range_le with (1:=H).
        intros a _; rewrite Uminus_plus_simpl; auto.
        unfold fplusok, finv; refine (ford_le_intro _); intro a.
        rewrite <-Uminus_one_left.
        apply Uminus_le_compat_left; trivial.
 Qed.

 Definition drange A (P:A->Prop) (d: Distr A) :=
  forall f, (0 == mu d f) -> (forall x, P x -> 0 == f x).

 Definition srange A (P:A->Prop) (d: Distr A) := range P d /\ drange P d.

(*
 Lemma drange_false: forall (A:Type) (d: Distr A),
  drange (fun _ => False) d.
 Proof.
   intros A d f Hf a H; tauto.
 Qed.


 Lemma drange_Mlet: forall (A B:Type) (P:A->Prop) (Q:B ->Prop) 
  (d: Distr A) (F: A -> Distr B),
  (exists a, P a) -> 
  drange P d ->
  (forall x, P x -> drange Q (F x)) -> 
  drange Q (Mlet d F).
 Proof.
  intros A B P Q d F [a Ha] Hdran HQ.
  intros f Hdf b Hb; simpl in *.
  refine (HQ a Ha _ _ _ Hb).
  apply (Hdran _ Hdf _ Ha).
 Qed.


 Lemma srange_Mlet: forall (A B : Type) (P : A -> Prop) (Q : B -> Prop) 
  (d : Distr A) (F : A -> Distr B),
  (exists a, P a) ->
  srange P d ->
  (forall x : A, P x -> srange Q (F x)) -> 
  srange Q (Mlet d F).
 Proof.
  unfold srange; intros A B P Q d F HP [Hran Hdran] H; split.
    apply (range_Mlet _ Hran).
    intros a Ha; apply (proj1 (H _ Ha)).

    refine (drange_Mlet _ HP Hdran _). 
    intros a Ha; apply (proj2 (H a Ha)).
 Qed.
*)

 Lemma drange_range:forall (A:Type) (P Q:A->Prop) (d: Distr A) (carP: MF A),
  (cover P carP) ->
  range P d ->
  drange Q d ->
  (forall a, Q a -> P a).
 Proof.
  unfold drange, range; intros.
  assert  (0 == mu d (finv carP)) by
    (apply H0; symmetry; eapply (cover_eq_zero _ (cover_neg H)); auto).
  apply NNPP.
  apply (cover_eq_zero_elim _ (cover_neg H) (Oeq_sym (H1 _  H3 _ H2))).
 Qed.

(* ********************************************************************** *)



Open Scope U_scope.


 Record elift (A B: Type) (R:A->B->Prop) (d:Distr (A * B))
   (d1:Distr A) (d2:Distr B) (ep:U) := Build_elift
 { 
   el_dist: forall f g,
     Uabs_diff (mu d (fun x => f (fst x))) (mu d1 f) + 
     Uabs_diff (mu d (fun x => g (snd x))) (mu d2 g) <= ep;
   el_range: range (prodP R) d ;
   el_supp_l: forall f,  mu d (fun ab => f (fst ab)) == 0 <-> mu d1 f == 0;
   el_supp_r: forall g,  mu d (fun ab => g (snd ab)) == 0 <-> mu d2 g == 0
 }.


 Lemma elift_Mlet: forall (A1 A2 B1 B2: Type) (R1: A1 -> B1 -> Prop)
  (R2: A2 -> B2 -> Prop) (d: Distr (A1 * B1)) 
  (d1: Distr A1) (d2: Distr B1) (F: A1 * B1 -> Distr (A2 * B2))
  (F1: A1 -> Distr A2) (F2: B1 -> Distr B2) (ep ep' :U),
  (exists carP, cover (prodP R1) carP) ->
  (exists Rd, srange Rd d) ->
  elift R1 d d1 d2 ep ->
  (forall (x : A1) (y : B1), R1 x y -> elift R2 (F (x, y)) (F1 x) (F2 y) ep') ->
  elift R2 (Mlet d F) (Mlet d1 F1) (Mlet d2 F2) (ep' + ep).
 Proof.
  intros; constructor. 
    (* distance *)
    intros; repeat rewrite Mlet_simpl.
    rewrite (Uabs_diff_triangle_ineq _ (mu d1 (fun x => mu (F1 x) f))
      (mu d (fun x => mu (F1 (fst x)) f))),
    (Uabs_diff_triangle_ineq _ (mu d2 (fun x => mu (F2 x) g))
      (mu d (fun x => mu (F2 (snd x)) g))).
    match goal with |- (?A + ?B) + (?C + ?D) <= _ =>
      rewrite <-(Uplus_assoc A), (Uplus_sym B), Uplus_assoc, (Uplus_assoc A), <-(Uplus_assoc), (Uplus_sym D)
    end.
    apply Uplus_le_compat.
      apply (Ueq_orc ep' 1); [apply Ule_class | | ]; intro Hep'. 
        rewrite Hep'; apply Unit .
        apply (Ule_diff_lt (Unit ep')) in Hep'.
        rewrite Uabs_diff_mu_compat, Uabs_diff_mu_compat,
          <-(mu_stable_plus_range (el_range H1)).
        rewrite <-(mu_cte_le d ep').
        apply (range_le (el_range H1)).
        intros (a,b) H'; unfold fabs_diff, fcte, fplus.
        apply (el_dist (H2 _ _ H')).
        intros (x,y) Hxy; unfold fabs_diff.
        apply Uplus_lt_Uinv.
        apply Ule_lt_trans with ep'; [ | exact Hep' ].
        rewrite Uplus_sym; apply (el_dist (H2 _ _ Hxy)).
      apply (el_dist H1 (fun x : A1 => (mu (F1 x)) f) (fun x : B1 => (mu (F2 x)) g)).
    (* range *)
    apply range_Mlet with (prodP R1).
      apply (el_range H1).
      intros (a,b) H'.
      apply (el_range (H2 _ _ H')).    
    (* supp_l *)
    destruct H as  [carP HcarP].
    destruct H0 as [Rd [Hdran Hddran] ].
    destruct H1 as (_, Hran, Hsupp, _).
    split; intros; simpl in *.
      (*  *)
      rewrite <-Hsupp.
      symmetry; apply Hdran.
      intros (a1,b1) Hab; simpl.
      destruct (H2 _ _ (drange_range HcarP Hran Hddran _ Hab)) as (_, Hran', Hsupp', _); simpl in *.
      symmetry; rewrite <-Hsupp'.
      symmetry; apply (Hddran _ (Oeq_sym H) _ Hab).
      (*  *)
      rewrite <-Hsupp in H.
      symmetry; apply Hdran.
      intros (a1,b1) Hab; simpl.
      destruct (H2 _ _ (drange_range HcarP Hran Hddran _ Hab)) as (_, Hran', Hsupp', _); simpl in *.
      symmetry; rewrite Hsupp'.
      symmetry; apply (Hddran _ (Oeq_sym H) _ Hab).
    (* supp_r *)
    destruct H as  [carP HcarP].
    destruct H0 as [Rd [Hdran Hddran] ].
    destruct H1 as (_, Hran, _, Hsupp).
    split; intros; simpl in *.
      (*  *)
      rewrite <-Hsupp.
      symmetry; apply Hdran.
      intros (a1,b1) Hab; simpl.
      destruct (H2 _ _ (drange_range HcarP Hran Hddran _ Hab)) as (_, Hran', _, Hsupp'); simpl in *.
      symmetry; rewrite <-Hsupp'.
      symmetry; apply (Hddran _ (Oeq_sym H) _ Hab).
      (*  *)
      rewrite <-Hsupp in H.
      symmetry; apply Hdran.
      intros (a1,b1) Hab; simpl.
      destruct (H2 _ _ (drange_range HcarP Hran Hddran _ Hab)) as (_, Hran', _,Hsupp'); simpl in *.
      symmetry; rewrite Hsupp'.
      symmetry; apply (Hddran _ (Oeq_sym H) _ Hab).
 Qed.



 Lemma elift_MletCase: forall (A1 A2 B1 B2: Type) (R1: A1 -> B1 -> Prop)
  (R2: A2 -> B2 -> Prop) (d: Distr (A1 * B1)) (dt df:A1 * B1 -> Distr (A2*B2))
  (d1: Distr A1) (d2: Distr B1) (Cond: A1 * B1 -> bool)
  (F1: A1 -> Distr A2) (F2: B1 -> Distr B2) (ep1 ep2 ep :U),
  (exists carP, cover (prodP R1) carP) ->
  (exists Rd, srange Rd d) ->
  elift R1 d d1 d2 ep ->
  (forall (x : A1) (y : B1), 
    R1 x y -> Cond (x,y) = true -> elift R2 (dt (x,y)) (F1 x) (F2 y) ep1) ->
  (forall (x : A1) (y : B1), 
    R1 x y -> Cond (x,y) = false -> elift R2 (df (x,y)) (F1 x) (F2 y) ep2) ->
  ep1 < 1 ->
  ep2 < 1 ->
  elift R2 (Mlet d (fun xy => if Cond xy then dt xy else df xy)) 
  (Mlet d1 F1) (Mlet d2 F2) (ep1 * mu d (charfun Cond) +
    ep2 * mu d (charfun (negP Cond)) + ep).
 Proof.
  intros; constructor. 
    (* distance *)
    intros; repeat rewrite Mlet_simpl.
    rewrite (Uabs_diff_triangle_ineq _ (mu d1 (fun x => mu (F1 x) f))
      (mu d (fun x => mu (F1 (fst x)) f))),
    (Uabs_diff_triangle_ineq _ (mu d2 (fun x => mu (F2 x) g))
      (mu d (fun x => mu (F2 (snd x)) g))).
    match goal with |- (?A + ?B) + (?C + ?D) <= ?epx + _ =>
      rewrite <-(Uplus_assoc A), (Uplus_sym B), Uplus_assoc, 
        (Uplus_assoc A), <-(Uplus_assoc), (Uplus_sym D); set (ep':=epx)
    end.
    apply Uplus_le_compat.
      apply (Ueq_orc ep' 1); [apply Ule_class | | ]; intro Hep'. 
        rewrite Hep'; apply Unit.
        apply (Ule_diff_lt (Unit ep')) in Hep'.
        rewrite Uabs_diff_mu_compat, Uabs_diff_mu_compat,
          <-(mu_stable_plus_range (el_range H1)).
        unfold ep'; rewrite <-(Distr_split d Cond ep1 ep2).
        apply (range_le (el_range H1)); intros (a,b) Hab.
          unfold fplus, fabs_diff.
          case_eq (Cond (a,b)); intro Hab'.
            apply (el_dist (H2 _ _ Hab Hab')).
            apply (el_dist (H3 _ _ Hab Hab')).
          intros (x,y) Hxy; unfold fabs_diff.
          apply Uplus_lt_Uinv; rewrite Uplus_sym.
          case_eq (Cond (x,y)); intro Hxy'.
            apply (Ule_lt_trans _ (el_dist (H2 _ _ Hxy Hxy') f g) H4).
            apply (Ule_lt_trans _ (el_dist (H3 _ _ Hxy Hxy') f g) H5).
      apply (el_dist H1 (fun x : A1 => (mu (F1 x)) f) (fun x : B1 => (mu (F2 x)) g)).
    (* range *)
    apply range_Mlet with (prodP R1).
      apply (el_range H1).
      intros (a,b) Hab.
      case_eq (Cond (a,b)); intro Hab'.
        apply (el_range (H2 _ _ Hab Hab')).
        apply (el_range (H3 _ _ Hab Hab')).
    (* supp_l *)
    destruct H as  [carP HcarP].
    destruct H0 as [Rd [Hdran Hddran] ].
    destruct H1 as (_, Hran, Hsupp, _).
    split; intros; simpl in *.
      (*  *)
      rewrite <-Hsupp.
      symmetry; apply Hdran.
      intros (a1,b1) Hab; simpl.
      case_eq (Cond (a1,b1)); intro HHab.
        (*   *)
        destruct (H2 _ _ (drange_range HcarP Hran Hddran _ Hab) HHab) as (_, Hran', Hsupp', _); simpl in *.
        symmetry; rewrite <-Hsupp'.
        generalize (Hddran _ (Oeq_sym H) _ Hab); rewrite HHab; intro.
        symmetry; trivial.
        (*   *)
        destruct (H3 _ _ (drange_range HcarP Hran Hddran _ Hab) HHab) as (_, Hran', Hsupp', _); simpl in *.
        symmetry; rewrite <-Hsupp'.
        generalize (Hddran _ (Oeq_sym H) _ Hab); rewrite HHab; intro.
        symmetry; trivial.
      (*  *)
      rewrite <-Hsupp in H.
      symmetry; apply Hdran.
      intros (a1,b1) Hab; simpl.
      case_eq (Cond (a1,b1)); intro HHab.
        (*   *)
        destruct (H2 _ _ (drange_range HcarP Hran Hddran _ Hab) HHab) as (_, Hran', Hsupp', _); simpl in *.
        symmetry; rewrite Hsupp'.
        symmetry; apply (Hddran _ (Oeq_sym H) _ Hab).
        (*   *)
        destruct (H3 _ _ (drange_range HcarP Hran Hddran _ Hab) HHab) as (_, Hran', Hsupp', _); simpl in *.
        symmetry; rewrite Hsupp'.
        symmetry; apply (Hddran _ (Oeq_sym H) _ Hab).
    (* supp_r *)
    destruct H as  [carP HcarP].
    destruct H0 as [Rd [Hdran Hddran] ].
    destruct H1 as (_, Hran, _, Hsupp).
    split; intros; simpl in *.
      (*  *)
      rewrite <-Hsupp.
      symmetry; apply Hdran.
      intros (a1,b1) Hab; simpl.
      case_eq (Cond (a1,b1)); intro HHab.
        (*   *)
        destruct (H2 _ _ (drange_range HcarP Hran Hddran _ Hab) HHab) as (_, Hran', _, Hsupp'); simpl in *.
        symmetry; rewrite <-Hsupp'.
        generalize (Hddran _ (Oeq_sym H) _ Hab); rewrite HHab; intro.
        symmetry; trivial.
        (*   *)
        destruct (H3 _ _ (drange_range HcarP Hran Hddran _ Hab) HHab) as (_, Hran', _, Hsupp'); simpl in *.
        symmetry; rewrite <-Hsupp'.
        generalize (Hddran _ (Oeq_sym H) _ Hab); rewrite HHab; intro.
        symmetry; trivial.
      (*  *)
      rewrite <-Hsupp in H.
      symmetry; apply Hdran.
      intros (a1,b1) Hab; simpl.
      case_eq (Cond (a1,b1)); intro HHab.
        (*   *)
        destruct (H2 _ _ (drange_range HcarP Hran Hddran _ Hab) HHab) as (_, Hran', _,Hsupp'); simpl in *.
        symmetry; rewrite Hsupp'.
        symmetry; apply (Hddran _ (Oeq_sym H) _ Hab).
        destruct (H3 _ _ (drange_range HcarP Hran Hddran _ Hab) HHab) as (_, Hran', _,Hsupp'); simpl in *.
        symmetry; rewrite Hsupp'.
        symmetry; apply (Hddran _ (Oeq_sym H) _ Hab).
 Qed.


 Lemma elift_weaken: forall A B (P Q:A -> B -> Prop), 
  (forall x y, P x y -> Q x y) ->
  forall ep ep',
  ep' <= ep ->
  forall d d1 d2, 
  elift P d d1 d2 ep' -> elift Q d d1 d2 ep.
 Proof.
  intros A B P Q H1 ep ep' H2 d d1 d2 (Hdist, Hran, Hsup_l, Hsup_r).
  constructor.
    intros f g; rewrite <-H2; trivial.
    apply range_weaken with (prodP P). 
      unfold prodP; auto.
      trivial.
    assumption.
    assumption.
 Qed.


 Lemma elift_stable_eq : forall A B (R:A -> B -> Prop) 
  (d d' : Distr (A*B)) (d1 d1':Distr A) (d2 d2':Distr B) ep ep',
  d == d' -> 
  d1 == d1' -> 
  d2 == d2' -> 
  ep == ep' ->
  elift R d d1 d2 ep -> elift R d' d1' d2' ep'.
 Proof.
  intros A B R d d' d1 d1' d2 d2' ep ep' Heq Heq1 Heq2 Heq3 (Hdist, Hran, Hsup_l, Hsup_r).
  constructor.
    intros.
    rewrite <-(eq_distr_elim Heq), <-(eq_distr_elim Heq), 
       <-(eq_distr_elim Heq1), <-(eq_distr_elim Heq2), <-Heq3; trivial.
    apply range_stable_eq with (1:=Heq); trivial.
    intro f; rewrite <-(eq_distr_elim Heq), <-(eq_distr_elim Heq1); auto.
    intro g; rewrite <-(eq_distr_elim Heq), <-(eq_distr_elim Heq2); auto.
 Qed.


 Lemma elift_Munit: forall (A:Type) (x y:A) (P:relation A), 
  P x y -> 
  elift P (Munit (x,y)) (Munit x) (Munit y) 0.
 Proof.
  intros; constructor.
   intros; repeat rewrite Uabs_diff_compat_eq; auto.
   apply range_Munit with (1:=H).
   intro; apply iff_refl.
   intro; apply iff_refl.
 Qed.
 

 Lemma elift_true: forall (A B: Type) (d1: Distr A) (d2: Distr B),
  ~ mu d1 (fone _) == 0 -> 
  ~ mu d2 (fone _) == 0 -> 
  elift (fun _ _ => True) (prod_distr d1 d2) d1 d2 
    ([1-] (mu d1 (fone _)) + [1-] (mu d2 (fone _))).
 Proof.
  intros.
  constructor.
    (* dist *)
    intros f g; rewrite prod_distr_fst, prod_distr_snd.
    rewrite <-(Umult_one_right (mu d1 f)),  <-(Umult_one_right (mu d2 g)) at 2.
    rewrite <-(Umult_sym (mu d1 f)), <-(Umult_sym (mu d2 g)).
    repeat rewrite Uabs_diff_mult.
    rewrite Uplus_sym; apply Uplus_le_compat; unfold Uabs_diff.
      rewrite (Uminus_le_zero _ 1); [ rewrite Uplus_zero_left, Uminus_one_left | ]; auto.
      rewrite (Uminus_le_zero _ 1); [ rewrite Uplus_zero_left, Uminus_one_left | ]; auto.
    (* range *)
    apply range_True.
    (* supp *)
    intros; rewrite prod_distr_fst; split; intro.
      symmetry; apply Umult_zero_simpl_right with (mu d2 (fone _)); auto.
      rewrite H1; auto.
    intros; rewrite prod_distr_snd; split; intro.
      symmetry; apply Umult_zero_simpl_left with (mu d1 (fone _)); [ 
        rewrite Umult_sym | ]; auto.
      rewrite H1; auto.
 Qed.


 Lemma elift_transp : forall (A B:Type) (d: Distr (A*B)) (d1:Distr A) (d2:Distr B) R ep, 
   elift (fun b a => R a b) (Mlet d (fun ab => Munit (snd ab, fst ab))) d2 d1 ep ->
   elift R d d1 d2 ep. 
 Proof.
  intros; constructor.
    (* distance *)
    intros f g; rewrite Uplus_sym; apply (el_dist H g f).
    (* range *)
    intros f Hf.
    rewrite (el_range H (fun ba => f (snd ba,fst ba))).
      rewrite Mlet_simpl; simpl.
      apply (mu_stable_eq d); refine (ford_eq_intro _); intros (a,b); trivial.
      auto.
    (* supp *)
    apply (el_supp_r H).
    apply (el_supp_l H).
 Qed.


 Lemma lift_elift: forall A B (P:A -> B -> Prop) d d1 d2, 
  elift P d d1 d2 0 <-> lift P d d1 d2.
 Proof.
  split; intros.
   (*  *)
    constructor.
      intro f.
      rewrite <-Uabs_diff_zero; apply Ule_zero_eq.
      rewrite <-(el_dist H f (fzero _)); auto.
      intro f.
      rewrite <-Uabs_diff_zero; apply Ule_zero_eq.
      rewrite <-(el_dist H (fzero _) f); auto.
      apply (el_range H).
    (*  *)
    constructor.  
      intros f g.
      rewrite (l_fst H), (l_snd H), Uabs_diff_compat_eq, Uabs_diff_compat_eq; auto.
      apply (l_range H).
      intro; rewrite (l_fst H); apply iff_refl.
      intro; rewrite (l_snd H); apply iff_refl.
 Qed.


Section LIFT_TRANS.
 
 Variables A B C : Type.
 Variable carB : B -> MF B.

 Hypothesis carB_prop : forall b, cover (fun x => b = x) (carB b).
 
 Variable P : A -> B -> Prop.
 Variable Q : B -> C -> Prop.
 Variable R : A -> C -> Prop.

 Hypothesis P_Q_R : forall x y z, P x y -> Q y z -> R x z.

 Variable d  : Distr (A*B).
 Variable d' : Distr (B*C). 
 Variable ep ep' : U.
 Variable d1 : Distr A.
 Variable d2 : Distr B.
 Variable d3 : Distr C.

 Hypothesis  Hd : elift P d  d1 d2 ep.
 Hypothesis  Hd': elift Q d' d2 d3 ep'.

 Definition dfst (b : B) : distr (B*C) := distr_mult (fun q => carB b (fst q)) d'.
 Definition dsnd (b : B) : distr (A*B) := distr_mult (fun q => carB b (snd q)) d.


 Lemma dfst_simpl : forall b f, 
  mu (dfst b) f = mu d' (fun q => carB b (fst q) * f q).
 Proof. trivial. Qed.

 Lemma dsnd_simpl : forall b f, 
  mu (dsnd b) f = mu d (fun q => carB b (snd q) * f q).
 Proof. trivial. Qed.


 Lemma dfst_le : forall b, 
  mu (dfst b) (fone _) <= mu d' (fun bc => carB b (fst bc)).
 Proof.
  intro; rewrite dfst_simpl; auto.
 Qed.

 Lemma dsnd_le : forall b, 
  mu (dsnd b) (fone _) <=  mu d (fun ab => carB b (snd ab)).
 Proof.
  intro; rewrite dsnd_simpl; auto. 
 Qed. 


 Hint Resolve dfst_le dsnd_le.

 Definition d_restr : B -> distr (A*B) := 
  fun b => distr_div (mu d (fun ab => carB b (snd ab))) (dsnd b) (dsnd_le b) .

 Definition d'_restr : B -> distr (B*C) := 
  fun b => distr_div (mu d' (fun bc => carB b (fst bc))) (dfst b) (dfst_le b).


 Definition dd' : distr (A * C) := 
  Mlet d2 (fun b => 
   Mlet (d_restr b) (fun p => 
    Mlet (d'_restr b) (fun q => Munit (fst p, snd q)))).   
   

  Lemma dd'_1: forall f, 
    mu dd' (fun ac => f (fst ac)) == 
    mu d2  (fun b  =>  (mu d (fun ab => (carB b (snd ab)) * (f (fst ab)))  /
       mu d (fun ab => carB b (snd ab)))).
  Proof.
   intros; simpl.
   apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intros b; simpl.
   apply (Ueq_orc 0 (mu d (fun ab => carB b (snd ab)))); auto; intros.
     repeat (rewrite Udiv_by_zero; auto).
     apply Udiv_eq_compat_left.
     apply (mu_stable_eq d); simpl; apply ford_eq_intro; intros (a,b'); simpl.
     Usimpl.
     apply Oeq_trans with (f a * (mu d' (fun bc => carB b (fst bc))) /
         (mu d' (fun bc => carB b (fst bc)))).
       apply Udiv_eq_compat_left.
       rewrite <- (mu_stable_mult d' (f a) (fun bc => carB b (fst bc))).
       apply (mu_stable_eq d'); simpl; apply ford_eq_intro; intros; unfold fmult; auto.
       rewrite Umult_div_assoc; auto.
       rewrite Udiv_refl; [ auto | ].
       apply neq_sym; intro H'; elim H; clear H; apply Oeq_sym.
       rewrite (Hd.(el_supp_r) (fun b' => carB b b')).
       apply (Hd'.(el_supp_l) (fun b' => carB b b')); assumption.
 Qed.


  Lemma dd'_2: forall g, 
    mu dd' (fun ac => g (snd ac)) ==  mu d2  (fun b  => 
      (mu d' (fun bc => (carB b (fst bc)) * (g (snd bc)))  /
       mu d' (fun bc => carB b (fst bc)))).
  Proof.
   intros; simpl.
   apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intros b; simpl.
   apply (Ueq_orc 0 (mu d' (fun bc => carB b (fst bc)))); auto; intros.

     repeat (rewrite Udiv_by_zero; auto).
     apply Oeq_sym; apply Oeq_sym in H.  
     rewrite (Hd.(el_supp_r) (fun b' => carB b b')).
     apply (Hd'.(el_supp_l) (fun b' => carB b b')); assumption.
     
     transitivity (mu d
     (fun ab => ((mu d') (fun bc : B * C => carB b (fst bc) * g (snd bc)) /
       (mu d') (fun bc : B * C => carB b (fst bc))) *
       carB b (snd ab))  /
     (mu d) (fun ab => carB b (snd ab))).
       apply Udiv_eq_compat_left.
       apply (mu_stable_eq d); simpl; apply ford_eq_intro; auto.

       rewrite (mu_stable_mult d ((mu d') (fun bc => carB b (fst bc) * g (snd bc)) /
         (mu d') (fun bc => carB b (fst bc))) (fun ab => carB b (snd ab))).
       rewrite Umult_div_assoc; [ | trivial ].
       rewrite Udiv_refl; [ auto | ].
       apply neq_sym; intro H'; elim H; clear H; apply Oeq_sym.
       rewrite (Hd'.(el_supp_l) (fun b' => carB b b')).
       apply (Hd.(el_supp_r) (fun b' => carB b b')); assumption.
 Qed.


 Lemma dd'_range : range (prodP R) dd'.
 Proof.
  red; intros.
  unfold dd'; simpl.
  transitivity (mu d2 (fzero B)); [auto | ].
  apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intro x; unfold fzero.
  apply (Ueq_orc 0  (mu d (fun ab => carB x (snd ab)))); [ auto | | ]; intros.
    (*   *)
    apply Oeq_sym; apply Udiv_by_zero; auto.
    (*   *)
    apply Oeq_sym; apply Udiv_zero_eq; auto.
    apply Hd.(el_range); intros.
    apply (cover_elim (carB_prop x) (snd x0)); auto; intros [H4 H5].
      rewrite H5; auto.
      rewrite H5; Usimpl.
      apply Oeq_sym; apply Udiv_zero_eq; auto.
      apply Hd'.(el_range); intros.
      destruct x1; destruct x0; simpl.
      simpl in H4; subst x.
      apply (cover_elim (carB_prop b0) b); auto; intros [H6 H7].
      rewrite H7; auto.
      rewrite <- H; auto.
      subst b0; red.  
      apply P_Q_R with b; trivial.
  Qed.


Section HYPO.

  Hypothesis hyp_d1_d : forall f:A -> U,
   mu d (fun ab => f (fst ab)) == 
   mu d (fun ab => 
    mu d (fun ab' => carB (snd ab) (snd ab') * f (fst ab')) /  
    mu d (fun ab' => carB (snd ab) (snd ab'))).

  Hypothesis hyp_d3_d' : forall g:C -> U,
   mu d' (fun bc => g (snd bc)) == 
   mu d' (fun bc => 
    mu d' (fun bc' => carB (fst bc) (fst bc') * g (snd bc')) /  
    mu d' (fun bc' => carB (fst bc) (fst bc'))).

  Lemma dd'_dist : forall (f : A -> U) (g : C -> U),
    Uabs_diff ((mu dd') (fun ac => f (fst ac))) ((mu d1) f) +
    Uabs_diff ((mu dd') (fun ac => g (snd ac))) ((mu d3) g) <=
    ep + ep'.
  Proof.
   intros.
   apply Uplus_le_compat.   
     rewrite (Uabs_diff_triangle_ineq _ _  (mu d (fun ab => f (fst ab)))).
     rewrite  dd'_1; rewrite hyp_d1_d at 1.
     rewrite Uabs_diff_sym, Uplus_sym. 
     refine (Hd.(el_dist) f (fun b =>
        mu d (fun ab => carB b (snd ab) * f (fst ab)) /
        mu d (fun ab => carB b (snd ab)))).

     rewrite (Uabs_diff_triangle_ineq _ _  (mu d' (fun bc => g (snd bc)))).
     rewrite  dd'_2; rewrite hyp_d3_d' at 1.
     rewrite Uabs_diff_sym. 
     refine (Hd'.(el_dist) (fun b =>
         mu d' (fun bc => carB b (fst bc) * g (snd bc)) /
         mu d' (fun bc => carB b (fst bc))) g).
 Qed.

 End HYPO.


 Section DISCRETE.

  Let p2_d := (Mlet d (fun ab => Munit (snd ab))).

  Variable p2D : is_Discrete p2_d.

  Let p2 := p2D.(D_points).

  Let c2 := coeff carB p2D.(D_points) p2_d.
 
  Lemma cp_retract_p2d : forall x, 
   wretract (fun k : nat => c2 k / c2 k * carB (p2 k) x).
  Proof.
   unfold wretract; intros.
   apply (Ueq_orc 0 (c2 k)); [auto | | ]; intros.
   rewrite Udiv_by_zero; trivial; repeat Usimpl; auto.
   apply (cover_elim (carB_prop (p2 k)) x); [auto | | ]; intros [H4 H5].
   rewrite H5; repeat Usimpl; auto.
   rewrite sigma_zero; [ auto | intros].
   apply (cover_elim (carB_prop (p2 k0)) x); [auto | | ]; intros [H2 H3].
   rewrite H3; repeat Usimpl; auto.
   elim H; unfold c2, coeff.
   set (P1:=fun k => exc (fun k0 => (k0 < k)%nat /\ p2 k = p2 k0)).
   rewrite (@cover_eq_one _ P1 _ k (cover_not_first_repr (@eq B) carB carB_prop (D_points p2D))).
   Usimpl; auto.
   red; apply exc_intro with k0; split; trivial.
   rewrite H2; trivial.
  Qed.
 
  Definition in_p2_d b := serie (fun k : nat => c2 k / c2 k * carB (p2 k) b).
  
  Lemma in_p2_d_dec : forall b, orc (in_p2_d b == 0) (in_p2_d b == 1).
  Proof.
   intros; apply orc_intro; intros.
   elim H.
   unfold in_p2_d.
   apply serie_zero.
   intros k; apply (Ueq_orc (c2 k / c2 k * carB (p2 k) b) 0); auto; intros.
   elim H0; split; trivial.
   transitivity (c2 k / c2 k * carB (p2 k) b).
   apply (Ueq_orc (c2 k)  0); auto; intros.
   elim H1; rewrite H2, Udiv_by_zero; auto.
   apply (cover_elim (carB_prop (p2 k)) b); [auto | | ]; intros [H4 H5].
   elim H1; rewrite H5; auto.
   rewrite H5, Udiv_refl; auto.
   exact (serie_le (fun k0 : nat => c2 k0 / c2 k0 * carB (p2 k0) b) k).
  Qed.

  Lemma in_p2_d_p : forall k, ~c2 k == 0 -> in_p2_d (p2 k) == 1.
  Proof.
   intros; unfold in_p2_d; split; trivial.
   transitivity (c2 k / c2 k * carB (p2 k) (p2 k)).
   rewrite Udiv_refl; [ auto | ].
   rewrite (cover_eq_one _ (carB_prop (p2 k)) (refl_equal (p2 k))).
   auto.
   auto.
   exact (serie_le (fun k0 : nat => c2 k0 / c2 k0 * carB (p2 k0) (p2 k)) k).
  Qed.

  Lemma d_ito_p2_d: forall f,
   mu d f ==
   mu p2_d (fun b : B =>
    mu d (fun ab => carB b (snd ab) * f ab) /  mu d (fun ab => carB b (snd ab))). 
  Proof.
   intros. 
   transitivity (serie (fun k =>
    mu d (fun p0 => (c2 k / c2 k) * carB (p2 k) (snd p0) * f p0))).
   rewrite <- mu_serie_eq.
   2:intro x; apply wretract_le with (2:=cp_retract_p2d (snd x)); auto.

   unfold serie_fun.
   apply range_eq with (P:=fun x => in_p2_d (snd x) == 1).
   unfold range; intros; split; auto.
   transitivity (mu d (fun p => [1-] (in_p2_d (snd p)))).
   apply (mu_monotonic d); intro x.
   apply (in_p2_d_dec (snd x)); [auto | | ]; intros H0; [rewrite H0 | rewrite <- H]; auto.
   transitivity (mu p2_d (fun b =>  [1-] in_p2_d b)); [ auto | ].
   rewrite (mu_is_Discrete carB carB_prop p2D), discrete_simpl.
   rewrite serie_zero; [auto | intros].
   fold (c2 k).
   apply (Ueq_orc (c2 k) 0); [auto | | ]; intros.
   rewrite H0; auto.
   fold p2; rewrite in_p2_d_p; [ Usimpl | ]; auto.
   intros.
   transitivity (serie (fun k => f a * (c2 k / c2 k * carB (p2 k) (snd a)))).
   rewrite serie_mult.   
   rewrite H; auto.
   apply cp_retract_p2d.
   apply serie_eq_compat; auto.

   rewrite (mu_is_Discrete carB carB_prop p2D), discrete_simpl. 
   apply serie_eq_compat; intros.
   set (g:=fun p0 => c2 k / c2 k * carB (p2 k) (snd p0) * f p0).
   apply (Ueq_orc (c2 k) 0); [auto | | ]; intros.
   fold c2; rewrite H; Usimpl.
   rewrite <- (mu_0 d).
   apply (mu_stable_eq d).
   simpl; apply ford_eq_intro; intros; unfold g; rewrite Udiv_by_zero; [Usimpl | ]; auto.
   unfold c2 in H; unfold coeff in *.
   apply (cover_elim (cover_not_first_repr (@eq B) carB carB_prop (D_points p2D)) k);
    [ auto | | ]; intros (H1, H2).
   generalize H; clear H; rewrite H2; repeat Usimpl; intros.
   unfold p2_d. rewrite Mlet_simpl.
   rewrite Umult_sym, Udiv_mult; [auto | | ].
   apply mu_stable_eq; unfold g; simpl; apply ford_eq_intro; intros.
   rewrite Udiv_refl; auto.
   unfold c2; rewrite H2; Usimpl; auto.
   auto.
   apply Ole_trans with (2:=dsnd_le (p2 k)).
   rewrite dsnd_simpl.
   apply (mu_monotonic d); intro; unfold fone; auto.
   elim H; rewrite H2;Usimpl; auto.
  Qed.


  Lemma elift_discr_fst : forall f : A -> U,
   mu d (fun ab => f (fst ab)) ==
   mu p2_d (fun b : B =>
    mu d (fun ab => carB b (snd ab) * f (fst ab)) /  mu d (fun ab => carB b (snd ab))). 
  Proof. intros; apply d_ito_p2_d. Qed.


 Lemma dd'_ndeg_l: forall f : A -> U,
   mu dd' (fun ac => f (fst ac)) == 0 <-> mu d1 f == 0.
 Proof.
   split; intros.
     rewrite dd'_1, <-(Hd.(el_supp_r)) in H.
     apply (Hd.(el_supp_l)).
     rewrite elift_discr_fst. 
     exact H.
     
     rewrite <-(Hd.(el_supp_l)) in H.
     rewrite dd'_1.
     rewrite <-(mu_zero d2).
     apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intro b; unfold fzero.
     apply Udiv_zero_eq; symmetry; apply Ule_zero_eq.
     rewrite <-H.
     refine (mu_monotonic _ _ _ _); refine (ford_le_intro _); intro ab; auto.
 Qed.


 End DISCRETE.

End LIFT_TRANS.


Section LIFT_TRANS_DISCR.

 Variables A B C : Type.
 Variable carB : B -> MF B.
 
 Hypothesis carB_prop : forall b, cover (fun x => b = x) (carB b).

 Variable P : A -> B -> Prop.
 Variable Q : B -> C -> Prop.
 Variable R : A -> C -> Prop.

 Hypothesis P_Q_R : forall x y z, P x y -> Q y z -> R x z.

 Variable d1 : Distr A.
 Variable d2 : Distr B.
 Variable d3 : Distr C.

 Variable d  : Distr (A * B).
 Variable d' : Distr (B * C).
 Variable ep ep' : U.

 Variable Hd : elift P d  d1 d2 ep.
 Variable Hd': elift Q d' d2 d3 ep'.
 
 Hypothesis discr_d : is_Discrete (Mlet d  (fun ab => Munit (snd ab))).
 Hypothesis discr_d': is_Discrete (Mlet d' (fun bc => Munit (fst bc))).


 Let d'' := dd' carB d d' d2.


 Lemma dd'_ndeg_r: forall g : C -> U,
   mu d'' (fun ac => g (snd ac)) == 0 <-> mu d3 g == 0.
 Proof.
   split; intros; unfold d'' in *.
     (*  *)
     rewrite (dd'_2 _ Hd Hd'), <-(Hd'.(el_supp_l)) in H.
     change (mu (Mlet (d_inv d') (fun cb => Munit (snd cb))) 
         (fun b => (mu (d_inv d')) (fun cb => carB b (snd cb) * g (fst cb)) /
          (mu (d_inv d')) (fun cb => carB b (snd cb))) == 0) in H.
     rewrite <-(elift_discr_fst _ carB_prop) in H; [ |
       refine (is_Discrete_eq_compat _ discr_d'); auto ].
     apply (Hd'.(el_supp_r)).
     rewrite d_inv_fst; exact H.
     (*  *)
     rewrite <-(Hd'.(el_supp_r)) in H.
     rewrite (dd'_2 _ Hd Hd').
     rewrite <-(mu_zero d2).
     apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intro b; unfold fzero.
     apply Udiv_zero_eq; symmetry; apply Ule_zero_eq.
     rewrite <-H.
     refine (mu_monotonic _ _ _ _); refine (ford_le_intro _); intro bc; auto.     
 Qed.


 Lemma elift_trans_discr: elift R  d'' d1 d3 (ep + ep').
 Proof.
  constructor. 
   (* distance *)
   apply dd'_dist with P Q; trivial.
     intro; refine (elift_discr_fst _ carB_prop discr_d _).
     intro.
     rewrite (d_inv_fst d'). rewrite (d_inv_snd d' (fun b =>
      (mu d') (fun bc' : B * C => carB b (fst bc') * g (snd bc')) /
      (mu d') (fun bc' : B * C => carB b (fst bc')))).
     refine (elift_discr_fst _ carB_prop _ _).
     refine (is_Discrete_eq_compat _ discr_d'); auto.
   (* range *)
   refine (dd'_range _ carB_prop _ P_Q_R Hd Hd').
   (* supp *)
   refine (dd'_ndeg_l _ carB_prop Hd Hd' discr_d).
   apply  dd'_ndeg_r.
 Qed.

End LIFT_TRANS_DISCR.


 Add Parametric Morphism A B : (elift (A:=A) (B:=B))
 with signature Fimp2 (A:=A) (B:=B) --> 
  Oeq (O:=Distr (A * B)) ==> Oeq (O:=Distr A) ==> 
  Oeq (O:=Distr B) ==> Oeq (O:=U) ==> Basics.flip impl
 as elift_morph.
 Proof.
  unfold impl, Fimp2; intros R1 R2 H d1 d2 H0 d3 d4 H1 d5 d6 H2 ep1 ep2 H3 H4.
  eapply elift_weaken  with R2 ep2; auto.
  apply elift_stable_eq with d2 d4 d6 ep2; auto.
 Qed.


 Lemma elift_dist: forall A B (R:A -> B -> Prop) 
  (d1:Distr A) (d2:Distr B) d ep (f:A -o> U) (g:B-o>U),
  (forall a b, R a b -> f a == g b) ->
  elift R d d1 d2 ep ->
  Uabs_diff (mu d1 f) (mu d2 g) <= ep.
 Proof.
  intros A B R d1 d2 d ep f g Hfg (Hdist, Hrange, _, _).
  rewrite (Uabs_diff_triangle_ineq (mu d1 f) _ (mu d (fun x => f (fst x)))).
  rewrite (Uabs_diff_triangle_ineq _ (mu d2 g) (mu d (fun x => g (snd x)))).
  match goal with 
   |- Uabs_diff ?F1 ?G1 + (Uabs_diff ?G1 ?G2 + Uabs_diff ?G2 ?F2) <= _ => 
     rewrite (proj2 (Uabs_diff_zero G1 G2)), Uplus_zero_left, (Uabs_diff_sym F1 G1)  
  end.
    apply Hdist.
    apply (range_eq Hrange); intros (a,b); apply (@Hfg a b).
 Qed.

