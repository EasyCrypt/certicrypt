(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

Require Import SwitchingSem.
Require Export While_stuff.
Require Export SD.
Require Import Classical.

Set Implicit Arguments.

 Hint Rewrite Uabs_diff_compat_eq.  
 Hint Resolve Oeq_sym neq_sym iff_refl.

(********************* MOVE THIS SOMEWHERE ELSE *********************)
(********************************************************************)

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


 Lemma Uplus_le_minus: forall a b c,
  a - b <= c -> a <= c + b.
 Proof.
   intros.
   apply (Ule_total a b); [auto|intro H'|intro H'].
     rewrite (Uminus_plus_le a b), (Uminus_le_zero _ _ H'); auto.
     apply (Uminus_le_perm_left _ _ _ H' H).
 Qed.


 Lemma Uabs_diff_restr: forall (A:Type) (d:Distr A)  f R,
  Uabs_diff (mu d f) (mu d (restr R f)) <= mu d (restr (negP R) f).
 Proof.
  intros.
  rewrite <-(Uplus_zero_right (mu d (restr R f))), 
    (mu_restr_split d R f), Uabs_diff_plus, Uabs_diff_compat_eq, Uplus_zero_left.
  unfold Uabs_diff; rewrite (Uminus_le_zero 0 _ (Upos _)); auto. 
 Qed.


 Lemma is_Discrete_eq_compat: forall (A:Type) (d1 d2:Distr A),
   d2 == d1 ->
   is_Discrete d2 ->
   is_Discrete d1.
 Proof.
  intros A d1 d3 Hd [p H].
  apply mkDiscr with p.
  unfold Discrete in *.
  refine (range_stable_eq Hd H).
 Qed.


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


 Definition d_inv (A B: Type) (d:distr (A*B)) := Mlet d (fun p => Munit (snd p, fst p)).

 Lemma d_inv_fst: forall (A B:Type) (d:distr (A*B)) g, 
   mu d (fun ab => g (snd ab)) == mu (d_inv d) (fun ba => g (fst ba)).
 Proof. intros; trivial. Qed.

 Lemma d_inv_snd: forall (A B:Type) (d:distr (A*B)) f, 
   mu d (fun ab => f (fst ab)) == mu (d_inv d) (fun ba => f (snd ba)).
 Proof. intros; trivial. Qed.


 Lemma discr_ext: forall (A:Type) (d1 d2: Distr A),
   (forall f, mu d1 f == 0 -> mu d2 f == 0) ->
   is_Discrete d1 ->
   is_Discrete d2.
 Proof.
  intros A d1 d2 Hd [p Hdis1].
  apply mkDiscr with p.
  unfold Discrete in *.
  intros f Hf.
  symmetry; apply Hd. 
  symmetry; apply (Hdis1 _ Hf).
 Qed.






(*
 Lemma foo'': forall (A:Type) (d1 d2:Distr A),
  (forall f, 0 == mu d1 f <-> 0 == mu d2 f) ->
  (forall R, srange R d1 <-> srange R d2).
 Proof.
  split; intros.
    destruct H0 as [H1 H2]; split.
      intros f Hf; rewrite <-H; apply (H1 _ Hf).
      intros f Hf; apply H2; rewrite H; trivial.
    destruct H0 as [H1 H2]; split.
      intros f Hf; rewrite H; apply (H1 _ Hf).
      intros f Hf; apply H2; rewrite <-H; trivial.
 Qed.


 Lemma foo''': forall (A:Type) (d1 d2:Distr A) R,
  srange R d1 -> 
  srange R d2 ->
  (forall f, 0 == mu d1 f <-> 0 == mu d2 f).
 Proof.
  intros A d1 d2 R [H11 H12] [H21 H22] f.
  split; intros.
    apply (H21 _ (H12 _ H)).
    apply (H11 _ (H22 _ H)).
 Qed.
*)

(*
 Lemma foo': forall (A:Type) (d1 d2:Distr A),
  (forall f, mu d1 f == 0 <-> mu d2 f == 0) ->
  (forall R, range R d1 <-> range R d2).
 Proof.
  intros; split.
    intros Hrd1 f Hf.
    symmetry; rewrite <-H; symmetry; apply (Hrd1 _ Hf).
    intros Hrd2 f Hf.
    symmetry; rewrite H; symmetry; apply (Hrd2 _ Hf).
 Qed.
*)

 Lemma deno_unroll_while_0: forall c e b k (m:Mem.t k),
   [[ unroll_while b c 0 ]] e m == Munit m.
 Proof.
   unfold unroll_while; intros.
   rewrite deno_cond.
   case (E.eval_expr b m); apply deno_nil.
 Qed.


 Ltac My_Usimpl :=  (try Usimpl); match goal with
    |- context [(Uabs_diff ?x ?x)] => setoid_rewrite (Uabs_diff_compat_eq x)
 end.  

Open Scope O_scope.
Open Scope U_scope.


(********************************************************************)
(* *** The classical statistical distance between two upto-bad  *** *)
(* *****  programs can be bounded by the probability of [bad] ***** *)
(********************************************************************)

 Lemma Fundamental_Lemma_GSD : forall E1 E2 c1 c2 k (m:Mem.t k) F,
   (forall P,  Pr E1 c1 m (P[&&]negP F) == Pr E2 c2 m (P[&&]negP F)) ->
   Pr E1 c1 m F <= Pr E2 c2 m F ->
   GSD ([[c1]] E1 m) ([[c2]] E2 m) (Pr E2 c2 m F).
 Proof.
  intros.
  eapply GSD_le_SD.
    apply mem_eqU_spec.
    apply sem_discr.  
    apply sem_discr.
    unfold SD; intros.
    apply Fundamental_Lemma.
    apply H.
    assumption.
 Qed.

 Lemma upto_bad_GSD : forall bad : Var.var T.Bool,
       Var.is_global bad ->
       forall (E1 E2 : env) (pi : upto_info bad E1 E2) (c1 c2 : cmd),
       check_bad pi c1 c2 ->
       lossless E2 c2 ->
       forall (k : nat) (m : Mem.t k), 
       GSD ([[c1]] E1 m) ([[c2]] E2 m) (Pr E2 c2 m (EP k bad)).
 Proof.
  intros.
  apply Fundamental_Lemma_GSD; intros.
  rewrite andP_comm; unfold Pr.
  transitivity (mu (([[ c1 ]]) E1 m) (restr (negP (EP k bad)) (charfun P)));
  [ apply mu_stable_eq; symmetry; apply restr_charfun_and | ].
  transitivity (mu (([[ c2 ]]) E2 m) (restr (negP (EP k bad)) (charfun P)));
  [ | apply mu_stable_eq; apply restr_charfun_and].
  unfold check_bad in H0.
  repeat (rewrite is_true_andb in H0; destruct H0).
  apply upto_bad_correct with pi; trivial; destruct pi; trivial.
  rewrite <- (negP_involutive (EP k bad)).
  unfold Pr.
  rewrite mu_neg_charfun, (fun d => mu_neg_charfun d (negP (EP k bad))).
  unfold fone; unfold lossless in H1; rewrite H1.
  fold (Pr E1 c1 m (negP (EP k bad))).
  rewrite (upto_bad_neg_bad H pi c1 c2); unfold Pr; auto.
 Qed.

(*
 Lemma foo: forall (A B: Type) (d:Distr (A * B)) R,
  range R d -> range (fun a => exists b, R (a,b)) (Mlet d (fun ab => Munit (fst ab))).
 Proof.
  intros.
  apply range_Mlet with (1:=H).
  intros (a,b) Hab; simpl.
  apply range_Munit; eauto.
 Qed.
*)
    
(********************************************************************)


Section Lift.

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


 Lemma elift_Munit: forall k (m1 m2: Mem.t k) (P:mem_rel), 
  P _ m1 m2 -> 
  elift (P k) (Munit (m1,m2)) (Munit m1) (Munit m2) (fzero nat k).
 Proof.
  intros; constructor.
   intros; repeat rewrite Uabs_diff_compat_eq; auto.
   apply range_Munit with (1:=H).
   intro; auto.
   intro; auto.
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
      intro; rewrite (l_fst H); auto.
      intro; rewrite (l_snd H); auto.
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
     rewrite (d_inv_fst d'), (d_inv_snd d' (fun b =>
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

End Lift.


 Lemma discr_srange: forall (A:Type) (d:Distr A)  
  (Hdiscr: is_Discrete d) (carA: A -> MF A),
  (forall a, cover (fun x => a = x) (carA a)) ->
  srange (fun a => exc (fun k => a = D_points Hdiscr k) /\ ~ mu d (carA a) == 0) d.
 Proof.
  intros.
  split.
    (* range *)
    intros f Hf.
    rewrite (mu_is_Discrete _ H Hdiscr); destruct Hdiscr; simpl in *.
    symmetry; apply serie_zero.
    intro k.
    apply (Ueq_orc (mu d (carA (D_points k))) 0); [ auto | | ]; intro Hk.
      unfold coeff; rewrite Hk; repeat Usimpl; trivial.
      rewrite <-Hf; [ auto | ];
        split; [ apply exc_intro with k | ]; trivial.
    (* drange *)
    intro f.
    rewrite (mu_is_Discrete _ H Hdiscr).
    intros Hf a [H1 H2]; simpl in *.
    generalize (serie_zero_elim _ (Oeq_sym Hf)); clear Hf; intro Hf.
    assert (H': exc (In_class eq (D_points Hdiscr) a)).
      apply H1;[auto | ].
      induction x using Wf_nat.lt_wf_ind; intros.
      apply (cover_elim (cover_not_first_repr _ _ H (D_points Hdiscr)) x);  
        [ auto | | ]; intros [H5 H6].
        apply exc_intro with x. 
        split; [ | red;intros;elim H5;apply exc_intro with k0];auto.
        apply H5;[auto | ].
        intros m (H7, H8);apply (H0 m); [ | rewrite <-H8 ]; auto.
    clear H1; apply H'; [ auto | intros k [Hk Hk']; subst; clear H' ].
    apply (Umult_zero_simpl_right (Oeq_sym (Hf k))).
    apply (cover_elim  (cover_not_first_repr _ _ H (D_points Hdiscr)) k); 
      [ auto | | ]; intros [H4 H5]. 
      unfold coeff; rewrite H5; repeat Usimpl; auto.
      apply H4; [auto | intros k2 [Hk2 Hk2'] ]; generalize (Hk' _ Hk2); tauto.
 Qed.



(*
   Given a distribution on a product, if both projections 
   are discrete, then the distribution is discrete. 
*)
Section DISCRETE.

 Variables A B: Type.

 Variable carB : B -> MF B.
 Variable carA : A -> MF A.
 
 Hypothesis carB_prop : forall b, cover (fun x => b = x) (carB b).
 Hypothesis carA_prop : forall a, cover (fun x => a = x) (carA a).

 Variable d  : Distr (A * B).
 
 Hypothesis discr_d1: is_Discrete (Mlet d (fun ab => Munit (fst ab))).
 Hypothesis discr_d2: is_Discrete (Mlet d (fun ab => Munit (snd ab))).


 Lemma discr_projs: is_Discrete d.
 Proof.
  destruct discr_d1 as [p1 H1]. 
  destruct discr_d2 as [p2 H2].
  apply mkDiscr with (fun k => (p1 (fst (bij_n_nxn k)), p2 (snd (bij_n_nxn k)))).
  unfold Discrete, range in *; simpl in *.
  intros f Hf.
  rewrite (d_ito_p2_d _ carB_prop discr_d2); simpl.
  apply H2 with (f:= fun b => 
      (mu d) (fun ab : A * B => carB b (snd ab) * f ab) /
      (mu d) (fun ab : A * B => carB b (snd ab))).
  intros b Hb; apply Hb; [ auto | intros kb Hkb ].
  symmetry; apply Udiv_zero_eq.

  transitivity (mu (d_inv d) (fun ba => carB b (fst ba) * f (snd ba, fst ba)));
    [ | simpl; apply (mu_stable_eq d); refine (ford_eq_intro _); intros (a',b'); auto ].
  rewrite (d_ito_p2_d _ carA_prop); [ simpl |
    refine (is_Discrete_eq_compat _  discr_d1); auto ].
  apply H1 with (f:= fun a  => mu d
    (fun ab => carA a (fst ab) * (carB b (snd ab) * f (fst ab, snd ab))) /
    mu d (fun ab => carA a (fst ab))).
  intros a Ha; apply Ha; [ auto | intros ka Hka ].
  symmetry; apply Udiv_zero_eq.

  rewrite <-(mu_zero d); unfold fzero;
  apply mu_stable_eq; refine (ford_eq_intro _).
  intros (a',b'); simpl.
  apply (cover_elim (carB_prop b) b'); [ auto | | ]; intros [H4 H5].
    rewrite H5; repeat Usimpl; trivial.
    rewrite H5, <-H4; Usimpl; clear H4 H5.
    apply (cover_elim (carA_prop a) a'); [ auto | | ]; intros [H4 H5].
      rewrite H5; repeat Usimpl; trivial.
      rewrite H5, <-H4; Usimpl; clear H4 H5.
      apply Hf.
      destruct (bij_surj ka kb) as [k Hk].
      apply exc_intro with k.
      rewrite Hk; simpl; rewrite Hkb, Hka; trivial.
 Qed.

End DISCRETE.



 Add Parametric Morphism A B : (elift (A:=A) (B:=B))
 with signature Fimp2 (A:=A) (B:=B) --> 
  Oeq (O:=Distr (A * B)) ==> Oeq (O:=Distr A) ==> 
  Oeq (O:=Distr B) ==> Oeq (O:=U) ==> inverse impl
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


 Lemma elift_deno_witness_discr: forall (c1 c2:cmd) e1 e2 k (m1 m2:Mem.t k) d R ep,
  elift R d ([[c1]] e1 m1) ([[c2]] e2 m2) ep ->
  is_Discrete d.
 Proof.
  intros.
  destruct H as (_, _, Hl, Hr).
  apply discr_projs with (carA:=@mem_eqU k) (carB:=@mem_eqU k).
    apply mem_eqU_spec.
    apply mem_eqU_spec.
    apply discr_ext with ([[c1]] e1 m1).
      intros f Hf; apply (proj2 (Hl f) Hf).
      apply sem_discr.
    apply discr_ext with ([[c2]] e2 m2).
      intros f Hf; apply (proj2 (Hr f) Hf).
      apply sem_discr.
 Qed.

(********************************************************************)
(********************************************************************)


 Definition dist_prg (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) (ep:nat-o>U) :=
  forall k, exists d,
   forall (m1 m2 : Mem.t k),
   P _ m1 m2 ->
   elift (@Q k) (d m1 m2) ([[c1]] E1 m1)  ([[c2]] E2 m2) (ep k).


 Lemma dist_prg_deno: forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) ep,
  dist_prg P E1 c1 E2 c2 Q ep ->
  forall (k : nat) (f g : Mem.t k -> U),
  (forall m1 m2 : Mem.t k, Q k m1 m2 -> f m1 == g m2) ->
   forall m1 m2 : Mem.t k,
   P k m1 m2 -> Uabs_diff (mu ([[c1]] E1 m1) f) (mu ([[c2]] E2 m2) g) <= ep k.
 Proof.
  unfold dist_prg; intros.
  destruct (H k) as [d Hd]; clear H.
  apply elift_dist with (Q k) (d m1 m2); auto.
 Qed.     


 Lemma dist_prg_sdeno: forall c1 E1 c2 E2 (P Q: mem_rel) ep,
   decMR P ->
   dist_prg P E1 c1 E2 c2 Q ep ->
   forall k (d1 d2 : Distr(Mem.t k)) (del:nat -o> U), 
   (exists d, elift (@P k) d d1 d2 (del k) /\ exists R, srange R d) ->
   forall f g,
   (forall m1 m2 : Mem.t k, Q k m1 m2 -> f m1 == g m2) ->
   Uabs_diff (mu (Mlet d1 ([[c1]] E1)) f) (mu (Mlet d2 ([[c2]] E2)) g) <= (ep k + del k).
 Proof.
  intros.
  destruct H0 as [d [Hd HdR] ].
  destruct (H k) as [d' Hd']; clear H.
  apply elift_dist with (R:=Q k) (d:=Mlet d (fun mm => d' (fst mm) (snd mm))).
    assumption.
    apply elift_Mlet with (P k); try assumption.
      exists (carac (fun mm => X k (fst mm) (snd mm)));
        apply (cover_dec (fun mm => X k (fst mm) (snd mm))).
 Qed.


 Lemma dist_prg_weaken: forall P E1 c1 E2 c2 Q ep P' Q' (ep':nat -o> U),
  implMR P P' ->
  implMR Q' Q ->
  ep' <= ep ->
  dist_prg P' E1 c1 E2 c2 Q' ep' ->
  dist_prg P  E1 c1 E2 c2 Q  ep.
 Proof.
  unfold dist_prg; intros.
  destruct (H2 k) as [d Hd]; clear H2.
  exists d.
  intros m1 m2 Hm. 
  apply elift_weaken with (Q' k) (ep' k); auto.
 Qed.

 Add Morphism dist_prg with signature 
   implMR --> (@eq env) ==> (@eq cmd) ==> (@eq env) ==> 
   (@eq cmd) ==> implMR ++> (@Ole (ford nat (tcpo U))) ++>
    impl as dist_prg_imp_Morph.
 Proof.
  unfold impl; intros.
  apply dist_prg_weaken with (4:=H2); assumption.
 Qed.   


 Add Morphism dist_prg with signature 
   iffMR ==> (@eq env) ==> (@eq cmd) ==> (@eq env) ==> 
   (@eq cmd) ==> iffMR ==> (@Oeq (ford nat (tcpo U))) ==> 
   iff as dist_prg_iff_Morph.
 Proof.
  unfold iffMR; intros. 
  destruct H; destruct H0.
  split; intros.
    apply dist_prg_weaken with (4:=H4); auto.
    apply dist_prg_weaken with (4:=H4); auto.
 Qed.


 Lemma dist_prg_trueR: forall (P:mem_rel) E1 c1 E2 c2 ep1 ep2,
  (forall k (m1 m2:Mem.t k), P _ m1 m2 ->
    ep1 k <=  mu ([[c1]] E1 m1) (fone _) /\
    ep2 k <=  mu ([[c2]] E2 m2) (fone _)) ->
  (forall k (m1 m2:Mem.t k), P _ m1 m2 ->
  ~ mu ([[c1]] E1 m1) (fone _) == 0 /\
  ~ mu ([[c2]] E2 m2) (fone _) == 0) ->
  dist_prg P E1 c1 E2 c2 trueR (fun k => [1-] (ep1 k) + [1-] (ep2 k)).
 Proof.
  unfold dist_prg; intros.
  exists (fun m1 m2 => prod_distr ([[c1]] E1 m1) ([[c2]] E2 m2)).
  intros m1 m2 Hm.
  eapply elift_weaken; [ | | apply (@elift_true _ _ ([[c1]] E1 m1) ([[c2]] E2 m2)) ].
    auto.
    apply Uplus_le_compat; Usimpl.
      exact (proj1 (H _ _ _ Hm)).
      exact (proj2 (H _ _ _ Hm)).
    exact (proj1 (H0 _ _ _ Hm)).
    exact (proj2 (H0 _ _ _ Hm)).
 Qed.


 Lemma dist_prg_trueR_lossless: forall (P:mem_rel) E1 c1 E2 c2,
   lossless E1 c1 -> 
   lossless E2 c2 -> 
   dist_prg P E1 c1 E2 c2 trueR (fzero _).
 Proof.
  intros.
  apply dist_prg_weaken with P trueR (fun k => [1-] fone _ k + [1-] fone _ k).
    trivial.
    trivial.
    unfold fzero, fone; refine (ford_le_intro _); intro k; rewrite Uinv_one; auto.
    apply dist_prg_trueR.
      intros k m1 m2 Hm; split; [ rewrite (H _ m1) | rewrite (H0 _ m2) ]; trivial.
      intros k m1 m2 Hm; split; [ rewrite (H _ m1) | rewrite (H0 _ m2) ]; auto.
 Qed.


 Lemma dist_prg_falseR: forall E1 c1 E2 c2 Q,
  dist_prg falseR E1 c1 E2 c2 Q (fzero _).
 Proof.
  unfold dist_prg; intros.
  exists (fun _ _ => distr0 _).
  unfold falseR; intros m1 m2 H; tauto.
 Qed.

 Hint Resolve dist_prg_falseR.


 Lemma dist_prg_transp: forall P E1 c1 E2 c2 Q ep,
   dist_prg (transpR P) E2 c2 E1 c1 (transpR Q) ep ->
   dist_prg P E1 c1 E2 c2 Q ep.
 Proof.
  unfold dist_prg, transpR; intros.
  destruct (H k) as [d Hd]; clear H.
  exists (fun m1 m2 => Mlet (d m2 m1) (fun mm => Munit (snd mm, fst mm))).
  intros.
  apply elift_transp.
  apply elift_stable_eq with (5:=Hd _ _ H); auto.
    rewrite Mcomp, <-(Mext (d m2 m1)) at 1.
    apply Mlet_eq_compat; trivial.
    refine (ford_eq_intro _); intros (m1',m2'); auto.
 Qed.


 Lemma dist_prg_sym :  forall P E1 c1 E2 c2 Q ep,
  symMR P ->
  symMR Q ->
  dist_prg P E2 c2 E1 c1 Q ep ->
  dist_prg P E1 c1 E2 c2 Q ep.
 Proof.
  intros.
  apply dist_prg_transp.
  unfold symMR in *; rewrite H, H0; trivial.
 Qed.


 Lemma dist_prg_case: forall  (P P':mem_rel) E1 c1 E2 c2 Q ep,
   decMR P' ->
   dist_prg (P /-\ P') E1 c1 E2 c2 Q ep ->
   dist_prg (P /-\ ~-P') E1 c1 E2 c2 Q ep ->
   dist_prg P E1 c1 E2 c2 Q ep. 
 Proof.
  unfold andR, notR, dist_prg; intros.
  destruct (H k) as (dt,Hdt); destruct (H0 k) as (df,Hdf); clear H H0.
  exists (fun m1 m2 => if X k m1 m2 then dt m1 m2 else df m1 m2); intros.
  destruct (X k m1 m2); auto.
 Qed.


 Lemma dist_prg_nil: forall P E1 E2, 
   dist_prg P E1 nil E2 nil P (fzero _).
 Proof.
  unfold dist_prg; intros.
  exists (fun m1 m2 => Munit (m1, m2)); intros.
  repeat rewrite deno_nil. 
  apply (elift_Munit _ _ _ H).
 Qed.


 Lemma dist_prg_seq: forall P E1 c1 E2 c2 Q' ep Q c1' c2' ep',
   decMR Q' ->
   dist_prg P E1 c1  E2 c2 Q' ep ->
   dist_prg Q' E1 c1' E2 c2' Q ep' ->
   dist_prg P E1 (c1 ++ c1') E2 (c2 ++ c2') Q (fplus ep' ep).
 Proof.
   unfold dist_prg; intros.
   destruct (H k) as (d, Hd); destruct (H0 k) as (d', Hd'); clear H H0.
   exists (fun m1 m2 => Mlet (d m1 m2) (fun p => d' (fst p) (snd p))). 
     intros.
     repeat rewrite deno_app.
     apply elift_Mlet with (Q' k); auto.
       exists (carac (fun mm => X k (fst mm) (snd mm))).
         apply (cover_dec (fun mm => X k (fst mm) (snd mm))).
         eexists; apply (discr_srange (elift_deno_witness_discr (Hd _ _ H)) _ 
           (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k))).
 Qed.


 Lemma dist_prg_trans_l : forall (P1 P2 Q1 Q2 Q3:mem_rel) E1 c1 E2 c2 E3 c3 ep ep',
  decMR P2 ->
  refl_supMR2 P2 P1 ->
  (forall k x y z, Q1 k x y -> Q2 k y z -> Q3 k x z) -> 
  dist_prg P1 E1 c1 E2 c2 Q1 ep-> 
  dist_prg P2 E2 c2 E3 c3 Q2 ep'->
  dist_prg P2 E1 c1 E3 c3 Q3 (fplus ep ep').
 Proof.
  intros.
  intros k; destruct (H1 k) as (d, Hd); destruct (H2 k) as (d',Hd').
  exists (
   fun m1 m3 =>
    match X k m1 m3 with
    | left _ =>
        dd' (@mem_eqU k) (d m1 m1) (d' m1 m3) ([[c2]] E2 m1)
    | _ => distr0 _
    end).  
  intros m1 m3 HP2.
  destruct (X k m1 m3); simpl.
    (* P m1 m3 *)
    apply elift_trans_discr with (P:=Q1 k) (Q:=Q2 k). 
      apply mem_eqU_spec.
      apply H0.
      apply (Hd _ _ (H _ _ _ p)).
      apply (Hd' _ _ p).
      apply discr_ext with (d1:=[[c2]] E2 m1).
        intros f Hf; apply (proj2 (el_supp_r (Hd _ _ (H _ _ _ p)) f) Hf).
        apply sem_discr.
      apply discr_ext with (d1:=[[c2]] E2 m1).
        intros f Hf; apply (proj2 (el_supp_l (Hd' _ _ p) f) Hf).
        apply sem_discr.
    (* ~P m1 m3 *)
    tauto.
 Qed.


 Lemma dist_prg_trans_r : forall (P1 P2 Q1 Q2 Q3:mem_rel) E1 c1 E2 c2 E3 c3 ep ep',
  decMR P1 ->
  refl_supMR2 (transpR P1) (transpR P2) ->
  (forall k x y z, Q1 k x y -> Q2 k y z -> Q3 k x z) -> 
  dist_prg P1 E1 c1 E2 c2 Q1 ep -> 
  dist_prg P2 E2 c2 E3 c3 Q2 ep' ->
  dist_prg P1 E1 c1 E3 c3 Q3 (fplus ep' ep).
 Proof.
  intros; apply dist_prg_transp.
  apply dist_prg_trans_l with (P1 := transpR P2) (P2:=transpR P1)
   (Q1 := transpR Q2) (Q2 := transpR Q1) (E2 := E2) (c2:= c2).
  auto. 
  trivial.
  unfold transpR; intros; eapply H0; eauto.
  apply dist_prg_transp; repeat rewrite transpR_transpR; trivial.
  apply dist_prg_transp; repeat rewrite transpR_transpR; trivial.
 Qed.


 Lemma dist_prg_cond_l : forall P E1 e c c' E2 c2 Q ep,
  dist_prg (P /-\ EP1 e) E1 c E2 c2 Q ep ->
  dist_prg (P /-\ ~- EP1 e) E1 c' E2 c2 Q ep ->
  dist_prg P E1 [If e then c else c'] E2 c2 Q ep.
 Proof.
  unfold dist_prg, andR, notR, EP1, is_true.
  intros P E3 e1 c c' E4 c2 Q ep Ht Hf k.
  destruct (Ht k) as (dt,Hdt); destruct (Hf k) as (df,Hdf); clear Ht Hf.
  exists (fun m1 m2 => if E.eval_expr e1 m1 then dt m1 m2  else df m1 m2). 
  intros.
  repeat rewrite deno_cond.
  case_eq (E.eval_expr e1 m1); intros Heq;
   [ apply Hdt | apply Hdf ]; (split; [ | rewrite Heq]; auto).
 Qed.


 Lemma dist_prg_cond_r :  forall P E1 c1 E2 e c c' Q ep,
  dist_prg (P /-\ EP2 e) E1 c1 E2 c Q ep ->
  dist_prg (P /-\ ~- EP2 e) E1 c1 E2 c' Q ep ->
  dist_prg P E1 c1 E2 [If e then c else c'] Q ep.
 Proof.
  unfold dist_prg, andR, notR, EP2, is_true.
  intros P E3 c c' e E4 c2 Q ep Ht Hf k.
  destruct (Ht k) as (dt,Hdt); destruct (Hf k) as (df,Hdf); clear Ht Hf.
  exists (fun m1 m2 => if E.eval_expr e m2 then dt m1 m2  else df m1 m2). 
  intros.
  repeat rewrite deno_cond.
  case_eq (E.eval_expr e m2); intros Heq;
   [ apply Hdt | apply Hdf ]; (split; [ | rewrite Heq]; auto).
 Qed.


 Lemma dist_prg_cond : forall P Q E1 (e1:E.expr T.Bool) c1 c2 E2 (e2:E.expr T.Bool) c3 c4 ep,
  dist_prg (P /-\ (EP1 e1 /-\ EP2 e2)) E1 c1 E2 c3 Q ep ->
  dist_prg (P /-\ (~- EP1 e1 /-\ ~- EP2 e2)) E1 c2 E2 c4 Q ep ->
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
  dist_prg P E1 [If e1 then c1 else c2] E2 [If e2 then c3 else c4] Q ep.
 Proof.
  intros; apply dist_prg_cond_l; apply dist_prg_cond_r.
  simplMR; trivial.
  apply dist_prg_weaken with falseR Q (fzero _); auto; unfold EP1, EP2.
    intros k m1 m2 ((H2, H3), H4); apply H4; erewrite <-H1; eauto.
  apply dist_prg_weaken with falseR Q (fzero _); auto; unfold EP1, EP2.
    intros k m1 m2 ((H2, H3), H4); apply H3; erewrite H1; eauto.
  simplMR; trivial.
 Qed.


 Lemma dist_prg_assign: forall E1 (t1 : T.type) (x1 : Var.var t1) 
   (e1 : E.expr t1) E2 (t2 : T.type) (x2 : Var.var t2) (e2 : E.expr t2)  Q,
    dist_prg (upd_para Q x1 e1 x2 e2) E1 [x1 <- e1] E2 [x2 <- e2] Q (fzero _).
 Proof.
  unfold dist_prg, upd_para; intros. 
  exists (fun m1 m2 => Munit (m1{!x1<-- E.eval_expr e1 m1!}, m2{!x2<--E.eval_expr e2 m2!})). 
  intros.
  repeat rewrite deno_assign; auto using elift_Munit.
 Qed.


(*
 Lemma dist_prg_failure_events: forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) (ep ep1: nat -o> U)
  (bad1 bad2: Var.var T.Bool),
  (forall k (m1 m2:Mem.t k), P _ m1 m2 -> Pr E1 c1 m1 (EP k bad1) + Pr E2 c2 m2 (EP k bad2) <= ep k) ->
   dist_prg P E1 c1 E2 c2 ((~-EP1 bad1 \-/ ~-EP2 bad2) |-> Q) ep1 ->
   dist_prg P E1 c1 E2 c2 Q (fplus (fplus ep1 ep) ep1).
 Proof.
  unfold dist_prg;  intros.
  destruct (H0 k) as [d Hd]; clear H0.
  exists (fun m1 m2 => drestr (d m1 m2) (fun mm => if andb (fst mm bad1) (snd mm bad2) then false else true)).
  intros m1 m2 Hm.
  constructor.
    (* dist *)
    intros.
    rewrite (Uabs_diff_triangle_ineq _ (mu ([[c1]] E1 m1) f) (mu (d m1 m2) (fun x => f (fst x)))).
    rewrite (Uabs_diff_triangle_ineq _ (mu ([[c2]] E2 m2) g) (mu (d m1 m2) (fun x => g (snd x)))).
    match goal with |- (?A + ?B) + (?C + ?D) <= _ =>
      rewrite <-(Uplus_assoc A), (Uplus_sym B), Uplus_assoc, (Uplus_assoc A), <-(Uplus_assoc), (Uplus_sym D)
    end.
    apply Uplus_le_compat.
      rewrite mu_drestr, (Uabs_diff_sym _ (mu _ (fun x => f (fst x)))), Uabs_diff_restr.
      rewrite mu_drestr, (Uabs_diff_sym _ (mu _ (fun x => g (snd x)))), Uabs_diff_restr.
      transitivity ( mu (d m1 m2) (fun x => charfun (EP k bad1) (fst x)) + 
        mu (d m1 m2) (fun x => charfun (EP k bad2) (snd x))).
        apply Uplus_le_compat; unfold charfun, restr, EP, negP;
          (apply mu_le_compat; [ trivial | simpl ]; refine (ford_le_intro _); 
            intro mm; case (fst mm bad1); case (snd mm bad2); simpl; auto).
      unfold fplus; rewrite <-(H _ _ _ Hm).
      apply Uplus_le_minus.
      rewrite <-(el_dist (Hd _ _  Hm) (charfun (EP k bad1)) (charfun (EP k bad2))).
      rewrite <-Uabs_diff_plus; apply Ule_plus_right.
      apply (el_dist (Hd _ _ Hm)).
    (* range *)
    unfold drestr; apply range_Mlet with (1:=el_range (Hd _ _ Hm)).
    unfold prodP, notR, impR, orR, EP1, EP2; intros (m1',m2') Hm'; 
     unfold fst, snd in *; generalize Hm'; simpl.
    case (m1' bad1); case (m2' bad2); intros Hbad; simpl. 
      apply distr0_range; trivial.
      apply range_Munit; apply Hbad; right; discriminate.
      apply range_Munit; apply Hbad; left; discriminate.
      apply range_Munit; apply Hbad; left; discriminate.
 Qed.
*)

  
 Lemma equiv_dist_prg: forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel),
   dist_prg P E1 c1 E2 c2 Q (fzero _) <-> equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold equiv, dist_prg; split; intros.
    (* dist_prg ==> equiv *)
    destruct (H k) as [d Hd]; clear H.
    exists d.
      intros m1 m2 H; rewrite <-lift_elift; exact (Hd _ _ H).
    (* equiv ==> dist_prg *)
    destruct (H k) as [d Hd]; clear H.
    exists d.
      intros m1 m2 H; rewrite lift_elift; exact (Hd _ _ H).
 Qed.


 Lemma dist_prg_random_permut: forall (Q:mem_rel) E1 t (x1:Var.var t) (D1:E.support t) 
   E2 (x2: Var.var t) (D2:E.support t) (h:forall k, Mem.t k -> Mem.t k -> T.interp k t -> T.interp k t),
  dist_prg 
   ((permut_support h D1 D2) /-\ (fun k m1 m2 => forall v, In v (E.eval_support D2 m2) -> 
     Q k (m1{!x1 <-- h k m1 m2 v!}) (m2{!x2 <-- v!})))
   E1 [x1 <$- D1] E2 [x2 <$- D2] Q (fzero _).
 Proof.
  intros.
  rewrite equiv_dist_prg.
  apply equiv_random_permut. 
 Qed.


 Lemma dist_prg_while : forall (P:mem_rel) E1 (e1:E.expr T.Bool) c1 E2 (e2:E.expr T.Bool) c2,
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
  dist_prg (P /-\ EP1 e1 /-\ EP2 e2) E1 c1 E2 c2 P (fzero _) -> 
  dist_prg P E1 [while e1 do c1] E2 [while e2 do c2] (P /-\ ~-EP1 e1 /-\ ~-EP2 e2) (fzero _).
 Proof.
  intros.
  rewrite equiv_dist_prg.
  apply (equiv_while H).
  rewrite <-equiv_dist_prg.
  assumption.
 Qed.

    
 Section For_loop_rule.
 
  Variables i : E.expr T.Nat.
  
 (* [q] is a constant expression *)
  Variable q: E.expr T.Nat.
  Variable q_interp : nat -> nat.
  Hypothesis Hq_cte : forall k (m:Mem.t k), E.eval_expr q m = q_interp k.

  Variables c1 c2 : cmd.
  Variables e1 e2 : env.

  Variables I: mem_rel.

  (* First argument is the security parameter *)
  Variable h : nat -> nat -o> U.

  Hypothesis Hc: forall n:nat, 
    dist_prg 
    (I /-\ EP1 (i=?=n) /-\ EP2 (i=?=n)) 
    e1 c1 e2 c2 
    (I /-\ EP1 (i=?=S n) /-\ EP2 (i=?=S n))
    (fun k => h k n).


  Variable P1 P2: forall k, Mem.t k -> Prop.

  Hypothesis H_P : forall k (m1 m2:Mem.t k), I m1 m2 -> P1 m1 /\ P2 m2.

  Hypothesis Hran1: forall k (m:Mem.t k),
    P1 m -> 
    range (fun m' => E.eval_expr i m' = S (E.eval_expr i m) /\ P1 m') (([[c1]]) e1 m).
  Hypothesis Hran2: forall k (m:Mem.t k),
    P2 m -> 
    range (fun m' => E.eval_expr i m' = S (E.eval_expr i m) /\ P2 m')  (([[c2]]) e2 m).

  Hypothesis I_dec: decMR I.


  Lemma cover_prec: forall (n k:nat),
    cover (prodP ((I /-\ EP1 (i =?= n) /-\ EP2 (i =?= n)) k )) 
     (fun mm => (fun z => if I_dec (fst z) (snd z) then 1 else 0) mm * (
     ((fun z => if nat_eqb (E.eval_expr i (fst z)) n then 1 else 0) mm) * 
     ((fun z => if nat_eqb (E.eval_expr i (snd z)) n then 1 else 0) mm))).
  Proof.
   intros; unfold prodP, andR.
   repeat apply cover_inter_mult.
     apply  (cover_dec (fun mm => @I_dec k (fst mm) (snd mm))).
     unfold cover; unfold EP1; simpl; unfold O.eval_op; simpl.
     intro mm; generalize (nat_eqb_spec (E.eval_expr i (fst mm)) n);
     case (nat_eqb (E.eval_expr i (fst mm)) n); split; intros; trivial.
       generalize is_true_true; tauto.
       discriminate.
     unfold cover; unfold EP2; simpl; unfold O.eval_op; simpl.
     intro mm; generalize (nat_eqb_spec (E.eval_expr i (fst mm)) n);
     case (nat_eqb (E.eval_expr i (snd mm)) n); split; intros; trivial.
       generalize is_true_true; tauto.
       discriminate.
 Qed.


 (* REMARK: wasn't able to weaken the poscondition in [Hc] 
    using [Hran1], [Hran2] and [H_P] *)

  Lemma dist_prg_for_loop :  dist_prg 
   (I /-\ EP1 (i=?=0%nat) /-\ EP2 (i=?=0%nat)) 
   e1 [ while (i <! q) do c1 ] e2 [ while (i <! q) do c2 ] 
   (I /-\ EP1 (i=?=q) /-\ EP2 (i=?=q))  
   (fun k => sigma (h k) (q_interp k)).
  Proof.
   unfold dist_prg; intros.
   cut (exists d: Mem.t k -> Mem.t k -> Distr (Mem.t k * Mem.t k),
     forall m1 m2 : Mem.t k,
     (I /-\ EP1 (i =?= 0%nat) /-\ EP2 (i =?= 0%nat)) k m1 m2 ->
     elift ((I /-\ EP1 (i =?= q_interp k) /-\ EP2 (i =?= q_interp k)) k) 
       (d m1 m2) (([[ [while i <! q_interp k do c1] ]]) e1 m1)
       (([[ [while i <! q_interp k do c2] ]]) e2 m2) ((sigma (h k)) (q_interp k))).
     intros [d Hd].
     exists d; intros m1 m2 Hm.
     eapply elift_weaken with (P:=(I /-\ EP1 (i =?= q_interp k) /-\ EP2 (i =?= q_interp k)) k).
       intros m1' m2' [HI [H1 H2] ]; repeat split; unfold EP1, EP2 in *.
         trivial.
         rewrite <-(Hq_cte m1') in H1; apply H1.
         rewrite <-(Hq_cte m2') in H2; apply H2.
       apply Ole_refl.
     eapply elift_stable_eq with (5:=Hd _ _ Hm); trivial.
     apply eq_distr_intro; intro f.
     apply while_eq_guard_compat_elim. 
     intro m'; change (leb (E.eval_expr i m' + 1) (q_interp k) = 
       leb (E.eval_expr i m' + 1) (E.eval_expr q m')); rewrite Hq_cte; trivial.
     apply eq_distr_intro; intro f.
     apply while_eq_guard_compat_elim. 
     intro m'; change (leb (E.eval_expr i m' + 1) (q_interp k) = 
       leb (E.eval_expr i m' + 1) (E.eval_expr q m')); rewrite Hq_cte; trivial.

   induction (q_interp k).
     (* base case *)
     exists (fun m1 m2 => Munit (m1,m2)).
     intros m1 m2 Hm; constructor.
       (* dist *)
       intros f g.
       repeat rewrite deno_while_elim, deno_cond_elim.
       replace (@E.eval_expr _ T.Bool (i <! 0) m1) with false by 
         (symmetry; apply (leb_correct_conv 0%nat (E.eval_expr i m1 + 1)); omega). 
       replace (@E.eval_expr _ T.Bool (i <! 0) m2) with false by 
         (symmetry; apply (leb_correct_conv 0%nat (E.eval_expr i m2 + 1)); omega). 
       repeat rewrite deno_nil_elim, Munit_eq, Uabs_diff_compat_eq; auto.
       (* range *)
       apply range_Munit; assumption.
       (* supp *)
       intro f.
       rewrite deno_while_elim, deno_cond_elim.
       replace (@E.eval_expr _ T.Bool (i <! 0) m1) with false by 
         (symmetry; apply (leb_correct_conv 0%nat (E.eval_expr i m1 + 1)); omega). 
       rewrite deno_nil_elim, Munit_eq; auto.
       intro g.
       rewrite deno_while_elim, deno_cond_elim.
       replace (@E.eval_expr _ T.Bool (i <! 0) m2) with false by 
         (symmetry; apply (leb_correct_conv 0%nat (E.eval_expr i m2 + 1)); omega). 
       rewrite deno_nil_elim, Munit_eq; auto.
     (* inductive case *)
      assert (H1: forall (m:Mem.t k) f, P1 m -> E.eval_expr i m = 0%nat -> 
        mu ([[ [while i <! S n do c1] ]] e1 m) f == 
        mu ([[ [while i <! n do c1] ]] e1 m) (fun m' => mu ([[c1]] e1 m') f)).
        intros.
         rewrite <-(deno_cons_elim e1 (while i <! n do c1) c1 m f).
         apply (init_for_loop_tail_unroll _ _ P1 m _ Hran1 H H0).  
      assert (H2: forall (m:Mem.t k) f, P2 m -> E.eval_expr i m = 0%nat -> 
        mu ([[ [while i <! S n do c2] ]] e2 m) f == 
        mu ([[ [while i <! n do c2] ]] e2 m) (fun m' => mu ([[c2]] e2 m') f)).
        intros.
         rewrite <-(deno_cons_elim e2 (while i <! n do c2) c2 m f).
         apply (init_for_loop_tail_unroll _ _ P2 m _ Hran2 H H0).
       


     destruct IHn as [d Hd].
     destruct (Hc n k) as [d' Hd']; clear Hc.
     exists (fun m1 m2 => Mlet (d m1 m2) (fun mm => d' (fst mm) (snd mm))).
     intros m1 m2 Hm; constructor.

       (* dist *)
       intros f g.
       set (Hm':=Hm).
       destruct Hm' as [HI [Hil Hir] ]; unfold EP1 in Hil; unfold EP2 in Hir.
       setoid_rewrite (eval_eq m1 i 0%nat) in Hil; apply nat_eqb_true in Hil.
       setoid_rewrite (eval_eq m2 i 0%nat) in Hir; apply nat_eqb_true in Hir.
       rewrite (H1 _ _ (proj1 (H_P HI)) Hil), (H2 _ _ (proj2 (H_P HI)) Hir).
       rewrite (Uabs_diff_triangle_ineq _ 
         (mu ([[ [while i <! n do c1] ]] e1 m1) (fun m => mu ([[c1]] e1 m) f))
         (mu (d m1 m2) (fun x => mu ([[c1]] e1 (fst x)) f))).
       rewrite (Uabs_diff_triangle_ineq _ 
         (mu ([[ [while i <! n do c2] ]] e2 m2) (fun m => mu ([[c2]] e2 m) g))
         (mu (d m1 m2) (fun x => mu ([[c2]] e2 (snd x)) g))).
       match goal with |- (?A + ?B) + (?C + ?D) <= _ =>
         rewrite <-(Uplus_assoc A), (Uplus_sym B), Uplus_assoc, (Uplus_assoc A), <-(Uplus_assoc), (Uplus_sym D)
       end.
       rewrite sigma_S; apply Uplus_le_compat.
         (* left inequality *)
         apply (Ueq_orc (h k n) 1); [apply Ule_class | | ]; intro Hhn.
           (* case [h n = 1] *)
           rewrite Hhn; auto.
           (* case [h n < 1] *)
           repeat rewrite Mlet_simpl.
           rewrite Uabs_diff_mu_compat, Uabs_diff_mu_compat, 
             <-(mu_stable_plus_range (el_range (Hd _ _ Hm))).
           rewrite <-(mu_cte_le (d m1 m2) (h k n)); apply (range_le (el_range (Hd _ _ Hm))).
             intros (m1',m2') Hm'; unfold fplus, fcte, fabs_diff.
             apply (el_dist (Hd' _ _ Hm')).
             intros (m1',m2') Hm'; unfold fabs_diff.
             apply Uplus_lt_Uinv; apply Ule_lt_trans with (h k n); [ | auto ].
             rewrite Uplus_sym; apply (el_dist (Hd' _ _ Hm')).
         (* right inequality *)
         apply (el_dist (Hd _ _ Hm) (fun m => mu ([[c1]] e1 m) f) (fun m => mu ([[c2]] e2 m) g)).

    (* range *)
    apply range_Mlet with (1:=el_range (Hd _ _ Hm)).
    intros (m1',m2') Hm'; apply (el_range (Hd' _ _ Hm')).

    (* supp_l *)
    assert (Hd_srange: exists R, srange R (d m1 m2)) by
       (eexists; apply (discr_srange  (elift_deno_witness_discr (Hd _ _ Hm)) _ 
         (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)))).
    destruct Hd_srange as (R,(Hd_ran,Hd_dran)).
    intro f.
    set (Hm':=Hm); destruct Hm' as [HI [Hil _] ]; unfold EP1 in Hil.
    setoid_rewrite (eval_eq m1 i 0%nat) in Hil; apply nat_eqb_true in Hil.
    rewrite Mlet_simpl, (H1 _ _ (proj1 (H_P HI)) Hil).
    generalize (el_supp_l (Hd _ _ Hm)); intro Hl.
    split; intro H.
      (*  *)
      rewrite <-Hl.
      symmetry; apply Hd_ran.
      intros (m1',m2') Hm'; simpl.
      assert (Hm'_2: (I /-\ EP1 (i =?= n) /-\ EP2 (i =?= n)) _ m1' m2') by
        refine (drange_range (@cover_prec n k) (el_range (Hd _ _ Hm)) Hd_dran _ Hm').
      destruct (Hd' _ _ Hm'_2) as (_, Hran', Hsupp', _); simpl in *.  
      symmetry; rewrite <-Hsupp'.
      symmetry; apply (Hd_dran _ (Oeq_sym H) _ Hm').
      (*  *)
      rewrite <-Hl in H.
      symmetry; apply Hd_ran.
      intros (m1',m2') Hm'; simpl.
      assert (Hm'_2: (I /-\ EP1 (i =?= n) /-\ EP2 (i =?= n)) _ m1' m2') by
        refine (drange_range (@cover_prec n k) (el_range (Hd _ _ Hm)) Hd_dran _ Hm').
      destruct (Hd' _ _ Hm'_2) as (_, Hran', Hsupp', _); simpl in *.  
      symmetry; rewrite Hsupp'.
      symmetry; apply (Hd_dran _ (Oeq_sym H) _ Hm').

    (* supp_r *)  
    assert (Hd_srange: exists R, srange R (d m1 m2)) by
       (eexists; apply (discr_srange  (elift_deno_witness_discr (Hd _ _ Hm)) _ 
         (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)))).
    destruct Hd_srange as (R,(Hd_ran,Hd_dran)).
    intro g.
    set (Hm':=Hm); destruct Hm' as [HI [_ Hir] ]; unfold EP2 in Hir.
    setoid_rewrite (eval_eq m2 i 0%nat) in Hir; apply nat_eqb_true in Hir.
    rewrite Mlet_simpl, (H2 _ _ (proj2 (H_P HI)) Hir).
    generalize (el_supp_r (Hd _ _ Hm)); intro Hr.
    split; intro H.
      (*  *)
      rewrite <-Hr.
      symmetry; apply Hd_ran.
      intros (m1',m2') Hm'; simpl.
      assert (Hm'_2: (I /-\ EP1 (i =?= n) /-\ EP2 (i =?= n)) _ m1' m2') by
        refine (drange_range (@cover_prec n k) (el_range (Hd _ _ Hm)) Hd_dran _ Hm').
      destruct (Hd' _ _ Hm'_2) as (_, Hran', _, Hsupp'); simpl in *.  
      symmetry; rewrite <-Hsupp'.
      symmetry; apply (Hd_dran _ (Oeq_sym H) _ Hm').
      (*  *)
      rewrite <-Hr in H.
      symmetry; apply Hd_ran.
      intros (m1',m2') Hm'; simpl.
      assert (Hm'_2: (I /-\ EP1 (i =?= n) /-\ EP2 (i =?= n)) _ m1' m2') by
        refine (drange_range (@cover_prec n k) (el_range (Hd _ _ Hm)) Hd_dran _ Hm').
      destruct (Hd' _ _ Hm'_2) as (_, Hran', _, Hsupp'); simpl in *.  
      symmetry; rewrite Hsupp'.
      symmetry; apply (Hd_dran _ (Oeq_sym H) _ Hm').
 Qed.

End For_loop_rule.



Section While_loop_rule.

  Variables c1 c2 : cmd.
  Variables e1 e2 : env.

  Variables I P1 P2: mem_rel.
  Variables b1 b2: E.expr T.Bool.


  Hypothesis I_b: forall k (m1 m2:Mem.t k), 
   I m1 m2 -> E.eval_expr b1 m1 = E.eval_expr b2 m2. 
 
  Hypothesis I_dec: decMR I.

  Hypothesis I_P: forall k (m1 m2:Mem.t k),
    I m1 m2 -> P1 m1 m1 /\ P2 m2 m2.

  Variable ep: nat -o> U.
  Hypothesis Hc:  
    dist_prg (I /-\ EP1 b1) e1 c1 e2 c2 I ep.


  Variable q: nat.

  Hypothesis H_while1:
    dist_prg 
    (Meq /-\ P1) 
    e1 [while b1 do c1]
    e1 (unroll_while b1 c1 q)
    (Meq /-\ ~-EP2 b1) 
    (fzero _).

  Hypothesis H_while2:
    dist_prg 
    (Meq /-\ P2) 
    e2 [while b2 do c2]
    e2 (unroll_while b2 c2 q)
    (Meq /-\ ~-EP2 b2) 
    (fzero _).

  Lemma while_rule: 
    dist_prg I e1 [while b1 do c1] e2  [while b2 do c2] (I /-\ ~-EP1 b1) 
    (fun k => q */ ep k).
  Proof.
   apply dist_prg_weaken with I (I /-\ ~-EP1 b1) (fplus (fzero _) (fplus (fzero _) 
      (fun k => q */ ep k))); trivial.
     unfold fplus, fzero; refine (ford_le_intro _); intro m; auto.
   apply dist_prg_trans_l  with (1:=I_dec) (4:=H_while1) (Q2:=I).
     intros k m1 m2 Hm; split; [ trivial | apply (proj1 (I_P Hm)) ].
     intros k m1 m2 m3 [H1 H2] H3; split; rewrite H1; trivial.
   eapply dist_prg_trans_r  with (1:=I_dec) (5:=dist_prg_transp H_while2) (Q1:=I).
     intros k m1 m2 Hm; split; [ trivial | apply (proj2 (I_P Hm)) ].
     intros k m1 m2 m3 H1 [H2 _]; rewrite H2; trivial.

   clear H_while1 H_while2.
   induction q.
     (* base case *)
     intro k.
     exists (fun m1 m2 => Munit (m1,m2)).
     intros m1 m2 Hm; repeat rewrite deno_unroll_while_0.
     constructor.
       intros; simpl; repeat My_Usimpl; auto.
       apply range_Munit; trivial.
       auto.
       auto.

     (* inductive case *)
     unfold unroll_while; fold (unroll_while b1 c1 n) (unroll_while b2 c2 n). 
     apply dist_prg_cond with (3:=I_b).
       apply dist_prg_weaken with (I /-\ EP1 b1) I (fplus (fun k => n */ ep k) ep).
         rewrite <-andR_assoc; apply proj1_MR.
         trivial.
         unfold fplus; refine (ford_le_intro _); intro m; rewrite Uplus_sym; auto.
       apply dist_prg_seq with I; trivial.
       apply dist_prg_weaken with I I (fzero _).
         apply proj1_MR.
         trivial.
         unfold fzero; refine (ford_le_intro _); intro m; trivial.
       apply dist_prg_nil.
 Qed.

 End While_loop_rule.






(*
Section Adv_rule.


  Variables i : E.expr T.Nat.

  Variable X: Vset.t.
  Hypothesis i_X: forall k (m1 m2: Mem.t k), 
    m1 =={X} m2 -> E.eval_expr i m1 = E.eval_expr i m2.

  
 (* [q] is a constant expression *)
  Variable q: E.expr T.Nat.
  Variable q_interp : nat -> nat.
  Hypothesis Hq_cte : forall k (m:Mem.t k), E.eval_expr q m = q_interp k.

  Variables e1 e2 : env.

  (* First argument is the security parameter *)
  Variable h : nat -> nat -o> U.

  Variable P:mem_rel.

  Definition H_P (cl cr:cmd) := forall n:nat, 
    dist_prg 
    (Meq /-\ EP1 (i=?=n) /-\ EP2 (i=?=n) /-\ P) 
    e1 cl e2 cr 
    (Meq /-\ EP1 (i=?=S n) /-\ EP2 (i=?=S n))
    (fun k => h k n).

  Definition H_nP (cl cr:cmd) := forall n:nat, 
    dist_prg 
    (Meq /-\ EP1 (i=?=n) /-\ EP2 (i=?=n) /-\ ~-P) 
    e1 cl e2 cr 
    (Meq /-\ EP1 (i=?=n) /-\ EP2 (i=?=n))
    (fzero _).


  Variables (PrOrcl PrPriv:PrSet.t) (Gadv Gcomm:Vset.t).
  Variable retT : T.type.
  Variable A : Proc.proc retT.

  Hypothesis A_wf : WFAdv PrOrcl PrPriv Gadv Gcomm e1 A.

  Hypothesis Or_P: forall t (f:Proc.proc t), 
   PrSet.mem (BProc.mkP f) PrOrcl -> 
    H_P (proc_body e1 f) (proc_body e2 f).

  Hypothesis Or_nP: forall t (f:Proc.proc t), 
   PrSet.mem (BProc.mkP f) PrOrcl -> 
    H_nP (proc_body e1 f) (proc_body e2 f).

  Hypothesis Gadv_disj : Vset.disjoint X Gadv.

(*
  Variables y : Var.var retT.
  Variable x : E.args (Proc.targs A).
 *)

 Lemma dist_prg_bounded_calls:  
   dist_prg 
   (Meq /-\ EP1 (i=?=0%nat) /-\ EP2 (i=?=0%nat)) 
   e1 (proc_body e1 A)  e2 (proc_body e1 A) 
   (Meq /-\ EP1 (i<=!q) /-\ EP2 (i<=!q))  
   (fun k => sigma (h k) (q_interp k)).
 Proof.
  destruct A_wf as [O [HO1 HO2] ]; clear A_wf.
  clear HO2.
  induction HO1 using WFAdv_c_prop  with
     (P:=fun I c' O (H: WFAdv_c PrOrcl PrPriv Gadv Gcomm e1 I c' O) =>
       dist_prg (Meq /-\ EP1 (i =?= 0%nat) /-\ EP2 (i =?= 0%nat)) e1 c' e2 c'
     (Meq /-\ EP1 (i <=! q) /-\ EP2 (i <=! q))
     (fun k : nat => (sigma (h k)) (q_interp k)))
    (P0:=fun I i' O (H:WFAdv_i PrOrcl PrPriv Gadv Gcomm e1 I i' O) =>  
      dist_prg (Meq /-\ EP1 (i =?= 0%nat) /-\ EP2 (i =?= 0%nat)) e1 [i'] e2 [i']
     (Meq /-\ EP1 (i <=! q) /-\ EP2 (i <=! q))
     (fun k : nat => (sigma (h k)) (q_interp k))).

range_eq
  Focus 2.
  






     (forall x, Vset.mem x I -> Var.is_local x) -> inv_bad [i]); intros; trivial.








  Lemma dist_prg_for_loop :  dist_prg 

Section UptoBad.
 
 Definition forallP (A:Type) (P:A->Prop) (l:list A) :=
  forall x, In x l -> P x.

  Definition slossless E c := forallP (fun i => lossless E [i]) c. 

 Lemma slossless_cons: forall E i c, slossless E (i::c) -> lossless E c.
 Proof.
  induction c.
    intros _.
    admit.
  Admitted.
    
    
    
  

 Lemma upto_bad_dist_prg: forall bad : Var.var T.Bool,
   Var.is_global bad ->
   forall (E1 E2 : env) (pi : upto_info bad E1 E2) (c1 c2 : cmd),
   check_bad pi c1 c2 ->
   slossless E2 c2 ->
   forall (ep: nat-o>U),
   (forall k (m:Mem.t k), Pr E2 c2 m (EP k bad) <= ep k) ->
   dist_prg Meq E1 c1 E2 c2 Meq ep.
 Proof.
  Opaque I.eqb deno.
  intros bad Gbad E1 E2 pi.
  induction c1 using I.cmd_ind with (Pi:=fun i => forall c2',
   (*  preserves_bad bad pi [i] -> *)
    preserves_bad bad pi c2' ->
    upto_bad bad pi [i] c2' ->
 (*    lossless E2 c2' -> *)
    forall ep' : nat -o> U,
      (forall (k : nat) (m : Mem.t k), Pr E2 c2' m (EP k bad) <= ep' k) ->
      dist_prg Meq E1 [i] E2 c2' Meq ep').
  
  intros c2 Hc2 H.
  destruct c2; [discriminate H | ].
  destruct i0; try discriminate H.
  destruct i; destruct b; try discriminate H.



  Focus 7.
  (* cons *)
    intros c2 H Hloss ep Hep.
    unfold check_bad, is_true in H; repeat rewrite andb_true_iff in H; 
      destruct H as [ [Hp1 Hp2] H ].
    destruct c2; [ destruct i; discriminate H | 
      destruct i; destruct i0; try discriminate H ].
    destruct b; destruct b0; try discriminate H.
      (* Assign *) 
      simpl in H; unfold is_true in H; apply orb_prop in H; destruct H.
        (* case 1 *)
        apply andb_prop in H; destruct H as [Heq1 Heq2].
        generalize (I.eqb_spec (v <- e) (bad <- true)); rewrite Heq1; intro H1. 
        generalize (I.eqb_spec (v0 <- e0) (bad <- true)); rewrite Heq2; intro H2. 
        rewrite H1, H2 in *; clear H1 H2 Heq1 Heq2.
        intro k; exists (fun m1 m2 => 
        prod_distr ([[ [bad <- true] ]] E1 m1) ([[ [bad <- true] ]] E2 m2)).
        intros m1 m2 Hm.
        apply elift_weaken with (Meq k) 1.
          auto.
          rewrite <-(Hep _ m2). 
          unfold Pr; rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
          simpl in Hp2; unfold is_true in Hp2;
            apply andb_prop in Hp2; destruct Hp2 as [_ Hp2].
          unfold charfun; rewrite <-(preserves_bad_spec Gbad (upto_pr2 pi) _ Hp2);
            [ | unfold EP; simpl; rewrite Mem.get_upd_same; trivial ].
          rewrite (slossless_cons Hloss (m2 {!bad <-- true!})); trivial. 
        constructor.
          auto.
          intros f Hf; simpl.
          rewrite (deno_assign_elim _ _ _ m1), (deno_assign_elim _ _ _ m2).
          apply Hf; rewrite Hm; apply Meq_refl.
        (* case 2 *)
        apply andb_prop in H; destruct H.
        generalize (I.eqb_spec (v <- e) (v0 <- e0)); 
          rewrite H; clear H; intro H; rewrite H; clear H.  
        apply dist_prg_weaken with (upd_para Meq v0 e0 v0 e0) Meq (fplus ep (fzero _)).
          unfold upd_para; intros k m1 m2 Hm; rewrite Hm; apply Meq_refl.
          auto.
          unfold fplus; auto. 
        apply dist_prg_seq with (c1:=[v0 <- e0]) (c2:=[v0 <- e0]) (c1':=c1) (c2':=c2) (Q':=Meq). 
          apply dist_prg_assign.
          apply IHc0.
            unfold check_bad, is_true; repeat rewrite andb_true_iff; repeat split.  
              simpl in Hp1; rewrite andb_true_iff in Hp1; destruct Hp1; assumption.
              simpl in Hp2; rewrite andb_true_iff in Hp2; destruct Hp2; assumption.
              assumption.
              admit.
              
              



              unfold lossless in *.
              intros k m.
              generalize (Hloss _ m).
              rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
              


        intro k; exists (fun m1 m2 => 
          prod_distr ([[ [v0 <- e0] ]] E1 m1) ([[ [v0 <- e0] ]] E2 m2)).
      intros m1 m2 Hm; constructor.
        intros.
        rewrite prod_distr_fst, (lossless_assign _ _ _ m2), Umult_one_left, Uabs_diff_compat_eq.
        rewrite prod_distr_snd, (lossless_assign _ _ _ m1), Umult_one_left, Uabs_diff_compat_eq.
        auto.
        intros f Hf; simpl.
        rewrite (deno_assign_elim _ _ _ m1), (deno_assign_elim _ _ _ m2).
        apply Hf.
        apply HPQ with m1 m2; split; [ exact Hm | simpl ].
          admit.

        

          


          apply HPQ with m1 m2; split; simpl.
          trivial.
          admit.
     
        exists 



              

              auto.
            split.
        
        
        
        


    (* Assign *)
    Opaque I.eqb deno.
    intros ep Hep.
    simpl in H; unfold is_true in H; apply orb_prop in H; destruct H.
      (* case 1 *)
      apply andb_prop in H; destruct H as [Heq1 Heq2].
      generalize (I.eqb_spec (v <- e) (bad <- true)); rewrite Heq1; intro H1. 
      generalize (I.eqb_spec (v0 <- e0) (bad <- true)); rewrite Heq2; intro H2. 
      rewrite H1, H2 in *; clear H1 H2 Heq1 Heq2.   
      intro k; exists (fun m1 m2 => 
        prod_distr ([[ [bad <- true] ]] E1 m1) ([[ [bad <- true] ]] E2 m2)).
      intros m1 m2 Hm.
      apply elift_weaken with (Q k) 1.
        auto.
        rewrite <-(Hep _ m2).
        unfold Pr; rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
        simpl in Hc2; unfold is_true in Hc2;
          apply andb_prop in Hc2; destruct Hc2 as [_ Hc2].
        unfold charfun; rewrite <-(preserves_bad_spec Gbad (upto_pr2 pi) _ Hc2);
          [ | unfold EP; simpl; rewrite Mem.get_upd_same; trivial ].
        generalize (Hloss _ m2); rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
        auto.
      constructor.
        auto.
        intros f Hf; simpl.
        rewrite (deno_assign_elim _ _ _ m1), (deno_assign_elim _ _ _ m2).
        apply Hf.
        apply HPQ with m1 m2; split; simpl.
          trivial.
          admit.
      (* case 2 *)
      apply andb_prop in H; destruct H.
      destruct c2; try discriminate; clear H0.
      generalize (I.eqb_spec (v <- e) (v0 <- e0)); 
        rewrite H; clear H; intro H; rewrite H; clear H.  
      intro k; exists (fun m1 m2 => 
        prod_distr ([[ [v0 <- e0] ]] E1 m1) ([[ [v0 <- e0] ]] E2 m2)).
      intros m1 m2 Hm; constructor.
        intros.
        rewrite prod_distr_fst, (lossless_assign _ _ _ m2), Umult_one_left, Uabs_diff_compat_eq.
        rewrite prod_distr_snd, (lossless_assign _ _ _ m1), Umult_one_left, Uabs_diff_compat_eq.
        auto.
        intros f Hf; simpl.
        rewrite (deno_assign_elim _ _ _ m1), (deno_assign_elim _ _ _ m2).
        apply Hf.
        apply HPQ with m1 m2; split; [ exact Hm | simpl ].
          admit.


    (* Random *)
    intros ep Hep.
    simpl in H; unfold is_true in H.
    apply andb_prop in H; destruct H as [Heq Hc2'].
    destruct c2; try discriminate.
    generalize (I.eqb_spec (v <$- s) (v0 <$- s0)); 
      rewrite Heq; intro H; rewrite H.
    intros k.
    exists (fun m1 m2 => Mlet (sum_support (T.default k t0) 
      (E.eval_support s0 m1)) (fun v => Munit (m1{!v0<--v!}, m2{!v0<--v!}))).
    intros m1 m2 Hm; constructor.
      intros; repeat rewrite Mlet_simpl, deno_random_elim.
      change ((Uabs_diff 
      (sum_dom (T.default k t0) (E.eval_support s0 m1) 
        (fun v => f (m1 {!v0 <-- v!})))
      (sum_dom (T.default k t0) (E.eval_support s0 m1) 
        (fun v => f (m1 {!v0 <-- v!}))))  + 
      (Uabs_diff 
      (sum_dom (T.default k t0) (E.eval_support s0 m1) 
        (fun v => g (m2 {!v0 <-- v!})))
      (sum_dom (T.default k t0) (E.eval_support s0 m2) 
        (fun v => g (m2 {!v0 <-- v!})))) <= ep k).
      rewrite Uabs_diff_compat_eq, Uplus_zero_left.
      rewrite <-(Upos (ep k)); apply Oeq_le; rewrite Uabs_diff_zero.
      (* assume constant supports and apply [PermutP_refl] *)
      admit.
      intros f Hf; rewrite Mlet_simpl.
      change (0 == sum_dom (T.default k t0) (E.eval_support s0 m1) 
        (fun v1 => f (m1 {!v0 <-- v1!}, m2 {!v0 <-- v1!}))).
      symmetry; apply sum_dom_zero with (fun _ => True); [ trivial | ].
      intros v1 _. symmetry; apply Hf.
      apply HPQ with m1 m2; split; [ exact Hm | simpl ].
      admit.



    Focus 4.
    (* nil *)
    intros c2 H Hloss ep Hep.
    simpl in H; destruct c2.
    eapply dist_prg_weaken; [ | | | apply (dist_prg_nil P) ]; auto.
      intros k m1 m2 Hm; apply HPQ with m1 m2; split; auto.
    unfold check_bad in H;  repeat rewrite andb_false_r in H; discriminate H.


    Focus 4.
   
        
        



 Lemma upto_bad_dist_prg: forall (P Q:mem_rel),
   (forall k (m1 m2 m1' m2': Mem.t k), P _ m1 m2 /\ (Meq _ m1 m2 -> Meq _ m1' m2') -> Q _ m1' m2') ->
   forall bad : Var.var T.Bool,
   Var.is_global bad ->
   forall (E1 E2 : env) (pi : upto_info bad E1 E2) (c1 c2 : cmd),
   check_bad pi c1 c2 ->
   lossless E2 c2 ->
   forall (ep: nat-o>U),
   (forall k (m:Mem.t k), Pr E2 c2 m (EP k bad) <= ep k) ->
   dist_prg P E1 c1 E2 c2 Q ep.
 Proof.
  intros P Q HPQ bad Gbad E1 E2 pi.
  induction c1 using I.cmd_ind with (Pi:=fun i => forall c2',
    preserves_bad bad pi [i] ->
    preserves_bad bad pi c2' ->
    upto_bad bad pi [i] c2' ->
    lossless E2 c2' ->
    forall ep' : nat -o> U,
      (forall (k : nat) (m : Mem.t k), Pr E2 c2' m (EP k bad) <= ep' k) ->
      dist_prg P E1 [i] E2 c2' Q ep').
  
  intros c2 Hi Hc2 H Hloss.
  destruct c2; [discriminate H | ].
  destruct i0; try discriminate H.
  destruct i; destruct b; try discriminate H.

    (* Assign *)
    Opaque I.eqb deno.
    intros ep Hep.
    simpl in H; unfold is_true in H; apply orb_prop in H; destruct H.
      (* case 1 *)
      apply andb_prop in H; destruct H as [Heq1 Heq2].
      generalize (I.eqb_spec (v <- e) (bad <- true)); rewrite Heq1; intro H1. 
      generalize (I.eqb_spec (v0 <- e0) (bad <- true)); rewrite Heq2; intro H2. 
      rewrite H1, H2 in *; clear H1 H2 Heq1 Heq2.   
      intro k; exists (fun m1 m2 => 
        prod_distr ([[ [bad <- true] ]] E1 m1) ([[ [bad <- true] ]] E2 m2)).
      intros m1 m2 Hm.
      apply elift_weaken with (Q k) 1.
        auto.
        rewrite <-(Hep _ m2).
        unfold Pr; rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
        simpl in Hc2; unfold is_true in Hc2;
          apply andb_prop in Hc2; destruct Hc2 as [_ Hc2].
        unfold charfun; rewrite <-(preserves_bad_spec Gbad (upto_pr2 pi) _ Hc2);
          [ | unfold EP; simpl; rewrite Mem.get_upd_same; trivial ].
        generalize (Hloss _ m2); rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
        auto.
      constructor.
        auto.
        intros f Hf; simpl.
        rewrite (deno_assign_elim _ _ _ m1), (deno_assign_elim _ _ _ m2).
        apply Hf.
        apply HPQ with m1 m2; split; simpl.
          trivial.
          admit.
      (* case 2 *)
      apply andb_prop in H; destruct H.
      destruct c2; try discriminate; clear H0.
      generalize (I.eqb_spec (v <- e) (v0 <- e0)); 
        rewrite H; clear H; intro H; rewrite H; clear H.  
      intro k; exists (fun m1 m2 => 
        prod_distr ([[ [v0 <- e0] ]] E1 m1) ([[ [v0 <- e0] ]] E2 m2)).
      intros m1 m2 Hm; constructor.
        intros.
        rewrite prod_distr_fst, (lossless_assign _ _ _ m2), Umult_one_left, Uabs_diff_compat_eq.
        rewrite prod_distr_snd, (lossless_assign _ _ _ m1), Umult_one_left, Uabs_diff_compat_eq.
        auto.
        intros f Hf; simpl.
        rewrite (deno_assign_elim _ _ _ m1), (deno_assign_elim _ _ _ m2).
        apply Hf.
        apply HPQ with m1 m2; split; [ exact Hm | simpl ].
          admit.


    (* Random *)
    intros ep Hep.
    simpl in H; unfold is_true in H.
    apply andb_prop in H; destruct H as [Heq Hc2'].
    destruct c2; try discriminate.
    generalize (I.eqb_spec (v <$- s) (v0 <$- s0)); 
      rewrite Heq; intro H; rewrite H.
    intros k.
    exists (fun m1 m2 => Mlet (sum_support (T.default k t0) 
      (E.eval_support s0 m1)) (fun v => Munit (m1{!v0<--v!}, m2{!v0<--v!}))).
    intros m1 m2 Hm; constructor.
      intros; repeat rewrite Mlet_simpl, deno_random_elim.
      change ((Uabs_diff 
      (sum_dom (T.default k t0) (E.eval_support s0 m1) 
        (fun v => f (m1 {!v0 <-- v!})))
      (sum_dom (T.default k t0) (E.eval_support s0 m1) 
        (fun v => f (m1 {!v0 <-- v!}))))  + 
      (Uabs_diff 
      (sum_dom (T.default k t0) (E.eval_support s0 m1) 
        (fun v => g (m2 {!v0 <-- v!})))
      (sum_dom (T.default k t0) (E.eval_support s0 m2) 
        (fun v => g (m2 {!v0 <-- v!})))) <= ep k).
      rewrite Uabs_diff_compat_eq, Uplus_zero_left.
      rewrite <-(Upos (ep k)); apply Oeq_le; rewrite Uabs_diff_zero.
      (* assume constant supports and apply [PermutP_refl] *)
      admit.
      intros f Hf; rewrite Mlet_simpl.
      change (0 == sum_dom (T.default k t0) (E.eval_support s0 m1) 
        (fun v1 => f (m1 {!v0 <-- v1!}, m2 {!v0 <-- v1!}))).
      symmetry; apply sum_dom_zero with (fun _ => True); [ trivial | ].
      intros v1 _. symmetry; apply Hf.
      apply HPQ with m1 m2; split; [ exact Hm | simpl ].
      admit.



    Focus 4.
    (* nil *)
    intros c2 H Hloss ep Hep.
    simpl in H; destruct c2.
    eapply dist_prg_weaken; [ | | | apply (dist_prg_nil P) ]; auto.
      intros k m1 m2 Hm; apply HPQ with m1 m2; split; auto.
    unfold check_bad in H;  repeat rewrite andb_false_r in H; discriminate H.


    Focus 4.
    (* cons *)
    intros c2 H Hloss ep Hep.
    unfold check_bad, is_true in H; repeat rewrite andb_true_iff in H; destruct H as [ [Hp1 Hp2] H ].
    destruct c2; [ destruct i; discriminate H | destruct i; destruct i0; try discriminate H ].

      destruct b; destruct b0; try discriminate H.
      

      (* Assign *) 
      simpl in H; unfold is_true in H; apply orb_prop in H; destruct H.
        (* case 1 *)
        apply andb_prop in H; destruct H as [Heq1 Heq2].
        generalize (I.eqb_spec (v <- e) (bad <- true)); rewrite Heq1; intro H1. 
        generalize (I.eqb_spec (v0 <- e0) (bad <- true)); rewrite Heq2; intro H2. 
        rewrite H1, H2 in *; clear H1 H2 Heq1 Heq2.   
        
        
        
    admit.
    admit.
    

    destruct b; simpl in H; repeat rewrite andb_false_r in H; try discriminate H.
    destruct b; simpl in H; repeat rewrite andb_false_r in H; try discriminate H.
    


Focus 2.
simpl in H.


intro Heq; unfold is_true in Heq.
    apply orb_prop in Heq; destruct Heq as [Heq | Heq].
    rewrite Heq; trivial.
    apply andb_prop in Heq; destruct Heq as [Heq _];  
     rewrite Heq; rewrite orb_true_r; trivial.
    apply andb_prop in Heq; destruct Heq as [Heq _]; rewrite Heq; trivial.
    apply andb_prop in Heq; destruct Heq as [Heq _]; rewrite Heq; trivial.
    apply andb_prop in Heq; destruct Heq as [Heq _]; rewrite Heq; trivial.
    intro Heq; unfold is_true in Heq.
    apply andb_prop in Heq; destruct Heq as [Heq _]; rewrite Heq; trivial.
    intro Heq; unfold is_true in Heq.
    apply andb_prop in Heq; destruct Heq as [Heq _]; rewrite Heq; trivial.

    
      
      SearchAbout false.
      discriminate H.

      simpl in H.
      
      

    
    repeat rewrite deno_niel_elim; trivial.
    discriminate.

      
    (* Cond *)
    intros ep Hep.
    destruct c2; try discriminate H.
    destruct i; try discriminate H.
    simpl in H; unfold is_true in H.
    apply andb_prop in H; destruct H as [H Hc0].
    destruct c2; try discriminate Hc0.
    apply andb_prop in H; destruct H as [H Hc2'].
    apply andb_prop in H; destruct H as [He Hc1'].
    generalize (E.eqb_spec b e); rewrite He; intro H; rewrite H in *.
    clear He Hc0 H.

 


    simpl in Hpb1; unfold is_true in Hpb1.
    rewrite andb_true_r in Hpb1; apply andb_prop in Hpb1; destruct Hpb1.
    simpl in Hpb2; unfold is_true in Hpb2.
    rewrite andb_true_r in Hpb2; apply andb_prop in Hpb2; destruct Hpb2.

      


     (*
     exists (fun m1 m2 => 
        prod_distr ([[ [v0 <$- s0] ]] E1 m1) ([[ [v0 <$- s0] ]] E2 m2)).
      intros m1 m2 Hm; constructor.
        intros.
        rewrite prod_distr_fst, (lossless_random _ _ _ m2), Umult_one_left, Uabs_diff_compat_eq.
        rewrite prod_distr_snd, (lossless_random _ _ _ m1), Umult_one_left, Uabs_diff_compat_eq.
        auto.
        intros f Hf; simpl.
        rewrite (deno_random_elim _ _ _ m1), (mu_stable_eq _ _ (fun v1 =>
          mu (sum_support (SwitchingSem.Sem.T.default k t0) (E.eval_support s0 m2))
          (fun v2 => f (m1 {!v0 <-- v1!}, m2 {!v0 <-- v2!}))));  [ | 
            refine (ford_eq_intro _); intro v1; apply (deno_random_elim E2 v0 s0 m2) ].
        change (0 == sum_dom (T.default k t0) (E.eval_support s0 m1)
          (fun v1 => sum_dom  (T.default k t0) (E.eval_support s0 m2)
            (fun v2 => f (m1 {!v0 <-- v1!}, m2 {!v0 <-- v2!})))).
        
        symmetry; apply sum_dom_zero with (fun _ => True); [ trivial | ].
        intros v1 _; apply sum_dom_zero with (fun v2 => True); [ trivial | ].
        intros v2 _; symmetry; apply Hf.
        apply HPQ with m1 m2; split; [ exact Hm | simpl ].
     *) 









SearchAbout check_bad.
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

 Variable ep1 ep2: U.
 Variable Hd : elift P d  d1 d2 ep1.
 Variable Hd': elift Q d' d2 d3 ep2.

 Definition dfst (b : B) : distr (B*C) := distr_mult (fun q => carB b (fst q)) d'.
 
 Definition dsnd (b : B) : distr (A*B) := distr_mult (fun q => carB b (snd q)) d.

 Lemma dfst_simpl : forall b f, 
  mu (dfst b) f = mu d' (fun q => carB b (fst q) * f q).
 Proof. 
  trivial.
 Qed.

 Lemma dsnd_simpl : forall b f, 
  mu (dsnd b) f = mu d (fun q => carB b (snd q) * f q).
 Proof. 
  trivial.
 Qed.


 Lemma dfst_le : forall b, mu (dfst b) (fone (B * C)) <= ep2 +  mu d2 (carB b).
 Proof.
  intro; rewrite dfst_simpl.
  apply Ole_trans with (mu d' (fun q => carB b (fst q)));  [auto | ].
  apply Uplus_le_minus.
  rewrite <-(Hd'.(el_dist) (carB b) (fzero _)), mu_zero, mu_zero,
    Uabs_diff_compat_eq, Uplus_zero_right.
  apply Ule_plus_right.
 Qed.




 Lemma dsnd_le : forall b, mu (dsnd b) (fone (A * B)) <= mu d2 (carB b).
 Proof.
  intro; rewrite dsnd_simpl.
  apply Ole_trans with (mu d (fun q => carB b (snd q))); [auto | ].
  rewrite Hd.(el_snd); trivial.
 Qed.

 Hint Resolve dfst_le dsnd_le.
*)

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
  subst b0; red; apply P_Q_R with b; trivial.
 Qed.

 






(*
 Lemma dist_prg_upto:  forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) (ep:nat -o> U) 
   (bad: Var.var T.Bool) (pi : upto_info bad E1 E2),
   Var.is_global bad ->
   check_bad pi c1 c2 ->
   lossless E2 c2 ->
   (forall k (m m':Mem.t k), P _ m' m -> Pr E2 c2 m (EP k bad) <= ep k) ->
   dist_prg (Meq /-\ P) E1 c1 E2 c2 Meq (fplus (fplus (fzero _) ep) (fzero _)).
 Proof.
  intros.
  eapply dist_prg_failure_event with bad.
    admit.
    unfold dist_prg.
    intros.
    exists (fun m1 m2 => Mlet ([[c1]] E1 m1) (fun m1' => Mlet ([[c2]] E2 m2) 
      (fun m2' => if m2 bad then Munit (m1',m2') else distr0 _))).
    intros.
    constructor.
      intros.
      repeat rewrite Mlet_simpl.
      rewrite 
    Focus 3.
  upto_bad_GSD
*)


(*
Definition iffR (A B: Type) (R1 R2: A -> B -> Prop) :=
   forall a b, R1 a b <-> R2 a b.

 Lemma iffR_refl: forall  (A B: Type),
   reflexive _ (@iffR A B).
 Proof.  split; intros; auto. Qed.

 Lemma iffR_sym: forall  (A B: Type),
   symmetric _ (@iffR A B).
 Proof. 
   intros A B R1 R2 H a b; split.
     apply (proj2 (H a b)).
     apply (proj1 (H a b)).
 Qed.


 Add Parametric Relation (A B:Type) : (A->B->Prop) (@iffR A B) 
  reflexivity proved by (@iffR_refl A B) 
  symmetry proved by (@iffR_sym A B)
  as iffR_rel.
*)
