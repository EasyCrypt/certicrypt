(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

Require Import Semantics.

Set Implicit Arguments.

Local Close Scope bool_scope.

(** TODO: suggest to add to ALEA *)
Lemma fplus_fzero_r: forall (A:Type) (f:A -o> U), fplus f (fzero _) == f.
Proof. 
 intros; unfold fplus; refine (ford_eq_intro _); trivial.
Qed.

Lemma fplus_fzero_l: forall (A:Type) (f:A -o> U), fplus (fzero _) f == f.
Proof. 
 intros; unfold fplus; refine (ford_eq_intro _); trivial.
Qed.

(** TODO: Move somewhere else *)
Section AUX.
 
 Variable A B : Type.
 Variable f : A -> B.
 Variable finv : B -> list A.
 Variable size : nat.
 
 Hypothesis finv_nodup : forall b, NoDup (finv b).
 
 Hypothesis f_spec : forall a b, In a (finv b) <-> f a = b.
 
 Hypothesis size_finv : forall x, length (finv x) <= size.
 
 Lemma permutation_cons_inv : forall a (l:list A),
  In a l -> exists l1, Permutation (a :: l1) l.
 Proof.
  induction l; intros.
  elim H.
  simpl in H; destruct H.
  subst; exists l; apply Permutation_refl.
  destruct (IHl H) as [l2 H0].
  exists (a0 :: l2).
  apply Permutation_trans with (a0 :: a :: l2).
  constructor.  
  constructor; trivial.
 Qed.

 Lemma incl_permutation: forall (l1 l2 : list A),
  NoDup l1 -> incl l1 l2 -> exists l3, Permutation l2 (l1 ++ l3).
 Proof.
  induction l1.
  intro l2; exists l2; apply Permutation_refl.
  intros l2 H H0.
  destruct (permutation_cons_inv a l2) as [l3 H1].
  intuition.
  destruct (IHl1 l3) as [l4 H2].
  inversion H; trivial.
  intros b Hb.
  assert (In b (a :: l3)).
  apply Permutation_sym in H1.
  apply (Permutation_in _ H1); intuition.
  simpl in H2; destruct H2; [ | trivial].
  subst; inversion_clear H; intuition.
  exists l4; simpl.
  apply Permutation_trans with (a :: l3).
  apply Permutation_sym; trivial.
  constructor; trivial.
 Qed.

 Lemma length_surj : forall (l1 l2:list A),
  NoDup l1 -> 
  incl l1 l2 ->
  length l1 <= length l2.
 Proof.
  intros.
  destruct (incl_permutation H H0).
  rewrite (Permutation_length H1).
  rewrite app_length; omega.
 Qed.

 Lemma fold_right_incl_eq : forall (la:list A) (lb:list B),
  NoDup la -> 
  NoDup lb -> 
  (forall a, In a la) ->
  (forall b, In b lb) ->
  length la = fold_right (fun b r => length (finv b) + r) 0 lb.
 Proof.
  intros la lb Hincl_b Hincl_a Hla_full Hlb_full.
  transitivity (length (flat_map finv lb)).
  2: clear; induction lb; simpl; auto.
  2: rewrite app_length; omega.
   
  apply le_antisym.
  apply length_surj; auto.
  red; intros.
  eapply in_flat_map.
  exists (f a); rewrite f_spec; auto.

  apply length_surj; auto.
  clear Hlb_full.
  induction lb; simpl.
  constructor.
  apply NoDup_app; auto.
 
  apply IHlb.
  inversion Hincl_a; auto.
  intros x H H0.  
  rewrite f_spec in H0.
  subst.
  apply List.in_flat_map in H.
  destruct H as [x2 [H1 H2] ].
  apply f_spec in H2.
  subst.
  inversion Hincl_a.
  subst.
  apply H2; trivial.
  red; auto.
 Qed.

End AUX.

Lemma finite_sum_In2 : forall (A:Type) (f:A -> U) l (v:U),
 (forall x, In x l -> f x == v) ->
 finite_sum f l == (length l) */ v.
Proof.
 induction l; simpl; trivial; intros.
 rewrite IHl; auto.
 rewrite H; auto.
 destruct (length l); auto.
Qed.

Lemma finite_sum_full2 : forall (A:Type) (v:A) (f:A -> U) l,
 (forall x, x <> v -> In x l -> f x == 0) ->
 In v l -> 
 NoDup l -> 
 finite_sum f l == f v.
Proof.
 induction l; simpl; intros; auto.
 elim H0.
 destruct H0; subst.
 rewrite finite_sum_notIn2; auto.
 intros; apply H; auto.
 inversion H1; subst.
 intro Heq; elim H4; subst; auto.
 rewrite H, IHl; auto.
 inversion H1; auto.
 inversion H1; subst.
 intro Heq; elim H4; subst; auto.
Qed.
(***)
 

Module Type POLYNOMIALLY_INVERTIBLE_ENCODING 
 (A:FINITE_TYPE) (B:FINITE_TYPE) (ENC:ENCODING A B).
 
 Export ENC.

 Parameter finv_NoDup : forall k (x:B.t k), NoDup (finv_def x).

 Parameter finv_spec : forall k (y:B.t k) x, 
  In x (finv_def y) <-> f_def x = y.

 Parameter finv_len_group : forall k, 
  length (A.elems k) <= length (B.elems k) * finv_len.
  
End POLYNOMIALLY_INVERTIBLE_ENCODING.


Module Type WEAK_ENCODING (A:FINITE_TYPE) (R:FINITE_TYPE) (P:FINITE_TYPE)
 (PAD:PADDING_ALGEBRA P R) (ENC:ENCODING A R).

 Module Sem := SEM_PADDING A R P PAD ENC.
 Export Sem.

 (** TODO: Move somewhere else *)
 Definition distr_cond (A:Type) (d:Distr A) (P:A -o> boolO) : Distr A :=
  distr_div (mu d (charfun P)) (drestr d P) (Oeq_le (mu_drestr _ _ _)).

 Notation r := (Var.Lvar (T.User R_) 1).
 Notation Invf := (Proc.mkP 1 (T.User R_ :: nil) (T.Option (T.User A_))).

 Parameter Invf_body : cmd.
 Parameter Invf_re   : E.expr (T.Option (T.User A_)).
 Parameter Invf_X    : Vset.t.

 Parameter alpha     : nat -> nat * nat. (* rational *)
 Parameter epsilon   : nat -> U.

 Definition one_over_alpha k := snd (alpha k) */ [1/]1+pred(fst (alpha k)).

 Definition Invf_args : var_decl (Proc.targs Invf) := dcons _ r (dnil _).

 Parameter Invf_args_local : dforallb Var.vis_local Invf_args.

 Parameter Invf_slossless : forall E, slossless_c E Invf_body.
 
 Parameter Invf_Modify : forall E, Modify E Invf_X Invf_body.

 Parameter Invf_ret_expr : fv_expr Invf_re [<=] Invf_X.

 Parameter Invf_X_local : forall x : VarP.Edec.t, 
  Vset.mem x Invf_X -> Var.is_local x.

 Parameter Invf_eqobs : forall E1 E2,
  EqObs {{r}} E1 Invf_body E2 Invf_body Invf_X.
 
 Parameter Invf_PPT : forall E, PPT_cmd E tsize_limit Invf_body.

 Section PROPERTIES.

  Variable E0 : env.
 
  Definition E' := add_decl E0 Invf Invf_args Invf_args_local Invf_body Invf_re.

  Notation a  := (Var.Lvar (T.Option (T.User A_)) 2).
  Notation a' := (Var.Lvar (T.User A_) 3).
  Notation x  := (Var.Lvar (T.User R_) 4).

  Parameter Invf_partial_inverter: forall k (m:Mem.t k),
   range (EP k ((IsSome a) ==> (x =?= f_ (Proj a)))) 
    ([[ [x <$- R; a <c- Invf with {x} ] ]] E' m).

  Parameter Invf_success_probability: forall k (m:Mem.t k),
   (one_over_alpha k <= 
    Pr E' [ x <$- R; a <c- Invf with {x} ] m (EP k (IsSome a)))%tord.

  Parameter Invf_distance_from_random: forall k (f g:Mem.t k -o> U),
   (forall m1 m2 : Mem.t k, kreq_mem {{a'}} m1 m2 -> f m1 == g m2) ->
   forall m1 m2,
    (Uabs_diff
     (mu (distr_cond ([[ [x <$- R; a <c- Invf with {x}; a' <- Proj a] ]] E' m1) 
      (EP k (IsSome a))) f)
     (mu ([[ [a' <$- A] ]] E' m2) g) <= epsilon k)%tord.

 End PROPERTIES.

End WEAK_ENCODING.


Module WE_FROM_PI (A:FINITE_TYPE) (R:FINITE_TYPE) (P:FINITE_TYPE)
 (PAD:PADDING_ALGEBRA P R) (ENC:ENCODING A R)
 (PI:POLYNOMIALLY_INVERTIBLE_ENCODING A R ENC) : WEAK_ENCODING A R P PAD ENC.
 
 Module Sem := SEM_PADDING A R P PAD ENC.
 Export Sem.

 (** TODO: Move somewhere else *)
 Definition distr_cond (A:Type) (d:Distr A) (P:A -o> boolO) : Distr A :=
  distr_div (mu d (charfun P)) (drestr d P) (Oeq_le (mu_drestr _ _ _)).

 Export PI.

 Notation r  := (Var.Lvar (T.User R_) 1).
 Notation n  := (Var.Lvar T.Nat 10).
 Notation n' := (Var.Lvar T.Nat 11).
 Notation r' := (Var.Lvar (T.Option (T.User A_)) 13).
 Notation l  := (Var.Lvar (T.List (T.User A_)) 14).

 Notation Invf := (Proc.mkP 1 (T.User R_ :: nil) (T.Option (T.User A_))).

 Definition Invf_body :=
  [ 
   n' <$- [0..N-!1];
   l <- finv_ r;
   n <$- [0..(Elen l -! 1)];
   If n' <! (N -! Elen l) then
    [ r' <- none _ ]
   else 
    [ r' <- some (Enth {n, l}) ]
  ].

 Definition Invf_re : E.expr _ := r'.

 Definition Invf_X := {{r', n, l, n'}}.

 Definition alpha k := (length (R.elems k) * finv_len, length (A.elems k)).

 Definition epsilon := fzero nat.

 Definition one_over_alpha k := snd (alpha k) */ [1/]1+pred (fst (alpha k)).

 Definition Invf_args : var_decl (Proc.targs Invf) := dcons _ r (dnil _).

 Lemma Invf_args_local : dforallb Var.vis_local Invf_args.
 Proof.
  trivial.
 Qed.

 (** TODO: Move somewhere else *)
 Ltac slossless_tac := 
  repeat apply slossless_cons; 
   (apply slossless_assign; apply lossless_assign) ||
   (apply slossless_random; apply lossless_random) || 
   (apply slossless_nil; apply lossless_nil) || 
   (apply slossless_cond; slossless_tac) ||
   (apply slossless_while; [ | slossless_tac ]) ||
    apply slossless_call_adv || idtac.

 Lemma Invf_slossless : forall E, slossless_c E Invf_body.
 Proof.
  intro; slossless_tac.
 Qed.

 Lemma Invf_Modify : forall E, Modify E Invf_X Invf_body.
 Proof.
  intro E; apply modify_correct with (refl1_info (empty_info E E)) Vset.empty.
  vm_compute; trivial.
 Qed.

 Lemma Invf_ret_expr : fv_expr Invf_re [<=] Invf_X.
 Proof.
  vm_compute; trivial.
 Qed.

 Ltac Vset_mem_inv H :=
  match type of H with
  | is_true (Vset.mem _ Vset.empty) =>
      discriminate H
  | is_true (Vset.mem ?x (Vset.singleton ?y)) =>
      change (is_true (Vset.mem x {{y}})) in H; Vset_mem_inversion H
  | is_true (Vset.mem ?x (Vset.add ?y ?X)) =>
      let H0 := fresh "H" in
      let H1 := fresh "H" in
      let Heq := fresh "Heq" in
      generalize (Var.eqb_spec y x); case_eq (Var.eqb y x); intros H0 H1;
       [ injection H1; clear H1; intros H1
       | pose proof (Vset.add_inversion _ H1 H) as Heq;
         Vset_mem_inv Heq ]; subst; clear H0 H
  end.

 Lemma Invf_X_local  : forall x : VarP.Edec.t, 
  Vset.mem x Invf_X -> Var.is_local x.
 Proof.
  unfold Invf_X; intros.
  Vset_mem_inv H; trivial.
 Qed.

 Lemma Invf_eqobs : forall E1 E2,
  EqObs {{r}} E1 Invf_body E2 Invf_body Invf_X.
 Proof. 
  intros; eqobs_in.
 Qed.
 
 Lemma Invf_PPT : forall E, PPT_cmd E tsize_limit Invf_body.
 Proof.
  intro E; PPT_tac (PPT_empty_info E).
 Qed.


 Section PROPERTIES.

  Variable E0 : env.
 
  Definition E' := add_decl E0 Invf Invf_args Invf_args_local Invf_body Invf_re.

  Notation a  := (Var.Lvar (T.Option (T.User A_)) 2).
  Notation a' := (Var.Lvar (T.User A_) 3).
  Notation x  := (Var.Lvar (T.User R_) 4).

  Definition i_EE :=
   let i_empty := empty_info E' E' in
   let i_Invf  := add_refl_info_rm Invf Vset.empty Vset.empty i_empty in i_Invf.

  Lemma Invf_partial_inverter: forall k (m:Mem.t k),
   range (EP k ((IsSome a) ==> (x =?= f_ (Proj a)))) 
    ([[ [x <$- R; a <c- Invf with {x} ] ]] E' m).
  Proof.
   intros; apply mu_range.
   assert (Hloss :  lossless E' [x <$- R; a <c- Invf with {x} ] ).
   apply is_lossless_correct with (refl1_info i_EE).
   vm_compute; trivial.
   rewrite <- (@Hloss _ m).
   apply equiv_deno with (kreq_mem Vset.empty) (req_mem_rel Vset.empty
    ((EP1 ((IsSome a) ==> 
     (x =?= f_ (Proj a)))) /-\ (EP2 ((IsSome a) ==> (x =?= f_ (Proj a)))))).   
   sinline i_EE Invf.
   eqobsrel_tail; simpl; unfold O.eval_op; simpl.
   red; intros.

   split.
   intros; auto.
   intros [H3 _].
   generalize (finv_spec v (nth v1 (finv_def v) (A.default k0))); intros.
   destruct H4; rewrite H4.
   rewrite R.eqb_refl; auto.
   destruct (finv_def v).
   simpl in *; destruct H2; auto.
   subst; elim H3.
   destruct H1.
   subst.
   generalize (finv_len_not_0).
   destruct finv_len; intros.
   exfalso; omega.
   apply leb_correct; auto.
   apply In_seq_le in H1; apply leb_correct; omega.

   apply nth_In; simpl.
   destruct H2.
   subst; omega.
   apply In_seq_le in H2; simpl in H2; omega.
 
   intros m1 m2 Hm.
   generalize Hm; unfold EP1, EP2, EP; simpl; unfold O.eval_op; simpl.
   red; intros; unfold req_mem_rel, andR in Hm0.
   destruct Hm0 as [ H1 [ H2 H3 ] ].
   rewrite H2; trivial; auto.
   auto.
  Qed.

  Lemma Invf_success_probability_eq : forall k (m:Mem.t k),
   Pr E' [ x <$- R; a <c- Invf with {x} ] m (EP k (IsSome a)) ==
   one_over_alpha k.
  Proof.
   symmetry; intros.
   transitivity (mu ([[ 
   [
     x <$- R;
     n' <$- [0..N -! 1];
     If n' <! (N -! Elen (finv_ x)) then 
      [ a <- none _ ]
     else 
      [ 
       n <$- [0..Elen (finv_ x) -! 1]; 
       a <- some Enth {n, finv_ x} 
      ]
   ] ]] E' m) (charfun (EP k (IsSome a)))).
   
   rewrite deno_cons_elim, Mlet_simpl.
   transitivity 
    (mu ([[ [x <$- R] ]] E' m)
     (fun m' => length (finv_def (m' x)) */ [1/]1+pred finv_len)).

   rewrite deno_random_elim, (sum_dom_finite (R.default k) (R.elems k)).

   transitivity (finite_sum (fun a => 
    (length (finv_def a) */ 
     [1/]1+pred(length (R.elems k) * finv_len))) (R.elems k)).
   rewrite finite_sum_mult.
   unfold one_over_alpha, alpha; simpl.
   apply Nmult_eq_compat_right.

   erewrite (fold_right_incl_eq (@f_def k) (@finv_def k)); trivial.
   apply finv_NoDup.
   intros; apply finv_spec.
   apply A.elems_NoDup.
   apply R.elems_NoDup.
   apply A.elems_full.
   apply R.elems_full.
   trivial.

   apply finite_sum_eq; intros.
   mem_upd_simpl.
   rewrite <- Nmult_Umult_assoc_right.

   apply Nmult_eq_compat_left; trivial.
   rewrite Unth_prod.
   generalize finv_len_not_0; destruct finv_len; intros.
   exfalso; omega.
   generalize (@R.elems_notnil k); destruct (R.elems k); intro.
   elim H1; trivial.
   split; apply Unth_anti_mon; simpl; omega.
   unfold Nmult_def.
   generalize (finv_len_spec x).
   destruct (finv_def x); simpl; intros; auto.
   apply Unth_anti_mon; simpl; omega.

   apply mu_stable_eq.
   refine (ford_eq_intro _); intro m'.
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   simpl T.default; simpl E.eval_support; unfold O.eval_op; simpl T.app_op.

   assert (H:0%nat :: seq 1 (finv_len - 1) = seq 0 finv_len).
   generalize finv_len_not_0; intros; destruct finv_len.
   exfalso; omega. 
   simpl; rewrite <- minus_n_O; trivial.

   rewrite H; clear H.
   transitivity (mu (sum_support 0%nat (seq 0 finv_len)) (fun x' => 
    if leb (x' + 1) (finv_len - length (finv_def (m' x))) then 0%tord else 1%U)).
   Opaque sum_dom.
   simpl; unfold O.eval_op; simpl.
   rewrite (sum_dom_finite 0%nat (seq 0%nat finv_len)).
   generalize (finv_len_spec (m' x)); intros.

   assert (finv_len = (finv_len - (length (finv_def (m' x))) +
    (length (finv_def (m' x))))%nat) by omega.

   rewrite H0 at 2.
   rewrite seq_append.
   rewrite finite_sum_app.
   match goal with |- (_ == (?a + ?b))%U%tord => assert (a == 0)%tord end.
   apply finite_sum_notIn2.
   intros.
   apply In_seq_le in H1.
   rewrite leb_correct.
   Usimpl; trivial.
   omega.

   rewrite H1; clear H1; Usimpl.
   rewrite finite_sum_In2, seq_length; auto.
   intros x H1; apply In_seq_le in H1.
   rewrite leb_correct_conv; [ | omega ].
   rewrite seq_length; auto.

   apply mu_stable_eq.
   refine (ford_eq_intro _); intro ms.
   rewrite deno_cond_elim.
   simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
   mem_upd_simpl.
   case_eq (leb (ms + 1) (finv_len - length (finv_def (m' x)))); intros; auto.
   rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim, deno_nil_elim.
   simpl; unfold charfun, EP, restr; simpl; mem_upd_simpl.
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   simpl T.default; simpl E.eval_support; unfold O.eval_op; simpl T.app_op.

   transitivity (mu (sum_support 0%nat
    (0%nat :: seq 1 (length (finv_def ((m' {!n' <-- ms!}) x)) - 1)))
    (fun v => 1%U)).
   rewrite BaseDef.sum_support_lossless; auto.
   intro; discriminate.
   apply mu_stable_eq.
   refine (ford_eq_intro _); intro.
   rewrite deno_assign_elim.
   unfold charfun, restr, EP.
   simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
   mem_upd_simpl.

   apply equiv_deno with (kreq_mem Vset.empty) (kreq_mem {{a}}); auto.
   inline_r i_EE Invf.
   eqobs_hd; ep; deadcode.
   eqobs_hd.
   cp_test (n' <! (N -! Elen (finv_ x))).
   deadcode; eqobs_in.
   deadcode; eqobs_in.
   intros; unfold charfun, restr, EP.
   simpl; unfold O.eval_op; simpl.
   rewrite (H _ a); auto.
  Qed.

  Lemma Invf_success_probability : forall k (m:Mem.t k),
   (one_over_alpha k <= 
   Pr E' [ x <$- R; a <c- Invf with {x} ] m (EP k (IsSome a)))%tord.
  Proof.
   intros; apply Oeq_le; symmetry; apply Invf_success_probability_eq.
  Qed.
 
  Lemma Invf_distance_from_random: forall k (f g:Mem.t k -o> U),
   (forall m1 m2, kreq_mem {{a'}} m1 m2 -> f m1 == g m2) ->
   forall m1 m2,
    (Uabs_diff 
     (mu (distr_cond ([[ [x <$- R; a <c- Invf with {x}; a' <- Proj a] ]] E' m1) 
      (EP k (IsSome a))) f)
     (mu ([[ [a' <$- A] ]] E' m2) g) <= epsilon k)%tord.
  Proof.
   Opaque deno.
   intros; unfold distr_cond; simpl.
  
   assert (mu ([[ [x <$- R; a <c- Invf with {x}; a' <- Proj a] ]] E' m1)  
    (charfun (EP k (IsSome a))) == one_over_alpha k).
   transitivity (mu ([[ [x <$- R; a <c- Invf with {x} ] ]] E' m1) 
    (charfun (EP k (IsSome a)))).
   apply EqObs_deno with Vset.empty {{a}}.
   deadcode i_EE.
   eqobs_in i_EE.
   intros; unfold charfun, restr, EP; simpl; unfold O.eval_op; simpl.
   rewrite (H0 _ a); auto.
   auto.
   apply Invf_success_probability_eq.
   
   Close Scope nat_scope.

   assert (mu ([[ [x <$- R; a <c- Invf with {x}; a' <- Proj a] ]] E' m1)
    (fun x : Mem.t k =>
     (mu (if EP k (IsSome a) x then Munit x else distr0 _)) f) == 
   (finite_sum 
    (fun s' => f (m1{!a' <-- s'!}) * [1/]1+pred (finv_len * (length (R.elems k))))
    (A.elems k))).
   transitivity ((mu (([[ [
    x <$- R;
    n' <$- [0..N -! 1];
    n <$- [0..Elen (finv_ x) -! 1];
    If (n') <! (N -! Elen (finv_ x))
    then [a <- none _]
    else [a <- some Enth {n, finv_ x } ]; a' <- Proj a ] ]]) E' m1)) 
   (fun x : Mem.t k => (mu (if EP k (IsSome a) x then Munit x else distr0 (Mem.t k))) g)).
   apply equiv_deno with (kreq_mem Vset.empty)  (kreq_mem {{ a, a' }} ); auto.
   sinline i_EE Invf.
   eqobs_hd.
   cp_test (n' <! (N -! Elen (finv_ x))).
   deadcode; eqobs_in.
   deadcode; eqobs_in.
   intros; unfold charfun, restr, EP; simpl; unfold O.eval_op; simpl.
   rewrite (H1 _ a); auto.
   case (m3 a); simpl; intros; auto.
   apply H. 
   unfold kreq_mem in *.
   eapply req_mem_weaken; eauto; auto with set.
   
   transitivity (mu 
    ([[ [x <$- R; n' <$- [0..N -! 1]; n <$- [0..Elen (finv_ x) -! 1] ] ]] E' m1)
    (fun m' => 
     charfun (EP k (!(n' <! (N -! Elen finv_ x)))) m' * 
     f (m1{!a' <-- E.eval_expr (Enth {n,finv_ x}) m'!}))).
   rewrite <- (firstn_skipn 3%nat _); unfold firstn, skipn.
   rewrite deno_app_elim.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
   rewrite deno_cons_elim, Mlet_simpl, deno_cond_elim.
   unfold charfun, restr, EP.
   simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   case (leb (m' n' + 1) (finv_len - length (finv_def (m' x)))); 
    intros; simpl; try Usimpl.
   
   rewrite (deno_assign_elim E' a _ m').
   rewrite (deno_assign_elim E' a' _ (m'{!a <-- _!})).
   mem_upd_simpl.

   rewrite (deno_assign_elim E' a _ m').
   rewrite (deno_assign_elim E' a' _ (m'{!a <-- _!})).
   mem_upd_simpl.
   unfold charfun, restr, EP, fone.
   simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   Usimpl.
   symmetry.
   apply H.
   unfold kreq_mem in *.
   apply req_mem_update;apply req_mem_empty.

   set (F m' := (fun s' => 
    (charfun (EP k (n' <! N)) m') * (
     (charfun (EP k (!(n' <! (N-! Elen finv_ x)))) m'* f (m1{!a' <-- s'!}) * 
      charfun (T.i_eqb k (T.User A_) s') (E.eval_expr (Enth {n,finv_ x}) m'))))).
   transitivity (mu 
    ([[ [x <$- R; n' <$- [0..N-! 1]; n <$- [0..Elen (finv_ x) -! 1] ] ]] E' m1)
    (fun m' => finite_sum (F m') (A.elems k))).
   rewrite (mu_range_restr (EP k (n' <! N))).
   apply mu_stable_eq;refine (ford_eq_intro _);intros m'.
   rewrite (@finite_sum_full _ (E.eval_expr (Enth {n, finv_ x}) m') (F m')).
   unfold F; unfold charfun at 4; unfold restr, fone.
   rewrite Ti_eqb_refl; auto.
   unfold charfun, restr.
   case (EP k (n' <! N) m'); Usimpl; auto.

   intros v Hdiff.
   unfold F; unfold charfun at 3; unfold restr, fone.
   generalize (T.i_eqb_spec k (T.User A_) v (E.eval_expr (Enth {n, finv_ x}) m')).
   destruct (T.i_eqb k (T.User A_) v (E.eval_expr (Enth {n, finv_ x}) m'));intros.
   elim (Hdiff H1).
   repeat Usimpl; auto.
   apply (@A.elems_full k).
   apply (A.elems_NoDup k).
   rewrite deno_cons.
   apply range_Mlet with (fun _ => True).
   apply range_True.
   intros m' _.
   rewrite deno_cons.
   apply range_Mlet with (fun m' => EP k (n' <! N) m' = true).
   unfold range; intros.
   rewrite deno_random_elim.
   simpl.
   rewrite (sum_dom_finite 0%nat).
   simpl; unfold O.eval_op; simpl.
   rewrite <- H1.
   rewrite finite_sum_notIn2.
   Usimpl; auto.
   intros.
   rewrite <- H1.
   Usimpl; auto.
   unfold EP; simpl; unfold O.eval_op; simpl.
   apply leb_correct.
   mem_upd_simpl; simpl.
   apply In_seq_le in H2; omega.
   unfold EP; simpl; unfold O.eval_op; simpl.
   apply leb_correct.
   mem_upd_simpl; simpl.
   apply finv_len_not_0.
   intros m''.
   unfold range; intros.
   rewrite deno_random_elim.
   transitivity ((mu
    (sum_support (T.default k Msg)
     (E.eval_support [0..Elen (finv_ x) -! 1] m''))) (fcte _ 0)).
   rewrite mu_cte.
   Usimpl; auto.
   apply mu_stable_eq;refine (ford_eq_intro _); intros m'''.
   apply H2.
   revert H1.
   unfold EP; simpl; unfold O.eval_op; simpl.  
   mem_upd_simpl.
   
   transitivity 
    (finite_sum (fun s' => mu
     (([[ [x <$- R; n' <$- [0..N-! 1]; n <$- [0..Elen (finv_ x) -! 1] ] ]]) E' m1)
     (fun m' => F m' s')) (A.elems k)).
   rewrite <- (@sigma_finite_sum _ (A.default k)).
   rewrite <- mu_sigma_eq.
   apply mu_stable_eq;refine (ford_eq_intro _);intros m'.
   unfold sigma_fun.
   rewrite sigma_finite_sum.
   trivial.
   intros m.
   unfold retract.
   intros.
   unfold F.
   Opaque T.i_eqb sigma.
   unfold charfun, restr, fone, EP; simpl; unfold O.eval_op; simpl.
   generalize (T.i_eqb_spec k (T.User A_) (nth k0 (A.elems k) (A.default k))
    (nth (m n) (finv_def (m x)) (A.default k))).  
   case(T.i_eqb k (T.User A_) (nth k0 (A.elems k) (A.default k))
    (nth (m n) (finv_def (m x)) (A.default k))); intros.
   Usimpl.
   case_eq (leb (m n' + 1) finv_len); intros; Usimpl; auto.
   match goal with |- _ <= [1-] (?x ?x') => 
    assert (forall k, (k <= k0)%nat -> x k == 0)
   end.
   induction k1; intros.
   rewrite sigma_0; trivial.
   rewrite sigma_S, IHk1;[ Usimpl | omega ].
   generalize (T.i_eqb_spec k (T.User A_) (nth k1 (A.elems k) (A.default k))
    (nth (m n) (finv_def (m x)) (A.default k))).  
   case(T.i_eqb k (T.User A_) (nth k1 (A.elems k) (A.default k))
    (nth (m n) (finv_def (m x)) (A.default k))); intros.
   case_eq (length (finv_def (m x))); intros.
   rewrite <- minus_n_O.
   rewrite H3.
   simpl; repeat Usimpl; auto.
   
   assert (k1 = k0).
   rewrite <- H2 in H5.
   revert H5 H1 H4.
   clear.
   revert k0 k1.
   generalize (@A.elems_NoDup k).
   induction 1; intros; simpl in *.
   elimtype False; omega.
   destruct k1; destruct k0; trivial.
   elim H.
   subst; apply nth_In.
   omega.
   elim H.
   subst; apply nth_In.
   omega.
   rewrite (IHNoDup k0 k1); auto; omega.
   repeat Usimpl; trivial.
   elimtype False; omega.
   
   Usimpl; trivial.
   rewrite H4; auto; Usimpl; auto.
   repeat Usimpl; trivial.
   
   apply finite_sum_eq;intros s' Hin.
   unfold F.

   transitivity
    (f (m1 {!a' <-- s'!}) *
     (mu
      (([[[x <$- R; n' <$- [0..N-! 1]; n <$- [0..Elen (finv_ x) -! 1] ] ]]) E'
       m1))
     (fun m' : Mem.t k =>
      charfun (EP k (n' <! N)) m' * (
       charfun (EP k (!n' <! (N-! Elen (finv_ x)))) m' *
       charfun (T.i_eqb k (T.User A_) s')
       (E.eval_expr (Enth {n, finv_ x}) m')))).
   rewrite Umult_sym, <- mu_stable_mult_right.
   apply mu_stable_eq; refine (ford_eq_intro _); intro m'.

   repeat rewrite <- Umult_assoc.
   apply Umult_eq_compat; trivial.
   repeat rewrite Umult_assoc.
   rewrite Umult_sym, Umult_assoc; apply Umult_eq_compat; trivial.
   
   apply Umult_eq_compat; trivial.
   transitivity 
    (mu
     (sum_support (T.default k (T.User R_))
      (E.eval_support (E.Duser (UR T.User)) m1))
     (fun vx => 
      charfun (fun w => negb (nat_eqb 0%nat w)) (length (finv_def vx)) *
      charfun (T.i_eqb k (T.User R_) (f_def s')) vx * [1/]1+pred (length (finv_def vx)) *
      ([1-] ((finv_len - length (finv_def vx)) */ [1/]1+pred finv_len)))).

   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   apply mu_stable_eq;refine (ford_eq_intro _);intros vx.
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   unfold charfun, restr, EP, fone; simpl mu.
   simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
   rewrite (sum_dom_finite (T.default k Msg)).
   assert (forall x, 0 < x -> 0%nat :: seq 1 (x - 1) = seq 0 x)%nat.
   destruct x; intros.
   elimtype False; omega.
   simpl.
   rewrite <- minus_n_O; trivial.
   rewrite H1.
   generalize (finv_len_spec vx); intros.

   assert (finv_len = (finv_len - (length (finv_def vx)) +
    (length (finv_def vx)))%nat) by omega.
   rewrite H3 at 1.
   rewrite seq_append, finite_sum_app.

   match goal with [ |- (?a + ?b)%U  == _ ] => assert (a == 0) end.
   apply finite_sum_notIn2.
   intros.
   apply In_seq_le in H4.
   rewrite deno_random_elim.
   simpl mu.
   simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
   mem_upd_simpl.
   rewrite (sum_dom_finite 0%nat).
   rewrite finite_sum_notIn2.
   auto.
   intros.
   mem_upd_simpl.
   case_eq (leb (x + 1) (finv_len - length (finv_def vx))); intros; simpl.
   repeat Usimpl; auto.
   apply leb_complete_conv in H6.
   elimtype False; omega.
   rewrite H4; clear H4.
   
   Usimpl.

   transitivity (finite_sum
    (fun a : T.interp k Msg =>
     [1/]1+pred (length (seq 0 finv_len)) * [1/]1+pred(length (finv_def vx)) * 
     (charfun (T.i_eqb k (T.User R_) (f_def s')) vx))
    (seq (0 + (finv_len - length (finv_def vx))) (length (finv_def vx)))).
   apply finite_sum_eq; intros a Ha.
   rewrite <- Umult_assoc;apply Umult_eq_compat; trivial.
   rewrite deno_random_elim.
   unfold charfun, restr, EP, fone.

   case_eq (T.i_eqb k (T.User R_) (f_def s') vx); intros.
   Opaque E.eval_support.
   Opaque T.i_eqb.
   simpl; rewrite (sum_dom_finite (T.default k Msg)).
   generalize (T.i_eqb_spec k (T.User R_) (f_def s') vx).
   rewrite H4; intros.
   apply finv_spec in H5.
   destruct (In_nth_inv s' (A.default k) (finv_def vx) H5) as [n [ H6 H7 ] ].

   rewrite (@finite_sum_full2 _ n).
   mem_upd_simpl; Usimpl.
   rewrite leb_correct; simpl.
   Usimpl.
   rewrite leb_correct_conv; simpl.
   Usimpl.
   rewrite H7.
   rewrite Ti_eqb_refl.
   Transparent E.eval_support.
   simpl; unfold O.eval_op; simpl T.app_op.
   rewrite seq_length; auto.
   mem_upd_simpl; Usimpl.
   rewrite pred_of_minus; trivial.
   apply In_seq_le in Ha; omega.

   apply In_seq_le in Ha.
   omega.

   Opaque In.
   simpl; unfold O.eval_op; simpl T.app_op.
   mem_upd_simpl; intros.
   rewrite H1 in H9.
   apply In_seq_le in H9.
   mem_upd_simpl; simpl.
   generalize (T.i_eqb_spec k (T.User A_) s' (nth x (finv_def vx) (A.default k))).
   destruct (T.i_eqb k (T.User A_) s' (nth x (finv_def vx) (A.default k))); intros.
   elim H8.
   destruct H9.
   revert H7 H8 H6 H11.
   rewrite H10.
   clear.
   revert n x.
   generalize (finv_NoDup vx).
   induction 1; intros; simpl in *.
   elimtype False; omega.
   destruct x0; destruct n; trivial.
   elim H.
   subst; apply nth_In.
   omega.
   elim H.
   subst; apply nth_In.
   omega.
   rewrite (IHNoDup x0 n); auto; omega.
   repeat Usimpl; trivial.
   simpl in H6; omega.
   simpl.
   simpl; unfold O.eval_op; simpl T.app_op.
   rewrite H1.
   mem_upd_simpl; simpl.
   apply le_In_seq; simpl in *; omega.
   mem_upd_simpl; simpl in *; omega.
   simpl; unfold O.eval_op; simpl T.app_op.
   rewrite H1.
   apply NoDup_seq.
   mem_upd_simpl; simpl.
   simpl in H6; omega.

   simpl.
   rewrite (sum_dom_finite 0%nat).
   Usimpl.
   apply finite_sum_notIn2.
   simpl; unfold O.eval_op; simpl T.app_op.
   intros.
   mem_upd_simpl; simpl.
   generalize (T.i_eqb_spec k (T.User A_) s' (nth x (finv_def vx) (A.default k))).
   destruct (T.i_eqb k (T.User A_) s' (nth x (finv_def vx) (A.default k))); intros.
   destruct (zerop (length (finv_def vx))).
   rewrite e; simpl.
   replace (leb (a + 1) (finv_len - 0)) with true.
   simpl; repeat Usimpl; auto.
   symmetry.
   apply leb_correct.
   apply In_seq_le in Ha.
   omega.
   
   replace vx with (f_def s') in H4.
   rewrite Ti_eqb_refl in H4.
   discriminate.
   apply finv_spec; subst.
   apply nth_In.
   rewrite H1 in H5.
   apply In_seq_le in H5.
   generalize H5; mem_upd_simpl; simpl in *; intros; omega.
   mem_upd_simpl; simpl.
   repeat Usimpl; auto.

   rewrite finite_sum_In2 with (v :=  (([1/]1+pred (length (seq 0 finv_len)) *
    [1/]1+pred (length (finv_def vx)) *
    charfun (T.i_eqb k (T.User R_) (f_def s')) vx))).
   repeat rewrite seq_length.
   destruct (length (finv_def vx)).
   simpl; repeat Usimpl; auto.
   simpl nat_eqb; simpl negb.
   cbv iota.
   Usimpl.
   rewrite Nmult_Umult_assoc_left.
   rewrite Umult_sym.
   rewrite <- Umult_assoc.
   apply Umult_eq_compat.
   trivial.
   rewrite Nmult_Unth_simpl_right.
   rewrite Uinv_Nmult.
   replace (S (pred finv_len) - (finv_len - S n))%nat with (S n )%nat.
   rewrite Umult_sym.
   rewrite <- Nmult_Umult_assoc_left.
   rewrite Nmult_Unth_simpl_right; trivial.
   unfold Nmult_def.
   apply Unth_anti_mon.
   omega.
   omega.
   unfold Nmult_def.
   rewrite Unth_prod.
   apply Unth_anti_mon.
   simpl.
   auto with arith.
   intros.
   auto.
   apply finv_len_not_0.

   simpl.
   rewrite (sum_dom_finite (R.default k)).
   simpl in s'. 
   rewrite (@finite_sum_full _ (f_def s')).
   unfold charfun, restr, fone; rewrite Ti_eqb_refl; Usimpl.
   case_eq (finv_def (f_def s')); intros.
   assert (W := @finv_spec k (f_def s') s').
   rewrite H1 in W.
   destruct W.
   elim H3; trivial.
   simpl.
   repeat Usimpl.
   rewrite Uinv_Nmult.
   replace (S (pred finv_len) - (finv_len - S (length l)))%nat with (S (length l))%nat.
   setoid_replace ( ([1/]1+length l * (S (length l) */ [1/]1+pred finv_len)) ) with ([1/]1+pred (finv_len)).
   
   generalize (@finv_len_spec k).
   generalize (@R.elems_notnil k).
   destruct (R.elems k); simpl; intros.
   elim H2; trivial.
   generalize finv_len_not_0.
   destruct (finv_len); intros.
   elimtype False; omega.
   rewrite <- Unth_prod.
   auto.
   rewrite <- Nmult_Umult_assoc_right.
   rewrite Nmult_Unth_simpl_left; trivial.
   unfold Nmult_def.
   apply Unth_anti_mon.
   change (length l) with (pred (length (t :: l))).
   rewrite <- H1.
   apply le_pred.
   apply finv_len_spec.
   generalize finv_len_not_0.
   assert (S (length l) <= finv_len)%nat.
   change (S (length l)) with (length (t :: l)).
   rewrite <- H1.
   apply finv_len_spec.
   omega.
   
   intros x Hdiff.
   unfold charfun, restr, fone.
   generalize (T.i_eqb_spec k (T.User R_) (f_def s') x).
   destruct (T.i_eqb k (T.User R_) (f_def s') x).
   intros Heq; elim Hdiff;auto.
   repeat Usimpl;auto.
   apply R.elems_full.
   apply R.elems_NoDup.

   assert ((mu (([[ [a' <$-A] ]]) E' m2)) g == 
    finite_sum (fun s' => f (m1{!a' <-- s'!}) * [1/]1+pred(length (A.elems k))) 
    (A.elems k)).
   rewrite deno_random_elim.
   Opaque sum_dom.
   simpl;rewrite (sum_dom_finite (A.default k)).
   apply finite_sum_eq.
   intros;rewrite Umult_sym.
   apply Umult_eq_compat_left.
   symmetry;apply H.
   apply req_mem_update;apply req_mem_empty.
   
   rewrite H0, H1, H2.
   (* TODO: make a lemma for this *)
   assert (finite_sum
    (fun s' : T.interp k (Var.btype a') =>
     f (m1 {!a' <-- s'!}) * [1/]1+pred (finv_len * length (R.elems k))) (A.elems k) /
    one_over_alpha k == 
    (finite_sum (fun s' : T.interp k (Var.btype a') =>
     f (m1 {!a' <-- s'!}) * [1/]1+pred (finv_len * length (R.elems k)) / one_over_alpha k) (A.elems k))).
   clear.
   induction (A.elems k); simpl; trivial.
   rewrite <- IHl.
   rewrite Udiv_plus; trivial.

   rewrite H3;unfold epsilon.
   match goal with |- ?x <= _ => assert (W:x==0);[ | rewrite W;trivial]  end.
   rewrite Uabs_diff_zero.
   apply finite_sum_eq.
   intros.
   set (M:=(pred (length (A.elems k)))).
   assert (length (A.elems k) = S M).
   unfold M;destruct (A.elems k);[ elim H4 | trivial].
   rewrite mult_comm.
   rewrite Umult_div_assoc.
   apply Umult_eq_compat;trivial.
   unfold one_over_alpha, alpha;simpl.
   symmetry;apply Umult_div_eq.
   rewrite H5;apply Nmult_neq_zero;auto.
   rewrite Umult_sym, <- Nmult_Umult_assoc_left, H5.
   apply Nmult_Unth_simpl_right.
   rewrite H5;simpl;apply Unth_anti_mon.
   unfold M; apply le_pred.
   apply finv_len_group.
 
   unfold one_over_alpha, alpha; simpl.
   change 
    ([1/]1+pred (length (R.elems k) * finv_len)) with 
    (1 */ ([1/]1+pred (length (R.elems k) * finv_len))).
   apply Nmult_le_compat_left; omega.
  Qed.

 End PROPERTIES.
 
End WE_FROM_PI.


Module Indifferentiability (A:FINITE_TYPE) (R:FINITE_TYPE) (P:FINITE_TYPE)
 (PAD:PADDING_ALGEBRA P R) (ENC:ENCODING A R) (WE:WEAK_ENCODING A R P PAD ENC).

 Export WE.

 (** TODO: see if this generalization can replace the existing rule for 
    random assignments in BaseProp.v *)
 Lemma equiv_random_permut : forall (Q:mem_rel) E1 E2 t1 t2 
  (x1:Var.var t1) (x2:Var.var t2)
  (f:forall k, Mem.t k -> Mem.t k -> T.interp k t2 -> T.interp k t1) 
  (d1:E.support t1) (d2:E.support t2),
  equiv ((permut_support f d1 d2) /-\ 
   (fun k m1 m2 => forall v, 
    In v (E.eval_support d2 m2) -> 
    Q k (m1{!x1 <-- f k m1 m2 v!}) (m2{!x2 <-- v!})))
  E1 [x1 <$- d1] 
  E2 [x2 <$- d2] 
  Q.
 Proof.
  unfold equiv; intros.
  exists (fun m1 m2 =>
   Mlet ([[ [x2 <$- d2] ]] E2 m2)
   (fun m => Munit (m1{! x1 <-- f k m1 m2 (m x2) !}, m))); intros.
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
   ([1/]1+pred (length (E.eval_support d2 m2))) H0.
  induction l; simpl; intros; trivial.
  rewrite <- IHl; auto.
  rewrite <- H1; auto.
  red; simpl.
  rewrite Mem.get_upd_same; auto.
 Qed.

 (** TODO: Move somewhere else *)
 Lemma distr_cond_simpl: forall (A: Type) (d:Distr A) (P:A -o> boolO) f,
  mu (distr_cond d P) f == (mu d (restr P f)) / (mu d (charfun P)).
 Proof.
  intros; unfold distr_cond, distr_div.
  rewrite (Mdiv_simpl ((mu d) (charfun P)) (mu (drestr d P))).
  apply Udiv_eq_compat_left.
  apply mu_drestr.
 Qed.

 Lemma equiv_strengthen_range: forall E c P 
  (Q:mem_rel) (R:forall k, Mem.t k -o> boolO),
  decMR Q ->
  lossless E c ->
  (forall k (m:Mem.t k), range (@R k) ([[c]] E m))  ->
  equiv P E c E c Q ->
  equiv P E c E c (Q /-\ (fun k m1 _ => R _ m1)).
 Proof.
  unfold equiv; intros.
  destruct (H1 k) as [d Hd]; clear H1.
  exists d; intros; constructor.
  apply (l_fst (Hd m1 m2 H1)).
  apply (l_snd (Hd m1 m2 H1)).
  apply range_weaken with 
   (P1:= fun v => ((fun xy => if @X k (fst xy) (snd xy) then true else false) 
    [&&] (fun xy => R k (fst xy))) v = true).
  unfold prodP, andP; intros; rewrite andb_true_iff in H2; destruct H2.
  split. 
  destruct (X k (fst x) (snd x)); [ trivial | discriminate ].
  trivial.
  apply range_strengthen.
  transitivity (mu (d m1 m2) (fun xy => fone _ (fst xy)));
   [ trivial | rewrite (l_fst (Hd m1 m2 H1)); apply H ].
  apply range_weaken with (2:=l_range (Hd m1 m2 H1)).
  intros (m1',m2'); unfold prodP, fst, snd.
  destruct (X k m1' m2'); [ trivial | intro; tauto ].
  apply mu_range.
  rewrite (l_fst (Hd m1 m2 H1) (fun m => if R k m then 1%U else D0)).
  rewrite (range_mu _ (H0 _ m1) ); apply H.
 Qed.

 Lemma equiv_inv_Modify : forall (inv:mem_rel) (X1 X2 M1 M2:Vset.t) 
  (P:mem_rel) (E1:env) (c1:cmd) (E2:env) (c2:cmd) (Q:mem_rel) ,
  depend_only_rel inv X1 X2 ->
  Modify E1 M1 c1 ->
  Modify E2 M2 c2 ->
  (forall k (m1 m2 m1' m2':Mem.t k),
    P k m1 m2 -> Q k m1' m2' -> Q k (m1 {!M1 <<- m1'!}) (m2 {!M2 <<- m2'!})) ->  
  Vset.disjoint X1 M1 -> 
  Vset.disjoint X2 M2 -> 
  equiv P E1 c1 E2 c2 (Q /-\ trueR) ->
  equiv (P /-\ inv) E1 c1 E2 c2 (Q /-\ inv).
 Proof. 
  intros; intros k.
  destruct (H5 k) as [d Hd].
  exists (fun m1 m2 => 
   Mlet (d m1 m2) (fun mm => Munit (m1{! M1 <<- fst mm !},m2{! M2 <<- snd mm!}))).
  intros.
  destruct H6 as [Hreq Hinv].
  destruct (Hd m1 m2 Hreq); clear Hd.
  constructor; intros.

  rewrite (Modify_deno_elim H0).
  apply (l_fst (fun m' => f (m1 {!M1 <<- m'!}))). 

  rewrite (Modify_deno_elim H1).
  apply (l_snd (fun m' => f (m2 {!M2 <<- m'!}))). 

  apply (range_Mlet _ l_range).
  unfold prodP, andR; intros (m1',m2') (H6,_) f Hf';  simpl; unfold fst, snd in *.
  apply Hf'; simpl; split.
  auto.
    
  apply H with (3:=Hinv).
  apply req_mem_sym; apply req_mem_update_disjoint; trivial.
  apply req_mem_sym; apply req_mem_update_disjoint; trivial.
 Qed.

 Ltac slossless_tac := 
  repeat apply slossless_cons; 
   (apply slossless_assign; apply lossless_assign) ||
   (apply slossless_random; apply lossless_random) || 
   (apply slossless_nil; apply lossless_nil) || 
   (apply slossless_cond; slossless_tac) ||
   (apply slossless_while; [ | slossless_tac ]) ||
    apply slossless_call_adv || idtac.

 Ltac elim_assign := 
  rewrite (@deno_cons_elim _ _ (_ <- _)), Mlet_simpl, deno_assign_elim.
 
 Ltac elim_cond b m := let H := fresh "Hguard" in
  repeat (rewrite (@deno_cons_elim _ _ (If _ then _ else _)), 
   Mlet_simpl, (@deno_cond_elim _ _ b _ _ m));
  case_eq (@E.eval_expr _ T.Bool b m); intro H.

 Ltac expr_simpl := 
  unfold EP1, EP2, notR, andR, orR, impR, E.eval_expr; simpl; 
   unfold O.eval_op; simpl; mem_upd_simpl.

 Section BOUNDED_LOOP.

  Variable c : cmd.
  Variable E : env.
  Variable b : E.expr T.Bool.
  Variable variant : E.expr T.Nat.

  Hypothesis Hvar: forall k (m:Mem.t k), E.eval_expr b m -> 
   range (EP k (variant <! (E.eval_expr variant m))) ([[c]] E m).

  Lemma lossless_bounded_while:
   lossless E c ->
   lossless E [while b do c].
  Proof.
   intros Hloss k.
   assert (forall (n:nat) (m : Mem.t k), E.eval_expr variant m = n ->
    (mu ([[ [while b do c] ]] E m)) (@fone _) == 1%U).
   induction n using lt_wf_ind;intros.
   rewrite deno_while_elim, deno_cond_elim.
   case_eq (E.eval_expr b m); intros Heq; [ | rewrite deno_nil_elim; trivial].
   rewrite deno_app_elim, <- (Hloss k m).
   apply range_eq with (1:=Hvar m Heq).
   intros m' Hlt; apply (H (E.eval_expr variant m')); trivial.
   rewrite <- H0; unfold EP in Hlt; simpl in Hlt; unfold O.eval_op in Hlt.
   simpl in Hlt.
   apply leb_complete in Hlt; omega.
   intros m;apply (H (E.eval_expr variant m) m (refl_equal _)).
  Qed.

  Lemma deno_bounded_while_elim: forall k n (m:Mem.t k) f,
   (forall m':Mem.t k, E.eval_expr variant m' = 0 -> E.eval_expr b m' = false) ->
   E.eval_expr variant m <= n ->
   mu ([[ [while b do c] ]] E m) f == mu ([[ unroll_while b c n ]] E m) f.
  Proof.
   induction n using lt_wf_ind; induction n.
   (* base case *)
   intros m f Hb Hm.
   rewrite (deno_while_false_elim _ _ _ _ _ (Hb _ (eq_sym (le_n_0_eq _ Hm)))).
   rewrite (deno_unroll_while_false_elim _ _ _ _ _ _ 
    (Hb _ (eq_sym (le_n_0_eq _ Hm)))).
   trivial.
   (* inductive case *)
   intros m f Hb Hn'.
   unfold unroll_while; fold (unroll_while b c n).
   rewrite deno_while_elim.
   repeat rewrite deno_cond_elim; case_eq (E.eval_expr b m); intro Heq.
   repeat rewrite deno_app_elim.
   apply range_eq with (1:=Hvar _ Heq).
   intros m' Hm'; apply H; auto.
   generalize Hn' Hm'; clear Hn' Hm'; unfold EP; rewrite <- eval_lt;
    change (E.eval_expr (E.eval_expr variant m) m') with (E.eval_expr variant m).
   omega.
   repeat rewrite deno_nil_elim; trivial.
  Qed.

 End BOUNDED_LOOP.


 (** Rule to move a piece of code outside a loop *)
 Section WHILE_HOIST.
 
  Variable E1 E2 : env.
  Variables c1 c2 c1' c2' : cmd.
  Variables b1 b2 : E.expr T.Bool.
  Variables I P Q : mem_rel.

  Hypothesis H_guards: forall k (m1 m2:Mem.t k),
   (I /-\ P) _ m1 m2 ->
   E.eval_expr b1 m1 = E.eval_expr b2 m2.
  
  Hypothesis H_c1_c2: equiv 
   (I /-\ EP1 b1 /-\ EP2 b2) 
   E1 c1 
   E2 c2
   (I /-\ P).
  
  Hypothesis H_c1'_c2': equiv 
   (I /-\ P /-\ ~- EP1 b1 /-\ ~- EP2 b2) 
   E1 c1' 
   E2 c2'
   (I /-\ Q /-\ ~- EP1 b1 /-\ ~- EP2 b2).

  Lemma loop_hoist: equiv 
   (I /-\ EP1 b1 /-\ EP2 b2) 
   E1 ([ while b1 do c1 ] ++ c1')
   E2 ([ while b2 do c2 ] ++ c2') 
   (I /-\ Q /-\ ~-EP1 b1 /-\ ~-EP2 b2).
  Proof.
   apply equiv_trans_eq_mem_r with trueR E2  
    ( [If b2 _then (c2 ++ [while b2 do c2])] ++ c2'); 
    [ rewrite proj1_MR; apply equiv_eq_sem; intros; apply eq_distr_intro;
     intro f; repeat rewrite deno_app_elim; apply eq_distr_elim;
      apply eq_distr_intro;  apply deno_while_elim | | 
       unfold trueR; intros k m1 _ _; trivial ].
   apply equiv_trans_eq_mem_l with trueR E1  
    ( [If b1 _then (c1 ++ [while b1 do c1])] ++ c1'); 
    [ rewrite proj1_MR; apply equiv_eq_sem; intros; apply eq_distr_intro;
     intro f; repeat rewrite deno_app_elim; apply eq_distr_elim;
      apply eq_distr_intro;  apply deno_while_elim | | 
       unfold trueR; intros k m1 _ _; trivial ].
   apply equiv_app with (Q:= (I /-\ P) /-\ ~- EP1 b1 /-\ ~- EP2 b2)
    (c1:= [If b1 _then c1 ++ [while b1 do c1] ] ) (c2:=c1') 
    (c3:= [If b2 _then c2 ++ [while b2 do c2] ]) (c4:=c2').
   apply equiv_cond.
   apply equiv_app with (I /-\ P).
   rewrite proj1_MR; assumption.
   apply equiv_while.
   assumption.
   apply equiv_strengthen with (2:=H_c1_c2).
   intros k m1 m2 ( (H1,_),H2); split; assumption.
   apply equiv_False; unfold notR; intros k m1 m2 ((_,(?,_)),(?,_)); tauto.
   intros k m1 m2  (_,(H1,H2)); rewrite H1, H2; trivial.
   rewrite andR_assoc; assumption.
  Qed.

 End WHILE_HOIST.
 (***)


 Section PERMUTATION_FACTS.

  Open Scope nat_scope.

  Lemma sampling_fact1: forall E 
   (x r:Var.var (T.User R_)) (p:Var.var (T.User P_)),
   Var.mkV x <> Var.mkV r -> 
   EqObs 
   (Vset.singleton r)
   E [p <$- P; x <- p |+->| r ]
   E [x <$- R; p <- x |-/-| r ]
   (Vset.add x (Vset.add p (Vset.singleton r))).
  Proof.
   intros.
   apply EqObs_sym.
   apply equiv_cons with (fun k (m1 m2:Mem.t k) => 
    E.eval_expr (p |+->| r) m2 = m1 x /\
    E.eval_expr (x |-/-| r) m1 = m2 p /\ 
    m1 r = m2 r).

   eapply equiv_strengthen; [ | apply equiv_random_permut with 
    (f:=fun k (m1 m2:Mem.t k) (v:T.interp k (T.User P_)) => PAD.pad v (m2 r))]. 
   intros; split.
   (* Permutation *)
   unfold permut_support; simpl E.eval_support.
   apply (PermutP_sym _ (PAD.P_R_iso_pad _)).

   (* Postcondition *)
   intros v Hv; repeat split; expr_simpl.
   rewrite Mem.get_upd_diff, (H0 _ r); 
    [ | apply Vset.singleton_correct | ]; trivial.
   apply (PAD.pad_padinv _ _ Hv).
   repeat rewrite Mem.get_upd_diff; [ | discriminate | trivial ].
   refine (H0 _ r _); apply Vset.singleton_correct; trivial.
   eapply equiv_strengthen ; [ | apply equiv_assign ].
   unfold upd_para; intros k m1 m2 [H1 [H2 H3] ] t v Hv.
   Vset_mem_inversion Hv; subst; mem_upd_simpl.
   symmetry; trivial.
   rewrite Mem.get_upd_diff; trivial.
  Qed.

  Lemma sampling_fact2: forall E 
   (x r:Var.var (T.User R_)) (p:Var.var (T.User P_)),
   Var.mkV r <> Var.mkV x -> 
   EqObs 
   (Vset.singleton x)
   E [p <$- P; r <- p |-->| x  ]
   E [r <$- R; p <- x |-/-| r ]
   (Vset.add x (Vset.add p (Vset.singleton r))).
  Proof.
   intros.
   apply EqObs_sym.
   apply equiv_cons with (fun k (m1 m2:Mem.t k) =>  
     E.eval_expr (p |-->| x) m2 = m1 r /\
     E.eval_expr (x |-/-| r) m1 = m2 p /\
     m1 x = m2 x).
   eapply equiv_strengthen; [ | apply equiv_random_permut with 
    (f:=fun k (m1 m2:Mem.t k) (v:T.interp k (T.User P_)) => 
   PAD.unpad  v (m2 x)) ].
   intros; split.
   (* Permutation *)
   unfold permut_support; simpl E.eval_support.
   apply (PermutP_sym _ (PAD.P_R_iso_unpad _)).

   (* Postcondition *)
   intros v Hv; expr_simpl; repeat split.
   rewrite Mem.get_upd_diff, (H0 _ x); 
    [ | apply Vset.singleton_correct | ]; trivial.
   apply (PAD.unpad_padinv _ _ Hv).
   rewrite Mem.get_upd_diff; [ | trivial ].
   refine (H0 _ x _); apply Vset.singleton_correct; trivial.
   eapply equiv_strengthen ; [ | apply equiv_assign ].
   unfold upd_para; intros k m1 m2 [H1 [H2 H3] ] t v Hv.
   Vset_mem_inversion Hv; subst; mem_upd_simpl.
   rewrite Mem.get_upd_diff; trivial.
   symmetry; trivial.
  Qed.

  Close Scope nat_scope.

 End PERMUTATION_FACTS.


 (** * Stuff to deal with abstract procedures *)
 Section BUILD_REFL_INFO.
 
  Variables E1 : env.
  Variable t : T.type. 
  Variable f : Proc.proc t.
  Variable X : Vset.t.

  Hypothesis H0 : forall E, lossless E (proc_body E1 f).
  Hypothesis H1 : forall E, Modify E X (proc_body E1 f).
  Hypothesis H2 : forall x, Vset.mem x X -> Var.is_local x.   
  Hypothesis H3 : forall x, 
   Vset.mem x (fv_expr (proc_res E1 f)) -> Var.is_local x.

  Hypothesis H4 : forall E E',
   EqObs (Vset_of_var_decl (proc_params E1 f))
   E  (proc_body E1 f) 
   E' (proc_body E1 f) 
   (fv_expr (proc_res E1 f)).

  Definition basic_refl_info : proc_eq_refl_info E1 f.
  refine (@Build_proc_eq_refl_info E1 t f
   (Build_dproc_eq_refl_info 
    Vset.empty Vset.empty 
    (Vset_of_var_decl (proc_params E1 f)) Vset.empty true) _).
  split; simpl; intros; try discriminate.
  trivial.
  apply VsetP.subset_refl.
  exists X; split.
  trivial.
  rewrite VsetP.union_sym, VsetP.union_empty; trivial.
  apply VsetP.subset_refl.
  exists (fv_expr (proc_res E1 f)); repeat split.
  trivial.
  rewrite VsetP.union_sym, VsetP.union_empty; trivial.
  rewrite VsetP.union_sym, VsetP.union_empty, VsetP.union_sym, VsetP.union_empty.
  apply EqObs_e_fv_expr.
  Defined.

  Definition add_basic_refl_info (pi:eq_refl_info E1) : eq_refl_info E1 :=
   fun (t':T.type) =>
    match T.eq_dec t t' with
     | left Heqr => 
      match Heqr in (_ = y0) return 
       forall (g:Proc.proc y0), option (proc_eq_refl_info E1 g) with
       | refl_equal =>
        fun (g:Proc.proc t) =>
         match Proc.eq_dec f g with
          | left Heqf =>
           match Heqf in (_ = y0) return option (proc_eq_refl_info E1 y0) with
            | refl_equal => Some basic_refl_info
           end
          | right _ => pi t g
         end
      end
     | right _ => fun g => pi t' g
    end.

 End BUILD_REFL_INFO.


 Section BUILD_INV_INFO.

  Variables E1 E2 : env.
  Variable t : T.type. 
  Variable f : Proc.proc t. 
  Variable X : Vset.t.

  Hypothesis H  : proc_body E1 f = proc_body E2 f.
  Hypothesis H0 : proc_params E1 f = proc_params E2 f.
  Hypothesis H1 : proc_res E1 f = proc_res E2 f.

  Hypothesis H2 : forall E, lossless E (proc_body E1 f).
  Hypothesis H3 : forall E, Modify E X (proc_body E1 f).
  Hypothesis H3' : fv_expr (proc_res E1 f) [<=] X.
  Hypothesis H4 : forall x, Vset.mem x X -> Var.is_local x.   
  Hypothesis H5 : forall x, 
   Vset.mem x (fv_expr (proc_res E1 f)) -> Var.is_local x.
  Hypothesis H6 : forall E E',
   EqObs (Vset_of_var_decl (proc_params E1 f))
   E  (proc_body E1 f) 
   E' (proc_body E1 f) 
   (fv_expr (proc_res E1 f)).

  Lemma H7 : forall E, lossless E (proc_body E2 f).
  Proof.
   rewrite <- H; trivial.
  Qed.

  Lemma H8 : forall E, Modify E X (proc_body E2 f).
  Proof.
   rewrite <- H; trivial.
  Qed.

  Lemma H9 : forall x, Vset.mem x (fv_expr (proc_res E2 f)) -> Var.is_local x.
  Proof.
   rewrite <- H1; trivial.
  Qed.

  Lemma H10 : forall E E',
   EqObs (Vset_of_var_decl (proc_params E2 f))
   E  (proc_body E2 f) 
   E' (proc_body E2 f) 
   (fv_expr (proc_res E2 f)).
  Proof.
   rewrite <- H, <- H0, <- H1; trivial.
  Qed.


  Definition add_basic_info (I:mem_rel) 
   (pii:eq_inv_info I E1 E2) : eq_inv_info I E1 E2.    
   intros I pii.
   refine (@add_pii_info _ E1 E2 t f _ pii).
   refine (Build_proc_eq_inv_info
    (dpii:=Build_dproc_eq_inv_info 
    (basic_refl_info _ _ H2 H3 H4 H5 H6)
    (basic_refl_info _ _ H7 H8 H4 H9 H10)
    Vset.empty
    (Vset_of_var_decl (proc_params E1 f))
    Vset.empty) _).
   split; simpl; intros; try discriminate.
   apply VsetP.subset_refl.
   rewrite H0; apply VsetP.subset_refl.
   exists (fv_expr (proc_res E1 f)); repeat split.
   trivial.
   rewrite VsetP.union_sym, VsetP.union_empty.
   destruct pii.
   apply SemTh.equiv_inv_Modify with 
    (X1:=pii_inv_X3) (X2:=pii_inv_X4) (M1:=X) (M2:=X).
   assumption.
   apply H3.
   rewrite <-H; apply H3.
   rewrite VsetP.inter_idem; apply H3'.
   unfold Vset.disjoint.
   destruct (VsetP.empty_dec (Vset.inter pii_inv_X3 X));
    [ rewrite H11; trivial | ].
   destruct H11 as [x Hx]; rewrite VsetP.inter_spec in Hx; destruct Hx.
   generalize (H4 _ H12); unfold Var.is_local.
   rewrite  pii_inv_global0; [ discriminate | auto with set ].
   unfold Vset.disjoint.
   destruct (VsetP.empty_dec (Vset.inter pii_inv_X4 X)); 
    [ rewrite <- H11; apply VsetP.eqb_eq; apply VsetP.eq_refl | ].
   destruct H11 as [x Hx]; rewrite VsetP.inter_spec in Hx; destruct Hx.
   generalize (H4 _ H12); unfold Var.is_local.
   rewrite  pii_inv_global0; [ discriminate | auto with set ].
   rewrite <-H.
   fold_eqobs_tac; apply H6.
   intros k m1 m2 Heq; rewrite <- H1.
   rewrite depend_only_fv_expr_subset with (2:=Heq); auto with set.
  Defined.

 End BUILD_INV_INFO.


 Section BUILD_UPTO_BAD_INFO.

  Variables E1 E2 : env.
  Variable t : T.type. 
  Variable f : Proc.proc t. 
  Variable X : Vset.t.
  Variable bad : Var.var T.Bool.

  Hypothesis Gbad : Var.is_global bad.
  Hypothesis H_args : proc_params E1 f = proc_params E2 f.
  Hypothesis H_ret : proc_res E1 f = proc_res E2 f.
  Hypothesis H_bodies: proc_body E1 f = proc_body E2 f.
  Hypothesis H_bodies_sem: forall k (m:Mem.t k) g,
   mu ([[ proc_body E1 f ]] E1 m) g == mu ([[ proc_body E2 f ]] E2 m) g.

  Hypothesis H_mod1: forall E, Modify E X (proc_body E1 f).
  Hypothesis H_mod2 : forall E, Modify E X (proc_body E2 f).

  Hypothesis H_mod_loc : forall x, Vset.mem x X -> Var.is_local x.   

  Definition f_add_upto_info 
   (pi:upto_info bad E1 E2) tp (p:Proc.proc tp) : bool :=
   if Proc.eqb p f then true else pi _ p.

  Lemma sadd_upto_info1 : forall  (pi:upto_info bad E1 E2), 
   prbad_spec bad E1 (f_add_upto_info pi).
  Proof.
   intros; unfold f_add_upto_info; red; intros.
   generalize (Proc.eqb_spec_dep p f); destruct (Proc.eqb p f).
   (* case [p = f] *)
   intro Heq.
   assert (H' : [[proc_body E1 p]] E1 m == [[proc_body E1 f]] E1 m) by
    (inversion Heq; subst;  simpl; trivial).
   rewrite (eq_distr_elim H'), 
    (@Modify_deno_elim _ X _ (@H_mod1 E1) _ _ f0).
   rewrite (eq_distr_elim H'), 
    (@Modify_deno_elim _ X _ (@H_mod1 E1) _ _ (restr _ f0)).
   apply deno_stable_eq; refine (ford_eq_intro _); intro m'.
   unfold restr, EP in *;  simpl in *.
   rewrite update_mem_notin, H0; trivial.
   intros H''; absurd (Var.is_global bad); [ | exact Gbad].
   rewrite Var.global_local; auto.
   (* case [p != f] *)
   intros; apply pi.(upto_pr1); trivial.
  Qed.

  Lemma sadd_upto_info2 : forall (pi:upto_info bad E1 E2), 
   prbad_spec bad E2 (f_add_upto_info pi).
  Proof.
   intros; unfold f_add_upto_info; red; intros.
   generalize (Proc.eqb_spec_dep p f); destruct (Proc.eqb p f).
   (* case [p = f] *)
   intro Heq.
   assert (H' : [[proc_body E2 p]] E2 m == [[proc_body E2 f]] E2 m) by
    (inversion Heq; subst;  simpl; trivial).
   rewrite (eq_distr_elim H'), 
    (@Modify_deno_elim _ X _ (@H_mod2 E2) _ _ f0).
   rewrite (eq_distr_elim H'), 
    (@Modify_deno_elim _ X _ (@H_mod2 E2) _ _ (restr _ f0)).
   apply deno_stable_eq; refine (ford_eq_intro _); intro m'.
   unfold restr, EP in *;  simpl in *.
   rewrite update_mem_notin, H0; trivial.
   intros H''; absurd (Var.is_global bad); [ | exact Gbad].
   rewrite Var.global_local; auto.
   (* case [p != f] *)
   intros; apply pi.(upto_pr2); trivial.
  Qed.

  Lemma sadd_upto_info : forall (pi:upto_info bad E1 E2),
   upto_spec bad E1 E2 (f_add_upto_info pi).
  Proof.
   intros; unfold f_add_upto_info; red; intros.
   generalize (Proc.eqb_spec_dep p f); destruct (Proc.eqb p f).
   (* case [p = f] *)
   intro Heq; inversion Heq; subst; apply T.inj_pair2 in H3; subst.
   split; [ | split]; intros.
   apply H_bodies_sem.
   apply H_ret. 
   apply H_args.
   (* case [p != f] *)
   intros; apply pi.(supto); trivial.
  Qed.
  
  Definition add_upto_info' (pi:upto_info bad E1 E2) : upto_info bad E1 E2.
   intro pi.
   apply mk_p_upto_info with (f_add_upto_info pi). 
   apply sadd_upto_info1.
   apply sadd_upto_info2.
   apply sadd_upto_info.
  Defined.

 End BUILD_UPTO_BAD_INFO.
 (***)


 (** * Variables *)
 Notation r  := (Var.Lvar (T.User R_) 1).
 Notation a  := (Var.Lvar (T.Option (T.User A_)) 2).
 Notation a' := (Var.Lvar (T.User A_) 3).
 Notation x  := (Var.Lvar (T.User R_) 4).
 Notation n  := (Var.Lvar T.Nat 10).
 Notation n' := (Var.Lvar T.Nat 11).
 Notation r' := (Var.Lvar (T.Option (T.User A_)) 12).
 Notation l  := (Var.Lvar (T.List (T.User A_)) 13).
 Notation InvF_in  := (Var.Lvar (T.User R_) 20).
 Notation InvF_out := (Var.Lvar (T.Option (T.Pair (T.User A_) (T.User P_))) 21).
 Notation i        := (Var.Lvar T.Nat 22).
 Notation p        := (Var.Lvar (T.User P_) 23).
 Notation ret      := (Var.Lvar (T.Option (T.Pair (T.User A_) (T.User P_))) 24).
 Notation m'       := (Var.Lvar Msg 25). 
 Notation ml       := (Var.Lvar Msg 26).
 Notation mr       := (Var.Lvar Msg 27).
 Notation b        := (Var.Lvar T.Bool 28).
 Notation bad      := (Var.Gvar T.Bool 29).
 Notation L        := (Var.Gvar 
  (T.List (T.Pair Msg 
   (T.Pair (T.Option (T.Pair (T.User A_) (T.User P_))) (T.User R_)))) 30).
 Notation Ll       := (Var.Gvar 
  (T.List (T.Pair Msg (T.Option (T.Pair (T.User A_) (T.User P_))))) 31).
 Notation Lr       := (Var.Gvar (T.List (T.Pair Msg (T.User R_))) 32).
 
 (** * Procedures *)
 Notation InvF     := (Proc.mkP 2 
  (T.User R_ :: nil) (T.Option (T.Pair (T.User A_) (T.User P_)))).
 Notation H        := (Proc.mkP 3 
  (Msg:: nil) 
  (T.Pair (T.Option (T.Pair (T.User A_) (T.User P_))) (T.User R_))).
 Notation Hl       := (Proc.mkP 4 
  (Msg:: nil) (T.Option (T.Pair (T.User A_) (T.User P_)))).
 Notation Hr       := (Proc.mkP 5 (Msg:: nil) (T.User R_)).
 Notation A        := (Proc.mkP 6 nil T.Bool).


 Definition InvF_args : var_decl (Proc.targs InvF) := dcons _ InvF_in (dnil _).
 Definition InvF_ret := InvF_out.

 Parameter E0 : env.

 Definition mkEnv (InvF_Body:cmd) := 
  add_decl (E' E0) InvF InvF_args (refl_equal true) InvF_Body InvF_ret.

 Close Scope nat_scope.
 Close Scope bool_scope.

 (* ******************************  CLAIM 2  ****************************** *)
 (* Let [f:A -> R] be an (alpha,epsilon)-weak encoding v2 and let           *) 
 (* [F : A x P -> R] be defined as [F (a,p) = p |-->| (f a)]. Then [F] is   *)
 (* an epsilon'-admissible encoding v2 with [epsilon' =  epsilon +          *)
 (* (1 - 1/alpha)^Tmax].                                                    *)
 (* *********************************************************************** *)

 Definition InvF_body :=
  [
   i <- 0%nat; 
   a <- none _; 
   p <- Pdef;  
   x <- Rdef; 
   a' <- Adef; 
   while ((i <=! TMax) && !(IsSome a)) do 
    [ 
     i <- i +! 1%nat;
     p <$- P;
     x <- p |+->| InvF_in;
     a <c- Invf with {x}
    ];     
    If (IsSome a) _then [ a' <- Proj a ];
    If (IsSome a) then
     [ InvF_out <- some (a' | p) ]
    else
     [ InvF_out <- none _ ]
  ].

 Definition E := mkEnv InvF_body. 

 Lemma Invf_lossless : forall E, lossless E Invf_body.
 Proof.
  intros.
  apply slossless_lossless.
  apply Invf_slossless.
 Qed.

 Definition i_EE : eq_inv_info trueR E E.
  refine (add_refl_info_rm InvF Vset.empty Vset.empty _).
  apply add_basic_info with (f:=Invf) (X:=Invf_X); trivial.
  apply Invf_lossless.
  apply Invf_Modify.
  apply Invf_ret_expr.
  apply Invf_X_local.
  intros ? H; apply Vset.subset_correct with (1:=Invf_ret_expr) in H.
  apply Invf_X_local; trivial.
  intros; eapply equiv_weaken; [ | apply Invf_eqobs ].
  intros; apply req_mem_weaken with (2:=H); apply Invf_ret_expr.
  apply empty_info.
 Defined.

 Definition Gi := [ r <$- R; ret <c- InvF with {r} ].

 Definition Gf := [ a' <$- A; p <$- P; ret <- some (a' | p) ]. 


 (* **************************** 1st STEP **************************** *)
 (* 1) Inline Inv                                                      *)
 (******************************************************************** *)

 Definition cond := (i <=! TMax) && !(IsSome a).

 Definition G1 :=
 ([
   r <$- R;
   i <- 0%nat; 
   a <- none _; 
   p <- Pdef;
   x <- Rdef; 
   a' <- Adef
  ] ++ 
  [
   while cond do 
    [ 
     i <- i +! 1%nat;
     p <$- P;
     x <- p |+->| r; 
     a <c- Invf with {x}
    ]  
  ]) ++ 
  [     
   If (IsSome a) _then [ a' <- Proj a ];
   If (IsSome a) then [ ret <- some (a' | p) ] else [ ret <- none _ ]
  ].

 Lemma G1_Gi: EqObs Vset.empty E G1 E Gi {{r,ret}}.
 Proof.
  unfold G1, Gi.
  sinline i_EE InvF.
  eqobs_hd i_EE.
  cp_test (IsSome a); deadcode; eqobs_in.
 Qed.


 (* **************************** 2nd STEP **************************** *)
 (* 1) Apply [sampling_fact1] to compute the values assigned           *)
 (* to [p] and [x]                                                     *)
 (******************************************************************** *)

 Definition G2 :=
  ([
    r <$- R;
    i <- 0%nat; 
    a <- none _; 
    p <- Pdef;
    x <- Rdef; 
    a' <- Adef
   ] ++ 
   [
    while cond do 
     [ 
      i <- i +! 1%nat;
      x <$- R;  
      p <- (x |-/-| r);
      a <c- Invf with {x}
     ]  
   ]) ++ 
   [
    If (IsSome a) _then [ a' <- Proj a ];
    If (IsSome a) then [ ret <- some (a' | p) ] else [ ret <- none _ ]
   ].

 Lemma G1_G2: EqObs Vset.empty E G1 E G2 {{r,ret}}.
 Proof.
  unfold G1, G2.
  apply equiv_app with (kreq_mem {{i,p,a,r}} /-\ ~- EP1 cond  /-\ ~- EP2 cond).
  apply equiv_app with (kreq_mem {{i,p,a,r}}).
  eqobs_in.
  apply equiv_while.
  intros k m1 m2 Hm.
  apply (depend_only_fv_expr cond).
  apply req_mem_weaken with (2:=Hm); apply eq_refl.
  eqobs_tl i_EE.
  rewrite proj1_MR; eqobs_hd_n 1%nat; union_mod.
  eapply equiv_sub; [ | | apply sampling_fact1 ].
  intro k; apply implMR_kreq_mem_subset; apply eq_refl.
  intro k; apply implMR_kreq_mem_subset; apply eq_refl.
  discriminate.
  cp_test (IsSome a); eqobs_in.
 Qed.


 (* **************************** 3rd STEP **************************** *)
 (* 1) Push assignment [ p <- log ( |-/-| r) ] outside the loop        *) 
 (******************************************************************** *)

 Definition G3 :=
  [
    r <$- R;
    i <- 0%nat; a <- none _; 
    p <- Pdef;  x <- Rdef; a' <- Adef
   ] ++ 
  ([
   while cond do 
    [ 
     i <- i +! 1%nat;
     x <$- R;  
     a <c- Invf with {x}
    ];
    p <- (x |-/-| r) 
  ] ++ 
  [
   If (IsSome a) _then [ a' <- Proj a ];
   If (IsSome a) then [ ret <- some (a' | p) ] else [ ret <- none _ ]
  ]).


 Lemma G2_G3: EqObs Vset.empty E G2 E G3 {{r,ret}}.
 Proof.
  unfold G2, G3; rewrite <- app_assoc.
  apply equiv_app with (kreq_mem {{a,i,r}} /-\ (EP1 cond) /-\ (EP2 cond)).
  fold (req_mem_rel {{a, i, r}} (EP1 cond /-\ EP2 cond)).
  eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl;
   intros _ _ _ _ _ _; split; trivial.
  apply equiv_app with (kreq_mem {{r,p,a}}).

  eapply equiv_weaken; [ | apply (@loop_hoist _ _ 
   ([ i <- i +! 1%nat; x <$- R;  p <- (x |-/-| r); a <c- Invf with {x}  ])  
   ([ i <- i +! 1%nat; x <$- R; a <c- Invf with {x} ] ) (@nil I.instr)  
   ([  p <- (x |-/-| r) ]) _ _ _ 
   (req_mem_rel {{x}} (EP1 (p =?= (x |-/-| r)))) (kreq_mem {{p}})) ].
  intros k m1 m2 (H1,(H2,_)).
  apply req_mem_weaken with (Vset.union {{a, i, r}} {{p}});
   [ apply eq_refl | apply req_mem_union; trivial ].

  intros k m1 m2 (H1,_); apply depend_only_fv_expr.
  apply req_mem_weaken with (2:=H1); apply eq_refl.

  apply equiv_trans_eq_mem_l with trueR E 
   [i <- i +! 1%nat; x <$-R; a <c- Invf with {x};  p <- (x |-/-| r) ];
   [ rewrite proj1_MR; swap i_EE; apply equiv_eq_mem | | 
    unfold trueR; intros k m1 _ _; trivial ].
  rewrite proj1_MR; eqobs_hd_n i_EE 3%nat.
  eapply equiv_strengthen; [ | apply equiv_assign_l ].
  intros k m1 m2 H; split.
  apply req_mem_trans with m1; [ apply req_mem_sym | ].
  apply req_mem_upd_disjoint; apply eq_refl.
  apply req_mem_weaken with (2:=H); apply eq_refl.
  split.
  apply req_mem_trans with m1; [ apply req_mem_sym | ].
  apply req_mem_upd_disjoint; apply eq_refl.
  apply req_mem_weaken with (2:=H); apply eq_refl.
  expr_simpl; apply (@Ti_eqb_refl k (T.User P_)).
  eapply equiv_strengthen; [ | apply equiv_assign_r ].
  intros k m1 m2 (H1,((H2,H3),(H4,H5))); unfold EP1, EP2, andR, notR in *; 
   split;[ | split; [ | split ] ].
  apply req_mem_trans with m2; [ assumption | 
   apply req_mem_upd_disjoint; apply eq_refl ].
  intros t v Hv; Vset_mem_inversion Hv; rewrite <-Heq.
  mem_upd_simpl.
  rewrite (@depend_only_fv_expr (T.User P_)  (x |-/-| r)  _ m2 m1); [ |
   apply req_mem_sym; apply req_mem_weaken with (Vset.union {{a, i, r}} {{x}});
    [ apply eq_refl | apply req_mem_union; trivial ] ].
  rewrite <-is_true_Ti_eqb.
  setoid_rewrite <-(@eval_eq k m1 (T.User P_) p (x |-/-| r)); trivial.
  assumption.
  intro H; elim H5; unfold is_true in *; rewrite <-H.
  apply (@depend_only_fv_expr T.Bool cond).
  apply req_mem_upd_disjoint; apply eq_refl.

  cp_test (IsSome a); eqobs_in.
 Qed.


 (* **************************** 4th STEP **************************** *)
 (* 1) Apply [sampling_fact2] to assign a fresh random value to [z]    *)
 (* (and remove variable [r] since it becomes dead code)               *)
 (******************************************************************** *)

 Definition G4 :=
  ([
    i <- 0%nat; a <- none _; 
    p <- Pdef;  x <- Rdef; a' <- Adef  
  ] ++ 
  [
   while cond do 
    [ 
     i <- i +! 1%nat;
     x <$- R;  
     a <c- Invf with {x}
    ];
    p <$- P 
  ]) ++ 
  [
   If (IsSome a) _then [ a' <- Proj a ];
   If (IsSome a) then [ ret <- some (a' | p) ] else [ ret <- none _ ]
  ].


 Lemma G3_G4: EqObs Vset.empty E G3 E G4 {{ret}}.
 Proof.
  unfold G3, G4.
  apply EqObs_trans with E
   ([
    i <- 0%nat; a <- none _; 
    p <- Pdef;  x <- Rdef; a' <- Adef;
     while cond do 
      [ 
       i <- i +! 1%nat;
       x <$- R;  
       a <c- Invf with {x}
      ];
     r <$- R;
     p <- (x |-/-| r) 
   ] ++ 
   [
    If (IsSome a) _then [ a' <- Proj a ];
    If (IsSome a) then [ ret <- some (a' | p) ] else [ ret <- none _ ]
  ]).
  swap i_EE; eqobs_hd_n i_EE 7%nat.
  cp_test (IsSome a); eqobs_in.
  apply equiv_app with (kreq_mem {{a,p}}).
  eqobs_hd i_EE; union_mod.
  apply equiv_strengthen with (kreq_mem {{x}}).
  intros; eapply req_mem_weaken with (2:=H); apply eq_refl.
  apply EqObs_trans with E [p <$-P;  r <- p |-->| x ].
  apply EqObs_sym; apply equiv_weaken with (kreq_mem {{x,p,r}});
   [ intros; eapply req_mem_weaken with (2:=H); apply eq_refl | ].
  apply (@sampling_fact2 E x r p); discriminate.
  deadcode; eqobs_in.
  cp_test (IsSome a); eqobs_in.
 Qed.


 (* **************************** 5th STEP **************************** *)
 (* 1) Use the fact that [f] is a weak-encoding to replace [Invf]      *)
 (* output with a truely random value when the inverter succeeds at    *)
 (* some iteration                                                     *)
 (* 2) Add the [bad] flag for the next transition                      *)
 (******************************************************************** *)

 Definition G5 :=
  [
    i <- 0%nat; a <- none _; 
    p <- Pdef;  x <- Rdef; a' <- Adef;
    bad <- false;
    while cond do 
      [ 
        i <- i +! 1%nat;
        x <$- R;  
        a <c- Invf with {x}
      ] 
  ] ++ 
  [
    If (IsSome a) then [ a' <$- A ] else [ bad <- true ];
    p <$- P;
    If (IsSome a) then [ ret <- some (a' | p) ] else [ ret <- none _ ]
  ].

 Lemma loop_lossless: forall (c:cmd) (E:env) (X:Vset.t),
   Modify E X c ->
   Vset.mem i X = false ->
   lossless E c ->
   lossless E [ while cond do ((i <- i +! 1%nat)::c) ].
 Proof.
  intros.
  apply lossless_bounded_while with (TMax +! 1%nat -! i).
  
  intros k m Hm f H_f.
  elim_assign.
  rewrite (Modify_deno_elim H).
    match goal with |- _ == fmonot (mu ?d) _ => rewrite <-(mu_zero d) end.
    apply mu_stable_eq; unfold fzero; refine (ford_eq_intro _); intro m'.
    apply H_f.
    generalize Hm; unfold cond, EP; clear Hm.
    expr_simpl; rewrite update_mem_notin; mem_upd_simpl.
    rewrite is_true_andb; intros [Hm _].
    apply leb_correct; apply leb_complete in Hm; omega.
    rewrite H0; apply diff_false_true.

  apply lossless_cons; [ apply lossless_assign | assumption ].
 Qed.

 Lemma G5_loop_lossless: lossless E
  [ while cond do [i <- i +! 1%nat; x <$- R; a <c- Invf with {x} ] ].
 Proof.
  apply loop_lossless with {{a,x}}.
    apply modify_correct with (refl1_info i_EE) Vset.empty; apply eq_refl.
    apply eq_refl.
    apply is_lossless_correct with (refl1_info i_EE); apply eq_refl.
 Qed.


 Definition i_EE' : eq_inv_info trueR E (E' E0).
  apply add_basic_info with (f:=Invf) (X:=Invf_X); trivial.
  apply Invf_lossless.
  apply Invf_Modify.
  apply Invf_ret_expr.
  apply Invf_X_local.
  intros ? H; apply Vset.subset_correct with (1:=Invf_ret_expr) in H.
  apply Invf_X_local; trivial.
  intros; eapply equiv_weaken; [ | apply Invf_eqobs ].
  intros; apply req_mem_weaken with (2:=H); apply Invf_ret_expr.
  apply empty_info.
 Defined.

 Opaque deno.

 Lemma Invf_distance : forall k (f g:Mem.t k -o> U),
  (forall m1 m2, kreq_mem {{a'}} m1 m2 -> f m1 == g m2) ->
  forall m1 m2,
   Uabs_diff
   (mu (distr_cond 
    ([[ [x <$-R; a <c- Invf with {x}; a' <- Proj a] ]] E m1) 
    (EP k (IsSome a))) f)   
   (mu ([[ [a' <$-A] ]] E m2) g) <= epsilon k.
 Proof.
  intros.
  setoid_replace
   (mu (distr_cond ([[ [x <$- R; a <c- Invf with {x}; a' <- Proj a] ]] E m1)
    (EP k (IsSome a))) f) with
   (mu (distr_cond ([[ [x <$- R; a <c- Invf with {x}; a' <- Proj a] ]] (E' E0) m1)
    (EP k (IsSome a))) f).
  setoid_replace 
   (mu ([[ [a' <$- A] ]] E m2) g) with (mu ([[ [a' <$- A] ]] (E' E0) m2) g).
  apply Invf_distance_from_random; trivial.
  apply EqObs_deno with Vset.empty {{a'}}; auto.
  eqobs_in.
  intros; transitivity (f m0); [symmetry | ]; auto.

  unfold distr_cond.
  simpl; apply Udiv_eq_compat.
  refine (EqObs_deno (I:=Vset.empty) (O:={{a,a'}}) _ _ _ _ _); auto.
  eqobs_in i_EE'.
  
  intros; unfold EP; simpl; unfold O.eval_op; simpl.
  rewrite (H0 _ a); destruct (m3 a); trivial.
  simpl; transitivity (g m3).
  apply H; apply req_mem_weaken with (2:=H0); vm_compute; trivial.
  symmetry; auto.
  
  refine (EqObs_deno (I:=Vset.empty) (O:={{a,a'}}) _ _ _ _ _); auto.
  eqobs_in i_EE'.
  intros; unfold EP, charfun, restr; simpl; unfold O.eval_op; simpl.
  rewrite (H0 _ a); destruct (m3 a); trivial.
 Qed.

 Transparent deno.

 Lemma Invf_output: forall k (f g:Mem.t k -o> U),
  (forall m1 m2 : Mem.t k, kreq_mem {{a'}} m1 m2 -> f m1 == g m2) ->  
  forall m1 m2,
   Uabs_diff 
   (mu ([[ [x <$- R; a <c- Invf with {x}; a' <- Proj a] ]] E m1) 
    (restr (EP k (IsSome a)) f)) 
   (mu ([[ [x <$- R; a <c- Invf with {x}; a' <$- A] ]] E m2) 
    (restr (EP k (IsSome a)) g)) <= 
   epsilon k * 
   Pr E [x <$- R; a <c- Invf with {x}; a' <- Proj a] m1 (EP k (IsSome a)).
 Proof.
  intros.
  unfold Pr. 
  set (X:=mu ([[ [x <$- R; a <c- Invf with {x}; a' <- Proj a] ]] E m1)
   (charfun (EP k (IsSome a)))).
  apply (Ueq_orc X 0); [auto | intro HX | intro HX].

  (* Pr E [x <$-R; a <c- Invf with {x}; a' <- Proj a] m1 (EP k (IsSome a)) = 0 *)
  apply Ole_trans with 0; [ apply Oeq_le; rewrite Uabs_diff_zero | auto ].
  apply Oeq_trans with 0.
  apply Ule_zero_eq; rewrite <-HX; unfold X.
  apply equiv_deno_le with Meq Meq.
  apply equiv_eq_mem.
  intros m1' m2' Hm'; unfold charfun; rewrite Hm'; apply restr_le_compat; auto.
  trivial.
  symmetry; apply Ule_zero_eq; rewrite <-HX; unfold X.
  apply equiv_deno_le with (kreq_mem Vset.empty) (kreq_mem {{a}}).
  deadcode i_EE; eqobs_in i_EE.
  intros m1' m2' Hm'; unfold charfun, restr, EP.
  rewrite <-(@depend_only_fv_expr T.Bool (IsSome a) _ m1' m2'); [ | trivial ].
  case (@E.eval_expr _ T.Bool (IsSome a) m1'); auto.
  apply req_mem_empty.
  
  (* Pr E [x <$-R; a <c- Invf with {x}; a' <- Proj a] m1 (EP k (IsSome a)) != 0 *)  rewrite <- (Umult_le_compat_left _ _ X (Invf_distance _ _ H m1 m2)).
  rewrite Umult_sym, <-Uabs_diff_mult, (@Umult_sym X), (@Umult_sym X).
  apply Oeq_le; apply Uabs_diff_morphism.
  rewrite distr_cond_simpl.
  symmetry; apply (Udiv_mult _ (neq_sym HX)).
  apply mu_monotonic; apply restr_le_compat; auto.

  symmetry.
  transitivity (mu ([[ [a' <$-A] ]] E m2) g *
   Pr E [x <$- R; a <c- Invf with {x} ] m2 (EP k (IsSome a))).
  apply Umult_eq_compat.
  apply equiv_deno with (kreq_mem Vset.empty) (kreq_mem {{a'}}).
  eqobs_in.
  intros m1' m2' Hm'; transitivity (f m1'); [ symmetry | ]; apply H; trivial.
  apply req_mem_empty.
  apply EqObs_Pr2 with Vset.empty {{a}};
   [ deadcode i_EE; eqobs_in i_EE | apply eq_refl | apply req_mem_empty ].

  unfold Pr, charfun; rewrite <-mu_restr_cte.
  rewrite (deno_app_elim _ [x <$- R; a <c- Invf with {x} ] [a' <$-A]).
  apply mu_stable_eq; unfold restr, EP, fcte; refine (ford_eq_intro _); intro m.
  case_eq (@E.eval_expr _ T.Bool (IsSome a) m); intro Hguard.
  (* case [IsSome a] *)
  repeat rewrite deno_random_elim; simpl E.eval_support.
  apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
  generalize Hguard; expr_simpl; intro Hg'; rewrite Hg'.
  transitivity (f (m2 {!a' <-- m'!})).
  symmetry; apply H; auto.
  apply H; apply req_mem_update; auto.
  (* case [~IsSome a] *)
  rewrite deno_random_elim.
  transitivity 
   (mu (sum_support (Sem.T.default k (T.User A_)) (A.elems k)) (fun _ => 0)).
  rewrite sum_support_const; [ trivial | apply A.elems_notnil ].
  apply sum_support_stable_eq; intros v Hv.
  rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ (m {!a' <-- v!}) m), Hguard;
   [ | apply req_mem_sym; apply req_mem_upd_disjoint ]; trivial.
 Qed.
 
 Lemma loop_unroll_distance : forall k (n:nat) (f g:Mem.t k -o> U),
  (forall m1 m2:Mem.t k, kreq_mem {{a'}} m1 m2 -> f m1 == g m2) ->
  forall m1 m2:Mem.t k,
   req_mem_rel {{a,i}} (EP1 (!(IsSome a))) _ m1 m2 -> 
   Uabs_diff
   (mu ([[ 
    unroll_while cond [ i <- i +! 1%nat; x <$- R; a <c- Invf with {x} ] (S n) ++
    [ If (IsSome a) _then [ a' <- Proj a ] ] 
   ]] E m1) (restr (EP k (IsSome a)) f))
   (mu ([[ 
    unroll_while cond [ i <- i +! 1%nat; x <$- R; a <c- Invf with {x} ] (S n) ++
    [ If (IsSome a) _then [ a' <$- A ]  ] 
   ]] E m2) (restr (EP k (IsSome a)) g))
   <= epsilon k.
 Proof.
  induction n; intros.
 
  (* base case *)
  unfold unroll_while.
  repeat rewrite deno_app_elim, deno_cond_elim.
  rewrite (@depend_only_fv_expr T.Bool cond _ m2 m1); 
   [ | refine (req_mem_weaken _ (req_mem_sym (proj1 H0))); apply eq_refl ].
  case_eq (E.eval_expr cond m1); intro Hcond; setoid_rewrite Hcond.
    (* cond *)
    transitivity (Uabs_diff
      (mu ([[ [  x <$- R; a <c- Invf with {x} ] ++ [a' <- Proj a] ]] E
        (m1 {!i <-- E.eval_expr (i +! 1%nat) m1!})) (restr (EP k (IsSome a)) f))
      (mu ([[ [x <$- R; a <c- Invf with {x} ] ++ [a' <$- A] ]] E 
        (m2 {!i <-- E.eval_expr (i +! 1%nat) m2!})) (restr (EP k (IsSome a)) g)));
    [ |  rewrite (Invf_output _ _ H); auto ].
    apply Oeq_le; apply Uabs_diff_morphism.

      rewrite deno_app_elim; elim_assign.
      rewrite deno_app_elim.
      apply mu_stable_eq; refine (ford_eq_intro _); intro m.
      unfold restr, EP; case_eq (@E.eval_expr _ T.Bool (IsSome a) m); intro Hguard.
      rewrite deno_cond_nil_elim, deno_cond_elim, Hguard; trivial.
      rewrite deno_assign_elim.
      setoid_rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ 
        (m {!a' <-- E.eval_expr (Proj a) m!}) m);
      [  rewrite Hguard | apply req_mem_sym; apply req_mem_upd_disjoint ]; trivial.
      rewrite deno_cond_nil_elim, deno_cond_elim, Hguard, deno_nil_elim, Hguard; trivial.

      rewrite deno_app_elim; elim_assign.
      rewrite deno_app_elim.
      apply mu_stable_eq; refine (ford_eq_intro _); intro m; unfold restr, EP.
      case_eq (@E.eval_expr _ T.Bool (IsSome a) m); intro Hguard.
      rewrite deno_cond_nil_elim, deno_cond_elim, Hguard; trivial.
      rewrite deno_cond_nil_elim, deno_cond_elim, Hguard, deno_nil_elim.
      rewrite deno_random_elim, Hguard.
      rewrite <- mu_0; apply mu_stable_eq; refine (ford_eq_intro _); intro v.
      rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ (m {!a' <-- v!}) m); 
        [ | apply req_mem_sym; apply req_mem_upd_disjoint ]; trivial.
      rewrite Hguard; trivial.
      
    (* ~cond *)
      repeat rewrite deno_nil_elim, deno_cond_elim.
      rewrite (@depend_only_fv_expr T.Bool  (IsSome a) _ m2 m1); 
        [ | refine (req_mem_weaken _ (req_mem_sym (proj1 H0))); apply eq_refl ].
      case_eq (@E.eval_expr _ T.Bool (IsSome a) m1); intro Hguard.
      (* case (IsSome a) *)
      generalize (proj2 H0) Hguard; expr_simpl; case (m1 a); discriminate.
      (* case ~(IsSome a) *)
      repeat rewrite deno_nil_elim.
      unfold restr, EP.
      rewrite (@depend_only_fv_expr T.Bool  (IsSome a) _ m2 m1); 
        [ | refine (req_mem_weaken _ (req_mem_sym (proj1 H0))); apply eq_refl ].
      rewrite Hguard, Uabs_diff_compat_eq; trivial.

  (* inductive case *)
  unfold unroll_while; fold (unroll_while cond 
   [i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ] (S n)).
  repeat rewrite deno_app_elim, deno_cond_elim.
  rewrite (@depend_only_fv_expr T.Bool cond _ m2 m1); 
   [ | refine (req_mem_weaken _ (req_mem_sym (proj1 H0))); apply eq_refl ].
  case_eq (E.eval_expr cond m1); intro Hcond; setoid_rewrite Hcond.

    (* cond *)
    repeat (rewrite deno_app_elim; elim_assign).
    match goal with |- Uabs_diff (fmonot (mu ?d) _) _ <= ?cte => 
      rewrite <-(@mu_cte_le _ d cte), (mu_restr_split d (EP k (IsSome a)) (fcte _ (epsilon k)))
    end.
    rewrite (mu_restr_split ([[ [x <$- R; a <c- Invf with {x} ] ]] E
      (m2 {!i<--E.eval_expr (i +! 1%nat) m2!})) (EP k (IsSome a))),
    (mu_restr_split ([[ [x <$- R; a <c- Invf with {x} ] ]] E
      (m1 {!i<--E.eval_expr (i +! 1%nat) m1!})) (EP k (IsSome a))).
    rewrite Uabs_diff_plus; apply Uplus_le_compat.

      (* IsSome a *)
      transitivity (Uabs_diff
        (mu ([[ [  x <$- R; a <c- Invf with {x} ] ++ [a' <- Proj a] ]] E
        (m1 {!i <-- E.eval_expr (i +! 1%nat) m1!})) (restr (EP k (IsSome a)) f))
        (mu ([[ [x <$- R; a <c- Invf with {x} ] ++ [a' <$- A] ]] E 
          (m2 {!i <-- E.eval_expr (i +! 1%nat) m2!})) (restr (EP k (IsSome a)) g))).
      apply Oeq_le; apply Uabs_diff_morphism.      

        rewrite deno_app_elim.
        apply mu_stable_eq; refine (ford_eq_intro _); intro m.
        unfold restr, EP; case_eq (@E.eval_expr _ T.Bool (IsSome a) m); intro Hguard.
          rewrite deno_unroll_while_false_elim; 
            [ | unfold cond; 
              rewrite eval_andb, eval_negb, Hguard, andb_false_r; trivial ].
          repeat rewrite deno_cond_elim; rewrite Hguard; trivial.
          rewrite deno_assign_elim.
          setoid_rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ 
            (m {!a' <-- E.eval_expr (Proj a) m!}) m);
          [ rewrite Hguard | apply req_mem_sym; apply req_mem_upd_disjoint ]; trivial.
     
        rewrite deno_app_elim.
        apply mu_stable_eq; refine (ford_eq_intro _); intro m; unfold restr, EP.
        case_eq (@E.eval_expr _ T.Bool (IsSome a) m); intro Hguard.
          rewrite deno_unroll_while_false_elim; [ | unfold cond;
            rewrite eval_andb, eval_negb, Hguard, andb_false_r; trivial ].
          rewrite deno_cond_elim, Hguard; trivial.
          repeat rewrite deno_random_elim.
          rewrite <- mu_0; apply mu_stable_eq; refine (ford_eq_intro _); intro v.
          rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ (m {!a' <-- v!}) m), Hguard; 
            [ | apply req_mem_sym; apply req_mem_upd_disjoint ]; trivial.

        rewrite Invf_output, mu_restr_cte; trivial; Usimpl.
        eapply EqObs_Pr with Vset.empty; deadcode i_EE; eqobs_in i_EE.

      (* ~ IsSome a *)
      match goal with |- Uabs_diff (fmonot (mu ?d1) ?f1) (fmonot (mu ?d2) ?f2) <= _ => 
        assert (Haux: mu d2 f2 == mu d1 f2) 
      end.
        apply equiv_deno with (kreq_mem {{a,i}}) (kreq_mem {{a,i}}).
          eqobs_in i_EE.
          intros m1' m2' H1m'; unfold restr, EP, negP, negb.
          rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ m2' m1'); 
            [ | refine (req_mem_weaken _ (req_mem_sym H1m')); apply eq_refl ].
          case (@E.eval_expr _ T.Bool (IsSome a) m1').
            trivial.
            apply equiv_deno with (kreq_mem {{a,i}}) (kreq_mem {{a,i}}); trivial.
              generalize (S n); clear IHn n; induction n.
                eqobs_in.
                unfold unroll_while; fold (unroll_while cond 
                  [i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ] n).
                apply equiv_cond.
                  apply equiv_app with (kreq_mem {{a, i}}); [ eqobs_in i_EE | apply IHn ].
                  eqobs_in i_EE.
                  intros; apply depend_only_fv_expr with (1:=H1).
              intros m1'' m2'' Hm''; clear m1' m2' H1m'.
              apply equiv_deno with (kreq_mem {{a,i}}) (req_mem_rel {{a,i}} 
                (fun k (m1 m2:Mem.t k) => EP k (IsSome a) m1 -> m1 a' = m2 a')); trivial.
                unfold EP; eqobsrel_tail; expr_simpl.
                intros k' m1' m2' Hm'; split.
                  intros _ v _ _; mem_upd_simpl.
                  case_eq (m1' a); intros; tauto.
                intros m1' m2' (H1m',H2m').
                rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ m2' m1'); 
                  [ | refine (req_mem_weaken _ (req_mem_sym H1m')); apply eq_refl ].
                case_eq (@E.eval_expr _ T.Bool (IsSome a) m1'); intro Hguard.
                  transitivity (f m1'); [ symmetry | ]; auto.
                  apply H; intros t x Hx; Vset_mem_inversion Hx; subst; apply (H2m' Hguard).
                  trivial.
              intros t x Hx; Vset_mem_inversion Hx; subst; mem_upd_simpl; symmetry.
                apply (proj1 H0 _ a); trivial.
                eapply depend_only_fv_expr_subset with (2:=proj1 H0); apply eq_refl.

      rewrite Haux, Uabs_diff_mu_compat; clear Haux.
      apply mu_monotonic; unfold fabs_diff, fcte; refine (ford_le_intro _); intro m.
      unfold restr, negP, negb.
      case_eq (EP k (IsSome a) m); intro Hguard.
        auto.
        repeat rewrite <-deno_app_elim; apply (IHn _ _ H).
        split; [ auto | unfold EP1, EP in *; rewrite eval_negb, Hguard; trivial ].

 
    (* ~cond *)
    repeat rewrite deno_nil_elim, deno_cond_elim.
    rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ m2 m1); 
      [ | refine (req_mem_weaken _ (req_mem_sym (proj1 H0))); apply eq_refl ].
    generalize (proj2 H0); unfold EP1, is_true.
    rewrite eval_negb, negb_true_iff; intro H0'; rewrite H0'.
    repeat rewrite deno_nil_elim.
    unfold restr, EP.
    rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ m2 m1); 
      [ | refine (req_mem_weaken _ (req_mem_sym (proj1 H0))); apply eq_refl ].
    rewrite H0', Uabs_diff_compat_eq; trivial.
 Qed.

 Lemma G4_G5: prg_SD 
  (kreq_mem Vset.empty) 
  E G4 E G5 
  (kreq_mem {{ret}}) 
  epsilon.
 Proof.
  intros k f g Hfg m1 m2 Hm.
  Opaque deno.
  set (G4' := 
   [ i <- 0%nat; a <- none _; p <- Pdef;  x <- Rdef; a' <- Adef;
     while cond do [i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ];
    If IsSome a _then [a' <- Proj a] ] ++
   [ p <$-P;
    If IsSome a
    then [ret <- some (a' | p)]
    else [ret <- none _]
   ]).
  set (G5' :=
   [ i <- 0%nat; a <- none _; p <- Pdef;  x <- Rdef; a' <- Adef;
    while cond do [i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ];
    If IsSome a _then [a' <$- A] ] ++
   [ p <$-P;
    If IsSome a
    then [ret <- some (a' | p)]
    else [ret <- none _]
   ]).
  transitivity (Uabs_diff (mu ([[G4']] E m1) g) (mu ([[G5']] E m2) f)).
  apply Uabs_diff_morphism.
    symmetry; apply equiv_deno with Meq (kreq_mem {{ret}});
      [ swap i_EE; eqobs_in i_EE | apply Hfg | trivial ].
   apply equiv_deno with Meq (kreq_mem {{ret}}); 
    [ deadcode i_EE; swap i_EE; eqobs_in i_EE | apply Hfg | trivial ].
  unfold G4', G5'.
  rewrite deno_app_elim, deno_app_elim. 
  repeat elim_assign; expr_simpl.
  match goal with |- Uabs_diff (fmonot (mu ([[ _ ]] _ ?m1'')) _)  (fmonot (mu ([[ _ ]] _ ?m2'')) _) <= _ => 
    set (m1':=m1''); set (m2':= m2'') 
  end.
  rewrite (mu_restr_split 
   ([[ [ while cond do [ i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ];
         If IsSome a _then [a' <- Proj a]
   ] ]] E m1') (EP k (IsSome a))), 
  (mu_restr_split ([[ 
   [  while cond do [ i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ];
     If IsSome a _then [a' <$- A]
   ] ]] E m2') (EP k (IsSome a))).
  rewrite <-(Uplus_zero_right (epsilon k)), Uabs_diff_plus.
  apply Uplus_le_compat.
  
    (* case [IsSome a] *)
    assert (aux: forall (m:Mem.t k) F,
      mu ([[  [ while cond do  
        [ i <- i +! 1%nat; x <$- R; a <c- Invf with {x} ] ] ]] E m) F ==
      mu ([[ unroll_while cond  [ i <- i +! 1%nat; x <$- R; a <c- Invf with {x} ]
        (E.eval_expr (TMax +! 1%nat -! i) m) ]] E m) F).
      intros.
      apply deno_bounded_while_elim with (TMax +! 1%nat -! i).
        intros k' m' Hm' f' H_f.
        elim_assign.
        rewrite (@Modify_deno_elim E {{a,x}} [x <$- R; a <c- Invf with {x} ]);
          [ | apply modify_correct with (refl1_info i_EE) Vset.empty; apply eq_refl ].
        match goal with |- _ == fmonot (mu ?d) _ => rewrite <-(mu_zero d) end.
        apply mu_stable_eq; unfold fzero; refine (ford_eq_intro _); intro m''.
        apply H_f.
        generalize Hm'; unfold cond, EP; clear Hm'.
        expr_simpl; mem_upd_simpl.
        rewrite is_true_andb; intros [Hm' _].
        apply leb_correct; apply leb_complete in Hm'; omega.
        intros m'; unfold cond; expr_simpl; intro H;
        rewrite leb_correct_conv, andb_false_l; [ trivial | omega ].
        trivial.
    rewrite (@deno_app_elim _ E [ while cond do [i <- i +! 1%nat; x <$- R; a <c- Invf with {x} ] ]
      [ If IsSome a _then [a' <- Proj a] ] ), aux,
      (@deno_app_elim _ E  
        [ while cond do [i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ] ] 
        [ If IsSome a _then [a' <$- A] ] ), aux, <-deno_app_elim, <-deno_app_elim.
    replace (E.eval_expr (TMax +! 1%nat -! i) m1') with (S (T_poly k)) by
      (unfold m1'; expr_simpl; omega).
    replace (E.eval_expr (TMax +! 1%nat -! i) m2') with (S (T_poly k)) by
      (unfold m2'; expr_simpl; omega).
    
    transitivity (Uabs_diff 
      (mu
        ([[unroll_while cond [i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ]
         (S (T_poly k)) ++ [If IsSome a _then [a' <- Proj a] ] ]] E m1')
        (restr (EP k (IsSome a)) (fun m' => mu ([[ [ p <$- P; ret <- some (a' | p) ] ]] E m') f)))  
      (mu ([[unroll_while cond [i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ]
        (S (T_poly k)) ++ [If IsSome a _then [a' <$- A] ] ]] E m2')
        (restr (EP k (IsSome a)) (fun m' => mu ([[ [ p <$- P; ret <- some (a' | p) ] ]] E m') g)))).
    apply Uabs_diff_morphism.
      apply mu_stable_eq; refine (ford_eq_intro _); intros m'.
      unfold restr, EP, charfun, restr.
      case_eq (@E.eval_expr k T.Bool (IsSome a) m'); intros.
        apply equiv_deno with (req_mem_rel {{a'}} (EP2 (IsSome a))) (kreq_mem {{ret}}).
          ep_eq_r (IsSome a) true.
            generalize H; expr_simpl; unfold req_mem_rel, andR; intuition.   
          eqobs_in.
          trivial.
          split; trivial.
        trivial.
      apply mu_stable_eq; refine (ford_eq_intro _); intros m'.
      unfold restr, EP, charfun, restr.
      case_eq (@E.eval_expr k T.Bool (IsSome a) m'); intros.
        apply equiv_deno with (req_mem_rel {{a'}} (EP2 (IsSome a))) (kreq_mem {{ret}}).
          ep_eq_r (IsSome a) true.
            generalize H; expr_simpl; unfold req_mem_rel, andR; intuition.   
          eqobs_in.
          intros; symmetry; auto.
          split; trivial.
        trivial.
  
    apply loop_unroll_distance.
      intros; apply EqObs_deno with {{a'}} {{ret}};
        [ eqobs_in i_EE | trivial | trivial ].
      split.
        intros t x Hx; Vset_mem_inversion Hx; subst; unfold m1', m2'; mem_upd_simpl.
        unfold m1', m2'; expr_simpl.

    (* case [~ IsSome a] *)
    apply Oeq_le; rewrite Uabs_diff_zero.
    apply equiv_deno with (kreq_mem {{i,a}}) (kreq_mem {{a}}).
      deadcode i_EE; eqobs_in i_EE.
       intros m1'' m2'' Hm''; unfold restr, negP, negb, EP.
      rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ m2'' m1''); 
        [ | exact (req_mem_sym Hm'') ]. 
      case_eq (@E.eval_expr _ T.Bool (IsSome a) m1''); intro Hguard.
        trivial.
        refine (@equiv_deno (req_mem_rel {{a}} (~-(EP1 (IsSome a))))
          _ _ _ _ (kreq_mem {{ret}}) _ _ _ _ _ _ _ _).
          cp_test (IsSome a).
            apply equiv_False; intros k' m1''' m2''' ((_,H1),(H2,_)); unfold notR in H1; tauto.
            eqobs_in.
          intros; symmetry; auto.
          split; [ trivial | unfold notR, EP1; rewrite Hguard; discriminate ].
      intros t x Hx; Vset_mem_inversion Hx; subst; unfold m1', m2'; mem_upd_simpl.
  Qed.
    

 (* **************************** 6th STEP **************************** *)
 (* 1) Assign [a'] a random value if inverter [Invf] fails in all the  *)
 (* iterations                                                         *)
 (******************************************************************** *)

 Definition G6 :=
  [
    i <- 0%nat; a <- none _; 
    p <- Pdef;  x <- Rdef; a' <- Adef;
    bad <- false;
    while cond do 
      [ 
        i <- i +! 1%nat;
        x <$- R;  
        a <c- Invf with {x}
      ] 
  ] ++ 
  [
    If (IsSome a) then [ a' <$- A ] else [ bad <- true; a' <$-A; a <- some Adef ];
    p <$- P;
    If (IsSome a) then [ ret <- some (a' | p) ] else [ ret <- none _ ]
  ].
 

 Lemma Invf_success : forall k (m:Mem.t k),
  one_over_alpha k <= 
  Pr E [ x <$- R; a <c- Invf with {x} ] m (EP k (IsSome a)).
 Proof.
  intros k m; rewrite (Invf_success_probability E0 m).
  apply EqObs_Pr with {{a,a'}}.
  eqobs_in i_EE'.
 Qed.

 Lemma loop_failure: forall n k (m:Mem.t k), 
  m bad = false ->
  n = (S (T_poly k) - (m i))%nat ->
  Pr E
  [
   while cond do [i <- i +! 1%nat; x <$- R; a <c- Invf with {x} ];
    If !(IsSome a) _then [bad <- true]
  ] m (EP k bad) <= (1 - one_over_alpha k) ^ n.
 Proof.
  unfold Pr; induction n; intros k m Hbad Hn.
  auto.
  rewrite deno_cons_elim, Mlet_simpl, deno_while_elim, deno_cond_elim.
  case_eq (@E.eval_expr _ T.Bool cond m); intro Hc.
  
  (* case [cond=true] *)
  rewrite deno_app_elim.
  rewrite (mu_restr_split _ (fun m' => EP k (IsSome a) m')).
  match goal with |- ?X' + _ <= _ => assert (X'==0) end.
  rewrite (@Modify_deno_elim E {{a,x,i}} 
   [i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ]); 
  [ | apply modify_correct with (refl1_info i_EE) Vset.empty; apply eq_refl ].
  match goal with |- fmonot (mu ?d) _ == 0 => rewrite <-(mu_zero d) end.
  apply mu_stable_eq; unfold fzero, restr; refine (ford_eq_intro _); intro m'.
  case_eq (EP k (IsSome a) (m {!{{a, x, i}} <<- m'!})); unfold EP; intro Heq.
  rewrite deno_while_elim, deno_cond_elim.
  replace (@E.eval_expr _ T.Bool cond (m {!{{a, x, i}} <<- m'!})) with false 
   by (unfold cond; rewrite eval_andb, eval_negb, Heq, andb_false_r; trivial).
  rewrite deno_nil_elim, deno_cond_elim, eval_negb, Heq;
   unfold negb, charfun, restr; rewrite deno_nil_elim;simpl;
    mem_upd_simpl; rewrite Hbad; trivial.
  trivial.
  rewrite H; Usimpl.
  transitivity  (mu ([[ [i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ] ]]
   E m) (restr (negP (fun m' => EP k (IsSome a) m')) (fcte _ ((1 - one_over_alpha k) ^ n)))).
       
  (*  *)
  apply range_le with (P:=fun m':Mem.t k =>  n = (S (T_poly k) - m' i)%nat /\ m' bad = false).
  intros f H_f.
  elim_assign.
  rewrite (@Modify_deno_elim E {{a,x}} [x <$-R; a <c- Invf with {x} ]); 
   [ | apply modify_correct with (refl1_info i_EE) Vset.empty; apply eq_refl ].
  match goal with |- _ == fmonot (mu ?d) _ => rewrite <-(mu_zero d) end.
  apply mu_stable_eq; unfold fzero; refine (ford_eq_intro _); intro m'.
  apply H_f; split.
  generalize Hc; unfold cond; clear Hc.
  rewrite eval_andb, (is_true_andb (E.eval_expr (i <=! TMax) m) 
   (E.eval_expr (!(IsSome a)) m)).
  rewrite update_mem_notin, Mem.get_upd_same; [ | discriminate ]; 
   change (E.eval_expr (i +! 1%nat) m) with (m i + 1)%nat.
  intros [Hm _]; apply (leb_complete (m i) (T_poly k)) in Hm.
  omega.
  rewrite update_mem_notin; mem_upd_simpl; discriminate. 
  intros m' [Hn' Hbad']; unfold restr, negP, negb.
  case_eq (EP k (IsSome a) m'); unfold EP; intro Heq.
  trivial.
  rewrite <-Mlet_simpl, <-deno_cons_elim; apply IHn; assumption.
  (*  *)
  rewrite mu_restr_cte, (Umult_sym (1-one_over_alpha k) ((1 - one_over_alpha k)^n)); Usimpl.
  rewrite Uminus_one_left, <- (Uinv_le_compat _ _ (Invf_success m)).
  rewrite (@Pr_neg _ E [i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ] m 
   (fun m' : Mem.t k => EP k (IsSome a) m'));
  [ |  apply is_lossless_correct with (refl2_info i_EE); apply eq_refl ].
  Usimpl.
  unfold Pr; apply Oeq_le; apply EqObs_deno_same with Vset.empty (fv_expr (IsSome a)).
  deadcode i_EE; eqobs_in i_EE.
  unfold  negP, charfun, restr, EP, fone; intros m1 m2 Hm.
  rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ _ _ Hm); trivial.
  (* case [cond=false] *)
  rewrite deno_nil_elim, deno_cond_elim.
  replace (@E.eval_expr _ T.Bool (!(IsSome a)) m) with false.
  rewrite deno_nil_elim.
  unfold charfun, restr, EP; simpl; rewrite Hbad; trivial.
  generalize Hc; unfold cond; simpl; unfold O.eval_op; simpl.
  replace (leb (m i) (T_poly k)) with true by 
   (symmetry; apply leb_correct; omega).
  auto.
 Qed.


 Definition i_EE_upto: upto_info bad E E.
  apply add_upto_info' with (f:=Invf) (X:=Invf_X); trivial.
  apply Invf_Modify.
  apply Invf_Modify.
  apply Invf_X_local.
  exact (empty_upto_info bad E E).
 Defined.


 Lemma G5_G6: prg_SD (kreq_mem Vset.empty) E G5 E G6 (kreq_mem {{ret}}) 
  (fun k => (1 - one_over_alpha k)^(S (T_poly k))).
 Proof.
  apply prg_SD_Meq_pre_weaken.
    Focus 2.
    unfold prg_SD; intros. 
    unfold fzero; apply Oeq_le; rewrite Uabs_diff_zero.
    apply equiv_deno with Meq (kreq_mem {{ret}}); trivial; eqobs_in i_EE.
    Focus 2.
    unfold prg_SD; intros. 
    unfold fzero; apply Oeq_le; rewrite Uabs_diff_zero.
    apply equiv_deno with (kreq_mem Vset.empty) (kreq_mem {{ret}}); trivial.
    eqobs_in i_EE.
    2:trivial.

  apply prg_SD_weaken with Meq (kreq_mem {{ret}})
   (fplus (fun k : nat => (1 - one_over_alpha k) ^ S (T_poly k)) (fzero _));
   [ | | unfold fplus, fzero | ];  auto.
  rewrite <- (firstn_skipn 8 G5), <- (firstn_skipn 8 G6).
  apply prg_SD_seq_Meq; simpl firstn; simpl skipn.
  rewrite <-rtriple_deno.
  intros k m f.
  repeat elim_assign.
  match goal with |- Uabs_diff (fmonot (mu ([[ _ ]] _ ?m'')) _) _ <= _ => 
   set (m':=m''); simpl in m'; unfold O.eval_op in m'; simpl in m' end.
  rewrite (@upto_bad_GSD _ _ _  bad is_true_true i_EE_upto); 
   [ | apply eq_refl | ].
  apply Ole_eq_left with  (Pr E [ while cond do 
   [i <- i +! 1%nat; x <$-R; a <c- Invf with {x} ];
   If !IsSome a _then  [bad <- true] ] m' (EP k bad)).
  apply EqObs_Pr with {{bad,i,a,a'}}.
  deadcode i_EE; eqobs_hd i_EE; cp_test (IsSome a); eqobs_in.

  apply loop_failure; unfold m'; mem_upd_simpl.
  apply lossless_cons.
  apply G5_loop_lossless.
  apply is_lossless_correct with (refl2_info i_EE); apply eq_refl.

  unfold prg_SD; intros. 
  unfold fzero; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with Meq (kreq_mem {{ret}}); trivial; eqobs_in.
 Qed.


 (* **************************** 7th STEP **************************** *)
 (* 1) Remove deadcode                                                 *)
 (******************************************************************** *)

 Lemma G6_Gf: EqObs Vset.empty E G6 E Gf {{ret}}.
 Proof.
  unfold G6, Gf.
  apply equiv_app with (c3:=@nil I.instr) (c4:=Gf) (Q:=trueR).
  apply equiv_True.
  rewrite <-(firstn_skipn 6); apply lossless_app; simpl.
  apply is_lossless_correct with (refl2_info i_EE); apply eq_refl.
  apply G5_loop_lossless.
  apply lossless_nil.
  cp_test_l (IsSome a).
  cp_test_r (IsSome a); apply equiv_strengthen 
   with (kreq_mem Vset.empty); try (intros; apply req_mem_empty).
  eqobs_in.
  eqobs_in.

  deadcode.
  cp_test_l (IsSome (some Adef)).
  apply equiv_strengthen with (kreq_mem Vset.empty); 
   try (intros; apply req_mem_empty).
  eqobs_in.
  apply equiv_False.
  intros k m1 m2 (_,H); generalize H.
  unfold notR, EP1; simpl; unfold O.eval_op; simpl; auto.
 Qed.



 (* When given a random input, [InvF]'s output is at distance
   [epsilon + (1-1/alpha)^Tmax] from the uniform distritubion *)
 Lemma Inv_F_distance_from_random: 
  prg_SD (kreq_mem Vset.empty) E Gi E Gf (kreq_mem {{ret}})  
   (fun k => epsilon k + (1 - one_over_alpha k)^(S (T_poly k))).
 Proof.
  set (F:= fplus epsilon (fun k => (1 - one_over_alpha k)^(S (T_poly k)))).
  change (fun k : nat =>  epsilon k + (1 - one_over_alpha k) ^ S (T_poly k)) with F.

  rewrite <- (fplus_fzero_l F).
  apply prg_SD_trans_PER with E G1; try apply req_mem_PER.
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.

  transitivity (mu ([[G1]] E m2) g).
  symmetry; apply equiv_deno with (1:=G1_Gi).
  intros; symmetry; apply H;
   apply req_mem_sym; apply req_mem_weaken with (2:=H1); apply eq_refl.
  apply req_mem_empty.

  eapply EqObs_deno with Vset.empty {{ret}}.
  eqobs_in i_EE.
  intros; transitivity (f m3); intuition.
  symmetry; auto.
  auto.
  
  rewrite <-(fplus_fzero_l F).
  apply prg_SD_trans_PER with E G2; try apply req_mem_PER. 
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.

  transitivity (mu ([[G1]] E m1) f).
  symmetry; apply EqObs_deno with Vset.empty {{ret}}.
  eqobs_in i_EE.
  intros; transitivity (g m0); intuition.
  symmetry; auto.
  auto.

  apply equiv_deno with (1:=G1_G2).
  intros; apply H; apply req_mem_weaken with (2:=H1); apply eq_refl.
  apply req_mem_empty.
  rewrite <-(fplus_fzero_l F).
  apply prg_SD_trans_PER with E G3; try apply req_mem_PER.
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.

  apply equiv_deno with (1:=G2_G3).
  intros; apply H; apply req_mem_weaken with (2:=H1); apply eq_refl.
  apply req_mem_empty.
  rewrite <-(fplus_fzero_l F).
  apply prg_SD_trans_PER with E G4; try apply req_mem_PER.

  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with (1:=G3_G4); trivial; apply req_mem_empty.


  apply prg_SD_trans_PER with (3:=G4_G5); try apply req_mem_PER.
  rewrite <-(fplus_fzero_r  (fun k => (1 - one_over_alpha k)^(S (T_poly k)))).
  apply prg_SD_trans_PER with (3:=G5_G6); try apply req_mem_PER.

  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with (1:=G6_Gf); trivial; apply req_mem_empty.
 Qed.

 Lemma Invf_partial : forall k (m:Mem.t k),
  range (EP k ((IsSome a) ==> (x =?= f_ (Proj a)))) 
  ([[ [x <$- R; a <c- Invf with {x} ] ]] E m).
 Proof.
  intros.
  apply mu_range.
  transitivity (mu ([[ [x <$-R; a <c- Invf with {x} ] ]] (E' E0) m)
     (fun m => if EP k ((IsSome a) ==> (x =?= f_ (Proj a))) m then 1 else 0)).
  apply EqObs_deno with Vset.empty {{a,x}}; trivial.
  eqobs_in i_EE'.
  intros.
  unfold EP; simpl; unfold O.eval_op; simpl; rewrite (H _ a), (H _ x); trivial.  
  rewrite range_mu; [ | apply Invf_partial_inverter].
  apply is_lossless_correct with (refl2_info i_EE').
  vm_compute; trivial.
 Qed.


 (* REMARK: this condition is equivalent to the one given in the paper *)
 Lemma InvF_is_partial_inverter : forall k (m:Mem.t k),
  range (fun m' => 
   EP k ((IsSome ret) ==> (r =?= (Esnd (Proj ret)) |-->| f_ (Efst (Proj ret)))) m')
  ([[ Gi ]] E m).
 Proof.
  intros k m.
  apply mu_range.
  change (Pr E Gi m (EP k ((IsSome ret) ==> 
    (r =?= (Esnd (Proj ret)) |-->| f_ (Efst (Proj ret))))) == 1).
  transitivity  (Pr E G1 m (EP k ((IsSome ret) ==> 
    (r =?= (Esnd (Proj ret)) |-->| f_ (Efst (Proj ret))))) ).
  symmetry.
  apply EqObs_Pr2 with (1:=G1_Gi); [ apply eq_refl | auto ].
  transitivity  (Pr E G2 m (EP k ((IsSome ret) ==> 
    (r =?= (Esnd (Proj ret)) |-->| f_ (Efst (Proj ret)))))).
  apply EqObs_Pr2 with (1:=G1_G2); [ apply eq_refl | auto ].
  transitivity  (Pr E G3 m (EP k ((IsSome ret) ==> 
    (r =?= (Esnd (Proj ret)) |-->| f_ (Efst (Proj ret)))))).
  apply EqObs_Pr2 with (1:=G2_G3); [ apply eq_refl | auto ].
  assert (lossless E G3).
  apply lossless_app; [ | apply lossless_app ].
  apply is_lossless_correct with (refl1_info i_EE); vm_compute; trivial.
  apply lossless_cons; [ apply G5_loop_lossless | apply lossless_assign ].
  apply is_lossless_correct with (refl1_info i_EE); vm_compute; trivial.
  rewrite <-(H _ m).
  apply equiv_deno with (kreq_mem Vset.empty) (req_mem_rel Vset.empty (EP1
    ((IsSome ret) ==> (r =?= (Esnd (Proj ret)) |-->| f_ (Efst (Proj ret)))))).
  unfold G3.
  apply equiv_app with 
   (req_mem_rel {{i,x,a}} (EP1 ((IsSome a) ==> (x  =?= f_ (Proj a))))).
  eqobsrel_tail; expr_simpl; intros ? _ _ _ _ _; trivial.
  eapply equiv_cons; [ apply equiv_while | ].
  intros k' m1' m2' (H1,_). 
  apply depend_only_fv_expr_subset with (2:=H1); apply eq_refl.
  apply equiv_strengthen_range.
          
  auto.
  apply is_lossless_correct with (refl1_info i_EE); vm_compute; trivial.
  intros; apply mu_range.
  transitivity (Pr E [x <$- R; a <c- Invf with {x} ] m0 
   (EP k0 ((IsSome a) ==> (x =?= f_ (Proj a))) )); symmetry.
  apply EqObs_Pr with (Vset.empty); deadcode i_EE; eqobs_in i_EE.
  assert (Hloss: lossless E [x <$- R; a <c- Invf with {x} ]) by
   (apply is_lossless_correct with (refl1_info i_EE); vm_compute; trivial).
  rewrite <- (Hloss _ m0); symmetry.
  apply range_mu; apply Invf_partial.    
  eqobs_in i_EE.
  eqobsrel_tail; expr_simpl.
  intros k' m1' m2'; case_eq (m1' a). 
  intros v Hv (H1',(H2',(H3',H4'))); split; intros; split; intros; trivial.
    rewrite is_true_impb in H2'; generalize (H2' is_true_true); clear H2';
      rewrite (@is_true_Ti_eqb k' (T.User R_) (m1' x) (ENC.f_def v)); intro H2'.
    rewrite <-H2', PAD.padinv_unpad.
    setoid_rewrite (@Ti_eqb_refl k' (T.User R_) (m1' r)); trivial.
    destruct H0; apply not_true_is_false in H0; discriminate.
    intros Ha (H1',(H2',(H3',H4'))); split; intros; split; intros; trivial.
    destruct H0; discriminate H0.
    destruct H1; discriminate H1.

  unfold EP1, charfun, restr, EP; intros m1 m2 (_,H'); rewrite H'; trivial.
  auto.
 Qed.


 (* *********************************************************************** *)
 (* ******************************  CLAIM 3  ****************************** *)
 (* Let [F : A x P -> R] as above definded be an epsilon'-admissible        *)
 (* encoding v2 with [epsilon' =  epsilon + (1 - 1/alpha)^Tmax] and let     *)
 (* [H : M -> A x P] be a random oracle. Then [F o H] is [(q, 2 q epsilon')]*)
 (* -indifferentiable from a random oracle into [R].                        *)  
 (* *********************************************************************** *)

 Lemma Invf_eq_sem: forall E1 E2,
  equiv Meq E1 Invf_body E2 Invf_body (kreq_mem Invf_X).
 Proof.
  intros.
  eapply equiv_strengthen; [ | apply Invf_eqobs ]. 
  intros; rewrite H; trivial.
 Qed.

 Definition Hi :=
  [ 
   a' <$- A; 
   p <$- P;
   ret <- some (a'|p); 
   r <- p |-->| f_ a'
  ].
 
 Definition Hf := 
  [ 
   r <$- R; 
   ret <c- InvF with {r}; 
   a' <- Efst (Proj ret); 
   p <- Esnd (Proj ret) 
  ].


 Lemma lossless_InvF_in_rnd: forall E,
  proc_body E InvF = InvF_body ->
  Modify E {{a}} [a <c- Invf with {x} ] ->
  lossless E [a <c- Invf with {x} ] ->
  lossless E [ r <$- R; ret <c- InvF with {r} ].
 Proof.
  intros.
  apply lossless_cons; [ apply lossless_random | ].
  apply lossless_call; rewrite H.
  unfold InvF_body.
  match goal with 
   |- lossless E1 [?i1;?i2;?i3;?i4;?i5;?i6;?i7;?i8] => 
    change  [i1;i2;i3;i4;i5;i6;i7;i8] with ([i1;i2;i3;i4;i5] ++ ([i6] ++ [i7;i8]))
  end.
  apply lossless_app; [ | apply lossless_app ].
  apply is_lossless_correct with (refl1_info (empty_info E1 E1)); vm_compute; trivial.
  change [p <$-P; x <- p |+->| InvF_in; a <c- Invf with {x} ] with 
    ([p <$-P; x <- p |+->| InvF_in] ++ [a <c- Invf with {x} ]).
  apply loop_lossless with (Vset.union {{x,p}} {{a}}).
    apply Modify_app.
      apply modify_correct with (refl1_info (empty_info E1 E1)) Vset.empty; apply eq_refl.
      trivial.
    apply eq_refl.
    apply lossless_app.
      apply is_lossless_correct with (refl2_info (empty_info E1 E1)); apply eq_refl.   
      trivial.
    apply is_lossless_correct with (refl2_info (empty_info E1 E1)); apply eq_refl.   
 Qed.


 Lemma lossless_InvF_in_rnd_E: lossless E [ r <$- R; ret <c- InvF with {r} ].
 Proof.
  apply lossless_InvF_in_rnd.
    apply eq_refl.
    apply modify_correct with (refl1_info i_EE) Vset.empty; apply eq_refl.
    apply is_lossless_correct with (refl2_info i_EE); apply eq_refl.
 Qed.



 (* ******************************  CLAIM 3.1****************************** *)
 (* Let [F] be an [epsilon]-admissible enconding v2, with inverter [InvF].  *)
 (* Then the probability that [InvF] fails to invert a uniformly chosen     *)
 (* value is upper bounded by [epsilon]                                     *)
 (* *********************************************************************** *)
 
 Lemma Pr_InvF_failure : forall k (m:Mem.t k), 
  Pr E [ r <$- R; ret <c- InvF with {r} ] m (EP k (!(IsSome ret))) <= 
  epsilon k + (1 - one_over_alpha k)^(S (T_poly k)).
 Proof.
  intros.
  transitivity 
   (Pr E [ r <$- R; ret <c- InvF with {r} ] m (negP (EP k (IsSome ret)))); 
   [ trivial | ].
  rewrite Pr_neg; [rewrite <- Uminus_one_left | apply lossless_InvF_in_rnd_E].
  assert 
   (H:Pr E [a' <$- A; p <$- P; ret <- some (a'|p)] m
    (EP k (IsSome ret)) == 1).
  assert (Hloss: lossless E [a' <$-A; p <$- P; ret <- some (a' | p)]) by
   (apply is_lossless_correct with (refl1_info i_EE); vm_compute; trivial).
  rewrite <-(Hloss _ m).
  apply equiv_deno with Meq (req_mem_rel Vset.empty (EP1 (IsSome ret))).
  eqobsrel_tail; expr_simpl; intros _ _ _ _ _ _ _ _; trivial.
  unfold EP1, charfun, restr, EP; intros  m1 m2 (_,H); rewrite H; trivial.
  trivial.
  rewrite (Uminus_triangle_ineq2 _ _ 
   (Pr E [ a' <$- A; p <$- P; ret <- some (a'|p)] m (EP k (IsSome ret))));
  trivial.
  rewrite H, Uminus_eq, Uplus_zero_right,<-H; rewrite H at 2.
  match goal with 
   |- ?x - ?y <= _ => 
    transitivity (Uabs_diff y x); [ unfold Uabs_diff; auto | ] 
  end.
  apply Inv_F_distance_from_random.
  intros m1 m2 H'; unfold charfun, restr, EP.
  rewrite (@depend_only_fv_expr T.Bool (IsSome ret) _ m1 m2); [ | apply H' ].
  case_eq (@E.eval_expr _ T.Bool (IsSome ret) m2); trivial.
  apply req_mem_empty.
  rewrite H; trivial.
 Qed.


 (* ******************************  CLAIM 3.2 ***************************** *)
 (* Let [F] be an [epsilon]-admissible enconding v2, with inverter [InvF].  *)
 (* Then, [prg_SD {{ }} Hi Hf {{r,a,a'}} (2*epsilon)].                      *)
 (* This corresponds to [Lemma 2] in Section 3.1 of the paper               *)
 (* *********************************************************************** *)

 (* Augment [Hi] with some dead code *)
 Let H_1 := 
  [ a' <$- A; p <$- P; ret <- some (a'|p) ] ++
  [
   bad <- false;
   If !(IsSome ret) then
    [ bad <- true; r <$- R; a' <- Efst (Proj ret); p <- Esnd (Proj ret) ]
   else
    [ a' <- Efst (Proj ret); p <- Esnd (Proj ret);   r <- p |-->| f_ a'  ]
  ].

 Lemma Hi_H1: EqObs Vset.empty E Hi E H_1 {{r,ret,a',p}}.
 Proof.
  unfold Hi, H_1.
  apply EqObs_trans with E [ a' <$- A; p <$- P; ret <- some (a'|p); 
   a' <- Efst (Proj ret); p <- Esnd (Proj ret); r <- p |-->| f_ a' ].
  apply equiv_app with 
   (Q :=req_mem_rel {{ret,a',p}} (EP2 (a' =?=  Efst (Proj ret)) /-\ EP2 (p =?= Esnd (Proj ret))))
   (c1:=[a' <$-A; p <$- P; ret <- some (a'|p)]) (c2:=[ r <- p |-->| f_ a' ]) 
   (c3:=[a' <$-A; p <$- P; ret <- some (a'|p)]) (c4:=[ a' <- Efst (Proj ret); p <- Esnd (Proj ret);  r <- p |-->| f_ a' ]).
    deadcode; unfold Hi; eqobsrel_tail; simpl; unfold O.eval_op, implMR; simpl; 
    intros; split;  [ apply (@Ti_eqb_refl k (T.User A_)) | apply (@Ti_eqb_refl k (T.User P_)) ].
  eqobs_tl.
  apply equiv_app with 
   (Q :=req_mem_rel {{ret,a',p}} (EP2 (p =?= Esnd (Proj ret))))
   (c1:= @nil I.instr) (c2:=@nil I.instr) 
   (c3:=[a' <- Efst (Proj ret)]) (c4:=[ p <- Esnd (Proj ret) ]).
  eapply equiv_strengthen; [ | apply equiv_assign_r ].     
  intros k m1 m2 (H1,(H2,H3)); split.
  intros t x Hx; Vset_mem_inversion Hx; subst; mem_upd_simpl; try (apply H1; trivial).
  rewrite <- (proj2 (expr_eval_eq m2 a' (Efst (Proj ret))) H2); apply H1; trivial.
  expr_simpl.
  eapply equiv_strengthen; [ | apply equiv_assign_r ].     
  intros k m1 m2 (H1,H2); 
   change (kreq_mem {{ret,a',p}} m1 (m2 {!p <-- E.eval_expr Esnd (Proj ret) m2!})).
  intros t x Hx; Vset_mem_inversion Hx; subst;  mem_upd_simpl; try (apply H1; trivial).
  setoid_rewrite <- (proj2 (expr_eval_eq m2 p (Esnd (Proj ret))) H2); apply H1; trivial.
  deadcode.
  apply equiv_app with 
   (c1:= [ a' <$- A; p <$- P; ret <- some (a'|p) ]) 
   (c2 := [ a' <- Efst (Proj ret); p <- Esnd (Proj ret);  r <- p |-->| f_ a' ])
   (c3:= [ a' <$- A; p <$- P; ret <- some (a'|p) ]) 
   (c4 := [ If !(IsSome ret)
    then [r <$- R; a' <- Efst (Proj ret); p <- Esnd (Proj ret)]
    else [ a' <- Efst (Proj ret); p <- Esnd (Proj ret);  r <- p |-->| f_ a' ] ])
   (Q :=req_mem_rel {{ret, a',p}} (EP2 (IsSome ret))).
  eqobsrel_tail; simpl; unfold O.eval_op, implMR; simpl; intros; split; trivial.
  cp_test (IsSome ret).
  deadcode; eqobs_in.
  apply equiv_False; unfold notR; intros k m1 m2 [ [_ H]  [_ H'] ]; tauto.    
 Qed.
      

 (* Use the fact that [f] is a weak encoding --lossy transformation-- *)
 Let H_2 := 
  [ r <$- R; ret <c- InvF with {r} ] ++
  [
   bad <- false;
   If !(IsSome ret) then
    [ bad <- true; r <$- R;  a' <- Efst (Proj ret); p <- Esnd (Proj ret) ]
   else
    [ a' <- Efst (Proj ret); p <- Esnd (Proj ret);  r <- p |-->| f_ a' ]
  ].

 Lemma H1_H2: prg_SD 
  (kreq_mem Vset.empty) 
  E H_1 
  E H_2 
  (kreq_mem {{r,ret,a',p}})
  (fun k : nat => epsilon k + (1 - one_over_alpha k)^S (T_poly k)).
 Proof.
  unfold H_1, H_2, prg_SD; intros.
  repeat rewrite deno_app_elim.
  rewrite Uabs_diff_sym.
  apply Inv_F_distance_from_random.
  intros m1' m2' Hm'.
  apply equiv_deno with (kreq_mem {{ret}}) (kreq_mem {{r, ret, a',p}}).
  deadcode; cp_test (IsSome ret); eqobs_in.
  intros m1'' m2'' Hm''; symmetry; apply (H _ _ (req_mem_sym Hm'')). 
  trivial.
  apply req_mem_empty.
 Qed.
        

 (* Eliminate the resampling of [r] when the adversary fails 
    --lossy transformation-- *)
 Let H_3 := 
  [ r <$- R; ret <c- InvF with {r} ] ++
  [
   bad <- false;
   If !(IsSome ret) then
    [ bad <- true;  a' <- Efst (Proj ret); p <- Esnd (Proj ret) ] 
   else
    [ a' <- Efst (Proj ret); p <- Esnd (Proj ret);  r <- p |-->| f_ a' ]
  ].


 Lemma H2_H3: forall k,
  @rtriple k E E H_2 H_3 (fun _ => epsilon k + (1 - one_over_alpha k) ^ S (T_poly k)).  
 Proof.
  intros k; unfold H_2, H_3.
  apply rtriple_weaken with 
   (fun m => Pr E [r <$- R; ret <c- InvF with {r} ] m (EP k (!(IsSome ret))) + (fzero _) m).
  unfold fzero; refine (ford_le_intro _); intro m; Usimpl; apply Pr_InvF_failure.  
  apply rtriple_app.
  apply rtriple_refl_zero.
  intros m f.
  repeat elim_assign; simpl (m {!bad <-- E.eval_expr false m!}).
  rewrite (@upto_bad_GSD _ E E bad is_true_true ( empty_upto_info bad E E)); [ | apply eq_refl |
   apply is_lossless_correct with (pi := refl2_info i_EE); apply eq_refl ].
  unfold Pr, EP, charfun, restr; rewrite deno_cond_elim.
  rewrite (@depend_only_fv_expr T.Bool (!(IsSome ret)) _ m (m {!bad <-- false!})); 
   [ | apply req_mem_upd_disjoint; trivial ].
  case_eq (@E.eval_expr _ T.Bool (!(IsSome ret)) (m {!bad <-- false!})); intro Heq.
  trivial.
  repeat elim_assign; rewrite deno_nil_elim; expr_simpl.
 Qed.


 Lemma H3_Hf: EqObs Vset.empty E H_3 E Hf {{r,ret,a',p}}.
 Proof.
  unfold H_3, Hf, app.
  apply equiv_weaken with (kreq_mem {{a',p,r,ret}}).
  apply (@implMR_kreq_mem_subset {{a',p,r,ret}} {{r,ret,a',p}}); apply eq_refl.
  deadcode i_EE.
  apply equiv_app with
   (c1:=[r <$- R; ret <c- InvF with {r} ]) 
   (c2:=[ If !(IsSome ret) 
    then [ a' <- Efst (Proj ret); p <- Esnd (Proj ret)]
    else [ a' <- Efst (Proj ret); p <- Esnd (Proj ret);  r <- p |-->| f_ a' ] ])
   (c3:= [r <$- R; ret <c- InvF with {r} ]) 
   (c4:=[  a' <- Efst (Proj ret); p <- Esnd (Proj ret) ])
   (Q:= req_mem_rel {{ret,r}} (EP1  ((IsSome ret) ==> 
     (r =?= (Esnd (Proj ret)) |-->| f_ (Efst (Proj ret)))))).
  apply equiv_strengthen_range.
  auto.
  apply lossless_InvF_in_rnd_E.
  apply InvF_is_partial_inverter.
  eqobs_in i_EE.
  cp_test_l (IsSome ret).
  (* case [IsSome ret] *)
  apply equiv_app with
   (c1:= [a' <- Efst (Proj ret); p <- Esnd (Proj ret)]) 
   (c2:= [ r <-  Esnd (Proj ret) |-->| f_ (Efst (Proj ret)) ])
   (c3:= [a' <- Efst (Proj ret); p <- Esnd (Proj ret)])    
   (c4:= @nil I.instr)
   (Q:= req_mem_rel {{a',p,r, ret}} (EP1 ((IsSome ret) ==> 
    (r =?=  (Esnd (Proj ret)) |-->| f_ (Efst (Proj ret))))  /-\ EP1 (IsSome ret))).
  eqobsrel_tail; expr_simpl; intros k m1 m2 (H1,(H2,H3)); split; trivial.
  eapply equiv_strengthen; [ | apply equiv_assign_l ].
  intros k m1 m2 (H,(H',H'')).
  intros t x Hx; Vset_mem_inversion Hx; subst; mem_upd_simpl; (try apply H; trivial).
  rewrite <-(proj2 (expr_eval_eq m1 r (Esnd (Proj ret) |-->| (f_ Efst (Proj ret))))
   (expr_modus_ponens _ _ _ H' H'')); apply H; trivial.
  (* case [!IsSome a] *)
  unfold req_mem_rel; repeat rewrite proj1_MR; eqobs_in.
 Qed.


 Lemma Hi_Hf :
  prg_SD (kreq_mem Vset.empty) E Hi E Hf (kreq_mem {{r,ret,a',p}}) 
  (fplus (fun k => epsilon k + (1 - one_over_alpha k)^S (T_poly k)) 
         (fun k => epsilon k + (1 - one_over_alpha k)^S (T_poly k))).
 Proof.
  rewrite <-(fplus_fzero_l (fplus _ _)).
  apply prg_SD_trans_PER with E H_1; try apply req_mem_PER.
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with (1:=Hi_H1); trivial; apply req_mem_empty.

  apply prg_SD_trans_PER with E H_2; try apply req_mem_PER.
  apply H1_H2.
    
  rewrite <-(fplus_fzero_r (fun k : nat => epsilon k + (1 - one_over_alpha k) ^ S (T_poly k))).
  apply prg_SD_trans_PER with E H_3; try apply req_mem_PER.

  rewrite <-(fplus_fzero_l (fun k : nat => epsilon k + (1 - one_over_alpha k) ^ S (T_poly k))).
  apply prg_trans_Meq_Meq.
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with (kreq_mem Vset.empty) (kreq_mem {{r, ret, a', p}}); auto.
  eqobs_in i_EE.
  apply rtriple_deno; exact H2_H3.  
  
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with (1:=H3_Hf); trivial; apply req_mem_empty.
 Qed.
   

 Theorem Hi_Hf_Meq: forall k, 
  @rtriple k E E Hi Hf (fun _ => 2 */ (epsilon k + (1 - one_over_alpha k)^S (T_poly k))).
 Proof.
  intros k m f.
  rewrite (@Modify_deno_elim E {{r,ret,p,a'}} Hi); 
   [ | apply modify_correct with (refl1_info i_EE) Vset.empty; apply eq_refl ].
  rewrite (@Modify_deno_elim E {{p,a',ret,r}} Hf); 
   [ | apply modify_correct with (refl1_info i_EE) Vset.empty; apply eq_refl ].
  apply Hi_Hf.
  intros m1 m2 Hm.
  assert (Meq _ (m {!{{r, ret,p, a'}} <<- m1!}) (m {!{{p,a',ret,r}} <<- m2!})).
  assert ({{r, ret,p, a'}} [=] {{p,a',ret,r}}) by (apply eq_refl).
  apply Mem.eq_leibniz; red; intros [t v].
  case_eq (Vset.mem v {{r, ret, p, a'}}); intro Hv.
  rewrite update_mem_in, update_mem_in; [ | rewrite <-H | ]; trivial.
  apply Hm; apply Vset.subset_correct with (2:=Hv); apply eq_refl.
  rewrite update_mem_notin, update_mem_notin; [ | rewrite <-H | ]; trivial.
  rewrite Hv; discriminate.
  rewrite Hv; discriminate.
  rewrite H; trivial.
  trivial.
 Qed.



 (* ******************************  CLAIM 3.3 ****************************** *)
 (* Let [F:A * Z -> G] be an epsilon-admissible enconding v2, with           *)
 (* inverter algorithm [InvF]. Then, an adversary making at most [q] queries *) 
 (* can tell appart [Hi] from [Hf] with probability at most [2q epsilon].    *)
 (****************************************************************************)

 Section ADVERSARY.

  Definition H_args : var_decl (Proc.targs H) := dcons _ m' (dnil _).
  Definition H_res := L[{m'}].

  (* Adversary declaration *)
  Definition A_args : var_decl (Proc.targs A) := dnil _.
  Variable A_res : E.expr T.Bool.
  Variable A_body : cmd.

  (* Resulting enviromnets contain info about [InvF], [H] and [A] *)
  Definition mkEnvA H_body := 
   let Einit := E in
   let Ef    := add_decl Einit H H_args (refl_equal true) H_body H_res in
   let EA    := add_decl Ef A A_args (refl_equal true) A_body A_res in 
     EA.

  (* Initial Game *)
  Definition Or_i :=
   [
    If !(m' in_dom L) _then
    [
     If (Elen L <! (qQ1 +! qQ2)) then 
      (Hi ++ [L <- (m' | (ret|r)) |::| L])
     else
      (bad <- true) :: 
      (Hi ++ [L <- (m' | (ret|r)) |::| L])
    ]
   ].

  Definition Ei := mkEnvA Or_i.

  Definition G := [ L <- Nil _; b <c- A with {} ].

  Definition Ev := b && (Elen L <=! (qQ1 +! qQ2)).


  (* Final Game *)
  Definition Or_f :=
   [
    If !(m' in_dom L) _then
    [
     If (Elen L <! (qQ1 +! qQ2)) then 
      (Hf ++ [L <- (m' | (ret|r)) |::| L])
     else
      (bad <- true) :: 
      (Hf ++ [L <- (m' | (ret|r)) |::| L])                          
    ]
   ].

  Definition Ef := mkEnvA Or_f.


  (* Adversary specification *)
  Definition PrOrcl := PrSet.singleton (BProc.mkP H).
  Definition PrPriv := PrSet.empty.

  Definition Gadv := Vset.empty.
  Definition Gcomm := Vset.empty.

  Hypothesis A_wf : WFAdv PrOrcl PrPriv Gadv Gcomm Ei A.

  Hypothesis A_slossless : forall Fbody,
   (forall O, PrSet.mem O PrOrcl -> 
    slossless_c (mkEnvA Fbody) (proc_body (mkEnvA Fbody) (BProc.p_name O))) -> 
   slossless_c (mkEnvA Fbody) A_body.

  Lemma EqAD : forall H_body1 H_body2, 
   Eq_adv_decl PrOrcl PrPriv (mkEnvA H_body1) (mkEnvA H_body2).
  Proof.
   unfold Eq_adv_decl, mkEnvA; intros.
   unfold proc_params, proc_body, proc_res.
   generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
   destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
   inversion H1; simpl; auto.
   repeat rewrite add_decl_other_mk; try tauto;
    intros Heq; 
     (apply H; rewrite <- Heq; vm_compute; reflexivity)
     || (apply H0; rewrite <- Heq; vm_compute; reflexivity).
  Qed.

  Lemma EqOP : forall H_body1 H_body2, 
   Eq_orcl_params PrOrcl (mkEnvA H_body1) (mkEnvA H_body2).
  Proof.
   unfold Eq_orcl_params, mkEnvA; intros.
   unfold PrOrcl in H.
   apply PrSet.singleton_complete in H; inversion H; simpl.
   vm_compute; trivial.
  Qed.

  Lemma EqOR : forall H_body1 H_body2 t (p:Proc.proc t), 
   PrSet.mem (BProc.mkP p) PrOrcl -> 
   proc_res (mkEnvA H_body1) p = proc_res (mkEnvA H_body2) p.
  Proof.
   unfold mkEnvA; intros.
   unfold PrOrcl in H.
   apply PrSet.singleton_complete in H; inversion H; simpl.
   vm_compute; trivial.
  Qed.

  (** The adversary is well-formed in any environment constructed with [mkEnvA].
      This follows from the adversary being well-formed in [Ei] *)
  Lemma A_wf_E : forall H_body,
   WFAdv PrOrcl PrPriv Gadv Gcomm (mkEnvA H_body) A.
  Proof.
   intros; apply WFAdv_trans with (5:=A_wf).
   unfold Ei; apply EqOP.
   unfold Ei; apply EqAD.
   vm_compute; intro; discriminate.
   vm_compute; intro; discriminate.
  Qed.


  (** Proof of Main Lemma *)

  Definition Or_i' :=
   [
    If !(m' in_dom L) _then
    [
     If (Elen L <! (qQ1 +! qQ2)) then 
      (Hi ++ [L <- (m' | (ret|r)) |::| L])
     else
      (bad <- true) :: 
      (Hf ++ [L <- (m' | (ret|r)) |::| L])                          
    ]
   ].

  Definition Ei' := mkEnvA Or_i'.

 
  (* Transition from Ei to Ei' *)

  Definition I := EP1 (Elen L <=! (qQ1 +! qQ2) ==> !bad).
 
  Lemma dep_I: depend_only_rel I {{bad,L}} Vset.empty.
  Proof.
   apply depend_only_EP1.
  Qed.

  Lemma dec_I: decMR I.
  Proof.
   unfold I; auto.
  Qed.

  Lemma H_I : 
   EqObsInv I 
   {{m',L}}
   Ei Or_i 
   Ei Or_i
   {{m',L}}.
  Proof.
   cp_test (m' in_dom L).
 
   eqobsrel_tail; unfold implMR, andR; intros.
   expr_simpl.
   decompose [and] H; trivial.
   
   cp_test (Elen L <! (qQ1 +! qQ2)).
  
   unfold I; eqobsrel_tail; unfold implMR, andR; expr_simpl; intros.
   decompose [and] H. 
   apply leb_complete in H3; destruct H3.
   rewrite is_true_impb in H4; rewrite H4.
   rewrite impb_true_r; trivial.
   apply leb_correct; auto with arith.
   apply is_true_impb; intro Hle.
   rewrite is_true_impb in H4; apply H4.
   apply leb_correct; apply leb_complete in Hle; auto with arith.
 
   unfold I; eqobsrel_tail; unfold implMR, andR; expr_simpl; intros.
   decompose [and] H; clear H H5.
   apply not_is_true_false in H3; apply leb_complete_conv in H3.
   apply is_true_impb; intro Hle.
   destruct (q1_poly k + q2_poly k)%nat; trivial.
   apply leb_complete in Hle.
   
   match goal with
    | H3 : (_ < ?len + 1)%nat |- _ => assert (n < len)%nat by omega
   end.
   exfalso; destruct H; omega.
  Qed.
 

  Definition i_Ei_Ei_empty: eq_inv_info I Ei Ei.
   refine (@empty_inv_info I _ _ _ _ _ _ _).
   apply dep_I. 
   vm_compute; trivial.
   apply dec_I.
  Defined.

  Definition i_Ei_Ei_I :=
   let i_empty := i_Ei_Ei_empty in
   let i_Or    := add_info H Vset.empty Vset.empty i_empty H_I in 
   let i_Adv   := add_adv_info_false (EqAD _ _ ) (A_wf_E _) i_Or in i_Adv.

  Lemma Pr_G : forall k (m:Mem.t k), 
   Pr Ei G m (EP k Ev) == 
   Pr Ei ((bad <- false) :: G) m (EP k Ev [&&] (negP (EP k bad))).
  Proof.
   intros.
   symmetry; apply equiv_deno with Meq (req_mem_rel {{L,b}} I).
   eqobs_tl i_Ei_Ei_I.
   unfold I; eqobsrel_tail; unfold implMR; expr_simpl.
   
   unfold I; intros m1 m2 [Heq H]; unfold charfun, restr, EP, fone.
   apply req_mem_sym in Heq.
   rewrite (@depend_only_fv_expr T.Bool Ev _ _ _ Heq).
   generalize H; unfold Ev, EP1, negP, andP, negb, andb.
   simpl; unfold O.eval_op; simpl; unfold andb; intros.
   repeat match goal with |- context[if ?b then _ else _] => case_eq b end;
    try discriminate; trivial.
   rewrite is_true_impb in H0; intros.
   rewrite H1 in H0; simpl in H0; discriminate H0; trivial.
   trivial.
  Qed.

  Definition  mk_i_Ei'_Ei'_InvF (I:mem_rel) (init_info: eq_inv_info I Ei' Ei'): 
   eq_inv_info I Ei' Ei'.
   intros.
   refine (add_refl_info_rm InvF Vset.empty Vset.empty _).
   apply add_basic_info with (f:=Invf) (X:=Invf_X); trivial.
   apply Invf_lossless.
   apply Invf_Modify.
   apply Invf_ret_expr.
   apply Invf_X_local.
   intros ? H; apply Vset.subset_correct with (1:=Invf_ret_expr) in H.
   apply Invf_X_local; trivial.
   intros.
   intros; eapply equiv_weaken; [ | apply Invf_eqobs ].
   intros; apply req_mem_weaken with (2:=H); apply Invf_ret_expr.
  Defined.

  Lemma EqObs_Invf : 
   EqObsInv I 
   {{r}}
   Ei' Invf_body
   Ei' Invf_body
   Invf_X.
  Proof.
   apply equiv_inv_Modify with (X1:={{bad,L}} ) (X2:=Vset.empty) 
    (M1:=Invf_X) (M2:=Invf_X); trivial.
   apply dep_I.
   apply Invf_Modify.
   apply Invf_Modify.
   intros; apply req_mem_update_same; trivial.   
   unfold Vset.disjoint.
   destruct (VsetP.empty_dec (Vset.inter {{bad,L}} Invf_X)); 
    [ rewrite H; trivial | ].
   destruct H as [(t,x) Hx]; rewrite VsetP.inter_spec in Hx; destruct Hx.
   exfalso.
   generalize (Invf_X_local _ H0); unfold Var.is_local.
   Vset_mem_inversion H; subst; simpl; discriminate. 
   rewrite andR_trueR_r; apply Invf_eqobs.
  Qed.

  Lemma EqObs_InvF: 
   EqObsInv I 
   {{InvF_in}}
   Ei' InvF_body
   Ei' InvF_body
   {{InvF_out}}.
  Proof.
   set (M:= Vset.union {{a',x,p,a,i}} (Vset.union (Vset.union {{x,p,i}} {{a}}) {{InvF_out,a'}})).
   assert (H_Mod:  Modify Ei' M InvF_body).
     change InvF_body with
       ([ i <- 0%nat; a <- none _; p <- Pdef; x <- Rdef; a' <- Adef ] ++
       [  while E.Eop O.Oand {i <=! TMax, !(IsSome a)} do 
         ( [i <- i +! 1%nat; p <$-P; x <- p |+->| InvF_in ] ++
           [ a <c- Invf with {x} ] ) ] ++
       [
         If IsSome a _then [a' <- Proj a];
         If IsSome a then [InvF_out <- some (a' | p)] else [InvF_out <- none _ ]
       ]).
     repeat apply Modify_app.
       apply modify_correct with 
         (refl1_info (empty_info Ei' Ei')) Vset.empty; apply eq_refl.
       apply Modify_while; apply Modify_app.
         apply modify_correct with 
           (refl1_info (empty_info Ei' Ei')) Vset.empty; apply eq_refl.
         setoid_replace Vset.empty with (get_globals Invf_X).
         refine (Modify_call a Invf _ (Invf_Modify Ei')).
         destruct (VsetP.empty_dec (get_globals Invf_X)); [ rewrite H; auto with set | ].
         destruct H as [(t,x) Hx]. 
         exfalso.
           generalize (Invf_X_local _ (Vset.subset_correct (get_globals_subset Invf_X) _ Hx)).
           unfold Var.is_local; rewrite (get_globals_spec _ _ Hx); simpl; discriminate.
       apply modify_correct with 
         (refl1_info (empty_info Ei' Ei')) Vset.empty; apply eq_refl.

   apply equiv_inv_Modify with (X1:={{bad,L}}) (X2:=Vset.empty) (M1:= M) (M2:= M).
   apply dep_I.
   apply H_Mod.
   apply H_Mod.
   intros k m1 m2 m1' m2' _ H t v Hv; Vset_mem_inversion Hv; subst.
   repeat rewrite update_mem_in.
     apply (H _ InvF_out); trivial.  
     apply Vset.union_complete_r;  apply Vset.union_complete_r; trivial.
     apply Vset.union_complete_r;  apply Vset.union_complete_r; trivial.
   unfold Vset.disjoint.
   destruct (VsetP.empty_dec (Vset.inter {{bad,L}} M)); [ rewrite H; trivial | ].
   destruct H as [(t,v) Hv]; rewrite VsetP.inter_spec in Hv; destruct Hv.
   exfalso.
   change M with {{ x,p,i,a,InvF_out,a'}} in H0.
     Vset_mem_inversion H0; subst; discriminate.
   auto.
   rewrite andR_trueR_r; eqobs_in (mk_i_Ei'_Ei'_InvF (empty_info Ei' Ei')).
  Qed.

  
  Definition I' :=  ~- EP1 (Elen L <! (qQ1 +! qQ2)).

  Lemma dep_I': depend_only_rel I' {{L}} Vset.empty.
  Proof.
     apply depend_only_notR; apply depend_only_EP1.
  Qed.

  Lemma dec_I': decMR I'.
  Proof.
   unfold I'; auto.
  Qed.
  
  Definition i_Ei'_Ei'_I'_empty: eq_inv_info I' Ei'  Ei'.
   refine (@empty_inv_info I' _ _ _ _ _ _ _).
   apply dep_I'. 
   vm_compute; trivial.
   apply dec_I'.
  Defined.

  Lemma H_I' : 
   EqObsInv I 
   {{m',L}}
   Ei' Or_i' 
   Ei' Or_i'
   {{m',L}}.
  Proof.
   cp_test (m' in_dom L).
 
   eqobsrel_tail; unfold implMR, andR; intros.
   expr_simpl.
   decompose [and] H; trivial.
   
   cp_test (Elen L <! (qQ1 +! qQ2)).
  
   unfold I; eqobsrel_tail; unfold implMR, andR; expr_simpl; intros.
   decompose [and] H; clear H H5.
   apply leb_complete in H3; destruct H3.
   rewrite is_true_impb in H4; rewrite H4.
   rewrite impb_true_r; trivial.
   apply leb_correct; auto with arith.
   apply is_true_impb; intro Hle.
   rewrite is_true_impb in H4; apply H4.
   apply leb_correct; apply leb_complete in Hle; auto with arith.

   apply equiv_strengthen with (req_mem_rel {{m', L}} I').
     intros ? ? ? (((?,_),_),(?,_));split; trivial.
   match goal with
   |- equiv _ _ ?c1 _ ?c1 _ => 
     rewrite <-(firstn_skipn 5%nat c1);
     apply equiv_app with (req_mem_rel {{m', L, r, ret}} I'); simpl
   end.
   eqobs_in (mk_i_Ei'_Ei'_InvF i_Ei'_Ei'_I'_empty).
   unfold I'; eqobsrel_tail; expr_simpl; intros k m1 m2 (_,H').
   unfold I, EP1; expr_simpl.
   rewrite leb_correct_conv; [ auto | simpl length ].
   generalize (leb_complete_conv _ _ (not_true_is_false  _ H')).
   rewrite <-(plus_comm (1%nat)); trivial.
  Qed.
 
  Definition i_Ei'Ei'_I_empty: eq_inv_info I Ei'  Ei'.
   refine (@empty_inv_info I _ _ _ _ _ _ _).
   apply dep_I. 
   vm_compute; trivial.
   apply dec_I.
  Defined.

  Definition  i_Ei'_Ei'_I: eq_inv_info I Ei' Ei'.
   apply (add_adv_info_false (EqAD _ _ ) (A_wf_E _)).
   refine (add_info H Vset.empty Vset.empty _ H_I').
   refine (add_info InvF Vset.empty Vset.empty _ EqObs_InvF).
   apply add_basic_info with (f:=Invf) (X:=Invf_X); trivial.
   apply Invf_lossless.
   apply Invf_Modify.
   apply Invf_ret_expr.
   apply Invf_X_local.
   intros ? H; apply Vset.subset_correct with (1:=Invf_ret_expr) in H.
   apply Invf_X_local; trivial.
   intros; eapply equiv_weaken; [ | apply Invf_eqobs ].
   intros; apply req_mem_weaken with (2:=H); apply Invf_ret_expr.
   exact i_Ei'Ei'_I_empty.
  Defined.

  Lemma Pr_G' : forall k (m:Mem.t k), 
   Pr Ei' G m (EP k Ev) == 
   Pr Ei' ((bad <- false) :: G) m (EP k Ev [&&] (negP (EP k bad))).
  Proof.
   intros.
   symmetry; apply equiv_deno with Meq (req_mem_rel {{L,b}} I).
   eqobs_tl i_Ei'_Ei'_I.
   unfold I; eqobsrel_tail; unfold implMR; expr_simpl.
   unfold I; intros m1 m2 [Heq H]; unfold charfun, restr, EP, fone.
   apply req_mem_sym in Heq.
   rewrite (@depend_only_fv_expr T.Bool Ev _ _ _ Heq).
   generalize H; unfold Ev, EP1, negP, andP, negb, andb.
   simpl; unfold O.eval_op; simpl; unfold andb; intros.
   repeat match goal with |- context[if ?b then _ else _] => case_eq b end;
    try discriminate; trivial.
   rewrite is_true_impb in H0; intros.
   rewrite H1 in H0; simpl in H0; discriminate H0; trivial.
   trivial.
  Qed.

  Definition i_Ei_Ei'_upto : upto_info bad Ei Ei'.
   refine (add_adv_upto_info _ (EqAD _ _ ) (EqOP _ _) (A_wf_E _)).
   refine (add_upto_info _ H).
   refine (add_upto_info _ InvF).
   apply add_upto_info' with (f:=Invf) (X:=Invf_X).
     trivial.
     trivial.
     trivial.
     intros.
     change (proc_body (mkEnvA Or_i) Invf) with Invf_body.
     change (proc_body (mkEnvA Or_i') Invf) with Invf_body.
     apply equiv_deno with Meq Meq.
       apply equiv_union_Modify_Meq with Invf_X Invf_X.
         split; apply Invf_Modify.
         trivial.
         rewrite VsetP.union_idem; apply Invf_eq_sem.
       intros m1 m2 Hm; rewrite Hm; trivial.
       trivial.
     apply Invf_Modify.
     apply Invf_Modify.
     apply Invf_X_local.
     apply empty_upto_info.
  Defined.

  Lemma Pr_i_i': forall k (m:Mem.t k),
   Pr Ei G m (EP k Ev) == Pr Ei' G m (EP k Ev).
  Proof.
   intros.
   rewrite Pr_G, Pr_G'.
   unfold Pr; elim_assign; elim_assign.
   apply upto_bad_and_neg with i_Ei_Ei'_upto; trivial.
  Qed.

 
  (* Transition from Ei' to Ef *)
  Section Rtriple.

   Variable k : nat.

   Definition h n := 
    if leb (S n) (q1_poly k + q2_poly k) 
    then 2 */ (epsilon k + (1 - one_over_alpha k)^(S (T_poly k))) else 0.

   Definition Fb c := fun m:Mem.t k => 
    mu ([[c]] Ef m) 
    (fun m' => sum_f (E.eval_expr (Elen L) m) (E.eval_expr (Elen L) m') h).

   Definition  i_Ef_Ef: eq_inv_info trueR Ef Ef.
    refine (add_refl_info_rm InvF {{L}} {{L}} _).
    apply add_basic_info with (f:= Invf) (X:=Invf_X); trivial.
    apply Invf_lossless.
    apply Invf_Modify.
    apply Invf_ret_expr.
    apply Invf_X_local.
    intros ? H; apply Vset.subset_correct with (1:=Invf_ret_expr) in H.
    apply Invf_X_local; trivial.
    intros; eapply equiv_weaken; [ | apply Invf_eqobs ].
    intros; apply req_mem_weaken with (2:=H); apply Invf_ret_expr.
    apply empty_info.
   Defined.

   Definition  i_Ef_E: eq_inv_info trueR Ef E.
    refine (add_refl_info_rm InvF {{L}} {{L}} _).
    apply add_basic_info with (f:=Invf) (X:=Invf_X); trivial.    
    apply Invf_lossless.
    apply Invf_Modify.
    apply Invf_ret_expr.
    apply Invf_X_local.
    intros ? H; apply Vset.subset_correct with (1:=Invf_ret_expr) in H.
    apply Invf_X_local; trivial.
    intros; eapply equiv_weaken; [ | apply Invf_eqobs ].
    intros; apply req_mem_weaken with (2:=H); apply Invf_ret_expr.
    apply empty_info.
   Defined.

   Definition  i_Ei'_Ef: eq_inv_info trueR Ei' Ef.
    refine (add_refl_info_rm InvF {{L}} {{L}} _).
    apply add_basic_info with (f:=Invf) (X:=Invf_X); trivial.
    apply Invf_lossless.
    apply Invf_Modify.
    apply Invf_ret_expr.
    apply Invf_X_local.
    intros ? H; apply Vset.subset_correct with (1:=Invf_ret_expr) in H.
    apply Invf_X_local; trivial.
    intros; eapply equiv_weaken; [ | apply Invf_eqobs ].
    intros; apply req_mem_weaken with (2:=H); apply Invf_ret_expr.
    apply empty_info.
   Defined.

   Lemma Orc_distance: rtriple Ef Ei' Or_f Or_i' (Fb Or_f).
   Proof.
    intros m f; unfold Or_i', Or_f, Fb.
    assert (H: forall E g, Oeq (O:=Mem.t k -o> U) (fun x =>
     mu ([[nil]] E x) (fun x' => mu ([[nil]] E x') g)) g) by 
    (intros; refine (ford_eq_intro _); intro; 
     repeat rewrite deno_nil_elim; trivial).
    elim_cond (!(m' in_dom L)) m.
    
    (* case [~(RO.m in_dom L)] *)
    elim_cond ( Elen L <! (qQ1 +! qQ2)) m; 
    repeat rewrite (mu_stable_eq _ _ _ (H _ _)).

    (* case [|L| < (qQ1 +! qQ2) ] *)
    rewrite (@rtriple_app _ _ _ _ _ _ _ (fzero (Mem.t k)) 
     (fun _ => 2 */ (epsilon k + (1 - one_over_alpha k)^(S (T_poly k))))).
    rewrite mu_zero, deno_app_elim; Usimpl.
    match goal with |- _ <= fmonot (mu _) ?F => 
     apply Ole_trans with (fmonot (mu ([[ nil ]] Ef m)) F) 
    end.
    rewrite deno_nil_elim, deno_assign_elim; expr_simpl; simpl length.
    rewrite sum_f_non_empty, <-(Ule_plus_right (h (length (m L)))); trivial.
    unfold h; rewrite leb_correct; trivial.
    apply (leb_complete (length (m L) + 1) (q1_poly k + q2_poly k)) in Hguard0;
     rewrite plus_comm in Hguard0; trivial.
    apply equiv_deno_le with (kreq_mem {{L}}) (kreq_mem {{L}}).

    deadcode i_Ef_Ef.
    apply EqObs_lossless_Modify with Vset.empty {{ret,r}}.
      apply lossless_nil.
      apply lossless_InvF_in_rnd.
        trivial.
        apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl.
        apply is_lossless_correct with (refl2_info i_Ef_Ef); apply eq_refl.
      apply Modify_nil.
      apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl.
      auto with set.
      auto with set.

    intros m1 m2 Hm; repeat rewrite deno_assign_elim; expr_simpl; simpl length. 
    rewrite (Hm _ L); trivial.
    trivial.
    apply rtriple_eq_deno_r with E Hi; 
     [ union_mod; auto; eqobs_in | ].
    apply rtriple_eq_deno_l with E Hf;
     [ union_mod  i_Ef_E; auto; eqobs_in i_Ef_E | ].
    apply rtriple_sym; apply Hi_Hf_Meq.

    apply rtriple_eq_deno_r with Ef [L <- (m' | ( ret | r)) |::| L ];
     [ union_mod; auto; eqobs_in | ].
    apply rtriple_refl_zero.

    (* case [|L| < (qQ1 +! qQ2) ] *)
    set (c:= ((bad <- true) :: Hf ++ [L <- (m' | (ret | r)) |::| L])).
    apply (@rtriple_eq_deno_r _ _ Ef _ _ c _ (Fb c)).  
    union_mod i_Ei'_Ef; auto; eqobs_in i_Ei'_Ef.
    apply rtriple_weaken with (fun _:Mem.t k => 0); 
     [ auto | apply rtriple_refl_zero ].
   
    (* case [~(RO.m in_dom L)] *)
    repeat rewrite deno_nil_elim; rewrite Uabs_diff_compat_eq; trivial.
   Qed.

   Lemma Orc_range: forall (m:Mem.t k),
    range (fun m' => E.eval_expr (Elen L) m <= E.eval_expr (Elen L) m')%nat
    ([[Or_f]] Ef m).
   Proof.
    intros m f H_f.
    rewrite <-(mu_zero ([[Or_f]] Ef m)).
    apply equiv_deno with (P:=Meq /-\ EP1 ((length (m L)) =?= Elen L))
     (Q:=req_mem_rel {{L}} (EP1 ((length (m L)) <=! Elen L))).
    unfold Or_f, Hf.
    cp_test (m' in_dom L).
    unfold EP1; eqobsrel_tail; simpl; unfold O.eval_op; simpl.
    intros k' m1 m2 [_ [H _] ]; apply leb_correct; 
     rewrite (nat_eqb_true H); trivial.
    set (c1:= [ r <$- R; ret <c- InvF with {r}; a' <- Efst (Proj ret); p <- Esnd (Proj ret) ]).
    set (c2:= [  L <- (m' | (ret | r)) |::| L ]).
    cp_test (Elen L <! (qQ1 +! qQ2)); rewrite proj1_MR, proj1_MR.
          (* case [ |L| < q ] *)
    apply equiv_app with  (Q:=Meq /-\ EP1 (length (m L) =?= Elen L))
     (c1:=c1) (c2:=c2) (c3:=c1) (c4:=c2).
    apply equiv_inv_Modify with {{L}} Vset.empty {{p,a',ret,r}} {{p,a',ret,r}} ; auto.
    apply depend_only_EP1.
    apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl.
    apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl. 
    intros.
    apply Mem.eq_leibniz; red; intros t; destruct t.
    destruct (VsetP.mem_dec v {{p,a', ret, r}}) as [Hv | Hv].
    rewrite update_mem_in, update_mem_in, H0; trivial.
    rewrite update_mem_notin, update_mem_notin, H; trivial.
    apply equiv_weaken with Meq; [ apply (proj2 (andR_trueR_r Meq)) | ].
    apply equiv_eq_mem.
    eqobsrel_tail; expr_simpl; intros k' m1 m2 (H1,H2).
    rewrite <-(nat_eqb_true H2); apply leb_correct; auto.

    (* case [ |L| < q ] *)
    unfold c2.
    apply equiv_app with  (Q:=Meq /-\ EP1 (length (m L) =?= Elen L))
     (c1:=(bad<-true)::c1) (c2:=c2) (c3:=(bad<-true)::c1) (c4:=c2).
    apply equiv_inv_Modify with {{L}} Vset.empty {{p,a',ret,r,bad}} {{p,a',ret,r,bad}}; auto.
    apply depend_only_EP1.
    apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl.
    apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl.
    intros.
    apply Mem.eq_leibniz; red; intros t; destruct t.
    destruct (VsetP.mem_dec v {{p,a',ret,r,bad}}) as [Hv | Hv].
    rewrite update_mem_in, update_mem_in, H0; trivial.
    rewrite update_mem_notin, update_mem_notin, H; trivial.
    apply equiv_weaken with Meq; [ apply (proj2 (andR_trueR_r Meq)) | ].
    apply equiv_eq_mem.
    eqobsrel_tail; expr_simpl; intros k' m1 m2 (H1,H2).
    rewrite <-(nat_eqb_true H2); apply leb_correct; auto.
    unfold EP1; intros m1 m2 [H1m H2m].
    apply H_f.
    generalize (proj2 (eval_le _ _ _) H2m); simpl; unfold O.eval_op; simpl.
    rewrite (H1m _ L); trivial.
    split; [ trivial | refine (nat_eqb_refl _) ].
   Qed.

   Lemma slossless_Hf: slossless_c Ef Hf.
   Proof.
    slossless_tac. 
    change (slossless_c Ef (InvF_body)); slossless_tac.
    apply loop_lossless with {{a,x,p}}.
      apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl.
      apply eq_refl.
      apply is_lossless_correct with (refl2_info i_Ef_Ef); apply eq_refl.
    apply Invf_slossless.
   Qed.

   Lemma slossless_Or_f: slossless_c Ef Or_f.
   Proof.
    unfold Or_f, app, Hf.
    slossless_tac.
    change (proc_body Ef InvF) with InvF_body; unfold InvF_body.
    slossless_tac.
    apply loop_lossless with {{a,x,p}}.
      apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl.
      apply eq_refl.
      apply is_lossless_correct with (refl2_info i_Ef_Ef); apply eq_refl.
    apply Invf_slossless.
    change (proc_body Ef InvF) with InvF_body; unfold InvF_body.
    slossless_tac.
    apply loop_lossless with {{a,x,p}}.
      apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl.
      apply eq_refl.
      apply is_lossless_correct with (refl2_info i_Ef_Ef); apply eq_refl.
    apply Invf_slossless.
   Qed.


   Lemma Pr_Ei'_Ef : forall (m:Mem.t k),
    Uabs_diff (Pr Ei' G m (EP k Ev)) (Pr Ef G m (EP k Ev)) <=
    (q1_poly k + q2_poly k) */ 
    (2 */ epsilon k + (1 - one_over_alpha k)^(S (T_poly k))).
   Proof.
    intros.
    unfold G, Pr.
    repeat elim_assign.
    rewrite Uabs_diff_sym.
    refine (rtriple_adv_cte (EqOP _ _) (EqOR _ _) (EqAD _ _) 
     (depend_only_fv_expr (Elen L)) _ _ 
     (q1_poly k + q2_poly k) _ _ _ _ _ _ _ _ _ _ (m {!L <-- nil!}) _).
    intros x Hx; rewrite <-(Vset.singleton_complete _ _ Hx); trivial.
    intros ? _; apply Vset.empty_spec.
    apply Orc_distance.
    apply Orc_range.
    apply A_slossless.
    intros; apply PrSet.singleton_complete in H; destruct H; simpl;
     change (proc_body (mkEnvA Or_f) H) with Or_f.
    apply slossless_Or_f.
    discriminate.
    discriminate.
    apply A_wf_E; intros x Hx; discriminate Hx.
    intros x Hx; discriminate Hx.
   Qed.
  
  End Rtriple.
  
  Theorem security_bound : forall k (m:Mem.t k),
   Uabs_diff (Pr Ei G m (EP k Ev)) (Pr Ef G m (EP k Ev)) <= 
   2 * (q1_poly k + q2_poly k) */ 
   (epsilon k + (1 - one_over_alpha k)^(S (T_poly k))).
  Proof.
   intros; rewrite Pr_i_i', Pr_Ei'_Ef, <- Nmult_mult_assoc, mult_comm; trivial.
  Qed.

 End ADVERSARY.

End Indifferentiability.
