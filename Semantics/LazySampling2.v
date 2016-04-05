(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * LazySampling2.v : A logic for swapping statements *)

Require Export LazySampling.


Module Make (SemO:SEM_OPT).
 Module LS := LazySampling.Make SemO.
 Export LS.

 Lemma equiv_union_Modify_Meq : forall E1 c1 E2 c2 P X1 X2,
  Modify E1 X1 c1 /\ Modify E2 X2 c2 ->
  implMR P Meq ->
  equiv P E1 c1 E2 c2 (kreq_mem (Vset.union X1 X2)) ->
  equiv P E1 c1 E2 c2 Meq.
 Proof.
  intros; destruct H.
  apply equiv_union_Modify_pre with
   (P1:=fun _ _ => True) (P2:=fun _ _ => True)
   (X1:=Vset.union X1 X2) (X2:=Vset.union X1 X2) 
   (Q:=kreq_mem (Vset.union X1 X2)); auto.
  intros.
  assert (W := H0 k m1 m2 H3).
  unfold Meq in *; subst.
  apply req_mem_eq; trivial.
  apply Modify_Modify_pre; apply Modify_weaken with (1:= H); auto with set.
  apply Modify_Modify_pre; apply Modify_weaken with (1:= H2); auto with set.
 Qed.
 
 Lemma equiv_swap2 : forall E1 E2 I1 I2 O1 O2 c1 c2,
  Modify E1 O1 c1 -> Modify E2 O1 c1 ->
  Modify E1 O2 c2 ->  Modify E2 O2 c2 ->
  EqObs I1 E1 c1 E2 c1 O1 ->
  EqObs I2 E1 c2 E2 c2 O2 ->
  Vset.disjoint O1 O2 ->
  Vset.disjoint I1 O2 ->
  Vset.disjoint I2 O1 -> 
  equiv Meq E1 (c1++c2) E2 (c2++c1) Meq.
 Proof.
  intros;apply equiv_trans with (P1:= Meq) (Q1:= Meq) (Q2:=Meq)
   (E2:=E1) (c2:=c2++c1).
  auto with *.
  red;unfold Meq;intros;transitivity m2;auto.
  unfold Meq;intros;subst;trivial.
  eapply equiv_swap;eauto.
  apply EqObs_trans with E2 c1;[ | apply EqObs_sym];trivial.
  apply EqObs_trans with E2 c2;[ | apply EqObs_sym];trivial.
  apply equiv_union_Modify_pre2 with (Vset.union O1 O2) (Vset.union O1 O2)
   (kreq_mem (Vset.union O1 O2)) (fun k m => True) (fun k m => True);
   auto with *.
  unfold kreq_mem, req_mem, eeq_mem,Meq;intros.
  apply Mem.eq_leibniz;intros.
  intros (t,x); destruct (VsetP.mem_dec x (Vset.union O1 O2));[auto | ].
  rewrite <- H10, <- H11, H8;trivial.
  apply Modify_Modify_pre; rewrite VsetP.union_sym;apply Modify_app;trivial.
  apply Modify_Modify_pre; rewrite VsetP.union_sym;apply Modify_app;trivial.
  apply equiv_app with (kreq_mem (Vset.union I1 O2)).
  apply equiv_union_Modify_pre2 with O2 O2
   (kreq_mem O2) (fun k m => True) (fun k m => True);
   auto with *.
  unfold kreq_mem, req_mem, eeq_mem,Meq;intros.
  apply Vset.union_correct in H12;destruct H12.
  rewrite <- H10, <- H11, H8;trivial.
  eapply VsetP.disjoint_mem_not_mem;eauto.
  eapply VsetP.disjoint_mem_not_mem;eauto.
  auto.
  apply Modify_Modify_pre;trivial.
  apply Modify_Modify_pre;trivial.
  apply equiv_strengthen with (kreq_mem I2);[ | exact H4].
  unfold Meq, kreq_mem;intros;subst;apply req_mem_refl.
  apply equiv_union_Modify_pre2 with O1 O1
   (kreq_mem O1) (fun k m => True) (fun k m => True);
   auto with *.
  unfold kreq_mem, req_mem, eeq_mem,Meq;intros.
  apply Vset.union_correct in H12;destruct H12;auto.
  rewrite <- H10, <- H11, H8;auto with set.
  apply VsetP.disjoint_mem_not_mem with O2;trivial.
  apply VsetP.disjoint_sym;trivial.
  apply VsetP.disjoint_mem_not_mem with O2;trivial.
  apply VsetP.disjoint_sym;trivial.
  apply Modify_Modify_pre;trivial.
  apply Modify_Modify_pre;trivial.
  apply equiv_strengthen with (kreq_mem I1);[ | exact H3].
  unfold kreq_mem;intros;subst;eapply req_mem_weaken;eauto;auto with set.
 Qed.

 Lemma equiv_union_Modify : forall E1 c1 E2 c2 I P X1 X2 O Q,
  Modify E1 X1 c1 /\ Modify E2 X2 c2 ->
  decMR P ->
  equiv (req_mem_rel I P) E1 c1 E2 c2 (req_mem_rel (Vset.diff O (Vset.diff I (Vset.union X1 X2))) Q) -> 
  equiv (req_mem_rel I P) E1 c1 E2 c2 (req_mem_rel O Q).
 Proof.
  intros; destruct H.  
  apply equiv_union_Modify_pre2 with 
   (P1:= fun _ _ => True) (P2:= fun _ _ => True)
   (X1:=X1) (X2:=X2) 
   (Q:=req_mem_rel (Vset.diff O (Vset.diff I (Vset.union X1 X2))) Q); auto.  
  unfold req_mem_rel, kreq_mem; intros k m1 m2 m1' m2' [W1 W2] [W3 W4]; split.
  intros t x Hx.
  destruct (VsetP.mem_dec x (Vset.diff I (Vset.union X1 X2))).
  rewrite VsetP.diff_spec, VsetP.union_spec in i; destruct i.
  rewrite <- H2; try tauto.
  rewrite <- H3; auto; try tauto.
  apply W3; auto with set.
  trivial. 
  apply Modify_Modify_pre; auto.
  apply Modify_Modify_pre; auto.
 Qed.

 Lemma EqObs_union_Modify : forall E1 c1 E2 c2 I X1 X2 O,
  Modify E1 X1 c1 /\ Modify E2 X2 c2 ->
  EqObs I E1 c1 E2 c2 (Vset.diff O (Vset.diff I (Vset.union X1 X2))) -> 
  EqObs I E1 c1 E2 c2 O.
 Proof.
  unfold EqObs;intros.
  apply equiv_weaken with (req_mem_rel O trueR);[unfold req_mem_rel, andR;intuition |].
  apply equiv_strengthen with (req_mem_rel I trueR);[unfold req_mem_rel, andR, trueR;intuition|].
  eapply equiv_union_Modify;eauto.
  eapply equiv_weaken;[ | eapply equiv_strengthen;[ | apply H0] ];
  unfold req_mem_rel, andR, trueR;intuition.
 Qed.

 Section CONTEXT.

  Variable S:cmd.
  Variable X:Vset.t.
  Variable I:Vset.t.
  Local Notation IX := (Vset.union I X).
  
  Section CONTEXT1.
   
   Variable E1 E2: env.
   Hypothesis Modify_S1 : Modify E1 X S.
   Hypothesis Modify_S2 : Modify E2 X S.
   Hypothesis EqObs_S : EqObs IX E1 S E2 S X.

   Lemma EqObs_S1 : EqObs IX E1 S E1 S X.
   Proof. 
    apply EqObs_trans with E2 S;auto using EqObs_sym.
   Qed.

   Lemma EqObs_S2 : EqObs IX E2 S E2 S X.
   Proof. 
    apply EqObs_trans with E1 S;auto using EqObs_sym.
   Qed.

   Lemma equiv_S : equiv Meq E1 S E2 S Meq.
   Proof.
    apply equiv_union_Modify_Meq with X X;auto.
    rewrite VsetP.union_idem;eapply equiv_strengthen;[ | apply EqObs_S].
    unfold Meq, kreq_mem;intros;subst;apply req_mem_refl.
   Qed.

   Lemma swap_sample_assign : 
    forall t (x:Var.var t) e, ~Vset.mem x IX -> Vset.disjoint X (fv_expr e) ->
     equiv Meq E1 ((x <- e)::S) E2 (S ++ [x<-e]) Meq.
   Proof.
    intros;change ((x<-e)::S) with (([x<-e]++S)).
    assert (W1:= @Modify_assign E1 _ x e);assert (W2:= @Modify_assign E2 _ x e).
    assert (Vset.disjoint X (Vset.add x (fv_expr e))).
    apply VsetP.disjoint_sym;apply VsetP.disjoint_complete;intros.
    rewrite VsetP.add_spec in H1;destruct H1.
    rewrite <- H1;intros Hin;apply H;auto with set.
    eapply VsetP.disjoint_mem_not_mem;eauto. 
    apply VsetP.disjoint_sym;trivial.
    assert (Vset.disjoint IX (Vset.singleton x)).
    apply disjoint_singleton;rewrite <- not_is_true_false;trivial.
    apply equiv_swap2 with (I1:=fv_expr e) (I2:= IX) (O1:=Vset.singleton x) (O2:= X);auto using VsetP.disjoint_sym.
    apply EqObs_assign.
    apply VsetP.disjoint_sym;apply VsetP.disjoint_subset_l with IX;eauto with set.
   Qed.
   
   Lemma swap_sample_random : 
    forall t (x:Var.var t) d, ~Vset.mem x IX -> Vset.disjoint X (fv_distr d) ->
     equiv Meq E1 ((x <$- d)::S) E2 (S ++ [x<$-d]) Meq.
   Proof.
    intros;change ((x<$-d)::S) with (([x<$-d]++S)).
    assert (W1:= @Modify_random E1 _ x d);assert (W2:= @Modify_random E2 _ x d).
    assert (Vset.disjoint X (Vset.add x (fv_distr d))).
    apply VsetP.disjoint_sym;apply VsetP.disjoint_complete;intros.
    rewrite VsetP.add_spec in H1;destruct H1.
    rewrite <- H1;intros Hin;apply H;auto with set.
    eapply VsetP.disjoint_mem_not_mem;eauto. 
    apply VsetP.disjoint_sym;trivial.
    assert (Vset.disjoint IX (Vset.singleton x)).
    apply disjoint_singleton;rewrite <- not_is_true_false;trivial.
    apply equiv_swap2 with (I1:=fv_distr d) (I2:= IX) (O1:=Vset.singleton x) (O2:= X);auto using VsetP.disjoint_sym.
    apply EqObs_random.
    apply VsetP.disjoint_sym;apply VsetP.disjoint_subset_l with IX;eauto with set.
   Qed.

  End CONTEXT1.

  Variable E1 E2: env.
  Hypothesis Modify_S1 : Modify E1 X S.
  Hypothesis Modify_S2 : Modify E2 X S.
  Hypothesis EqObs_S : EqObs IX E1 S E2 S X.
  
  (* Move this *)
  Lemma equiv_Meq_deno : forall E1 c1 E2 c2,
   equiv Meq E1 c1 E2 c2 Meq ->
   forall k (m:Mem.t k), [[ c1]] E1 m == [[c2]] E2 m.
  Proof.
   intros; refine (ford_eq_intro _);intros f.
   apply equiv_deno with (1:= H);auto.
   unfold Meq;intros;subst;trivial.
  Qed.

  Lemma swap_sample_nil : equiv Meq E1 (nil++S) E2 (S++nil) Meq.
  Proof. 
   rewrite <-app_nil_end;apply equiv_S;trivial. 
  Qed.
   
  Lemma swap_sample_app : forall c1 c1' c2 c2',
   equiv Meq E1 (c1++S) E2 (S++c1') Meq ->
    equiv Meq E1 (c2++S) E2 (S++c2') Meq ->
    equiv Meq E1 ((c1++c2)++S) E2 (S++(c1'++c2')) Meq.
  Proof.
   intros; apply equiv_eq_sem; intros.
   assert (W1:=equiv_Meq_deno _ _ _ _ H k). 
   symmetry; rewrite ass_app.
   rewrite deno_app, <- W1.
   rewrite deno_app; rewrite <-ass_app,deno_app, Mcomp.
   apply Mlet_eq_compat; [trivial | ].
   apply ford_eq_intro; intro m1.
   rewrite equiv_Meq_deno, <- deno_app.
   symmetry; apply (equiv_Meq_deno _ _ _ _ H0).
   apply equiv_S; eauto.
  Qed.

  Lemma swap_sample_app2 : forall c1 c2 c2' Q,
   equiv Meq E2 (c1++S) E2 (S++c1) Meq ->
   equiv Meq E1 c1 E2 c1 Meq -> 
   equiv Meq E1 (c2++S) E2 (S++c2') Q ->
   equiv Meq E1 ((c1++c2)++S) E2 (S++(c1++c2')) Q.
  Proof.
   intros;apply equiv_trans_eq_mem_r with trueR E2 (c1++(S++c2')).
   rewrite proj1_MR;repeat rewrite <- app_ass.
   apply equiv_app with Meq;trivial.
   apply equiv_sym;trivial.
   apply equiv_eq_mem.
   rewrite app_ass;apply equiv_app with Meq;auto.
   red;red;trivial.
  Qed.
  
  Definition equiv_le E1 c1 E2 c2 (R:mem_rel) :=
   forall k (f:Mem.t k -> U),
    (forall m1 m2, R k m1 m2 -> f m1 <= f m2) ->
    forall m, mu ([[c1]] E1 m) f <= mu ([[c2]] E2 m) f.
  
  Lemma swap_equiv_le_app : forall c1 c2,
   equiv_le E1 (S++c1) E2 (c1++S) Meq ->
   equiv_le E1 (S++c2) E2 (c2++S) Meq ->
   equiv_le E1 (S++(c1++c2)) E2 ((c1++c2)++S) Meq.
  Proof.
   unfold equiv_le;intros.
   rewrite app_ass, (deno_app_elim E2).
   transitivity (mu ([[ c1 ]] E2 m) (fun m' : Mem.t k =>
    mu ([[S]] E2 m') (fun m'' => mu ([[c2 ]] E1 m'') f))).
   rewrite <- deno_app_elim, <- app_ass, deno_app_elim;apply H;trivial.
   intros m1 m2 Heq;rewrite Heq;trivial.
   apply mu_le_compat;[trivial | intros m'].
   transitivity (mu (([[ S ++ c2 ]]) E1 m') f); [ | auto].
   rewrite deno_app_elim;apply mu_le_compat;[apply Oeq_le | trivial].
   symmetry;apply equiv_Meq_deno;apply equiv_S;trivial.
  Qed.

  Lemma swap_equiv_le_app2 : forall c1 c2 c2' Q,
   equiv Meq E1 (S++c1) E2 (c1++S) Meq ->
   equiv_le E1 (S++c2) E2 (c2'++S) Q ->
   equiv_le E1 (S++(c1++c2)) E2 ((c1++c2')++S) Q.
  Proof.
   unfold equiv_le;intros.
   transitivity  
    (mu ([[c1]] E2 m) (fun m' => mu ([[S]] E2 m') (fun m'' => mu ([[c2]] E1 m'') f))).
   rewrite <- deno_app_elim, <- app_ass, deno_app_elim.
   apply mu_le_compat;[apply Oeq_le | trivial ].
   apply equiv_Meq_deno;trivial.
   rewrite app_ass, deno_app_elim;apply mu_le_compat;[trivial | intros m'].
   transitivity (mu (([[ S ]]) E1 m') (fun m'' : Mem.t k => (mu (([[ c2 ]]) E1 m'')) f)).
   apply mu_le_compat;[ apply Oeq_le;apply equiv_Meq_deno| trivial].
   apply equiv_sym;auto using equiv_S.
   rewrite <- deno_app_elim;auto.
  Qed.
  
  Lemma swap_sample_cons : forall i c,
   equiv Meq E1 (i::S) E2 (S++[i]) Meq ->
   equiv Meq E1 (c++S) E2 (S++c) Meq ->
   equiv Meq E1 ((i::c)++S) E2 (S++(i::c)) Meq.
  Proof. 
   intros i c.
   apply (swap_sample_app [i] [i] c c). 
  Qed.
  
  Lemma swap_equiv_le_cons : forall i c,
   equiv_le E1 (S++[i]) E2 (i::S) Meq ->
   equiv_le E1 (S++c) E2 (c++S) Meq ->
   equiv_le E1 (S++(i::c)) E2 ((i::c)++S) Meq.
  Proof. 
   intros i c;exact (swap_equiv_le_app [i] c). 
  Qed.

  Lemma swap_sample_if : forall e c1 c2,
   Vset.disjoint (fv_expr e) X ->
   equiv Meq E1 (c1++S) E2 (S++c1) Meq ->
   equiv Meq E1 (c2++S) E2 (S++c2) Meq ->
   equiv Meq E1 ((If e then c1 else c2)::S) E2 (S++[If e then c1 else c2]) Meq.
  Proof.
   intros;apply equiv_eq_sem;intros.
   rewrite deno_cons;rewrite deno_cond.
   rewrite deno_app, (@Modify_deno _ _ _ Modify_S2 k m), Mcomp.
   case_eq (E.eval_expr e m);intros;rewrite <- deno_app;
    [rewrite (equiv_Meq_deno _ _ _ _ H0 k) | rewrite (equiv_Meq_deno _ _ _ _ H1 k)];rewrite deno_app;
     rewrite (@Modify_deno _ _ _ Modify_S2 k m) at 1;rewrite Mcomp;
      (apply Mlet_eq_compat;[trivial | ]); refine (ford_eq_intro _);intros m1;
       repeat rewrite Mlet_unit;rewrite deno_cond;
        (replace (E.eval_expr e (m {!X <<- m1!})) with (E.eval_expr e m);
         [ rewrite H2;trivial |
          apply depend_only_fv_expr;apply req_mem_sym;apply req_mem_update_disjoint;trivial]).
  Qed.
  
  Lemma swap_equiv_le_if : forall e c1 c2,
   Vset.disjoint (fv_expr e) X ->
   equiv_le E1 (S++c1) E2 (c1++S)  Meq ->
   equiv_le E1 (S++c2) E2 (c2++S) Meq ->
   equiv_le E1 (S++[If e then c1 else c2]) E2 ((If e then c1 else c2)::S) Meq.
  Proof.
   unfold equiv_le;intros.
   rewrite deno_cons_elim, Mlet_simpl, deno_cond_elim.
   rewrite deno_app_elim, (ford_eq_elim (@Modify_deno _ _ _ Modify_S1 k m)), Mlet_simpl.
   case_eq (E.eval_expr e m);intros;rewrite <- deno_app_elim;
    [ apply Ole_trans with (2:= H0 k f H2 m) | apply Ole_trans with (2:= H1 k f H2 m)];
    (set (S1 := S);unfold S1 at 2;
     rewrite deno_app_elim, (ford_eq_elim (@Modify_deno _ _ _ Modify_S1 k m)), Mlet_simpl;
      apply mu_le_compat;[trivial | intros m1];
       rewrite Munit_eq, Munit_eq, deno_cond_elim;
        (replace (E.eval_expr e (m {!X <<- m1!})) with (E.eval_expr e m);
         [ rewrite H3;trivial
          | apply depend_only_fv_expr;apply req_mem_sym;apply req_mem_update_disjoint;trivial])).
  Qed.
  
  Lemma swap_sample_if2 : forall e c1 c2 c1' c2' P Q,
   (forall b:bool, equiv (Meq /-\ EP1 (e =?= b)) E2 S E2 S (Meq /-\ EP1 (e =?= b))) ->
   equiv (P /-\ EP1 e) E1 (c1++S) E2 (S++c1') Q ->
   equiv (P /-\ ~-EP1 e) E1 (c2++S) E2 (S++c2') Q ->
   (forall k m1 m2, P k m1 m2 -> E.eval_expr e m1 = E.eval_expr e m2) ->
   equiv P E1 ((If e then c1 else c2)::S) E2 (S++[If e then c1' else c2']) Q.
  Proof.
   intros;apply equiv_case1 with (EP1 e).
   apply decMR_EP1.
   apply equiv_trans_eq_mem_l with (EP1 e) E1 (c1++S).
   apply equiv_eq_sem_pre.
   intros;rewrite deno_cons, deno_cond.
   unfold EP1 in H3;rewrite H3, deno_app;trivial.
   apply equiv_trans_eq_mem_r with (EP1 e) E2 (S++c1').
   apply equiv_eq_sem_pre;intros.
   repeat rewrite deno_app.
   refine (ford_eq_intro _);intros f;repeat rewrite Mlet_simpl.
   apply equiv_deno with (1:= H true).
   intros m1 m2 (Heq, Hep1);rewrite Heq in *.
   rewrite deno_cond_elim.
   unfold EP1 in Hep1;rewrite <- (expr_eval_eq m2 e) in Hep1.
   rewrite Hep1;trivial.
   split;[trivial | unfold EP1;rewrite <- (expr_eval_eq m e);trivial].
   apply H0.
   unfold refl_supMR2, transpR, andR, EP1, EP2.
   unfold is_true;intros k m1 m2 (H_1, H_2).
   rewrite <- H_2;symmetry;apply H2;trivial.
   unfold refl_supMR2, transpR, andR, EP1, EP2;intuition.
   
   apply equiv_trans_eq_mem_l with (~-EP1 e) E1 (c2++S).
   apply equiv_eq_sem_pre.
   intros;rewrite deno_cons, deno_cond.
   unfold EP1,notR in H3;rewrite not_is_true_false in H3;rewrite H3, deno_app;trivial.
   apply equiv_trans_eq_mem_r with (~-(EP1 e)) E2 (S++c2').
   apply equiv_eq_sem_pre;intros.
   repeat rewrite deno_app.
   refine (ford_eq_intro _);intros f;repeat rewrite Mlet_simpl.
   apply equiv_deno with (1:= H false).
   intros m1 m2 (Heq, Hep1);rewrite Heq in *.
   rewrite deno_cond_elim.
   unfold EP1 in Hep1;rewrite <- (expr_eval_eq m2 e) in Hep1.
   rewrite Hep1;trivial.
   split;[trivial | unfold EP1;rewrite <- (expr_eval_eq m e);trivial].
   unfold notR, EP1 in H3;rewrite not_is_true_false in H3;trivial.
   apply H1.
   unfold refl_supMR2, transpR, andR, EP1, EP2, notR.
   intros k m1 m2 (H3, H4);rewrite <- (H2 _ _ _ H3);trivial.
   unfold refl_supMR2, transpR, andR, EP1, EP2;intuition.
  Qed.
  
  Lemma swap_sample_if_Q : forall e c1 c1' c2 c2' Q,
   Vset.disjoint (fv_expr e) X ->
   equiv Meq E1 (c1++S) E2 (S++c1') Q ->
   equiv Meq E1 (c2++S) E2 (S++c2') Q ->
   equiv Meq E1 ((If e then c1 else c2)::S) E2 (S++[If e then c1' else c2']) Q.
  Proof.
   intros;apply swap_sample_if2.
   intros b;apply equiv_union_Modify_pre with (P1:= fun k m => True) (P2:= fun k m => True)
    (X1:= X) (X2:= X) (Q := Meq);auto.
   unfold Meq;intros k m1 m2 m1' m2' (W1, W2) W3;subst;split;trivial.
   unfold EP1, is_true in *;rewrite <- W2.
   refine (depend_only_fv_expr (e =?= b) _ ).
   apply req_mem_update_disjoint;trivial.
   apply Modify_Modify_pre;trivial.
   apply Modify_Modify_pre;trivial.
   rewrite proj1_MR;apply equiv_eq_mem.
   rewrite proj1_MR;trivial.
   rewrite proj1_MR;trivial.
   intros k m1 m2 Heq;rewrite Heq;trivial.
  Qed.

  Lemma swap_sample_assign2 : 
   forall t (x:Var.var t) e , ~Vset.mem x IX -> 
    (forall k (m:Mem.t k), range (fun m1 => E.eval_expr e m = E.eval_expr e (m {!X <<- m1!})) ([[S]] E2 m)) -> 
     equiv Meq E1 ((x <- e)::S) E2 (S ++ [x<-e]) Meq.
  Proof.
   intros;apply equiv_eq_sem;intros.
   rewrite deno_cons, deno_app, deno_assign, Mlet_unit.
   rewrite (Modify_deno Modify_S1).
   rewrite (Modify_deno Modify_S2).
   refine (ford_eq_intro _);intros f.
   repeat rewrite Mlet_simpl.
   transitivity (mu ([[ S ]] E2 m)
  (fun x0 : Mem.t k =>
   (mu (Munit ((m {!x <-- E.eval_expr e m!}) {!X <<- x0!}))) f)).
   apply (equiv_deno EqObs_S).
   simpl;intros m1 m2 H1;rewrite (req_mem_eq (m {!x <-- E.eval_expr e m!}) H1);trivial.
   red;apply req_mem_sym;apply req_mem_upd_disjoint.
   rewrite <- not_is_true_false;trivial.
   apply (range_eq (H0 k m)).
   intros m1 Heq.
   repeat rewrite Munit_eq.
   rewrite deno_assign_elim.
   rewrite <- Heq.
   replace ((m {!x <-- E.eval_expr e m!}) {!X <<- m1!}) with 
    ((m {!X <<- m1!}) {!x <-- E.eval_expr e m!});trivial.
   apply Mem.eq_leibniz;intros (tz, z).
   destruct (Var.eq_dec x z).
   inversion e0;simpl;rewrite Mem.get_upd_same.
   rewrite update_mem_notin.
   rewrite Mem.get_upd_same;trivial.
   intros H4;elim H;auto with set.
   rewrite Mem.get_upd_diff;trivial.
   destruct (VsetP.mem_dec z X).
   repeat rewrite update_mem_in;trivial.
   repeat rewrite update_mem_notin;trivial.
   rewrite Mem.get_upd_diff;trivial.
  Qed.

  Lemma swap_sample_while : forall e c,
   Vset.disjoint (fv_expr e) X ->
   equiv Meq E1 (c++S) E2 (S++c) Meq ->
   equiv Meq E1 ((while e do c)::S) E2 (S++[while e do c]) Meq.
  Proof.
   intros;apply equiv_eq_sem;intros.
   rewrite deno_cons, deno_app.
   rewrite deno_while_unfold.
   assert (W:= lub_comp_eq (unroll_while_sem E1 e c m) (@Mlet_continuous_left (Mem.t k) (Mem.t k))).
   rewrite (ford_eq_elim W ([[S]] E1));clear W.
   
   assert (W:=lub_comp_eq 
    (@fnatO_intro (Mem.t k -O-> cDistr (Mem.t k))
     (fun n m => @unroll_while_sem k E2 e c m n)
     (fun n m => fnatO_elim (@unroll_while_sem k E2 e c m) n))
    (@Mlet_continuous_right (Mem.t k) (Mem.t k) ([[S]] E2 m))).
   eapply Oeq_trans;[ | symmetry;eapply Oeq_trans;[ | apply W ] ].
   refine (lub_eq_compat _);refine (ford_eq_intro _);clear W.
   intros n;refine (ford_eq_intro _);intros f;simpl.
   transitivity 
     (mu (([[ unroll_while e c n ]]) E1 m)
      (fun x : Mem.t k =>
       mu ([[S]] E1 x) (fun x0 =>  mu (if negP (E.eval_expr e) x0 then Munit x0 else distr0 (Mem.t k))
        f))).
   refine (mu_stable_eq _ _ _ _);refine (ford_eq_intro _);intros m1;unfold negP.
   rewrite (ford_eq_elim (@Modify_deno _ _ _ Modify_S1 k m1)), Mlet_simpl.
   case_eq (E.eval_expr e m1);intros;simpl.
   transitivity (mu ([[S]] E1 m1) (fun _ => 0)).
   symmetry;apply mu_zero.
   apply mu_stable_eq;refine (ford_eq_intro _);intros m0.
   replace  (E.eval_expr e (m1 {!X <<- m0!})) with (E.eval_expr e m1);[rewrite H1;trivial |].
   apply depend_only_fv_expr;apply req_mem_sym;apply req_mem_update_disjoint;trivial.
   rewrite (ford_eq_elim (@Modify_deno _ _ _ Modify_S1 k m1)) at 1;rewrite Mlet_simpl.
   apply mu_stable_eq;refine (ford_eq_intro _);intros m0.
   replace  (E.eval_expr e (m1 {!X <<- m0!})) with (E.eval_expr e m1);[rewrite H1;trivial |].
   apply depend_only_fv_expr;apply req_mem_sym;apply req_mem_update_disjoint;trivial.
   rewrite <- deno_app_elim, <- (deno_app_elim E2 S (unroll_while e c n) m).
   apply ford_eq_elim;refine (equiv_Meq_deno _ _ _ _ _ k m);induction n;simpl.
   apply swap_sample_if;auto using swap_sample_nil.
   apply swap_sample_if;auto using swap_sample_nil.
   apply swap_sample_app;auto.
   refine (Mlet_eq_compat _ _);[trivial | refine (ford_eq_intro _);intros m1].
   rewrite deno_while_unfold;refine (lub_eq_compat _);refine (ford_eq_intro _);trivial.
  Qed.

  Lemma swap_equiv_le_nil : equiv_le E1 (S++nil) E2 (nil++S) Meq.
  Proof. 
   rewrite <-app_nil_end;red;simpl;intros.
   refine (mu_le_compat _ _);[apply Oeq_le | trivial].
   apply equiv_Meq_deno;apply equiv_S;trivial.
  Qed.

  Lemma swap_equiv_le_while : forall e c,
   Vset.disjoint (fv_expr e) X ->
   equiv_le E1 (S++c) E2 (c++S) Meq ->
   equiv_le E1 (S++[while e do c]) E2 ((while e do c)::S) Meq.
  Proof.
   unfold equiv_le;intros.
   apply mu_le_compat;[ | trivial].
   rewrite deno_cons, deno_app, deno_while_unfold.
   assert (W:= lub_comp_eq (unroll_while_sem E2 e c m) (@Mlet_continuous_left (Mem.t k) (Mem.t k))).
   rewrite (ford_eq_elim W ([[S]] E2));clear W.
   
   assert (W:=lub_comp_eq 
    (@fnatO_intro (Mem.t k -O-> cDistr (Mem.t k))
     (fun n m => @unroll_while_sem k E1 e c m n)
     (fun n m => fnatO_elim (@unroll_while_sem k E1 e c m) n))
    (@Mlet_continuous_right (Mem.t k) (Mem.t k) ([[S]] E1 m))).
   eapply Ole_trans.
   2: eapply Ole_trans.
   2: apply Oeq_le;apply W.
   refine (@Mlet_le_compat (Mem.t k) (Mem.t k) _ _ _ _ _ _);trivial.
   apply ford_le_intro;intros m1;rewrite deno_while_unfold.
   refine (@lub_le_compat (cDistr (Mem.t k)) _ _ _).
   simpl;intros;trivial.
   refine (@lub_le_compat (cDistr (Mem.t k)) _ _ _).
   clear W H1 f;intros n f;simpl.
   transitivity
   (mu ([[ unroll_while e c n ]] E2 m)
    (fun x : Mem.t k =>
     mu ([[ S ]] E2 x) (fun x0 => 
      mu (if negP (E.eval_expr e) x0 then Munit x0 else distr0 (Mem.t k)) f))).
   Focus 2.
   apply mu_le_compat;[trivial| intros m'].
   rewrite (ford_eq_elim (@Modify_deno _ _ _ Modify_S2 k m')), Mlet_simpl.
   unfold negP;case_eq (E.eval_expr e m');intros Heq;simpl.
   transitivity (mu ([[ S ]] E2 m') (fun _ => 0));[ | rewrite mu_0;trivial].
   refine (mu_le_compat _ _);[trivial | intros m2].
   replace (E.eval_expr e (m' {!X <<- m2!})) with true;[trivial | ].
   rewrite <- Heq;apply (depend_only_fv_expr e);apply req_mem_sym;apply req_mem_update_disjoint;trivial.
   rewrite (ford_eq_elim (@Modify_deno _ _ _ Modify_S2 k m') f), Mlet_simpl.
   refine (mu_le_compat _ _);[trivial | intros m2].
   replace (E.eval_expr e (m' {!X <<- m2!})) with false;[trivial | ].
   rewrite <- Heq;apply (depend_only_fv_expr e);apply req_mem_sym;apply req_mem_update_disjoint;trivial.
   set (f1 := fun x0 : Mem.t k =>
    (mu (if negP (E.eval_expr e) x0 then Munit x0 else distr0 (Mem.t k))) f).
   change (mu ([[ S ]] E1 m) (fun x : Mem.t k => mu ([[ unroll_while e c n ]] E1 x) f1) <=
     mu ([[ unroll_while e c n ]] E2 m) (fun x : Mem.t k => mu ([[ S ]] E2 x) f1)).
   repeat rewrite <- deno_app_elim.
   generalize k m f1;clear k m f f1.
   induction n;simpl unroll_while; simpl app;intros k m f;apply swap_equiv_le_if;auto using swap_equiv_le_nil.
   intros m1 m2 Heq;rewrite Heq;trivial.
   apply swap_equiv_le_app;[auto | red;auto].
   intros m1 m2 Heq;rewrite Heq;trivial.
  Qed.
  
  Hypothesis X_global : forall x, Vset.mem x IX -> Var.is_global x.
  
  Lemma swap_sample_call : forall t (f:Proc.proc t) (x:Var.var t) args, 
   equiv Meq E1 ((proc_body E1 f)++S) E2 (S++(proc_body E2 f)) Meq ->
   proc_params E1 f = proc_params E2 f ->
   proc_res E1 f = proc_res E2 f ->
   Vset.disjoint (fv_expr (proc_res E1 f)) X->
   ~Vset.mem x IX ->
   Vset.disjoint (fv_args args) X ->
   equiv Meq E1 ([x <c- f with args]++S) E2 (S++[x <c- f with args]) Meq.
 Proof.
  intros;apply equiv_eq_sem;intros.
  rewrite deno_app,deno_call, Mcomp.
  transitivity (Mlet (([[ proc_body E1 f ]]) E1 (init_mem E1 f args m))
  (fun x0 : Mem.t k => Mlet ([[S]] E1 x0) (fun m' => (Munit (return_mem E2 x f m m'))))).
    apply Mlet_eq_compat;[trivial | refine (ford_eq_intro _); intros m'].
    refine (ford_eq_intro _);intros g;simpl.
    rewrite (ford_eq_elim (@Modify_deno _ _ _ Modify_S1 k m')), Mlet_simpl.
    rewrite (ford_eq_elim (@Modify_deno _ _ _ Modify_S1 k (return_mem E1 x f m m'))), Mlet_simpl.
    apply EqObs_deno with IX X;[apply EqObs_S1 with E2;trivial | | ].
    intros m1 m2 Heq;simpl.
    replace  (return_mem E1 x f m m' {!X <<- m1!}) with (return_mem E2 x f m (m' {!X <<- m2!}));
     [trivial | ].
    apply Mem.eq_leibniz;intros (ty, y).
    destruct (Var.eq_dec x y).
    inversion e;simpl.
    rewrite return_mem_dest, update_mem_notin, return_mem_dest;trivial.
    rewrite <- H1;apply depend_only_fv_expr;apply req_mem_update_disjoint;trivial.
    intros Hin;apply H3;auto with set.
    case_eq (Var.is_global y);intros.
    rewrite return_mem_global;trivial.
    destruct (VsetP.mem_dec y X).
    repeat rewrite update_mem_in;trivial;rewrite Heq;trivial.
    repeat rewrite update_mem_notin;trivial;rewrite return_mem_global;trivial.
    assert (Var.is_local y) by (unfold Var.is_local;rewrite H5;trivial);clear H5.
    assert (~Vset.mem y X). 
      intros Hin;unfold Var.is_local in H6;
       rewrite (X_global _ (Vset.union_complete_r I X y Hin)) in H6;discriminate.
    rewrite update_mem_notin, return_mem_local, return_mem_local;trivial.
    intros ty y Hin;rewrite return_mem_global;[ trivial | | auto].
    intros Heq;apply H3;rewrite Heq;trivial.
  refine (ford_eq_intro _);simpl;intros g.
  rewrite <- (@deno_app_elim k E1 (proc_body E1 f) S).
  rewrite (ford_eq_elim (equiv_Meq_deno _ _ _ _ H k (init_mem E1 f args m))).
  replace (init_mem E1 f args m) with (init_mem E2 f args m);
    [ | symmetry;apply init_mem_eq2;trivial].
  rewrite deno_app_elim, (deno_app_elim E2 S [x <c- f with args] m).
  rewrite (ford_eq_elim (@Modify_deno _ _ _ Modify_S2 k m)), Mlet_simpl.
  rewrite (ford_eq_elim (@Modify_deno _ _ _ Modify_S2 k (init_mem E2 f args m))), Mlet_simpl.
  apply EqObs_deno with IX X;[apply EqObs_S2 with E1;trivial | | ].
  simpl;intros.
  rewrite (deno_call_elim E2 x f args (m {!X <<-m2!})).
  replace (init_mem E2 f args (m {!X <<- m2!})) with (init_mem E2 f args m {!X <<- m1!}).
  refine (mu_stable_eq _ _ _ (ford_eq_intro _));intros m'.
  replace (return_mem E2 x f m m') with (return_mem E2 x f (m {!X <<- m2!}) m');trivial.
    apply Mem.eq_leibniz;intros (ty, y).
    destruct (Var.eq_dec x y).
    inversion e;simpl.
    rewrite return_mem_dest, return_mem_dest;trivial.
    case_eq (Var.is_global y);intros.
    repeat rewrite return_mem_global;trivial.
    assert (Var.is_local y) by (unfold Var.is_local;rewrite H6;trivial);clear H6.
      repeat rewrite return_mem_local;trivial.
    rewrite update_mem_notin;trivial.
    intros Hin;unfold Var.is_local in H7;rewrite X_global in H7;[discriminate | auto with set].
  apply Mem.eq_leibniz;intros (ty, y).
   destruct (VsetP.mem_dec y X).
   rewrite update_mem_in, init_mem_global, update_mem_in;auto with set.
   rewrite update_mem_notin;trivial.
   case_eq (Var.is_global y);intros.
   rewrite init_mem_global, init_mem_global, update_mem_notin;trivial.
   assert (Var.is_local y) by (unfold Var.is_local;rewrite H6;trivial);clear H6.
   apply init_mem_local;trivial.
   destruct depend_only_fv_expr_rec_and.
   apply (H8 _ args nil);apply req_mem_sym;apply req_mem_update_disjoint;trivial.
  intros ty y Hin;rewrite init_mem_global;auto.
 Qed.

  Lemma swap_sample_call2 : forall t (f:Proc.proc t) (x:Var.var t) args M, 
   Modify E1 M (proc_body E1 f) ->
   Modify E2 M (proc_body E2 f) ->
   equiv Meq E1 ((proc_body E1 f)++S) E2 (S++(proc_body E2 f)) 
        (kreq_mem (Vset.union (Vset.union (get_globals M) X) (fv_expr (proc_res E1 f)))) ->
   proc_params E1 f = proc_params E2 f ->
   proc_res E1 f = proc_res E2 f ->
   Vset.disjoint (fv_expr (proc_res E1 f)) X->
   ~Vset.mem x IX ->
   Vset.disjoint (fv_args args) X ->
   equiv Meq E1 ([x <c- f with args]++S) E2 (S++[x <c- f with args]) Meq.
 Proof.
  intros;apply equiv_eq_sem;intros.
  rewrite deno_app,deno_call, Mcomp.
  transitivity (Mlet (([[ proc_body E1 f ]]) E1 (init_mem E1 f args m))
  (fun x0 : Mem.t k => Mlet ([[S]] E1 x0) (fun m' => (Munit (return_mem E2 x f m m'))))).
    apply Mlet_eq_compat;[trivial | refine (ford_eq_intro _); intros m'].
    refine (ford_eq_intro _);intros g;simpl.
    rewrite (ford_eq_elim (@Modify_deno _ _ _ Modify_S1 k m')), Mlet_simpl.
    rewrite (ford_eq_elim (@Modify_deno _ _ _ Modify_S1 k (return_mem E1 x f m m'))), Mlet_simpl.
    apply EqObs_deno with IX X;[apply EqObs_S1 with E2;trivial | | ].
    intros m1 m2 Heq;simpl.
    replace  (return_mem E1 x f m m' {!X <<- m1!}) with (return_mem E2 x f m (m' {!X <<- m2!}));
     [trivial | ].
    apply Mem.eq_leibniz;intros (ty, y).
    destruct (Var.eq_dec x y).
    inversion e;simpl.
    rewrite return_mem_dest, update_mem_notin, return_mem_dest;trivial.
    rewrite <- H3;apply depend_only_fv_expr;apply req_mem_update_disjoint;trivial.
    intros Hin;apply H5;auto with set.
    case_eq (Var.is_global y);intros.
    rewrite return_mem_global;trivial.
    destruct (VsetP.mem_dec y X).
    repeat rewrite update_mem_in;trivial;rewrite Heq;trivial.
    repeat rewrite update_mem_notin;trivial;rewrite return_mem_global;trivial.
    assert (Var.is_local y) by (unfold Var.is_local;rewrite H7;trivial);clear H7.
    assert (~Vset.mem y X). 
      intros Hin;unfold Var.is_local in H8;
       rewrite (X_global _ (Vset.union_complete_r I X y Hin)) in H8;discriminate.
    rewrite update_mem_notin, return_mem_local, return_mem_local;trivial.
    intros ty y Hin;rewrite return_mem_global;[ trivial | | auto].
    intros Heq;apply H5;rewrite Heq;trivial.
  refine (ford_eq_intro _);simpl;intros g.
  rewrite <- (@deno_app_elim k E1 (proc_body E1 f) S).
  assert (init_mem E1 f args m = init_mem E2 f args m).
   apply Mem.eq_leibniz;intros (ty, y).
   case_eq (Var.is_global y);intros.
   rewrite init_mem_global, init_mem_global;trivial.
   assert (Var.is_local y) by (unfold Var.is_local;rewrite H7;trivial);clear H7.
  rewrite (init_mem_eq2 E1 E2 f args args m H2 (refl_equal (E.eval_args args m))).
  apply init_mem_local;trivial.
  rewrite H7;clear H7.
  assert (Modify E1 (Vset.union (Vset.union M0 (fv_expr (proc_res E1 f))) X) (proc_body E1 f ++ S)).
    apply Modify_app;trivial.
    apply Modify_weaken with M0;auto with set.
 rewrite (Modify_deno_elim H7 (init_mem E2 f args m)).
 set (F := fun m' : Mem.t k =>
   g
     (return_mem E2 x f m
        (init_mem E2 f args m
         {!Vset.union (Vset.union M0 (fv_expr (proc_res E1 f))) X <<- m'!}))).
 assert (forall m1 m2 : Mem.t k,
  kreq_mem (Vset.union (Vset.union (get_globals M0) X) (fv_expr (proc_res E1 f))) m1 m2 ->
  F m1 == F m2).
   unfold F;intros.
  match goal with |- _ ?x1 == _ ?x2 => replace x1 with x2;[trivial | ] end.
    apply Mem.eq_leibniz;intros (ty, y).
    destruct (Var.eq_dec x y).
    inversion e;simpl.
    rewrite return_mem_dest, return_mem_dest;trivial.
      apply depend_only_fv_expr.
    rewrite <- H3; apply req_mem_trans with m2.
    eapply req_mem_weaken;[ | apply req_mem_update_mem_l];auto with set.
    apply req_mem_trans with m1.
    eapply req_mem_weaken;[ | apply req_mem_sym;apply H8];auto with set.
    apply req_mem_sym;eapply req_mem_weaken;[ | apply req_mem_update_mem_l];auto with set.
    case_eq (Var.is_global y);intros.
    repeat rewrite return_mem_global;trivial.
    case_eq (Vset.mem y (Vset.union (Vset.union M0 (fv_expr (proc_res E1 f))) X));intros.
      rewrite update_mem_in, update_mem_in;trivial.
      symmetry;apply H8.
      change (is_true (Vset.mem y (Vset.union (Vset.union M0 (fv_expr (proc_res E1 f))) X))) in H10.
      repeat rewrite VsetP.union_spec.
      rewrite VsetP.union_spec in H10;destruct H10;auto.
      rewrite VsetP.union_spec in H10;destruct H10;auto.
      left;left; apply get_globals_complete;trivial.
      rewrite <- not_is_true_false in H10.
      rewrite update_mem_notin, update_mem_notin;trivial.
    assert (Var.is_local y) by (unfold Var.is_local;rewrite H9;trivial);clear H9.
      repeat rewrite return_mem_local;trivial.
 rewrite (equiv_deno H1 F F H8 (init_mem E2 f args m) (init_mem E2 f args m));clear H8 H7.
  assert (Modify E2 (Vset.union (Vset.union M0 (fv_expr (proc_res E1 f))) X) (S ++ proc_body E2 f)).
    rewrite VsetP.union_sym;  apply Modify_app;trivial.
    apply Modify_weaken with M0;auto with set.
 unfold F.
 rewrite <- (Modify_deno_elim H7 (init_mem E2 f args m) (fun m' => g (return_mem E2 x f m m'))).
 rewrite deno_app_elim, (deno_app_elim E2 S [x <c- f with args] m).
 rewrite (ford_eq_elim (@Modify_deno _ _ _ Modify_S2 k m)), Mlet_simpl.
 rewrite (ford_eq_elim (@Modify_deno _ _ _ Modify_S2 k (init_mem E2 f args m))), Mlet_simpl.
 apply EqObs_deno with IX X;[apply EqObs_S2 with E1;trivial| | ].
  simpl;intros.
  rewrite (deno_call_elim E2 x f args (m {!X <<-m2!})).
  replace (init_mem E2 f args (m {!X <<- m2!})) with (init_mem E2 f args m {!X <<- m1!}).
  refine (mu_stable_eq _ _ _ (ford_eq_intro _));intros m'.
  replace (return_mem E2 x f m m') with (return_mem E2 x f (m {!X <<- m2!}) m');trivial.
    apply Mem.eq_leibniz;intros (ty, y).
    destruct (Var.eq_dec x y).
    inversion e;simpl.
    rewrite return_mem_dest, return_mem_dest;trivial.
    case_eq (Var.is_global y);intros.
    repeat rewrite return_mem_global;trivial.
    assert (Var.is_local y) by (unfold Var.is_local;rewrite H9;trivial);clear H9.
      repeat rewrite return_mem_local;trivial.
    rewrite update_mem_notin;trivial.
    intros Hin;unfold Var.is_local in H10;rewrite X_global in H10;[discriminate | auto with set].
  apply Mem.eq_leibniz;intros (ty, y).
   destruct (VsetP.mem_dec y X).
   rewrite update_mem_in, init_mem_global, update_mem_in;auto with set.
   rewrite update_mem_notin;trivial.
   case_eq (Var.is_global y);intros.
   rewrite init_mem_global, init_mem_global, update_mem_notin;trivial.
   assert (Var.is_local y) by (unfold Var.is_local;rewrite H9;trivial);clear H9.
   apply init_mem_local;trivial.
   destruct depend_only_fv_expr_rec_and.
   apply (H11 _ args nil);apply req_mem_sym;apply req_mem_update_disjoint;trivial.
  intros ty y Hin;rewrite init_mem_global;auto.
  trivial.
 Qed.

 Lemma swap_equiv_le_call : forall t (f:Proc.proc t) (x:Var.var t) args, 
   equiv_le E1 (S++(proc_body E1 f)) E2 ((proc_body E2 f)++S) Meq ->
   proc_params E1 f = proc_params E2 f ->
   proc_res E1 f = proc_res E2 f ->
   Vset.disjoint (fv_expr (proc_res E1 f)) X->
   ~Vset.mem x IX ->
   Vset.disjoint (fv_args args) X ->
   equiv_le E1 (S++[x <c- f with args]) E2 ([x <c- f with args]++S) Meq.
 Admitted.

 Lemma swap_equiv_le_call2 : forall t (f:Proc.proc t) (x:Var.var t) args M, 
   Modify E1 M (proc_body E1 f) ->
   Modify E2 M (proc_body E2 f) ->
   equiv_le E1 (S++(proc_body E1 f)) E2 ((proc_body E2 f)++S) 
        (kreq_mem (Vset.union (Vset.union (get_globals M) X) (fv_expr (proc_res E1 f)))) ->
   proc_params E1 f = proc_params E2 f ->
   proc_res E1 f = proc_res E2 f ->
   Vset.disjoint (fv_expr (proc_res E1 f)) X->
   ~Vset.mem x IX ->
   Vset.disjoint (fv_args args) X ->
   equiv_le E1 (S++[x <c- f with args]) E2 ([x <c- f with args]++S) Meq.
 Admitted.

 Section DEC.

  Definition sw_info t (f:Proc.proc t) := 
   forall x args, ~Vset.mem (Var.mkV x) IX -> 
    Vset.disjoint (fv_args args) X -> 
    equiv Meq E1 ([x <c- f with args] ++ S) E2 (S ++ [x<c- f with args]) Meq.
  
  Definition sw_info_le t (f:Proc.proc t) := 
   forall x args, ~Vset.mem (Var.mkV x) IX -> 
    Vset.disjoint (fv_args args) X -> 
    equiv_le E1 (S++[x <c- f with args]) E2 ([x<c- f with args]++S) Meq.
  
  Variable pi : forall t (f:Proc.proc t),option (sw_info t f).
 
  Variable pi_le : forall t (f:Proc.proc t),option (sw_info_le t f).

  Definition check_swap_base (bi:I.baseInstr) : bool :=
   match bi with
   | I.Assign t x e => negb (Vset.mem x IX) && Vset.disjoint X (fv_expr e)
   | I.Random t x d => negb (Vset.mem x IX) && Vset.disjoint X (fv_distr d)
   end.

  Fixpoint check_swap_i (i:I.instr) : bool := 
    match i with
    | I.Instr bi => check_swap_base bi
    | I.Cond e c1 c2 => 
         Vset.disjoint (fv_expr e) X && forallb check_swap_i c1 && forallb check_swap_i c2
    | I.While e c =>  Vset.disjoint (fv_expr e) X && forallb check_swap_i c
    | I.Call t x f args =>
      match pi t f with
      | Some _ => negb (Vset.mem x IX) && Vset.disjoint (fv_args args) X
      | _ => false
      end
    end.

  Definition check_swap_c (c:cmd) := forallb check_swap_i c.

  Fixpoint check_swap_le_i (i:I.instr) : bool := 
    match i with
    | I.Instr bi => check_swap_base bi
    | I.Cond e c1 c2 => 
         Vset.disjoint (fv_expr e) X && forallb check_swap_le_i c1 && forallb check_swap_le_i c2
    | I.While e c =>  Vset.disjoint (fv_expr e) X && forallb check_swap_le_i c
    | I.Call t x f args =>
      match pi_le t f with
      | Some _ => negb (Vset.mem x IX) && Vset.disjoint (fv_args args) X
      | _ => false
      end
    end.

  Definition check_swap_le_c (c:cmd) := forallb check_swap_le_i c.

  Lemma check_swap_c_correct : forall c,
   check_swap_c c -> 
   equiv Meq E1 (c++S) E2 (S++c) Meq.
  Proof.
   induction c using I.cmd_ind with 
    (Pi := fun i => check_swap_i i -> equiv Meq E1 ([i]++S) E2 (S++[i]) Meq);simpl;intros.
   destruct i;simpl in H; rewrite is_true_andb, is_true_negb in H;destruct H.
   apply swap_sample_assign;trivial.
   apply swap_sample_random;trivial.
   repeat rewrite is_true_andb in H;decompose [and] H.
   apply swap_sample_if;auto.
   rewrite is_true_andb in H;destruct H;apply swap_sample_while;auto.
   destruct pi;[ | discriminate].
   unfold sw_info in s;decompose [and] s;rewrite is_true_andb, is_true_negb in H;destruct H.
   apply s;trivial.
   refine swap_sample_nil.
   case_eq (check_swap_i i);intros Heq;rewrite Heq in H;[ | discriminate].
   apply swap_sample_cons;auto.
  Qed.

  Lemma check_swap_le_c_correct : forall c,
   check_swap_le_c c -> 
   equiv_le E1 (S++c) E2 (c++S) Meq.
  Proof.
   induction c using I.cmd_ind with 
    (Pi := fun i => check_swap_le_i i -> equiv_le E1 (S++[i]) E2 ([i]++S) Meq);simpl;intros.
   destruct i;simpl in H; rewrite is_true_andb, is_true_negb in H;destruct H.
   red;intros;apply mu_le_compat;[apply Oeq_le | trivial].
   apply equiv_Meq_deno;apply equiv_sym;auto.
   apply swap_sample_assign;trivial;apply EqObs_sym;trivial.
   red;intros;apply mu_le_compat;[apply Oeq_le | trivial].
   apply equiv_Meq_deno;apply equiv_sym;auto.
    apply swap_sample_random;trivial;apply EqObs_sym;trivial.
   repeat rewrite is_true_andb in H;decompose [and] H.
   apply swap_equiv_le_if;auto.
   rewrite is_true_andb in H;destruct H;apply swap_equiv_le_while;auto.
   destruct pi_le;[ | discriminate].
   unfold sw_info in s;decompose [and] s;rewrite is_true_andb, is_true_negb in H;destruct H.
   apply s;trivial.
   refine swap_equiv_le_nil.
   case_eq (check_swap_le_i i);intros Heq;rewrite Heq in H;[ | discriminate].
   apply swap_equiv_le_cons;auto.
  Qed.

  Definition add_sw_info t (f:Proc.proc t) 
   (H:equiv Meq E1 (proc_body E1 f ++ S) E2 (S ++ proc_body E2 f) Meq) : 
   forall tg (g:Proc.proc tg),option (sw_info tg g).
   intros t f H.
   case_eq (eqb_var_decl (proc_params E1 f) (proc_params E2 f)
           && E.eqb (proc_res E1 f) (proc_res E2 f)
           && Vset.disjoint (fv_expr (proc_res E1 f)) X).
   intros H1 tg g.
   case_eq (Proc.eqb f g);intros Heq.
   refine (Some _).
   abstract (
   unfold sw_info;assert (W:= Proc.eqb_spec_dep f g);rewrite Heq in W;inversion W;simpl;
   repeat rewrite andb_true_iff in H1;intuition;
   assert (W1:= eqb_var_decl_spec (proc_params E1 f) (proc_params E2 f));
   rewrite H1 in W1;
   assert (W2 := E.eqb_spec (proc_res E1 f) (proc_res E2 f));rewrite H6 in W2;
   intros;apply swap_sample_call;trivial).
   exact (pi tg g).
   intros _;exact pi.
  Defined.

 Definition add_sw_info2 t (f:Proc.proc t) M1 M2
  (HM1: Modify E1 M1 (proc_body E1 f)) (HM2: Modify E2 M2 (proc_body E2 f))
  (H:equiv Meq E1 (proc_body E1 f ++ S) E2 (S ++ proc_body E2 f) 
   (kreq_mem (Vset.union (Vset.union (get_globals (Vset.union M1 M2)) X) (fv_expr (proc_res E1 f))))) : 
  forall tg (g:Proc.proc tg),option (sw_info tg g).
   intros t f M1 M2 HM1 HM2 H.
   case_eq (eqb_var_decl (proc_params E1 f) (proc_params E2 f)
           && E.eqb (proc_res E1 f) (proc_res E2 f)
           && Vset.disjoint (fv_expr (proc_res E1 f)) X).
   intros H1 tg g.
   case_eq (Proc.eqb f g);intros Heq.
   refine (Some _).
   abstract (unfold sw_info;assert (W:= Proc.eqb_spec_dep f g);rewrite Heq in W;inversion W;simpl;
   repeat rewrite andb_true_iff in H1;intuition;
   assert (W1:= eqb_var_decl_spec (proc_params E1 f) (proc_params E2 f));
   rewrite H1 in W1;
   assert (W2 := E.eqb_spec (proc_res E1 f) (proc_res E2 f));rewrite H6 in W2;
   intros;apply swap_sample_call2 with (Vset.union M1 M2);trivial;
   eapply Modify_weaken;eauto with set).
   exact (pi tg g).
   intros _;exact pi.
  Defined.

  Definition add_sw_info_refl t (f:Proc.proc t) : 
   forall tg (g:Proc.proc tg),option (sw_info tg g).
  intros t f.
  case_eq (I.ceqb (proc_body E1 f) (proc_body E2 f) &&
   check_swap_c (proc_body E2 f));intros Heq.
  refine (add_sw_info t f _).
  abstract (apply andb_true_iff in Heq;destruct Heq as (Heq, Hc);
  assert (W:= I.ceqb_spec(proc_body E1 f) (proc_body E2 f));rewrite Heq in W;rewrite W;
  apply check_swap_c_correct;trivial).
  exact pi.
  Defined.

 Definition add_sw_info_le t (f:Proc.proc t) 
    (H:equiv_le E1 (S++proc_body E1 f) E2 ((proc_body E2 f)++S) Meq) : 
    forall tg (g:Proc.proc tg),option (sw_info_le tg g).
   intros t f H.
   case_eq (eqb_var_decl (proc_params E1 f) (proc_params E2 f)
           && E.eqb (proc_res E1 f) (proc_res E2 f)
           && Vset.disjoint (fv_expr (proc_res E1 f)) X).
   intros H1 tg g.
   case_eq (Proc.eqb f g);intros Heq.
   refine (Some _).
   abstract ( 
   unfold sw_info_le;assert (W:= Proc.eqb_spec_dep f g);rewrite Heq in W;inversion W;simpl;
   repeat rewrite andb_true_iff in H1;intuition;
   assert (W1:= eqb_var_decl_spec (proc_params E1 f) (proc_params E2 f));
   rewrite H1 in W1;
   assert (W2 := E.eqb_spec (proc_res E1 f) (proc_res E2 f));rewrite H6 in W2;
   intros;apply swap_equiv_le_call;trivial).
   exact (pi_le tg g).
   intros _;exact pi_le.
  Defined.

 Definition add_sw_info2_le t (f:Proc.proc t) M1 M2
    (HM1: Modify E1 M1 (proc_body E1 f)) (HM2: Modify E2 M2 (proc_body E2 f))
    (H:equiv_le E1 (S ++ proc_body E1 f) E2 (proc_body E2 f ++ S) 
        (kreq_mem (Vset.union (Vset.union (get_globals (Vset.union M1 M2)) X) (fv_expr (proc_res E1 f))))) : 
    forall tg (g:Proc.proc tg),option (sw_info_le tg g).
   intros t f M1 M2 HM1 HM2 H.
   case_eq (eqb_var_decl (proc_params E1 f) (proc_params E2 f)
           && E.eqb (proc_res E1 f) (proc_res E2 f)
           && Vset.disjoint (fv_expr (proc_res E1 f)) X).
   intros H1 tg g.
   case_eq (Proc.eqb f g);intros Heq.
   refine (Some _).
   abstract (unfold sw_info_le;assert (W:= Proc.eqb_spec_dep f g);rewrite Heq in W;inversion W;simpl;
   repeat rewrite andb_true_iff in H1;intuition;
   assert (W1:= eqb_var_decl_spec (proc_params E1 f) (proc_params E2 f));
   rewrite H1 in W1;
   assert (W2 := E.eqb_spec (proc_res E1 f) (proc_res E2 f));rewrite H6 in W2;
   intros;apply swap_equiv_le_call2 with (Vset.union M1 M2);trivial;
   eapply Modify_weaken;eauto with set).
   exact (pi_le tg g).
   intros _;exact pi_le.
  Defined.


  Definition add_sw_info_le_refl t (f:Proc.proc t) : 
   forall tg (g:Proc.proc tg),option (sw_info_le tg g).
  intros t f.
  case_eq (I.ceqb (proc_body E1 f) (proc_body E2 f) &&
           check_swap_le_c (proc_body E2 f));intros Heq.
  refine (add_sw_info_le t f _).
  abstract (apply andb_true_iff in Heq;destruct Heq as (Heq, Hc);
  assert (W:= I.ceqb_spec(proc_body E1 f) (proc_body E2 f));rewrite Heq in W;rewrite W;
  apply check_swap_le_c_correct;trivial).
  exact pi_le.
  Defined.

  Section ADV.
   
   Variables PrOrcl PrPriv : PrSet.t.
   Variables Gadv Gcomm : Vset.t.
   
   Hypothesis EqA : Eq_adv_decl PrOrcl PrPriv E1 E2.
   
   Hypothesis X_G : Vset.disjoint X (Vset.union Gadv Gcomm).
   Hypothesis I_G : Vset.disjoint I Gadv.
   
   Hypothesis piPrOrcl : 
    forall tr (f:Proc.proc tr), PrSet.mem (BProc.mkP f) PrOrcl -> pi _ f <> None.
   
   Hypothesis pilePrOrcl : 
    forall tr (f:Proc.proc tr), PrSet.mem (BProc.mkP f) PrOrcl -> pi_le _ f <> None.

   Lemma WFRead_not_mem: forall I te (e:E.expr te) x,
    (forall x : Vset.E.t, Vset.mem x I -> Var.is_local x) ->
    WFRead Gadv Gcomm e I -> Vset.mem x (fv_expr e) -> ~ Vset.mem x X.
   Proof.
    intros.
    destruct (H0 _ H1).
    assert (W:= H _ H2); unfold Var.is_local in W; intro H3.
    rewrite (X_global _ (@Vset.union_complete_r I _ _ H3)) in W;discriminate W.
    apply VsetP.disjoint_mem_not_mem with (Vset.union Gadv Gcomm).
    apply VsetP.disjoint_sym; trivial.
    rewrite VsetP.union_spec; trivial.
   Qed.
   
   Lemma WFRead_disjoint: forall I te (e:E.expr te),
    (forall x : Vset.E.t, Vset.mem x I -> Var.is_local x) ->
    WFRead Gadv Gcomm e I -> Vset.disjoint (fv_expr e) X.
   Proof.
    intros.
    apply VsetP.disjoint_complete; intros.
    eapply WFRead_not_mem; eauto.
   Qed.
   
   Lemma WFWrite_not_mem : forall I x,
    (forall x : Vset.E.t, Vset.mem x I -> Var.is_local x) ->
    WFWrite Gadv x -> ~ Vset.mem x IX.
   Proof.
    intros; case_eq (Var.is_global x); intros.
    apply VsetP.disjoint_mem_not_mem with Gadv;auto.
    apply disjoint_union.
    apply VsetP.disjoint_sym; trivial.
    apply VsetP.disjoint_subset_l with (Vset.union Gadv Gcomm);auto using VsetP.disjoint_sym with set .
    intros Hin;rewrite (X_global _ Hin) in H1;discriminate.
   Qed.
   
   Hypothesis E1_eq_E2 : Eq_adv_decl PrOrcl PrPriv E1 E2.
   
   Lemma Adv_c_context : forall I c O, 
    WFAdv_c PrOrcl PrPriv Gadv Gcomm E1 I c O -> 
    (forall x, Vset.mem x I -> Var.is_local x) -> 
    equiv Meq E1 (c++S) E2 (S++c) Meq.
   Proof.
    induction 1 using WFAdv_c_prop with 
     (P0:=fun I i O (H:WFAdv_i PrOrcl PrPriv Gadv Gcomm E1 I i O) => 
      (forall x, Vset.mem x I -> Var.is_local x) -> equiv Meq E1 ([i]++S) E2 (S++[i]) Meq); intros.
    apply swap_sample_nil.
    apply swap_sample_cons;auto.
    apply IHWFAdv_c0; apply (WFAdv_i_local w H0).
    apply swap_sample_assign;auto.
    destruct x as (tv, v);apply (WFWrite_not_mem I0 v H w).
    apply VsetP.disjoint_sym;apply (WFRead_disjoint _ _ _  H w0).
    apply swap_sample_random;auto.
    destruct x as (tv, v);apply (WFWrite_not_mem I0 v H w).
    apply VsetP.disjoint_complete; intros.
    intros Hin;destruct (w0 _ Hin).
    assert (W:= H _ H1);unfold Var.is_local in W;rewrite (X_global _ (@Vset.union_complete_r I _ _ H0)) in W;
     discriminate.
    apply (@VsetP.disjoint_mem_not_mem _ _ X_G x0);[ | rewrite VsetP.union_spec];trivial.
    apply swap_sample_if;[apply (WFRead_disjoint _ _ _  H1 w) | | ];auto.
    apply swap_sample_while;[apply (WFRead_disjoint _ _ _  H0 w) | ];auto.
    generalize (piPrOrcl _ _ i);destruct (pi _ f);[intros _ | intros Heq;elim Heq;trivial].
    apply s.
    apply (WFWrite_not_mem I0 x H w0).
    apply VsetP.disjoint_complete; intros.
    destruct (fv_args_fv_expr _ _ H0) as (te, (e, (W1, W2))).
    eapply WFRead_not_mem; eauto.
    assert (W:= E1_eq_E2 _ _ n n0);decompose [and] W;clear W.
    assert (forall x0 : VarP.Edec.t,
          Vset.mem x0 (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x0).
    intros; destruct x0; apply Vset_of_var_decl_ind with (lv:=proc_params E1 f) 
     (P:= fun t (x:Var.var t) =>Var.is_local x); trivial.
    intros t1 x0 W2; assert (W:= proc_params_local E1 f x0 W2).
    rewrite <- Var.vis_local_local; trivial.
    apply swap_sample_call;trivial.
    rewrite <- H3;apply IHWFAdv_c;trivial.
    apply WFRead_disjoint with O;[ apply (WFAdv_c_local H H2) | trivial].
    eapply WFWrite_not_mem; eauto.
    apply VsetP.disjoint_complete; intros.
    destruct (fv_args_fv_expr _ _ H5) as (te, (e, (W1, W2))).
    apply (WFRead_not_mem _ _ _  _ H0 (w0 _ _ W1));trivial.
   Qed.
   
   Lemma Adv_c_context_le : forall I c O, 
    WFAdv_c PrOrcl PrPriv Gadv Gcomm E1 I c O -> 
    (forall x, Vset.mem x I -> Var.is_local x) -> 
    equiv_le E1 (S++c) E2 (c++S) Meq.
   Proof.
    induction 1 using WFAdv_c_prop with 
     (P0:=fun I i O (H:WFAdv_i PrOrcl PrPriv Gadv Gcomm E1 I i O) => 
      (forall x, Vset.mem x I -> Var.is_local x) -> equiv_le E1 (S++[i]) E2 ([i]++S) Meq); intros.
    apply swap_equiv_le_nil.
    apply swap_equiv_le_cons;auto.
    apply IHWFAdv_c0; apply (WFAdv_i_local w H0).
    red;intros;apply mu_le_compat;[apply Oeq_le | trivial].
    apply equiv_Meq_deno;apply equiv_sym;auto.
    apply swap_sample_assign;trivial.
    apply equiv_sym;auto.
    destruct x as (tv, v);apply (WFWrite_not_mem I0 v H w).
    apply VsetP.disjoint_sym;apply (WFRead_disjoint _ _ _  H w0).
    red;intros;apply mu_le_compat;[apply Oeq_le | trivial].
    apply equiv_Meq_deno;apply equiv_sym;auto.
    apply swap_sample_random;trivial.
    apply equiv_sym;auto.
    destruct x as (tv, v);apply (WFWrite_not_mem I0 v H w).
    apply VsetP.disjoint_complete; intros.
    intros Hin;destruct (w0 _ Hin).
    assert (W:= H _ H2);unfold Var.is_local in W;rewrite (X_global _ (@Vset.union_complete_r I _ _ H1)) in W;
     discriminate.
    apply (@VsetP.disjoint_mem_not_mem _ _ X_G x0);[ | rewrite VsetP.union_spec];trivial.
    apply swap_equiv_le_if;[apply (WFRead_disjoint _ _ _  H1 w) | | ];auto.
    apply swap_equiv_le_while;[apply (WFRead_disjoint _ _ _  H0 w) | ];auto.
    generalize (pilePrOrcl _ _ i);destruct (pi_le _ f);[intros _ | intros Heq;elim Heq;trivial].
    apply s.
    apply (WFWrite_not_mem I0 x H w0).
    apply VsetP.disjoint_complete; intros.
    destruct (fv_args_fv_expr _ _ H0) as (te, (e, (W1, W2))).
    eapply WFRead_not_mem; eauto.
    assert (W:= E1_eq_E2 _ _ n n0);decompose [and] W;clear W.
    assert (forall x0 : VarP.Edec.t,
     Vset.mem x0 (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x0).
    intros; destruct x0; apply Vset_of_var_decl_ind with (lv:=proc_params E1 f) 
     (P:= fun t (x:Var.var t) =>Var.is_local x); trivial.
    intros t1 x0 W2; assert (W:= proc_params_local E1 f x0 W2).
    rewrite <- Var.vis_local_local; trivial.
    apply swap_equiv_le_call;trivial.
    rewrite <- H3;apply IHWFAdv_c;trivial.
    apply WFRead_disjoint with O;[ apply (WFAdv_c_local H H2) | trivial].
    eapply WFWrite_not_mem; eauto.
    apply VsetP.disjoint_complete; intros.
    destruct (fv_args_fv_expr _ _ H5) as (te, (e, (W1, W2))).
    apply (WFRead_not_mem _ _ _  _ H0 (w0 _ _ W1));trivial.
   Qed.
  
  End ADV. 
 
 End DEC.
 
 Definition add_sw_info_Adv (pi : forall (t : T.type) (f : Proc.proc t), option (sw_info t f))
  t (f:Proc.proc t) (PrOrcl PrPriv : PrSet.t) (Gadv Gcomm : Vset.t) :
  Eq_adv_decl PrOrcl PrPriv E1 E2 ->
  WFAdv PrOrcl PrPriv Gadv Gcomm E1 f -> 
  forall tg (g:Proc.proc tg),option (sw_info tg g).
  intros pi t f PrOrcl PrPriv Gadv Gcomm HEQ HWF.
  case_eq (Vset.disjoint X (Vset.union Gadv Gcomm));intros Heq;[ | exact pi].
  case_eq (Vset.disjoint I Gadv);intros HeqI;[ | exact pi].
  case_eq (PrSet.forallb (fun f => match pi _ (BProc.p_name f) with None => false | _ => true end) PrOrcl);
  intros Heq0;[ | exact pi].
  case_eq (PrSet.mem (BProc.mkP f) PrOrcl);intros Hnot;[ exact pi | ].
  case_eq (PrSet.mem (BProc.mkP f) PrPriv);intros Hnot1;[ exact pi | ].
  intros tg g;case_eq (Proc.eqb f g);intros Heq1;[ | apply (pi _ g)].
   refine (Some _).
  abstract (generalize (Proc.eqb_spec_dep f g);rewrite Heq1;intros Heq2;inversion Heq2;
   simpl;clear H2 H1 H Heq2 Heq1 g tg;
   destruct (HEQ _ f) as (H, (H0, H1));[rewrite Hnot;discriminate | rewrite Hnot1;discriminate | ];
   destruct HWF as (O, (W1, W2));
   assert (forall x0 : VarP.Edec.t,
     Vset.mem x0 (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x0) by (
      intros; destruct x0; apply Vset_of_var_decl_ind with (lv:=proc_params E1 f) 
        (P:= fun t (x:Var.var t) =>Var.is_local x); trivial;
        intros t1 x0 W3; assert (W:= proc_params_local E1 f x0 W3);
        rewrite <- Var.vis_local_local; trivial);
  set (F:= (fun f : ProcD.t =>
          match pi (BProc.p_type f) (BProc.p_name f) with
          | Some _ => true
          | None => false
          end));
  assert (W3:forall x y : ProcD.t, ProcD.eq x y -> F x = F y) by 
   (intros x y Heq1;inversion Heq1;trivial);
  red;intros;apply swap_sample_call;trivial;
   [ | apply VsetP.disjoint_complete; intros;refine (WFRead_not_mem _ _ Heq _ _ _ _ _ W2 _);
    [apply (WFAdv_c_local W1)| ];trivial ];
  rewrite H0;apply Adv_c_context with pi PrOrcl PrPriv Gadv
    Gcomm (Vset_of_var_decl (proc_params E1 f)) O;trivial;
  [ intros tr f0 Hin;assert (W:= PrSet.forallb_correct F W3 _ Heq0 _ Hin);
    unfold F in W;simpl in W;destruct (pi tr f0);discriminate
  | rewrite <- H0;trivial]).
  Defined.

  Definition add_sw_info_le_Adv 
   (pi : forall (t : T.type) (f : Proc.proc t), option (sw_info_le t f))
   t (f:Proc.proc t) (PrOrcl PrPriv : PrSet.t) (Gadv Gcomm : Vset.t) :
   Eq_adv_decl PrOrcl PrPriv E1 E2 ->
   WFAdv PrOrcl PrPriv Gadv Gcomm E1 f -> 
   forall tg (g:Proc.proc tg),option (sw_info_le tg g).
  intros pi t f PrOrcl PrPriv Gadv Gcomm HEQ HWF.
  case_eq (Vset.disjoint X (Vset.union Gadv Gcomm));intros Heq;[ | exact pi].
  case_eq (Vset.disjoint I Gadv);intros HeqI;[ | exact pi].
  case_eq (PrSet.forallb (fun f => match pi _ (BProc.p_name f) with None => false | _ => true end) PrOrcl);
  intros Heq0;[ | exact pi].
  case_eq (PrSet.mem (BProc.mkP f) PrOrcl);intros Hnot;[ exact pi | ].
  case_eq (PrSet.mem (BProc.mkP f) PrPriv);intros Hnot1;[ exact pi | ].
  intros tg g;case_eq (Proc.eqb f g);intros Heq1;[ | apply (pi _ g)].
   refine (Some _).
  abstract (
  generalize (Proc.eqb_spec_dep f g);rewrite Heq1;intros Heq2;inversion Heq2;
   simpl;clear H2 H1 H Heq2 Heq1 g tg;
   destruct (HEQ _ f) as (H, (H0, H1));[rewrite Hnot;discriminate | rewrite Hnot1;discriminate | ];
   destruct HWF as (O, (W1, W2));
   assert (forall x0 : VarP.Edec.t,
     Vset.mem x0 (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x0) by (
      intros; destruct x0; apply Vset_of_var_decl_ind with (lv:=proc_params E1 f) 
        (P:= fun t (x:Var.var t) =>Var.is_local x); trivial;
        intros t1 x0 W3; assert (W:= proc_params_local E1 f x0 W3);
        rewrite <- Var.vis_local_local; trivial);
  set (F:= (fun f : ProcD.t =>
          match pi (BProc.p_type f) (BProc.p_name f) with
          | Some _ => true
          | None => false
          end));
  assert (W3:forall x y : ProcD.t, ProcD.eq x y -> F x = F y) by 
   (intros x y Heq1;inversion Heq1;trivial);
  red;intros;apply swap_equiv_le_call;trivial;
   [ | apply VsetP.disjoint_complete; intros;refine (WFRead_not_mem _ _ Heq _ _ _ _ _ W2 _);
    [apply (WFAdv_c_local W1)| ];trivial ];
  rewrite H0;apply Adv_c_context_le with pi PrOrcl PrPriv Gadv
    Gcomm (Vset_of_var_decl (proc_params E1 f)) O;trivial;
  [ intros tr f0 Hin;assert (W:= PrSet.forallb_correct F W3 _ Heq0 _ Hin);
    unfold F in W;simpl in W;destruct (pi tr f0);discriminate
  | rewrite <- H0;trivial]).
  Defined.

 End CONTEXT.

End Make.
