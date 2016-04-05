(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

Require Import Coq.Logic.Epsilon.
Require Import Coq.Logic.ClassicalChoice. 
Require Export le_lift.
Require Export SD_Others.


Set Implicit Arguments.

Declare Module DOM: REALS_GE_ONE.



(*********************** SOME AUXILIARY STUFF ***********************)
(********************************************************************)

Module Make (SemO:SEM_OPT).

 Module OPT2 := SD_Others.Make SemO.
 Export OPT2.

 Module AP_LIFT := APPROX_LIFT DOM.
 Export AP_LIFT.

 (* TODO: move this somewhere else *)
 Lemma deno_while_false_elim : forall E (e:E.expr T.Bool) c k (m:Mem.t k) f,
  E.eval_expr e m = false ->
  mu ([[ [while e do c] ]] E m) f == f m.
 Proof.
  intros.
  rewrite deno_while_elim, deno_cond_elim, H.
  apply deno_nil_elim.
 Qed.

 Lemma deno_cond_nil_elim : forall (e:E.expr T.Bool) E k (m:Mem.t k) f,
  mu (([[ [If e _then nil] ]]) E m) f == f m.
 Proof.
  intros.
  rewrite deno_cond_elim.
  case (E.eval_expr e m); rewrite deno_nil_elim; trivial.
 Qed.

 Lemma deno_unroll_while_false_elim: forall (e:E.expr T.Bool) c E k (m:Mem.t k) n f,
   E.eval_expr e m = false ->
   mu (([[unroll_while e c n]]) E m) f == f m.
 Proof.
  intros.
  intros; case n; unfold unroll_while.
  apply deno_cond_nil_elim.
  intro n'; fold (unroll_while e c n').
  rewrite deno_cond_elim, H, deno_nil_elim; trivial.
 Qed.

 Lemma req_mem_self_upd_r : forall k (m:Mem.t k) t (x : Var.var t),
    m = m{!x <-- m x!}.
 Proof.
  intros. 
  apply Mem.eq_leibniz; red; intros [t' x'].
  generalize (Var.eqb_spec x x'); case_eq (Var.eqb x x'); intros _ Heq.
    rewrite <-Heq, Mem.get_upd_same; trivial.
    rewrite  Mem.get_upd_diff; trivial.
 Qed.

 Lemma unroll_while_0_elim: forall e b c k (m:Mem.t k) f, 
   mu ([[ unroll_while b c 0%nat ]] e m) f == f m.
 Proof.
  unfold unroll_while; intros.
  rewrite deno_cond_elim.
  case (E.eval_expr b m); apply deno_nil_elim.
 Qed.

  Definition EP_eq_expr t (e1 e2:E .expr t) : mem_rel := 
   fun k (m1 m2:Mem.t k) => E.eval_expr e1 m1 = E.eval_expr e2 m2.

Section BOUNDED_LOOP.

  Variable c : cmd.
  Variable E : env.
  Variable b : E.expr T.Bool.
  Variable variant : E.expr T.Nat.

  Hypothesis Hvar: forall k (m:Mem.t k), E.eval_expr b m -> 
   range (EP k (variant <! (E.eval_expr variant m))) ([[c]] E m).

  Open Scope nat_scope.

  Lemma deno_bounded_while_elim: forall k n (m:Mem.t k) f,
   (forall m':Mem.t k, E.eval_expr variant m' = 0%nat -> E.eval_expr b m' = false) ->
   E.eval_expr variant m <= n ->
   mu ([[ [while b do c] ]] E m) f == 
   mu (drestr ([[ unroll_while b c n ]] E m) (negP (@EP k b))) f.
  Proof.
   induction n using lt_wf_ind; induction n.
   (* base case *)
   intros m f Hb Hm.
   rewrite (deno_while_false_elim _ _ _ _ _ (Hb _ (eq_sym (le_n_0_eq _ Hm)))).
   unfold drestr, negP, EP, negb; rewrite Mlet_simpl.
   rewrite (deno_unroll_while_false_elim _ _ _ _ _ _ 
    (Hb _ (eq_sym (le_n_0_eq _ Hm)))).
   rewrite Hb; auto with arith.
   (* inductive case *)
   intros m f Hb Hn'.
   unfold drestr; rewrite Mlet_simpl.
   unfold unroll_while; fold (unroll_while b c n).
   rewrite deno_while_elim.
   repeat rewrite deno_cond_elim; case_eq (E.eval_expr b m); intro Heq.
   repeat rewrite deno_app_elim.
   apply range_eq with (1:=Hvar _ Heq).
   intros m' Hm'; rewrite (H n); auto.
     generalize Hn' Hm'; clear Hn' Hm'; unfold EP; rewrite <- eval_lt;
       change (E.eval_expr (E.eval_expr variant m) m') with (E.eval_expr variant m).
     omega.
   unfold negP, EP, negb.
   rewrite deno_nil_elim, deno_nil_elim, Heq; trivial.
  Qed.
 
  (*
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
  *)

  Close Scope nat_scope.

 End BOUNDED_LOOP.

 Definition eequiv (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) (lam:nat -o> D) (ep:nat-o>U) :=
  forall k m1 m2,
   sig (fun d => P k m1 m2 -> 
     le_lift (Q k) d ([[c1]] E1 m1) ([[c2]] E2 m2) (lam k) (ep k)).


 Lemma equiv_eequiv:  forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel),
  equiv P E1 c1 E2 c2 Q -> eequiv P E1 c1 E2 c2 Q (fun _ => D1) (fzero _).
 Proof.
  unfold eequiv, equiv; intros.
  apply constructive_indefinite_description.
  destruct (H k) as (d,Hd).
  exists (d m1 m2); intros; rewrite le_lift_lift; auto.
 Qed.


 Lemma eequiv_equiv:  forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel),
  eequiv P E1 c1 E2 c2 Q (fun _ => D1) (fzero _) -> equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold eequiv, equiv; intros.
  cut (exists d, forall mm:(Mem.t k * Mem.t k),
     P k (fst mm) (snd mm) -> lift (Q k) (d mm) (([[ c1 ]]) E1 (fst mm)) (([[ c2 ]]) E2 (snd mm))).
    intros (d,Hd); exists (fun m1 m2 => d (m1,m2)).
    intros m1 m2 Hm; apply (Hd (m1,m2) Hm).
  destruct (choice (fun (mm:Mem.t k * Mem.t k) (dd:Distr(Mem.t k * Mem.t k)) =>  
    P k (fst mm) (snd mm) ->
    lift (Q k) dd (([[ c1 ]]) E1 (fst mm)) (([[ c2 ]]) E2 (snd mm)))) as (d',Hd').
    intros (m1,m2); destruct (X _ m1 m2) as (d,Hd).
    exists d; simpl; intro; rewrite <-le_lift_lift; auto.
  eauto.
 Qed.


 Lemma eequiv_deno: forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) lam ep,
  eequiv P E1 c1 E2 c2 Q lam ep ->
  forall k (f g : Mem.t k -> U),
  (forall m1 m2 : Mem.t k, Q k m1 m2 -> f m1 == g m2) ->
  forall m1 m2 : Mem.t k,
  P k m1 m2 -> 
  d_expr ([[ c1 ]] E1 m1) ([[ c2 ]] E2 m2) (lam k) f g <= (ep k).
 Proof.
  unfold eequiv; intros.
  destruct (X k m1 m2) as [d Hd]; trivial.
  apply le_lift_elim with (Q k) d; auto.
 Qed.     


 Lemma eequiv_sdeno: forall c1 E1 c2 E2 (P Q: mem_rel) ep ep' lam lam'
  k (d1 d2 : Distr(Mem.t k)),
  eequiv P E1 c1 E2 c2 Q lam' ep' ->
  (exists d, le_lift (@P k) d d1 d2 (lam k) (ep k)) ->
  forall f g,
  (forall m1 m2 : Mem.t k, Q k m1 m2 -> f m1 == g m2) ->
  d_expr (Mlet d1 ([[c1]] E1)) (Mlet d2 ([[c2]] E2)) (lam k *D* lam' k) f g <= 
   (lam' k ** ep k + lam k ** ep' k).
 Proof.
  unfold eequiv; intros.
  transitivity (max (ep k + lam k ** ep' k) (ep' k + lam' k ** ep k));
    [ |  apply max_le; [ | rewrite Uplus_sym ]; apply Uplus_le_compat; auto ].
  destruct H as [d Hd].
  apply le_lift_elim with (R:=Q k) 
    (d:=Mlet d (fun mm => proj1_sig (X _ (fst mm) (snd mm)))); trivial.
  apply le_lift_Mlet with (P k). 
    apply Hd.
    intros m1 m2 Hm; simpl.
    destruct (X k m1 m2) as (d', Hd'); auto.
 Qed.


 Lemma eequiv_weaken: forall P E1 c1 E2 c2 Q lam ep P' Q' (lam': nat -o> D) (ep':nat -o> U),
  implMR P P' ->
  implMR Q' Q ->
  lam' <= lam ->
  ep' <= ep ->
  eequiv P' E1 c1 E2 c2 Q' lam' ep' ->
  eequiv P  E1 c1 E2 c2 Q  lam ep.
 Proof.
  unfold eequiv; intros.
  destruct (X _ m1 m2) as (d,Hd); clear X.
  exists d.
  intros Hm; apply le_lift_weaken with (Q' k) (lam' k) (ep' k); auto.
 Qed.


 Lemma eequiv_trueR: forall (P:mem_rel) E1 c1 E2 c2 (lam:nat -o> D) ep1 ep2,
  (forall k (m1 m2:Mem.t k), P _ m1 m2 ->
    ep1 k <=  mu ([[c1]] E1 m1) (fone _) /\
    ep2 k <=  mu ([[c2]] E2 m2) (fone _)) ->
   eequiv P E1 c1 E2 c2 trueR lam (fun k => [1-] (lam k ** min (ep1 k) (ep2 k))).
 Proof.
  unfold eequiv; intros.
  exists (prod_distr ([[c1]] E1 m1) ([[c2]] E2 m2)).
  intros Hm.
  eapply le_lift_weaken; [ | | | apply 
    (@le_lift_true _ _ ([[c1]] E1 m1) ([[c2]] E2 m2) (lam k)) ]; trivial.
    destruct (H _ _ _ Hm).
  apply Uinv_le_compat; apply multDU_le_compat; [ | apply min_le_compat ]; trivial.
 Qed.


 Lemma eequiv_trueR_lossless: forall (P:mem_rel) E1 c1 E2 c2,
   lossless E1 c1 -> 
   lossless E2 c2 -> 
   eequiv P E1 c1 E2 c2 trueR (fun _ => D1) (fzero _).
 Proof.
  intros.
  eapply eequiv_weaken; [ | | | | 
    apply (eequiv_trueR P E1 c1 E2 c2 (fun _ => D1) (fone _) (fone _)) ]; trivial.
    unfold fzero, fone; refine (ford_le_intro _); intro k;
      rewrite multDU_D1_l, min_eq_right; auto.
    split; [ rewrite (H _ m1) | rewrite (H0 _ m2) ]; trivial.
 Qed.


 Lemma eequiv_falseR: forall E1 c1 E2 c2 Q,
  eequiv falseR E1 c1 E2 c2 Q (fun _ => D1) (fzero _).
 Proof.
  unfold eequiv; intros.
  exists (distr0 _).
  unfold falseR; intros H; tauto.
 Qed.


 Hint Resolve eequiv_falseR.


 Lemma eequiv_transp: forall P E1 c1 E2 c2 Q lam ep,
   eequiv (transpR P) E2 c2 E1 c1 (transpR Q) lam ep ->
   eequiv P E1 c1 E2 c2 Q lam ep.
 Proof.
  unfold eequiv, transpR; intros.
  destruct (X k m2 m1) as [d Hd]; clear X.
  exists (Mlet d (fun mm => Munit (snd mm, fst mm))).
  intros.
  apply le_lift_transp.
  eapply le_lift_eq_compat with (6:=Hd H); auto.
    rewrite Mcomp, <-(Mext d) at 1.
    apply Mlet_eq_compat; trivial.
    refine (ford_eq_intro _); intros (m1',m2'); auto.
 Qed.


 Lemma eequiv_sym :  forall P E1 c1 E2 c2 Q lam ep,
  symMR P ->
  symMR Q ->
  eequiv P E2 c2 E1 c1 Q lam ep ->
  eequiv P E1 c1 E2 c2 Q lam ep.
 Proof.
  intros P E1 c1 E2 c2 Q lam ep (HP,_) (_,HQ) H.
  apply eequiv_transp.
  eapply eequiv_weaken with (5:=H); trivial.
 Qed.


 Lemma eequiv_case: forall  (P P':mem_rel) E1 c1 E2 c2 Q lam ep,
   decMR P' ->
   eequiv (P /-\ P') E1 c1 E2 c2 Q lam ep ->
   eequiv (P /-\ ~-P') E1 c1 E2 c2 Q lam ep ->
   eequiv P E1 c1 E2 c2 Q lam ep. 
 Proof.
  unfold andR, notR, eequiv; intros.
  destruct (X0 _ m1 m2) as (dt,Hdt); destruct (X1 _ m1 m2) as (df,Hdf); clear X0 X1.
  destruct (X k m1 m2); [ exists dt | exists df ]; auto.
 Qed.


 Lemma eequiv_nil: forall P E1 E2, 
   eequiv P E1 nil E2 nil P (fun _ => D1) (fzero _).
 Proof.
  unfold eequiv; intros.
  exists (Munit (m1, m2)); intros.
  repeat rewrite deno_nil. 
  apply (le_lift_Munit _ _ _ _ H).
 Qed.


 Lemma eequiv_seq: forall P E1 c1 E2 c2 Q' lam ep Q c1' c2' lam' ep',
   eequiv P E1 c1  E2 c2 Q' lam ep ->
   eequiv Q' E1 c1' E2 c2' Q lam' ep' ->
   eequiv P E1 (c1 ++ c1') E2 (c2 ++ c2') Q (fun k => lam k *D* lam' k) 
   (fun k => max (ep k + lam k ** ep' k) (ep' k + lam' k ** ep k)).
 Proof.
   unfold eequiv; intros.
   destruct (X _ m1 m2) as (d, Hd).
   exists (Mlet d (fun mm => proj1_sig (X0 _ (fst mm) (snd mm)))). 
   intro Hm.
   repeat rewrite deno_app.
   apply le_lift_Mlet with (Q' k); simpl.
     auto.
     intros; destruct (X0 _ x y); auto.
 Qed.


 Lemma eequiv_cond_l : forall P E1 e c c' E2 c2 Q lam ep,
  eequiv (P /-\ EP1 e) E1 c E2 c2 Q lam ep ->
  eequiv (P /-\ ~- EP1 e) E1 c' E2 c2 Q lam ep ->
  eequiv P E1 [If e then c else c'] E2 c2 Q lam ep.
 Proof.
  unfold eequiv, andR, notR, EP1, is_true.
  intros P E3 e1 c c' E4 c2 Q lam ep Ht Hf k m1 m2.
  case_eq (E.eval_expr e1 m1); intro Heq.
    destruct (Ht _ m1 m2) as (dt,Hdt).
    exists dt; intro Hm; rewrite deno_cond, Heq; auto.
    destruct (Hf _ m1 m2) as (df,Hdf).
    exists df; intro Hm. rewrite deno_cond, Heq.
      apply Hdf; rewrite Heq; auto using diff_false_true.
 Qed.


 Lemma eequiv_cond_r :  forall P E1 c1 E2 e c c' Q lam ep,
  eequiv (P /-\ EP2 e) E1 c1 E2 c Q lam ep ->
  eequiv (P /-\ ~- EP2 e) E1 c1 E2 c' Q lam ep ->
  eequiv P E1 c1 E2 [If e then c else c'] Q lam ep.
 Proof.
  unfold eequiv, andR, notR, EP2, is_true.
  intros P E3 c c' e E4 c2 Q lam ep Ht Hf k m1 m2.
  case_eq (E.eval_expr e m2); intro Heq.
    destruct (Ht _ m1 m2) as (dt,Hdt).
    exists dt; intro Hm; rewrite deno_cond, Heq; auto.
    destruct (Hf _ m1 m2) as (df,Hdf).
    exists df; intro Hm. rewrite deno_cond, Heq.
      apply Hdf; rewrite Heq; auto using diff_false_true.
 Qed.


 Lemma eequiv_cond : forall P Q E1 (e1:E.expr T.Bool) c1 c2 E2 (e2:E.expr T.Bool) c3 c4 lam ep,
  eequiv (P /-\ (EP1 e1 /-\ EP2 e2)) E1 c1 E2 c3 Q lam ep ->
  eequiv (P /-\ (~- EP1 e1 /-\ ~- EP2 e2)) E1 c2 E2 c4 Q lam ep ->
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
  eequiv P E1 [If e1 then c1 else c2] E2 [If e2 then c3 else c4] Q lam ep.
 Proof.
  intros; apply eequiv_cond_l; apply eequiv_cond_r.
  eapply eequiv_weaken with (5:=X); auto; simplMR; trivial.
  apply eequiv_weaken with falseR Q (fun _ => D1) (fzero _); auto; unfold EP1, EP2.
    intros k m1 m2 ((H2, H3), H4); apply H4; erewrite <-H; eauto.
  apply eequiv_weaken with falseR Q  (fun _ => D1) (fzero _); auto; unfold EP1, EP2.
    intros k m1 m2 ((H2, H3), H4); apply H3; erewrite H; eauto.
  eapply eequiv_weaken with (5:=X0); auto; simplMR; trivial.
 Qed.


 Lemma eequiv_assign_l : forall Q E1 E2 t1 (x1:Var.var t1) e1,
  eequiv (upd1 Q x1 e1) E1 [x1 <- e1] E2 nil Q (fun _ => D1) (fzero _).
 Proof.
  unfold eequiv; intros.
  exists (Munit (m1{!x1<--E.eval_expr e1 m1!}, m2)); intros.
  rewrite deno_assign; rewrite deno_nil. 
  apply le_lift_Munit; trivial.
 Qed.


 Lemma eequiv_assign_r : forall Q E1 E2 t2 (x2:Var.var t2) e2,
  eequiv (upd2 Q x2 e2) E1 nil E2 [x2 <- e2] Q (fun _ => D1) (fzero _).
 Proof.
  unfold eequiv; intros.
  exists (Munit (m1, m2{!x2<--E.eval_expr e2 m2!})); intros.
  rewrite deno_assign; rewrite deno_nil.
  apply le_lift_Munit; trivial.
 Qed.

 
 Lemma eequiv_assign : forall Q E1 E2 t1 (x1:Var.var t1) t2 (x2:Var.var t2) e1 e2, 
   eequiv (upd_para Q x1 e1 x2 e2) E1 [x1 <- e1] E2 [x2 <- e2] Q (fun _ => D1) (fzero _).
 Proof.
  unfold eequiv; intros.
  exists (Munit (m1{!x1<-- E.eval_expr e1 m1!}, m2{!x2<--E.eval_expr e2 m2!})); intros.
  repeat rewrite deno_assign.
  apply le_lift_Munit; trivial.
 Qed.


 Lemma equiv_random:  forall (P Q:mem_rel) E1 E2 t1 t2 (x1:Var.var t1) 
   (x2:Var.var t2) (d1:E.support t1) (d2:E.support t2) lam ep,
   (forall k (m1 m2:Mem.t k), sig (fun d => P _ m1 m2 -> 
      le_lift (fun v1 v2 => Q _ (m1 {!x1 <-- v1!}) (m2 {!x2 <-- v2!})) 
     d (sum_support (T.default k t1) (E.eval_support d1 m1))
     (sum_support (T.default k t2) (E.eval_support d2 m2)) (lam k) (ep k))) ->
   eequiv P E1 [x1 <$- d1] E2 [x2 <$- d2] Q lam ep.
 Proof.
  unfold eequiv; intros.
  destruct (X _ m1 m2) as (d,Hd); clear X.
  exists (Mlet d (fun v12 => Munit ((m1 {!x1 <-- fst v12!}),(m2 {!x2 <-- snd v12!})))); intros Hm.
  repeat rewrite deno_random.
  apply le_lift_weaken with (@Q k) (lam k *D* D1) (max (ep k + (lam k) ** 0) (0 + D1 ** ep k)).
    trivial.
    rewrite multDD_comm; auto. 
    apply max_le; [ rewrite multDU_0_r | rewrite multDU_D1_l]; auto.
    apply le_lift_Mlet with (1:=Hd Hm).
      intros; apply le_lift_Munit; trivial.
 Qed.


 Fixpoint sum_powD (lam:D) (ep:U) (n:nat) : U :=
    match n with
      | 0%nat => 0 
      | S n' =>  ep + lam ** (sum_powD lam ep n')
    end.

 Fixpoint sum_powD' (lam:D) (ep:U) (n:nat) : U :=
    match n with
      | 0%nat => 0 
      | S n' =>  max (ep + lam ** (sum_powD' lam ep n')) ((sum_powD' lam ep n') + powD lam n' ** ep)
    end.

 Lemma sum_powD_podD': forall lam ep n, 
   sum_powD' lam ep n == sum_powD lam ep n.
 Proof.
  induction n; simpl.
    trivial.
    rewrite IHn; apply max_eq_right.
    clear IHn; induction n; simpl.
      admit.
      rewrite <-Uplus_assoc; apply Uplus_le_compat_right.
      rewrite multDD_multDU_assoc, multDD_distr_plus_l.
      apply multDU_le_compat; auto.
 Qed.


 Lemma eequiv_nwhile_cte: forall (P:mem_rel) E1 (e1:E.expr T.Bool) c1 E2 (e2:E.expr T.Bool) c2 lam ep n,
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
  eequiv (P /-\ EP1 e1 /-\ EP2 e2) E1 c1 E2 c2 P lam ep -> 
  eequiv P E1 (unroll_while e1 c1 n) E2 (unroll_while e2 c2 n) P
  (fun k => powD (lam k) n) (fun k => sum_powD (lam k) (ep k) n).
 Proof.
  intros I E1 e1 c1 E2 e2 c2 lam ep n I_e Hc.
  apply eequiv_weaken with I I (fun k : nat => powD (lam k) n)
    (fun k : nat => sum_powD' (lam k) (ep k) n); auto using sum_powD_podD'.
  induction n; simpl.
    (* base case *)
    refine (eequiv_cond _ _ I_e).
    eapply eequiv_weaken; [  rewrite proj1_MR | | | | apply eequiv_nil with (P:=I) ]; auto.
    eapply eequiv_weaken; [  rewrite proj1_MR | | | | apply eequiv_nil with (P:=I) ]; auto.
    (* inductive case *)
    refine (eequiv_cond _ _ I_e).
      apply eequiv_seq with I; trivial.
      eapply eequiv_weaken with I I (fun _ => D1) (fzero _);
       [  rewrite proj1_MR | | | | ]; auto.
      apply eequiv_nil.
 Qed.


Section nWHILE.

  Variables c1 c2 : cmd.
  Variables e1 e2 : env.

  Variables I: mem_rel.
  Variables b1 b2: E.expr T.Bool.

  Variable k:nat.

  Variable ep:U.
  Variable lam:D.
  Variable q:nat.

  Hypothesis Hc: forall m1 m2 : Mem.t k, sig (fun d =>
   (I /-\ EP1 b1 /-\ EP2 b2) _ m1 m2 ->
   le_lift 
   ((I /-\ EP_eq_expr b1 b2) k) d 
   (([[ c1 ]]) e1 m1) (([[ c2 ]]) e2 m2) 
   lam ep).


  Lemma nwhile_le_lift: forall m1 m2 : Mem.t k,
    sig (fun d' => (I /-\ EP_eq_expr b1 b2) _ m1 m2 ->
     le_lift ((I /-\ ~- EP1 b1 /-\ ~- EP2 b2) k) d' 
       (drestr ([[ unroll_while b1 c1 q ]] e1 m1) (negP (EP k b1))) 
       (drestr ([[ unroll_while b2 c2 q ]] e2 m2) (negP (EP k b2)))
       (powD lam q) (sum_powD lam ep q)).
  Proof.
   cut (forall m1 m2 : Mem.t k, sig (fun d' => (I /-\ EP_eq_expr b1 b2) _ m1 m2 ->
     le_lift ((I /-\ ~- EP1 b1 /-\ ~- EP2 b2) k) d'
       (drestr ([[ unroll_while b1 c1 q ]] e1 m1) (negP (EP k b1))) 
       (drestr ([[ unroll_while b2 c2 q ]] e2 m2) (negP (EP k b2)))
       (powD lam q) (sum_powD' lam ep q))).
     intros H m1 m2; destruct (H m1 m2) as (d',Hd'); clear H.
     exists d'; intro Hm.
     apply le_lift_weaken with (4:=Hd' Hm); auto using sum_powD_podD'.
   unfold EP_eq_expr; induction q; intros m1 m2.
   (* base case *)
   case_eq (E.eval_expr b1 m1); intro Heq.
     (* case [b1] *)
     exists (distr0 _); intros (H1m, H2m).
     rewrite (eq_distr_intro _ (Munit m1) (unroll_while_0_elim e1 b1 c1 m1)),
       (eq_distr_intro _ (Munit m2) (unroll_while_0_elim e2 b2 c2 m2)).
     unfold drestr, negP, negb, EP; rewrite 2 Mlet_unit, <-H2m, Heq.
     eapply le_lift_eq_compat; [ apply Oeq_refl |  | | | | apply le_lift_prod ]; auto.
     (* case [~b1] *)
     exists (Munit (m1, m2)); intros (H1m, H2m).
     rewrite (eq_distr_intro _ (Munit m1) (unroll_while_0_elim e1 b1 c1 m1)),
       (eq_distr_intro _ (Munit m2) (unroll_while_0_elim e2 b2 c2 m2)).
     unfold drestr, negP, negb, EP; rewrite 2 Mlet_unit, <-H2m, Heq.
     apply le_lift_Munit.
     unfold EP1, EP2, notR; repeat split; [ trivial | | rewrite <-H2m ];
       apply (proj2 (not_true_iff_false _) Heq).
   (* inductive case *)
   case_eq (E.eval_expr b1 m1); intro Heq.
     (* case [b1] *)
     destruct (Hc m1 m2) as (d',Hd'); clear Hc.
     exists (Mlet d' (fun mm => proj1_sig (IHn (fst mm) (snd mm)))); intros (H1m,H2m).
     simpl; rewrite deno_cond, deno_cond, <-H2m, Heq.
     unfold drestr; repeat rewrite deno_app, (Mcomp _ _ _).
     eapply le_lift_Mlet.
       apply Hd'. 
       repeat split; [ trivial | | unfold EP2; rewrite <-H2m ]; apply Heq.
       intros m1' m2' Hm'; unfold fst, snd.
       destruct (IHn m1' m2') as (dn,Hdn); auto.
     (* case [~b1] *)
     exists (Munit (m1,m2)); intros (H1m, H2m).
     simpl; rewrite deno_cond, deno_cond, <-H2m, Heq.
     unfold drestr, negP, negb, EP.
     rewrite deno_nil, deno_nil, Mlet_unit, Mlet_unit, <-H2m, Heq.
     eapply le_lift_weaken; [  intros ? ? H'; apply H' | apply Ole_refl | | 
       apply le_lift_Munit ]; trivial.
     unfold EP1, EP2, notR; repeat split; [ trivial | | rewrite <-H2m ];
       apply (proj2 (not_true_iff_false _) Heq).
 Qed.

 End nWHILE.


 Lemma eequiv_while : forall (P:mem_rel) E1 (e1:E.expr T.Bool) c1 E2 (e2:E.expr T.Bool) c2 lam ep q,
  (forall k (m1 m2:Mem.t k),  (P /-\ EP_eq_expr e1 e2) _ m1 m2 -> 
   [[ [while e1 do c1] ]] E1 m1 == drestr ([[ unroll_while e1 c1 (q k) ]] E1 m1) (negP (@EP k e1)) /\
   [[ [while e2 do c2] ]] E2 m2 == drestr ([[ unroll_while e2 c2 (q k) ]] E2 m2) (negP (@EP k e2))) ->
  eequiv (P /-\ EP1 e1 /-\ EP2 e2) E1 c1 E2 c2 (P /-\ EP_eq_expr e1 e2) lam ep -> 
  eequiv (P /-\ EP_eq_expr e1 e2) E1 [while e1 do c1] E2 [while e2 do c2] 
  (P /-\ ~-EP1 e1 /-\ ~-EP2 e2) (fun k => powD (lam k) (q k)) (fun k => sum_powD (lam k) (ep k) (q k)).
 Proof.
  unfold eequiv; intros.  
  destruct (nwhile_le_lift (q k) (X k) m1 m2) as (d,Hd).
  exists d; intro Hm.
  apply le_lift_eq_compat with (6:=Hd Hm); trivial.
    symmetry; apply (proj1 (H _ _ _ Hm)).
    symmetry; apply (proj2 (H _ _ _ Hm)).
 Qed.



 (* ProdDD f i 0      = 1                          *)
 (* ProdDD f i (S n)  = (f i) x ... x (f (i + n))  *)
 Fixpoint ProdDD (f:nat -o> D) i (n:nat) {struct n} : D :=
   match n with 
     | 0 => D1
     | S n' => f i *D* ProdDD f (S i) n'
   end.

 Fixpoint sum_powD2' (lam: nat -> D) (ep: nat -> U) (i:nat) (n:nat) {struct n} : U :=
    match n with
      | 0%nat => 0 
      | S n' => max
        (ep i + lam i ** sum_powD2' lam ep  (S i) n')
        (sum_powD2' lam ep (S i) n' + ProdDD lam (S i) n' ** ep i)
    end.

Section nWHILE_GEN.

  Variables c1 c2 : cmd.
  Variables e1 e2 : env.

  Variables I: mem_rel.
  Variables b1 b2: E.expr T.Bool.
  Variable i: Var.var T.Nat.

  Variable HI: implMR I (EP_eq_expr b1 b2).

  Variable k:nat.
  Variable ep: nat -o> U.
  Variable lam: nat -o> D.

   Hypothesis Hd: forall (m1 m2 : Mem.t k),  
    sig (fun d =>
    (I /-\ EP1 b1 /-\ EP2 b2) _ m1 m2 ->
    le_lift 
      ((I /-\ (fun k (m1' m2':Mem.t k) => m1' i = S (m1 i))) k) 
      d  
      (([[ c1 ]]) e1 m1) 
      (([[ c2 ]]) e2 m2) 
      (lam (m1 i)) (ep (m1 i))).


  Lemma nwhile_le_lift': forall n (m1 m2 : Mem.t k), sig (fun d' => 
    I m1 m2 ->
    le_lift ((I /-\ ~- EP1 b1 /-\ ~- EP2 b2) k) d'
       (drestr ([[ unroll_while b1 c1 n ]] e1 m1) (negP (EP k b1))) 
       (drestr ([[ unroll_while b2 c2 n ]] e2 m2) (negP (EP k b2)))
       (ProdDD lam (m1 i) n) (sum_powD2' lam ep (m1 i) n)).
  Proof.
   unfold EP_eq_expr in *.
   induction n; intros m1 m2.
   (* base case *)
   case_eq (E.eval_expr b1 m1); intro Heq.
     (* case [b1] *)
     exists (distr0 _); intro Hm.
     rewrite (eq_distr_intro _ (Munit m1) (unroll_while_0_elim e1 b1 c1 m1)),
       (eq_distr_intro _ (Munit m2) (unroll_while_0_elim e2 b2 c2 m2)).
     unfold drestr, negP, negb, EP; rewrite 2 Mlet_unit, <-(HI Hm), Heq.
     eapply le_lift_eq_compat; [ apply Oeq_refl |  | | | | apply le_lift_prod ]; auto.
     (* case [~b1] *)
     exists (Munit (m1, m2)); intro Hm.
     rewrite (eq_distr_intro _ (Munit m1) (unroll_while_0_elim e1 b1 c1 m1)),
       (eq_distr_intro _ (Munit m2) (unroll_while_0_elim e2 b2 c2 m2)).
     unfold drestr, negP, negb, EP; rewrite 2 Mlet_unit, <-(HI Hm), Heq.
     apply le_lift_Munit.
     unfold EP1, EP2, notR; repeat split; [ trivial | | rewrite <-(HI Hm) ];
       apply (proj2 (not_true_iff_false _) Heq).

   (* inductive case *)
   case_eq (E.eval_expr b1 m1); intro Heq.
     (* case [b1] *)
     destruct (Hd m1 m2) as (d',Hd'); clear Hd.
     exists (Mlet d' (fun mm => proj1_sig (IHn (fst mm) (snd mm)))); intro Hm.
     simpl; rewrite deno_cond, deno_cond, <-(HI Hm), Heq.
     unfold drestr; repeat rewrite deno_app, (Mcomp _ _ _).
     eapply le_lift_Mlet.
       apply Hd'. 
       repeat split; [ trivial | | unfold EP2; rewrite <-(HI Hm) ]; apply Heq.
       intros m1' m2' (H1m',Hi_m1'); unfold fst, snd.
       rewrite <-Hi_m1'; destruct (IHn m1' m2'); auto.
     (* case [~b1] *)
     exists (Munit (m1,m2)); intro Hm.
     simpl; rewrite deno_cond, deno_cond, <-(HI Hm), Heq.
     unfold drestr, negP, negb, EP.
     rewrite deno_nil, deno_nil, Mlet_unit, Mlet_unit, <-(HI Hm), Heq.
     eapply le_lift_weaken with  (P':=(I /-\ ~- EP1 b1  /-\ ~- EP2 b2) k) 
       (lam' := lam (m1 i) *D* ProdDD lam (S (m1 i)) n); [ | | | apply le_lift_Munit ]; trivial.
     unfold EP1, EP2, notR; repeat split; [ trivial | | rewrite <-(HI Hm) ];
       apply (proj2 (not_true_iff_false _) Heq).
 Qed.

 End nWHILE_GEN.


 Lemma eequiv_while': forall (P:mem_rel) E1 (e1:E.expr T.Bool) c1 E2 (e2:E.expr T.Bool) c2 
   (i:Var.var T.Nat) (lam:nat -> nat -> D)  (ep:nat -> nat -> U) (q: nat -> nat),
   implMR P (EP_eq_expr e1 e2) ->
   (forall k (m1 m2:Mem.t k),  P _ m1 m2 -> 
   [[ [while e1 do c1] ]] E1 m1 == drestr ([[ unroll_while e1 c1 (q k) ]] E1 m1) (negP (@EP k e1)) /\
   [[ [while e2 do c2] ]] E2 m2 == drestr ([[ unroll_while e2 c2 (q k) ]] E2 m2) (negP (@EP k e2))) ->
  (forall (n:nat -> nat), 
    eequiv 
    (P /-\ EP1 e1 /-\ EP2 e2 /-\ (fun k (m1 _:Mem.t k) => m1 i = n k)) 
    E1 c1 E2 c2 
    (P /-\ (fun k (m1 _:Mem.t k) => m1 i = S (n k))) 
    (fun k => lam k (n k)) (fun k => ep k (n k))) ->
  forall (i0:nat -> nat), 
    eequiv (P /-\ (fun k (m1 _:Mem.t k) => m1 i = i0 k)) 
    E1 [while e1 do c1] E2 [while e2 do c2] 
    (P /-\ ~-EP1 e1 /-\ ~-EP2 e2)
    (fun k => ProdDD (lam k) (i0 k) (q k)) (fun k => sum_powD2' (lam k) (ep k) (i0 k) (q k)).
 Proof.
  unfold eequiv; intros.
  destruct (fun H''=> @nwhile_le_lift' c1 c2 E1 E2 P e1 e2 i H k (ep k) (lam k) H'' (q k) m1 m2) as (dn, Hdn).
    intros m1' m2'.
    destruct (X (fun k => m1' i) _ m1' m2') as (d,Hd); clear X H0.
    exists d; intros (?,(?,?)).
    eapply le_lift_weaken; [ | | | apply Hd ]; trivial.
      repeat split; trivial.
  exists dn; intros (H1m, H2m).
  eapply le_lift_weaken; [  intros ? ? Hm'; apply Hm' | 
    rewrite <-H2m; apply Ole_refl | rewrite <-H2m; apply Ole_refl | ]; trivial.
  eapply le_lift_eq_compat; [ | | | | | apply (Hdn H1m) ]; trivial.
    symmetry; apply (proj1 (H0 _ _ _ H1m)).
    symmetry; apply (proj2 (H0 _ _ _ H1m)).
 Qed.



 

 (* Some further properties about [eequiv] *)
 Lemma eequiv_inv_Modify : forall (Q:mem_rel) (X1 X2 M1 M2:Vset.t) 
  (P:mem_rel) (E1:env) (c1:cmd) (E2:env) (c2:cmd) (O:Vset.t) del ep,
  depend_only_rel Q X1 X2 ->
  Modify E1 M1 c1 ->
  Modify E2 M2 c2 ->
  O [<=] Vset.inter M1 M2 ->
  Vset.disjoint X1 M1 -> 
  Vset.disjoint X2 M2 -> 
  eequiv P E1 c1 E2 c2 (req_mem_rel O trueR) del ep ->
  eequiv (P /-\ Q) E1 c1 E2 c2 (req_mem_rel O Q) del ep.
 Proof.
  intros; intros k m1 m2.
  destruct (X _ m1 m2) as [d Hd].
  exists (Mlet d (fun mm => Munit (m1{! M1 <<- fst mm !}, m2{! M2 <<- snd mm!}))).
  intros H6.
  destruct H6 as [Hreq Hinv].
  destruct (Hd Hreq); clear Hd.
  constructor; intros.
  (* distance *)
  apply max_le; unfold d_expr, le_lift.p1, le_lift.p2.
    rewrite (Mlet_simpl (Mlet d _)), (Modify_deno_elim H0),  
    <-(le_d0 (fun m' => f (m1 {!M1 <<- m'!})) (fun m' => g (m2 {!M2 <<- m'!}))); auto.
    rewrite (Mlet_simpl (Mlet d _)), (Modify_deno_elim H1),  
    <-(le_d0 (fun m' => f (m1 {!M1 <<- m'!})) (fun m' => g (m2 {!M2 <<- m'!}))); auto.
  (* range *)
  apply (range_Mlet _ le_r0).
  unfold prodP, req_mem_rel, andR; intros (m1',m2') H6 f Hf; simpl.
  apply Hf; simpl; split.
  intros ? ? ?.
  rewrite update_mem_in, update_mem_in.
  destruct H6; auto.
  eapply Vset.inter_correct_r; apply Vset.subset_correct with (1:=H2); trivial.
  eapply Vset.inter_correct_l; apply Vset.subset_correct with (1:=H2); trivial.
  apply H with (3:=Hinv).
  apply req_mem_sym; apply req_mem_update_disjoint; trivial.
  apply req_mem_sym; apply req_mem_update_disjoint; trivial.
  (* projections *)
  rewrite (Modify_deno_elim H0), <-le_p3; apply Ole_refl.
  rewrite (Modify_deno_elim H1), <-le_p4; apply Ole_refl.
 Qed.

 (** TODO: Move to VsetP and prove *)
 Lemma Vset_diff_union : forall X Y Z, 
  Vset.diff X (Vset.union Y Z) [=] Vset.diff (Vset.diff X Y) Z.
 Admitted.

 Lemma Vset_diff_disjoint : forall X Y,
  Vset.disjoint X Y ->
  Vset.diff X Y [=] X.
 Admitted.
 
 Lemma Vset_diff_subset : forall X Y,
  X [<=] Y ->
  Vset.diff X Y [=] Vset.empty.
 Admitted.

 Lemma eqobs_composition : 
  forall W X Y Z W1 W2 W1' W2' E1 c1 c1' E2 c2 c2',
   Vset.disjoint X Y ->
   Vset.disjoint Y Z ->
   Vset.disjoint X W1  ->
   Vset.disjoint Y W2  ->
   Vset.disjoint X W1' ->
   Vset.disjoint Y W2' ->
   Modify E1 W1  c1 ->
   Modify E1 W2  c2 ->
   Modify E2 W1' c1' ->
   Modify E2 W2' c2' ->
   EqObs (Vset.union X W) E1 c1 E2 c1' Y ->
   EqObs (Vset.union X Y) E1 c2 E2 c2' Z ->
   EqObs (Vset.union X W) E1 (c1 ++ c2) E2 (c1' ++ c2') (Vset.union Y Z).
 Proof.
  intros; apply equiv_app with (kreq_mem (Vset.union X Y)).

  apply EqObs_union_Modify with W1 W1'.
  split; trivial.
  eapply equiv_weaken with (2:=H9).
  intros; apply req_mem_weaken with (2:=H11).
  rewrite <-VsetP.union_diff_assoc, Vset_diff_subset, VsetP.union_empty.
  auto with set.
  rewrite <-VsetP.union_diff_assoc, Vset_diff_union.
  rewrite (Vset_diff_disjoint X), Vset_diff_disjoint; auto with set.  
  
  apply EqObs_union_Modify with W2 W2'.
  split; trivial.
  apply equiv_weaken with (2:=H10).     
  intros; apply req_mem_weaken with (2:=H11).
  rewrite <-VsetP.union_diff_assoc, Vset_diff_subset, VsetP.union_empty.
  auto with set.
  rewrite <-VsetP.union_diff_assoc, VsetP.union_sym, Vset_diff_union.
  rewrite (Vset_diff_disjoint Y), Vset_diff_disjoint; auto with set.
 Qed.

 Lemma eequiv_composition : 
  forall P X Y Z W1 W2 W1' W2' E1 c1 c1' E2 c2 c2' lam1 lam2 ep1 ep2,
   Vset.disjoint X Y ->
   Vset.disjoint Y Z ->
   Vset.disjoint X W1  ->
   Vset.disjoint Y W2  ->
   Vset.disjoint X W1' ->
   Vset.disjoint Y W2' ->
   Modify E1 W1  c1 ->
   Modify E1 W2  c2 ->
   Modify E2 W1' c1' ->
   Modify E2 W2' c2' ->
   depend_only_rel P X X ->
   eequiv P E1 c1 E2 c1' (kreq_mem Y) lam1 ep1 ->
   eequiv (P /-\ kreq_mem Y) E1 c2 E2 c2' (kreq_mem Z) lam2 ep2 ->
   eequiv P E1 (c1 ++ c2) E2 (c1' ++ c2') (kreq_mem (Vset.union Y Z)) 
    (fun k => lam1 k *D* lam2 k) (fun k : nat => max (ep1 k + lam1 k ** ep2 k) (ep2 k + lam2 k ** ep1 k)).
 Proof.
  intros; apply eequiv_seq with (req_mem_rel Y P).
 
  assert (eequiv (P /-\ P) E1 c1 E2 c1' (req_mem_rel Y P) lam1 ep1).
  apply eequiv_inv_Modify with X X (Vset.union Y W1) (Vset.union Y W1'); trivial.
  apply Modify_weaken with W1; auto with set.
  apply Modify_weaken with W1'; auto with set.
  rewrite VsetP.inter_union_comm, VsetP.inter_sym, VsetP.inter_union_comm.
  rewrite VsetP.inter_idem; auto with set.
  apply disjoint_union; trivial.
  apply disjoint_union; trivial.

  eapply eequiv_weaken; [ | | | | apply X0]; trivial.
  apply req_mem_rel_trueR.
  
  eapply eequiv_weaken; [ | | | | apply X2]; trivial.
  unfold implMR, andR, kreq_mem; auto.
  
  apply eequiv_weaken with 
   ((P /-\ kreq_mem Y) /-\ kreq_mem Y) 
   (kreq_mem Z /-\ kreq_mem Y) lam2 ep2; trivial.
  unfold implMR, req_mem_rel, andR; intros; tauto.
  unfold implMR, req_mem_rel, andR; intros; apply req_mem_union; tauto.
  
  apply eequiv_inv_Modify with Y Y (Vset.union Z W2) (Vset.union Z W2'); trivial.  
  apply Modify_weaken with W2; auto with set.
  apply Modify_weaken with W2'; auto with set.
  rewrite VsetP.inter_union_comm, VsetP.inter_sym, VsetP.inter_union_comm.
  rewrite VsetP.inter_idem; auto with set.
  apply disjoint_union; trivial.
  apply disjoint_union; trivial.
  eapply eequiv_weaken with (5:=X1); auto using (proj2 (req_mem_rel_trueR Z)).
 Qed.

 Definition eq_dot (X:Vset.t) k (m1 m2:Mem.t k) :=
  exists x, Vset.mem x X /\ kreq_mem (Vset.remove x X) m1 m2. 

 Lemma eq_dot_dec : forall X, decMR (eq_dot X).
 Proof.
 Admitted.

 Lemma depend_only_eq_dot : forall X, depend_only_rel (eq_dot X) X X.
 Proof.
 Admitted. 

 Lemma eq_dot_union_l : forall X Y k (m1 m2:Mem.t k), 
  eq_dot (Vset.union X Y) m1 m2 ->
  eq_dot X m1 m2.
 Admitted.

 Lemma eq_dot_union_r : forall X Y k (m1 m2:Mem.t k), 
  eq_dot (Vset.union X Y) m1 m2 ->
  eq_dot Y m1 m2.
 Admitted.

 Lemma eq_dot_union_case : forall X Y k (m1 m2:Mem.t k),
  eq_dot (Vset.union X Y) m1 m2 ->
  ~kreq_mem X m1 m2 ->
  kreq_mem Y m1 m2.
 Admitted.

 Parameter maxD : D -> D -> D.

 Lemma maxD_le_left : forall x y : D, y <= maxD x y.
 Admitted.

 Lemma maxD_le_right : forall x y : D, x <= maxD x y.
 Admitted.


 Lemma eequiv_parallel : 
  forall W1 W2 W1' W2' X1 X2 Y1 Y2 E1 c1 c1' E2 c2 c2' lam1 lam2 ep1 ep2,
   Vset.disjoint X2 W1  ->
   Vset.disjoint X2 W1' ->
   Vset.disjoint Y1 W2  ->
   Vset.disjoint Y1 W2' ->
   Vset.disjoint X2 Y1  -> 
   Vset.disjoint Y1 Y2  ->
   Modify E1 W1  c1  ->
   Modify E1 W2  c2  ->
   Modify E2 W1' c1' ->
   Modify E2 W2' c2' ->
   EqObs X1 E1 c1 E2 c1' Y1 ->
   EqObs X2 E1 c2 E2 c2' Y2 ->
   eequiv (eq_dot X1) E1 c1 E2 c1' (kreq_mem Y1) lam1 ep1 ->
   eequiv (eq_dot X2) E1 c2 E2 c2' (kreq_mem Y2) lam2 ep2 ->
   eequiv (eq_dot (Vset.union X1 X2)) E1 (c1 ++ c2) E2 (c1' ++ c2') 
    (kreq_mem (Vset.union Y1 Y2)) 
    (fun k => maxD (lam1 k) (lam2 k)) (fun k => max (ep1 k) (ep2 k)).
 Proof.
  intros; apply equiv_eequiv in H9; apply equiv_eequiv in H10.
  apply eequiv_case with (P':=kreq_mem X1); [ auto | | ].
  
  apply eequiv_weaken with
   (kreq_mem X1 /-\ eq_dot X2)
   (kreq_mem Y1 /-\ kreq_mem Y2)
   (fun k => D1 *D* lam2 k) 
   (fun k =>  max (0 + D1 ** ep2 k) (ep2 k + (lam2 k) ** 0)).
  unfold implMR, andR; intros k m1 m2 [? ?].
  split; trivial; apply eq_dot_union_r with X1; trivial.
  unfold implMR, req_mem_rel, andR; intros; apply req_mem_union; tauto.
  apply ford_le_intro; intro; rewrite multDD_D1_l.
  apply maxD_le_left.
  apply ford_le_intro; intro k.
  rewrite multDU_D1_l, Uplus_zero_left, multDU_0_r,  Uplus_zero_right,
  <-(max_le_left  (ep1 k) (ep2 k)); apply max_le; trivial.
  apply eequiv_seq with (kreq_mem Y1 /-\ eq_dot X2).
 
  apply eequiv_inv_Modify with X2 X2 (Vset.union Y1 W1) (Vset.union Y1 W1').
  apply depend_only_eq_dot.
  apply Modify_weaken with W1; auto with set.
  apply Modify_weaken with W1'; auto with set.
  rewrite VsetP.inter_union_comm, VsetP.inter_sym, VsetP.inter_union_comm.
  rewrite VsetP.inter_idem; auto with set.
  apply disjoint_union; trivial.
  apply disjoint_union; trivial.
  eapply eequiv_weaken; [ | | | | apply H9]; trivial;
    apply req_mem_rel_trueR.

  eapply eequiv_weaken with (P':=eq_dot X2 /-\ kreq_mem Y1)
    (Q':= kreq_mem Y2 /-\ kreq_mem Y1);
   [ rewrite andR_comm | rewrite andR_comm | | | ]; trivial.
  apply eequiv_inv_Modify with Y1 Y1 (Vset.union Y2 W2) (Vset.union Y2 W2').
  auto.
  apply Modify_weaken with W2; auto with set.
  apply Modify_weaken with W2'; auto with set.
  rewrite VsetP.inter_union_comm, VsetP.inter_sym, VsetP.inter_union_comm.
  rewrite VsetP.inter_idem; auto with set.
  apply disjoint_union; trivial.
  apply disjoint_union; trivial.
  eapply eequiv_weaken; [ | | | | apply X0]; trivial;
    apply req_mem_rel_trueR.

  apply eequiv_weaken with
   (kreq_mem X2 /-\ eq_dot X1)
   (kreq_mem Y2 /-\ kreq_mem Y1)
   (fun k => lam1 k *D* D1) 
   (fun k =>  max (ep1 k + (lam1 k) ** 0) (0 + D1 ** ep1 k)).
  unfold implMR, andR; intros k m1 m2 [? ?].
  split; trivial.
  apply eq_dot_union_case with X1; trivial.
  apply eq_dot_union_l with X2; trivial.
  unfold implMR, req_mem_rel, andR; intros; apply req_mem_union; tauto.
  apply ford_le_intro; intro; rewrite multDD_comm, multDD_D1_l.
  apply maxD_le_right.
  apply ford_le_intro; intro k.
  rewrite multDU_D1_l, Uplus_zero_left, multDU_0_r,  Uplus_zero_right,
    <-(max_le_right (ep1 k) (ep2 k)); apply max_le; trivial.

  apply eequiv_seq with (kreq_mem X2 /-\ kreq_mem Y1).

  eapply eequiv_weaken with (P':=eq_dot X1 /-\ kreq_mem X2) 
    (Q':=kreq_mem Y1 /-\ kreq_mem X2);
   [ rewrite andR_comm | rewrite andR_comm | | | ]; trivial.
  apply eequiv_inv_Modify with X2 X2 (Vset.union Y1 W1) (Vset.union Y1 W1').
  auto.
  apply Modify_weaken with W1; auto with set.
  apply Modify_weaken with W1'; auto with set.
  rewrite VsetP.inter_union_comm, VsetP.inter_sym, VsetP.inter_union_comm.
  rewrite VsetP.inter_idem; auto with set.
  apply disjoint_union; trivial.
  apply disjoint_union; trivial.
  eapply eequiv_weaken; [ | | | | apply X]; trivial;
    apply req_mem_rel_trueR.

 
  apply eequiv_inv_Modify with Y1 Y1 (Vset.union Y2 W2) (Vset.union Y2 W2').
  auto.
  apply Modify_weaken with W2; auto with set.
  apply Modify_weaken with W2'; auto with set.
  rewrite VsetP.inter_union_comm, VsetP.inter_sym, VsetP.inter_union_comm.
  rewrite VsetP.inter_idem; auto with set.
  apply disjoint_union; trivial.
  apply disjoint_union; trivial.
  eapply eequiv_weaken; [ | | | | apply H10]; trivial;
    apply req_mem_rel_trueR.
 Qed.

 
End Make.


