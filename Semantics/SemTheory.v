(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * SemTheory,v : Properties about the denotational semantics of programs and
  general theory of program equivalence *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Export BaseProp.

  
Module Make (Sem:SEM).

 Module BP := BaseProp.Make Sem.
 Export BP.

 Lemma equiv_refl : forall E c, 
  equiv Mem.eq E c E c Mem.eq.
 Proof.
  intros E c k.
  exists (fun m1 m2 => Mlet ([[c]] E m2) (fun m => Munit (m,m))).
  constructor; simpl; intros.
  apply Mem.eq_leibniz in H; rewrite H.
  refine (mu_stable_eq _ _ _ _); refine (ford_eq_intro _); intro m; trivial.
  refine (mu_stable_eq _ _ _ _); refine (ford_eq_intro _); intro m; trivial.
  intros f Hf; simpl.
  rewrite <- (mu_0 ([[c]] E m2)).
  apply mu_stable_eq; refine (ford_eq_intro _); intro m; apply Hf.
  unfold Mem.eq, prodP; auto.
 Qed.

 Lemma equiv_strengthen : forall (P P' Q:mem_rel) E1 c1 E2 c2,
  (forall k (m1 m2:Mem.t k), P' k m1 m2 -> P k m1 m2) ->
  equiv P  E1 c1 E2 c2 Q -> 
  equiv P' E1 c1 E2 c2 Q.
 Proof. 
  unfold equiv; intros.
  destruct (H0 k) as (d,Hd); exists d; intros; auto.
 Qed.
 
 Lemma equiv_weaken : forall (P Q Q':mem_rel) E1 c1 E2 c2, 
  (forall k (m1 m2:Mem.t k), Q k m1 m2 -> Q' k m1 m2) ->
  equiv P E1 c1 E2 c2 Q -> 
  equiv P E1 c1 E2 c2 Q'.
 Proof. 
  unfold equiv; intros.
  destruct (H0 k) as (d,Hd); exists d; intros.
  apply lift_weaken with (Q k); auto.
 Qed.

 Lemma equiv_sub : forall (P P' Q Q':mem_rel) E1 c1 E2 c2,
  (forall k (m1 m2:Mem.t k), P' k m1 m2 -> P k m1 m2) ->
  (forall k (m1 m2:Mem.t k), Q k m1 m2 -> Q' k m1 m2) ->
  equiv P  E1 c1 E2 c2 Q ->
  equiv P' E1 c1 E2 c2 Q'.
 Proof.
  intros.
  apply equiv_strengthen with P; [ | apply equiv_weaken with Q]; trivial.
 Qed.

 Add Morphism equiv 
  with signature implMR ++> (@eq env) ==> (@eq cmd) ==> 
   (@eq env) ==> (@eq cmd) ==> implMR --> Basics.flip impl
  as equiv_imp_Morph.
 Proof.
  unfold flip, implMR, impl; intros P P' H ? ? ? ? Q Q' ? ?.
  eapply equiv_sub with P' Q'; auto.
 Qed.

 Add Morphism equiv 
  with signature iffMR ==> (@eq env) ==> (@eq cmd) ==> 
   (@eq env) ==> (@eq cmd) ==> iffMR ==> iff 
  as equiv_iff_Morph.
 Proof.
  unfold iffMR; intros.
  destruct H; destruct H0; split; intros.
  rewrite <- H0, H1; trivial.
  rewrite <- H2, H; trivial.
 Qed.

 Lemma equiv_sym_transp : forall (P Q:mem_rel) E1 c1 E2 c2,
  equiv (transpR P) E1 c1 E2 c2 (transpR Q) -> 
  equiv P E2 c2 E1 c1 Q.
 Proof.
  unfold equiv; intros.
  destruct (H k) as (d,Hd).
  exists (fun m1 m2 => Mlet (d m2 m1) (fun p => Munit (snd p, fst p))).
  intros; apply lift_weaken with (transp _ (transp _ (Q k))).
  intros x y H1; exact H1.
  apply lift_sym.
  apply Hd.
  red; trivial.
 Qed.
 
 Lemma equiv_sym : forall (P Q:mem_rel) E1 c1 E2 c2,
  symMR P -> symMR Q ->
  equiv P E1 c1 E2 c2 Q -> 
  equiv P E2 c2 E1 c1 Q.
 Proof. 
  unfold symMR; intros; apply equiv_sym_transp.
  rewrite H, H0; trivial.
 Qed.

 Lemma equiv_trans : forall (P1 P2 Q1 Q2 Q3:mem_rel) E1 c1 E2 c2 E3 c3,
  decMR P2 ->
  refl_supMR2 P2 P1 ->
  (forall k x y z, Q1 k x y -> Q2 k y z -> Q3 k x z) -> 
  equiv P1 E1 c1 E2 c2 Q1 -> 
  equiv P2 E2 c2 E3 c3 Q2 ->
  equiv P2 E1 c1 E3 c3 Q3.
 Proof.
  intros.
  intros k; destruct (H1 k) as (d, Hd); destruct (H2 k) as (d',Hd').
  exists (
   fun m1 m3 =>
    match X k m1 m3 with
    | left HP2 =>
       let HP1 := H _ _ _ HP2 in
        dd' (@mem_eqU k) (Hd _ _ HP1) (Hd' _ _ HP2)
    | _ => distr0 _
    end).
  intros m1 m3 HP2. 
  destruct (X k m1 m3); simpl.
  apply lift_trans_discr; auto using mem_eqU_spec.
  exact (H0 k).
  apply sem_discr.
  elim n; trivial.
 Qed.

 Lemma equiv_trans_r : forall (P1 P2 Q1 Q2 Q3:mem_rel) E1 c1 E2 c2 E3 c3,
  decMR P1 ->
  refl_supMR2 (transpR P1) (transpR P2) ->
  (forall k x y z, Q1 k x y -> Q2 k y z -> Q3 k x z) -> 
  equiv P1 E1 c1 E2 c2 Q1 -> 
  equiv P2 E2 c2 E3 c3 Q2 ->
  equiv P1 E1 c1 E3 c3 Q3.
 Proof.
  intros; apply equiv_sym_transp.
  apply equiv_trans with (P1 := transpR P2) (P2:=transpR P1)
   (Q1 := transpR Q2) (Q2 := transpR Q1) (E2 := E2) (c2:= c2).
  auto. 
  trivial.
  unfold transpR; intros; eapply H0; eauto.
  apply equiv_sym_transp; repeat rewrite transpR_transpR; trivial.
  apply equiv_sym_transp; repeat rewrite transpR_transpR; trivial.
 Qed.

 Lemma equiv_trans_trial : forall (P1 P2 P3 Q1 Q2 Q3:mem_rel) E1 c1 E2 c2 E3 c3,
  decMR P3 ->
  (forall k x z, P3 k x z -> sigS (fun y  =>  P1 k x y /\ P2 k y z)) -> 
  (forall k x y z, Q1 k x y -> Q2 k y z -> Q3 k x z) -> 
  equiv P1 E1 c1 E2 c2 Q1 -> 
  equiv P2 E2 c2 E3 c3 Q2 ->
  equiv P3 E1 c1 E3 c3 Q3.
 Proof.
  intros.
  intros k; destruct (H0 k) as (d, Hd); destruct (H1 k) as (d',Hd').
  exists (
   fun m1 m3 =>
    match X k m1 m3 with
    | left HP3 =>
       let (m2, HH) := X0 k m1 m3 HP3 in
       let (HP1, HP2) := HH in
       dd' (@mem_eqU k) (Hd _ _ HP1) (Hd' _ _ HP2)
    | _ => distr0 _
    end).
  intros m1 m3 HP3. 
  destruct (X k m1 m3); simpl.
  destruct (X0 k m1 m3) as (m2, (HP1, HP2)).
  apply lift_trans_discr; auto using mem_eqU_spec.
  exact (H k).
  apply sem_discr.
  elim n; trivial.
 Qed.

 Lemma equiv_trans_trans : forall P Q E1 c1 E2 c2 E3 c3,
   decMR P ->
   refl_supMR P ->
   transMR Q ->
   equiv P E1 c1 E2 c2 Q -> 
   equiv P E2 c2 E3 c3 Q ->
   equiv P E1 c1 E3 c3 Q.
 Proof.
  intros; eapply equiv_trans; eauto; trivial.
 Qed.

 (* Used for optimizations *)
 Lemma equiv_trans_eq_mem_l : forall P1 P Q E1 c1 E1' c1' E2 c2,
  equiv (Meq /-\ P1) E1 c1 E1' c1' Meq ->
  equiv P E1' c1' E2 c2 Q ->
  refl_supMR2 P P1 ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold equiv, implMR; intros.
  destruct (H k) as (d, Hd); destruct (H0 k) as (d',Hd').
  exists d'; intros.
  eapply lift_eq_trans_l with (d:=d m1 m1); auto.
  apply lift_weaken with (Meq k).
  unfold Meq; trivial.
  apply Hd ; red; split; eauto.
 Qed.

 Lemma equiv_trans_eq_mem_r : forall P2 P Q E1 c1 E2 c2 E2' c2',
  equiv (Meq /-\ P2) E2 c2 E2' c2' Meq ->
  equiv P E1 c1 E2' c2' Q ->
  refl_supMR2 (transpR P) P2 ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  intros; apply equiv_sym_transp.
  apply equiv_trans_eq_mem_l with P2 E2' c2'; trivial.
  apply equiv_sym_transp; simplMR; trivial.
 Qed.

 Lemma equiv_depend_only_l : forall (P:mem_rel) E1 c1 E1' c1' E2 c2 (Q:mem_rel) X1 X2,
  decMR P ->
  depend_only_rel Q X1 X2 ->
  equiv Meq E1 c1 E1' c1' (kreq_mem X1) ->
  equiv P E1' c1' E2 c2 Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  intros; apply equiv_trans with (P1:= Meq) (Q1:= kreq_mem X1) (Q2 := Q)
    (E2:= E1') (c2:= c1'); auto.
  red; red; trivial.
  unfold kreq_mem; intros k x y z H2 H3; apply H with (3:= H3); auto.
 Qed.

 Lemma equiv_depend_only_r : forall (P:mem_rel) E1 c1 E2 c2 E2' c2' Q X1 X2,
  decMR P ->
  depend_only_rel Q X1 X2 ->
  equiv Meq E2 c2 E2' c2' (kreq_mem X2) ->
  equiv P E1 c1 E2' c2' Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  intros; apply equiv_sym_transp.
  eapply equiv_depend_only_l with (X2:= X1); eauto.
  apply equiv_sym_transp; simplMR; trivial.
 Qed.

 Lemma equiv_True : forall P E1 c1 E2 c2, 
  lossless E1 c1 ->
  lossless E2 c2 ->
  equiv P E1 c1 E2 c2 trueR.
 Proof.
  unfold lossless, equiv; intros P E1 c1 E2 c2 Hc1 Hc2 k.
  exists (fun m1 m2 => prod_distr ([[c1]] E1 m1) ([[c2]] E2 m2)); intros.
  constructor; simpl; intros.
  apply (mu_stable_eq ([[c1]] E1 m1)); simpl; apply ford_eq_intro; intros.
  change (fun _ :Mem.t k=> f n) with (fcte (Mem.t k) (f n)).
  rewrite (mu_cte ([[c2]] E2 m2) (f n)).
  unfold fone; rewrite Hc2; auto.
  change (
   mu (([[c1]]) E1 m1) (fcte (Mem.t k) (mu (([[c2]]) E2 m2) (fun (x0 : Mem.t k) => f x0))) == 
   mu (([[c2]]) E2 m2) f).
  rewrite  (mu_cte ([[c1]] E1 m1)).
  unfold fone; rewrite Hc1;Usimpl.
  apply (mu_stable_eq ([[c2]]E2 m2)); simpl; apply ford_eq_intro; trivial.
  unfold prodP; apply range_True.
 Qed.

 Lemma equiv_falseR : forall E E' Q c c', 
  equiv falseR E c E' c' Q.
 Proof.
  unfold equiv; intros.
  exists (fun m1 m2 => distr0 _).
  unfold falseR; tauto.
 Qed.

 Hint Resolve equiv_falseR.

 Lemma equiv_False : forall (P:mem_rel) E1 c1 E2 c2 Q,
  (forall k m1 m2, P k m1 m2 -> False) ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  intros; apply equiv_strengthen with falseR.
  unfold falseR; trivial.
  apply equiv_falseR.
 Qed.

 Lemma equiv_case1 : forall (A P Q:mem_rel) E1 c1 E2 c2,
  (forall k x y, sumbool (A k x y) (~A k x y)) ->
  equiv (P /-\ A) E1 c1 E2 c2 Q ->
  equiv (P /-\ ~- A) E1 c1 E2 c2 Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold andR, notR; intros A P Q E1 c1 E2 c2 H H0 H1 k.
  destruct (H0 k) as (d,Hd); destruct (H1 k) as (d',Hd').
  exists (fun m1 m2 => if H k m1 m2 then d m1 m2 else d' m1 m2); intros.
  destruct (H k m1 m2); auto.
 Qed.

 Lemma equiv_case2 : forall (A P Q:mem_rel) E1 c1 E2 c2,
  (forall k x y,sumbool (P k x y) (~P k x y)) ->
  (forall k x y, P k x y -> sumbool (A k x y) (~A k x y)) ->
  equiv (P /-\ A) E1 c1 E2 c2 Q ->
  equiv (P /-\ ~- A) E1 c1 E2 c2 Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold andR, notR; intros A P Q E1 c1 E2 c2 H H0 H1 H2 k.
  destruct (H1 k) as (d,Hd); destruct (H2 k) as (d',Hd').
  exists (fun m1 m2 =>
    match H k m1 m2 with
    | left H1 => if (H0 k m1 m2 H1) then d m1 m2 else d' m1 m2
    | _ => distr0 _
    end); intros.
  destruct (H k m1 m2); intros.
  destruct (H0 k m1 m2 p); auto.
  elim n; trivial.
 Qed.

 Lemma equiv_eq_sem_pre : forall E1 E2 c1 c2 (P:mem_rel),
  (forall k (m:Mem.t k), P k m m -> [[c1]] E1 m == [[c2]] E2 m) ->
  equiv (Meq /-\ P ) E1 c1 E2 c2 Meq.
 Proof.
  unfold equiv; intros.
  exists (fun m1 m2 => Mlet ([[c1]] E1 m1) (fun x => Munit (x, x))).
  unfold Meq, andR; intros m1 m2 (H1, H2); subst.
  apply lift_weaken with (@eq (Mem.t k)); auto.
  rewrite (H _ _ H2).
  apply lift_eq_refl.
 Qed.

 Lemma equiv_eq_sem : forall E1 c1 E2 c2, 
  (forall k (m:Mem.t k), [[c1]] E1 m == [[c2]] E2 m) ->
  equiv Meq E1 c1 E2 c2 Meq.
 Proof.
  intros; apply equiv_strengthen with (Meq /-\ trueR).
  unfold andR, trueR; tauto.
  apply equiv_eq_sem_pre; auto.
 Qed.

 Lemma equiv_eq_mem : forall E c, equiv Meq E c E c Meq.
 Proof.
  intros; apply equiv_eq_sem; trivial.
 Qed.

 Lemma equiv_nil : forall P E1 E2, equiv P E1 nil E2 nil P.
 Proof.
  unfold equiv; intros.
  exists (fun m1 m2 => Munit (m1, m2)); intros.
  repeat rewrite deno_nil; apply lift_unit; trivial.
 Qed.

 Lemma equiv_nil_impl : forall P E1 E2 Q,
  implMR P Q -> equiv P E1 nil E2 nil Q.
 Proof.
  intros P E1 E2 Q H; rewrite H; apply equiv_nil.
 Qed.

 Lemma equiv_app : forall P Q R E c1 c2 E' c3 c4,
  equiv P E c1 E' c3 Q ->
  equiv Q E c2 E' c4 R -> 
  equiv P E (c1++c2) E' (c3++c4) R.
 Proof.
  unfold equiv; intros.
  destruct (H k) as (d, Hd); destruct (H0 k) as (d', Hd').
  exists (fun m1 m2 => Mlet (d m1 m2) (fun p => d' (fst p) (snd p))); intros.
  repeat rewrite deno_app; apply lift_Mlet with (Q k); auto.
 Qed.

 Lemma equiv_cons : forall P Q R E1 i1 c1 E2 i2 c2,
  equiv P E1 [i1] E2 [i2] Q ->
  equiv Q E1 c1 E2 c2 R -> 
  equiv P E1 (i1::c1) E2 (i2::c2) R.
 Proof.
  intros P Q R E1 i1 c1 E2 i2 c2  H H0. 
  apply equiv_app with (Q:=Q) (c1:=[i1]) (c2:=c1) (c3:=[i2]) (c4:=c2); trivial.
 Qed.
 
 Lemma equiv_cond_l : forall P E1 e c c' E2 c2 Q,
  equiv (P /-\ EP1 e) E1 c E2 c2 Q ->
  equiv (P /-\ ~- EP1 e) E1 c' E2 c2 Q ->
  equiv P E1 [If e then c else c'] E2 c2 Q.
 Proof.
  unfold equiv, andR, notR,EP1,is_true.
  intros P E3 e1 c c' E4 c2 Q HD HD' k.
  destruct (HD k) as (d3,Hd); destruct (HD' k) as (d',Hd').
  exists (fun m1 m2 =>
   if E.eval_expr e1 m1 then d3 m1 m2  else d' m1 m2); intros.
  case_eq (E.eval_expr e1 m1); intros Heq;
   rewrite deno_cond; rewrite Heq;[apply Hd | apply Hd']; split; autob.
 Qed.

 Lemma equiv_cond_r :  forall P E1 c1 E2 e c c' Q,
  equiv (P /-\ EP2 e) E1 c1 E2 c Q ->
  equiv (P /-\ ~- EP2 e) E1 c1 E2 c' Q ->
  equiv P E1 c1 E2 [If e then c else c'] Q.
 Proof.
  intros; apply equiv_sym_transp.
  apply equiv_cond_l; apply equiv_sym_transp; simplMR; trivial.
 Qed.

 Lemma equiv_cond : forall P Q E1 (e1:E.expr T.Bool) c1 c2 E2 (e2:E.expr T.Bool) c3 c4,
  equiv (P /-\ (EP1 e1 /-\ EP2 e2)) E1 c1 E2 c3 Q ->
  equiv (P /-\ (~- EP1 e1 /-\ ~- EP2 e2)) E1 c2 E2 c4 Q ->
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
  equiv P E1 [If e1 then c1 else c2] E2 [If e2 then c3 else c4] Q.
 Proof.
  intros; apply equiv_cond_l; apply equiv_cond_r.
  simplMR; trivial.
  apply equiv_False; unfold andR,notR,EP1,EP2.
  intros k m1 m2 ((H2, H3), H4); apply H4; erewrite <- H1; eauto.
  apply equiv_False; unfold andR,notR,EP1,EP2.
  intros k m1 m2 ((H2, H3), H4); apply H3; erewrite H1; eauto.
  simplMR; trivial.
 Qed.

 Lemma equiv_while : forall (P:mem_rel) E1 (e1:E.expr T.Bool) c1 E2 (e2:E.expr T.Bool) c2,
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
  equiv (P /-\ EP1 e1 /-\ EP2 e2) E1 c1 E2 c2 P -> 
  equiv P E1 [while e1 do c1] E2 [while e2 do c2] (P /-\ ~-EP1 e1 /-\ ~-EP2 e2).
 Proof.
  unfold equiv,andR,notR,EP1, EP2, is_true; intros.
  destruct (H0 k) as (d, Hd).
  assert  (forall (m1 m2 : Mem.t k),
   P k m1 m2 ->
   E.eval_expr e1 m1 = true ->
   lift (P k) (d m1 m2) (([[c1]]) E1 m1) (([[c2]]) E2 m2)).
  intros; apply Hd.
  rewrite <- (H _ _ _ H1); auto.
  destruct (while_indR d _ _ (H k) H1) as (d', Hd').
  exists d'; intros.
  apply lift_weaken with (2:= Hd' _ _ H2).
  intros x y (H4,H3); rewrite <- (H _ _ _ H4); rewrite H3; auto.
 Qed.

 Lemma equiv_assign_l : forall Q E1 E2 t1 (x1:Var.var t1) e1,
  equiv (upd1 Q x1 e1) E1 [x1 <- e1] E2 nil Q.
 Proof.
  unfold equiv; intros.
  exists (fun m1 m2 => Munit (m1{!x1<--E.eval_expr e1 m1!}, m2)); intros.
  rewrite deno_assign; rewrite deno_nil; auto using lift_unit.
 Qed.

 Lemma equiv_assign_r : forall Q E1 E2 t2 (x2:Var.var t2) e2,
  equiv (upd2 Q x2 e2) E1 nil E2 [x2 <- e2] Q.
 Proof.
  unfold equiv; intros.
  exists (fun m1 m2 => Munit (m1, m2{!x2<--E.eval_expr e2 m2!})); intros.
  rewrite deno_assign; rewrite deno_nil; auto using lift_unit.
 Qed.
 
 Lemma equiv_assign : forall Q E1 E2 t1 (x1:Var.var t1) t2 (x2:Var.var t2) e1 e2, 
   equiv (upd_para Q x1 e1 x2 e2) E1 [x1 <- e1] E2 [x2 <- e2] Q.
 Proof.
  unfold equiv; intros.
  exists (fun m1 m2 => Munit (m1{!x1<-- E.eval_expr e1 m1!}, m2{!x2<--E.eval_expr e2 m2!})); intros.
  repeat rewrite deno_assign; auto using lift_unit.
 Qed.
 
 (* We can replace the equality of the two list by the permutation *)
 Lemma equiv_random : forall (Q:mem_rel) E1 E2 t (x1 x2:Var.var t) (d1 d2:E.support t),
  equiv (eq_support d1 d2 /-\ forall_random Q x1 x2 d1) 
  E1 [x1 <$- d1] E2 [x2 <$- d2] Q.
 Proof.
  unfold equiv; intros.
  exists (fun m1 m2 => Mlet (sum_support (T.default k t) (E.eval_support d1 m1))
   (fun v => Munit (m1{!x1<--v!}, m2{!x2<--v!}))).
  intros; destruct H as (H1, H2).
  repeat rewrite deno_random; constructor; intros.
  repeat rewrite Mlet_simpl.
  apply mu_stable_eq; simpl; apply ford_eq_intro; intro; trivial.
  repeat rewrite Mlet_simpl.
  rewrite H1; apply mu_stable_eq; simpl; apply ford_eq_intro; intro; trivial.
  apply range_Mlet with (fun v => In v (E.eval_support d1 m1)).
  unfold range; intros; simpl.
  assert (forall n, (n <= (length (E.eval_support d1 m1)))%nat ->
   0 ==
   comp Uplus 0
   (fun n : nat =>
    [1/]1+pred (length (E.eval_support d1 m1)) *
    f (nth n (E.eval_support d1 m1) (T.default k t))) n); auto with arith.
  induction n; simpl; intros; trivial. 
  rewrite <- H. 
  repeat Usimpl; apply IHn; auto with arith.
  apply nth_In; auto with arith.
  intros; unfold range; simpl; intros.
  apply H0; red; simpl; auto.
 Qed.
 
 Lemma equiv_random_permut : forall (Q:mem_rel) E1 E2 t (x1 x2:Var.var t) 
  (f:forall k, Mem.t k -> Mem.t k -> T.interp k t -> T.interp k t) (d1 d2:E.support t),
  equiv ((permut_support f d1 d2) /-\ 
   (fun k m1 m2 => 
    forall v, In v (E.eval_support d2 m2) -> 
     Q k (m1{!x1 <-- f k m1 m2 v!}) (m2{!x2 <-- v!})))
  E1 [x1 <$- d1] E2 [x2<$-d2] Q.
 Proof.
  unfold equiv; intros.
  exists (fun m1 m2 =>
   Mlet (([[ [x2 <$- d2] ]]) E2 m2)
   (fun m => 
    Munit (m1{! x1 <-- f k m1 m2 (m x2) !}, m))); intros.
  destruct H; constructor; intros.
  rewrite Mlet_simpl, deno_random_elim, deno_random_elim.
  change  (fun x0 : T.interp k t =>
   mu
   (Munit
    (m1 {!x1 <-- f k m1 m2 ((m2 {!x2 <-- x0!}) x2)!}, m2 {!x2 <-- x0!}))
   (fun x : Mem.t k * Mem.t k => f0 (fst x))) with
  (fun x0 : T.interp k t =>f0 (m1 {!x1 <-- f k m1 m2 ((m2 {!x2 <-- x0!}) x2)!})).
  symmetry.
  refine (@sum_dom_permut_eq 
    (T.interp k t) (T.interp k t)
    (T.default k t) (T.default k t) 
    (E.eval_support d1 m1) (E.eval_support d2 m2) 
    (fun x0 : T.interp k t => f0 (m1 {!x1 <-- x0!}))
    (fun x0 : T.interp k t =>
    f0 (m1 {!x1 <-- f k m1 m2 ((m2 {!x2 <-- x0!}) x2)!})) _ ).
  red in H.
  generalize (E.eval_support d1 m1) (E.eval_support d2 m2) H; clear H H0.
  induction 1; constructor; subst; trivial.
  rewrite Mem.get_upd_same; trivial.
  rewrite Mlet_simpl, deno_random_elim, deno_random_elim; trivial.
  rewrite deno_random.
  unfold range; intros.
  repeat rewrite Mlet_simpl.
  change (0 == sum_dom (T.default k t) (E.eval_support d2 m2)
   (fun x : T.interp k t => f0 (m1 {!x1 <-- f k m1 m2 (m2 {!x2 <-- x!} x2)!}, m2 {!x2 <-- x!}))).
  rewrite sum_dom_finite.
  generalize (E.eval_support d2 m2) ([1/]1+pred (length (E.eval_support d2 m2))) H0.
  induction l; simpl; intros; trivial.
  rewrite <- IHl; auto.
  rewrite <- H1; auto.
  red; simpl.
  rewrite Mem.get_upd_same; auto.
 Qed.
   
 Lemma equiv_union_Modify_pre : forall X1 X2 (P Q Q':mem_rel) 
  (P1 P2:forall k, Mem.t k -> Prop) E1 c1 E2 c2,
  (forall k m1 m2, P k m1 m2 -> P1 k m1 /\ P2 k m2) ->
  (forall k m1 m2 m1' m2', 
   P k m1 m2 -> Q k m1' m2' ->
   Q' k (m1{!X1 <<- m1'!}) (m2{!X2 <<- m2'!})) ->
  Modify_pre P1 E1 X1 c1 ->
  Modify_pre P2 E2 X2 c2 ->
  equiv P E1 c1 E2 c2 Q ->
  equiv P E1 c1 E2 c2 Q'.
 Proof.
  unfold equiv; intros.
  destruct (H3 k) as (d, Hd).
  exists (fun m1 m2 => 
   Mlet (d m1 m2) (fun p => Munit (m1{!X1<<-fst p!}, m2{!X2<<-snd p!}))).
  intros m1 m2 HP; constructor; simpl; intros.
  rewrite ((Hd _ _ HP).(l_fst) (fun x => f (m1 {!X1 <<- x!}))).
  symmetry; eapply Modify_pre_deno_elim with (k:=k); eauto.
  destruct (H _ _ _ HP); trivial.
  rewrite ((Hd _ _ HP).(l_snd) (fun x => f (m2 {!X2 <<- x!}))).
  symmetry; eapply Modify_pre_deno_elim with (k:= k); eauto.
  destruct (H _ _ _ HP); trivial.
  unfold range; intros; simpl.
  apply (Hd _ _ HP).(l_range); intros; apply H4.
  red; simpl; apply H0; auto.
 Qed.

 Lemma equiv_union_Modify_pre2 : forall X1 X2 (P Q Q':mem_rel) 
  (P1 P2:forall k, Mem.t k -> Prop) E1 c1 E2 c2,
  decMR P ->
  (forall k m1 m2, P k m1 m2 -> P1 k m1 /\ P2 k m2) ->
  (forall k m1 m2 m1' m2', 
   P k m1 m2 -> Q k m1' m2' -> eeq_mem X1 m1 m1' -> eeq_mem X2 m2 m2' ->
   Q' k m1' m2') ->
  Modify_pre P1 E1 X1 c1 ->
  Modify_pre P2 E2 X2 c2 ->
  equiv P E1 c1 E2 c2 Q ->
  equiv P E1 c1 E2 c2 Q'.
 Proof.
  unfold equiv; intros.
  destruct (H3 k) as (d, Hd).
  assert (forall m1:Mem.t k, P1 k m1 ->
   lift (fun m m'=> m = m' /\ eeq_mem X1 m1 m)
     (Mlet ([[c1]] E1 m1) (fun m => Munit (m, m))) ([[c1]] E1 m1) ([[c1]] E1 m1)).
   constructor; intros.
   rewrite Mlet_simpl; apply (mu_stable_eq ([[c1]] E1 m1)).
   simpl; apply ford_eq_intro; intro; trivial.
   rewrite Mlet_simpl; apply (mu_stable_eq ([[c1]] E1 m1)).
   simpl; apply ford_eq_intro; intro; trivial.
   unfold range; intros; rewrite Mlet_simpl.
   assert (W:= Modify_pre_deno H1 _ H4).
   transitivity (mu (Mlet (([[ c1 ]]) E1 m1) (fun m' : Mem.t k => Munit (m1 {!X1 <<- m'!})))
                   (fun x : Mem.t k => mu (Munit (x, x)) f)).
   rewrite Mlet_simpl.
   rewrite <- (mu_0 (([[ c1 ]]) E1 m1)).
   apply mu_stable_eq; simpl; apply ford_eq_intro; intro; apply H5; split; trivial.
   red; intros; simpl.
   rewrite update_mem_notin; trivial.
   assert (W':= ford_eq_elim (Oeq_sym W)); trivial.
  assert (exists d1, 
     forall m1 m2, P k m1 m2 ->
        (lift (fun m1' m2' => Q k m1' m2' /\ eeq_mem X1 m1 m1') (d1 m1 m2)
             (([[ c1 ]]) E1 m1) (([[ c2 ]]) E2 m2))).
   assert (forall (k : nat) (m1 m2 : Mem.t k), P k m1 m2 -> P1 k m1).
    intros k0 m1 m2 HP; destruct (H k0 m1 m2 HP); trivial.
   exists 
    (fun  m1 m2 =>
      match X k m1 m2 with
      | left HP =>
        dd' (@mem_eqU k) (H4 m1 (H5 _ _ _ HP)) (Hd _ _ HP)
      | _ => distr0 _
      end).
   intros m1 m3 HP. 
   destruct (X k m1 m3); simpl.
   apply lift_trans_discr; auto using mem_eqU_spec, sem_discr.
   intros x y z (W1, W2); subst; tauto.
   elim n; trivial.
  assert (forall m2:Mem.t k, P2 k m2 ->
   lift (fun m m'=> m = m' /\ eeq_mem X2 m2 m')
     (Mlet ([[c2]] E2 m2) (fun m => Munit (m, m))) ([[c2]] E2 m2) ([[c2]] E2 m2)).
   constructor; intros.
   rewrite Mlet_simpl; apply (mu_stable_eq ([[c2]] E2 m2)).
   simpl; apply ford_eq_intro; intro; trivial.
   rewrite Mlet_simpl; apply (mu_stable_eq ([[c2]] E2 m2)).
   simpl; apply ford_eq_intro; intro; trivial.
   unfold range; intros; rewrite Mlet_simpl.
   assert (W:= Modify_pre_deno H2 _ H6).
   transitivity (mu (Mlet (([[ c2 ]]) E2 m2) (fun m' : Mem.t k => Munit (m2 {!X2 <<- m'!})))
                   (fun x : Mem.t k => mu (Munit (x, x)) f)).
   rewrite Mlet_simpl.
   rewrite <- (mu_0 (([[ c2 ]]) E2 m2)).
   apply mu_stable_eq; simpl; apply ford_eq_intro; intro; apply H7; split; trivial.
   red; intros; simpl.
   rewrite update_mem_notin; trivial.
   assert (W':= ford_eq_elim (Oeq_sym W)); trivial.
  destruct H5 as (d1, Hd1).
  assert (forall (k : nat) (m1 m2 : Mem.t k), P k m1 m2 -> P2 k m2).
    intros k0 m1 m2 HP; destruct (H k0 m1 m2 HP); trivial.
  exists  
   (fun  m1 m2 =>
      match X k m1 m2 with
      | left HP =>
        dd' (@mem_eqU k) (Hd1 _ _ HP) (H6 m2 (H5 _ _ _ HP))
      | _ => distr0 _
    end).
   intros m1 m3 HP. 
   destruct (X k m1 m3); simpl.
   apply lift_trans_discr; auto using mem_eqU_spec, sem_discr.
   intros x y z (W1, W2) (W3, W4); subst; eauto.
   elim n; trivial.
 Qed.
 
 Lemma equiv_lossless_Modify : forall P X1 X2 M1 M2 E1 c1 E2 c2,
  depend_only_rel P X1 X2 ->
  lossless E1 c1 ->
  lossless E2 c2 ->
  Modify E1 M1 c1 ->
  Modify E2 M2 c2 ->
  Vset.disjoint X1 M1 ->
  Vset.disjoint X2 M2 ->
  equiv P E1 c1 E2 c2 P.
 Proof.
  intros; intro k.
  exists (fun m1 m2 => prod_distr ([[c1]] E1 m1) ([[c2]] E2 m2)); intros.
  constructor; intros.
  rewrite prod_distr_fst.
  unfold lossless in H1; unfold fone; rewrite H1; auto.
  rewrite prod_distr_snd.
  unfold lossless in H0; unfold fone; rewrite H0; auto.
  unfold range, prod_distr; simpl; intros.
  rewrite (Modify_deno_elim H2 (k:=k)).
  transitivity (mu (([[c1]]) E1 m1) (fun _ => 0)).
  symmetry; apply mu_0.
  apply mu_stable_eq; simpl; apply ford_eq_intro; intros m'.
  rewrite (Modify_deno_elim H3 (k:=k)).
  transitivity (mu (([[c2]]) E2 m2) (fun _ => 0)).
  symmetry; apply mu_0.
  apply mu_stable_eq; simpl; apply ford_eq_intro; intros m''.
  apply H7; red; simpl.
  apply H with (3:= H6);
  apply req_mem_sym; apply req_mem_update_disjoint; trivial.
 Qed.

 Lemma equiv_inv_Modify : forall (inv:mem_rel) (X1 X2 M1 M2:Vset.t) 
  (P:mem_rel) (E1:env) (c1:cmd) (E2:env) (c2:cmd) (O:Vset.t),
  depend_only_rel inv X1 X2 ->
  Modify E1 M1 c1 ->
  Modify E2 M2 c2 ->
  O [<=] Vset.inter M1 M2 ->
  Vset.disjoint X1 M1 -> 
  Vset.disjoint X2 M2 -> 
  equiv P E1 c1 E2 c2 (req_mem_rel O trueR) ->
  equiv (P /-\ inv) E1 c1 E2 c2 (req_mem_rel O inv).
 Proof.
  intros; intros k.
  destruct (H5 k) as [d Hd].
  exists (fun m1 m2 => 
   Mlet (d m1 m2) (fun mm => Munit (m1{! M1 <<- fst mm !}, m2{! M2 <<- snd mm!}))).
  intros.
  destruct H6 as [Hreq Hinv].
  destruct (Hd m1 m2 Hreq); clear Hd.
  constructor; intros.

  rewrite (Modify_deno_elim H0).
  apply (l_fst (fun m' => f (m1 {!M1 <<- m'!}))). 

  rewrite (Modify_deno_elim H1).
  apply (l_snd (fun m' => f (m2 {!M2 <<- m'!}))). 

  apply (range_Mlet _ l_range).
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
 Qed.

 Definition injR1 (P : forall k, Mem.t k -> Prop) : mem_rel :=
   fun k m1 m2 => P k m1.

 Definition injR2 (P : forall k, Mem.t k -> Prop) : mem_rel :=
   fun k m1 m2 => P k m2.
  
Lemma lift_trans_l A P (HP : forall (x : A), sumbool (P x) (~P x)) : 
  forall B (R : A -> B -> Prop) d d1 d1' d' d2,
 lift (fun (a1 a2: A) => a1 = a2 /\ P a1) d d1 d1' ->
 lift R d' d1' d2 ->
 lift (fun (a : A) (b : B) => R a b /\ P a) d' d1 d2.
Proof.
 intros; constructor.
 intros.
 
 rewrite H0.(l_fst).
 rewrite <- H.(l_snd).
 rewrite <- H.(l_fst).
 destruct H.
 apply range_eq with (1:= l_range).
 intros (a1,a2) (H1,H2); simpl.
 simpl in *; subst; trivial.

 apply H0.(l_snd).

 assert (range (fun p => P (fst p)) d').
  unfold range.
  intros.
  split.
  auto.
  pose (F := fun a => if HP a then 0 else 1).
  transitivity (mu d' (fun p => F (fst p))).
  apply mu_le_compat; trivial.
  intros p.
  unfold F.
  destruct (HP (fst p)).
  rewrite H1; trivial.
  auto.
  rewrite H0.(l_fst).
  rewrite <- H.(l_snd).
  destruct H.
  unfold range in l_range.
  rewrite <- l_range.
  auto.
  intros (a1,a2) (H2,H3); subst.
  unfold F; simpl in *; subst.
  destruct (HP a2); trivial.
  elim n; trivial.

 unfold range; intros.
 transitivity ((mu d') (fun p => if HP (fst p) then f p else 0)).
 destruct H0.
 unfold range in l_range.
 apply l_range.
 intros.
 destruct (HP (fst x)).
 apply H2.
 split; trivial.
 trivial.
 
 apply range_eq with (1 := H1).
 intros.
 destruct (HP (fst a)); trivial.
 elim n; trivial.
Qed.

 Lemma equiv_trans_injR1 : forall P1 P Q Q1 E1 c1 E2 c2 (* E1' c1' *),
   (forall k (x : Mem.t k), sumbool (Q1 k x) (~ Q1 k x)) ->
  equiv (Meq /-\ injR1 P1) E1 c1 E1 c1 (Meq /-\ injR1 Q1) ->
  equiv P E1 c1 E2 c2 Q ->
  equiv (P /-\ injR1 P1) E1 c1 E2 c2 (Q /-\ injR1 Q1).
Proof.
  intros; intro k.
  destruct (H k) as (d, Hd); destruct (H0 k) as (d',Hd').
  exists d'; intros m1 m2 (W0, W1).
  unfold andR, injR1.
  eapply lift_trans_l.
  trivial.  
  apply lift_weaken with ((Meq /-\ injR1 Q1) k).
  intros m1' m2' (W2, W3); auto.
  apply Hd.
  unfold injR1 in W1.
  split; auto.
  auto.
Qed.
   
 Lemma equiv_modify : forall (P Q : mem_rel) (E1 E2 : env) (c1 c2 : cmd) 
   (t : T.type) (x : Var.var t) (c : forall k, T.interp k t) X,
   ~Vset.mem x X ->
   Modify E1 X c1 ->
   equiv P E1 c1 E2 c2 Q ->
   equiv (P /-\ fun k m1 m2 => E.eval_expr x m1 = c k)
   E1 c1 E2 c2 
   (Q /-\ fun k m1 m2 => E.eval_expr x m1 = c k).
 Proof.
  intros.
  apply equiv_trans_injR1.  
  intros.
  generalize (T.i_eqb_spec k t (E.eval_expr x x0) (c k)).
  destruct (T.i_eqb k t (E.eval_expr x x0) (c k)); auto.
  intro; exists (fun m1 m2 => Mlet ([[c1]] E1 m1) (fun m' => Munit (m', m'))).
  intros m1 m2 (W0, W1); constructor; intros.
  rewrite Mlet_simpl.
  apply mu_stable_eq.
  refine (ford_eq_intro _); intros; trivial.
  rewrite Mlet_simpl.
  rewrite W0.
  apply mu_stable_eq.
  refine (ford_eq_intro _); intros; trivial.
  rewrite (@Modify_deno E1 X c1 H0), Mcomp.
  apply range_Mlet with (fun _ => True).
  apply range_True.
  unfold range; intros; simpl.
  apply H3.
  split; trivial; simpl.
  unfold injR1 in *.
  rewrite <- W1.
  apply update_mem_notin; trivial.
  trivial.
Qed.

 Lemma equiv_call : forall (P Pf Qf Q:mem_rel) t E1 (x1:Var.var t) f1 a1 E2 (x2:Var.var t) f2 a2,
  (forall k m1 m2, P k m1 m2 -> 
   Pf k (init_mem E1 f1 a1 m1) (init_mem E2 f2 a2 m2)) ->
  (forall k m1 m1' m2 m2', P k m1 m2 -> Qf k m1' m2' -> 
   Q k (return_mem E1 x1 f1 m1 m1') (return_mem E2 x2 f2 m2 m2')) ->
  equiv Pf E1 (proc_body E1 f1) E2 (proc_body E2 f2) Qf ->
  equiv P E1 [x1 <c- f1 with a1] E2 [x2 <c- f2 with a2] Q.
 Proof.
  unfold equiv; intros. 
  destruct (H1 k) as (d, Hd).
  exists (fun m1 m2 => 
   Mlet (d (init_mem E1 f1 a1 m1) (init_mem E2 f2 a2 m2))
   (fun p => Munit (return_mem E1 x1 f1 m1 (fst p), return_mem E2 x2 f2 m2 (snd p)))).
  intros; repeat rewrite deno_call.
  apply lift_Mlet with (Qf k); auto.
  intros m1' m2' HQf; apply lift_unit; auto.
 Qed.

 Lemma equiv_deno : forall P E1 c1 E2 c2 Q,
  equiv P E1 c1 E2 c2 Q ->
  forall k (f g:Mem.t k->U), (forall m1 m2, Q k m1 m2 -> f m1 == g m2) ->
   forall m1 m2, P k m1 m2 -> mu ([[c1]] E1 m1) f == mu ([[c2]] E2 m2) g.
 Proof.
  unfold equiv; intros.
  destruct (H k) as (d, Hd).
  rewrite <- (Hd _ _ H1).(l_fst). 
  rewrite <- (Hd _ _ H1).(l_snd).
  apply range_eq with (1:= (Hd _ _ H1).(l_range)).
  intros; apply H0; auto.
 Qed.
 
 Lemma equiv_deno_le : forall P E1 c1 E2 c2 Q,
  equiv P E1 c1 E2 c2 Q ->
  forall k (f g:Mem.t k->U), 
  (forall m1 m2, Q k m1 m2 -> f m1 <= g m2) ->
   forall m1 m2, P k m1 m2 -> mu ([[c1]] E1 m1) f <= mu ([[c2]] E2 m2) g.
 Proof.
  unfold equiv; intros.
  destruct (H k) as (d, Hd).
  rewrite <- (Hd _ _ H1).(l_fst). 
  rewrite <- (Hd _ _ H1).(l_snd).
  apply range_le with (1:= (Hd _ _ H1).(l_range)).
  intros; apply H0; auto.
 Qed.

 (** ** Observationnal equivalence with pre and post conditions *)

 (* Three variations of equiv *)
 
 Definition EqObsRel I P E1 c1 E2 c2 O Q :=
  equiv (req_mem_rel I P) E1 c1 E2 c2 (req_mem_rel O Q).
 
 Definition EqObsInv P I E1 c1 E2 c2 O :=
  equiv (req_mem_rel I P) E1 c1 E2 c2 (req_mem_rel O P).
  
 Lemma equiv_trueR_EqObs : forall I E1 c1 E2 c2 O,
  equiv (req_mem_rel I trueR) E1 c1 E2 c2 (req_mem_rel O trueR) ->
  EqObs I E1 c1 E2 c2 O.
 Proof.
  unfold EqObs, req_mem_rel; intros I E1 c1 E2 c2 O; simplMR; trivial.
 Qed.

 Lemma EqObs_equiv_trueR : forall I E1 c1 E2 c2 O,
  EqObs I E1 c1 E2 c2 O ->
  equiv (req_mem_rel I trueR) E1 c1 E2 c2 (req_mem_rel O trueR).
 Proof.
  intros; simplMR; trivial. 
 Qed.
 
 Lemma EqObs_sym : forall I E1 c1 E2 c2 O,
  EqObs I E1 c1 E2 c2 O -> EqObs I E2 c2 E1 c1 O.
 Proof.
  unfold EqObs; intros; apply equiv_sym; auto.
 Qed.

 Lemma EqObs_trans : 
   forall I E1 c1 E2 c2 E3 c3 O,
   EqObs I E1 c1 E2 c2 O ->
   EqObs I E2 c2 E3 c3 O ->
   EqObs I E1 c1 E3 c3 O.
 Proof.
  unfold EqObs; intros.
  apply equiv_trans_trans with E2 c2; auto.
 Qed.
 
 Add Morphism EqObs 
  with signature Vset.subset ++> (@eq env) ==> (@eq cmd) ==> 
   (@eq env) ==> (@eq cmd) ==> Vset.subset --> impl 
  as EqObs_imp_Morph.
 Proof.
  unfold EqObs, flip, impl; intros.
  rewrite H0, <- H; trivial.
 Qed.

 Add Morphism EqObs
  with signature Vset.eq ==> (@eq env) ==> (@eq cmd) ==> 
   (@eq env) ==> (@eq cmd) ==> Vset.eq ==> iff 
  as EqObs_iff_Morph.
 Proof.
  unfold EqObs; intros.
  rewrite <- H, H0; tauto.
 Qed.

 Add Morphism EqObsInv 
  with signature iffMR ==> Vset.subset ++> (@eq env) ==> (@eq cmd) ==> 
   (@eq env) ==> (@eq cmd) ==> Vset.subset --> impl 
  as EqObsInv_imp_Morph.
 Proof.
  unfold EqObsInv, flip, impl; intros.
  rewrite <- H, <- H0, H1; trivial.
 Qed.

 Add Morphism EqObsInv 
  with signature iffMR ==> Vset.eq ==> (@eq env) ==> (@eq cmd) ==> 
   (@eq env) ==> (@eq cmd) ==> Vset.eq ==> iff 
  as EqObsInv_iff_Morph.
 Proof.
  unfold EqObsInv; intros.
  rewrite <- H, <- H0, H1; tauto.
 Qed.

 Add Morphism EqObsRel 
  with signature Vset.subset ++> implMR --> (@eq env) ==> (@eq cmd) ==> 
   (@eq env) ==> (@eq cmd) ==> Vset.subset --> implMR ++> impl 
  as EqObsRel_imp_Morph.
 Proof.
  unfold EqObsRel, flip, impl; intros.
  rewrite <- H, H1, H0, <- H2; trivial.
 Qed.

 Add Morphism EqObsRel 
  with signature Vset.eq ==> iffMR ==> (@eq env) ==> (@eq cmd) ==> 
   (@eq env) ==> (@eq cmd) ==> Vset.eq ==> iffMR ==> iff 
  as EqObsRel_iff_Morph.
 Proof.
  unfold EqObsRel; intros.
  rewrite <- H, H0, H1, <- H2; split; trivial.
 Qed.

 Lemma EqObs_deno : forall I E1 c1 E2 c2 O,
  EqObs I E1 c1 E2 c2 O ->
  forall k (f g:Mem.t k -> U),
   (forall m1 m2, m1 =={O} m2 -> f m1 == g m2) ->
   forall m1 m2,
    m1 =={I} m2 -> 
    mu ([[ c1 ]] E1 m1) f == mu ([[ c2 ]] E2 m2) g.
 Proof.
  intros; apply equiv_deno with (kreq_mem I) (kreq_mem O); trivial.
 Qed.

 Lemma EqObs_deno_same :forall I E1 c1 E2 c2 O,
  EqObs I E1 c1 E2 c2 O ->
  forall k (f g:Mem.t k -> U),
   (forall m1 m2, m1 =={O} m2 -> f m1 == g m2) ->
   forall m, mu ([[ c1 ]] E1 m) f == mu ([[ c2 ]] E2 m) g. 
 Proof.
  intros; apply EqObs_deno with I O; trivial.
 Qed.
 
 Lemma EqObs_assign : forall E1 E2 t (v:Var.var t) (e:E.expr t),
  EqObs (fv_expr e) E1 [v <- e] E2 [v <- e] (Vset.singleton v).
 Proof.
  unfold EqObs; intros; eapply equiv_strengthen; [ | apply equiv_assign].
  unfold kreq_mem; intros; red; red; intros.
  apply Vset.singleton_complete in H0.
  inversion H0; simpl; repeat rewrite Mem.get_upd_same.
  apply EqObs_e_fv_expr; trivial.
 Qed.
  
 Lemma EqObs_random : forall E1 E2 t (v:Var.var t) (d:E.support t),
  EqObs (fv_distr d) E1 [v <$- d] E2 [v <$- d] (Vset.singleton v).
 Proof.
  unfold EqObs; intros; eapply equiv_strengthen; [ | apply equiv_random].
  unfold kreq_mem; intros; red; intros; split.
  unfold eq_support; apply EqObs_d_fv_expr; trivial.
  red; red; intros.
  apply Vset.singleton_complete in H1.
  inversion H1; simpl; repeat rewrite Mem.get_upd_same; trivial.
 Qed.

 (** ** Procedure info used for equivalence *)
 
 Record dproc_eq_refl_info : Type := 
  {
   dpi_mod : Vset.t;      (* modified globals variables *)
   dpi_input : Vset.t;    (* global variables *)
   dpi_params : Vset.t;   (* local variables  *)
   dpi_output : Vset.t;   (* global variables *)
   dpi_lossless : bool
  }.

 Record sproc_eq_refl_info (E:env) (t:T.type) (f:Proc.proc t) (data:dproc_eq_refl_info) : Prop := 
  {
   slossless_spec : data.(dpi_lossless) -> lossless E (proc_body E f);  
   sinput_global : forall x, Vset.mem x data.(dpi_input) -> Var.is_global x;
   sparams_subset : data.(dpi_params) [<=] Vset_of_var_decl (proc_params E f);
   soutput_global : forall x, Vset.mem x data.(dpi_output) -> Var.is_global x;
   smod_global : forall x, Vset.mem x data.(dpi_mod) -> Var.is_global x;
   smod_spec : exists L, 
    (forall x, Vset.mem x L -> Var.is_local x) /\ 
    Modify E (Vset.union L data.(dpi_mod)) (proc_body E f);
   soutput_subset : data.(dpi_output) [<=] data.(dpi_mod); 
    spi_spec : 
    exists ls, 
     (forall x, Vset.mem x ls -> Var.is_local x) /\ 
     EqObs (Vset.union data.(dpi_input) data.(dpi_params))
     E (proc_body E f) E (proc_body E f) (Vset.union ls data.(dpi_output)) /\ 
     EqObs_e (Vset.union (Vset.union ls data.(dpi_output)) 
      (Vset.diff data.(dpi_input) data.(dpi_mod)))
     (proc_res E f) (proc_res E f)    
  }.

 Record proc_eq_refl_info (E:env) (t:T.type) (f:Proc.proc t) : Type := 
  {
   dpi : dproc_eq_refl_info;
   spi : sproc_eq_refl_info E f dpi
  }.
 
 Definition pi_mod E t f (pi:@proc_eq_refl_info E t f) := 
  pi.(dpi).(dpi_mod).
 
 Definition pi_input E t f (pi:@proc_eq_refl_info E t f) := 
  pi.(dpi).(dpi_input).
 
 Definition pi_params E t f (pi:@proc_eq_refl_info E t f) := 
  pi.(dpi).(dpi_params).
 
 Definition pi_output E t f (pi:@proc_eq_refl_info E t f) := 
  pi.(dpi).(dpi_output).
 
 Definition pi_lossless E t f (pi:@proc_eq_refl_info E t f) := 
  pi.(dpi).(dpi_lossless).

 Definition pi_lossless_spec E t f (pi:@proc_eq_refl_info E t f) :
  (pi_lossless pi) -> lossless E (proc_body E f) :=
  pi.(spi).(slossless_spec).
 
 Definition input_global E t f (pi:@proc_eq_refl_info E t f) :
  forall x, Vset.mem x (pi_input pi) -> Var.is_global x := 
   pi.(spi).(sinput_global).
 
 Definition params_subset E t f (pi:@proc_eq_refl_info E t f) :
  (pi_params pi) [<=] Vset_of_var_decl (proc_params E f):= 
  pi.(spi).(sparams_subset).
 
 Definition output_global E t f (pi:@proc_eq_refl_info E t f) :
  forall x, Vset.mem x (pi_output pi) -> Var.is_global x := 
   pi.(spi).(soutput_global).
 
 Definition mod_global E t f (pi:@proc_eq_refl_info E t f) :
  forall x, Vset.mem x (pi_mod pi) -> Var.is_global x := 
   pi.(spi).(smod_global).
 
 Definition mod_spec E t f (pi:@proc_eq_refl_info E t f) :
  exists L, 
   (forall x, Vset.mem x L -> Var.is_local x) /\ 
   Modify E (Vset.union L (pi_mod pi)) (proc_body E f) := 
   pi.(spi).(smod_spec).
 
 Definition output_subset E t f (pi:@proc_eq_refl_info E t f) :
  (pi_output pi) [<=] (pi_mod pi):= 
  pi.(spi).(soutput_subset).

 Definition pi_spec E t f (pi:@proc_eq_refl_info E t f) :
  exists ls, 
   (forall x, Vset.mem x ls -> Var.is_local x) /\ 
   EqObs (Vset.union (pi_input pi) (pi_params pi))
   E (proc_body E f) E (proc_body E f) (Vset.union ls (pi_output pi)) /\ 
   EqObs_e (Vset.union (Vset.union ls (pi_output pi)) 
    (Vset.diff (pi_input pi) (pi_mod pi)))
   (proc_res E f) (proc_res E f) := 
   pi.(spi).(spi_spec).
 
 Lemma pi_spec_call_1 : forall E t (f:Proc.proc t) (pi:proc_eq_refl_info E f),
  forall (d1 d2:Var.var t) args1 args2 I,
   EqObs_args (proc_params E f) args1 (proc_params E f) args2 (pi_params pi) I ->
   pi_input pi [<=] I ->
   equiv (kreq_mem I) E [d1 <c- f with args1] E [d2 <c- f with args2] 
   (fun k m1 m2 => 
    m1 =={Vset.remove d1 
     (Vset.remove d2 (Vset.union (pi_output pi) (Vset.diff I (pi_mod pi))))} m2 /\
    E.eval_expr d1 m1 = E.eval_expr d2 m2).
 Proof.
  intros.
  apply equiv_call with 
   (Pf:= kreq_mem 
    (Vset.union (Vset.union (pi_input pi) (pi_params pi))
     (Vset.diff (get_globals I) (pi_mod pi))))
   (Qf := fun k m1 m2 => 
    m1 =={Vset.union (pi_output pi) (Vset.diff (get_globals I) (pi_mod pi))} m2 /\
    E.eval_expr (proc_res E f) m1 = E.eval_expr (proc_res E f) m2).
  (* init *)
  unfold kreq_mem; intros.
  eapply req_mem_weaken;[ | apply EqObs_args_correct with (1:= H)]; trivial.
  rewrite (VsetP.union_sym (pi_input pi)).
  rewrite VsetP.union_assoc; apply VsetP.subset_union_ctxt; auto with set.
  apply VsetP.subset_trans with (Vset.union (get_globals I) (get_globals I)).
  apply VsetP.subset_union_ctxt; auto with set.
  apply Vset.subset_complete; intros. 
  apply get_globals_complete.
  apply Vset.subset_correct with (1:= H0); trivial.
  apply (input_global pi); trivial.
  rewrite VsetP.union_idem; auto with set.
  (* post *)
  intros k m1 m1' m2 m2' H1 (H2,H3); split.
  red; intros.
  repeat rewrite VsetP.remove_spec in H4; destruct H4 as ((H4,H5),H6).
  rewrite VsetP.union_spec, VsetP.diff_spec in H4.
  case_eq (Var.is_global x); intros.
  repeat rewrite return_mem_global; trivial.
  apply H2; rewrite VsetP.union_spec, VsetP.diff_spec; intuition.
  right; split; trivial. 
  apply get_globals_complete; trivial.
  assert (Var.is_local x) by (unfold Var.is_local; rewrite H7; trivial).
  repeat rewrite return_mem_local; trivial.
  apply H1; intuition.
  apply output_global in H9; rewrite H7 in H9; trivialb.
  simpl. repeat rewrite return_mem_dest; trivial.
  (* body *)
  destruct (mod_spec pi) as (L, (H1,H2)).
  destruct (pi_spec pi) as (ls, (H3,(H4,H5))).
  assert (Modify_pre (fun _ _ => True) E 
   (Vset.union (Vset.union L (pi_mod pi)) ls) (proc_body E f)).
  apply Modify_Modify_pre.    
  apply Modify_weaken with (1:=H2); auto with set.
  apply equiv_union_Modify_pre with (3:= H6) (4:=H6) 
   (Q:= kreq_mem (Vset.union ls (pi_output pi))); auto.
  unfold kreq_mem; intros; split.
  red; intros t0 x H9; rewrite VsetP.union_spec, VsetP.diff_spec in H9; destruct H9.
  assert (Vset.mem x (Vset.union (Vset.union L (pi_mod pi)) ls)).
  repeat rewrite VsetP.union_spec; left; right.
  apply Vset.subset_correct with (1:= output_subset pi); trivial.
  repeat rewrite update_mem_in; trivial.
  apply H8; rewrite VsetP.union_spec; auto.
  assert (~Vset.mem x (Vset.union (Vset.union L (pi_mod pi)) ls)).
  destruct H9; repeat rewrite (VsetP.union_spec).
  apply get_globals_spec in H9.
  intros [ [W|W] | W]; auto.
  apply H1 in W; unfold Var.is_local in W; rewrite H9 in W; discriminate.
  apply H3 in W; unfold Var.is_local in W; rewrite H9 in W; discriminate.
  repeat rewrite update_mem_notin; trivial. 
  apply H7; rewrite VsetP.union_spec,VsetP.diff_spec; auto.
  apply H5.
  repeat apply req_mem_union; red; intros.
  repeat rewrite update_mem_in; auto with set.
  assert (W:= Vset.subset_correct (output_subset pi) _ H9).
  repeat rewrite update_mem_in; auto with set.
  rewrite VsetP.diff_spec in H9; destruct H9.
  assert (W1:= input_global pi _ H9).
  assert (~Vset.mem x (Vset.union (Vset.union L (pi_mod pi)) ls)).
  repeat rewrite (VsetP.union_spec); intros [ [W|W] | W]; auto.
  apply H1 in W; unfold Var.is_local in W; rewrite W1 in W; discriminate.
  apply H3 in W; unfold Var.is_local in W; rewrite W1 in W; discriminate.
  repeat rewrite update_mem_notin; trivial; auto with set.
  apply equiv_strengthen with (2:=H4); unfold kreq_mem; intros.
  apply req_mem_weaken with (2:=H7); auto with set.
 Qed.

 Lemma pi_spec_call : forall E t (f:Proc.proc t) (pi:proc_eq_refl_info E f),
  forall (d:Var.var t) args I,
   EqObs_args (proc_params E f) args (proc_params E f) args (pi_params pi) I ->
   pi_input pi [<=] I ->
   EqObs I E [d <c- f with args] E [d<c- f with args] 
   (Vset.union (Vset.add d (pi_output pi)) (Vset.diff I (pi_mod pi))).
 Proof.
  intros; unfold EqObs.
  eapply equiv_weaken;[ | apply (pi_spec_call_1 pi)]; auto.
  intros k m1 m2 (H1,H2) tx x Hin.
  destruct (VarP.eq_dec d x); subst.
  inversion e; simpl; trivial.
  apply H1.
  repeat (rewrite VsetP.remove_spec; split; trivial).
  rewrite <- VsetP.add_union_comm,VsetP.add_spec in Hin; destruct Hin; trivial.
  elim (n H3).
 Qed.

 Lemma mod_spec_call : forall E t (f:Proc.proc t) 
  (pif: proc_eq_refl_info E f) (d:Var.var t) args,
  Modify E (Vset.add d (pi_mod pif)) [d <c- f with args].
 Proof.
  intros; destruct (mod_spec pif) as (L,(H,H0)).
  eapply Modify_weaken;[ apply Modify_call with (1:=H0) | ].
  apply VsetP.subset_add_ctxt.
  apply Vset.subset_complete; intros.
  assert (W:=get_globals_spec _ _ H1).
  assert (Vset.mem x (Vset.union L (pi_mod pif))).
  apply Vset.subset_correct with 
   (1:= get_globals_subset(Vset.union L (pi_mod pif))); trivial.
  rewrite VsetP.union_spec in H2; destruct H2; trivial.
  apply H in H2; unfold Var.is_local in H2; rewrite W in H2; discriminate.
 Qed.

 Lemma Vset_of_var_decl_ind : forall (P:forall t, Var.var t -> Prop) lt 
  (lv:var_decl lt), 
  (forall t (x:Var.var t), DIn t x lv -> P t x) ->
  forall t (x:Var.var t), Vset.mem x (Vset_of_var_decl lv) -> P t x.
 Proof.
  unfold Vset_of_var_decl; induction lv; simpl; intros; trivialb.
  rewrite VsetP.add_spec in H0; destruct H0; auto.
  apply H; left; inversion H0; constructor.
 Qed. 
 
 Lemma params_local : forall E t (f:Proc.proc t) (pif:proc_eq_refl_info E f),
  forall x, Vset.mem x (pi_params pif) -> Var.is_local x.
 Proof.
  intros; destruct x as (tx, x).
  refine (@Vset_of_var_decl_ind 
   (fun t x => is_true (Var.is_local x)) _ (proc_params E f) _ tx x _).
  intros; rewrite <- Var.vis_local_local.
  unfold proc_params in H0.
  apply proc_params_local with (p:=f) (1:= H0).
  apply (Vset.subset_correct (params_subset pif)); trivial.
 Qed.

 Definition eq_refl_info E := 
  forall t (f:Proc.proc t), option (proc_eq_refl_info E f).


 (** Probability *)

 Lemma EqObs_Pr2 : forall I E1 c1 E2 c2 O,
  EqObs I E1 c1 E2 c2 O ->
  forall e, fv_expr e [<=] O ->
   forall k (m1 m2:Mem.t k), m1 =={I} m2 -> Pr E1 c1 m1 (EP k e) == Pr E2 c2 m2 (EP k e).
 Proof.
  unfold Pr; intros.
  apply EqObs_deno with I O; trivial.
  unfold charfun,restr, EP; intros.
  assert (W := req_mem_weaken H0 H2).
  rewrite (EqObs_e_fv_expr e W); trivial.
 Qed.

 Lemma EqObs_Pr : forall I E1 c1 E2 c2 e,
  EqObs I E1 c1 E2 c2 (fv_expr e) ->
  forall k m, Pr E1 c1 m (EP k e) == Pr E2 c2 m (EP k e).
 Proof.
  intros; eapply EqObs_Pr2; eauto with set.
 Qed.

End Make.
