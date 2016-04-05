Require Import SwitchingSem.

Set Implicit Arguments.

Notation bad := (Var.Gvar T.Bool 1).
Notation L := (Var.Gvar (T.List (T.Pair (T.User BS_k) (T.User BS_k))) 1).
Notation x := (Var.Lvar (T.User BS_k) 2).
Notation y := (Var.Lvar (T.User BS_k) 3).
Notation b := (Var.Lvar T.Bool 4).

Notation O := (Proc.mkP 1 ((T.User BS_k):: nil) (T.User BS_k)).

Definition O_params : var_decl (Proc.targs O) := dcons _ x (dnil _).

Definition O_re := y.

(** Random function *)
Definition Of :=
 [ 
  If !(x in_dom L) _then 
  [ 
   y <$- {0,1}^k; 
   L <- (x|y) |::| L
  ];
  y <- L[{x}]
 ].

(* Random permutation *)
Definition Op_gen c :=
 [ 
  If !(x in_dom L) _then 
  [ 
   y <$- {0,1}^k; 
   If y in_range L _then c;
   L <- (x|y) |::| L
  ];
  y <- L[{x}]
 ].

Definition c := [ while y in_range L do [ y <$- {0,1}^k ] ].

Definition Op := Op_gen c.


Section ADVERSARY.

 Variable env_adv : env.

 Notation A := (Proc.mkP 2 nil T.Bool).

 Definition A_params : var_decl (Proc.targs A) := dnil _.
 Variable A_body : cmd.
 Variable A_re : E.expr T.Bool.

 Definition mkEnv O_body := 
  let Ef := add_decl env_adv O O_params (refl_equal true) O_body O_re in
   add_decl Ef A A_params (refl_equal true) A_body A_re.
 
 (* Initial Game *)
 Definition G0 := [ L <- Nil _; b <c- A with {} ].

 Definition Ef := mkEnv Of.
 Definition Ep := mkEnv Op.

 Definition PrOrcl := PrSet.singleton (BProc.mkP O).
 Definition PrPriv := PrSet.empty.
 Definition Gadv := Vset.empty.
 Definition Gcomm := Vset.empty.

 Hypothesis A_wf : WFAdv PrOrcl PrPriv Gadv Gcomm Ef A.
 
 Hypothesis A_lossless : forall body,
  (forall p, PrSet.mem p PrOrcl -> 
   lossless (mkEnv body) (proc_body (mkEnv body) (BProc.p_name p))) -> 
  lossless (mkEnv body) A_body.

 Hypothesis A_range : forall k m, range (EP k (Elength L <=! q)) ([[G0]] Ef m).

 Lemma EqAD : forall O_body1 O_body2, 
  Eq_adv_decl PrOrcl PrPriv (mkEnv O_body1) (mkEnv O_body2).
 Proof.
  unfold Eq_adv_decl, mkEnv, proc_params, proc_body, proc_res; intros.
  generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
  case (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto;
  intros Heq; apply H; rewrite <- Heq; vm_compute; reflexivity.
 Qed.
 
 Lemma EqOP : forall O_body1 O_body2, 
  Eq_orcl_params PrOrcl (mkEnv O_body1) (mkEnv O_body2).
 Proof.
  unfold Eq_orcl_params, mkEnv, PrOrcl; intros.
  apply PrSet.singleton_complete in H; inversion H; trivial.
 Qed.

 (** The adversary is well-formed in any environment constructed with [mkEnv].
     This follows from the adversary being well-formed in [Ef] *)
 Lemma A_wf_E : forall O_body,
  WFAdv PrOrcl PrPriv Gadv Gcomm (mkEnv O_body) A.
 Proof.
  intros; apply WFAdv_trans with (5:=A_wf).
  apply EqOP.
  apply EqAD.
  vm_compute; intro; discriminate.
  vm_compute; intro; discriminate.
 Qed. 


 (* Helper functions to build [eq_inv_info] *)
 Definition i_refl Obody Obody' Or Or' :=
  let E := mkEnv Obody in
   let E' := mkEnv Obody' in
    let piF := add_refl_info_rm O Or Or' (empty_info E E') in
     add_adv_info_lossless (EqAD _ _ ) (A_wf_E _) (@A_lossless _) (@A_lossless _) piF.
 
 Definition iEiEi Obody := i_refl Obody Obody Vset.empty Vset.empty.

 Definition iEinv Obody Obody' inv 
  (ie:eq_inv_info inv (mkEnv Obody) (mkEnv Obody')) 
  R1 R2 I X  
  (Obody_Obody': EqObsInv inv I (mkEnv Obody) Obody (mkEnv Obody') Obody' X):=
  let E := mkEnv Obody in
   let E' := mkEnv Obody' in 
    let piO := add_info O R1 R2 ie Obody_Obody' in
     add_adv_info_lossless (EqAD _ _ ) (A_wf_E _) (@A_lossless _) (@A_lossless _) piO.
 
 (* Helper function to build [upto_bad info] *)
 Definition i_upto bad Obody Obody' :=
  let E := mkEnv Obody in
   let E' := mkEnv Obody' in
    let i0 := empty_upto_info bad E E' in
     let iH := add_upto_info i0 O in
      add_adv_upto_info iH (EqAD _ _ ) (EqOP _ _) (A_wf_E _).


 Definition Of_bad := Op_gen [bad <- true].
 Definition Ef_bad := mkEnv Of_bad.

 Definition Op_bad := Op_gen ((bad <- true)::c).
 Definition Ep_bad := mkEnv Op_bad.

 Definition iEfEf_bad : eq_inv_info trueR Ef Ef_bad := 
  i_refl Of Of_bad Vset.empty {{bad}}.

 Definition iEpEp_bad : eq_inv_info trueR Ep Ep_bad := 
  i_refl Op Op_bad Vset.empty {{bad}}.

 Lemma EqObs_f_fbad : 
  EqObs Gadv Ef G0 Ef_bad G0 {{b,L}}.
 Proof. 
  eqobs_in iEfEf_bad. 
 Qed.

 Lemma diff_bad : forall k (m:Mem.t k),
  Uabs_diff (Pr Ef G0 m (EP k b)) (Pr Ep G0 m (EP k b)) <=
  Pr Ef_bad G0 (m{!bad <-- false!}) (EP k bad).
 Proof.
  intros k m.
  assert (Pr Ef G0 m (EP k b) == Pr Ef_bad G0 (m{!bad <-- false!}) (EP k b)).
   apply EqObs_Pr2 with (1:=EqObs_f_fbad); trivial.
   vm_compute; trivial.
  rewrite H; clear H.
  assert (Pr Ep G0 m (EP k b) == Pr Ep_bad G0 (m{!bad <-- false!}) (EP k b)). 
   apply EqObs_Pr2 with Gadv (fv_expr b); auto with set.
   eqobs_in iEpEp_bad.
  rewrite H, Uabs_diff_sym; clear H.
  apply upto_bad_Uabs_diff with (i_upto bad Op_bad Of_bad); trivial.
  apply is_lossless_correct with (refl2_info iEfEf_bad); trivial.
 Qed.

 Section FAILURE_BOUND.

  Variable k : nat.

  Let h n := n/2^k.
  Let q := q_poly k.

  Definition f := failure_inv (Elength L) q (EP k bad) h.

  Definition fi : failure_info Ef_bad f.
  apply empty_fi with {{L, bad}}.
  intros m1 m2 H; unfold f, failure_inv, charfun, restr, EP, negP, negb.
  simpl E.eval_expr; unfold O.eval_op; simpl.
  rewrite (H _ L), (H _ bad); trivial.
  apply Vset.forallb_correct; [intros; rewrite H | ]; trivial.
  Defined.

  Lemma triple_O : triple Ef_bad (proc_body Ef_bad O) f f.
  Proof.
   change (proc_body Ef_bad O) with Of_bad; unfold Of_bad, Op_gen. 
   apply triple_oracle with (EP k (!(x in_dom L))).
   unfold EP; intros m Heq.
   rewrite deno_cons_elim, Mlet_simpl, deno_cond_elim.
   case (@E.eval_expr _ T.Bool (!(x in_dom L)) m).
  
   set (def:=T.default k (T.Pair (T.User BS_k) (T.User BS_k))).
   transitivity 
    (mu (sum_support (T.default _ (T.User BS_k)) (E.eval_support {0,1}^k m))
     (sigma_fun 
      (fun i v => charfun (T.i_eqb k (T.User BS_k) v) (snd (nth i (m L) def)))
      (length (m L)))).
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.      
   apply mu_monotonic; intro v; unfold sigma_fun.
   rewrite (sigma_finite_sum def (fun w => charfun (T.i_eqb _ _ v) (snd w))).
   rewrite deno_cons_elim, Mlet_simpl, deno_cond_elim.
   case_eq (@E.eval_expr _ T.Bool (y in_range L) (m{!y <-- v!})); intros.
   repeat rewrite deno_assign_elim.
   generalize H; clear H; unfold charfun, restr, fone.
   simpl; unfold O.eval_op; simpl; mem_upd_simpl.
   generalize (m L); induction 0; simpl; intros; try discriminate.
   destruct (UT.i_eqb v (snd a)); Usimpl; auto.
   rewrite deno_nil_elim, deno_assign_elim, deno_assign_elim.
   unfold charfun, restr, fone; simpl; unfold O.eval_op; simpl; mem_upd_simpl.
   change (m bad) with (E.eval_expr bad m); rewrite Heq; trivial.
   unfold h; rewrite mu_sigma_le, Nmult_sigma; apply sigma_le_compat.
   intros i Hi.
   set (li := snd (nth i (m L) def)); simpl in li; fold li.
   apply (@Pr_bs_support k (T.default _ (T.User BS_k)) li
    (fun e v => if T.i_eqb k (T.User BS_k) v e then 1 else 0)).
   intros x; rewrite <- (is_true_Ti_eqb k (T.User BS_k) x).
   destruct (T.i_eqb _ (T.User BS_k) x li); intros H; [ elim H | ]; trivial.
   rewrite Ti_eqb_refl; trivial.

   rewrite deno_nil_elim, deno_assign_elim. 
   unfold charfun, restr.
   rewrite (@depend_only_fv_expr _ _ _ _ m), Heq; trivial.
   apply req_mem_sym; apply req_mem_upd_disjoint; trivial.

   unfold EP; red; intros m Heq g Hg.
   rewrite deno_cons_elim, Mlet_simpl, deno_cond_elim. 
   unfold O.tres in Heq |- *; rewrite Heq, deno_nil_elim, deno_assign_elim.
   apply Hg.
   split; rewrite depend_only_fv_expr with (m2:=m); trivial; 
   apply req_mem_sym; apply req_mem_upd_disjoint; trivial.
   
   unfold EP; red; intros m Heq g Hg.
   rewrite deno_cons_elim, Mlet_simpl, deno_cond_elim, Heq.
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   rewrite <- (@sum_support_const _ (T.default k (T.User BS_k)) 0
    (E.eval_support {0,1}^k m)).
   apply mu_stable_eq; refine (ford_eq_intro _); intro v.
   rewrite deno_cons_elim, Mlet_simpl, deno_cond_elim.
   case (@E.eval_expr _ T.Bool (y in_range L) (m{!y <-- v!})).
   repeat rewrite deno_assign_elim; apply Hg.
   simpl; unfold O.eval_op; simpl.
   mem_upd_simpl; apply le_n.
   rewrite deno_nil_elim, deno_assign_elim, deno_assign_elim; apply Hg.
   simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   apply le_n.
   apply E.eval_support_nil.  
  Qed.

  Definition fi' : failure_info Ef_bad f.
   set (fi':=add_fi fi O triple_O).
   eapply add_fi_adv with (p:=A); eauto.
   apply A_wf_E.
  Defined.

  Lemma failure_bound : forall m:Mem.t k, 
   m bad = false ->
   Pr Ef_bad G0 m (EP k bad) <= ((q_poly k - 1) * q_poly k)/2^(1 + k).
  Proof.
   unfold Pr; intros m Hm.
   assert (range (fun x => EP k (Elength L <=! q) x) ([[G0]] Ef_bad m)).
    apply mu_range.
    transitivity (mu ([[G0]] Ef m) 
     (fun a => if EP k (Elength L <=! q) a then 1 else 0)).
    apply EqObs_deno with Gadv {{L}}; trivial.
    apply EqObs_sym; eqobs_in iEfEf_bad.
    unfold EP; intros; rewrite depend_only_fv_expr with (m2:=m2); trivial.
    assert (lossless Ef G0).
    apply is_lossless_correct with (refl1_info iEfEf_bad); vm_compute; trivial.
    rewrite <- (H k); apply range_mu; apply A_range.
   
   rewrite (Pr_range _ (EP k bad) H), andP_comm.
   unfold Pr, G0; rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
   eapply Ole_trans.
   apply failure_event_mult with (a:=1/2^k);
   [apply check_fail_correct with fi'; vm_compute; trivial | | ]; 
   simpl; unfold EP, O.eval_op; simpl; mem_upd_simpl.  
   trivial.
  Qed.

 End FAILURE_BOUND.
 
 Lemma switching : forall k m,
  Uabs_diff (Pr Ef G0 m (EP k b)) (Pr Ep G0 m (EP k b)) <=
  ((q_poly k - 1) * q_poly k)/2^(1 + k).
 Proof.
  intros; eapply Ole_trans; [apply diff_bad | apply failure_bound].
  rewrite Mem.get_upd_same; trivial.
 Qed.

End ADVERSARY.
