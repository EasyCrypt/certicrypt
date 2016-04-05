(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

Require Import SwitchingSem.

Set Implicit Arguments.

Notation bad := (Var.Gvar T.Bool 1).
Notation L := (Var.Gvar (T.List (T.Pair (T.User BS_k) (T.User BS_k))) 2).
Notation R := (Var.Gvar (T.List (T.User BS_k)) 3).
Notation R' := (Var.Gvar (T.List (T.User BS_k)) 4).
Notation x := (Var.Lvar (T.User BS_k) 5).
Notation y := (Var.Lvar (T.User BS_k) 6).
Notation b := (Var.Lvar T.Bool 7).
Notation yR := (Var.Gvar (T.User BS_k) 8).
Notation used := (Var.Gvar T.Bool 9).
Notation N := (Var.Lvar T.Nat 10).

Notation F := (Proc.mkP 1 ((T.User BS_k):: nil) (T.User BS_k)).

Definition F_params : var_decl (Proc.targs F) := dcons _ x (dnil _).

Definition F_res := y.

(* Random function *)
Definition Ff :=
 [ 
  If !(x in_dom L) _then 
  [ 
   y <$- {0,1}^k; 
   L <- (x|y) |::| L
  ];
  y <- L[{x}]
 ].

(* Random permutation *)
Definition Fp_gen C :=
 [ 
  If !(x in_dom L) _then 
  [ 
   y <$- {0,1}^k; 
   If y in_range L _then C;
   L <- (x|y) |::| L
  ];
  y <- L[{x}]
 ].

Definition c := [ while y in_range L do [ y <$- {0,1}^k ] ].

Definition Fp := Fp_gen c.


Section ADVERSARY.

 Variable env_adv : env.

 Notation A  := (Proc.mkP 2 nil T.Bool).

 Definition A_params : var_decl (Proc.targs A) := dnil _.
 Variable A_body : cmd.
 Variable A_res : E.expr T.Bool.

 Definition mkEnv F_body := 
  let Ef := add_decl env_adv F F_params (refl_equal true) F_body F_res in
   add_decl Ef A A_params (refl_equal true) A_body A_res.
 
 (* Initial Game *)
 Definition G0 :=
  [ 
   L <- Nil _;
   b <c- A with {}
  ].

 Definition Ef := mkEnv Ff.
 Definition Ep := mkEnv Fp.

 Definition PrOrcl := PrSet.singleton (BProc.mkP F).
 Definition PrPriv := PrSet.empty.

 Definition Gadv := Vset.empty.
 Definition Gcomm := Vset.empty.

 Hypothesis A_wf : WFAdv PrOrcl PrPriv Gadv Gcomm Ef A.
 
 Hypothesis A_lossless : forall Fbody,
  (forall O, PrSet.mem O PrOrcl -> 
   lossless (mkEnv Fbody) (proc_body (mkEnv Fbody) (BProc.p_name O))) -> 
  lossless (mkEnv Fbody) A_body.

 Hypothesis A_range :forall k m, 
  range (EP k (Elength L <=! q)) ([[G0]] Ef m).

 Lemma EqAD : forall F_body1 F_body2, 
  Eq_adv_decl PrOrcl PrPriv (mkEnv F_body1) (mkEnv F_body2).
 Proof.
  unfold Eq_adv_decl, mkEnv; intros.
  unfold proc_params, proc_body, proc_res.
  generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto;
   intros Heq; 
    (apply H; rewrite <- Heq; vm_compute; reflexivity)
    || (apply H0; rewrite <- Heq; vm_compute; reflexivity).
 Qed.
 
 Lemma EqOP : forall F_body1 F_body2, 
  Eq_orcl_params PrOrcl (mkEnv F_body1) (mkEnv F_body2).
 Proof.
  unfold Eq_orcl_params, mkEnv; intros.
  unfold PrOrcl in H.
  apply PrSet.singleton_complete in H; inversion H; simpl.
  vm_compute; trivial.
 Qed.

 (** The adversary is well-formed in any environment constructed with [mkEnv].
     This follows from the adversary being well-formed in [E0] *)
 Lemma A_wf_E : forall F_body,
  WFAdv PrOrcl PrPriv Gadv Gcomm (mkEnv F_body) A.
 Proof.
  intros; apply WFAdv_trans with (5:=A_wf).
  unfold Ef; apply EqOP.
  unfold Ef; apply EqAD.
  vm_compute; intro; discriminate.
  vm_compute; intro; discriminate.
 Qed.


 (* Functions to build [eq_inv_info] *)
 Definition i_refl Fbody Fbody' Fr Fr' :=
  let E := mkEnv Fbody in
   let E' := mkEnv Fbody' in
    let piF := add_refl_info_rm F Fr Fr' (empty_info E E') in
     add_adv_info_lossless (EqAD _ _ ) (A_wf_E _) (@A_lossless _) (@A_lossless _) piF.

 Definition iEiEi Fbody := i_refl Fbody Fbody Vset.empty Vset.empty.

 Definition iEinv Fbody Fbody' inv 
  (ie:eq_inv_info inv (mkEnv Fbody) (mkEnv Fbody')) 
  R1 R2 I O
  (Fbody_Fbody': EqObsInv inv I (mkEnv Fbody) Fbody (mkEnv Fbody') Fbody' O):=
  let E := mkEnv Fbody in
   let E' := mkEnv Fbody' in 
    let piF := add_info F R1 R2 ie Fbody_Fbody' in
     add_adv_info_lossless (EqAD _ _ ) (A_wf_E _) (@A_lossless _) (@A_lossless _) piF.

 (* Function to build [upto_bad_info] *)
 Definition i_upto bad Fbody Fbody' :=
  let E := mkEnv Fbody in
   let E' := mkEnv Fbody' in
    let i0 := empty_upto_info bad E E' in
     let iH := add_upto_info i0 F in
      add_adv_upto_info iH (EqAD _ _ ) (EqOP _ _) (A_wf_E _).


 Definition Ff_bad := Fp_gen [bad <- true].
 
 Definition Ef_bad := mkEnv Ff_bad.

 Definition iEfEf_bad : eq_inv_info trueR Ef Ef_bad := 
  i_refl Ff Ff_bad Vset.empty (Vset.singleton bad).

 Definition Fp_bad := Fp_gen ((bad <- true)::c).

 Definition Ep_bad := mkEnv Fp_bad.

 Definition iEpEp_bad : eq_inv_info trueR Ep Ep_bad := 
  i_refl Fp Fp_bad Vset.empty (Vset.singleton bad).

 Lemma EqObs_f_fbad : 
  EqObs Gadv Ef G0 Ef_bad G0 (Vset.add b (Vset.singleton L)).
 Proof. 
  eqobs_in iEfEf_bad. 
 Qed.

 Lemma diff_bad : forall k (m:Mem.t k),
  Uabs_diff (Pr Ef G0 m (EP k b)) (Pr Ep G0 m (EP k b)) <=
  Pr Ef_bad G0 (m{!bad<--false!}) (EP k bad).
 Proof.
  intros k m; assert (Pr Ef G0 m (EP k b) == Pr Ef_bad G0 (m{!bad <-- false!}) (EP k b)).
  apply EqObs_Pr2 with (1:= EqObs_f_fbad);trivial.
  vm_compute;trivial.
  rewrite H; clear H.
  assert (Pr Ep G0 m (EP k b) == Pr Ep_bad G0 (m{!bad <-- false!}) (EP k b)). 
  apply EqObs_Pr2 with Gadv (fv_expr b);auto with set.
  eqobs_in iEpEp_bad.
  rewrite H, Uabs_diff_sym; clear H.
  apply upto_bad_Uabs_diff with (i_upto bad Fp_bad Ff_bad);trivial.
  apply is_lossless_correct with (refl2_info iEfEf_bad);trivial.
 Qed.

 (** Boolean version of [NoDup] *)
 Fixpoint noDup (A:Type) (eqb:A -> A -> bool) (l:list A) :=
  match l with
   | nil => true
   | a::l => andb (negb (existsb (eqb a) l)) (noDup eqb l)
  end.

 Lemma noDup_spec : forall A (eqb:A->A->bool)
  (eqb_spec : forall x y, if eqb x y then x = y else x <> y),
  forall l, noDup eqb l <-> NoDup l.
 Proof.
  induction l; simpl; split; intros; trivial.
  constructor.
  rewrite is_true_andb, is_true_negb, is_true_existsb in H; destruct H.
  intro; apply H; exists a; split; trivial.
  generalize (eqb_spec a a); destruct (eqb a a); trivial; intros H2; elim H2; trivial.
  rewrite <- IHl; trivial.
  rewrite is_true_andb in H; tauto.
  inversion_clear H.
  rewrite <- IHl in H1; rewrite  H1, andb_true_r, is_true_negb; intro; apply H0.
  rewrite is_true_existsb in H; destruct H as (x, (H2, H3)).
  assert (W:=eqb_spec a x); rewrite H3 in W; rewrite W; trivial.
 Qed.

 Definition inv_dup := 
  EP1 bad |-> (fun k m1 m2 => negb (noDup (T.i_eqb k (T.User BS_k)) (map (@snd _ _) (m2 L)))).
 
 Lemma inv_dup_dep : 
  depend_only_rel inv_dup 
  (Vset.union (fv_expr bad) Vset.empty)
  (Vset.union Vset.empty (Vset.singleton L)).
 Proof.
  apply depend_only_impR; auto.
  red; intros.
  rewrite <- (H0 _ L); trivial.
 Qed.

 Lemma inv_dup_dec : decMR inv_dup.
 Proof.
  apply decMR_imp; auto.
  red; intros.
  destruct (noDup (T.i_eqb k (T.User BS_k))
   (map (@snd _ _) (y L))); auto.
  right; discriminate.
 Qed.
 
 Definition eEfbadEf : eq_inv_info inv_dup Ef_bad Ef.
  refine (@empty_inv_info inv_dup _ _ inv_dup_dep _ inv_dup_dec Ef_bad Ef).
  vm_compute; trivial.
 Defined.

 Lemma existsb_snd :  forall k v l,
  existsb (UT.i_eqb v) (map (@snd _ _) l) =
  existsb (fun p : UT.interp k BS_k * UT.interp k BS_k => UT.i_eqb v (snd p)) l.
 Proof.
  induction l; simpl; trivial.
  rewrite IHl; trivial.
 Qed. 

 Lemma Ff_bad_Ff_dup : 
  EqObsInv inv_dup (Vset.add x (Vset.singleton L)) 
  Ef_bad Ff_bad Ef Ff 
  (Vset.add y (Vset.singleton L)).
 Proof.
  eqobs_tl eEfbadEf.
  cp_test (x in_dom L); rewrite proj1_MR.
  eqobs_in eEfbadEf.
  eqobs_hd eEfbadEf.
  cp_test (y in_range L);
  unfold inv_dup; eqobsrel_tail;
   unfold implMR, andR, impR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl; intros;
    rewrite Mem.get_upd_same; simpl.
  rewrite existsb_snd.
  destruct H as (H2, (H3, (H4, H5))); rewrite H5; simpl; trivial.
  destruct H as (H2, (H3, (H4, H5))).
  rewrite <- is_true_negb in H5; rewrite existsb_snd, H5; simpl; auto.
 Qed.

 Definition iEfbadEf : eq_inv_info inv_dup Ef_bad Ef :=
  iEinv eEfbadEf Vset.empty Vset.empty Ff_bad_Ff_dup.

 Lemma bad_dup: forall k m,
  Pr Ef_bad G0 (m{!bad <-- false!}) (EP k bad) <=
  Pr Ef G0 m (fun m => negb (noDup (T.i_eqb k (T.User BS_k)) (map (@snd _ _) (m L)))).
 Proof.
  unfold Pr; intros.
  apply equiv_deno_le with (P:=EP1 (!bad)) (Q:=req_mem_rel Vset.empty inv_dup).
  eqobs_tl iEfbadEf.
  unfold inv_dup; eqobsrel_tail.
  unfold implMR, trueR, req_mem_rel, andR, impR; simpl; unfold O.eval_op; simpl; intros; split; intros.
  apply req_mem_empty.
  rewrite Mem.get_upd_same.
  unfold EP1 in H; simpl in H;  trivialb.
  unfold req_mem_rel, inv_dup, impR, andR, EP1, charfun,restr, EP; intros m1 m2 (H1, H2).
  case_eq (E.eval_expr bad m1); intros; trivial.
  rewrite H2; trivial.
  red; simpl; rewrite Mem.get_upd_same; trivial.
 Qed.


 (** Eagerly sampling the responses of the oracle *)

 Definition Fr :=
 [ 
  If !(x in_dom L) _then 
  [ 
   If 0 <! Elength R 
   then [ y <- Ehd R; R <- Etl R ]
   else [ y <$- {0,1}^k ];
   L <- (x|y) |::| L
  ];
  y <- L[{x}]
 ].

 Definition Er := mkEnv Fr.

 Definition GR :=
  [
   R <- Nil _;
   while (Elength R <! q) do [ y <$- {0,1}^k; R <- y |::| R ];
   L <- Nil _;
   b <c- A with {}
  ].
 

 (**  One step of lazy sampling *)

 Definition FrR :=
  [ 
   If !(x in_dom L) _then 
   [ 
    If 0 <! Elength R 
    then [ y <- Ehd R; R <- Etl R ]
    else [ If !used then [ used <- true; y <- yR ] else [ y <$- {0,1}^k ] ];
    L <- (x|y)|::|L
   ];
   y <- L[{x}]
  ].

 Definition Fr'  := [ If !used then (yR <$- {0,1}^k) :: FrR else Fr ].
 
 Definition FrR' := [ If !used then FrR else Fr ].
 
 Lemma Fr_Fr' : forall E E', 
  EqObsInv trueR (Vset.add x (Vset.add R (Vset.singleton L)))
  E Fr E' Fr' 
  (Vset.add y (Vset.add R (Vset.singleton L))).
 Proof.
  unfold Fr', FrR, Fr; intros.
  cp_test_r used.
  eqobs_in.
  cp_test (x in_dom L).
  deadcode; eqobs_in.
  eqobs_tl.
  cp_test (0 <! Elength R).
  deadcode; eqobs_in.
  alloc_r yR y; ep; deadcode; eqobs_in.
 Qed.

 Lemma FrR'_FrR : forall E' E, 
  EqObsInv trueR (Vset.add used (Vset.add yR (Vset.add x (Vset.add R (Vset.singleton L)))))
  E' FrR' E FrR 
  (Vset.add used (Vset.add y (Vset.add R (Vset.singleton L)))).
 Proof.
  unfold FrR', FrR, Fr; intros.
  cp_test used; eqobs_in.
 Qed.

 Definition Er' := mkEnv Fr'.
 Definition ErR' := mkEnv FrR'.
 Definition ErR := mkEnv FrR.

 Definition iErEr : eq_inv_info trueR Er Er := 
  i_refl Fr Fr Vset.empty Vset.empty.

 Definition iErEr' : eq_inv_info trueR Er Er' := 
  iEinv (empty_info Er Er') Vset.empty Vset.empty (Fr_Fr' Er Er').

 Definition iErR'ErR : eq_inv_info trueR ErR' ErR := 
  iEinv (empty_info ErR' ErR) Vset.empty Vset.empty (FrR'_FrR ErR' ErR).

 Definition Ci :=
  let C1 := (If !used then (yR <$- {0,1}^k) :: FrR else Fr) in
   let C2 := (If !used then FrR else Fr) in
    let nR := Vset.singleton yR in
     let nW:= (Vset.add yR (Vset.union (fv_expr (!used)) (fv_distr {0,1}^k))) in
      let i0 := empty_context_info Er' ErR' C1 C2 nR nW in
       let iF := add_context_info Er' ErR' C1 C2 nR nW i0 _ F in
        add_adv_context_info Er' ErR' C1 C2 nR nW iF 
        PrOrcl PrPriv Gadv Gcomm (EqAD _ _) _ A (A_wf_E _).

 Lemma fix_r_R : 
  EqObs (Vset.add L (Vset.singleton R))
  Er  [ b <c- A with {} ]
  ErR [ used <- false; yR <$- {0,1}^k; b <c- A with {} ]
  (Vset.add L (Vset.singleton R)).
 Proof.
  apply EqObs_trans with Er [used<-false; b <c- A with {}].
  deadcode iErEr; eqobs_in iErEr.
  apply EqObs_trans with Er' ([used<-false; b <c- A with {}] ++ [If !used _then [yR <$- {0,1}^k] ]).
  eqobs_hd_n 1%nat; deadcode iErEr'; eqobs_in iErEr'.
  unfold EqObs; apply equiv_cons with 
   (req_mem_rel (Vset.add used (Vset.add L (Vset.singleton R)))
    (EP1 (!used))).
  eqobsrel_tail; unfold implMR; simpl; unfold O.eval_op; simpl; trivial.
  match goal with |- equiv _ _ [?i1;?i2] _ ?c _ =>
   apply equiv_trans_eq_mem_l with (P1 := EP1 (!used))
    (E1' := ErR') (c1' := c); [change [i1; i2] with ([i1]++[i2]) | | ] end .
  apply (@equiv_context_true Er' ErR' FrR Fr _ yR ({0,1}^k) (!used)).
  vm_compute; trivial.
  apply dcontext_correct with (ci := Ci).
  vm_compute; trivial.
  
  (* Fr preserves the negation of the test *)
  unfold Fr; union_mod.
  apply proj1_MR.
  eqobsrel_tail.
  unfold implMR,andR,notR,EP1; simpl; unfold O.eval_op; simpl.
  unfold Meq; intros k m1 m2 (Heq, H1); subst.
  split; intros; trivial.
  split; intros; trivial.

  (* FrR uses only once yR *)
  unfold FrR; union_mod.
  (* TODO : Change union such that this goal disapears *)
  apply proj1_MR.
  ep_eq_l (!used) true.
  intros k m1 m2 (Heq, H1); exact H1.
  ep_eq_r (!used) true.
  intros k m1 m2 (Heq, H1); unfold Meq in Heq; rewrite <- Heq; exact H1.
  cp_test (0 <! Elength R).
  ep_eq_l (!used) true.
  intros k m1 m2 ((Heq, H1), _); exact H1.
  deadcode; swap; eqobs_in.
  cp_test (x in_dom L).
  ep_eq_l (!used) true.
  intros k m1 m2 (((Heq, H1), _),_); exact H1.
  deadcode; swap; eqobs_in.
  eqobs_in.

  eqobs_in iErR'ErR.
  red; intros k m1 m2 (H1, H2); trivial.
 Qed.

 (** Now we go back to the initial oracle where the list [R] has been extended with [yR] *) 

 Definition inv_R_r :mem_rel :=
  (EP2 (0 <! Elength R) |-> 
   (fun k m1 m2 => E.eval_expr (R |++| (yR |::| Nil _)) m1 = E.eval_expr R m2) /-\ EP1 (!used)) /-\
  (EP2 (!(0 <! Elength R)) |-> EP1 used /-\ EP1 (!(0 <! Elength R))).

 Lemma inv_R_r_dep :
  depend_only_rel inv_R_r 
  (Vset.add used (fv_expr (R |++| (yR |::| Nil _))))
  (Vset.singleton R).
 Proof.
  unfold inv_R_r; eapply depend_only_rel_weaken.
  Focus 3.
  apply depend_only_andR.   
  apply depend_only_impR; [auto | ]. 
  apply depend_only_andR; [ | auto].
  apply depend_only_rel_weaken with (fv_expr (R |++| (yR |::| Nil _))) (Vset.singleton R);
   auto with set. 
  red; intros.
  eapply trans_eq; [ | eapply trans_eq;[ apply H1| ] ].
  symmetry; apply depend_only_fv_expr; exact H.
  apply depend_only_fv_expr; exact H0.
  apply depend_only_impR; auto.
  vm_compute; trivial.
  vm_compute; trivial.
 Qed.

 Lemma inv_R_r_dec : decMR inv_R_r.
 Proof.
  apply decMR_and; apply decMR_imp; auto.
  apply decMR_and; auto.
  red; intros k m1 m2.
  match goal with |- sumbool (?x = ?y) _ => 
   assert (W:=T.i_eqb_spec k (T.List (T.User BS_k)) x y); 
   destruct (T.i_eqb k (T.List (T.User BS_k)) x y); auto 
  end.
 Qed.

 Definition eErREr : eq_inv_info inv_R_r ErR Er.
  refine (@empty_inv_info inv_R_r _ _ inv_R_r_dep _ inv_R_r_dec ErR Er).
  vm_compute; trivial.
 Defined.

 Lemma F_extend_R_r :
  EqObsInv inv_R_r (Vset.add x (Vset.singleton L))
  ErR FrR Er Fr
  (Vset.add y (Vset.singleton L)).
 Proof.
  unfold FrR, Fr.
  cp_test (x in_dom L); rewrite proj1_MR.
  eqobs_in eErREr.
  cp_test_r (0 <! Elength R).
  cp_test_l (0 <! Elength R).
  eqobs_tl eErREr. 
  repeat rewrite req_mem_rel_assoc. 
  union_mod_tac eErREr.
  unfold EqObsRel; 
   match goal with
    |- equiv (req_mem_rel ?I ?P) _ _ _ _ _ =>
     apply equiv_cons with (req_mem_rel (Vset.add y I) P) 
   end.
  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold upd_para; intros k m1 m2 (H1, ((H2, H3),H4)); split; unfold kreq_mem in *.
  match goal with |- req_mem _ (Mem.upd _ _ ?v1) (Mem.upd _ _ ?v2) => 
   replace v1 with v2
  end.
  apply req_mem_update; trivial.
  destruct H2 as (H2, H5); destruct (H2 H3).
  Opaque leb T.i_eqb.
  generalize H H4; unfold EP1; simpl; unfold O.eval_op; simpl; intros Heq Hle.
  rewrite <- Heq; destruct (m1 R); trivial.
  Transparent leb.
  discriminate Hle.
  assert_depend_only eErREr 
  ((inv_R_r /-\ EP2 (0 <! Elength (R))) /-\ EP1 (0 <! Elength (R))).
  apply Hdep with m1 m2.
  apply req_mem_upd_disjoint; vm_compute; trivial.
  apply req_mem_upd_disjoint; vm_compute; trivial.
  unfold andR; tauto.
  eapply equiv_strengthen;[ | apply equiv_assign].
  unfold upd_para; intros k m1 m2 (H1, ((H2, H3),H4)); split; unfold kreq_mem in *.
  apply req_mem_trans with m1.
  apply req_mem_sym.
  apply req_mem_upd_disjoint; vm_compute; trivial.
  apply req_mem_trans with m2.
  apply req_mem_weaken with (2:= H1); vm_compute; trivial.
  apply req_mem_upd_disjoint; vm_compute; trivial.
  generalize H2 H3 H4; clear H2 H3 H4; unfold inv_R_r, impR, andR, EP1, EP2;
   simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  mem_upd_simpl.
  intros (H2, H3); split; intros.
  destruct (H2 H0).
  rewrite <- H5; split; auto.
  destruct (m1 R); trivial.
  discriminate H4. 
  
  rewrite is_true_negb in H |- *.
  elim H; destruct (H2 H0).
  rewrite <- H5.
  destruct (m1 R); trivial.
  simpl; rewrite app_length, plus_comm; trivial.
  ep_eq_l (!used) true.
  intros k m1 m2 (((_,(H1,_)), H2),_).
  destruct (H1 H2) as (_, H0); exact H0.
  eqobs_tl eErREr. 
  match goal with
   |- equiv (((req_mem_rel ?X _) /-\ ?P2) /-\ ?P3) _ (?i::?c) _ ?c' _ => 
    change (i::c) with ([i]++c); change c' with (nil ++ c') end.
  apply equiv_app with (req_mem_rel (Vset.add x (Vset.singleton L))
   ((fun k m1 m2 => m2 R = m1 yR :: nil) 
    /-\ (EP2 (0 <! Elength R) /-\ ~- EP1 (0 <! Elength R))
    /-\ EP1 used)).
  eapply equiv_strengthen;[ | apply equiv_assign_l].
  unfold upd1; intros k m1 m2 (((H1, (H4, H5)), H2), H3).
  split.
  unfold kreq_mem in *.
  apply req_mem_trans with m1; trivial.
  apply req_mem_sym; apply req_mem_upd_disjoint; vm_compute; trivial.
  split.
  rewrite Mem.get_upd_diff;[ | intro; discriminate].
  destruct (H4 H2).
  generalize H3 H; unfold EP1, notR; simpl; unfold O.eval_op; simpl; intros W1 W; rewrite <- W.
  destruct (m1 R); trivial.
  elim W1; trivial.
  split.
  assert_depend_only eErREr (EP2 (0 <! Elength (R)) /-\ ~- EP1 (0 <! Elength (R))).
  apply Hdep with m1 m2; trivial.
  apply req_mem_upd_disjoint; vm_compute; trivial.
  split; trivial.
  unfold EP1; simpl; rewrite Mem.get_upd_same; trivial.
  match goal with
   |- equiv (req_mem_rel ?X ?P) _ _ _ _ _ =>
    apply equiv_cons with (req_mem_rel (Vset.add y X) 
     ((fun k m1 m2 => m1 yR = m2 y) /-\ P)) end.
  eapply equiv_strengthen;[ | apply equiv_assign].
  unfold upd_para; intros k m1 m2 (H1, (H2, H3)); split; unfold kreq_mem in *.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite H2; apply req_mem_update; trivial.
  generalize H3; unfold notR,andR, EP1, EP2; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  rewrite H2; simpl.
  auto.
  match goal with
   |- equiv _ _ ?c _ (?i::?c') _ =>
    change c with (nil ++ c); change (i::c') with ([i]++c') end.
  apply equiv_app with
   (req_mem_rel (Vset.add y (Vset.add x (Vset.singleton L)))
    ((fun (k : nat) (m1 m2 : Mem.t k) =>
     m1 yR = m2 y) /-\
    (~-EP2 (0 <! Elength (R)) /-\ ~- EP1 (0 <! Elength (R))) /-\
    EP1 used)).
  eapply equiv_strengthen;[ | apply equiv_assign_r].
  unfold req_mem_rel,upd2,andR,EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 (H1, (H2, (H3, (H4, H5)))); split.
  unfold kreq_mem in *.
  apply req_mem_trans with m2; trivial.
  apply req_mem_upd_disjoint; vm_compute; trivial.
  mem_upd_simpl.
  rewrite H3; simpl.
  destruct H4; repeat split; trivial; discriminate.
  match goal with
   |- equiv ?P _ _ _ _ _ => apply equiv_cons with P end.
  eapply equiv_strengthen;[ | apply equiv_assign].
  unfold upd_para, req_mem_rel, kreq_mem, andR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 (H1, H2).
  mem_upd_simpl.
  split; trivial.
  destruct H2 as (H2, _).
  rewrite H2, (H1 _ L); trivial; rewrite (H1 _ x); trivial.
  match goal with |- ?m1 =={?S} ?m2 => 
   apply req_mem_weaken with (Vset.add L S) end. 
  vm_compute; trivial.
  apply req_mem_update; trivial.
  eqobsrel_tail.
  unfold implMR, inv_R_r, req_mem_rel,upd_para,andR, impR,EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 (H1, (H2, ((H3, H4), H5))).
  split; intros. 
  elim H3; trivial.  
  rewrite is_true_negb; auto.
  
  ep_eq_l (0 <! Elength R) false.
  unfold req_mem_rel,inv_R_r, notR, andR, impR, EP1, EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 ((H1, (_, H2)), H3).
  rewrite <- is_true_negb_false.
  apply H2; rewrite is_true_negb; trivial.
  
  ep_eq_l (used) true.
  intros k m1 m2 ((H1, (H2, H4)), H3).
  destruct H4.
  generalize H3; unfold notR, EP2; simpl; unfold O.eval_op; simpl.
  intros; rewrite is_true_negb; trivial.
  exact H.
  rewrite proj1_MR.
  eqobs_in eErREr.
 Qed.

 Definition iRr : eq_inv_info inv_R_r ErR Er :=
  iEinv eErREr Vset.empty Vset.empty F_extend_R_r.

 Lemma Er_fix_1 :
  EqObs (Vset.add L (Vset.singleton R))
  Er [ b <c- A with {}]
  Er [ yR <$- {0,1}^k; R <- R |++| (yR |::| Nil _); b <c- A with {}]
  (Vset.singleton L).
 Proof.
  apply EqObs_trans with ErR [used <- false; yR <$- {0,1}^k; b <c- A with{}].
  apply equiv_weaken with (2:= fix_r_R).
  unfold kreq_mem; intros k; apply req_mem_weaken; vm_compute; trivial.
  unfold EqObs.
  match goal with
   |- equiv (kreq_mem ?II) _ [?i1;?i2;?i3] _ [?i4;?i5;?i6] (kreq_mem ?OO) =>
    change [i1; i2; i3] with  ([i1; i2]++[i3]);
     change [i4; i5; i6] with ([i4; i5]++[i6]) end.
  apply equiv_app with (req_mem_rel (Vset.singleton L) inv_R_r).
  eqobsrel_tail.
  unfold implMR, inv_R_r, EP1, EP2, andR, impR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 Hreq v;
  mem_upd_simpl.
  rewrite app_length, plus_comm; simpl; split; intros;[ | discriminate].
  split;[ rewrite (Hreq _ R)| ]; trivial.
  eqobs_in iRr.
 Qed.

 (* Proof by induction *)

 Definition GR_n := 
  [
   L <- Nil _;
   R <- Nil _;
   while (Elength R <! N) do [ y <$- {0,1}^k; R <- y |::| R ];
   b <c- A with {}
  ].

 Definition inv0 : mem_rel := EP2 (R =?= Nil _).

 Lemma inv0_dep :
  depend_only_rel inv0 Vset.empty (fv_expr (R =?= Nil _)).
 Proof.
  unfold inv0; auto.
 Qed.

 Lemma inv0_dec : decMR inv0.
 Proof.
  unfold inv0; auto.
 Qed.
 
 Definition eEfEr_0 : eq_inv_info inv0 Ef Er.
  refine (@empty_inv_info inv0 _ _ inv0_dep _ inv0_dec Ef Er).
  vm_compute; trivial.
 Defined.

 Lemma Ff_Fr0 : 
  EqObsInv inv0 (Vset.add L (Vset.singleton x))
  Ef Ff Er Fr 
  (Vset.add L (Vset.singleton y)).
 Proof.
  unfold Ff, Fr.
  ep_eq_r (0 <! Elength (R)) false.
  intros k m1 m2 (H1, H2); generalize H2; clear H2.
  unfold inv0,EP2; simpl; unfold O.eval_op; simpl.
  rewrite is_true_Ti_eqb; intros Heq; rewrite Heq; trivial.
  eqobs_in eEfEr_0.
 Qed.

 Definition ibad0 : eq_inv_info inv0 Ef Er :=
  iEinv  eEfEr_0 Vset.empty Vset.empty Ff_Fr0.

 Lemma equiv_ind : forall n:nat,
  EqObsRel Vset.empty (fun k m1 m2 => E.eval_expr N m2 = n)
  Ef G0 Er GR_n
  (Vset.singleton L) trueR.
 Proof.
  induction n.
  (* Case 0 *)
  unfold G0, GR_n.
  eqobs_tl ibad0.
  unfold EqObsRel.
  match goal with
   |- equiv (req_mem_rel _ ?P) _ ?n ?E [?i1;?i2;?i3] _ =>
    change n with (n++ nil);
     change [i1; i2; i3] with ([i1; i2]++[i3]);
      apply equiv_app with (req_mem_rel (Vset.singleton L) (P /-\ inv0)) end.
  unfold inv0; eqobsrel_tail.
  unfold implMR,andR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 (H1, H2); mem_upd_simpl.
  rewrite Ti_eqb_refl; auto.
  (* This does not work ... :
     ep_eq_r (Elength (R) <! N) false *)
  apply equiv_trans_eq_mem_r with (E2':=Er) (c2':=nil) (P2 := fun (k : nat) (m1 m2 : Mem.t k) => E.eval_expr N m1 = 0%nat).
  apply equiv_eq_sem_pre; intros.
  rewrite deno_while, deno_cond.
  match goal with |- (if ?X then _ else _) == _ => replace X with false;[trivial| ] end.
  generalize H; clear H; simpl; unfold O.eval_op; simpl; intros H; rewrite H, plus_comm; simpl; trivial.
  apply equiv_nil_impl; rewrite proj2_MR; trivial.
  red; intros k m1 m2 (H,(H1, H2)); trivial.

  (* Case S *)

  unfold G0, GR_n in *.
  unfold EqObsRel.
  apply equiv_trans_r with
   (P2 := req_mem_rel (Vset.singleton N)
    (fun k (m1 m2:Mem.t k) => E.eval_expr N m2 = S n))
   (Q1 := kreq_mem (Vset.singleton L))
   (Q2 := kreq_mem (Vset.singleton L))
   (E2 := Er)
   (c2 := [N <- N -! 1%nat] ++
    [
     L <- Nil _;
     R <- Nil _;
     while Elength R <! N do [y <$- {0,1}^k; R <- y |::| R];
     b <c- A with {}
    ]).
  apply decMR_req_mem_rel.
  red; intros.
  generalize (T.i_eqb_spec k T.Nat (y N) (S n)).
  destruct (T.i_eqb k T.Nat (y N) (S n)); simpl; auto.
  red; unfold transpR, req_mem_rel, andR; intros k m1 m2 (H1, H2); split; trivial.
  intros; split;[ | red; trivial].
  apply req_mem_trans with y; trivial.
  match goal with |- equiv _ _ ?c1 _ _ _ => change c1 with (nil ++ c1) end.
  eapply equiv_weaken;[ | apply equiv_app with (2:= IHn)].
  intros k m1 m2 (H1,_); trivial.
  eqobsrel_tail; unfold implMR,andR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 (_, H); rewrite Mem.get_upd_same, H; simpl.
  symmetry; apply minus_n_O.
  clear IHn; apply equiv_trans_r with
   (P2 := req_mem_rel (Vset.singleton N) (EP2 (0 <! N)))
   (Q1 := kreq_mem (Vset.singleton L))
   (Q2 := kreq_mem (Vset.singleton L))
   (E2 := Er)
   (c2 :=
    [N <- N -! 1%nat; L <- Nil _;
     R <- Nil _; while Elength (R) <! N do [y <$- {0,1}^k; R <- y |::| R] ] ++
    [yR <$- {0,1}^k; R <- R |++| (yR |::| Nil _); b <c- A with {} ] ).
  apply decMR_req_mem_rel.
  red; intros.
  generalize (T.i_eqb_spec k T.Nat (y N) (S n)).
  destruct (T.i_eqb k T.Nat (y N) (S n)); simpl; auto.
  red; unfold transpR, req_mem_rel, andR, EP2; intros k m1 m2 (H1, H2); split; trivial.
  generalize H2; simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq; trivial.
  intros; apply req_mem_trans with y; trivial.
  match goal with
   |- equiv _ _ ([?i1] ++ [?i2;?i3;?i4;?i5]) _ _ _ => 
    change ([i1] ++ [i2; i3; i4; i5]) with ([i1; i2; i3; i4]++[i5]) end.
  apply equiv_app with (2:= Er_fix_1).
  eqobs_in.
  
  eqobs_tl iErEr.
  match goal with
   |- equiv _ _ (?iN::?iL::?iR::?c1) _ (?iL::?iR::?c2) _ => 
    change (iN::iL::iR::c1) with ([iN; iL; iR]++c1);
     change (iL::iR::c2) with ([iL; iR]++c2) end.
  apply equiv_app with (req_mem_rel (Vset.add R (Vset.singleton L))
   ((fun k m1 m2 => E.eval_expr N m1 = (E.eval_expr N m2 - 1)%nat) 
    /-\ EP2 (0 <! N) /-\ EP1 (R =?= Nil _))).
  eqobsrel_tail.
  unfold implMR, andR, EP1,EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 (H1, H2); intuition.
  mem_upd_simpl.
  rewrite (H1 _ N); trivial.

  apply equiv_trans_eq_mem_l with trueR Er
   [ 
    yR <$- {0,1}^k;
    while Elength (R) <! N do 
     [
      y <$- {0,1}^k; 
      R <- y |::| R
     ]; 
     R <- R |++| yR |::| Nil _ 
   ]. 
  swap; rewrite proj1_MR; apply equiv_eq_mem.
  apply equiv_trans_eq_mem_r with 
   (P2 := EP2 (0 <! N) /-\ EP2 (R =?= E.Cnil (T.User BS_k)))
   (E2':=Er) 
   (c2':= 
    [ y <$- {0,1}^k;
     R <- y |::| R;
      while Elength (R) <! N do 
       [
        y <$- {0,1}^k; 
        R <- y |::| R
       ]
    ]). 
  apply equiv_eq_sem_pre; intros; rewrite deno_while, deno_cond.
  match goal with |- (if ?X then _ else _) == _ => replace X with true; trivial end.
  generalize H; clear H; unfold andR, EP2; simpl; unfold O.eval_op; simpl.
  intros (H1, H2); rewrite is_true_Ti_eqb in H2; rewrite H2.
  rewrite plus_comm; simpl; symmetry; trivial.
  assert (
   decMR
   (req_mem_rel (Vset.add R (Vset.singleton L))
    ((fun (k : nat) (m1 m2 : Mem.t k) =>
     E.eval_expr N m1 = (E.eval_expr N m2 - 1)%nat) /-\
    EP2 (0 <! N) /-\ EP1 (R =?= E.Cnil (T.User BS_k))))).
  apply decMR_req_mem_rel; apply decMR_and; auto.
  red; intros.
  generalize (T.i_eqb_spec k T.Nat (E.eval_expr N x) (E.eval_expr N y - 1)%nat).
  destruct (T.i_eqb k T.Nat (E.eval_expr N x) (E.eval_expr N y - 1)%nat); simpl; auto.
  apply equiv_depend_only_r with 
   (X1 := Vset.add L (Vset.singleton R))
   (X2 := Vset.add L (Vset.singleton R))
   (E2':= Er)
   (c2':= [yR <$- {0,1}^k; R <- yR |::| R;
    while Elength (R) <! N do [y <$- {0,1}^k; R <- y |::| R] ]); trivial.
  eqobs_tl.
  alloc_l y yR; ep; deadcode; eqobs_in.
  match goal with
   |- equiv _ _ [?i1;?i2;?i3] _ [?i4;?i5;?i6] _ =>
    change [i1; i2; i3] with ([i1] ++ ([i2]++[i3]));
     change [i4; i5; i6] with ([i4; i5] ++ ([i6] ++ nil)) end.
  apply equiv_app with
   (req_mem_rel (Vset.add yR (Vset.singleton L))
    (fun k m1 m2 => E.eval_expr (R |++| (yR|::|Nil _)) m1 = E.eval_expr R m2 /\
     E.eval_expr (N +! 1%nat) m1 = E.eval_expr N m2)).
  eqobsrel_tail.
  unfold implMR, EP1, EP2, andR; simpl; unfold O.eval_op; simpl; intros k m1 m2 (H1, (H2, (H3, H4))).
  intros v _; repeat rewrite Mem.get_upd_same.
  repeat (rewrite Mem.get_upd_diff;[ | discriminate]).
  rewrite H2, <- (H1 _ R); trivial.
  rewrite plus_comm, <- le_plus_minus.
  rewrite is_true_Ti_eqb in H4; rewrite H4; auto.
  destruct (m2 N);[discriminate H3 | auto with arith].
  match goal with |- equiv ?P _ _ _ _ _ => apply equiv_app with P end.
  eapply equiv_weaken;[ | apply equiv_while].
  unfold andR; intros k m1 m2 (H1, _); trivial.
  intros k m1 m2 (H1, (H2, H3)); generalize H2 H3; clear H2 H3.
  simpl; unfold O.eval_op; simpl; intros H2 H3.
  rewrite (plus_comm (length (m2 R))), <- H2, <- H3,app_length.
  rewrite (plus_comm (m1 N)); trivial.
  rewrite proj1_MR.
  eqobsrel_tail.
  unfold implMR, EP1, EP2, andR; simpl; unfold O.eval_op; simpl; intros k m1 m2 (H1, (H2, H3)).
  intros v _; mem_upd_simpl.
  simpl; rewrite H2; auto.
  eapply equiv_strengthen;[ | apply equiv_assign_l].
  unfold upd1, req_mem_rel, andR; simpl; unfold O.eval_op; simpl.
  unfold kreq_mem; intros k m1 m2 (H1, (H2, H3)).
  rewrite H2.
  match goal with
   |- _ =={?W} _ => change W with (Vset.add L (Vset.singleton R))end.
  red; intros tx x Hin; repeat rewrite VsetP.add_spec in Hin.
  destruct Hin as [ Hin | Hin ].
  inversion Hin; simpl; rewrite Mem.get_upd_diff;[ apply (H1 _ L); trivial | discriminate].
  apply Vset.singleton_complete in Hin.
  inversion Hin; simpl; rewrite Mem.get_upd_same; trivial.
  red; unfold transpR, EP1, EP2, req_mem_rel, andR.
  intros k m1 m2 (H1, (H2, (H3, H4))); split; trivial.
  assert (W:= @EqObs_e_fv_expr _ (R =?= E.Cnil (T.User BS_k)) k m1 m2).
  simpl in H4, W |- *; unfold O.eval_op in H4, W |- *; simpl in H4, W |- *.
  rewrite H4 in W; apply W.
  apply req_mem_sym; apply req_mem_weaken with (2:= H1); vm_compute; trivial.
  unfold trueR; red; intros; trivial.
 Qed.

 Definition GR_q :=
  [ 
   R <- Nil _;
   while Elength R <! q do [y <$- {0,1}^k; R <- y |::| R]; 
   R' <- R;
   L <- Nil _; 
   b <c- A with {} 
  ].

 Lemma G0_GR_q : EqObs Vset.empty Ef G0 Er GR_q (Vset.singleton L).
 Proof.
  apply EqObs_trans with Er 
   ([ N <- q ] ++
    [ 
     L <- Nil _; 
     R <- Nil _;
     while Elength R <! N do [y <$- {0,1}^k; R <- y |::| R]; 
     b <c- A with {} 
    ]).
  change G0 with (nil ++ G0).
  apply equiv_app with (req_mem_rel Vset.empty (EP2 (N =?= q))).
  eqobsrel_tail.
  unfold implMR; simpl; unfold O.eval_op; simpl; intros; apply Ti_eqb_refl.
  red; intros.
  destruct (@equiv_ind (q_poly k) k) as (d, H); exists d; intros.
  eapply lift_weaken;[ | apply H].
  intros x y (H1, _); trivial.  
  split;[ apply req_mem_empty | ].
  destruct H0 as (_, H0); generalize H0; unfold EP2; simpl; unfold O.eval_op; simpl; intros.
  rewrite is_true_Ti_eqb in H1; trivial.
  ep iErEr; deadcode iErEr; swap iErEr; eqobs_in iErEr.
 Qed.


 (** Invariant of [GR_q] *)

 Definition inv_app : mem_rel :=
  (EP1 (Elength R' =?= q)) /-\
  (EP1 (Elength L <=! q) |-> 
   (fun k m1 m2 => m1 R' = rev_append (map (@snd _ _) (m1 L)) (m1 R))).
 
 Lemma inv_app_dep : 
  depend_only_rel inv_app
  (Vset.union (fv_expr (Elength R' =?= q))
   (Vset.union (fv_expr (Elength L <=! q)) (Vset.add R' (Vset.add R (Vset.singleton L)))))
  (Vset.union Vset.empty (Vset.union Vset.empty Vset.empty)).
 Proof.
  apply depend_only_andR; auto.
  apply depend_only_impR; auto.
  red; intros.
  rewrite <- (H _ R'); trivial; rewrite H1.  
  rewrite (H _ L); trivial; rewrite (H _ R); trivial.
 Qed.

 Lemma inv_app_dec : decMR inv_app.
 Proof.
  apply decMR_and; auto.
  apply decMR_imp; auto.
  red; intros.
  match goal with |- sumbool (?e1 = ?e2) _ => 
   generalize (T.i_eqb_spec k (T.List (T.User BS_k)) e1 e2); 
   destruct (T.i_eqb k (T.List (T.User BS_k)) e1 e2); auto end.
 Qed.

 Definition eErEr_app : eq_inv_info inv_app Er Er.
  refine (@empty_inv_info inv_app _ _ inv_app_dep _ inv_app_dec Er Er).
  vm_compute; trivial.
 Defined.

 Lemma Fr_inv_app : 
  EqObsInv inv_app (Vset.add x (Vset.add R' (Vset.add R (Vset.singleton L))))
  Er Fr Er Fr (Vset.add y (Vset.add R (Vset.singleton L))). 
 Proof.
  unfold Fr.
  cp_test (x in_dom L); rewrite proj1_MR.
  eqobs_in eErEr_app.
  cp_test (0 <! Elength (R)).
  unfold inv_app; eqobsrel_tail.
  unfold implMR, andR, impR, EP1, EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 (H1, ((H2, H3), (H4, H5))).
  mem_upd_simpl.
  split; trivial.
  intros H6; change (is_true 
   (Compare_dec.leb (S (length (m1 L))) (q_poly k))) in H6.
  rewrite H3.
  destruct (m1 R);[ discriminate H4 | trivial].
  apply leb_correct; apply leb_complete in H6; omega.
  unfold inv_app; eqobsrel_tail.
  unfold implMR, andR, impR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 (H1, ((H2, H3), (H4, H5))) v _.
  mem_upd_simpl.
  split; trivial.
  intros H6; change (is_true 
   (Compare_dec.leb (S (length (m1 L))) (q_poly k))) in H6.
  apply leb_complete in H6.
  elimtype False.
  rewrite is_true_Ti_eqb, H3, rev_append_rev, app_length, rev_length, map_length in H2.
  rewrite <- H2 in H6; destruct (m1 R).
  simpl in H6; omega.
  apply H4; trivial.
  apply leb_correct; omega.
 Qed.

 Definition iapp : eq_inv_info inv_app Er Er :=
  iEinv  eErEr_app Vset.empty Vset.empty Fr_inv_app.

 Lemma pr_while_dup : forall E k n (m:Mem.t k),
  n = E.eval_expr (q -! Elength R) m ->
  noDup (T.i_eqb k (T.User BS_k)) (m R) ->
  mu ([[ [ while Elength R <! q do [ y <$- {0,1}^k; R <- y |::| R ] ] ]] E m)
  (charfun
   (fun m0:Mem.t k =>
    negb (noDup (T.i_eqb k (T.User BS_k)) (m0 R)))) <= 
  (sum_k_p (E.eval_expr (Elength R) m) (E.eval_expr (q -! 1%nat) m)) */ [1/2]^k.  
 Proof.
  unfold Pr; induction n; intros; rewrite deno_while_elim, deno_cond_elim;
   match goal with
    |- ?Q => match Q with context [if ?X then _ else _] => case_eq X; intros end end.
  elimtype False; generalize H0 H1; clear H0 H1; simpl; unfold O.eval_op; simpl; intros.
  simpl in H; unfold O.eval_op in H; simpl in H.
  apply leb_complete in H1; omega.
  rewrite deno_nil_elim; unfold charfun,restr, EP; simpl; rewrite H; trivial.
  simpl in H0; rewrite H0; trivial.
  simpl app; rewrite deno_cons_elim, Mlet_simpl.
  transitivity 
   (mu (sum_support (T.default k (T.User BS_k)) (E.eval_support {0,1}^k m))
    (fplus (fun v : T.interp k (T.User BS_k) =>
     (if E.eval_expr (y is_in R) (m {!y <-- v!}) then 1 else 0))
    (fcte _ (sum_k_p (S (E.eval_expr Elength R m)) (E.eval_expr (q -! 1%nat) m) */[1/2]^k)))).
  unfold fplus, fcte; rewrite deno_random_elim.
  apply mu_monotonic; intro.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  match goal with
   |- ?G => match G with context [if ?e then _ else _] => case_eq e; intros;Usimpl;[trivial | ] end end.
  set (m1 := ((m {!y <-- x!}) {!R <-- E.eval_expr (y |::| R) (m {!y <-- x!})!})).
  replace (S (E.eval_expr Elength (R) m)) with (E.eval_expr (Elength R) m1).
  change (E.eval_expr (q -! 1%nat) m) with (E.eval_expr (q -! 1%nat) m1).
  apply IHn; unfold m1; clear m1 IHn.
  generalize H; clear H; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl; simpl; intros; omega.
  generalize H2; clear H2; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  intro; simpl; rewrite H2; trivial.
  unfold m1; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  rewrite mu_le_plus, (@sum_Sk_p (E.eval_expr Elength (R) m)).
  rewrite plus_Nmult_distr.
  apply Uplus_le_compat.
  transitivity 
   (mu (sum_support (T.default k (T.User BS_k)) (E.eval_support {0,1}^k m))
    (sigma_fun 
     (fun i v =>
      if T.i_eqb k (T.User BS_k) v
       (nth i (m R) (T.default k (T.User BS_k)))
       then 1
       else 0)
     (length (m R)))). 
  apply mu_monotonic; intro v; unfold sigma_fun.
  rewrite (sigma_finite_sum
   (T.default k (T.User BS_k))
   (fun w : T.interp k (T.User BS_k) => if T.i_eqb k (T.User BS_k) v w then 1 else 0)).
  simpl; unfold O.eval_op; simpl.
  rewrite Mem.get_upd_same; rewrite Mem.get_upd_diff;[ | discriminate].
  generalize (m R).
  induction i; simpl; trivial.
  destruct (T.i_eqb k (T.User BS_k) v a);Usimpl; simpl; auto.
  rewrite mu_sigma_le.
  change (E.eval_expr Elength (R) m) with (length (m R)).
  rewrite Nmult_sigma.
  apply sigma_le_compat.
  intros i Hlt.
  apply (@Pr_bs_support k (T.default k (T.User BS_k)) 
   (nth i (m R) (T.default k (T.User BS_k)))
   (fun e v => if T.i_eqb k (T.User BS_k) v e then 1 else 0)).
  intros.
  generalize (T.i_eqb_spec k (T.User BS_k) x
   (nth i (m R) (T.default k (T.User BS_k)))).
  destruct (T.i_eqb k (T.User BS_k) x
   (nth i (m R) (T.default k (T.User BS_k)))); trivial.
  intros; elim H2; trivial.
  rewrite Ti_eqb_refl; trivial.

  apply mu_cte_le.
  generalize H1; clear H1; simpl; unfold O.eval_op; simpl; intros.
  apply leb_complete in H1; omega.
  rewrite deno_nil_elim; unfold charfun,restr, EP; simpl in H0 |- *; rewrite H0; trivial. 
 Qed.

 Lemma switching : forall k m,
  Uabs_diff (Pr Ef G0 m (EP k b)) (Pr Ep G0 m (EP k b)) <=
  ((q_poly k - 1) * q_poly k) /2^(1 + k).
 Proof.
  intros k m; rewrite (diff_bad m).
  rewrite bad_dup.
  match goal with |- Pr _ _ _ ?F <= _ => set (f:=F) end.
  unfold Pr.
  transitivity (mu (([[G0]]) Ef m) (restr (EP k (Elength (L) <=! q)) (charfun f))).
  apply (range_le (A_range m)).
  unfold restr; intros a H; rewrite H; trivial.
  set (f1 := restr (EP k (Elength (L) <=! q)) (charfun f)).
  assert (H : forall m1 m2 : Mem.t k,
   kreq_mem (Vset.singleton L) m1 m2 -> f1 m1 == f1 m2).
  intros m1 m2 H; unfold f1, charfun, restr, EP, f.
  simpl; unfold O.eval_op; simpl; rewrite (H _ L); trivial.
  rewrite (equiv_deno G0_GR_q f1 f1 H m m (req_mem_refl _ _)); clear H.
  set (cW := [ R <- E.Cnil (T.User BS_k);
   while Elength (R) <! q do [y <$- {0,1}^k; R <- y |::| R] ]).
  change GR_q with
   (cW
    ++
    [R'<-R;L <- Nil _; b <c- A with{} ]).
  rewrite deno_app_elim.
  assert (equiv trueR Er cW Er cW (req_mem_rel (Vset.singleton R) (EP1 (Elength R =?= q)))).
  apply equiv_cons with (req_mem_rel (Vset.singleton R) (EP1 (Elength R <=! q))).
  eqobsrel_tail.
  unfold implMR, req_mem_rel, andR; simpl; unfold O.eval_op; simpl; intros; split; trivial.
  apply req_mem_empty. 
  eapply equiv_weaken;[ | apply equiv_while].
  unfold req_mem_rel, notR, andR, EP1; simpl; unfold O.eval_op; simpl; intros.
  destruct H as ((H1, H2),(H3,H4)); split; trivial.
  rewrite is_true_Ti_eqb.
  apply leb_complete in H2.
  rewrite <- is_true_negb, is_true_negb_false in H3.
  apply leb_complete_conv in H3.
  omega.
  intros k0 m1 m2 (H1, H2); apply EqObs_e_fv_expr; exact H1.
  eqobsrel_tail.
  unfold implMR, EP1, req_mem_rel, andR; simpl; unfold O.eval_op; simpl; intros.  
  destruct H as (_, (_, (H, _))).
  rewrite plus_comm in H; trivial.
  transitivity 
   (mu (([[cW]]) Er m)
    (restr (EP k (Elength R =?= q))
     (fun mn' : Mem.t k =>
      mu
      (([[[ R' <- R;L <- E.Cnil (T.Pair (T.User BS_k) (T.User BS_k));
       b <c- A with{}] ]]) Er mn') f1))).
  apply equiv_deno_le with (1:= H).
  unfold restr, EP, EP1.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  intros m1 m2 (H1, H2); rewrite <- (H1 _ R); trivial; rewrite H2; trivial.
  apply equiv_deno_le with (P:= kreq_mem (Vset.singleton R)) (Q:= kreq_mem (Vset.singleton L)); trivial.
  eqobs_in iErEr.
  unfold f1, f, charfun, restr,EP; simpl; unfold O.eval_op; simpl. 
  intros m3 m4 H3; rewrite (H3 _ L); trivial.
  red; trivial.
  transitivity 
   (mu (([[cW]]) Er m) (charfun (fun m : Mem.t k => negb (noDup (T.i_eqb k (T.User BS_k)) (m R))))).
  apply mu_monotonic; intro m'.
  unfold restr; case_eq (EP k (Elength (R) =?= q) m'); intros;[ | trivial].
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim, deno_cons_elim, Mlet_simpl, deno_assign_elim.
  compute_assertion Heq res (modify (refl1_info iErEr) Vset.empty [b <c- A with{}]).  
  apply modify_correct in Heq.
  transitivity 
   (mu
    (([[[b <c- A with{}] ]]) Er
     ((m' {!R' <-- E.eval_expr R m'!}) {!L <--
      E.eval_expr (E.Cnil (T.Pair (T.User BS_k) (T.User BS_k)))
      (m' {!R' <-- E.eval_expr R m'!})!})) 
    (charfun (fun m0 : Mem.t k =>
     negb (noDup (T.i_eqb k (T.User BS_k)) (m0 R'))))).
  assert (EqObsInv inv_app (Vset.add L (Vset.add R (Vset.singleton R')))
   Er [b <c- A with{}] Er [b <c- A with{}] (Vset.add L (Vset.add R (Vset.singleton R')))).
  eqobs_in iapp.
  apply equiv_deno_le with (1:= H1); clear H1.
  unfold req_mem_rel, inv_app, andR, impR, f1, f, fcte, charfun, 
   EP1, EP, restr, fone; simpl; unfold O.eval_op; simpl.
  intros m1 m2 (H1, (H2, H3)).
  match goal with |- (if ?e then _ else _) <= _ => case_eq e; intros Heq1; trivial end.
  apply H3 in Heq1; clear H3.
  rewrite <- (H1 _ R'); trivial.
  match goal with |- _ <= (if ?e1 then _ else _) => case_eq e1; intros Heq2; trivial end.
  match goal with |- (if ?e then _ else _) <= _ => replace e with false; trivial end.
  symmetry; rewrite <- is_true_negb_false, negb_involutive.
  rewrite <- is_true_negb_false, negb_involutive in Heq2.
  rewrite noDup_spec in Heq2; [ | apply (T.i_eqb_spec k (T.User BS_k))].
  rewrite noDup_spec; [ | apply (T.i_eqb_spec k (T.User BS_k))].
  rewrite Heq1, rev_append_rev in Heq2.
  apply NoDup_app_inv in Heq2; destruct Heq2.
  apply Permutation_NoDup with (2:=H3).
  apply Permutation_sym; apply Permutation_rev.
  unfold req_mem_rel, inv_app, andR, impR; split.
  red; red; intros.
  repeat rewrite VsetP.add_spec in H1; destruct H1 as [H1 | [ H1 | H1 ] ].
  inversion H1; simpl; mem_upd_simpl.
  inversion H1; simpl; mem_upd_simpl.
  apply Vset.singleton_complete in H1.
  inversion H1; simpl; mem_upd_simpl.
  generalize H0; clear H0; unfold EP, EP1; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  intros; split; trivial.
  rewrite (Modify_deno_elim Heq).
  rewrite <- (@mu_cte_eq _
   (([[[b <c- A with{}] ]]) Er
    ((m' {!R' <-- E.eval_expr R m'!}) {!L <--
     E.eval_expr (E.Cnil (T.Pair (T.User BS_k) (T.User BS_k)))
     (m' {!R' <-- E.eval_expr R m'!})!}))
   (charfun
    (fun m0 : Mem.t k =>
     negb (noDup (T.i_eqb k (T.User BS_k)) (m0 R))) m')).
  apply mu_monotonic; intro.
  unfold charfun, fcte, restr, fone.
  rewrite update_mem_notin.
  mem_upd_simpl.
  intros Hin; discriminate Hin.
  unfold fone.
  apply is_lossless_correct with (refl1_info iErEr).
  vm_compute; trivial.
  unfold cW; rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  rewrite (@pr_while_dup Er k (q_poly k)).
  simpl; unfold O.eval_op; simpl.
  rewrite Mem.get_upd_same; simpl.
  replace ((q_poly k - 1) * q_poly k)%nat with
   ((q_poly k - 1) * ((q_poly k - 1) + 1))%nat.
  rewrite <- sum_0_n.
  rewrite mult_comm, Nmult_mult_assoc, Nmult_Umult_assoc_left;[ | apply Nmult_def_Unth].
  simpl; rewrite Unth_one_plus;Usimpl; trivial.
  destruct (q_poly k); simpl; trivial.
  rewrite <- minus_n_O, plus_comm; trivial.
  simpl; unfold O.eval_op; simpl; mem_upd_simpl.
  rewrite <- minus_n_O; trivial.
  mem_upd_simpl.
 Qed.

End ADVERSARY.
