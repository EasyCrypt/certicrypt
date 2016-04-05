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
Notation Rinit := (Var.Gvar (T.List (T.User BS_k)) 11).
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
  rewrite is_true_andb, is_true_negb, is_true_existsb in H; destruct H.
  constructor.
  intro; apply H; exists a; split; trivial.
  generalize (eqb_spec a a); destruct (eqb a a); 
   trivial; intros H2; elim H2; trivial.
  rewrite <- IHl; trivial.
  inversion_clear H.
  rewrite <- IHl in H1; rewrite  H1, andb_true_r, is_true_negb; intro; apply H0.
  rewrite is_true_existsb in H; destruct H as (x, (H2, H3)).
  assert (W:=eqb_spec a x); rewrite H3 in W; rewrite W; trivial.
 Qed.

 Definition inv_dup := 
  EP1 bad |-> 
   (fun k m1 m2 => negb (noDup (T.i_eqb k (T.User BS_k)) (map (@snd _ _) (m2 L)))).
 
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
   If !(R =?= (Nil _)) then [ y <- Ehd R; R <- Etl R ]
   else [ y <$- {0,1}^k ];
   L <- (x|y) |::| L
  ];
  y <- L[{x}]
 ].

 Definition Er := mkEnv Fr.

 Definition SR := [
  R <- Nil _;
  while (Elength L +! Elength R <! q) do 
   [
    yR <$-{0,1}^k; 
    R <- R |++| (yR |::| Nil _)
   ];
  yR <$-{0,1}^k
  ].

 Definition get_option (o:option Vset.t) :=
  match o with 
  | Some s => s 
  | None => Vset.empty
  end.

 Definition XSR : Vset.t := 
  Eval vm_compute in get_option (modify (refl1_info (empty_info Ef Ef)) Vset.empty SR).

 Lemma SR_Modify : forall E, Modify E XSR SR.
 Proof.
  intros E;apply modify_correct with (refl1_info (empty_info E E)) Vset.empty.
  vm_compute;trivial.
 Qed.

 Definition ISR := Vset.singleton L.

 Lemma EqObs_SR : EqObs (Vset.union ISR XSR) Ef SR Er SR XSR.
 Proof. eqobs_in. Qed.

 Lemma IX_glob :  forall x : VarP.Edec.t, Vset.mem x (Vset.union ISR XSR) -> Var.is_global x.
 Proof.
  apply Vset.forallb_correct.
  intros x y Heq;rewrite Heq;trivial.
  vm_compute;trivial.
 Qed.

 Notation L1 := (Var.Gvar (T.List (T.Pair (T.User BS_k) (T.User BS_k))) 12).

 Lemma swap_F : equiv Meq Ef (Ff ++ SR) Er (SR ++ Fr) Meq.
 Proof.
  unfold Ff, Fr.
  union_mod;[ trivial | ].
  swap. eqobs_tl.
  cp_test (x in_dom L);rewrite proj1_MR.
   eqobs_in.
  cp_test (Elength (L) <! q).
  alloc_l L L1. ep.
  match goal with |- equiv _ _ (?i1::?i2::?i3::?c) _ _ _ =>
    apply equiv_trans_eq_mem_l with trueR Ef ((i1::i2::c)++[i3]) end.
  rewrite proj1_MR;union_mod;[trivial | ]. swap;eqobs_in.
  eqobs_tl;ep;deadcode.
  match goal with |- equiv ?P _ _ ?E2 (?i1::(while ?e do ?C)::?T) ?Q => 
    change (i1::(while e do C)::T) with
     ([i1] ++ ([while e do C] ++ T));
    apply equiv_trans_eq_mem_r with trueR E2
      ([i1]++([If e _then C ++ [while e do C] ]++ T)) end.
  rewrite proj1_MR;apply equiv_eq_sem; intros k m.
  rewrite deno_app, deno_app;apply Mlet_eq_compat;[trivial | ].
  apply ford_eq_intro; clear m;intros m.
  rewrite deno_app, deno_app;apply Mlet_eq_compat;[|trivial].
  apply deno_while.
  ep. ep_eq_r (Elength (Nil (T.User BS_k))) 0%nat;[ trivial | ].
  ep_eq_r (Elength (L) <! q) true.
    intros k m1 m2 (H1, (_, H2));exact H2.
  rewrite proj1_MR.
  match goal with |- equiv ?P _ [?i1;?i2;?i3] _ [?i4;?i5;?i6;?i7;?i8] ?Q => 
    change [i1;i2;i3] with ([i1;i2]++([i3] ++ nil));
    change [i4;i5;i6;i7;i8] with ([i4;i5;i6] ++ ([i7] ++[i8])) end.
  apply equiv_app with (req_mem_rel (Vset.add x (Vset.singleton L))
                          (fun k m1 m2 => E.eval_expr R m2 = E.eval_expr (y |::| R) m1)).
   set (P:= (fun (k : nat) (m1 m2 : Mem.t k) =>
      E.eval_expr R m2 = E.eval_expr (y |::| R) m1)).
   assert (Hdep : depend_only_rel P (fv_expr (y |::| R)) (fv_expr R)).
       red;intros;red.
       rewrite <- (depend_only_fv_expr _ H), <- (depend_only_fv_expr _ H0);trivial.
   assert (Hdep1 := @depend_only_req_mem_rel (Vset.add x (Vset.singleton L)) _ _ _ Hdep).
   assert (Hdec : decMR Meq) by auto.
   match type of Hdep1 with depend_only_rel ?p ?x1 ?x2 => set (P1 := p);set (X1 := x1); set (X2:= x2) end.
   set (c1 := [y <$- {0,1}^k; R <- Nil _]).
   set (c2 := [R <- Nil _;yR <$- {0,1}^k;R <- yR |::| Nil _]).
   compute_assertion Heq1 res1 (alloc_c_out (refl1_info (empty_info Ef Er)) y yR c1 X1).
   refine (@alloc_c_out_equiv_l _ y yR _ Ef (refl1_info (empty_info Ef Er)) c1 res1 Er c2 
                 X1 X2 P1 Hdec Hdep1 Heq1 _).
    ep;unfold P1, P.
    eqobsrel_tail;intros k m1 m2 Heq;unfold Meq in Heq;subst;simpl;unfold O.eval_op;simpl.
    intros; mem_upd_simpl.
   apply equiv_app with (req_mem_rel (Vset.add x (Vset.singleton L))
    (fun k m1 m2 => E.eval_expr R m2 = E.eval_expr (y |::| R) m1)).
   eapply equiv_weaken;[ | apply equiv_while].
    intros k m1 m2 (H1, _);trivial.
    intros k m1 m2 (H1, H2);generalize H2;clear H2.
Opaque leb.    
    simpl;unfold O.eval_op;simpl;intros Heq;rewrite Heq, (H1 _ L);trivial.
    simpl length. 
    repeat rewrite <- plus_Snm_nSm;trivial.
   eqobsrel_tail;intros k m1 m2;simpl;unfold O.eval_op;simpl; intros (H1, (H2, _)).
   intros; mem_upd_simpl.
   rewrite H2;trivial.
  ep_eq_r (R =?= Nil _) false.
  simpl;unfold O.eval_op;simpl;intros k m1 m2 (H1, H2);rewrite H2;trivial.
  apply equiv_weaken with
     (req_mem_rel (Vset.add x (Vset.singleton L)) 
         (fun k m1 m2 => E.eval_expr R m1 = E.eval_expr R m2 /\  E.eval_expr y m1 = E.eval_expr y m2)).
     intros k m1 m2 (H1, (H2, H3)).
     change (kreq_mem
      (Vset.add L (Vset.add y (Vset.add x (Vset.singleton R)))) m1 m2).
     intros t v;repeat rewrite VsetP.add_spec.
     intros [H | [ H | [ H | H ] ] ];
      try (apply Vset.singleton_complete in H);
      inversion H;simpl;trivial;(apply (H1 _ L)|| apply (H1 _ x));trivial.
   eqobsrel_tail;unfold EP1;simpl;unfold O.eval_op;simpl;intros k m1 m2 (H1, H2).
   mem_upd_simpl.   
   rewrite H2;auto.
  red;red;trivial.
  red;red;trivial.
  (***************************)
  match goal with |- equiv _ _ [?i1;?i2;?i3;?i4] _ _ _ =>
    change [i1;i2;i3;i4] with ([i1;i2;i3]++[i4]);
    apply equiv_trans_eq_mem_l with (~- EP1 (Elength (L) <! q)) Ef ([i1;i2;i3] ++ nil) end.
  union_mod;[rewrite proj1_MR;trivial | ].
  apply equiv_app with (req_mem_rel (Vset.add y (Vset.add L (Vset.add R (Vset.singleton yR)))) 
                         (~-EP1 ((Elength (L) +! Elength (R)) <! q))).
    eqobsrel_tail;unfold EP1, notR;simpl;unfold O.eval_op;simpl;intros k m1 m2 (H1, H2).
   apply not_is_true_false in H2;apply leb_complete_conv in H2.
   intros v _ Hleb; apply leb_complete in Hleb.
   change (S (length (m1 L) + 0 + 1)) with (1 + length (m1 L) + 0 + 1)%nat in Hleb.
   omega.
 
  ep_eq_l (Elength L +! Elength R <! q) false.
  unfold notR, EP1;intros k m1 m2 (_, H);apply not_is_true_false in H;trivial.
  eqobs_in.
  match goal with 
   |- equiv _ _ _ _ [?i1;?i2;?i3;?i4] _ =>
    change [i1;i2;i3;i4] with (([i1]++[i2])++[i3;i4]);
    apply equiv_trans_eq_mem_r with (~- EP1 (Elength L <! q)) Er (([i1] ++ nil) ++[i3;i4]) 
  end.
  union_mod; [rewrite proj1_MR;trivial | ].
  apply equiv_app with (kreq_mem {{x,y,L,R,yR}}).
  apply equiv_app with (req_mem_rel {{x,y,L,R,yR}}
   (~-EP1 ((Elength L +! Elength R) <! q))).
  eqobsrel_tail;unfold EP1, notR;simpl;unfold O.eval_op;simpl;intros k m1 m2 (H1, H2).
  rewrite plus_0_r; trivial.
  ep_eq_l (Elength L +! Elength R <! q) false.
   unfold notR, EP1;intros k m1 m2 (_, H);apply not_is_true_false in H;trivial.
   eqobs_in.
   eqobs_in.
  ep;swap;eqobs_in.
  intros k m1 m2 (H1, (H2, H3));trivial.
  intros k m1 m2 (H1, (H2, H3));trivial.
 Qed.

 (* Move this *)
 Lemma lossless_while : forall E (b:E.expr T.Bool) c (variant:E.expr T.Nat),
  lossless E c ->
  (forall k (m:Mem.t k), E.eval_expr b m -> 
   range (EP k (variant <! (E.eval_expr variant m))) ([[c]] E m)) ->  
  lossless E [while b do c].
 Proof.
  intros E b C variant Hloss Hvar k.
  assert (forall (n:nat) (m : Mem.t k), E.eval_expr variant m = n ->
     (mu (([[ [while b do C] ]]) E m)) (fun _ : Mem.t k => 1) == 1).
   induction n using lt_wf_ind;intros.
   rewrite deno_while_elim, deno_cond_elim.
   case_eq (E.eval_expr b m);intros Heq;[ | rewrite deno_nil_elim;trivial].
   rewrite deno_app_elim, <- (Hloss k m).
   apply range_eq with (1:= Hvar k m Heq).
   intros m' Hlt;apply (H (E.eval_expr variant m'));trivial.
   rewrite <- H0;unfold EP in Hlt;simpl in Hlt;unfold O.eval_op in Hlt;simpl in Hlt.
   apply leb_complete in Hlt;omega.
  intros m;apply (H (E.eval_expr variant m) m (refl_equal _)).
 Qed.

 Lemma range_EP_equiv_EP1 : forall E c (pre post:E.expr T.Bool),
  equiv (Meq /-\ EP1 pre) E c E c (EP1 post) ->
  forall k (m:Mem.t k), E.eval_expr pre m -> range (EP k post) ([[ c ]] E m).
 Proof.
  intros E C pre post Hequiv k m Hpre f Hf.
  rewrite <- (mu_zero ([[C]] E m)).
  symmetry;apply equiv_deno with (1:= Hequiv);[intros m1 m2 Hpost | split;trivial].
  symmetry;apply (Hf m1 Hpost).
 Qed.

 (* Instantiation *)
 Lemma lossless_while_equiv : forall E (b:E.expr T.Bool) c (variant:E.expr T.Nat),
  lossless E c ->
  (forall (n:nat), equiv (Meq /-\ EP1 (b && (variant =?= n))) E c E c 
   (req_mem_rel Vset.empty (EP1 (variant <! n)))) ->
  lossless E [while b do c].
 Proof.
  intros E b C variant Hloss Hequiv.
  apply lossless_while with (variant := variant);[trivial | ].
  intros k m Hb;apply range_EP_equiv_EP1 with (pre:= (b && (variant =?= (E.eval_expr variant m)))).
    apply equiv_weaken with (2:= Hequiv (E.eval_expr variant m)).
    intros k1 m1 m2 (H1, H2);trivial.
    simpl;unfold O.eval_op;simpl;rewrite Hb;apply nat_eqb_refl.
 Qed.
 (* End MOVE THIS *)

 Definition iEf := i_refl Ff Ff Vset.empty Vset.empty.

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
  match goal with 
   |- sumbool (?e1 = ?e2) _ => 
    generalize (T.i_eqb_spec k (T.List (T.User BS_k)) e1 e2); 
     destruct (T.i_eqb k (T.List (T.User BS_k)) e1 e2); auto
  end.
 Qed.

 Definition eErEr_app : eq_inv_info inv_app Er Er.
  refine (@empty_inv_info inv_app _ _ inv_app_dep _ inv_app_dec Er Er).
  vm_compute; trivial.
 Defined.

 Lemma Fr_inv_app : 
  EqObsInv inv_app (Vset.add x (Vset.add R' (Vset.add R (Vset.singleton L))))
  Er Fr Er Fr (Vset.add y (Vset.add R (Vset.singleton L))). 
 Proof.
Opaque T.i_eqb.
  unfold Fr.
  cp_test (x in_dom L); rewrite proj1_MR.
  eqobs_in eErEr_app.
  cp_test (R =?= Nil _); unfold inv_app; eqobsrel_tail;
  unfold implMR, andR, impR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl;
  intros k m1 m2 (H1, ((H2, H3), (H4, H5)));intros;
  repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff;[ | intro; discriminate]));
  (split; [trivial|intros]);rewrite is_true_Ti_eqb in *.
  elimtype False.
  rewrite H3, H4, rev_append_rev, app_length, rev_length, map_length in H2;
  apply leb_complete in H0;simpl length in H2;[| apply leb_correct].
  rewrite <- H2 in H0; rewrite plus_0_r in H0.
  change (SwitchingSem.Sem.T.List) with T.List in H0.
  change (SwitchingSem.Sem.T.User) with T.User in H0.
  change (SwitchingSem.Sem.T.Pair) with T.Pair in H0. 
  omega.
  change (SwitchingSem.Sem.T.List) with T.List in H0.
  change (SwitchingSem.Sem.T.User) with T.User in H0.
  change (SwitchingSem.Sem.T.Pair) with T.Pair in H0.
  omega.
  rewrite H3;simpl.
  destruct (m1 R);[elim H4|];trivial.
  apply leb_correct; apply leb_complete in H.
  apply le_trans with (2:=H); auto.
 Qed.

 Definition iapp : eq_inv_info inv_app Er Er :=
  iEinv  eErEr_app Vset.empty Vset.empty Fr_inv_app.

 Lemma pr_while_dup : forall E k n (m:Mem.t k),
  n = E.eval_expr (q -! Elength R) m ->
  noDup (T.i_eqb k (T.User BS_k)) (m R) ->
  mu ([[ [ while Elength R <! q do [ yR <$- {0,1}^k; R <- R |++| yR |::| Nil _ ] ] ]] E m)
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
     (if E.eval_expr (yR is_in R) (m {!yR <-- v!}) then 1 else 0))
    (fcte _ (sum_k_p (S (E.eval_expr Elength R m)) (E.eval_expr (q -! 1%nat) m) */[1/2]^k)))).
  unfold fplus, fcte; rewrite deno_random_elim.
  apply mu_monotonic; intro.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  match goal with
   |- ?G => match G with context [if ?e then _ else _] => case_eq e; intros;Usimpl;[trivial | ] end end.
  set (m1 := ((m {!yR <-- x!}) {!R <-- E.eval_expr (R |++| yR |::| Nil _) (m {!yR <-- x!})!})).
  replace (S (E.eval_expr Elength (R) m)) with (E.eval_expr (Elength R) m1).
  change (E.eval_expr (q -! 1%nat) m) with (E.eval_expr (q -! 1%nat) m1).
  apply IHn; unfold m1; clear m1 IHn.
  generalize H; clear H; simpl; unfold O.eval_op; simpl.
  repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff;[ | intro; discriminate])); trivial.
  rewrite app_length;simpl; intros; omega.
  generalize H2; clear H2; simpl; unfold O.eval_op; simpl.
  repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff;[ | intro; discriminate])); simpl; intros.
  assert (W:= noDup_spec _ (@T.i_eqb_spec k (T.User BS_k))).
  rewrite W;apply NoDup_app;try rewrite <- W;trivial.
  intros x0 [Hin | Hin]; inversion Hin;subst.
  clear H3;apply not_is_true_false in H2;intros Hin;elim H2;rewrite is_true_existsb.
  exists x0;split;[trivial | apply Ti_eqb_refl].
  unfold m1; simpl; unfold O.eval_op; simpl.
  repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff;[ | intro; discriminate])); trivial.
  rewrite app_length;simpl;ring.
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

 Definition iEr := i_refl Fr Fr Vset.empty Vset.empty.

 Lemma switching : forall k m,
  Uabs_diff (Pr Ef G0 m (EP k b)) (Pr Ep G0 m (EP k b)) <=
  ((q_poly k - 1) * q_poly k) /2^(1 + k).
 Proof.
  intros k m; rewrite (diff_bad m).
  rewrite bad_dup.
  match goal with |- Pr _ _ _ ?F <= _ => set (f:=F) end.
  unfold Pr.
  transitivity (mu (([[G0]]) Ef m) (restr (EP k (Elength L <=! q)) (charfun f))).
  apply (range_le (A_range m)).
  unfold restr; intros a H; rewrite H; trivial.
  set (f1 := restr (EP k (Elength L <=! q)) (charfun f)).
  assert (H : forall m1 m2 : Mem.t k,
   kreq_mem (Vset.singleton L) m1 m2 -> f1 m1 == f1 m2).
  intros m1 m2 H; unfold f1, charfun, restr, EP, f.
  simpl; unfold O.eval_op; simpl; rewrite (H _ L); trivial.
  set (SW:= [R<-Nil _; while (Elength R) <! q do [yR <$- {0,1}^k; R <- R |++| yR |::| Nil _] ]).

  transitivity (mu ([[ SW ]] Er m) 
                 (charfun (fun m : Mem.t k => negb (noDup (T.i_eqb k (T.User BS_k)) (m R))))).
    Focus 2.
      unfold SW;rewrite deno_cons_elim, Mlet_simpl,deno_assign_elim. 
      set (m1 := m {! R <-- E.eval_expr (E.Cnil (T.User BS_k)) m!}).
      eapply Ole_trans;[ apply pr_while_dup with (n := E.eval_expr q m1) | ];
      unfold m1;simpl;unfold O.eval_op;simpl;
      repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff;[ | intro; discriminate]));
      trivial;simpl length.
      rewrite <- minus_n_O;trivial.
      replace ((q_poly k - 1) * q_poly k)%nat with ((q_poly k - 1) * ((q_poly k - 1) + 1))%nat.
      rewrite <- sum_0_n.
      rewrite mult_comm, Nmult_mult_assoc, Nmult_Umult_assoc_left;[ | apply Nmult_def_Unth].
      simpl; rewrite Unth_one_plus;Usimpl; trivial.
      destruct (q_poly k); simpl; trivial.
      rewrite <- minus_n_O, plus_comm; trivial.

  transitivity (mu ([[ SW ++ [ R' <- R;L<-Nil _;b <c- A with{} ] ]] Er m) 
                 (charfun (fun m : Mem.t k => negb (noDup (T.i_eqb k (T.User BS_k)) (m R'))))).
    Focus 2.
      rewrite deno_app_elim.
      apply mu_le_compat;[trivial | intros m'].
      transitivity (mu ([[ [R' <- R] ]] Er m') 
                     (charfun (fun m : Mem.t k => negb (noDup (T.i_eqb k (T.User BS_k)) (m R'))))).
      apply Oeq_le;apply equiv_deno with Meq (kreq_mem (Vset.singleton R'));trivial.
      deadcode iEr;eqobs_in.
      intros m1 m2 Heq ;unfold charfun, restr; rewrite (Heq _ R');trivial.
      apply Oeq_le;rewrite deno_assign_elim;unfold charfun,restr, fone;simpl;rewrite Mem.get_upd_same;trivial.

  transitivity (mu ([[ SW ++ [ R' <- R;L<-Nil _;b <c- A with{} ] ]] Er m) f1).
    Focus 2.
      apply equiv_deno_le with Meq (req_mem_rel (Vset.add L (Vset.add R' (Vset.singleton R))) inv_app);trivial.
      eqobs_tl iapp.
      apply equiv_cons with (req_mem_rel (Vset.singleton R) (EP1 (Elength R <=! q))).
       eqobsrel_tail;simpl;unfold O.eval_op;simpl;red;trivial.
      apply equiv_cons with (req_mem_rel (Vset.singleton R) (EP1 (Elength R =?= q))).
      eapply equiv_weaken;[ | apply equiv_while].
       unfold notR, EP1;simpl;unfold O.eval_op;simpl;intros k1 m1 m2 ((H1, H2), (H3, H4));split;[trivial | ].
       apply not_is_true_false in H3;apply leb_complete_conv in H3;apply leb_complete in H2;
       rewrite is_true_Ti_eqb.
       change (SwitchingSem.Sem.T.List) with T.List in H3.
       change (SwitchingSem.Sem.T.User) with T.User in H3.
       change (SwitchingSem.Sem.T.Pair) with T.Pair in H3. 
       omega.
       intros k1 m1 m2 (H1, _);apply depend_only_fv_expr;trivial.
       eqobsrel_tail;unfold EP1;simpl;unfold O.eval_op;simpl;intros k1 m1 m2 (_, (_, (H1, _))) v _.
       rewrite app_length;trivial.
      unfold inv_app;eqobsrel_tail;unfold EP1;simpl;unfold O.eval_op;simpl;intros k1 m1 m2 (H1, H2);
       split;[trivial | ].
       intros _;repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff;[ | intro; discriminate]));trivial.
      unfold inv_app, f1, EP1, impR, charfun,restr, EP;intros m1 m2 (H1, (H2, H3)).
       match goal with |- (if ?b then _ else _) <= _ => destruct b;[ | trivial] end.
       unfold f;rewrite <- (H1 _ R'), H3;trivial.
       match goal with |- _ <= (if ?b then _ else _) => case_eq b;[ unfold fone;trivial | intros Heq] end.
       apply not_is_true_false in Heq.
       assert (W:= noDup_spec _ (@T.i_eqb_spec k (T.User BS_k))).
       rewrite <- is_true_negb, negb_involutive, W,  rev_append_rev  in Heq.
       destruct (NoDup_app_inv _ _ Heq) as (H0, _).
       apply Permutation_NoDup with (l' := map (@snd _ _) (m1 L)) in H0;rewrite <- W in H0.
       rewrite H0;trivial.
       apply Permutation_sym;apply Permutation_rev.
  apply Oeq_le;apply equiv_deno with Meq (kreq_mem (Vset.singleton L));trivial.
  apply equiv_trans with Meq (kreq_mem (Vset.singleton L)) (kreq_mem (Vset.singleton L))
     Ef (G0 ++ SR);auto. red;trivial. apply req_mem_trans.
    rewrite (app_nil_end G0) at 1.
    apply equiv_app with (kreq_mem (Vset.singleton L)).
    eqobs_in iEf. deadcode;union_mod.
    apply equiv_strengthen with (kreq_mem Vset.empty).
    intros k1 m1 m2 H1;apply req_mem_weaken with (2:= H1);vm_compute;trivial.
    apply equiv_lossless_Modify with Vset.empty Vset.empty Vset.empty (Vset.add yR (Vset.singleton R));trivial.
    apply lossless_nil.
    apply lossless_cons;[apply lossless_assign | ].
    apply lossless_while_equiv with (variant := q -! Elength R).
    apply is_lossless_correct with (pi := refl1_info iEf); vm_compute;trivial.
    intros n;eqobsrel_tail;unfold EP1, implMR, Meq;simpl;unfold O.eval_op;simpl;intros k1 m1 m2 (Heq, H1);subst.
    intros v _;rewrite is_true_andb in H1;destruct H1.
    apply nat_eqb_true in H1; apply leb_complete in H0;apply leb_correct.
    rewrite app_length;simpl length.
    rewrite <- H1.
    change (SwitchingSem.Sem.T.List) with T.List in *.
    change (SwitchingSem.Sem.T.User) with T.User in *.
    change (SwitchingSem.Sem.T.Pair) with T.Pair in *. 
    omega.
    apply modify_correct with (refl1_info iEf) Vset.empty;vm_compute;trivial.
    apply modify_correct with (refl1_info iEf) Vset.empty;vm_compute;trivial.
  change (G0 ++ SR) with (([L<-Nil _] ++ [b <c- A with {}])++SR);rewrite app_ass.
  apply equiv_trans_eq_mem_l with trueR Er ([L<-Nil _] ++ (SR ++ [b <c- A with {}])).
    rewrite proj1_MR;apply equiv_app with Meq.
    union_mod;[trivial | eqobs_in].
    set (sw_i := @add_sw_info_Adv
          SR XSR ISR Ef Er (SR_Modify _) (SR_Modify _) EqObs_SR IX_glob
          (@add_sw_info SR XSR ISR Ef Er (SR_Modify _) (SR_Modify _) EqObs_SR IX_glob
                      (fun _ _ => None) _ F swap_F) _ A _ _ _ _
          (EqAD _ _) (A_wf_E _)).
   apply check_swap_c_correct with XSR ISR sw_i.
   apply SR_Modify. apply SR_Modify. apply EqObs_SR. vm_compute;trivial.
  eqobs_tl iEr;ep.
  ep_eq_l (Elength (Nil (T.Pair (T.User BS_k) (T.User BS_k)))) 0%nat;trivial.
  deadcode;swap;eqobs_in.
  red;red;trivial.
 Qed.

End ADVERSARY.
