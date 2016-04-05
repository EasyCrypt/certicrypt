(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * Adversary.v : Well-formedness conditions for adversaries *)

Set Implicit Arguments.

Require Export Fundamental.


Module Make (SemO:SEM_OPT).
 
 Module Fund := Fundamental.Make_Fundamental_Lemma SemO.
 Export Fund.

 Module BProc.

  Record bproc : Type := 
   mkP {
    p_type : T.type;
    p_name : Proc.proc p_type
   }.

  Definition t := bproc.
  Definition eqb p1 p2 := Proc.eqb (p_name p1) (p_name p2).

  Lemma eqb_spec : forall p1 p2, if eqb p1 p2 then p1 = p2 else p1 <> p2.   
  Proof.
   intros (t1,f1) (t2,f2); generalize (Proc.eqb_spec_dep f1 f2); unfold eqb.
   simpl; destruct (Proc.eqb f1 f2); intros.
   inversion H; trivial.
   intros Heq; apply H; inversion Heq; trivial.
  Qed.
 
 End BProc.    
 
 Module ProcD  := MkEqBool_Leibniz BProc.
 Module PrSet  := MkListSet ProcD.
 Module PrSetP := MkSet_Theory PrSet.

 Section WF_ADV.

  Variables PrOrcl PrPriv: PrSet.t.

  Variables Gadv Gcomm : Vset.t.

  Hypothesis Ga_global : forall x, Vset.mem x Gadv -> Var.is_global x.
  Hypothesis Gc_global : forall x, Vset.mem x Gcomm -> Var.is_global x.

  Definition WFWrite x :=
   Var.is_global x -> Vset.mem x Gadv.

  Definition WFRead t (e:E.expr t) I :=
   forall x, Vset.mem x (fv_expr e) -> 
    Vset.mem x I \/ Vset.mem x Gadv \/ Vset.mem x Gcomm.
 
  Definition WFReadD t (d:E.support t) I :=
   forall x, Vset.mem x (fv_distr d) -> 
     Vset.mem x I \/ Vset.mem x Gadv \/ Vset.mem x Gcomm.

  Section DEF.

   Variable E : env.

   Definition add_read x I := if Var.is_global x then I else Vset.add x I.

   Inductive WFAdv_i : Vset.t -> I.t -> Vset.t -> Prop :=
   | GA_assign : forall I x e,
     WFWrite x ->
     WFRead e I ->
     WFAdv_i I (x <- e) (add_read x I)
   | GA_random : forall I x d,
     WFWrite x ->
     WFReadD d I ->
     WFAdv_i I (I.Instr (I.Random x d)) (add_read x I)
   | GA_cond : forall I e c1 c2 O1 O2,
     WFRead e I ->
     WFAdv_c I c1 O1 ->
     WFAdv_c I c2 O2 ->
     WFAdv_i I (If e then c1 else c2) (Vset.inter O1 O2)
   | GA_while : forall I e c O,
     WFRead e I ->
     WFAdv_c I c O ->
     WFAdv_i I (while e do c) I
   | GA_call_orcl : forall t (x:Var.var t) (f:Proc.proc t) (args:E.args (Proc.targs f)) I,
     PrSet.mem (BProc.mkP f) PrOrcl ->
     (forall t (e:E.expr t), DIn (P:=E.expr) t e args -> WFRead e I) ->
     WFWrite x ->
     WFAdv_i I (x <c- f with args) (add_read x I)
   | GA_call_adv : forall t (x:Var.var t) (f:Proc.proc t) (args:E.args (Proc.targs f)) I O,
     ~PrSet.mem (BProc.mkP f) PrOrcl -> 
     ~PrSet.mem (BProc.mkP f) PrPriv ->
     WFAdv_c (Vset_of_var_decl (proc_params E f)) (proc_body E f) O ->
     WFRead (proc_res E f) O ->
     (forall t (e:E.expr t), DIn (P:=E.expr) t e args -> WFRead e I) ->
     WFWrite x ->
     WFAdv_i I (x <c- f with args) (add_read x I)
     
   with WFAdv_c : Vset.t -> cmd -> Vset.t -> Prop :=
   | GA_nil : forall I, WFAdv_c I nil I
   | GA_cons : forall I IO O i c,
     WFAdv_i I i IO ->
     WFAdv_c IO c O ->
     WFAdv_c I (i::c) O.

   Scheme WFAdv_c_prop := Induction for WFAdv_c Sort Prop
    with WFAdv_i_prop := Induction for WFAdv_i Sort Prop.

   Definition WFAdv t (f:Proc.proc t) :=
    exists O, 
     WFAdv_c  (Vset_of_var_decl (proc_params E f)) (proc_body E f) O /\
     WFRead (proc_res E f) O.

   Lemma add_read_subset : forall x I, I [<=] add_read x I.
   Proof. 
    unfold add_read; intros x I; destruct (Var.is_global x); auto with set. 
   Qed.

   Lemma add_read_local : forall x I, 
    (forall y, Vset.mem y I -> Var.is_local y) ->
    forall y, Vset.mem y (add_read x I) -> Var.is_local y.
   Proof.
    unfold add_read; intros x I H y; case_eq (Var.is_global x); auto.
    rewrite VsetP.add_spec; intros Heq [H1 | H1]; auto.
    rewrite <- (H1:x=y); unfold Var.is_local; rewrite Heq; trivial.
   Qed.

   Lemma WFAdv_i_subset : forall I i O, WFAdv_i I i O -> I [<=] O.
   Proof.
    induction 1 using WFAdv_i_prop with 
     (P:=fun I (c:cmd) O (H:WFAdv_c I c O) => I [<=] O);
    auto using add_read_subset with set.
    apply VsetP.subset_trans with IO; trivial.
    rewrite <- (VsetP.inter_idem I); auto with set.
    apply VsetP.subset_inter_ctxt; trivial.
   Qed.
   
   Lemma WFAdv_c_subset :  forall I c O, WFAdv_c I c O -> I [<=] O.
   Proof.
    induction 1; auto with set.
    apply VsetP.subset_trans with IO; trivial.
    apply WFAdv_i_subset with (1:= H).
   Qed.

   Lemma WFAdv_i_local : forall I i O, WFAdv_i I i O ->
    (forall x, Vset.mem x I -> Var.is_local x) -> 
    forall x, Vset.mem x O -> Var.is_local x.
   Proof.
    induction 1 using WFAdv_i_prop with 
     (P:=fun I (c:cmd) O (H:WFAdv_c I c O) =>
      (forall x, Vset.mem x I -> Var.is_local x) -> 
      forall x, Vset.mem x O -> Var.is_local x);
     eauto using add_read_local; intros.
    rewrite VsetP.inter_spec in H0; destruct H0; eauto.
   Qed.

   Lemma WFAdv_c_local : forall I c O, WFAdv_c I c O ->
    (forall x, Vset.mem x I -> Var.is_local x) -> 
    forall x, Vset.mem x O -> Var.is_local x.
   Proof.
    induction 1; auto; intros.
    apply IHWFAdv_c; trivial.
    intros; apply WFAdv_i_local with (1:= H); trivial.
   Qed.
  
  End DEF.

 
  Section TRANS.

   Variable E1 E2 : env.
  
   Definition Eq_orcl_params := forall t (o:Proc.proc t), 
    PrSet.mem (BProc.mkP o) PrOrcl -> proc_params E1 o = proc_params E2 o.

   Definition Eq_adv_decl :=
    forall t (f:Proc.proc t),
     ~ PrSet.mem (BProc.mkP f) PrOrcl -> 
     ~ PrSet.mem (BProc.mkP f) PrPriv ->
     proc_params E1 f = proc_params E2 f /\
     proc_body E1 f = proc_body E2 f /\
     proc_res E1 f = proc_res E2 f.

   Lemma WFAdv_c_trans : 
    Eq_orcl_params -> 
    Eq_adv_decl ->
    forall I c O,
     WFAdv_c E1 I c O -> WFAdv_c E2 I c O.
   Proof.
    intros Ho Ha; induction 1 using WFAdv_c_prop with
     (P0:=fun I i O (_:WFAdv_i E1 I i O) => WFAdv_i E2 I i O);
     try (econstructor; eauto; fail).
    destruct (Ha _ _ n n0) as (H1,(H2,H3)). 
    apply GA_call_adv with O; auto. 
    rewrite <- H1, <-H2; auto. 
    rewrite <- H3; auto.
   Qed.

   Lemma WFAdv_trans : 
    Eq_orcl_params -> 
    Eq_adv_decl ->
    forall t (adv:Proc.proc t),
     ~PrSet.mem (BProc.mkP adv) PrOrcl -> 
     ~PrSet.mem (BProc.mkP adv) PrPriv ->
     WFAdv E1 adv -> WFAdv E2 adv.
   Proof.
    intros Ho Ha t adv Hm1 Hm2  (O, (H1, H2));
     destruct (Ha _ _ Hm1 Hm2) as (H3, (H4,H5));
      exists O; split; trivial. 
    rewrite <- H3,<-H4; apply WFAdv_c_trans; trivial.
    rewrite <- H5; trivial.
   Qed.

  End TRANS.


  Section REFL_INFO.

   Variable E : env.
   Variable pi : eq_refl_info E.

   Definition mod_adv :=
    PrSet.fold (fun f res =>
     match res, pi (BProc.p_name f) with
     | Some res, Some pif => Some (Vset.union (pi_mod pif) res)
     | _, _ => None
     end) PrOrcl (Some Gadv).
   
   Lemma mod_adv_global : forall X,
    mod_adv = Some X ->
    forall x, Vset.mem x X -> Var.is_global x.
   Proof. 
    unfold mod_adv; rewrite PrSet.fold_spec.
    generalize (PrSet.elements PrOrcl) Gadv Ga_global.
    induction l; simpl; intros.
    inversion H; clear H; subst; auto.
    destruct (pi (BProc.p_name a)) as [pif | _ ].
    apply IHl with (2:= H); trivial.
    intros x0; rewrite VsetP.union_spec; intros [H1 | H1]; 
     auto using (mod_global pif).      
    generalize l H.
    induction l0; simpl; intros; auto; try discriminate.
   Qed.

   Lemma mod_adv_incl : forall X,
    mod_adv = Some X ->
    Gadv [<=] X /\ 
    forall f, PrSet.mem f PrOrcl -> 
     exists pif, pi (BProc.p_name f) = Some pif /\ (pi_mod pif) [<=] X.
   Proof. 
    unfold mod_adv; rewrite PrSet.fold_spec. 
    intros X; assert (forall l R, 
     fold_left
     (fun (x : option Vset.t) (a : ProcD.t) =>
      match x with
      | Some res => 
        match pi (BProc.p_name a) with
        | Some pif => Some (Vset.union (pi_mod pif) res)
        | None => None 
        end
      | None => None
      end) l (Some R) = Some X ->
     R [<=] X /\
     (forall f, InA (@eq _) f l -> 
      exists pif, pi  (BProc.p_name f) = Some pif /\ (pi_mod pif) [<=] X)).
    induction l; simpl; intros.
    injection H; clear H; intros; subst; split; intros; auto with set.
    inversion H.
    case_eq (pi (BProc.p_name a)); 
     [intros pia Heq | intros Heq]; rewrite Heq in H.
    destruct (IHl _ H); split; auto.
    apply VsetP.subset_trans with (2:= H0); auto with set.
    intros f Hin; inversion Hin; clear Hin; intros; subst.
    exists pia; split; auto.
    apply VsetP.subset_trans with (2:= H0); auto with set.
    eapply H1; eauto.
    elimtype False. 
    generalize l H; clear IHl H l Heq.
    induction l; simpl; intros; try discriminate; auto.
    intros H1; destruct (H _ _ H1); split; auto.
    intros; apply H2; auto.
    apply PrSet.elements_correct; auto.
   Qed.
   
   Lemma mod_adv_write : forall x X,  
    mod_adv = Some X ->
    WFWrite x ->
    Var.is_global x ->
    Vset.singleton x [<=] X.
   Proof.
    intros x X Heq; destruct (mod_adv_incl Heq).
    unfold WFWrite,add_read; intros.
    apply VsetP.subset_trans with Gadv; trivial.
    apply Vset.subset_complete; intros.
    apply Vset.singleton_complete in H3; rewrite <- (H3:x = x0); auto.
   Qed.
 
   Lemma union_union_same : forall X Li Lc,
    Vset.union (Vset.union X Li) (Vset.union X Lc) [=]
    Vset.union X (Vset.union Li Lc).
   Proof.
    intros; rewrite VsetP.union_assoc. 
    rewrite (VsetP.union_sym X Lc), <- (VsetP.union_assoc Li).
    rewrite (VsetP.union_sym (Vset.union Li Lc)), <- VsetP.union_assoc.
    rewrite VsetP.union_idem; auto with set.
   Qed.

   Lemma get_global_union : forall X Lf,
    mod_adv = Some X ->
    (forall x : VarP.Edec.t, Vset.mem x Lf -> Var.is_local x) ->
    get_globals (Vset.union Lf X) [=] X.
   Proof.
    intros X Lf Heq HL.
    assert (W:= mod_adv_global Heq).
    rewrite VsetP.eq_spec; split; apply Vset.subset_complete; intros.
    assert (W1:=Vset.subset_correct (get_globals_subset (Vset.union Lf X)) _ H).
    rewrite VsetP.union_spec in W1; destruct W1; trivial.
    absurd (Var.is_global x).
    assert (W1:= HL _ H0).
    unfold Var.is_local in W1; intro H1; rewrite H1 in W1; discriminate.
    apply (get_globals_spec _ _ H).
    apply get_globals_complete; auto with set.
   Qed.

   Lemma mod_adv_correct : forall X, 
    mod_adv = Some X ->
    forall I c O, WFAdv_c E I c O -> 
     exists L, (forall x, Vset.mem x L -> Var.is_local x) /\ 
      Modify E (Vset.union L X) c. 
   Proof.
    intros X Heq; destruct (mod_adv_incl Heq).
    induction 1 using WFAdv_c_prop with
     (P0:=fun I i O (_:WFAdv_i E I i O) =>
      exists L, (forall x, Vset.mem x L -> Var.is_local x) /\ 
       Modify E (Vset.union L X) [i]).
    exists Vset.empty; split.
    intros x W; elim (Vset.empty_spec W).
    eapply Modify_weaken;[apply Modify_nil|]; auto with set.
    destruct IHWFAdv_c as (Li, (H2,H3)); destruct IHWFAdv_c0 as [Lc [H4 H5] ].
    exists (Vset.union Lc Li); split; intros.
    rewrite VsetP.union_spec in H6; destruct H6; auto.
    rewrite VsetP.union_sym, <- union_union_same, VsetP.union_sym.
    repeat rewrite (VsetP.union_sym X).
    apply Modify_cons with (1:= H3) (2:= H5).
    case_eq (Var.is_global x); intros; 
     [exists Vset.empty | exists (Vset.singleton x)]; split; intros.
    elim (Vset.empty_spec H2).
    eapply Modify_weaken;[apply Modify_assign|].
    apply VsetP.subset_trans with X; auto with set.
    destruct x; simpl Var.btype ; auto using mod_adv_write with set.
    apply Vset.singleton_complete in H2; 
     rewrite <- (H2: x = x0); unfold Var.is_local; rewrite H1; trivial.
    eapply Modify_weaken;
     [apply Modify_assign|]; destruct x; simpl Var.btype; auto with set.
    case_eq (Var.is_global x); intros;
     [exists Vset.empty | exists (Vset.singleton x)]; split; intros.
    elim (Vset.empty_spec H2).
    eapply Modify_weaken;[apply Modify_random|].
    destruct x; simpl Var.btype.
    apply VsetP.subset_trans with X; auto using mod_adv_write with set.
    apply Vset.singleton_complete in H2; 
     rewrite <- (H2: x = x0); unfold Var.is_local; rewrite H1; trivial.
    eapply Modify_weaken;
     [apply Modify_random | ]; destruct x; simpl Var.btype; auto with set.
    destruct IHWFAdv_c1 as (L1, (H2,H3)); destruct IHWFAdv_c2 as [L2 [H4 H5] ].
    exists (Vset.union L1 L2); split; intros.
    rewrite VsetP.union_spec in H1; destruct H1; auto.
    rewrite VsetP.union_sym, <- union_union_same.
    repeat rewrite (VsetP.union_sym X).
    apply Modify_cond with (1:= H3) (2:= H5).
    destruct IHWFAdv_c as (L, (H2,H3)).
    exists L; split; auto.
    apply Modify_while; trivial.

    (* Call Orcl *)
    destruct (H0 _ i) as (pif, (Hpif, Hsub)).
    case_eq (Var.is_global x); intros;
     [exists Vset.empty | exists (Vset.singleton x)]; split; intros.
    elim (Vset.empty_spec H2).
    eapply Modify_weaken;[apply (mod_spec_call pif)|].
    apply VsetP.subset_trans with (Vset.add x X).
    apply VsetP.subset_add_ctxt; trivial.
    rewrite VsetP.add_idem; auto with set.
    apply Vset.subset_correct with (1:=mod_adv_write Heq w0 H1); auto with set.
    apply Vset.singleton_complete in H2; 
     rewrite <- (H2: Var.mkV x = x0); unfold Var.is_local; rewrite H1; trivial.
    rewrite VsetP.union_sym.
    eapply Modify_weaken;[apply (mod_spec_call pif)|].
    rewrite VsetP.union_sym.
    apply VsetP.subset_trans with (Vset.add x X); 
     auto using VsetP.subset_add_ctxt with set.

    (* Call Adv *)
    destruct IHWFAdv_c as (Lf,(H2,H3)).
    case_eq (Var.is_global x); intros;
     [exists Vset.empty | exists (Vset.singleton x)]; split; intros.
    elim (Vset.empty_spec H5).
    eapply Modify_weaken;[apply Modify_call with (1:= H3)|].
    rewrite get_global_union; trivial.
    apply VsetP.subset_trans with (Vset.add x X).
    apply VsetP.subset_add_ctxt; auto with set.
    rewrite VsetP.add_idem; auto with set.
    apply Vset.subset_correct with (1:=mod_adv_write Heq w1 H4); auto with set.
    apply Vset.singleton_complete in H5; 
     rewrite <- (H5: Var.mkV x = x0); unfold Var.is_local; rewrite H4; trivial.
    rewrite VsetP.union_sym.
    eapply Modify_weaken;[apply Modify_call with (1:= H3)|].
    rewrite get_global_union; trivial.
    rewrite VsetP.union_sym.
    apply VsetP.subset_trans with (Vset.add x X); 
     auto using VsetP.subset_add_ctxt with set.
   Qed.
   
   Lemma mod_adv_spec : forall X, 
    mod_adv = Some X ->
    forall t (f:Proc.proc t), WFAdv E f -> 
     forall (x:Var.var t) args, Modify E (Vset.add x X) [x <c- f with args].
   Proof.
    intros X Heq t f [O [H H0] ] x args.
    destruct (mod_adv_correct Heq H) as [L [H1 H2] ].
    eapply Modify_weaken;[apply Modify_call with (1:= H2)|].
    rewrite get_global_union; auto with set.
   Qed.
   
   Definition input_Adv :=
    PrSet.fold (fun f res =>
     match res, pi (BProc.p_name f) with
     | Some res, Some pif => Some (Vset.union (pi_input pif) res)
     | _, _ => None
     end) PrOrcl (Some (Vset.union Gadv Gcomm)).
   
   Section EQ_OBS.
    
    Variable IA : Vset.t.
  
    Hypothesis IA_def : input_Adv = Some IA.

    Lemma input_Adv_global : forall x, Vset.mem x IA -> Var.is_global x.
    Proof.
     generalize IA_def; unfold input_Adv.
     rewrite PrSet.fold_spec.
     assert (forall x, Vset.mem x (Vset.union Gadv Gcomm) -> Var.is_global x).
     intros x; rewrite VsetP.union_spec; intros [H | H]; auto.
     generalize (PrSet.elements PrOrcl) (Vset.union Gadv Gcomm) H; clear H.
     induction l; simpl; intros.
     apply H; inversion IA_def0; trivial.
     destruct (pi (BProc.p_name a)).
     apply IHl with (2:= IA_def0); trivial.
     intros x0; rewrite VsetP.union_spec; intros [H1 | H1]; 
      auto using (input_global p).
     generalize l IA_def0; clear IHl IA_def0 l.
     induction l; simpl; intros; try discriminate; auto.
    Qed.

    Lemma input_Adv_subset : 
     Gcomm [<=] IA /\
     Gadv [<=] IA /\
     forall t (f:Proc.proc t) pif, 
      PrSet.mem (BProc.mkP f) PrOrcl -> 
      pi f = Some pif ->
      (pi_input pif) [<=] IA.
    Proof.
     unfold input_Adv in IA_def.
     rewrite PrSet.fold_spec in IA_def. 
     assert (forall l X,
      fold_left
      (fun x a =>
       match x with
       | Some res =>
         match pi (BProc.p_name a) with
         | Some pif => Some (Vset.union (pi_input pif) res)
         | None => None (A:=Vset.t)
         end
       | None => None (A:=Vset.t)
       end) l (Some X) = Some IA ->
      X [<=] IA /\ 
      forall (f : ProcD.t) (pif : proc_eq_refl_info E (BProc.p_name f)),
       InA (@eq _) f l -> 
       pi (BProc.p_name f) = Some pif -> pi_input pif [<=] IA).
     induction l; simpl; intros; trivial.
     inversion H; split; intros; auto with set.
     inversion H0.
     generalize H; clear H; case_eq (pi (BProc.p_name a)); intros.
     destruct (IHl _ H0); split.
     apply VsetP.subset_trans with (2 := H1); auto with set.
     intros f pif Hin; inversion Hin; intros; auto; subst.
     rewrite H in H6; inversion H6; subst.
     apply VsetP.subset_trans with (2 := H1); auto with set.
     elimtype False; generalize l H0; clear IHl H0 l.
     induction l; simpl; intros; try discriminate; auto.
     destruct (H _ _ IA_def).
     split.
     apply VsetP.subset_trans with (2:= H0); auto with set.
     split.
     apply VsetP.subset_trans with (2:= H0); auto with set.
     intros; apply H1 with (f := BProc.mkP f); trivial.
     apply PrSet.elements_correct; trivial.
    Qed.

    Hypothesis pi_def : forall o, 
     PrSet.mem o PrOrcl -> exists pio, pi (BProc.p_name o) = Some pio.
    
    Hypothesis input_orcl_pre : forall o pio, 
     PrSet.mem o PrOrcl -> pi (BProc.p_name o) = Some pio ->
     forall x, Vset.mem x IA -> 
      Vset.mem x (pi_mod pio) -> Vset.mem x (pi_output pio).
    
    Lemma equiv_WFRead : forall t (e:E.expr t) I k (m1 m2:Mem.t k), 
     WFRead e I -> 
     Gcomm[<=]IA ->
     Gadv[<=]IA -> 
     m1 =={ Vset.union IA I}m2 ->
     E.eval_expr e m1 = E.eval_expr e m2.
    Proof.
     intros; apply EqObs_e_fv_expr.
     apply req_mem_weaken with (2:= H2).
     unfold WFRead in H; apply Vset.subset_complete; intros.
     apply Vset.subset_correct with (Vset.union (Vset.union Gadv Gcomm) I).
     rewrite <- (VsetP.union_idem IA); 
      repeat apply VsetP.subset_union_ctxt; auto with set.
     repeat rewrite VsetP.union_spec; destruct (H _ H3); tauto.
    Qed.

    Lemma equiv_WFWrite : forall k t (x:Var.var t) v I (m1 m2:Mem.t k), 
     m1 =={ Vset.union IA I} m2 ->
     m1 {!x <-- v!} =={ Vset.union IA (add_read x I)} m2 {!x <-- v!}.
    Proof.
     intros k t x; unfold add_read.
     case_eq (Var.is_global x); intros; red; intros.
     destruct (Var.eq_dec x x0).
     inversion e; simpl; repeat rewrite Mem.get_upd_same; trivial.
     repeat rewrite Mem.get_upd_diff; trivial; auto.
     destruct (Var.eq_dec x x0).
     inversion e; simpl; repeat rewrite Mem.get_upd_same; trivial.
     repeat rewrite Mem.get_upd_diff; trivial; auto.
     rewrite VsetP.union_spec, VsetP.add_spec in H1; destruct H1; auto with set.
     destruct H1; auto with set.
     elim (n H1).
    Qed.

    Lemma get_arg_some : forall t (x:Var.var t) e tv (lv:var_decl tv) 
     te (le:E.args te), get_arg x lv le = Some e -> DIn t e le.
    Proof.
     induction lv; simpl; intros; try discriminate.
     destruct le; try discriminate.
     case_eq (get_arg x lv le); intros.
     rewrite H0 in H; inversion H; simpl; subst; auto.
     rewrite H0 in H. 
     generalize H; clear H; case_eq (Var.veqb x p).
     case_eq (T.eq_dec a0 t); try (intros; discriminate).
     intros e1; generalize e1 e e0; rewrite e1.
     intros e2; rewrite (T.UIP_refl e2); intros.
     injection H2; intros.
     rewrite H3; constructor; trivial.
     intros; discriminate.
    Qed.

    Lemma WFAdv_c_EqObs : forall I c O, 
     WFAdv_c E I c O -> 
     (forall x, Vset.mem x I -> Var.is_local x) -> 
     EqObs (Vset.union IA I) E c E c (Vset.union IA O).
    Proof.
     destruct input_Adv_subset as (Hcomm,(Hadv, Horcl)).
     induction 1 using WFAdv_c_prop with
      (P0:= fun I i O (_:WFAdv_i E I i O) =>
       (forall x, 
        Vset.mem x I -> 
        Var.is_local x) -> 
       EqObs (Vset.union IA I) E [i] E [i] (Vset.union IA O));
      unfold EqObs in *; intros.
     apply equiv_nil.
     apply equiv_cons with (1:= IHWFAdv_c H0); eauto using WFAdv_i_local.
     eapply equiv_strengthen;[ | apply equiv_assign].
     unfold upd_para, kreq_mem; intros; simpl.
     rewrite (equiv_WFRead w0 Hcomm Hadv H0).
     destruct x; apply equiv_WFWrite; trivial.
     eapply equiv_strengthen;[ | apply equiv_random].
     unfold forall_random,kreq_mem; intros; simpl; split.
     unfold eq_support.
     apply EqObs_d_fv_expr.
     apply req_mem_weaken with (2:= H0).
     unfold WFReadD in w0; apply Vset.subset_complete; intros.
     apply Vset.subset_correct with (Vset.union (Vset.union Gadv Gcomm) I).
     rewrite <- (VsetP.union_idem IA); 
      repeat apply VsetP.subset_union_ctxt; auto with set.
     repeat rewrite VsetP.union_spec; destruct (w0 _ H1); tauto.
     destruct x; intros; apply equiv_WFWrite; trivial.
     apply equiv_cond.
     eapply equiv_strengthen; 
      [ | eapply equiv_weaken; [ | apply (IHWFAdv_c1 H1)] ].
     unfold kreq_mem; intros k m1 m2 (W, _); trivial.
     unfold kreq_mem; intros k m1 m2 W; apply req_mem_weaken with (2:= W).
     apply VsetP.subset_union_ctxt; auto with set.
     eapply equiv_strengthen; 
      [ | eapply equiv_weaken; [ | apply (IHWFAdv_c2 H1)] ].
     unfold kreq_mem; intros k m1 m2 (W, _); trivial.
     unfold kreq_mem; intros k m1 m2 W; apply req_mem_weaken with (2:= W).
     apply VsetP.subset_union_ctxt; auto with set.
     unfold kreq_mem; intros k m1 m2 W.
     rewrite  (equiv_WFRead w Hcomm Hadv W); trivial.
     eapply equiv_weaken; [ | apply equiv_while].
     unfold kreq_mem; intros k m1 m2 (W, _); trivial.
     unfold kreq_mem; intros k m1 m2 W.
     rewrite  (equiv_WFRead w Hcomm Hadv W); trivial.
     eapply equiv_strengthen;[ | apply equiv_weaken with (2:=IHWFAdv_c H0)].
     unfold kreq_mem; intros k m1 m2 (W, _); trivial.
     unfold kreq_mem; intros k m1 m2 W; apply req_mem_weaken with (2:= W).
     apply VsetP.subset_union_ctxt; auto with set.
     apply WFAdv_c_subset with E c; trivial.

     (* Call Orcl *)
     destruct (pi_def _ i) as (pif, Hdef).
     eapply equiv_weaken;[ | apply pi_spec_call with (pi:=pif)].
     unfold kreq_mem; red; intros.
     rewrite VsetP.union_spec in H1; destruct H1. 
     apply H0; rewrite VsetP.union_spec, VsetP.diff_spec.
     rewrite VsetP.union_spec; 
      destruct (VsetP.mem_dec x0 (pi_mod pif)); try tauto.
     left; rewrite VsetP.add_spec; right; eapply input_orcl_pre; eauto.
     generalize H1; unfold add_read; clear H1.
     case_eq (Var.is_global x); intros.
     apply H0; rewrite VsetP.union_spec, VsetP.diff_spec.
     rewrite VsetP.union_spec; 
      destruct (VsetP.mem_dec x0 (pi_mod pif)); try tauto.
     apply H in H2; unfold Var.is_local in H2.
     apply mod_global in i0; rewrite i0 in H2; discriminate.
     apply H0; rewrite VsetP.add_spec in H2; 
      rewrite VsetP.union_spec, VsetP.add_spec; destruct H2; try tauto.
     rewrite VsetP.diff_spec, VsetP.union_spec.
     destruct (VsetP.mem_dec x0 (pi_mod pif)); try tauto.
     apply H in H2; unfold Var.is_local in H2.
     apply mod_global in i0; rewrite i0 in H2; discriminate.
     red; intros.
     assert (forall ta (args0:E.args ta), 
      ta = (Proc.targs f) -> 
      exists e, get_arg x0 (proc_params E f) args0 = Some e).
     apply  Vset_of_var_decl_ind with (P:= fun t0 x0 => 
      forall ta (args0:E.args ta), ta = (Proc.targs f) ->
       exists e0 : E.expr t0, get_arg x0 (proc_params E f) args0 = Some e0)
     (lv:= proc_params E f) .
     generalize (Proc.targs f) (proc_params E f). 
     induction v; simpl; intros.
     elim H1.
     destruct args0; try discriminate.
     injection H2; clear H2; intros; subst.
     destruct H1.
     inversion H1; subst.
     assert (W:= T.inj_pair2 H5); clear H1 H4 H5; subst.
     destruct (get_arg p v args0); eauto.
     generalize (Var.veqb_spec p p); destruct (Var.veqb p p); intros.
     case_eq (T.eq_dec a a); intros.
     rewrite (T.UIP_refl e0); eauto.
     elim (T.eq_dec_r H2); trivial.
     elim H1; trivial.
     destruct (IHv _ _ H1 _ args0 (refl_equal _)).
     rewrite H2; eauto.
     apply Vset.subset_correct with (2:= H0).
     apply params_subset.
     simpl; destruct (H1 _ args (refl_equal _)) as (e0, Heq); rewrite Heq.
     red; intros.
     assert (W:= get_arg_some _ _ _ Heq).   
     apply equiv_WFRead with (1:= w _ _ W); auto.
     apply VsetP.subset_trans with (1:= Horcl _ _ _ i Hdef); auto with set.

     (* Call Adv *)
     assert (W:forall t (x:Var.var t), 
      Vset.mem x (Vset_of_var_decl (proc_params E f)) -> Var.is_local x).
     intros; apply Vset_of_var_decl_ind with 
      (P:= fun t (x:Var.var t) => Var.is_local x) (lv:= proc_params E f); auto.
     intros; change (Var.vis_local x1).
     apply proc_params_local with E t f; trivial.
     assert (forall x, 
      Vset.mem x (Vset_of_var_decl (proc_params E f)) -> Var.is_local x). 
     intros (t0,x0); auto.
     clear W.
     apply  equiv_call with (3:= IHWFAdv_c H1).
     unfold kreq_mem; red; intros.
     rewrite VsetP.union_spec in H3; destruct H3. 
     repeat rewrite init_mem_global; auto using input_Adv_global.
     apply H2; auto with set.
     apply init_mem_local; auto.
     generalize args w0.
     generalize (Proc.targs f). induction args0; simpl; auto; intros.
     rewrite IHargs0; auto.
     rewrite (@equiv_WFRead a p I k m1 m2); auto.
     unfold kreq_mem; red; intros. 
     destruct (Var.eq_dec x x0).
     inversion e; simpl.
     repeat rewrite return_mem_dest.
     apply equiv_WFRead with (1 := w); auto.
     rewrite VsetP.union_spec in H4; destruct H4. 
     repeat rewrite return_mem_global; auto using input_Adv_global.
     apply H3; auto with set.
     assert (Vset.mem x0 I). 
     unfold add_read in H4; destruct (Var.is_global x); auto.
     rewrite VsetP.add_spec in H4; destruct H4; trivial.
     elim (n1 H4).
     repeat rewrite return_mem_local; auto. 
     apply H2; auto with set.
    Qed.

    Variable MA : Vset.t.
  
    Hypothesis MA_def : mod_adv = Some MA. 
    
    Definition output_adv := Vset.inter IA MA.
    
    Lemma WFAdv_EqObs : forall t (f:Proc.proc t), WFAdv E f ->
     exists ls, 
      (forall x, Vset.mem x ls -> Var.is_local x) /\ 
      EqObs (Vset.union IA (Vset_of_var_decl (proc_params E f)))
      E (proc_body E f) E (proc_body E f) (Vset.union ls output_adv) /\ 
      EqObs_e (Vset.union (Vset.union ls output_adv) (Vset.diff IA MA))
      (proc_res E f) (proc_res E f).
    Proof.
     intros t f (O,(H1,H2)).
     exists O; split.
     intros; apply WFAdv_c_local with (1:= H1); trivial.
     intros (t0, x0) H0.
     apply  Vset_of_var_decl_ind with 
      (P:=fun t (x:Var.var t) => Var.is_local x) (lv:=proc_params E f); trivial.
     intros; change (Var.vis_local x1).
     apply proc_params_local with E t f; trivial.
     split.
     unfold EqObs; eapply equiv_weaken;[ | apply WFAdv_c_EqObs with (1:=H1)].
     unfold kreq_mem; intros; rewrite VsetP.union_sym.
     apply req_mem_weaken with (2:= H).
     apply VsetP.subset_union_ctxt; unfold output_adv; auto with set.
     intros (t0, x0) H0.
     apply  Vset_of_var_decl_ind with 
      (P:=fun t (x:Var.var t) => Var.is_local x) (lv:=proc_params E f); trivial.
     intros; change (Var.vis_local x).
     apply proc_params_local with E t f; trivial.
     red; intros.
     destruct input_Adv_subset as (Hcomm,(Hadv, Horcl)).
     apply equiv_WFRead with (1 := H2); auto.
     apply req_mem_weaken with (2:= H).
     rewrite VsetP.union_assoc, VsetP.union_sym.
     apply VsetP.subset_union_ctxt; auto with set.
     unfold output_adv; apply Vset.subset_complete; intros.
     rewrite VsetP.union_spec,VsetP.diff_spec, VsetP.inter_spec.
     destruct (VsetP.mem_dec x MA); auto with set.
    Qed.

   End EQ_OBS.

  End REFL_INFO.


  Section INFO.

   Variable inv : mem_rel.
   Variables E1 E2 : env.
   Variables X1 X2 : Vset.t.
   Variable pii : eq_inv_info_o inv E1 E2.
   
   Hypothesis inv_dep : depend_only_rel inv X1 X2.

   Hypothesis inv_global : forall x, 
    Vset.mem x (Vset.union X1 X2) -> Var.is_global x.

   Hypothesis inv_dec : forall k (m1 m2:Mem.t k), sumbool (inv m1 m2) (~inv m1 m2).

   Hypothesis disjoint_Orcl1 : Vset.disjoint X1 Gadv.

   Hypothesis disjoint_Orcl2 : Vset.disjoint X2 Gadv.

   Hypothesis Eq_adv_decl_12 : Eq_adv_decl E1 E2.

   Hypothesis Eq_orcl_params_12: Eq_orcl_params E1 E2.

   Definition iinput_Adv :=
    PrSet.fold (fun f res =>
     match res, pii (BProc.p_name f) with
     | Some res, Some pif => Some (Vset.union (pii_input pif) res)
     | _, _ => None
     end) PrOrcl (Some (Vset.union Gadv Gcomm)).


   Section EQ_OBS_INV.
    
    Variable IA : Vset.t.

    Hypothesis IA_def : iinput_Adv = Some IA.

    Lemma iinput_Adv_global : forall x, Vset.mem x IA -> Var.is_global x.
    Proof.
     generalize IA_def; unfold iinput_Adv.
     rewrite PrSet.fold_spec.
     assert (forall x, Vset.mem x (Vset.union Gadv Gcomm) -> Var.is_global x).
     intros x; rewrite VsetP.union_spec; intros [H | H]; auto.
     generalize (PrSet.elements PrOrcl) (Vset.union Gadv Gcomm) H; clear H.
     induction l; simpl; intros.
     apply H; inversion IA_def0; trivial.
     destruct (pii (BProc.p_name a)).
     apply IHl with (2:= IA_def0); trivial.
     intros x0; rewrite VsetP.union_spec; intros [H1 | H1]; 
      auto using (iinput_global p).
     generalize l IA_def0; clear IHl IA_def0 l.
     induction l; simpl; intros; try discriminate; auto.
    Qed.
  
    Lemma iinput_Adv_subset : 
     Gcomm [<=] IA /\
     Gadv [<=] IA /\
     forall t (f:Proc.proc t) pif, 
      PrSet.mem (BProc.mkP f) PrOrcl -> 
      pii f = Some pif -> 
      (pii_input pif) [<=] IA.
    Proof.
     unfold iinput_Adv in IA_def.
     rewrite PrSet.fold_spec in IA_def. 
     assert (forall l X,
      fold_left
      (fun (x : option Vset.t) (a : ProcD.t) =>
       match x with
       | Some res =>
         match pii (BProc.p_name a) with
         | Some pif => Some (Vset.union (pii_input pif) res)
         | None => None (A:=Vset.t)
         end
       | None => None (A:=Vset.t)
       end) l (Some X) = Some IA ->
      X [<=] IA /\ 
      forall (f : ProcD.t) (pif : proc_eq_inv_info inv E1 E2 (BProc.p_name f)),
       InA (@eq _) f l -> 
       pii (BProc.p_name f) = Some pif -> 
       pii_input pif [<=] IA).
     induction l; simpl; intros; trivial.
     inversion H; split; intros; auto with set.
     inversion H0.
     generalize H; clear H; case_eq (pii (BProc.p_name a)); intros.
     destruct (IHl _ H0); split.
     apply VsetP.subset_trans with (2 := H1); auto with set.
     intros f pif Hin; inversion Hin; intros; auto; subst.
     rewrite H in H6; inversion H6; subst.
     apply VsetP.subset_trans with (2 := H1); auto with set.
     elimtype False; generalize l H0; clear IHl H0 l.
     induction l; simpl; intros; try discriminate; auto.
     destruct (H _ _ IA_def).
     split.
     apply VsetP.subset_trans with (2:= H0); auto with set.
     split.
     apply VsetP.subset_trans with (2:= H0); auto with set.
     intros; apply H1 with (f := BProc.mkP f); trivial.
     apply PrSet.elements_correct; trivial.
    Qed.

    Hypothesis pi_def : forall o, 
     PrSet.mem o PrOrcl -> exists pio, pii (BProc.p_name o) = Some pio.

    Hypothesis input_orcl_pre : 
     forall o pio, PrSet.mem o PrOrcl -> pii (BProc.p_name o) = Some pio ->
      forall x, Vset.mem x IA -> 
       Vset.mem x (pi_mod (pi_eq_refl1 pio)) \/
       Vset.mem x (pi_mod (pi_eq_refl2 pio)) -> Vset.mem x (pii_output pio).

    Lemma WFAdv_c_EqObsInv : forall I c O,  
     WFAdv_c E1 I c O ->
     (forall x, Vset.mem x I -> Var.is_local x) -> 
     EqObsInv inv (Vset.union IA I) E1 c E2 c (Vset.union IA O).
    Proof.
     destruct iinput_Adv_subset as (Hcomm,(Hadv, Horcl)).
     induction 1 using WFAdv_c_prop with
      (P0:= fun I i O (_:WFAdv_i E1 I i O) =>
       (forall x, Vset.mem x I -> Var.is_local x) -> 
       EqObsInv inv (Vset.union IA I) E1 [i] E2 [i] (Vset.union IA O));
      unfold EqObsInv in *; intros.
     apply equiv_nil.
     apply equiv_cons with (1:= IHWFAdv_c H0); eauto using WFAdv_i_local.
     eapply equiv_strengthen;[ | apply equiv_assign].
     intros k m1 m2 (H1, H2); split; unfold kreq_mem in *.
     rewrite (equiv_WFRead w0 Hcomm Hadv H1).
     destruct x; apply equiv_WFWrite; trivial.
     apply inv_dep with m1 m2; trivial;
     red; intros; rewrite Mem.get_upd_diff; trivial; intro.
     assert (W: Var.is_global x0) by auto with set.
     contradict H0. 
     apply VsetP.disjoint_mem_not_mem with 
      (1:=VsetP.disjoint_sym disjoint_Orcl1).
     generalize W; rewrite <- H3; auto; destruct x; auto.
     assert (W: Var.is_global x0) by auto with set.
     contradict H0. 
     apply VsetP.disjoint_mem_not_mem with 
      (1:=VsetP.disjoint_sym disjoint_Orcl2).
     generalize W; rewrite <- H3; auto; destruct x; auto.

     eapply equiv_strengthen;[ | apply equiv_random].
     intros k m1 m2 (H1, H2); split; unfold kreq_mem in *.
     unfold eq_support.
     apply EqObs_d_fv_expr.
     apply req_mem_weaken with (2:= H1).
     unfold WFReadD in w0; apply Vset.subset_complete; intros.
     apply Vset.subset_correct with (Vset.union (Vset.union Gadv Gcomm) I).
     rewrite <- (VsetP.union_idem IA); 
      repeat apply VsetP.subset_union_ctxt; auto with set.
     repeat rewrite VsetP.union_spec; destruct (w0 _ H0); tauto.
     destruct x; intros; split; unfold kreq_mem.
     apply equiv_WFWrite; trivial.
     apply inv_dep with m1 m2; trivial;
     red; intros; rewrite Mem.get_upd_diff; trivial; intro.
     assert (W: Var.is_global x) by auto with set.
     contradict H3. 
     apply VsetP.disjoint_mem_not_mem with 
      (1:=VsetP.disjoint_sym disjoint_Orcl1).
     generalize W; rewrite <- H4; auto.
     assert (W: Var.is_global x) by auto with set.
     contradict H3. 
     apply VsetP.disjoint_mem_not_mem with 
      (1:=VsetP.disjoint_sym disjoint_Orcl2).
     generalize W; rewrite <- H4; auto.

     (* Cond *)
     apply equiv_cond.
     eapply equiv_strengthen; 
      [ | eapply equiv_weaken; [ | apply (IHWFAdv_c1 H1)] ].
     intros k m1 m2 (W, _); trivial.
     intros k m1 m2 W; apply req_mem_rel_weaken with (3:= W); auto with set.
     apply VsetP.subset_union_ctxt; auto with set.
     unfold Basics.flip; trivial.
     eapply equiv_strengthen; 
      [ | eapply equiv_weaken; [ | apply (IHWFAdv_c2 H1)] ].
     intros k m1 m2 (W, _); trivial.
     intros k m1 m2 W; apply req_mem_rel_weaken with (3:= W); auto with set.
     apply VsetP.subset_union_ctxt; auto with set.
     unfold Basics.flip; trivial.
     intros k m1 m2 (W, Wi); rewrite  (equiv_WFRead w Hcomm Hadv W); trivial.

     (* While *)  
     eapply equiv_weaken;[ | apply equiv_while].
     intros k m1 m2 (W, _); trivial.
     intros k m1 m2 (W,_); rewrite  (equiv_WFRead w Hcomm Hadv W); trivial.
     eapply equiv_strengthen;[ | apply equiv_weaken with (2:= IHWFAdv_c H0)].
     intros k m1 m2 (W, _); trivial.
     intros k m1 m2 W; apply req_mem_rel_weaken with (3:= W); auto.
     apply VsetP.subset_union_ctxt; auto with set.
     apply WFAdv_c_subset with E1 c; trivial.
     unfold Basics.flip; trivial.
     
     (* Call Orcl *)
     destruct (pi_def _ i) as (pif, Hdef).
     apply equiv_call with 
       (Pf:= req_mem_rel (Vset.union (pii_params pif) IA) inv)
       (Qf :=  
        (req_mem_rel (Vset.union (pii_output pif) 
         (Vset.diff IA 
          (Vset.union (pi_mod (pi_eq_refl1 pif)) 
           (pi_mod (pi_eq_refl2 pif))))) inv) /-\
        fun k m1 m2 => 
         E.eval_expr (proc_res E1 f) m1 = E.eval_expr (proc_res E2 f) m2). 

     (* Init *)
     unfold req_mem_rel, kreq_mem, andR; simpl; intros k m1 m2 (W3, W4).
     assert (init_mem E1 f args m1 =={ Vset.union (pii_params pif) IA} 
             init_mem E2 f args m2).
     apply req_mem_weaken with 
      (Vset.union (pii_params pif) (get_globals (Vset.union IA I))).
     apply VsetP.subset_union_ctxt; auto with set. 
     apply Vset.subset_complete; intros. 
     apply get_globals_complete; auto with set.
     apply iinput_Adv_global; trivial.
     eapply EqObs_args_correct; eauto.
     red; intros.
     rewrite <- (Eq_orcl_params_12 _ i).
     assert (forall ta (args0:E.args ta), ta = (Proc.targs f) -> 
      exists e, get_arg x0 (proc_params E1 f) args0 = Some e).
     apply Vset_of_var_decl_ind with (P:= fun t0 x0 => 
      forall ta (args0:E.args ta), ta = (Proc.targs f) ->
       exists e0 : E.expr t0, get_arg x0 (proc_params E1 f) args0 = Some e0)
     (lv:= proc_params E1 f) .
     generalize (Proc.targs f) (proc_params E1 f). 
     induction v; simpl; intros.
     elim H1.
     destruct args0; try discriminate.
     injection H2; clear H2; intros; subst.
     destruct H1.
     inversion H1; subst.
     assert (W:= T.inj_pair2 H5); clear H1 H4 H5; subst.
     destruct (get_arg p v args0); eauto.
     generalize (Var.veqb_spec p p); destruct (Var.veqb p p); intros.
     case_eq (T.eq_dec a a); intros.
     rewrite (T.UIP_refl e0); eauto.
     elim (T.eq_dec_r H2); trivial.
     elim H1; trivial.
     destruct (IHv _ _ H1 _ args0 (refl_equal _)).
     rewrite H2; eauto.
     apply Vset.subset_correct with (2:= H0).
     apply params_subset1.
     simpl; destruct (H1 _ args (refl_equal _)) as (e0, Heq); rewrite Heq.
     red; intros.
     assert (W:= get_arg_some _ _ _ Heq).   
     apply equiv_WFRead with (IA:=IA) (1:= w _ _ W); auto.
     split; trivial.
     unfold depend_only_rel in inv_dep.
     apply inv_dep with m1 m2; trivial; red; intros;
     rewrite init_mem_global; trivial; apply inv_global; 
      rewrite VsetP.union_spec; auto.

     (* Post *)
     unfold req_mem_rel, kreq_mem, andR; simpl.
     intros k m1 m1' m2 m2' (W3, W4) ((W5, W6), W7); split.
     red; intros.
     destruct (Vset.ET.eq_dec x x0).
     inversion e; subst; simpl.
     repeat rewrite return_mem_dest; trivial.
     change (Var.mkV x <> x0) in n.
     case_eq (Var.is_global x0); intros.
     repeat rewrite return_mem_global; trivial.
     apply W5.
     rewrite VsetP.union_spec, VsetP.diff_spec.
     case_eq (Vset.mem x0 (pii_output pif)); intros; auto.
     right.
     rewrite VsetP.union_spec in H0; destruct H0.
     split; trivial; rewrite VsetP.union_spec; intro.
     rewrite (input_orcl_pre _ i Hdef _ H0 H3) in H2; discriminate.
     assert (XX:= add_read_local _ _ H _ H0); unfold Var.is_local in XX;
      rewrite H1 in XX; discriminate.
     assert (Var.is_local x0) by (unfold Var.is_local; rewrite H1; trivial).
     repeat rewrite return_mem_local; trivial.
     apply W3.
     rewrite VsetP.union_spec in H0 |- *; destruct H0; auto.
     unfold add_read in H0.
     destruct (Var.is_global x); auto.
     rewrite VsetP.add_spec in H0; destruct H0; auto.
     elim (n H0).
     red in inv_dep.
     apply inv_dep with m1' m2'; trivial; red; intros; 
      rewrite return_mem_global; trivial.
     intros Heq; rewrite <-Heq in H0.
     assert (W: Var.is_global x) by auto with set.
     contradict H0. 
     apply VsetP.disjoint_mem_not_mem with 
      (1:= VsetP.disjoint_sym disjoint_Orcl1); auto.
     auto with set.
     intros Heq; rewrite <-Heq in H0.
     assert (W: Var.is_global x) by auto with set.
     contradict H0. 
     apply VsetP.disjoint_mem_not_mem with 
      (1:= VsetP.disjoint_sym disjoint_Orcl2); auto.
     auto with set.

     (* Body *)
     destruct (mod_spec (pi_eq_refl1 pif)) as (L1, (T1,T2)).
     destruct (mod_spec (pi_eq_refl2 pif)) as (L2, (T3,T4)).
     destruct (pii_spec pif) as (ls, (H3,(H4,H5))).
     apply Modify_Modify_pre with (P := fun _ _ => True)in T2.
     apply Modify_Modify_pre with (P := fun _ _ => True)in T4.
     apply equiv_union_Modify_pre2 with (4:= T2) (5:= T4) 
      (Q:= req_mem_rel (Vset.union ls (pii_output pif)) inv); intros.
     auto.
     tauto.
     destruct H0; destruct H1; unfold kreq_mem in *.
     assert (m1' =={Vset.diff IA 
      (Vset.union (pi_mod (pi_eq_refl1 pif)) (pi_mod (pi_eq_refl2 pif)))} m2').
     red; intros.
     rewrite VsetP.diff_spec, VsetP.union_spec in H9.
     destruct H9.
     rewrite <- H2.
     rewrite <- H6.
     apply H0; rewrite VsetP.union_spec; tauto.
     rewrite VsetP.union_spec; intros [W | W]; try tauto.
     assert (V1 := T3 _ W); unfold Var.is_local in V1.
     rewrite (iinput_Adv_global _ H9) in V1; discriminate.
     rewrite VsetP.union_spec; intros [W | W]; try tauto.
     assert (V1 := T1 _ W); unfold Var.is_local in V1;
      rewrite (iinput_Adv_global _ H9) in V1; discriminate.
     split.
     split; unfold kreq_mem; trivial.
     apply req_mem_union; trivial.
     apply req_mem_weaken with (2:= H1); auto with set.
     apply H5.
     apply req_mem_union; trivial.
     apply req_mem_weaken with (2:= H9). 
     apply VsetP.diff_le_compat; auto with set.
     eapply equiv_strengthen;[ | apply H4].
     intros k m1 m2 (W3, W4); split; trivial.
     unfold kreq_mem; rewrite VsetP.union_sym.
     apply req_mem_weaken with (2:= W3).
     apply VsetP.subset_union_ctxt; auto with set.

     (* Call Adv *)
     destruct (Eq_adv_decl_12 f) as (Heq1, (Heq2, Heq3)); trivial.

     assert (W:forall t (x:Var.var t),  Vset.mem x 
      (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x).
     intros; apply Vset_of_var_decl_ind with 
      (P:= fun t (x:Var.var t) => Var.is_local x) (lv:= proc_params E1 f); auto.
     intros; change (Var.vis_local x1).
     apply proc_params_local with E1 t f; trivial.
     assert (forall x, Vset.mem x 
      (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x). 
     intros (t0,x0); auto.
     clear W.
     generalize (IHWFAdv_c H1).
     pattern (proc_body E1 f) at 2; rewrite Heq2; intros.
     apply  equiv_call with (3:= H2).
     intros k m1 m2 (W1, W2); split.
     unfold kreq_mem; red; intros.
     rewrite (init_mem_eq2 E1 E2 f args args m1 Heq1); trivial.
     rewrite VsetP.union_spec in H3; destruct H3. 
     repeat rewrite init_mem_global; auto using iinput_Adv_global.
     apply W1; auto with set.
     apply init_mem_local; auto.
     generalize args w0.
     generalize (Proc.targs f). induction args0; simpl; auto; intros.
     rewrite IHargs0; auto.
     rewrite (@equiv_WFRead IA a p I k m1 m2); auto.
     unfold depend_only_rel in inv_dep.
     apply inv_dep with m1 m2; trivial; red; intros;
      rewrite init_mem_global; trivial; 
      apply inv_global; rewrite VsetP.union_spec; auto.
     intros k m1 m1' m2 m2' (W1, W2) (W3, W4); split; unfold kreq_mem in *.
     red; intros. 
     destruct (Var.eq_dec x x0).
     inversion e; simpl.
     repeat rewrite return_mem_dest.
     rewrite <- Heq3.
     apply equiv_WFRead with (IA:= IA) (1 := w); auto.
     rewrite VsetP.union_spec in H3; destruct H3. 
     repeat rewrite return_mem_global; auto using iinput_Adv_global.
     apply W3; auto with set.
     assert (Vset.mem x0 I). 
     unfold add_read in H3; destruct (Var.is_global x); auto.
     rewrite VsetP.add_spec in H3; destruct H3; trivial.
     elim (n1 H3).
     repeat rewrite return_mem_local; auto. 
     apply W1; auto with set.
     unfold depend_only_rel in inv_dep.
     apply inv_dep with m1' m2'; trivial; red; 
      intros; rewrite return_mem_global; trivial.
     intros Heq; rewrite <-Heq in H3.
     assert (W: Var.is_global x) by auto with set.
     contradict H3. 
     apply VsetP.disjoint_mem_not_mem with 
      (1:=VsetP.disjoint_sym disjoint_Orcl1); auto.
     auto with set.
     intros Heq; rewrite <-Heq in H3.
     assert (W: Var.is_global x) by auto with set.
     contradict H3. 
     apply VsetP.disjoint_mem_not_mem with 
      (1:=VsetP.disjoint_sym disjoint_Orcl2); auto.
     auto with set.
    Qed.

    (* TODO: Move these 2 definitions *)
    Definition eq_refl_i1 t (f:Proc.proc t) :=
     match pii f with
     | Some pif => Some (pi_eq_refl1 pif)
     | None => None
     end.

    Definition eq_refl_i2 t (f:Proc.proc t) :=
     match pii f with
     | Some pif => Some (pi_eq_refl2 pif)
     | None => None
     end.

    Variable MA1 MA2 : Vset.t.

    Hypothesis MA1_def : mod_adv eq_refl_i1 = Some MA1. 

    Hypothesis MA2_def : mod_adv eq_refl_i2 = Some MA2.

    Definition ioutput_adv := Vset.inter IA (Vset.union MA1 MA2).

    Lemma WFAdv_EqObsInv : forall t (f:Proc.proc t), WFAdv E1 f ->
     ~ PrSet.mem (BProc.mkP f) PrOrcl -> 
     ~ PrSet.mem (BProc.mkP f) PrPriv -> 
     exists ls, 
      (forall x, Vset.mem x ls -> Var.is_local x) /\ 
      EqObsInv inv (Vset.union IA (Vset_of_var_decl (proc_params E1 f)))
      E1 (proc_body E1 f) E2 (proc_body E2 f) (Vset.union ls ioutput_adv) /\ 
      EqObs_e (Vset.union (Vset.union ls ioutput_adv) 
       (Vset.diff IA (Vset.union MA1 MA2)))
      (proc_res E1 f) (proc_res E2 f).
    Proof.
     intros t f (O,(H1,H2)) XX1 XX2.
     exists O; split.
     intros; apply WFAdv_c_local with (1:= H1); trivial.
     intros (t0, x0) H0.
     apply Vset_of_var_decl_ind with 
      (P:=fun t (x:Var.var t) => Var.is_local x) (lv:=proc_params E1 f); trivial.
     intros; change (Var.vis_local x1).
     apply proc_params_local with E1 t f; trivial.
     destruct (Eq_adv_decl_12 f) as (Heq1, (Heq2, Heq3)); trivial.
     rewrite <- Heq3, <- Heq2.
     split.
     unfold EqObsInv; eapply equiv_weaken; 
      [ | apply WFAdv_c_EqObsInv with (1:= H1)].
     intros; eapply req_mem_rel_weaken; eauto.
     rewrite VsetP.union_sym.
     apply VsetP.subset_union_ctxt; unfold ioutput_adv; auto with set.
     unfold Basics.flip; trivial.
     intros (t0, x0) H0.
     apply Vset_of_var_decl_ind with 
      (P:=fun t (x:Var.var t) => Var.is_local x) (lv:=proc_params E1 f); trivial.
     intros; change (Var.vis_local x).
     apply proc_params_local with E1 t f; trivial.
     red; intros.
     destruct iinput_Adv_subset as (Hcomm,(Hadv, Horcl)).
     apply equiv_WFRead with (IA:= IA) (1 := H2); auto.
     apply req_mem_weaken with (2:= H).
     rewrite VsetP.union_assoc, VsetP.union_sym.
     apply VsetP.subset_union_ctxt; auto with set.
     unfold ioutput_adv; apply Vset.subset_complete; intros.
     rewrite VsetP.union_spec,VsetP.diff_spec, VsetP.inter_spec.
     destruct (VsetP.mem_dec x (Vset.union MA1 MA2)); auto with set.
    Qed.

   End EQ_OBS_INV.

  End INFO.


  Section UPTO.

   Variable bad : Var.var T.Bool.
  
   Variable Gbad : Var.is_global bad.

   Definition check_adv_upto_info (pi:forall t (p:Proc.proc t), bool) :=
    (negb (Vset.mem bad Gadv) &&
     (PrSet.forallb (fun p => pi _ p.(BProc.p_name)) PrOrcl))%bool.

   Lemma upto_adv_preserves : forall E (pi:forall t (p:Proc.proc t), bool) I c O,
    check_adv_upto_info pi ->
    prbad_spec bad E pi ->
    WFAdv_c E I c O -> 
    forall k (m:Mem.t k) f,
     EP k bad m ->
     mu ([[ c ]] E m) f ==
     mu ([[ c ]] E m) (restr (EP k bad) f).
   Proof.
    intros E pi I c O Hadv Hpi Hwf.
    unfold check_adv_upto_info in Hadv; rewrite is_true_andb in Hadv.
    destruct Hadv as (W1, W2).
    assert (forall x y : PrSet.E.t, PrSet.E.eq x y -> 
     (fun p : PrSet.E.t => pi (BProc.p_type p) (BProc.p_name p)) x = 
     (fun p : PrSet.E.t => pi (BProc.p_type p) (BProc.p_name p)) y).
    intros x y Heq; rewrite (Heq:x = y); trivial.
    assert (W:= PrSet.forallb_correct _ H _ W2); clear W2 H.
    rewrite is_true_negb in W1.
    intros k;
    refine (WFAdv_c_prop
    (fun _ c _ _ =>
     forall m f,
      EP k bad m ->
      mu ([[ c ]] E m) f ==
      mu ([[ c ]] E m) (restr (EP k bad) f))
    (fun _ i _ _ =>
     forall m f,
      EP k bad m ->
      mu ([[ [i] ]] E m) f ==
      mu ([[ [i] ]] E m) (restr (EP k bad) f))
    _ _ _ _ _ _ _ _ Hwf); unfold restr; intros.

    repeat rewrite deno_nil_elim; rewrite H; trivial.

    intros; repeat rewrite deno_cons_elim; repeat rewrite Mlet_simpl.
    rewrite H; trivial.
    symmetry; rewrite H; trivial.
    apply mu_stable_eq; refine (ford_eq_intro _); intro m'.   
    case_eq (EP k bad m'); [ | trivial]; intro Hm'.
    symmetry; rewrite H0; trivial.

    intros; repeat rewrite deno_assign_elim.
    unfold EP in H |- *; simpl in H |- *.
    rewrite Mem.get_upd_diff.
    rewrite H; trivial.  
    intro Hx; elim W1.  
    rewrite <- Hx in Gbad |- *; destruct x; simpl; apply w; trivial.

    intros; repeat rewrite deno_random_elim.
    apply mu_stable_eq; refine (ford_eq_intro _); intro.
    unfold EP in H |- *; simpl in H |- *.
    rewrite Mem.get_upd_diff.
    rewrite H; trivial.  
    intro Hx; elim W1.  
    rewrite <- Hx in Gbad |- *; destruct x; simpl; apply w; trivial.

    intros; repeat rewrite deno_cond_elim.
    case (E.eval_expr e m); auto.

    intros; apply range_eq with (fun m => is_true (EP k bad m)).
    eapply range_weaken with (fun m => EP k bad m /\ E.eval_expr e m = false).
    intros; tauto.
    apply while_ind0; intros;[ | trivial].
    intros g Hg.
    rewrite H; trivial.
    transitivity (mu ([[ c0 ]] E m0) (fzero _)).
    symmetry; apply mu_zero.
    apply mu_stable_eq.
    refine (ford_eq_intro _); intro m'.
    generalize (Hg m'); case (EP k bad m'); auto.
    intros a Heq; rewrite Heq; trivial.

    intros; repeat rewrite deno_call_elim.
    rewrite (Hpi _ f (W _ i)).
    apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
    unfold restr; case_eq (EP k bad m'); intro Hm'.
    unfold EP; simpl; rewrite return_mem_global; trivial.
    unfold EP in Hm'; simpl in Hm'; rewrite Hm'; trivial.  
    intro Hx; elim W1.
    rewrite <- Hx in Gbad |- *; destruct x; simpl; apply w0; trivial.
    unfold EP; simpl; rewrite return_mem_global; trivial.
    unfold EP in Hm'; simpl in Hm'; rewrite Hm'; trivial. 
    intro Hx; elim W1.
    rewrite <- Hx in Gbad |- *; destruct x; simpl; apply w0; trivial.
    unfold EP; simpl; rewrite init_mem_global; trivial.

    intros; repeat rewrite deno_call_elim.
    rewrite (H (init_mem E f args m)).
    apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
    unfold restr; case_eq (EP k bad m'); intro Hm'.
    unfold EP; simpl; rewrite return_mem_global; trivial.
    unfold EP in Hm'; simpl in Hm'; rewrite Hm'; trivial.  
    intro Hx; elim W1.
    rewrite <- Hx in Gbad |- *; destruct x; simpl; apply w2; trivial.
    unfold EP; simpl; rewrite return_mem_global; trivial.
    unfold EP in Hm'; simpl in Hm'; rewrite Hm'; trivial. 
    intro Hx; elim W1.
    rewrite <- Hx in Gbad |- *; destruct x; simpl; apply w2; trivial.
    unfold EP; simpl; rewrite init_mem_global; trivial.
   Qed.

   Lemma  upto_adv_upto : forall E1 E2 (pi:upto_info bad E1 E2) I c O,
    check_adv_upto_info pi ->
    Eq_adv_decl E1 E2 -> Eq_orcl_params E1 E2 ->
    WFAdv_c E1 I c O ->
    (forall k (m:Mem.t k) f,
     mu ([[c]] E1 m) (restr (negP (EP k bad)) f) ==
     mu ([[c]] E2 m) (restr (negP (EP k bad)) f)).
   Proof.
    intros E1 E2 pi I c O Hadv HEq HeqO Hwf k; generalize Hadv.
    unfold check_adv_upto_info in Hadv; rewrite is_true_andb in Hadv.
    destruct Hadv as (W1, W2).
    assert (forall x y : PrSet.E.t, PrSet.E.eq x y -> 
     (fun p : PrSet.E.t => pi (BProc.p_type p) (BProc.p_name p)) x = 
     (fun p : PrSet.E.t => pi (BProc.p_type p) (BProc.p_name p)) y).
    intros x y Heq; rewrite (Heq:x = y); trivial.
    assert (W:= PrSet.forallb_correct _ H _ W2); clear W2 H.
    rewrite is_true_negb in W1.
    intros Hadv; refine (WFAdv_c_prop
     (fun _ c _ _ => 
      forall m f,
       mu ([[ c ]] E1 m) (restr (negP (EP k bad)) f) ==
       mu ([[ c ]] E2 m) (restr (negP (EP k bad)) f))
     (fun _ i _ _ =>
      forall m f,
       mu ([[ [i] ]] E1 m) (restr (negP (EP k bad)) f) ==
       mu ([[ [i] ]] E2 m) (restr (negP (EP k bad)) f))
     _ _ _ _ _ _ _ _ Hwf); clear Hwf c; unfold restr; intros.
    repeat rewrite deno_nil_elim; trivial.

    (* cons *)
    rewrite deno_cons_elim, Mlet_simpl.
    rewrite (deno_cons_elim E2 i c m), Mlet_simpl.
    rewrite (mu_restr_split (([[ [i] ]]) E1 m) (EP k bad)).
    unfold restr; rewrite (mu_restr_split (([[ [i] ]]) E2 m) (EP k bad)).
    apply Uplus_eq_compat.

    transitivity (mu (([[ [i] ]]) E1 m) (fzero _)).
    apply mu_stable_eq; refine (ford_eq_intro _); intros m'.
    case_eq (EP k bad m'); intros;[ | trivial].
    rewrite (@upto_adv_preserves E1 pi IO c O0); trivial.
    transitivity (mu (([[ c ]]) E1 m') (fzero _)).
    apply mu_stable_eq; refine (ford_eq_intro _); intros m''.
    unfold restr, negP; destruct (EP k bad m''); trivial.
    symmetry; rewrite mu_zero; trivial.
    apply upto_pr1. 

    transitivity (mu (([[ [i] ]]) E2 m) (fzero _)).
    repeat rewrite mu_zero; trivial.
    apply mu_stable_eq; refine (ford_eq_intro _); intros m'.
    unfold restr; case_eq (EP k bad m'); intros;[ | trivial].
    rewrite (@upto_adv_preserves E2 pi IO c O0); trivial.
    transitivity (mu (([[ c ]]) E2 m') (fzero _)).
    rewrite mu_zero; trivial.
    apply mu_stable_eq; refine (ford_eq_intro _); intros m''.
    unfold restr, negP; destruct (EP k bad m''); trivial.
    apply upto_pr2. 
    apply WFAdv_c_trans with E1; trivial.

    unfold restr; rewrite H.
    apply mu_stable_eq; refine (ford_eq_intro _); intros m'.
    unfold negP; case_eq (EP k bad m'); intros; unfold negb; trivial.

    (* Assign *)
    repeat rewrite deno_assign_elim; trivial.

    (* Random *)
    repeat rewrite deno_random_elim; trivial.

    (* Cond *)
    repeat rewrite deno_cond_elim.
    destruct (E.eval_expr e m); trivial.

    (* While *)
    transitivity
     (mu (lub (unroll_while_sem E1 e c m)) (restr (negP (EP k bad)) f));
     [ refine (eq_distr_elim _ _); apply deno_while_unfold | ].
    transitivity
     (mu (lub (unroll_while_sem E2 e c m)) (restr (negP (EP k bad)) f));
     [ | refine (eq_distr_elim _ _); symmetry; apply deno_while_unfold ].
    simpl; apply lub_eq_compat.
    refine (ford_eq_intro _); intro n; simpl.
    generalize m; clear m; induction n; intro m; simpl;
     repeat rewrite (deno_cond_elim (k:=k)).
    case (E.eval_expr e m); repeat rewrite deno_nil_elim; trivial.
    case (E.eval_expr e m); repeat rewrite deno_app_elim.
    rewrite (mu_restr_split ([[c]] E1 m) (EP k bad)).
    unfold restr; rewrite (mu_restr_split ([[c]] E2 m) (EP k bad)).
    apply Uplus_eq_compat. 

    transitivity (mu ([[c]] E1 m) (fzero _)).
    apply mu_stable_eq; refine (ford_eq_intro _); intro m'; unfold restr.
    case_eq (EP k bad m'); intro Heq; [ | trivial].
    assert (PR:= upto_adv_preserves Hadv pi.(upto_pr1) w0).
    rewrite (fun f => unroll_while_preserves_bad2 E1 e c n (PR k) f Heq).
    transitivity (mu (([[ unroll_while e c n ]]) E1 m') (fzero _)).
    apply mu_stable_eq; refine (ford_eq_intro _); intros m''; unfold restr, negP.
    case_eq (EP k bad m''); intros; trivial.
    case (E.eval_expr e m''); trivial; simpl; rewrite H0; trivial.
    apply mu_zero.
    transitivity (mu ([[c]] E2 m) (fzero _)).
    repeat rewrite mu_zero; trivial.
    apply mu_stable_eq; refine (ford_eq_intro _); intro m'; unfold restr.
    case_eq (EP k bad m'); intro Heq; [ | trivial].
    assert (PR:= upto_adv_preserves Hadv pi.(upto_pr2) 
     (WFAdv_c_trans HeqO HEq w0)).
    rewrite (fun f => unroll_while_preserves_bad2 E2 e c n (PR k) f Heq).
    transitivity (mu (([[ unroll_while e c n ]]) E2 m') (fzero _)).
    rewrite mu_zero; trivial.
    apply mu_stable_eq; refine (ford_eq_intro _); intros m''; unfold restr, negP.
    case_eq (EP k bad m''); intros; trivial.
    case (E.eval_expr e m''); trivial; simpl; rewrite H0; trivial.

    unfold restr; rewrite H.
    apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
    destruct (negP (EP k bad) m'); trivial.
    repeat rewrite deno_nil_elim; trivial.

    (* Call Orcl *)
    repeat rewrite deno_call_elim.
    destruct (pi.(supto) _ (W _ i))as (H0, (H1, H2)).
    transitivity
     (mu ([[proc_body E1 f]] E1 (init_mem E1 f args m))
      (restr (negP (EP k bad)) (fun m' => f0 (return_mem E1 x f m m')))).
    apply mu_stable_eq.
    unfold restr, negP, EP; refine (ford_eq_intro _); intro m'.
    simpl; rewrite return_mem_global; trivial.
    intro Hx; elim W1.
    rewrite <- Hx in Gbad |- *; destruct x; simpl; apply w0; trivial.
    rewrite H0; unfold BProc.p_name.
    rewrite (init_mem_eq2 E1 (k:=k) E2 f args args); trivial.
    apply mu_stable_eq.
    unfold restr, negP, EP; refine (ford_eq_intro _); intro m'.
    simpl; rewrite (return_mem_eq E1 E2 f x m m' H1).
    rewrite return_mem_global; trivial.
    intro Hx; elim W1.
    rewrite <- Hx in Gbad |- *; destruct x; simpl; apply w0; trivial.

    (* Call Adv *)
    repeat rewrite deno_call_elim.
    destruct (HEq _ f n n0) as (H0, (H1, H2)).
    transitivity
     (mu ([[proc_body E1 f]] E1 (init_mem E1 f args m))
      (restr (negP (EP k bad)) (fun m' => f0 (return_mem E1 x f m m')))).
    apply mu_stable_eq.
    unfold restr, negP, EP; refine (ford_eq_intro _); intro m'.
    simpl; rewrite return_mem_global; trivial.
    intro Hx; elim W1.
    rewrite <- Hx in Gbad |- *; destruct x; simpl; apply w2; trivial.
    unfold restr; rewrite H.
    rewrite <- H1.
    rewrite (init_mem_eq2 E1 (k:=k) E2 f args args); trivial.
    apply mu_stable_eq.
    unfold restr, negP, EP; refine (ford_eq_intro _); intro m'.
    simpl; rewrite (return_mem_eq E1 E2 f x m m' H2).
    rewrite return_mem_global; trivial.
    intro Hx; elim W1.
    rewrite <- Hx in Gbad |- *; destruct x; simpl; apply w2; trivial.
   Qed.

  End UPTO.


  Section UPTO2.

   Variable Inv : mem_rel.

   Variables E1 E2 : env.

   Variables X1 X2 : Vset.t.
  
   Hypothesis inv_dep : depend_only_rel Inv X1 X2.

   Hypothesis inv_global : forall x,
    Vset.mem x (Vset.union X1 X2) -> Var.is_global x.
   
   Hypothesis disjoint_Orcl1 : Vset.disjoint X1 Gadv.
   Hypothesis disjoint_Orcl2 : Vset.disjoint X2 Gadv.

   Hypothesis Eq_adv_decl_12 : Eq_adv_decl E1 E2.

   Hypothesis Eq_orcl_params_12: Eq_orcl_params E1 E2.

   Section EQ_OBS_INV.
     
    (* TODO: Move this to WP.v *) 
    Definition mem_pred := forall k : nat, Mem.t k -> Prop.
    
    Definition andp (P1 P2:mem_pred) k (m:Mem.t k) := P1 k m /\ P2 k m.
    Definition orp (P1 P2:mem_pred) k (m:Mem.t k) := P1 k m \/ P2 k m.
    Definition impp (P1 P2:mem_pred) k (m:Mem.t k) := P1 k m -> P2 k m.
    Definition eqp (P1 P2:mem_pred) k (m:Mem.t k) := P1 k m <-> P2 k m.
    Definition notp (P:mem_pred) k (m:Mem.t k) := ~ P k m.
    Definition falsep:mem_pred := fun k (m:Mem.t k), False.
    Definition truep:mem_pred := fun k (m:Mem.t k), True.
    Definition EPp (e:E.expr T.Bool) k (m:Mem.t k) := is_true (E.eval_expr e m).

    Definition upd_pred 
     (P:mem_pred) (t:T.type) (x:Var.var t) (e:E.expr t) : mem_pred :=
     fun k (m:Mem.t k) => P k (m {!x <-- E.eval_expr e m!}).

    Definition eqR (P1 P2:mem_rel) := andR (impR P1 P2) (impR P2 P1).
    
    Definition rel_pred1 (P:mem_pred) : mem_rel := fun k m1 m2 => P k m1.

    Definition rel_pred2 (P:mem_pred) : mem_rel := fun k m1 m2 => P k m2.

    Lemma rel_pred1_spec k (m1 m2:Mem.t k) P :
     (rel_pred1 P) k m1 m2 -> P k m1.
    Proof. 
     auto. 
    Qed.

    Lemma rel_pred2_spec k (m1 m2:Mem.t k) P :
      (rel_pred2 P) k m1 m2 -> P k m2.
    Proof.
     auto.
    Qed.
   
 
    Section HOARE_RULES.
      
     Variable k : nat.
      
     Definition Hoare 
      (m:Mem.t k) (E:env) (P:mem_pred) (c:cmd) (Q:mem_pred) : Prop :=
      P k m -> range (Q k) ([[ c ]] E m).

     Lemma range_Munit k (Q:mem_pred) (m:Mem.t k) : Q k m -> range (Q k) (Munit m).
     Proof.
      intros; unfold range, mu; simpl; intros; auto.
     Qed.

     Lemma Hoare_nil (m:Mem.t k) E (P Q:mem_pred) : 
      (forall k (m:Mem.t k), P k m -> Q k m) ->
      Hoare m E P nil Q.
     Proof.
      intros; unfold Hoare; rewrite deno_nil; intros;  apply range_Munit; auto.
     Qed.
      
     Lemma Hoare_assign (m:Mem.t k) E P t (x:Var.var t) (e:E.expr t) :
      Hoare m E (upd_pred P x e) [ x <- e ] P.
     Proof.
      intros; unfold Hoare, upd_pred; rewrite deno_assign; apply range_Munit.
     Qed.

     Lemma Hoare_random (m:Mem.t k) E (P Q:mem_pred) 
      t (x:Var.var t) (d:E.support t) :
      (forall x0:T.interp k t, P k m -> Q k (m {!x <-- x0!})) ->
      Hoare m E P [ x <$- d ] Q.
     Proof.
      unfold Hoare; intros.
      rewrite deno_random.
      eapply range_Mlet.
      apply range_True.
      intros.
      apply range_Munit.
      auto.
     Qed.
      
     Lemma Hoare_cons m E P Q R i c:
      Hoare m E P [i] R ->
      (forall m, Hoare m E R c Q) ->
      Hoare m E P (i :: c) Q.
     Proof.
      unfold Hoare; intros; rewrite deno_cons; eapply range_Mlet; auto.
     Qed.
     
     Lemma Hoare_false m E c Q : Hoare m E falsep c Q.
     Proof.
      intros; unfold Hoare; intros; elim H.
     Qed.
      
     Lemma Hoare_cond m E b c1 c2 P Q :
      Hoare m E (andp P (EPp b)) c1 Q ->
      Hoare m E (andp P (notp (EPp b))) c2 Q ->
      Hoare m E P [If b then c1 else c2] Q.
     Proof.
      unfold Hoare, andp, notp, EPp; intros; rewrite deno_cond.
      case_eq (E.eval_expr b m); intros; [ | apply not_is_true_false in H2]; auto.
     Qed.

     Lemma Hoare_case m E c (P Q R:mem_pred) :
      sumbool (R k m) (~R k m) ->
      Hoare m E (andp P (notp R)) c Q ->
      Hoare m E (andp P R) c Q ->
      Hoare m E P c Q.
     Proof.
      intros; intro.
      destruct H.
      apply H1; unfold andp; auto.
      apply H0; unfold andp; auto.
     Qed.

     Lemma Hoare_call (m:Mem.t k) E (P Q:mem_pred) t (x:Var.var t) f la :
      (P k m -> P k (init_mem E f la m)) ->
      (forall m0, Q k m0 ->  Q k (return_mem E x f m m0)) ->
      Hoare (init_mem E f la m) E P (proc_body E f) Q ->
      Hoare m E P [x <c- f with la] Q.
     Proof.
      unfold Hoare; intros.
      rewrite deno_call.
      eapply range_Mlet.
      apply (H1 (H H2)).
      intros; apply range_Munit; auto.     
     Qed.

     Lemma Hoare_app m E c1 c2 P Q R :
      Hoare m E P c1 R -> 
      (forall m, Hoare m E R c2 Q) ->
      Hoare m E P (c1 ++ c2) Q.
     Proof.
      unfold Hoare; intros; rewrite deno_app.
      eapply range_Mlet; intros.
      apply H; trivial.
      apply H0; trivial.
     Qed.
     
     Lemma Hoare_strengthen (m:Mem.t k) E c (P Q R:mem_pred) :
      (P k m -> R k m) ->
      Hoare m E R c Q ->
      Hoare m E P c Q.
     Proof.
      unfold Hoare; intros; eapply range_weaken; eauto.
     Qed.
     
     Lemma Hoare_weaken (m:Mem.t k) E c (P Q R:mem_pred) :
      (forall m, R k m -> Q k m) ->
      Hoare m E P c R ->
      Hoare m E P c Q.
     Proof.
      unfold Hoare; intros; eapply range_weaken; eauto.
     Qed.
     
     Lemma Hoare_while m E e c (P:mem_pred) :
      (forall m, Hoare m E (andp P (EPp e)) c P) ->
      Hoare m E P [while e do c] (andp P (notp (EPp e))).
     Proof.
      intros; unfold Hoare; intros.
      unfold andp, notp, EPp in *.
      eapply range_weaken with (fun m0:Mem.t k => P k m0 /\ E.eval_expr e m0 = false).
      intros; rewrite not_is_true_false; split; try tauto.
      apply while_ind0; intros; trivial.
      apply H; tauto.
     Qed.
    
    End HOARE_RULES.

    Variables bad1_expr bad2_expr : E.expr T.Bool.

    Definition bad1 := EPp bad1_expr.
    Definition bad2 := EPp bad2_expr.

    Hypothesis Gbad1 : forall x, Vset.mem x (fv_expr bad1_expr) -> Var.is_global x.
    Hypothesis Gbad2 : forall x, Vset.mem x (fv_expr bad2_expr) -> Var.is_global x. 
    Hypothesis bad1_adv : Vset.disjoint (fv_expr bad1_expr) Gadv.
    Hypothesis bad2_adv : Vset.disjoint (fv_expr bad2_expr) Gadv.

    Hypothesis bad1_dec : forall k (m1 m2:Mem.t k), 
     sumbool ((rel_pred1 bad1) k m1 m2) (~(rel_pred1 bad1) k m1 m2).

    Hypothesis bad2_dec : forall k (m1 m2:Mem.t k), 
     sumbool ((rel_pred2 bad2) k m1 m2) (~(rel_pred2 bad2) k m1 m2).

    Hypothesis Gcomm_empty : Gcomm [=] Vset.empty.
   
    Lemma equiv_rel_pred : forall (P1 P2 Q1 Q2: mem_pred) (P: mem_rel) c1 E1 c2 E2,
     lossless E1 c1 -> lossless E2 c2 -> 
     (forall k (m:Mem.t k), Hoare m E1 P1 c1 Q1) ->
     (forall k (m:Mem.t k), Hoare m E2 P2 c2 Q2) ->
     (forall k (m1 m2:Mem.t k), P k m1 m2 -> (P1 k m1 /\ P2 k m2)) ->
     (forall k (m1:Mem.t k), sumbool (Q1 k m1) (~ Q1 k m1)) ->
     (forall k (m2:Mem.t k), sumbool (Q2 k m2) (~ Q2 k m2)) ->
     (equiv P E1 c1 E2 c2 ((rel_pred1 Q1) /-\ (rel_pred2 Q2))).
    Proof.
    intros.
    intro k.
     exists (fun m1 m2 => prod_distr ([[ c1 ]] E0 m1) ([[ c2 ]] E3 m2)); intros.
     apply H3 in H4; destruct H4.
     constructor; intros.
     rewrite prod_distr_fst; unfold lossless in H0; rewrite H0; auto.
     rewrite prod_distr_snd; unfold lossless in H; rewrite H; auto.
     unfold range, prod_distr; intros.
     rewrite Mlet_simpl.
     rewrite (@range_cover _ (Q1 k)  (([[ c1 ]]) E0 m1) (carac (X k))); auto.
     rewrite <- mu_0.
     apply mu_stable_eq.
     refine (@ford_eq_intro _ _ _ _ _); intros.
     unfold carac.
     case (X k n); intros; Usimpl; trivial.
     rewrite Mlet_simpl.
     rewrite (@range_cover _ (Q2 k)  (([[ c2 ]]) E3 m2) (carac (X0 k))); auto.
     rewrite <- mu_0.
     apply mu_stable_eq.
     refine (@ford_eq_intro _ _ _ _ _); intros.
     unfold carac.
     case (X0 k n0); intros; Usimpl; trivial.
     simpl.
     apply H6.
     split; trivial.
     apply H2; trivial.
     apply cover_dec.
     apply H1; trivial.
     apply cover_dec.
    Qed.

    Definition depend_only_pred (P:mem_pred) (X:Vset.t) :=
     forall (k:nat) (m m':Mem.t k), m =={X}m' -> P k m -> P k m'.

    Lemma depend_only_rel_pred1 I X1 X2 :
     depend_only_pred I X1 <->
     depend_only_rel (rel_pred1 I) X1 X2.
    Proof.
     unfold depend_only_pred, depend_only_rel, rel_pred1; split; intros.
     eapply H; eauto.
     apply H with m m m; auto with set.
    Qed.

    Lemma depend_only_rel_pred2 I X1 X2 :
     depend_only_pred I X2 <->
     depend_only_rel (rel_pred2 I) X1 X2.
    Proof.
     unfold depend_only_pred, depend_only_rel, rel_pred2; split; intros.
     eapply H; eauto.
     apply H with m m m; auto with set.
    Qed.


    Section ADV_PRESERVES_BAD.

     Variables X : Vset.t.

     Variables E : env.

     Variables bad : mem_pred.

     Hypothesis bad_dep : depend_only_pred bad X.

     Hypothesis X_global : forall x : VarP.Edec.t,
      Vset.mem x X -> Var.is_global x.

     Hypothesis disjoint_Orcl : Vset.disjoint X Gadv.

     Hypothesis o_preserve_bad : forall k (m:Mem.t k) (t:T.type) (f:Proc.proc t),
      PrSet.mem {| BProc.p_type := t; BProc.p_name := f |} PrOrcl ->
      Hoare m E bad (proc_body E f) bad.

     Lemma a_preserve_bad :forall I c O,
      WFAdv_c E I c O ->
      (forall k (m:Mem.t k), Hoare m E bad c bad).
     Proof.
      induction 1 using WFAdv_c_prop with 
       (P0 := fun I i O (_:WFAdv_i E I i O) =>
        (forall k (m:Mem.t k) , Hoare m E bad [i] bad)); intros.
      apply Hoare_nil; intros; trivial.
      eapply Hoare_cons; eauto.
      eapply Hoare_strengthen;[ | apply Hoare_assign].
      intros.
      unfold upd_pred.
      eapply bad_dep; [ | eauto ].
      red; intros; destruct x.
      rewrite Mem.get_upd_diff; trivial; intro.
      assert (W:Var.is_global x0) by auto with set.
      contradict H0.
      apply VsetP.disjoint_mem_not_mem with (1:=VsetP.disjoint_sym disjoint_Orcl).
      generalize w; rewrite <- H1 in *; destruct x0; auto.

      apply Hoare_random; intros.
      eapply bad_dep;[ | eauto ].
      red; intros; destruct x.
      rewrite Mem.get_upd_diff; trivial; intro.
      assert (W:Var.is_global x1) by auto with set.
      contradict H0.
      apply VsetP.disjoint_mem_not_mem with
       (1:=VsetP.disjoint_sym disjoint_Orcl).
      generalize w; rewrite <- H1 in *; destruct x1; auto.

      apply Hoare_cond.
      eapply Hoare_strengthen; [ | apply IHWFAdv_c1 ].
      unfold andp; tauto.
      eapply Hoare_strengthen; [ | apply IHWFAdv_c2 ].
      unfold andp; tauto.

      eapply Hoare_weaken; [ |  apply Hoare_while ].
      intros m0 (H1, _); trivial.
      intros m0 (H1, _).
      apply IHWFAdv_c; trivial.

      apply Hoare_call; auto; intros.
      eapply bad_dep; [ | eauto ].
      red; intros; rewrite init_mem_global; trivial.
      auto with set.
      eapply bad_dep; [ | eauto ].
      red; intros; rewrite return_mem_global; trivial.
      intro.
      eapply VsetP.disjoint_mem_not_mem with 
       (1 := VsetP.disjoint_sym disjoint_Orcl).
      apply w0.
      rewrite H1; auto with set.
      rewrite H1; auto with set.
      auto with set.

      apply Hoare_call; auto; intros.
      eapply bad_dep; [ | eauto ].
      red; intros; rewrite init_mem_global; auto with set.
      eapply bad_dep; [ | eauto ].
      red; intros; rewrite return_mem_global; trivial.
      intro.
      eapply VsetP.disjoint_mem_not_mem with (1:=VsetP.disjoint_sym disjoint_Orcl).
      apply w1.
      rewrite H2; auto with set.
      rewrite H2; auto with set.
      auto with set.
     Qed.

    End ADV_PRESERVES_BAD.


    Hypothesis o_preserve_bad1 : forall k (m:Mem.t k) (t:T.type) (f:Proc.proc t),
     PrSet.mem {| BProc.p_type := t; BProc.p_name := f |} PrOrcl ->
     Hoare m E1 bad1 (proc_body E1 f) bad1.

    Hypothesis o_preserve_bad2 : forall k (m:Mem.t k) (t:T.type) (f:Proc.proc t),
     PrSet.mem {| BProc.p_type := t; BProc.p_name := f |} PrOrcl ->
     Hoare m E2 bad2 (proc_body E2 f) bad2.

    Inductive slossless_i : env -> I.t -> Prop :=
    | slossless_assign : forall E t (x:Var.var t) e,
      lossless E [x <- e] ->
      slossless_i E (x <- e)
    | slossless_random : forall E t (x:Var.var t) d,
      lossless E [x <$- d] ->
      slossless_i E (x <$- d)
    | slossless_cond : forall E e c1 c2,
      slossless_c E c1 ->
      slossless_c E c2 ->
      slossless_i E (If e then c1 else c2)
    | slossless_while : forall E e c,
      lossless E [while e do c] ->
      slossless_c E c ->
      slossless_i E (while e do c)
    | slossless_call_adv : forall E t (x:Var.var t) f args,
      slossless_c E (proc_body E f) ->
      slossless_i E (x <c- f with args)
    with slossless_c : env -> cmd -> Prop :=
    | slossless_nil : forall E, lossless E nil -> slossless_c E nil
    | slossless_cons : forall E i c,
      slossless_i E i ->
      slossless_c E c ->
      slossless_c E (i::c).

    Scheme slossless_c_prop := Induction for slossless_c Sort Prop
     with slossless_i_prop := Induction for slossless_i Sort Prop.

    Lemma slossless_lossless E c :
     slossless_c E c ->
     lossless E c.
    Proof.
     induction 1 using slossless_c_prop with 
      (P0 := fun E i (_:slossless_i E i) => lossless E [i]); trivial.
     apply lossless_cons; trivial.
     apply lossless_cond; trivial.
     apply lossless_call; trivial.
    Qed.  

    Lemma slossless_app : forall E c1 c2,
     slossless_c E c1 ->
     slossless_c E c2 ->
     slossless_c E (c1 ++ c2).
    Proof.
     intro E'; induction c1.
     intros; simpl; trivial.
     intros; inversion_clear H.
     rewrite <-app_comm_cons.
     apply slossless_cons; auto.
    Qed.

    Lemma local_global : forall v, 
     Var.is_local v <-> ~Var.is_global v.
    Proof.  
     intros (tx, x); destruct x; unfold Var.is_local, Var.is_global; 
      split; simpl; intro; trivialb.
    Qed.

    Variable e_bad : E.expr T.Bool.

    Lemma equiv_while_ind : forall (P:mem_rel) E1 E2 e1 e2 c1 c2,
     (forall k (m1 m2:Mem.t k), P k m1 m2 -> 
      E.eval_expr e1 m1 = E.eval_expr e2 m2 ) ->
     equiv (P /-\ EP1 e1) E1 c1 E2 c2 P ->
     equiv P E1 [while e1 do c1] E2 [while e2 do c2] 
     (fun k (m1 m2:Mem.t k) => P k m1 m2 /\ 
      E.eval_expr e1 m1 = false).
    Proof.
     intros P ? ? e1 e2 c1 c2 H1 H2 k.
     destruct (H2 k).
     destruct (@while_indR k (P k) x E0 e1 c1 E3 e2 c2).
     intros; apply H1; trivial.
     intros.
     apply H.
     split; trivial.
     exists x0; intros.
     apply H0; trivial.
    Qed.

    Lemma equiv_deno_eq : forall (P Q:mem_rel) c1 c2 c1' c2',
     (forall k (m:Mem.t k), ([[ c1 ]]) E1 m == ([[ c1' ]]) E1 m) ->
     (forall k (m:Mem.t k), ([[ c2 ]]) E2 m == ([[ c2' ]]) E2 m) ->
     equiv P E1 c1' E2 c2' Q ->
     equiv P E1 c1 E2 c2 Q.
    Proof.
     intros.
     eapply equiv_trans_eq_mem_l with (P1 := Meq).
     2: eapply equiv_trans_eq_mem_r with (P2 := Meq).
     3: apply H1.
     eapply equiv_strengthen.
     2: apply equiv_eq_sem; intros; auto.
     intros k m1 m2 (W1, W2); trivial.
     eapply equiv_strengthen.
     2: apply equiv_eq_sem; intros; auto.
     intros k m1 m2 (W1, W2); trivial.
     unfold refl_supMR2; intros; auto.
     unfold refl_supMR2; intros; auto.
    Qed.

    Lemma equiv_while_false : forall (P Q:mem_rel) (e:E.expr T.Bool)  c,
     (forall k (m1 m2:Mem.t k), P k m1 m2 -> 
      (Q k m1 m2 /\ E.eval_expr e m1 = false /\ 
       E.eval_expr e m2 = false)) ->
     equiv P E1 [while e do c] E2 [while e do c] Q.
    Proof.
     intros.
     apply equiv_deno_eq with 
      (c1' := [If e _then c ++ [while e do c] ]) 
      (c2' := [If e _then c ++ [while e do c] ]).
     intros; apply deno_while.
     intros; apply deno_while.
     apply equiv_cond.
     intro.
     exists (fun m1 m2 => Munit (m1, m2)); intros.
     destruct H0 as (H0 & H1 & H2).
     apply H in H0.
     decompose [and] H0.
     rewrite H1 in H5.
     discriminate.
     eapply equiv_strengthen;[ | apply equiv_nil ].
     intros.
     apply H.
     destruct H0 as (W1, _); trivial.
     intros.
     apply H in H0.
     decompose [and] H0.
     rewrite H3, H4; trivial.
    Qed.

    Lemma unroll_while_false : forall E (e:E.expr T.Bool) c k (m:Mem.t k) f n,
     E.eval_expr e m = false ->
     mu ([[ unroll_while e c n ]] E m) f == mu ([[ nil ]] E m) f.
    Proof.
     clear.
     induction n; simpl; intros.
     rewrite (deno_cond_elim E e nil nil m f).
     rewrite H; simpl; trivial.
     rewrite (deno_cond_elim E e _ _  m f).  
     rewrite H; simpl; trivial.
    Qed.

    Lemma unroll_while_plus : forall E (e:E.expr T.Bool) c k (m:Mem.t k) f n1 n2,
     mu ([[ unroll_while e c (n1 + n2) ]] E m) f == 
     mu ([[ (unroll_while e c n1) ++ (unroll_while e c n2) ]] E m) f.
    Proof.
     clear; split.
     revert m.
     induction n1; simpl; intros.
     rewrite (deno_cons_elim E _ _ m).
     rewrite Mlet_simpl.
     rewrite (deno_cond_elim E e nil nil m _).
     case_eq (E.eval_expr e m); intros;
      rewrite deno_nil_elim; trivial.

     rewrite (deno_cond_elim E e _ _ m _).
     rewrite (deno_cons_elim E _ _ m).
     rewrite Mlet_simpl.
     rewrite (deno_cond_elim E e _ _ m _).
     case_eq (E.eval_expr e m); intros.
     rewrite deno_app_elim.
     rewrite deno_app_elim.
     apply mu_le_compat; trivial.
     intro.
     rewrite <- deno_app_elim; trivial.
     rewrite deno_nil_elim.
     rewrite deno_nil_elim.
     clear IHn1.
     destruct n2; simpl;
      rewrite (deno_cond_elim E _ _ _ m), H, deno_nil_elim; trivial.

     revert m.
     induction n1; simpl; intros.
     rewrite (deno_cons_elim E _ _ m).
     rewrite Mlet_simpl.
     rewrite (deno_cond_elim E e nil nil m _).
     case_eq (E.eval_expr e m); intros;
      rewrite deno_nil_elim; trivial.

     rewrite (deno_cond_elim E e _ _ m _).
     rewrite (deno_cons_elim E _ _ m).
     rewrite Mlet_simpl.
     rewrite (deno_cond_elim E e _ _ m _).
     case_eq (E.eval_expr e m); intros.
     rewrite deno_app_elim.
     rewrite deno_app_elim.
     apply mu_le_compat; trivial.
     intro.
     rewrite <- deno_app_elim; trivial.
     rewrite deno_nil_elim.
     rewrite deno_nil_elim.
     clear IHn1.
     destruct n2; simpl;
      rewrite (deno_cond_elim E _ _ _ m), H, deno_nil_elim; trivial.
    Qed.


    Lemma deno_while_bad : forall e e' c E (k:nat) (m:Mem.t k),
     ([[ [while e do c] ]]) E m ==
     ([[ [while E.Eop O.Oand {e, !e'} do c; while e do c] ]]) E m.
    Proof.
     intros.
     case_eq ( E.eval_expr (!e') m); intros.

     split.

     rewrite deno_while_unfold.

     apply lub_le with (c:=cDistr (Mem.t k)); intros.

     revert m H.
     induction n; intros; simpl; intros. 
     rewrite (deno_cond_elim E e nil nil m).
     unfold negP, negb.
     case_eq ( E.eval_expr e m); intros; 
      rewrite deno_nil_elim, H0; simpl; trivial.
     rewrite (deno_cons_elim E _ _  m x), Mlet_simpl, 
      deno_while_elim, deno_cond_elim.
     simpl; unfold O.eval_op; simpl.
     rewrite H0; simpl.
     rewrite (deno_nil_elim E m), (deno_while_elim E e c m), 
      deno_cond_elim, H0, (deno_nil_elim E m); trivial.
     rewrite (deno_cond_elim E e _ nil m).
     case_eq ( E.eval_expr e m); intros.

     rewrite (deno_cons_elim E _ _  m), Mlet_simpl,
      (deno_while_elim E _ c m), deno_cond_elim.
     simpl  E.eval_expr in *; unfold O.eval_op in *; simpl in *.
     unfold negP; rewrite H, H0; simpl.

     rewrite (deno_app_elim E c _ m ), (deno_app_elim E c _ m ).
     apply mu_le_compat; trivial; intro m'.
     case_eq ( negb (E.eval_expr e' m')); intros.
     assert (W := IHn m' H1 x).
     rewrite (deno_cons_elim E _ [while e do c] m') in W; trivial.

     rewrite deno_while_elim, deno_cond_elim.
     simpl  E.eval_expr in *; unfold O.eval_op in *; simpl in *.
     rewrite H1, andb_false_r, (deno_nil_elim E m'), 
      (deno_while_unfold_elim E e c m').
     eapply Ole_trans;[ | apply le_lub ].
     simpl; trivial.

     rewrite deno_nil_elim, (deno_cons_elim E _ _ m), Mlet_simpl,
      deno_while_elim, deno_cond_elim.
     simpl E.eval_expr; unfold O.eval_op; simpl; unfold negP.
     rewrite H0; simpl.
     rewrite (deno_nil_elim E m), (deno_while_elim E e c m), 
      deno_cond_elim, H0; simpl.
     rewrite (deno_nil_elim E m); trivial.

     Focus 2.
     split; simpl; intros.
     rewrite (deno_cons_elim E _ [while e do c]  m), Mlet_simpl, 
      (deno_while_elim E _ c m), (deno_cond_elim E _ _ _ m).
     simpl  E.eval_expr in *; unfold O.eval_op in *; simpl in *.
     rewrite H, andb_false_r, (deno_nil_elim E m); trivial.
     rewrite (deno_cons_elim E _ [while e do c]  m), Mlet_simpl, 
      (deno_while_elim E _ c m), (deno_cond_elim E _ _ _ m).
     simpl  E.eval_expr in *; unfold O.eval_op in *; simpl in *.
     rewrite H, andb_false_r, (deno_nil_elim E m); trivial.

     simpl; intros. 
     rewrite (deno_cons_elim E _ _  m), Mlet_simpl, 
      (deno_while_unfold_elim E _ c m).
     apply lub_le; intros; simpl.
     revert m H.
     induction n; simpl; intros.
     rewrite (deno_cond_elim E _ _ _ m).
     simpl  E.eval_expr in *; unfold O.eval_op in *; simpl in *.
     rewrite H; simpl.
     rewrite (deno_while_elim E _ c m), (deno_cond_elim E _ _ _ m).
     case_eq ( E.eval_expr e m); intros; simpl;
      rewrite (deno_nil_elim E m);
       unfold negP; rewrite H0, H; simpl; auto.
     rewrite (deno_while_elim E _ c m), (deno_cond_elim E _ _ _ m), H0; auto.

     rewrite (deno_while_elim E _ c m), (deno_cond_elim E _ _ _ m), 
      (deno_cond_elim E _ _ _ m).
     simpl  E.eval_expr in *; unfold O.eval_op in *; simpl in *.
     rewrite H; simpl.
     case_eq ( E.eval_expr e m); intros; simpl.
     rewrite (deno_app_elim E _ _ m), (deno_app_elim E _ _ m).
     apply mu_le_compat; trivial; intro m'.
     case_eq ( negb (E.eval_expr e' m')); intros. 
     apply IHn; auto.
     rewrite unroll_while_false, deno_nil_elim.
     unfold negP; rewrite H1; simpl.
     rewrite andb_false_r; simpl; auto.
     simpl  E.eval_expr in *; unfold O.eval_op in *; simpl in *.
     rewrite H1, andb_false_r; trivial.
     rewrite (deno_nil_elim E m), (deno_nil_elim E m).
     unfold negP; rewrite H, H0; simpl.
     rewrite (deno_while_elim E _ c m), (deno_cond_elim E _ _ _ m), H0, 
      (deno_nil_elim E m); trivial.
    Qed.

    Hypothesis bad_orcl : forall (t:T.type) (f:Proc.proc t),
     PrSet.mem {| BProc.p_type := t; BProc.p_name := f |} PrOrcl ->
     slossless_c E1 (proc_body E1 f) ->
     slossless_c E2 (proc_body E2 f) ->
     proc_params E1 f = proc_params E2 f ->
     equiv ((notR (rel_pred1 bad1) /-\ notR (rel_pred2 bad2)) /-\ Inv /-\ 
      (fun k m1 m2 =>  m1 =={ Vset_of_var_decl (proc_params E1 f) } m2))
     E1 (proc_body E1 f) E2 (proc_body E2 f)
     ((eqR (rel_pred1 bad1) (rel_pred2 bad2)) /-\
      ((notR (rel_pred1 bad1)) |-> 
       (Inv /-\ kreq_mem Gadv /-\ 
        (fun k m1 m2 =>
         E.eval_expr (proc_res E1 f) m1 = E.eval_expr (proc_res E2 f) m2)))).

    Lemma equiv_bad_inv : forall I c O,
     WFAdv_c E1 I c O ->
     (forall x, Vset.mem x I -> Var.is_local x) ->
     slossless_c E1 c ->
     slossless_c E2 c ->
     equiv ((eqR (rel_pred1 bad1) (rel_pred2 bad2)) /-\ 
      ((notR (rel_pred1 bad1)) |-> (Inv /-\ (kreq_mem (Vset.union Gadv I)))))
     E1 c E2 c 
     ((eqR (rel_pred1 bad1) (rel_pred2 bad2)) /-\ 
      ((notR (rel_pred1 bad1)) |-> (Inv /-\ kreq_mem (Vset.union Gadv O)))).
    Proof.
     induction 1 using WFAdv_c_prop with 
      (P0 := fun I i O (_:WFAdv_i E1 I i O)  =>
       (forall x, Vset.mem x I -> Var.is_local x) ->
       slossless_i E1 i -> slossless_i E2 i ->
       equiv ((eqR (rel_pred1 bad1) (rel_pred2 bad2)) /-\ 
        ((notR (rel_pred1 bad1)) |->
         (Inv /-\ kreq_mem (Vset.union Gadv I))))
       E1 [i] E2 [i] 
       ((eqR (rel_pred1 bad1) (rel_pred2 bad2)) /-\ 
        ((notR (rel_pred1 bad1)) |-> 
         (Inv /-\ kreq_mem (Vset.union Gadv O))))); 
      intros I_local lossless1 lossless2; intros.

     (* nil *)
     apply equiv_nil.

     (* cons *)
     inversion lossless1.
     inversion lossless2.
     eapply equiv_cons; eauto using WFAdv_i_local.

     (* assign *)
     eapply equiv_strengthen;[ | apply equiv_assign].
     intros k m1 m2 ((H1,H2),H3); unfold kreq_mem in *.
     destruct x.

     assert (HX1:m1 =={ X1}m1 {!v <-- E.eval_expr e m1!}).
     red; intros; rewrite Mem.get_upd_diff; trivial; intro.
     assert (W: Var.is_global x) by auto with set.
     contradict H.
     apply VsetP.disjoint_mem_not_mem with
      (1:=VsetP.disjoint_sym disjoint_Orcl1).
     generalize w; rewrite <- H0 in *; destruct x; auto.

     assert (HX2:m2 =={ X2}m2 {!v <-- E.eval_expr e m2!}).
     red; intros; rewrite Mem.get_upd_diff; trivial; intro.
     assert (W: Var.is_global x) by auto with set.
     contradict H.
     apply VsetP.disjoint_mem_not_mem with
      (1:=VsetP.disjoint_sym disjoint_Orcl2).
     generalize w; rewrite <- H0 in *; destruct x; auto.

     unfold eqR, impR, andR in *; split.
     split; intros.
     revert H.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     case_eq (Var.is_global v); intro.
     apply w in H.
     intros.
     rewrite depend_only_fv_expr_subset with (m2 := m2) (X :=  fv_expr bad2_expr).
     apply H1.
     unfold rel_pred1, bad1, EPp.
     rewrite depend_only_fv_expr_subset with (m2 :=  (m1 {!v <-- E.eval_expr e m1!})) (X :=  fv_expr bad1_expr); auto with set.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H5 in H4.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H4.
     auto.
     auto with set.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H5 in H4.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad2_adv.
     apply H4.
     auto.
     auto with set.
     unfold bad1, bad2, EPp; simpl.
     intros.
     rewrite depend_only_fv_expr_subset with (m2 := m2) (X :=  fv_expr bad2_expr).
     apply H1.
     unfold rel_pred1, bad1, EPp.
     rewrite depend_only_fv_expr_subset with (m2 :=  (m1 {!v <-- E.eval_expr e m1!})) (X :=  fv_expr bad1_expr); auto with set.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H5 in H4.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H4.
     auto.
     auto with set.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H5 in H4.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad2_adv.
     apply H4.
     auto.
     revert H.
     unfold rel_pred1, rel_pred2.
     case_eq (Var.is_global v); intro.
     apply w in H.
     unfold bad1, bad2, EPp; simpl.
     intros.
     rewrite depend_only_fv_expr_subset with (m2 := m1) (X :=  fv_expr bad1_expr).
     apply H2.
     unfold rel_pred2, bad2, EPp.
     rewrite depend_only_fv_expr_subset with (m2 := (m2 {!v <-- E.eval_expr e m2!})) (X :=  fv_expr bad2_expr); auto with set.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H5 in H4.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad2_adv.
     apply H4.
     auto.
     auto with set.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H5 in H4.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H4.
     auto.
     auto with set.
     unfold bad1, bad2, EPp; simpl.
     intros.
     rewrite depend_only_fv_expr_subset with (m2 := m1) (X :=  fv_expr bad1_expr).
     apply H2.
     unfold rel_pred2, bad2, EPp.
     rewrite depend_only_fv_expr_subset with (m2 := (m2 {!v <-- E.eval_expr e m2!})) (X :=  fv_expr bad2_expr); auto with set.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H5 in H4.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad2_adv.
     apply H4.
     auto.
     auto with set.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H5 in H4.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H4.
     auto.

     intros.
     destruct H3.
     intro; elim H.
     revert H0.
     unfold rel_pred1.
     unfold bad1, EPp; simpl.
     case_eq (Var.is_global v); intro.
     apply w in H0.
     intros.
     rewrite depend_only_fv_expr_subset with (m2 := m1) (X :=  fv_expr bad1_expr).
     apply H3.
     auto with set.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H5 in H4.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H4.
     auto.
     intros.
     rewrite depend_only_fv_expr_subset with (m2 := m1) (X :=  fv_expr bad1_expr).
     apply H3.
     auto with set.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H5 in H4.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H4.
     auto.
     split.
     apply inv_dep with m1 m2; auto.
     erewrite equiv_WFRead;[ | | | | apply H3 ]; trivial; 
      auto with set.
     destruct v; apply equiv_WFWrite; trivial.
     rewrite Gcomm_empty; auto with set.

     (* random *)
     apply equiv_case1 with (rel_pred1 bad1); auto.
     apply equiv_weaken with 
      ((rel_pred1 bad1) /-\ (rel_pred2 bad2)).
     intros k m1 m2 (H1, H2); split.
     split; intro; tauto.
     intro; elim H; trivial.
     apply equiv_rel_pred with bad1 bad2; trivial; intros.
     apply slossless_lossless     .
     constructor; auto.
     apply slossless_nil.
     apply lossless_nil.
     apply slossless_lossless     .
     constructor; auto.
     apply slossless_nil.
     apply lossless_nil.
     eapply a_preserve_bad; auto.
     3: apply bad1_adv.
     red; intros.
     unfold bad1, EPp in *.
     rewrite depend_only_fv_expr_subset with (m2 := m0) (X :=  fv_expr bad1_expr); eauto.
     auto with set.
     auto.
     eapply GA_cons.
     apply GA_random; eauto.
     apply GA_nil.
     eapply a_preserve_bad; auto.
     3: apply bad2_adv.
     red; intros.
     unfold bad2, EPp in *.
     rewrite depend_only_fv_expr_subset with (m2 := m0) (X :=  fv_expr bad2_expr); eauto.
     auto with set.
     auto.
     eapply WFAdv_c_trans; eauto.
     eapply GA_cons.
     apply GA_random; eauto.
     apply GA_nil.
     destruct H as (((H1, H2) , H3), H4).
     split; auto.
     apply H1; auto.
     destruct (bad1_dec m1 m1); auto.
     destruct (bad2_dec m2 m2); auto.
     eapply equiv_strengthen;[ | apply equiv_random].
     intros k m1 m2 ((H1, H2),H4); unfold kreq_mem in *.
     split. 
     unfold eq_support.
     apply EqObs_d_fv_expr.
     red.
     unfold WFReadD in w0; intros.
     destruct (w0 _ H); auto with set.
     destruct H2; auto with set.
     destruct H0.
     destruct H2; auto with set.
     rewrite Gcomm_empty in H0. 
     elimtype False; apply (Vset.empty_spec H0).
     unfold forall_random; intros.
     destruct x.
     assert (HX1:m1 =={ X1}m1 {! v0 <-- v!}).
     red; intros; rewrite Mem.get_upd_diff; trivial; intro.
     assert (W: Var.is_global x) by auto with set.
     contradict H0.
     apply VsetP.disjoint_mem_not_mem with
      (1:=VsetP.disjoint_sym disjoint_Orcl1).
     generalize w; rewrite <- H3 in *; destruct x; auto.
     assert (HX2:m2 =={ X2}m2 {! v0 <-- v!}).
     red; intros; rewrite Mem.get_upd_diff; trivial; intro.
     assert (W: Var.is_global x) by auto with set.
     contradict H0.
     apply VsetP.disjoint_mem_not_mem with
      (1:=VsetP.disjoint_sym disjoint_Orcl2).
     generalize w; rewrite <- H3 in *; destruct x; auto.
     unfold eqR, impR, andR in *; split.
     destruct H1.
     split; intros.
     case_eq (Var.is_global v0); intro.
     apply w in H5.
     unfold rel_pred1, rel_pred2, bad1, bad2, EPp in *.
     erewrite depend_only_fv_expr_subset.
     apply H0.
     erewrite depend_only_fv_expr_subset.
     apply H3.
     apply VsetP.subset_refl.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H7 in H6.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H6.
     auto.
     apply VsetP.subset_refl.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H7 in H6.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad2_adv.
     apply H6.
     auto.
     unfold rel_pred1, rel_pred2, bad1, bad2, EPp in *.
     erewrite depend_only_fv_expr_subset.
     apply H0.
     erewrite depend_only_fv_expr_subset.
     apply H3.
     apply VsetP.subset_refl.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H7 in H6.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H6.
     auto.
     apply VsetP.subset_refl.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H7 in H6.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad2_adv.
     apply H6.
     auto.
     case_eq (Var.is_global v0); intro.
     apply w in H5.
     unfold rel_pred1, rel_pred2, bad1, bad2, EPp in *.
     erewrite depend_only_fv_expr_subset.
     apply H1.
     erewrite depend_only_fv_expr_subset.
     apply H3.
     apply VsetP.subset_refl.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H7 in H6.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad2_adv.
     apply H6.
     auto.
     apply VsetP.subset_refl.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H7 in H6.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H6.
     auto.
     unfold rel_pred1, rel_pred2, bad1, bad2, EPp in *.
     erewrite depend_only_fv_expr_subset.
     apply H1.
     erewrite depend_only_fv_expr_subset.
     apply H3.
     apply VsetP.subset_refl.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H7 in H6.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad2_adv.
     apply H6.
     auto.
     apply VsetP.subset_refl.
     red; intros.
     rewrite Mem.get_upd_diff; trivial.
     intro.
     rewrite <- H7 in H6.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H6.
     auto.
     intros.
     revert H.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     intros.
     split.
     apply inv_dep with m1 m2; auto.
     apply H2; auto.
     destruct v0; apply equiv_WFWrite; trivial.
     apply H2; auto.
     apply H2; auto.

     (* cond *)
     apply equiv_case1 with (rel_pred1 bad1); auto.
     apply equiv_weaken with ((rel_pred1 bad1) /-\ (rel_pred2 bad2)).
     intros k m1 m2 (H1, H2); split.
     split; intro; tauto.
     intro; elim H3; trivial.
     apply equiv_rel_pred with bad1 bad2; trivial; intros.
     apply slossless_lossless     .
     constructor; auto.
     apply slossless_nil.
     apply lossless_nil.
     apply slossless_lossless     .
     constructor; auto.
     apply slossless_nil.
     apply lossless_nil.
     eapply a_preserve_bad; auto.
     rewrite depend_only_rel_pred1 with (X2 := Vset.empty); eauto.
     3: apply bad1_adv.
     red; intros.
     unfold rel_pred1, bad1, EPp in *.
     erewrite depend_only_fv_expr_subset with (m2 := m1) (X :=  fv_expr bad1_expr); eauto.
     auto with set.
     auto.
     eapply GA_cons.
     apply GA_cond; eauto.
     apply GA_nil.
     eapply a_preserve_bad; auto.
     rewrite depend_only_rel_pred2 with (X1 := Vset.empty); eauto.
     3: apply bad2_adv.
     red; intros.
     unfold rel_pred2, bad2, EPp in *.
     rewrite depend_only_fv_expr_subset with (m2 := m2) (X :=  fv_expr bad2_expr); eauto.
     auto with set.
     auto.
     auto with set.     
     eapply WFAdv_c_trans; eauto.
     eapply GA_cons.
     apply GA_cond; eauto.
     apply GA_nil.
     destruct H1 as (((H1, H2) , H3), H4).
     split; auto.
     apply H1; auto.
     destruct (bad1_dec m1 m1); auto.
     destruct (bad2_dec m2 m2); auto.
     apply equiv_cond.
     eapply equiv_strengthen; 
      [ | eapply equiv_weaken; [ | apply IHWFAdv_c1] ]; trivial.
     intros k m1 m2 ((W1,W2) , _); trivial.
     intros.
     destruct H1.
     split; trivial.
     intro.
     destruct H2; trivial.
     split; trivial.
     eapply req_mem_weaken; eauto.
     apply VsetP.subset_union_ctxt; auto with set.     
     inversion lossless1; trivial.
     inversion lossless2; trivial.
     eapply equiv_strengthen; 
      [ | eapply equiv_weaken; [ | apply IHWFAdv_c2] ]; trivial.
     intros k m1 m2 ((W1,W2) , _); trivial.
     intros.
     destruct H1.
     split; trivial.
     intro.
     destruct H2; trivial.
     split; trivial.
     eapply req_mem_weaken; eauto.
     apply VsetP.subset_union_ctxt; auto with set.
     inversion lossless1; trivial.
     inversion lossless2; trivial.
     intros k m1 m2 ((H1, H2), H3).
     destruct H2 as [H4 H5]; trivial.
     eapply equiv_WFRead;[ apply w | | | apply H5 ]; auto with arith.
     rewrite Gcomm_empty; auto with set.
     auto with set.

     (* while *)
     apply equiv_deno_eq with 
      (c1' := [while (E.Eop O.Oand {e, ! bad1_expr}) do c; 
       while e do c])
      (c2' := [while (E.Eop O.Oand {e, ! bad2_expr}) do c; 
       while e do c] ).
     intros; rewrite deno_while_bad; trivial.
     intros; rewrite deno_while_bad; trivial.

     apply equiv_cons with 
      ((eqR (rel_pred1 bad1) (rel_pred2 bad2) /-\
       (~- rel_pred1 bad1 |-> 
        Inv /-\ kreq_mem (Vset.union Gadv I))) /-\ 
      (fun k m1 m2 => 
       E.eval_expr ( E.Eop O.Oand {e, !bad1_expr} ) m1 = false)).

     eapply equiv_weaken;[ | apply equiv_while_ind ].

     intros.
     revert H0.
     simpl; unfold O.eval_op; simpl.
     intros ((H0, H1), H2). 
     split; trivial.
     split; trivial.

     intros k m1 m2 ((H0, H1), H2).
     simpl; unfold O.eval_op; simpl.
     destruct (decMR_EP1 bad1_expr m1 m2).
     rewrite e0.
     apply H0 in e0.
     rewrite e0.
     simpl.
     repeat rewrite andb_false_r; trivial.

     destruct H2; trivial.
     assert ((~- rel_pred2 bad2) k m1 m2).
     intro; apply n; auto.
     apply H1; trivial.
     apply is_true_negb in n.
     apply is_true_negb in H4.
     rewrite n, H4.
     repeat rewrite andb_true_r.
     erewrite equiv_WFRead.
     reflexivity.
     apply w.
     2: apply VsetP.subset_refl.
     rewrite Gcomm_empty; auto with set.
     apply H3.

     eapply equiv_strengthen; 
      [ | eapply equiv_weaken; [ | apply IHWFAdv_c ] ]; auto.
     intros k m1 m2 (W1, W2); trivial.
     intros k m1 m2 (W1, W2); trivial.
     split; trivial.
     intro; split.
     apply W2; trivial.
     red; intros.
     eapply req_mem_weaken.
     2: apply W2; trivial.
     apply VsetP.subset_union_ctxt; auto with set.
     eapply WFAdv_c_subset; eauto.
     inversion lossless1; trivial.
     inversion lossless2; trivial.

     simpl; unfold O.eval_op; simpl.
     apply equiv_case1 with (EP1 bad1_expr); auto.

     eapply equiv_weaken with ((rel_pred1 bad1) /-\ (rel_pred2 bad2)).
     intros k m1 m2 (W1, W2).
     split.
     split; intro; auto.
     intro.
     elim H0; trivial.

     apply equiv_rel_pred with bad1 bad2.
     inversion lossless1; trivial.
     inversion lossless2; trivial.

     intros.
     eapply a_preserve_bad; auto.
     rewrite depend_only_rel_pred1 with (X2 := Vset.empty); eauto.
     3: apply bad1_adv.
     red; intros.
     unfold rel_pred1, bad1, EPp in *.
     rewrite depend_only_fv_expr_subset with (m2 := m1) (X :=  fv_expr bad1_expr); eauto.
     auto with set.
     auto.
     eapply GA_cons.
     eapply GA_while; eauto.
     apply GA_nil.
     eapply a_preserve_bad; auto.
     rewrite depend_only_rel_pred2 with (X1 := Vset.empty); eauto.
     3: apply bad2_adv.
     red; intros.
     unfold rel_pred2, bad2, EPp in *.
     rewrite depend_only_fv_expr_subset with (m2 := m2) (X :=  fv_expr bad2_expr); eauto.
     auto with set.
     auto.
     eapply WFAdv_c_trans; eauto.
     eapply GA_cons.
     eapply GA_while; eauto.
     apply GA_nil.

     intros k m1 m2 (((W1, _) , _), W2).
     split.
     apply W2.
     apply W1.
     apply W2.
     intros.
     apply bad1_dec with (m2 := m1).
     intros.
     apply bad2_dec with (m1 := m2).

     apply equiv_while_false.
     intros k m1 m2 ((W1, W2), W3).
     split; trivial.

     assert (  E.eval_expr e m1 = E.eval_expr e m2).
     eapply equiv_WFRead;[ apply w | | | apply W1 ]; 
      auto with arith.
     rewrite Gcomm_empty; auto with set.
     auto with set.
     rewrite <- H0.
     apply andb_false_elim in W2.
     destruct W2.
     auto.
     unfold notR, EP1 in W3.
     apply is_true_negb in W3.
     rewrite e0 in W3.
     discriminate.

     (* Call Orcl *)
     apply equiv_case1 with (rel_pred1 bad1); auto.
     apply equiv_weaken with 
      ((rel_pred1 bad1) /-\ (rel_pred2 bad2)).
     intros k m1 m2 (H1, H2); split.
     split; intro; tauto.
     intro H3; elim H3; trivial.
     apply equiv_rel_pred with bad1 bad2; trivial; intros.
     apply slossless_lossless.
     constructor; auto.
     apply slossless_nil.
     apply lossless_nil.
     apply slossless_lossless.
     constructor; auto.
     apply slossless_nil.
     apply lossless_nil.
     eapply a_preserve_bad; auto.
     3: apply bad1_adv.
     red; intros.
     unfold rel_pred1, bad1, EPp in *.
     rewrite depend_only_fv_expr_subset with (m2 := m0) (X :=  fv_expr bad1_expr); eauto.
     auto with set.
     auto.
     eapply GA_cons.
     eapply GA_call_orcl; eauto.
     apply GA_nil.
     eapply a_preserve_bad; auto.
     3: apply bad2_adv.
     red; intros.
     unfold rel_pred2, bad2, EPp in *.
     rewrite depend_only_fv_expr_subset with (m2 := m0) (X := fv_expr bad2_expr); eauto.
     auto with set.
     auto.
     eapply WFAdv_c_trans; eauto.
     eapply GA_cons.
     eapply GA_call_orcl; eauto.
     apply GA_nil.
     destruct H as (((H1, H2) , H3), H4).
     split; auto.
     apply H1; auto.
     destruct (bad1_dec m1 m1); auto.
     destruct (bad2_dec m2 m2); auto.
     eapply equiv_call; intros;[ | | apply bad_orcl; trivial].

     (** Init *)
     assert (W:forall t (x:Var.var t),  Vset.mem x 
      (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x).
     intros; apply Vset_of_var_decl_ind with 
      (P:= fun t (x:Var.var t) => Var.is_local x) (lv:= proc_params E1 f); auto.
     intros; change (Var.vis_local x1).
     apply proc_params_local with E1 t f; trivial.
     destruct H as (((H1,H2) & H3) & H4).
     assert (HX1:m1 =={ X1}init_mem E1 f args m1).
     red; intros; rewrite init_mem_global; trivial.
     apply inv_global; rewrite VsetP.union_spec; auto.
     assert (HX2:m2 =={ X2}init_mem E2 f args m2).
     red; intros; rewrite init_mem_global; trivial.
     apply inv_global; rewrite VsetP.union_spec; auto.
     split.
     split.
     intro.
     elim H4.
     revert H.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     intros.
     erewrite depend_only_fv_expr_subset.
     apply H.
     apply VsetP.subset_refl.
     red; intros.
     rewrite init_mem_global; trivial.
     auto.
     intro Heq; elim H4.
     revert Heq.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     erewrite depend_only_fv_expr_subset.
     intros.
     apply H2.
     apply Heq.
     apply VsetP.subset_refl.
     red; intros.
     rewrite init_mem_global; trivial.
     auto.
     split.
     eapply inv_dep; [ | | apply H3]; auto.
     red; intros.

     rewrite init_mem_eq2 with (E2 := E2) (a2 := args); trivial.
     apply init_mem_local; auto.
     generalize args w.
     generalize (Proc.targs f). induction args0; simpl; auto; intros.
     rewrite IHargs0; auto.
     rewrite (@equiv_WFRead Gadv a p I k m1 m2); auto.
     rewrite Gcomm_empty; auto with set.
     auto with set.
     apply H3; trivial.
     apply Eq_orcl_params_12; auto.

     (** Post *)
     destruct H as (((H1,H2) & H3) & H4).
     destruct H0 as ((H5, H6), H7).

     assert (HX1:m1' =={ X1}return_mem E1 x f m1 m1').
     red; intros; rewrite return_mem_global; trivial.
     assert (W: Var.is_global x0) by auto with set.
     contradict H.
     apply VsetP.disjoint_mem_not_mem with
      (1:=VsetP.disjoint_sym disjoint_Orcl1).
     generalize w; rewrite <- H in *; destruct x; auto.
     auto with set.

     assert (HX2:m2' =={ X2}return_mem E2 x f m2 m2').
     red; intros; rewrite return_mem_global; trivial.
     assert (W: Var.is_global x0) by auto with set.
     contradict H.
     apply VsetP.disjoint_mem_not_mem with
      (1:=VsetP.disjoint_sym disjoint_Orcl2).
     generalize w; rewrite <- H in *; destruct x; auto.
     auto with set.

     split.
     split; intro.

     revert H.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     intros.
     erewrite depend_only_fv_expr_subset.
     apply H5.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     erewrite depend_only_fv_expr_subset.
     apply H.
     apply VsetP.subset_refl.
     red; intros.
     rewrite return_mem_global; trivial.
     intro.
     rewrite <- H8 in H0.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H0.
     auto.
     auto with set.
     apply VsetP.subset_refl.
     red; intros.
     rewrite return_mem_global; trivial.
     intro.
     rewrite <- H8 in H0.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad2_adv.
     apply H0.
     auto.
     auto with set.

     revert H.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     intros.
     erewrite depend_only_fv_expr_subset.
     apply H6.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     erewrite depend_only_fv_expr_subset.
     apply H.
     apply VsetP.subset_refl.
     red; intros.
     rewrite return_mem_global; trivial.
     intro.
     rewrite <- H8 in H0.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad2_adv.
     apply H0.
     auto.
     auto with set.
     apply VsetP.subset_refl.
     red; intros.
     rewrite return_mem_global; trivial.
     intro.
     rewrite <- H8 in H0.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H0.
     auto.
     auto with set.

     intro.
     destruct H7.
     intro; elim H.
     revert H0.
     unfold rel_pred1.
     unfold bad1, EPp; simpl.
     intros.
     erewrite depend_only_fv_expr_subset.
     apply H0.
     apply VsetP.subset_refl.
     red; intros.
     rewrite return_mem_global; trivial.
     intro.
     rewrite <- H8 in H7.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H7.
     auto.
     auto with set.
     split.
     eapply inv_dep; [ | | apply H0]; auto.
     red; intros.
     red; intros.
     destruct (Vset.ET.eq_dec x x0).
     inversion e.
     repeat rewrite return_mem_dest.
     apply H7.
     apply Vset.union_correct in H8; destruct H8.
     repeat rewrite return_mem_global; auto with set.
     apply H7; auto.

     assert (Vset.mem x0 I).
     unfold add_read in H8; destruct (Var.is_global x); auto.
     rewrite VsetP.add_spec in H8; destruct H8; trivial.
     elim (n H8).
     repeat rewrite return_mem_local; auto.
     apply H3; auto with set.
     inversion lossless1.
     inversion H3.
     trivial.
     inversion lossless2.
     inversion H3.
     trivial.
     apply Eq_orcl_params_12.
     trivial.

     (* Call Adv *)
     apply equiv_case1 with (rel_pred1 bad1); auto.
     apply equiv_weaken with ((rel_pred1 bad1) /-\ (rel_pred2 bad2)).
     intros k m1 m2 (H1, H2); split.
     split; intro; tauto.
     intro H3; elim H3; trivial.
     apply equiv_rel_pred with bad1 bad2; trivial; intros.
     apply slossless_lossless     .
     constructor; auto.
     apply slossless_nil.
     apply lossless_nil.
     apply slossless_lossless     .
     constructor; auto.
     apply slossless_nil.
     apply lossless_nil.
     eapply a_preserve_bad; auto.
     rewrite depend_only_rel_pred1 with (X2 := Vset.empty); eauto.
     3: apply bad1_adv.
     red; intros.
     unfold rel_pred1, bad1, EPp in *.
     rewrite depend_only_fv_expr_subset with (m2 := m1) (X :=  fv_expr bad1_expr); eauto.
     auto with set.
     auto.
     auto with set.
     eapply GA_cons.
     eapply GA_call_adv; eauto.
     apply GA_nil.
     eapply a_preserve_bad; auto.
     rewrite depend_only_rel_pred2 with (X1 := Vset.empty); eauto.
     3: apply bad2_adv.
     red; intros.
     unfold rel_pred2, bad2, EPp in *.
     rewrite depend_only_fv_expr_subset with (m2 := m2) (X :=  fv_expr bad2_expr); eauto.
     auto with set.
     auto.
     auto with set.
     eapply WFAdv_c_trans; eauto.
     eapply GA_cons.
     eapply GA_call_adv; eauto.
     apply GA_nil.
     destruct H0 as (((H1, H2) , H3), H4).
     split; auto.
     apply H1; auto.
     destruct (bad1_dec m1 m1); auto.
     destruct (bad2_dec m2 m2); auto.

     destruct (Eq_adv_decl_12 f) as (Heq1, (Heq2, Heq3)); trivial.

     assert (W:forall t (x:Var.var t),  Vset.mem x 
      (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x).
     intros; apply Vset_of_var_decl_ind with 
      (P:= fun t (x:Var.var t) => Var.is_local x) (lv:= proc_params E1 f); auto.
     intros; change (Var.vis_local x1).
     apply proc_params_local with E1 t f; trivial.
     assert (W0:forall x, Vset.mem x 
      (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x). 
     intros (t0,x0); auto.

     eapply equiv_call.
     3: rewrite <- Heq2; apply IHWFAdv_c; auto.
     intros.
     destruct H0 as (((H1,H2) & H3) & H4).
     assert (HX1:m1 =={ X1}init_mem E1 f args m1).
     red; intros; rewrite init_mem_global; trivial.
     apply inv_global; rewrite VsetP.union_spec; auto.
     assert (HX2:m2 =={ X2}init_mem E2 f args m2).
     red; intros; rewrite init_mem_global; trivial.
     apply inv_global; rewrite VsetP.union_spec; auto.
     split.
     split.
     intro.
     elim H4.
     revert H.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     intros.
     erewrite depend_only_fv_expr_subset.
     apply H0.
     apply VsetP.subset_refl.
     red; intros.
     rewrite init_mem_global; trivial.
     auto.
     intro Heq; elim H4.
     revert Heq.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     erewrite depend_only_fv_expr_subset.
     intros.
     apply H2.
     apply Heq.
     apply VsetP.subset_refl.
     red; intros.
     rewrite init_mem_global; trivial.
     auto.
     split.
     eapply inv_dep; [ | | apply H3]; auto.
     red; red; intros.
     rewrite (init_mem_eq2 E1 E2 f args args m1 Heq1); trivial.
     rewrite VsetP.union_spec in H5; destruct H5.
     repeat rewrite init_mem_global; auto with set.
     apply H3; trivial; auto with set.
     apply init_mem_local; auto.
     generalize args w0.
     generalize (Proc.targs f). induction args0; simpl; auto; intros.
     rewrite IHargs0; auto.
     rewrite (@equiv_WFRead Gadv a p I k m1 m2); auto with set.
     rewrite Gcomm_empty; auto with set.
     apply H3; trivial.

     intros k m1 m1' m2 m2' (((H1, H2), H3), H4) ((H5, H6), H7).

     assert (HX1:m1' =={ X1}return_mem E1 x f m1 m1').
     red; intros; rewrite return_mem_global; trivial.
     assert (Var.is_global x0) by auto with set.
     contradict H0.
     apply VsetP.disjoint_mem_not_mem with
      (1:=VsetP.disjoint_sym disjoint_Orcl1).
     generalize w; rewrite <- H0 in *; destruct x; auto.
     auto with set.
     assert (HX2:m2' =={ X2}return_mem E2 x f m2 m2').
     red; intros; rewrite return_mem_global; trivial.
     assert (Var.is_global x0) by auto with set.
     contradict H0.
     apply VsetP.disjoint_mem_not_mem with
      (1:=VsetP.disjoint_sym disjoint_Orcl2).
     generalize w; rewrite <- H0 in *; destruct x; auto.
     auto with set.

     split.
     split; intro.

     revert H.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     intros.
     erewrite depend_only_fv_expr_subset.
     apply H5.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     erewrite depend_only_fv_expr_subset.
     apply H0.
     apply VsetP.subset_refl.
     red; intros.
     rewrite return_mem_global; trivial.
     intro.
     rewrite <- H9 in H8.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H8.
     auto.
     auto with set.
     apply VsetP.subset_refl.
     red; intros.
     rewrite return_mem_global; trivial.
     intro.
     rewrite <- H9 in H8.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad2_adv.
     apply H8.
     auto.
     auto with set.

     revert H0.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     intros.
     erewrite depend_only_fv_expr_subset.
     apply H6.
     unfold rel_pred1, rel_pred2.
     unfold bad1, bad2, EPp; simpl.
     erewrite depend_only_fv_expr_subset.
     apply H0.
     apply VsetP.subset_refl.
     red; intros.
     rewrite return_mem_global; trivial.
     intro.
     rewrite <- H9 in H8.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad2_adv.
     apply H8.
     auto.
     auto with set.
     apply VsetP.subset_refl.
     red; intros.
     rewrite return_mem_global; trivial.
     intro.
     rewrite <- H9 in H8.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H8.
     auto.
     auto with set.

     intro.
     destruct H7.
     intro; elim H0.
     revert H7.
     unfold rel_pred1.
     unfold bad1, EPp; simpl.
     intros.
     erewrite depend_only_fv_expr_subset.
     apply H7.
     apply VsetP.subset_refl.
     red; intros.
     rewrite return_mem_global; trivial.
     intro.
     rewrite <- H9 in H8.
     eapply VsetP.disjoint_mem_not_mem.
     apply bad1_adv.
     apply H8.
     auto.
     auto with set.
     split.
     eapply inv_dep; [ | | apply H7]; auto.
     red; red; intros.

     destruct (Var.eq_dec x x0).
     inversion e; simpl.
     repeat rewrite return_mem_dest.
     rewrite <- Heq3.
     apply equiv_WFRead with (IA:= Gadv) (1 := w); auto with set.
     rewrite Gcomm_empty; auto with set.
     rewrite VsetP.union_spec in H9; destruct H9.
     repeat rewrite return_mem_global; auto with set.
     assert (Vset.mem x0 I). 
     unfold add_read in H9; destruct (Var.is_global x); auto.
     rewrite VsetP.add_spec in H9; destruct H9; trivial.
     elim (n1 H9).
     repeat rewrite return_mem_local; auto. 
     apply H3; auto with set.

     inversion lossless1; subst.
     apply inj_pair2_eq_dec in H4; subst; trivial.
     intros.
     generalize (T.eqb_spec x0 y).
     case (T.eqb x0 y); auto.
     rewrite Heq2.
     inversion lossless2; subst.
     apply inj_pair2_eq_dec in H4; subst; trivial.
     intros.
     generalize (T.eqb_spec x0 y).
     case (T.eqb x0 y); auto.
    Qed.

   End EQ_OBS_INV.

  End UPTO2.

 End WF_ADV.

 Hint Constructors WFAdv_c WFAdv_i.
 
 Lemma WFAdv_subset : forall PrOrcl PrPriv X Y Gcomm E I c O,
  X [<=] Y ->
  WFAdv_c PrOrcl PrPriv X Gcomm E I c O ->
  WFAdv_c PrOrcl PrPriv Y Gcomm E I c O.
 Proof.
  intros; induction H0 using WFAdv_c_prop with
   (P0:=fun I i O H => WFAdv_i PrOrcl PrPriv Y Gcomm E I i O).
  auto.
  eauto.

  constructor.
  intro; apply Vset.subset_correct with X; auto.
  intros y Hy; decompose [or] (w0 y Hy); auto.
  right; left; apply Vset.subset_correct with X; auto.

  constructor.
  intro; apply Vset.subset_correct with X; auto.
  intros y Hy; decompose [or] (w0 y Hy); auto.
  right; left; apply Vset.subset_correct with X; auto.
 
  constructor; auto.
  intros y Hy; decompose [or] (w y Hy); auto.
  right; left; apply Vset.subset_correct with X; auto.

  apply GA_while with O.
  intros y Hy; decompose [or] (w y Hy); auto.
  right; left; apply Vset.subset_correct with X; auto.
  trivial.

  apply GA_call_orcl; trivial.
  intros t0 e H0 y Hy; decompose [or] (w t0 e H0 y Hy); auto.
  right; left; apply Vset.subset_correct with X; auto.
  intro; apply Vset.subset_correct with X; auto.

  apply GA_call_adv with O; eauto.
  intros y Hy; decompose [or] (w y Hy); auto.
  right; left; apply Vset.subset_correct with X; auto.
  intros t0 e H1 y Hy; decompose [or] (w0 t0 e H1 y Hy); auto.
  right; left; apply Vset.subset_correct with X; auto.
  intro; apply Vset.subset_correct with X; auto.  
 Qed.
 
End Make.
