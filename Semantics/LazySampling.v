(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * LazySampling.v : Derandomization *)

Set Asymmetric Patterns.

Require Export BuildGame.


Module Make (SemO:SEM_OPT).

 Module NE := BuildGame.Make SemO.
 Export NE.

 Section CONTEXT.

  Variables E1 E2 : env.
  Variables I1 I2 : I.instr.
  Variables nR nW : Vset.t.
  
  Definition context_bi (i:I.baseInstr) :=
   match i with
   | I.Assign t x e => ~Vset.mem x nW /\ Vset.disjoint (fv_expr e) nR
   | I.Random t x d => ~Vset.mem x nW /\ Vset.disjoint (fv_distr d) nR
   end.

  Inductive context_i : I.instr -> I.instr -> Prop :=
  | Ctxt_replace : context_i I1 I2
  | Ctxt_i : forall i, context_bi i -> context_i (I.Instr i) (I.Instr i)
  | Ctxt_cond : forall e c1 c2 c3 c4,
    Vset.disjoint (fv_expr e) nR ->
    context c1 c3 -> context c2 c4 -> 
    context_i (If e then c1 else c2) (If e then c3 else c4)
  | Ctxt_while : forall e c1 c2,
    Vset.disjoint (fv_expr e) nR ->
    context c1 c2 -> context_i (while e do c1) (while e do c2)
  | Ctxt_call : forall t (x:Var.var t) f args,
    ~Vset.mem x nW ->
    Vset.disjoint (fv_args args) nR ->
    proc_params E1 f = proc_params E2 f ->
    proc_res E1 f = proc_res E2 f ->
    Vset.disjoint (fv_expr (proc_res E1 f)) nR ->
    context (proc_body E1 f) (proc_body E2 f) ->
    context_i (x <c- f with args) (x <c- f with args)

  with context : cmd -> cmd -> Prop :=
  | Ctxt_nil : context nil nil 
  | Ctxt_cons : forall i1 i2 c1 c2,
    context_i i1 i2 ->
    context c1 c2 -> 
    context (i1::c1) (i2::c2).


  Scheme context_prop := Induction for context Sort Prop
  with context_i_prop := Induction for context_i Sort Prop.

  Definition context_proc t (f:Proc.proc t) :=
   proc_params E1 f = proc_params E2 f /\
   proc_res E1 f = proc_res E2 f /\
   Vset.disjoint (fv_expr (proc_res E1 f)) nR /\
   context (proc_body E1 f) (proc_body E2 f).

  Record context_info : Type := {
   ctxt_i :> forall t, Proc.proc t -> bool;
   ctxt_spec : forall t (f:Proc.proc t), ctxt_i t f -> context_proc t f
  }.

  Section DEC.

   Section DCONTEXT_AUX.

    Variable dcontext_i_aux : I.instr -> I.instr -> bool.

    Fixpoint dcontext_c_aux (c c': cmd) : bool :=
     match c, c' with  
       | nil, nil => true
       | i1::c1, i2::c2 =>
          if dcontext_c_aux c1 c2
              then if dcontext_i_aux i1 i2
                      then true
                      else if (andb (I.eqb i1 I1) (I.eqb i2 I2))
                           then true
                           else false
              else false
       | _, _ => false         
    end.

   End DCONTEXT_AUX.        

   Variable ci : context_info.

   Definition dcontext_bi (i:I.baseInstr) :=
    match i with
    | I.Assign t x e => 
      if Vset.mem x nW then false else Vset.disjoint (fv_expr e) nR
    | I.Random t x d => 
      if Vset.mem x nW then false else Vset.disjoint (fv_distr d) nR
    end.

   Fixpoint dcontext_i (i i':I.instr) : bool :=
    match i, i' with
    | I.Instr b, I.Instr b' =>
      if I.eqb i i' then dcontext_bi b else false
    | I.Cond e c1 c2, I.Cond e' c1' c2' =>
      if E.eqb e e' then
       if Vset.disjoint (fv_expr e) nR then
        if dcontext_c_aux dcontext_i c1 c1' then dcontext_c_aux dcontext_i c2 c2' else false
       else false
      else false
    | I.While e c, I.While e' c' =>
      if E.eqb e e' then    
       if Vset.disjoint (fv_expr e) nR then dcontext_c_aux dcontext_i c c'
       else false
      else false
    | I.Call t x f args, I.Call t' x' f' args' =>
      if Var.eqb x x' then 
       if Proc.eqb f f' then
        if E.args_eqb args args' then 
         if ci _ f then 
          if Vset.mem x nW then false else Vset.disjoint (fv_args args) nR 
         else false
        else false
       else false
      else false
    | _, _ => false
    end.
   
 
   Lemma dcontext_c_aux_spec : 
    (forall i i', dcontext_i i i' -> context_i i i') /\ 
    (forall c c', dcontext_c_aux dcontext_i c c' -> context c c').
   Proof.
    apply I.cmd_ind2; simpl; intros; try (destruct i'; trivialb).
    generalize (I.eqb_spec (I.Instr i) (I.Instr b));
    destruct (I.eqb (I.Instr i) (I.Instr b)); intros; trivialb.
    rewrite H0; constructor.
    injection H0; clear H0; intros; subst.
    destruct b; simpl in H.
    case_eq (Vset.mem v nW); intros Hmem; rewrite Hmem in H; trivialb;
    split; trivial; intro; trivialb.
    case_eq (Vset.mem v nW); intros Hmem; rewrite Hmem in H; trivialb;
    split; trivial; intro; trivialb.
    generalize (E.eqb_spec b e); destruct (E.eqb b e); trivialb; intro; subst.
    case_eq (Vset.disjoint (fv_expr e) nR); intro Hdis; rewrite Hdis in H1; trivialb.
    generalize (H l); destruct (dcontext_c_aux dcontext_i c1 l); intros; trivialb.
    constructor; auto.
    generalize (E.eqb_spec b e); destruct (E.eqb b e); trivialb; intro; subst.
    case_eq (Vset.disjoint (fv_expr e) nR); intro Hdis; rewrite Hdis in H0; trivialb.
    constructor; auto.
    generalize (Var.eqb_spec x v); destruct (Var.eqb x v); intros; trivialb.
    inversion H0; clear H0; subst.
    assert (W:= T.inj_pair2 H3); clear H3; subst.
    generalize (Proc.eqb_spec f f0); destruct (Proc.eqb f f0); trivialb; intros; subst. 
    generalize (E.args_eqb_spec a a0); destruct (E.args_eqb a a0); trivialb; intros; subst.
    case_eq (ci t0 f0); intros Heq; rewrite Heq in H; trivialb.
    case_eq (Vset.mem v nW); intros Hmem; rewrite Hmem in H; trivialb.  
    generalize (ci.(ctxt_spec) _ _ Heq).
    intros (H1, (H2, (H3, H4))); constructor; auto.
    rewrite Hmem; intros; trivialb.
    case_eq c'; intros; [constructor | rewrite H0 in H; trivialb].
    case_eq c'.
    intro Hc'; subst ; trivialb.
    intros c'_head c'_tail Hc'; subst.
    case_eq (dcontext_c_aux dcontext_i c c'_tail); 
    intro Hcc'; rewrite Hcc' in H1.
    case_eq (dcontext_i i c'_head); intro Hic'; rewrite Hic' in H1.
    constructor; auto.
    case_eq (andb (I.eqb i I1) (I.eqb c'_head I2)); 
    intro HI; rewrite HI in H1.
    destruct (@andb_prop _ _ HI).
    generalize (I.eqb_spec i I1); destruct (I.eqb i I1); trivialb; intro; subst.
    generalize (I.eqb_spec c'_head I2); destruct (I.eqb c'_head I2); trivialb; intro; subst.
    constructor.
    constructor.
    apply H0; trivial.
    trivialb.
    trivialb.
   Qed.
 
   Definition dcontext := dcontext_c_aux dcontext_i.

   Lemma dcontext_correct : forall c c', dcontext c c' -> context c c'.
   Proof.
    intros.
    destruct dcontext_c_aux_spec; eauto.
   Qed.
   
   Definition check_context_info tr (f:Proc.proc tr) :=  
    if eqb_var_decl (proc_params E1 f) (proc_params E2 f) then
     if E.eqb (proc_res E1 f) (proc_res E2 f) then
      if Vset.disjoint (fv_expr (proc_res E1 f)) nR then
       dcontext_c_aux dcontext_i (proc_body E1 f) (proc_body E2 f) 
       else false
      else false
     else false.

   Lemma check_context_info_correct : forall tr (f:Proc.proc tr),
    check_context_info tr f -> context_proc tr f.
   Proof.
    unfold check_context_info; intros tr f.
    generalize (eqb_var_decl_spec (proc_params E1 f) (proc_params E2 f)).
    destruct (eqb_var_decl (proc_params E1 f) (proc_params E2 f));
     try (intros; trivialb; fail).
    generalize (E.eqb_spec (proc_res E1 f) (proc_res E2 f)); destruct 
     (E.eqb (proc_res E1 f) (proc_res E2 f)); try (intros; trivialb; fail).
    case_eq (Vset.disjoint (fv_expr (proc_res E1 f)) nR); intros; trivialb.
    destruct dcontext_c_aux_spec; red; auto.
   Qed.

   Definition add_context_info tr (f:Proc.proc tr) : context_info.
    intros tr f; generalize (@check_context_info_correct _ f).
    case (check_context_info tr f); intros.
    refine (@Build_context_info (fun tg (g:Proc.proc tg) => if Proc.eqb f g then true else ci _ g) _).
    abstract (intros tg g; generalize (Proc.eqb_spec_dep f g); destruct (Proc.eqb f g); intros;
    [ inversion H0; subst; simpl; auto | apply ctxt_spec with ci; trivial]).
    exact ci.
   Defined.

   Definition empty_context_info : context_info.
    apply Build_context_info with (fun _ _ => false).
    intros t p.
    apply false_true_elim.
   Defined.


   Section ADV.

    Variables PrOrcl PrPriv : PrSet.t.
    Variables Gadv Gcomm : Vset.t.

    Hypothesis EqA : Eq_adv_decl PrOrcl PrPriv E1 E2.

    Section DEF.

     Hypothesis nW_global : forall x, Vset.mem x nW -> Var.is_global x.
     Hypothesis nR_global : forall x, Vset.mem x nR -> Var.is_global x.
     Hypothesis nW_Gadv : Vset.disjoint nW Gadv.
     Hypothesis nR_G : Vset.disjoint nR (Vset.union Gadv Gcomm).
     Hypothesis ciPrOrcl : 
      forall tr (f:Proc.proc tr), PrSet.mem (BProc.mkP f) PrOrcl -> ci _ f.

     Lemma WFRead_not_mem: forall I te (e:E.expr te) x,
      (forall x : Vset.E.t, Vset.mem x I -> Var.is_local x) ->
      WFRead Gadv Gcomm e I -> Vset.mem x (fv_expr e) -> ~ Vset.mem x nR.
     Proof.
      intros.
      destruct (H0 _ H1).
      assert (W:= H _ H2); unfold Var.is_local in W; intro H3; rewrite (nR_global _ H3) in W.
      discriminate W.
      apply VsetP.disjoint_mem_not_mem with (Vset.union Gadv Gcomm).
      apply VsetP.disjoint_sym; trivial.
      rewrite VsetP.union_spec; trivial.
     Qed.

     Lemma WFRead_disjoint: forall I te (e:E.expr te),
      (forall x : Vset.E.t, Vset.mem x I -> Var.is_local x) ->
      WFRead Gadv Gcomm e I -> Vset.disjoint (fv_expr e) nR.
     Proof.
      intros.
      apply VsetP.disjoint_complete; intros.
      eapply WFRead_not_mem; eauto.
     Qed.

     Lemma WFWrite_not_mem : forall I x,
      (forall x : Vset.E.t, Vset.mem x I -> Var.is_local x) ->
      WFWrite Gadv x ->
      ~ Vset.mem x nW.
     Proof.
      intros; case_eq (Var.is_global x); intros.
      apply VsetP.disjoint_mem_not_mem with Gadv.
      apply VsetP.disjoint_sym; trivial.
      destruct x; simpl in *; auto.
      destruct x; intro Hmem; assert (W:=nW_global _ Hmem); simpl in *; 
       rewrite H1 in W; trivialb.
     Qed.

     Lemma Adv_c_context : forall I c O, 
      WFAdv_c PrOrcl PrPriv Gadv Gcomm E1 I c O -> 
      (forall x, Vset.mem x I -> Var.is_local x) -> 
      context c c.
     Proof.
      induction 1 using WFAdv_c_prop with 
       (P0:=fun I c O (H:WFAdv_i PrOrcl PrPriv Gadv Gcomm E1 I c O) => 
        (forall x, Vset.mem x I -> Var.is_local x) -> context_i c c); intros.
      constructor.
      constructor; auto.
      apply IHWFAdv_c0.
      apply (WFAdv_i_local w H0).
      constructor; simpl.
      split;[eapply WFWrite_not_mem; eauto | eapply WFRead_disjoint; eauto].
      destruct x; simpl in *; trivial.
      constructor; simpl; split.
      eapply WFWrite_not_mem; eauto.
      destruct x; simpl in *; trivial.
      apply VsetP.disjoint_complete; intros.
      destruct (w0 _ H0).
      assert (W:= H _ H1); unfold Var.is_local in W; intro H2; rewrite (nR_global _ H2) in W.
      discriminate W.
      apply VsetP.disjoint_mem_not_mem with (Vset.union Gadv Gcomm).
      apply VsetP.disjoint_sym; trivial.
      rewrite VsetP.union_spec; trivial.
      constructor; auto.
      eapply WFRead_disjoint; eauto.
      constructor; auto.
      eapply WFRead_disjoint; eauto.
      destruct (ci.(ctxt_spec) _ _ (ciPrOrcl _ _ i)) as (w1,(w2,(w3,w4))).
      constructor; auto.
      eapply WFWrite_not_mem; eauto.
      apply VsetP.disjoint_complete; intros.
      destruct (fv_args_fv_expr _ _ H0) as (te, (e, (H1, H2))).
      eapply WFRead_not_mem; eauto.
      destruct (EqA _ _ n n0) as (w2, (w3, w4)).
      assert (forall x0 : Vset.E.t,
        Vset.mem x0 (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x0).
       intros; destruct x0; apply Vset_of_var_decl_ind with (lv:=proc_params E1 f) 
        (P:= fun t (x:Var.var t) =>Var.is_local x); trivial.
       intros t1 x0 H2; assert (W:= proc_params_local E1 f x0 H2).
       rewrite <- Var.vis_local_local; trivial.
      constructor; auto.
      eapply WFWrite_not_mem; eauto.
      apply VsetP.disjoint_complete; intros.
      destruct (fv_args_fv_expr _ _ H2) as (te, (e, (H3, H4))).
      apply WFRead_not_mem with I te e; eauto.
      eapply WFRead_disjoint with O; eauto.
      apply (WFAdv_c_local H H1).
      rewrite <- w3; auto.
     Qed.

     Lemma Adv_context : forall fr (f:Proc.proc fr), 
      ~PrSet.mem (BProc.mkP f) PrOrcl ->
      ~PrSet.mem (BProc.mkP f) PrPriv ->
      WFAdv PrOrcl PrPriv Gadv Gcomm E1 f -> 
      context_proc _ f.
     Proof.
      intros.
      destruct H1 as (O, (H1, H2)).
      destruct (EqA _ _ H H0) as (w1, (w2, w3)).
      assert (forall x0 : Vset.E.t,
        Vset.mem x0 (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x0).
       intros; destruct x0; apply Vset_of_var_decl_ind with (lv:=proc_params E1 f) 
        (P:= fun t (x:Var.var t) =>Var.is_local x); trivial.
       intros t1 x0 H4; assert (W:= proc_params_local E1 f x0 H4).
       rewrite <- Var.vis_local_local; trivial.
      repeat split; trivial.
      eapply WFRead_disjoint with O; eauto.
      apply (WFAdv_c_local H1 H3).
      rewrite <- w2.
      eapply Adv_c_context; eauto.
     Qed.

    End DEF.

    Definition check_adv_context_info fr (f:Proc.proc fr) :=
     if PrSet.mem (BProc.mkP f) PrOrcl then false
      else if PrSet.mem (BProc.mkP f) PrPriv then false
       else
        if Vset.forallb Var.is_global nW then
         if Vset.forallb Var.is_global nR then
          if Vset.disjoint nW Gadv then 
           if Vset.disjoint nR (Vset.union Gadv Gcomm) then
            PrSet.forallb (fun f => ci _ (BProc.p_name f)) PrOrcl
            else false
           else false
          else false
         else false.

    Lemma check_adv_context_info_spec : forall fr (f:Proc.proc fr),
     check_adv_context_info fr f ->
     ~PrSet.mem (BProc.mkP f) PrOrcl /\
     ~PrSet.mem (BProc.mkP f) PrPriv /\
     (forall x, Vset.mem x nW -> Var.is_global x) /\
     (forall x, Vset.mem x nR -> Var.is_global x) /\
     Vset.disjoint nW Gadv /\
     Vset.disjoint nR (Vset.union Gadv Gcomm) /\
     (forall tr (f:Proc.proc tr), PrSet.mem (BProc.mkP f) PrOrcl -> ci _ f).
    Proof. 
     unfold check_adv_context_info; intros fr f.  
     case_eq (PrSet.mem (BProc.mkP f) PrOrcl); try (intros; trivialb; fail).
     case_eq (PrSet.mem (BProc.mkP f) PrPriv); try (intros; trivialb; fail).
     case_eq (Vset.forallb Var.is_global nW); try (intros; trivialb; fail).
     case_eq (Vset.forallb Var.is_global nR); try (intros; trivialb; fail).
     case_eq (Vset.disjoint nW Gadv); try (intros; trivialb; fail).
     case_eq (Vset.disjoint nR (Vset.union Gadv Gcomm)); try (intros; trivialb; fail).
     intros; repeat split; autob.
     apply Vset.forallb_correct; trivial.
     intros x y Heq; rewrite (Heq:x = y); trivial.
     apply Vset.forallb_correct; trivial.
     intros x y Heq; rewrite (Heq:x = y); trivial.
     set (F:= fun f : PrSet.E.t => ci (BProc.p_type f) (BProc.p_name f)) in *.
     assert (W1: forall x y : PrSet.E.t, PrSet.E.eq x y -> F x = F y).
     intros x y Heq; rewrite (Heq:x = y); trivial. 
     intros tr f0 Hf0; exact (PrSet.forallb_correct F W1 _ H5 _ Hf0).
    Qed.

    Definition add_adv_context_info fr (f:Proc.proc fr) (Ha : WFAdv PrOrcl PrPriv Gadv Gcomm E1 f) : context_info.
     intros fr f Ha; generalize (check_adv_context_info_spec fr f).
     case (check_adv_context_info fr f).
     intros H.
     refine (@Build_context_info (fun tg (g:Proc.proc tg) => if Proc.eqb f g then true else ci _ g) _).
     abstract (intros tg g; generalize (Proc.eqb_spec_dep f g); destruct (Proc.eqb f g); intros;
     [destruct (H (refl_equal _)) as (w1, (w2, (w3, (w4, (w5, (w6, w7))))));
      inversion H0; clear H0; simpl; apply Adv_context; trivial
     |apply ctxt_spec with ci; trivial]).
     intros; exact ci.
    Defined.

   End ADV.

  End DEC.

 End CONTEXT.

Section CONTEXT_PROOF.

  Variable E1 E2 : env.
  Variables C1 C2 : cmd.  
  Variable t : T.type.
  Variable y : Var.var t.
  Variable d : E.support t.
  Variable e : E.expr T.Bool.

  Hypothesis fvd_glob : forall x, Vset.mem x (fv_distr d) -> Var.is_global x.
  Hypothesis fve_glob : forall x, Vset.mem x (fv_expr e) -> Var.is_global x.
  Hypothesis y_glob : Var.is_global y.

  Hypothesis equiv_C2 : 
   equiv (Meq /-\ ~- EP1 e) E1 C2 E2 C2 (Meq /-\ ~- EP1 e).
  
  Lemma context_false : forall c1 c2,
   context E1 E2 (If e then (y <$- d)::C1 else C2) (If e then C1 else C2)
   (Vset.singleton y) (Vset.add y (Vset.union (fv_expr e) (fv_distr d)))
   c1 c2 ->
   equiv (Meq /-\ ~-EP1 e) E1 c1 E2 c2 (Meq /-\ ~-EP1 e).
  Proof.
   induction 1 using context_prop
   with (P0 := fun i1 i2 
    (H:context_i E1 E2 (If e then (y <$- d)::C1 else C2) (If e then C1 else C2) (Vset.singleton y) (Vset.add y (Vset.union (fv_expr e) (fv_distr d))) i1 i2) =>
    equiv (Meq /-\ ~-EP1 e) E1 [i1] E2 [i2] (Meq /-\ ~-EP1 e));
   simpl; intros.
   apply equiv_nil.
   eapply equiv_cons; eauto.
   apply equiv_cond.
   apply equiv_False.
   unfold andR,notR; tauto.
   rewrite proj1_MR; trivial.
   unfold Meq, andR; intros k m1 m2 (H1, H2); rewrite H1; trivial.
   destruct i; simpl in c; destruct c.
   eapply equiv_strengthen;[ | apply equiv_assign].
   unfold upd_para, Meq; intros k m1 m2 (H1, H2); split; subst; trivial.
   unfold notR, EP1 in *; intro; apply H2.
   rewrite (@EqObs_e_fv_expr _ e _ m2 (m2 {!v <-- E.eval_expr e0 m2!})); trivial.
   apply req_mem_upd_disjoint.
   apply not_true_is_false; rewrite VsetP.add_spec, VsetP.union_spec in H; tauto.
   eapply equiv_strengthen;[ | apply equiv_random].
   unfold Meq, forall_random; intros k m1 m2 (H1, H2); split; subst; trivial.
   unfold eq_support; trivial.
   intros; split; trivial.
   unfold notR, EP1 in *; intro; apply H2.
   rewrite (@EqObs_e_fv_expr _ e _ m2 (m2 {!v <-- v0!})); trivial.
   apply req_mem_upd_disjoint.
   apply not_true_is_false; rewrite VsetP.add_spec, VsetP.union_spec in H; tauto.
   apply equiv_cond; try rewrite proj1_MR; trivial.
   unfold Meq; intros k m1 m2 (H1, H2); rewrite H1; trivial.
   eapply equiv_weaken;[ | apply equiv_while with (P := Meq /-\ ~- EP1 e)].
   unfold andR; tauto.
   unfold Meq; intros k m1 m2 (H1, H2); rewrite H1; trivial.
   rewrite proj1_MR; trivial.  
   apply equiv_call with (3:= IHcontext).
   unfold Meq; intros k m1 m2 (H1, H2); subst; split; trivial.
   apply init_mem_eq2; trivial.
   intros; unfold notR, EP1 in *; intro; apply H2.
   rewrite (@EqObs_e_fv_expr _ e _ m2 (init_mem E1 f args m2)); trivial.
   red; intros.
   symmetry; apply init_mem_global; auto.
   unfold Meq; intros k m1 m1' m2 m2' (H1, H2) (H4, H6); subst; split.
   apply Mem.eq_leibniz; intros (tw, w).
   destruct (Var.eq_dec (Var.mkV x) w).
   inversion e2; simpl.
   repeat rewrite return_mem_dest; rewrite e1; trivial.
   case_eq (Var.is_global w); intros.
   repeat rewrite return_mem_global; trivial.
   assert (Var.is_local w) by (unfold Var.is_local; rewrite H0; trivial).
   repeat rewrite return_mem_local; trivial.
    unfold notR, EP1 in *; intro; apply H6.
    rewrite (@EqObs_e_fv_expr _ e _ m2' (return_mem E1 x f m2 m2')); trivial.
    red; intros; rewrite return_mem_global; trivial.
    intro Heq; apply n; rewrite Heq; auto with set.
    auto. 
  Qed.

  (* TODO: unify this with cond_hoist *)
  Lemma swap_if : forall E c e X k,
   Modify E X c ->
   Vset.disjoint (fv_expr e) X ->
   forall c1 c2 (m:Mem.t k),
    [[ c++[If e then c1 else c2] ]] E m ==
    [[ [If e then c++c1 else c ++ c2] ]] E m.
  Proof.
   intros; rewrite deno_app.
   rewrite (Modify_deno H), deno_cond.
   case_eq (E.eval_expr e0 m); intros.
   transitivity 
     (Mlet (Mlet (([[ c ]]) E m) (fun m' : Mem.t k => Munit (m {!X <<- m'!})))
        (([[ c1 ]]) E)).
   repeat rewrite Mcomp; apply Mlet_eq_compat; trivial.
   apply ford_eq_intro; intro m0; repeat rewrite Mlet_unit.
   rewrite deno_cond.
   rewrite  <- (@EqObs_e_fv_expr _ e0 _ m (m {!X <<- m0!})).
   rewrite H1; trivial.
   apply req_mem_sym; apply req_mem_update_disjoint; trivial.
   rewrite <- (Modify_deno H), deno_app; trivial.
   transitivity 
     (Mlet (Mlet (([[ c ]]) E m) (fun m' : Mem.t k => Munit (m {!X <<- m'!})))
        (([[ c2 ]]) E)).
   repeat rewrite Mcomp; apply Mlet_eq_compat; trivial.
   apply ford_eq_intro; intro m0; repeat rewrite Mlet_unit.
   rewrite deno_cond.
   rewrite  <- (@EqObs_e_fv_expr _ e0 _ m (m {!X <<- m0!})).
   rewrite H1; trivial.
   apply req_mem_sym; apply req_mem_update_disjoint; trivial.
   rewrite <- (Modify_deno H), deno_app; trivial.
  Qed.

  Hypothesis equiv_C1 : 
   equiv 
    (Meq /-\ EP1 e) 
    E1 ((y <$- d) :: C1 ++ [If e _then [y <$- d] ]) 
    E2 ((y <$- d):: C1) 
    Meq. 

  Hypothesis y_e : ~ Vset.mem y (fv_expr e).

  Lemma equiv_C1C2 : 
   equiv 
    (Meq /-\ EP1 e) 
    E1 [ If e then (y <$- d) :: C1 else C2; If e _then [y <$- d] ]
    E2 [y <$- d; If e then C1 else C2] 
    Meq.
  Proof.
   apply equiv_trans_eq_mem_r with (P2 := EP1 e) (E2':= E2)
    (c2' := [ If e then (y <$- d)::C1 else (y <$- d)::C2 ]).
   apply equiv_eq_sem_pre.
   unfold EP1; intros.
   rewrite deno_cond, H.
   rewrite deno_cons; symmetry; rewrite deno_cons; symmetry.
   rewrite deno_random, Mcomp, Mcomp.
   apply Mlet_eq_compat; trivial.
   apply ford_eq_intro; intro v.
   repeat rewrite Mlet_unit.
   rewrite deno_cond.
   replace (E.eval_expr e (m {!y <-- v!})) with (E.eval_expr e m).
   rewrite H; trivial.
   apply EqObs_e_fv_expr.
   apply req_mem_upd_disjoint.
   destruct (Vset.mem y (fv_expr e)); autob.
   apply equiv_trans_eq_mem_l with (P1 := EP1 e ) (E1':= E1)
    (c1' := [ If e then (y <$- d)::C1 ++ [ If e _then [y <$- d] ]  else
       C2 ++ [ If e _then [y <$- d] ] ]).
   apply equiv_eq_sem_pre.
   intros; rewrite deno_cons; repeat rewrite deno_cond. 
   unfold EP1 in H; rewrite H.
   change (Mlet (([[ (y <$- d) :: C1 ]]) E1 m) (([[ [If e _then [y <$- d] ] ]]) E1) ==
    ([[ ((y <$- d) :: C1) ++ [If e _then [y <$- d] ] ]]) E1 m).
   rewrite deno_app; trivial.
   apply equiv_cond.
   rewrite proj1_MR; apply equiv_C1.
   apply equiv_False; unfold andR, notR; intuition.
   unfold Meq; intros k m1 m2 (H1, _); rewrite H1; trivial.
   unfold EP1, andR; intuition.
   unfold Meq, EP1, andR; intuition; subst; trivial.
   red; tauto.
   unfold andR,transpR, EP1,Meq; red; intuition; subst; tauto.
  Qed.

  Lemma context_true : forall c1 c2,
   context E1 E2 (If e then (y <$- d)::C1 else C2) (If e then C1 else C2)
   (Vset.singleton y) (Vset.add y (Vset.union (fv_expr e) (fv_distr d)))
   c1 c2 ->
   forall k (m:Mem.t k),
    E.eval_expr e m = true ->
    [[ c1 ++ [ If e _then [y<$- d] ] ]] E1 m == [[ (y<$- d)::c2 ]] E2 m.
  Proof.
   induction 1 using context_prop
   with (P0 := fun i1 i2 
    (H:context_i E1 E2 (If e then (y <$- d)::C1 else C2) (If e then C1 else C2) (Vset.singleton y) (Vset.add y (Vset.union (fv_expr e) (fv_distr d))) i1 i2) =>
    forall k (m:Mem.t k),
     E.eval_expr e m = true ->
     [[ [ i1; If e _then [y<$- d] ] ]] E1 m == [[ [y<$- d; i2] ]] E2 m);
   simpl; intros. 
   rewrite deno_cond; simpl; rewrite H.
   repeat rewrite deno_random; trivial.
   change ((y <$- d) :: i2 :: c2) with ([(y <$- d); i2] ++ c2).
   rewrite deno_app. 
   rewrite <- IHcontext; trivial.
   rewrite deno_cons.
   rewrite (@deno_cons k E1 i1 [If e _then [y <$- d] ]).
   rewrite Mcomp.
   apply Mlet_eq_compat; trivial.
   apply ford_eq_intro; intros m0.
   rewrite deno_cond; simpl.
   case_eq (E.eval_expr e m0); intros H1; simpl.
   rewrite IHcontext0; trivial.
   rewrite deno_cons.
   repeat rewrite deno_random; trivial.
   rewrite deno_nil, Mlet_unit.
   rewrite deno_app.
   refine (@ford_eq_intro _ _ _ _ _).
   intro f; rewrite Mlet_simpl.
   refine (equiv_deno (context_false _ _ H) _ _ _ _ _ _).
   unfold Meq, notR, EP1; intros m1 m2 (H2, H3); subst.
   rewrite deno_cond_elim.
   destruct (E.eval_expr e m2).
   elim H3; trivial.
   apply deno_nil_elim. 
   unfold Meq, notR, EP1; split; trivial; rewrite H1; intro; discriminate.
   refine (@ford_eq_intro _ _ _ _ _); intro f.
   refine (equiv_deno equiv_C1C2 _ _ _ _ _ _).
   unfold Meq; intros; subst; trivial.
   unfold Meq, EP1; split; trivial.
   destruct i; destruct c as (H1, H2).
   transitivity (([[ [v <- e0; y <$- d] ]]) E2 m).
   repeat (rewrite deno_cons, deno_assign, Mlet_unit; symmetry).
   rewrite deno_cond.
   rewrite <- (@EqObs_e_fv_expr _ e _ m (m {!v <-- E.eval_expr e0 m!})).
   rewrite H; repeat rewrite deno_random; trivial.
    apply req_mem_upd_disjoint.
    apply not_true_is_false; rewrite VsetP.add_spec, VsetP.union_spec in H1; tauto.
   assert (equiv Meq E2 [v <- e0; y <$- d] E2  [y <$- d; v <- e0] Meq).
     eapply equiv_swap with (c1 := [v <- e0]) (c2:= [y <$- d]);
      eauto using Modify_assign, Modify_random, EqObs_assign, EqObs_random;
   apply disjoint_singleton; apply not_true_is_false.
   refine (VsetP.singleton_mem_diff _ ).
   intro Heq; rewrite Heq, VsetP.add_spec in H1; apply H1; auto.
   intro; apply H1; auto with set.
   refine (@ford_eq_intro _ _ _ _ _); intro f; refine (equiv_deno H0 _ _ _ _ _ _);
    unfold Meq; intros; subst; trivial.
   transitivity (([[ [v <$- s; y <$- d] ]]) E2 m).
   assert (equiv (Meq /-\ EP1 e) E1 [v <$- s] E2 [v <$- s] (Meq /-\ EP1 e)).
    eapply equiv_strengthen;[ | apply equiv_random].
    unfold Meq; intros k0 m1 m2 (H3, H5); subst; split.
    unfold eq_support; trivial.
    red; intros; split; trivial.
    unfold EP1; rewrite <- (@EqObs_e_fv_expr _ e _ m2 (m2 {!v <-- v0!})); trivial.
    apply req_mem_upd_disjoint.
    apply not_true_is_false; rewrite VsetP.add_spec, VsetP.union_spec in H1; tauto.
   rewrite deno_cons; symmetry; rewrite deno_cons; symmetry.
   refine (@ford_eq_intro _ _ _ _ _); intro f; rewrite Mlet_simpl.
   refine (equiv_deno H0 _ _ _ _ _ _); unfold Meq, EP1.
    intros m1 m2 (H3, H5); subst.
    rewrite deno_cond_elim, H5.
    repeat rewrite deno_random_elim; trivial.
    repeat split; trivial.
    assert (equiv Meq E2 [v <$- s; y <$- d] E2  [y <$- d; v <$- s] Meq).
     eapply equiv_swap with (c1 := [v <$- s]) (c2:= [y <$- d]);
      eauto using Modify_assign, Modify_random, EqObs_assign, EqObs_random;
      apply disjoint_singleton; apply not_true_is_false.
    refine (VsetP.singleton_mem_diff _ ).
    intro Heq; rewrite Heq, VsetP.add_spec in H1; apply H1; auto.
    intro; apply H1; auto with set.
    refine (@ford_eq_intro _ _ _ _ _); intro f; refine (equiv_deno H0 _ _ _ _ _ _);
    unfold Meq; intros; subst; trivial.
   change [y <$- d; If e0 then c3 else c4] with
    ([y <$- d] ++ [If e0 then c3 else c4]).
   rewrite (swap_if E2 [y<$-d] e0 (Vset.singleton y) k); trivial.  
   rewrite deno_cons; repeat rewrite deno_cond; case (E.eval_expr e0 m);
   rewrite <- deno_app.
   exact (IHcontext1 _ _ H1).
   exact (IHcontext2 _ _ H1).
   apply Modify_random.
   rewrite deno_cons, deno_while_unfold.
   assert (W:=@lub_cont2_comp2_eq 
      (cDistr (Mem.t k)) (Mem.t k -O-> cDistr (Mem.t k)) (cDistr (Mem.t k)) 
      (MLet _ _) (@Mlet_continuous2 _ _)
      (unroll_while_sem E1 e0 c1 m) 
      (@fmon_cte natO (Mem.t k -O-> cDistr (Mem.t k)) (@deno k [If e _then [y <$- d] ] E1))).
   match type of W with ?X == _ => transitivity X end.
   refine (Mlet_eq_compat _ _); trivial.
   apply Oeq_sym; refine (lub_cte (D := Mem.t k -O-> cDistr (Mem.t k)) _).
   rewrite W; clear W.
   assert (W:=@lub_cont2_comp2_eq 
      (cDistr (Mem.t k)) (Mem.t k -O-> cDistr (Mem.t k)) (cDistr (Mem.t k)) 
      (MLet _ _) (@Mlet_continuous2 _ _)
       (@fmon_cte natO (cDistr (Mem.t k)) (@deno k [y <$- d] E2 m))
       (@fnatO_intro (Mem.t k -O-> cDistr (Mem.t k))
            (fun n m => @unroll_while_sem k E2 e0 c2 m n)
            (fun n m => fnatO_elim (@unroll_while_sem k E2 e0 c2 m) n))).
   match type of W with ?X == _ => transitivity X end.
   match type of W with _ == ?X => transitivity X;[clear W | symmetry; trivial] end.
   refine (lub_eq_compat _).
   refine (ford_eq_intro _); intro n.
   change (Mlet (drestr (([[ unroll_while e0 c1 n ]]) E1 m) (negP (EP k e0)))
                ([[ [If e _then [y <$- d] ] ]] E1) ==
           Mlet ([[ [y <$- d] ]] E2 m) 
                (fun m => drestr ([[ unroll_while e0 c2 n ]] E2 m) (negP (EP k e0)))).
   assert (forall k (m:Mem.t k) v, E.eval_expr e0 m = E.eval_expr e0 (m{!y <--v!})). 
     intros; apply EqObs_e_fv_expr.
     apply req_mem_upd_disjoint.
     apply not_true_is_false.
     change (~Vset.mem y (fv_expr e0)).
     apply VsetP.disjoint_sym in i; apply VsetP.disjoint_mem_not_mem with (1:= i); auto with set.
   transitivity 
    (drestr (Mlet (([[ unroll_while e0 c1 n ]]) E1 m) (([[ [If e _then [y <$- d] ] ]]) E1))
       (negP (EP k e0))).
   unfold drestr; repeat rewrite Mcomp; apply Mlet_eq_compat; trivial; apply ford_eq_intro; intros m0.
   refine (ford_eq_intro _); intro g.
   repeat rewrite Mlet_simpl; rewrite deno_cond_elim.
   unfold negP, EP; case_eq (E.eval_expr e0 m0); intros; unfold negb.
   destruct (E.eval_expr e m0).
   rewrite deno_random_elim.
   transitivity (mu (sum_support (T.default k t) (E.eval_support d m0))(fun _  => 0)).
   rewrite mu_0; trivial.
   apply (mu_stable_eq (sum_support (T.default k t) (E.eval_support d m0))).
   refine (ford_eq_intro _); intro v; rewrite <- H1, H2; trivial.
   rewrite deno_nil_elim, H2; trivial.
   rewrite Munit_eq.
   repeat rewrite deno_cond_elim.
   destruct (E.eval_expr e m0).
   repeat rewrite deno_random_elim.
   apply (mu_stable_eq (sum_support (T.default k t) (E.eval_support d m0))).
   refine (ford_eq_intro _); intro v; rewrite <- H1, H2; trivial.
   repeat rewrite deno_nil_elim; rewrite H2; trivial.
   unfold drestr; rewrite <- Mcomp; apply Mlet_eq_compat; trivial.

    generalize m H0; clear m H0; induction n; simpl; intros.
    assert (forall E (m:Mem.t k), ([[ [If e0 _then nil] ]]) E m == [[ nil ]] E m).
      intros; rewrite deno_cond; case (E.eval_expr e0 m0); intros; trivial.
    rewrite H2, deno_nil, Mlet_unit, deno_cond, H0.
    repeat rewrite deno_random; rewrite Mcomp; apply Mlet_eq_compat; trivial.
    refine (ford_eq_intro _); intro v.
    rewrite Mlet_unit, H2, deno_nil; trivial.
    rewrite deno_cond; case_eq (E.eval_expr e0 m); intros.
    transitivity (([[ ((y <$- d) :: c2) ++ unroll_while e0 c2 n ]]) E2 m).
    symmetry; rewrite deno_app; symmetry.
    rewrite <- IHcontext; trivial.
    repeat rewrite deno_app, Mcomp.
    apply Mlet_eq_compat; trivial; apply ford_eq_intro; intro m0.
    rewrite deno_cond; case_eq (E.eval_expr e m0); intros.
    rewrite IHn; trivial; apply Mlet_eq_compat; trivial.
    repeat rewrite deno_random; trivial.
    rewrite deno_nil, Mlet_unit.
    assert (equiv (Meq /-\ ~- EP1 e) E1 (unroll_while e0 c1 n) E2 (unroll_while e0 c2 n) 
        (Meq /-\ ~-EP1 e )).
      clear IHn; induction n; simpl.
      apply equiv_cond.
      eapply equiv_strengthen;[ | apply equiv_nil].
      intros k0 m1 m2 (W1, W2); trivial.
      eapply equiv_strengthen;[ | apply equiv_nil].
      intros k0 m1 m2 (W1, W2); trivial.
      unfold Meq; intros k0 m1 m2 (W1, _); subst; trivial.
      apply equiv_cond.
      apply equiv_strengthen with (Meq /-\ ~- EP1 e).
      intros k0 m1 m2 (W1, W2); trivial.
      apply equiv_app with (Meq /-\ ~-EP1 e); trivial.
      apply context_false; trivial.
      apply equiv_strengthen with (Meq /-\ ~- EP1 e).
      intros k0 m1 m2 (W1, W2); trivial.
      apply equiv_nil.
      unfold Meq; intros k0 m1 m2 (W1, _); subst; trivial.
    refine (ford_eq_intro _); intro g.
    rewrite Mlet_simpl. 
    apply (equiv_deno H4).
    unfold Meq, notR, EP1; intros m1 m2 (W1, W3); subst; rewrite deno_cond_elim.
    destruct (E.eval_expr e m2).
    elim W3; trivial.
    rewrite deno_nil_elim; trivial.
    unfold Meq, notR, EP1, andR; split; trivial; rewrite H3; intro; discriminate.
    simpl; rewrite deno_cons; repeat rewrite deno_random, Mcomp; rewrite Mcomp.
    apply Mlet_eq_compat; trivial; apply ford_eq_intro; intro v.
    repeat rewrite Mlet_unit; rewrite deno_cond, <- H1, H2; trivial.

    rewrite deno_nil, Mlet_unit, deno_cond, H0.
    repeat rewrite deno_random; rewrite Mcomp; apply Mlet_eq_compat; trivial.
    apply ford_eq_intro; intro v.
    rewrite Mlet_unit, deno_cond, <- H1, H2, deno_nil; trivial.
   (* ******* *)
   clear W.
   transitivity (Mlet (([[ [y <$- d] ]]) E2 m) (([[ [while e0 do c2] ]]) E2)).
   refine (Mlet_eq_compat _ _); trivial.
   refine (@lub_cte (cDistr (Mem.t k)) _).
   apply ford_eq_intro; intro m0.
   transitivity (lub (c:=cDistr (Mem.t k)) (unroll_while_sem E2 e0 c2 m0)).
   refine (lub_eq_compat _).
   apply fmon_eq_intro; intro n; trivial.
   rewrite deno_while_unfold; trivial.
   symmetry; apply deno_cons.

   (* Call *)
   rewrite deno_cons, deno_call.
   transitivity 
    (Mlet
     (Mlet (([[ proc_body E1 f ]]) E1 (init_mem E1 f args m))
       (([[ [If e _then [y <$- d] ] ]]) E1))
      (fun m' : Mem.t k => Munit (return_mem E1 x f m m'))).
   repeat rewrite Mcomp; apply Mlet_eq_compat; trivial.
   apply ford_eq_intro; intros m0.
   rewrite Mlet_unit; repeat rewrite deno_cond.
   replace (E.eval_expr e (return_mem E1 x f m m0)) with (E.eval_expr e m0).
    destruct (E.eval_expr e m0).
    repeat rewrite deno_random.
   rewrite Mcomp.
   replace (E.eval_support d (return_mem E1 x f m m0)) with (E.eval_support d m0).
   apply Mlet_eq_compat; trivial.
   apply ford_eq_intro; intros v0.
   rewrite Mlet_unit.
   replace (return_mem E1 x f m m0 {!y <-- v0!}) 
     with (return_mem E1 x f m (m0 {!y <-- v0!})); trivial.
   apply Mem.eq_leibniz; red; intros.
   destruct (Var.eq_dec x x0).
   inversion e2; simpl.
   assert (Var.mkV y <> x).
    intro Heq; apply n; rewrite Heq; auto with set.
   rewrite Mem.get_upd_diff; trivial.
   repeat rewrite return_mem_dest.
   apply EqObs_e_fv_expr.
   apply req_mem_sym; apply req_mem_upd_disjoint.
   apply not_true_is_false.
   change  (~Vset.mem y (fv_expr (proc_res E1 f))).
   apply VsetP.disjoint_sym in i0; apply VsetP.disjoint_mem_not_mem with (1:= i0).
   auto with set.
   case_eq (Var.is_global x0); intros.
    destruct (Var.eq_dec y x0).
    rewrite <- e2 in n0; generalize H1; inversion e2; simpl; intros.
    rewrite Mem.get_upd_same; repeat rewrite return_mem_global; trivial.
    rewrite Mem.get_upd_same; trivial.
    destruct x0.
    rewrite Mem.get_upd_diff; trivial; repeat rewrite return_mem_global; trivial.
    rewrite Mem.get_upd_diff; trivial.
    assert (Var.is_local x0) by (unfold Var.is_local; rewrite H1; trivial).
    assert (Var.mkV y <> x0).
    intros Heq; generalize H1 y_glob; inversion Heq; simpl; intros.
    rewrite H3, H1 in y_glob0; discriminate.
    destruct x0; rewrite Mem.get_upd_diff; trivial; repeat rewrite return_mem_local; trivial.
   apply EqObs_d_fv_expr; red; intros.
   rewrite return_mem_global; trivial. 
   intro Heq; apply n; rewrite Heq; auto with set.
   auto.
   repeat rewrite deno_nil; rewrite Mlet_unit; trivial.
   apply EqObs_e_fv_expr; red; intros.
   rewrite return_mem_global; trivial.
   intro Heq; apply n; rewrite Heq; auto with set.
   auto.
   rewrite <- deno_app.
   rewrite IHcontext.
   rewrite deno_cons, Mcomp.
   transitivity 
    (Mlet (([[ [y <$- d] ]]) E2 m)
      (fun x0 : Mem.t k =>
        Mlet (([[ proc_body E2 f ]]) E2 (init_mem E2 f args x0))
          (fun m' : Mem.t k => Munit (return_mem E2 x f x0 m')))).
   repeat rewrite deno_random, Mcomp.
   replace (E.eval_support d (init_mem E1 f args m)) with 
       (E.eval_support d m).
   apply Mlet_eq_compat; trivial.
   apply ford_eq_intro; intros v0; repeat rewrite Mlet_unit.
   replace (init_mem E1 f args m {!y <-- v0!}) with
     (init_mem E2 f args (m {!y <-- v0!})).
   apply Mlet_eq_compat; trivial.
   apply ford_eq_intro; intro m'.
    replace (return_mem E1 x f m m') with  (return_mem E2 x f (m {!y <-- v0!}) m'); trivial.
    apply Mem.eq_leibniz; red; intros.
    destruct (Var.eq_dec x x0).
    inversion e2; simpl.
    repeat rewrite return_mem_dest; rewrite e1; trivial.
    case_eq (Var.is_global x0); intros.
     destruct x0; repeat rewrite return_mem_global; trivial.
    assert (Var.is_local x0) by (unfold Var.is_local; rewrite H1; trivial).
     destruct x0.
     repeat rewrite return_mem_local; trivial.
     rewrite Mem.get_upd_diff; trivial.
     intros Heq; generalize y_glob H1; inversion Heq; simpl; intros.
     rewrite y_glob0 in H3; discriminate.
   replace (init_mem E1 f args m) with (init_mem E2 f args m).
   apply Mem.eq_leibniz; red; intros (t1,x0).
   destruct (Var.eq_dec y x0).
   inversion e2; simpl.
   rewrite Mem.get_upd_same, init_mem_global; auto.
   rewrite Mem.get_upd_same; trivial.
   rewrite Mem.get_upd_diff; trivial.
   case_eq (Var.is_global x0); intros.
   repeat rewrite init_mem_global; trivial.
   rewrite Mem.get_upd_diff; trivial.
   assert (Var.is_local x0) by (unfold Var.is_local; rewrite H1; trivial).
   apply init_mem_local; trivial.
   repeat rewrite init_mem_local; trivial.
   destruct depend_only_fv_expr_rec_and.
   apply H4 with Vset.empty.
   change (m {!y <-- v0!} =={ fv_args args}m).
   apply req_mem_sym; apply req_mem_upd_disjoint.
   apply not_true_is_false.
   change  (~Vset.mem y (fv_args args)).
   apply VsetP.disjoint_sym in i; apply VsetP.disjoint_mem_not_mem with (1:= i).
   auto with set.
   symmetry; apply init_mem_eq2; trivial.
   apply EqObs_d_fv_expr; red; intros.
   rewrite init_mem_global; auto.
   symmetry; rewrite deno_cons.
   apply Mlet_eq_compat; trivial.
   apply ford_eq_intro; intro m0.
   apply deno_call.
   rewrite <- H0; apply EqObs_e_fv_expr; red; intros.
   rewrite init_mem_global; auto.
  Qed.

  Definition check_equiv_context_hyp := 
   let fv_e := fv_expr e in
    Vset.forallb Var.is_global (fv_distr d) &&
    (Vset.forallb Var.is_global fv_e &&
     (Var.is_global y && negb (Vset.mem y fv_e))).
 
 End CONTEXT_PROOF.

 Lemma equiv_context_true : forall (E1 E2:env) (C1 C2:cmd) (t0:T.type) (y:Var.var t0)
  (d:E.support t0) (e:E.expr T.Bool) c1 c2,
  check_equiv_context_hyp t0 y d e ->
  context E1 E2 (If e then (y <$- d)::C1 else C2) (If e then C1 else C2)
  (Vset.singleton y) (Vset.add y (Vset.union (fv_expr e) (fv_distr d)))
  c1 c2 ->
  equiv (Meq /-\ ~- EP1 e) E1 C2 E2 C2 (Meq /-\ ~- EP1 e) ->
  equiv (Meq /-\ EP1 e) E1 ((y <$- d) :: C1 ++ [If e _then [y <$- d] ])
  E2 ((y <$- d) :: C1) Meq ->
  equiv (Meq /-\ EP1 e) E1 (c1 ++ [ If e _then [y<$- d] ])
  E2 ((y<$- d)::c2) Meq.
 Proof.
  intros; apply equiv_eq_sem_pre.
  unfold check_equiv_context_hyp in H.
  generalize H; bprop.
  intros (H5, (H6, (H3, H4))); intros.
  intros; apply context_true with (7:= H0); trivial.
  apply Vset.forallb_correct; trivial.
  unfold Vset.E.eq; intros; subst; trivial.
  apply Vset.forallb_correct; trivial.
  unfold Vset.E.eq; intros; subst; trivial.
 Qed.

End Make.
