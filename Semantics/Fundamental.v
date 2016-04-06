(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * UpToBad.v : Fundamental lemma of game-playing *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Export Inlining.


(** The Fundamental Lemma of Game-Playing *)
Module Make_Fundamental_Lemma (SemO:SEM_OPT).

 Module Inl := Inlining.Make SemO.
 Export Inl.

 Open Scope bool_scope.

 Section FUNDAMENTAL_LEMMA.

  (** The flag variable, [bad] *)
  Variable bad : Var.var T.Bool.

  Hypothesis Gbad : Var.is_global bad.

  Section PRESERVES_BAD.

   Variable E : env.

   Variable pb_info : forall t (p:Proc.proc t), bool.

   Definition prbad_spec := forall t (p:Proc.proc t),
    pb_info p -> 
    forall k (m:Mem.t k) f,
     EP k bad m ->
     mu ([[proc_body E p]] E m) f == 
     mu ([[proc_body E p]] E m) (restr (EP k bad) f).
   
   Hypothesis pb_spec : prbad_spec.

   Fixpoint preserves_bad_instr (i:I.t) : bool :=
    match i with
    | I.Instr (I.Assign t v e) => 
      implb (Var.eqb v bad) (E.eqb e true)
    | I.Instr (I.Random t v d) => 
      negb (Var.eqb v bad)
    | I.Cond e c1 c2 =>
      forallb preserves_bad_instr c1 && forallb preserves_bad_instr c2
    | I.While e c => 
      forallb preserves_bad_instr c 
    | I.Call t d p a => 
      negb (Var.eqb d bad) && pb_info p
    end.

   Definition preserves_bad : cmd -> bool := forallb preserves_bad_instr.

   Lemma preserves_bad_spec : forall c,
    preserves_bad c ->
    forall k (m:Mem.t k) f,
    EP k bad m ->
    mu ([[c]] E m) f == mu ([[c]] E m) (restr (EP k bad) f).
   Proof.
    induction c using I.cmd_ind with
     (Pi:=fun i => 
      preserves_bad_instr i -> 
       forall (k : nat) (m : Mem.t k) (f : Mem.t k -O-> U),
        EP k bad m ->
        forall f, 
         mu ([[ [i] ]] E m) f == mu ([[ [i] ]] E m) (restr (EP k bad) f));
     unfold EP, restr in *; intros.

    destruct i.

    (* Assign *)
    repeat rewrite deno_assign_elim.
    simpl in H.
    generalize (Var.eqb_spec v bad) H; clear H.
    case (Var.eqb v bad); intros Heq H; simpl in H.
    inversion Heq; subst.
    rewrite (T.inj_pair2 H3).
    simpl; rewrite Mem.get_upd_same.
    generalize (E.eqb_spec e true).
    rewrite H; intro H1; rewrite H1; trivial.
    simpl in H0 |- *; rewrite Mem.get_upd_diff;[rewrite H0 | ]; trivial. 

    (* Random *)   
    repeat rewrite deno_random_elim.
    apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
    simpl in H, H0 |- *.
    generalize (Var.eqb_spec v bad) H; clear H.  
    case (Var.eqb v bad); intros Heq H.
    discriminate.
    rewrite Mem.get_upd_diff;[rewrite H0 | ]; trivial. 

    (* Cond *)
    repeat rewrite deno_cond_elim.
    simpl in H; unfold is_true in H; apply andb_prop in H; destruct H.
    case (E.eval_expr b m); auto.   

    (* While *)
    apply range_eq with (fun m => is_true (@E.eval_expr k _ bad m)).
    eapply range_weaken with 
     (fun m => @E.eval_expr k _ bad m /\ E.eval_expr b m = false).
    intros; tauto.
    apply while_ind0; intros;[ | trivial].

    intros g Hg.
    rewrite IHc; trivial.
    transitivity (mu ([[c]] E m0) (fzero _)).
    symmetry; apply mu_zero.
    apply mu_stable_eq.
    refine (ford_eq_intro _); intro m'.
    generalize (Hg m'); case (E.eval_expr bad m'); auto.
    simpl; intros a H1; rewrite H1; trivial.

    (* Call *)
    repeat rewrite deno_call_elim.
    simpl in H; unfold is_true in H; apply andb_prop in H; destruct H.
    rewrite (pb_spec H1).
    refine (mu_stable_eq _ _ _ _).    
    refine (ford_eq_intro _); intro m'.
    simpl; rewrite return_mem_global; trivial.
    generalize (Var.eqb_spec x bad) H; clear H.
    case (Var.eqb x bad); intros Heq H; [ discriminate | trivial].
    unfold EP; simpl.
    rewrite init_mem_global; trivial.

    (* nil *)
    repeat rewrite deno_nil_elim.
    rewrite H0; trivial.

    (* cons *)
    repeat rewrite deno_cons_elim; rewrite Mlet_simpl, Mlet_simpl.
    simpl in H; unfold is_true in H; apply andb_prop in H; destruct H.
    rewrite IHc; trivial.
    symmetry; rewrite IHc; trivial.
    apply mu_stable_eq.
    refine (ford_eq_intro _); intro m'.
    case_eq (E.eval_expr bad m'); intro Hm'; trivial.
    symmetry; rewrite IHc0; trivial.
   Qed.

   Lemma unroll_while_preserves_bad : forall e c n,
    preserves_bad c ->
    preserves_bad (unroll_while e c n).
   Proof.
    induction n; intro.
    trivial.
    simpl.
    rewrite forallb_app.    
    change (((preserves_bad c && preserves_bad (unroll_while e c n))&&true)&&true).
    repeat rewrite andb_true_r.
    rewrite H; auto.
   Qed.   
   
   Lemma unroll_while_preserves_bad2 : forall k e c n,
    (forall m f,
     EP k bad m ->
     mu ([[ c ]] E m) f == mu ([[ c ]] E m) (restr (EP k bad) f)) ->
    (forall m f,
     EP k bad m ->
     mu ([[ unroll_while e c n ]] E m) f == 
     mu ([[ unroll_while e c n ]] E m) (restr (EP k bad) f)).
   Proof.    
    induction n; intros.
    unfold unroll_while; repeat rewrite deno_cond_elim.
    case (E.eval_expr e m); repeat rewrite deno_nil_elim;
     unfold restr; rewrite H0; trivial.    
    simpl unroll_while; repeat rewrite deno_cond_elim.
    case (E.eval_expr e m).
    repeat rewrite deno_app_elim.
    rewrite H; trivial.
    unfold restr; symmetry; rewrite H; trivial.
    apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
    unfold restr; case_eq (EP k bad m'); intro Hm'.
    symmetry; rewrite IHn; trivial.
    trivial.
    unfold restr; repeat rewrite deno_nil_elim; rewrite H0; trivial.
   Qed.  

  End PRESERVES_BAD.


  Section UPTO.

   Section MAP_UPTO.

    Variable upto_instr : I.t -> I.t -> bool.

    Fixpoint map_upto (c1 c2:cmd) {struct c1} : bool :=
     match c1, c2 with
     | nil, nil => true
     | I.Instr i1::c1', I.Instr i2::c2' =>
       match i1, i2 with        
       | I.Assign t1 v1 e1, I.Assign t2 v2 e2 =>
         I.eqb (I.Instr i1) (bad <- true) && I.eqb (I.Instr i2) (bad <- true) ||
         I.eqb (I.Instr i1) (I.Instr i2) && map_upto c1' c2'
       | _, _ =>
         I.eqb (I.Instr i1) (I.Instr i2) && map_upto c1' c2'
       end
     | i1::c1', i2::c2' => upto_instr i1 i2 && map_upto c1' c2' 
     | _, _ => false
     end.

   End MAP_UPTO.

   Variables E1 E2 : env.

   Variable info : forall t (p:Proc.proc t), bool.

   Definition upto_spec := forall t (p:Proc.proc t),
    info p -> 
     (forall k (m:Mem.t k) f,
      mu ([[proc_body E1 p]] E1 m) (restr (negP (EP k bad)) f) ==
      mu ([[proc_body E2 p]] E2 m) (restr (negP (EP k bad)) f)) /\
     proc_res E1 p = proc_res E2 p /\
     proc_params E1 p = proc_params E2 p.

   Hypothesis upto_spec : upto_spec.

   Fixpoint upto_bad_instr (i1 i2:I.t) {struct i1} : bool :=
    match i1, i2 with
    | I.Cond e1 c11 c12, I.Cond e2 c21 c22 =>
      E.eqb e1 e2 && 
      map_upto upto_bad_instr c11 c21 &&
      map_upto upto_bad_instr c12 c22      
    | I.While e1 c1, I.While e2 c2 => 
      E.eqb e1 e2 && map_upto upto_bad_instr c1 c2
    | I.Call t d p a, I.Call _ _ _ _ => 
      info p && I.eqb i1 i2
    | _, _ => false
    end.

   Definition upto_bad := map_upto upto_bad_instr.

   Hypothesis pb_info1 : prbad_spec E1 info.
   Hypothesis pb_info2 : prbad_spec E2 info.
   
  
   Lemma upto_bad_correct : forall c1 c2,
    preserves_bad info c1 ->
    preserves_bad info c2 ->
    upto_bad c1 c2 ->
    forall k (m:Mem.t k) f,
     mu ([[c1]] E1 m) (restr (negP (EP k bad)) f) ==
     mu ([[c2]] E2 m) (restr (negP (EP k bad)) f).
   Proof.
    induction c1 using I.cmd_ind with
     (Pi:=fun i => 
      forall c2,
       preserves_bad info [i] ->
       preserves_bad info c2 ->
       upto_bad [i] c2 ->
       forall k (m:Mem.t k) f,
        mu ([[ [i] ]] E1 m) (restr (negP (EP k bad)) f) ==
        mu ([[c2]] E2 m) (restr (negP (EP k bad)) f));
     intros ? Hpb1 Hpb2 H k m ?; unfold restr,EP, negP in *.

    destruct c2; [discriminate H | ].
    destruct i0; try discriminate H.
    destruct i; destruct b.

    (* Assign *)
    simpl in H.
    unfold is_true in H; apply orb_prop in H.
    destruct H.
    apply andb_prop in H; destruct H as [Heq1 Heq2].
    generalize (I.eqb_spec (v <- e) (bad <- true)); rewrite Heq1; intro H1. 
    generalize (I.eqb_spec (v0 <- e0) (bad <- true)); rewrite Heq2; intro H2. 
    rewrite H1, H2; clear H1 H2.   
    rewrite deno_assign_elim.
    rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
    rewrite (preserves_bad_spec pb_info2).
    simpl; rewrite Mem.get_upd_same; simpl.
    transitivity (mu ([[c2]] E2 (m{!bad <-- true!})) (fzero _)).
    symmetry; apply mu_zero.
    refine (mu_stable_eq _ _ _ _).
    unfold fzero, EP, restr; simpl.
    refine (ford_eq_intro _); intro m'.
    case (m' bad); trivial.
    simpl in Hpb2; unfold is_true in Hpb2.
    apply andb_prop in Hpb2; destruct Hpb2; trivial.
    unfold EP; simpl; rewrite Mem.get_upd_same; trivial.   

    apply andb_prop in H; destruct H.
    destruct c2; try discriminate.
    generalize (I.eqb_spec (v <- e) (v0 <- e0)); rewrite H; clear H; intro H.
    rewrite H; repeat rewrite deno_assign_elim; trivial.

    simpl in H; unfold is_true in H.
    apply andb_prop in H; destruct H as [Heq _].
    generalize (I.eqb_spec (v <- e) (v0 <$- s)); rewrite Heq; intro H.
    discriminate H.

    simpl in H; unfold is_true in H.
    apply andb_prop in H; destruct H as [Heq _].
    generalize (I.eqb_spec (v <$- s) (v0 <- e)); rewrite Heq; intro H.
    discriminate H.

    (* Random *)
    simpl in H; unfold is_true in H.
    apply andb_prop in H; destruct H as [Heq Hc2].
    destruct c2; try discriminate.
    generalize (I.eqb_spec (v <$- s) (v0 <$- s0)); rewrite Heq; intro H.
    rewrite H; repeat rewrite deno_random_elim; trivial.

    (* Cond *)
    destruct c2; try discriminate H.
    destruct i; try discriminate H.
    simpl in H; unfold is_true in H.
    apply andb_prop in H; destruct H as [H Hc0].
    destruct c2; try discriminate Hc0.
    apply andb_prop in H; destruct H as [H Hc2].
    apply andb_prop in H; destruct H as [He Hc1].
    generalize (E.eqb_spec b e); rewrite He; intro H; rewrite H.
    simpl in Hpb1; unfold is_true in Hpb1.
    rewrite andb_true_r in Hpb1; apply andb_prop in Hpb1; destruct Hpb1.
    simpl in Hpb2; unfold is_true in Hpb2.
    rewrite andb_true_r in Hpb2; apply andb_prop in Hpb2; destruct Hpb2.
    repeat rewrite deno_cond_elim; case (E.eval_expr e m).   
    apply IHc1_1; trivial.
    apply IHc1_2; trivial.

    (* While *)
    destruct c2; try discriminate.
    destruct i; try discriminate.
    simpl in H; unfold is_true in H.
    apply andb_prop in H; destruct H as [H Hc0].
    apply andb_prop in H; destruct H as [He Hc].
    destruct c2; try discriminate.
    generalize (E.eqb_spec b e); rewrite He; intro H; rewrite H.
    simpl in Hpb1; unfold is_true in Hpb1.    rewrite andb_true_r in Hpb1.
    simpl in Hpb2; unfold is_true in Hpb2.
    rewrite andb_true_r in Hpb2.

    transitivity
     (mu (lub (unroll_while_sem E1 e c1 m)) (restr (negP (EP k bad)) f));
    [ refine (eq_distr_elim _ _); apply deno_while_unfold | ].
    transitivity
     (mu (lub (unroll_while_sem E2 e l m)) (restr (negP (EP k bad)) f));
    [ | refine (eq_distr_elim _ _); symmetry; apply deno_while_unfold ].
    simpl; apply lub_eq_compat.
    refine (ford_eq_intro _); intro n; simpl.
    generalize m; clear m; induction n; intro m; simpl;
     repeat rewrite (deno_cond_elim (k:=k)).
    case (E.eval_expr e m); repeat rewrite deno_nil_elim; trivial.
    case (E.eval_expr e m); repeat rewrite deno_app_elim.
    rewrite (mu_restr_split ([[c1]] E1 m) (EP k bad)).
    unfold restr; rewrite (mu_restr_split ([[l]] E2 m) (EP k bad)).
    apply Uplus_eq_compat. 

    symmetry; transitivity (mu ([[l]] E2 m) (fzero _)).
    apply mu_stable_eq.
    refine (ford_eq_intro _); intro m'; unfold restr.
    case_eq (EP k bad m'); intro Heq; [ | trivial].
    rewrite (preserves_bad_spec pb_info2); trivial.
    transitivity (mu ([[unroll_while e l n]] E2 m') (fzero _)).
    apply mu_stable_eq.
    unfold restr, negP; refine (ford_eq_intro _); intro m''.
    case (E.eval_expr e m''); simpl; case (EP k bad m''); trivial. 
    apply mu_zero.
    apply unroll_while_preserves_bad; trivial. 
    symmetry; transitivity (mu ([[c1]] E1 m) (fzero _)).
    apply mu_stable_eq.
    refine (ford_eq_intro _); intro m'; unfold restr.
    case_eq (EP k bad m'); intro Heq; [ | trivial].
    rewrite (preserves_bad_spec pb_info1); trivial.
    transitivity (mu ([[unroll_while e c1 n]] E1 m') (fzero _)).
    apply mu_stable_eq.
    unfold restr, negP; refine (ford_eq_intro _); intro m''.
    case (E.eval_expr e m''); simpl; case (EP k bad m''); trivial. 
    apply mu_zero.
    apply unroll_while_preserves_bad; trivial. 
    repeat rewrite mu_zero; trivial.  

    unfold EP.
    unfold negP, restr in *; rewrite (IHc1 l Hpb1 Hpb2 Hc).
    apply mu_stable_eq.
    refine (ford_eq_intro _); intro m'.
    case (E.eval_expr bad m'); unfold Datatypes.negb; trivial.
    repeat rewrite deno_nil_elim; trivial.

    (* Call *)
    destruct c2; try discriminate.
    destruct i; try discriminate.
    simpl in H; unfold is_true in H.
    apply andb_prop in H; destruct H as [H Hc2].
    apply andb_prop in H; destruct H as [Hf Heq].
    destruct c2; try discriminate.
    generalize (I.eqb_spec (x <c- f with a) (v <c- f1 with a0));
     rewrite Heq; intro H; rewrite <- H.
    simpl in Hpb1. 
    rewrite andb_true_r in Hpb1; unfold is_true in Hpb1.
    apply andb_prop in Hpb1; destruct Hpb1 as [? _].   
    generalize (Var.eqb_spec x bad) H0.
    case (Var.eqb x bad); intros; [discriminate | ].

    repeat rewrite deno_call_elim.
    destruct (upto_spec Hf) as [Hb [Hr Ha] ].
    transitivity
     (mu ([[proc_body E1 f]] E1 (init_mem E1 f a m))
      (restr (negP (EP k bad)) (fun m' => f0 (return_mem E1 x f m m')))).
    apply mu_stable_eq.
    unfold restr, EP; refine (ford_eq_intro _); intro m'.
    simpl; rewrite return_mem_global; trivial.

    rewrite (Hb k (init_mem E1 f a m)).
    rewrite (init_mem_eq2 E1 (k:=k) E2 f a a); trivial.
    apply mu_stable_eq.
    unfold restr, negP, EP; refine (ford_eq_intro _); intro m'.
    simpl; rewrite (return_mem_eq E1 E2 f x m m' Hr).
    rewrite return_mem_global; trivial.

    (* nil *)
    simpl in H; destruct c2.
    repeat rewrite deno_nil_elim; trivial.
    discriminate.

    (* cons *)
    destruct c2.
    destruct i; try discriminate.
    repeat rewrite deno_cons_elim; repeat rewrite Mlet_simpl.   
    simpl in Hpb1; unfold is_true in Hpb1; 
     apply andb_prop in Hpb1; destruct Hpb1.
    simpl in Hpb2; unfold is_true in Hpb2; 
     apply andb_prop in Hpb2; destruct Hpb2.
    rewrite (mu_restr_split ([[ [i] ]] E1 m) (EP k bad)).
    unfold restr; rewrite (mu_restr_split ([[ [i0] ]] E2 m) (EP k bad)).
    apply Uplus_eq_compat.

    transitivity (mu ([[ [i] ]] E1 m) (fzero _)).
    apply mu_stable_eq.
    unfold restr, EP; refine (ford_eq_intro _); intro m'.
    case_eq (E.eval_expr bad m'); intro Heq; [ | trivial].
    rewrite (preserves_bad_spec pb_info1); trivial.
    transitivity (mu ([[c1]] E1 m') (fzero _)).
    apply mu_stable_eq.
    unfold restr, EP; refine (ford_eq_intro _); intro m''.
    case (E.eval_expr bad m''); trivial.
    apply mu_zero.
    symmetry; transitivity (mu ([[ [i0] ]] E2 m) (fzero _)).
    apply mu_stable_eq.
    unfold restr, EP; refine (ford_eq_intro _); intro m'.
    case_eq (E.eval_expr bad m'); intro Heq; [ | trivial].
    rewrite (preserves_bad_spec pb_info2); trivial.
    transitivity (mu ([[c2]] E2 m') (fzero _)).
    apply mu_stable_eq.
    unfold restr, EP; refine (ford_eq_intro _); intro m''.
    case (E.eval_expr bad m''); trivial.
    apply mu_zero.
    repeat rewrite mu_zero; trivial.  

    case_eq (upto_bad c1 c2); intro Hupto.

    unfold negP, EP, restr; rewrite (IHc1 [i0]).
    apply mu_stable_eq.
    refine (ford_eq_intro _); intro m'.
    case (E.eval_expr bad m'); trivial.
    refine (IHc0 _ _ _ _ _ _ _); trivial.

    simpl; rewrite H0; trivial.
    simpl; rewrite H2; trivial.
    generalize H; simpl.
    destruct i; destruct i0; trivial.
    destruct b; destruct b0; intro Heq; unfold is_true in Heq.
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
    intro Heq; unfold is_true in Heq.
    apply andb_prop in Heq; destruct Heq as [Heq _]; rewrite Heq; trivial.

    generalize H Hupto; clear.
    simpl.
    destruct i; destruct i0; intros W1 Hupto; rewrite Hupto in W1; 
     try (rewrite andb_false_r in W1; discriminate).
    destruct b; destruct b0.
    rewrite andb_false_r, orb_false_r in W1; unfold is_true in W1.
    apply andb_prop in W1; destruct W1 as [Heq1 Heq2].
    generalize (I.eqb_spec (v <- e) (bad <- true)); rewrite Heq1; intro W1. 
    generalize (I.eqb_spec (v0 <- e0) (bad <- true)); rewrite Heq2; intro W2. 
    rewrite W1, W2; clear W1 W2.
    unfold restr,EP; repeat rewrite (deno_assign_elim (k:=k)).
    unfold negP; simpl; rewrite Mem.get_upd_same; trivial.

    rewrite andb_false_r in W1; discriminate.
    rewrite andb_false_r in W1; discriminate.
    rewrite andb_false_r in W1; discriminate.
   Qed.

 End UPTO.
  
 Section INFO.

  Variables E1 E2 : env.

  Record upto_info := 
   mk_p_upto_info {
    dupto :> forall t (p:Proc.proc t), bool;
    upto_pr1 : prbad_spec E1 dupto;
    upto_pr2 : prbad_spec E2 dupto;
    supto : upto_spec E1 E2 dupto
   }.

  Variable pi : upto_info.

  Variable c1 c2 : cmd.

  Definition check_bad := 
   preserves_bad pi c1 && preserves_bad pi c2 && upto_bad pi c1 c2.

  Hypothesis check_ok : check_bad.

  Lemma upto_bad_and_neg : forall k (m:Mem.t k) P, 
   Pr E1 c1 m (P [&&] negP (EP k bad)) == Pr E2 c2 m (P [&&] negP (EP k bad)).
  Proof.
   intros; repeat rewrite (andP_comm P); unfold Pr.
   transitivity (mu (([[ c1 ]]) E1 m) (restr (negP (EP k bad)) (charfun P))).
   apply mu_stable_eq; symmetry; apply restr_charfun_and.
   transitivity (mu (([[ c2 ]]) E2 m) (restr (negP (EP k bad)) (charfun P))).
   unfold check_bad in check_ok; repeat rewrite is_true_andb in check_ok.
   destruct check_ok as [ [H1 H2] H3].
   apply upto_bad_correct with  pi; trivial.
   apply supto.
   apply upto_pr1.
   apply upto_pr2.
   apply mu_stable_eq; apply restr_charfun_and.
  Qed.

  Lemma upto_bad_neg_bad : forall k (m:Mem.t k),
   Pr E1 c1 m (negP (EP k bad)) == Pr E2 c2 m (negP (EP k bad)).
  Proof.
   intros; rewrite <- (andP_true_l (negP (EP k bad))).
   apply upto_bad_and_neg.
  Qed.

  Lemma upto_bad_bad : forall k (m:Mem.t k),
   lossless E1 c1 ->
   lossless E2 c2 ->
   Pr E1 c1 m (EP k bad) == Pr E2 c2 m (EP k bad).
  Proof.
   intros; apply Uinv_simpl.
   repeat rewrite <- Pr_neg; trivial.
   apply upto_bad_neg_bad.
  Qed.

  Lemma upto_bad_le: forall k (m:Mem.t k) P,
   Pr E1 c1 m P <= Pr E2 c2 m P + Pr E1 c1 m (EP k bad).
  Proof.
   intros; rewrite Uplus_sym.
   rewrite (Pr_split E1 c1 m (EP k bad)).
   rewrite upto_bad_and_neg.
   apply Uplus_le_compat; trivial.
   rewrite proj2_BP; trivial.
   rewrite proj1_BP; trivial.
  Qed.

  End INFO.

  Section COMM.

   Variables E1 E2 : env.

   Variable pi : upto_info E1 E2.

   Definition upto_info_sym : upto_info E2 E1.
    apply (@mk_p_upto_info E2 E1 pi).
    apply pi.(upto_pr2).
    apply pi.(upto_pr1).
    red; intros.
    destruct (pi.(supto) p H) as (H1, (H2, H3)).
    split; auto.
   Defined.

   Lemma upto_bad_comm : forall t c1 c2,
    upto_bad t c1 c2 = upto_bad t c2 c1.
   Proof.
    intros t; induction c1 using I.cmd_ind with
     (Pi := fun i1 => forall i2,  
      upto_bad_instr t i1 i2 = upto_bad_instr t i2 i1);
     match goal with
     | |- forall _:I.t, _ => intros i2; destruct i2; trivial
     | |- forall _:cmd, _ => intros c2; destruct c2; trivial
     end.
    simpl; unfold upto_bad in IHc1_1, IHc1_2; rewrite IHc1_1, IHc1_2, (Eeqb_comm b e); trivial.
    simpl; unfold upto_bad in IHc1; rewrite IHc1, (Eeqb_comm b e); trivial.
    simpl; rewrite Ieqb_comm.
    generalize (I.eqb_spec (v <c- f0 with a0) (x <c- f with a));
    destruct (I.eqb (v <c- f0 with a0) (x <c- f with a)); intros Heq.
    inversion Heq; subst.
    rewrite (T.inj_pair2 H2); trivial.
    repeat rewrite andb_false_r; trivial.
    simpl; destruct i; trivial.
    simpl; destruct i; trivial.
    Opaque upto_bad_instr.
    destruct i; destruct i0; trivial; simpl.
    destruct b; destruct b0; trivial.
    rewrite andb_comm, IHc0, (Ieqb_comm (v <- e) (v0 <- e0)); trivial.
    rewrite Ieqb_comm, IHc0; trivial.
    rewrite Ieqb_comm, IHc0; trivial.
    rewrite Ieqb_comm, IHc0; trivial.
    rewrite IHc1, IHc0; trivial.
    rewrite IHc1, IHc0; trivial.
    rewrite IHc1, IHc0; trivial.
   Qed.

   Lemma check_bad_comm : forall c1 c2,
    check_bad pi c1 c2 = check_bad upto_info_sym c2 c1.
   Proof.
    unfold check_bad; simpl; intros.
    rewrite upto_bad_comm.
    rewrite (andb_comm (preserves_bad pi c1)), <- andb_assoc; trivial.
   Qed.

  End COMM.

 Lemma Fundamental_Lemma : 
   forall E1 E2 c1 c2 k (m:Mem.t k) A B F,
      Pr E1 c1 m (A [&&] negP F) == Pr E2 c2 m (B [&&] negP F) -> 
      Pr E1 c1 m F <= Pr E2 c2 m F ->
      Uabs_diff (Pr E1 c1 m A) (Pr E2 c2 m B) <= Pr E2 c2 m F.
 Proof.
  intros.
  apply (Ule_total (Pr E1 c1 m A) (Pr E2 c2 m B)); trivial; intros.
  rewrite (Uabs_diff_compat_le (Pr E1 c1 m A) (Pr E2 c2 m B) H1).
  apply Uplus_le_perm_left.
  rewrite (Pr_split E1 c1 m F A), (Pr_split E2 c2 m F B).
  rewrite H,proj2_BP, Uplus_sym, <- Uplus_assoc; trivial.
  rewrite Uabs_diff_sym. 
  rewrite (Uabs_diff_compat_le (Pr E2 c2 m B) (Pr E1 c1 m A) H1).
  transitivity (Pr E1 c1 m F); trivial.
  apply Uplus_le_perm_left.
  rewrite (Pr_split E1 c1 m F A), (Pr_split E2 c2 m F B).
  rewrite H,proj2_BP, Uplus_sym, <- Uplus_assoc; trivial.
 Qed.

 Lemma upto_bad_Uabs_diff : 
   forall (E1 E2:env) (pi:upto_info E1 E2) (c1 c2:cmd),
    check_bad pi c1 c2 ->
    lossless E2 c2 ->
    forall k (m:Mem.t k) (P:Mem.t k -o> boolO),
     Uabs_diff (Pr E1 c1 m P) (Pr E2 c2 m P) <= Pr E2 c2 m (EP k bad).
 Proof.
  intros.
  apply Fundamental_Lemma.
  rewrite andP_comm; unfold Pr.
  transitivity (mu (([[ c1 ]]) E1 m) (restr (negP (EP k bad)) (charfun P)));
  [ apply mu_stable_eq; symmetry; apply restr_charfun_and | ].
  transitivity (mu (([[ c2 ]]) E2 m) (restr (negP (EP k bad)) (charfun P)));
  [ | apply mu_stable_eq; apply restr_charfun_and].
  unfold check_bad in H.
  repeat (rewrite is_true_andb in H; destruct H).
  apply upto_bad_correct with pi; trivial; destruct pi; trivial.
  rewrite <- (negP_involutive (EP k bad)).
  unfold Pr.
  rewrite mu_neg_charfun, (fun d => mu_neg_charfun d (negP (EP k bad))).
  unfold fone; unfold lossless in H0; rewrite H0.
  fold (Pr E1 c1 m (negP (EP k bad))).
  rewrite (upto_bad_neg_bad pi c1 c2); unfold Pr; auto.
 Qed.
  
 End FUNDAMENTAL_LEMMA.

End Make_Fundamental_Lemma.
