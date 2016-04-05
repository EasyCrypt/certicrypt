Require Export EqObsRelDec.

Set Implicit Arguments.


Module Make (SemO:SEM_OPT).

 Module EQRD := EqObsRelDec.Make SemO.
 Export EQRD.

 Section TRIPLES.

  Variable k : nat.
  Variable E : env.

  Definition triple c (f g:Mem.t k -> U) := forall m, mu ([[c]] E m) g <= f m.

  Local Notation "'[|' c '|]' g '<~' f" := (triple c f g) (at level 50).
 
  Lemma triple_EqObs : forall I O c c' f g, 
   depend_only_f f I ->
   depend_only_f g O ->
   EqObs I E c E c' O ->
   [| c'|] g <~ f ->
   [| c |] g <~ f.
  Proof.
   red; intros. 
   eapply Ole_trans; [ | apply H2].
   apply Oeq_le; apply EqObs_deno with I O; trivial.
  Qed.

  Lemma triple_ass : forall t (x:Var.var t) e f,
   [| [x <- e] |] f <~ (fun m => f (m{!x <-- E.eval_expr e m!})).
  Proof.   
   red; intros; rewrite deno_assign_elim; trivial.   
  Qed.

  Lemma triple_ass_dep : forall t (x:Var.var t) e f X,
   depend_only_f f X ->
   ~Vset.mem x X ->
   [| [x <- e] |] f <~ f.
  Proof.   
   red; intros; rewrite deno_assign_elim.
   rewrite <- (H m); trivial.
   apply not_is_true_false in H0.
   apply req_mem_upd_disjoint; trivial.
  Qed.

  Lemma triple_rand : forall t (x:Var.var t) s f,
   [| [x <$- s] |] f <~ 
   (fun m => sum_dom (T.default _ _) (E.eval_support s m) 
    (fun v => f (m{!x <-- v!}))). 
  Proof.
   red; intros; rewrite deno_random_elim; trivial.
  Qed.  

  Lemma triple_rand_dep : forall t (x:Var.var t) s f X,
   depend_only_f f X ->
   ~Vset.mem x X ->
   [| [x <$- s] |] f <~ f.
  Proof.
   red; intros; rewrite deno_random_elim.
   apply Oeq_le.
   transitivity (mu (sum_support (T.default _ _) (E.eval_support s m))
    (fun v => f m)).
   symmetry; apply sum_support_stable_eq.
   intros; apply H.
   apply req_mem_upd_disjoint; trivial.
   apply not_is_true_false in H0; trivial.
   apply sum_support_const.
   apply E.eval_support_nil.
  Qed.  

  Lemma triple_nil : forall (f g:Mem.t k -o> U), 
   g <= f ->
   [| nil |] g <~ f.
  Proof.
   red; intros; rewrite deno_nil_elim; auto.
  Qed.

  Lemma triple_app : forall c1 c2 f g h, 
   [| c1 |] g <~ f -> 
   [| c2 |] h <~ g -> 
   [| c1 ++ c2 |] h <~ f. 
  Proof.
   red; intros; rewrite deno_app_elim.
   transitivity (mu ([[ c1 ]] E m) g); auto. 
  Qed.

  Lemma triple_cons : forall i c f g h,
   [| [i] |] g <~ f -> 
   [| c |] h <~ g -> 
   [| i::c |] h <~ f.
  Proof.
   intros; change (i::c) with ([i]++c); apply triple_app with g; trivial.
  Qed.

  Lemma triple_cond : forall (e:E.expr T.Bool) c1 c2 f g,
   [| c1 |] g <~ f -> 
   [| c2 |] g <~ f -> 
   [| [If e then c1 else c2] |] g <~ f. 
  Proof.
   red; intros; rewrite deno_cond_elim.
   generalize (H m) (H0 m).
   case (E.eval_expr e m); auto.  
  Qed.

  Lemma triple_strengthen : forall (f f':Mem.t k -o> U) g c,
   f' <= f -> 
   [| c |] g <~ f' ->
   [| c |] g <~ f.
  Proof.
   red; intros.
   transitivity (f' m); auto.
  Qed.

  Lemma triple_weaken : forall (f g g':Mem.t k -o> U) c,
   g <= g' -> 
   [| c |] g' <~ f ->
   [| c |] g  <~ f.
  Proof.
   red; intros.
   transitivity (mu ([[ c ]] E m) g'); auto.
  Qed.

  Lemma triple_false : forall g c,
   [| c |] g <~ fone _. 
  Proof.
   red; intros; trivial.
  Qed.

  Lemma triple_true : forall f c,
   [| c |] (fzero _) <~ f.
  Proof.
   red; intros; rewrite mu_zero; trivial.
  Qed.

  Lemma triple_while : forall (e:E.expr T.Bool) c f,
   [| c |] f <~ f ->
   [| [while e do c] |] f <~ f.
  Proof.
   unfold triple; intros. 
   rewrite deno_while_unfold_elim.
   assert (Hind:forall n, [| unroll_while e c n |] f <~ f).
   clear m; induction n; simpl.
   
   apply triple_cond; apply triple_nil; trivial.   
   
   apply triple_cond.
   apply triple_app with f; trivial. 
   apply triple_nil; trivial.
   
   apply lub_le; intros n.
   eapply Ole_trans; [ | eapply (Hind n m) ].
   unfold unroll_while_sem; simpl.  
   refine (mu_monotonic _ _ _ _); intro m0.
   case (negP (E.eval_expr e) m0); trivial.
  Qed. 

  Lemma triple_call : forall t (p:Proc.proc t) f g (x:Var.var t) la X Y, 
   [| proc_body E p |] g <~ f ->
   depend_only_f f X ->
   depend_only_f g Y ->
   (forall x, Vset.mem x X -> Var.is_global x) ->
   (forall x, Vset.mem x Y -> Var.is_global x) ->
   ~Vset.mem x X ->
   ~Vset.mem x Y -> 
   [| [x <c- p with la] |] g <~ f.
  Proof.
   unfold triple; intros; rewrite deno_call_elim.
   generalize (H (init_mem E p la m)).
   transitivity (f (init_mem E p la m)). 
   eapply Ole_trans; [ | apply H ].
   apply mu_monotonic; intro m'.   
   apply Oeq_le; apply H1.
   red; intros.
   rewrite return_mem_global; [trivial | | auto].
   intros Heq; apply H5; generalize H7; inversion Heq; trivial.
   apply Oeq_le; apply H0.
   red; intros; apply init_mem_global; auto.
  Qed.

  Section ADVERSARY.
   
   Variables PrOrcl PrPriv : PrSet.t.
   Variables Gadv Gcomm :Vset.t. 
   Variable f : Mem.t k -> U.  
   Variable X : Vset.t.

   Hypothesis Gadv_disj : Vset.disjoint X Gadv.

   Hypothesis X_global : forall x, Vset.mem x X -> Var.is_global x.

   Hypothesis X_depend_only: depend_only_f f X.

   Hypothesis triple_orcl: forall t (p:Proc.proc t), 
    PrSet.mem (BProc.mkP p) PrOrcl ->
    [| proc_body E p |] f <~ f.

   Lemma triple_adv : forall ca I O,
    WFAdv_c PrOrcl PrPriv Gadv Gcomm E I ca O ->
    (forall x, Vset.mem x I -> Var.is_local x) ->
    [| ca |] f <~ f.
   Proof.
    intros ca I O H; induction H using WFAdv_c_prop with
     (P := fun I c O (H: WFAdv_c PrOrcl PrPriv Gadv Gcomm E I c O) =>
      (forall x, Vset.mem x I -> Var.is_local x) -> triple c f f)
     (P0 := fun I i O (H:WFAdv_i PrOrcl PrPriv Gadv Gcomm E I i O) => 
      (forall x, Vset.mem x I -> Var.is_local x) -> triple [i] f f);
     intros; trivial.
    apply triple_nil; intro; auto.
    apply triple_cons with f.
    apply IHWFAdv_c; trivial.
    apply IHWFAdv_c0; intros; trivial.
    apply WFAdv_i_local with PrOrcl PrPriv Gadv Gcomm E I i IO; auto.
    
    apply triple_ass_dep with X; trivial.
    apply LS.WFWrite_not_mem with Gadv I; auto; destruct x; trivial.

    apply triple_rand_dep with X; trivial.
    apply LS.WFWrite_not_mem with Gadv I; auto; destruct x; trivial.

    apply triple_cond; auto.    
    apply triple_while; auto.

    (* Oracle *)
    apply triple_call with X X; auto.
    apply LS.WFWrite_not_mem with Gadv I; auto; destruct x; trivial. 
    apply LS.WFWrite_not_mem with Gadv I; auto; destruct x; trivial. 

    (* Adv *)
    apply triple_call with X X; auto.
    apply IHWFAdv_c; intros (t0, x0) H3.
    apply  Vset_of_var_decl_ind with 
     (P:=fun t (x:Var.var t) => Var.is_local x) (lv:=proc_params E f0); trivial.
    intros; change (Var.vis_local x1).
    apply proc_params_local with E t f0; trivial.
    apply LS.WFWrite_not_mem with Gadv I; auto; destruct x; trivial.
    apply LS.WFWrite_not_mem with Gadv I; auto; destruct x; trivial.
   Qed.

   Lemma triple_adv_Call : forall t (x:Var.var t) (A:Proc.proc t) la,
     WFAdv PrOrcl PrPriv Gadv Gcomm E A ->
     ~Vset.mem x X ->
     (forall x, Vset.mem x (Vset_of_var_decl (proc_params E A)) -> Var.is_local x) ->
     [| [x <c- A with la] |] f <~ f.
   Proof.
    intros t x A la [O [H H0] ] Hx Hparams m.
    rewrite deno_call_elim.
    assert (H1:[| proc_body E A |] f <~ f).
     apply triple_adv with (Vset_of_var_decl (proc_params E A)) O; trivial.

    transitivity (mu ([[ proc_body E A]] E (init_mem E A la m)) f).
    apply mu_le_compat; trivial.
    apply ford_le_intro; intro m'.
    apply Oeq_le; apply X_depend_only.
    intros ? y Hy; apply return_mem_global.
    intro Heq; elim Hx; rewrite Heq; trivial.    
    apply X_global; trivial.
   
    transitivity (f (init_mem E A la m)).
    apply H1.
    apply Oeq_le; apply X_depend_only.
    intros ? y Hy; apply init_mem_global.
    apply X_global; trivial.
   Qed.

  End ADVERSARY.


  Section INFO.

   Variable f : Mem.t k -> U.

   Record failure_info : Type :=
    { 
     fail_dep : Vset.t; 
     fail_dep_correct : depend_only_f f fail_dep;
     fail_dep_global : forall x, Vset.mem x fail_dep -> Var.is_global x;
     fail_info_b : forall t, Proc.proc t -> bool;
     fail_info_spec : forall t (p:Proc.proc t), 
      fail_info_b p -> [| proc_body E p |] f <~ f
    }.

   Section DEC.
    
    Variable fi : failure_info.
    
    Definition check_fail_base (bi:I.baseInstr) : bool :=
     match bi with
      | I.Assign t x e => negb (Vset.mem x (fail_dep fi))
      | I.Random t x d => negb (Vset.mem x (fail_dep fi))
     end.

    Open Scope bool_scope.

    Fixpoint check_fail_i (i:I.instr) : bool := 
     match i with
      | I.Instr bi => check_fail_base bi
      | I.Cond e c1 c2 => forallb check_fail_i c1 && forallb check_fail_i c2
      | I.While e c => forallb check_fail_i c
      | I.Call t x f args => fail_info_b fi f && negb (Vset.mem x (fail_dep fi))
     end.

    Definition check_fail (c:cmd) := forallb check_fail_i c.
    
    Lemma check_fail_correct : forall c,
     check_fail c -> 
     [| c |] f <~ f.
    Proof.
     induction c using I.cmd_ind with 
      (Pi := fun i => check_fail_i i -> [| [i] |] f <~ f);simpl;intros.
     destruct i;
      [apply triple_ass_dep with (fail_dep fi) | 
       apply triple_rand_dep with (fail_dep fi) ];
      auto using fail_dep_correct;simpl in H;rewrite <- is_true_negb;trivial.
     destruct (if_and _ _ H); apply triple_cond; auto.
     apply triple_while; auto.
     destruct (if_and _ _ H).
     apply triple_call with (fail_dep fi) (fail_dep fi).
     apply fail_info_spec with fi; trivial.
     apply fail_dep_correct.
     apply fail_dep_correct.       
     apply fail_dep_global.
     apply fail_dep_global.
     rewrite <- is_true_negb; trivial.
     rewrite <- is_true_negb; trivial.
     apply triple_nil; trivial.
     generalize H; case_eq (check_fail_i i).
     intros; apply triple_cons with f; auto.
     intros; discriminate.
    Qed.

   End DEC.

   Definition empty_fi (D:Vset.t) (H:depend_only_f f D)
    (H0: forall x, Vset.mem x D -> Var.is_global x) : failure_info.
   intros; apply Build_failure_info with D (fun _ _ => false); trivial.
   intros; discriminate.
   Defined.

   Definition add_fi (fi:failure_info) t (p:Proc.proc t)  (H:[| proc_body E p |] f <~ f) : failure_info.
   intros; destruct fi.
   apply Build_failure_info with fail_dep0 (fun tg g => if (Proc.eqb p g) then true else fail_info_b0 tg g);trivial.
   abstract (intros;case_eq (Proc.eqb p p0);intros;
    [assert (W:= Proc.eqb_spec_dep p p0);rewrite H1 in W;inversion W;simpl;trivial
     |rewrite H1 in H0;eauto]).
   Defined.

   Definition add_fi_refl (fi:failure_info) t (p:Proc.proc t) : failure_info.
   intros; case_eq (check_fail fi (proc_body E p)); intros; [ | apply fi].
   exact (add_fi fi p (check_fail_correct fi _ H)).
   Defined.

   Definition add_fi_adv (fi:failure_info) t (p:Proc.proc t)
    (PrOrcl PrPriv : PrSet.t) (Gadv Gcomm : Vset.t) (H:WFAdv PrOrcl PrPriv Gadv Gcomm E p): failure_info.
   intros; set (F:=fun g => fail_info_b fi (BProc.p_name g)).
   case_eq (PrSet.forallb F PrOrcl);intros;[ | exact fi].
   case_eq (Vset.disjoint (fail_dep fi) Gadv);intros;[ | exact fi].
   assert (W:[| proc_body E p |] f <~ f).
   abstract (destruct fi; simpl in *;
    destruct H as (O,(H3,H2));
     eapply triple_adv; eauto;
      [intros;apply fail_info_spec0;
       apply PrSet.forallb_correct with (2:= H0) (3:= H);
        intros x y Heq;rewrite Heq;trivial
       |intros (t0,x0) H4;apply  Vset_of_var_decl_ind with 
        (P:=fun t (x:Var.var t) => Var.is_local x) (lv:=proc_params E p); trivial;
         intros; change (Var.vis_local x); apply proc_params_local with E _ p; trivial]).
   exact (add_fi fi p W).
   Defined.

  End INFO.


  Section FEL.

   Variable e : E.expr T.Nat.
   Variable q : nat.
   Variable F : Mem.t k -> bool.
  
   Let sum_k_p k p (f:nat -> U) := (sigma (fun n => f (p - S n)) (p - k))%nat.

   Lemma sum_k_p_S : forall k p f, 
    (k < p)%nat ->
    sum_k_p k p f == f k + sum_k_p (S k) p f.
   Proof.
    intros; unfold sum_k_p.
    replace (p - k0)%nat with (S (p - (S k0)))%nat by omega.
    rewrite sigma_S.
    replace (p - S (p - S k0))%nat with k0 by omega. 
    trivial.
   Qed.

   Lemma sigma_minus : forall m f, 
    sigma f m == sigma (fun n => f (m - S n))%nat m.
   Proof.
    induction m; intros.
    rewrite sigma_0; trivial.
    rewrite sigma_S, sigma_S_lift.
    replace (S m - 1)%nat with m; [ | omega].
    apply Uplus_eq_compat; [trivial | ].
    rewrite IHm; apply sigma_eq_compat; intros.
    replace (m - S k0)%nat with (S m - S (S k0))%nat; [trivial | omega].
   Qed.

   Definition failure_inv h (m:Mem.t k) : U :=
    if leb (E.eval_expr e m) q 
     then charfun F m + charfun (negP F) m * sum_k_p (E.eval_expr e m) q h
     else 0.

   Section ORACLE.

    Variable body : cmd.
    Variable h : nat -> U.
    Variable P : Mem.t k -> bool.
  
    Let f := failure_inv h.

    Hypothesis Hbody: forall (m:Mem.t k),
     F m = false -> mu ([[body]] E m) (charfun F) <= h (E.eval_expr e m).

    Hypothesis range_true : forall (m:Mem.t k),
     P m = false ->
     range (fun m' => F m' = F m /\ E.eval_expr e m' = E.eval_expr e m)
     ([[body]] E m).

    Hypothesis range_false : forall (m:Mem.t k),
     P m = true ->
     range (fun m' => E.eval_expr e m < E.eval_expr e m')%nat ([[body]] E m).

    Lemma triple_oracle : [|body|] f <~ f.
    Proof.
     intro m; unfold f, failure_inv, charfun, restr, fone, negP, negb.
     case_eq (P m); intro HP.

     (* P m = true *)
     case (le_lt_dec q (E.eval_expr e m)); intro Hlt.  

     (* e >= q *)
     rewrite (range_le (range_false HP) _ (fzero _)).
     rewrite mu_zero; trivial.
     intros; rewrite leb_correct_conv; [trivial | omega].
   
     (* e < q *)
     rewrite leb_correct; [ | omega].
     case_eq (F m); intro HF; repeat Usimpl; [trivial | ]. 
     rewrite (range_le (range_false HP) _ 
      (fplus (charfun F) 
       (fmult (sum_k_p (S (E.eval_expr e m)) q h) (charfun (negP F))))).
     rewrite (@mu_stable_plus _ _ _), (mu_stable_mult _ _), (Hbody HF).
     rewrite Ule_mult_right, <- sum_k_p_S; trivial.

     intro m'; unfold charfun, restr, finv, fmult, negP, negb, fone.
     case (F m'); repeat Usimpl; trivial.

     intros m' He; unfold fplus, fmult, charfun, restr, negP, negb, fone.
     case (leb (E.eval_expr e m') q); [ | trivial].
     repeat Usimpl; apply sigma_incr; omega.

     (* P = false *)
     setoid_rewrite (range_le (range_true HP) _ (fcte  _ _)).
     rewrite mu_cte; apply Ule_mult_right.
     intros m' [H H0]; rewrite H, H0; trivial.
    Qed.

   End ORACLE.
     
   Lemma failure_event : forall (m:Mem.t k) c h,
    [| c |] (failure_inv h) <~ failure_inv h ->
    F m = false ->
    E.eval_expr e m = O ->
    Pr E c m (F [&&] EP k (e <=! q)) <= sigma h q.
   Proof.
    intros m c h H HF He.
    eapply Ole_trans; [eapply Ole_trans; [ | apply (H m)] | ].
    apply mu_le_compat; [trivial | ].
    intros m'.
    unfold failure_inv, EP, charfun, restr, andP, andb, negP, negb, fone.
    simpl; unfold O.eval_op; simpl.
    case (leb (E.eval_expr e m') q); case (F m'); trivial.
    unfold failure_inv, charfun, restr, negP, negb, fone, sum_k_p.
    rewrite He, HF, <- minus_n_O, leb_correct; [Usimpl | omega].
    rewrite <- sigma_minus; trivial.
   Qed.

   Lemma failure_event_const : forall (m:Mem.t k) c a,
    [| c |] (failure_inv (fcte _ a)) <~ failure_inv (fcte _ a) ->
    F m = false ->
    E.eval_expr e m = O ->
    Pr E c m (F [&&] EP k (e <=! q)) <= q */ a.
   Proof.
    intros; eapply Ole_trans; [apply (failure_event H); trivial | ].
    clear H; induction q.
    rewrite sigma_0; trivial.
    rewrite sigma_S, Nmult_S, IHn; trivial.
   Qed.

   Lemma failure_event_mult : forall (m:Mem.t k) c a,
    [| c |] (failure_inv (fun n => n */ a)) <~ failure_inv (fun n => n */ a) ->
    F m = false ->
    E.eval_expr e m = O ->
    Pr E c m (F [&&] EP k (e <=! q)) <= (q-1)*q */ [1/2]*a.
   Proof.
    intros; eapply Ole_trans; [apply (failure_event H); trivial | ].
    clear H; induction q.
    rewrite sigma_0; trivial.
    rewrite sigma_S, IHn.
    setoid_replace (n */ a) with (2 * n */ [1/2] * a).
    rewrite <- plus_Nmult_distr.
    apply Nmult_le_compat_left.
    match goal with |- _ ?a ?b => replace a with b end; trivial.
    destruct n; simpl; [trivial | rewrite <- minus_n_O; ring].
    rewrite mult_comm, Nmult_mult_assoc, Nmult_Unth_simpl_left; trivial.
   Qed.

  End FEL.

 End TRIPLES.

End Make.
