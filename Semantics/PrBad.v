Set Implicit Arguments.

Require Export EqObsRelDec.

Module Make (SemO:SEM_OPT).
  Module EQRD := EqObsRelDec.Make SemO.
  Export EQRD.

 Lemma deno_while_unfold_elim : 
  forall (k : nat) (E : env) (e : E.expr T.Bool) (c : cmd) (m:Mem.t k) f,
   mu ([[ [while e do c] ]] E m) f ==
   lub ((@Mu _ @ (unroll_while_sem E e c m)) <_> f).
 Proof.
  intros; transitivity (mu (lub (c:=cDistr (Mem.t k)) (unroll_while_sem E e c m)) f).
  apply (ford_eq_elim (deno_while_unfold E e c m)).
  trivial.
 Qed.

 Section PR_bad.

  Variable k : nat.

  Variable E : env.

  Section RULE.

  Variable bad_K : Mem.t k -> U.

  Definition depend_only_f (f:Mem.t k -> U) X := 
   forall m1 m2, m1 =={X} m2 -> f m1 == f m2.

  Variable D: Vset.t.

  Hypothesis D_bad_K : depend_only_f bad_K D.
  
  Definition inv_bad (c:cmd) :=
     forall m, mu ([[c]] E m) bad_K <= bad_K m  .

  Lemma EqObs_inv_bad : forall I c c', EqObs I E c E c' D ->
    inv_bad c -> inv_bad c'.
  Proof.
   unfold inv_bad;intros.
   eapply Ole_trans;[ | apply H0].
   apply Oeq_le;symmetry.
   apply (EqObs_deno_same H);trivial.
  Qed.
  
  Lemma inv_bad_ass : forall t (x:Var.var t) e,
   ~Vset.mem x D ->
   inv_bad [x <- e].
  Proof.
   red;intros;rewrite deno_assign_elim.
   rewrite (@D_bad_K m (m{!x <-- @E.eval_expr k t e m!})); trivial.
   apply req_mem_upd_disjoint.
   destruct (Vset.mem x D);[elim H | ]; trivial.
  Qed.

  Lemma inv_bad_rand : forall t (x:Var.var t) s,
   ~Vset.mem x D ->
   inv_bad [x <$- s].
  Proof.
   red;intros; rewrite deno_random_elim.
   set (ss := @sum_support (T.interp k t) (T.default k t) (@E.eval_support k t s m)).
   transitivity (bad_K m * mu ss (fone _));[ | auto].
   rewrite <- (mu_stable_mult ss (bad_K m)).
   apply mu_le_compat;[trivial | intros v; unfold fmult].
   unfold fone; rewrite (@D_bad_K m (m{!x <-- v!})); auto.
   apply req_mem_upd_disjoint.
   destruct (Vset.mem x D);[elim H | ]; trivial.
  Qed.

  Lemma inv_bad_nil : inv_bad nil.
  Proof.
   red;intros;rewrite deno_nil_elim;auto.
  Qed.

  Lemma inv_bad_app : forall c1 c2,
   inv_bad c1 -> inv_bad c2 -> inv_bad (c1 ++ c2).
  Proof.
   red;intros;rewrite deno_app_elim.
   apply Ole_trans with (mu ([[c1]] E m) bad_K);[ | apply H].
   apply mu_monotonic;intro;apply H0.
  Qed.

  Lemma inv_bad_cons : forall i c,
   inv_bad [i] -> inv_bad c -> inv_bad (i :: c).
  Proof.
   intros; change (i::c) with ([i]++c); apply inv_bad_app; trivial.
  Qed.

  Lemma inv_bad_if : forall e c1 c2,
   inv_bad c1 -> inv_bad c2 -> inv_bad [If e then c1 else c2].
  Proof.
   red;intros;rewrite deno_cond_elim.
   destruct (@E.eval_expr k T.Bool e m);auto.
  Qed.

  Lemma inv_bad_while : forall e c,
   inv_bad c -> inv_bad [while e do c].
  Proof.
   unfold inv_bad; intros; rewrite deno_while_unfold_elim.
   assert (forall n, inv_bad (unroll_while e c n)).
   clear m; induction n; simpl; auto using inv_bad_if, inv_bad_nil, inv_bad_app.
   apply lub_le; intros n.
   eapply Ole_trans;[ |eapply (H0 n m) ].
   unfold unroll_while_sem;simpl.
   refine (mu_monotonic _ _ _ _);intro.
   destruct (negP (E.eval_expr e) x);auto.
  Qed.

  Hypothesis D_global : forall x, Vset.mem x D -> Var.is_global x.

  Lemma inv_bad_call : forall t (f:Proc.proc t), 
   inv_bad (proc_body E f) ->
   forall (x:Var.var t) args, ~Vset.mem x D -> inv_bad [x <c- f with args].
  Proof.
   unfold inv_bad; intros; rewrite deno_call_elim.
   transitivity (bad_K (init_mem E f args m)).
   eapply Ole_trans;[|eapply H ].  
   apply mu_monotonic;intro.
   apply Oeq_le;apply D_bad_K.
   red; intros.
    rewrite return_mem_global;[trivial | | auto].
    intros Heq; apply H0; generalize H1; inversion Heq; trivial.
   apply Oeq_le;apply D_bad_K.
   red; intros; apply init_mem_global; auto.
  Qed.

  Variables (PrOrcl PrPriv:PrSet.t) (Gadv Gcomm:Vset.t).
  Hypothesis Gadv_disj : Vset.disjoint D Gadv.

  Hypothesis inv_bad_orcl: forall t (f:Proc.proc t), 
   PrSet.mem (BProc.mkP f) PrOrcl ->
   inv_bad (proc_body E f).

  Lemma inv_pres_adv : forall ca I O,
   WFAdv_c PrOrcl PrPriv Gadv Gcomm E I ca O ->
   (forall x, Vset.mem x I -> Var.is_local x) ->
   inv_bad ca.
  Proof.
   intros ca I O H.
   induction H using WFAdv_c_prop with  
    (P:=fun I c O (H: WFAdv_c PrOrcl PrPriv Gadv Gcomm E I c O) =>
     (forall x, Vset.mem x I -> Var.is_local x) -> inv_bad c)
    (P0:=fun I i O (H:WFAdv_i PrOrcl PrPriv Gadv Gcomm E I i O) => 
     (forall x, Vset.mem x I -> Var.is_local x) -> inv_bad [i]); intros; trivial.
   apply inv_bad_nil.
   apply inv_bad_cons.
   apply IHWFAdv_c; trivial.
   apply IHWFAdv_c0; intros; trivial.
   apply WFAdv_i_local with PrOrcl PrPriv Gadv Gcomm E I i IO; auto.
   apply inv_bad_ass.
   apply LS.WFWrite_not_mem with Gadv I; auto; destruct x; trivial.
   apply inv_bad_rand.
   apply LS.WFWrite_not_mem with Gadv I; auto; destruct x; trivial.
   apply inv_bad_if; auto.
   apply inv_bad_while; auto.
   (* Oracle *)
   apply inv_bad_call; auto.
   apply LS.WFWrite_not_mem with Gadv I; auto; destruct x; trivial.
   (* Adv *)
   apply inv_bad_call; auto.
   apply IHWFAdv_c; intros (t0, x0) H3.
   apply  Vset_of_var_decl_ind with 
    (P:=fun t (x:Var.var t) => Var.is_local x) (lv:=proc_params E f); trivial.
   intros; change (Var.vis_local x1).
   apply proc_params_local with E t f; trivial.
   apply LS.WFWrite_not_mem with Gadv I; auto; destruct x; trivial.
  Qed.

  End RULE.

  Section INFO.

  Variable bad_K : Mem.t k -> U.

  Record PrBad_info : Type :=
    { prb_dep : Vset.t; 
      prb_dep_correct : depend_only_f bad_K prb_dep;
      prb_dep_global : forall x, Vset.mem x prb_dep -> Var.is_global x;
      prb_info_b : forall t, Proc.proc t -> bool;
      prb_info_spec : forall t (f:Proc.proc t), prb_info_b f ->  inv_bad bad_K (proc_body E f)
    }.

  Section DEC.

  Variable pi : PrBad_info.

  Definition check_inv_bad_base (bi:I.baseInstr) : bool :=
   match bi with
   | I.Assign t x e => negb (Vset.mem x (prb_dep pi))
   | I.Random t x d => negb (Vset.mem x (prb_dep pi))
   end.

  Fixpoint check_inv_bad_i (i:I.instr) : bool := 
    match i with
    | I.Instr bi => check_inv_bad_base bi
    | I.Cond e c1 c2 => forallb check_inv_bad_i c1 && forallb check_inv_bad_i c2
    | I.While e c => forallb check_inv_bad_i c
    | I.Call t x f args => prb_info_b pi f && negb (Vset.mem x (prb_dep pi))
    end.

  Definition check_inv_bad_c (c:cmd) := forallb check_inv_bad_i c.

  Lemma check_inv_bad_c_correct : forall c,
     check_inv_bad_c c -> 
     inv_bad bad_K c.
  Proof.
   induction c using I.cmd_ind with 
    (Pi := fun i => check_inv_bad_i i -> inv_bad bad_K [i]);simpl;intros.
   destruct i;[apply inv_bad_ass with (prb_dep pi)| apply inv_bad_rand with (prb_dep pi)];
   auto using prb_dep_correct;simpl in H;rewrite <- is_true_negb;trivial.
   destruct (if_and _ _ H);apply inv_bad_if;auto.
   apply inv_bad_while;auto.
   destruct (if_and _ _ H).
   apply inv_bad_call with (prb_dep pi).
   apply prb_dep_correct.
   apply prb_dep_global.
   apply prb_info_spec with pi;trivial.
   rewrite <- is_true_negb;trivial.
   apply inv_bad_nil.
   generalize H;case_eq (check_inv_bad_i i).
   intros;apply inv_bad_cons;auto.
   intros; discriminate.
  Qed.

  End DEC.

  Definition empty_prbad (D:Vset.t) (H:depend_only_f bad_K D)
                (H0: forall x, Vset.mem x D -> Var.is_global x) : PrBad_info.
  intros; apply Build_PrBad_info with D (fun _ _ => false);trivial.
  intros; discriminate.
  Defined.

  Definition add_prbad (pi:PrBad_info) t (f:Proc.proc t) (H:inv_bad bad_K (proc_body E f)) :PrBad_info.
  intros;destruct pi.
  apply Build_PrBad_info with prb_dep0 (fun tg g => if (Proc.eqb f g) then true else prb_info_b0 tg g);trivial.
  abstract (intros;case_eq (Proc.eqb f f0);intros;
  [assert (W:= Proc.eqb_spec_dep f f0);rewrite H1 in W;inversion W;simpl;trivial
  |rewrite H1 in H0;eauto]).
  Defined.

  Definition add_prbad_comp (pi:PrBad_info) t (f:Proc.proc t) : PrBad_info.
  intros pi t f;case_eq (check_inv_bad_c pi (proc_body E f));intros;[ | apply pi].
  exact (add_prbad pi f (check_inv_bad_c_correct pi _ H)).
  Defined.

  Definition add_prbad_adv (pi:PrBad_info) t (f:Proc.proc t)
    (PrOrcl PrPriv : PrSet.t) (Gadv Gcomm : Vset.t) (H:WFAdv PrOrcl PrPriv Gadv Gcomm E f): PrBad_info.
  intros;set (F:= fun g => prb_info_b pi (BProc.p_name g)).
  case_eq (PrSet.forallb F PrOrcl);intros;[ | exact pi].
  case_eq (Vset.disjoint (prb_dep pi) Gadv);intros;[ | exact pi].
  assert (W:inv_bad bad_K (proc_body E f)).
  abstract(destruct pi;simpl in *;
   destruct H as (O,(H3,H2));
   eapply inv_pres_adv;eauto;
   [intros;apply prb_info_spec0;
   apply PrSet.forallb_correct with (2:= H0) (3:= H);
   intros x y Heq;rewrite Heq;trivial
   |intros (t0,x0) H4;apply  Vset_of_var_decl_ind with 
    (P:=fun t (x:Var.var t) => Var.is_local x) (lv:=proc_params E f); trivial;
   intros; change (Var.vis_local x);apply proc_params_local with E _ f; trivial]).
  exact (add_prbad pi f W).
  Defined.

 End INFO.

 Section INSTANCE.

  Variable bad : E.expr T.Bool.
  Variables (count max: E.expr T.Nat).
 
  Definition T := charfun (EP k (count <=! max)).
  Definition Bad := charfun (EP k bad).

  Lemma sigma_minus : forall m f, sigma f m == sigma (fun n => f (m - (S n))%nat) m.
  Proof.
   induction m;intros.
   rewrite sigma_0;trivial.
   rewrite sigma_S.
   rewrite sigma_S_lift.
   replace (S m - 1)%nat with m;[ | omega].
   apply Uplus_eq_compat;[trivial | ].
   rewrite IHm;apply sigma_eq_compat;intros.
   replace (m - S k0)%nat with (S m - S (S k0))%nat;[trivial | omega].
  Qed.

  Section PR1.

  Variable pr : nat -> U.

  Let sum_k_p (k p:nat) (f:nat -> U) :=
    sigma (fun n => f (p - S n)%nat) (p - k)%nat.

  Let bad_sum (m:Mem.t k) :=
     sum_k_p (E.eval_expr count m) (E.eval_expr max m) pr.

  Definition bad_K :=
   Fmult (fplus Bad (Fmult bad_sum (finv Bad))) T.
 
  Let bad_K_D := Vset.union (fv_expr bad) (fv_expr (count <=! max)).

  Lemma depend_only_bad_K : depend_only_f bad_K bad_K_D.
  Proof.
   red;unfold bad_K, bad_K_D, Fmult, fplus, Bad, T, charfun,restr, finv, EP, bad_sum;intros.
   assert (W: m1 =={ fv_expr bad} m2) by (eapply req_mem_weaken;eauto with set).
   rewrite (depend_only_fv_expr bad W);clear W.
   assert (W: m1 =={ fv_expr (count <=! max)} m2) by (eapply req_mem_weaken;eauto with set).
   rewrite (depend_only_fv_expr (t:=T.Bool) (count <=! max) W);clear W.
   assert (W: m1 =={ fv_expr count} m2).
     eapply req_mem_weaken;eauto.
     eapply VsetP.subset_trans; [ | apply VsetP.subset_union_r].
     unfold fv_expr;simpl;apply fv_expr_rec_subset.
   rewrite (depend_only_fv_expr (t:=T.Nat) count W);clear W.
   assert (W: m1 =={ fv_expr max} m2).
     eapply req_mem_weaken;eauto.
     eapply VsetP.subset_trans; [ | apply VsetP.subset_union_r].
     unfold fv_expr;simpl.
     fold (fv_expr_extend max (fv_expr_rec Vset.empty count)).
     rewrite union_fv_expr_spec;unfold fv_expr;auto with set.
   rewrite (depend_only_fv_expr (t:=T.Nat) max W);trivial.
  Qed.
 
  Hypothesis Global : Vset.forallb Var.is_global (Vset.union (fv_expr bad) (fv_expr (count <=! max))).

  Definition empty_bad_K : PrBad_info bad_K.
   refine (empty_prbad depend_only_bad_K _).
   abstract (apply Vset.forallb_correct;[intros x y Heq;inversion Heq;trivial | trivial]).
  Defined.

  Lemma PrBad : forall (m:Mem.t k) c,
     inv_bad bad_K c ->
     E.eval_expr bad m = false ->
     E.eval_expr count m = 0%nat ->
     Pr E c m (EP k bad [&&] EP k (count <=! max)) <= sigma pr (E.eval_expr max m).
  Proof.
   unfold inv_bad;intros m c H Heq1 Heq2; eapply Ole_trans;
   [eapply Ole_trans ;[ | apply (H m) ] | ].
   unfold Pr;apply mu_le_compat;[trivial | ].
   rewrite charfun_and;intros m0;unfold bad_K, Fmult, fplus;fold (Bad m);auto.
   unfold bad_K, Fmult, fplus, Bad, T, charfun, restr, EP, bad_sum, finv, sum_k_p.
   rewrite Heq1, Heq2, <- minus_n_O;repeat Usimpl.
   rewrite <- sigma_minus;auto.
  Qed.

  Variable c:cmd.

  Hypothesis range_c : forall (m:Mem.t k),
     range (fun m' => E.eval_expr count m' = (E.eval_expr count m + 1)%nat /\ 
                      E.eval_expr max m' = E.eval_expr max m)
           ([[c]] E m).

  Hypothesis Pr_bad : forall m, E.eval_expr bad m = false -> Pr E c m (EP k bad) <= pr (E.eval_expr count m).

  Lemma inv_bad_c : inv_bad bad_K c.
  Proof.
   unfold inv_bad;intros.
   case_eq (E.eval_expr (count +! 1%nat <=! max) m);intros H;unfold bad_K at 2, Fmult, fplus,finv;
   assert (HH:= H);simpl in H;unfold O.eval_op in H;simpl in H.
   unfold T, charfun,restr, EP;simpl;unfold O.eval_op;simpl.
   apply leb_complete in H;unfold sum_k_p.
   rewrite leb_correct;[ unfold fone;Usimpl | omega].
   unfold Bad, charfun,restr, EP, fone.
   case_eq (E.eval_expr bad m);intros;repeat Usimpl;[auto | ].
   transitivity (mu ([[ c ]] E m)
                  (fplus Bad (fcte _ (sum_k_p (E.eval_expr count m + 1) (E.eval_expr max m) pr)))).
   apply range_le with (1:= range_c m).
   unfold bad_K, Fmult, fplus, fcte, bad_sum.
   intros m1 (Heq1, Heq2);rewrite Heq1, Heq2.
   unfold T, charfun,restr, EP;simpl;unfold O.eval_op;simpl.
   rewrite leb_correct;[ unfold fone;Usimpl;auto | omega].
   eapply Ole_trans;[apply mu_le_plus | unfold bad_sum].
   transitivity (pr (E.eval_expr count m) + sum_k_p (E.eval_expr count m + 1)%nat (E.eval_expr max m) pr).
   apply Uplus_le_compat;[exact (Pr_bad m H0)| apply mu_cte_le].
   unfold sum_k_p.
   replace (E.eval_expr max m - E.eval_expr count m)%nat with
      (S (E.eval_expr max m - (E.eval_expr count m + 1)));[ | omega].
   rewrite sigma_S.
   replace (E.eval_expr max m - S (E.eval_expr max m - (E.eval_expr count m + 1)))%nat with
      (E.eval_expr count m);[ trivial| omega].
   apply leb_complete_conv in H.
   transitivity (mu ([[ c ]] E m) (fun _ => 0));[ | rewrite mu_0;trivial].
   apply range_le with (1:= range_c m).
   unfold bad_K, T, charfun,restr, EP,Fmult;simpl;unfold O.eval_op;simpl.
   intros m1 (Heq1, Heq2);rewrite Heq1, Heq2, leb_correct_conv;[auto | omega].
  Qed.

  End PR1.

 Lemma PrBad_cte : forall u (m:Mem.t k) c,
     inv_bad (bad_K (fcte _ u)) c ->
     E.eval_expr bad m = false ->
     E.eval_expr count m = 0%nat ->
     Pr E c m (EP k bad [&&] EP k (count <=! max)) <= (E.eval_expr max m) */ u.
 Proof.
  intros;eapply Ole_trans;[apply (@PrBad (fcte _ u));trivial | ].
  induction (E.eval_expr max m).
  rewrite sigma_0;trivial.
  rewrite sigma_S, Nmult_S, IHi;trivial.
 Qed.

 Lemma PrBad_Nmult : forall u (m:Mem.t k) c,
     inv_bad (bad_K (fun n => n */ u)) c ->
     E.eval_expr bad m = false ->
     E.eval_expr count m = 0%nat ->
     Pr E c m (EP k bad [&&] EP k (count <=! max)) <= ((E.eval_expr max m -1)* E.eval_expr max m) */ ([1/2]*u).
 Proof.
  intros;eapply Ole_trans;[apply (@PrBad (fun n => n */ u));trivial | ].
  induction (E.eval_expr max m).
  rewrite sigma_0;trivial.
  rewrite sigma_S, IHi.
  setoid_replace (i */u) with (2 * i */ [1/2] * u).
  rewrite <- plus_Nmult_distr.
  replace (2 * i + (i - 1)%nat * i)%nat with (((1+ i) - 1)%nat * (1+ i))%nat;[trivial | ].
  destruct i;simpl;[trivial | rewrite <- minus_n_O;ring].
  rewrite mult_comm, Nmult_mult_assoc, Nmult_Unth_simpl_left;trivial.
 Qed.
 End INSTANCE.

 End PR_bad.

End Make.
