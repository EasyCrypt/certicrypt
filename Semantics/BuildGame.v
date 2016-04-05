(** * BuildGame.v : Reflection-based algorithms for constructing information
   used in analyses *)
 
Set Implicit Arguments.

Require Export Adversary.


Module Make (SemO:SEM_OPT).

 Module ADV := Adversary.Make SemO.
 Export ADV.

 Definition empty_inv_info inv X1 X2 (Hdep : depend_only_rel inv X1 X2)
  (Hglob : Vset.forallb Var.is_global (Vset.union X1 X2)) 
  (Hdec : decMR inv)
  E1 E2 : eq_inv_info inv E1 E2.
  intros inv X1 X2 Hdep Hglob Hdec E1 E2.
  refine (Build_eq_inv_info Hdep _ Hdec (fun _ _ => None)).
  apply Vset.forallb_correct with (2:= Hglob).
  intros x y H; rewrite (H:x = y); trivial. 
 Defined. 

 Definition empty_info E1 E2 : eq_inv_info trueR E1 E2.
  intros E1 E2.
  refine (@empty_inv_info trueR Vset.empty Vset.empty _ _ _ E1 E2); auto.
 Defined.

 (** A useful function to print the infos *)
 Definition print_info inv E1 E2 (pii:eq_inv_info inv E1 E2) fr (f:Proc.proc fr) :=
  match pii.(pii_info) f with
  | Some pif => 
    Some (dpi (pi_eq_refl1 pif), dpi (pi_eq_refl2 pif),
           pii_input pif, pii_params pif, pii_output pif)
  | _ => None
  end.

 Definition add_pii_info inv E1 E2 fr (f:Proc.proc fr) 
  (i:proc_eq_inv_info inv E1 E2 f) 
  (pii:eq_inv_info inv E1 E2) : eq_inv_info inv E1 E2 :=
  let (X1, X2, Hdep, Hglob, Hdec, pio) := pii in
   Build_eq_inv_info
   Hdep Hglob Hdec
   (fun (gr:T.type) =>
    match T.eq_dec fr gr with
    | left Heqr => 
      match Heqr in (_ = y0) return 
       forall (g:Proc.proc y0), option (proc_eq_inv_info inv E1 E2 g) with
      | refl_equal =>
        fun (g:Proc.proc fr) =>
        match Proc.eq_dec f g with
        | left Heqf =>
          match Heqf in (_ = y0) return option (proc_eq_inv_info inv E1 E2 y0) with
          | refl_equal => Some i
          end
        | right _ => pio fr g
        end
      end
    | right _ => fun g => pio gr g
    end).

 (* [R] is the set of modified global variables which whose equality may be 
    not ensured upon termination *)
 Definition build_drefl_info_rm (n:positive) (E:env) (pi:eq_refl_info E) 
  t (f:Proc.proc t) (R:Vset.t) : option dproc_eq_refl_info :=
   let params:=proc_params E f in
   let c:= proc_body E f in 
   let res := proc_res E f in
   match modify pi Vset.empty c with
   | Some Mc => 
     let modi := get_globals Mc in
     let output := Vset.diff modi R in
     let fv := fv_expr res in
     let O:= Vset.union fv output in
     match eqobs_in n pi c O with
     | Some Input =>
       let nparams:= get_locals Input in
       let input := get_globals Input in
       if nparams [<=?] Vset_of_var_decl params then
        if Vset.diff (get_globals fv) output [<=?] Vset.diff input modi then 
          Some (Build_dproc_eq_refl_info modi input nparams output (is_lossless pi c))
        else None
       else None
     | None => None
     end
   | None => None
   end.

 Ltac case_opt := 
  match goal with
  | |- match ?e with Some _ => _ | None => _ end = Some _ -> _ =>
     case_eq e; [ | intros; discriminate]
  | |- (if ?e then _ else _) = _ -> _ => 
     case_eq e; try (intros; discriminate)
  end.

 Lemma build_srefl_info_rm : forall (n:positive) (E:env) (pi:eq_refl_info E) 
  t (f:Proc.proc t) (R:Vset.t) (d:dproc_eq_refl_info),
    build_drefl_info_rm n pi f R = Some d ->
    sproc_eq_refl_info E f d.
 Proof.
  intros n E pi t0 f R d; unfold build_drefl_info_rm.
  case_opt; intros Mc HMc.
  case_opt; intros Input HInput.
  case_opt; intros Hsub.
  case_opt; intros Hsub1 Heq; injection Heq; clear Heq; intros; subst.
  constructor; simpl.
  apply is_lossless_correct.
  apply get_globals_spec.
  exact Hsub.
  intros x; rewrite VsetP.diff_spec; intros (H1, H2);
   apply get_globals_spec with Mc; trivial.
  apply get_globals_spec.
  exists (get_locals Mc); split.
  apply get_locals_spec.
  rewrite union_locals_globals; apply modify_correct with (1:= HMc).
  auto with set.
  exists (get_locals (fv_expr (proc_res E f))).
  split;[apply get_locals_spec | ].
  assert 
   (H : 
    Vset.union
     (get_locals (fv_expr (proc_res E f))) (Vset.diff (get_globals Mc) R)
    [<=] Vset.union (fv_expr (proc_res E f)) (Vset.diff (get_globals Mc) R)).
  apply VsetP.subset_union_ctxt; auto using get_locals_subset with set.
  split.
  unfold EqObs; rewrite H, VsetP.union_sym, union_locals_globals.
  apply eqobs_in_correct with n pi; trivial.
  intros k m1 m2 H0; apply EqObs_e_fv_expr.
  rewrite <- (union_locals_globals (fv_expr (proc_res E f))).
  apply req_mem_union; intros tx x Hin; apply H0; repeat rewrite VsetP.union_spec; auto.
  destruct (VsetP.mem_dec x (Vset.diff (get_globals Input) (get_globals Mc))); auto.
  left; destruct (VsetP.mem_dec x (Vset.diff (get_globals Mc) R)); auto.
  elim n0.
  apply Vset.subset_correct with (1:= Hsub1); rewrite VsetP.diff_spec; auto.
 Qed.
  
 Definition build_refl_info_rm (n:positive) (E:env) (pi:eq_refl_info E) 
  t (f:Proc.proc t) (R:Vset.t): option (proc_eq_refl_info E f).
 intros n E pi t0 f R.
 generalize (build_srefl_info_rm n pi f R).
 destruct (build_drefl_info_rm n pi f R);[ | intros; exact None].
 intros H; exact (Some (@Build_proc_eq_refl_info E t0 f d (H _ (refl_equal (Some d))))).
 Defined.
 
 (* [R1 R2] are the set of modified global variables whose equality may not be 
    ensured in the reflexive part of the info *)
 Definition build_dinv_info_rm (n:positive) inv (E1 E2:env) 
   (pii:eq_inv_info inv E1 E2) t (f:Proc.proc t) I O R1 R2 :
    option (dproc_eq_inv_info E1 E2 f) :=
  match build_refl_info_rm n (refl1_info pii) f R1,
        build_refl_info_rm n (refl2_info pii) f R2 with
  | Some eqr1, Some eqr2 => 
    let res1 := proc_res E1 f in
    let res2 := proc_res E2 f in
    if E.eqb res1 res2 then 
     let fv := fv_expr res1 in
     let output := get_globals O in
     let input := get_globals I in
     let local := get_locals I in
     if fv [<=?] O then
      if local [<=?] Vset_of_var_decl (proc_params E1 f) then
       if local [<=?] Vset_of_var_decl (proc_params E2 f) then
        Some (Build_dproc_eq_inv_info eqr1 eqr2 input local output)
       else None
      else None
     else None
    else None
  | _, _ => None
  end.

 Lemma build_sinv_info_rm : forall (n:positive) inv (E1 E2:env) 
   (pii:eq_inv_info inv E1 E2) t (f:Proc.proc t) I O R1 R2 d,
   EqObsInv inv I E1 (proc_body E1 f) E2 (proc_body E2 f) O ->
   build_dinv_info_rm n pii f I O R1 R2 = Some d ->
   sproc_eq_inv_info inv d.
 Proof.
  intros n inv E1 E2 pii t f I O R1 R2 d HEO; unfold build_dinv_info_rm.
  case_opt; intros eqr1 _.
  case_opt; intros eqr2 _.
  case_opt; intros Hres.
  case_opt; intros Hfv.
  case_opt; intros Hp1.  
  case_opt; intros Hp2.
  intros Heq; injection Heq; clear Heq; intros; subst. 
  constructor; simpl; trivial.
  apply get_globals_spec.
  apply get_globals_spec.
  exists (get_locals O); split; [apply get_locals_spec | split].
  rewrite VsetP.union_sym; repeat rewrite union_locals_globals; trivial.
  generalize (E.eqb_spec (proc_res E1 f) (proc_res E2 f));
  rewrite Hres; intros Heq; rewrite <- Heq.
  rewrite union_locals_globals.
  eapply EqObs_e_strengthen; auto using EqObs_e_fv_expr;
  apply VsetP.subset_trans with (1:= Hfv); auto with set.
 Qed.

 Definition build_inv_info_rm (n:positive) inv (E1 E2:env) 
   (pii:eq_inv_info inv E1 E2) t (f:Proc.proc t) (I O R1 R2:Vset.t) 
   (HEO : EqObsInv inv I E1 (proc_body E1 f) E2 (proc_body E2 f) O) :
   option (proc_eq_inv_info inv E1 E2 f).
 intros n inv E1 E2 pii t0 f I O R1 R2 HEO.
 generalize (fun d => @build_sinv_info_rm n inv E1 E2 pii t0 f I O R1 R2 d HEO).
 destruct (build_dinv_info_rm n pii f I O R1 R2); intros;[ | exact None].
 exact (Some (@Build_proc_eq_inv_info inv E1 E2 t0 f d (H _ (refl_equal _)))).
 Defined.

 Definition simplify (n:positive) inv (E1 E2:env) 
  (pii:eq_inv_info inv E1 E2) c1 c2 O :=
  if I.ceqb c1 c2 then Some c1
   else
    let O1 := Vset.union O pii.(pii_inv_X1) in
    let O2 := Vset.union O pii.(pii_inv_X2) in
    let c1' := @Ep.optimize n E1 (refl1_info pii) c1 in
    let c2' := @Ep.optimize n E2 (refl2_info pii) c2 in
    if I.ceqb c1' c2' then Some c1'
    else 
     match @dead_code n E1 (refl1_info pii) c1' O1, 
           @dead_code n E2 (refl2_info pii) c2' O2 with
     | Some c1'', Some c2'' => 
       if I.ceqb c1'' c2'' then Some c1'' else None
     | _, _ => None
     end.

 Lemma simplify_spec : forall n inv E1 E2 (pii:eq_inv_info inv E1 E2) c1 c2 O c',
  simplify n  pii c1 c2 O = Some c' ->
  equiv Meq E1 c1 E1 c' (kreq_mem (Vset.union O pii.(pii_inv_X1))) /\
  equiv Meq E2 c' E2 c2 (kreq_mem (Vset.union O pii.(pii_inv_X2))).
 Proof.
  intros n inv E1 E2 pii c1 c2 O c'; unfold simplify.
   generalize (I.ceqb_spec c1 c2); destruct (I.ceqb c1 c2).
   intro; subst; intros H1; inversion H1; clear H1; subst.
   split;(apply equiv_weaken with Meq; 
    [ unfold Meq, kreq_mem; intros; subst; apply req_mem_refl 
    | apply equiv_eq_mem]).
   intros _; assert (equiv Meq E1 c1 E1 (Ep.optimize n (refl1_info pii) c1) Meq /\
    equiv Meq E2 c2 E2 (Ep.optimize n (refl2_info pii) c2) Meq).
   unfold Ep.optimize, Ep.optimize_pre; split.
   eapply equiv_weaken;[ | eapply equiv_strengthen; [ | 
    apply Ep.opt_correct with (a:= EpEntries.Abot) ] ].
   intros k m1 m2 (H1, H2); subst; unfold Meq; trivial.
   unfold Meq; intros; subst; split; auto using EpEntries.valid_bot.
   eapply equiv_weaken;[ | eapply equiv_strengthen; [ | 
    apply Ep.opt_correct with (a:= EpEntries.Abot) ] ].
   intros k m1 m2 (H1, H2); subst; unfold Meq; trivial.
   unfold Meq; intros; subst; split; auto using EpEntries.valid_bot.
   generalize (I.ceqb_spec (Ep.optimize n (refl1_info pii) c1)
    (Ep.optimize n (refl2_info pii) c2)).
   destruct (I.ceqb (Ep.optimize n (refl1_info pii) c1)
    (Ep.optimize n (refl2_info pii) c2)).
   intros H1 H0; inversion H0; clear H0; subst.
   rewrite <- H1 in H; destruct H; split.
   apply equiv_weaken with (2:= H).
   unfold Meq,kreq_mem; intros; subst; apply req_mem_refl.
   apply equiv_sym; auto using Meq_sym.
   apply equiv_weaken with (2:= H0).
   unfold Meq; intros; subst; trivial.
   intros _.
   case_eq (dead_code n (refl1_info pii) (Ep.optimize n (refl1_info pii) c1)
    (Vset.union O (pii_inv_X1 pii))); try (intros; discriminate).
   case_eq (dead_code n (refl2_info pii) (Ep.optimize n (refl2_info pii) c2)
    (Vset.union O (pii_inv_X2 pii))); intros; try discriminate.
   generalize (I.ceqb_spec l0 l).
   destruct (I.ceqb l0 l); intros; try discriminate.
   inversion H2; clear H2; subst; subst.
   destruct H; split.
   apply equiv_trans_eq_mem_l with (fun k (m1 m2:Mem.t k) => True) 
    E1 (Ep.optimize n (refl1_info pii) c1); trivial.
   apply equiv_strengthen with (2:= H).
   intros k m1 m2 (W1, W2); trivial.
   apply dead_code_correct with (1:= H1).
   red; trivial.
   apply equiv_trans_eq_mem_r with (fun k (m1 m2:Mem.t k) => True) 
    E2 (Ep.optimize n (refl2_info pii) c2); trivial.
   apply equiv_strengthen with (2:= H2).
   intros k m1 m2 (W1, W2); trivial.
   apply equiv_sym; auto using Meq_sym.
   unfold kreq_mem; auto using req_mem_sym.
   apply dead_code_correct with (1:= H0).
   red; trivial.
  Qed.
  
  Definition build_inv_refl_info_O (n:positive) inv (E1 E2:env) 
    t (f:Proc.proc t) (O R1 R2 : Vset.t) (pii:eq_inv_info inv E1 E2) :
    option (proc_eq_inv_info inv E1 E2 f).
   intros n inv E1 E2 t0 f O R1 R2 pii.
   generalize (simplify_spec n pii (proc_body E1 f) (proc_body E2 f) O).
   destruct (simplify n pii (proc_body E1 f) (proc_body E2 f) O) as [ c' | ];
   intros;[ | exact None].
   intros; generalize (eqobsinv_in_correct n pii c' O).
   destruct (eqobsinv_in n pii c' O) as [I | ]; intros;[ | exact None].
   refine (@build_inv_info_rm n inv E1 E2 pii t0 f I O R1 R2 _).
   abstract (unfold EqObsInv; destruct (H _ (refl_equal _));
   assert (W:= @depend_only_req_mem_rel O inv _ _ (pii_inv_dep pii));
   apply equiv_depend_only_l with (2:= W) (3:= H1);
   [ apply decMR_req_mem_rel; apply pii.(pii_inv_dec)
   | apply equiv_sym in H2; auto;
     apply equiv_depend_only_r with (2:= W) (3:= H2);
     [ apply decMR_req_mem_rel; apply pii.(pii_inv_dec)
     | exact (H0 _ (refl_equal _))]
   ]).
  Defined.

  Definition build_inv_refl_info (n:positive) inv (E1 E2:env) 
    t (f:Proc.proc t) (pii:eq_inv_info inv E1 E2) :
    option (proc_eq_inv_info inv E1 E2 f) :=
   match modify (refl1_info pii) Vset.empty (proc_body E1 f),
         modify (refl2_info pii) Vset.empty (proc_body E2 f) with
   | Some Mc1, Some Mc2 => 
     let O := Vset.inter Mc1 Mc2 in
     build_inv_refl_info_O n f O (Vset.diff Mc1 O) (Vset.diff Mc2 O) pii
   | _, _ => None
   end.

  Definition build_inv_refl_info_rm (n:positive) inv (E1 E2:env) 
    t (f:Proc.proc t) R1 R2 (pii:eq_inv_info inv E1 E2) :
    option (proc_eq_inv_info inv E1 E2 f) :=
   match modify (refl1_info pii) Vset.empty (proc_body E1 f),
         modify (refl2_info pii) Vset.empty (proc_body E2 f) with
   | Some Mc1, Some Mc2 => 
     let O := Vset.diff (Vset.inter Mc1 Mc2) (Vset.union R1 R2) in
     build_inv_refl_info_O n f O (Vset.diff Mc1 O) (Vset.diff Mc2 O) pii
   | _, _ => None
   end.

  Definition add_info inv E1 E2 fr (f:Proc.proc fr) R1 R2 (pii:eq_inv_info inv E1 E2)
   I O (HEO: EqObsInv inv I E1 (proc_body E1 f) E2 (proc_body E2 f) O) :=
   match @build_inv_info_rm 100%positive inv E1 E2 pii fr f I O R1 R2 HEO with
   | Some i => @add_pii_info inv E1 E2 fr f i pii
   | _ => pii
   end.

 Definition add_refl_info_O inv E1 E2 fr (f:Proc.proc fr) (O R1 R2 :Vset.t) (pii:eq_inv_info inv E1 E2) :=
   match build_inv_refl_info_O 100%positive f O R1 R2 pii with
   | Some i => @add_pii_info inv E1 E2 fr f i pii
   | _ => pii
   end.

 Definition add_refl_info_rm inv E1 E2 fr (f:Proc.proc fr) (R1 R2 :Vset.t) (pii:eq_inv_info inv E1 E2) :=
   match build_inv_refl_info_rm 100%positive f R1 R2 pii with
   | Some i => @add_pii_info inv E1 E2 fr f i pii
   | _ => pii
   end.

 Definition add_refl_info inv E1 E2 fr (f:Proc.proc fr) (pii:eq_inv_info inv E1 E2) :=
   match build_inv_refl_info 100%positive f pii with
   | Some i => @add_pii_info inv E1 E2 fr f i pii
   | _ => pii
   end.


 Section ADVERSARY1.
  
  Variable E : env.
  Variable pi : eq_refl_info E.
  Variables PrOrcl PrPriv : PrSet.t.
  Variables Gadv Gcomm : Vset.t.

  Definition check_global : Vset.t -> bool := Vset.forallb Var.is_global.
  
  Lemma check_global_spec : forall X, 
   check_global X ->
   forall x, Vset.mem x X -> Var.is_global x.
  Proof.
   unfold check_global; intros. 
   apply Vset.forallb_correct with (2:= H); trivial.
   intros x0 y H1; rewrite (H1:x0=y); trivial.
  Qed.

  Definition test_orcl_info IA o :=
   match pi (BProc.p_name o) with
   | Some pio =>
     Vset.forallb (fun x => 
      if Vset.mem x (pi_mod pio) then Vset.mem x (pi_output pio) else true) IA
   | None => false
   end.

  Definition check_orcl_info IA := PrSet.forallb (test_orcl_info IA) PrOrcl.
  
  Lemma check_orcl_info_exists : forall IA, 
   check_orcl_info IA ->
   forall (o : ProcD.t),
    PrSet.mem o PrOrcl ->
    exists pio : proc_eq_refl_info E (BProc.p_name o), pi (BProc.p_name o) = Some pio.
  Proof.
   unfold check_orcl_info; intros.
   assert (forall x y, x = y -> test_orcl_info IA x = test_orcl_info IA y)
    by (intros; subst; trivial).
   assert (W:= PrSet.forallb_correct _ H1 _ H _ H0).
   unfold test_orcl_info in W; simpl in W.
   destruct (pi (BProc.p_name o)); trivialb; eauto.
  Qed.
  
  Lemma check_orcl_info_incl : forall IA, 
   check_orcl_info IA ->
   forall (o : ProcD.t) (pio : proc_eq_refl_info E (BProc.p_name o)),
    PrSet.mem o PrOrcl ->
    pi (BProc.p_name o) = Some pio ->
    forall x : VarP.Edec.t,
     Vset.mem x IA ->
     Vset.mem x (pi_mod pio) -> Vset.mem x (pi_output pio).
  Proof.
   unfold check_orcl_info; intros.
   assert (forall x y, x = y -> test_orcl_info IA x = test_orcl_info IA y)
      by (intros; subst; trivial).
   assert (W:= PrSet.forallb_correct _ H4 _ H _ H0).
   unfold test_orcl_info in W; simpl in W; rewrite H1 in W.
   match type of W with
   | is_true (Vset.forallb ?f _) => 
     assert (forall x y, x = y -> f x = f y) by (intros; subst; trivial) end.
   assert (W1:= Vset.forallb_correct _ H5 _ W _ H2); clear H4 H5.
   simpl in W1; rewrite H3 in W1; trivial.
  Qed.

  Variable  t : T.type.
  Variable f : Proc.proc t.

  Hypothesis WF_f : WFAdv PrOrcl PrPriv Gadv Gcomm E f.

  Variable alossless : bool.
  Hypothesis alossless_spec : alossless -> lossless E (proc_body E f).

  Definition build_adv_dinfo : option dproc_eq_refl_info :=
   if check_global Gadv then
    if check_global Gcomm then
     match input_Adv PrOrcl Gadv Gcomm pi with
     | Some input =>
       if check_orcl_info input then
        match mod_adv PrOrcl Gadv pi with
        | Some moda => 
          let output := output_adv input moda in
          let nparams := Vset_of_var_decl (proc_params E f) in
          Some (Build_dproc_eq_refl_info moda input nparams output alossless)
        | None => None
        end
       else None
     | None => None
     end
    else None
   else None.

  Lemma build_adv_sinfo : forall d, build_adv_dinfo = Some d ->
   sproc_eq_refl_info E f d.
  Proof.
   intros d; unfold build_adv_dinfo.
   case_opt; intros Hadv.
   case_opt; intros Hcomm.
   case_opt; intros input Hin.
   case_opt; intros Horcl.
   case_opt; intros moda Hmod Heq; injection Heq; intros; clear Heq; subst.
   constructor; simpl; trivial.
   exact (input_Adv_global _ _ _ 
    (check_global_spec Gadv Hadv) (check_global_spec Gcomm Hcomm) _ Hin).
   auto with set.
   intros x H; unfold output_adv in H; rewrite VsetP.inter_spec in H; destruct H;
    exact (input_Adv_global _ _ _ 
     (check_global_spec Gadv Hadv) (check_global_spec Gcomm Hcomm) _ Hin _ H).
   exact (mod_adv_global _ _ (check_global_spec Gadv Hadv) pi Hmod).
   destruct WF_f as (x, (H,H0));
    exact (mod_adv_correct (check_global_spec Gadv Hadv) pi Hmod H).
   unfold output_adv; auto with set.
   exact (WFAdv_EqObs (check_global_spec Gadv Hadv) (check_global_spec Gcomm Hcomm)
    pi Hin (check_orcl_info_exists _ Horcl) (check_orcl_info_incl _ Horcl) moda
    WF_f).
  Qed.

  Definition build_adv_info : option (proc_eq_refl_info E f).
   generalize build_adv_sinfo.
   destruct build_adv_dinfo; intros; [ | exact None].
   apply Some; econstructor.
   apply H; trivial.
  Defined.

 End ADVERSARY1. 
 

 Section ADVERSARY2.

  Variable inv : mem_rel.
  Variables E1 E2 : env.
  Variable pii : eq_inv_info inv E1 E2.
  Variables PrOrcl PrPriv : PrSet.t.
  Variables Gadv Gcomm : Vset.t.

  Hypothesis Eqadvdecl : Eq_adv_decl PrOrcl PrPriv E1 E2.

  Definition test_orcl IA o :=  
   let no := BProc.p_name o in
    if eqb_var_decl (proc_params E1 no) (proc_params E2 no) then 
     match pii.(pii_info) no with
     | Some pio => 
       Vset.forallb (fun x => 
        if Vset.mem x (pi_mod (pi_eq_refl1 pio)) then Vset.mem x (pii_output pio)
         else if Vset.mem x (pi_mod (pi_eq_refl2 pio)) then Vset.mem x (pii_output pio)
         else true) IA
     | _ => false
     end
    else false.

  Definition check_orcl IA := PrSet.forallb (test_orcl IA) PrOrcl.
  
  Lemma test_orcl_spec : forall IA o, test_orcl IA o ->
   proc_params E1 (BProc.p_name o) = proc_params E2 (BProc.p_name o) /\
   exists pio : proc_eq_inv_info inv E1 E2 (BProc.p_name o),
    pii.(pii_info) (BProc.p_name o) = Some pio /\
    forall x : Vset.E.t,
     Vset.mem x IA ->
     Vset.mem x (pi_mod (pi_eq_refl1 pio)) \/
     Vset.mem x (pi_mod (pi_eq_refl2 pio)) -> Vset.mem x (pii_output pio).
  Proof.
   unfold test_orcl; intros IA o.
   generalize (eqb_var_decl_spec 
    (proc_params E1 (BProc.p_name o)) (proc_params E2 (BProc.p_name o)));
   destruct (eqb_var_decl (proc_params E1 (BProc.p_name o)) (proc_params E2 (BProc.p_name o)));
   [intro | intros; discriminate].
   destruct (pii_info pii (BProc.p_name o)); intros; try discriminate.
   split; trivial.
   exists p; split; trivial.
   intros x Hx; apply Vset.forallb_correct with (x:=x) in H0; trivial.
   intros [W | W]; rewrite W in H0; trivial.
   destruct (Vset.mem x (pi_mod (pi_eq_refl1 p))); trivial.
   intros x0 y Heq; rewrite (Heq: x0 = y); trivial.
  Qed.
  
  Lemma check_orcl_params : forall IA, 
   check_orcl IA ->
   forall o, PrSet.mem o PrOrcl -> 
    proc_params E1 (BProc.p_name o) = proc_params E2 (BProc.p_name o).
  Proof.
   unfold check_orcl; intros.
   apply PrSet.forallb_correct with (x:=o) in H; trivial.
   apply test_orcl_spec in H; destruct H; trivial.
   intros x y Heq; rewrite (Heq : x = y); trivial.
  Qed.

  Lemma check_orcl_exists : forall IA, check_orcl IA ->
   forall o, PrSet.mem o PrOrcl -> 
    exists pio : proc_eq_inv_info inv E1 E2 (BProc.p_name o),
     pii.(pii_info) (BProc.p_name o) = Some pio.
  Proof.
   unfold check_orcl; intros.
   apply PrSet.forallb_correct with (x:=o) in H; trivial.
   apply test_orcl_spec in H; destruct H; trivial.
   destruct H1 as (pio, (H2, _)); exists pio; trivial.
   intros x y Heq; rewrite (Heq : x = y); trivial.
  Qed.

  Lemma check_orcl_incl : forall IA, check_orcl IA ->
   forall o, PrSet.mem o PrOrcl ->    
    forall pio, pii.(pii_info) (BProc.p_name o) = Some pio ->
     forall x : Vset.E.t,
      Vset.mem x IA ->
      Vset.mem x (pi_mod (pi_eq_refl1 pio)) \/
      Vset.mem x (pi_mod (pi_eq_refl2 pio)) -> Vset.mem x (pii_output pio).
  Proof.
   unfold check_orcl; intros.
   apply PrSet.forallb_correct with (x:=o) in H; trivial.
   apply test_orcl_spec in H; destruct H; trivial.
   destruct H4 as (pio', (H5, H6)).
   rewrite H1 in H5; inversion H5; clear H5; subst; auto.
   intros x0 y Heq; rewrite (Heq : x0 = y); trivial.
  Qed.

  Definition build_adv_inv_info fr (f:Proc.proc fr)
   (Hwf : WFAdv PrOrcl PrPriv Gadv Gcomm E1 f)
   (alossless : bool)
   (aloss1 : alossless -> lossless E1 (proc_body E1 f))
   (aloss2 : alossless -> lossless E2 (proc_body E2 f)) :
   option (proc_eq_inv_info inv E1 E2 f).
   intros fr f Hwf alossless aloss1 aloss2.
   set (tga := check_global Gadv).
   case_eq tga;[intros Htga | intros; exact None].
   set (tgc := check_global Gcomm).
   case_eq tgc;[intros Htgc | intros; exact None].
   generalize check_orcl_exists check_orcl_incl.
   case pii.
   intros X1 X2 Hdep Hglob Hdec pio WW1 WW2.
   case_eq (Vset.disjoint X1 Gadv); intros Hd1;[ | exact None].
   case_eq (Vset.disjoint X2 Gadv); intros Hd2;[ | exact None].
   case_eq (iinput_Adv PrOrcl Gadv Gcomm pio);[intros IA HIA | intros; exact None].
   case_eq (check_orcl IA); intros;[ | exact None].
   assert (Eq_orcl_params PrOrcl E1 E2).
   refine (fun t (o : Proc.proc t) => check_orcl_params _ H (BProc.mkP o)).
   case_eq (PrSet.mem (BProc.mkP f) PrOrcl); intros; [ exact None | ].
   case_eq (PrSet.mem (BProc.mkP f) PrPriv); intros; [ exact None | ].
   assert (~ PrSet.mem (BProc.mkP f) PrOrcl).
     clear WW1 WW2 H2 H0 H HIA IA Hd2 Hd1 pio Hglob Hdep X2 X1 Htgc tgc Htga tga aloss2 aloss1 alossless.
     abstract (rewrite H1; intro; discriminate).
   assert (~ PrSet.mem (BProc.mkP f) PrPriv).
     clear WW1 WW2 H1 H0 H HIA IA Hd2 Hd1 pio Hglob Hdep X2 X1 Htgc tgc Htga tga aloss2 aloss1 alossless.
     abstract (rewrite H2; intro; discriminate).
   assert (WFAdv PrOrcl PrPriv Gadv Gcomm E2 f).
     apply WFAdv_trans with E1; trivial.
   case (@build_adv_info E1 (@refl1_info inv E1 E2 pii) 
           PrOrcl PrPriv Gadv Gcomm fr f Hwf alossless aloss1);[intros eqr1 | exact None].
   case (@build_adv_info E2 (@refl2_info inv E1 E2 pii) 
           PrOrcl PrPriv Gadv Gcomm fr f H5 alossless aloss2);[intros eqr2 | exact None].
   set (output := ioutput_adv IA (pi_mod eqr1) (pi_mod eqr2)).
   set (d:= Build_dproc_eq_inv_info eqr1 eqr2 IA (Vset_of_var_decl (proc_params E1 f)) output).
   apply Some; apply Build_proc_eq_inv_info with (dpii := d).
   abstract (constructor; simpl;
   [ intros; apply iinput_Adv_global with (3 := HIA); trivial;
     apply check_global_spec; trivial
   | destruct (Eqadvdecl f H3 H4) as (W1, _); rewrite W1; auto with set
   | destruct (Eqadvdecl f H3 H4) as (W1, _); rewrite W1; auto with set
   | unfold output, ioutput_adv; intros x; rewrite VsetP.inter_spec;
     intros (W1, _); apply iinput_Adv_global with (3 := HIA); trivial;
     apply check_global_spec; trivial
   | unfold output; apply WFAdv_EqObsInv with PrOrcl PrPriv Gadv Gcomm X1 X2 pio; trivial;
     [ apply check_global_spec; trivial
     | apply check_global_spec; trivial
     | intros o H6; exact (WW1 _ H o H6)
     | intros o pio0 Hm; exact (WW2 _ H o Hm pio0) ]
   ]).
  Defined.
 
  Definition add_adv_info fr (f:Proc.proc fr)
   (Hwf : WFAdv PrOrcl PrPriv Gadv Gcomm E1 f)
   (alossless : bool)
   (aloss1 : alossless -> lossless E1 (proc_body E1 f))
   (aloss2 : alossless -> lossless E2 (proc_body E2 f)) :=
   match @build_adv_inv_info fr f Hwf alossless aloss1 aloss2 with 
   | Some i => @add_pii_info inv E1 E2 fr f i pii
   | _ => pii
   end.

 End ADVERSARY2.


 Section ADVERSARY3.

  Variable inv : mem_rel.
  Variables E1 E2 : env.
  Variables PrOrcl PrPriv : PrSet.t.
  Variables Gadv Gcomm : Vset.t.
  Variable EqAD : Eq_adv_decl PrOrcl PrPriv E1 E2.
  Variable Ar : T.type.
  Variable A : Proc.proc Ar.

  Hypothesis Awf : WFAdv PrOrcl PrPriv Gadv Gcomm E1 A.

  Hypothesis Aloss1 : 
   (forall O, PrSet.mem O PrOrcl -> lossless E1 (proc_body E1 (BProc.p_name O))) -> 
   lossless E1 (proc_body E1 A).

  Hypothesis Aloss2 : 
   (forall O, PrSet.mem O PrOrcl -> lossless E2 (proc_body E2 (BProc.p_name O))) -> 
   lossless E2 (proc_body E2 A).

  Variable pii : eq_inv_info inv E1 E2.

  Definition test_lossless_orcl O := 
   match pii.(pii_info) (BProc.p_name O) with 
   | Some pi => 
     andb (pi_lossless (pi_eq_refl1 pi)) (pi_lossless (pi_eq_refl2 pi))
   | _ => false
   end.

  Lemma check_lossless_spec :
   PrSet.forallb test_lossless_orcl PrOrcl ->
   lossless E1 (proc_body E1 A) /\ lossless E2 (proc_body E2 A).
  Proof.
   intros.
   assert (forall x y : PrSet.E.t, PrSet.E.eq x y -> test_lossless_orcl x = test_lossless_orcl y).
   intros x y H1; rewrite (H1 : x = y); trivial.
   assert (W:=  PrSet.forallb_correct _ H0 _ H). 
   split;[apply Aloss1 | apply Aloss2];
   (intros O H1; assert (W1:= W _ H1); unfold test_lossless_orcl in W1;
   destruct (pii_info pii (BProc.p_name O));[ | discriminate];
   rewrite is_true_andb in W1; destruct W1).
   apply (pi_lossless_spec _ H2).
   apply (pi_lossless_spec _ H3).
  Qed.
  
  Definition add_adv_info_lossless  : eq_inv_info inv E1 E2.
   intros.
   apply add_adv_info with (1:= pii) (2:= EqAD) (3:= Awf) 
    (alossless:=PrSet.forallb test_lossless_orcl PrOrcl).
   abstract (intros H1; exact (proj1 (check_lossless_spec H1))).
   abstract (intros H1; exact (proj2 (check_lossless_spec H1))).
  Defined.

  Definition add_adv_info_false : eq_inv_info inv E1 E2.
   intros.
   apply add_adv_info with (1:= pii) (2:= EqAD) (3:= Awf) 
   (alossless :=false).
   abstract (intros; discriminate).
   abstract (intros; discriminate).
  Defined.

 End ADVERSARY3.


 Section UPTO.
 
  Variable bad : Var.var T.Bool.

  Definition empty_upto_info bad E1 E2 : upto_info bad E1 E2.
   intros.
   refine (@mk_p_upto_info _ _ _ (fun _ _ => false) _ _ _);
    intros ? ? H; discriminate.
  Defined.

  Definition dadd_upto_info E1 E2 (pi:upto_info bad E1 E2) tf (f:Proc.proc tf) :=
   let i_f := 
    (Var.is_global bad &&
     E.eqb (proc_res E1 f) (proc_res E2 f) &&
     eqb_var_decl (proc_params E1 f) (proc_params E2 f) &&
     preserves_bad bad pi (proc_body E1 f) &&
     preserves_bad bad pi (proc_body E2 f) &&
     upto_bad bad pi (proc_body E1 f) (proc_body E2 f))%bool in
    fun tg (g:Proc.proc tg) =>
     if Proc.eqb f g then i_f else pi _ g.
  
  Lemma sadd_upto_info1 : forall E1 E2 (pi:upto_info bad E1 E2) tf (f:Proc.proc tf),
   prbad_spec bad E1 (dadd_upto_info pi f).
  Proof.
   intros; unfold dadd_upto_info; red; intros.
   generalize (Proc.eqb_spec_dep f p); destruct (Proc.eqb f p).
   intros Heq; inversion Heq; simpl.
   repeat rewrite is_true_andb in H.
   destruct H as (((((Gbad, W1), W2), W3), W4), W5).
   apply (@preserves_bad_spec _ Gbad E1 pi (pi.(upto_pr1)) (proc_body E1 f) W3 _ m f0); trivial.
   intros; apply pi.(upto_pr1); trivial.
  Qed.

  Lemma sadd_upto_info2 : forall E1 E2 (pi:upto_info bad E1 E2) tf (f:Proc.proc tf),
   prbad_spec bad E2 (dadd_upto_info pi f).
  Proof.
   intros; unfold dadd_upto_info; red; intros.
   generalize (Proc.eqb_spec_dep f p); destruct (Proc.eqb f p).
   intros Heq; inversion Heq; simpl.
   repeat rewrite is_true_andb in H.
   destruct H as (((((Gbad, W1), W2), W3), W4), W5).
   apply (@preserves_bad_spec _ Gbad E2 pi (pi.(upto_pr2)) (proc_body E2 f) W4 _ m f0); trivial.
   intros; apply pi.(upto_pr2); trivial.
  Qed.
  
  Lemma sadd_upto_info : forall E1 E2 (pi:upto_info bad E1 E2) tf (f:Proc.proc tf),
   upto_spec bad E1 E2 (dadd_upto_info pi f).
  Proof.
   intros; unfold dadd_upto_info; red; intros.
   generalize (Proc.eqb_spec_dep f p); destruct (Proc.eqb f p).
   intros Heq; inversion Heq; simpl.
   repeat rewrite is_true_andb in H.
   destruct H as (((((Gbad, W1), W2), W3), W4), W5).
   split.
   intros; apply upto_bad_correct with (info := pi) (k:=k); auto.
   apply pi.(supto).
   apply pi.(upto_pr1).
   apply pi.(upto_pr2).
   split.
   generalize (E.eqb_spec (proc_res E1 f) (proc_res E2 f)); rewrite W1; trivial.
   generalize (eqb_var_decl_spec (proc_params E1 f) (proc_params E2 f)); rewrite W2; trivial.
   intros; apply pi.(supto); trivial.
  Qed.

  Definition add_upto_info E1 E2 (pi:upto_info bad E1 E2) tf (f:Proc.proc tf) :=
   @mk_p_upto_info bad E1 E2
   (dadd_upto_info pi f) 
   (sadd_upto_info1 pi f) 
   (sadd_upto_info2 pi f) 
   (sadd_upto_info pi f).

  
  Section Adv.

   Variables PrOrcl PrPriv : PrSet.t.
   Variables Gadv Gcomm : Vset.t.
   Variables E1 E2 : env.
   Variable pi : upto_info bad E1 E2.

   Hypothesis HEq : Eq_adv_decl PrOrcl PrPriv E1 E2.

   Hypothesis HeqO : Eq_orcl_params PrOrcl E1 E2.
   
   Variable tA : T.type.
   Variable A : Proc.proc tA.
  
   Hypothesis Hwf : WFAdv PrOrcl PrPriv Gadv Gcomm E1 A.
   
   Definition dadd_adv_upto_info := 
    let i_A := 
     (Var.is_global bad &&
      check_adv_upto_info PrOrcl Gadv bad pi &&
      negb (PrSet.mem (BProc.mkP  A) PrOrcl) && 
      negb (PrSet.mem (BProc.mkP  A) PrPriv))%bool in
     fun tg (g:Proc.proc tg) =>
      if Proc.eqb A g then i_A else pi _ g.
   
   Lemma sadd_adv_upto_info1 : prbad_spec bad E1 dadd_adv_upto_info.
   Proof.
    unfold dadd_adv_upto_info; red; intros.
    destruct Hwf as (O, (H1, H2)).
    generalize (Proc.eqb_spec_dep A p); destruct (Proc.eqb A p).
    repeat rewrite is_true_andb in H; destruct H as (((Gbad, W1), W2), W3).   
    intros Heq; inversion Heq; simpl.
    eapply upto_adv_preserves with (pi:= pi) (k:= k); eauto.
    apply pi.(upto_pr1).
    intros; apply pi.(upto_pr1); trivial.
   Qed.

   Lemma sadd_adv_upto_info2 : prbad_spec bad E2 dadd_adv_upto_info.
   Proof.
    unfold dadd_adv_upto_info; red; intros.
    generalize (Proc.eqb_spec_dep A p); destruct (Proc.eqb A p).
    intros Heq; inversion Heq; simpl.
    repeat rewrite is_true_andb in H; destruct H as (((Gbad, W1), W2), W3).   
    rewrite is_true_negb in W2, W3.
    destruct (WFAdv_trans HeqO HEq W2 W3 Hwf) as (O, (H5, H6)).
    eapply upto_adv_preserves with (pi:= pi) (k:= k); eauto.
    apply pi.(upto_pr2).
    intros; apply pi.(upto_pr2); trivial.
   Qed.

   Lemma sadd_adv_upto_info :  upto_spec bad E1 E2 dadd_adv_upto_info.
   Proof.
    unfold dadd_adv_upto_info; red; intros.
    generalize (Proc.eqb_spec_dep A p); destruct (Proc.eqb A p).
    intros Heq; inversion Heq; simpl.
    repeat rewrite is_true_andb in H; destruct H as (((Gbad, W1), W2), W3).   
    rewrite is_true_negb in W2, W3.
    destruct (HEq A W2 W3) as (V1, (U2, U3)).
    split; auto.
    destruct Hwf as (O, (I1, I2)).
    intros; rewrite <- U2; eapply upto_adv_upto with (pi:= pi) (k:=k); eauto.
    intros; apply pi.(supto); trivial.
   Qed.

   Definition add_adv_upto_info  :=
    @mk_p_upto_info bad E1 E2
    dadd_adv_upto_info
    sadd_adv_upto_info1
    sadd_adv_upto_info2
    sadd_adv_upto_info.

  End Adv.

 End UPTO.

 Lemma add_decl_same_mk : forall (E:env) (t:T.type) (f:Proc.proc t)
  (params:var_decl (Proc.targs f)) (Hl:dforallb Var.vis_local params)
  (body:cmd) (res:E.expr t),
  (add_decl E f params Hl body res) _ f =
  mk_Decl params res body (dforallb_local params Hl).
 Proof.
  intros; unfold add_decl; simpl. 
  case_eq (T.eq_dec t t); intros.
  rewrite (T.UIP_refl e).
  case_eq (Proc.eq_dec f f); intros.
  rewrite (Proc.UIP_refl e0); auto.
  elim (Proc.eq_dec_r H0); trivial.
  elim (T.eq_dec_r H); trivial.
 Qed.

 Lemma add_decl_other_mk : forall (E:env) (t1 t2:T.type) 
  (f:Proc.proc t1) (g:Proc.proc t2)
  (params:var_decl (Proc.targs f)) (Hl:dforallb Var.vis_local params)
  (body:cmd) (res:E.expr t1), 
  (BProc.mkP f) <> (BProc.mkP g) ->
  (add_decl E f params Hl body res) _ g = E _ g.
 Proof.
  intros; unfold add_decl; simpl. 
  case_eq (T.eq_dec t1 t2); intros; auto.
  clear H0.
  generalize e g H; clear g H; rewrite <- e; intros.
  rewrite (T.UIP_refl e0).
  case_eq (Proc.eq_dec f g); intros; auto.
  elim H; rewrite e1; constructor.
 Qed.

End Make.
