Require Export SwitchingSem.

Set Implicit Arguments.


(* ***************************** SOME AUXILIARY STUFF  ***************************** *)


Lemma eval_le : forall k (m:Mem.t k) (e1 e2:E.expr T.Nat),
 (E.eval_expr e1 m <= E.eval_expr e2 m)%nat <->
 E.eval_expr (e1 <=! e2) m.
Proof.
 intros; simpl; unfold O.eval_op; simpl; split; intro.
 apply leb_correct; omega.
 apply leb_complete in H; omega.
Qed.

 Ltac elim_random := rewrite (@deno_cons_elim _ _ (_ <$- _)), Mlet_simpl, deno_random_elim.
 Ltac elim_assign := rewrite (@deno_cons_elim _ _ (_ <- _)), Mlet_simpl, deno_assign_elim.
 Ltac elim_cond b m := let H := fresh "Hguard" in
   repeat (rewrite (@deno_cons_elim _ _ (If _ then _ else _)), Mlet_simpl, (@deno_cond_elim _ _ b _ _ m));
     case_eq (@E.eval_expr _ T.Bool b m); intro H.
 Ltac welim_cond b m := rewrite (@deno_cons_elim _ _ (If _ then _ else _)), Mlet_simpl, deno_cond_elim.

    
 Lemma non_lossless_uptobad: forall e1 c1 e2 c2 (bad: Var.var T.Bool) (pi: upto_info bad e1 e2) 
    k (m:Mem.t k) (P : Mem.t k -o> boolO),
   Var.is_global bad ->
   check_bad pi c1 c2 ->
   Uabs_diff (Pr e1 c1 m P) (Pr e2 c2 m P) <= 
   Uabs_diff (Pr e1 c1 m (P[&&]EP k bad)) (Pr e2 c2 m (P[&&]EP k bad)).
 Proof.
  intros.
  rewrite (@Pr_split _ e1 _ _ (EP k bad)), (@Pr_split _ e2 _ _ (EP k bad)).
  rewrite Uabs_diff_plus.
  match goal with |- _ + ?X <= _ =>  assert (X == 0) end.
    rewrite Uabs_diff_zero.
    unfold Pr; apply upto_bad_and_neg with pi; trivial.
  rewrite H1, Uplus_zero_right; trivial.
 Qed.

(* ********************************************************************************* *)


Notation bad1 := (Var.Gvar T.Bool 1).
Notation bad2 := (Var.Gvar T.Bool 2).
Notation L := (Var.Gvar (T.List (T.Pair (T.User BS_k) (T.User BS_k))) 3).
Notation x := (Var.Lvar (T.User BS_k) 4).
Notation y := (Var.Lvar (T.User BS_k) 5).
Notation b := (Var.Lvar T.Bool 6).

Notation F := (Proc.mkP 1 ((T.User BS_k):: nil) (T.User BS_k)).
Definition F_params : var_decl (Proc.targs F) := dcons _ x (dnil _).
Definition F_res := y.


Section ADVERSARY.

 Variable env_adv : env.

 Notation A  := (Proc.mkP 2 nil T.Bool).

 Definition A_params : var_decl (Proc.targs A) := dnil _.
 Variable A_body : cmd.
 Variable A_res : E.expr T.Bool.

 Definition mkEnv F_body := 
  let Ef := add_decl env_adv F F_params (refl_equal true) F_body F_res in
   add_decl Ef A A_params (refl_equal true) A_body A_res.



 (* *********************************************************************** *)
 (* ********************** GAME Gf: random function  ********************** *)
 (* *********************************************************************** *)

 Definition G0 :=
  [ 
   L <- Nil _;
   b <c- A with {}
  ].


 Definition Of :=
 [ 
  If !(x in_dom L) _then 
  [ 
   y <$- {0,1}^k; 
   L <- (x|y) |::| L
  ];
  y <- L[{x}]
 ].

 Definition Ef := mkEnv Of.

 Definition PrOrcl := PrSet.singleton (BProc.mkP F).
 Definition PrPriv := PrSet.empty.

 Definition Gadv := Vset.empty.
 Definition Gcomm := Vset.empty.

 Hypothesis A_wf : WFAdv PrOrcl PrPriv Gadv Gcomm Ef A.
 
 Hypothesis A_lossless : forall Fbody,
  (forall O, PrSet.mem O PrOrcl -> 
   lossless (mkEnv Fbody) (proc_body (mkEnv Fbody) (BProc.p_name O))) -> 
  lossless (mkEnv Fbody) A_body.

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

 Lemma EqOR : forall F_body1 F_body2 t (p:Proc.proc t), 
  PrSet.mem (BProc.mkP p) PrOrcl -> 
  proc_res (mkEnv F_body1) p = proc_res (mkEnv F_body2) p.
 Proof.
  unfold mkEnv; intros.
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

 (* Function to build infos for invariants *)
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



 (* *********************************************************************** *)
 (* ********************* GAME Gp: random permutation  ******************** *)
 (* *********************************************************************** *)

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

 Definition Ep := mkEnv Op.

 Definition iEp := i_refl Op Op Vset.empty Vset.empty.

 (* Event of interest *)
 Definition Ev :=  b && (Elength L <=! q).



 (* *********************************************************************** *)
 (* ******************************  GAME Gf'  ***************************** *)
 (* *********************************************************************** *)
 (* Augment Gf with bad flags *)

 Definition Of' := (bad1<-false) :: 
   (Op_gen [ If (Elength L <! q) then [bad1 <- true] else [bad2 <- true] ]).

 Definition Ef' := mkEnv Of'.

 Definition i_Ef_Ef' : eq_inv_info trueR Ef Ef' := 
  i_refl Of Of' Vset.empty {{bad1}}.

 Lemma Pr_f_f': forall k (m:Mem.t k),
  Pr Ef G0 m (EP k Ev) == Pr Ef' G0 m (EP k Ev).
 Proof.
  intros. 
  apply EqObs_Pr with Gadv.
  eqobs_in i_Ef_Ef'. 
 Qed.



 (* *********************************************************************** *)
 (* ***************************** GAME Gp_bad ***************************** *)
 (* *********************************************************************** *)
 (*  Resample the hash value when a collisions ocurres only if [|L|<q] *) 


 Definition Op_bad := (bad1<-false) :: 
   (Op_gen [ If (Elength L <! q) then (bad1 <- true)::c else [bad2<-true] ]).

 Definition Epbad := mkEnv Op_bad.

 Section Rtriple.
  
  Variable k: nat.
  
  Definition h := fun n => if leb (S n) (q_poly k) then n*/([1/2]^k) else 0.

  Definition Fb c := fun (m:Mem.t k) => mu ([[c]] Ef' m)
       (fun m' => sum_f (E.eval_expr (Elength L) m) (E.eval_expr (Elength L) m') h).

  Lemma Orc_distance: rtriple Ef' Epbad Of' Op_bad (Fb Of').
  Proof.
   intros m f; unfold Of', Op_bad, Fb.
   repeat elim_assign; simpl (E.eval_expr false m); set (mb:= m {!bad1 <-- false!}).
   rewrite Uabs_diff_sym, (@upto_bad_GSD _ _ _  bad1 is_true_true (empty_upto_info bad1 _ _));
     [ | |  apply is_lossless_correct with (pi := refl2_info i_Ef_Ef'); vm_compute ]; trivial.
   unfold Pr, Op_gen, Fb.
   elim_cond (!(x in_dom L)) mb.
     (* case [~(x in_dom L)] *)
     transitivity (if @E.eval_expr _ T.Bool (Elength L <! q) m then
       E.eval_expr (Elength L) m /2^ k else 0).

       set (def:=T.default k (T.Pair (T.User BS_k) (T.User BS_k))).
       transitivity ( mu (sum_support (T.default k (T.User BS_k)) (E.eval_support {0,1}^k mb))
         (fun x => if @E.eval_expr _ T.Bool (Elength L <! q) m then sigma (fun i =>
           charfun (T.i_eqb k (T.User BS_k) x) (snd (nth i (m L) def)))
         (length (m L)) else 0)).
         elim_random; apply mu_monotonic; intro v.
         elim_cond  (y in_range L)  (mb{!y <-- v!}).
           (* collision ocurred *)
           rewrite deno_cond_elim.
           rewrite (@depend_only_fv_expr T.Bool (Elength (L) <! q) _ _ m); [ |
            intros t x Hx; rewrite <-(Vset.singleton_complete _ _ Hx); unfold mb; mem_upd_simpl ]. 
           case (@E.eval_expr _ T.Bool (Elength (L) <! q) m).
             (* case [ < q ] *)
            rewrite (sigma_finite_sum def (fun w => charfun (T.i_eqb _ _ v) (snd w))). 
            repeat rewrite deno_assign_elim.
            generalize Hguard0; clear Hguard0.
            unfold EP, charfun, restr, fone, mb; simpl; unfold O.eval_op; simpl; mem_upd_simpl.
            generalize (m L); induction 0; simpl; intros; try discriminate.
            destruct (UT.i_eqb v (snd a)); Usimpl; auto.
            (* case [ >= q ] *)
            repeat rewrite deno_assign_elim.
            unfold EP, charfun, restr, fone, mb; simpl; unfold O.eval_op; simpl; mem_upd_simpl.
          (* no collision *)
          rewrite deno_nil_elim, deno_assign_elim, deno_assign_elim.
          unfold EP, charfun, restr, fone, mb; simpl; unfold O.eval_op; simpl; mem_upd_simpl.

        case (@E.eval_expr _ T.Bool (Elength (L) <! q) m).
          rewrite (mu_sigma_le _ (fun i v => charfun (T.i_eqb k (T.User BS_k) v) 
            (snd (nth i (m L) def))) (length (m L))), Nmult_sigma; apply sigma_le_compat.
          intros i Hi.
          set (li := snd (nth i (m L) def)); simpl in li; fold li.
          apply (@Pr_bs_support k (T.default _ (T.User BS_k)) li
            (fun e v => if T.i_eqb k (T.User BS_k) v e then 1 else 0)).
          intros x; rewrite <- (is_true_Ti_eqb k (T.User BS_k) x).
          destruct (T.i_eqb _ (T.User BS_k) x li); intros H; [ elim H | ]; trivial.
          rewrite Ti_eqb_refl; trivial.
          rewrite sum_support_const; [ trivial | apply bs_support_not_nil ].

      rewrite deno_cons_elim, Mlet_simpl.
      rewrite <-(mu_cte_eq ([[ [y <$- {0,1}^k] ]] Ef' mb) _);
        [ | apply lossless_random ].
      repeat rewrite deno_random_elim.
      refine (mu_monotonic _ _ _ _); refine (ford_le_intro _); intro i; unfold fcte.
      elim_cond (y in_range L) (mb {!y <-- i!}).
        (* collision occurred *)
        rewrite deno_cond_elim.
        rewrite (@depend_only_fv_expr T.Bool (Elength (L) <! q) _ m (mb {!y <-- i!})); [ |
          intros t x Hx; rewrite <-(Vset.singleton_complete _ _ Hx); unfold mb; mem_upd_simpl ]. 
        case_eq (@E.eval_expr _ T.Bool (Elength (L) <! q) (mb{!y<--i!})); intro HlenL.
          (* [ _ < q] *)
          repeat rewrite deno_assign_elim.
          simpl; unfold O.eval_op; simpl; mem_upd_simpl; simpl.
          replace (mb L) with (m L) by (unfold mb; mem_upd_simpl).
          rewrite sum_f_non_empty, <-Ule_plus_right; trivial.
          unfold h.
          replace (m L) with ((mb {!y <-- i!}) L) by (unfold mb; mem_upd_simpl).
          replace (S (length ((mb {!y <-- i!}) L))) with ((length ((mb {!y <-- i!}) L)) + 1)%nat by omega.
          setoid_rewrite HlenL; trivial.
          (* [ _ > q] *)
          trivial.
        (* no collision *)
        rewrite deno_nil_elim, deno_assign_elim, deno_assign_elim.
        simpl; unfold O.eval_op; simpl; mem_upd_simpl; simpl.
        replace (mb L) with (m L) by (unfold mb; mem_upd_simpl).
        rewrite sum_f_non_empty, <-Ule_plus_right; trivial.
        replace ((length (m L)) + 1)%nat with (S (length (m L))) by omega; trivial.

    (* case [(x in_dom L)] *)
    rewrite deno_nil_elim, deno_assign_elim.
    unfold EP, charfun, restr, fone, mb; simpl; unfold O.eval_op; simpl; mem_upd_simpl.
  Qed.

  Lemma Orc_range: forall (m:Mem.t k),
    range (fun m' => (E.eval_expr (Elength L) m <= E.eval_expr (Elength L) m')%nat)
     (([[proc_body Ef' F]]) Ef' m).
  Proof.
   intros m f Hf.
   rewrite <-(mu_zero ([[proc_body Ef' F]] Ef' m)).
   apply equiv_deno with (P:=Meq /-\ EP1 ((length (m L)) =?= Elength L))
     (Q:=req_mem_rel {{L}} (EP1 ((length (m L)) <=! Elength L))).
     deadcode.
     unfold EP1; eqobsrel_tail; simpl; unfold O.eval_op; simpl.
     intros k' m1 m2 [_ H2]; rewrite (nat_eqb_true H2); split; [ intros _ v _ | intros _].
       mem_upd_simpl; simpl; apply leb_correct; auto.
       apply leb_correct; auto.
   unfold EP1; intros m1 m2 [H1m H2m].
   apply Hf.
     generalize (proj2 (eval_le _ _ _) H2m); simpl; unfold O.eval_op; simpl.
     rewrite (H1m _ L); trivial.
     split; [ trivial | refine (nat_eqb_refl _) ].
 Qed.

  Lemma Pr_Ef'_Epbad : forall (m:Mem.t k),
    Uabs_diff (Pr Ef' G0 m (EP k Ev)) (Pr Epbad G0 m (EP k Ev)) <=
    ((q_poly k - 1) * q_poly k)/2^(1 + k).
  Proof.
   intros.
   unfold G0, Pr.
   repeat elim_assign.
   refine (rtriple_adv_retract (EqOP _ _) (EqOR _ _) (EqAD _ _) (depend_only_fv_expr (Elength L)) 
     _ _ (q_poly k) ([1/2]^k) _ _ _ _ _ _ _ _ _ (m {!L <-- nil!}) _).
    intros x Hx; rewrite <-(Vset.singleton_complete _ _ Hx); trivial.
    intros ? _; apply Vset.empty_spec.
    apply is_lossless_correct with (pi := refl2_info i_Ef_Ef'); 
     vm_compute; trivial.
    apply Orc_distance.
    apply Orc_range.
    discriminate.
    discriminate.
    unfold Ef'; apply A_wf_E; intros x Hx; discriminate Hx.
    intros x Hx; discriminate Hx.
   Qed.
 
 End Rtriple.


 
 (* *********************************************************************** *)
 (* ******************************  GAME Gp'  ***************************** *)
 (* *********************************************************************** *)
 (* Augment Gp with bad flags *)

 Definition Op' := (bad1<-false) :: 
   (Op_gen [ If (Elength L <! q) then (bad1 <- true)::c else (bad2<-true)::c ]).

 Definition Ep' := mkEnv Op'.

 Definition i_Ep_Ep' : eq_inv_info trueR Ep Ep' := 
  i_refl Op Op' Vset.empty {{bad1}}.

 Lemma Pr_p_p': forall k (m:Mem.t k),
  Pr Ep G0 m (EP k Ev) == Pr Ep' G0 m (EP k Ev).
 Proof.
  intros. 
  apply EqObs_Pr with Gadv.
  eqobs_in i_Ep_Ep'. 
 Qed.


 Definition inv:= EP1 (bad2 && (Elength L <=! q) =?= false).

 Lemma dep_inv: depend_only_rel inv (Vset.union {{L, bad2}} Vset.empty) Vset.empty.
 Proof.  apply depend_only_EP1. Qed.

 Definition i_inv_empty_Epbad: eq_inv_info inv Epbad  Epbad.
  refine (@empty_inv_info inv (Vset.union {{L,bad2}} Vset.empty)  
   Vset.empty _ _ _ _ _).
    exact dep_inv.
    vm_compute; trivial.
    unfold inv; auto.
 Defined.


 Lemma O_inv_Epbad_Epbad: 
  EqObsInv inv (Vset.add bad2 (Vset.add x (Vset.singleton L))) 
  Epbad Op_bad Epbad Op_bad 
  (Vset.add bad2 (Vset.add y (Vset.singleton L))).
 Proof.
  unfold Op_bad, Op_gen.
  eqobs_ctxt i_inv_empty_Epbad.
  deadcode i_inv_empty_Epbad.
  cp_test (x in_dom L); rewrite proj1_MR.
    (* [~ (x in_dom L)] *)
    eqobsrel_tail; intros k m1 m2; intros [_ ?]; assumption. 
    (* [x in_dom L] *)
    eqobs_hd i_inv_empty_Epbad.
    cp_test (y in_range L); rewrite proj1_MR.
      (* collision *)
      cp_test (Elength L <! q).
        (* case [ |L| < q] *)
        rewrite proj1_MR.
        apply equiv_cons with (Q:=req_mem_rel {{y, bad1, bad2, x, L}} inv).
          eapply equiv_weaken; [ | apply equiv_while ].
            intros k m1 m2 [ ? _]; assumption.
            intros k m1 m2 [ H _]; apply depend_only_fv_expr;
              eapply req_mem_weaken with (2:=H); vm_compute; trivial.
            eqobs_in i_inv_empty_Epbad; intros k m1 m2 [_ [? _] ]; assumption.
          eqobsrel_tail; unfold inv, EP1; simpl; unfold O.eval_op; simpl.
          intros k m1 m2 [H1 H2]; mem_upd_simpl.
          generalize H2; clear H2; case (m1 bad2);
            [ repeat rewrite andb_true_l | repeat rewrite andb_false_l ]; intro H2.
            rewrite leb_correct_conv; [ trivial | change (length ((m1 x, m1 y) :: m1 L))
              with (S (length (m1 L)))  ].
            apply lt_trans with (1:=leb_complete_conv _ _ (eqb_prop _ _ H2)); auto.
            trivial.
        (* case [ |L| >= q] *)
        eqobsrel_tail; unfold inv, notR, EP1; simpl; unfold O.eval_op; simpl.
        intros k m1 m2 [H1 [_ [H2 _] ] ]; mem_upd_simpl.
        rewrite andb_true_l, leb_correct_conv; [ trivial | change (length ((m1 x, m1 y) :: m1 L))
              with (S (length (m1 L)))  ].
        generalize (leb_complete_conv _ _ (not_true_is_false _ H2)).
        rewrite plus_comm; trivial.
      (* no collision *)
      eqobsrel_tail; unfold inv, EP1; simpl; unfold O.eval_op; simpl.
      intros k m1 m2 [H1 H2]; mem_upd_simpl.
      generalize H2; clear H2; case (m1 bad2);
        [ repeat rewrite andb_true_l | repeat rewrite andb_false_l ]; intro H2.
         rewrite leb_correct_conv; [ trivial | change (length ((m1 x, m1 y) :: m1 L))
              with (S (length (m1 L)))  ].
            apply lt_trans with (1:=leb_complete_conv _ _ (eqb_prop _ _ H2)); auto.
            trivial.
 Qed.

 Definition i_inv_Epbad_Epbad := iEinv i_inv_empty_Epbad Vset.empty Vset.empty O_inv_Epbad_Epbad.

 Definition i_inv_empty_Ep': eq_inv_info inv Ep' Ep'.
  refine (@empty_inv_info inv (Vset.union {{L,bad2}} Vset.empty)  
   Vset.empty _ _ _ _ _).
    apply depend_only_EP1.
    vm_compute; trivial.
    unfold inv; auto.
 Defined.

 Lemma O_inv_Ep'_Ep': 
  EqObsInv inv (Vset.add bad2 (Vset.add x (Vset.singleton L))) 
  Ep' Op' Ep' Op' 
  (Vset.add bad2 (Vset.add y (Vset.singleton L))).
 Proof.
  unfold Op', Op_gen.
  eqobs_ctxt i_inv_empty_Ep'.
  deadcode i_inv_empty_Ep'.
  cp_test (x in_dom L); rewrite proj1_MR.
    (* [~ (x in_dom L)] *)
    eqobsrel_tail; intros k m1 m2; intros [_ ?]; assumption. 
    (* [x in_dom L] *)
    eqobs_hd i_inv_empty_Ep'.
    cp_test (y in_range L); rewrite proj1_MR.
      (* collision *)
      cp_test (Elength L <! q).
        (* case [ |L| < q] *)
        rewrite proj1_MR.
        apply equiv_cons with (Q:=req_mem_rel {{y, bad1, bad2, x, L}} inv).
          eapply equiv_weaken; [ | apply equiv_while ].
            intros k m1 m2 [ ? _]; assumption.
            intros k m1 m2 [ H _]; apply depend_only_fv_expr;
              eapply req_mem_weaken with (2:=H); vm_compute; trivial.
            eqobs_in i_inv_empty_Ep'; intros k m1 m2 [_ [? _] ]; assumption.
          eqobsrel_tail; unfold inv, EP1; simpl; unfold O.eval_op; simpl.
          intros k m1 m2 [H1 H2]; mem_upd_simpl.
          generalize H2; clear H2; case (m1 bad2);
            [ repeat rewrite andb_true_l | repeat rewrite andb_false_l ]; intro H2.
            rewrite leb_correct_conv; [ trivial | change (length ((m1 x, m1 y) :: m1 L))
              with (S (length (m1 L)))  ].
            apply lt_trans with (1:=leb_complete_conv _ _ (eqb_prop _ _ H2)); auto.
            trivial.
        (* case [ |L| >= q] *)
        set (c' := [ while y in_range L do [y <$- {0,1}^k];
          bad2 <- true; L <- (x | y) |::| L ]).
        apply equiv_trans_eq_mem_l with trueR Ep' c'; [ rewrite proj1_MR; swap; 
          apply equiv_eq_mem | | intros k m1 m2 _; unfold trueR; trivial ].
        apply equiv_trans_eq_mem_r with trueR Ep' c'; [ rewrite proj1_MR; swap; 
          apply equiv_eq_mem | | intros k m1 m2 _; unfold trueR; trivial ].
        unfold c'.
        match goal with |- equiv ?P _ _ _ _ _ => apply equiv_cons with P end.
          eapply equiv_weaken; [ | apply equiv_while ].
            intros k m1 m2 [ ? _]; assumption.
            intros k m1 m2 [ [H _] _]; apply depend_only_fv_expr;
              eapply req_mem_weaken with (2:=H); vm_compute; trivial.
            eapply equiv_strengthen; [ | apply equiv_random ].
              unfold notR, EP1, EP2; intros k m1 m2 [ [ [H1 H2] [H3 H4] ] _]; split.
                apply eq_refl.
                intros v _; split; split.  
                  eapply req_mem_weaken; [ | apply (req_mem_update _ _ H1) ]; compute; trivial.
                  refine (dep_inv _ _ H2); apply req_mem_upd_disjoint; trivial.
                  rewrite (@depend_only_fv_expr T.Bool (Elength (L) <! q) _ _  m1); [ |
                    apply req_mem_sym; apply req_mem_upd_disjoint ]; trivial.
                  rewrite (@depend_only_fv_expr T.Bool (Elength (L) <! q) _ _  m2); [ |
                    apply req_mem_sym; apply req_mem_upd_disjoint ]; trivial.
          eqobsrel_tail; unfold inv, notR, EP1; simpl; unfold O.eval_op; simpl.
          intros k m1 m2 [H1 [_ [H2 _] ] ]; mem_upd_simpl.
        rewrite andb_true_l, leb_correct_conv; [ trivial | change (length ((m1 x, m1 y) :: m1 L))
              with (S (length (m1 L)))  ].
        generalize (leb_complete_conv _ _ (not_true_is_false _ H2)).
        rewrite plus_comm; trivial.
      (* no collision *)
      eqobsrel_tail; unfold inv, EP1; simpl; unfold O.eval_op; simpl.
      intros k m1 m2 [H1 H2]; mem_upd_simpl.
      generalize H2; clear H2; case (m1 bad2);
        [ repeat rewrite andb_true_l | repeat rewrite andb_false_l ]; intro H2.
         rewrite leb_correct_conv; [ trivial | change (length ((m1 x, m1 y) :: m1 L))
              with (S (length (m1 L)))  ].
            apply lt_trans with (1:=leb_complete_conv _ _ (eqb_prop _ _ H2)); auto.
            trivial.
 Qed.

 Definition i_inv_Ep'_Ep' := iEinv i_inv_empty_Ep' Vset.empty Vset.empty O_inv_Ep'_Ep'.


 Definition i_Ep'_Ep':= i_refl Op' Op' Vset.empty {{bad2}}.

 Definition i_Epbad_Epbad:= i_refl Op_bad Op_bad Vset.empty {{bad2}}.

 Lemma Pr_Epbad_Ep': forall k m,
  Pr Epbad G0 m (EP k Ev) == Pr Ep' G0 m (EP k Ev).
 Proof.
  intros; unfold Pr.
  transitivity (Pr Epbad ((bad2<-false)::G0) m (EP k Ev)). 
    apply EqObs_Pr with Gadv; deadcode i_Epbad_Epbad; eqobs_in i_Epbad_Epbad.
  symmetry; transitivity (Pr Ep' ((bad2<-false)::G0) m (EP k Ev)); [ | symmetry ].
    apply EqObs_Pr with Gadv; deadcode i_Ep'_Ep'; eqobs_in i_Ep'_Ep'.
  unfold Pr; repeat elim_assign.
  rewrite <-Uabs_diff_zero; split; [ | trivial ].
  rewrite (@non_lossless_uptobad  _ G0 _ G0 _ (i_upto bad2 Op_bad Op') _ 
    (m{!bad2 <-- E.eval_expr false m!}) (EP k Ev)); trivial.
  apply (proj2 (Uabs_diff_zero _ _)).
  unfold Pr; apply Oeq_trans with 0; [ | symmetry ].

  rewrite <-(mu_zero (([[G0]]) (mkEnv Op_bad) (m {!bad2 <-- E.eval_expr false m!}))).
  apply equiv_deno with (Meq /-\ (EP1 (!bad2))) (req_mem_rel Vset.empty inv).  
    eqobs_tl i_inv_Epbad_Epbad.
    eqobsrel_tail; unfold inv, EP1; simpl; unfold O.eval_op; simpl.
    intros k' m1 m2 [H1 H2]; mem_upd_simpl; rewrite (proj1 (is_true_negb_false _) H2); trivial.  
    intros m1 m2 [_ H]; generalize H; clear H.
    unfold inv, EP1, charfun, restr, EP, andP; simpl; unfold O.eval_op; simpl.
    case (m1 bad2); simpl.
      intro H; rewrite (eqb_prop _ _ H), andb_false_r; trivial.  
      rewrite andb_false_r; trivial.
    split; [ trivial | unfold EP1; simpl; unfold O.eval_op; simpl; mem_upd_simpl ].
 
  rewrite <-(mu_zero (([[G0]]) (mkEnv Op') (m {!bad2 <-- E.eval_expr false m!}))).
  apply equiv_deno with (Meq /-\ (EP1 (!bad2))) (req_mem_rel Vset.empty inv).  
    eqobs_tl i_inv_Ep'_Ep'.
    eqobsrel_tail; unfold inv, EP1; simpl; unfold O.eval_op; simpl.
    intros k' m1 m2 [H1 H2]; mem_upd_simpl; rewrite (proj1 (is_true_negb_false _) H2); trivial.  
    intros m1 m2 [_ H]; generalize H; clear H.
    unfold inv, EP1, charfun, restr, EP, andP; simpl; unfold O.eval_op; simpl.
    case (m1 bad2); simpl.
      intro H; rewrite (eqb_prop _ _ H), andb_false_r; trivial.  
      rewrite andb_false_r; trivial.
    split; [ trivial | unfold EP1; simpl; unfold O.eval_op; simpl; mem_upd_simpl ].
 Qed.


 Theorem Switching: forall k m,
  Uabs_diff (Pr Ef G0 m (EP k (b && (Elength L <=! q)))) (Pr Ep G0 m (EP k (b && (Elength L <=! q)))) <=
  ((q_poly k - 1) * q_poly k)/2^(1 + k).
 Proof.
  intros.
  rewrite Pr_f_f', Pr_p_p', <- Pr_Epbad_Ep'.
  apply Pr_Ef'_Epbad.
 Qed.

End ADVERSARY.




   




