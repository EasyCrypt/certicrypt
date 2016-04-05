(** * BuildTac.v : Tactics for program transformation *)

Set Implicit Arguments.

Require Export Triples.
Require Export SD_Others.
Require Export SD_Hoare. 
Require Export PPT.

Module Type BUILD_ENTRIES.

  Declare Module SemO : SEM_OPT.

  Declare Module BP : SEM_THEORY SemO.Sem.

  Declare Module Uppt : UPPT SemO.Sem BP.

End BUILD_ENTRIES.


Module Make (Entries:BUILD_ENTRIES).

 Export Entries.

 Module PPTSem := Make_PPT SemO.Sem BP Uppt.
 Export PPTSem.

 Module OPT2 := SD_Hoare.Make SemO.
 Export OPT2.


(* 
 Module EQRD := Triples.Make SemO.
 Export EQRD.

 Module StDist_Hoare := SD_Hoare.Make SemO.
 Export StDist_Hoare.


 Module StDist_Adv := SD_Others.Make_Adv SemO.
 Export StDist_Adv.
*)

 (* TODO: move this somewhere else *)
 Definition PPT_add_adv_infob : forall E1 E t (A:Proc.proc t) PrOrcl PrPriv
  (EqAD:Eq_adv_decl PrOrcl PrPriv E1 E)
  (A_PPT:forall E,
   Eq_adv_decl PrOrcl PrPriv E1 E ->
   (forall O, PrSet.mem O PrOrcl -> PPT_proc E (BProc.p_name O)) ->
   PPT_proc E A), 
  PPT_info E ->
  PPT_info E.
 
  intros E1 E t A PrOrc PrPriv Heq HA pi.
  case_eq (PrSet.forallb (fun f => res_poly E tsize_limit (BProc.p_name f)) PrOrc);
  [intro | intro; exact pi].
  case_eq (PrSet.forallb (fun f => cmd_poly pi (proc_body E (BProc.p_name f))) PrOrc);
  [intro | intro; exact pi].
  case_eq (PrSet.forallb (fun f => expr_poly (proc_res E (BProc.p_name f))) PrOrc);
  [intro | intro; exact pi].
  refine (mkPPT_info (fun _ f => if Proc.eqb f A then true else pi _ f) _).
  intros t1 f.
  generalize (Proc.eqb_spec_dep f A).
  case (Proc.eqb f A); intros H2 H3.
  inversion H2; subst.
  rewrite (T.inj_pair2 H7).
  apply (HA E Heq).
  intros; repeat split.
  refine (res_poly_spec _); trivial.  
  refine (PrSet.forallb_correct _ _ PrOrc H _ H4).
  intros x y; unfold PrSet.E.eq; intro Hxy; rewrite Hxy; trivial.
  refine (cmd_poly_spec pi _ _).
  refine (PrSet.forallb_correct _ _ PrOrc H0 _ H4).
  intros x y; unfold PrSet.E.eq; intro Hxy; rewrite Hxy; trivial.
  refine (expr_poly_spec _ _).
  refine (PrSet.forallb_correct _ _ PrOrc H1 _ H4).
  intros x y; unfold PrSet.E.eq; intro Hxy; rewrite Hxy; trivial.
  apply ppt_spec with pi; trivial.
 Defined.

 Definition tac_counter := 100%positive.

 Ltac compute_assertion Heq  id t :=
  let t' := eval vm_compute in t in
   pose (id := t');
   assert (Heq : t = id);
    [vm_cast_no_check (refl_equal id) | unfold id in Heq].

 Ltac get_option id :=
  match eval red in id with
  | Some ?t => fun f => f t
  | _ => fail 1 "get_option"
  end.

 Ltac get_pair res :=
  match eval red in res with
  | (?x1, ?x2) => fun f => f x1 x2 
  | _ => fail 1 "get_pair"
  end.

 Ltac get_triple res :=
  match eval red in res with
  | Triple ?h1 ?h2 ?t => fun f => f h1 h2 t 
  | _ => fail 1 "get_triple"
  end.

 Ltac get_quad res :=
  match eval red in res with
  | Quad ?k ?h1 ?h2 ?t => fun f => f k h1 h2 t 
  | _ => fail 1 "get_quad"
  end.

 Ltac check_info E1 E2 pi :=
  match type of pi with
  | eq_inv_info _ ?E1' ?E2' =>
    let x := constr:(refl_equal E1: E1 = E1') in
    let y := constr:(refl_equal E2: E2 = E2') in idtac
  | _ => fail 1 "check_info"
  end.

 Ltac get_inv pii := 
  match type of pii with 
  | eq_inv_info ?inv _ _ => constr:(inv)
  | _ => fail 1 "get_inv"
  end.

 Tactic Notation "decMR_tac" constr(pii) := 
  auto 20 using pii.(pii_inv_dec).
   
 Ltac fold_eqobs_tac :=
  match goal with
  | |- equiv _ ?E1 ?c1 ?E2 ?c2 (req_mem_rel _ trueR) =>
    rewrite req_mem_rel_trueR;
    fold_eqobs_tac
 | |- equiv (req_mem_rel _ trueR) ?E1 ?c1 ?E2 ?c2 _ =>
    rewrite req_mem_rel_trueR;
    fold_eqobs_tac
  | |- equiv (kreq_mem ?I ) ?E1 ?c1 ?E2 ?c2 (kreq_mem ?O) =>
    change (EqObs I E1 c1 E2 c2 O)
  | |- equiv (req_mem_rel ?I ?inv) ?E1 ?c1 ?E2 ?c2 (req_mem_rel ?O ?inv) =>
    change (EqObsInv inv I E1 c1 E2 c2 O)
  | |- equiv (req_mem_rel ?I ?P) ?E1 ?c1 ?E2 ?c2 (req_mem_rel ?O ?Q) =>
    change (EqObsRel I P E1 c1 E2 c2 O Q)
  | _ => idtac
  end.

 Ltac unfold_eqobs :=
  match goal with
  | |- EqObs _ _ _ _ _ _ => unfold EqObs
  | |- EqObsInv _ _ _ _ _ _ _ => unfold EqObsInv
  | |- EqObsRel _ _ _ _ _ _ _ _ => unfold EqObsRel
  | _ => idtac
  end.

 Ltac apply_equiv_tac1 :=
  match goal with
  | |- equiv ?P ?E1 ?c1 ?E2 ?c2 ?Q => fun f => f P E1 c1 E2 c2 Q
  | _ => fail 1 "apply_equiv_tac"
  end.

 Ltac apply_equiv_tac f:=
  unfold_eqobs; apply_equiv_tac1 f.

 Ltac apply_empty_info f :=
   let Main P E1 c1 E2 c2 Q := f (empty_info E1 E2) in
   apply_equiv_tac Main.

 Ltac depend_only_rel_tac pii Q :=
   match pii with  
   | ?W =>
     let Hdep := build_depend_only_rel_tac (pii_inv_dep pii) Q in
     match type of Hdep with 
     | depend_only_rel _ ?X1 ?X2 => fun f => f Hdep X1 X2
     end
   | _ => fail 1 "assert_depend_only_rel"
   end.

 Ltac assert_depend_only pii Q :=
   let Main Hdep X1 X2 :=
     let H := fresh "Hdep" in
     assert (H := Hdep)
   in depend_only_rel_tac pii Q Main.


 (** Swap *)

 Ltac swap_tac pii :=
  let Main P E1 c1 E2 c2 Q:=
   check_info E1 E2 pii;
   let Heq := fresh "Heq" in
   let res := fresh "res" in
    compute_assertion Heq res 
     (@swap tac_counter E1 E2 (refl1_info pii) (refl2_info pii) c1 c2);
    let end_tac h1 h2 t :=
     refine (@swap_correct tac_counter E1 E2 (refl1_info pii) (refl2_info pii)
      c1 c2 h1 h2 t Heq P Q _);
     clear Heq res;
     fold_eqobs_tac in
     get_triple res end_tac
  in apply_equiv_tac Main.

 Tactic Notation "swap" constr(pii) := swap_tac pii.

 Tactic Notation "swap" := apply_empty_info swap_tac.


 (** Dead Code *)

 Ltac deadcode_tac pii :=
  let Main P E1 c1 E2 c2 Q :=
   check_info E1 E2 pii;
   let Finish Qdep X1 X2 :=
     let Heq := fresh "Heq" in
     let res := fresh "res" in
     compute_assertion Heq res 
        (@dead_code_para tac_counter E1 E2 (refl1_info pii) (refl2_info pii) c1 c2 X1 X2);
     match eval red in res with
     | Some (?c1', ?c2') =>
         refine (@dead_code_para_equiv tac_counter E1 E2 (refl1_info pii) (refl2_info pii) 
             c1 c1' c2 c2' P Q X1 X2 _ Qdep Heq _);
         clear Heq res; [decMR_tac pii | fold_eqobs_tac]
     | _ => fail 1 "dead_code_tac"
     end
   in depend_only_rel_tac pii Q Finish
  in apply_equiv_tac Main.

 Tactic Notation "deadcode" constr(pii) := deadcode_tac pii.

 Tactic Notation "deadcode" := apply_empty_info deadcode_tac.


 (** Expression propagation *)  

 Ltac ep_tac pii :=
  let Main P E1 c1 E2 c2 Q :=
    check_info E1 E2 pii;
    let Heq1 := fresh "Heq" in
    let res1 := fresh "res" in
    let Heq2 := fresh "Heq" in
    let res2 := fresh "res" in
    compute_assertion Heq1 res1 
     (@Ep.optimize tac_counter E1 (refl1_info pii) c1);
    compute_assertion Heq2 res2 
     (@Ep.optimize tac_counter E2 (refl2_info pii) c2);
    refine (@Ep.optimize_para tac_counter P E1 (refl1_info pii) c1 res1 
             E2 (refl2_info pii) c2 res2 Q Heq1 Heq2 _);
    unfold res1, res2;
    clear Heq1 Heq2 res1 res2;
    fold_eqobs_tac
  in apply_equiv_tac Main.
 
 Tactic Notation "ep" constr(pii) := ep_tac pii.

 Tactic Notation "ep" := apply_empty_info ep_tac.


 (** Expression propagation with precondition *)

 Ltac ep_eq_l_tac pii e1 e2 :=
    let Main P E1 c1 E2 c2 Q :=
      check_info E1 E2 pii;
      let res := fresh "res" in    
      let Heq := fresh "Heq" in
      compute_assertion Heq res (ep_eq tac_counter (refl1_info pii) e1 e2 c1);
      refine (@ep_correct_l tac_counter E1 E2 (refl1_info pii) _ e1 e2 P c1 c2 Q res _ Heq _);
      unfold res; clear Heq res; fold_eqobs_tac
    in apply_equiv_tac Main.

  Ltac ep_eq_r_tac pii e1 e2 :=
    let Main P E1 c1 E2 c2 Q :=
      check_info E1 E2 pii;
      let res := fresh "res" in    
      let Heq := fresh "Heq" in
      compute_assertion Heq res (ep_eq tac_counter (refl2_info pii) e1 e2 c2);
      refine (@ep_correct_r tac_counter E1 E2 (refl2_info pii) _ e1 e2 P c1 c2 Q res _ Heq _);
      unfold res; clear Heq res; fold_eqobs_tac
    in apply_equiv_tac Main.

  Ltac ep_eq_tac pii e1 e2 :=
    let Main P E1 c1 E2 c2 Q :=
     check_info E1 E2 pii;
      let res1 := fresh "res" in    
      let Heq1 := fresh "Heq" in
      let res2 := fresh "res" in    
      let Heq2 := fresh "Heq" in
      compute_assertion Heq1 res1 (ep_eq tac_counter (refl1_info pii) e1 e2 c1);
      compute_assertion Heq2 res2 (ep_eq tac_counter (refl2_info pii) e1 e2 c2);
      refine (@ep_correct_para tac_counter _ E1 E2 pii _ e1 e2 P c1 c2 Q res1 res2 _ Heq1 Heq2 _);
      unfold res1, res2; clear Heq1 Heq2 res1 res2; fold_eqobs_tac
    in apply_equiv_tac Main.

 Tactic Notation "ep_eq_l" constr(pii) constr(e1) constr(e2) :=
    ep_eq_l_tac pii e1 e2.

 Tactic Notation "ep_eq_r" constr(pii) constr(e1) constr(e2) :=
    ep_eq_r_tac pii e1 e2.

 Tactic Notation "ep_eq" constr(pii) constr(e1) constr(e2) :=
    ep_eq_tac pii e1 e2.

 Tactic Notation "ep_eq_l" constr(e1) constr(e2) :=
   let Main pii := ep_eq_l_tac pii e1 e2 in
   apply_empty_info Main.

 Tactic Notation "ep_eq_r" constr(e1) constr(e2) :=
   let Main pii := ep_eq_r_tac pii e1 e2 in
   apply_empty_info Main.

 Tactic Notation "ep_eq" constr(e1) constr(e2) :=
   let Main pii := ep_eq_tac pii e1 e2 in
   apply_empty_info Main.


 (** Case analysis on a boolean expression *)

 Ltac cp_test_l_tac pii e :=
  let Main P E1 c1 E2 c2 Q :=
   check_info E1 E2 pii;
   let res := fresh "res" in
   let Heq := fresh "Heq" in
   compute_assertion Heq res (cp_test tac_counter (refl1_info pii) e c1);
   let concl c1t c1f :=
     refine (@cp_test_correct_l tac_counter E1 E2 (refl1_info pii) 
               e P c1 c2 Q c1t c1f Heq _ _);
     clear Heq res;
     fold_eqobs_tac
   in get_pair res concl
  in apply_equiv_tac Main.

 Ltac cp_test_r_tac pii e :=
  let Main P E1 c1 E2 c2 Q :=
   check_info E1 E2 pii;
   let res := fresh "res" in
   let Heq := fresh "Heq" in
   compute_assertion Heq res (cp_test tac_counter (refl2_info pii) e c2);
   let concl c2t c2f :=
    refine (@cp_test_correct_r tac_counter E1 E2 (refl2_info pii) 
              e P c1 c2 Q c2t c2f Heq _ _);
    clear Heq res;
    fold_eqobs_tac
   in get_pair res concl
  in apply_equiv_tac Main.

 Ltac eq_expr_tac P e :=
  let k := fresh "k" in
  let m1 := fresh "m1" in
  let m2 := fresh "m2" in
  let H := fresh "H" in
  intros k m1 m2 H;
  let rec aux P H (* : P k m1 m2*) :=
   match P with
   | Meq => rewrite (H : m1 = m2); trivial
   | kreq_mem ?X => 
     refine (@depend_only_fv_expr_subset _ e X _ k m1 m2 H);
     vm_compute; reflexivity
   | req_mem ?X => 
     refine (@depend_only_fv_expr_subset _ e X _ k m1 m2 H);
     vm_compute; reflexivity
   | req_mem_rel ?X ?Q => aux (kreq_mem X) (@proj1_MR (kreq_mem X) Q k m1 m2 H)
   | req_mem_rel ?X ?Q => aux Q (@proj2_MR (kreq_mem X) Q k m1 m2 H)
   | ?P1 /-\ ?P2 => aux P1 (@proj1_MR P1 P2 k m1 m2 H)
   | ?P1 /-\ ?P2 => aux P2 (@proj2_MR P1 P2 k m1 m2 H)
   end in
  aux P H.

 Ltac cp_test_tac_gen pii e :=
  let Main P E1 c1 E2 c2 Q :=
   check_info E1 E2 pii;
   let res1 := fresh "res" in
   let res2 := fresh "res" in
   let Heq1 := fresh "Heq" in
   let Heq2 := fresh "Heq" in
    compute_assertion Heq1 res1 (cp_test tac_counter (refl1_info pii) e c1);
    compute_assertion Heq2 res2 (cp_test tac_counter (refl2_info pii) e c2);
    let concl c1t c1f c2t c2f :=
     refine (@cp_test_correct tac_counter _ E1 E2 pii P e c1 c2 Q 
               c1t c2t c1f c2f Heq1 Heq2 _ _ _);
     clear Heq1 Heq2 res1 res2;
     [ try eq_expr_tac P e | fold_eqobs_tac | fold_eqobs_tac ]
   in get_pair res2 ltac:(get_pair res1 concl)
  in apply_equiv_tac Main.

 Tactic Notation "cp_test_l" constr(pii) constr(e) :=
   cp_test_l_tac pii e.

 Tactic Notation "cp_test_r" constr(pii) constr(e) :=
   cp_test_r_tac pii e.

 Tactic Notation "cp_test" constr(pii) constr(e) :=
   cp_test_tac_gen pii e.

 Tactic Notation "cp_test_l" constr(e) :=
   let Main pii := cp_test_l_tac pii e in
   apply_empty_info Main.

 Tactic Notation "cp_test_r" constr(e) :=
   let Main pii := cp_test_r_tac pii e in
   apply_empty_info Main.

 Tactic Notation "cp_test" constr(e) :=
   let Main pii := cp_test_tac_gen pii e in
   apply_empty_info Main.


 (** Inlining *)

 Ltac inline_l_tac f pii :=
   let Main P E1 c1 E2 c2 Q :=
     check_info E1 E2 pii;
     let Finish Qdep X1 X2 :=
       let Heq1 := fresh "Heq" in
       let c1' := fresh "c1'" in
       compute_assertion Heq1 c1' 
         (@inline tac_counter E1 (refl1_info pii) _ f c1 X1);
       refine (@inline_l_equiv tac_counter _ f P E1 
             (refl1_info pii) c1 c1' E2 (refl2_info pii) c2 Q X1 X2
             Heq1 _ Qdep _);
       [ auto | ]; 
       unfold c1';
       clear c1' Heq1;
       fold_eqobs_tac
     in depend_only_rel_tac pii Q Finish
    in apply_equiv_tac Main.
 
 Ltac inline_r_tac f pii :=
   let Main P E1 c1 E2 c2 Q :=
     check_info E1 E2 pii;
     let Finish Qdep X1 X2 :=
       let Heq2 := fresh "Heq" in
       let c2' := fresh "c2'" in
       compute_assertion Heq2 c2' 
         (@inline tac_counter E2 (refl2_info pii) _ f c2 X2);
       refine (@inline_r_equiv tac_counter _ f P E1 
             (refl1_info pii) c1 E2 (refl2_info pii) c2 c2' Q X1 X2
             Heq2 _ Qdep _);
       [ auto | ]; 
       unfold c2'; clear c2' Heq2;
       fold_eqobs_tac
     in depend_only_rel_tac pii Q Finish
    in apply_equiv_tac Main.

 Ltac inline_tac f pii :=
   let Main P E1 c1 E2 c2 Q :=
     check_info E1 E2 pii;
     let Finish Qdep X1 X2 :=
       let Heq1 := fresh "Heq" in
       let Heq2 := fresh "Heq" in
       let c1' := fresh "c1'" in
       let c2' := fresh "c2'" in
       compute_assertion Heq1 c1' 
         (@inline tac_counter E1 (refl1_info pii) _ f c1 X1);
       compute_assertion Heq2 c2' 
         (@inline tac_counter E2 (refl2_info pii) _ f c2 X2);
       refine (@inline_para_equiv tac_counter _ f P E1 
             (refl1_info pii) c1 c1' E2 (refl2_info pii) c2 c2' Q X1 X2
             Heq1 Heq2 _ Qdep _);
       [ auto | ]; 
       unfold c1', c2';
       clear c1' c2' Heq1 Heq2;
       fold_eqobs_tac
     in depend_only_rel_tac pii Q Finish
    in apply_equiv_tac Main.

 Ltac strong_inline_l_tac f pii :=
  inline_l_tac f pii;
  ep_tac pii;
  deadcode_tac pii.

 Ltac strong_inline_r_tac f pii :=
  inline_r_tac f pii;
  ep_tac pii;
  deadcode_tac pii.

 Ltac strong_inline_tac f pii :=
  inline_tac f pii;
  ep_tac pii;
  deadcode_tac pii.

 Tactic Notation "inline_l" constr(pii) constr(f) :=
  let f := constr:(f) in inline_l_tac f pii.

 Tactic Notation "sinline_l" constr(pii) constr(f) :=
  let f := constr:(f) in strong_inline_l_tac f pii.

 Tactic Notation "inline_r" constr(pii) constr(f) :=
  let f := constr:(f) in inline_r_tac f pii.

 Tactic Notation "sinline_r" constr(pii) constr(f) :=
  let f := constr:(f) in strong_inline_r_tac f pii.

 Tactic Notation "inline" constr(pii) constr(f) :=
  let f := constr:(f) in inline_tac f pii.

 Tactic Notation "sinline" constr(pii) constr(f) :=
  let f := constr:(f) in strong_inline_tac f pii.

 (** Variable allocation *)

 Ltac alloc_l_tac pii r d :=
  let Main P E1 c1 E2 c2 Q :=  
   check_info E1 E2 pii;   
   let res1 := fresh "res" in  
   let Heq1 := fresh "Heq" in
   match pii with  
   | ?W =>
     let Hdep := build_depend_only_rel_tac (pii_inv_dep pii) Q in
     match type of Hdep with 
     | depend_only_rel _ ?X1 ?X2 => 
       compute_assertion Heq1 res1 (alloc_c_out (refl1_info pii) r d c1 X1);
       refine (@alloc_c_out_equiv_l _ r d P E1 (refl1_info pii) c1 res1 E2 c2 X1 X2 Q
                  _ Hdep Heq1 _);
       unfold res1; clear Heq1 res1; [decMR_tac pii | fold_eqobs_tac]
     end
   | _ => 
       compute_assertion Heq1 res1 (alloc_c (refl1_info pii) r d c1);
       refine (@alloc_c_equiv_l _ r d P E1 pi1 c1 res1 E2 c2 Q Heq1 _);
       unfold res1; clear Heq1 res1; fold_eqobs_tac
   end
  in apply_equiv_tac Main.

 Ltac alloc_r_tac pii r d :=
  let Main P E1 c1 E2 c2 Q :=  
   check_info E1 E2 pii;   
   let res2 := fresh "res" in  
   let Heq2 := fresh "Heq" in
   match pii with  
   | ?W =>
     let Hdep := build_depend_only_rel_tac (pii_inv_dep pii) Q in
     match type of Hdep with 
     | depend_only_rel _ ?X1 ?X2 => 
       compute_assertion Heq2 res2 (alloc_c_out (refl2_info pii) r d c2 X2);
       refine (@alloc_c_out_equiv_r _ r d P E1 c1 E2 (refl2_info pii) c2 res2 X1 X2 Q
                  _ Hdep Heq2 _);
       unfold res2; clear Heq2 res2; [decMR_tac pii | fold_eqobs_tac]
     end
   | _ => 
       compute_assertion Heq2 res2 (alloc_c (refl2_info pii) r d c2);
       refine (@alloc_c_equiv_r _ r d P E1 pi1 c1 E2 c2 res2 Q Heq2 _);
       unfold res2; clear Heq2 res2; fold_eqobs_tac
   end
  in apply_equiv_tac Main.

 Ltac alloc_tac pii r d :=
  let Main P E1 c1 E2 c2 Q :=  
   check_info E1 E2 pii;   
   let res1 := fresh "res" in
   let res2 := fresh "res" in
   let Heq1 := fresh "Heq" in
   let Heq2 := fresh "Heq" in
   match pii with  
   | ?W =>
     let Hdep := build_depend_only_rel_tac (pii_inv_dep pii) Q in
     match type of Hdep with 
     | depend_only_rel _ ?X1 ?X2 => 
       compute_assertion Heq1 res1 (alloc_c_out (refl1_info pii) r d c1 X1);
       compute_assertion Heq2 res2 (alloc_c_out (refl2_info pii) r d c2 X2);
       let Hdec := fresh "Hdec" in
       assert (Hdec : decMR P);
       [ decMR_tac pii; clear Heq1 Heq2 res1 res2
       | refine (@alloc_c_out_equiv_l _ r d P E1 (refl1_info pii) c1 res1 E2 c2 X1 X2 Q
                  Hdec Hdep Heq1 _);
         refine (@alloc_c_out_equiv_r _ r d P E1 res1 E2 (refl2_info pii) c2 res2 X1 X2 Q
                  Hdec Hdep Heq2 _);
         unfold res1, res2; clear Heq1 Heq2 res1 res2; fold_eqobs_tac
       ]
      end
   | _ => 
     compute_assertion Heq1 res1 (alloc_c (refl1_info pii) r d c1);
     compute_assertion Heq2 res2 (alloc_c (refl2_info pii) r d c2);
     refine (@alloc_c_equiv_l _ r d P E1 pi1 c1 res1 E2 c2 Q Heq1 _);
     refine (@alloc_c_equiv_r _ r d P E1 pi1 c1 E2 c2 res2 Q Heq2 _);
     unfold res1, res2; clear Heq1 Heq2 res1 res2; fold_eqobs_tac
   end 
  in apply_equiv_tac Main.

 Tactic Notation "alloc_l" constr(pii)  constr(r) constr(d) :=
  let r1 := constr:(r) in
  let d1 := constr:(d) in
  alloc_l_tac pii r1 d1.

 Tactic Notation "alloc_l" constr(r) constr(d) :=
  let r1 := constr:(r) in
  let d1 := constr:(d) in
  let Main pii := alloc_l_tac pii r1 d1 in
  apply_empty_info Main.

 Tactic Notation "alloc_r" constr(pii)  constr(r) constr(d) :=
  let r1 := constr:(r) in
  let d1 := constr:(d) in
  alloc_r_tac pii r1 d1.

 Tactic Notation "alloc_r" constr(r) constr(d) :=
  let r1 := constr:(r) in
  let d1 := constr:(d) in
  let Main pii := alloc_r_tac pii r1 d1 in
  apply_empty_info Main.

 Tactic Notation "alloc" constr(pii)  constr(r) constr(d) :=
  let r1 := constr:(r) in
  let d1 := constr:(d) in
  alloc_tac pii r1 d1.

 Tactic Notation "alloc" constr(r) constr(d) :=
  let r1 := constr:(r) in
  let d1 := constr:(d) in
  let Main pii := alloc_tac pii r1 d1 in
  apply_empty_info Main.


 (** Dealing with context *)

 (* Move this lemma *)
 Lemma implMR_trueR : forall P, implMR P trueR.
 Proof. 
  red; red; trivial.
 Qed.

 Lemma equiv_weaken_kreq_mem : forall P E1 c1 E2 c2 O Q,
  equiv P E1 c1 E2 c2 (req_mem_rel O Q) ->
  equiv P E1 c1 E2 c2 (kreq_mem O).
 Proof.
  intros; unfold req_mem_rel.
  rewrite <- (@proj1_MR (kreq_mem O) Q); trivial.
 Qed.
 
 Lemma equiv_strengthen_kreq_mem : forall I E1 c1 E2 c2 Q,
  equiv (req_mem_rel I trueR) E1 c1 E2 c2 Q ->
  equiv (kreq_mem I) E1 c1 E2 c2 Q.
 Proof.
  intros I E1 c1 E2 c2 Q; simplMR; trivial.
 Qed.
 
 Lemma equiv_weaken_req_mem_rel_implMR : forall P E1 c1 E2 c2 O Q Q',
  implMR Q Q' ->
  equiv P E1 c1 E2 c2 (req_mem_rel O Q) ->
  equiv P E1 c1 E2 c2 (req_mem_rel O Q').
 Proof.
  intros.
  rewrite <- H; trivial.
 Qed.
 
 Lemma req_mem_rel_subset : forall X1 X2 P, X2 [<=] X1 ->
  implMR (req_mem_rel X1 P) (req_mem_rel X2 P).
 Proof.
  intros; rewrite <- H; trivial.
 Qed.

 Lemma implMR_req_mem_rel_and : forall P X Q,
  implMR P (kreq_mem X) ->
  implMR P Q ->
  implMR P (req_mem_rel X Q).
 Proof.
  unfold implMR, req_mem_rel, andR; split; auto.
 Qed.

 Lemma implMR_kreq_mem_and_and : forall P X Q,
  implMR P (kreq_mem X) ->
  implMR P Q ->
  implMR P (kreq_mem X /-\ Q).
 Proof.
  unfold implMR, req_mem_rel, andR; split; auto.
 Qed.

 Lemma kreq_mem_and_subset : forall X1 X2 P, 
  X2 [<=] X1 ->
  implMR (kreq_mem X1 /-\ P) (kreq_mem X2 /-\ P).
 Proof.
  intros; rewrite <- H; trivial.
 Qed.

 Lemma kreq_mem_and_subset2 : forall X1 X2 P1 P2, 
  X2 [<=] X1 -> 
  implMR (kreq_mem X1 /-\ P1) P2 ->
  implMR (kreq_mem X1 /-\ P1) (kreq_mem X2 /-\ P2).
 Proof.
  intros.
  apply implMR_kreq_mem_and_and; trivial.
  rewrite proj1_MR, H; trivial.
 Qed.

 Lemma implMR_Meq_kreq_mem : forall X, implMR Meq (kreq_mem X).
 Proof.
  red; unfold Meq; intros.
  rewrite H; trivial.
 Qed.

 Lemma implMR_Meq_kreq_mem_and1 : forall X P, 
  implMR (Meq /-\ P) (kreq_mem X /-\ P).
 Proof.
  intros; rewrite <- implMR_Meq_kreq_mem; trivial.
 Qed.

 Lemma implMR_Meq_kreq_mem_and2 : forall X P1 P2, 
  implMR (Meq /-\ P1) P2 ->
  implMR (Meq /-\ P1) (kreq_mem X /-\ P2).
 Proof.
  intros; apply implMR_kreq_mem_and_and; trivial.
  rewrite <- implMR_Meq_kreq_mem; apply proj1_MR.
 Qed.

 Lemma equiv_strengthen_implMR : forall P P' E1 c1 E2 c2 Q,
  implMR P' P ->
  equiv P E1 c1 E2 c2 Q ->
  equiv P' E1 c1 E2 c2 Q.
 Proof.
  intros; apply equiv_strengthen with P; auto.
 Qed.

 Ltac set_post_req_mem_rel inv Q :=
  match Q with
  | kreq_mem ?X =>
    fun f => refine (@equiv_weaken_kreq_mem _ _ _ _ _ X inv _); f X
  | req_mem_rel ?X inv => fun f => f X 
  | req_mem_rel ?X trueR =>
    fun f => 
      refine (@equiv_weaken_req_mem_rel_implMR _ _ _ _ _ X inv trueR (implMR_trueR inv) _);
      f X
  | req_mem_rel ?X ?inv' =>
    fun f =>
      let Himp := fresh "Himp" in
      assert (Himp : implMR inv inv');
      [ idtac |
      | refine (@equiv_weaken_req_mem_rel_implMR _ _ _ _ _ X inv trueR Himp _);
        f X] 
  | _ => fail 1 "post_req_mem_rel"
  end.

 Ltac set_pre_req_mem_rel inv P :=
  match P with
  | kreq_mem ?X =>
    match inv with
    | trueR => 
      fun f => refine (@equiv_strengthen_kreq_mem X _ _ _ _ _ _); f X
    end
  | req_mem_rel ?X inv => fun f => f X
  end.
 
 Lemma implMR_kreq_mem_subset : forall X1 X2, X2 [<=] X1 ->
   implMR (kreq_mem X1) (kreq_mem X2).
 Proof. 
  intros X1 X2 H; rewrite H; trivial.
 Qed.

 Ltac implMR_req_mem_rel_tac :=
   unfold req_mem_rel;
   let rec aux :=
     match goal with
     | |- implMR ?P ?P => trivial

     | |- implMR ((?P1 /-\ ?P2) /-\ ?P3) _ =>
       rewrite (@andR_assoc P1 P2 P3); aux
     | |- implMR _ ((?P1 /-\ ?P2) /-\ ?P3) =>
       rewrite (@andR_assoc P1 P2 P3); aux

     (* kreq_mem *)

     | |- implMR (kreq_mem ?X1) (kreq_mem ?X2) =>
       refine (@implMR_kreq_mem_subset X1 X2 _);
       vm_compute; reflexivity

     | |- implMR (kreq_mem ?X1 /-\ ?P) (kreq_mem ?X2) =>
       rewrite (@proj1_MR (kreq_mem X1) P);
       refine (@implMR_kreq_mem_subset X1 X2 _);
       vm_compute; reflexivity

     | |- implMR Meq (kreq_mem ?X2) =>
       apply implMR_Meq_kreq_mem

     | |- implMR (Meq /-\ ?P) (kreq_mem ?X2) =>
       rewrite (@proj1_MR Meq P);
       apply implMR_Meq_kreq_mem

     (* kreq_mem /-\ P *)

     | |- implMR (kreq_mem ?X1 /-\ ?P) (kreq_mem ?X2 /-\ ?P) =>
       apply kreq_mem_and_subset;
       vm_compute; reflexivity

     | |- implMR _ (kreq_mem ?X /-\ trueR) =>
       rewrite (@andR_trueR_r (kreq_mem X)); aux

     | |- implMR (kreq_mem ?X1 /-\ ?P1) (kreq_mem ?X2 /-\ ?P1) =>
       apply kreq_mem_and_subset2;
       [ vm_compute; reflexivity | ]


     | |- implMR (Meq /-\ ?P) (kreq_mem ?X /-\ ?P) =>
       apply (@implMR_Meq_kreq_mem_and1 X P)

     | |- implMR (Meq /-\ ?P1) (kreq_mem ?X /-\ ?P2) =>
       apply (@implMR_Meq_kreq_mem_and1 X P1 P2)

     | |- implMR _ (kreq_mem ?X2 /-\ ?P2) =>
       apply implMR_kreq_mem_and_and;
       [ aux | idtac ]
     end
    in aux.

 Ltac check_eq t1 t2 :=
  match t1 with 
  | _ => let x := constr:(refl_equal t1 : t1 = t2) in idtac
  | _ => fail 1 "check_eq"
  end.

 Ltac eqobs_in_tac pii :=
  let Main P E1 c1 E2 c2 Q :=
    check_info E1 E2 pii; 
    check_eq c1 c2;
    let inv := get_inv pii in
    let to_post O :=
      let res := fresh "res" in
      let Heq := fresh "Heq" in
      compute_assertion Heq res (eqobsinv_in tac_counter pii c1 O);
      let to_pre I :=
        let pr := constr:(@eqobsinv_in_correct tac_counter inv E1 E2 pii c1 O I Heq) in
        refine (@equiv_strengthen_implMR (req_mem_rel I inv) 
                   P E1 c1 E2 c1 (req_mem_rel O inv) _ pr);
        clear Heq res;
        implMR_req_mem_rel_tac in
      get_option res to_pre in
    set_post_req_mem_rel inv Q to_post 
  in apply_equiv_tac Main.
   
 Ltac eqobs_head_n_tac pii k :=
  let Main P E1 c1 E2 c2 Q :=
   check_info E1 E2 pii;
   let inv := get_inv pii in
   let to_pre I :=
     let Heq1 := fresh "Heq" in
     let res1 := fresh "res" in
     compute_assertion Heq1 res1 (eqobsinv_head_n pii k I c1 c2);
     let cont IO t1 t2 :=
      refine (@eqobsinv_head_n_correct 
       inv E1 E2 pii k I Q c1 c2 t1 t2 IO Heq1 _);
      clear Heq1 res1;
      fold_eqobs_tac
     in get_triple res1 cont
   in set_pre_req_mem_rel inv P to_pre
  in apply_equiv_tac Main. 

 Ltac eqobs_head_tac pii :=
  let Main P E1 c1 E2 c2 Q :=
   check_info E1 E2 pii;   
   let inv := get_inv pii in
   let to_pre I := 
    let Heq1 := fresh "Heq" in
    let res1 := fresh "res" in
     compute_assertion Heq1 res1 (eqobsinv_head pii I c1 c2);
     let cont IO t1 t2 :=
      refine (@eqobsinv_head_correct 
       inv E1 E2 pii I Q c1 c2 t1 t2 IO Heq1 _);
      clear Heq1 res1;
      fold_eqobs_tac 
     in get_triple res1 cont 
   in set_pre_req_mem_rel inv P to_pre
  in apply_equiv_tac Main. 

 Ltac eqobs_tail_n_tac pii k :=
  let Main P E1 c1 E2 c2 Q :=
   check_info E1 E2 pii;
   let inv := get_inv pii in
   let to_post O :=
     let Heq1 := fresh "Heq" in
     let res1 := fresh "res" in
     compute_assertion Heq1 res1 (eqobsinv_tail_n tac_counter pii k c1 c2 O);
     let cont h1 h2 IO :=
      refine (@eqobsinv_tail_n_correct 
       tac_counter inv E1 E2 pii k P c1 c2 O h1 h2 IO Heq1 _);
      clear Heq1 res1;
      fold_eqobs_tac 
     in get_triple res1 cont 
   in set_post_req_mem_rel inv Q to_post 
  in apply_equiv_tac Main.

 Ltac eqobs_tail_tac pii :=
  let Main P E1 c1 E2 c2 Q :=
   check_info E1 E2 pii;
   let inv := get_inv pii in
   let to_post O :=
    let Heq1 := fresh "Heq" in
    let res1 := fresh "res" in
    compute_assertion Heq1 res1 (eqobsinv_tail tac_counter pii c1 c2 O);
    let cont h1 h2 IO :=
      refine (@eqobsinv_tail_correct 
       tac_counter inv E1 E2 pii P c1 c2 O h1 h2 IO Heq1 _);
      clear Heq1 res1;
      fold_eqobs_tac
    in get_triple res1 cont 
   in set_post_req_mem_rel inv Q to_post 
  in apply_equiv_tac Main.

 Ltac eqobs_context_tac pii :=
  let Main P E1 c1 E2 c2 Q :=
   check_info E1 E2 pii;  
   let inv := get_inv pii in
   let to_post O :=
     let to_pre I :=
       let Heq1 := fresh "Heq" in
       let res1 := fresh "res" in
       compute_assertion Heq1 res1 (eqobsinv_context tac_counter pii I c1 c2 O);
       let cont I' c1' c2' O' :=
          refine (@eqobsinv_context_correct tac_counter inv E1 E2 pii I c1 c2 O 
                  I' c1' c2' O' Heq1 _); 
          clear Heq1 res1;
          fold_eqobs_tac
       in get_quad res1 cont
     in set_pre_req_mem_rel inv P to_pre
   in set_post_req_mem_rel inv Q to_post 
  in apply_equiv_tac Main.


 Tactic Notation "eqobs_in" constr(pii) := eqobs_in_tac pii.
 Tactic Notation "eqobs_in" := apply_empty_info eqobs_in_tac.

 Tactic Notation "eqobs_hd_n" constr(pii) constr(k) := eqobs_head_n_tac pii k.
 Tactic Notation "eqobs_hd_n" constr(k) := 
   let Main pii := eqobs_head_n_tac pii k in 
   apply_empty_info Main.

 Tactic Notation "eqobs_hd" constr(pii) := eqobs_head_tac pii.
 Tactic Notation "eqobs_hd" := apply_empty_info eqobs_head_tac.

 Tactic Notation "eqobs_tl_n" constr(pii) constr(k) := eqobs_tail_n_tac pii k.
 Tactic Notation "eqobs_tl_n" constr(k) := 
   let Main pii := eqobs_tail_n_tac pii k in 
   apply_empty_info Main.

 Tactic Notation "eqobs_tl" constr(pii) := eqobs_tail_tac pii.
 Tactic Notation "eqobs_tl" := apply_empty_info eqobs_tail_tac.

 Tactic Notation "eqobs_ctxt" constr(pii) := eqobs_context_tac pii.
 Tactic Notation "eqobs_ctxt" := apply_empty_info eqobs_context_tac.

 
 (** Tactics for proving program invariants *) 
 
 Inductive ABS_prop : Type :=
   | ABS_closed : formula -> ABS_prop
   | ABS_base : mem_rel -> formula -> ABS_prop.

 Ltac ABS_op2 P op ab1 ab2 :=
  match ab1 with
  | ABS_closed ?f1 =>
    match ab2 with
    | ABS_closed ?f2 => constr:(ABS_closed (op f1 f2))
    | ABS_base ?P2 ?f2 =>constr:(ABS_base P2 (op f1 f2))
    end
  | ABS_base ?P1 ?f1 =>
    match ab2 with
    | ABS_closed ?f2 => constr:(ABS_base P1 (op f1 f2))
    | ABS_base ?P1 ?f2 => constr:(ABS_base P1 (op f1 f2))
    | _ => constr:(ABS_base P Fbase)
    end
  end.

 Ltac ABS_op1 op ab1 :=
  match ab1 with
  | ABS_closed ?f1 => constr:(ABS_closed (op f1))
  | ABS_base ?P1 ?f1 => constr:(ABS_base P1 (op f1))
  end.

 Ltac abs_prop P :=
  match P with
  | ?P1 /-\ ?P2 => 
    let F1 := abs_prop P1 in
    let F2 := abs_prop P2 in
    ABS_op2 P Fand F1 F2
  | ?P1 |-> ?P2 =>
    let F1 := abs_prop P1 in
    let F2 := abs_prop P2 in
    ABS_op2 P Fimp F1 F2
  | ~- ?P1 => 
    let F1 := abs_prop P1 in
    ABS_op1 Fnot F1
  | ?P1 \-/ ?P2 =>
    let F1 := abs_prop P1 in
    let F2 := abs_prop P2 in
    ABS_op2 P For F1 F2
  | EP1 ?e => constr:(ABS_closed (Fbool1 e))
  | EP2 ?e => constr:(ABS_closed (Fbool2 e))
  | eq_assoc_except ?v ?l => constr:(ABS_closed (Feq_assoc_except v l))
  | _ => constr:(ABS_base P Fbase)
  end.

 Ltac abs_prop2 P :=
  match abs_prop P with
  | ABS_closed ?F => constr:(trueR, F)
  | ABS_base ?P1 ?F => constr:(P1, F)
  end.

 Ltac nil_nil_tac :=
   unfold EqObsRel, EqObsInv;
   apply equiv_nil_impl;
   try implMR_req_mem_rel_tac.

 Ltac eqobsrel_tail_n n :=
  let Main P E1 c1 E2 c2 Q1 :=
    match Q1 with
    | req_mem_rel ?O ?Q =>
      match abs_prop2 Q with
      | (?Qb, ?F) =>
        let Heq  := fresh "Heq" in
        let res := fresh "res" in
        compute_assertion Heq res (eqobsrel_tail_n n c1 c2 O F);
        let cont c1' c2' O' Fres :=
          refine (@eqobsrel_tail_n_correct Qb n P E1 c1 E2 c2 O F  c1' c2' O' Fres Heq _);
          clear Heq res; fold_eqobs_tac
        in get_quad res cont
      end 
    | _ => fail 1 "eqobsrel_tail_n: unexpected output relation (expected req_mem_rel)"
    end 
  in 
  apply_equiv_tac Main;
  try nil_nil_tac.

 Ltac eqobsrel_tail :=
  let Main P E1 c1 E2 c2 Q1 :=
   let n1 := eval vm_compute in (length c1) in
   let n2 := eval vm_compute in (length c2) in
   match eval vm_compute in (Compare_dec.leb n1 n2) with
   | true => eqobsrel_tail_n n2
   | false => eqobsrel_tail_n n1
   | _ => fold_eqobs_tac
   end 
  in apply_equiv_tac Main.


 (** Union modify *)

 (* REMARK: decMR can be weakened, P has to be decidable only if m1 =={I} m2 *)
 Lemma equiv_union_Modify : forall E1 c1 E2 c2 I P X1 X2 O Q,
  Modify E1 X1 c1 /\ Modify E2 X2 c2 ->
  decMR P ->
  equiv (req_mem_rel I P) E1 c1 E2 c2 (req_mem_rel (Vset.diff O (Vset.diff I (Vset.union X1 X2))) Q) -> 
  equiv (req_mem_rel I P) E1 c1 E2 c2 (req_mem_rel O Q).
 Proof.
  intros; destruct H.  
  apply equiv_union_Modify_pre2 with 
   (P1:= fun _ _ => True) (P2:= fun _ _ => True)
   (X1:=X1) (X2:=X2) 
   (Q:=req_mem_rel (Vset.diff O (Vset.diff I (Vset.union X1 X2))) Q); auto.  
  unfold req_mem_rel, kreq_mem; intros k m1 m2 m1' m2' [W1 W2] [W3 W4]; split.
  intros t x Hx.
  destruct (VsetP.mem_dec x (Vset.diff I (Vset.union X1 X2))).
  rewrite VsetP.diff_spec, VsetP.union_spec in i; destruct i.
  rewrite <- H2; try tauto.
  rewrite <- H3; auto; try tauto.
  apply W3; auto with set.
  trivial. 
  apply Modify_Modify_pre; auto.
  apply Modify_Modify_pre; auto.
 Qed.

 Lemma equiv_union_Modify_Meq : forall E1 c1 E2 c2 P X1 X2,
  Modify E1 X1 c1 /\ Modify E2 X2 c2 ->
  implMR P Meq ->
  equiv P E1 c1 E2 c2 (kreq_mem (Vset.union X1 X2)) ->
  equiv P E1 c1 E2 c2 Meq.
 Proof.
  intros; destruct H.
  apply equiv_union_Modify_pre with
   (P1:=fun _ _ => True) (P2:=fun _ _ => True)
   (X1:=Vset.union X1 X2) (X2:=Vset.union X1 X2) 
   (Q:=kreq_mem (Vset.union X1 X2)); auto.
  intros.
  assert (W := H0 k m1 m2 H3).
  unfold Meq in *; subst.
  apply req_mem_eq; trivial.
  apply Modify_Modify_pre; apply Modify_weaken with (1:= H); auto with set.
  apply Modify_Modify_pre; apply Modify_weaken with (1:= H2); auto with set.
 Qed.
 
 Lemma equiv_union_Modify_Meq_and : forall E1 c1 E2 c2 P X1 X2 Q Y1 Y2,
  depend_only_rel Q Y1 Y2 ->
  Modify E1 X1 c1 /\ Modify E2 X2 c2 ->
  implMR P Meq ->
  equiv P E1 c1 E2 c2 (req_mem_rel (Vset.union (Vset.union X1 X2) (Vset.union Y1 Y2)) Q) ->
  equiv P E1 c1 E2 c2 (Meq /-\ Q).
 Proof.
  intros; set (X:= Vset.union (Vset.union X1 X2) (Vset.union Y1 Y2)).
  destruct H0.
  intros; apply equiv_union_Modify_pre with
   (P1 := fun _ _ => True) (P2 := fun _ _ => True)
   (X1 := X) (X2 := X) 
   (Q:= req_mem_rel X Q); auto.
  intros.
  assert (W := H1 k m1 m2 H4).
  destruct H5.
  unfold Meq, andR in *; subst; split.
  apply req_mem_eq; trivial.
  apply (H k m1' m2').
  apply req_mem_sym; apply req_mem_weaken with X;
  [ unfold X; auto with set | apply req_mem_update_mem_l].
  apply req_mem_sym; apply req_mem_weaken with X;
  [ unfold X; auto with set | apply req_mem_update_mem_l].
  trivial.
  apply Modify_Modify_pre; apply Modify_weaken with (1:= H0); unfold X; auto with set.
  apply Modify_Modify_pre; apply Modify_weaken with (1:= H3); unfold X; auto with set.
 Qed.

 Definition modify2 inv E1 E2 (pii: eq_inv_info inv E1 E2) c1 c2 :=
  match modify (refl1_info pii) Vset.empty c1,
        modify (refl2_info pii) Vset.empty c2 with
  | Some X1, Some X2 => Some (X1, X2)
  | _, _ => None
  end.

 Lemma modify2_correct : forall inv E1 E2 (pii: eq_inv_info inv E1 E2) c1 c2 X1 X2,
  modify2 pii c1 c2 = Some (X1, X2) ->
  Modify E1 X1 c1 /\ Modify E2 X2 c2.
 Proof.
  unfold modify2; intros.
  generalize (modify_correct (refl1_info pii) c1 Vset.empty).
  generalize (modify_correct (refl2_info pii) c2 Vset.empty).
  destruct (modify (refl1_info pii) Vset.empty c1); try discriminate.
  destruct (modify (refl2_info pii) Vset.empty c2); inversion H; auto.
 Qed.

 Ltac union_mod_tac pii :=
   let Main P E1 c1 E2 c2 Q :=
     check_info E1 E2 pii;
     let Heq := fresh "Heq"in
     let res := fresh "res" in
     compute_assertion Heq res (modify2 pii c1 c2);
     let cont XX :=
       match XX with
       | (?X1, ?X2) =>
         let Hmod := constr:(@modify2_correct _ E1 E2 pii c1 c2 X1 X2 Heq) in
         match Q with
         | Meq =>
           refine (@equiv_union_Modify_Meq E1 c1 E2 c2 P X1 X2 Hmod _ _);
           unfold res; clear Heq res;
           [ | fold_eqobs_tac]
         | Meq /-\ ?Q' =>
           let contDep Hdep Y1 Y2 :=
              refine (@equiv_union_Modify_Meq_and E1 c1 E2 c2 P X1 X2 Q' Y1 Y2
                          Hdep Hmod _ _);
              unfold res; clear Heq res;
              [ | fold_eqobs_tac]  in
            depend_only_rel_tac pii Q' contDep
          | req_mem_rel ?O ?QQ => 
            match P with 
            | req_mem_rel ?I ?PP => 
              refine (equiv_union_Modify O Hmod _ _);
               unfold res in |- *; clear Heq res; 
              [decMR_tac pii | simpl Vset.diff in |- *; fold_eqobs_tac]   
            end 
         | _ => 
          let to_post O :=
           let to_pre I :=
            refine (@equiv_union_Modify E1 c1 E2 c2 I _ X1 X2 O _ Hmod _ _);            
            unfold res; clear Heq res;
            [decMR_tac pii | simpl Vset.diff; fold_eqobs_tac]            
           in set_pre_req_mem_rel trueR P to_pre
          in set_post_req_mem_rel trueR Q to_post     
         | _ => fail 2 "union_mod: cannot recognize the postcondition"
         end 
       end in
     get_option res cont
   in apply_equiv_tac Main.

 Tactic Notation "union_mod" constr(pii) := union_mod_tac pii.

 Tactic Notation "union_mod" := apply_empty_info union_mod_tac.


 (*** Transitivity Tactic *)

 Ltac equiv_trans_tac pii E c :=
   match goal with
   | |- EqObs _ _ _ _ _ _ =>
     apply EqObs_trans with E c
   | _ => 
     unfold EqObsRel, EqObsInv;
     match goal with
     | |- equiv _ _ _ _ _ _ =>
       apply equiv_trans_trans with E c;
       [ auto
       | try (refl_support [pii])
       | try (transMR [pii])
       | idtac
       | idtac
       ]
     | _ => fail 2 "equiv_trans : can not reconize the goal"
     end
   | _ => fail 1 "equiv_trans : can not reconize the goal"
   end.

 Tactic Notation "equiv_trans" constr(pii) constr(E) constr(c) := 
    equiv_trans_tac pii E c.

 Tactic Notation "equiv_trans" constr(E) constr(c) := 
    let Main pii := equiv_trans_tac pii E c in
    apply_empty_info Main.

 Ltac mem_upd_simpl :=
 repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff; 
  [ | discriminate])); trivial.
  
End Make.
