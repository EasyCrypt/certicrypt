(** * EqThInv.v : Decision procedures for determining program equivalence and
   invariants *)

Set Implicit Arguments.

Require Export While_loop.
Require Export EqTh.


Module Make (Sem:SEM).

 Module EqT := EqTh.Make Sem.
 Export EqT.

 (* Information for two different environments *)

 Record dproc_eq_inv_info (E1 E2:env) (t:T.type) (f:Proc.proc t) : Type := {
  dpi_eq_refl1 : proc_eq_refl_info E1 f;
  dpi_eq_refl2 : proc_eq_refl_info E2 f;
  dpii_input : Vset.t;  (* global variables *)
  dpii_params : Vset.t; (* local variables  *)
  dpii_output : Vset.t (* global variables *)  
 }.

 Record sproc_eq_inv_info (inv : mem_rel) (E1 E2:env) (t:T.type) (f:Proc.proc t) 
   (data : dproc_eq_inv_info E1 E2 f) : Prop := {
  siinput_global : forall x, Vset.mem x data.(dpii_input) -> Var.is_global x;
  sparams_subset1 : data.(dpii_params) [<=] Vset_of_var_decl (proc_params E1 f);
  sparams_subset2 : data.(dpii_params) [<=] Vset_of_var_decl (proc_params E2 f);
  spii_output_global : forall x, Vset.mem x data.(dpii_output) -> Var.is_global x;
  spii_spec : 
   exists ls, 
    (forall x, Vset.mem x ls -> Var.is_local x) /\ 
    EqObsInv inv (Vset.union data.(dpii_input) data.(dpii_params)) 
     E1 (proc_body E1 f) E2 (proc_body E2 f) (Vset.union ls data.(dpii_output)) /\ 
     EqObs_e 
     (Vset.union (Vset.union ls data.(dpii_output))
      (Vset.diff data.(dpii_input) 
        (Vset.union (pi_mod data.(dpi_eq_refl1)) (pi_mod data.(dpi_eq_refl2)))))
     (proc_res E1 f) (proc_res E2 f)
 }.

 Record proc_eq_inv_info (inv : mem_rel) (E1 E2:env) (t:T.type) (f:Proc.proc t) : Type := {
  dpii : dproc_eq_inv_info E1 E2 f;
  spii : sproc_eq_inv_info inv dpii
 }.


 Definition pi_eq_refl1 inv E1 E2 t f (pii:@proc_eq_inv_info inv E1 E2 t f) :=
    pii.(dpii).(dpi_eq_refl1).

 Definition pi_eq_refl2 inv E1 E2 t f (pii:@proc_eq_inv_info inv E1 E2 t f) :=
    pii.(dpii).(dpi_eq_refl2).

 Definition pii_input inv E1 E2 t f (pii:@proc_eq_inv_info inv E1 E2 t f) :=
    pii.(dpii).(dpii_input).

 Definition pii_params inv E1 E2 t f (pii:@proc_eq_inv_info inv E1 E2 t f) :=
    pii.(dpii).(dpii_params).

 Definition pii_output inv E1 E2 t f (pii:@proc_eq_inv_info inv E1 E2 t f) :=
    pii.(dpii).(dpii_output).


 Definition iinput_global inv E1 E2 t f (pii:@proc_eq_inv_info inv E1 E2 t f) :
   forall x, Vset.mem x (pii_input pii) -> Var.is_global x := 
  pii.(spii).(siinput_global).

 Definition params_subset1 inv E1 E2 t f (pii:@proc_eq_inv_info inv E1 E2 t f) :
   (pii_params pii) [<=] Vset_of_var_decl (proc_params E1 f):= 
  pii.(spii).(sparams_subset1).

 Definition params_subset2 inv E1 E2 t f (pii:@proc_eq_inv_info inv E1 E2 t f) :
   (pii_params pii) [<=] Vset_of_var_decl (proc_params E2 f):= 
  pii.(spii).(sparams_subset2).

 Definition pii_output_global inv E1 E2 t f (pii:@proc_eq_inv_info inv E1 E2 t f) :
   forall x, Vset.mem x (pii_output pii) -> Var.is_global x := 
  pii.(spii).(spii_output_global).

 Definition pii_spec inv E1 E2 t f (pii:@proc_eq_inv_info inv E1 E2 t f) :
    exists ls, 
    (forall x, Vset.mem x ls -> Var.is_local x) /\ 
    EqObsInv inv (Vset.union (pii_input pii) (pii_params pii)) 
     E1 (proc_body E1 f) E2 (proc_body E2 f) (Vset.union ls (pii_output pii)) /\ 
     EqObs_e 
     (Vset.union (Vset.union ls (pii_output pii))
      (Vset.diff (pii_input pii) 
        (Vset.union (pi_mod (pi_eq_refl1 pii)) (pi_mod (pi_eq_refl2 pii)))))
     (proc_res E1 f) (proc_res E2 f) := 
  pii.(spii).(spii_spec).

 Definition eq_inv_info_o inv (E1 E2:env) := 
  forall t (f:Proc.proc t), option (proc_eq_inv_info inv E1 E2 f).

 Record eq_inv_info (inv:mem_rel) (E1 E2:env) : Type := {
  pii_inv_X1 : Vset.t;
  pii_inv_X2 : Vset.t;
  pii_inv_dep : depend_only_rel inv pii_inv_X1 pii_inv_X2;
  pii_inv_global : forall x, 
   Vset.mem x (Vset.union pii_inv_X1 pii_inv_X2) -> Var.is_global x;
  pii_inv_dec : decMR inv;
  pii_info : eq_inv_info_o inv E1 E2
 }.

 Definition refl1_info inv E1 E2 (pii:eq_inv_info inv E1 E2) : eq_refl_info E1:=
  fun t f => 
   match pii.(pii_info) f with
   | Some pif => Some (pi_eq_refl1 pif)
   | None => None
   end.

 Definition refl2_info inv E1 E2 (pii:eq_inv_info inv E1 E2) : eq_refl_info E2:=
  fun t f => 
   match pii.(pii_info) f with
   | Some pif => Some (pi_eq_refl2 pif)
   | None => None
   end.

 Section EqObsInv_IN_NM.

  Variable n : positive.
  Variable inv : mem_rel.
  Variables E1 E2 : env.
  Variables X1 X2 : Vset.t.
  Variable pii : eq_inv_info_o inv E1 E2.

  Hypothesis inv_dep : depend_only_rel inv X1 X2.
  Hypothesis inv_global : forall x, 
   Vset.mem x (Vset.union X1 X2) -> Var.is_global x.
  Hypothesis inv_dec : decMR inv.

  Definition eqobsinv_in_b_nm (i:I.baseInstr) O :=
   match i with
   | I.Assign t x e =>
     if Vset.mem x X1 then None
     else if Vset.mem x X2 then None
     else if Vset.mem x O then Some (fv_expr_extend e (Vset.remove x O))
     else Some O
   | I.Random t x e => 
     if Vset.mem x X1 then None
     else if Vset.mem x X2 then None
     else if Vset.mem x O then  Some (Vset.union (fv_distr e) (Vset.remove x O))
     else Some O
   end.

  Fixpoint eqobsinv_in_i (i:I.instr) (O:Vset.t) {struct i} : option Vset.t :=
   match i with
   | I.Instr ib => eqobsinv_in_b_nm ib O
   | I.Cond e c1 c2 =>
     let oI1 := List.fold_right (fun i => opt_app (eqobsinv_in_i i)) (Some O) c1 in
     let oI2 := List.fold_right (fun i => opt_app (eqobsinv_in_i i)) (Some O) c2 in
      match oI1, oI2 with
      | Some I1, Some I2 => 
        Some (fv_expr_extend e (Vset.union I1 I2))
      | _, _ => None
      end
   | I.While e c =>
     let loop O :=     
     let oI := List.fold_right (fun i => opt_app (eqobsinv_in_i i)) (Some O) c in
      match oI with
      | Some II => 
        if II [<=?] O then Result Vset.t (Some O)
        else Continue (option Vset.t) (Vset.union II O)
      | None => Result Vset.t None
      end in
      let Oe := fv_expr_extend e O in
       match While_loop.while loop n Oe with
       | Continue _ => None
       | Result r => r
       end
   | I.Call t d f arg =>
     if Vset.mem d X1 then None
     else if Vset.mem d X2 then None
     else
     let lv1 := proc_params E1 f in
     let lv2 := proc_params E2 f in
      match pii f with
      | Some pif =>
        let fout := Vset.add d (pii_output pif) in
        let other := Vset.diff O fout in
         if Vset.disjoint other
           (Vset.union (pi_mod (pi_eq_refl1 pif)) (pi_mod (pi_eq_refl2 pif))) then 
         let gif := Vset.union (pii_input pif) other in
          match needed_args lv1 arg lv2 arg (pii_params pif) gif with
          | None => None
          | Some Ifun => Some Ifun
          end
         else None
      | _ => None
      end
   end.
  
  Lemma eqobsinv_in_b_nm_correct : forall (i:I.baseInstr) O I,
   eqobsinv_in_b_nm i O = Some I ->
   EqObsInv inv I E1 [I.Instr i] E2 [I.Instr i] O.
  Proof.
   destruct i; simpl; intros O I.
   case_eq (Vset.mem v X1); intro; try (intros; discriminate).
   case_eq (Vset.mem v X2); intro; try (intros; discriminate). 
   case_eq  (Vset.mem v O); intros H1 H2; unfold EqObsInv; inversion H2; clear H2; subst.
   eapply equiv_strengthen;[ | apply equiv_assign].
   unfold req_mem_rel, kreq_mem, andR; intros k m1 m2 (H3,H4); split.
   rewrite union_fv_expr_spec in H3.
   apply req_mem_weaken with (Vset.add v (Vset.remove v O)).
   rewrite VsetP.add_remove; auto with set.
   rewrite (@EqObs_e_fv_expr t e k m1 m2).
   apply req_mem_update.
   apply req_mem_weaken with (2:= H3); auto with set.
   apply req_mem_weaken with (2:= H3); auto with set.
   apply inv_dep with (m1 := m1) (m2 := m2); auto using req_mem_upd_disjoint.
   apply  equiv_lossless_Modify with (X1 := Vset.union I X1) (X2:=Vset.union I X2) 
    (M1 := Vset.singleton v) (M2:=Vset.singleton v);
   auto using lossless_assign, Modify_assign, depend_only_req_mem_rel.
   apply disjoint_singleton.
   case_eq (Vset.mem v (Vset.union I X1)); intros; trivial.
   change (is_true (Vset.mem v (Vset.union I X1))) in H2.
   rewrite VsetP.union_spec, H, H1 in H2; destruct H2; trivialb.
   apply disjoint_singleton.
   case_eq (Vset.mem v (Vset.union I X2)); intros; trivial.
   change (is_true (Vset.mem v (Vset.union I X2))) in H2.
   rewrite VsetP.union_spec, H1, H0 in H2; destruct H2; trivialb.

   case_eq (Vset.mem v X1); intro; try (intros; discriminate).
   case_eq (Vset.mem v X2); intro; try (intros; discriminate). 
   case_eq  (Vset.mem v O); intros H1 H2; unfold EqObsInv; inversion H2; clear H2; subst.
   eapply equiv_strengthen;[ | apply equiv_random].
   unfold req_mem_rel, kreq_mem, andR; intros k m1 m2 (H3,H4); split.
   unfold eq_support.
   apply EqObs_d_fv_expr.
   apply req_mem_weaken with (2:= H3); auto with set.  
   intros; split.
   apply req_mem_weaken with (Vset.add v (Vset.remove v O)).
   rewrite VsetP.add_remove; auto with set.
   apply req_mem_update.
   apply req_mem_weaken with (2:= H3); auto with set.
   apply inv_dep with (m1 := m1) (m2 := m2); auto using req_mem_upd_disjoint.
   apply  equiv_lossless_Modify with (X1 := Vset.union I X1) (X2:=Vset.union I X2) 
    (M1 := Vset.singleton v) (M2:=Vset.singleton v);
   auto using lossless_random, Modify_random, depend_only_req_mem_rel.
   apply disjoint_singleton.
   case_eq (Vset.mem v (Vset.union I X1)); intros; trivial.
   change (is_true (Vset.mem v (Vset.union I X1))) in H2.
   rewrite VsetP.union_spec, H, H1 in H2; destruct H2; trivialb.
   apply disjoint_singleton.
   case_eq (Vset.mem v (Vset.union I X2)); intros; trivial.
   change (is_true (Vset.mem v (Vset.union I X2))) in H2.
   rewrite VsetP.union_spec, H1, H0 in H2; destruct H2; trivialb.
  Qed.
 
 Lemma eqobsinv_in_i_correct_aux :
  (forall i O I, 
   eqobsinv_in_i i O = Some I -> EqObsInv inv I E1 [i] E2 [i] O) /\
  forall c O I, 
   List.fold_right (fun i => opt_app (eqobsinv_in_i i)) (Some O) c = Some I ->
   EqObsInv inv I E1 c E2 c O.
 Proof.
  apply I.cmd_ind2; simpl.
  intros; apply eqobsinv_in_b_nm_correct; trivial.
  (* Cond *)
  intros.
  assert (IH1 := H O); assert (IH2 := H0 O). 
  destruct (fold_right (fun i : I.instr => opt_app (eqobsinv_in_i i)) (Some O) c1); try discriminate.
  destruct (fold_right (fun i : I.instr => opt_app (eqobsinv_in_i i)) (Some O) c2); try discriminate.
  inversion H1; clear H1; subst.
  red; apply equiv_cond.
  apply equiv_strengthen with (2:= IH1 _ (refl_equal _)).
  intros k m1 m2 (W1, (W2, W3)).
  eapply req_mem_rel_weaken; eauto.
  rewrite union_fv_expr_spec; auto with set.
  unfold Basics.flip; trivial.
  apply equiv_strengthen with (2:= IH2 _ (refl_equal _)).
  intros k m1 m2 (W1, (W2, W3)).
  eapply req_mem_rel_weaken; eauto.
  rewrite union_fv_expr_spec; auto with set.
  unfold Basics.flip; trivial.
  intros k m1 m2 (W1, W2).
  unfold kreq_mem in W1; rewrite union_fv_expr_spec in W1.
  apply EqObs_e_fv_expr.
  apply req_mem_weaken with (2:= W1); auto with set.
  (* While *)
  intros b c IH O I H0.
   set (P1 := fun X => Vset.union O (fv_expr b) [<=] X).
   set (P2 := fun res =>
    match res with
     | Continue X => P1 X
     | Result None => True
     | Result (Some X) => Vset.union O (fv_expr b) [<=] X /\  EqObsInv inv X E1 c E2 c X
    end).
   match type of H0 with
    | match ?t with
       | Result _ => _ 
       | Continue _ => _ 
      end = _ => cut (P2 t); [destruct t; try discriminate|]
   end.
   destruct o; [injection H0; clear H0; intro; subst | discriminate].
   unfold P2; clear P2 P1; intros [H1 H2].
   red; apply equiv_weaken with (req_mem_rel I inv).
    intros k m1 m2 W; apply req_mem_rel_weaken with (3:= W); auto.
    apply VsetP.subset_trans with (Vset.union O (fv_expr b)); auto with set.
   unfold Basics.flip; trivial.
   eapply equiv_strengthen;[ | eapply equiv_weaken;[ | apply equiv_while;
     [ | eapply equiv_strengthen; [ | apply H2 ] ] ] ]; unfold andR; try (simpl; tauto); intros.
   apply EqObs_e_fv_expr.
   destruct H as (W1, _); apply req_mem_weaken with (2:= W1); auto with set.
   apply VsetP.subset_trans with (Vset.union O (fv_expr b)); auto with set.
 
   (* Body of the loop *)
   apply while_P with P1; intros.
   unfold P1 in *; generalize (IH a); clear P1 IH; intros.
   destruct (fold_right (fun i : I.instr => opt_app (eqobsinv_in_i i)) (Some a)).
   assert (U:=H1 _ (refl_equal _)); clear H1.
   case_eq (t [<=?] a); intros; simpl.
   change (t [<=] a) in H1; split; auto.
   unfold EqObsInv in *; eapply equiv_strengthen;[ | apply U].
    intros k m1 m2 W1; apply req_mem_rel_weaken with (3:= W1); auto with set.
   unfold Basics.flip; trivial.
   apply VsetP.subset_trans with a; auto with set.
   simpl; trivial.
   exact H.
   unfold P1; auto with set.
   rewrite union_fv_expr_spec, VsetP.union_sym; auto with set.

  (* Call *)
  intros t0 x f a O I.
  case_eq (Vset.mem x X1); intro; try (intros; discriminate).
  case_eq (Vset.mem x X2); intro; try (intros; discriminate).
  destruct (pii f); try (intros; discriminate).
  case_eq (Vset.disjoint (Vset.diff O (Vset.add x (pii_output p)))
            (Vset.union (pi_mod (pi_eq_refl1 p)) (pi_mod (pi_eq_refl2 p)))); intro;
  try (intros; discriminate).
  case_eq (needed_args (proc_params E1 f) a (proc_params E2 f) a (pii_params p)
    (Vset.union (pii_input p) (Vset.diff O (Vset.add x (pii_output p))))); intros;
  try discriminate.  
  inversion H3; clear H3; subst.
  destruct (needed_args_correct _ _ _ _ _ _ H2) as (W1, W2).
  red.
  apply equiv_call with 
     (Pf:= req_mem_rel (Vset.union (pii_params p) (get_globals I)) inv)
     (Qf := 
       req_mem_rel (Vset.union (pii_output p) 
              (Vset.diff (get_globals I) 
                  (Vset.union (pi_mod (pi_eq_refl1 p)) 
                              (pi_mod (pi_eq_refl2 p))))) 
        (inv /-\ (fun k m1 m2 => E.eval_expr (proc_res E1 f) m1 = E.eval_expr (proc_res E2 f) m2))). 
  (* init *)
  unfold req_mem_rel, kreq_mem, andR; simpl; intros k m1 m2 (W3, W4).
  assert (init_mem E1 f a m1 =={ Vset.union (pii_params p) (get_globals I)} init_mem E2 f a m2).
  eapply EqObs_args_correct; eauto.
  split; trivial.
  unfold depend_only_rel in inv_dep.
  apply inv_dep with m1 m2; trivial; red; intros;
  rewrite init_mem_global; trivial; apply inv_global; rewrite VsetP.union_spec; auto.
  (* post *)
  unfold req_mem_rel, kreq_mem, andR; simpl; intros k m1 m1' m2 m2' (W3, W4) (W5, (W6, W7)); split.
  red; intros.
  destruct (Vset.ET.eq_dec x x0).
  inversion e; subst.
  apply T.inj_pair2 in H6; subst.
  repeat rewrite return_mem_dest; trivial.
  change (Var.mkV x <> x0) in n0.
  case_eq (Var.is_global x0); intros.
  repeat rewrite return_mem_global; trivial.
  apply W5.
  rewrite VsetP.union_spec, VsetP.diff_spec.
  case_eq (Vset.mem x0 (pii_output p)); intros; auto.
  assert (Vset.mem x0 (Vset.diff O (Vset.add x (pii_output p)))).
   rewrite VsetP.diff_spec, VsetP.add_spec, H5; intuition.
  right; split.
  apply get_globals_complete; auto.
  apply Vset.subset_correct with (1:= W2); auto with set.
  eapply VsetP.disjoint_mem_not_mem; eauto; trivial.
  repeat rewrite return_mem_local; unfold Var.is_local; try rewrite H4; trivial.
  apply W3.
  apply Vset.subset_correct with (1:= W2).
  rewrite VsetP.union_spec, VsetP.diff_spec, VsetP.add_spec.
  right; intuition.
  assert (U:= pii_output_global p _ H6); rewrite H4 in U; discriminate.
  red in inv_dep.
  apply inv_dep with m1' m2'; trivial; red; intros; rewrite return_mem_global; trivial.
  intros Heq; rewrite <-Heq, H in H3; discriminate.
  auto with set.
  intros Heq; rewrite <-Heq, H0 in H3; discriminate.
  auto with set.

  (* Body *)
  destruct (mod_spec (pi_eq_refl1 p)) as (L1, (T1,T2)).
  destruct (mod_spec (pi_eq_refl2 p)) as (L2, (T3,T4)).
  destruct (pii_spec p) as (ls, (H3,(H4,H5))).
  apply Modify_Modify_pre with (P := fun _ _ => True)in T2.
  apply Modify_Modify_pre with (P := fun _ _ => True)in T4.
  apply equiv_union_Modify_pre2 with (4:= T2) (5:= T4) 
   (Q:= req_mem_rel (Vset.union ls (pii_output p)) inv); intros.
  auto.
  tauto.
  destruct H6; destruct H7; unfold kreq_mem in *.
  assert (m1' =={
            Vset.diff (get_globals I)
              (Vset.union (pi_mod (pi_eq_refl1 p)) (pi_mod (pi_eq_refl2 p)))}m2').
   red; intros.
   rewrite VsetP.diff_spec, VsetP.union_spec in H12.
   destruct H12.
   rewrite <- H8.
   rewrite <- H9.
   apply H6; rewrite VsetP.union_spec; tauto.
   rewrite VsetP.union_spec; intros [W | W]; try tauto.
   assert (V1 := T3 _ W); unfold Var.is_local in V1; rewrite (get_globals_spec _ _ H12) in V1;
    discriminate.
   rewrite VsetP.union_spec; intros [W | W]; try tauto.
   assert (V1 := T1 _ W); unfold Var.is_local in V1; rewrite (get_globals_spec _ _ H12) in V1;
    discriminate.
  split.
   unfold kreq_mem.
   apply req_mem_union; trivial.
   apply req_mem_weaken with (2:= H7); auto with set.
  split; trivial.
   apply H5.
   apply req_mem_union; trivial.
   apply req_mem_weaken with (2:= H12). 
   apply VsetP.diff_le_compat; auto with set.
   apply Vset.subset_complete; intros.
   apply get_globals_complete.
   apply Vset.subset_correct with (1:= W2); auto with set.
   apply (iinput_global p); trivial.
  eapply equiv_strengthen;[ | apply H4].
  intros k m1 m2 (W3, W4); split; trivial.
  unfold kreq_mem; rewrite VsetP.union_sym.
  apply req_mem_weaken with (2:= W3).
  apply VsetP.subset_union_ctxt; auto with set.
   apply Vset.subset_complete; intros.
   apply get_globals_complete.
   apply Vset.subset_correct with (1:= W2); auto with set.
   apply (iinput_global p); trivial.
 
  (* nil and cons *)
  intros O I H; inversion H; red; apply equiv_nil.
  unfold EqObsInv; intros.
  generalize (H0 O); clear H0;
   destruct(fold_right (fun i : I.instr => opt_app (eqobsinv_in_i i)) (Some O) c);
   simpl in H1; try discriminate; intros.
  apply equiv_cons with (req_mem_rel t inv); auto.
 Qed.

 Lemma eqobsinv_in_i_correct : forall i O I, 
  eqobsinv_in_i i O = Some I -> 
  EqObsInv inv I E1 [i] E2 [i] O.
 Proof.
  destruct eqobsinv_in_i_correct_aux; trivial.
 Qed.
 

 (* [eqobsinv_out_i I i] computes the largest [O] such that [EqObs_i I i i O] *)
 Definition eqobsinv_out_b I (i:I.baseInstr) :=
  match i with
  | I.Assign t x e =>
    if Vset.mem x X1 then None
    else if Vset.mem x X2 then None
    else Some (if fv_expr e [<=?] I then Vset.add x I else Vset.remove x I)
  | I.Random t x d =>
    if Vset.mem x X1 then None
    else if Vset.mem x X2 then None
    else Some (if fv_distr d [<=?] I then Vset.add x I else Vset.remove x I)
  end.


 Section OUT.
  
  Variable eqobsinv_out_i : Vset.t -> I.instr -> option Vset.t.
 
  Fixpoint eqobsinv_out_aux (I:Vset.t) (c:cmd) {struct c} : option Vset.t :=
   match c with
   | nil => Some I
   | i::c =>
     match eqobsinv_out_i I i with
     | Some OI => eqobsinv_out_aux OI c
     | _ => None
     end
   end.
  
 End OUT.
 
 Fixpoint eqobsinv_out_i (I:Vset.t) (i:I.instr) {struct i}: option Vset.t :=
  match i with
  | I.Instr i => eqobsinv_out_b I i
  | I.Cond e c1 c2 =>
    if fv_expr e [<=?] I then 
     match eqobsinv_out_aux eqobsinv_out_i I c1, eqobsinv_out_aux eqobsinv_out_i I c2 with
     | Some O1, Some O2 => Some (Vset.inter O1 O2)
     | _, _ => None
     end
     else None
  | I.While e c => 
    if fv_expr e [<=?] I then 
     match eqobsinv_out_aux eqobsinv_out_i I c with
     | Some O' => if I [<=?] O' then Some I else None
     | _ => None
     end
    else None
  | I.Call t d f args =>  
    if Vset.mem d X1 then None
     else if Vset.mem d X2 then None
     else
     let lv1 := proc_params E1 f in
     let lv2 := proc_params E2 f in
     match pii f with
     | Some pif =>
       match needed_args lv1 args lv2 args (pii_params pif) Vset.empty with
       | None => None
       | Some Ia =>
         if Ia [<=?] I then
          if (pii_input pif) [<=?] I then
           Some 
             (Vset.union 
                  (Vset.add d (pii_output pif))
                  (Vset.diff 
                    (Vset.diff I (pi_mod (pi_eq_refl1 pif)))
                                  (pi_mod (pi_eq_refl2 pif))))
          else None
         else None
       end
     | None => None
     end
   end.
  
  Lemma eqobsinv_out_correct_aux : 
   (forall i I O, eqobsinv_out_i I i = Some O -> 
    EqObsInv inv I E1 [i] E2 [i] O) /\ 
   (forall c I O, eqobsinv_out_aux eqobsinv_out_i I c = Some O -> 
    EqObsInv inv I E1 c E2 c O).
  Proof.
   unfold EqObsInv; apply I.cmd_ind2; simpl; intros.
   
   (* baseInstr *) 
   generalize H; clear H.
   destruct i as [t x e | t x d]; simpl;
   (case_eq (Vset.mem x X1); intro H1;
    [  intros; discriminate |
       case_eq (Vset.mem x X2); intros H2 H3; inversion H3; clear H3; subst]).
   case_eq (fv_expr e[<=?]I); intros.
   eapply equiv_strengthen;[ | apply equiv_assign].
   unfold req_mem_rel, kreq_mem; intros k m1 m2 (H3, H4); split.
   rewrite (@EqObs_e_fv_expr t e k m1 m2).
   apply req_mem_update; trivial.
   apply req_mem_weaken with (2:= H3); auto with set.
   apply inv_dep with (m1 := m1) (m2 := m2); auto using req_mem_upd_disjoint.
   eapply equiv_strengthen;[ | apply equiv_lossless_Modify with 
    (X1 := Vset.union (Vset.remove x I) X1) (X2:=Vset.union (Vset.remove x I) X2) 
    (M1 := Vset.singleton x) (M2:=Vset.singleton x);
    auto using lossless_assign, Modify_assign, depend_only_req_mem_rel].
   intros k m1 m2 H3; apply req_mem_rel_weaken with (3 := H3); auto with set.
   unfold Basics.flip; trivial.
   apply disjoint_singleton.
   case_eq (Vset.mem x (Vset.union (Vset.remove x I) X1)); intros; trivial.
   change (is_true (Vset.mem x (Vset.union (Vset.remove x I) X1))) in H0.
   rewrite VsetP.union_spec, VsetP.remove_spec, H1 in H0.
   intuition.
   elim H4; trivial.
   apply disjoint_singleton.
   case_eq (Vset.mem x (Vset.union (Vset.remove x I) X2)); intros; trivial.
   change (is_true (Vset.mem x (Vset.union (Vset.remove x I) X2))) in H0.
   rewrite VsetP.union_spec, VsetP.remove_spec, H2 in H0.
   intuition.
   elim H4; trivial.
   case_eq (fv_distr d[<=?]I); intros.
   eapply equiv_strengthen;[ | apply equiv_random].
   unfold req_mem_rel, kreq_mem; intros k m1 m2 (H3, H4); split.
   unfold eq_support.
   apply EqObs_d_fv_expr.
   apply req_mem_weaken with (2:= H3); auto with set.  
   intros; split.
   apply req_mem_update.
   apply req_mem_weaken with (2:= H3); auto with set.
   apply inv_dep with (m1 := m1) (m2 := m2); auto using req_mem_upd_disjoint.
   eapply equiv_strengthen ; [ |apply  equiv_lossless_Modify with (X1 := Vset.union (Vset.remove x I) X1)
    (X2:=Vset.union  (Vset.remove x I) X2) 
    (M1 := Vset.singleton x) (M2:=Vset.singleton x);
   auto using lossless_random, Modify_random, depend_only_req_mem_rel].
   intros k m1 m2 H3; apply req_mem_rel_weaken with (3 := H3); auto with set.
   unfold Basics.flip; trivial.
   apply disjoint_singleton.
   case_eq (Vset.mem x (Vset.union (Vset.remove x I) X1)); intros; trivial.
   change (is_true (Vset.mem x (Vset.union (Vset.remove x I) X1))) in H0.
   rewrite VsetP.union_spec, VsetP.remove_spec, H1 in H0.
   intuition.
   elim H4; trivial.
   apply disjoint_singleton.
   case_eq (Vset.mem x (Vset.union (Vset.remove x I) X2)); intros; trivial.
   change (is_true (Vset.mem x (Vset.union (Vset.remove x I) X2))) in H0.
   rewrite VsetP.union_spec, VsetP.remove_spec, H2 in H0.
   intuition.
   elim H4; trivial.
   (* cond *)
   case_eq (fv_expr b[<=?]I); intro Heq; rewrite Heq in H1; try discriminate.
   generalize (H I) (H0 I).
   destruct (eqobsinv_out_aux eqobsinv_out_i I c1); try discriminate.
   destruct (eqobsinv_out_aux eqobsinv_out_i I c2); try discriminate.
   inversion H1; clear H1; subst; intros.
   apply equiv_cond.
   eapply equiv_strengthen;[ | eapply equiv_weaken; [ | apply H1; reflexivity] ].
   unfold andR; tauto.
   intros; eapply req_mem_rel_weaken; eauto; auto with set.
   unfold Basics.flip; trivial.
   eapply equiv_strengthen;[ | eapply equiv_weaken; [ | apply H2; reflexivity] ].
   unfold andR; tauto.
   intros; eapply req_mem_rel_weaken; eauto; auto with set.
   unfold Basics.flip; trivial.
   intros k m1 m2 (H3, H4); apply EqObs_e_fv_expr.
   apply req_mem_weaken with (2:= H3); trivial.
   (* While *)
   case_eq (fv_expr b[<=?]I); intro Heq; rewrite Heq in H0; try discriminate.
   generalize (H I);   destruct (eqobsinv_out_aux eqobsinv_out_i I c); try discriminate.
   case_eq (I[<=?]t); intro Heq2; rewrite Heq2 in H0; try discriminate.
   inversion H0; clear H0; subst; intros.
   eapply equiv_weaken;[ | apply equiv_while].
   unfold andR; tauto.
   intros k m1 m2 (H3, H4); apply EqObs_e_fv_expr.
   apply req_mem_weaken with (2:= H3); trivial.
   eapply equiv_strengthen;[ | eapply equiv_weaken; [ | apply H0; reflexivity] ].
   unfold andR; tauto.
   change (O[<=]t) in Heq2; intros; eapply req_mem_rel_weaken; eauto with set.
   unfold Basics.flip; trivial.
   (* Function *)
   generalize H; clear H.
   case_eq (Vset.mem x X1); intro; try (intros; discriminate).
   case_eq (Vset.mem x X2); intro; try (intros; discriminate).
   destruct (pii f); try (intros; discriminate).
   case_eq (needed_args (proc_params E1 f) a (proc_params E2 f) a (pii_params p)
     Vset.empty); try (intros; discriminate).
   intros Ia H1; case_eq (Ia[<=?]I); intro; try (intros; discriminate). 
   destruct (needed_args_correct _ _ _ _ _ _ H1) as (W1, W2).
   case_eq (pii_input p[<=?]I); intros; try discriminate. 
   inversion H4; clear H4; subst.
   apply equiv_call with 
     (Pf:= req_mem_rel (Vset.union (pii_params p) (get_globals I)) inv)
     (Qf :=  
       req_mem_rel (Vset.union (pii_output p) 
              (Vset.diff (get_globals I) 
                  (Vset.union (pi_mod (pi_eq_refl1 p)) 
                              (pi_mod (pi_eq_refl2 p))))) 
       (inv  /-\ (fun k m1 m2 =>
       E.eval_expr (proc_res E1 f) m1 = E.eval_expr (proc_res E2 f) m2))). 
  (* init *)
  unfold req_mem_rel, kreq_mem, andR; simpl; intros k m1 m2 (W3, W4).
  assert (init_mem E1 f a m1 =={ Vset.union (pii_params p) (get_globals I)} init_mem E2 f a m2).
    eapply EqObs_args_correct; eauto.
    eapply EqObs_args_strengthen with Ia; eauto; trivial.
  unfold depend_only_rel in inv_dep.
  split; trivial.
  apply inv_dep with m1 m2; trivial; red; intros;
  rewrite init_mem_global; trivial; apply inv_global; rewrite VsetP.union_spec; auto.
  (* post *)
  unfold req_mem_rel, kreq_mem, andR; simpl; intros k m1 m1' m2 m2' (W3, W4) (W5, (W6, W7)); split.
  red; intros.
  destruct (Vset.ET.eq_dec x x0).
  inversion e; subst; simpl.
  repeat rewrite return_mem_dest; trivial.
  change (Var.mkV x <> x0) in n0.
  case_eq (Var.is_global x0); intros.
  repeat rewrite return_mem_global; trivial.
  apply W5.
  rewrite VsetP.union_spec, VsetP.diff_spec in H4 |- *.
  destruct H4.
  rewrite VsetP.add_spec in H4; destruct H4; auto.
  elim (n0 H4).
  rewrite VsetP.diff_spec in H4; rewrite VsetP.union_spec; right; intuition.
  apply get_globals_complete; trivial.
  repeat rewrite return_mem_local; unfold Var.is_local; try rewrite H4; trivial.
  apply W3.
  rewrite VsetP.union_spec, VsetP.add_spec, VsetP.diff_spec in H4; intuition.
  rewrite (pii_output_global p _ H4) in H5; discriminate.
  rewrite VsetP.diff_spec in H4; intuition.
  rewrite H5; trivial. rewrite H5; trivial.
  red in inv_dep.
  apply inv_dep with m1' m2'; trivial; red; intros; rewrite return_mem_global; trivial.
  intros Heq; rewrite <-Heq, H in H4; discriminate.
  auto with set.
  intros Heq; rewrite <-Heq, H0 in H4; discriminate.
  auto with set.
  (* body *)
  destruct (mod_spec (pi_eq_refl1 p)) as (L1, (T1,T2)).
  destruct (mod_spec (pi_eq_refl2 p)) as (L2, (T3,T4)).
  destruct (pii_spec p) as (ls, (H6,(H4,H5))).
  apply Modify_Modify_pre with (P := fun _ _ => True)in T2.
  apply Modify_Modify_pre with (P := fun _ _ => True)in T4.
  apply equiv_union_Modify_pre2 with (4:= T2) (5:= T4) 
   (Q:= req_mem_rel (Vset.union ls (pii_output p)) inv); intros.
  auto.
  tauto.
  destruct H7; destruct H8; unfold kreq_mem in *.
  assert (m1' =={
            Vset.diff (get_globals I)
              (Vset.union (pi_mod (pi_eq_refl1 p)) (pi_mod (pi_eq_refl2 p)))}m2').
   red; intros.
   rewrite VsetP.diff_spec, VsetP.union_spec in H13.
   destruct H13.
   rewrite <- H9.
   rewrite <- H10.
   apply H7; rewrite VsetP.union_spec; tauto.
   rewrite VsetP.union_spec; intros [W | W]; try tauto.
   assert (V1 := T3 _ W); unfold Var.is_local in V1; rewrite (get_globals_spec _ _ H13) in V1;
    discriminate.
   rewrite VsetP.union_spec; intros [W | W]; try tauto.
   assert (V1 := T1 _ W); unfold Var.is_local in V1; rewrite (get_globals_spec _ _ H13) in V1;
    discriminate.
  split.
   unfold kreq_mem; apply req_mem_union; trivial.
   apply req_mem_weaken with (2:= H8); auto with set.
  split; trivial; apply H5.
   apply req_mem_union; trivial.
   apply req_mem_weaken with (2:= H13). 
   apply VsetP.diff_le_compat; auto with set.
   apply Vset.subset_complete; intros.
   apply get_globals_complete.
   apply Vset.subset_correct with (1:= H3); auto with set.
   apply (iinput_global p); trivial.
  eapply equiv_strengthen;[ | apply H4].
  intros k m1 m2 (W3, W4); split; trivial.
  unfold kreq_mem; rewrite VsetP.union_sym.
  apply req_mem_weaken with (2:= W3).
  apply VsetP.subset_union_ctxt; auto with set.
   apply Vset.subset_complete; intros.
   apply get_globals_complete.
   apply Vset.subset_correct with (1:= H3); auto with set.
   apply (iinput_global p); trivial.
 
  (* nil and cons *)
  inversion H; apply equiv_nil.
  unfold EqObsInv; intros.
  generalize (H I); clear H; destruct(eqobsinv_out_i I i); simpl in H1; try discriminate; intros.
  apply equiv_cons with (req_mem_rel t inv); auto.
 Qed.
 
 Lemma eqobsinv_out_i_correct: forall i I O, 
  eqobsinv_out_i I i = Some O -> 
  EqObsInv inv I E1 [i] E2 [i] O.
 Proof.
  destruct eqobsinv_out_correct_aux; trivial.
 Qed.

 
 (* Reducing the context *)
 Fixpoint eqobsinv_context_rev_n (n:nat) (cr cr':cmd) (O:Vset.t) {struct n} : 
  triple cmd cmd Vset.t :=
  match n, cr, cr' with
  | S n, i::cr1, i'::cr1' =>
    if I.eqb i i' then 
     match eqobsinv_in_i i O with
     | Some IO => eqobsinv_context_rev_n n cr1 cr1' IO
     | None => Triple (List.rev' cr) (List.rev' cr') O
     end
     else Triple (List.rev' cr) (List.rev' cr') O
  | _, _, _ => Triple (List.rev' cr) (List.rev' cr') O
  end.
 
 Definition eqobsinv_context_tail_n n (c c':cmd) O :=
  eqobsinv_context_rev_n n (List.rev' c) (List.rev' c') O.
 
 Fixpoint eqobsinv_context_head_n (n:nat) (I:Vset.t) (c c':cmd) {struct n} : 
  triple Vset.t cmd cmd :=
  match n, c, c' with
  | S n, i::c1, i'::c1' =>
    if I.eqb i i' then 
     match eqobsinv_out_i I i with 
     | Some OI => eqobsinv_context_head_n n OI c1 c1'
     | _ => Triple I c c'
     end
    else Triple I c c'
  | _, _, _ => Triple I c c'
  end.
 
 Lemma eqobsinv_context_rev_n_correct : forall n1 cr1 cr2 O h1 h2 IO,
  eqobsinv_context_rev_n n1 cr1 cr2 O = Triple h1 h2 IO ->
  exists t, 
   (rev cr1) = h1++t /\ 
   (rev cr2) = h2++t /\ 
   EqObsInv inv IO E1 t E2 t O.
 Proof.
   induction n1; simpl.
   (* 0 *)
   intros cr1 cr2 O h1 h2 IO Heq; inversion_clear Heq.
   exists (@nil I.t); repeat split; auto.
   rewrite <- app_nil_end; exact (rev_alt cr1).
   rewrite <- app_nil_end; exact (rev_alt cr2).
   red; apply equiv_nil.
 
   (* S n1 *)
   destruct cr1 as [ |a cr1].
 
   (* nil, c2 *)
   intros cr2 nO h1 h2 IO Heq; inversion_clear Heq.
   exists (@nil I.t); repeat split; auto.
   rewrite <- app_nil_end; exact (rev_alt cr2).
   red; apply equiv_nil.
   
   destruct cr2; simpl; intros O h1 h2 IO.
   (* _, nil *)
   intros Heq; inversion_clear Heq.
   exists (@nil I.t); repeat split; auto.
   rewrite <- app_nil_end. 
   change (rev cr1 ++ [a]) with (rev (a::cr1)).
   rewrite rev_alt; trivial.
   red; apply equiv_nil.
   
   (* a::c1, t::c2 *)
   case_eq (I.eqb a i); intro Heq'.
   case_eq (eqobsinv_in_i a O).
   intros I' Heq1 Heq2.
   destruct (IHn1 _ _ _ _ _ _ Heq2) as (tl, (V1, (V2, V3))); subst.
   exists (tl ++ [a]); repeat split.
   rewrite V1; apply app_ass.
   assert (W:= I.eqb_spec a i); rewrite Heq' in W; rewrite W, V2; apply app_ass.
   red; apply equiv_app with (req_mem_rel I' inv); trivial.
   apply (@eqobsinv_in_i_correct _ _ _ Heq1).
   intros H1 H2; inversion H2; clear H2; subst.
   
   exists (@nil I.t); repeat split; auto.
   rewrite <- app_nil_end. 
   change (rev cr1 ++ [a]) with (rev (a::cr1)).
   rewrite rev_alt; trivial.
   rewrite <- app_nil_end.
   change (rev cr2 ++ [i]) with (rev (i::cr2)).
   rewrite rev_alt; trivial.
   red; apply equiv_nil.
 
   intros Heq; inversion Heq; clear Heq; subst.
   exists (@nil I.t); repeat split; auto.
   rewrite <- app_nil_end. 
   change (rev cr1 ++ [a]) with (rev (a::cr1)).
   rewrite rev_alt; trivial.
   rewrite <-app_nil_end. 
   change (rev cr2 ++ [i]) with (rev (i::cr2)).
   rewrite rev_alt; trivial.
   red; apply equiv_nil.
  Qed.
 
  Lemma eqobsinv_context_tail_n_correct :  forall n1 P c1 c2 O h1 h2 IO,
   eqobsinv_context_tail_n n1 c1 c2 O = Triple h1 h2 IO ->
   equiv P E1 h1 E2 h2 (req_mem_rel IO inv) ->
   equiv P E1 c1 E2 c2 (req_mem_rel O inv).
  Proof.
   intros. 
   destruct (eqobsinv_context_rev_n_correct  _ _ _ _ H) as [t [H1 [H2 H3] ] ].
   unfold rev' in H1, H2.
   rewrite <- rev_alt in H1, H2.
   rewrite rev_involutive in H1, H2; subst.
   red; apply equiv_app with (req_mem_rel IO inv); trivial.
  Qed.
 
  Lemma eqobsinv_context_head_n_correct_aux : forall N I c1 c2 t1 t2 IO, 
   eqobsinv_context_head_n N I c1 c2 = Triple IO t1 t2 ->  
   exists h, c1 = h ++ t1 /\ c2 = h ++ t2 /\ EqObsInv inv I E1 h E2 h IO.
  Proof.
   induction N; simpl; intros I c1 c2 t1 t2 IO.
   (* 0 *)
   intros Heq; inversion Heq; exists (@nil I.t); repeat split.
   red; apply equiv_nil.
   (* S n *)
   destruct c1.
   intros Heq; inversion Heq; exists (@nil I.t); repeat split.
   red; apply equiv_nil.
   destruct c2.
   intros Heq; inversion Heq; exists (@nil I.t); repeat split.
   red; apply equiv_nil.
   (* t::c1, t0::c2 *)
   case_eq (I.eqb i i0); intros H.
   assert (H0 := I.eqb_spec i i0); rewrite H in H0; clear H; subst.
   case_eq (eqobsinv_out_i I i0); [intros OI Heqi | intros Heqi].
   intros Heq; destruct (IHN _ _ _ _ _ _ Heq) as [h [H1 [H2 H3] ] ]; subst.
   exists (i0::h); repeat split; auto.
   red; apply equiv_cons with (req_mem_rel OI inv); auto.
   apply eqobsinv_out_i_correct; trivial.
   intros Heq; inversion Heq; exists (@nil I.t); repeat split.
   red; apply equiv_nil.
   intros Heq; inversion Heq; exists (@nil I.t); repeat split.
   red; apply equiv_nil.
  Qed.
 
  Lemma eqobsinv_context_head_n_correct : forall n I Q c1 c2 t1 t2 IO, 
   eqobsinv_context_head_n n I c1 c2 = Triple IO t1 t2 ->  
   equiv (req_mem_rel IO inv) E1 t1 E2 t2 Q->
   equiv (req_mem_rel I inv) E1 c1 E2 c2 Q.
  Proof.
   intros.
   destruct (eqobsinv_context_head_n_correct_aux _ _ _ _ H) as [h [H1 [H2 H3] ] ].
   subst; red; apply equiv_app with (req_mem_rel IO inv); auto.
  Qed.
    
 End EqObsInv_IN_NM.


 Section WRAPPER.

  Variable n : positive.
  Variable inv : mem_rel.
  Variables E1 E2 : env.
  Variable pii : eq_inv_info inv E1 E2.

  (* [eqobsinv_in i O] compute the smallest [I] such that [Eqobsinv_i I i i O] *)
  Definition eqobsinv_in c O :=
    match pii with
    | Build_eq_inv_info X1 X2 _ _ _ pio =>
      List.fold_right 
       (fun i => opt_app (@eqobsinv_in_i n inv E1 E2 X1 X2 pio i)) (Some O) c
    end. 

  Lemma eqobsinv_in_correct : forall c O I, 
   eqobsinv_in c O = Some I -> 
   EqObsInv inv I E1 c E2 c O.
  Proof.
   unfold eqobsinv_in; destruct pii.
   destruct (eqobsinv_in_i_correct_aux n pii_info0 pii_inv_dep0 pii_inv_global0);
    trivial.
  Qed.

  Definition eqobsinv_out :=  
   match pii with
   | Build_eq_inv_info X1 X2 _ _ _ pio =>
     eqobsinv_out_aux (@eqobsinv_out_i inv E1 E2 X1 X2 pio)
   end.

  Lemma eqobsinv_out_correct: forall c I O, 
   eqobsinv_out I c = Some O -> 
   EqObsInv inv I E1 c E2 c O.
  Proof.
   unfold eqobsinv_out; destruct pii.
   destruct (eqobsinv_out_correct_aux pii_info0 pii_inv_dep0 pii_inv_global0);
    trivial.
  Qed.

  Definition eqobsinv_tail_n p c1 c2 O :=
   match pii with
   | Build_eq_inv_info X1 X2 _ _ _ pio =>
     @eqobsinv_context_tail_n n inv E1 E2 X1 X2 pio p c1 c2 O
   end.

  Definition eqobsinv_tail c1 c2 O := eqobsinv_tail_n (length c1) c1 c2 O.

  Definition eqobsinv_head_n p I c1 c2 :=
    match pii with
    | Build_eq_inv_info X1 X2 _ _ _ pio =>
      @eqobsinv_context_head_n inv E1 E2 X1 X2 pio p I c1 c2
    end.

  Definition eqobsinv_head I c1 c2 := eqobsinv_head_n (length c1) I c1 c2.

  Definition eqobsinv_context I c c' O :=
   let (I1, c1, c1') := eqobsinv_head I c c' in
   let (c2, c2', O2) := eqobsinv_tail c1 c1' O in
    Quad I1 c2 c2' O2.

  Lemma eqobsinv_tail_n_correct : forall p P c1 c2 O h1 h2 IO,
   eqobsinv_tail_n p c1 c2 O = Triple h1 h2 IO ->
   equiv P E1 h1 E2 h2 (req_mem_rel IO inv) ->
   equiv P E1 c1 E2 c2 (req_mem_rel O inv).
  Proof.
   unfold eqobsinv_tail_n; destruct pii.
   apply eqobsinv_context_tail_n_correct; trivial.
  Qed.

  Lemma eqobsinv_tail_correct : forall P c1 c2 O h1 h2 IO,
   eqobsinv_tail c1 c2 O = Triple h1 h2 IO ->
   equiv P E1 h1 E2 h2 (req_mem_rel IO inv) ->
   equiv P E1 c1 E2 c2 (req_mem_rel O inv).
  Proof.
   intros P c1.
   exact (@eqobsinv_tail_n_correct (length c1) P c1).
  Qed.

  Lemma eqobsinv_head_n_correct : forall p I Q c1 c2 t1 t2 IO, 
   eqobsinv_head_n p I c1 c2 = Triple IO t1 t2 ->  
   equiv (req_mem_rel IO inv) E1 t1 E2 t2 Q ->
   equiv (req_mem_rel I inv) E1 c1 E2 c2 Q.
  Proof.
   unfold eqobsinv_head_n; destruct pii.
   apply eqobsinv_context_head_n_correct; trivial.
  Qed.

  Lemma eqobsinv_head_correct : forall I Q c1 c2 t1 t2 IO, 
   eqobsinv_head I c1 c2 = Triple IO t1 t2 ->  
   equiv (req_mem_rel IO inv) E1 t1 E2 t2 Q ->
   equiv (req_mem_rel I inv) E1 c1 E2 c2 Q.
  Proof.
   intros I Q c1.
   exact (@eqobsinv_head_n_correct (length c1) I Q c1).
  Qed.

  Lemma eqobsinv_context_correct : forall I c1 c2 O I' c1' c2' O',
   eqobsinv_context I c1 c2 O = Quad I' c1' c2' O' ->
   EqObsInv inv I' E1 c1' E2 c2' O' ->
   EqObsInv inv I E1 c1 E2 c2 O.
  Proof.
   unfold eqobsinv_context; intros I c1 c2 O I' c1' c2' O'.
   case_eq (eqobsinv_head I c1 c2); intros t0 c c0 Heq.
   case_eq (eqobsinv_tail c c0 O); intros.
   inversion H0; clear H0; subst.
   refine (@eqobsinv_head_correct  _ _ _ _ _ _ _ Heq _).
   apply (@eqobsinv_tail_correct  _ _ _ _ _ _ _ H H1).
  Qed.

 End WRAPPER. 

End Make.
