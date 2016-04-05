(** * Alloc.v : Reflection based implementation of a simplified 
   register-allocation optimizer *)


Set Implicit Arguments.

Require Export GenOpt.

Module Make (SemO:SEM_OPT).
 
 Module GO := GenOpt.Make SemO.
 Export GO.
 
 Section ALLOC.

 Variable n : positive.
 Variable E : env.
 Variable pi : eq_refl_info E.
 Variable t : T.type. 
 Variables r d : Var.var t.

 Definition alloc_b (i:I.baseInstr) (dep:bool) : cmd :=
  match i with
  | I.Assign tx x e => 
    if andb (negb dep) (Var.veqb x r) then 
      match T.eq_dec tx t with 
      | left H =>
        match H in _ = y0 return Var.var y0 -> cmd with
        | refl_equal => fun d => [d <- e; x <- d]
        end d
      | right _ => (* never appear *) [x<-e]
      end 
    else [x<- e]
  | I.Random tx x di => 
    if andb (negb dep) (Var.veqb x r) then 
      match T.eq_dec tx t with 
      | left H =>
        match H in _ = y0 return Var.var y0 -> cmd with
        | refl_equal => fun d => [d <$- di; x<-d] 
        end d
      | right _ => (* never appear *) [x<$- di]
      end 
    else [x <$- di]
  end.
 
 Section ALLOC_C.

  Variable alloc_i : I.instr -> bool -> bool * cmd.

  Fixpoint alloc_c_aux (c:cmd) (dep:bool) {struct c} : bool * cmd :=
   match c with
   | nil => (dep, nil)
   | i::c' => 
     let (depc, ca) := alloc_c_aux c' dep in
     let (depi,ia) := alloc_i i depc in (depi, ia ++ ca)
   end.
 
 End ALLOC_C.

 Definition depend_b ib dep :=
  match ib with
  | I.Assign tx x e => 
    if Vset.mem d (fv_expr e) then true
    else if Var.veqb x d then false else dep
  | I.Random tx x e =>
    if Vset.mem d (fv_distr e) then true
    else if Var.veqb x d then false else dep
  end.

 Fixpoint alloc_i (i:I.instr) (dep:bool) {struct i} : bool * cmd :=
  match i with
  | I.Instr ib => 
    (depend_b ib dep, alloc_b ib dep)
  | I.Cond e c1 c2 =>
    let (dep1,c1a) := alloc_c_aux alloc_i c1 dep in
    let (dep2, c2a) := alloc_c_aux alloc_i c2 dep in
    let depi := if orb dep1 dep2 then true else Vset.mem d (fv_expr e) in
     (depi, [If e then c1a else c2a])
  | I.While e c =>
    let dep' := if Vset.mem d (fv_expr e) then true else dep in
    let (depc, ca) := alloc_c_aux alloc_i c dep' in
     if orb dep' (negb depc) then (dep', [while e do ca])
      else 
       let (depc, ca) := alloc_c_aux alloc_i c true in
        (true, [while e do ca])
  | I.Call tx x f arg =>
    let ia :=
     if andb (negb dep) (Var.veqb x r) then   
      match T.eq_dec tx t with 
      | left H =>
        match H in _ = y0 return Var.var y0 -> cmd with
        | refl_equal => fun d => [d<c- f with arg; x <- d] 
        end d
      | right _ => (* never appear *) [i]
      end 
     else [i] in
      let depi :=
       match pi f with
       | Some pif =>
         if pi_mod pif [<=?] pi_output pif then
          if Vset.mem d (fv_args arg) then true  
          else if Vset.mem d (pi_input pif) then true
          else if Var.veqb x d then false
          else dep
         else true
       | _ => true
       end
     in (depi, ia)
  end.

  Definition alloc_pred (dep:bool) : mem_rel :=
   if dep then Meq else eeq_mem (Vset.singleton d).

  Lemma not_fv_eeq_mem : forall x t (e:E.expr t) k (m1 m2:Mem.t k), 
   Vset.mem x (fv_expr e) = false ->
   eeq_mem (Vset.singleton x) m1 m2 ->
   E.eval_expr e m1 = E.eval_expr e m2.
  Proof.
   intros; apply depend_only_fv_expr. 
   red; intros.
   apply H0.
   intro H2; apply Vset.singleton_complete in H2.
   rewrite (H2:x = x0) in H; rewrite H in H1; trivialb.
  Qed.
 

  Lemma alloc_call : forall tx (f:Proc.proc tx)
   (args : E.args (Proc.targs f))
   (p : proc_eq_refl_info E f)
   (H0 : (pi_mod p[<=?]pi_output p) = true)
   (H1 : Vset.mem d (fv_args args) = false)
   (H2 : Vset.mem d (pi_input p) = false)
   (H3 : forall k (m1 m2 : Mem.t k),
    alloc_pred false m1 m2 ->
    dmap (P1:=E.expr) _ (fun t e => E.eval_expr e m1) args =
    dmap (P1:=E.expr) _ (fun t e => E.eval_expr e m2) args)
   (x1 x2:Var.var tx), 
   equiv (eeq_mem (Vset.singleton d)) 
   E [x1 <c- f with args] 
   E [x2 <c- f with args]
   (fun k (m1 m2 : Mem.t k) =>
    eeq_mem (Vset.add x1 (Vset.add x2 (Vset.singleton d))) m1 m2 /\
    E.eval_expr x1 m1 = E.eval_expr x2 m2).
  Proof.
   intros. assert (H:= I).
   destruct (pi_spec p) as (ls, (W1, (W2, W3))).
   destruct (mod_spec p) as (L, (W4,W5)).
   apply equiv_call with 
    (Pf:=if Var.is_global d then eeq_mem (Vset.singleton d) else Meq)
    (Qf:=fun k m1 m2 => 
     eeq_mem (Vset.add d (Vset.diff (Vset.union L (pi_mod p)) (Vset.union ls (pi_output p)))) m1 m2 /\
     E.eval_expr (proc_res E f) m1 = E.eval_expr (proc_res E f) m2).

   (* Init *)
   intros.
   case_eq (Var.is_global d); intros.
   red; intros.
   case_eq (Var.is_global x); intros.
   repeat rewrite init_mem_global; trivial; apply H4; trivial.
   assert (Var.is_local x) by (unfold Var.is_local; rewrite H7; trivial).
   simpl alloc_pred in H3; apply init_mem_local; unfold E.eval_args; auto.
   unfold Meq; apply Mem.eq_leibniz; red; intros (t0,x).
   case_eq (Var.is_global x); intros.
   repeat rewrite init_mem_global; trivial; apply H4; trivial.
   apply VsetP.singleton_mem_diff. 
   intros Heq.
   rewrite (Heq : Var.mkV d = x) in H5; rewrite H5 in H6; discriminate.
   assert (Var.is_local x) by (unfold Var.is_local; rewrite H6; trivial).
   apply init_mem_local; unfold E.eval_args; auto.

   (* Return *)
   intros k m1 m1' m2 m2' H4 (H5,H6); split.
   red; intros.
   repeat rewrite VsetP.add_spec in H7.
   assert (Var.mkV x1 <> x /\ Var.mkV x2 <> x /\ Var.mkV d <> x).
   repeat split; try tauto.
   apply VsetP.mem_singleton_diff; tauto.
   destruct H8 as (H8, (H9, HH9)); case_eq (Var.is_global x); intros.
   repeat rewrite return_mem_global; auto.
   apply H5.
   rewrite VsetP.add_spec, VsetP.diff_spec, VsetP.union_spec, VsetP.union_spec.
   intros [ Y | (Y1,Y2)]; try tauto.
   destruct Y1.
   apply W4 in H11; unfold Var.is_local in H11; rewrite H10 in H11; discriminate.
   apply Y2; right; apply Vset.subset_correct with (2:= H11); trivial.
   assert (Var.is_local x) by (unfold Var.is_local; rewrite H10; trivial).
   repeat rewrite return_mem_local; trivial.
   apply H4; tauto.
   simpl; repeat  rewrite return_mem_dest; trivial.

   (* Body *)
   unfold Meq in *.
   assert (Modify_pre (fun _ _ => True) E 
    (Vset.union (Vset.union L (pi_output p)) ls) (proc_body E f)).
   apply Modify_Modify_pre.    
   apply Modify_weaken with (1:=W5); auto with set.
   rewrite VsetP.union_assoc; apply VsetP.subset_union_ctxt; auto with set.
   apply VsetP.subset_trans with (pi_output p); auto with set. 
   apply equiv_union_Modify_pre with (3:= H4) (4:=H4) 
    (Q:=fun k => @req_mem k (Vset.union ls (pi_output p))); auto.
   split.
   red; intros.
   rewrite VsetP.add_spec, VsetP.diff_spec, VsetP.union_spec, VsetP.union_spec in H7.
   destruct (VsetP.mem_dec x (Vset.union (Vset.union L (pi_output p)) ls)).
   repeat rewrite update_mem_in; trivial.
   repeat rewrite VsetP.union_spec in i.
   apply H6; rewrite VsetP.union_spec; destruct i; try tauto.
   destruct H8; try tauto.
   destruct (VsetP.mem_dec x ls); try tauto.
   destruct (VsetP.mem_dec x (pi_output p)); try tauto.
   repeat rewrite update_mem_notin; trivial.
   destruct (Var.is_global d); try rewrite H5; trivial.
   apply VsetP.singleton_mem_diff.
   intro; repeat rewrite VsetP.union_spec in n0; try tauto.
   apply W3.
   red; intros.
   rewrite VsetP.union_spec in H7; destruct H7.
   assert (Vset.mem x (Vset.union (Vset.union L (pi_output p)) ls)).
   apply Vset.subset_correct with (2:= H7).
   rewrite VsetP.union_assoc, VsetP.union_sym; auto with set.
   repeat rewrite update_mem_in; trivial.
   apply H6; trivial.
   rewrite VsetP.diff_spec in H7; destruct H7.
   assert (~Vset.mem x (Vset.union (Vset.union L (pi_output p)) ls)).
   apply input_global in H7.
   repeat rewrite VsetP.union_spec; intros [ [Y | Y] | Y].
   apply W4 in Y; unfold Var.is_local in Y; rewrite H7 in Y; discriminate.
   apply H8; apply Vset.subset_correct with (2:=Y); apply output_subset.
   apply W1 in Y; unfold Var.is_local in Y; rewrite H7 in Y; discriminate.
   repeat rewrite update_mem_notin; trivial.
   case_eq (Var.is_global d); intros Heq; 
    rewrite Heq in H5; rewrite H5; trivial.
   apply VsetP.singleton_mem_diff.
   intros Heq'.
   rewrite <- (Heq':Var.mkV d = x) in H7; rewrite H2 in H7; trivialb.
   apply equiv_strengthen with (2:= W2).
   unfold kreq_mem; case_eq (Var.is_global d); intros.
   red; intros; apply H6.
   apply VsetP.singleton_mem_diff; intros Heq.
   rewrite <- (Heq: Var.mkV d = x) in H7.
   rewrite VsetP.union_spec in H7; destruct H7.
   rewrite H2 in H7; trivialb.
   apply params_local in H7; unfold Var.is_local in H7.
   rewrite H5 in H7; discriminate.
   rewrite H6; apply req_mem_refl.
  Qed.

  Lemma alloc_spec : 
   (forall i dep depi ia, alloc_i i dep = (depi, ia) -> 
    equiv (alloc_pred depi) E [i] E ia (alloc_pred dep)) /\ 
   (forall c dep depc ca, alloc_c_aux alloc_i c dep = (depc, ca) -> 
    equiv (alloc_pred depc) E c E ca (alloc_pred dep)).
  Proof.
   apply I.cmd_ind2; intros.

   (* baseInstr *)
   inversion_clear H.
   destruct i; simpl.

   (* Assign *)
   match goal with 
    |- equiv _ _ _ _ (if ?b then _ else _) _ => case_eq b; intros end.
   destruct dep; simpl in H; try discriminate.
   assert (Var.mkV v = r).
     generalize (Var.veqb_spec_dep v r); rewrite H; intros. 
     inversion H0; trivial.
   inversion H0; subst.
   case_eq (T.eq_dec t t); intros.
   rewrite (T.UIP_refl e0). 
   rewrite (T.inj_pair2 H3).
   change [r <- e] with (nil ++ [ r <- e]).
   change [d <- e; r <- d] with ([d <- e] ++ [r <- d]).
   apply equiv_app with 
    (fun k m1 m2 => alloc_pred false m1 m2 /\ E.eval_expr d m2 = E.eval_expr e m1).
   eapply equiv_strengthen; [ | apply equiv_assign_r].
   replace (if Var.veqb r d then false else false) with false;
    [ | destruct (Var.veqb r d); trivial].
   case_eq (Vset.mem d (fv_expr e));
   simpl; unfold Meq; intros; subst; split; try red; intros.
   rewrite Mem.get_upd_diff; trivial.
   apply VsetP.mem_singleton_diff; trivial.
   rewrite Mem.get_upd_same; trivial.
   rewrite Mem.get_upd_diff; trivial.
   apply H4; trivial.
   apply VsetP.mem_singleton_diff; trivial.
   rewrite Mem.get_upd_same; trivial.
   symmetry; apply not_fv_eeq_mem with d; trivial.
   eapply equiv_strengthen;[ | apply equiv_assign]. 
   simpl; intros k m1 m2 (H4,H5) tx x H6. 
   generalize (Var.veqb_spec_dep r x).
   destruct (Var.veqb r x); intros.
   inversion H2; subst; simpl.
   repeat rewrite Mem.get_upd_same; rewrite H5; trivial.
   assert (Var.mkV r <> x) by 
    (intros Heq; apply H2; inversion Heq; simpl; trivial).
   repeat rewrite Mem.get_upd_diff; trivial.
   apply H4; trivial.
   elim (T.eq_dec_r H1); trivial.
   eapply equiv_strengthen;[  | apply equiv_assign].
   unfold upd_para.
   destruct dep; simpl.
   case_eq (Vset.mem d (fv_expr e)); simpl.
   unfold Meq; intros; subst; trivial. 
   unfold Meq; generalize (Var.veqb_spec_dep v d).
   destruct (Var.veqb v d); simpl; intros.
   inversion H0; subst.
   rewrite (T.inj_pair2 H6).
   rewrite (not_fv_eeq_mem _ H1 H2).
   apply Mem.eq_leibniz; intros (tx,x); destruct (Var.eq_dec d x); subst.
   inversion e0; simpl.
   repeat rewrite Mem.get_upd_same; trivial.
   repeat rewrite Mem.get_upd_diff; trivial.
   apply H2; apply VsetP.singleton_mem_diff; exact n0.
   unfold Meq in H2; rewrite H2; trivial.
   replace (if Var.veqb v d then false else false) with false; 
    [ | destruct (Var.veqb v d); trivial].
   case_eq (Vset.mem d (fv_expr e)); simpl; intros; subst; red; intros; trivial.
   unfold Meq in H1; rewrite H1; trivial.
   destruct (Var.eq_dec v x).
   inversion e0; simpl.
   repeat rewrite Mem.get_upd_same.
    apply not_fv_eeq_mem with d; trivial.
   repeat rewrite Mem.get_upd_diff; trivial; apply H1; trivial.
      (* Random *)
   match goal with 
   |- equiv _ _ _ _ (if ?b then _ else _) _ => case_eq b; intros end.
   destruct dep; simpl in H; try discriminate.
   assert (Var.mkV v = r).
     generalize (Var.veqb_spec_dep v r); rewrite H; intros. 
     inversion H0; trivial.
   inversion H0; subst.
   case_eq (T.eq_dec t t); intros.
   rewrite (T.UIP_refl e). 
   rewrite (T.inj_pair2 H3).
   replace (if Var.veqb r d then false else false) with false; 
    [ | destruct (Var.veqb r d); trivial].
   apply equiv_cons with 
    (fun k m1 m2 => eeq_mem (Vset.add r (Vset.singleton d)) m1 m2 /\ E.eval_expr r m1 = E.eval_expr d m2).
   eapply equiv_strengthen;[ | apply equiv_random].

   Opaque Vset.add.

   case_eq (Vset.mem d (fv_distr s)); 
   simpl; unfold Meq; intros; subst; split; try red; intros; trivial.
   split; try red; intros.
   assert (Var.mkV r <> x /\ Var.mkV d <> x).
     rewrite VsetP.add_spec in H5.
     split; intro; apply H5; subst; auto with set.
   destruct H6; repeat rewrite Mem.get_upd_diff; trivial.
   repeat rewrite Mem.get_upd_same; trivial.
   apply EqObs_d_fv_expr.
   red; intros; apply H4.
   apply VsetP.singleton_mem_diff; intro.
   rewrite (H6:Var.mkV d = x) in H2; rewrite H2 in H5; trivialb.
   split; try red; intros.
   assert (Var.mkV r <> x /\ Var.mkV d <> x).
     rewrite VsetP.add_spec in H6.
     split; intro; apply H6; subst; auto with set.
   destruct H7; repeat rewrite Mem.get_upd_diff; trivial.
   apply H4. apply VsetP.singleton_mem_diff; trivial.
   repeat rewrite Mem.get_upd_same; trivial.
   eapply equiv_strengthen;[ | apply equiv_assign_r].
   intros k m1 m2 (H4,H5) tx x H6.
   destruct (Var.eq_dec r x).
     inversion e0; simpl.
     rewrite Mem.get_upd_same.
     exact H5.  
   rewrite Mem.get_upd_diff; trivial; apply H4.
   rewrite VsetP.add_spec; tauto.
   elim (T.eq_dec_r H1); trivial.
   eapply equiv_strengthen;[ | apply equiv_random].
   unfold forall_random.
   destruct dep; simpl.
   case_eq (Vset.mem d (fv_distr s)); intro; simpl.
   unfold Meq; intros; subst; split; try red; auto.
   unfold Meq; generalize (Var.veqb_spec_dep v d).
   destruct (Var.veqb v d); simpl; intros.
   inversion H1; subst.
   assert (W:= T.inj_pair2 H6); subst.
   split; trivial.
   red; apply EqObs_d_fv_expr; red; intros; apply H2.
   apply VsetP.singleton_mem_diff; intro.
   rewrite (H4:Var.mkV d = x) in H0; rewrite H0 in H3; trivialb.
   intros; apply Mem.eq_leibniz; intros (tx, x).
   destruct (VarP.eq_dec d x).
    inversion e; simpl.
    repeat rewrite Mem.get_upd_same; trivial.
    repeat rewrite Mem.get_upd_diff; trivial.
    apply H2; apply VsetP.singleton_mem_diff; trivial.
   unfold Meq in H2; rewrite H2; split; trivial.
   red; trivial.
   replace (if Var.veqb v d then false else false) with false.
   case_eq (Vset.mem d (fv_distr s)); intro; simpl; unfold Meq; intros; subst.
   red; split; red; intros; trivial.
   split; red; intros.
   apply EqObs_d_fv_expr; red; intros; apply H1.
   apply VsetP.singleton_mem_diff; intro.
   rewrite (H3:Var.mkV d = x) in H0; rewrite H0 in H2; trivialb.
   destruct (VarP.eq_dec v x).
   inversion e; simpl.
     repeat rewrite Mem.get_upd_same; trivial.
     repeat rewrite Mem.get_upd_diff; trivial.
   apply H1; trivial.
   destruct (Var.veqb v d); trivial.
   (* Cond *)
   simpl in H1.
   generalize (H dep) (H0 dep) H1; clear H H0 H1;
   destruct (alloc_c_aux alloc_i c1 dep) as (dep1, c1a);
   destruct (alloc_c_aux alloc_i c2 dep) as (dep2, c2a); intros.
   inversion H1; clear H1; subst.
   apply equiv_cond.
   eapply equiv_strengthen; [ | apply H]; trivial.
   intros k m1 m2 (H1,H2).
   destruct dep1; simpl in H1; trivial.
   destruct dep2; simpl in H1; unfold Meq in H1; subst.
   simpl; red; trivial.
   destruct (Vset.mem d (fv_expr b)); trivial.
   simpl in H1|-*; unfold Meq in H1; rewrite H1; red; trivial.
   eapply equiv_strengthen; [ | apply H0]; trivial.
   intros k m1 m2 (H1,H2).
   destruct dep1; simpl in H1; trivial.
   unfold Meq in H1; subst; destruct dep2; simpl; try red; trivial.
   clear H2; destruct dep2; simpl in H1; subst; simpl; trivial.
   destruct (Vset.mem d (fv_expr b)); trivial.
   simpl in H1|-*; unfold Meq in H1; rewrite H1; red; trivial.
   destruct (orb dep1 dep2); simpl.
   unfold Meq; intros; subst; trivial. 
   case_eq (Vset.mem d (fv_expr b)); simpl; unfold Meq; intros; subst; trivial.
   rewrite (not_fv_eeq_mem _ H1 H2); trivial.
   (* While *)
   simpl in H0.
   generalize (H (if Vset.mem d (fv_expr b) then true else dep)) H0.
   clear H0; destruct 
    (alloc_c_aux alloc_i c
     (if Vset.mem d (fv_expr b) then true else dep)) as (depc,ca).
   case_eq (orb (if Vset.mem d (fv_expr b) then true else dep) (Datatypes.negb depc)); intros.
   inversion H2; clear H2; subst.
   eapply equiv_weaken; [ | apply equiv_while].
   intros k m1 m2 [H2 _].
   destruct dep.
   replace true with (if Vset.mem d (fv_expr b) then true else true); trivial.
   destruct (Vset.mem d (fv_expr b)); trivial.
   destruct (Vset.mem d (fv_expr b)); trivial.
   rewrite (H2 : m1 = m2); simpl; red; intros; trivial.
   case_eq (Vset.mem d (fv_expr b)); simpl; unfold Meq; intros; subst; trivial.
   destruct dep; simpl in H3; unfold Meq in H3; subst; trivial.
   rewrite (not_fv_eeq_mem _ H2 H3); trivial.
   eapply equiv_strengthen;[ | apply H1; trivial].
   intros k m1 m2 (H2, _).
   destruct (if Vset.mem d (fv_expr b) then true else dep).
   simpl in H2; unfold Meq in H2; subst.
   destruct depc; simpl; try red; trivial.
   destruct depc; trivial; try discriminate.
   clear H1.
   case_eq (Vset.mem d (fv_expr b)); intros Heq; 
    rewrite Heq in H0; try discriminate H0.
   destruct dep; try discriminate H0.
   destruct depc; try discriminate H0; clear H0.
   generalize (H true) H2; clear H H2.
   destruct (alloc_c_aux alloc_i c true); intros.
   inversion H2; clear H2; subst; simpl.
   eapply equiv_weaken; [ | apply equiv_while].
   intros k m1 m2 (H1,_); unfold Meq in *; subst; red; trivial.
   unfold Meq; intros; subst; trivial.
   eapply equiv_strengthen;[ | apply H; trivial].
   unfold Meq; intros k m1 m2 [H1 _]; subst; 
    destruct b0; simpl; try red; trivial.

   (* Call *)
   inversion H; clear H; subst.
   assert 
    (equiv (alloc_pred true) E [x <c- f with a] 
     E (if andb (Datatypes.negb dep) (Var.veqb x r)
      then 
       match T.eq_dec t0 t with
       | left H =>
         match H in (_ = y0) return (Var.var y0 -> cmd) with
         | refl_equal => fun d0 : Var.var t0 => [d0 <c- f with a; x <- d0]
         end d
       | right _ => [x <c- f with a]
       end
      else [x <c- f with a]) (alloc_pred dep)).
   destruct dep; simpl. 
   apply equiv_eq_mem.
   case_eq (Var.veqb x r); intros. 
   assert (Var.mkV x = r).
   generalize (Var.veqb_spec_dep x r); rewrite H; intros. 
   inversion H0; trivial.
   inversion H0; subst.
   case_eq (T.eq_dec t t); intros.
   rewrite (T.UIP_refl e). 
   rewrite (T.inj_pair2 H3).
   assert (W:= T.inj_pair2 H3); subst.
   apply equiv_cons with 
    (fun k m1 m2 => eeq_mem (Vset.add r (Vset.singleton d)) m1 m2 /\
     E.eval_expr r m1 = E.eval_expr d m2).
   apply equiv_call with (Pf := Meq) (Qf := Meq); 
    unfold Meq; intros; subst; trivial.
   split.
   red; intros.
   assert (Var.mkV r <> x /\ Var.mkV d <> x).
   rewrite VsetP.add_spec in H2; split; intro; apply H2; auto.
   right; apply Vset.singleton_correct; trivial. 
   destruct H4.
   case_eq (Var.is_global x); intros.
   repeat rewrite return_mem_global; trivial.
   assert (Var.is_local x) by (unfold Var.is_local; rewrite H6; trivial).
   repeat rewrite return_mem_local; trivial.
   simpl; repeat rewrite return_mem_dest; trivial.
   apply equiv_eq_mem.
   eapply equiv_strengthen; [ | apply equiv_assign_r].
   intros k m1 m2 (H4,H5) tx x H6.
   destruct (Var.eq_dec r x).
   inversion e0; simpl.
   rewrite Mem.get_upd_same.
   exact H5.
   rewrite Mem.get_upd_diff; trivial; apply H4.
   rewrite VsetP.add_spec; tauto.
   eapply equiv_weaken; [ | apply equiv_eq_mem].
   unfold Meq; intros; subst; red; trivial. 
   eapply equiv_weaken; [ | apply equiv_eq_mem].
   unfold Meq; intros; subst; red; trivial. 
   destruct (pi f); try apply H.
   case_eq (pi_mod p[<=?]pi_output p); intro; try apply H.
   case_eq (Vset.mem d (fv_args a)); intro; try apply H.
   case_eq (Vset.mem d (pi_input p)); intro; try apply H.
   assert (forall k (m1 m2:Mem.t k), alloc_pred false m1 m2 ->
    dmap (P1:=E.expr) _ (fun t e => E.eval_expr e m1) a = dmap (P1:=E.expr) _ (fun t e => E.eval_expr e m2) a).
   intros.
   generalize  (Proc.targs f) a (fv_args a) H1 (@depend_only_fv_args _ a).
   induction a0; simpl; intros; trivial.
   rewrite (IHa0 t1); auto.
   replace (E.eval_expr p0 m2) with (E.eval_expr p0 m1); trivial.
   apply H5; auto.
   red; intros; apply H3.
   apply VsetP.singleton_mem_diff; intro.
   rewrite (H7 : Var.mkV d = x0) in H4; rewrite H4 in H6; trivialb.
   case_eq (andb (Datatypes.negb dep) (Var.veqb x r)); intros.
   destruct dep; try discriminate; simpl in H4.
   assert (H5 := Var.veqb_spec_dep x r); rewrite H4 in H5.
   inversion H5; subst.
   assert (W:= T.inj_pair2 H9); subst.
   case_eq (T.eq_dec t t); intros.
   rewrite (T.UIP_refl e).
   replace (if Var.veqb r d then false else false) with false;
    [ | destruct (Var.veqb r d); trivial]; simpl.
   apply equiv_cons with 
    (fun k m1 m2 => eeq_mem (Vset.add r (Vset.singleton d)) m1 m2 /\ 
     E.eval_expr r m1 = E.eval_expr d m2).
   eapply equiv_weaken; [ | eapply alloc_call; eauto].
   intros k m1 m2 (W1,W2); split; trivial.
   assert (Vset.add d (Vset.singleton d) [=] Vset.singleton d).
   rewrite VsetP.eq_spec; split; auto with set.
   apply Vset.subset_complete; intro; rewrite VsetP.add_spec; intuition.
   red; intros; apply W1; rewrite H7; trivial. 
   eapply equiv_strengthen;[ | apply equiv_assign_r]. 
   intros k m1 m2 (W1,W2) tx x W3. 
   destruct (Var.eq_dec r x); subst.
   inversion e0; simpl.
   rewrite Mem.get_upd_same.
   exact W2.
   rewrite Mem.get_upd_diff; trivial.
   apply W1; rewrite VsetP.add_spec; tauto.
   elim (T.eq_dec_r H6); trivial.
   case_eq (Var.veqb x d); intros; simpl.
   eapply equiv_weaken; [ | eapply alloc_call; eauto].
   intros k m1 m2 (W1,W2).
   assert (m1 = m2).
   apply Mem.eq_leibniz; intros (tx0, x0).
   destruct (Var.eq_dec x x0).
   inversion e; exact W2.
   apply W1; repeat rewrite VsetP.add_spec; intuition.
   assert (W:= Var.veqb_spec_dep x d); rewrite H5 in W; inversion W; subst.
   clear W; assert (W:= T.inj_pair2 H10); subst.
   apply Vset.singleton_complete in H6.
   apply n0; trivial. 
   destruct dep; trivial; intro; rewrite H6; trivial.
   destruct dep; trivial.
   eapply equiv_weaken; [ | eapply alloc_call; eauto].
   simpl; intros k m1 m2 (W1,W2); red; intros.
   destruct (VarP.eq_dec x x0).
   inversion e; simpl; trivial.
   apply W1; repeat rewrite VsetP.add_spec; tauto.
   
   (* nil *)
   inversion H; apply equiv_nil.
   
   (* cons *)
   simpl alloc_c_aux in H1.
   generalize (H0 dep); clear H0.
   destruct (alloc_c_aux alloc_i c dep) as (depc',ca').
   generalize (H depc'); clear H.
   destruct (alloc_i i depc') as (depi, ia).
   inversion H1; clear H1; subst; intros.
   change (i::c) with ([i]++c); apply equiv_app with (alloc_pred depc'); auto.
  Qed.

  Definition alloc_c c := snd (alloc_c_aux alloc_i c true).
  
  Definition alloc_c_out (c:cmd) (O:Vset.t) : cmd :=
   snd (alloc_c_aux alloc_i c (Vset.mem d O)).
  
  Lemma alloc_c_correct : forall c,
   equiv Meq E c E (alloc_c c) Meq.
  Proof. 
   unfold alloc_c; intros; destruct alloc_spec.
   generalize (H0 c true); destruct (alloc_c_aux alloc_i c true); simpl.
   intros H1; eapply equiv_strengthen;[ | eapply H1; eauto].
   unfold Meq; intros; subst; destruct b; simpl; try red; intros; trivial. 
  Qed.
   
  Lemma alloc_c_out_correct : forall c O,
   equiv Meq E c E (alloc_c_out c O) (kreq_mem O).
  Proof. 
   unfold alloc_c_out; intros; destruct alloc_spec.
   generalize (H0 c (Vset.mem d O)).
   destruct (alloc_c_aux alloc_i c (Vset.mem d O)) as (b,ca'); simpl.
   intros H1; apply equiv_strengthen with (alloc_pred b).
   unfold Meq; intros; subst; destruct b; simpl; try red; intros; trivial. 
   eapply equiv_weaken;[ | eapply H1; eauto].
   unfold kreq_mem; intros; red; intros.
   generalize H2.
   case_eq (Vset.mem d O); simpl; unfold Meq; intros; subst; trivial.
   apply H5; apply VsetP.singleton_mem_diff; intro.
   rewrite (H6:Var.mkV d= x) in H4; rewrite H4 in H3; trivialb.
  Qed.
 
 End ALLOC.
  
 Lemma alloc_c_equiv_l : forall t (r d:Var.var t) 
  P E1 (pi1:eq_refl_info E1) c1 c1' E2 c2 Q,
  alloc_c pi1 r d c1 = c1' ->
  equiv P E1 c1' E2 c2 Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.   
  intros; apply equiv_trans_eq_mem_l with trueR E1 c1'; trivial.
  apply equiv_strengthen with Meq.   
  unfold Meq; intros k m1 m2 (H1, _); trivial.
  rewrite <- H.
  apply alloc_c_correct.
  red; red; trivial.
 Qed.
 
 Lemma alloc_c_equiv_r : forall t (r d:Var.var t) 
  P E1 c1 E2 (pi2:eq_refl_info E2) c2 c2' Q,
  alloc_c pi2 r d c2 = c2' ->
  equiv P E1 c1 E2 c2' Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.   
  intros; apply equiv_trans_eq_mem_r with trueR E2 c2'; trivial.
  apply equiv_strengthen with Meq.   
  intros k m1 m2 (H1, _); trivial.
  rewrite <- H.
  apply alloc_c_correct.
  red; red; trivial.
 Qed.

 Lemma alloc_c_out_equiv_l : forall t (r d:Var.var t) 
  (P:mem_rel) E1 (pi1:eq_refl_info E1) c1 c1' E2 c2 X1 X2 Q,
  decMR P ->
  depend_only_rel Q X1 X2 ->
  alloc_c_out pi1 r d c1 X1 = c1' ->
  equiv P E1 c1' E2 c2 Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof. 
  intros.
  apply equiv_depend_only_l with (2:= H) (4:= H1); trivial.
  rewrite <- H0; apply alloc_c_out_correct.
 Qed.

 Lemma alloc_c_out_equiv_r : forall t (r d:Var.var t) 
  (P:mem_rel) E1 c1 E2 (pi2:eq_refl_info E2) c2 c2' X1 X2 Q,
  decMR P ->
  depend_only_rel Q X1 X2 ->
  alloc_c_out pi2 r d c2 X2 = c2' ->
  equiv P E1 c1 E2 c2' Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof. 
  intros.
  apply equiv_depend_only_r with (2:= H) (4:= H1); trivial.
  rewrite <- H0; apply alloc_c_out_correct.
 Qed.

End Make. 
