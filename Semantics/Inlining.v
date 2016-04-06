(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * Inlining.v : Reflection based implementation of inlining *)


Require Export Alloc.

Set Asymmetric Patterns.

Module Make (SemO:SEM_OPT).

 Module Al := Alloc.Make SemO.
 Export Al.

 Section INLINE.
   
  Variables (n:positive) (E:env) (pi:eq_refl_info E).

  Fixpoint assign_params_aux (tv ta:list T.type) (lv:dlist Var.var tv) (la:dlist E.expr ta) {struct lv} : cmd :=
   match lv, la with
   | dcons tx tv x lv, dcons te ta e la =>
     match T.eq_dec tx te with
     | left Heq =>
       match Heq in (_ = y0) return E.expr y0 -> cmd with
       | refl_equal => fun e => (x<-e) :: assign_params_aux tv ta lv la
       end e
     | right _ => assign_params_aux tv ta lv la
     end 
   | _, _ => nil
   end.

  Definition assign_params l (lv:dlist Var.var l) (la:dlist E.expr l) :=
   assign_params_aux l l lv la.

  Definition inline1 t (d:Var.var t) (f:Proc.proc t) (arg:E.args (Proc.targs f)) O :=
   let body := proc_body E f in
    match modify pi Vset.empty body with
    | Some X =>
       let lO := get_locals O in
       if Vset.disjoint lO (get_locals X) then
         let lv := proc_params E f in
         if dforallb (P:= Var.var) (fun tx x => negb (Vset.mem x lO)) lv then
          let res := proc_res E f in
          let Of := fv_expr_extend res (Vset.remove d (get_globals O)) in
          if Vset.disjoint lO Of then
            match eqobs_in n pi body Of with
            | Some II =>
              match needed_args_refl lv arg (get_locals II) (get_globals II) with
              | Some III => 
                let Li := get_locals III in
                if dforallb (P:=Var.var) (fun tx  x => negb (Vset.mem x Li)) lv then
                 Some (Vset.union lO III,  assign_params (Proc.targs f) lv arg ++ (body ++ [d <- (proc_res E f)]))
                else None
              | _ => None
              end
            | _ => None
            end
           else None
         else None 
       else None
    | _ => None
    end.

  Section ASSIGN_PARAM.

   Variable k : nat.
  
   Fixpoint assign_param_mem (m:Mem.t k) (tv ta:list T.type) (lv:dlist Var.var tv) (le:E.args ta) {struct lv} : Mem.t k:=
    match lv, le with  
    | dcons tx tv x lv, dcons te ta e la =>
      match T.eq_dec tx te with
      | left Heq =>
        match Heq in (_ = y0) return E.expr y0 -> Mem.t k with
        | refl_equal => fun e => assign_param_mem (m{!x<-- E.eval_expr e m!}) tv ta lv la
        end e
      | right _ => assign_param_mem m tv ta lv la
      end 
    | _, _ => m
    end.

   Lemma assign_param_correct : forall tv (lv:dlist Var.var tv) ta 
    (le:E.args ta) m f,
    mu ([[assign_params_aux tv ta lv le]] E m) f == 
    f (assign_param_mem m tv ta lv le).
   Proof.
    induction lv; simpl; intros.
    rewrite (@deno_nil_elim k); trivial.
    destruct le.
    rewrite (@deno_nil_elim k); trivial.
    case_eq (T.eq_dec a a0); intros; auto.
    generalize e0 e; rewrite <- e0; intros.
    rewrite (T.UIP_refl e1).
    rewrite (@deno_cons_elim k).
    rewrite Mlet_simpl.
    rewrite deno_assign_elim; trivial.
   Qed.

   Lemma assign_param_mem_global : forall t (x:Var.var t), 
    Var.is_global x ->
    forall tv (lv:dlist Var.var tv) ta (la:E.args ta) m, (forall t (x:Var.var t), DIn _ x lv -> Var.is_local x) ->
     assign_param_mem m tv ta lv la x = m x.
   Proof.
    induction lv; simpl; trivial.
    destruct la; intros; trivial.
    case_eq (T.eq_dec a a0); intros; auto.
    generalize e0 e; rewrite <- e0; intros.
    rewrite (T.UIP_refl e1).
    rewrite IHlv; auto.
    rewrite Mem.get_upd_diff; trivial.
    intro Heq; rewrite <- Heq in H.
    assert (Var.is_local p) by (apply H0; auto).
    unfold Var.is_local in H2; rewrite H in H2; discriminate.
   Qed.

   Lemma assign_param_get_arg_None : forall t (x:Var.var t)  tv (lv:dlist Var.var tv) ta (la:E.args ta) m,
    get_arg x lv la = None ->
    assign_param_mem m tv ta lv la x = m x.
   Proof.
    induction lv; simpl; trivial.
    destruct la; simpl; trivial.
    generalize (IHlv l0 la); destruct (get_arg x lv la); try (intros; discriminate).
    generalize (Var.veqb_spec_dep x p); destruct (Var.veqb x p).
    intros Hd; inversion Hd; subst; simpl.
    case_eq (T.eq_dec a0 a).
    intros e0; generalize e0 e; rewrite e0.
    intros Heq; rewrite (T.UIP_refl Heq); intros; discriminate.
    case_eq (T.eq_dec a a0).
    intros e0; generalize e0 e; rewrite <- e0; intros.
    elim (T.eq_dec_r H0); trivial.
    tauto.
    case_eq (T.eq_dec a a0); trivial.
    intros e0; generalize e0 e; rewrite <- e0; intros.
    rewrite (T.UIP_refl e1).
    rewrite H1; trivial.
    rewrite Mem.get_upd_diff; trivial.
    intros Heq; apply H0; inversion Heq; trivial.
   Qed.

   Lemma assign_param_mem_local : forall I t (x:Var.var t)  tv (lv:dlist Var.var tv) ta (la:E.args ta) m,
    (forall t (x:Var.var t), DIn _ x lv -> Var.is_local x) ->
    dforallb (fun t (x:Var.var t)  => Datatypes.negb (Vset.mem x (get_locals I)))
    lv = true ->
    match get_arg x lv la with
    | Some e =>  EqObs_e I e e -> assign_param_mem m _ _ lv la x = E.eval_expr e m
    | None => True
    end.
   Proof.
    induction lv; simpl; trivial.
    destruct la; simpl; trivial. 
    generalize (IHlv _ la); clear IHlv; case_eq (get_arg x lv la); intros.
    case_eq (T.eq_dec a a0); intros. 
     generalize e1 e; rewrite <- e1; intros. 
     rewrite (T.UIP_refl e2).
    rewrite H0; auto.
    apply H3; red; intros.
    rewrite Mem.get_upd_diff; trivial.
    intro W; rewrite W in H2.
    replace (Vset.mem x0 (get_locals I)) with true in H2; try discriminate.
    symmetry; change (Vset.mem x0 (get_locals I)); apply get_locals_complete; auto.
    apply H1; inversion W; simpl; auto.
    destruct ((Vset.mem p (get_locals I))); trivial; discriminate.
    apply H0; auto.
    destruct ((Vset.mem p (get_locals I))); trivial; discriminate.
    generalize (Var.veqb_spec_dep x p); destruct (Var.veqb x p); trivial; intros.
    destruct (T.eq_dec a0 t); trivial.
    generalize e0 e ; rewrite e0.
    intros e1 e2; rewrite (T.UIP_refl e1); intros.
    case_eq (T.eq_dec a t); intros; trivial.
    generalize e3 e2 x H H3; rewrite <- e3; intros.
    rewrite (T.UIP_refl e4).
    rewrite assign_param_get_arg_None; trivial.
    rewrite (T.eq_dep_eq H7).
    rewrite Mem.get_upd_same; trivial. 
    rewrite assign_param_get_arg_None; trivial.
    elim (T.eq_dec_r H5). 
    inversion H3; trivial.
   Qed.

  End ASSIGN_PARAM.


  Lemma inline1_correct : forall t (d:Var.var t) f arg O I c, 
   inline1 t d f arg O = Some (I, c) ->
   EqObs I E [d<c- f with arg] E c O.
  Proof. 
   unfold inline1; intros t d f arg O I c.
   generalize (modify_correct pi (proc_body E f) Vset.empty);
    destruct (modify pi Vset.empty (proc_body E f)); try (intros; discriminate).
   intro; case_eq (Vset.disjoint (get_locals O) (get_locals t0)); intro; try (intros; discriminate).
   generalize (fun I => @eqobs_in_correct n E  pi (proc_body E f) I 
    (fv_expr_extend (proc_res E f) (Vset.remove d (get_globals O)))).
   destruct (eqobs_in n pi (proc_body E f)
    (fv_expr_extend (proc_res E f) (Vset.remove d (get_globals O)))); try (intros;
     discriminate).
   intro.
   case_eq (dforallb
    (fun (tx : T.type) (x : Var.var tx) => Datatypes.negb (Vset.mem x (get_locals O)))
    (proc_params E f)); intro; try (intros; discriminate).
   match goal with |- (if ?t then _ else _) = _ -> _ =>
    case_eq t; intro Hdisj; try (intros; discriminate) end.
   generalize (@needed_args_refl_correct (get_locals t1) _
    (proc_params E f) _ arg (get_globals t1)).
   destruct (needed_args_refl (proc_params E f) arg (get_locals t1) (get_globals t1));
    try (intros; discriminate).
   intro; case_eq 
    (dforallb
     (fun (tx : T.type) (x : Var.var tx) => Datatypes.negb (Vset.mem x (get_locals t2)))
     (proc_params E f)); intros; try discriminate.
   inversion H5; clear H5; subst.
   intro k.
   destruct (H1 _ (refl_equal _) k) as (D,HD).
   assert (H1' := H1 _ (refl_equal _) k); clear H1; rename H1' into H1.
   destruct (H3 _ (refl_equal _)); clear H3.
   set (Of:= fv_expr_extend (proc_res E f) (Vset.remove d (get_globals O))) in *.
   assert (HM:Modify E (Vset.union Of t0) (proc_body E f)). 
   apply Modify_weaken with (1:= H _ (refl_equal _)); auto with set.
   exists (fun m1 m2 =>
    Mlet (D (init_mem E f arg m1) (assign_param_mem k m2 _ _ (proc_params E f) arg))
    (fun p => 
     let m1' := (init_mem E f arg m1){!Vset.union Of t0 <<- fst p!} in
      let m2' := (assign_param_mem k m2 _ _ (proc_params E f) arg){!Vset.union Of t0 <<- snd p!} in
       Munit (return_mem E d f m1 m1' ,m2' {!d<-- E.eval_expr (proc_res E f) m2'!}))).
   unfold kreq_mem; intros m1 m2 Heq.
   assert ((init_mem E f arg m1) =={t1} (assign_param_mem k m2 _ _ (proc_params E f) arg)).
   red; intros.
   case_eq (Var.is_global x); intros.
   rewrite init_mem_global; trivial.
   rewrite assign_param_mem_global; trivial.
   apply Heq; rewrite VsetP.union_spec; right.
   apply Vset.subset_correct with (1:= H6).
   apply get_globals_complete; trivial.
   exact (proc_params_local E f).
   assert (Vset.mem x (get_locals t1)).
   apply get_locals_complete; trivial.
   unfold Var.is_local; rewrite H7; trivial.
   generalize (H5 _ _ H8).
   case_eq (get_arg x (proc_params E f) arg); intros; try (elimtype False; trivial; fail).
   generalize (lookup_init_mem E f arg m1 x); rewrite H9; intros H11; rewrite H11; clear H11.
   generalize (assign_param_mem_local k (Vset.union (get_locals O) t2)
    _ x _ (proc_params E f) _ arg m2); rewrite H9; intros.
   rewrite H11; auto; clear H11.
   apply H10; apply req_mem_weaken with (2:= Heq); auto with set.
   exact (proc_params_local E f).
   generalize (Proc.targs f) (proc_params E f) H2 H4.
   induction v; simpl; trivial.
   case_eq (Vset.mem p (get_locals O)); simpl; try (intros; discriminate).
   case_eq (Vset.mem p (get_locals t2)); simpl; intros; try discriminate.
   replace (Vset.mem p (get_locals (Vset.union (get_locals O) t2))) with false; auto.
   case_eq (Vset.mem p (get_locals (Vset.union (get_locals O) t2))); intros; trivial.
   assert (Vset.mem p (Vset.union (get_locals O) t2)).
   apply Vset.subset_correct with (2:= H15).
   apply get_locals_subset.
   rewrite VsetP.union_spec in H16; destruct H16.
   rewrite H12 in H16; discriminate H16. 
   assert (W:= get_locals_complete _ _ H16 (get_locals_spec _ _ H15));
    rewrite H11 in W; discriminate W.
   red; intros.
   apply H10; apply req_mem_weaken with (2:= H11); auto with set.
   assert (HD' := HD _ _ H3); clear HD.
   rewrite deno_call; rewrite <- app_ass; repeat rewrite deno_app.
   constructor; simpl; intros.
   rewrite (HD'.(l_fst) (fun x => f0 (return_mem E d f m1 (init_mem E f arg m1 {!Vset.union Of t0 <<- x!})))).
   symmetry; refine (Modify_deno_elim HM _ _).
   unfold assign_params; rewrite (assign_param_correct k).
   rewrite (Modify_deno_elim (k:=k) HM).
   rewrite <- HD'.(l_snd); trivial.
   apply (mu_stable_eq (D (init_mem E f arg m1) (assign_param_mem k m2 _ _ (proc_params E f) arg))).
   simpl; apply ford_eq_intro; intros p.
   rewrite (deno_assign_elim (k:=k)); trivial.
   (* range *)
   red; intros; simpl.
   apply HD'.(l_range).
   unfold prodP; intros (m1',m2'); simpl; intros.
   apply H7; red; simpl.
   red; intros.
   destruct (Var.eq_dec d x).
   inversion e; simpl.
   rewrite return_mem_dest, Mem.get_upd_same.
   apply EqObs_e_fv_expr.
   assert (m1' =={fv_expr (proc_res E f)} m2').
   apply req_mem_weaken with Of; trivial.
   unfold Of; rewrite union_fv_expr_spec; auto with set.
   red; intros.
   assert (Vset.mem x0 (Vset.union Of t0)).
   unfold Of; rewrite  union_fv_expr_spec; auto with set.
   repeat rewrite update_mem_in; auto.
   rewrite Mem.get_upd_diff; auto.
   case_eq (Var.is_global x); intros.
   rewrite return_mem_global; trivial.
   assert (Vset.mem x Of).
   unfold Of; rewrite union_fv_expr_spec.
   assert (W:= get_globals_complete _ _ H9 H10); auto with set.
   repeat rewrite update_mem_in; auto with set. 
   assert (Var.is_local x) by (unfold Var.is_local; rewrite H10; trivial).
   rewrite return_mem_local; trivial.
   rewrite update_mem_notin.
   rewrite assign_param_get_arg_None.
   apply Heq.
   rewrite VsetP.union_spec; left; apply get_locals_complete; trivial.
   assert (forall (l : list T.type) (v : var_decl l),
    dforallb
    (fun (tx : T.type) (x0 : Var.var tx) =>
     Datatypes.negb (Vset.mem x0 (get_locals O))) v = true ->
    forall l0 (arg0 : E.args l0), get_arg x v arg0 = None); auto.
   induction v; simpl; trivial.
   destruct arg0; trivial.
   case_eq (Vset.mem p (get_locals O)); simpl; intros; try discriminate.
   rewrite H13 in H12; discriminate.
   rewrite IHv; trivial.
   generalize (Var.veqb_spec_dep x p); destruct (Var.veqb x p); intros; trivial.
   generalize (get_locals_complete _ _ H9 H11).
   inversion H14; subst.
   rewrite (T.inj_pair2 H18), H13; intros; discriminate.
   rewrite H13 in H12; trivial.
   intros H12; rewrite VsetP.union_spec in H12; destruct H12.
   apply (@VsetP.disjoint_mem_not_mem _ _ Hdisj x); trivial.
   apply get_locals_complete; trivial.
   apply (@VsetP.disjoint_mem_not_mem _ _ H0 x);
    apply get_locals_complete; trivial.
   destruct (dforallb
    (fun (tx : T.type) (x : Var.var tx) =>
     Datatypes.negb (Vset.mem x (get_locals O))) (proc_params E f)); try (intros; discriminate).
   destruct (Vset.disjoint (get_locals O)
    (fv_expr_extend (proc_res E f) (Vset.remove d (get_globals O)))); intros; discriminate.
  Qed.

  Definition is_var t (e:E.expr t) : option (Var.var t) :=
   match e in E.expr t0 return option (Var.var t0) with
   | E.Evar t x => Some x
   | _ => None
   end.
 
  Lemma is_var_correct : forall t (e:E.expr t) x, 
   is_var t e = Some x -> e = E.Evar x.
  Proof. 
   destruct e; intros x H; inversion H; trivial. 
  Qed.
 

  Section AUX.

   Variable inline_i : I.instr -> Vset.t -> option (Vset.t*cmd).

   Fixpoint inline_aux (c:cmd) (O:Vset.t) {struct c} :option (Vset.t*cmd) :=
    match c with
    | nil => Some (O,nil)
    | i::c =>
      match inline_aux c O with
      | Some (IO, c') =>
        match inline_i i IO with
        | Some (I1,i') => Some (I1, i'++c')
        | None => None
        end
      | None => None
      end
    end.

  End AUX.
 
  Variable t : T.type.
  Variable g : Proc.proc t.

  Fixpoint inline_i (i:I.instr) (O:Vset.t) {struct i} : option (Vset.t*cmd) :=
   match i with
   | I.Cond e c1 c2 =>
     let r1 := inline_aux inline_i c1 O in
     let r2 := inline_aux inline_i c2 O in
      match r1, r2 with
      | Some (I1, c1'), Some (I2,c2') =>
        Some (fv_expr_extend e (Vset.union I1 I2), [If e then c1' else c2'])
      | _, _ => None
      end
   | I.Call t d f arg =>
     if Proc.eqb f g then 
      match inline1 t d f arg O with
      | Some (I1,c0) =>
        let c1 :=
         match is_var t (proc_res E f) with
         | Some r => alloc_c pi r d c0 
         | None => c0
         end in
         Some (I1, c1)
         (* let c2 := Cse.optimize n pi c1  in 
         let c3 :=
          match dead_code n pi c2 O with
          | Some c3 => c3
          | _ => c2
         end 
         in Some (I1, c3) *)
      | None => None
      end
     else 
      match eqobs_in_i n pi i O with
      | Some I1 => Some (I1, [i])
      | None => None
      end
   | _ => 
     match eqobs_in_i n pi i O with
     | Some I1 => Some (I1, [i])
     | None => None
     end
   end.

  Lemma inline_aux_correct : 
   (forall i O I i', inline_i i O = Some (I, i') -> EqObs I E [i] E i' O) /\  
   (forall c O I c', inline_aux inline_i c O = Some (I,c') -> EqObs I E c E c' O).
  Proof.
   apply I.cmd_ind2.
   unfold inline_i; intros i O I i'.
   case_eq (eqobs_in_i n pi (I.Instr i) O); intros; try discriminate.
   inversion H0; clear H0; subst.
   apply eqobs_in_i_correct with (1:= H).
   intros b c1 c2 H1 H2 O I i'; simpl.
   case_eq (inline_aux inline_i c1 O); try (intros; discriminate).
   destruct p as (I1,c1'); intro.
   case_eq (inline_aux inline_i c2 O); intros; try discriminate.
   destruct p as (I2,c2'); inversion H3; clear H3; subst.
   unfold EqObs; apply equiv_cond.
   eapply equiv_strengthen; [ | apply (H1 _ _ _ H)].
   unfold kreq_mem; intros k m1 m2 (W,_); apply req_mem_weaken with (2:=W).
   rewrite union_fv_expr_spec; auto with set.
   eapply equiv_strengthen; [ | apply (H2 _ _ _ H0)].
   unfold kreq_mem; intros k m1 m2 (W,_); apply req_mem_weaken with (2:=W).
   rewrite union_fv_expr_spec; auto with set.
   unfold kreq_mem; intros; replace (E.eval_expr b m2) with (E.eval_expr b m1); trivial.
   apply EqObs_e_fv_expr; apply req_mem_weaken with (2:=H3).
   rewrite union_fv_expr_spec; auto with set.
   intros b c _ O I i'; unfold inline_i.
   case_eq  (eqobs_in_i n pi  (while b do c) O); intros; try discriminate.
   inversion H0; clear H0; subst.
   apply eqobs_in_i_correct with (1:= H).
   (* Call *)
   simpl; intros t0 x f args O I i'.
   generalize (Proc.eqb_spec_dep f g); destruct (Proc.eqb f g); intro; subst.
   inversion H; subst.
   assert (W:= T.inj_pair2 H3); clear H H2 H3; subst.
   case_eq (inline1 t x g args O); try (intros; discriminate).
   intros (I1,c0) H H0; inversion H0; clear H0; subst.
   set (c1:= match is_var t (proc_res E g) with
             | Some r => alloc_c pi r x c0
             | None => c0
             end).
   unfold EqObs; apply equiv_trans_eq_mem_r with trueR E c0.
   simplMR.
   apply equiv_sym; auto.
   unfold c1; clear c1; destruct (is_var t (proc_res E g)) as [r|].
   apply alloc_c_correct.
   apply equiv_eq_mem.
   apply inline1_correct; trivial.
   red; red; trivial.
   change (
    match eqobs_in_i n pi (x <c- f with args) O with
    | Some I1 => Some (I1,  [x <c- f with args])
    | None => None
    end = Some (I,i') -> EqObs I E [x <c- f with args] E i' O).
   case_eq (eqobs_in_i n pi  (x <c- f with args) O); intros; try discriminate.
   inversion H1; clear H1; subst.
   apply eqobs_in_i_correct with (1:= H0).
   (* nil and cons *)
   simpl; intros O I c' H; inversion H.
   unfold EqObs; apply equiv_nil.
   simpl; intros i c Hi Hc O I c'.
   case_eq (inline_aux inline_i c O); try (intros; discriminate).
   destruct p as (IO,c''); case_eq (inline_i i IO); try (intros; discriminate).
   destruct p as (I1, i'); intros. 
   inversion H1; clear H1; subst.
   unfold EqObs; change (i::c) with ([i]++c);
    apply equiv_app with (1:= Hi _ _ _ H) (2:= Hc _ _ _ H0).
  Qed.

  Definition inline c O := 
   match inline_aux inline_i c O with
   | Some (_, c') => c'
   | _ => c
   end.

  Lemma inline_correct : forall c O c',
   inline c O = c' ->
   equiv Meq E c E c' (kreq_mem O).
  Proof.
   intros c O; unfold inline.
   case_eq (inline_aux inline_i c O); intros.
   destruct p; subst.
   apply equiv_strengthen with (kreq_mem t0).
   unfold kreq_mem, Meq; intros; subst; apply req_mem_refl.
   destruct inline_aux_correct.
   exact (H1 c O t0 c' H).
   subst; apply equiv_weaken with Meq.
   unfold Meq,kreq_mem; intros; subst; apply req_mem_refl.
   apply equiv_eq_mem.
  Qed.

 End INLINE.

 Lemma inline_l_equiv : forall n t (f:Proc.proc t) (P : mem_rel)
  E1 (pi1:eq_refl_info E1) c1 c1' E2 (pi2:eq_refl_info E2) c2 Q X1 X2,
  inline n E1 pi1 t f c1 X1 = c1' ->
  decMR P ->
  depend_only_rel Q X1 X2 ->
  equiv P E1 c1' E2 c2 Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  intros.         
  apply equiv_depend_only_l with E1 c1' X1 X2; auto.
  eapply inline_correct; eauto.
 Qed.

 Lemma inline_r_equiv : forall n t (f:Proc.proc t) (P : mem_rel)
  E1 (pi1:eq_refl_info E1) c1 E2 (pi2:eq_refl_info E2) c2 c2' Q X1 X2,
  inline n E2 pi2 t f c2 X2 = c2' -> 
  decMR P ->
  depend_only_rel Q X1 X2 ->
  equiv P E1 c1 E2 c2' Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  intros.         
  apply equiv_depend_only_r with E2 c2' X1 X2; auto.
  eapply inline_correct; eauto.
 Qed.

 Lemma inline_para_equiv : forall n t (f:Proc.proc t) (P : mem_rel)
  E1 (pi1:eq_refl_info E1) c1 c1' E2 (pi2:eq_refl_info E2) c2 c2' Q X1 X2,
  inline n E1 pi1 t f c1 X1 = c1' ->
  inline n E2 pi2 t f c2 X2 = c2' -> 
  decMR P ->
  depend_only_rel Q X1 X2 ->
  equiv P E1 c1' E2 c2' Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  intros.         
  apply equiv_depend_only_l with E1 c1' X1 X2; auto.
  eapply inline_correct; eauto.
  apply equiv_depend_only_r with E2 c2' X1 X2; auto.
  eapply inline_correct; eauto.
 Qed.

End Make.
