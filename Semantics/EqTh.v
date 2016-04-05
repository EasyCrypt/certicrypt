(** * EqTh.v: decision procedures for determining program equivalence,
 e.g. dead code, code movement, semantic equivalence *)

Set Implicit Arguments.


Require Export While_loop.
Require Export NotModifyDec.


Module Make (Sem:SEM).
 
 Module NM_dec := NotModifyDec.Make Sem.
 Export NM_dec.

 Section EQOBS.

 Variable n : positive.
 Variable E : env.
 Variable pi : eq_refl_info E.

 (* [needed_args lv arg needed res] computes a set [I] such that [res [<=] I] 
     and [EqObs_args lv arg arg needed I] *)

 Definition needed_args ltv1 (lv1:var_decl ltv1) 
  lt1 (la1:E.args lt1) ltv2 (lv2:var_decl ltv2) lt2 (la2:E.args lt2)
  (needed:Vset.t) (res:Vset.t) :=
  Vset.fold (fun x r => 
   match r, get_arg x lv1 la1, get_arg x lv2 la2 with
   | Some r, Some a1, Some a2 =>
     if E.eqb a1 a2 then Some (fv_expr_extend a1 r)
     else None
   | _, _, _ => None
   end) needed (Some res).
 
 Definition needed_args_refl ltv (lv:var_decl ltv) lt (la:E.args lt) 
  (needed:Vset.t) (res:Vset.t) :=
  Vset.fold (fun x r =>
   match r, get_arg x lv la with
   | Some r, Some a => Some (fv_expr_extend a r)
   | _, _ => None
   end) needed (Some res).
 
 Lemma needed_args_correct : 
  forall needed ltv1 (lv1:var_decl ltv1) lt1 (la1:E.args lt1) 
   ltv2 (lv2:var_decl ltv2) lt2 (la2:E.args lt2)
   res I,
   needed_args lv1 la1 lv2 la2 needed res = Some I ->
   EqObs_args lv1 la1 lv2 la2 needed I /\ res [<=] I.
 Proof.
  intros needed ltv1 lv1 lt1 la1 ltv2 lv2 lt2 la2 res I; unfold EqObs_args.
  assert (forall (L:list Var.t), fold_left (fun r (x:Var.t) => 
   match r, get_arg x lv1 la1, get_arg x lv2 la2 with
   | Some r, Some a1, Some a2 =>
     if E.eqb a1 a2 then Some (fv_expr_extend a1 r)
     else None  
   | _, _, _ => None
   end) L None = None).
  induction L; simpl; intros; auto.
  assert (forall L R I, 
   fold_left (fun r (x:Var.t) => 
    match r, get_arg x lv1 la1, get_arg x lv2 la2 with
    | Some r, Some a1, Some a2 =>
     if E.eqb a1 a2 then Some (fv_expr_extend a1 r)
      else None  
    | _, _, _ => None
    end) L (Some R)  = Some I ->
   (forall x,
    InA (@eq _) x L ->
    match get_arg x lv1 la1 with
    | Some e1 =>
     match get_arg x lv2 la2 with
     | Some e2 => EqObs_e I e1 e2
     | None => False
     end
    | None => False
     end) /\ R[<=]I).
  rename H into ZZ. induction L; simpl; intros; auto.
  inversion_clear H; split; auto with set.
  intros x H; inversion H.
  case_eq (get_arg a lv1 la1); intros.
  case_eq (get_arg a lv2 la2); intros.
  rewrite H0 in H; rewrite H1 in H.
  assert (W:=E.eqb_spec e e0); destruct (E.eqb e e0); subst.
  destruct (IHL _ _ H); split; intros.
  inversion H4; clear H4; subst; auto.
  rewrite H0; rewrite H1. 
  apply EqObs_e_strengthen with (fv_expr e0); trivial.
  apply VsetP.subset_trans with (2:= H3).
  rewrite union_fv_expr_spec; auto with set.
  apply H2; auto.
  apply VsetP.subset_trans with (2:= H3).
  rewrite union_fv_expr_spec; auto with set.
  rewrite ZZ in H; discriminate.
  rewrite H0 in H; rewrite H1 in H; rewrite ZZ in H; discriminate.
  rewrite H0 in H; rewrite ZZ in H; discriminate.
  
  unfold needed_args; rewrite Vset.fold_spec; intros V.
  destruct (H0 _ _ _ V); split; auto.
  intros; apply (H1 x); apply Vset.elements_correct; trivial.
 Qed.

 Lemma needed_args_refl_spec : forall needed
  ltv (lv:var_decl ltv) lt (la:E.args lt) res,
  needed_args_refl lv la needed res =
  needed_args lv la lv la needed res.
 Proof.
  unfold needed_args_refl, needed_args; intros; repeat rewrite Vset.fold_spec.
  generalize (Vset.elements needed) (Some res).
  induction l; simpl; intros; trivial.
  match goal with
   |- fold_left _ l ?o1 = fold_left _ l ?o2 =>
    assert (Heq : o1 = o2);[ | rewrite Heq; trivial] end.
  destruct o; trivial.
  destruct (get_arg a lv la); trivial.
  generalize (E.eqb_spec e e); destruct (E.eqb e e); trivial.
  intro Hd; elim Hd; trivial.
 Qed.

 Lemma needed_args_refl_correct : forall needed 
  ltv (lv:var_decl ltv) lt (la:E.args lt) res I,
  needed_args_refl lv la needed res = Some I ->
  EqObs_args lv la lv la needed I /\ res [<=] I.
 Proof.
  intros needed ltv lv lt la res I; rewrite needed_args_refl_spec; apply
   needed_args_correct.
 Qed.

 (* [eqobs_in_I i O] computes a set [I] such that [EqObs_i I i i O] *)
 
 Definition eqobs_in_b (i:I.baseInstr) O :=
  match i with
  | I.Assign t x e =>
    if Vset.mem x O then  fv_expr_extend e (Vset.remove x O)
    else O
  | I.Random t x e => 
    if Vset.mem x O then  Vset.union (fv_distr e) (Vset.remove x O)
    else O
  end.

 Definition is_lossless_nm O c := 
  if is_lossless pi c then is_notmodify pi O c else false.
 
 Definition is_lossless_nm_i O i := 
  if is_lossless_i pi i then is_notmodify_i pi O i else false.
 
 Lemma is_lossless_nm_spec : forall O c,
  is_lossless_nm O c ->
  lossless E c /\ exists X, Modify E X c /\ Vset.disjoint O X.
 Proof.
  unfold is_lossless_nm; intros O c.
  generalize (is_lossless_correct pi c).
  destruct (is_lossless pi c).
  split; intros; auto.
  apply is_notmodify_correct with (1:= H0).
  intros; trivialb.
 Qed.
 
 Lemma is_lossless_nm_i_spec : forall O i,
  is_lossless_nm_i O i ->
  lossless E [i] /\ 
  exists X, Modify E X [i] /\ Vset.disjoint O X.
 Proof.
  unfold is_lossless_nm_i; intros O i.
  generalize (is_lossless_i_correct pi i);
   destruct (is_lossless_i pi i).
  split; intros; auto.
  apply is_notmodify_i_correct with (1:= H0).
  intros; trivialb.
 Qed.
 
 Fixpoint eqobs_in_i (i:I.instr) (O:Vset.t) {struct i} : option Vset.t :=
  match i with
  | I.Instr ib => Some (eqobs_in_b ib O)
  | I.Cond e c1 c2 =>
    let oI1 := List.fold_right (fun i => opt_app (eqobs_in_i i)) (Some O) c1 in
    let oI2 := List.fold_right (fun i => opt_app (eqobs_in_i i)) (Some O) c2 in
     match oI1, oI2 with
     | Some I1, Some I2 => 
       let test :=
        if Vset.eqb I1 O then
         if Vset.eqb I2 O then
          if is_lossless_nm O c1 then is_lossless_nm O c2 
           else false
          else false
         else false
        in if test then Some O else Some (fv_expr_extend e (Vset.union I1 I2))
     | _, _ => None
     end
  | I.While e c =>
    let loop O :=     
    let oI := List.fold_right (fun i => opt_app (eqobs_in_i i)) (Some O) c in
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
    if is_lossless_nm_i O i then Some O else 
     let lv := proc_params E f in
      match pi f with
      | Some pif =>
        let fout := Vset.add d (pi_output pif) in
        let other := Vset.diff O fout in
         if Vset.disjoint other  (pi_mod pif) then 
          let gif := Vset.union (pi_input pif) other in
           match needed_args_refl lv arg (pi_params pif) gif with
           | None => None
           | Some Ifun => Some Ifun
           end
          else None
      | _ => None
      end
  end.
 
  (* [eqobsinv_in i O] compute the smallest [I] such that [Eqobsinv_i I i i O] *)
 Definition eqobs_in c O := 
  List.fold_right (fun i => opt_app (eqobs_in_i i)) (Some O) c.
 
 Lemma EqObs_lossless_Modify : forall X M1 M2 E1 c1 E2 c2,
  lossless E1 c1 ->
  lossless E2 c2 ->
  Modify E1 M1 c1 ->
  Modify E2 M2 c2 ->
  Vset.disjoint X M1 ->
  Vset.disjoint X M2 ->
  EqObs X E1 c1 E2 c2 X.
 Proof.
  unfold EqObs; intros.
  apply equiv_lossless_Modify with X X M1 M2; trivial.
 Qed.

 Lemma disjoint_singleton : forall v O,
  Vset.mem v O = false ->
  Vset.disjoint O (Vset.singleton v).
 Proof.
  unfold Vset.disjoint; intros.
  change (Vset.inter O (Vset.singleton v) [=] Vset.empty).
  rewrite VsetP.eq_spec; split; auto with set.
  apply Vset.subset_complete; intro.
  rewrite VsetP.inter_spec; intros (H1, H2).
  assert (v = x).
  apply (Vset.singleton_complete _ _ H2). 
  subst; rewrite H in H1; trivialb.
 Qed.

 Lemma disjoint_union : forall I X1 X2,
  Vset.disjoint I X1 -> Vset.disjoint I X2 -> Vset.disjoint I (Vset.union X1 X2).
 Proof.
  unfold Vset.disjoint; intros.
  change  (Vset.inter I (Vset.union X1 X2) [=] Vset.empty).
  rewrite VsetP.inter_union_comm; rewrite (H :Vset.inter I X1 [=] Vset.empty).
  rewrite (H0 :Vset.inter I X2 [=] Vset.empty).
  auto with set.
 Qed.

 Lemma eqobs_in_b_correct : forall i O,
  EqObs (eqobs_in_b i O) E [I.Instr i] E [I.Instr i] O.
 Proof.
  unfold EqObs; intros.
  destruct i as [ t v e | t v d]; simpl; case_eq (Vset.mem v O); intros.
  eapply equiv_strengthen;[ | apply equiv_assign].
  unfold kreq_mem; intros; simpl.
  red; apply req_mem_weaken with (Vset.add v (Vset.remove v O)).
  rewrite VsetP.add_remove; auto with set.
  rewrite union_fv_expr_spec in H0.
  rewrite (@EqObs_e_fv_expr t e k m1 m2).
  apply req_mem_update.
  apply req_mem_weaken with (2:= H0); auto with set.
  apply req_mem_weaken with (2:= H0); auto with set.
  fold (EqObs O E [v<-e] E [v<-e] O).
  apply EqObs_lossless_Modify with (Vset.singleton v) (Vset.singleton v);
   auto using lossless_assign,Modify_assign,disjoint_singleton.
  eapply equiv_strengthen;[ | apply equiv_random].
  unfold kreq_mem; intros; simpl.
  split; unfold eq_support.
  apply EqObs_d_fv_expr.
  apply req_mem_weaken with (2:= H0); auto with set.
  red; intros; apply req_mem_weaken with (Vset.add v (Vset.remove v O)).
  rewrite VsetP.add_remove; auto with set.
  apply req_mem_update.
  apply req_mem_weaken with (2:= H0); auto with set.
  fold (EqObs O E [v<$-d] E [v<$-d] O).
  apply EqObs_lossless_Modify with (Vset.singleton v) (Vset.singleton v);
   auto using lossless_random,Modify_random,disjoint_singleton.
 Qed.
 
 
 Section WHILE.
  
  Variable c : cmd.

  Hypothesis eqobs_in_correct :  
   forall I O, eqobs_in c O = Some I -> EqObs I E c E c O.
  
  Lemma eqobs_in_while : forall b O I,
   eqobs_in_i (while b do c) O = Some I ->
   Vset.union O (fv_expr b) [<=]  I /\ EqObs I E c E c I.
  Proof.
   simpl; intros.
   set (P1 := fun X => (Vset.union O (fv_expr b) [<=] X)).
   set (P2 := fun res =>
    match res with
    | Continue X => P1 X
    | Result None => True
    | Result (Some X) => Vset.union O (fv_expr b) [<=] X /\  EqObs X E c E c X
    end).
   match type of H with
   | match ?t with
     | Result _ => _ 
     | Continue _ => _ 
     end = _ => cut (P2 t); [destruct t; try discriminate|]
   end.
   subst; trivial.
   apply while_P with P1; intros.
   unfold P1 in *; generalize (fun I => @eqobs_in_correct I a); clear P1; intros.
   unfold eqobs_in in H1.
   destruct (fold_right (fun i => opt_app (eqobs_in_i i)) (Some a) c).
   assert (U:=H1 t (refl_equal _)); clear H1.
   case_eq (t [<=?] a); intros; simpl.
   change (t [<=] a) in H1; split; auto.
   red; apply equiv_strengthen with (2:= U).
   unfold kreq_mem; intros; apply req_mem_weaken with (1:= H1); trivial.
   apply VsetP.subset_trans with a; auto with set.
   simpl; trivial.
   exact H0.
   unfold P1; rewrite union_fv_expr_spec; rewrite VsetP.union_sym; auto with set.
  Qed.

 End WHILE.
 
 Lemma eqobs_in_aux : 
  (forall i I O, eqobs_in_i i O = Some I -> EqObs I E [i] E [i] O) /\
  (forall c I O, eqobs_in c O = Some I -> EqObs I E c E c O).
 Proof.
   unfold eqobs_in, EqObs; apply I.cmd_ind2; simpl; intros.
 
   (* baseInstr *)
   inversion_clear H.
   apply eqobs_in_b_correct. 

   (* Cond *)
   generalize (fun I => H I O) (fun I => H0 I O); clear H H0;
    destruct (fold_right (fun i => opt_app (eqobs_in_i i)) (Some O) c1);
     try discriminate.
   destruct (fold_right (fun i => opt_app (eqobs_in_i i)) (Some O) c2);
     try (intros; discriminate).
   intros H H0;
   match type of H1 with (if ?test then _ else _) = _ =>
    generalize H1; clear H1; case_eq test;
     intros Heq H1; inversion H1; clear H1; subst 
   end.
   destruct (Vset.eqb t I); try discriminate.
   destruct (Vset.eqb t0 I); try discriminate.
   case_eq (is_lossless_nm I c1);
   intros H1; rewrite H1 in Heq; try discriminate Heq.
   destruct (is_lossless_nm_spec I c1 H1) as (H2, (X1,(H3,H4))).
   destruct (is_lossless_nm_spec I c2 Heq) as (H5, (X2,(H6,H7))).
   assert (lossless E [If b then c1 else c2]) by (apply lossless_cond; trivial).
   assert (Modify E (Vset.union X1 X2) [If b then c1 else c2]).
     apply Modify_cond; trivial.
   change (EqObs I E [If b then c1 else c2] E [If b then c1 else c2] I).
   apply EqObs_lossless_Modify with (Vset.union X1 X2) (Vset.union X1 X2);
    auto using disjoint_union.
   clear Heq.
   apply equiv_cond.
   apply equiv_strengthen with (kreq_mem t); auto.
   unfold kreq_mem; intros k m1 m2 (H1, _); rewrite union_fv_expr_spec in H1;
   apply req_mem_weaken with (2:= H1); auto with set.
   apply equiv_strengthen with (kreq_mem t0); auto.
   unfold kreq_mem; intros k m1 m2 (H1, _); rewrite union_fv_expr_spec in H1;
   apply req_mem_weaken with (2:= H1); auto with set.
   unfold kreq_mem; intros; assert (EqObs_e (fv_expr b) b b).
   apply EqObs_e_fv_expr.
   apply H2.   
   apply req_mem_weaken with (2:= H1); rewrite union_fv_expr_spec; auto with set.
 
   (* While *)
   destruct (eqobs_in_while H b O H0); clear H0.
   eapply equiv_weaken;[ | apply equiv_while]; trivial.
   unfold kreq_mem; intros k m1 m2 (H3, _); apply req_mem_weaken with I; trivial.
   apply VsetP.subset_trans with (Vset.union O (fv_expr b)); auto with set.
   unfold kreq_mem; intros; apply ((@EqObs_e_fv_expr _ b)).
   apply req_mem_weaken with I; trivial.
   apply VsetP.subset_trans with (Vset.union O (fv_expr b)); auto with set.
   apply equiv_strengthen with (2:= H2).
   intros k m1 m2 (H3,_); trivial. 
 
   (* Call *)
   match type of H with
   | (if ?test then _ else _) = _ =>
     generalize H; clear H; case_eq test; intros Heq H;
      inversion H; clear H; subst 
   end.
   destruct (is_lossless_nm_i_spec _ _ Heq) as (H1, (X, (H2,H3))).
   change (EqObs I E [x <c- f with a] E [x <c- f with a] I);
     apply EqObs_lossless_Modify with X X; trivial.
   clear Heq; destruct (pi f) as [pif | ]; try discriminate.
   set (other:= Vset.diff O (Vset.add x (pi_output pif))) in *.
   case_eq (Vset.disjoint other (pi_mod pif));
    intros H2; rewrite H2 in H1; try discriminate.
   generalize H1; clear H1.
   case_eq (needed_args_refl 
    (proc_params E f) a (pi_params pif) (Vset.union (pi_input pif) other));
   intros; try discriminate.
   inversion H1; clear H1; subst.
   destruct (needed_args_refl_correct _ _ _ _ H).
   eapply equiv_weaken; [ | apply (pi_spec_call pif) ]; trivial.
   unfold kreq_mem; intros; red; intros.
   apply H3; destruct (VsetP.mem_dec x0 (Vset.add x (pi_output pif)));
     auto with set.
   rewrite VsetP.union_spec, VsetP.diff_spec; right.
   assert (Vset.mem x0 other).
     unfold other; rewrite VsetP.diff_spec; split; trivial.
   split;[ apply Vset.subset_correct with (1:= H1); auto with set | ].
   apply VsetP.disjoint_mem_not_mem with (1:= H2); trivial.
   apply VsetP.subset_trans with (2:= H1); auto with set.
 
   (* nil *)
   inversion H; apply equiv_nil.
   
   (* cons *)
   generalize (fun I => H0 I O); clear H0.
   destruct (fold_right (fun i0 => opt_app (eqobs_in_i i0)) (Some O) c); 
    try discriminate.
   intros H0; assert (U:= H0 t (refl_equal _)); clear H0.
   assert (Ui := H _ _ H1).
   apply equiv_cons with (1:= Ui); auto.
  Qed.

  Lemma eqobs_in_i_correct : forall i I O, 
   eqobs_in_i i O = Some I -> 
    EqObs I E [i] E [i] O.
  Proof. 
   destruct eqobs_in_aux; trivial. 
  Qed.

  Lemma eqobs_in_correct : forall c I O, 
   eqobs_in c O = Some I -> 
    EqObs I E c E c O.
  Proof. 
   destruct eqobs_in_aux; trivial. 
  Qed.

  Definition eqobs_in_subset I c O :=
   match eqobs_in c O with
   | Some I' => I' [<=?] I
   | _ => false
   end.

  Lemma eqobs_in_subset_correct : forall I c O,
   eqobs_in_subset I c O = true ->
   EqObs I E c E c O.
  Proof.
   intros I c O; unfold eqobs_in_subset. 
   generalize (fun I => @eqobs_in_correct c I O).
   destruct (eqobs_in c O); intros; try discriminate.
   unfold EqObs ; apply equiv_strengthen with (2:= H _ (refl_equal _)). 
   unfold kreq_mem; intros; apply req_mem_weaken with I; auto.
  Qed.


 (** Dead Code **)

 Section DEADCODE_AUX.
   
   Variable dead_code_i : I.t -> Vset.t -> option (Vset.t * cmd).

   Fixpoint dead_code_aux (c:cmd) (O:Vset.t) {struct c} : option (Vset.t * cmd) :=
    match c with
    | nil => Some (O, nil)
    | i::c1 =>
      match dead_code_aux c1 O with
      | Some (I1, c2) =>
        match dead_code_i i I1 with
        | Some (II, ci) => Some (II, ci++c2)
        | _ => None
        end
      | _ => None
      end
    end.

  End DEADCODE_AUX.
 
  Fixpoint dead_code_i (i:I.t) (O:Vset.t) {struct i} : option (Vset.t * cmd) :=
   match i with
   | I.Instr ib =>
     if is_notmodify_i pi O i then Some (O, nil)
     else Some (eqobs_in_b ib O, [i])
   | I.Cond e c1 c2 =>
     if E.eqb e true then dead_code_aux dead_code_i c1 O
     else if E.eqb e false then dead_code_aux dead_code_i c2 O
     else 
     match dead_code_aux dead_code_i c1 O, dead_code_aux dead_code_i c2 O with
     | Some (I1,c1'), Some (I2,c2') => 
        if I.ceqb c1' c2' then Some (Vset.union I1 I2, c1')
        else 
         Some (Vset.union (fv_expr e) (Vset.union I1 I2), 
               [If e then c1' else c2'])
     | _, _ => None
     end
   | I.While e c => 
     if E.eqb e false then Some (O,nil)
     else 
      match eqobs_in_i i O with
      | Some II => Some (II, [i])
  (* Correct but hard to prove ....
     match dead_code_aux dead_code_i c II with
     | Some (_, c') => Some (II, [while e do c'])
     | _ => None
     end
   *)
      | None => None
      end
   | I.Call _ _ _ _ =>
     if is_lossless_nm_i O i then Some (O, nil)
     else 
      match eqobs_in_i i O with
      | Some II => Some (II, [i])
      | None => None
      end
   end.
  
  Lemma dead_code_aux_correct : 
   (forall i O I ci, 
    dead_code_i i O = Some (I,ci) -> EqObs I E [i] E ci O) /\
   (forall c O I cc,
    dead_code_aux dead_code_i c O = Some (I, cc) -> EqObs I E c E cc O).
  Proof.
   unfold EqObs; apply I.cmd_ind2; simpl; intros.
   
   (* baseInstr *)
   case_eq (is_notmodify_i pi O (I.Instr i));
   intros Heq; rewrite Heq in H; inversion H; clear H; subst.
   destruct (is_notmodify_i_correct _ _ _ Heq) as (X, (H1,H2)).
   apply equiv_lossless_Modify with 
    (1:= @depend_only_kreq_mem I) (M1:=X) (M2:=X); trivial.
   destruct i;[apply lossless_assign | apply lossless_random].
   apply lossless_nil.
   eapply Modify_weaken;[apply Modify_nil | auto with set].
   apply eqobs_in_b_correct. 

   (* Cond *)
   generalize H1; clear H1.
   assert (W:=E.eqb_spec b true); destruct (E.eqb b true); subst; intros.
   apply equiv_cond_l; simplMR; auto.
   clear W; assert (W:=E.eqb_spec b false); destruct (E.eqb b false); subst; intros.
   apply equiv_cond_l; simplMR; auto.
   generalize (H O) (H0 O); clear W H H0;
   destruct (dead_code_aux dead_code_i c1 O); try discriminate.
   destruct (dead_code_aux dead_code_i c2 O); try discriminate.
   intros.
   destruct p as (I1, c1'); destruct p0 as (I2, c2').
   assert (W:= I.ceqb_spec c1' c2'); destruct (I.ceqb c1' c2'); intros;
   inversion H1; clear H1; subst; subst.
   apply equiv_cond_l.
   rewrite proj1_MR, <- VsetP.subset_union_l; auto.
   rewrite proj1_MR, <- VsetP.subset_union_r; auto.
   apply equiv_cond.
   rewrite proj1_MR, <- VsetP.subset_union_r, <- VsetP.subset_union_l; auto.
   rewrite proj1_MR, <- VsetP.subset_union_r, <- VsetP.subset_union_r; auto.
   unfold kreq_mem; intros; apply ((@EqObs_e_fv_expr _ b)).
   apply req_mem_weaken with (2:= H1); auto with set.
   destruct p; discriminate.

   (* While *)
   change ((if E.eqb b false then Some (O, nil) 
                 else match (eqobs_in_i (while b do c) O) with
                 | Some II => Some (II, [while b do c])
                 | None => None (A:=Vset.t * cmd)
                end) = Some (I, ci)) in H0.
   assert (W:=E.eqb_spec b false); destruct (E.eqb b false); subst; intros;
   inversion H0; clear H0; subst.
   apply equiv_lossless_Modify with (1:=@depend_only_kreq_mem I) (M1:=Vset.empty)
     (M2:=Vset.empty).
   unfold lossless; intros.
   rewrite (eq_distr_elim (deno_while E false c m)).
   rewrite deno_cond_elim.
   simpl. rewrite (@deno_nil_elim k); trivial.
   apply lossless_nil.
   unfold Modify,range; intros.
   rewrite (eq_distr_elim (deno_while E false c m)).
   rewrite deno_cond_elim.
   simpl; rewrite (@deno_nil_elim k).
   apply H0; red; trivial.
   apply Modify_nil. 
   change (Vset.inter I Vset.empty [=] Vset.empty); auto with set.
   change (Vset.inter I Vset.empty [=] Vset.empty); auto with set.
   case_eq (eqobs_in_i (while b do c) O); intros.
   assert (W1:=eqobs_in_i_correct _ _ H0).
   simpl in H0; rewrite H0 in H2; clear H0; inversion H2; clear H2; subst; trivial.
   simpl in H0; rewrite H0 in H2; discriminate H2.
   (* Call *)
   match type of H with
   | (if ?test then _ else _) = _ =>
     case_eq test; intros Heq; rewrite Heq in H end.
   destruct (is_lossless_nm_i_spec _ _ Heq) as (H1, (X, (H2, H3))).
   inversion H; clear H; subst.
   apply equiv_lossless_Modify with 
    (1:=@depend_only_kreq_mem I) (M1:=X) (M2:=Vset.empty); trivial.
   apply lossless_nil. 
   apply Modify_nil.
   change (Vset.inter I Vset.empty [=] Vset.empty); auto with set.
   case_eq (eqobs_in_i (x <c- f with a) O); intros.
   assert (W:=eqobs_in_i_correct _ _ H0).
   simpl in H0; rewrite Heq in H0; rewrite H0 in H; clear Heq H0.
   inversion H; clear H; subst; trivial.
   simpl in H0; rewrite Heq in H0; rewrite H0 in H; discriminate.
   (* nil *)
   inversion H.
   apply equiv_nil.
   (* cons *)
   generalize (H0 O); clear H0.
   destruct (dead_code_aux dead_code_i c O); try discriminate.
   destruct p as (I1,c2); generalize (H I1); clear H;
    destruct (dead_code_i i I1); try discriminate.
   destruct p; inversion H1; clear H1; subst; intros.
   change (i::c) with ([i]++c); apply equiv_app with 
    (1:= H _ _ (refl_equal _)); auto.
  Qed.

  Definition dead_code c O := 
   match dead_code_aux dead_code_i c O with
   | Some (_, c') => Some c'
   | _ => None
   end.

  Lemma dead_code_correct : forall c O c', 
   dead_code c O = Some c' -> equiv Meq E c E c' (kreq_mem O).
  Proof. 
   intros c O c'; destruct dead_code_aux_correct as (_, H); unfold dead_code.
   generalize (H c O); clear H.
   destruct (dead_code_aux dead_code_i c O) as [(I,c1) | ].
   intros H H0; inversion H0; clear H0; subst.
   apply equiv_strengthen with (2:= H _ _ (refl_equal _)).
   unfold Meq, kreq_mem; intros; subst; apply req_mem_refl.
   intros; discriminate.
  Qed.

  Lemma dead_code_equiv_l : forall c1 c1' E2 c2 P Q X1 X2,
   decMR P ->
   depend_only_rel Q X1 X2 ->
   dead_code c1 X1 = Some c1' ->
   equiv P E c1' E2 c2 Q ->
   equiv P E c1 E2 c2 Q.
  Proof.
   intros.
   assert (H2:= dead_code_correct _ _ H0). 
   apply equiv_depend_only_l with (2:= H) (4:= H1); trivial.
  Qed.

  Lemma dead_code_equiv_r : forall c2 c2' E1 c1 P Q X1 X2,
   decMR P ->
   depend_only_rel Q X1 X2 ->
   dead_code c2 X2 = Some c2' ->
   equiv P E1 c1 E c2' Q ->
   equiv P E1 c1 E c2 Q.
  Proof.
   intros.
   assert (H2:= dead_code_correct _ _ H0). 
   apply equiv_depend_only_r with (2:= H) (4:= H1); trivial.
  Qed.

 End EQOBS.

 Section DEAD_CODE.
   
  Variables n : positive.
  Variables E1 E2 : env. 
  Variables (pi1:eq_refl_info E1) (pi2:eq_refl_info E2). 

  Definition dead_code_para c1 c2 O1 O2 :=
   match dead_code n pi1 c1 O1, dead_code n pi2 c2 O2 with
   | Some c1', Some c2' => Some (c1', c2')
   | _, _ => None
   end.

  Lemma dead_code_para_equiv :  forall c1 c1' c2 c2' P Q X1 X2,
   decMR P ->
   depend_only_rel Q X1 X2 ->
   dead_code_para c1 c2 X1 X2 = Some (c1',c2') ->
   equiv P E1 c1' E2 c2' Q ->
   equiv P E1 c1 E2 c2 Q.
  Proof.
   intros c1 c1' c2 c2' P Q X1 X2 Hdec Hdep Heq Hequiv;
    generalize Heq; clear Heq; unfold dead_code_para.
   case_eq (dead_code n pi1 c1 X1);
    [intros C1' H | intros; discriminate].
   case_eq (dead_code n pi2 c2 X2);
    [intros C2' H' H1; inversion H1; clear H1; subst|intros; discriminate].
   apply (@dead_code_equiv_l n E1 pi1 c1 c1' E2 c2 P _ _ _ Hdec Hdep H); trivial.
   apply (@dead_code_equiv_r n E2 pi2 c2 c2' E1 c1' P _ _ _ Hdec Hdep H'); trivial.
  Qed.

 End DEAD_CODE.


 Section CODE_MOVEMENT.

  Fixpoint split_cmd_aux (i:I.t) (r c:cmd) {struct c} : option (cmd * cmd) :=
   match c with
   | nil => None
   | i'::c' =>
     if I.eqb i i' then Some (r, c')
     else split_cmd_aux i (i'::r) c'
   end.

  Definition split_cmd i c := split_cmd_aux i nil c.

  Lemma split_cmd_aux_correct : forall i c r r' t,
   split_cmd_aux i r c = Some (r',t) ->
   rev_append r c = rev_append r' (i::t).
  Proof.
   induction c; simpl; intros r r' t.
   intros; discriminate.
   generalize (I.eqb_spec i a); destruct (I.eqb i a); intros.
   inversion H0; clear IHc H0; subst; trivial.
   rewrite <- (IHc _ _ _ H0); trivial.
  Qed.

  Lemma split_cmd_correct : forall i c r t, 
   split_cmd i c = Some (r,t) ->
   c = rev_append r (i::t).
  Proof.
   intros i c r t H; rewrite <- (split_cmd_aux_correct _ _ _  H); trivial.
  Qed.
  
  Lemma EqObs_swap_aux : forall E I1 I2 O1 O2 c1 c2,
   Modify E O1 c1 ->
   Modify E O2 c2 ->
   EqObs I2 E c2 E c2 O2 ->
   Vset.disjoint I2 O1 ->
   forall k (m1 m2 : Mem.t k),
    m1 =={Vset.union I1 I2} m2 ->
    forall f: Mem.t k -> U, 
     mu ([[c1]] E m1) (fun m' => mu ([[c2]] E m') f) ==
     mu ([[c1]] E m1) (fun m' => mu ([[c2]] E m2) 
      (fun m'' => f (m1{!O1 <<- m'!} {!O2 <<- m''!}))).
  Proof.
   intros.
   rewrite (Modify_deno_elim H).
   apply (mu_stable_eq (([[c1]]) E m1)).
   simpl; apply ford_eq_intro; intros m'.
   rewrite (Modify_deno_elim H0 (k:=k)).
   match goal with |- ?x == _ => set (F:= x) end.
   rewrite (Modify_deno_elim H0 (k:=k)); unfold F; clear F.
   assert (m1 {!O1 <<- m'!} =={I2} m2).
   apply req_mem_trans with m1.
   apply req_mem_update_disjoint; trivial.
   apply req_mem_weaken with (2:= H3); auto with set.
   apply (equiv_deno H1); trivial; unfold kreq_mem; intros.
   rewrite (@req_mem_eq k O2 (m1 {!O1 <<- m'!}) m0 (m2 {!O2 <<- m3!})); trivial.
   apply req_mem_trans with (1:= H5).
   apply req_mem_sym; apply req_mem_update_mem_l.
  Qed.

  Lemma swap_comm :  forall E I1 I2 O1 O2 c1 c2,
   Modify E O1 c1 ->    Modify E O2 c2 ->
   EqObs I1 E c1 E c1 O1 ->
   EqObs I2 E c2 E c2 O2 ->
   Vset.disjoint I2 O1 ->
   Vset.disjoint I1 O2 ->
   Vset.disjoint O1 O2 ->
   forall k (m:Mem.t k) f,
    mu ([[c1++c2]] E m) f ==
    mu ([[c2++c1]] E m) f.
  Proof.
   intros; repeat rewrite deno_app_elim.
   assert (H6:= req_mem_refl (Vset.union I1 I2) m).
   rewrite (EqObs_swap_aux I1 H H0 H2 H3 H6).
   rewrite VsetP.union_sym in H6; apply req_mem_sym in H6.
   rewrite (EqObs_swap_aux I2 H0 H H1 H4 H6).
   rewrite deno_comm.
   apply mu_stable_eq.
   refine (@ford_eq_intro _ _ _ _ _); intros m'.
   apply mu_stable_eq.
   simpl; apply ford_eq_intro; intro m''.
   replace (m {!O1 <<- m''!} {!O2 <<- m'!}) with 
    (m {!O2 <<- m'!} {!O1 <<- m''!}); trivial.
   apply Mem.eq_leibniz.
   intros (t, x); destruct (VsetP.mem_dec x O1).
   rewrite update_mem_in; trivial.
   rewrite update_mem_notin.
   rewrite update_mem_in; trivial.
   apply VsetP.disjoint_mem_not_mem with (1:= H5); trivial.
   rewrite update_mem_notin; trivial. 
   destruct (VsetP.mem_dec x O2).
   repeat rewrite update_mem_in; trivial.
   repeat rewrite update_mem_notin; trivial.
  Qed.

  Lemma equiv_swap : forall E I1 I2 O1 O2 c1 c2,
   Modify E O1 c1 ->
   Modify E O2 c2 ->
   EqObs I1 E c1 E c1 O1 ->
   EqObs I2 E c2 E c2 O2 ->
   Vset.disjoint O1 O2 ->
   Vset.disjoint I1 O2 ->
   Vset.disjoint I2 O1 -> 
   equiv Meq E (c1++c2) E (c2++c1) Meq.
  Proof.
   intros; intro k.
   exists (fun m1 m2 => Mlet ([[c1++c2]] E m1) (fun m => Munit (m,m))).
   unfold Meq; intros; subst; constructor; simpl; intros; trivial.
   apply (mu_stable_eq (([[c1 ++ c2]]) E m2)).
   simpl; apply ford_eq_intro; trivial.
   rewrite (swap_comm H H0 H1 H2 H5 H4 H3 m2).
   apply (mu_stable_eq (([[c2 ++ c1]]) E m2)).
   simpl; apply ford_eq_intro; trivial. 
   red; unfold prodP; intros; simpl.
   transitivity (mu (([[c1 ++ c2]]) E m2) (fun x : Mem.t k=> 0)).
   symmetry; apply mu_0.
   apply (mu_stable_eq (([[c1 ++ c2]]) E m2)).
   simpl; apply ford_eq_intro; auto.
  Qed.

  Variable n : positive.
  Variable E1 E2 : env.
  Variables (pi1:eq_refl_info E1) (pi2:eq_refl_info E2). 

  Definition swapable (E:env) (pi:eq_refl_info E) (i:I.instr) (c:cmd) :=
   match modify_i pi Vset.empty i, modify pi Vset.empty c with
   | Some M1, Some M2 =>
     if Vset.disjoint M1 M2 then
     match eqobs_in_i n pi i M1, eqobs_in n pi c M2 with
     | Some I1, Some I2 =>
       if Vset.disjoint I1 M2 then Vset.disjoint I2 M1 
       else false
     | _, _ => false
     end
     else false
   | _, _ => false
   end.

  Lemma swapable_correct : forall (E:env) (pi:eq_refl_info E) (i:I.instr) (c:cmd),
   swapable pi i c = true ->
   equiv Meq E (i::c) E (c++[i]) Meq.
  Proof.
   unfold swapable; intros E pi i c.
   generalize (modify_i_correct pi i Vset.empty);
    destruct (modify_i pi Vset.empty i) as [M1 | ]; intro; try (intros; discriminate).
   generalize (modify_correct pi c Vset.empty);
    destruct (modify pi Vset.empty c) as [M2 | ]; intro; try (intros; discriminate).
   case_eq (Vset.disjoint M1 M2); intro; try (intros; discriminate).
   generalize (fun I => @eqobs_in_i_correct n E pi i I M1);
    destruct (eqobs_in_i n pi i M1) as [I1 | ]; intro; try (intros; discriminate).
   generalize (fun I => @eqobs_in_correct n E pi c I M2);
    destruct (eqobs_in n pi c M2) as [I2 | ]; intro; try (intros; discriminate).
   case_eq (Vset.disjoint I1 M2); intros; try discriminate.
   apply equiv_swap with (3:= H2 _ (refl_equal _)) (4:=  H3 _ (refl_equal _)); auto.
  Qed.

  Fixpoint swap_aux (rh1 t1 c2 t : cmd) {struct rh1} : (triple cmd cmd cmd) :=
   match rh1 with
   | nil => Triple t1 c2 t
   | i::rh1' =>
     if swapable pi1 i t1 then
      match split_cmd i c2 with
      | Some (r2,t2) =>
        if swapable pi2 i t2 then swap_aux rh1' t1 (rev_append r2 t2) (i::t)
        else swap_aux rh1' (i::t1) c2 t
      | None => swap_aux rh1' (i::t1) c2 t 
      end 
      else swap_aux rh1' (i::t1) c2 t
   end.
  
  Lemma swap_aux_correct : forall rh1 t1 c2 t h1 h2 t',
   swap_aux rh1 t1 c2 t = Triple h1 h2 t' ->
   equiv Meq E1 ((rev_append rh1 t1) ++ t) E1 (h1++t') Meq /\
   equiv Meq E2 (c2 ++ t) E2 (h2++t') Meq.
  Proof.
   induction rh1; simpl; intros t1 c2 t h1 h2 t'.
   intros Heq; inversion Heq; split; apply equiv_eq_mem.
   assert (forall h1 h2 t', swap_aux rh1 (a :: t1) c2 t = Triple h1 h2 t' ->
     equiv Meq E1 (rev_append rh1 (a :: t1) ++ t) E1 (h1 ++ t') Meq /\
     equiv Meq E2 (c2 ++ t) E2 (h2 ++ t') Meq).
     intros h3 h4 t'0 H1; refine (IHrh1 _ _ _ _ _ _ H1).
   generalize (swapable_correct pi1 a t1).
   destruct (swapable pi1 a t1); intro; auto.
   generalize (split_cmd_correct a c2).
   destruct (split_cmd a c2) as [(h3,t2) | ]; intro; auto.
   generalize (swapable_correct pi2 a t2).
   destruct (swapable pi2 a t2); intros; auto.  
   destruct (IHrh1 _ _ _ _ _ _ H3). 
   split.
   apply equiv_trans_eq_mem_l with 
    (P1:=trueR) (2:= H4); trivial.
   simplMR; repeat rewrite rev_append_rev.
   change (a::t) with ([a]++t).
   rewrite ass_app; apply equiv_app with Meq; auto using equiv_eq_mem.
   rewrite app_ass; apply equiv_app with Meq; auto using equiv_eq_mem.
   red; red; trivial.
   rewrite (H1 _ _ (refl_equal _)).
   apply equiv_trans_eq_mem_l with (P1:=trueR) (2:= H5); trivial.
   simplMR; change (a::t) with ([a]++t).
   rewrite ass_app; apply equiv_app with Meq; auto using equiv_eq_mem.
   repeat rewrite rev_append_rev; rewrite rev_append_rev in H5.
   rewrite app_ass; apply equiv_app with Meq; auto using equiv_eq_mem.
   red; red; trivial.
  Qed.

  Definition swap c1 c2 := swap_aux (rev' c1) nil c2 nil. 

  Lemma swap_correct : forall c1 c2 h1 h2 t,
   swap c1 c2 = Triple h1 h2 t ->
   forall P Q, equiv P E1 (h1++t) E2 (h2++t) Q ->
    equiv P E1 c1 E2 c2 Q.
  Proof.
   intros. 
   destruct (swap_aux_correct _ _ _ _ H).
   rewrite <- app_nil_end in H1, H2.
   unfold rev' in H1; repeat rewrite rev_append_rev in H1.
   repeat rewrite <- app_nil_end in H1; rewrite rev_involutive in H1.
   apply equiv_trans_eq_mem_l with (P1:=trueR) (E1':= E1) (c1':= (h1 ++ t)); trivial.
   simplMR; trivial.
   apply equiv_trans_eq_mem_r with (P2:=trueR) (E2':= E2) (c2':= (h2 ++ t)); trivial.
   simplMR; trivial.
   red; red; trivial.
   red; red; trivial.
  Qed.

 End CODE_MOVEMENT.

End Make.
