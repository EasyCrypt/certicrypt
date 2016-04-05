(** * NotModifyDec.v : Decision procedure for determining the 
   variables that a progam (not) modifies *)


Set Implicit Arguments.

Require Export SemTheory.


Module Make (Sem:SEM). 
 
 Module SemTh := SemTheory.Make Sem.
 Export SemTh.

 Definition modify_base X (i:I.baseInstr) := 
   match i with
   | I.Assign t x e =>
      if E.eqb e x then X else Vset.add x X
   | I.Random t x _ => Vset.add x X
   end.

 Section MODIFY.

  Variable E: env.
  Variable mod_info :  forall t (f:Proc.proc t), option Vset.t.
  Hypothesis mod_info_correct : forall t (f:Proc.proc t) GM,
     mod_info f = Some GM ->  
     (forall x, Vset.mem x GM -> Var.is_global x) /\
     (exists L, (forall x, Vset.mem x L -> Var.is_local x) /\ 
      Modify E (Vset.union L GM) (proc_body E f)).
   
  Fixpoint modify_i_1 (X:Vset.t) (i:I.instr) {struct i} : option Vset.t :=
   match i with
   | I.Instr i  => Some (modify_base X i)
   | I.Cond _ c1 c2 => 
     opt_app (fold_left_opt modify_i_1 c1) (fold_left_opt modify_i_1 c2 X)
   | I.While _ c => fold_left_opt modify_i_1 c X
   | I.Call t d f _ => 
     match mod_info f with
     | Some GM => Some (Vset.add d (Vset.union GM X))
     | None => None
     end
    end.

  Definition modify_1 X (c:cmd) := fold_left_opt modify_i_1 c X.
 
  Lemma modify_1_correct_aux : 
   (forall i X, spec_opt (fun R => Modify E R [i] /\ X [<=] R) 
    (modify_i_1 X i)) /\
   (forall c X, spec_opt (fun R => Modify E R c /\ X [<=] R) 
    (modify_1 X c)).
  Proof.
   unfold modify_1; intros; apply I.cmd_ind2; simpl; intros.
   (* baseInstr *)
   destruct i; simpl.
   generalize (E.eqb_spec e v); destruct (E.eqb e v); 
    intros; split; auto with set.
   rewrite H; apply Modify_weaken with Vset.empty; auto with set.
   apply Modify_assign_same.
   apply Modify_weaken with (Vset.singleton v).
   apply Modify_assign.
   apply Vset.subset_complete; intro; rewrite VsetP.add_spec.
   intros H1; left; apply (Vset.singleton_complete _ _ H1).
   split; auto with set.
   apply Modify_weaken with (Vset.singleton v).
   apply Modify_random.
   apply Vset.subset_complete; intro; rewrite VsetP.add_spec.
   intros H1; left; apply (Vset.singleton_complete _ _ H1).
 
   (* Cond *)
   assert (H0' := H0 X); clear H0.
   destruct (fold_left_opt modify_i_1 c2 X) as [R2|]; try exact I.
   assert (H' := H R2); clear H.
   unfold opt_app; destruct (fold_left_opt modify_i_1 c1 R2) as [R1|]; 
    try exact I.
   destruct H0'; destruct H'; split.
   apply Modify_weaken with (Vset.union R1 R2).
   apply Modify_cond; auto.
   rewrite VsetP.union_sym; rewrite VsetP.subset_union; auto with set.
   apply VsetP.subset_trans with R2; auto. 
   
   (* While *)
   assert (H' := H X); destruct (fold_left_opt modify_i_1 c X); destruct H'; 
    split; auto.
   apply Modify_while; auto.

   (* Call *)
   generalize (@mod_info_correct _ f).
   destruct (mod_info f) as [GM | ]; simpl; trivial; split;auto with set.
   destruct (H _ (eq_refl _)) as (H2,(L,(H0,H1))).
   apply Modify_weaken with  (Vset.add x GM).
   eapply Modify_weaken;[ apply Modify_call with (1:=H1) | ].
   apply VsetP.subset_add_ctxt.
   apply Vset.subset_complete; intros.
   assert (W:=get_globals_spec _ _ H3).
   assert (Vset.mem x0 (Vset.union L GM)).
   apply Vset.subset_correct with 
    (1:= get_globals_subset(Vset.union L GM)); trivial.
   rewrite VsetP.union_spec in H4; destruct H4; trivial.
   apply H0 in H4; unfold Var.is_local in H4; rewrite W in H4; discriminate.
   apply VsetP.subset_add_ctxt;auto with set.

   (* nil *)
   split; auto with set.
   apply Modify_weaken with Vset.empty; auto with set.
   apply Modify_nil.
   
   (* cons *)
   assert (H':= H X); clear H; destruct (modify_i_1 X i) as [Ri|]; try exact I; simpl.
   assert (H0' := H0 Ri); clear H0; unfold opt_app; 
     destruct (fold_left_opt modify_i_1 c Ri) as [Rc|]; try exact I; simpl in *.
   destruct H'; destruct H0'; split.
   apply Modify_weaken with (Vset.union Ri Rc); auto with set.
   apply Modify_cons; auto.
   rewrite VsetP.subset_union; auto with set.
   apply VsetP.subset_trans with Ri; auto.
  Qed.
 
  Definition modify_2 := modify_1 Vset.empty.
 
  Lemma modify_2_correct : 
    forall c M, modify_2 c = Some M -> Modify E M c.
  Proof.
    destruct modify_1_correct_aux;unfold modify_2;intros.
    assert (W:=H0 c Vset.empty);rewrite H1 in W;destruct W;trivial.
  Qed.

 End MODIFY.

 Section LOSSLESS.
  Variable E: env.
  Variable lossless_info :  forall t, Proc.proc t ->  bool.
  Hypothesis lossless_info_correct : forall t (f:Proc.proc t),
   lossless_info f -> lossless E (proc_body E f).

  Definition list_forall := Eval cbv beta delta [forallb andb ifb] in forallb.
  
  Fixpoint is_lossless_i_1 (i:I.t) : bool :=
   match i with
   | I.Instr _ => true
   | I.Cond _ c1 c2 => 
     if list_forall is_lossless_i_1 c1 then list_forall is_lossless_i_1 c2
     else false
   | I.Call t d f arg => lossless_info f
   | _ => false
  end.
 
  Definition is_lossless_1 : cmd -> bool := list_forall is_lossless_i_1.

  Lemma is_lossless_1_correct_aux : 
   (forall i, is_lossless_i_1 i -> lossless E [i]) /\ 
   (forall c, is_lossless_1 c -> lossless E c).
  Proof.
   apply I.cmd_ind2; simpl; intros; trivialb.
   destruct i; auto using lossless_assign, lossless_random.
   unfold is_lossless_1 in *.
   destruct (list_forall is_lossless_i_1 c1); trivialb.
   destruct (list_forall is_lossless_i_1 c2); trivialb.
   apply lossless_cond; trivial.
   apply lossless_call;auto.
   apply lossless_nil.
   destruct (is_lossless_i_1 i); trivialb.
   apply lossless_cons; trivial.
  Qed.

  Lemma is_lossless_1_correct : forall c, is_lossless_1 c -> lossless E c.
  Proof. 
   destruct is_lossless_1_correct_aux; trivial.
  Qed.

 End LOSSLESS.

 Section NOTMODIFY.
 
  Variable E : env.
  Variable pi : eq_refl_info E.

  Definition pi_to_mod_info := fun t f => 
    match @pi t f with 
    | Some i => Some (pi_mod i) 
    | _ => None 
    end.

  Definition modify_i := modify_i_1 pi_to_mod_info.

  Definition modify X (c:cmd) := fold_left_opt modify_i c X.
 
  Lemma modify_correct_aux : 
   (forall i X, spec_opt (fun R => Modify E R [i] /\ X [<=] R) 
    (modify_i X i)) /\
   (forall c X, spec_opt (fun R => Modify E R c /\ X [<=] R) 
    (modify X c)).
  Proof.
   apply modify_1_correct_aux.
   unfold pi_to_mod_info;intros t f GM.
   destruct (pi f);[ | discriminate].
   intros Heq;injection Heq;intros;subst;split.
   apply mod_global. apply mod_spec.
  Qed.

  Lemma modify_i_correct_subset : forall i X R,
   modify_i X i = Some R ->
   Modify E R [i] /\ X [<=] R.
  Proof.
   destruct modify_correct_aux as (H1,H2); intros i Y R Heq.
   assert (H3 := H1 i Y); rewrite Heq in H3; trivial.
  Qed.
  
  Lemma modify_i_correct : forall i X R,
   modify_i X i = Some R ->
   Modify E R [i].
  Proof.
   intros i X R H; destruct (modify_i_correct_subset _ _ H); trivial.
  Qed.
  
  Lemma modify_correct_subset : forall c X R, 
   modify X c = Some R ->
   Modify E R c /\ X [<=] R.
  Proof.
   destruct modify_correct_aux as (H1,H2); intros c Y R Heq.
   assert (H3 := H2 c Y); rewrite Heq in H3; trivial.
  Qed.
  
  Lemma modify_correct : forall c X R, 
   modify X c = Some R ->
   Modify E R c.
  Proof.
   intros c Y R H; destruct (modify_correct_subset _ _ H); trivial.
  Qed.
  
  Definition is_notmodify X c := 
   match modify Vset.empty c with
   | Some X' => Vset.disjoint X X'
   | _ => false
   end.

  Definition is_notmodify_i X i := 
   match modify_i Vset.empty i with
   | Some X' => Vset.disjoint X X'
   | _ => false
   end.

  Lemma is_notmodify_correct : forall X c,
   is_notmodify X c -> exists M, Modify E M c /\ Vset.disjoint X M.
  Proof.
   unfold is_notmodify; intros X c.
   case_eq (modify Vset.empty c); intros; trivialb.
   exists t; split; trivial.
   eapply modify_correct; eauto.
  Qed.
  
  Lemma is_notmodify_i_correct : forall X i,
   is_notmodify_i X i -> exists M, Modify E M [i] /\ Vset.disjoint X M.
  Proof.
   unfold is_notmodify_i; intros X i.
   case_eq (modify_i Vset.empty i); intros; trivialb.
   exists t; split; trivial.
   eapply modify_i_correct; eauto.
  Qed.


  (** Deciding lossless *)
 
  Definition pi_to_lossless_info := fun t f => 
    match @pi t f with 
    | Some i =>  pi_lossless i
    | _ => false
    end.

  Lemma pi_to_lossless_info_correct : forall t (f:Proc.proc t),
   pi_to_lossless_info f -> lossless E (proc_body E f).
  Proof.
   unfold pi_to_lossless_info;intros.
   destruct (pi f);[ | discriminate].
   apply pi_lossless_spec with p;trivial.
  Qed.

  Definition is_lossless_i := is_lossless_i_1 pi_to_lossless_info.
 
  Definition is_lossless : cmd -> bool := is_lossless_1 pi_to_lossless_info.

  Lemma is_lossless_correct_aux : 
   (forall i, is_lossless_i i -> lossless E [i]) /\ 
   (forall c, is_lossless c -> lossless E c).
  Proof.
   apply is_lossless_1_correct_aux;apply pi_to_lossless_info_correct.
  Qed.
  
  Lemma is_lossless_i_correct : forall i, is_lossless_i i -> lossless E [i].
  Proof. 
   destruct is_lossless_correct_aux; trivial.
  Qed.
  
  Lemma is_lossless_correct : forall c, is_lossless c -> lossless E c.
  Proof. 
   destruct is_lossless_correct_aux; trivial.
  Qed.

 End NOTMODIFY.

End Make.
