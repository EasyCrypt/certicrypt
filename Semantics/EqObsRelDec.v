(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

Set Implicit Arguments.

Require Export LazySampling2.

Module Make (SemO:SEM_OPT).
  Module LS2 := LazySampling2.Make SemO.
  Export LS2.

  Inductive formula : Type :=
    | Fbase  : formula
    | Fupd1  : formula -> forall t, Var.var t -> E.expr t -> formula 
    | Fupd2  : formula -> forall t, Var.var t -> E.expr t -> formula 
    | Fupd_p : formula -> forall t, Var.var t -> E.expr t -> formula  
    | Fand   : formula -> formula -> formula 
    | For    : formula -> formula -> formula
    | Fimp   : formula -> formula -> formula 
    | Fnot   : formula -> formula 
    | Fbool1 : E.expr T.Bool -> formula 
    | Fbool2 : E.expr T.Bool -> formula
    | Feq_assoc_except : forall t1 t2, Var.var t1 -> Var.var (T.List (T.Pair t1 t2)) -> formula
    | Fforall_random : forall t, E.support t -> Var.var t -> formula -> formula.

  Section INTERP.

  Variable (iB : mem_rel).

  Fixpoint interp_F (F:formula) : mem_rel:=
    match F with
    | Fbase => iB   
    | Fupd1 F t x e => upd1 (interp_F F) x e
    | Fupd2 F t x e => upd2 (interp_F F) x e
    | Fupd_p F t x e => upd_para (interp_F F) x e x e
    | Fand F1 F2 => (interp_F F1) /-\ (interp_F F2)
    | For F1 F2 => (interp_F F1) \-/ (interp_F F2)
    | Fimp F1 F2 =>(interp_F F1) |-> (interp_F F2)
    | Fnot F => ~- (interp_F F)
    | Fbool1 e => EP1 e
    | Fbool2 e => EP2 e
    | Feq_assoc_except t1 t2 v l => eq_assoc_except v l
    | Fforall_random t d x F => forall_random (interp_F F) x x d 
    end.

  Fixpoint eqobsrel_tail_rm1 (r1:cmd) O Q :=
    match r1 with
    | I.Instr (I.Assign t1 x1 e1) :: r1' =>
      if Vset.mem x1 O then (r1, Q)
      else eqobsrel_tail_rm1 r1' O (Fupd1 Q x1 e1)
    | _ => (r1, Q)
    end.

  Fixpoint eqobsrel_tail_rm2 (r2:cmd) O Q :=
    match r2 with
    | I.Instr (I.Assign t2 x2 e2) :: r2' =>
      if Vset.mem x2 O then (r2, Q)
      else eqobsrel_tail_rm2 r2' O (Fupd2 Q x2 e2)
    | _ => (r2, Q)
    end.

  Lemma eqobsrel_tail_rm1_spec : forall (P : mem_rel) (E1 : env) (r1 r1': cmd) (E2 : env)
          (c2 : cmd) (O : Vset.t) Q Q',
        eqobsrel_tail_rm1 r1 O Q = (r1', Q') ->
        equiv P E1 (rev r1') E2 c2 (req_mem_rel O (interp_F Q')) ->
        equiv P E1 (rev r1) E2 c2 (req_mem_rel O (interp_F Q)).
  Proof.
    induction r1; simpl; intros. 
    injection H; clear H; intros; subst; exact H0.
    destruct a; try match goal with | H : (_, _) = (_, _) |- _ => 
       injection H; clear H; intros; subst; exact H0 end.   
    destruct b; try match goal with | H : (_, _) = (_, _) |- _ => 
       injection H; clear H; intros; subst; exact H0 end.
    case_eq (Vset.mem v O); intros Heq; rewrite Heq in H;
    try match goal with | H : (_, _) = (_, _) |- _ => 
       injection H; clear H; intros; subst; exact H0 end.
    rewrite (app_nil_end c2); apply equiv_app with (1:= IHr1 _ _ _ _ _ _ H H0).
    eapply equiv_strengthen;[ | apply equiv_assign_l].
    unfold req_mem_rel,andR, kreq_mem; simpl; intros k m1 m2 (H2,H3); split; trivial.
    apply req_mem_trans with m1; trivial.
    apply req_mem_sym; apply req_mem_upd_disjoint; trivial.
  Qed.    

  Lemma eqobsrel_tail_rm2_spec : forall (P : mem_rel) (E1 : env) (c1 : cmd) (E2 : env)
          (r2 r2': cmd) (O : Vset.t) Q Q',
        eqobsrel_tail_rm2 r2 O Q = (r2', Q') ->
        equiv P E1 c1 E2 (rev r2') (req_mem_rel O (interp_F Q')) ->
        equiv P E1 c1 E2 (rev r2) (req_mem_rel O (interp_F Q)).
  Proof.
    induction r2; simpl; intros. 
    injection H; clear H; intros; subst; exact H0.
    destruct a; try match goal with | H : (_, _) = (_, _) |- _ => 
       injection H; clear H; intros; subst; exact H0 end.   
    destruct b; try match goal with | H : (_, _) = (_, _) |- _ => 
       injection H; clear H; intros; subst; exact H0 end.
    case_eq (Vset.mem v O); intros Heq; rewrite Heq in H;
    try match goal with | H : (_, _) = (_, _) |- _ => 
       injection H; clear H; intros; subst; exact H0 end.
    rewrite (app_nil_end c1); apply equiv_app with (1:= IHr2 _ _ _ _ H H0).
    eapply equiv_strengthen;[ | apply equiv_assign_r].
    unfold req_mem_rel,andR, kreq_mem; simpl; intros k m1 m2 (H2,H3); split; trivial.
    apply req_mem_trans with m2; trivial.
    apply req_mem_upd_disjoint; trivial.
  Qed.    
 
  Definition eqobs_rel_rm r1 r2 O Q :=
    let (r1', Q1) := eqobsrel_tail_rm1 r1 O Q in
    let (r2', Q2) := eqobsrel_tail_rm2 r2 O Q1 in
    Triple r1' r2' Q2.

  Lemma eqobsrel_tail_rm_spec : forall (P : mem_rel) (E1 : env) (r1 c1: cmd) (E2 : env)
          (r2 c2: cmd) (O : Vset.t) Q Q',
        eqobs_rel_rm r1 r2 O Q = Triple c1 c2 Q' ->
        equiv P E1 (rev c1) E2 (rev c2) (req_mem_rel O (interp_F Q')) ->
        equiv P E1 (rev r1) E2 (rev r2) (req_mem_rel O (interp_F Q)).
  Proof.
   unfold eqobs_rel_rm; simpl; intros.
   case_eq (eqobsrel_tail_rm1 r1 O Q); intros r1' Q1 Heq1; rewrite Heq1 in H.
   apply eqobsrel_tail_rm1_spec with (1:= Heq1).
   case_eq (eqobsrel_tail_rm2 r2 O Q1); intros r2' Q2 Heq2; rewrite Heq2 in H.
   apply eqobsrel_tail_rm2_spec with (1:= Heq2). 
   injection H; clear H; intros; subst; trivial.
  Qed.

  Section EOR_tail_cmd.

   Variable eqobsrel_tail_rev_i : 
    I.instr -> I.instr -> Vset.t -> formula -> option (Vset.t * formula).
  
   Hypothesis Hrec_i : 
     forall E1 i1 E2 i2 O Q O' Q',
       eqobsrel_tail_rev_i i1 i2 O Q = Some (O', Q') ->
       equiv (req_mem_rel O' (interp_F Q')) E1 [i1] E2 [i2] (req_mem_rel O (interp_F Q)).
 
   Fixpoint eqobsrel_tail_rev_aux (n:nat) (r1 r2:cmd) O Q {struct n} :=
    match n with 
    | O => Quad (rev r1) (rev r2) O Q
    | S n =>
      let (r1', r2', Q') := eqobs_rel_rm r1 r2 O Q in
      match r1', r2' with
      | i1::r1'', i2::r2'' =>
        match eqobsrel_tail_rev_i i1 i2 O Q' with
        | Some (O'', Q'') => eqobsrel_tail_rev_aux n r1'' r2'' O'' Q''
        | None => Quad (rev r1') (rev r2') O Q'
        end
      | _ , _ => Quad (rev r1') (rev r2') O Q'
      end
    end.

  Lemma eqobsrel_tail_rev_aux_spec : 
    forall n P E1 r1 E2 r2 O Q c1 c2 O' Q',
       eqobsrel_tail_rev_aux n r1 r2 O Q = Quad c1 c2 O' Q' ->
       equiv P E1 c1 E2 c2 (req_mem_rel O' (interp_F Q')) ->
       equiv P E1 (rev r1) E2 (rev r2) (req_mem_rel O (interp_F Q)).
  Proof.
   induction n; simpl; intros.
   injection H; clear H; intros; subst; trivial.
   case_eq (eqobs_rel_rm r1 r2 O Q); intros r1' r2' Q'' Heq.
   eapply eqobsrel_tail_rm_spec; eauto.
   rewrite Heq in H; destruct r1'; try (injection H; clear H; intros; subst; trivial).
   destruct r2'; try (injection H; clear H; intros; subst; trivial).
   case_eq (eqobsrel_tail_rev_i i i0 O Q'').
   intros (O'', Q3) Heq1; rewrite Heq1 in H.
   simpl; apply equiv_app with (req_mem_rel O'' (interp_F Q3)); eauto.
   intros Heq1; rewrite Heq1 in H.
   injection H; clear H; intros; subst; simpl; trivial. 
  Qed.    

  Definition eqobsrel_tail_rev_i_body (i1 i2:I.instr) O Q := 
   match i1 with 
   | I.Instr (I.Assign t1 x1 e1) =>
      match i2 with 
      | I.Instr (I.Assign t2 x2 e2) =>
        if Var.eqb x1 x2 then 
         if E.eqb e1 e2 then 
          let O' := fv_expr_extend e1 (Vset.remove x1 O) in
          let Q' := Fupd_p Q x1 e1 in
          Some (O', Q')
         else None
        else None
      | _ => None
      end
   | I.Instr (I.Random t1 x1 d1) =>
     match i2 with
     | I.Instr (I.Random t2 x2 d2) =>
       if Var.eqb x1 x2 then
         if E.seqb d1 d2 then
          let Q' := Fforall_random d1 x1 Q in
          let O' := Vset.union (fv_distr d1) (Vset.remove x1 O) in
          Some (O', Q') 
         else None
       else None
     | _ => None
     end
   | I.Cond e1 c1t c1f =>
     match i2 with
     | I.Cond e2 c2t c2f =>
       if E.eqb e1 e2 then
       match eqobsrel_tail_rev_aux (length c1t) (rev c1t) (rev c2t) O Q with
       | Quad nil nil Ot Qt =>
         match eqobsrel_tail_rev_aux (length c1f) (rev c1f) (rev c2f) O Q with
         | Quad nil nil Of Qf =>
           Some (fv_expr_extend e1 (Vset.union Ot Of), 
                  Fand (Fimp (Fand (Fbool1 e1) (Fbool2 e2)) Qt)
                       (Fimp (Fand (Fnot (Fbool1 e1)) (Fnot (Fbool2 e2))) Qf))
         | _ => None
         end
       | _ => None
       end
       else None
     | _ => None
     end
   | _ => None
   end.

  Lemma eqobsrel_tail_rev_i_body_spec : forall E1 i1 E2 i2 O Q O' Q',
       eqobsrel_tail_rev_i_body i1 i2 O Q = Some (O', Q') ->
       equiv (req_mem_rel O' (interp_F Q')) E1 [i1] E2 [i2] (req_mem_rel O (interp_F Q)).
  Proof.
   destruct i1; simpl; intros E2 i2 O Q O' Q' H; try discriminate.
   destruct b; try discriminate.

   destruct i2; try discriminate.
   destruct b; try discriminate.
   generalize (Var.eqb_spec v v0); destruct (Var.eqb v v0); intros; try discriminate.
   inversion H0; clear H0; subst.
   assert (W:= T.inj_pair2 H3); clear H3; subst.
   generalize (E.eqb_spec e e0); destruct (E.eqb e e0); intros; subst; try discriminate.
   injection H; clear H; intros; subst.
   eapply equiv_strengthen;[ | apply equiv_assign].
   unfold upd_para, req_mem_rel, kreq_mem, andR; intuition.
   rewrite union_fv_expr_spec in H0.
   apply req_mem_weaken with (Vset.add v0 (Vset.remove v0 O)).
   rewrite VsetP.add_remove; auto with set.
   rewrite (@EqObs_e_fv_expr _ e0 k m1 m2).
   apply req_mem_update.
   apply req_mem_weaken with (2:= H0); auto with set.
   apply req_mem_weaken with (2:= H0); auto with set.

   destruct i2; try discriminate.
   destruct b; try discriminate.
   generalize (Var.eqb_spec v v0); destruct (Var.eqb v v0); intros; try discriminate.
   inversion H0; clear H0; subst.
   assert (W:= T.inj_pair2 H3); clear H3; subst.
   generalize (E.seqb_spec s s0); destruct (E.seqb s s0); intros; subst; try discriminate.
   injection H; clear H; intros; subst.
   eapply equiv_strengthen;[ | apply equiv_random].
   unfold forall_random, upd_para, req_mem_rel, kreq_mem, andR; intuition.
   unfold eq_support; intros.
   apply EqObs_d_fv_expr; apply req_mem_weaken with (2:= H0); auto with set.
   apply req_mem_weaken with (Vset.add v0 (Vset.remove v0 O)).
   rewrite VsetP.add_remove; auto with set.
   apply req_mem_update.
   apply req_mem_weaken with (2:= H0); auto with set.

   destruct i2; try discriminate.
   generalize (E.eqb_spec e e0); destruct (E.eqb e e0); intros; subst; try discriminate.
   case_eq (eqobsrel_tail_rev_aux (length l) (rev l) (rev l1) O Q); intros x1 x2 Ot Qt Heq.
   rewrite Heq in H; destruct x1; try discriminate; destruct x2; try discriminate.
   case_eq (eqobsrel_tail_rev_aux (length l0) (rev l0) (rev l2) O Q); intros y1 y2 Of Qf Heq2.
   rewrite Heq2 in H; destruct y1; try discriminate; destruct y2; try discriminate.
   injection H; clear H; intros; subst.
   apply equiv_cond.
   rewrite <- (rev_involutive l), <- (rev_involutive l1).
   apply eqobsrel_tail_rev_aux_spec with (1:= Heq).
   eapply equiv_strengthen;[ | apply equiv_nil].
   simpl; intros k m1 m2; unfold req_mem_rel, andR, impR,kreq_mem; intuition.
   apply req_mem_weaken with (2:= H).
   rewrite union_fv_expr_spec; auto with set.
   rewrite <- (rev_involutive l0), <- (rev_involutive l2).
   apply eqobsrel_tail_rev_aux_spec with (1:= Heq2).
   eapply equiv_strengthen;[ | apply equiv_nil].
   simpl; intros k m1 m2; unfold req_mem_rel, andR, impR,kreq_mem; intuition.
   apply req_mem_weaken with (2:= H).
   rewrite union_fv_expr_spec; auto with set.
   intros k m1 m2 (H1, H2).
   apply EqObs_e_fv_expr; apply req_mem_weaken with (2:= H1).
   rewrite union_fv_expr_spec; auto with set.
  Qed.

  End EOR_tail_cmd.

  (* Arrrrg !!! We Really need size based termination ...*)
  Fixpoint eqobsrel_tail_rev_i (n:nat) (i1 i2:I.instr) O Q {struct n} := 
   match n with
   | O => None
   | S n => eqobsrel_tail_rev_i_body (eqobsrel_tail_rev_i n) i1 i2 O Q
   end.

  Lemma eqobsrel_tail_rev_i_spec : forall n E1 i1 E2 i2 O Q O' Q',
       eqobsrel_tail_rev_i n i1 i2 O Q = Some (O', Q') ->
       equiv (req_mem_rel O' (interp_F Q')) E1 [i1] E2 [i2] (req_mem_rel O (interp_F Q)).
  Proof.
   induction n; simpl; intros; try discriminate.
   eapply eqobsrel_tail_rev_i_body_spec; eauto.
  Qed.

  Definition eqobsrel_tail_rev_i100 := eqobsrel_tail_rev_i 100.

 
  Section ABS_INTERP.
   Variable (k:nat).

  Section ABS_EVAL.
   Variable init : Mem.t k.

   Inductive abs_val : T.type -> Type :=
    | Aval : forall t : T.type, T.interp k t -> abs_val t
    | Avar : forall t : T.type, Var.var t -> abs_val t
    | Aop : forall op : O.op, dlist abs_val (O.targs op) -> abs_val (O.tres op)
    | Aexists : 
       forall t : T.type,
           (T.interp k t -> abs_val T.Bool) -> abs_val (T.List t) -> abs_val T.Bool
    | Aforall :
       forall t : T.type,
           (T.interp k t -> abs_val T.Bool) -> abs_val (T.List t) -> abs_val T.Bool
    | Afind :
       forall t : T.type,
           (T.interp k t -> abs_val T.Bool) -> abs_val (T.List t) -> abs_val t.

  Fixpoint interp_av (t:T.type) (v:abs_val t) :=
   match v in abs_val t0 return T.interp k t0 with
   | Aval t v => v
   | Avar t x => init x
   | Aop op args =>
     O.eval_op (k:=k) op (dmap (T.interp k) interp_av args)
   | Aexists t f l =>
     existsb (fun v : T.interp k t => interp_av (f v)) (interp_av l)
   | Aforall t f l =>
     forallb (fun v : T.interp k t => interp_av (f v)) (interp_av l)
   | Afind t f l =>
     find_default (fun v : T.interp k t => interp_av (f v)) (interp_av l) (T.default k t)
   end.

  Inductive abs_mem : Type :=
   | AMinit : abs_mem
   | AMupd : abs_mem -> forall t, Var.var t -> abs_val t -> abs_mem.

 
  Fixpoint interp_mem (m:abs_mem) : Mem.t k := 
    match m with 
    | AMinit => init
    | AMupd m t x v => (interp_mem m) {! x <-- interp_av v!}
    end.
 
   Fixpoint abs_get (m:abs_mem) tx (x:Var.var tx) : abs_val tx :=
    match m with
    | AMinit => Avar x
    | AMupd m ty y v =>
      if Var.eqb x y then
        match T.eq_dec ty tx with
        | left H =>
          match H in _ = t return abs_val t with
          | refl_equal => v
          end
        | right _ => (* never appear *) Avar x
        end
      else abs_get m x
     end.

  Fixpoint abs_eval (t : T.type) (e : E.expr t) (m : abs_mem) {struct e} : abs_val t :=
    match e in (E.expr t0) return abs_val t0 with
    | E.Ecte t0 c => Aval t0 (E.eval_cexpr k c)
    | E.Evar t0 v => abs_get m v
    | E.Eop op la =>
      Aop op (dmap abs_val (fun (t0 : T.type) (e0 : E.expr t0) => abs_eval e0 m) la)
    | E.Eexists t0 x e1 e2 =>
      Aexists (fun v : T.interp k t0 => abs_eval e1 (AMupd m x (Aval t0 v))) 
         (abs_eval e2 m)
    | E.Eforall t0 x e1 e2 =>
      Aforall (fun v : T.interp k t0 => abs_eval e1 (AMupd m x (Aval t0 v))) 
         (abs_eval e2 m)
    | E.Efind t0 x e1 e2 =>
      Afind (fun v : T.interp k t0 => abs_eval e1 (AMupd m x (Aval t0 v))) 
         (abs_eval e2 m)
    end.
  
  Lemma abs_get_correct : 
     forall m tx (x:Var.var tx),
     interp_av (abs_get m x) = (interp_mem m) x.
  Proof.
   induction m; simpl; intros; trivial.
   generalize (Var.eqb_spec  x v); destruct (Var.eqb x v); intros.
   inversion H; clear H; subst.
   rewrite (T.inj_pair2 H2); clear H2.
   case_eq (T.eq_dec t t); intros.
   rewrite (T.UIP_refl e). 
   symmetry; apply Mem.get_upd_same. 
   elim (T.eq_dec_r H); trivial.
   rewrite Mem.get_upd_diff; auto.
  Qed.
  
  Lemma abs_eval_correct : forall t (e:E.expr t) m,
    interp_av (abs_eval e m) = E.eval_expr e (interp_mem m).
  Proof.
   induction e using E.expr_ind2 with
    (Pl := fun lt la => forall m,
       dmap (T.interp k) interp_av 
         (dmap abs_val (fun (t0 : T.type) (e0 : E.expr t0) => abs_eval e0 m) la) =
       dmap (T.interp k)
           (fun (t0 : T.type) (e0 : E.expr t0) => E.eval_expr e0 (interp_mem m)) la); simpl; intros; trivial.
   apply abs_get_correct.
   rewrite IHe; trivial.
   rewrite IHe2; generalize (E.eval_expr e2 (interp_mem m)).
   induction i; simpl; trivial.
   rewrite IHi, IHe1; trivial.
   rewrite IHe2; generalize (E.eval_expr e2 (interp_mem m)).
   induction i; simpl; trivial.
   rewrite IHi, IHe1; trivial.
   rewrite IHe2; generalize (E.eval_expr e2 (interp_mem m)); intros i; unfold find_default.
   replace (find (fun v0 : T.interp k t => interp_av (abs_eval e1 (AMupd m v (Aval t v0)))) i)
   with (find (fun v0 : T.interp k t => E.eval_expr e1 (interp_mem m {!v <-- v0!})) i).
   trivial.
   induction i; simpl; trivial.
   rewrite IHi, IHe1; trivial.
   rewrite IHe, IHe0; trivial.
  Qed.

  Inductive abs_support : T.type -> Type :=
   | ADbool : abs_support T.Bool
   | ADnat : abs_val T.Nat -> abs_support T.Nat
   | ADZ : abs_val T.Zt -> abs_val T.Zt -> abs_support T.Zt
   | ADuser : forall t : T.type, US.usupport t -> abs_support t
   | ADprod : forall t1 t2, abs_support t1 -> abs_support t2 -> abs_support (T.Pair t1 t2).

   Fixpoint abs_eval_support t (s:E.support t) m :=
    match s in E.support t0 return abs_support t0 with 
    | E.Dbool => ADbool  
    | E.Dnat e => ADnat (abs_eval e m)
    | E.DZ e1 e2 => ADZ (abs_eval e1 m) (abs_eval e2 m)
    | E.Duser t s => ADuser s
    | E.Dprod t1 t2 s1 s2 => ADprod (abs_eval_support s1 m) (abs_eval_support s2 m)
    end.

   Fixpoint interp_asup t (s:abs_support t) :=
    match s in abs_support t0 return (list (T.interp k t0)) with
    | ADbool => true :: false :: nil 
    | ADnat e => seq 0 (S (interp_av e))
    | ADZ e1 e2 => Z_support (interp_av e1) (interp_av e2)
    | ADuser t s => US.eval k s
    | ADprod t1 t2 s1 s2 => list_prod (interp_asup s1) (interp_asup s2)
    end.

   Lemma abs_eval_support_correct : forall t (s:E.support t) m,
     interp_asup (abs_eval_support s m) = E.eval_support s (interp_mem m).
   Proof.
    induction s; simpl; trivial; intros.
    rewrite abs_eval_correct; trivial.
    repeat rewrite abs_eval_correct; trivial.
    rewrite IHs1, IHs2; trivial.
   Qed.

  End ABS_EVAL.
  
  Inductive abs_formula : Type :=
    | AFbase : abs_mem -> abs_mem -> abs_formula 
    | AFand  : abs_formula -> abs_formula -> abs_formula 
    | AFor  : abs_formula -> abs_formula -> abs_formula 
    | AFimp  : abs_formula -> abs_formula -> abs_formula 
    | AFnot  : abs_formula -> abs_formula 
    | AFbool1 : abs_val T.Bool -> abs_formula 
    | AFbool2 : abs_val T.Bool -> abs_formula 
    | AFeq_assoc_except : forall t1 t2, abs_val t1 -> 
      abs_val (T.List (T.Pair t1 t2)) -> abs_val (T.List (T.Pair t1 t2)) -> abs_formula
    | AFforall_random :
      forall t, abs_support t -> (T.interp k t -> abs_formula) -> abs_formula.

  Variable (init1 init2 : Mem.t k).

  Fixpoint interp_aF (F:abs_formula) :=
    match F with
    | AFbase m1 m2 => @iB k (interp_mem init1 m1) (interp_mem init2 m2)
    | AFand F1 F2 => interp_aF F1 /\ interp_aF F2
    | AFor F1 F2 => interp_aF F1 \/ interp_aF F2
    | AFimp F1 F2 => interp_aF F1 -> interp_aF F2
    | AFnot F => ~interp_aF F
    | AFbool1 v => is_true (interp_av init1 v)
    | AFbool2 v => is_true (interp_av init2 v)
    | AFeq_assoc_except t1 t2 v l1 l2 =>
       let v := interp_av init1 v in
       let l1 := interp_av init1 l1 in
       let l2 := interp_av init2 l2 in
       forall r,  
        r <> v ->
        O.interp_op k (O.Oin_dom _ _) r l1 =
        O.interp_op k (O.Oin_dom _ _) r l2 /\
        O.interp_op k (O.Oimg _ _) r l1 =
        O.interp_op k (O.Oimg _ _) r l2
    | AFforall_random t d f => 
      forall v, In v (interp_asup init1 d) -> interp_aF (f v)
    end.

  Fixpoint abs_eval_F (F:formula) (m1 m2:abs_mem) : abs_formula :=
    match F with
    | Fbase  => AFbase m1 m2
    | Fupd1 F t x e => abs_eval_F F (AMupd m1 x (abs_eval e m1)) m2
    | Fupd2 F t x e => abs_eval_F F m1 (AMupd m2 x (abs_eval e m2))
    | Fupd_p F t x e => abs_eval_F F (AMupd m1 x (abs_eval e m1)) (AMupd m2 x (abs_eval e m2))
    | Fand F1 F2 => AFand (abs_eval_F F1 m1 m2) (abs_eval_F F2 m1 m2)
    | For F1 F2 => AFor (abs_eval_F F1 m1 m2) (abs_eval_F F2 m1 m2)
    | Fimp F1 F2 => AFimp (abs_eval_F F1 m1 m2) (abs_eval_F F2 m1 m2)
    | Fnot F => AFnot (abs_eval_F F m1 m2)
    | Fbool1 e => AFbool1 (abs_eval e m1)
    | Fbool2 e => AFbool2 (abs_eval e m2)
    | Feq_assoc_except t1 t2 v l =>
      AFeq_assoc_except (abs_eval v m1) (abs_eval l m1) (abs_eval l m2)
    | Fforall_random t d x F =>
      AFforall_random (abs_eval_support d m1) 
       (fun v : T.interp k t =>
         abs_eval_F F (AMupd m1 x (Aval t v)) (AMupd m2 x (Aval t v)))
    end.

  Lemma abs_eval_F_correct : forall F m1 m2,
    interp_aF (abs_eval_F F m1 m2) <->
    interp_F F (interp_mem init1 m1) (interp_mem init2 m2).
 Proof.
  induction F; intros; simpl; try tauto.
  rewrite IHF; simpl; unfold upd1.
  rewrite abs_eval_correct; tauto.
  rewrite IHF; simpl; unfold upd2.
  rewrite abs_eval_correct; tauto.
  rewrite IHF; unfold upd_para; simpl; repeat rewrite abs_eval_correct; tauto.
  unfold andR; rewrite IHF1, IHF2; tauto.
  unfold orR; rewrite IHF1, IHF2; tauto.
  unfold impR; rewrite IHF1, IHF2; tauto.
  unfold notR; rewrite IHF; tauto. 
  unfold EP1; rewrite abs_eval_correct; tauto.
  unfold EP2; rewrite abs_eval_correct; tauto.
  repeat rewrite abs_get_correct; tauto.
  unfold forall_random; rewrite abs_eval_support_correct; split; intros.
  assert (W:= H _ H0); rewrite IHF in W; exact W.
  rewrite IHF; simpl; auto.
 Qed.

 End ABS_INTERP.

 Definition eqobsrel_tail_n n c1 c2 O Q:= 
   let (c1', c2', O', Q') := 
     eqobsrel_tail_rev_aux eqobsrel_tail_rev_i100 n (rev c1) (rev c2) O Q in
   (Quad c1' c2' O' (fun k => abs_eval_F Q' (AMinit k) (AMinit k))).


  Lemma eqobsrel_tail_n_correct : 
       forall n P E1 c1 E2 c2 O Q c1' c2' O' Q',
       eqobsrel_tail_n n c1 c2 O Q = Quad c1' c2' O' Q' ->
       equiv P E1 c1' E2 c2' (req_mem_rel O' (fun k m1 m2 => interp_aF m1 m2 (Q' k))) ->
       equiv P E1 c1 E2 c2 (req_mem_rel O (interp_F Q)).
  Proof.
   unfold eqobsrel_tail_n, eqobsrel_tail_rev_i100; intros.
   rewrite <- (rev_involutive c1), <- (rev_involutive c2).
   case_eq (eqobsrel_tail_rev_aux (eqobsrel_tail_rev_i 100) n (rev c1) (rev c2)
           O Q); intros c1'' c2'' O'' Q'' Heq;
   rewrite Heq in H; injection H; clear H; intros; subst.
   assert (equiv P E1 c1' E2 c2' (req_mem_rel O' (interp_F Q''))).
     eapply equiv_weaken;[ | apply H0].
     apply req_mem_rel_weaken; auto with set.
     intros k m m'; rewrite abs_eval_F_correct; simpl; trivial.
   apply eqobsrel_tail_rev_aux_spec with (2:= Heq); trivial.
   apply eqobsrel_tail_rev_i_spec.
  Qed.

 End INTERP.
   
End Make.
