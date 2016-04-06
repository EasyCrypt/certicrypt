(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * Instructions.v : Definition of basic instructions and boolean equality 
   over commands *)


Set Implicit Arguments.
Set Asymmetric Patterns.

Require Export Expressions.


Module Type INSTR (UT:UTYPE) (T:TYPE UT) (Var:VAR UT T) (Proc:PROC UT T)
 (Uop : UOP UT T) (O:OP UT T Uop) (US:USUPPORT UT T)
 (Mem: MEM UT T Var)
 (E : EXPR UT T Var Uop O US Mem).

 Inductive baseInstr : Type := 
 | Assign : forall t, Var.var t -> E.expr t -> baseInstr
 | Random : forall t, Var.var t -> E.support t -> baseInstr.

 (* Definition of instructions *)

 Reserved Notation "'cmd'".

 Inductive instr : Type :=
 | Instr : baseInstr -> instr
 | Cond  : E.expr T.Bool -> cmd -> cmd -> instr
 | While : E.expr T.Bool -> cmd -> instr
 | Call  : forall t (v:Var.var t) (f:Proc.proc t), E.args (Proc.targs f) -> instr
  where "'cmd'" := (list instr).

 Definition t := instr.

 Parameter eqb : instr -> instr -> bool.  

 Parameter eqb_spec : forall x y, if eqb x y then x = y else x <> y.

 Parameter ceqb : cmd -> cmd -> bool.

 Parameter ceqb_spec : forall x y, if ceqb x y then x = y else x <> y.

 Notation Local "[ x ; .. ; y ]" := 
  (@cons instr x .. (@cons instr y (@nil instr)) ..).

 Notation Local "'If' e 'then' c1 'else' c2" := (Cond e c1 c2) (at level 65).

 Notation Local "'If' e '_then' c" := (Cond e c nil) (at level 65).

 Notation Local "'while' e 'do' c" := (While e c) (at level 65).

 Notation Local "d '<c-' f 'with' a" := (Call d f a) (at level 61). 

 Notation Local "x '<-' e" := (Instr (Assign x e)) (at level 65).

 Notation Local " x '<$-' d " := (Instr (Random x d)) (at level 65).

 Parameter instr_ind2 : forall (Pi: instr -> Prop) (Pc:cmd -> Prop),
  (forall i, Pi (Instr i)) ->
  (forall b c1 c2, Pc c1 -> Pc c2 -> Pi (If b then c1 else c2)) ->
  (forall b c, Pc c -> Pi (while b do c)) ->
  (forall t (x:Var.var t) (f:Proc.proc t) (a:E.args (Proc.targs f)), 
   Pi (x <c- f with a)) ->
  (Pc nil) ->
  (forall i c, Pi i -> Pc c -> Pc (i::c)) ->
  forall i, Pi i.

 Parameter cmd_ind : forall (Pi: instr -> Prop) (Pc:cmd -> Prop),
  (forall i, Pi (Instr i)) ->
  (forall b c1 c2, Pc c1 -> Pc c2 -> Pi (If b then c1 else c2)) ->
  (forall b c, Pc c -> Pi (while b do c)) ->
  (forall t (x:Var.var t) (f:Proc.proc t) (a:E.args (Proc.targs f)), 
   Pi (x <c- f with a)) ->
  (Pc nil) ->
  (forall i c, Pi i -> Pc c -> Pc (i::c)) ->
  forall c, Pc c.

 Parameter cmd_ind2 : forall (Pi: instr -> Prop) (Pc:list instr -> Prop),
  (forall i, Pi (Instr i)) ->
  (forall b c1 c2, Pc c1 -> Pc c2 -> Pi (If b then c1 else c2)) ->
  (forall b c, Pc c -> Pi (while b do c)) ->
  (forall t (x:Var.var t) (f:Proc.proc t) (a:E.args (Proc.targs f)), 
   Pi (x <c- f with a)) ->
  (Pc nil) ->
  (forall i c, Pi i -> Pc c -> Pc (i::c)) ->
  (forall i, Pi i) /\ (forall c, Pc c).

End INSTR. 


Module MakeInstr (UT:UTYPE) (T:TYPE UT) (Var:VAR UT T) (Proc:PROC UT T)
 (Uop : UOP UT T) (O:OP UT T Uop) (US:USUPPORT UT T)
 (Mem: MEM UT T Var)
 (E : EXPR UT T Var Uop O US Mem) <: INSTR UT T Var Proc Uop O US Mem E.
 
 Inductive baseInstr : Type := 
 | Assign : forall t, Var.var t -> E.expr t -> baseInstr
 | Random : forall t, Var.var t -> E.support t -> baseInstr.

 (* Definition of instructions *)

 Reserved Notation "'cmd'".

 Inductive instr : Type :=
 | Instr : baseInstr -> instr
 | Cond  : E.expr T.Bool -> cmd -> cmd -> instr
 | While : E.expr T.Bool -> cmd -> instr
 | Call  : forall t (v:Var.var t) (f:Proc.proc t), E.args (Proc.targs f) -> instr
  where "'cmd'" := (list instr).

 Definition t := instr.

 Notation Local "[ x ; .. ; y ]" := 
  (@cons instr x .. (@cons instr y (@nil instr)) ..).

 Notation Local "'If' e 'then' c1 'else' c2" := (Cond e c1 c2) (at level 65).

 Notation Local "'If' e '_then' c" := (Cond e c nil) (at level 65).

 Notation Local "'while' e 'do' c" := (While e c) (at level 65).

 Notation Local "d '<c-' f 'with' a" := (Call d f a) (at level 61). 

 Notation Local "x '<-' e" := (Instr (Assign x e)) (at level 65).

 Notation Local " x '<$-' d " := (Instr (Random x d)) (at level 65).

 Lemma instr_ind2 : forall (Pi: instr -> Prop) (Pc:cmd -> Prop),
  (forall i, Pi (Instr i)) ->
  (forall b c1 c2, Pc c1 -> Pc c2 -> Pi (If b then c1 else c2)) ->
  (forall b c, Pc c -> Pi (while b do c)) ->
  (forall t (x:Var.var t) (f:Proc.proc t) (a:E.args (Proc.targs f)), 
   Pi (x <c- f with a)) ->
  (Pc nil) ->
  (forall i c, Pi i -> Pc c -> Pc (i::c)) ->
  forall i, Pi i.
 Proof.
  intros Pi Pc Hb Hif Hw Hca Hnil Hcons.
  fix instr_rect2 1.
  intros i; case i; intros.
  apply Hb.
  apply Hif.
  induction l; auto.
  induction l0; auto.
  apply Hw.
  induction l; auto.
  apply Hca.
 Qed.

 Lemma cmd_ind : forall (Pi: instr -> Prop) (Pc:cmd -> Prop),
  (forall i, Pi (Instr i)) ->
  (forall b c1 c2, Pc c1 -> Pc c2 -> Pi (If b then c1 else c2)) ->
  (forall b c, Pc c -> Pi (while b do c)) ->
  (forall t (x:Var.var t) (f:Proc.proc t) (a:E.args (Proc.targs f)), 
   Pi (x <c- f with a)) ->
  (Pc nil) ->
  (forall i c, Pi i -> Pc c -> Pc (i::c)) ->
  forall c, Pc c.
 Proof.
  intros; induction c; auto.
  apply H4; auto.
  eapply instr_ind2; eauto.
 Qed.

 Lemma cmd_ind2 : forall (Pi: instr -> Prop) (Pc:list instr -> Prop),
  (forall i, Pi (Instr i)) ->
  (forall b c1 c2, Pc c1 -> Pc c2 -> Pi (If b then c1 else c2)) ->
  (forall b c, Pc c -> Pi (while b do c)) ->
  (forall t (x:Var.var t) (f:Proc.proc t) (a:E.args (Proc.targs f)), 
   Pi (x <c- f with a)) ->
  (Pc nil) ->
  (forall i c, Pi i -> Pc c -> Pc (i::c)) ->
  (forall i, Pi i) /\ (forall c, Pc c).
 Proof.
  intros; split; intros;[eapply instr_ind2 | eapply cmd_ind]; eauto.
 Qed.

 Definition bi_eqb (x y:baseInstr) : bool :=
  match x, y with
  | Assign t1 v1 e1, Assign t2 v2 e2 =>
    if Var.veqb v1 v2 then E.eqb e1 e2 else false
  | Random t1 v1 s1, Random t2 v2 s2 =>
    if Var.veqb v1 v2 then E.seqb s1 s2 else false
  | _, _ => false
  end.

 Lemma bi_eqb_spec : forall x y, if bi_eqb x y then x = y else x <> y.  
 Proof.
  destruct x; destruct y; simpl; try (intro; discriminate).
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); intros; subst.
  inversion H; clear H; subst.
  rewrite (T.inj_pair2 H3); clear H2 H3.
  generalize (E.eqb_spec e e0); destruct (E.eqb e e0); intros; subst; trivial.
  intros Heq; apply H; inversion Heq.  
  apply (T.inj_pair2 H1).
  intros Heq; apply H; inversion Heq; trivial. 
  subst; rewrite (T.inj_pair2 H2); constructor. 
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); intros; subst.
  inversion H; clear H; subst.
  rewrite (T.inj_pair2 H3); clear H2 H3.
  generalize (E.seqb_spec s s0); destruct (E.seqb s s0); intros; subst; trivial.
  intros Heq; apply H; inversion Heq.  
  apply (T.inj_pair2 H1).
  intros Heq; apply H; inversion Heq; trivial. 
  subst; rewrite (T.inj_pair2 H2); constructor. 
 Qed.

 Fixpoint eqb (i i' : t) {struct i} : bool :=
  match i, i' with
  | Instr i, Instr i' => bi_eqb i i' 
  | Cond e c1 c2, Cond e' c1' c2' => 
    if E.eqb e e' then 
     if eqb_list eqb c1 c1' then eqb_list eqb c2 c2'
     else false
    else false
  | While e c, While e' c' => 
    if E.eqb e e' then eqb_list eqb c c' else false
  | Call t x f a, Call t' x' f' a' => 
    if Var.veqb x x' then 
     if Proc.eqb f f' then E.args_eqb a a' 
     else false
    else false
  | _, _ => false
  end. 

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  induction x using instr_ind2 with
   (Pc := fun x => forall y, if eqb_list eqb x y then x = y else x <> y);
   destruct y; simpl; try (intro; discriminate).
  generalize (bi_eqb_spec i b); destruct (bi_eqb i b); intros; subst; trivial.
  intros Heq; apply H; inversion Heq; trivial.
  generalize (E.eqb_spec b e); destruct (E.eqb b e); intros; subst.
  generalize (IHx l); destruct (eqb_list eqb c1 l); clear IHx; intros; subst.
  generalize (IHx0 l0); destruct (eqb_list eqb c2 l0); clear IHx0;
   intros; subst; trivial.
  intros Heq; apply H; inversion Heq; trivial.
  intros Heq; apply H; inversion Heq; trivial.
  intros Heq; apply H; inversion Heq; trivial.
  generalize (E.eqb_spec b e); destruct (E.eqb b e); intros; subst.
  generalize (IHx l); destruct (eqb_list eqb c l); clear IHx;
   intros; subst; trivial.
  intros Heq; apply H; inversion Heq; trivial.
  intros Heq; apply H; inversion Heq; trivial.
  generalize (Var.veqb_spec_dep x v); destruct (Var.veqb x v); intros; subst.
  inversion H; clear H; subst.
  rewrite (T.inj_pair2 H3); clear H2 H3.
  generalize (Proc.eqb_spec f f0); destruct (Proc.eqb f f0); 
   intros; subst; trivial.
  generalize (E.args_eqb_spec a a0); destruct (E.args_eqb a a0); 
   intros; subst; trivial.
  intros Heq; apply H; inversion Heq.
  apply (Proc.inj_pair2 (T.inj_pair2 H1)).
  intros Heq; apply H; inversion Heq.
  apply (T.inj_pair2 H1).
  intros Heq; apply H; inversion Heq; trivial.
  subst; rewrite (T.inj_pair2 H2); constructor.
  trivial.
  generalize (IHx t0); destruct (eqb x t0); intros; subst.
  generalize (IHx0 y); destruct (eqb_list eqb c y); intros; subst; trivial.
  intros Heq; apply H; inversion Heq; trivial.
  intros Heq; apply H; inversion Heq; trivial. 
 Qed.

 Definition ceqb : cmd -> cmd -> bool := eqb_list eqb.
 
 Lemma ceqb_spec : forall x y, if ceqb x y then x = y else x <> y.
 Proof.
  induction x; destruct y; simpl; trivial; try (intro; discriminate).
  generalize (eqb_spec a i); destruct (eqb a i); intros; subst.
  generalize (IHx y); destruct (ceqb x y); intros; subst; trivial.
  intros Heq; apply H; inversion Heq; trivial.
  intros Heq; apply H; inversion Heq; trivial.
 Qed.

End MakeInstr.
