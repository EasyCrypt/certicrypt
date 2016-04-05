(** * EasyCrypt.v : Validation of EasyCrypt pRHL derivations *)

Set Implicit Arguments.

Require Export BuildTac.


Module Make (Entries:BUILD_ENTRIES).
  
 Module Tactics := BuildTac.Make Entries.
 Export Tactics.

 Close Scope nat_scope.
 Lemma Var_eqb_veqb : forall t1 (v1:Var.var t1) t2 (v2:Var.var t2),
  Var.eqb v1 v2 = Var.veqb v1 v2.
 Proof.
  intros; auto.
  generalize (Var.eqb_spec v1 v2).
  generalize (Var.veqb_spec_dep v1 v2).
  destruct (Var.eqb v1 v2); destruct (Var.veqb v1 v2); intros; trivial.
  elim H; subst; inversion H0; subst; constructor.
  inversion H; subst; apply T.inj_pair2 in H4; subst; elim H0; trivial.
 Qed.

 Lemma veqb_type_diff : forall t1 (v1:Var.var t1) t2 (v2:Var.var t2), 
  t1 <> t2 -> Var.veqb v1 v2 = false.
 Proof.
  intros.
  generalize (Var.veqb_spec_dep v1 v2).
  destruct (Var.veqb v1 v2); intros; trivial.
  inversion H0; subst; elim H; auto.
 Qed.

 Lemma veqb_true : forall t (v1:Var.var t) (v2:Var.var t), 
  Var.veqb v1 v2 = true -> v1 = v2.
 Proof.
  intros.
  generalize (Var.veqb_spec v1 v2).
  rewrite H; auto.
 Qed.

 Lemma veqb_false : forall t (v1:Var.var t) (v2:Var.var t), 
  Var.veqb v1 v2 = false -> v1 <> v2.
 Proof.
  intros.
  generalize (Var.veqb_spec v1 v2).
  rewrite H; auto.
 Qed.
 
 Lemma veqb_refl : forall t (v:Var.var t), 
  Var.veqb v v = true.
 Proof.
  intros.
  generalize (Var.veqb_spec v v).
  destruct (Var.veqb v v); intros; trivial.
  elim H; trivial.
 Qed.
 
 Lemma Var_eqb_sym : forall t1 (v1:Var.var t1) t2 (v2:Var.var t2),
  Var.eqb v1 v2 = Var.eqb v2 v1.
 Proof.
  intros.
  generalize (Var.eqb_spec v1 v2).
  case_eq (Var.eqb v1 v2); intros.
  rewrite H0 in *; auto.
  symmetry.
  apply not_true_is_false; intro.
  apply VarP.eq_eqb_r in H1.
  rewrite H1 in H0; elim H0; trivial.
 Qed.

 Lemma veqb_sym : forall t1 (v1:Var.var t1) t2 (v2:Var.var t2),
  Var.veqb v1 v2 = Var.veqb v2 v1.
 Proof.
  intros.
  repeat rewrite <- Var_eqb_veqb.
  apply Var_eqb_sym.
 Qed.

 (* Sides *)
 Definition side_left  := true.
 Definition side_right := false.
     
 (* EasyCrypt Variables *)
 Inductive lvar (t:T.type) : Type :=
 | VarLeft  : Var.var t -> lvar t
 | VarRight : Var.var t -> lvar t
 | VarLogic : Var.var t -> lvar t.

 Notation "v '<1>'" := (@VarLeft _ v)  (at level 3).
 Notation "v '<2>'" := (@VarRight _ v) (at level 3).

 Definition lvar_eqb t1 t2 (lv1:lvar t1) (lv2:lvar t2) :=
  match lv1, lv2 with
   | VarLeft v1, VarLeft v2 => Var.veqb v1 v2
   | VarRight v1, VarRight v2 => Var.veqb v1 v2
   | VarLogic v1, VarLogic v2 => Var.veqb v1 v2
   | _, _ => false
  end.

 Lemma lvar_eqb_spec_dep : forall t1 (e1:lvar t1) t2 (e2:lvar t2),
  if lvar_eqb e1 e2 
  then eq_dep T.type lvar t1 e1 t2 e2
  else ~eq_dep T.type lvar t1 e1 t2 e2.
 Proof.
  destruct e1; destruct e2; simpl; try (intros Heq; inversion Heq; fail).
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); intros.
  inversion H; trivial.
  intros H1; elim H; inversion H1; trivial.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); intros.
  inversion H; trivial.
  intros H1; elim H; inversion H1; trivial.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); intros.
  inversion H; trivial.
  intros H1; elim H; inversion H1; trivial.
 Qed.

 Lemma lvar_eqb_spec : forall t (e1 e2:lvar t),
  if lvar_eqb e1 e2 then e1 = e2 else e1 <> e2.
 Proof.
  intros t e1 e2.
  generalize (lvar_eqb_spec_dep e1 e2); destruct (lvar_eqb e1 e2); intros.
  inversion H. apply T.inj_pair2 with (1:= H2).
  intros Heq; elim H; rewrite Heq; trivial.
 Qed.

 (** Valuation of logical variables *)
 Record lvar_val k := LVV { t : T.type; var : Var.var t; val : T.interp k t}.
 Definition lmem k := list (lvar_val k).

 (** Gets the value of a logical variable in a valuation *)
 Fixpoint assoc k t (v:Var.var t) (l:lmem k) : T.interp k t :=
  match l with
   | nil => T.default k t
   | LVV t' v' x :: l =>
     if Var.veqb v v' then
     match T.eq_dec t' t with
      | left H =>
        match H in (_ = t1) return T.interp k t1 with
        | eq_refl => x
        end
      | _ => T.default k t
     end
     else assoc v l
  end.

 Lemma assoc_same : forall k l t (v1:Var.var t) (v2:Var.var t) (x:T.interp k t),
  Var.veqb v1 v2 = true ->
  assoc v1 ({| t := t; var := v2; val := x |} :: l) = x.
 Proof.
  simpl; intros; rewrite H, Teq_dep_refl; trivial.
 Qed.

 Lemma assoc_diff : forall k l t1 t2
  (v1:Var.var t1) (v2:Var.var t2) (x:T.interp k t2),
  Var.veqb v1 v2 = false ->
  assoc v1 ({| t := t2; var := v2; val := x |} :: l) = assoc v1 l .
 Proof.
  simpl; intros; rewrite H; trivial.
 Qed.

 Lemma assoc_diff_type : forall k (l:lmem k) t1 t2 
  (v1:Var.var t1) (v2:Var.var t2) x,
  t1 <> t2 ->
  assoc v1 ({| t := t2; var := v2; val := x |} :: l) = assoc v1 l .
 Proof.
  intros.
  rewrite assoc_diff; trivial.
  apply veqb_type_diff; trivial.
 Qed.
 
 Lemma assoc_eq : forall k t' (v:Var.var t') (a:lvar_val k) l1 l2,   
  assoc v l1 = assoc v l2 ->
  assoc v (a :: l1) = assoc v (a :: l2).
 Proof.
  intros; simpl.
  destruct a; case (Var.veqb v var0); trivial. 
 Qed.

 Opaque assoc.

 (** Domain of a valuation: set of logical vars appearing in a valuation *)
 Definition dom k (l:lmem k) : Vset.t :=
  fold_right (fun x X => Vset.add x.(var) X) Vset.empty l.

 (** Cast a value to an equivalent type *)
 Definition convert : forall k t1 t2 (x:T.interp k t1) (W:t1 = t2), T.interp k t2.
  intros; subst; exact x.
 Defined.

 (** The value of a logical var coincides with a given value when 
    the var appears in the assignment in the head in the valuation and
    the values are convertible, or when the tail of the valuation maps
    the variable to the given value 
 *)
 Lemma assoc_case : forall k (l:lmem k) t1 t2 
  (v1:Var.var t1) (v2:Var.var t2) (a:T.interp k t1) (x:T.interp k t2),
  (forall (W:t1 = t2), Var.veqb v1 v2 = true -> x = convert k a W) ->
  (Var.veqb v1 v2 = false -> assoc v1 l = a) ->
  assoc v1 ({| t := t2; var := v2; val := x |} :: l) = a.
 Proof.
  intros.
  generalize (Var.veqb_spec_dep v1 v2).   
  case_eq (Var.veqb v1 v2); intros.
  simpl.
  inversion H2; subst.
  rewrite assoc_same; trivial.
  rewrite (H (eq_refl _)); trivial.
  rewrite assoc_diff; trivial.
  apply H0; trivial.
 Qed.
 
 (** Equality of types is decidable *)
 Lemma Teq_dec : forall (t1 t2:T.type),
  sumbool (t1 = t2) (t1 <> t2).
 Proof.
  intros t1 t2; generalize (T.eqb_spec t1 t2); destruct (T.eqb t1 t2); auto. 
 Qed.

 (** Equality of list of types is decidable *)
 Lemma Tlist_eq_dec : forall (t1 t2:list T.type),
  sumbool (t1 = t2) (t1 <> t2).
 Proof.
  induction t1; intros; destruct t2; auto.
  right; intro; discriminate.
  right; intro; discriminate.
  destruct (Teq_dec a t0); subst.
  destruct (IHt1 t2); subst.
  auto.
  right; intro; inversion H; elim n; trivial.   
  right; intro; inversion H; elim n; trivial.   
 Qed.

 (** Convert Boolean equality of EasyCrypt variables to Prop *)
 Ltac veqb_prop :=
  match goal with
   | [ H : Var.veqb ?v1 ?v2 = false |- _ ] => apply veqb_false in H
   | [ H : Var.veqb ?v1 ?v2 = true |- _ ] => apply veqb_true in H
  end; try veqb_prop.
 
 (** Elim contradicting equalities *)
 Ltac elim_neq :=
  match goal with
   | [ H1 : ?a = ?b, H2 : ?a <> ?b |- _] => elim H2; apply H1
   | [ H : ?a <> ?a |- _] => elim H; trivial
  end.
 
 (** Try to get the value of a variable in a valuation *)
 Ltac assoc_case :=
  apply assoc_case; intros; subst;
   [ unfold convert, eq_rect_r; simpl;
     try (rewrite <- eq_rect_eq_dec; [ | apply Teq_dec ] )
   | simpl];
   try veqb_prop; trivial; repeat elim_neq.
 
 Lemma assoc_comm :  forall k l (a1 a2:lvar_val k) t (v:Var.var t),
  Var.veqb (var a1) (var a2) = false ->
  assoc v (a1 :: a2 :: l) = assoc v (a2 :: a1 :: l).
 Proof.
  intros; auto.
  destruct a1; destruct a2; simpl in *.
  assoc_case.
  symmetry.
  assoc_case.
  assoc_case.
  assoc_case.
  symmetry.
  assoc_case. 
  symmetry.
  assoc_case. 
  assoc_case. 
 Qed.
   

 (** Eval an EasyCrypt variable (logic or tagged) given a pair of
     memories and a valuation for logical variables *)
 Definition Eval_LvBase k (m1 m2:Mem.t k) (l:lmem k) t (v:lvar t) : T.interp k t :=
  match v with
   | VarLeft v'  => m1 v'
   | VarRight v' => m2 v'
   | VarLogic v' => assoc v' l
  end.

 (* EasyCrypt expressions *)
 Inductive Exp : T.type -> Type :=
 | Ecnst   :> forall t : T.type, E.cexpr t -> Exp t
 | Evar    :> forall t : T.type, lvar t -> Exp t
 | Eapp    :  forall op : O.op, dlist Exp (O.targs op) -> Exp (O.tres op)
 | Eexists :  forall t : T.type,
               Var.var t -> Exp T.Bool -> Exp (T.List t) -> Exp T.Bool
 | Eforall :  forall t : T.type,
               Var.var t -> Exp T.Bool -> Exp (T.List t) -> Exp T.Bool
 | Efind   :  forall t : T.type,
               Var.var t -> Exp T.Bool -> Exp (T.List t) -> Exp t.
 
 Notation "x '?=' y" := (@Eapp (O.Oeq_ _) (dcons _ x (dcons _ y (dnil _)))).
 Definition Eeq t (x y : Exp t) : Exp T.Bool := x ?= y.
 
 Notation "'efst' p " := (@Eapp (O.Ofst _ _) (dcons _  p (dnil _))) (at level 0).
 Notation "'esnd' p " := (@Eapp (O.Osnd _ _) (dcons _  p (dnil _))) (at level 0).
 
 Notation "'(' x '!' y ')'" := 
  (@Eapp (O.Opair _ _) (dcons _ x (dcons _ y (dnil _)))).
 Definition Epair t1 t2 (e1 : Exp t1) (e2 : Exp t2) := (e1 ! e2).

 Notation "b '_?' x '_?:' y" := 
  (@Eapp (O.Oif _) (dcons _ b (dcons _ x (dcons _ y (dnil _))))) 
  (at level 60).
 Definition Eif t c (e1 e2 : Exp t) := c _? e1 _?: e2.

 Notation "x '!+' y " := 
  (@Eapp O.OZadd (dcons _ x (dcons _ y (dnil _)))) 
  (at level 40, left associativity).
 Definition EZplus e1 e2 := e1 !+ e2.

 Notation "x '!*' y " := 
  (@Eapp O.OZmul (dcons _ x (dcons _ y (dnil _)))) 
  (at level 40, left associativity).
 Definition EZmult e1 e2 := e1 !* e2.

 Notation "x '!-' y " := 
  (@Eapp O.OZsub (dcons _ x (dcons _ y (dnil _)))) 
  (at level 40, left associativity).
 Definition EZsub e1 e2 := e1 !- e2.

 Notation "x '!<=' y " := 
  (@Eapp O.OZle (dcons _ x (dcons _ y (dnil _)))) 
  (at level 40, left associativity).
 Definition EZle e1 e2 := e1 !<= e2.
 
 Notation "x '!<' y " := 
  (@Eapp O.OZlt (dcons _ x (dcons _ y (dnil _)))) 
  (at level 40, left associativity).
 Definition EZlt e1 e2 := e1 !< e2.
 
 Notation "x '!>=' y " := 
  (@Eapp O.OZge (dcons _ x (dcons _ y (dnil _)))) 
  (at level 40, left associativity).
 Definition EZge e1 e2 := e1 !>= e2.
 
 Notation "x '!>' y " := 
  (@Eapp O.OZgt (dcons _ x (dcons _ y (dnil _)))) 
  (at level 40, left associativity).
 Definition EZgt e1 e2 := e1 !> e2.
 
 Notation "x '!%' y " :=
  (@Eapp O.OZmod (dcons _ x (dcons _ y (dnil _)))) 
  (at level 40, left associativity).
 Definition EZmod e1 e2 := e1 !% e2.
 
 Notation "x '!/\' y " := 
  (@Eapp O.Oand (dcons _ x (dcons _ y (dnil _)))) 
  (at level 40, left associativity).
 Definition Eand e1 e2 := e1 !/\ e2.
 
 Notation "x '!\/' y " := 
  (@Eapp O.Oor (dcons _ x (dcons _ y (dnil _)))) 
  (at level 40, left associativity).
 Definition Eor e1 e2 := e1 !/\ e2.
 
 Notation "x '!->' y " := 
  (@Eapp O.Oimp (dcons _ x (dcons _ y (dnil _)))) 
  (at level 40, left associativity).
 Definition Eimpl e1 e2 := e1 !-> e2.

 Notation "'!~' x " := (@Eapp O.Onot (dcons _ x (dnil _))) 
  (at level 40, left associativity).
 Definition Enot e1 := !~ e1.

 Notation "x '!in' y " := 
  (@Eapp (O.Omem _) (dcons _ x (dcons _ y (dnil _)))) 
  (at level 40, left associativity).
 Definition Ein t (e1 : Exp t) e2 := e1 !in e2.

 Notation "x '!in_dom' y " := 
  (@Eapp (O.Oin_dom _ _) (dcons _ x (dcons _ y (dnil _)))) 
  (at level 60).
 Definition Ein_dom t1 (e1:Exp t1) t2 (e2:Exp (T.List (T.Pair t1 t2))) := 
  e1 !in_dom e2.

 Notation "x '!in_range' y " :=
  (@Eapp (O.Oin_range _ _) (dcons _ x (dcons _ y (dnil _)))) 
  (at level 60).
 Definition Ein_range t1 t2 (e1:Exp t2) (e2:Exp (T.List (T.Pair t1 t2))) := 
  e1 !in_range e2.
  
 Notation "x '[!' y '!]'" := 
  (@Eapp (O.Oimg _ _) (dcons _ y (dcons _ x (dnil _)))) 
  (at level 59).
 Definition Eimg t1 t2 (L:Exp (T.List (T.Pair t1 t2))) (x:Exp t1) := L [! x !].

 Notation "l '.[!' x '<<-' v '!]'" := 
  (@Eapp (O.Oupd _ _) (dcons _ x (dcons _ v (dcons _ l (dnil _))))) 
  (at level 50).
 Definition Eupd t1 t2 (L:Exp (T.List (T.Pair t1 t2))) (x:Exp t1) (v:Exp t2) :=
  L.[! x <<- v !].

 Notation "'!Zlen' L"   := 
  (@Eapp (O.OZlength _) (dcons _ L (dnil _))) 
  (at level 40).
 Definition lengthZ t (L:Exp (T.List t)) := !Zlen L. 
 

 (** Arguments as a dependent list of EasyCrypt expressions *)
 Definition args := dlist Exp.


 (** Induction principles for expressions *)
 Lemma Exp_ind2 : forall 
  (P : forall t, Exp t -> Prop)
  (Pl : forall l, args l -> Prop),
  (forall t (c:E.cexpr t), P _ (Ecnst c)) ->
  (forall t (v:lvar t), P _ (Evar v)) ->
  (forall op args, Pl (O.targs op) args -> P _ (Eapp op args)) ->
  (forall (t : T.type) (v : Var.var t) (e1 : Exp T.Bool)
   (e2 : Exp (T.List t)),
   P T.Bool e1 -> P (T.List t) e2 -> P T.Bool (Eexists v e1 e2)) ->
  (forall (t : T.type) (v : Var.var t) (e1 : Exp T.Bool)
   (e2 : Exp (T.List t)),
   P T.Bool e1 -> P (T.List t) e2 -> P T.Bool (Eforall v e1 e2)) ->
  (forall (t : T.type) (v : Var.var t) (e1 : Exp T.Bool)
   (e2 : Exp (T.List t)),
   P T.Bool e1 -> P (T.List t) e2 -> P t (Efind v e1 e2)) ->
  (Pl nil (dnil Exp)) ->
  (forall t l e le, P t e -> Pl l le -> Pl (t::l) (dcons t e le)) ->
  forall t e, P t e.
 Proof.
  intros P Pl Hc Hv Happ Hex Hforall Hfind Hnil Hcons.
  fix Exp_ind2 2.
  destruct e.
  apply Hc.
  apply Hv.
  apply Happ.
  generalize (O.targs op) d; clear d op.
  induction d.
  apply Hnil.
  apply Hcons; auto.
  apply Hex; auto.
  apply Hforall; auto.
  apply Hfind; auto.
 Qed.

 Lemma Exp_ind_and :  forall (P : forall t, Exp t -> Prop)
  (Pl : forall l, args l -> Prop),
  (forall t (c:E.cexpr t), P _ (Ecnst c)) ->
  (forall t (v:lvar t), P _ (Evar v)) ->
  (forall op args, Pl (O.targs op) args -> P _ (Eapp op args)) ->
  (forall (t : T.type) (v : Var.var t) (e1 : Exp T.Bool)
   (e2 : Exp (T.List t)),
   P T.Bool e1 -> P (T.List t) e2 -> P T.Bool (Eexists v e1 e2)) ->
  (forall (t : T.type) (v : Var.var t) (e1 : Exp T.Bool)
   (e2 : Exp (T.List t)),
   P T.Bool e1 -> P (T.List t) e2 -> P T.Bool (Eforall v e1 e2)) ->
  (forall (t : T.type) (v : Var.var t) (e1 : Exp T.Bool)
   (e2 : Exp (T.List t)),
   P T.Bool e1 -> P (T.List t) e2 -> P t (Efind v e1 e2)) ->
  (Pl nil (dnil Exp)) ->
  (forall t l e le, P t e -> Pl l le -> Pl (t::l) (dcons t e le)) ->
  (forall t e, P t e) /\ (forall lt args, Pl lt args).
 Proof.
  split; intros.
  eapply Exp_ind2; eauto.
  induction args0; auto.
  apply H6; auto.
  eapply Exp_ind2; eauto.
 Qed.


 (** Eval an EasyCrypt expression given a pair of memories and a
     valuation for logical variables *)
 Fixpoint eeval k (m1 m2:Mem.t k) (l:lmem k) t (e:Exp t) : T.interp k t :=
  match e with
   | Ecnst t c => E.eval_cexpr k c
   | Evar t lv => Eval_LvBase m1 m2 l lv
   | Eapp op larg => T.app_op _ (O.interp_op k op) (dmap _ (eeval m1 m2 l) larg)
   | Eexists t0 x e1 e2 =>
     existsb 
     (fun v : T.interp k t0 => eeval m1 m2 (LVV k x v :: l) e1) 
     (eeval m1 m2 l e2)
   | Eforall t0 x e1 e2 =>
     forallb 
     (fun v : T.interp k t0 => eeval m1 m2 (LVV k x v :: l) e1) 
     (eeval m1 m2 l e2)
   | Efind t0 x e1 e2 =>
     find_default
     (fun v : T.interp k t0 => eeval m1 m2 (LVV k x v :: l) e1)
     (eeval m1 m2 l e2) 
     (T.default k t0)
  end.

 (** Substitute free occurrences of a variable by an expression *)
 Record dep_assoc T (A B : T -> Type) := 
   mkAssoc {
     da_t : T;
     da_a : A da_t;
     da_b : B da_t
  }.

 Definition asubst := list (dep_assoc lvar Exp).

 Definition is_lvar_assoc t (x:lvar t) (a:dep_assoc lvar Exp) :=
   lvar_eqb x a.(da_a).
   
 Fixpoint find_assoc t (x:lvar t) (s:asubst) : Exp t :=
   match s with
   | nil => x
   | (mkAssoc t' x' e') :: s =>
     if lvar_eqb x x' then
       match T.eq_dec t' t with
       | left H =>
         match H in (_ = t1) return Exp t1 with
         | eq_refl => e'
         end
       | _ => x
       end
     else find_assoc x s
   end.

 Fixpoint remove_assoc t (x:lvar t) (s:asubst) : asubst :=
   match s with
   | nil => nil
   | a :: s =>
     let  (t', x', _) := a in
     if lvar_eqb x x' then remove_assoc x s
     else a :: remove_assoc x s
   end.
 
 Fixpoint esubst_para s t (e:Exp t) : Exp t :=
  match e in Exp t0 return Exp t0 with
   | Ecnst t1 c => (Ecnst c)
   | Evar t1 lv => find_assoc lv s 
   | Eapp op larg => Eapp op (dmap Exp (@esubst_para s) larg)
   | Eexists t0 x e1 e2 =>
     Eexists x (esubst_para (remove_assoc (VarLogic x) s) e1) (esubst_para s e2)
   | Eforall t0 x e1 e2 =>
     Eforall x (esubst_para (remove_assoc (VarLogic x) s) e1) (esubst_para s e2)
   | Efind t0 x e1 e2 =>
     Efind x (esubst_para (remove_assoc (VarLogic x) s) e1) (esubst_para s e2) 
   end.
 
 Fixpoint esubst t' (v:lvar t') (e':Exp t') t (e:Exp t) : Exp t :=
  match e in Exp t0 return Exp t0 with
   | Ecnst t1 c => (Ecnst c)
   | Evar t1 lv =>
     if lvar_eqb lv v then
     match T.eq_dec t' t1 with
      | left H =>
       match H in (_ = t2) return Exp t2 with
        | eq_refl => e'
       end
      | _ => Evar lv
     end
     else Evar lv
   | Eapp op larg => Eapp op (dmap Exp (@esubst t' v e') larg)
   | Eexists t0 x e1 e2 =>
     let e1 := if lvar_eqb (VarLogic x) v then e1 else (esubst v e' e1) in
     Eexists x e1 (esubst v e' e2)
   | Eforall t0 x e1 e2 =>
     let e1 := if lvar_eqb (VarLogic x) v then e1 else (esubst v e' e1) in
     Eforall x e1 (esubst v e' e2)
   | Efind t0 x e1 e2 =>
     let e1 := if lvar_eqb (VarLogic x) v then e1 else (esubst v e' e1) in
     Efind x e1 (esubst v e' e2)
   end.
 
 (** Set of free logical variables of an expression *)
 Fixpoint lfv_rec t (FV:Vset.t) (e:Exp t) : Vset.t :=
  match e with
   | Evar _ (VarLogic x) => Vset.add x FV
   | Eapp _ larg => dfold_left lfv_rec larg FV
   | Eexists t0 x e1 e2 =>
     let FV1 := Vset.remove x (lfv_rec Vset.empty e1) in
     lfv_rec (Vset.union FV1 FV) e2
   | Eforall t0 x e1 e2 =>
     let FV1 := Vset.remove x (lfv_rec Vset.empty e1) in
     lfv_rec (Vset.union FV1 FV) e2
   | Efind t0 x e1 e2 =>
     let FV1 := Vset.remove x (lfv_rec Vset.empty e1) in
     lfv_rec (Vset.union FV1 FV) e2
   | _ => FV
  end.

 Definition lfv t e := @lfv_rec t Vset.empty e.
 
 Lemma lfv_rec_union_and : 
  (forall t e FV, @lfv_rec t FV e [=] Vset.union (@lfv t e) FV) /\ 
  (forall l larg FV, 
   @dfold_left _ _ _ lfv_rec l larg FV [=] 
   Vset.union (dfold_left lfv_rec larg Vset.empty) FV).
 Proof.
  apply Exp_ind_and; simpl; intros; auto with set.
  simpl; intros; auto with set.
  destruct v; auto with set.
  rewrite H0.
  rewrite (H0 (Vset.union (Vset.remove v (lfv_rec Vset.empty e1)) Vset.empty)).
  rewrite VsetP.union_assoc.
  match goal with |- context [Vset.union ?x Vset.empty] =>
   rewrite (VsetP.union_sym x Vset.empty), VsetP.union_empty end; auto with set.
  rewrite H0.
  rewrite (H0 (Vset.union (Vset.remove v (lfv_rec Vset.empty e1)) Vset.empty)).
  rewrite VsetP.union_assoc.
  match goal with |- context [Vset.union ?x Vset.empty] =>
   rewrite (VsetP.union_sym x Vset.empty), VsetP.union_empty end; auto with set.
  rewrite H0.
  rewrite (H0 (Vset.union (Vset.remove v (lfv_rec Vset.empty e1)) Vset.empty)).
  rewrite VsetP.union_assoc.
  match goal with |- context [Vset.union ?x Vset.empty] =>
   rewrite (VsetP.union_sym x Vset.empty), VsetP.union_empty end; auto with set.
  rewrite H0, (H0 (lfv_rec Vset.empty e)), (H FV).
  rewrite VsetP.union_assoc; auto with set.
 Qed.
 
 Lemma lfv_rec_union : forall t e FV,
  (@lfv_rec t FV e) [=] (Vset.union (@lfv t e) FV).
 Proof. 
  destruct lfv_rec_union_and; trivial. 
 Qed.

 Lemma lfv_Eexists : forall t (v:Var.var t) e1 e2,
  lfv (Eexists v e1 e2) [=] Vset.union (Vset.remove v (lfv e1)) (lfv e2).
 Proof.
  unfold lfv; intros; simpl.
  rewrite lfv_rec_union.
  rewrite VsetP.union_sym.
  apply VsetP.union_morphism; auto with set.
  rewrite VsetP.union_sym, VsetP.union_empty; auto with set.
 Qed.

 Lemma lfv_Eforall : forall t (v:Var.var t) e1 e2,
  lfv (Eforall v e1 e2) [=] Vset.union (Vset.remove v (lfv e1)) (lfv e2).
 Proof.
  unfold lfv; intros; simpl.
  rewrite lfv_rec_union.
  rewrite VsetP.union_sym.
  apply VsetP.union_morphism; auto with set.
  rewrite VsetP.union_sym, VsetP.union_empty; auto with set.
 Qed.

 Lemma lfv_Efind : forall t (v:Var.var t) e1 e2,
  lfv (Efind v e1 e2) [=] Vset.union (Vset.remove v (lfv e1)) (lfv e2).
 Proof.
  unfold lfv; intros; simpl.
  rewrite lfv_rec_union.
  rewrite VsetP.union_sym.
  apply VsetP.union_morphism; auto with set.
  rewrite VsetP.union_sym, VsetP.union_empty; auto with set.
 Qed.

 (** Set of logical variables with bound occurrences in an expression *)
 Fixpoint lbind_rec t (BV:Vset.t) (e:Exp t) : Vset.t :=
  match e with
   | Eapp _ larg => dfold_left lbind_rec larg BV
   | Eexists t0 x e1 e2 => lbind_rec (lbind_rec (Vset.add x BV) e1) e2
   | Eforall t0 x e1 e2 => lbind_rec (lbind_rec (Vset.add x BV) e1) e2
   | Efind t0 x e1 e2 => lbind_rec (lbind_rec (Vset.add x BV) e1) e2
   | _ => BV
  end.

 Definition lbind t e := @lbind_rec t Vset.empty e.

 Lemma lbind_rec_union_and : 
  (forall t e lb, (@lbind_rec t lb e) [=] (Vset.union (@lbind t e) lb)) /\
  (forall l (larg:dlist _ l)  b,
   dfold_left lbind_rec larg b [=] 
   Vset.union (dfold_left lbind_rec larg Vset.empty) b) .
 Proof.
  unfold lbind; apply Exp_ind_and; simpl; intros; auto with set.
  rewrite H0, (H (Vset.add v lb)), (H0 (lbind_rec _ e1)).
  rewrite (H (@cons VarP.Edec.t (@Var.mkV t0 v) (@nil VarP.Edec.t))), 
   VsetP.union_assoc.
  apply VsetP.union_morphism; auto with set.
  rewrite VsetP.union_assoc; apply VsetP.union_morphism; auto with set.
  rewrite H0, (H (Vset.add v lb)), (H0 (lbind_rec _ e1)).
  rewrite (H (@cons VarP.Edec.t (@Var.mkV t0 v) (@nil VarP.Edec.t))), 
   VsetP.union_assoc.
  apply VsetP.union_morphism; auto with set.
  rewrite VsetP.union_assoc; apply VsetP.union_morphism; auto with set.
  rewrite H0, (H (Vset.add v lb)), (H0 (lbind_rec _ e1)).
  rewrite (H (@cons VarP.Edec.t (@Var.mkV t0 v) (@nil VarP.Edec.t))), 
   VsetP.union_assoc.
  apply VsetP.union_morphism; auto with set.
  rewrite VsetP.union_assoc; apply VsetP.union_morphism; auto with set.
  rewrite H0, (H0 (lbind_rec Vset.empty e)), (H b).
  rewrite VsetP.union_assoc; auto with set.
 Qed.
 
 Lemma lbind_rec_union : forall t e lb, 
  (@lbind_rec t lb e) [=] (Vset.union (@lbind t e) lb).
 Proof. 
  destruct lbind_rec_union_and; trivial. 
 Qed.

 Lemma lbind_Eexists : forall t (v:Var.var t) e1 e2,
  lbind (Eexists v e1 e2) [=] Vset.add v (Vset.union (lbind e1) (lbind e2)).
 Proof.
  unfold lbind; intros; simpl.
  rewrite lbind_rec_union.
  rewrite lbind_rec_union.
  unfold lbind.
  rewrite VsetP.add_union_comm.
  rewrite <- VsetP.union_sym.
  apply VsetP.union_morphism; auto with set.
  rewrite <- VsetP.union_sym.
  setoid_rewrite <- (VsetP.union_empty (lbind_rec Vset.empty e1)) at 2.
  rewrite VsetP.add_union_comm.
  apply VsetP.union_morphism; auto with set.
 Qed.
 
 Lemma lbind_Eforall : forall t (v:Var.var t) e1 e2,
  lbind (Eforall v e1 e2) [=] Vset.add v (Vset.union (lbind e1) (lbind e2)).
 Proof.
  unfold lbind; intros; simpl.
  rewrite lbind_rec_union.
  rewrite lbind_rec_union.
  unfold lbind.
  rewrite VsetP.add_union_comm.
  rewrite <- VsetP.union_sym.
  apply VsetP.union_morphism; auto with set.
  rewrite <- VsetP.union_sym.
  setoid_rewrite <- (VsetP.union_empty (lbind_rec Vset.empty e1)) at 2.
  rewrite VsetP.add_union_comm.
  apply VsetP.union_morphism; auto with set.
 Qed.
 
 Lemma lbind_Efind : forall t (v:Var.var t) e1 e2,
  lbind (Efind v e1 e2) [=] Vset.add v (Vset.union (lbind e1) (lbind e2)).
 Proof.
  unfold lbind; intros; simpl.
  rewrite lbind_rec_union.
  rewrite lbind_rec_union.
  unfold lbind.
  rewrite VsetP.add_union_comm.
  rewrite <- VsetP.union_sym.
  apply VsetP.union_morphism; auto with set.
  rewrite <- VsetP.union_sym.
  setoid_rewrite <- (VsetP.union_empty (lbind_rec Vset.empty e1)) at 2.
  rewrite VsetP.add_union_comm.
  apply VsetP.union_morphism; auto with set.
 Qed.

 (** TODO: Move to VsetP *)
 Lemma disjoint_subset_r : forall X Y Z : Vset.t,
  X[<=]Y -> Vset.disjoint Z Y -> Vset.disjoint Z X.
 Proof.
  intros.
  apply VsetP.disjoint_sym.
  apply VsetP.disjoint_sym in H0.
  eapply VsetP.disjoint_subset_l; eauto.
 Qed. 
 
 Lemma disjoint_subset : forall X1 X2 Y1 Y2 : Vset.t,
  X1[<=]Y1 -> X2[<=]Y2 -> Vset.disjoint Y1 Y2 -> Vset.disjoint X1 X2.
 Proof.
  intros.
  eapply VsetP.disjoint_subset_l; eauto.
  eapply disjoint_subset_r; eauto.
 Qed.

 Lemma union_disjoint : forall I X1 X2,
  Vset.disjoint (Vset.union X1 X2) I ->
  Vset.disjoint X1 I /\ Vset.disjoint X2 I.
 Proof.
  unfold Vset.disjoint; intros.
  rewrite VsetP.inter_sym in H.
  rewrite VsetP.inter_union_comm in H.
  apply VsetP.empty_union in H; auto.
  split; rewrite VsetP.inter_sym; tauto.
 Qed.

 Lemma remove_add : forall x s, Vset.remove x (Vset.add x s) [<=] s.
 Proof.
  intros; apply Vset.subset_complete.
  intros x0; rewrite VsetP.remove_spec, VsetP.add_spec; intuition.
 Qed.
 (**)

 (** Update the value of a tagged variable in a left/right memory *)
 Definition mem_upd (side:bool) k (m1 m2:Mem.t k) (l:lmem k) t 
  (v:lvar t) (e:Exp t) : Mem.t k :=
  match v with
   | VarLeft v => if side then m1{!v <-- eeval m1 m2 l e!} else m2
   | VarRight v => if side then m1 else m2{!v<--eeval m1 m2 l e !}
   | _ => if side then m1 else m2
  end.

 (** Update the value of a logical variable in a valuation *)
 Definition lmem_upd k m1 m2 (l:lmem k) t (v:lvar t) (e:Exp t) : lmem k :=
  match v with
   | VarLogic x => LVV k x (eeval m1 m2 l e) :: l
   | _ => l
  end.

 (** TODO: Move somewhere else *)
 Lemma existsb_feq_compat : forall A (l:list A) f1 f2, 
  (forall a, In a l -> f1 a = f2 a) ->
  existsb f1 l = existsb f2 l.
 Proof. 
  intros; apply eq_true_iff_eq.
  change (existsb f1 l <-> existsb f2 l).
  rewrite is_true_existsb, is_true_existsb.
  split; intros (x,(Hin,Hf));(exists x; split; trivial).
  rewrite <- H; trivial.
  rewrite H; trivial.
 Qed.

 Lemma forallb_feq_compat : forall A (l:list A) f1 f2, 
  (forall a, In a l -> f1 a = f2 a) ->
  forallb f1 l = forallb f2 l.
 Proof. 
  intros; apply eq_true_iff_eq.
  change (forallb f1 l <-> forallb f2 l).
  rewrite is_true_forallb, is_true_forallb.
  split; intros;[ rewrite <- H | rewrite H]; auto.
 Qed.

 Lemma find_feq_compat : forall A (l:list A) f1 f2 d, 
  (forall a, In a l -> f1 a = f2 a) ->
  find_default f1 l d = find_default f2 l d.
 Proof. 
  unfold find_default; intros; induction l; simpl; auto.
  rewrite <- H; simpl; auto.
  case_eq (f1 a); intros; auto.
  apply IHl; intros.
  apply H; simpl; auto.
 Qed.   
 (***)

 (** The value of an expression only depends on the valuation of its
    free logical variables *)
 Lemma eeval_eq_assoc : forall k (m1 m2:Mem.t k) t (e:Exp t) (l1 l2:lmem k),
  (forall t' (x:Var.var t'), Vset.mem x (lfv e) -> assoc x l1 = assoc x l2) ->
  eeval m1 m2 l1 e = eeval m1 m2 l2 e.
 Proof.
  intros k m1 m2; induction e using Exp_ind2 with 
   (Pl :=
    fun l0 larg => forall (l1 l2:lmem k),
     (forall t' (x:Var.var t'),
      Vset.mem x (dfold_left lfv_rec larg Vset.empty) ->
      assoc x l1 = assoc x l2) ->
     (dmap _ (eeval m1 m2 l1) larg) = (dmap _ (eeval m1 m2 l2) larg)); 
  simpl; intros; auto.
  (* Var *)
  destruct v; simpl; auto.
  apply H; simpl.
  rewrite Vset.ET.eqb_refl; auto.
  
  (* App *)
  apply f_equal; auto.
  
  (* Exists *)
  rewrite (IHe2 l1 l2); trivial.
  apply existsb_feq_compat; intros a _.
  apply IHe1; intros.
  assoc_case; symmetry; assoc_case.
  symmetry; apply H; rewrite lfv_Eexists.
  apply Vset.union_complete_l.
  apply VsetP.remove_spec; split; trivial.
  unfold Vset.E.eq; intro.
  injection H3; intros; subst.
  apply T.inj_pair2 in H4; subst.
  rewrite veqb_refl in H2; discriminate.
  intros; apply H; rewrite lfv_Eexists.   
  apply Vset.union_complete_r; trivial.

  (* Forall *)
  rewrite (IHe2 l1 l2); trivial.
  apply forallb_feq_compat; intros a _.
  apply IHe1; intros.
  assoc_case; symmetry; assoc_case.
  symmetry; apply H; rewrite lfv_Eforall.
  apply Vset.union_complete_l; apply VsetP.remove_spec; split; trivial.
  unfold Vset.E.eq; intro.
  injection H3; intros; subst.
  apply T.inj_pair2 in H4; subst.
  rewrite veqb_refl in H2; discriminate.
  intros; apply H; rewrite lfv_Eforall.   
  apply Vset.union_complete_r; trivial.

  (* Find *)
  rewrite (IHe2 l1 l2); trivial.
  apply find_feq_compat; intros a _.
  apply IHe1; intros.
  assoc_case; symmetry; assoc_case.
  symmetry; apply H; rewrite lfv_Efind.
  apply Vset.union_complete_l.
  apply VsetP.remove_spec; split; trivial.
  unfold Vset.E.eq; intro.
  injection H3; intros; subst.
  apply T.inj_pair2 in H4; subst.
  rewrite veqb_refl in H2; discriminate.
  intros; apply H; rewrite lfv_Efind.   
  apply Vset.union_complete_r; trivial.

  (* Cons *)
  destruct lfv_rec_union_and.
  f_equal; [apply IHe | apply IHe0]; intros; apply H; rewrite H1; auto with set.
 Qed.
 

 (** Valuations are order-oblivious *)
 Lemma eval_exp_comm : forall k (m1 m2:Mem.t k) t (e:Exp t) l (v1 v2:lvar_val k),
  Var.veqb (var v1) (var v2) = false ->
  eeval m1 m2 (v1 :: v2 :: l)  e = eeval m1 m2 (v2 :: v1 :: l) e.
 Proof.
  intros; apply eeval_eq_assoc.
  intros; apply assoc_comm; trivial.
 Qed.

 Lemma eeval_assoc : forall k (m1 m2:Mem.t k) t (e:Exp t) l t0 (v:Var.var t0) x,
  ~Vset.mem v (lfv e) ->
  eeval m1 m2 l e = eeval m1 m2 ({| t := t0; var := v; val := x |} :: l) e.
 Proof.
  intros.
  apply eeval_eq_assoc; intros.
  symmetry; assoc_case.
  elim H; rewrite <- H1; trivial.
 Qed.

 Lemma mem_upd_assoc : forall k (m1 m2:Mem.t k) side t0 (v0:Var.var t0) a t' 
  v (e':Exp t') l,
  ~Vset.mem v0 (lfv e') ->
  mem_upd side m1 m2 ({| t := t0; var := v0; val := a |} :: l) v e' =
  mem_upd side m1 m2 l v e'.
 Proof.
  intros; destruct v; destruct side; simpl; trivial.
  f_equal.
  rewrite <- eeval_assoc; trivial.
  rewrite <- eeval_assoc; trivial.
 Qed.   

 (** Valuations are interpreted as sets of assignments *)
 Lemma assoc_double : forall k t (v:Var.var t) (a1:T.interp k t) a2 l t'
  (x:Var.var t'),
  assoc x ({|t:=t; var:=v; val:=a1 |} :: l) =
  assoc x ({|t:=t; var:=v; val:=a1 |} :: {| t:=t; var:=v; val:=a2 |} :: l).
 Proof.
  intros; assoc_case; symmetry; assoc_case; assoc_case.
 Qed.
 
 (** Substitution Lemma for expressions *)
 Lemma esubst_correct : forall k (m1 m2:Mem.t k) t' (v:lvar t') (e':Exp t') t 
  (e:Exp t) (l:lmem k),
  Vset.disjoint (lfv e') (lbind e) ->
  eeval m1 m2 l (esubst v e' e) =
  eeval (mem_upd side_left m1 m2 l v e') (mem_upd side_right m1 m2 l v e') 
  (lmem_upd m1 m2 l v e') e.
 Proof.
  Opaque lvar_eqb.
  intros k m1 m2 t' v e'.
  induction e using Exp_ind2 with (Pl :=
   fun l0 larg => forall l, 
    Vset.disjoint (lfv e') (dfold_left lbind_rec larg Vset.empty) ->
    dmap _ (eeval m1 m2 l) (dmap Exp (@esubst t' v e') larg) =
    dmap _ (eeval (mem_upd side_left m1 m2 l v e') 
     (mem_upd side_right m1 m2 l v e') (lmem_upd m1 m2 l v e'))
    larg); 
  simpl; trivial; intros.
  
  (* Var *)
  generalize (lvar_eqb_spec_dep v0 v).
  destruct (lvar_eqb v0 v); intros Heq.
  inversion Heq; subst.
  apply T.inj_pair2 in H3; subst.
  rewrite Teq_dep_refl.
  unfold mem_upd, lmem_upd; destruct v; simpl; 
   try (symmetry; apply Mem.get_upd_same).
  rewrite assoc_same; trivial.
  apply veqb_refl.
  unfold mem_upd, lmem_upd; destruct v; simpl.
  destruct v0; simpl; trivial.
  rewrite Mem.get_upd_diff; trivial.
  intros Hv; elim Heq; inversion Hv; trivial.
  destruct v0; simpl; trivial.
  rewrite Mem.get_upd_diff; trivial.
  intros Hv; elim Heq; inversion Hv; trivial.
  destruct v0; trivial.
  unfold Eval_LvBase.
  rewrite assoc_diff; trivial.
  generalize (Var.veqb_spec_dep v0 v); intros.
  destruct (Var.veqb v0 v); trivial.
  elim Heq; inversion H0; constructor.

  (* App *)
  intros; rewrite IHe; trivial.

  (* Exists *)
  rewrite IHe2; simpl.
  apply existsb_feq_compat; trivial; intros a _.
  assert (~ Vset.mem v0 (lfv e')).
  apply VsetP.disjoint_sym in H.
  apply VsetP.disjoint_mem_not_mem with (1 := H).
  rewrite lbind_Eexists.
  auto with set.
  generalize (lvar_eqb_spec_dep (VarLogic v0) v).
  case_eq (lvar_eqb (VarLogic v0) v); simpl; intros.
  inversion H2; subst. 
  apply T.inj_pair2 in H6; subst.
  simpl.
  apply (@eeval_eq_assoc k m1 m2 T.Bool e1).
  intros.
  apply assoc_double.   
  rewrite IHe1; trivial.
  rewrite mem_upd_assoc, mem_upd_assoc; trivial.
  rewrite eeval_eq_assoc with 
   (l2 := ({| t := t0; var := v0; val := a |} :: lmem_upd m1 m2 l v e')); auto.
  intros.
  destruct v; simpl; trivial.
  rewrite assoc_comm.
  rewrite <- eeval_assoc; trivial.
  simpl.
  Transparent lvar_eqb.
  simpl in H1.
  rewrite veqb_sym; trivial.
  Opaque lvar_eqb.
  apply disjoint_subset_r with (2 := H).
  rewrite lbind_Eexists; auto with set.
  apply disjoint_subset_r with (2 := H).
  rewrite lbind_Eexists; auto with set.

  (* Forall *)
  rewrite IHe2; simpl.
  apply forallb_feq_compat; trivial; intros a _.
  assert (~ Vset.mem v0 (lfv e')).
  apply VsetP.disjoint_sym in H.
  apply VsetP.disjoint_mem_not_mem with (1 := H).
  rewrite lbind_Eforall.
  auto with set.
  generalize (lvar_eqb_spec_dep (VarLogic v0) v).
  case_eq (lvar_eqb (VarLogic v0) v); simpl; intros.
  inversion H2; subst. 
  apply T.inj_pair2 in H6; subst.
  simpl.
  apply (@eeval_eq_assoc k m1 m2 T.Bool e1).
  intros.
  apply assoc_double.   
  rewrite IHe1; trivial.
  rewrite mem_upd_assoc, mem_upd_assoc; trivial.
  rewrite eeval_eq_assoc with 
   (l2 := ({| t := t0; var := v0; val := a |} :: lmem_upd m1 m2 l v e')); auto.
  intros.
  destruct v; simpl; trivial.
  rewrite assoc_comm.
  rewrite <- eeval_assoc; trivial.
  simpl.
  Transparent lvar_eqb.
  simpl in H1.
  rewrite veqb_sym; trivial.
  Opaque lvar_eqb.
  apply disjoint_subset_r with (2 := H).
  rewrite lbind_Eforall; auto with set.
  apply disjoint_subset_r with (2 := H).
  rewrite lbind_Eforall; auto with set.

  (* Find *)
  rewrite IHe2; simpl.
  apply find_feq_compat; trivial; intros a _.
  assert (~ Vset.mem v0 (lfv e')).
  apply VsetP.disjoint_sym in H.
  apply VsetP.disjoint_mem_not_mem with (1 := H).
  rewrite lbind_Efind.
  auto with set.
  generalize (lvar_eqb_spec_dep (VarLogic v0) v).
  case_eq (lvar_eqb (VarLogic v0) v); simpl; intros.
  inversion H2; subst. 
  apply T.inj_pair2 in H6; subst.
  simpl.
  apply (@eeval_eq_assoc k m1 m2 T.Bool e1).
  intros.
  apply assoc_double.   
  rewrite IHe1; trivial.
  rewrite mem_upd_assoc, mem_upd_assoc; trivial.
  rewrite eeval_eq_assoc with 
   (l2 := ({| t := t0; var := v0; val := a |} :: lmem_upd m1 m2 l v e')); auto.
  intros.
  destruct v; simpl; trivial.
  rewrite assoc_comm.
  rewrite <- eeval_assoc; trivial.
  simpl.
  Transparent lvar_eqb.
  simpl in H1.
  rewrite veqb_sym; trivial.
  Opaque lvar_eqb.
  apply disjoint_subset_r with (2 := H).
  rewrite lbind_Efind; auto with set.
  apply disjoint_subset_r with (2 := H).
  rewrite lbind_Efind; auto with set.

  (* Cons *)
  destruct lbind_rec_union_and.
  f_equal.
  apply IHe.
  apply disjoint_subset_r with (2 := H).
  rewrite H1; auto with set.
  apply IHe0.
  apply disjoint_subset_r with (2 := H).
  rewrite (H1 _ le (lbind_rec Vset.empty e)); auto with set.
 Qed.

 Fixpoint mem_upd_para k (m1 m2:Mem.t k) (l:lmem k) (s:asubst) :=
   match s with
   | nil => ((m1,m2),l)
   | mkAssoc t x e :: s =>
     match mem_upd_para m1 m2 l s with
     | ((m1',m2'),l') => 
       match x with
       | v0 <1> => ((m1'{!v0 <-- eeval m1 m2 l e!},m2'),l')
       | v0 <2> => ((m1',m2'{!v0 <-- eeval m1 m2 l e!}),l')
       | VarLogic v0 => ((m1',m2'), {| t := t; var := v0; val := eeval m1 m2 l e |} :: l')
       end
     end  
   end.

 Definition mem_upd_para1 k (m1 m2:Mem.t k) l s := fst (fst (mem_upd_para m1 m2 l s)).

 Definition mem_upd_para2 k (m1 m2:Mem.t k) l s := snd (fst (mem_upd_para m1 m2 l s)).

 Definition mem_upd_paral k (m1 m2:Mem.t k) l s := snd (mem_upd_para m1 m2 l s).

 Definition sfv (s:asubst) := 
   List.fold_right (fun a => Vset.union (lfv a.(da_b))) Vset.empty s.

 Lemma mem_upd_para_notmem : forall k (m1 m2:Mem.t k) t0 l (v:Var.var t0) a s, 
  ~Vset.mem v (sfv s) ->
     (mem_upd_para1 m1 m2 ({| t := t0; var := v; val := a |} :: l) (remove_assoc (VarLogic v) s)) =
     (mem_upd_para1 m1 m2 l s) /\
     (mem_upd_para2 m1 m2 ({| t := t0; var := v; val := a |} :: l) (remove_assoc (VarLogic v) s)) = 
     (mem_upd_para2 m1 m2 l s) /\
     forall t' (x:Var.var t'), 
     assoc x (mem_upd_paral m1 m2 ({| t := t0; var := v; val := a |} :: l) (remove_assoc (VarLogic v) s))  =
     assoc x ({| t := t0; var := v; val := a |} :: mem_upd_paral m1 m2 l s).
 Proof.
  unfold mem_upd_para1,  mem_upd_para2,  mem_upd_paral;induction s;simpl;intros;auto.
  destruct a0 as (t1, x, e).
  destruct (mem_upd_para m1 m2 l s) as ((m1'',m2''),l'').
  destruct IHs as (H1,(H2,H3)).
  intros Hmem;apply H;auto with set.
  generalize (lvar_eqb_spec_dep (VarLogic v) x);destruct (lvar_eqb (VarLogic v) x);intros.  
  inversion H0;clear H0;subst. apply T.inj_pair2 in H7;subst;simpl;repeat split;auto.
  intros;rewrite H3;trivial.
  assoc_case;symmetry;assoc_case;assoc_case.
  simpl;  destruct (mem_upd_para m1 m2 ({| t := t0; var := v; val := a |} :: l) (remove_assoc (VarLogic v) s))
    as ((m1', m2'),l');simpl in *;subst.
  assert (~ Vset.mem v (lfv e)).
    simpl in H;intros Hin;apply H;auto with set.
  destruct x;simpl;repeat split;trivial;try rewrite <- eeval_assoc;trivial.
  intros;assoc_case.
  symmetry;assoc_case.
  elim H0;rewrite H4;trivial.
  rewrite assoc_same;[ trivial | apply veqb_refl].
  rewrite H3;assoc_case;symmetry;assoc_case.
  rewrite !assoc_diff;trivial.
 Qed.
 
 Lemma sfv_remove_assoc_subset : forall t (v:Var.var t) s,
     sfv (remove_assoc (VarLogic v) s)[<=]sfv s.
 Proof.
  induction s;simpl;auto with set.
  destruct a as (t',x',e');destruct (lvar_eqb (VarLogic v) x').
  rewrite IHs;auto with set.
  simpl;apply VsetP.union_subset;auto with set.
  rewrite IHs;auto with set.
 Qed.

 Lemma esubst_para_correct : forall k (m1 m2:Mem.t k) t 
  (e:Exp t) s (l:lmem k),
   Vset.disjoint (sfv s) (lbind e) ->
  eeval m1 m2 l (esubst_para s e) =
  eeval (mem_upd_para1 m1 m2 l s) (mem_upd_para2 m1 m2 l s) (mem_upd_paral m1 m2 l s) e.
 Proof.
  intros k m1 m2.
  induction e using Exp_ind2 with (Pl :=
   fun l0 larg => forall s l, 
    Vset.disjoint (sfv s) (dfold_left lbind_rec larg Vset.empty) -> 
    dmap _ (eeval m1 m2 l) (dmap Exp (@esubst_para s) larg) =
    dmap _ (eeval  (mem_upd_para1 m1 m2 l s) (mem_upd_para2 m1 m2 l s) (mem_upd_paral m1 m2 l s))
    larg); 
  simpl; trivial; intros.
  (* var *)
  clear H. 
  unfold mem_upd_para1, mem_upd_para2, mem_upd_paral.
  induction s;simpl;trivial.
  destruct a as (t',x,e').
  destruct (mem_upd_para m1 m2 l s) as ((m1',m2'),l');simpl in IHs.
  generalize (lvar_eqb_spec_dep v x);destruct (lvar_eqb v x);intros.
  inversion H;clear H;subst.
  apply T.inj_pair2 in H3;clear H2;subst.
  rewrite Teq_dep_refl.
  destruct x;simpl.
  rewrite Mem.get_upd_same;trivial.
  rewrite Mem.get_upd_same;trivial.
  rewrite assoc_same;[trivial | apply veqb_refl].
  rewrite IHs;destruct x;simpl; destruct v;simpl;trivial.
  rewrite Mem.get_upd_diff;trivial.
  intros Heq;elim H;inversion Heq;trivial.
  rewrite Mem.get_upd_diff;trivial.
  intros Heq;elim H;inversion Heq;trivial.
  rewrite assoc_diff;trivial.
  generalize (Var.veqb_spec_dep v v0);destruct (Var.veqb v v0);trivial.
  intros Heq;elim H;inversion Heq;trivial.
  (* op *)
  intros; rewrite IHe; trivial.
  (* exists *)
  rewrite IHe2; simpl.
  apply existsb_feq_compat; trivial; intros a _.
  rewrite IHe1.
  assert (~Vset.mem v (sfv s)).
   apply VsetP.disjoint_sym in H.
   apply VsetP.disjoint_mem_not_mem with (1 := H).
   rewrite lbind_Eexists;auto with set.
  destruct (mem_upd_para_notmem m1 m2 l v a s H0) as (H1,(H2,H3)).
  rewrite H1, H2.
  rewrite eeval_eq_assoc with 
   (l2 := ({| t := t0; var := v; val := a |} :: mem_upd_paral m1 m2 l s)); auto.
  apply disjoint_subset with (3 := H).
  apply  sfv_remove_assoc_subset.
  rewrite lbind_Eexists; auto with set.
  apply disjoint_subset_r with (2:= H);rewrite lbind_Eexists; auto with set.
  (* forall *)
  rewrite IHe2; simpl.
  apply forallb_feq_compat; trivial; intros a _.
  rewrite IHe1.
  assert (~Vset.mem v (sfv s)).
   apply VsetP.disjoint_sym in H.
   apply VsetP.disjoint_mem_not_mem with (1 := H).
   rewrite lbind_Eforall;auto with set.
  destruct (mem_upd_para_notmem m1 m2 l v a s H0) as (H1,(H2,H3)).
  rewrite H1, H2.
  rewrite eeval_eq_assoc with 
   (l2 := ({| t := t0; var := v; val := a |} :: mem_upd_paral m1 m2 l s)); auto.
  apply disjoint_subset with (3 := H).
  apply  sfv_remove_assoc_subset.
  rewrite lbind_Eforall; auto with set.
  apply disjoint_subset_r with (2:= H);rewrite lbind_Eforall; auto with set.
  (* find *)
  rewrite IHe2; simpl.
  apply find_feq_compat; trivial; intros a _.
  rewrite IHe1.
  assert (~Vset.mem v (sfv s)).
   apply VsetP.disjoint_sym in H.
   apply VsetP.disjoint_mem_not_mem with (1 := H).
   rewrite lbind_Efind;auto with set.
  destruct (mem_upd_para_notmem m1 m2 l v a s H0) as (H1,(H2,H3)).
  rewrite H1, H2.
  rewrite eeval_eq_assoc with 
   (l2 := ({| t := t0; var := v; val := a |} :: mem_upd_paral m1 m2 l s)); auto.
  apply disjoint_subset with (3 := H).
  apply  sfv_remove_assoc_subset.
  rewrite lbind_Efind; auto with set.
  apply disjoint_subset_r with (2:= H);rewrite lbind_Efind; auto with set.
  (* Cons *)
  destruct lbind_rec_union_and.
  f_equal.
  apply IHe.
  apply disjoint_subset_r with (2 := H).
  rewrite H1; auto with set.
  apply IHe0.
  apply disjoint_subset_r with (2 := H).
  rewrite (H1 _ le (lbind_rec Vset.empty e)); auto with set.
 Qed.

 (** Set of non-logical variables on which an expression depends *)
 Fixpoint ldepend_rec t (XX:Vset.t * Vset.t) (e:Exp t) : Vset.t * Vset.t:= 
  match e with
   | Ecnst _ _ => XX
   | Evar t v =>
     match v with 
     | VarLeft v => let (X1,X2) := XX in (Vset.add v X1, X2)
     | VarRight v => let (X1,X2) := XX in (X1, Vset.add v X2)
     | _ => XX
     end
   | Eapp op args => dfold_left ldepend_rec args XX
   | Eexists t x f l => ldepend_rec (ldepend_rec XX f) l
   | Eforall t x f l => ldepend_rec (ldepend_rec XX f) l
   | Efind t x f l => ldepend_rec (ldepend_rec XX f) l
  end.

 Definition ldepend t := @ldepend_rec t (Vset.empty, Vset.empty).

 Lemma ldepend_rec_union_and : 
  (forall t (e:Exp t) XX,
   fst (ldepend_rec XX e) [=] Vset.union (fst (ldepend e)) (fst XX) /\
   snd (ldepend_rec XX e) [=] Vset.union (snd (ldepend e)) (snd XX)) /\
  (forall l0 (args:dlist Exp l0) XX,fst (dfold_left ldepend_rec args XX) [=] 
   Vset.union 
   (fst (dfold_left ldepend_rec args (Vset.empty,Vset.empty))) (fst XX) /\
  snd (dfold_left ldepend_rec args XX) [=] 
  Vset.union (snd (dfold_left ldepend_rec args (Vset.empty,Vset.empty))) (snd XX)).
 Proof.
  apply Exp_ind_and; simpl; intros; auto with set.
  destruct v; simpl; trivial; destruct XX; simpl; auto with set.
  unfold ldepend; simpl; destruct (H0 (ldepend_rec XX e1)); destruct (H XX).
  rewrite H1, H2, H3, H4.
  destruct (H0 (ldepend_rec (Vset.empty,Vset.empty) e1)).
  rewrite H5, H6, !VsetP.union_assoc; auto with set.
  unfold ldepend; simpl; destruct (H0 (ldepend_rec XX e1)); destruct (H XX).
  rewrite H1, H2, H3, H4.
  destruct (H0 (ldepend_rec (Vset.empty,Vset.empty) e1)).
  rewrite H5, H6, !VsetP.union_assoc; auto with set.
  unfold ldepend; simpl; destruct (H0 (ldepend_rec XX e1)); destruct (H XX).
  rewrite H1, H2, H3, H4.
  destruct (H0 (ldepend_rec (Vset.empty,Vset.empty) e1)).
  rewrite H5, H6, !VsetP.union_assoc; auto with set.
  destruct (H0 (ldepend_rec XX e)); destruct (H XX).
  rewrite H1, H2, H3, H4.
  destruct (H0 (ldepend_rec (Vset.empty, Vset.empty) e)).
  rewrite H5, H6, <- !VsetP.union_assoc; auto with set.
 Qed.

 Lemma ldepend_rec_union : forall t (e:Exp t) XX,
  fst (ldepend_rec XX e) [=] Vset.union (fst (ldepend e)) (fst XX) /\
  snd (ldepend_rec XX e) [=] Vset.union (snd (ldepend e)) (snd XX).
 Proof. 
  destruct ldepend_rec_union_and; trivial. 
 Qed.
  
 Lemma ldepend_rec_correct : forall k (m1 m1' m2 m2':Mem.t k) t (e:Exp t) XX l,
  m1 =={fst (ldepend_rec XX e)} m1' ->
  m2 =={snd (ldepend_rec XX e)} m2' ->
  eeval m1 m2 l e = eeval m1' m2' l e.
 Proof.
  intros k m1 m1' m2 m2'; induction e using Exp_ind2 with 
   (Pl :=
    fun l0 args => forall XX l,
     m1 =={fst (dfold_left ldepend_rec args XX)} m1' ->
     m2 =={snd (dfold_left ldepend_rec args XX)} m2' ->
     dmap (T.interp k) (eeval m1 m2 l) args =
     dmap (T.interp k) (eeval m1' m2' l) args); simpl; intros; trivial.
  destruct v; simpl; trivial; destruct XX;[apply H | apply H0]; 
   simpl; auto with set.
  f_equal; apply IHe with XX; auto.
  destruct (ldepend_rec_union e2 (ldepend_rec XX e1)).
  rewrite H1 in H; rewrite H2 in H0.
  rewrite (IHe2 (ldepend_rec XX e1) l).
  apply existsb_feq_compat; intros; apply (IHe1 XX).
  apply req_mem_weaken with (2:= H); auto with set.
  apply req_mem_weaken with (2:= H0); auto with set.
  apply req_mem_weaken with (2:= H); auto with set.
  apply req_mem_weaken with (2:= H0); auto with set.
  destruct (ldepend_rec_union e2 (ldepend_rec XX e1)).
  rewrite H1 in H; rewrite H2 in H0.
  rewrite (IHe2 (ldepend_rec XX e1) l).
  apply forallb_feq_compat; intros; apply (IHe1 XX).
  apply req_mem_weaken with (2:= H); auto with set.
  apply req_mem_weaken with (2:= H0); auto with set.
  apply req_mem_weaken with (2:= H); auto with set.
  apply req_mem_weaken with (2:= H0); auto with set.
  destruct (ldepend_rec_union e2 (ldepend_rec XX e1)).
  rewrite H1 in H; rewrite H2 in H0.
  rewrite (IHe2 (ldepend_rec XX e1) l).
  apply find_feq_compat; intros; apply (IHe1 XX).
  apply req_mem_weaken with (2:= H); auto with set.
  apply req_mem_weaken with (2:= H0); auto with set.
  apply req_mem_weaken with (2:= H); auto with set.
  apply req_mem_weaken with (2:= H0); auto with set.
  destruct ldepend_rec_union_and.
  destruct (H2 _ le (ldepend_rec XX e)).
  rewrite H3 in H; rewrite H4 in H0; clear H1 H2 H3 H4.
  f_equal.
  apply IHe with XX.  
  apply req_mem_weaken with (2:= H); auto with set.
  apply req_mem_weaken with (2:= H0); auto with set.
  apply IHe0 with (Vset.empty,Vset.empty).
  apply req_mem_weaken with (2:= H); auto with set.
  apply req_mem_weaken with (2:= H0); auto with set.
 Qed.

 
 (** Cast a CertiCrypt expression to a sided-Easycrpt expression *)
 Fixpoint e2E_rec (to_lv:Vset.t) (side:bool) t (e:E.expr t) : Exp t :=
  match e with
   | E.Ecte t c =>  Ecnst c
   | E.Evar t v => 
     if Vset.mem v to_lv then VarLogic v 
     else if side then Evar (VarLeft v) else Evar (VarRight v)
   | E.Eop op args => Eapp op (dmap _ (e2E_rec to_lv side) args)
   | E.Eexists _ v e l => 
     Eexists v (e2E_rec (Vset.add v to_lv) side e) (e2E_rec to_lv side l)
   | E.Eforall _ v e l => 
     Eforall v (e2E_rec (Vset.add v to_lv) side e) (e2E_rec to_lv side l)
   | E.Efind _ v e l => 
     Efind v (e2E_rec (Vset.add v to_lv) side e) (e2E_rec to_lv side l)
   end.

 Definition e2E := e2E_rec Vset.empty.

 Definition smem (side:bool) k (m1 m2:Mem.t k) := if side then m1 else m2.

 Lemma smem_upd : forall side k (m1 m2:Mem.t k) t (x:Var.var t) v,
  smem side (m1{!x<--v!}) (m2{!x<--v!}) = (smem side m1 m2){!x<--v!}.
 Proof. 
  destruct side; trivial. 
 Qed.

 Lemma e2E_rec_correct : forall (side:bool) t (e:E.expr t) k 
  (m1 m1' m2 m2':Mem.t k) l to_lv,
  (forall t (x:Var.var t), Vset.mem x to_lv -> assoc x l = smem side m1' m2' x) -> 
  (forall t (x:Var.var t), 
   ~Vset.mem x to_lv -> smem side m1 m2 x = smem side m1' m2' x) ->
  eeval m1 m2 l (e2E_rec to_lv side e) = E.eval_expr e (smem side m1' m2').
 Proof.
  intros side; induction e using  E.expr_ind2 with 
   (Pl :=
   fun l0 larg => forall k (m1 m1' m2 m2' : Mem.t k) l to_lv,
    (forall t (x:Var.var t), 
     Vset.mem x to_lv -> assoc x l = smem side m1' m2' x) ->
    (forall t (x:Var.var t), 
     ~Vset.mem x to_lv -> smem side m1 m2 x = smem side m1' m2' x) ->
    dmap _ (eeval m1 m2 l) (dmap _ (e2E_rec to_lv side) larg) =
    dmap _ (fun t0 (e:E.expr t0) => E.eval_expr e (smem side m1' m2')) larg);
  simpl; intros; trivial.
  case_eq (Vset.mem v to_lv); intros;[simpl; auto | ].
  rewrite <- not_is_true_false in H1.
  destruct side; simpl; auto.
  unfold O.eval_op; f_equal; auto.
  (* exists *)
  rewrite IHe2 with (m1':=m1') (m2':=m2'); auto.
  apply existsb_feq_compat; intros.
  rewrite IHe1 with(m1':=m1'{!v<--a!}) (m2':=m2'{!v<--a!});
   intros; rewrite smem_upd; trivial.
  assoc_case. 
  subst; rewrite Mem.get_upd_same; trivial.
  apply VsetP.add_spec in H2; destruct H2.
  revert H3; inversion H2; rewrite veqb_refl; discriminate.
  assert (Var.mkV v <> x) by (intros Heq; revert H3; inversion Heq; 
   rewrite veqb_refl; discriminate).
  rewrite Mem.get_upd_diff; trivial; apply H; trivial.
  assert (Var.mkV v <> x) by (intros Heq; apply H2; rewrite Heq; auto with set).
  rewrite Mem.get_upd_diff; auto with set.
  (* forall *)
  rewrite IHe2 with (m1':=m1') (m2':=m2'); auto.
  apply forallb_feq_compat; intros.
  rewrite IHe1 with(m1':=m1'{!v<--a!}) (m2':=m2'{!v<--a!}); intros; 
   rewrite smem_upd; trivial.
  assoc_case. 
  subst; rewrite Mem.get_upd_same; trivial.
  apply VsetP.add_spec in H2; destruct H2.
  revert H3; inversion H2; rewrite veqb_refl; discriminate.
  assert (Var.mkV v <> x) by (intros Heq; revert H3; inversion Heq; 
   rewrite veqb_refl; discriminate).
  rewrite Mem.get_upd_diff; trivial; apply H; trivial.
  assert (Var.mkV v <> x) by (intros Heq; apply H2; rewrite Heq; auto with set).
  rewrite Mem.get_upd_diff; auto with set.
  (* find *)
  rewrite IHe2 with (m1':=m1') (m2':=m2'); auto.
  apply find_feq_compat; intros.
  rewrite IHe1 with(m1':=m1'{!v<--a!}) (m2':=m2'{!v<--a!}); intros; 
   rewrite smem_upd; trivial.
  assoc_case. 
  subst; rewrite Mem.get_upd_same; trivial.
  apply VsetP.add_spec in H2; destruct H2.
  revert H3; inversion H2; rewrite veqb_refl; discriminate.
  assert (Var.mkV v <> x) by (intros Heq; revert H3; inversion Heq; 
   rewrite veqb_refl; discriminate).
  rewrite Mem.get_upd_diff; trivial; apply H; trivial.
  assert (Var.mkV v <> x) by (intros Heq; apply H2; rewrite Heq; auto with set).
  rewrite Mem.get_upd_diff; auto with set.
  (* cons *)
  rewrite IHe with (m1':= m1') (m2':= m2'); auto.
  rewrite IHe0 with (m1':= m1') (m2':= m2'); auto.
 Qed.

 Lemma e2E_correct : forall (side:bool) t (e:E.expr t) k (m1 m2:Mem.t k) l,
  eeval m1 m2 l (e2E side e) = E.eval_expr e (smem side m1 m2).
 Proof.
  intros; unfold e2E; apply e2E_rec_correct; intros; [ discriminate | trivial].
 Qed.

 Lemma lfv_e2E_rec : forall side t (e:E.expr t) X, lfv (e2E_rec X side e) [<=] X.
 Proof.
  intros side; induction e using  E.expr_ind2 with 
   (Pl :=
   fun l0 larg => forall X,
    dfold_left lfv_rec (dmap _ (e2E_rec X side) larg) Vset.empty [<=]  X); 
  unfold lfv in *; simpl; intros;
  auto with set.
  case_eq (Vset.mem v X); intros; simpl; auto with set.
  red; simpl; rewrite H; trivial.
  destruct side; auto with set.
  rewrite lfv_rec_union, lfv_rec_union; apply VsetP.union_subset; unfold lfv; auto.
  apply VsetP.subset_trans with (2:= remove_add v X).
  rewrite VsetP.union_sym, VsetP.union_empty; apply VsetP.subset_remove_ctxt.
  rewrite VsetP.union_sym, VsetP.union_empty; auto.
  rewrite lfv_rec_union, lfv_rec_union; apply VsetP.union_subset; unfold lfv; auto.
  apply VsetP.subset_trans with (2:= remove_add v X).
  rewrite VsetP.union_sym, VsetP.union_empty; apply VsetP.subset_remove_ctxt.
  rewrite VsetP.union_sym, VsetP.union_empty; auto.
  rewrite lfv_rec_union, lfv_rec_union; apply VsetP.union_subset; unfold lfv; auto.
  apply VsetP.subset_trans with (2:= remove_add v X).
  rewrite VsetP.union_sym, VsetP.union_empty; apply VsetP.subset_remove_ctxt.
  rewrite VsetP.union_sym, VsetP.union_empty; auto.
  destruct lfv_rec_union_and; rewrite H0.
  apply VsetP.union_subset; auto.
 Qed.

 (** Embedding does not contain free logical variables *)
 Lemma lfv_e2E : forall side t (e:E.expr t), (lfv (e2E side e)) [=] Vset.empty.
 Proof.
  intros; unfold e2E; apply Vset.eq_complete; auto using lfv_e2E_rec with set.
 Qed.

 Local Open Scope bool_scope.
 
 (** Boolean equality of EasyCrypt expressions *)
 Fixpoint exp_eqb t1 t2 (e1:Exp t1) (e2:Exp t2) :=
  match e1, e2 with
   | Ecnst _ c1, Ecnst _ c2 => E.ceqb c1 c2
   | Evar _ v1, Evar _ v2 => lvar_eqb v1 v2
   | Eapp op1 args1, Eapp op2 args2 => 
     if O.eqb op1 op2 then dforall2 exp_eqb args1 args2 else false
   | Eexists _ v1 e1_1 e2_1, Eexists _ v2 e1_2 e2_2 => 
     Var.veqb v1 v2 && exp_eqb e1_1 e1_2 && exp_eqb e2_1 e2_2
   | Eforall _ v1 e1_1 e2_1, Eforall _ v2 e1_2 e2_2 => 
     Var.veqb v1 v2 && exp_eqb e1_1 e1_2 && exp_eqb e2_1 e2_2
   | Efind _ v1 e1_1 e2_1, Efind _ v2 e1_2 e2_2 => 
     Var.veqb v1 v2 && exp_eqb e1_1 e1_2 && exp_eqb e2_1 e2_2
   | _, _ => false
  end.

 Lemma exp_eqb_spec : forall t1 (e1:Exp t1) t2 (e2:Exp t2),
  if exp_eqb e1 e2 then eq_dep T.type Exp t1 e1 t2 e2 
  else ~eq_dep T.type Exp t1 e1 t2 e2 .
 Proof.
  induction e1 using Exp_ind2 with
   ( P := fun t1 (e1 : Exp t1) => forall t2 (e2 : Exp t2),
    if exp_eqb e1 e2 then eq_dep T.type Exp t1 e1 t2 e2 
     else ~eq_dep T.type Exp t1 e1 t2 e2)
   ( Pl := fun l1 (le1: dlist Exp l1) =>
    forall l2 (le2: dlist Exp l2),
     if dforall2 exp_eqb le1 le2 then
      eq_dep (list T.type) (dlist Exp) l1 le1 l2 le2
      else ~eq_dep (list T.type) (dlist Exp) l1 le1 l2 le2);
   match goal with
    |- forall (t2:T.type) (e2:Exp t2), _ => 
     destruct e2; simpl; try (intros Heq; inversion Heq; fail) 
    | _ => idtac end; simpl; intros.
  (* Cnst *)
  generalize (E.ceqb_spec_dep c c0); destruct (E.ceqb c c0); intros H.
  inversion H; subst; simpl; constructor.
  intros Heq; apply H; inversion Heq; simpl; constructor.
  
  (* Var *)
  generalize (lvar_eqb_spec_dep v l); destruct (lvar_eqb v l); intros.
  inversion H; subst; simpl; constructor.
  intros Heq; apply H; inversion Heq; simpl; constructor.
  
  (* App *)
  generalize (O.eqb_spec op op0); destruct (O.eqb op op0); intros; subst.
  generalize (IHe1 _ d); destruct (dforall2 exp_eqb args0 d); intros.
  rewrite (T.l_eq_dep_eq H); constructor.
  intros Heq; apply H; inversion Heq.
  rewrite (O.inj_pair2 H0); constructor.
  intros Heq; apply H; inversion Heq; trivial.

  (* Exists *)
  generalize (IHe1_1 _ e2_1); clear IHe1_1.
  generalize (IHe1_2 _ e2_2); clear IHe1_2.
  case_eq (exp_eqb e1_2 e2_2); simpl.
  case_eq (exp_eqb e1_1 e2_1); simpl.
  case_eq (Var.veqb v v0); simpl; intros.
  inversion H2; subst.
  apply inj_pair2_eq_dec in H7; subst; trivial.
  inversion H3; subst.
  apply inj_pair2_eq_dec in H4; subst; trivial.
  apply veqb_true in H.
  rewrite H; trivial.
  apply Teq_dec.
  apply Teq_dec.
  intro.
  inversion H4; subst.
  apply inj_pair2_eq_dec in H7; subst; trivial.
  rewrite veqb_refl in H; discriminate.
  apply Teq_dec.
  intros.
  rewrite andb_false_r; simpl.
  intro Heq; apply H2.
  inversion Heq; subst.
  apply inj_pair2_eq_dec in H7; subst; trivial.
  apply Teq_dec.
  intros.
  rewrite andb_false_r; simpl.
  intro Heq; apply H0.
  inversion Heq; subst.
  apply inj_pair2_eq_dec in H6; subst; trivial.
  apply Teq_dec.

  (* Forall *)
  generalize (IHe1_1 _ e2_1); clear IHe1_1.
  generalize (IHe1_2 _ e2_2); clear IHe1_2.
  case_eq (exp_eqb e1_2 e2_2); simpl.
  case_eq (exp_eqb e1_1 e2_1); simpl.
  case_eq (Var.veqb v v0); simpl; intros.
  inversion H2; subst.
  apply inj_pair2_eq_dec in H7; subst; trivial.
  inversion H3; subst.
  apply inj_pair2_eq_dec in H4; subst; trivial.
  apply veqb_true in H.
  rewrite H; trivial.
  apply Teq_dec.
  apply Teq_dec.
  intro.
  inversion H4; subst.
  apply inj_pair2_eq_dec in H7; subst; trivial.
  rewrite veqb_refl in H; discriminate.
  apply Teq_dec.
  intros.
  rewrite andb_false_r; simpl.
  intro Heq; apply H2.
  inversion Heq; subst.
  apply inj_pair2_eq_dec in H7; subst; trivial.
  apply Teq_dec.
  intros.
  rewrite andb_false_r; simpl.
  intro Heq; apply H0.
  inversion Heq; subst.
  apply inj_pair2_eq_dec in H6; subst; trivial.
  apply Teq_dec.

  (* Find *)
  generalize (IHe1_1 _ e2_1); clear IHe1_1.
  generalize (IHe1_2 _ e2_2); clear IHe1_2.
  case_eq (exp_eqb e1_2 e2_2); simpl.
  case_eq (exp_eqb e1_1 e2_1); simpl.
  case_eq (Var.veqb v v0); simpl; intros.
  inversion H2; subst.
  apply inj_pair2_eq_dec in H7; subst; trivial.
  inversion H3; subst.
  apply inj_pair2_eq_dec in H4; subst; trivial.
  apply veqb_true in H.
  rewrite H; trivial.
  apply Teq_dec.
  apply Teq_dec.
  intro.
  inversion H4; subst.
  apply inj_pair2_eq_dec in H9; subst; trivial.
  rewrite veqb_refl in H; discriminate.
  apply Teq_dec.
  intros.
  rewrite andb_false_r; simpl.
  intro Heq; apply H2.
  inversion Heq; subst.
  apply inj_pair2_eq_dec in H7; subst; trivial.
  apply Teq_dec.
  intros.
  rewrite andb_false_r; simpl.
  intro Heq; apply H0.
  inversion Heq; subst.
  apply inj_pair2_eq_dec in H6; subst; trivial.
  apply Teq_dec.

  (* Nil *)
  destruct le2; simpl.
  constructor.
  intro H; inversion H.

  (* Cons *)
  destruct le2; simpl.
  intro H; inversion H.
  generalize (IHe1 _ e); clear IHe1.
  case_eq (exp_eqb e1 e); intros.
  generalize (IHe0 _ le2); clear IHe0.
  case_eq (dforall2 exp_eqb le le2); intros.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H6; subst; trivial.
  inversion H2; subst.
  apply inj_pair2_eq_dec in H7; subst; trivial.
  apply Tlist_eq_dec.
  apply Teq_dec.
  intro; apply H2.
  inversion H3; subst.
  apply inj_pair2_eq_dec in H11; subst; trivial.
  apply Teq_dec.
  intro; apply H0.
  inversion H1; subst.
  apply inj_pair2_eq_dec in H9; subst; trivial.
  apply Teq_dec.
 Qed.

 Lemma exp_eqb_spec2 : forall t (e1:Exp t) (e2:Exp t),
  if exp_eqb e1 e2 then e1 = e2 else e1 <> e2. 
 Proof.
  intros; generalize (exp_eqb_spec e1 e2).
  destruct (exp_eqb e1 e2); intros.
  inversion H.
  apply inj_pair2_eq_dec in H2; subst; trivial.
  apply Teq_dec.
  intro Heq; elim H; subst; auto.
 Qed.

 (**************************************************)
 (************ Relational Predicates ***************)
 (**************************************************)

 (** Predicates over EasyCrypt expressions *)
 Inductive pred : Type :=
 | Ptrue : pred
 | Pfalse : pred
 | Pnot : pred -> pred
 | Pand : pred -> pred -> pred
 | Por : pred -> pred -> pred
 | Pimplies : pred -> pred -> pred
 | Piff : pred -> pred -> pred
 | Pif : Exp T.Bool -> pred -> pred -> pred
 | Pforall : forall t : T.type, Var.var t -> pred -> pred
 | Pexists : forall t : T.type, Var.var t -> pred -> pred
 | Plet : forall t : T.type, Var.var t -> Exp t -> pred -> pred
 | Pexp : Exp T.Bool -> pred
 | Peq : forall t : T.type, Exp t -> Exp t -> pred
 | Ple : Exp T.Zt -> Exp T.Zt -> pred 
 | Plt : Exp T.Zt -> Exp T.Zt -> pred.

 (** Boolean equality of relational predicates *)
 Fixpoint pred_eqb p1 p2 {struct p1} :=
  match p1, p2 with
   | Ptrue, Ptrue => true
   | Pfalse, Pfalse => true
   | Pnot p1, Pnot p2 => pred_eqb p1 p2
   | Pand p1a p1b, Pand p2a p2b => pred_eqb p1a p2a && pred_eqb p1b p2b
   | Por p1a p1b, Por p2a p2b => pred_eqb p1a p2a && pred_eqb p1b p2b
   | Pimplies p1a p1b, Pimplies p2a p2b => pred_eqb p1a p2a && pred_eqb p1b p2b
   | Piff p1a p1b, Piff p2a p2b => pred_eqb p1a p2a && pred_eqb p1b p2b
   | Pif c1 pt1 pf1, Pif c2 pt2 pf2 => 
     exp_eqb c1 c2 && pred_eqb pt1 pt2 && pred_eqb pf1 pf2
   | Pforall _ v1 p1, Pforall _ v2 p2 => Var.veqb v1 v2 && pred_eqb p1 p2
   | Pexists _ v1 p1, Pexists _ v2 p2 => Var.veqb v1 v2 && pred_eqb p1 p2
   | Plet _ v1 e1 p1, Plet _ v2 e2 p2 => 
     Var.veqb v1 v2 && exp_eqb e1 e2 && pred_eqb p1 p2
   | Pexp e1, Pexp e2 => exp_eqb e1 e2
   | Peq _ e1 e2, Peq _ e3 e4 => exp_eqb e1 e3 && exp_eqb e2 e4
   | Ple e1 e2, Ple e3 e4 => exp_eqb e1 e3 && exp_eqb e2 e4
   | Plt e1 e2, Plt e3 e4 => exp_eqb e1 e3 && exp_eqb e2 e4
   | _, _ => false
  end.
 
 Lemma pred_eqb_spec : forall p1 p2, if pred_eqb p1 p2 then p1 = p2 else p1 <> p2.
 Proof.
  induction p1; destruct p2; simpl; trivial; try discriminate;
   try ((generalize (IHp1_1 p2_1); destruct (pred_eqb p1_1 p2_1); intros Heq1;
    [subst | intros Heq2; apply Heq1; inversion Heq2]; trivial;
     generalize (IHp1_2 p2_2); destruct (pred_eqb p1_2 p2_2); intros Heq3;
      [subst; simpl | intros Heq4; apply Heq3; inversion Heq4]; trivial)).
  generalize (IHp1 p2); destruct (pred_eqb p1 p2); intros Heq1;
   [subst | intros Heq2; apply Heq1; inversion Heq2]; trivial.
  generalize (exp_eqb_spec e e0); destruct (exp_eqb e e0); intros Heq;
   [ inversion Heq | intros Heq2; apply Heq; inversion Heq2; trivial].
  apply T.inj_pair2 in H; subst.
  generalize (IHp1_1 p2_1); destruct (pred_eqb p1_1 p2_1); intros Heq1;
   [subst | intros Heq2; apply Heq1; inversion Heq2]; trivial;
    generalize (IHp1_2 p2_2); destruct (pred_eqb p1_2 p2_2); intros Heq3;
     [subst; simpl | intros Heq4; apply Heq3; inversion Heq4]; trivial.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); intros Heq;
   [ inversion Heq; clear Heq | intros Heq2; apply Heq; inversion Heq2; trivial];
   subst; apply T.inj_pair2 in H2; subst;
    generalize (IHp1 p2); destruct (pred_eqb p1 p2); intros Heq1;
     [subst; simpl | intros Heq2; apply Heq1; inversion Heq2]; trivial.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); intros Heq;
   [ inversion Heq; clear Heq | intros Heq2; apply Heq; inversion Heq2; trivial];
   subst; apply T.inj_pair2 in H2; subst;
    generalize (IHp1 p2); destruct (pred_eqb p1 p2); intros Heq1;
     [subst; simpl | intros Heq2; apply Heq1; inversion Heq2]; trivial.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); intros Heq;
   [ inversion Heq; clear Heq | 
     simpl; intros Heq2; apply Heq; inversion Heq2; trivial].
  subst; apply T.inj_pair2 in H2; subst.
  generalize (exp_eqb_spec e e0); destruct (exp_eqb e e0); intros Heq;
   [ inversion Heq | intros Heq2; apply Heq; inversion Heq2; trivial].
  apply T.inj_pair2 in H2; subst.
  generalize (IHp1 p2); destruct (pred_eqb p1 p2); intros Heq1;
   [subst; simpl | intros Heq2; apply Heq1; inversion Heq2]; trivial.
  apply T.inj_pair2 in H0; subst; trivial.
  subst; apply T.inj_pair2 in H1; subst; trivial.
  generalize (exp_eqb_spec e e0); destruct (exp_eqb e e0); intros Heq;
   [ inversion Heq | intros Heq2; apply Heq; inversion Heq2; trivial].
  apply T.inj_pair2 in H; subst; trivial.
  generalize (exp_eqb_spec e e1); destruct (exp_eqb e e1); intros Heq;
   [ inversion Heq | intros Heq2; apply Heq; inversion Heq2; trivial].
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); intros Heq1;
   [ inversion Heq1; simpl; subst | 
     intros Heq2; apply Heq1; inversion Heq2; trivial].
  apply T.inj_pair2 in H2; apply T.inj_pair2 in H5; subst; trivial.
  subst; apply T.inj_pair2 in H1; subst; trivial.
  generalize (exp_eqb_spec e e1); destruct (exp_eqb e e1); intros Heq;
   [ inversion Heq | intros Heq2; apply Heq; inversion Heq2; trivial].
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); intros Heq1;
   [ inversion Heq1; simpl; subst | 
     intros Heq2; apply Heq1; inversion Heq2; trivial].
  apply T.inj_pair2 in H; apply T.inj_pair2 in H0; subst; trivial.
  generalize (exp_eqb_spec e e1); destruct (exp_eqb e e1); intros Heq;
   [ inversion Heq | intros Heq2; apply Heq; inversion Heq2; trivial].
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); intros Heq1;
   [ inversion Heq1; simpl; subst | 
     intros Heq2; apply Heq1; inversion Heq2; trivial].
  apply T.inj_pair2 in H; apply T.inj_pair2 in H0; subst; trivial.
 Qed.

 (** Eval a relational preidcate given a pair of memories and a
     valuation for logical variables *)
 Fixpoint peval k (m1 m2:Mem.t k) (l:lmem k) (p:pred) : Prop :=
  match p with
   | Ptrue => True
   | Pfalse => False
   | Pnot p' => ~ (peval m1 m2 l p')
   | Pand p1 p2 => (peval m1 m2 l p1) /\ (peval m1 m2 l p2)
   | Por p1 p2 => (peval m1 m2 l p1) \/ (peval m1 m2 l p2)
   | Pimplies p1 p2 =>  (peval m1 m2 l p1) -> (peval m1 m2 l p2)
   | Piff p1 p2 => (peval m1 m2 l p1) <-> (peval m1 m2 l p2)
   | Pif e pt pf => if eeval m1 m2 l e then 
     peval m1 m2 l pt else peval m1 m2 l pf
   | Pforall t X P => forall (x : T.interp k t),
     peval m1 m2 (LVV k X x :: l) P
   | Pexists t X P =>  exists x : T.interp k t,
     peval m1 m2 (LVV k X x :: l) P
   | Plet t X e P => 
     peval m1 m2 (LVV k X (eeval m1 m2 l e) :: l) P
   | Pexp e => eeval m1 m2 l e = true
   | Peq _ e1 e2 => eeval m1 m2 l e1 = eeval m1 m2 l e2
   | Ple e1 e2 => 
     (eeval m1 m2 l e1 <= eeval m1 m2 l e2)%Z
   | Plt e1 e2 =>
     (eeval m1 m2 l e1 < eeval m1 m2 l e2)%Z
  end.

 Definition ipred (p:pred) : mem_rel := fun k (m1 m2:Mem.t k) => peval m1 m2 nil p.

 Lemma pred_eqb_eval : forall p1 p2 k (m1 m2:Mem.t k) l,
  pred_eqb p1 p2 = true ->
  (peval m1 m2 l p1 <-> peval m1 m2 l p2).
 Proof.
  intros p1 p2 k m1 m2 l H; generalize (pred_eqb_spec p1 p2);
   rewrite H; intros; subst; split; auto.
 Qed.

 (** Free variables of a relational predicate *) 
 Fixpoint pfv_rec X (p:pred) : Vset.t :=
  match p with
   | Ptrue | Pfalse => X
   | Pnot p' => pfv_rec X p'
   | Pand p1 p2 => pfv_rec (pfv_rec X p1) p2
   | Por p1 p2 => pfv_rec (pfv_rec X p1) p2
   | Pimplies p1 p2 => pfv_rec (pfv_rec X p1) p2
   | Piff p1 p2 => pfv_rec (pfv_rec X p1) p2
   | Pif c p1 p2 => pfv_rec (pfv_rec (lfv_rec X c) p1) p2
   | Pforall t x p => Vset.union X (Vset.remove x (pfv_rec Vset.empty p))
   | Pexists t x p => Vset.union X (Vset.remove x (pfv_rec Vset.empty p))
   | Plet t x e p => 
     Vset.union (lfv_rec X e) (Vset.remove x (pfv_rec Vset.empty p))
   | Pexp e => lfv_rec X e
   | Peq t e1 e2 => lfv_rec (lfv_rec X e1) e2
   | Ple e1 e2 => lfv_rec (lfv_rec X e1) e2
   | Plt e1 e2 => lfv_rec (lfv_rec X e1) e2
  end.

 Definition pfv := pfv_rec Vset.empty.

 Lemma pfv_rec_union : forall P X, pfv_rec X P [=] Vset.union (pfv P) X.
 Proof.
  induction P; simpl; intros; auto with set; unfold pfv; simpl;
   try ((rewrite IHP2, IHP2, IHP1, VsetP.union_assoc;
    auto using VsetP.union_morphism with set) || apply VsetP.union_sym ||
   ( repeat rewrite lfv_rec_union; rewrite VsetP.union_assoc;
    apply VsetP.union_morphism;[  | apply VsetP.union_morphism;[
     rewrite VsetP.union_sym; rewrite VsetP.union_empty | ] ]; auto with set)).
  rewrite IHP1; apply VsetP.union_morphism; auto with set.
  rewrite VsetP.union_assoc; apply VsetP.union_morphism; auto with set.
  apply lfv_rec_union.
  rewrite lfv_rec_union, !VsetP.union_assoc.
  apply VsetP.union_morphism; auto with set.
  apply VsetP.union_sym.
  apply lfv_rec_union.
 Qed.

 
 (**********************************************)
 (****** Smart Predicate Constructors **********)
 (**********************************************)

 Definition pnot p := 
  match p with
   | Ptrue => Pfalse
   | Pfalse => Ptrue
   | Pnot (Pexp e) => Pexp e
(* | Pnot p => p (* classical *) *)
   | _ => Pnot p
  end.

 Definition pand p1 p2 :=
  match p1, p2 with
   | Ptrue, _ => p2
   | Pfalse, _ => Pfalse
   | _, Ptrue => p1
   | _, Pfalse => Pfalse
   | _, _ => Pand p1 p2
  end.

 Definition por p1 p2 :=
  match p1,p2 with
   | Ptrue, _ => Ptrue
   | Pfalse, _ => p2
   | _, Ptrue => Ptrue
   | _, Pfalse => p1
   | _, _=> Por p1 p2
  end.

 Fixpoint pimplies p1 p2 := 
  if pred_eqb p1 p2 then Ptrue 
  else
   match p1, p2 with
    | Ptrue, _ => p2
    | Pfalse, _ => Ptrue
    | Pand p1a p1b, _ =>  pimplies p1a (pimplies p1b p2)
    | _, Ptrue => Ptrue
    | _, Pfalse => pnot p1
    | _, _ => if pred_eqb p1 p2 then Ptrue else  Pimplies p1 p2
   end.
 
 Definition pforall t (x:Var.var t) p := Pforall x p.
 (* if Vset.mem x (pfv p) then Pforall x p else p. *)

 Definition pexists t (x:Var.var t) p := Pexists x p.
 (* if Vset.mem x (pfv p) then Pexists x p else p. *)
 
 Definition plet t (x:Var.var t) e p :=
  if Vset.mem x (pfv p) then Plet x e p else p.
 
 Definition ple (e1 e2:Exp T.Zt) := Ple e1 e2.
 
 Definition plt e1 e2:= Plt e1 e2.
 
 (* TODO: Make further simplifications *)
 Definition pexp (e:Exp T.Bool) := Pexp e.

 Definition peq t (e1 e2 : Exp t) : pred :=
   if exp_eqb e1 e2 then Ptrue else @Peq t e1 e2.

 (* Definition peq_bool (e1 e2 : Exp T.Bool) : pred := *)
 (*   match e1, e2 with *)
 (*     | _, Ecnst _ true => Pexp e1 *)
 (*     | Ecnst _ true, _ => Pexp e2 *)
 (*     | _, _ => peq e1 e2 *)
 (*  end. *)

 Definition pif (e:Exp T.Bool) p1 p2 : pred :=
  match p1, p2 with
   | Ptrue, _ => pimplies (pnot (pexp e)) p2
   | _, Ptrue => pimplies (pexp e) p1
   | _,_ => (if pred_eqb p1 p2 then p1 else Pif e p1 p2)
  end.

 Definition piff p1 p2 := 
  match p1, p2 with
   | Ptrue, _ => p2
   | _, Ptrue => p1
   | Pfalse, _ => pnot p2
   | _, Pfalse => pnot p1
   | Pexp e1, Pexp e2 => peq e1 e2
   | _, _ => if pred_eqb p1 p2 then Ptrue else Piff p1 p2
  end.
 
 Lemma peval_pnot : forall k (m1 m2:Mem.t k) l P,
  peval m1 m2 l (pnot P) <-> ~peval m1 m2 l P.
 Proof.
  induction P; try (simpl; tauto).
  destruct P; try (simpl; tauto).
 Qed.
 
 Lemma peval_pand : forall k (m1 m2:Mem.t k) l P Q,
  peval m1 m2 l (pand P Q) <-> (peval m1 m2 l P /\ peval m1 m2 l Q).
 Proof.
  induction P; destruct Q; try (simpl; tauto).
 Qed.
 
 Lemma pand_Ptrue : forall p:pred, pand Ptrue p = p.
 Proof.
  trivial.
 Qed.
 
 Lemma peval_por : forall k (m1 m2:Mem.t k) l P Q,
  peval m1 m2 l (por P Q) <-> (peval m1 m2 l P \/ peval m1 m2 l Q).
 Proof.
  induction P; destruct Q; try (simpl; tauto).
 Qed.

 Lemma pimplies_Ptrue : forall p, pimplies Ptrue p = p.
 Proof.
  unfold pimplies;intros p.
  generalize (pred_eqb_spec Ptrue p); destruct (pred_eqb Ptrue p); trivial.
 Qed.

 Lemma peval_pimplies : forall k (m1 m2:Mem.t k) P Q l,
  peval m1 m2 l (pimplies P Q) <->
  (peval m1 m2 l P -> peval m1 m2 l Q).
 Proof.
  induction P; destruct Q; simpl; intros; try tauto;
   try (generalize (pred_eqb_spec P1 Q1); destruct (pred_eqb P1 Q1);
    simpl; intros; subst; try tauto;
     generalize (pred_eqb_spec P2 Q2); destruct (pred_eqb P2 Q2); 
      simpl; intros; subst; try tauto);
   try (rewrite IHP1, IHP2; simpl; tauto); 
    try (generalize (exp_eqb_spec2 e e0); destruct (exp_eqb e e0); 
     simpl; intros; subst; tauto).
  destruct P; simpl; tauto.
  generalize (pred_eqb_spec P Q); destruct (pred_eqb P Q); 
   trivial; intros; simpl; [rewrite H | ]; tauto.

  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); simpl; intros.
  inversion H; subst; apply inj_pair2_eq_dec in H3; subst; trivial.
  generalize (pred_eqb_spec P Q); destruct (pred_eqb P Q); 
   trivial; intros; simpl; [rewrite H0 | ]; split; intros; auto.
  apply Teq_dec.
  split; intros; auto.

  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); simpl; intros.
  inversion H; subst; apply inj_pair2_eq_dec in H3; subst; trivial.
  generalize (pred_eqb_spec P Q); destruct (pred_eqb P Q); 
   trivial; intros; simpl; [rewrite H0 | ]; split; intros; auto.
  apply Teq_dec.
  split; intros; auto.

  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); 
   simpl; intros; try tauto.
  inversion H; subst; apply inj_pair2_eq_dec in H3; subst; trivial.
  generalize (exp_eqb_spec2 e e0); destruct (exp_eqb e e0); 
   simpl; intros; subst; try tauto.
  generalize (pred_eqb_spec P Q); destruct (pred_eqb P Q); 
   trivial; intros; simpl; [rewrite H0 | ]; split; intros; auto; try tauto.
  apply Teq_dec.

  generalize (exp_eqb_spec e e1); destruct (exp_eqb e e1); simpl; try tauto.
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); 
   simpl; intros; try tauto.
  inversion H; subst.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H4; subst; trivial.
  apply inj_pair2_eq_dec in H5; subst; trivial.
  tauto.
  apply Teq_dec.
  apply Teq_dec.

  generalize (exp_eqb_spec e e1); destruct (exp_eqb e e1); simpl; try tauto.
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); 
   simpl; intros; try tauto.
  inversion H; subst.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H1; subst; trivial.
  apply inj_pair2_eq_dec in H2; subst; trivial.
  tauto.
  apply Teq_dec.
  apply Teq_dec.

  generalize (exp_eqb_spec e e1); destruct (exp_eqb e e1); simpl; try tauto.
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); 
   simpl; intros; try tauto.
  inversion H; subst.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H1; subst; trivial.
  apply inj_pair2_eq_dec in H2; subst; trivial.
  tauto.
  apply Teq_dec.
  apply Teq_dec.
 Qed.

 Lemma peval_pif : forall k (m1 m2:Mem.t k) l e Qt Qf, 
  peval m1 m2 l (pif e Qt Qf) <-> peval m1 m2 l (Pif e Qt Qf).
 Proof.
  destruct Qt; destruct Qf; simpl; try (case_eq (eeval m1 m2 l e); intros He); 
   try tauto; 
   try solve [ split; intros; auto | split; intros; auto; try discriminate | 
               generalize (pred_eqb_spec Qt1 Qf1); destruct (pred_eqb Qt1 Qf1); 
               intros; subst; simpl; try rewrite He; try tauto;
               generalize (pred_eqb_spec Qt2 Qf2); 
               destruct (pred_eqb Qt2 Qf2); 
               intros; subst; simpl; try rewrite He; try tauto ].
  destruct Qf; simpl; try rewrite He; split; intros; auto.
  generalize (exp_eqb_spec e e0); destruct (exp_eqb e e0); simpl; try tauto.
  destruct Qf; simpl; try rewrite He; split; intros; auto.
  generalize (exp_eqb_spec e e0); destruct (exp_eqb e e0); 
   simpl; try tauto; intros.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H1; subst; trivial.
  rewrite He; intro Heq; discriminate.
  apply Teq_dec.
  intro Heq; elim H0; simpl in *.
  elim H; trivial.
  rewrite He; intro Heq'; discriminate.
  generalize (exp_eqb_spec e e0); destruct (exp_eqb e e0); simpl; try tauto; intros.
  split; intros; destruct (eeval m1 m2 l e0); auto.
  generalize (pred_eqb_spec Qt Qf); destruct (pred_eqb Qt Qf); 
   intros; subst; simpl; try rewrite He; tauto.
  generalize (pred_eqb_spec Qt Qf); destruct (pred_eqb Qt Qf); 
   intros; subst; simpl; try rewrite He; tauto.
  generalize (pred_eqb_spec Qt1 Qf1); destruct (pred_eqb Qt1 Qf1); 
   intros; subst; simpl; try rewrite He; try tauto;
   generalize (pred_eqb_spec Qt2 Qf2); destruct (pred_eqb Qt2 Qf2); 
    intros; subst; simpl; try rewrite He; try tauto;
    generalize (exp_eqb_spec e0 e1); destruct (exp_eqb e0 e1);
     simpl; try tauto; try rewrite He; intros; tauto.
  generalize (pred_eqb_spec Qt1 Qf1); destruct (pred_eqb Qt1 Qf1); 
   intros; subst; simpl; try rewrite He; try tauto;
   generalize (pred_eqb_spec Qt2 Qf2); destruct (pred_eqb Qt2 Qf2);
    intros; subst; simpl; try rewrite He; try tauto;
    generalize (exp_eqb_spec e0 e1); destruct (exp_eqb e0 e1); 
     simpl; try tauto; try rewrite He; intros; try tauto.
  inversion H; subst.
  apply inj_pair2_eq_dec in H0; subst; trivial;
   [ split; intros; auto | apply Teq_dec ].
  generalize (pred_eqb_spec Qt Qf); destruct (pred_eqb Qt Qf); 
   intros; subst; simpl; try rewrite He.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); simpl; intros.  
  split; intros; auto.
  rewrite He; split; intros; auto.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); simpl; intros.
  rewrite He; split; intros; auto.
  rewrite He; split; intros; auto.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); simpl; intros.
  generalize (pred_eqb_spec Qt Qf); destruct (pred_eqb Qt Qf); 
   intros; subst; simpl; try rewrite He.
  split; intros; auto.   
  inversion H; subst.
  apply inj_pair2_eq_dec in H4; subst; auto; apply Teq_dec.
  inversion H; subst.
  apply inj_pair2_eq_dec in H4; subst; auto; apply Teq_dec.
  inversion H; subst.
  apply inj_pair2_eq_dec in H4; subst;[ split; intros; auto | apply Teq_dec ].
  rewrite He; split; intros; auto.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); simpl; intros.
  generalize (pred_eqb_spec Qt Qf); destruct (pred_eqb Qt Qf); 
   intros; subst; simpl; try rewrite He; tauto.
  rewrite He; split; intros; auto.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); simpl; intros.
  generalize (pred_eqb_spec Qt Qf); destruct (pred_eqb Qt Qf); 
   intros; subst; simpl; try rewrite He.
  inversion H; subst.
  apply inj_pair2_eq_dec in H3; subst;[ split; intros; auto | apply Teq_dec ].
  inversion H; subst.
  apply inj_pair2_eq_dec in H4; subst;[ split; intros; auto | apply Teq_dec ].
  rewrite He; split; intros; auto.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); simpl; intros.
  generalize (exp_eqb_spec e0 e1); destruct (exp_eqb e0 e1);
   simpl; try tauto; intros.
  generalize (pred_eqb_spec Qt Qf); destruct (pred_eqb Qt Qf); 
   intros; subst; simpl; try rewrite He; tauto.
  rewrite He; split; intros; auto.   
  rewrite He; split; intros; auto.   
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); simpl; intros.
  generalize (exp_eqb_spec e0 e1); destruct (exp_eqb e0 e1); 
   simpl; try tauto; intros.
  generalize (pred_eqb_spec Qt Qf); destruct (pred_eqb Qt Qf); 
   intros; subst; simpl; try rewrite He.
  inversion H; subst.
  apply inj_pair2_eq_dec in H4; subst;[ split; intros; auto | apply Teq_dec ].
  inversion H0; subst.
  apply inj_pair2_eq_dec in H5; subst; auto; apply Teq_dec.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H5; subst; auto; apply Teq_dec.
  split; intros; auto.   
  rewrite He; split; intros; auto.   
  rewrite He; split; intros; auto.
  generalize (exp_eqb_spec e e0); destruct (exp_eqb e e0); 
   simpl; try tauto; intros.
  inversion H; subst.
  apply inj_pair2_eq_dec in H0; subst; try tauto; apply Teq_dec.
  generalize (exp_eqb_spec e e0); destruct (exp_eqb e e0); 
   simpl; try tauto; intros.
  split; intros; auto.
  rewrite He in H1; discriminate.
  generalize (exp_eqb_spec e0 e1); destruct (exp_eqb e0 e1); 
   simpl; try tauto; intros.
  rewrite He; split; intros; auto.   
  generalize (exp_eqb_spec e0 e1); destruct (exp_eqb e0 e1); 
   simpl; try tauto; intros.
  inversion H; subst.
  apply inj_pair2_eq_dec in H0; subst; try tauto; apply Teq_dec.
  rewrite He; split; intros; auto.   
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); 
   simpl; try tauto; intros.
  generalize (exp_eqb_spec e1 e3); destruct (exp_eqb e1 e3); 
   simpl; try tauto; intros.
  rewrite He; split; intros; auto.
  rewrite He; split; intros; auto.  
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); 
   simpl; try tauto; intros.
  generalize (exp_eqb_spec e1 e3); destruct (exp_eqb e1 e3); 
   simpl; try tauto; intros.
  inversion H; subst.
  apply inj_pair2_eq_dec in H4; subst; try tauto; try apply Teq_dec.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H4; subst; try tauto; try apply Teq_dec.
  rewrite He; split; intros; auto.
  rewrite He; split; intros; auto.
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); 
   simpl; try tauto; intros.
  generalize (exp_eqb_spec e1 e3); destruct (exp_eqb e1 e3); 
   simpl; try tauto; intros.
  rewrite He; split; intros; auto.
  rewrite He; split; intros; auto.
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); 
   simpl; try tauto; intros.
  generalize (exp_eqb_spec e1 e3); destruct (exp_eqb e1 e3); 
   simpl; try tauto; intros.
  inversion H; subst.
  apply inj_pair2_eq_dec in H1; subst; try tauto; try apply Teq_dec.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H1; subst; try tauto; try apply Teq_dec.
  rewrite He; split; intros; auto.
  rewrite He; split; intros; auto.
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); 
   simpl; try tauto; intros.
  generalize (exp_eqb_spec e1 e3); destruct (exp_eqb e1 e3); 
   simpl; try tauto; intros.
  rewrite He; split; intros; auto.
  rewrite He; split; intros; auto.
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); 
   simpl; try tauto; intros.
  generalize (exp_eqb_spec e1 e3); destruct (exp_eqb e1 e3); 
   simpl; try tauto; intros.
  inversion H; subst.
  apply inj_pair2_eq_dec in H1; subst; try tauto; try apply Teq_dec.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H1; subst; try tauto; try apply Teq_dec.
  rewrite He; split; intros; auto.
  rewrite He; split; intros; auto.
 Qed.

 Lemma peval_piff : forall k (m1 m2:Mem.t k) l p1 p2, 
  peval m1 m2 l (piff p1 p2) <-> peval m1 m2 l (Piff p1 p2).
 Proof.
  simpl; destruct p1; destruct p2; simpl; try tauto;
    try (
  generalize (pred_eqb_spec p1_1 p2_1); destruct (pred_eqb p1_1 p2_1); 
               intros; subst; simpl; try rewrite He; try tauto;
               generalize (pred_eqb_spec p1_2 p2_2); 
               destruct (pred_eqb p1_2 p2_2); 
               intros; subst; simpl; try rewrite He; try tauto).
  destruct p2; simpl; try tauto.
  destruct p1; simpl; try tauto. 
  generalize (pred_eqb_spec p1 p2); destruct (pred_eqb p1 p2); simpl; try tauto; intros; subst; tauto.
  generalize (exp_eqb_spec e e0); destruct (exp_eqb e e0); simpl; try tauto; intros.
  inversion H.
  apply inj_pair2_eq_dec in H0; subst; trivial.
  tauto.
  apply Teq_dec.
  rewrite andb_false_r; simpl; tauto.
  rewrite andb_false_r; simpl; tauto.
  rewrite andb_false_r; simpl; tauto.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); simpl; intros.  
  inversion H; subst.
  apply inj_pair2_eq_dec in H3; subst; try tauto; try apply Teq_dec.
  generalize (pred_eqb_spec p1 p2); destruct (pred_eqb p1 p2); 
   intros; subst; simpl; try rewrite He; tauto.
  tauto.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); simpl; intros.  
  inversion H; subst.
  apply inj_pair2_eq_dec in H3; subst; try tauto; try apply Teq_dec.
  generalize (pred_eqb_spec p1 p2); destruct (pred_eqb p1 p2); 
   intros; subst; simpl; try rewrite He; tauto.
  tauto.
  generalize (Var.veqb_spec_dep v v0); destruct (Var.veqb v v0); simpl; intros.  
  inversion H; subst.
  apply inj_pair2_eq_dec in H3; subst; try tauto; try apply Teq_dec.
  generalize (exp_eqb_spec e e0); destruct (exp_eqb e e0); simpl; try tauto; intros.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H4; subst; try tauto; try apply Teq_dec.
  generalize (pred_eqb_spec p1 p2); destruct (pred_eqb p1 p2); 
   intros; subst; simpl; try rewrite He.
  tauto.
  tauto.
  tauto.
  unfold peq; simpl.
  generalize (exp_eqb_spec e e0); destruct (exp_eqb e e0); simpl; try tauto; intros.
  inversion H; subst.
  apply inj_pair2_eq_dec in H0; subst; try tauto; try apply Teq_dec.
  split; intros.
  rewrite H0; tauto.
  destruct H0.
  case_eq ( eeval m1 m2 l e ); intros.
  symmetry.
  apply H0; trivial.
  symmetry.  
  apply not_true_is_false; intro.
  apply H1 in H3.
  rewrite H2 in H3; discriminate.
  generalize (exp_eqb_spec e e1); destruct (exp_eqb e e1); simpl; try tauto; intros.
  inversion H; subst.
  apply inj_pair2_eq_dec in H3; subst; try tauto; try apply Teq_dec.
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); simpl; try tauto; intros.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H4; subst; try tauto; try apply Teq_dec.
  generalize (exp_eqb_spec e e1); destruct (exp_eqb e e1); simpl; try tauto; intros.
  inversion H; subst.
  apply inj_pair2_eq_dec in H0; subst; try tauto; try apply Teq_dec.
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); simpl; try tauto; intros.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H1; subst; try tauto; try apply Teq_dec.
  generalize (exp_eqb_spec e e1); destruct (exp_eqb e e1); simpl; try tauto; intros.
  inversion H; subst.
  apply inj_pair2_eq_dec in H0; subst; try tauto; try apply Teq_dec.
  generalize (exp_eqb_spec e0 e2); destruct (exp_eqb e0 e2); simpl; try tauto; intros.
  inversion H0; subst.
  apply inj_pair2_eq_dec in H1; subst; try tauto; try apply Teq_dec.
Qed.
 
 Notation "P1 /_\ P2" := (@pand P1 P2) (at level 80, right associativity).
 Notation "P1 \_/ P2" := (@por P1 P2) (at level 80, right associativity).
 Notation "P1 |_> P2" := (@pimplies P1 P2) (at level 80, right associativity).
 Notation "P1 <--> P2" := (@piff P1 P2) (at level 85, right associativity).
 Notation "'~_' P" := (@pnot P) (at level 75, right associativity).
 Notation "x '===' y" := (@peq _ x y).
 
 (** Bound variables of a relational predicate *)
 Fixpoint pbind_rec X (p:pred) : Vset.t := 
  match p with
   | Ptrue | Pfalse => X
   | Pnot p' => pbind_rec X p'
   | Pand p1 p2 => pbind_rec (pbind_rec X p1) p2
   | Por p1 p2 => pbind_rec (pbind_rec X p1) p2
   | Pimplies p1 p2 => pbind_rec (pbind_rec X p1) p2
   | Piff p1 p2 => pbind_rec (pbind_rec X p1) p2
   | Pif c p1 p2 => pbind_rec (pbind_rec (lbind_rec X c) p1) p2
   | Pforall t x p => pbind_rec (Vset.add x X) p
   | Pexists t x p => pbind_rec (Vset.add x X) p
   | Plet t x e p => pbind_rec (lbind_rec (Vset.add x X) e) p
   | Pexp e => lbind_rec X e
   | Peq t e1 e2 => lbind_rec (lbind_rec X e1) e2
   | Ple e1 e2 => lbind_rec (lbind_rec X e1) e2
   | Plt e1 e2 => lbind_rec (lbind_rec X e1) e2
  end.

 Definition pbind := pbind_rec Vset.empty.

 Lemma pbind_rec_union: forall P X, 
  pbind_rec X P [=] Vset.union (pbind P) X.
 Proof.
  induction P; simpl; intros; auto with set; unfold pbind; simpl;
   try ((rewrite IHP2, IHP2, IHP1, VsetP.union_assoc;
    auto using VsetP.union_morphism with set) || 
   (rewrite IHP, IHP, VsetP.union_assoc; 
    apply VsetP.union_morphism; auto with set) || 
   ( repeat rewrite lbind_rec_union; rewrite VsetP.union_assoc;
    apply VsetP.union_morphism;[  | apply VsetP.union_morphism;
     [ rewrite VsetP.union_sym; rewrite VsetP.union_empty | ] ]; auto with set)).
  rewrite IHP1; apply VsetP.union_morphism; auto with set.
  rewrite VsetP.union_assoc; apply VsetP.union_morphism; auto with set.
  apply lbind_rec_union.
  rewrite !lbind_rec_union, VsetP.union_assoc; auto with set.
  apply lbind_rec_union.
 Qed.
 
 Lemma pbind_Pnot : forall p, 
  pbind (Pnot p) [=] pbind p.
 Proof.
  intros; unfold pbind; 
  auto with set.
 Qed.

 Lemma pbind_Pand : forall p1 p2, 
  pbind (Pand p1 p2) [=] Vset.union (pbind p1) (pbind p2).
 Proof.
  intros; unfold pbind; simpl.
  rewrite pbind_rec_union, VsetP.union_sym; auto with set.
 Qed.
 
 Lemma pbind_Por : forall p1 p2, 
  pbind (Por p1 p2) [=] Vset.union (pbind p1) (pbind p2).
 Proof.
  intros; unfold pbind; simpl.
  rewrite pbind_rec_union, VsetP.union_sym; auto with set.
 Qed.

 Lemma pbind_Pimplies : forall p1 p2, 
  pbind (Pimplies p1 p2) [=] Vset.union (pbind p1) (pbind p2).
 Proof.
  intros; unfold pbind; simpl.
  rewrite pbind_rec_union, VsetP.union_sym; auto with set.
 Qed.

 Lemma pbind_Piff : forall p1 p2, 
  pbind (Piff p1 p2) [=] Vset.union (pbind p1) (pbind p2).
 Proof.
  intros; unfold pbind; simpl.
  rewrite pbind_rec_union, VsetP.union_sym; auto with set.
 Qed.

 Lemma pbind_Pif : forall e p1 p2, 
  pbind (Pif e p1 p2) [=] Vset.union (lbind e) (Vset.union (pbind p1) (pbind p2)).
 Proof.
  intros; unfold pbind at 1; simpl.
  rewrite !pbind_rec_union, <- VsetP.union_assoc.
  rewrite VsetP.union_sym; apply VsetP.union_morphism; auto with set.
  rewrite VsetP.union_sym; auto with set.
 Qed.

 Lemma pbind_Pforall : forall t x p, 
  pbind (@Pforall t x p) [=] Vset.add x (pbind p).
 Proof. 
  intros; unfold pbind at 1; simpl; rewrite !pbind_rec_union.
  rewrite VsetP.union_sym; auto with set.
 Qed.

 Lemma pbind_Pexists : forall t x p, 
  pbind (@Pexists t x p) [=] Vset.add x (pbind p).
 Proof. 
  intros; unfold pbind at 1; simpl; rewrite !pbind_rec_union.
  rewrite VsetP.union_sym; auto with set.
 Qed.

 Lemma pbind_Plet : forall t x e p,
  pbind (@Plet t x e p) [=] Vset.add x (Vset.union (lbind e) (pbind p)).
 Proof.
  intros; unfold pbind at 1; simpl.
  rewrite pbind_rec_union, lbind_rec_union, <- VsetP.union_assoc.
  rewrite VsetP.union_sym, (VsetP.union_sym (pbind p)); auto with set.
 Qed.

 Lemma pbind_Pexp : forall e,
  pbind (@Pexp e) [=] lbind e.
 Proof.
  auto with set.
 Qed.

 Lemma pbind_Peq : forall t e1 e2, 
  pbind (@Peq t e1 e2) [=] Vset.union (lbind e1) (lbind e2).
 Proof. 
  intros; unfold pbind at 1; simpl.
  rewrite lbind_rec_union; apply VsetP.union_sym.
 Qed.

 Lemma pbind_Ple : forall e1 e2,
  pbind (@Ple e1 e2) [=] Vset.union (lbind e1) (lbind e2).
 Proof. 
  intros; unfold pbind at 1; simpl.
  rewrite lbind_rec_union; apply VsetP.union_sym.
 Qed.

 Lemma pbind_Plt : forall e1 e2, 
  pbind (@Plt e1 e2) [=] Vset.union (lbind e1) (lbind e2).
 Proof. 
  intros; unfold pbind at 1; simpl.
  rewrite lbind_rec_union; apply VsetP.union_sym.
 Qed.

 

 (** Substitution in relational predicates *)
 Fixpoint psubst (p:pred) t (v:lvar t) (e:Exp t) : pred :=
  match p with 
   | Ptrue => Ptrue
   | Pfalse => Pfalse
   | Pnot p' => Pnot (psubst p' v e)
   | Pand p1 p2 => Pand (psubst p1 v e) (psubst p2 v e)
   | Por p1 p2 => Por (psubst p1 v e) (psubst p2 v e)
   | Pimplies p1 p2 => Pimplies (psubst p1 v e) (psubst p2 v e)
   | Piff p1 p2 => Piff (psubst p1 v e) (psubst p2 v e)
   | Pif c pt pf => Pif (esubst v e c) (psubst pt v e) (psubst pf v e)
   | Pforall _ x P => 
     Pforall x (if lvar_eqb (VarLogic x) v then P else psubst P v e)
   | Pexists _ x P => 
     Pexists x (if lvar_eqb (VarLogic x) v then P else psubst P v e)
   | Plet t x e' P => 
     let P := if lvar_eqb (VarLogic x) v then P else psubst P v e in
      Plet x (esubst v e e') P
   | Pexp e' => Pexp (esubst v e e')
   | Peq _ e1 e2 => Peq (esubst v e e1) (esubst v e e2)
   | Ple e1 e2 => Ple (esubst v e e1) (esubst v e e2)
   | Plt e1 e2 => Plt (esubst v e e1) (esubst v e e2)
  end.

  Fixpoint psubst_para (p:pred) s : pred :=
  match p with 
   | Ptrue => Ptrue
   | Pfalse => Pfalse
   | Pnot p' => Pnot (psubst_para p' s)
   | Pand p1 p2 => Pand (psubst_para p1 s) (psubst_para p2 s)
   | Por p1 p2 => Por (psubst_para p1 s) (psubst_para p2 s)
   | Pimplies p1 p2 => Pimplies (psubst_para p1 s) (psubst_para p2 s)
   | Piff p1 p2 => Piff (psubst_para p1 s) (psubst_para p2 s)
   | Pif c pt pf => Pif (esubst_para s c) (psubst_para pt s) (psubst_para pf s)
   | Pforall _ x P => 
     Pforall x (psubst_para P (remove_assoc (VarLogic x) s))
   | Pexists _ x P => 
     Pexists x (psubst_para P (remove_assoc (VarLogic x) s))
   | Plet t x e' P => 
      Plet x (esubst_para s e') (psubst_para P (remove_assoc (VarLogic x) s))
   | Pexp e' => Pexp (esubst_para s e')
   | Peq _ e1 e2 => Peq (esubst_para s e1) (esubst_para s e2)
   | Ple e1 e2 => Ple (esubst_para s e1) (esubst_para s e2)
   | Plt e1 e2 => Plt (esubst_para s e1) (esubst_para s e2)
  end.

 Lemma peval_eq_assoc : forall k (m1 m2:Mem.t k) p (l1 l2:lmem k),
  (forall t' (x:Var.var t'), Vset.mem x (pfv p) -> assoc x l1 = assoc x l2) ->
  (peval m1 m2 l1 p <-> peval m1 m2 l2 p).
 Proof.
  induction p; simpl; intros; try tauto.
  rewrite (IHp l1 l2); tauto.
  rewrite (IHp1 l1 l2), (IHp2 l1 l2); try tauto; intros; apply H;
   unfold pfv; simpl; rewrite pfv_rec_union; auto with set.
  rewrite (IHp1 l1 l2), (IHp2 l1 l2); try tauto; intros; apply H;
   unfold pfv; simpl; rewrite pfv_rec_union; auto with set.
  rewrite (IHp1 l1 l2), (IHp2 l1 l2); try tauto; intros; apply H;
   unfold pfv; simpl; rewrite pfv_rec_union; auto with set.
  rewrite (IHp1 l1 l2), (IHp2 l1 l2); try tauto; intros; apply H;
   unfold pfv; simpl; rewrite pfv_rec_union; auto with set.
  (* if *)
  rewrite eeval_eq_assoc with (l2:= l2).
  destruct (eeval m1 m2 l2 e).
  apply IHp1; intros.
  apply H; unfold pfv; simpl; rewrite !pfv_rec_union; auto with set.
  apply IHp2; intros.
  apply H; unfold pfv; simpl; rewrite !pfv_rec_union; auto with set.
  intros; apply H; unfold pfv; simpl; rewrite !pfv_rec_union; auto with set.
  (* forall *)
  split; intros.
  rewrite IHp with (l2:={| t := t0; var := v; val := x |} :: l1); trivial.
  intros; assoc_case; symmetry; assoc_case.
  apply H; unfold pfv; simpl.
  rewrite VsetP.remove_spec; split;
   [trivial | intros Heq; revert H2; inversion Heq].
  rewrite veqb_refl; discriminate.
  rewrite IHp with (l2:={| t := t0; var := v; val := x |} :: l2); trivial.
  intros; assoc_case; symmetry; assoc_case.
  symmetry; apply H; unfold pfv; simpl.
  rewrite VsetP.remove_spec; split;
   [trivial | intros Heq; revert H2; inversion Heq].
  rewrite veqb_refl; discriminate.
  (* exists *)
  split; intros (x,Hx); exists x.
  rewrite IHp with (l2:={| t := t0; var := v; val := x |} :: l1); trivial.
  intros; assoc_case; symmetry; assoc_case.
  apply H; unfold pfv; simpl.
  rewrite VsetP.remove_spec; split;
   [trivial | intros Heq; revert H2; inversion Heq].
  rewrite veqb_refl; discriminate.
  rewrite IHp with (l2:={| t := t0; var := v; val := x |} :: l2); trivial.
  intros; assoc_case; symmetry; assoc_case.
  symmetry; apply H; unfold pfv; simpl.
  rewrite VsetP.remove_spec; split;
   [trivial | intros Heq; revert H2; inversion Heq].
  rewrite veqb_refl; discriminate.
  (* let *)
  rewrite eeval_eq_assoc with (l2:= l2).
  apply IHp; intros; assoc_case; symmetry; assoc_case.
  symmetry; apply H; unfold pfv; simpl.
  rewrite VsetP.union_spec; right.
  rewrite VsetP.remove_spec; split;
   [trivial | intros Heq; revert H2; inversion Heq].
  rewrite veqb_refl; discriminate.
  intros; apply H; unfold pfv; simpl; auto with set.
  (* Pexp *)   
  rewrite eeval_eq_assoc with (l2 := l2);[ tauto | ].
  intros; apply H; trivial.
  (* Peq *)
  rewrite (eeval_eq_assoc m1 m2 e) with (l2 := l2).
  rewrite (eeval_eq_assoc m1 m2 e0) with (l2 := l2);[ tauto | ].
  intros; apply H; unfold pfv; simpl; rewrite lfv_rec_union; auto with set.
  intros; apply H; unfold pfv; simpl; rewrite lfv_rec_union; auto with set.
  (* Ple *)
  rewrite (eeval_eq_assoc m1 m2 e) with (l2 := l2).
  rewrite (eeval_eq_assoc m1 m2 e0) with (l2 := l2);[ tauto | ].
  intros; apply H; unfold pfv; simpl; rewrite lfv_rec_union; auto with set.
  intros; apply H; unfold pfv; simpl; rewrite lfv_rec_union; auto with set.
  (* Plt *)
  rewrite (eeval_eq_assoc m1 m2 e) with (l2 := l2).
  rewrite (eeval_eq_assoc m1 m2 e0) with (l2 := l2);[ tauto | ].
  intros; apply H; unfold pfv; simpl; rewrite lfv_rec_union; auto with set.
  intros; apply H; unfold pfv; simpl; rewrite lfv_rec_union; auto with set.
 Qed.

 (** Substitution Lemma for relational predicates *)
 Lemma psubst_correct : forall k (m1 m2 : Mem.t k) t (v:lvar t) (e:Exp t)
  (p:pred) (l:lmem k), 
  Vset.disjoint (pbind p) (lfv e) ->
  ((peval m1 m2 l (psubst p v e) ) <->  
   peval (mem_upd side_left m1 m2 l v e) 
   (mem_upd side_right m1 m2 l v e) (lmem_upd m1 m2 l v e) p).
 Proof.
  intros k m1 m2 t v e; induction p; simpl in *; intros l Hc; try tauto.
  rewrite IHp; tauto.
  rewrite IHp1, IHp2; try tauto;
   apply VsetP.disjoint_subset_l with (2:=Hc); 
   rewrite pbind_Pand; auto with set.
  rewrite IHp1, IHp2; try tauto;
   apply VsetP.disjoint_subset_l with (2:=Hc); 
   rewrite pbind_Por; auto with set.
  rewrite IHp1, IHp2; try tauto;
   apply VsetP.disjoint_subset_l with (2:=Hc); 
   rewrite pbind_Pimplies; auto with set.
  rewrite IHp1, IHp2; try tauto;
   apply VsetP.disjoint_subset_l with (2:= Hc); rewrite pbind_Piff; auto with set.
  (* if *)
  rewrite esubst_correct.
  match goal with |- (if ?b then _ else _) <-> _ => destruct b end.
  apply IHp1; apply VsetP.disjoint_subset_l with (2:=Hc); 
   rewrite pbind_Pif; auto with set.
  apply IHp2; apply VsetP.disjoint_subset_l with (2:= Hc); 
   rewrite pbind_Pif; auto with set.
  apply VsetP.disjoint_sym.
  apply VsetP.disjoint_subset_l with (2:= Hc); rewrite pbind_Pif; auto with set.
  (* forall *)
  split; intros.
  revert H; generalize (lvar_eqb_spec_dep (VarLogic v0) v).
  case_eq (lvar_eqb (VarLogic v0) v); simpl; intros.
  inversion H0; subst. 
  apply T.inj_pair2 in H5; subst; simpl.
  rewrite (@peval_eq_assoc k m1 m2 p ) with 
   (l2:={| t := t; var := v0; val := x |} :: l); trivial.
  intros; symmetry; apply assoc_double.
  rewrite peval_eq_assoc with 
   (l2:= lmem_upd m1 m2 ({| t := t0; var := v0; val := x |} :: l) v e).
  rewrite <- mem_upd_assoc with (v0:= v0) (a:=x).
  rewrite <- mem_upd_assoc with (side:= side_right) (v0:= v0) (a:=x).
  rewrite <- IHp; auto.
  apply VsetP.disjoint_subset_l with (2:=Hc);
   rewrite pbind_Pforall; auto with set.
  apply VsetP.disjoint_mem_not_mem with (1:=Hc);
   rewrite pbind_Pforall; auto with set.
  apply VsetP.disjoint_mem_not_mem with (1:=Hc); 
   rewrite pbind_Pforall; auto with set.
  intros; destruct v; simpl; trivial.
  rewrite assoc_comm.
  rewrite <- eeval_assoc; trivial.
  apply VsetP.disjoint_mem_not_mem with (1:=Hc); 
   rewrite pbind_Pforall; auto with set.
  exact H.   
  revert H; generalize (lvar_eqb_spec_dep (VarLogic v0) v).
  case_eq (lvar_eqb (VarLogic v0) v); simpl; intros.
  inversion H0; subst. 
  apply T.inj_pair2 in H5; subst; simpl.
  assert (W:= H1 x).
  rewrite (@peval_eq_assoc k m1 m2 p ) with 
   (l2:={| t := t; var := v0; val := x |} :: l) in W; trivial.
  intros; symmetry; apply assoc_double.
  assert (W:= H1 x).
  rewrite IHp.
  rewrite mem_upd_assoc with (v0:= v0) (a:=x).
  rewrite mem_upd_assoc with (side:= side_right) (v0:= v0) (a:=x).
  rewrite peval_eq_assoc with 
   (l2:= lmem_upd m1 m2 ({| t := t0; var := v0; val := x |} :: l) v e) in W;
   trivial.
  intros; destruct v; simpl; trivial.
  rewrite assoc_comm.
  rewrite <- eeval_assoc; trivial.
  apply VsetP.disjoint_mem_not_mem with (1:= Hc); 
   rewrite pbind_Pforall; auto with set.
  exact H.  
  apply VsetP.disjoint_mem_not_mem with (1:= Hc); 
   rewrite pbind_Pforall; auto with set.
  apply VsetP.disjoint_mem_not_mem with (1:= Hc); 
   rewrite pbind_Pforall; auto with set.
  apply VsetP.disjoint_subset_l with (2:= Hc); 
   rewrite pbind_Pforall; auto with set.
  (* exists *)
  split; intros (x, H); exists x.
  revert H; generalize (lvar_eqb_spec_dep (VarLogic v0) v).
  case_eq (lvar_eqb (VarLogic v0) v); simpl; intros.
  inversion H0; subst. 
  apply T.inj_pair2 in H5; subst; simpl.
  rewrite (@peval_eq_assoc k m1 m2 p ) with 
   (l2:={| t := t; var := v0; val := x |} :: l); trivial.
  intros; symmetry; apply assoc_double.
  rewrite peval_eq_assoc with 
   (l2:= lmem_upd m1 m2 ({| t := t0; var := v0; val := x |} :: l) v e).
  rewrite <- mem_upd_assoc with (v0:= v0) (a:=x).
  rewrite <- mem_upd_assoc with (side:= side_right) (v0:= v0) (a:=x).
  rewrite <- IHp; auto.
  apply VsetP.disjoint_subset_l with (2:= Hc); 
   rewrite pbind_Pexists; auto with set.
  apply VsetP.disjoint_mem_not_mem with (1:= Hc); 
   rewrite pbind_Pexists; auto with set.
  apply VsetP.disjoint_mem_not_mem with (1:= Hc); 
   rewrite pbind_Pexists; auto with set.
  intros; destruct v; simpl; trivial.
  rewrite assoc_comm.
  rewrite <- eeval_assoc; trivial.
  apply VsetP.disjoint_mem_not_mem with (1:= Hc); 
   rewrite pbind_Pexists; auto with set.
  exact H.   
  revert H; generalize (lvar_eqb_spec_dep (VarLogic v0) v).
  case_eq (lvar_eqb (VarLogic v0) v); simpl; intros.
  inversion H0; subst. 
  apply T.inj_pair2 in H5; subst; simpl.
  rewrite (@peval_eq_assoc k m1 m2 p ) with 
   (l2:={| t := t; var := v0; val := x |} :: l) in H1; trivial.
  intros; symmetry; apply assoc_double.
  rewrite IHp.
  rewrite mem_upd_assoc with (v0:= v0) (a:=x).
  rewrite mem_upd_assoc with (side:= side_right) (v0:= v0) (a:=x).
  rewrite peval_eq_assoc with 
   (l2:= lmem_upd m1 m2 ({| t := t0; var := v0; val := x |} :: l) v e) in H1; trivial.
  intros; destruct v; simpl; trivial.
  rewrite assoc_comm.
  rewrite <- eeval_assoc; trivial.
  apply VsetP.disjoint_mem_not_mem with (1:=Hc);
   rewrite pbind_Pexists; auto with set.
  exact H.  
  apply VsetP.disjoint_mem_not_mem with (1:=Hc);
   rewrite pbind_Pexists; auto with set.
  apply VsetP.disjoint_mem_not_mem with (1:=Hc);
   rewrite pbind_Pexists; auto with set.
  apply VsetP.disjoint_subset_l with (2:=Hc); 
   rewrite pbind_Pexists; auto with set.

  (* let *)
  rewrite <- esubst_correct.
  generalize (lvar_eqb_spec_dep (VarLogic v0) v).
  case_eq (lvar_eqb (VarLogic v0) v); simpl; intros.
  inversion H0; subst. 
  apply T.inj_pair2 in H4; subst; simpl.
  apply peval_eq_assoc.
  intros; apply assoc_double.
  rewrite <- mem_upd_assoc with (v0:= v0) (a:=eeval m1 m2 l (esubst v e e0)).
  rewrite <- mem_upd_assoc with 
   (side:= side_right) (v0:= v0) (a:=eeval m1 m2 l (esubst v e e0)).
  rewrite IHp.
  apply peval_eq_assoc.
  intros; destruct v; simpl; trivial.
  rewrite assoc_comm.
  rewrite <- eeval_assoc; trivial.
  apply VsetP.disjoint_mem_not_mem with (1:=Hc);
   rewrite pbind_Plet; auto with set.
  rewrite veqb_sym; exact H.
  apply VsetP.disjoint_subset_l with (2:=Hc);
   rewrite pbind_Plet; auto with set.
  apply VsetP.disjoint_mem_not_mem with (1:=Hc);
   rewrite pbind_Plet; auto with set.
  apply VsetP.disjoint_mem_not_mem with (1:=Hc);
   rewrite pbind_Plet; auto with set.
  apply VsetP.disjoint_sym.
  apply VsetP.disjoint_subset_l with (2:=Hc); rewrite pbind_Plet; auto with set.
  (* Pexp *)
  rewrite esubst_correct;[ tauto | rewrite VsetP.disjoint_sym; trivial].
  (* Peq *)
  rewrite <- !esubst_correct; try tauto; apply VsetP.disjoint_sym;
   apply VsetP.disjoint_subset_l with (2:= Hc); rewrite pbind_Peq; auto with set.
  (* Ple *)
  rewrite <- !esubst_correct; try tauto; apply VsetP.disjoint_sym;
   apply VsetP.disjoint_subset_l with (2:= Hc); rewrite pbind_Ple; auto with set.
  (* Plt *)
  rewrite <- !esubst_correct; try tauto; apply VsetP.disjoint_sym;
   apply VsetP.disjoint_subset_l with (2:= Hc); rewrite pbind_Plt; auto with set.
 Qed.

 Lemma psubst_para_correct : forall k (m1 m2 : Mem.t k) (p:pred) s (l:lmem k), 
  Vset.disjoint (pbind p) (sfv s) ->
  ((peval m1 m2 l (psubst_para p s) ) <->  
   peval (mem_upd_para1 m1 m2 l s) (mem_upd_para2 m1 m2 l s)
         (mem_upd_paral m1 m2 l s) p).
 Proof.
  intros k m1 m2; induction p; simpl in *; intros s l Hc; try tauto.
  rewrite IHp; tauto.
  rewrite IHp1, IHp2; try tauto;
   apply VsetP.disjoint_subset_l with (2:=Hc); 
   rewrite pbind_Pand; auto with set.
  rewrite IHp1, IHp2; try tauto;
   apply VsetP.disjoint_subset_l with (2:=Hc); 
   rewrite pbind_Por; auto with set.
  rewrite IHp1, IHp2; try tauto;
   apply VsetP.disjoint_subset_l with (2:=Hc); 
   rewrite pbind_Pimplies; auto with set.
  rewrite IHp1, IHp2; try tauto;
   apply VsetP.disjoint_subset_l with (2:= Hc); rewrite pbind_Piff; auto with set.
  (* if *)
  rewrite esubst_para_correct.
  match goal with |- (if ?b then _ else _) <-> _ => destruct b end.
  apply IHp1; apply VsetP.disjoint_subset_l with (2:=Hc); 
   rewrite pbind_Pif; auto with set.
  apply IHp2; apply VsetP.disjoint_subset_l with (2:= Hc); 
   rewrite pbind_Pif; auto with set.
  apply VsetP.disjoint_sym.
  apply VsetP.disjoint_subset_l with (2:= Hc); rewrite pbind_Pif; auto with set.
  (* forall *)
  split; intros. 
  destruct (mem_upd_para_notmem m1 m2 l v x s) as (H1,(H2,H3)).
  apply VsetP.disjoint_mem_not_mem with (1:=Hc);
   rewrite pbind_Pforall; auto with set.
  rewrite <- H1, <- H2.
  rewrite peval_eq_assoc with 
   (l2:=  (mem_upd_paral m1 m2 ({| t := t0; var := v; val := x |} :: l)
            (remove_assoc (VarLogic v) s)));[ | auto].
  rewrite <- IHp;trivial.
  apply disjoint_subset with (3:=Hc).
   rewrite pbind_Pforall; auto with set.
   apply sfv_remove_assoc_subset.
  destruct (mem_upd_para_notmem m1 m2 l v x s) as (H1,(H2,H3)).
  apply VsetP.disjoint_mem_not_mem with (1:=Hc);
   rewrite pbind_Pforall; auto with set.
  generalize (H x).
  rewrite <- H1, <- H2.
  rewrite peval_eq_assoc with 
   (l2:=  (mem_upd_paral m1 m2 ({| t := t0; var := v; val := x |} :: l)
            (remove_assoc (VarLogic v) s)));[ | auto].
  rewrite <- IHp;trivial.
  apply disjoint_subset with (3:=Hc).
   rewrite pbind_Pforall; auto with set.
   apply sfv_remove_assoc_subset.
  (* exists *)
  split; intros (x, H); exists x.
  destruct (mem_upd_para_notmem m1 m2 l v x s) as (H1,(H2,H3)).
  apply VsetP.disjoint_mem_not_mem with (1:=Hc);
   rewrite pbind_Pexists; auto with set.
  rewrite <- H1, <- H2.
  rewrite peval_eq_assoc with 
   (l2:=  (mem_upd_paral m1 m2 ({| t := t0; var := v; val := x |} :: l)
            (remove_assoc (VarLogic v) s)));[ | auto].
  rewrite <- IHp;trivial.
  apply disjoint_subset with (3:=Hc).
   rewrite pbind_Pexists; auto with set.
   apply sfv_remove_assoc_subset.
  destruct (mem_upd_para_notmem m1 m2 l v x s) as (H1,(H2,H3)).
  apply VsetP.disjoint_mem_not_mem with (1:=Hc);
   rewrite pbind_Pexists; auto with set.
  generalize H.
  rewrite <- H1, <- H2.
  rewrite peval_eq_assoc with 
   (l2:=  (mem_upd_paral m1 m2 ({| t := t0; var := v; val := x |} :: l)
            (remove_assoc (VarLogic v) s)));[ | auto].
  rewrite <- IHp;trivial.
  apply disjoint_subset with (3:=Hc).
  rewrite pbind_Pexists; auto with set.
  apply sfv_remove_assoc_subset.
  (* let *)
  rewrite <- esubst_para_correct.
  rewrite IHp.
  destruct (mem_upd_para_notmem m1 m2 l v (eeval m1 m2 l (esubst_para s e)) s) as (H1,(H2,H3)).
  apply VsetP.disjoint_mem_not_mem with (1:=Hc);
   rewrite pbind_Plet; auto with set.
  rewrite H1, H2.
  apply peval_eq_assoc;auto.
  apply disjoint_subset with (3:=Hc).
   rewrite pbind_Plet; auto with set.
   apply sfv_remove_assoc_subset.
  apply VsetP.disjoint_sym.
  apply VsetP.disjoint_subset_l with (2:=Hc); rewrite pbind_Plet; auto with set.
  (* Pexp *)
  rewrite esubst_para_correct;[ tauto | rewrite VsetP.disjoint_sym; trivial].
  (* Peq *)
  rewrite <- !esubst_para_correct; try tauto; apply VsetP.disjoint_sym;
   apply VsetP.disjoint_subset_l with (2:= Hc); rewrite pbind_Peq; auto with set.
  (* Ple *)
  rewrite <- !esubst_para_correct; try tauto; apply VsetP.disjoint_sym;
   apply VsetP.disjoint_subset_l with (2:= Hc); rewrite pbind_Ple; auto with set.
  (* Plt *)
  rewrite <- !esubst_para_correct; try tauto; apply VsetP.disjoint_sym;
   apply VsetP.disjoint_subset_l with (2:= Hc); rewrite pbind_Plt; auto with set.
 Qed.

 (** Set of variables on which a relational predicate depends *)
 Fixpoint pdepend_rec XX (p:pred) : Vset.t * Vset.t :=
  match p with
   | Ptrue | Pfalse => XX
   | Pnot p => pdepend_rec XX p
   | Pand p1 p2 => pdepend_rec (pdepend_rec XX p1) p2
   | Por p1 p2 => pdepend_rec (pdepend_rec XX p1) p2
   | Pimplies p1 p2 => pdepend_rec (pdepend_rec XX p1) p2
   | Piff p1 p2 => pdepend_rec (pdepend_rec XX p1) p2
   | Pif e p1 p2 => pdepend_rec (pdepend_rec (ldepend_rec XX e) p1) p2
   | Pforall t x p => pdepend_rec XX p
   | Pexists t x p => pdepend_rec XX p
   | Plet t x e p => pdepend_rec (ldepend_rec XX e) p
   | Pexp e => ldepend_rec XX e
   | Peq t e1 e2 => ldepend_rec (ldepend_rec XX e1) e2
   | Ple e1 e2 => ldepend_rec (ldepend_rec XX e1) e2
   | Plt e1 e2 => ldepend_rec (ldepend_rec XX e1) e2
  end.

 Definition pdepend := pdepend_rec (Vset.empty, Vset.empty).

 Lemma pdepend_rec_union : forall p XX, 
  fst (pdepend_rec XX p) [=] Vset.union (fst (pdepend p)) (fst XX) /\
  snd (pdepend_rec XX p) [=] Vset.union (snd (pdepend p)) (snd XX).
 Proof.
  induction p; simpl; intros; auto with set;
   try (
    unfold pdepend; destruct (IHp2 (pdepend_rec XX p1)); destruct (IHp1 XX);
     destruct (IHp2 (pdepend_rec (Vset.empty, Vset.empty) p1));
      rewrite H, H0, H1, H2, H3, H4, <- !VsetP.union_assoc; auto with set).
  unfold pdepend; simpl; 
   destruct (IHp2 (pdepend_rec (ldepend_rec XX e) p1)); 
   destruct (IHp1 (ldepend_rec XX e));
   destruct (IHp2 (pdepend_rec (ldepend e) p1)); destruct (ldepend_rec_union e XX).
  destruct (IHp1 (ldepend e)).
  unfold ldepend in H3, H4, H7, H8.
  rewrite H, H0, H1, H2, H3, H4, H5, H6, H7, H8, <- !VsetP.union_assoc.
  auto with set.
  unfold pdepend; simpl.
  destruct (IHp (ldepend_rec XX e)); 
  destruct (IHp (ldepend e)); 
  destruct (ldepend_rec_union e XX).
  unfold ldepend in H1, H2; rewrite H, H0, H1, H2, H3, H4, <- !VsetP.union_assoc.
  auto with set.
  apply ldepend_rec_union.
  unfold pdepend; simpl. 
  destruct (ldepend_rec_union e XX); 
  destruct (ldepend_rec_union e0 (ldepend_rec XX e)).
  destruct (ldepend_rec_union e0 (ldepend e)).
  rewrite H1, H2, H, H0, H3, H4, <- !VsetP.union_assoc; auto with set.
  unfold pdepend; simpl. 
  destruct (ldepend_rec_union e XX); 
  destruct (ldepend_rec_union e0 (ldepend_rec XX e)).
  destruct (ldepend_rec_union e0 (ldepend e)).
  rewrite H1, H2, H, H0, H3, H4, <- !VsetP.union_assoc; auto with set.
  unfold pdepend; simpl. 
  destruct (ldepend_rec_union e XX); 
  destruct (ldepend_rec_union e0 (ldepend_rec XX e)).
  destruct (ldepend_rec_union e0 (ldepend e)).
  rewrite H1, H2, H, H0, H3, H4, <- !VsetP.union_assoc; auto with set.
 Qed.

 Lemma pdepend_correct_aux : forall k (m1 m1' m2 m2':Mem.t k) p l,
  m1 =={fst (pdepend p)} m1' ->
  m2 =={snd (pdepend p)} m2' ->
  (peval m1 m2 l p <-> peval m1' m2' l p).
 Proof.
  induction p; simpl; intros; try tauto;
   try (unfold pdepend in H, H0; simpl in H, H0;
    destruct (pdepend_rec_union p2 (pdepend p1));
     rewrite H1 in H; rewrite H2 in H0;
      rewrite IHp1, IHp2; try tauto; eapply req_mem_weaken; eauto with set).
  rewrite IHp; trivial; tauto.
  unfold pdepend in H, H0; simpl in H, H0;
   destruct (pdepend_rec_union p2 (pdepend_rec (ldepend e) p1)).
  rewrite H1 in H; rewrite H2 in H0; clear H1 H2.
  destruct (pdepend_rec_union p1 (ldepend e)).
  rewrite H1 in H; rewrite H2 in H0; clear H1 H2.
  match goal with |- (if ?e1 then _ else _) <-> if ?e2 then _ else _ => 
   replace e1 with e2;[destruct e2 | ] end.
  apply IHp1; eapply req_mem_weaken; eauto with set.
  apply IHp2; eapply req_mem_weaken; eauto with set.
  apply ldepend_rec_correct with (Vset.empty,Vset.empty); 
   eapply req_mem_weaken; eauto with set.
  unfold pdepend in H, H0; simpl in H, H0; split; intros.
  rewrite <- IHp; auto.
  rewrite IHp; auto.
  unfold pdepend in H, H0; simpl in H, H0; split; intros (x, H1); exists x.
  rewrite <- IHp; auto.
  rewrite IHp; auto.
  unfold pdepend in H, H0; simpl in H, H0; intros.
  destruct (pdepend_rec_union p (ldepend e)).
  rewrite H1 in H; rewrite H2 in H0.
  replace (eeval m1 m2 l e) with (eeval m1' m2' l e).
  apply IHp; eapply req_mem_weaken; eauto with set.
  apply ldepend_rec_correct with 
   (XX:= (Vset.empty, Vset.empty)); eapply req_mem_weaken; eauto with set.
  rewrite <- eq_iff_eq_true. 
  apply (@ldepend_rec_correct k m1 m1' m2 m2' _ e (Vset.empty, Vset.empty)); 
   eapply req_mem_weaken; eauto with set.
  unfold pdepend in H, H0; simpl in H, H0.
  destruct (ldepend_rec_union e0 (ldepend e)).
  rewrite H1 in H; rewrite H2 in H0.
  rewrite (@ldepend_rec_correct k m1 m1' m2 m2' _ e (Vset.empty, Vset.empty)),
   (@ldepend_rec_correct k m1 m1' m2 m2' _ e0 (Vset.empty, Vset.empty)); 
   try tauto; eapply req_mem_weaken; eauto with set.
  unfold pdepend in H, H0; simpl in H, H0.
  destruct (ldepend_rec_union e0 (ldepend e)).
  rewrite H1 in H; rewrite H2 in H0.
  rewrite (@ldepend_rec_correct k m1 m1' m2 m2' _ e (Vset.empty, Vset.empty)),
   (@ldepend_rec_correct k m1 m1' m2 m2' _ e0 (Vset.empty, Vset.empty)); 
   try tauto; eapply req_mem_weaken; eauto with set.
  unfold pdepend in H, H0; simpl in H, H0.
  destruct (ldepend_rec_union e0 (ldepend e)).
  rewrite H1 in H; rewrite H2 in H0.
  rewrite (@ldepend_rec_correct k m1 m1' m2 m2' _ e (Vset.empty, Vset.empty)),
   (@ldepend_rec_correct k m1 m1' m2 m2' _ e0 (Vset.empty, Vset.empty)); 
   try tauto; eapply req_mem_weaken; eauto with set.
 Qed.

 Lemma pdepend_correct : forall p, 
  depend_only_rel (ipred p) (fst (pdepend p)) (snd (pdepend p)).
 Proof.
  red; unfold ipred; intros.
  rewrite <- (@pdepend_correct_aux k m1 m1' m2 m2' p nil); trivial.
 Qed.

 Lemma lbind_esubst : forall t (e:Exp t) t' (x:lvar t') (e':Exp t'),
  lbind (esubst x e' e) [<=] Vset.union (lbind e) (lbind e').
 Proof.
  induction e using Exp_ind2 with 
   (Pl :=
    fun lt la => 
     forall t' (x:lvar t') (e':Exp t') X,
      dfold_left lbind_rec (dmap Exp (esubst x e') la) X [<=] 
      Vset.union (dfold_left lbind_rec la (Vset.union X (lbind e'))) (lbind e'));
   intros; simpl.

  auto with set.

  destruct (lvar_eqb v x).
  destruct (T.eq_dec t' t0).
  destruct e.
  auto with set.
  auto with set.
  auto with set.
  
  unfold lbind;  simpl.
  rewrite IHe.     
  destruct (lbind_rec_union_and).
  rewrite H0, VsetP.union_assoc, VsetP.union_idem; auto with set.

  rewrite lbind_Eexists, lbind_Eexists.
  rewrite <- VsetP.add_union_comm; apply VsetP.subset_add_ctxt.
  rewrite <- (VsetP.union_idem (lbind e')).
  transitivity (Vset.union
   (Vset.union (lbind e1) (lbind e')) (Vset.union (lbind e2) (lbind e'))).
  destruct (lvar_eqb (VarLogic v) x);
   apply VsetP.subset_union_ctxt; auto with set.
  rewrite <- VsetP.union_assoc, <- VsetP.union_assoc.
  apply VsetP.subset_union_ctxt.
  rewrite VsetP.union_assoc, VsetP.union_assoc.
  apply VsetP.subset_union_ctxt.
  auto with set.
  rewrite VsetP.union_sym; auto with set.
  auto with set.

  rewrite lbind_Eforall, lbind_Eforall.
  rewrite <- VsetP.add_union_comm; apply VsetP.subset_add_ctxt.
  rewrite <- (VsetP.union_idem (lbind e')).
  transitivity (Vset.union
   (Vset.union (lbind e1) (lbind e')) (Vset.union (lbind e2) (lbind e'))).
  destruct (lvar_eqb (VarLogic v) x);
   apply VsetP.subset_union_ctxt; auto with set.
  rewrite <- VsetP.union_assoc, <- VsetP.union_assoc.
  apply VsetP.subset_union_ctxt.
  rewrite VsetP.union_assoc, VsetP.union_assoc.
  apply VsetP.subset_union_ctxt.
  auto with set.
  rewrite VsetP.union_sym; auto with set.
  auto with set.

  rewrite lbind_Efind, lbind_Efind.
  rewrite <- VsetP.add_union_comm; apply VsetP.subset_add_ctxt.
  rewrite <- (VsetP.union_idem (lbind e')).
  transitivity (Vset.union
   (Vset.union (lbind e1) (lbind e')) (Vset.union (lbind e2) (lbind e'))).
  destruct (lvar_eqb (VarLogic v) x);
   apply VsetP.subset_union_ctxt; auto with set.
  rewrite <- VsetP.union_assoc, <- VsetP.union_assoc.
  apply VsetP.subset_union_ctxt.
  rewrite VsetP.union_assoc, VsetP.union_assoc.
  apply VsetP.subset_union_ctxt.
  auto with set.
  rewrite VsetP.union_sym; auto with set.
  auto with set.

  auto with set.

  rewrite IHe0; clear IHe0.
  apply VsetP.subset_union_ctxt; [ | auto with set].
  destruct lbind_rec_union_and.
  rewrite H0, (H0 _ le (lbind_rec _ _)).
  apply VsetP.subset_union_ctxt.
  auto with set.

  rewrite lbind_rec_union, lbind_rec_union.
  rewrite VsetP.union_sym.
  rewrite <- VsetP.union_assoc.
  rewrite (VsetP.union_sym X).
  rewrite <- VsetP.union_assoc.
  apply VsetP.subset_union_ctxt; [ | auto with set].
  
  rewrite <- (VsetP.union_idem (lbind e')) at 2.
  rewrite <- VsetP.union_assoc, VsetP.union_sym.
  apply VsetP.subset_union_ctxt; auto with set.
 Qed.

 Lemma pbind_psubst : forall t (x:lvar t) p e,
  pbind (psubst p x e) [<=] Vset.union (pbind p) (lbind e).
 Proof.
  induction p; intros; simpl.
  auto with set.
  auto with set.

  rewrite pbind_Pnot, pbind_Pnot; auto with set.

  rewrite pbind_Pand, pbind_Pand; apply VsetP.union_subset.     
  rewrite IHp1; apply VsetP.subset_union_ctxt; auto with set.
  rewrite IHp2; apply VsetP.subset_union_ctxt; auto with set.

  rewrite pbind_Por, pbind_Por; apply VsetP.union_subset.     
  rewrite IHp1; apply VsetP.subset_union_ctxt; auto with set.
  rewrite IHp2; apply VsetP.subset_union_ctxt; auto with set.

  rewrite pbind_Pimplies, pbind_Pimplies; apply VsetP.union_subset.     
  rewrite IHp1; apply VsetP.subset_union_ctxt; auto with set.
  rewrite IHp2; apply VsetP.subset_union_ctxt; auto with set.

  rewrite pbind_Piff, pbind_Piff; apply VsetP.union_subset.     
  rewrite IHp1; apply VsetP.subset_union_ctxt; auto with set.
  rewrite IHp2; apply VsetP.subset_union_ctxt; auto with set.

  rewrite pbind_Pif, pbind_Pif; apply VsetP.union_subset.
  rewrite lbind_esubst; apply VsetP.subset_union_ctxt; auto with set.
  rewrite <- (VsetP.union_idem (lbind e0)).
  rewrite <- VsetP.union_assoc.
  rewrite <- (VsetP.union_sym (lbind e0)). 
  rewrite VsetP.union_assoc.
  rewrite VsetP.union_assoc.
  rewrite <- VsetP.union_assoc.
  rewrite <- VsetP.union_assoc.
  apply VsetP.subset_union_ctxt.
  rewrite IHp1.
  rewrite VsetP.union_sym.
  apply VsetP.subset_union_ctxt; auto with set.
  trivial.
  
  rewrite pbind_Pforall, pbind_Pforall.
  rewrite <- VsetP.add_union_comm; apply VsetP.subset_add_ctxt.
  destruct (lvar_eqb (VarLogic v) x); auto with set.
  
  rewrite pbind_Pexists, pbind_Pexists.
  rewrite <- VsetP.add_union_comm; apply VsetP.subset_add_ctxt.
  destruct (lvar_eqb (VarLogic v) x); auto with set.
  
  rewrite pbind_Plet, pbind_Plet.
  rewrite <- VsetP.add_union_comm; apply VsetP.subset_add_ctxt.
  rewrite (VsetP.union_sym (lbind e)), VsetP.union_assoc, VsetP.union_sym.
  destruct (lvar_eqb (VarLogic v) x); auto with set.
  apply VsetP.subset_union_ctxt; [auto with set | apply lbind_esubst].
  rewrite <- (VsetP.union_idem (lbind e0)).
  rewrite <- VsetP.union_assoc.
  rewrite <- VsetP.union_assoc.
  rewrite (VsetP.union_sym _ (lbind e0)).
  rewrite VsetP.union_assoc.
  rewrite <- VsetP.union_assoc.
  apply VsetP.subset_union_ctxt; [ | apply lbind_esubst].
  rewrite VsetP.union_sym; trivial.
  
  rewrite pbind_Pexp, pbind_Pexp, lbind_esubst; auto with set.
  
  rewrite pbind_Peq, pbind_Peq.
  rewrite <- (VsetP.union_idem (lbind e1)).
  rewrite <- VsetP.union_assoc.
  rewrite (VsetP.union_sym _ (lbind e1)).
  rewrite VsetP.union_assoc.
  rewrite <- VsetP.union_assoc.
  apply VsetP.subset_union_ctxt; [ | apply lbind_esubst].
  rewrite VsetP.union_sym.
  apply lbind_esubst.
  
  rewrite pbind_Ple, pbind_Ple.
  rewrite <- (VsetP.union_idem (lbind e1)).
  rewrite <- VsetP.union_assoc.
  rewrite (VsetP.union_sym _ (lbind e1)).
  rewrite VsetP.union_assoc.
  rewrite <- VsetP.union_assoc.
  apply VsetP.subset_union_ctxt; [ | apply lbind_esubst].
  rewrite VsetP.union_sym.
  apply lbind_esubst.
  
  rewrite pbind_Plt, pbind_Plt.
  rewrite <- (VsetP.union_idem (lbind e1)).
  rewrite <- VsetP.union_assoc.
  rewrite (VsetP.union_sym _ (lbind e1)).
  rewrite VsetP.union_assoc.
  rewrite <- VsetP.union_assoc.
  apply VsetP.subset_union_ctxt; [ | apply lbind_esubst].
  rewrite VsetP.union_sym.
  apply lbind_esubst.
 Qed. 

 Lemma ipred_true : iffMR (ipred Ptrue) trueR.
 Proof. 
  unfold iffMR, implMR; split; intros; auto. 
 Qed.

 Lemma ipred_false : iffMR (ipred Pfalse) falseR.
 Proof. 
  unfold iffMR, implMR; split; intros; auto. 
 Qed.

 Lemma ipred_pnot : forall P, iffMR (ipred (pnot P)) (~-(ipred P)).
 Proof. 
  destruct P; trivial; simpl.
  rewrite ipred_true, ipred_false; symmetry; apply notR_trueR.
  rewrite ipred_true, ipred_false; symmetry; apply notR_falseR.
  destruct P; trivial; simpl.
  unfold iffMR, implMR, ipred, notR; simpl; unfold not; split; intros; tauto.
 Qed.

 Lemma ipred_pand : forall P Q, iffMR (ipred (pand P Q)) ((ipred P) /-\ (ipred Q)).
 Proof.
  intros P Q; destruct P; simpl;
  try (rewrite ipred_true,andR_trueR_l; trivial);
  try (rewrite ipred_false, andR_falseR_l; trivial); destruct Q; trivial;
  try (rewrite ipred_true, andR_trueR_r; trivial);
  try (rewrite ipred_false, andR_falseR_r; trivial).
  Qed.

 (* TODO: Move this *)
 Lemma orR_trueR_l : forall P, iffMR (trueR \-/ P) trueR.
 Proof. 
  compute; split; intros; tauto. 
 Qed.

 Lemma orR_trueR_r : forall P, iffMR (P \-/ trueR) trueR.
 Proof. 
  compute; split; intros; tauto. 
 Qed.

 Lemma orR_falseR_l : forall P, iffMR (falseR \-/ P) P.
 Proof. 
  compute; split; intros; tauto. 
 Qed.

 Lemma orR_falseR_r : forall P, iffMR (P \-/ falseR) P.
 Proof. 
  compute; split; intros; tauto. 
 Qed.

 Lemma iffMR_impR_same : forall P, iffMR (P |-> P) trueR.
 Proof. 
  compute; split; intros; tauto. 
 Qed.

 Lemma iffMR_andR_impR : forall P1 P2 Q, 
  iffMR (P1 |-> (P2 |-> Q)) ((P1 /-\ P2) |-> Q).
 Proof. 
  compute; split; intros; tauto. 
 Qed.
 (***)

 Lemma ipred_por : forall P Q, iffMR (ipred (por P Q)) ((ipred P) \-/ (ipred Q)).
 Proof.
  intros P Q; destruct P; simpl;
  try (rewrite ipred_true,orR_trueR_l; trivial);
  try (rewrite ipred_false, orR_falseR_l; trivial); destruct Q; trivial;
  try (rewrite ipred_true, orR_trueR_r; trivial);
  try (rewrite ipred_false, orR_falseR_r; trivial).
 Qed.

 Opaque pred_eqb pnot.

 Lemma ipred_pimplies : forall P Q, iffMR (ipred (pimplies P Q)) 
  ((ipred P) |-> (ipred Q)).
 Proof.
  induction P; intros Q; simpl;
   match goal with 
    |- context [pred_eqb ?x ?y] =>
    generalize (pred_eqb_spec x y); case_eq (pred_eqb x y); intros Heq1 Heq2;
     [ rewrite <- Heq2,iffMR_impR_same; trivial | ]
   end;
   try (rewrite ipred_true,impR_trueR_l; trivial);
   try (rewrite ipred_false, impR_falseR_l; trivial);
   try (rewrite IHP1, IHP2, iffMR_andR_impR; trivial); destruct Q; trivial;
   try (rewrite ipred_true,impR_trueR_r; trivial);
   try (rewrite ipred_false, impR_falseR_r; trivial);
   rewrite ipred_pnot; trivial.
 Qed.

 Transparent pred_eqb pnot. 

 Lemma ipred_pexp : forall e, iffMR (ipred (pexp e)) (ipred (Pexp e)).
 Proof. 
  trivial. 
 Qed.

 Lemma ipred_pexp_left : forall e, 
  iffMR (ipred (pexp (e2E side_left e))) (EP1 e).
 Proof.
  intros; rewrite ipred_pexp.
  unfold iffMR, implMR, EP1, ipred; simpl; split; intros.
  rewrite e2E_correct in H; trivial.
  rewrite e2E_correct; trivial.
 Qed.

 Lemma ipred_pexp_right : forall e, 
  iffMR (ipred (pexp (e2E side_right e))) (EP2 e).
 Proof.
  intros; rewrite ipred_pexp.
  unfold iffMR, implMR, EP2, ipred; simpl; split; intros.
  rewrite e2E_correct in H; trivial.
  rewrite e2E_correct; trivial.
 Qed.

 Lemma ipred_peq : forall t (e1 e2:Exp t) k (m1 m2:Mem.t k), 
  ipred (peq e1 e2) m1 m2 <-> eeval m1 m2 nil e1 = eeval m1 m2 nil e2.
 Proof.
  unfold peq; intros.
  generalize (exp_eqb_spec e1 e2); destruct (exp_eqb e1 e2); 
   intros Heq; [| intuition].
  inversion Heq; clear Heq; subst. apply T.inj_pair2 in H1; subst. 
  unfold ipred; simpl; intuition.
 Qed.

 
 (** One-sided Weakest Precondition Calculus *)
 Section WP_CMD.

  Variable E : env.   
  Variable wp_i : bool -> I.instr -> pred -> option pred.

  Hypothesis wp_i_correct : forall side (i:I.instr) (Q Q':pred),
   wp_i side i Q = Some Q' ->
   lossless E [i] /\     
   forall k (m1 m2:Mem.t k), 
    ipred Q' m1 m2 ->
    range (fun m => (ipred Q) k (smem side m m1) (smem side m2 m)) 
          ( [[ [i] ]] E (smem side m1 m2)).

  Fixpoint wp side (c:cmd) (Q:pred) : pred * cmd :=
   match c with
    | nil => (Q, nil)
    | i :: c' => 
     match wp side c' Q with
      | (Q', c'') =>
       match c'' with
        | nil => 
         match wp_i side i Q' with
          | None => (Q', i :: nil)
          | Some Q'' => (Q'', nil)
         end
        | _ :: _ => (Q', i :: c'')
       end
     end
   end.

  Lemma wp_correct : forall side (c c':cmd) (Q Q':pred),
   wp side c Q = (Q', c') ->
   lossless E (skipn (length c') c) /\
   c' = firstn (length c') c /\ 
   forall  k (m1 m2 : Mem.t k), ipred Q' m1 m2 ->
    range (fun m => ipred Q (smem side m m1) (smem side m2 m))
    ( [[ skipn (length c') c ]] E (smem side m1 m2)).
  Proof.
   induction c; simpl; intros.
   injection H; clear H; intros; subst.
   split; [apply lossless_nil | split; intros; trivial].
   rewrite deno_nil; unfold range; simpl; intros f H1. 
   apply H1; destruct side; trivial.
   (* cons *)     
   revert H; case_eq (wp side c Q).
   intros p [ | i0 l0] Heq; apply IHc in Heq; trivial; destruct Heq as (Hl,(H,H0)).
   case_eq (wp_i side a p); intros.
   destruct (wp_i_correct H1) as (Hli, Hr).
   inversion H2; clear H2; subst; simpl in *; auto.
   split; [apply lossless_cons | split]; trivial.
   intros; rewrite deno_cons.
   apply range_Mlet with (1:= Hr _ _ _ H2); intros; auto.
   apply H0 in H3; destruct side; auto.
   inversion H2; clear H2; intros; subst; simpl; auto.
   intros H3; injection H3; clear H3; intros; subst.
   set (c1:= i0::l0) in *.
   revert Hl H H0; generalize c1; clear c1; intros.
   split; [ | split]; trivial.
   rewrite H at 1; trivial.
  Qed.
   
 End WP_CMD.

 (* WP : assign *)

 Definition wp_ass (side:bool) t (v:Var.var t) (e:E.expr t) Q := 
  psubst Q (if side then VarLeft v else VarRight v) (e2E side e).
 
 Definition wp_i_asgn (side:bool) (i:I.instr) (Q:pred) : option pred :=
  match i with 
   | I.Instr (I.Assign t v e) => Some (wp_ass side v e Q)
   | _ => None
  end.

 Definition wp_asgn := wp wp_i_asgn.

 Lemma wp_ass_correct : forall E side t (x:Var.var t) (e:E.expr t) Q, 
  forall k (m1 m2:Mem.t k),
  ipred (wp_ass side x e Q) m1 m2 ->
  range (fun m => ipred Q (smem side m m1) (smem side m2 m)) 
  ([[ [x<-e] ]] E (smem side m1 m2)).
 Proof.
  red; intros; rewrite deno_assign_elim.
  apply H0; unfold ipred, wp_ass in H.
  generalize H; rewrite psubst_correct.
  unfold smem; destruct side; simpl; rewrite e2E_correct; trivial.
  apply VsetP.disjoint_complete; intros; rewrite lfv_e2E; intros; discriminate.
 Qed.

 Lemma wp_i_asgn_correct : forall E side (i:I.instr) (Q Q':pred),
  wp_i_asgn side i Q = Some Q' ->
  lossless E [i] /\    
  forall k (m1 m2 : Mem.t k), 
   ipred Q' m1 m2 -> 
   range (fun m => ipred Q (smem side m m1) (smem side m2 m))
   ([[ [i] ]] E (smem side m1 m2)).
 Proof.
  intros E side; destruct i; simpl in *; intros; try discriminate.
  destruct b; simpl; [ inversion H; subst| discriminate].
  split;[apply lossless_assign | apply wp_ass_correct]; trivial.
 Qed.

 Lemma wp_asgn_correct : forall side E (c c':cmd) (Q Q':pred),
  wp_asgn side c Q = (Q', c') ->
  lossless E (skipn (length c') c) /\
  c' = firstn (length c') c /\ 
  forall  k (m1 m2 : Mem.t k), ipred Q' m1 m2 ->
   range (fun m => ipred Q (smem side m m1) (smem side m2 m)) 
   ( [[ skipn (length c') c ]] E (smem side m1 m2)).
 Proof.
  intros.
  apply wp_correct with (wp_i := wp_i_asgn); trivial.
  intros; apply wp_i_asgn_correct with (Q' := Q'0); trivial.
 Qed.

 (* WP : assign + cond  *)

 Fixpoint wp_i_cond (side:bool) (i:I.instr) (Q:pred) : option pred :=
  match i with 
   | I.Instr (I.Assign t v e) => Some (wp_ass side v e Q)
   | I.Cond e ct cf => 
     match wp wp_i_cond side ct Q, wp wp_i_cond side cf Q  with 
      | (Qt, nil), (Qf, nil) => Some (pif (e2E side e) Qt Qf)
      | _, _  => None
     end
   | _ => None
  end.
 
 Definition wp_cond := wp wp_i_cond.

 Lemma wp_i_cond_correct : forall E side (i:I.instr) (Q Q':pred),
  wp_i_cond side i Q = Some Q' ->
  lossless E [i] /\    
  forall k (m1 m2 : Mem.t k), 
   ipred Q' m1 m2 ->
   range (fun m => ipred Q (smem side m m1) (smem side m2 m)) 
         ([[ [i] ]] E (smem side m1 m2)).
 Proof.
  intros E side;
   induction i using I.instr_ind2
   with (Pc := fun c => forall c' (Q Q': pred),
    wp wp_i_cond side c Q = (Q', c') ->
    lossless E (skipn (length c') c) /\
    c' = firstn (length c') c /\
    forall k (m1 m2 : Mem.t k), ipred Q' m1 m2 ->
     range (fun m => ipred Q (smem side m m1) (smem side m2 m)) 
           ([[ skipn (length c') c ]] E (smem side m1 m2)));
   simpl; unfold ipred in *; intros; try discriminate.
  
  (* assign *)
  destruct i; simpl; [ inversion H; subst| discriminate].
  split;[apply lossless_assign | apply wp_ass_correct]; trivial.
  (* cond *)
  revert H.
  case_eq (wp wp_i_cond side c1 Q); intros Qt [ | hd tl] Heqt; [ | discriminate].
  case_eq (wp wp_i_cond side c2 Q); intros Qf [ | hd tl] Heqf; [ | discriminate].
  intros Heq; injection Heq; clear Heq; intros Heq; subst.
  destruct (IHi _ _ _ Heqt) as (Hl, Hr); 
  destruct (IHi0 _ _ _ Heqf) as (Hl0, Hr0); split.
  apply lossless_cond; trivial.
  intros k m1 m2 H0; rewrite deno_cond; rewrite peval_pif in H0; simpl in H0.
  rewrite e2E_correct in H0.
  destruct (E.eval_expr b (smem side m1 m2));[apply Hr | apply Hr0]; auto.
    (* nil *)
  injection H; clear H; intros; subst.
  split;[apply lossless_nil | split; intros; trivial].
  rewrite deno_nil; unfold range; simpl; intros f H1.
  apply H1; destruct side; trivial.
  (* cons *)     
  revert H; case_eq (wp wp_i_cond side c Q).
  intros p [ | i0 l0] Heq; apply IHi0 in Heq; trivial; destruct Heq as (Hl,(H,H0)).
  case_eq (wp_i_cond side i p); intros.
  destruct (IHi _ _ H1) as (Hli, Hr).
  inversion H2; clear H2; subst; simpl in *; auto.
  split; [apply lossless_cons | split]; trivial.
  intros; rewrite deno_cons.
  apply range_Mlet with (1:= Hr _ _ _ H2); intros; auto.
  apply H0 in H3; destruct side; auto.
  inversion H2; clear H2; intros; subst; simpl; auto.
  intros H3; injection H3; clear H3; intros; subst.
  set (c1:= i0::l0) in *.
  revert Hl H H0; generalize c1; clear c1; intros.
  split; [ | split]; trivial.
  rewrite H at 1; trivial. 
 Qed.

 Lemma wp_cond_correct : forall side E (c c':cmd) (Q Q':pred),
  wp_cond side c Q = (Q', c') ->
  lossless E (skipn (length c') c) /\
  c' = firstn (length c') c /\
  forall  k (m1 m2 : Mem.t k), ipred Q' m1 m2 ->
   range (fun m => ipred Q (smem side m m1) (smem side m2 m)) 
   ( [[ skipn (length c') c ]] E (smem side m1 m2)).
 Proof.
  intros.
  apply wp_correct with (wp_i := wp_i_cond); trivial.
  intros; apply wp_i_cond_correct with (Q' := Q'0); trivial.
 Qed.

 (* TODO: Move this *) 
 Lemma range_equiv_l : forall (P R:mem_rel) E1 c1 E2,
  lossless E1 c1 ->
  (forall k (m1 m2:Mem.t k), P k m1 m2 -> 
   range (fun m1 => R k m1 m2) ([[ c1 ]] E1 m1)) ->
  equiv P E1 c1 E2 nil R.
 Proof.
  unfold equiv; intros.
  exists (fun m1 m2 => Mlet ([[c1]] E1 m1) (fun m1' => Munit (m1',m2))).
  constructor; intros.
  rewrite Mlet_simpl; apply mu_stable_eq.
  refine (ford_eq_intro _); trivial.
  rewrite Mlet_simpl,deno_nil_elim.
  transitivity (mu (([[ c1 ]]) E1 m1) (fcte _ (f m2))).
  apply mu_stable_eq; refine (ford_eq_intro _); trivial.
  apply mu_cte_eq; apply H.
  eapply range_Mlet;[apply (H0 _ m1 m2) | unfold range; intros]; simpl; auto.
 Qed.
 
 Lemma range_equiv_r : forall (P R:mem_rel) E1 E2 c2,
  lossless E2 c2 ->
  (forall k (m1 m2:Mem.t k), P k m1 m2 -> 
   range (fun m2 => R k m1 m2) ([[ c2 ]] E2 m2)) ->
  equiv P E1 nil E2 c2 R.
 Proof.
  intros; apply equiv_sym_transp.
  apply range_equiv_l; trivial.
  intros k m1 m2 HP; apply range_weaken with (2:= H0 k m2 m1 HP).
  unfold transpR; auto.
 Qed.

 Lemma equiv_and_NotModify : forall (P:mem_rel) 
  (E1:env) (c1:cmd) (E2:env) (c2:cmd)
  (Q:mem_rel) (M1 M2:Vset.t) (M:mem_rel) (X1 X2:Vset.t),
  equiv P E1 c1 E2 c2 Q ->
  Modify E1 X1 c1 ->
  Modify E2 X2 c2 ->
  depend_only_rel M M1 M2 ->
  Vset.disjoint X1 M1 ->
  Vset.disjoint X2 M2 -> equiv (P /-\ M) E1 c1 E2 c2 (Q /-\ M).
 Proof.
  unfold equiv; intros.
  destruct (H k) as (d, Hd).
  exists d; intros m1 m2 (HP, HM0).
  apply Hd in HP; clear Hd.
  assert (exists d, 
   lift (fun m1' m2' => m1' = m2' /\ eeq_mem X1 m1 m1') d 
    ([[ c1 ]] E1 m1) ([[ c1 ]] E1 m1)).
  exists (Mlet ([[ c1 ]] E1 m1) (fun m => Munit (m,m))).
  constructor; intros.
  rewrite Mlet_simpl; apply mu_stable_eq; refine (ford_eq_intro _); trivial.
  rewrite Mlet_simpl; apply mu_stable_eq; refine (ford_eq_intro _); trivial.
  apply range_Mlet with (1:= H0 k m1); red; simpl; intros.
  apply H6; split; auto.
  destruct H5 as (d1,Hd1).
  assert (Hdec1 : forall m', sumbool (eeq_mem X1 m1 m') (~eeq_mem X1 m1 m')).
  intros; apply eeq_mem_dec'.
  assert (HH:= lift_trans_l (eeq_mem X1 m1) Hdec1 Hd1 HP); clear HP.
  apply lift_sym in HH.
  assert (exists d, 
   lift (fun m1' m2' => m1' = m2' /\ eeq_mem X2 m2 m1') d 
    ([[ c2 ]] E2 m2) ([[ c2 ]] E2 m2)).
  exists (Mlet ([[ c2 ]] E2 m2) (fun m => Munit (m,m))).
  constructor; intros.
  rewrite Mlet_simpl; apply mu_stable_eq; refine (ford_eq_intro _); trivial.
  rewrite Mlet_simpl; apply mu_stable_eq; refine (ford_eq_intro _); trivial.
  apply range_Mlet with (1:= H1 k m2); red; simpl; intros.
  apply H6; split; auto.
  destruct H5 as (d2,Hd2).
  assert (Hdec2 : forall m', sumbool (eeq_mem X2 m2 m') (~eeq_mem X2 m2 m')).
   intros; apply eeq_mem_dec'.
  assert (HHH:= lift_trans_l (eeq_mem X2 m2) Hdec2 Hd2 HH); clear HH.
  apply lift_sym in HHH.
  match type of HHH with lift _ ?d' _ _ => assert (d' == d m1 m2) end.
  refine (ford_eq_intro _); intros f; rewrite !Mlet_simpl.
  apply mu_stable_eq; refine (ford_eq_intro _); intros (x,y); trivial.
  rewrite H5 in HHH; clear H5 Hd1 Hd2 Hdec1 Hdec2.
  apply lift_weaken with (2:= HHH).
  intros m1' m2' ((HQ,Heeq1),Heeq2); split; trivial.
  apply H2 with m1 m2; trivial.
  intros t x Hin; apply Heeq1.
  apply VsetP.disjoint_mem_not_mem with (2:=Hin); 
   apply VsetP.disjoint_sym; trivial.
  intros t x Hin; apply Heeq2.
  apply VsetP.disjoint_mem_not_mem with (2:=Hin); 
   apply VsetP.disjoint_sym; trivial.
 Qed.
 (***)

 Local Open Scope bool_scope.

 Fixpoint is_decMR R := 
  match R with
   | Pforall _ _ _ | Pexists _ _ _ => false
   | Ptrue | Pfalse => true
   | Pnot r | Plet _ _ _ r => is_decMR r
   | Pand r1 r2 | Por r1 r2 | Pimplies r1 r2 | Pif _ r1 r2 | Piff r1 r2 => 
     is_decMR r1 && is_decMR r2
   | _ => true
  end.

 Lemma decMR_pred : forall P, is_decMR P -> decMR (ipred P).
 Proof.
  unfold ipred, decMR.
  assert (forall k (m1 m2:Mem.t k) P l,
   is_decMR P -> sumbool (peval m1 m2 l P) (~ peval m1 m2 l P)).
  intros k m1 m2.
  induction P; simpl; intros; auto;
   try (apply andb_true_iff in H; destruct H); try discriminate.
  destruct (IHP l); tauto.
  destruct (IHP1 l), (IHP2 l); tauto.
  destruct (IHP1 l), (IHP2 l); tauto.
  destruct (IHP1 l), (IHP2 l); tauto.
  destruct (IHP1 l), (IHP2 l); tauto.
  case (eeval m1 m2 l e); auto.
  case (eeval m1 m2 l e); auto.
  assert (W:= T.i_eqb_spec _ _ (eeval m1 m2 l e) (eeval m1 m2 l e0)).
  match type of W with if ?b then _ else _ => destruct b end; auto.
  apply Z_le_dec.
  apply Z_lt_dec.
  intros; auto.
 Qed.

 Definition Equiv P E1 c1 E2 c2 Q := equiv (ipred P) E1 c1 E2 c2 (ipred Q).
 
 Lemma Equiv_Sub : forall P P' E1 c1 E2 c2 Q Q',
  (forall k (m1 m2 : Mem.t k), 
   peval m1 m2 nil P -> peval m1 m2 nil P') ->
  (forall k (m1 m2 : Mem.t k), 
   peval m1 m2 nil Q' -> peval m1 m2 nil Q) ->    
  Equiv P' E1 c1 E2 c2 Q' ->
  Equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold Equiv, ipred; intros.
  eapply equiv_sub; intros; [ | | apply H1]; auto.
  simpl; auto.
 Qed.
 
 Lemma Equiv_Case : forall P E1 c1 E2 c2 Q e,
  is_decMR e ->
  Equiv (P /_\ e) E1 c1 E2 c2 Q ->
  Equiv (P /_\ ~_ e) E1 c1 E2 c2 Q ->
  Equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold Equiv, ipred; simpl; intros.
  apply equiv_case1 with (A := ipred e); auto.
  apply decMR_pred; trivial.
  eapply equiv_strengthen in H0.
  apply H0.
  intros; rewrite peval_pand; auto.
  eapply equiv_strengthen in H1.
  apply H1.
  intros; rewrite peval_pand, peval_pnot; auto.
 Qed.
 
  Definition wp_return t1 t2 
   E1 (f1:Proc.proc t1) E2 (f2:Proc.proc t2) Q res1 res2 :=
   psubst (psubst Q (res1<1>) (e2E side_left (proc_res E1 f1))) 
    (res2<2>) (e2E side_right (proc_res E2 f2)).

  Lemma Equiv_Sub' : forall P P' E1 c1 E2 c2 Q Q',
   (forall k (m1 m2 : Mem.t k), (ipred P) k m1 m2 -> (ipred P') k m1 m2) ->
   (forall k (m1 m2 : Mem.t k), (ipred Q') k m1 m2 -> (ipred Q) k m1 m2) ->
   Equiv P' E1 c1 E2 c2 Q' ->
   Equiv P E1 c1 E2 c2 Q.
  Proof.
   unfold ipred; intros.
   eapply equiv_sub; intros; [ | | apply H1]; auto.
   apply H; eauto.
   apply H0; eauto.
  Qed.

  Definition only_params_or_global t1 t2 
   E1 (f1:Proc.proc t1) E2 (f2:Proc.proc t2) P :=
   let p1 := Vset_of_var_decl (proc_params E1 f1) in
   let p2 := Vset_of_var_decl (proc_params E2 f2) in
   let (X1, X2) := pdepend P in
    (get_locals X1 [<=?] p1) && (get_locals X2 [<=?] p2).
 
 Definition only_global_or_res t1 t2 
  (f1:Proc.proc t1) (f2:Proc.proc t2) Q (res1:Var.var t1) (res2:Var.var t2) :=
  let (X1, X2) := pdepend Q in
   (get_locals X1 [<=?] {{res1}}) && (get_locals X2 [<=?] {{res2}}).

 Record EquivFun t P E1 (f1:Proc.proc t) E2 (f2:Proc.proc t) Q :=
  {
   eqf_res1  : Var.var t;
   eqf_res2  : Var.var t;
   eqf_equiv : Equiv P E1 (proc_body E1 f1) E2 (proc_body E2 f2) 
    (wp_return E1 f1 E2 f2 Q eqf_res1 eqf_res2);
   eqf_pre   : only_params_or_global E1 f1 E2 f2 P;
   eqf_post  : only_global_or_res f1 f2 Q eqf_res1 eqf_res2
  }.

 Fixpoint forall_fresh_l (p:pred) (X:list Var.t) (fresh:list positive) : pred :=
   match X with
   | nil => p
   | Var.mkV t0 v :: tlv => 
      let v' := (Var.Lvar t0 (hd 1%positive fresh)) in
      let p := forall_fresh_l p tlv (tl fresh) in
      if Vset.mem v' (pbind p) || Vset.mem v' (pfv p) then Pfalse
      else Pforall v' (psubst p (VarLeft v) (VarLogic v'))
   end.

 Fixpoint forall_fresh_r (p:pred) (X:list Var.t) (fresh:list positive) : pred :=
  match X with
   | nil => p
   | Var.mkV t0 v :: tlv => 
     let v' := (Var.Lvar t0 (hd 1%positive fresh)) in
     let p := forall_fresh_r p tlv (tl fresh) in
     if Vset.mem v' (pbind p) || Vset.mem v' (pfv p) then Pfalse
     else Pforall v' (psubst p (VarRight v) (VarLogic v'))
  end.

 Definition get_pos (v : Var.t) : positive :=
  match v with
   | Var.mkV _ (Var.Gvar _ p) => p
   | Var.mkV _ (Var.Lvar _ p) => p
  end.

 Definition cast_var t (v:Var.var t) t' :=
  match v with
   | Var.Gvar _ p => Var.Gvar t' p
   | Var.Lvar _ p => Var.Lvar t' p
  end.
 
 Inductive tuple3 (A B C:Type) : Type := 
 | Tuple3 : A -> B -> C -> tuple3 A B C
 | Tuple3_Error : tuple3 A B C.

 Inductive tuple4 (A B C D:Type) : Type := 
 | Tuple4 : A -> B -> C -> D -> tuple4 A B C D
 | Tuple4_Error : tuple4 A B C D.
 (* End move this *)

 Definition destruct_cond (c:cmd) := 
  match c with 
   | I.Cond e ct cf::c' => Tuple4 e ct cf c'
   | _ => Tuple4_Error _ _ _ _
  end.
 
 Section CHECK_PROOF.
   
  Variable E1 E2 : env.

  (* TODO: Add a definition after each EquivFun *)
  Inductive EquivFun_info := 
  | Mk_EquivFun_info : forall t pre (f1:Proc.proc t) (f2:Proc.proc t) post,  
    EquivFun pre E1 f1 E2 f2 post -> EquivFun_info.

  Inductive TypeRand :=
  | RIid         : TypeRand
  | RIidempotant : forall t, Exp t -> TypeRand 
  | RIbij        : forall t, Exp t -> Exp t -> TypeRand. 
 
  Inductive RhlRule : Type :=
  | Rnil : RhlRule 
  | Rsub_pre : pred -> RhlRule -> RhlRule 
  | Rsub_post : pred -> RhlRule -> RhlRule 
  | Rcase : pred -> RhlRule -> RhlRule -> RhlRule
  | RcondLeft : RhlRule -> RhlRule -> RhlRule
  | RcondRight: RhlRule -> RhlRule -> RhlRule
  | RcondBoth : RhlRule -> RhlRule -> RhlRule
  | Rapp  : nat -> nat -> pred -> RhlRule -> RhlRule -> RhlRule
  | Rwp_asgn  : RhlRule -> RhlRule
  | Rwp_simpl : RhlRule -> RhlRule
  | Rwp_call : list Var.t -> list Var.t -> EquivFun_info -> RhlRule -> RhlRule
  | Rrand_bij : Var.t -> TypeRand -> RhlRule -> RhlRule
  | Rrand_disj : Var.t -> bool -> RhlRule -> RhlRule
  | Rpre_false : RhlRule
  | Rpost_true : RhlRule
  | Rnot_modify : pred (* M *) -> pred (* Q' *) -> RhlRule -> RhlRule
  | RinlineLeft : cmd -> RhlRule -> RhlRule 
  | RinlineRight : cmd -> RhlRule -> RhlRule
  | Rderandomize : cmd -> cmd -> RhlRule -> RhlRule
  | Rswap : 
     bool (*side*) -> 
     nat (* start *) -> 
     nat (* length *) -> 
     bool (* sign, true = positive *) -> 
     nat -> 
     RhlRule -> RhlRule.

  Inductive deriv_status := 
  | DS_cond : list pred -> deriv_status
  | DS_error : pred -> cmd -> cmd -> pred -> RhlRule -> deriv_status.

  Definition app_cond s (f: list pred -> deriv_status) :=
   match s with
   | DS_cond cond => f cond
   | _ => s
   end.

  Fixpoint simpl_pred (p:pred) :=
   match p with
   | Ptrue => Ptrue
   | Pfalse => Pfalse
   | Pnot p => pnot (simpl_pred p)
   | Pand p1 p2 => pand (simpl_pred p1) (simpl_pred p2)
   | Por p1 p2 => por (simpl_pred p1) (simpl_pred p2)
   | Pimplies p1 p2 => pimplies (simpl_pred p1) (simpl_pred p2)
   | Piff p1 p2 => piff (simpl_pred p1) (simpl_pred p2)
   | Pif e p1 p2 => pif e  (simpl_pred p1) (simpl_pred p2)
   | Pforall t x p => pforall x (simpl_pred p)
   | Pexists t x p => pexists x (simpl_pred p)
   | Plet t x e p => plet x e (simpl_pred p)
   | Pexp e => pexp e
   | Peq t e1 e2 => peq e1 e2
   | Ple e1 e2 => ple e1 e2
   | Plt e1 e2 => plt e1 e2
   end.

  Definition add_cond (p:pred) cond := 
   (* let p := simpl_pred p in *)
   if pred_eqb p Ptrue then cond else p :: cond.

  Variable pi1 : eq_refl_info E1.
  Variable pi2 : eq_refl_info E2. 

  (* TODO: Move this *)
  Definition split_list (A:Type) (n:nat) (l:list A) := (firstn n l, skipn n l).
 
  Lemma split_list_correct : forall (A:Type) n (l hd tl:list A),
   split_list n l = (hd,tl) -> l = hd ++ tl.
  Proof.
   unfold split_list; simpl; intros.
   injection H; clear H; intros; subst.
   symmetry; apply firstn_skipn.
  Qed.
  (* End Move *)

  Fixpoint make_assoc_var_exp (side:bool)
       tvars (params:var_decl tvars) targs (args:E.args targs) s : asubst :=
    match params, args with
    | dcons tx tvars x params, dcons te targs e args => 
        let x := cast_var x te in
        let x := if side then x<1> else x<2> in
        make_assoc_var_exp side params args (mkAssoc lvar Exp te x (e2E side e) :: s)
    | _, _ => s
    end.

  Definition wp_call fresh1 fresh2 (info:EquivFun_info) c1 c2 Q :=
   let (t,pre,f1,f2,post,equ) := info in    
   match List.rev c1, List.rev c2 with
    | I.Call t1' x1 f1' args1 :: c1', I.Call t2' x2 f2' args2 :: c2' =>
      if (Proc.eqb f1 f1' && Proc.eqb f2 f2')%bool then 
       match pi1 f1', pi2 f2' with 
        | Some i1, Some i2 =>
          let f1_modify := pi_mod i1 in
          let f2_modify := pi_mod i2 in
          let s := 
            make_assoc_var_exp side_left (proc_params E1 f1') args1 
             (make_assoc_var_exp side_right (proc_params E2 f2') args2 nil) in
          let pre := psubst_para pre s in
          let res1 := cast_var (eqf_res1 equ) t1' in
          let res2 := cast_var (eqf_res2 equ) t2' in
          let p := psubst Q (VarLeft x1) (VarLeft res1) in
          let p := psubst p (VarRight x2) (VarRight res2) in
          let p := pimplies post p in
          let (fresh1, fresh2) := (map get_pos fresh1, map get_pos fresh2) in
          let p := 
            forall_fresh_r 
              (forall_fresh_l p (Var.mkV res1::nil) fresh1 )
              (Var.mkV res2::nil) fresh2 in
          let p := 
           forall_fresh_l p (f1_modify) (List.tl fresh1) in 
          let p := 
           forall_fresh_r p (f2_modify) (List.tl fresh2) in 
          let (X1, X2) := pdepend Q in
          if Vset.mem res1 X1 || Vset.mem res2 X2 then Tuple3_Error _ _ _
          else Tuple3 (List.rev c1') (List.rev c2') (pand pre p) 
        | _, _ => Tuple3_Error _ _ _
        end
      else Tuple3_Error _ _ _
    | _,_ => Tuple3_Error _ _ _
    end.

  Definition bound_random (side:bool) t (d:E.support t) (vx:lvar t) 
   (cond:pred) : pred * pred :=
   match d in E.support t0 return lvar t0 -> pred * pred with
   | E.DZ l r => fun vx:lvar T.Zt =>
     let l := e2E side l in
     let r := e2E side r in
     (ple l r, pand (ple l vx) (ple vx r))
   | _ => fun _ => (cond, Ptrue)
   end vx.

  Definition wp_rnd_disj (x:Var.t) (side:bool) c1 c2 Q :=
   let fv:= pfv Q in
   let bind := pbind Q in
   let c := if side then c1 else c2 in
    match List.rev c with
    | I.Instr (I.Random t y d) :: c' =>
      let vq := cast_var x t in
      let q := VarLogic vq in
      let y := if side then y<1> else y<2> in
      let (cond, bound) := bound_random side d q Ptrue in
      let P := pand cond (pforall vq (pimplies bound (psubst Q y (Evar q)))) in
      let c1 := if side then List.rev c' else c1 in
      let c2 := if side then c2 else List.rev c' in
      if Vset.mem vq fv || Vset.mem vq bind then Tuple3_Error _ _ _
      else Tuple3 c1 c2 P
    | _ => Tuple3_Error _ _ _
   end.

  Definition wp_eq_random t1 (d1:E.support t1) t2 (d2:E.support t2) :=
   match d1, d2 with
   | E.Dbool, E.Dbool => Ptrue
   | E.DZ l1 r1, E.DZ l2 r2 =>
     let l1 := e2E side_left l1 in
     let r1 := e2E side_left r1 in
     let l2 := e2E side_right l2 in
     let r2 := e2E side_right r2 in
     pand (peq l1 l2) (peq r1 r2)
   | E.Duser t1 us1 , E.Duser t2 us2 => if US.eqb us1 us2 then Ptrue else Pfalse
   | _, _ => Pfalse
   end.

  (** Rrnd_disj *)
  Lemma equiv_random_l : forall E E' t (x:Var.var t) d (Q:mem_rel),
   equiv (fun k (m1 m2:Mem.t k) => 
    forall v, In v (E.eval_support d m1) ->
     Q k (m1{!x<--v!}) m2) E [x<$-d] E'  nil Q.
  Proof.
   unfold equiv; intros.
   exists (fun m1 m2 => Mlet (([[ [x <$- d] ]]) E m1)
          (fun m1' => Munit (m1',m2))); intros.
   constructor; intros; try rewrite Mlet_simpl.
   apply mu_stable_eq; refine (ford_eq_intro _ ); trivial.
   rewrite deno_nil_elim.
   transitivity  (mu ([[ [x<$-d] ]] E m1) (fcte _ (f m2))).
    apply mu_stable_eq; refine (ford_eq_intro _ ); trivial.
   apply mu_cte_eq; apply lossless_random.
   rewrite deno_random, Mcomp.
   apply range_Mlet with (fun v => In v (E.eval_support d m1)).
   unfold range; intros; simpl.
   assert (forall n, (n <= (length (E.eval_support d m1)))%nat ->
    0 ==
    comp Uplus 0
    (fun n : nat =>
     [1/]1+Peano.pred (length (E.eval_support d m1)) *
     f (nth n (E.eval_support d m1) (T.default k t0))) n)%U; auto with arith.
   induction n; simpl; intros; trivial. 
   rewrite <- H0. 
   repeat Usimpl; apply IHn; auto with arith.
   apply nth_In; auto with arith.
   intros; unfold range; simpl; intros.
   apply H1; red; simpl; auto.
  Qed.

  Lemma equiv_random_r : forall E E' t (x:Var.var t) d (Q:mem_rel),
   equiv (fun k (m1 m2:Mem.t k) => 
    forall v, In v (E.eval_support d m2) -> 
     Q k m1 (m2{!x<--v!})) E nil E' [x<$-d] Q.
  Proof.
   intros; apply equiv_sym_transp.  
   eapply equiv_strengthen;[ | apply equiv_random_l]. 
   trivial.
  Qed.

  Definition check_notmodify (P:pred) c1 c2 :=
   match modify pi1 Vset.empty c1, modify pi2 Vset.empty c2 with
    | Some M1, Some M2 => 
     let (X1, X2) := pdepend P in
      (Vset.disjoint M1 X1 && Vset.disjoint M2 X2)%bool
    | _, _ => false 
   end.

  Definition check_inline (side:bool) (c c':cmd) (Q:pred) := true.

  Definition check_derandomize (side:bool) (c1 c1':cmd) (Q:pred) := true.

  Definition n_swapable := 1000%positive.

   Definition swapable (E:env) (pi:eq_refl_info E) (c1 c2:cmd) :=
   match modify pi Vset.empty c1, modify pi Vset.empty c2 with
   | Some M1, Some M2 =>
     if Vset.disjoint M1 M2 then
     match eqobs_in n_swapable pi c1 M1, eqobs_in n_swapable pi c2 M2 with
     | Some I1, Some I2 =>
       if Vset.disjoint I1 M2 then Vset.disjoint I2 M1 
       else false
     | _, _ => false
     end
     else false
   | _, _ => false
   end.

  Lemma swapable_correct : forall (E:env) (pi:eq_refl_info E) (c1 c2:cmd),
   swapable pi c1 c2 = true ->
   equiv Meq E (c1++c2) E (c2++c1) Meq.
  Proof.
   unfold swapable; intros E pi c1 c2.
   generalize (modify_correct pi c1 Vset.empty);
   destruct (modify pi Vset.empty c1) as [M1 | ]; 
   intro; try (intros; discriminate).

   generalize (modify_correct pi c2 Vset.empty);
   destruct (modify pi Vset.empty c2) as [M2 | ]; 
   intro; try (intros; discriminate).

   case_eq (Vset.disjoint M1 M2); intro; try (intros; discriminate).
   generalize (fun I => @eqobs_in_correct n_swapable E pi c1 I M1);
   destruct (eqobs_in n_swapable pi c1 M1) as [I1 | ]; 
    intro; try (intros; discriminate).

   generalize (fun I => @eqobs_in_correct n_swapable E pi c2 I M2);
    destruct (eqobs_in n_swapable pi c2 M2) as [I2 | ]; 
    intro; try (intros; discriminate).

   case_eq (Vset.disjoint I1 M2); intros; try discriminate.
   apply equiv_swap with (3:=H2 _ (eq_refl _)) (4:=H3 _ (eq_refl _)); auto.
  Qed.

  Definition check_swap (side:bool) (c:cmd) start length (dir:bool) delta := 
   let check := if side then swapable pi1 else swapable pi2 in
   let (hd,tl1) := split_list start c in
   let (to_move, tl) := split_list length tl1 in
    if dir then
     let (tlhd, tltl) := split_list delta tl in
     if check to_move tlhd then Some (hd++(tlhd++(to_move++tltl)))
     else None
    else 
     let len := List.length hd in
     let (hdhd,hdtl) := split_list (len - delta) hd in
     if check hdtl to_move then Some (hdhd++(to_move++(hdtl++tl)))
     else None.

  Lemma check_swap_correct : forall side c start length dir delta c',
   check_swap side c start length dir delta = Some c' ->
   let E := if side then E1 else E2 in
   equiv Meq E c E c' Meq.
  Proof.
   unfold check_swap; intros side c start length dir delta c'.
   case_eq (split_list start c); intros hd tl1 Heq1.
   apply split_list_correct in Heq1; subst.
   case_eq (split_list length tl1); intros to_move tl Heq1.
   apply split_list_correct in Heq1; subst.
   destruct dir.
   case_eq (split_list delta tl); intros tlhd tltl Heq1.
   apply split_list_correct in Heq1; subst.
   case_eq ((if side then swapable pi1 else swapable pi2) to_move tlhd); 
    intros; try discriminate.
   injection H0; clear H0; intros; subst.
   apply equiv_app with Meq;[ apply equiv_eq_mem | ].
   repeat rewrite List.app_assoc.
   apply equiv_app with Meq;[ | apply equiv_eq_mem].
   destruct side; apply swapable_correct with (1:= H).
   case_eq (split_list (Datatypes.length hd - delta) hd); intros hdhd hdtl Heq1.
   apply split_list_correct in Heq1; subst.
   case_eq ((if side then swapable pi1 else swapable pi2) hdtl to_move); 
    intros; try discriminate.
   injection H0; clear H0; intros; subst.
   rewrite <- List.app_assoc.
   apply equiv_app with Meq;[ apply equiv_eq_mem | ].
   repeat rewrite List.app_assoc.
   apply equiv_app with Meq;[ | apply equiv_eq_mem].
   destruct side; apply swapable_correct with (1:= H).
  Qed.


  Section RANDOM.

   Variable user_is_uniform : forall t, US.usupport t -> bool.

   Hypothesis user_is_uniform_correct : forall t (d:US.usupport t) k,
    user_is_uniform d = true -> NoDup (US.eval k d).

   Fixpoint is_uniform t (e:E.support t) : bool :=
    match e with
     | E.Dbool => true
     | E.Dnat _ => true
     | E.DZ _ _ => true
     | E.Dprod _ _ d1 d2 => is_uniform d1 && is_uniform d2
     | E.Duser t' u => user_is_uniform u
    end.

   Variable user_is_full : forall t, US.usupport t -> bool.

   Hypothesis user_is_full_correct : forall t (d:US.usupport t) k,
    user_is_full d = true -> forall x, In x (US.eval k d). 

   Fixpoint is_full t (e:E.support t) : bool :=
    match e with
     | E.Dbool => true
     | E.Dnat _ => false
     | E.DZ _ _ => false
     | E.Dprod _ _ d1 d2 => is_full d1 && is_full d2
     | E.Duser t' u => user_is_full u
    end.

   Definition check_bij t (y2 x :Var.var t) (d:E.support t) (tr:TypeRand) :=
    let lx := VarLogic x in
     match tr with
      | RIid => (Ptrue, Evar lx, Evar lx)
      | RIidempotant t' f => 
        match T.eq_dec t' t with
        | left Heq =>
          let fx := match Heq in _ = t2 return Exp t2 with eq_refl => f end in
          let f := match Heq in _ = t2 return Exp t2 with eq_refl => f end in
          let f_x := esubst (y2<2>) lx f in
          let f_f_x := esubst (y2<2>) f_x f in 
          let cond := peq f_f_x lx in
          if Vset.mem x (lfv f) || 
             Vset.mem x (lbind f) ||
             negb (Vset.disjoint (lfv f_x) (lbind f))
          then (Pfalse, Evar lx, Evar lx) else (cond, f_x, f_x)
        | _ => (Pfalse, Evar lx, Evar lx)
        end
      | RIbij t' f finv =>
        match T.eq_dec t' t with
        | left Heq =>
          let f := match Heq in _ = t2 return Exp t2 with eq_refl => f end in
          let finv := match Heq in _ = t2 return Exp t2 with eq_refl => finv end in
          let f_x := esubst (y2<2>) lx f in
          let finv_f_x := esubst (y2<2>) f_x finv in
          let finv_x := esubst (y2<2>) lx finv in
          let f_finv_x := esubst (y2<2>) finv_x f in
          let cond := pand (peq finv_f_x lx) (peq f_finv_x lx) in
           if Vset.mem x (lfv f) || Vset.mem x (lfv finv) ||
              Vset.mem x (lbind f) || Vset.mem x (lbind finv) ||
              negb (Vset.disjoint (lfv f_x) (lbind f)) ||
              negb (Vset.disjoint (lfv finv_x) (lbind finv)) || 
              negb (Vset.disjoint (lfv f_x) (lbind finv)) ||
              negb (Vset.disjoint (lfv finv_x) (lbind f))
           then (Pfalse, Evar lx, Evar lx) else (cond, f_x, finv_x)
       | _ => (Pfalse, Evar lx, Evar lx)
     end    
   end.

   Definition wp_rnd_bij (r:Var.t) (tr:TypeRand) c1 c2 Q :=
    let fv:= pfv Q in
    let bind := pbind Q in
    match List.rev c1, List.rev c2 with
    | I.Instr (I.Random t1 y1 d1)::c1', I.Instr (I.Random t2 y2 d2)::c2' => 
      if is_uniform d1 && is_uniform d2 then
      match T.eq_dec t1 t2 with
      | left Heq =>
        let y1:=match Heq in (_ = t3) return Var.var t3 with eq_refl => y1 end in
        let d1:=match Heq in (_ = t3) return E.support t3 with eq_refl => d1 end in
        let vx := cast_var r t2 in
        let x := VarLogic vx in
        let cond2 := if is_full d2 then Ptrue else Pfalse in
        let (cond1, bound) := bound_random side_right d2 x cond2 in
        let eq_cond := wp_eq_random d1 d2 in
        let (condfx, finvx) := check_bij y2 vx d2 tr in
        let (cond, fx) := condfx in
        let cond := pand (pand (psubst bound x fx) (psubst bound x finvx)) cond in
        let e_x := Evar x in
        let Q := psubst (psubst Q (y1<1>) e_x) (y2<2>) fx in
        let Q := pforall vx (pimplies bound (pand cond (pimplies cond Q))) in
        let Q := pand eq_cond (pand cond1 Q) in
         if Vset.mem vx fv || 
            Vset.mem vx bind || 
            negb (Vset.disjoint (lfv fx) bind) ||
            negb (Vset.disjoint (lfv fx) (pbind bound)) ||
            negb (Vset.disjoint (lfv finvx) (pbind bound)) 
         then Tuple3_Error _ _ _
         else Tuple3 (List.rev c1') (List.rev c2') Q
       | _ => Tuple3_Error _ _ _
      end
      else Tuple3_Error _ _ _
     | _, _ => Tuple3_Error _ _ _
    end.

   Lemma NoDup_seqZ : forall len start, NoDup (seqZ start len).
   Proof.
    induction len; simpl; auto; intros.
    constructor; auto.
    intro H.
    apply In_seqZ_le in H; omega.
   Qed.

   Lemma le_In_seqZ: forall (n:nat) (m i:Z), 
    (m <= i < Z_of_nat n + m)%Z ->  
    In i (seqZ m n).
   Proof.
    induction n; intros m i [Hge Hle].
    simpl in Hle; elimtype False; omega.

    rewrite inj_S, Zplus_succ_l, Zlt_succ_r in Hle.   
    case (Zle_lt_or_eq _ _ Hle); clear Hle; intro.

    case (Zle_lt_or_eq _ _ Hge); clear Hge; intro.
    right; apply IHn; omega.
    left; rewrite H0; trivial.

    case (Zle_lt_or_eq _ _ Hge); clear Hge; intro.
    right; apply IHn; omega.
    left; rewrite H0; trivial.
   Qed.

   Lemma In_Z_support : forall k (e1 e2:E.expr T.Zt) (m:Mem.t k) (v:Z),
    (E.eval_expr e1 m <= E.eval_expr e2 m)%Z ->
    (E.eval_expr e1 m <= v <= E.eval_expr e2 m)%Z ->
    In v (E.eval_support [e1,,e2] m).
   Proof.
    intros; simpl; unfold Z_support.
    generalize (Zle_cases (E.eval_expr e1 m) (E.eval_expr e2 m)).
    case (Zle_bool (E.eval_expr e1 m) (E.eval_expr e2 m)); intro.  
    apply le_In_seqZ.
    rewrite inj_Zabs_nat, Zabs_eq; omega.
    exfalso; omega.
   Qed.

   Lemma is_uniform_correct : forall k (m:Mem.t k) t (d:E.support t),
    is_uniform d = true ->
    NoDup (E.eval_support d m).
   Proof.
    simpl in *.
    intros; induction d; simpl in *.
    constructor; simpl; auto.
    intro Heq; elim Heq; intros; auto; discriminate.
    constructor; simpl; auto.
    intro Hin; apply In_seq_le in Hin; omega.
    apply NoDup_seq.
    unfold Z_support.
    case_eq (Zle_bool (E.eval_expr e m) (E.eval_expr e0 m)); intros; auto.
    apply NoDup_seqZ.
    apply user_is_uniform_correct; trivial.
    apply andb_true_iff in H.
    apply NoDup_list_prod; tauto.
   Qed.

   Lemma is_full_correct : forall k (m:Mem.t k) t (d:E.support t),
    is_full d = true ->
    forall x, In x (E.eval_support d m).
   Proof.
    induction d; simpl; intros.
    destruct x; tauto.
    discriminate.
    discriminate.
    apply user_is_full_correct; trivial.
    apply andb_prop in H; destruct H.
    destruct x; apply in_prod_iff; auto.
   Qed.

   Fixpoint check_proof (P:pred) (c1 c2:cmd) 
    (Q:pred) (d:RhlRule) cond : deriv_status :=
    match d with
    | Rnil => 
      match c1, c2 with
       | nil, nil => DS_cond (add_cond (pimplies P Q) cond)
       | _, _ => DS_error P c1 c2 Q d
      end                 
    | Rsub_pre P' d => check_proof P' c1 c2 Q d (add_cond (pimplies P P') cond)
    | Rsub_post Q' d => check_proof P c1 c2 Q' d (add_cond (pimplies Q' Q) cond)
    | Rcase R dt df => 
     if is_decMR R then 
      app_cond 
      (check_proof (pand P R) c1 c2 Q dt cond)
      (check_proof (pand P (pnot R)) c1 c2 Q df) 
      else DS_error P c1 c2 Q d
    | RcondLeft dt df =>
      match destruct_cond c1 with
      | Tuple4 e ct cf c1' => 
        let pe := pexp (e2E side_left e) in 
        app_cond
        (check_proof (pand P pe) (ct++c1') c2 Q dt cond) 
        (check_proof (pand P (pnot pe)) (cf++c1') c2 Q df) 
      | _ => DS_error P c1 c2 Q d
      end
    | RcondRight dt df =>
      match destruct_cond c2 with
      | Tuple4 e ct cf c2' => 
        let pe := pexp (e2E side_right e) in 
        app_cond 
        (check_proof (pand P pe) c1 (ct++c2') Q dt cond) 
        (check_proof (pand P (pnot pe)) c1 (cf++c2') Q df) 
      | _ => DS_error P c1 c2 Q d
      end
    | RcondBoth dt df =>
      match destruct_cond c1, destruct_cond c2 with
      | Tuple4 e1 ct1 cf1 c1', Tuple4 e2 ct2 cf2 c2' =>
        let e1 := (e2E side_left e1) in 
        let e2 := (e2E side_right e2) in 
        let cond := add_cond (pimplies P (peq e1 e2)) cond in
        let ep1 := pexp e1 in
        let ep2 := pexp e2 in
        let Pt := pand P (pand ep1 ep2) in
        let Pf := pand P (pand (pnot ep1) (pnot ep2)) in
         app_cond 
         (check_proof Pt (ct1++c1') (ct2++c2') Q dt cond) 
         (check_proof Pf (cf1++c1') (cf2++c2') Q df) 
      | _, _ => DS_error P c1 c2 Q d
      end
    | Rapp k1 k2 R dh dt =>
      let (ch1,ct1) := split_list k1 c1 in
      let (ch2,ct2) := split_list k2 c2 in
      app_cond 
      (check_proof P ch1 ch2 R dh cond) 
      (check_proof R ct1 ct2 Q dt)
    | Rwp_asgn d =>
      let (Q,c1) := wp_asgn side_left c1 Q in
      let (Q,c2) := wp_asgn side_right c2 Q in
      check_proof P c1 c2 Q d cond
    | Rwp_simpl d =>
      let (Q,c1) := wp_cond side_left c1 Q in
      let (Q,c2) := wp_cond side_right c2 Q in
      check_proof P c1 c2 Q d cond
    | Rwp_call fresh1 fresh2 info d' =>
      match wp_call fresh1 fresh2 info c1 c2 Q with
      | Tuple3 c1 c2 Q => check_proof P c1 c2 Q d' cond
      | _ =>  DS_error P c1 c2 Q d
      end
    | Rrand_bij v info d' =>
      match wp_rnd_bij v info c1 c2 Q with
      | Tuple3 c1 c2 Q => check_proof P c1 c2 Q d' cond
      | _ =>  DS_error P c1 c2 Q d      end 
    | Rrand_disj v side d' => 
      match wp_rnd_disj v side c1 c2 Q with
      | Tuple3 c1 c2 Q => check_proof P c1 c2 Q d' cond
      | _ =>  DS_error P c1 c2 Q d
      end      
    | Rpre_false => 
      DS_cond (add_cond (pimplies P Pfalse) cond)
    | Rpost_true =>
      if (is_lossless pi1 c1 && is_lossless pi2 c2)%bool then 
       DS_cond (add_cond Q cond)
      else DS_error P c1 c2 Q d
    | Rnot_modify M Q' d' =>
      if (check_notmodify M c1 c2)%bool then
       let cond := 
        add_cond (pimplies P M) 
        (add_cond (pimplies M (pimplies Q' Q)) cond) in
        check_proof P c1 c2 Q' d' cond 
       else DS_error P c1 c2 Q d
    | RinlineLeft c1' d' =>
      if check_inline side_left c1 c1' Q
      then check_proof P c1' c2 Q d' cond
      else DS_error P c1 c2 Q d
    | RinlineRight c2' d' =>
      if check_inline side_right c2 c2' Q then
        check_proof P c1 c2' Q d' cond 
      else DS_error P c1 c2 Q d
    | Rderandomize c1' c2' d' =>
      if (check_derandomize side_left c1 c1' Q && 
          check_derandomize side_right c2 c2' Q)%bool then
       check_proof P c1' c2' Q d' cond
      else DS_error P c1 c2 Q d
    | Rswap side start length dir delta d' =>
      let c := if side then c1 else c2 in
      match check_swap side c start length dir delta with
      | Some c =>
        let c1 := if side then c else c1 in
        let c2 := if side then c2 else c in
        check_proof P c1 c2 Q d' cond
      | None => DS_error P c1 c2 Q d
      end
   end.

   Definition interp_cond1 P := forall k (m1 m2:Mem.t k), ipred P m1 m2.
   Definition interp_cond := Forall interp_cond1.

   Lemma interp_cond_add : forall P cond, 
    interp_cond (add_cond P cond) ->
    interp_cond1 P /\ interp_cond cond.
   Proof.
    intros P cond; unfold add_cond, interp_cond; intros H; inversion H; auto.
    generalize (pred_eqb_spec P Ptrue); destruct (pred_eqb P Ptrue); intro; subst.
    split; [ | trivial].
    unfold interp_cond1, ipred; intros; simpl; trivial.
    discriminate.

    generalize (pred_eqb_spec P Ptrue); destruct (pred_eqb P Ptrue); intro; subst.
    split; [ | trivial].
    unfold interp_cond1, ipred; intros; simpl; trivial.
    injection H0; intros; subst; tauto.
   Qed.

   Lemma interp_pimplies : forall P Q, 
    interp_cond1 (pimplies P Q) <-> 
    forall k (m1 m2:Mem.t k), ipred P m1 m2 -> ipred Q m1 m2.
   Proof.
    intros P Q.
    destruct (ipred_pimplies P Q); unfold implMR in *; unfold impR in *.
    unfold interp_cond1; split; auto.
   Qed.

   Lemma app_cond_DS_cond : forall res f cond, 
    app_cond res f = DS_cond cond ->
    exists cond', res = DS_cond cond' /\ f cond' = DS_cond cond.
   Proof.
    destruct res;[ | discriminate].
    simpl; intros; exists l; auto.
   Qed.

   Lemma destruct_cond_correct : forall c e ct cf c',
    destruct_cond c = Tuple4 e ct cf c' ->
    c = (If e then ct else cf) :: c'.
   Proof.
    intros c e ct cf c'; destruct c; [ discriminate | ].
    destruct i; simpl; try discriminate.
    intros Heq; injection Heq; clear Heq; intros; subst; trivial.
   Qed.

   Lemma equiv_cond_l : forall P E1 e ct cf c1 E2 c2 Q,
    equiv (P /-\ EP1 e) E1 (ct++c1) E2 c2 Q ->
    equiv (P /-\ ~- EP1 e) E1 (cf++c1) E2 c2 Q ->
    equiv P E1 ((If e then ct else cf)::c1) E2 c2 Q.
   Proof.
    unfold equiv, andR, notR,EP1,is_true.
    intros P E3 e1 ct cf c1 E4 c2 Q HD HD' k.
    destruct (HD k) as (d3,Hd); destruct (HD' k) as (d',Hd').
    exists (fun m1 m2 =>
     if E.eval_expr e1 m1 then d3 m1 m2  else d' m1 m2); intros.
    case_eq (E.eval_expr e1 m1); intros Heq;
     rewrite deno_cons, deno_cond, Heq, <- deno_app;
     [apply Hd | apply Hd']; split; autob.
   Qed.

   Lemma Equiv_cond_l : forall P E1 e ct cf c1 E2 c2 Q,
    Equiv (pand P (pexp (e2E side_left e))) E1 (ct++c1) E2 c2 Q ->
    Equiv (pand P (pnot (pexp (e2E side_left e)))) E1 (cf++c1) E2 c2 Q ->
    Equiv P E1 ((If e then ct else cf)::c1) E2 c2 Q.
   Proof.
    unfold Equiv; intros.
    rewrite ipred_pand, ipred_pexp_left in H.  
    rewrite ipred_pand, ipred_pnot, ipred_pexp_left in H0.
    apply equiv_cond_l; auto.
   Qed.

   Lemma equiv_cond_r :  forall P E1 c1 E2 e ct cf c2 Q,
    equiv (P /-\ EP2 e) E1 c1 E2 (ct++c2) Q ->
    equiv (P /-\ ~- EP2 e) E1 c1 E2 (cf++c2) Q ->
    equiv P E1 c1 E2 ((If e then ct else cf)::c2) Q.
   Proof.
    intros; apply equiv_sym_transp.
    apply equiv_cond_l; apply equiv_sym_transp; simplMR; trivial.
   Qed.

   Lemma Equiv_cond_r : forall P E1 c1 E2 e ct cf c2 Q,
    Equiv (pand P (pexp (e2E side_right e))) E1 c1 E2 (ct++c2) Q ->
    Equiv (pand P (pnot (pexp (e2E side_right e)))) E1 c1 E2 (cf++c2)  Q ->
    Equiv P E1 c1 E2 ((If e then ct else cf)::c2) Q.
   Proof.
    unfold Equiv; intros.
    rewrite ipred_pand, ipred_pexp_right in H.  
    rewrite ipred_pand, ipred_pnot, ipred_pexp_right in H0.
    apply equiv_cond_r; auto.
   Qed.

   Lemma equiv_cond : forall P Q E1 (e1:E.expr T.Bool) ct1 cf1 c1 E2 
    (e2:E.expr T.Bool) ct2 cf2 c2,
    equiv (P /-\ (EP1 e1 /-\ EP2 e2)) E1 (ct1++c1) E2 (ct2++c2) Q ->
    equiv (P /-\ (~- EP1 e1 /-\ ~- EP2 e2)) E1 (cf1++c1) E2 (cf2++c2) Q ->
    (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
    equiv P 
    E1 ((If e1 then ct1 else cf1)::c1) 
    E2 ((If e2 then ct2 else cf2)::c2) 
    Q.
   Proof.
    intros; apply equiv_cond_l; apply equiv_cond_r.
    simplMR; trivial.
    apply equiv_False; unfold andR,notR,EP1,EP2.
    intros k m1 m2 ((H2, H3), H4); apply H4; erewrite <- H1; eauto.
    apply equiv_False; unfold andR,notR,EP1,EP2.
    intros k m1 m2 ((H2, H3), H4); apply H3; erewrite H1; eauto.
    simplMR; trivial.
   Qed.

   Lemma Equiv_cond : forall P Q E1 (e1:E.expr T.Bool) ct1 cf1 c1 E2 
    (e2:E.expr T.Bool) ct2 cf2 c2,
    Equiv 
    (pand P (pand (pexp (e2E side_left e1)) (pexp (e2E side_right e2)))) 
    E1 (ct1++c1) 
    E2 (ct2++c2) 
    Q ->
    Equiv 
    (pand P (pand (pnot (pexp (e2E side_left e1))) 
     (pnot (pexp (e2E side_right e2))))) 
    E1 (cf1++c1) 
    E2 (cf2++c2) 
    Q ->
    (forall k (m1 m2:Mem.t k), 
     ipred P m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
    Equiv P 
    E1 ((If e1 then ct1 else cf1)::c1) 
    E2 ((If e2 then ct2 else cf2)::c2) 
    Q.
   Proof.
    unfold Equiv; intros.
    rewrite !ipred_pand in H, H0; rewrite !ipred_pnot in H0.
    rewrite !ipred_pexp_right,!ipred_pexp_left in H, H0.
    apply equiv_cond; trivial.
   Qed.

(* REMARK: To keep for the next revision of CertiCrypt
  Record prod_rel (A B:Type) (R:A -> B -> Prop) := mkPR
   { pr1 : A; pr2 : B; pr_prop : R pr1 pr2 }.

  Record lift2 (A B:Type) (R:A -> B -> Prop) (d:Distr (prod_rel R)) 
   (d1:Distr A) (d2:Distr B) : Prop :=
   { 
    l_fst2 : forall f : A -> U,
             (mu d) (fun x : prod_rel R => f (pr1 x)) == (mu d1) f;
    l_snd2 : forall f : B -> U,
             (mu d) (fun x : prod_rel R => f (pr2 x)) == (mu d2) f
   }.

  Definition distr_pr2p (A B:Type) (R:A -> B -> Prop) 
  (d:Distr (prod_rel R)) : Distr (A * B) :=
   Mlet d (fun pr => Munit (pr1 pr, pr2 pr)).

  Lemma lift2_range : forall A B (R:A -> B -> Prop) (d:Distr (prod_rel R)) d1 d2,
   lift2 d d1 d2 -> range (prodP R) (distr_pr2p d).
  Proof.
   intros; apply range_Mlet with (fun _ => True).
   apply range_True.
   unfold range; simpl; intros.
   apply H1; apply (pr_prop x).
  Qed.

  Lemma lift2_lift : forall (A B:Type) (R:A -> B -> Prop) (d:Distr (prod_rel R)) 
  (d1:Distr A) (d2:Distr B),
  lift2 d d1 d2 -> lift R (distr_pr2p d) d1 d2.
  Proof.
   unfold distr_pr2p; intros; constructor.
   intros; rewrite <- (l_fst2 H), Mlet_simpl.
   apply mu_stable_eq; refine (ford_eq_intro _); trivial.
   intros; rewrite <- (l_snd2 H), Mlet_simpl.
   apply mu_stable_eq; refine (ford_eq_intro _); trivial.
   apply lift2_range with (1:= H).
  Qed.

  Definition equiv2 (P:mem_rel) (E1:env) (c1:cmd) (E2:env) (c2:cmd) (Q:mem_rel) :=
   forall k (pr:prod_rel (P k)), 
   exists d, @lift2 _ _ (Q k) d ([[c1]] E1 (pr1 pr)) ([[c2]] E2 (pr2 pr)).

  Lemma equiv2_app : forall (P Q R:mem_rel) 
   (E:env) (c1 c2:cmd) (E':env) (c3 c4:cmd),
   equiv2 P E c1 E' c3 Q ->
   equiv2 Q E c2 E' c4 R -> equiv2 P E (c1 ++ c2) E' (c3 ++ c4) R.
  Proof.
   unfold equiv2; intros.
   destruct (H k pr) as (d, Hd).
   assert (W1:= H0 k); apply choice in W1; destruct W1 as (F, HF).
   exists (Mlet d F).
   constructor; intros; rewrite deno_app_elim, Mlet_simpl.
   rewrite <- (l_fst2 Hd).
   apply mu_stable_eq; refine (ford_eq_intro _); intros pr'.
   rewrite <- (l_fst2 (HF pr')).
   apply mu_stable_eq; refine (ford_eq_intro _); trivial.
   rewrite <- (l_snd2 Hd).
   apply mu_stable_eq; refine (ford_eq_intro _); intros pr'.
   rewrite <- (l_snd2 (HF pr')).
   apply mu_stable_eq; refine (ford_eq_intro _); trivial.
  Qed.

  Lemma equiv2_trans : forall (P1 P2 Q1 Q2 Q3:mem_rel) 
   (E1:env) (c1:cmd) (E2:env) (c2:cmd) (E3:env) (c3:cmd),
   refl_supMR2 P2 P1 ->
   (forall (k : nat) (x y z : Mem.t k), Q1 k x y -> Q2 k y z -> Q3 k x z) ->
   equiv2 P1 E1 c1 E2 c2 Q1 ->
   equiv2 P2 E2 c2 E3 c3 Q2 -> equiv2 P2 E1 c1 E3 c3 Q3.
  Proof.
   unfold equiv2; intros.
   assert (HP1 : P1 k (pr1 pr) (pr1 pr)).
     red in H; apply H with (pr2 pr); apply pr_prop.
   destruct (H1 k (mkPR (P1 k) _ _ HP1)) as (d, Hd); simpl in Hd.
   destruct (H2 k pr) as (d', Hd').
   exists (dd' (@mem_eqU k) (lift2_lift Hd) (lift2_lift Hd')).
*)

   Lemma dlist_ind2: forall (A:Type) 
    (P1 P2:A -> Type)
    (P:forall l, dlist P1 l -> dlist P2 l -> Prop),
     (forall x y:A, sumbool (x = y) (x <> y) ) ->
     P nil (dnil P1) (dnil P2) ->
     (forall a l (p1:P1 a) (p2:P2 a) (d1:dlist P1 l) (d2:dlist P2 l),
      P l d1 d2 -> P (a :: l) (dcons a p1 d1) (dcons a p2 d2)) ->
    forall (l:list A) (d1:dlist P1 l) (d2:dlist P2 l), P l d1 d2.
   Proof.
    induction d1; simpl; intros.
    generalize (dlist_nil d2); intros.
    inversion H1; subst; apply inj_pair2_eq_dec in H2; subst; trivial.
    apply list_eq_dec; trivial.
    generalize (dlist_cons d2); intros.
    destruct H1.
    destruct H1.
    inversion H1; subst; apply inj_pair2_eq_dec in H2; subst; trivial.
    apply H0.
    apply IHd1.
    apply list_eq_dec; trivial.
   Qed.

   Opaque pimplies forall_fresh_l forall_fresh_r.	 
	  	 
   Lemma var_dec : forall (a : T.type) (v1 v2 : Var.var a), sumbool (v1 = v2) (v1 <> v2).
   Proof.
     intros.
     generalize (Var.eqb_spec v1 v2).
     destruct (Var.eqb v1 v2); intros H.
     inversion H; subst; apply inj_pair2_eq_dec in H1; subst; auto.
     apply Teq_dec.
     right; intro Heq; elim H.
     rewrite Heq; trivial.
   Qed.
	 
   Definition geeq_mem (X:Vset.t) (k:nat) (m1 m2:Mem.t k) :=
    forall t (x:Var.var t), Var.is_global x -> ~Vset.mem x X -> m1 x = m2 x.

   Lemma mem_upd_paral_make_assoc :
    forall k (m1 m2:Mem.t k) l side tparams (params: var_decl tparams) targs (args:E.args targs) s,
    mem_upd_paral m1 m2 l (make_assoc_var_exp side params args s) = 
      mem_upd_paral m1 m2 l s.
   Proof.
    induction params;intros targs args;destruct args;simpl;trivial;intros.
    rewrite IHparams.
    unfold mem_upd_paral in *;simpl.
    destruct (mem_upd_para m1 m2 l s) as 
      ((m1',m2'),l');simpl;intros;subst.
    destruct side;trivial.
   Qed.

   Lemma mem_upd_para1_make_assoc2 :  
     forall k (m1 m2:Mem.t k) l tparams (params: var_decl tparams) targs (args:E.args targs) s,
    (mem_upd_para1 m1 m2 l (make_assoc_var_exp side_right params args s)) =
    (mem_upd_para1 m1 m2 l s).
   Proof.
    induction params;intros targs args;destruct args;simpl;trivial;intros.
    rewrite IHparams.
    unfold mem_upd_para1 in *;simpl.
    destruct (mem_upd_para m1 m2 l s) as 
      ((m1',m2'),l');simpl;intros;subst;trivial.
   Qed.
 
   Lemma mem_upd_para2_make_assoc1 :  
     forall k (m1 m2:Mem.t k) l tparams (params: var_decl tparams) targs (args:E.args targs) s,
    (mem_upd_para2 m1 m2 l (make_assoc_var_exp side_left params args s)) =
    (mem_upd_para2 m1 m2 l s).
   Proof.
    induction params;intros targs args;destruct args;simpl;trivial;intros.
    rewrite IHparams.
    unfold mem_upd_para2 in *;simpl.
    destruct (mem_upd_para m1 m2 l s) as 
      ((m1',m2'),l');simpl;intros;subst;trivial.
   Qed.

   Lemma get_arg_None : 
     forall tx (x:Var.var tx) tparams (params : var_decl tparams) targs (args:E.args targs),
     tparams = targs ->
     get_arg x params args = None ->
     ~DIn _ x params.
   Proof.
    induction params;intros targs args0;destruct args0;simpl;try discriminate;try tauto.
    intros Heq;inversion Heq;clear Heq;subst.
    generalize (IHparams _ args0 (eq_refl _)).
    destruct (get_arg x params args0);try discriminate.
    generalize (Var.veqb_spec_dep x p);destruct (Var.veqb x p);try tauto.
    intros Heq;inversion Heq;clear Heq;subst.
    apply T.inj_pair2 in H2;clear H1;subst.
    rewrite Teq_dep_refl;discriminate.
   Qed.

   Lemma make_assoc_not_in : 
    forall k (m1 m2:Mem.t k) l tx (x:Var.var tx) tparams (params : var_decl tparams) targs (args:E.args targs) s,
     tparams = targs ->
    ~ DIn tx x params ->
      (mem_upd_para1 m1 m2 l
        (make_assoc_var_exp side_left params args s)) x =
      (mem_upd_para1 m1 m2 l s) x.
   Proof.
    induction params;intros targs args;destruct args;try discriminate;simpl;intros;trivial.
    inversion H;clear H;subst;rewrite IHparams;try tauto.
    unfold mem_upd_para1;simpl.
    destruct (mem_upd_para m1 m2 l s) as ((m1',m2'),l');simpl.
    rewrite Mem.get_upd_diff;trivial.
    intros Heq;apply H0;inversion Heq;subst.
    apply T.inj_pair2 in H2;subst.
    left;destruct p;trivial.
   Qed.

    Lemma make_assoc_not_in2 : 
    forall k (m1 m2:Mem.t k) l tx (x:Var.var tx) tparams (params : var_decl tparams) targs (args:E.args targs) s,
     tparams = targs ->
    ~ DIn tx x params ->
      (mem_upd_para2 m1 m2 l
        (make_assoc_var_exp side_right params args s)) x =
      (mem_upd_para2 m1 m2 l s) x.
   Proof.
    induction params;intros targs args;destruct args;try discriminate;simpl;intros;trivial.
    inversion H;clear H;subst;rewrite IHparams;try tauto.
    unfold mem_upd_para2;simpl.
    destruct (mem_upd_para m1 m2 l s) as ((m1',m2'),l');simpl.
    rewrite Mem.get_upd_diff;trivial.
    intros Heq;apply H0;inversion Heq;subst.
    apply T.inj_pair2 in H2;subst.
    left;destruct p;trivial.
   Qed.

   Lemma get_arg_make_assoc : 
     forall k (m1 m2:Mem.t k) l tx (x:Var.var tx) tparams (params : var_decl tparams) targs (args:E.args targs) s,
     tparams = targs ->
     Vset.mem x (Vset_of_var_decl params) ->
     exists e, 
     get_arg x params args = Some e /\
     E.eval_expr e m1 = 
     (mem_upd_para1 m1 m2 l (make_assoc_var_exp side_left params args s) x).
   Proof.
    intros k m1 m2 l tx x tparams params targs args0 s Heq Hin;revert tx x Hin.
    refine (Vset_of_var_decl_ind _ _ _ ).
    intros t0 x Hin;revert tparams params targs args0 Heq Hin s;clear.
    induction params;intros targs args0;destruct args0;try discriminate;simpl;try tauto.
    intros Heq Hin s;inversion Heq;clear Heq;subst.
    case_eq (get_arg x params args0);intros.
    assert (W:= get_arg_Some _ _ _ H).
    destruct (IHparams _ args0 (refl_equal l1) W 
      ({|da_t := a0;da_a := (cast_var p a0) <1>;da_b := e2E side_left e |} :: s)) as (e1,(H1,H2)).
    rewrite H in H1;inversion H1;clear H1;subst.
    exists e1;auto.
    apply get_arg_None in H;trivial.
    rewrite make_assoc_not_in;trivial.
    destruct Hin;try tauto.
    inversion H0;clear H0;subst.
    clear H3;apply T.inj_pair2 in H4;subst.
     rewrite veqb_refl, Teq_dep_refl;exists e;split;trivial.
    unfold mem_upd_para1;simpl.
    destruct (mem_upd_para m1 m2 l s) as ((m1',m2'),l');simpl.
    assert (cast_var p a0 = p) by (destruct p;trivial).
    rewrite H0, Mem.get_upd_same.
    rewrite e2E_correct;trivial.
   Qed.
 
   Lemma get_arg_make_assoc2 : 
     forall k (m1 m2:Mem.t k) l tx (x:Var.var tx) tparams (params : var_decl tparams) targs (args:E.args targs) s,
     tparams = targs ->
     Vset.mem x (Vset_of_var_decl params) ->
     exists e, 
     get_arg x params args = Some e /\
     E.eval_expr e m2 = 
     (mem_upd_para2 m1 m2 l (make_assoc_var_exp side_right params args s) x).
   Proof.
    intros k m1 m2 l tx x tparams params targs args0 s Heq Hin;revert tx x Hin.
    refine (Vset_of_var_decl_ind _ _ _ ).
    intros t0 x Hin;revert tparams params targs args0 Heq Hin s;clear.
    induction params;intros targs args0;destruct args0;try discriminate;simpl;try tauto.
    intros Heq Hin s;inversion Heq;clear Heq;subst.
    case_eq (get_arg x params args0);intros.
    assert (W:= get_arg_Some _ _ _ H).
    destruct (IHparams _ args0 (refl_equal l1) W 
      ({|da_t := a0;da_a := (cast_var p a0) <2>;da_b := e2E side_right e |} :: s)) as (e1,(H1,H2)).
    rewrite H in H1;inversion H1;clear H1;subst.
    exists e1;auto.
    apply get_arg_None in H;trivial.
    rewrite make_assoc_not_in2;trivial.
    destruct Hin;try tauto.
    inversion H0;clear H0;subst.
    clear H3;apply T.inj_pair2 in H4;subst.
     rewrite veqb_refl, Teq_dep_refl;exists e;split;trivial.
    unfold mem_upd_para2;simpl.
    destruct (mem_upd_para m1 m2 l s) as ((m1',m2'),l');simpl.
    assert (cast_var p a0 = p) by (destruct p;trivial).
    rewrite H0, Mem.get_upd_same.
    rewrite e2E_correct;trivial.
   Qed.

   Lemma sfv_make_assoc : 
     forall side tparams (params : var_decl tparams) targs (args:E.args targs) s,
     sfv (make_assoc_var_exp side params args s) [=] sfv s.
   Proof.
    induction params;intros targs args;destruct args;simpl;auto with set.
    intros;rewrite IHparams;simpl.
    rewrite lfv_e2E;auto with set.
   Qed.
 
   Transparent forall_fresh_r.   

   Lemma forall_fresh_r_nil : forall k (m1 m2:Mem.t k) l lf P,
     peval m1 m2 l (forall_fresh_r P nil lf) ->
     peval m1 m2 l P.
   Proof. trivial. Qed.

   Lemma forall_fresh_r_cons : forall k (m1 m2:Mem.t k) l lv lf t (x:Var.var t) P,
     peval m1 m2 l (forall_fresh_r P (Var.mkV x::lv) lf) ->
     forall v:T.interp k t,
      peval m1 (m2{!x <-- v!}) l (forall_fresh_r P lv (tl lf)).
   Proof.
    simpl;intros k m1 m2 l lv lf t x P.
    match goal with |- context [if ?test then _ else _] => case_eq test;intros Heq1 end;simpl;[tauto | ].
    intros H x0;assert (W:= H x0).
    rewrite orb_false_iff in Heq1;destruct Heq1.
    rewrite psubst_correct in W.
    simpl in W;rewrite assoc_same in W;[ | apply veqb_refl].
    rewrite peval_eq_assoc with (l2 := l) in W;trivial.
    intros;assoc_case.
    rewrite <- H3, H2 in H1;discriminate.
    refine (disjoint_singleton (Var.Lvar t (hd 1%positive lf)) _ H0).
   Qed.

   Opaque forall_fresh_r.

   Transparent forall_fresh_l.   

   Lemma forall_fresh_l_nil : forall k (m1 m2:Mem.t k) l lf  P,
     peval m1 m2 l (forall_fresh_l P nil lf) ->
     peval m1 m2 l P.
   Proof. trivial. Qed.

   Lemma forall_fresh_l_cons : forall k (m1 m2:Mem.t k) l lv lf t (x:Var.var t) P,
     peval m1 m2 l (forall_fresh_l P (Var.mkV x::lv) lf) ->
     forall v:T.interp k t,
      peval (m1{!x <-- v!}) m2 l (forall_fresh_l P lv (tl lf)).
   Proof.
    simpl;intros k m1 m2 l lv lf t x P.
    match goal with |- context [if ?test then _ else _] => case_eq test;intros Heq1 end;simpl;[tauto | ].
    intros H x0;assert (W:= H x0).
    rewrite orb_false_iff in Heq1;destruct Heq1.
    rewrite psubst_correct in W.
    simpl in W;rewrite assoc_same in W;[ | apply veqb_refl].
    rewrite peval_eq_assoc with (l2 := l) in W;trivial.
    intros;assoc_case.
    rewrite <- H3, H2 in H1;discriminate.
    refine (disjoint_singleton (Var.Lvar t (hd 1%positive lf)) _ H0).
   Qed.

   Opaque forall_fresh_l.

   Lemma cast_var_eq : forall t (x:Var.var t), cast_var x t = x.
   Proof. destruct x;simpl;trivial. Qed.

   Lemma wp_call_correct : forall fresh1 fresh2 info c1 c2 Q c1' c2' Q',
    wp_call fresh1 fresh2 info c1 c2 Q = Tuple3 c1' c2' Q' ->
     forall P, 
      Equiv P E1 c1' E2 c2' Q' ->
      Equiv P E1 c1 E2 c2 Q.
   Proof.
    intros fresh1 fresh2 info c1 c2 Q c1' c2' Q'.
    unfold wp_call.
    destruct info as (t, pre, f1, f2, post, equ).
    case_eq (rev c1); [discriminate | intros i tl1 Heq1].
    destruct i; try discriminate.
    rename v into x1; rename f into f1'; rename a into args1.
    case_eq (rev c2); [discriminate | intros i tl2 Heq2].
    destruct i; try discriminate.
    rename v into x2; rename f into f2'; rename a into args2.
    generalize (Proc.eqb_spec_dep f1 f1'); 
     destruct (Proc.eqb f1 f1'); intros Heq; [ | discriminate].
    inversion Heq; clear Heq; subst.
    clear H1; apply T.inj_pair2 in H2; subst.
    generalize (Proc.eqb_spec_dep f2 f2'); 
    destruct (Proc.eqb f2 f2'); intros Heq; [ | discriminate].
    inversion Heq; clear Heq; subst.
    clear H1; apply T.inj_pair2 in H2; subst.
    destruct (pi1 f1'); [ | discriminate].
    destruct (pi2 f2'); [ | discriminate].
    generalize (pdepend_correct Q);destruct (pdepend Q) as (QX1, QX2); intros HdepQ.
    simpl.
    match goal with |- context [if ?test then _ else _] => case_eq test;intros HmemQ end;simpl;[discriminate| ].    
    simpl; intros Heq; inversion Heq; clear Heq; subst; intros.
    rewrite <- (rev_involutive c1), <- (rev_involutive c2), Heq1, Heq2; simpl.
    destruct equ as (res1, res2, Hequ, Hpre, Hpost); simpl in H, HmemQ.
    apply equiv_app with (1:= H); clear H Heq1 Heq2.
    match goal with 
     |- equiv (ipred (pand _ (forall_fresh_r (forall_fresh_l ?P _ _) _ _))) 
      _ _ _ _ _ => set (P0 := P) 
    end.
    match goal with
     |- equiv (ipred (pand _ ?P)) _ _ _ _ _ => set (P1 := P) 
    end.
    rewrite ipred_pand.
    unfold Equiv, equiv in *; intros.
    destruct (Hequ k) as (d, Hd); clear Hequ.
    exists (fun m1 m2 => 
     Mlet (d (init_mem E1 f1' args1 m1) (init_mem E2 f2' args2 m2))
     (fun p => Munit (return_mem E1 x1 f1' m1 (fst p), 
               return_mem E2 x2 f2' m2 (snd p)))).
    intros m1 m2 (Hparams, HpostQ).
    repeat rewrite deno_call.
    assert (ipred pre (init_mem E1 f1' args1 m1) (init_mem E2 f2' args2 m2)).
    unfold ipred in Hparams.
    rewrite psubst_para_correct in Hparams.
    rewrite !mem_upd_paral_make_assoc in Hparams;unfold mem_upd_paral in Hparams;simpl in Hparams.
    unfold only_params_or_global in Hpre.
    refine (pdepend_correct pre _ _ Hparams).
 
    destruct (pdepend pre) as (X1,X2); rewrite is_true_andb in Hpre;destruct Hpre;simpl.
    red;intros; case_eq (Var.is_global x);intros.
    rewrite init_mem_global;trivial.
    rewrite make_assoc_not_in;trivial.
    rewrite mem_upd_para1_make_assoc2;trivial.
    unfold proc_params;destruct (E1 f1');simpl.
    intros Hin;apply d_all_local0 in Hin.
    unfold Var.is_global in H2; unfold Var.vis_local in Hin.
    simpl in H2, Hin;rewrite H2 in Hin;discriminate.
    rewrite <- negb_true_iff in H2;assert (W:= get_locals_complete _ _ H1 H2).
    assert (Hin := Vset.subset_correct H _ W);clear W.
    destruct (get_arg_make_assoc m1 m2 nil x (proc_params E1 f1') args1  
       (make_assoc_var_exp side_right (proc_params E2 f2') args2 nil)) as (e1,(Hget,He1));trivial.
    rewrite <- He1.
    generalize (lookup_init_mem E1 f1' args1 m1 x);rewrite Hget;auto.
 
    destruct (pdepend pre) as (X1,X2); rewrite is_true_andb in Hpre;destruct Hpre;simpl.
    red;intros; case_eq (Var.is_global x);intros.
    rewrite mem_upd_para2_make_assoc1.
    rewrite init_mem_global;trivial.
    rewrite make_assoc_not_in2;trivial.
    unfold proc_params;destruct (E2 f2');simpl.
    intros Hin;apply d_all_local0 in Hin.
    unfold Var.is_global in H2; unfold Var.vis_local in Hin.
    simpl in H2, Hin;rewrite H2 in Hin;discriminate.
    rewrite <- negb_true_iff in H2;assert (W:= get_locals_complete _ _ H1 H2).
    assert (Hin := Vset.subset_correct H0 _ W);clear W.
    rewrite mem_upd_para2_make_assoc1. 
    destruct (get_arg_make_assoc2 m1 m2 nil x (proc_params E2 f2') args2 nil) as (e1,(Hget,He1));trivial.
    rewrite <- He1.
    generalize (lookup_init_mem E2 f2' args2 m2 x);rewrite Hget;auto.

    apply disjoint_subset_r with Vset.empty.
    rewrite !sfv_make_assoc;compute;trivial.
    apply VsetP.disjoint_sym;trivial.

    apply Hd in H; clear Hd Hparams.
    clear c1 c2.
    set (c1 := proc_body E1 f1') in *.
    set (c2:= proc_body E2 f2') in *.
    rename m1 into mm1; rename m2 into mm2.
    set (m1 := init_mem E1 f1' args1 mm1) in *.
    set (m2 := init_mem E2 f2' args2 mm2) in *.
    assert (Gmod1 := mod_global p); assert (Gmod2 := mod_global p0).
    assert (Hmod1 := mod_spec p); assert (Hmod2 := mod_spec p0).
    destruct Hmod1 as (L1, (HL1, Hmod1)).
    destruct Hmod2 as (L2, (HL2, Hmod2)).
    set (X1:= Vset.union L1 (pi_mod p)) in *.
    set (X2:= Vset.union L2 (pi_mod p0)) in *.
    assert (exists d, 
     lift (fun m1' m2' => m1' = m2' /\ eeq_mem X1 m1 m1') d 
     ([[ c1 ]] E1 m1) ([[ c1 ]] E1 m1)).
     exists (Mlet ([[ c1 ]] E1 m1) (fun m => Munit (m,m))).
     constructor; intros.
     rewrite Mlet_simpl; apply mu_stable_eq; refine (ford_eq_intro _); trivial.
     rewrite Mlet_simpl; apply mu_stable_eq; refine (ford_eq_intro _); trivial.
     apply range_Mlet with (1:= Hmod1 k m1); red; simpl; intros.
     apply H1; split; auto.
    destruct H0 as (d1,Hd1).
    assert (Hdec1 : forall m', sumbool (eeq_mem X1 m1 m') (~eeq_mem X1 m1 m')).
     intros; apply eeq_mem_dec'.
    assert (HH:= lift_trans_l (eeq_mem X1 m1) Hdec1 Hd1 H); clear H Hdec1 Hd1 d1. 
     apply lift_sym in HH.
    assert (exists d, 
     lift (fun m1' m2' => m1' = m2' /\ eeq_mem X2 m2 m1') d 
     ([[ c2 ]] E2 m2) ([[ c2 ]] E2 m2)).
     exists (Mlet ([[ c2 ]] E2 m2) (fun m => Munit (m,m))).
     constructor; intros.
     rewrite Mlet_simpl; apply mu_stable_eq; refine (ford_eq_intro _); trivial.
     rewrite Mlet_simpl; apply mu_stable_eq; refine (ford_eq_intro _); trivial.
     apply range_Mlet with (1:= Hmod2 k m2); red; simpl; intros.
     apply H0; split; auto.
    destruct H as (d2,Hd2).
    assert (Hdec2 : forall m', sumbool (eeq_mem X2 m2 m') (~eeq_mem X2 m2 m')).
     intros; apply eeq_mem_dec'.
    assert (HHH:= lift_trans_l (eeq_mem X2 m2) Hdec2 Hd2 HH); 
     clear HH Hdec2 Hd2 d2.
    apply lift_sym in HHH.
    match type of HHH with lift _ ?d' _ _ => assert (d' == d m1 m2) end.
    refine (ford_eq_intro _); intros f; rewrite !Mlet_simpl.
    apply mu_stable_eq; refine (ford_eq_intro _); intros (x,y); trivial.
    rewrite H in HHH; clear H.
    apply lift_Mlet with (1:= HHH); clear HHH.
    intros m1' m2' ((Hwppost, Heeq1), Heeq2); apply lift_unit.


    generalize HmemQ HdepQ Hwppost HpostQ Heeq1 Heeq2 HL1 HL2 Hpost; unfold P1, P0, ipred; clear; intros.
    unfold wp_return in Hwppost.
    apply psubst_correct in Hwppost; simpl in Hwppost.
    apply psubst_correct in Hwppost; simpl in Hwppost.
    rewrite !e2E_correct in Hwppost; simpl in Hwppost.
    assert (geeq_mem (pi_mod p) mm1 m1').
     red;intros; rewrite <- Heeq1.
     unfold m1;rewrite init_mem_global;trivial.
     unfold X1;rewrite VsetP.union_spec;intros [Hin | Hin];try tauto.
     apply HL1 in Hin;unfold Var.is_local in Hin;rewrite H in Hin;discriminate.
    clear Heeq1; assert (geeq_mem (pi_mod p0) mm2 m2').
     red;intros; rewrite <- Heeq2.
     unfold m2;rewrite init_mem_global;trivial.
     unfold X2;rewrite VsetP.union_spec;intros [Hin | Hin];try tauto.
     apply HL2 in Hin;unfold Var.is_local in Hin;rewrite H0 in Hin;discriminate.
    clear Heeq2 m1 m2 X1 X2.
    assert (return_mem E1 x1 f1' mm1 m1' = mm1{!pi_mod p <<- m1'!}{!x1 <-- E.eval_expr (proc_res E1 f1') m1'!}).
      apply Mem.eq_leibniz;red;intros.
      destruct (Var.eq_dec x1 x);subst.
      rewrite return_mem_dest, Mem.get_upd_same;trivial.
      simpl.
      destruct x; rewrite Mem.get_upd_diff;trivial.
      case_eq (Var.is_global v);intros.
      rewrite return_mem_global;trivial.
      case_eq (Vset.mem v (pi_mod p));intros.
      rewrite update_mem_in;trivial.
      assert (~ Vset.mem v (pi_mod p)) by (rewrite H2;discriminate).
      symmetry;rewrite update_mem_notin;trivial.
      apply H;trivial.
      rewrite return_mem_local;trivial.
      rewrite update_mem_notin;trivial.
      intros Hin;apply mod_global in Hin;rewrite H1 in Hin;discriminate.
      unfold Var.is_local;rewrite H1;trivial.
    rewrite H1;clear H1.
    assert (return_mem E2 x2 f2' mm2 m2' = mm2{!pi_mod p0 <<- m2'!}{!x2 <-- E.eval_expr (proc_res E2 f2') m2'!}).
      apply Mem.eq_leibniz;red;intros.
      destruct (Var.eq_dec x2 x);subst.
      rewrite return_mem_dest, Mem.get_upd_same;trivial.
      simpl.
      destruct x; rewrite Mem.get_upd_diff;trivial.
      case_eq (Var.is_global v);intros.
      rewrite return_mem_global;trivial.
      case_eq (Vset.mem v (pi_mod p0));intros.
      rewrite update_mem_in;trivial.
      assert (~ Vset.mem v (pi_mod p0)) by (rewrite H2;discriminate).
      symmetry;rewrite update_mem_notin;trivial.
      apply H0;trivial.
      rewrite return_mem_local;trivial.
      rewrite update_mem_notin;trivial.
      intros Hin;apply mod_global in Hin;rewrite H1 in Hin;discriminate.
      unfold Var.is_local;rewrite H1;trivial.
     rewrite H1;clear H1 HL1 HL2 L1 L2.
     set (Q' := (forall_fresh_r
                      (forall_fresh_l
                         (pimplies post
                            (psubst (psubst Q x1 <1> (cast_var res1 t1) <1>)
                               x2 <2> (cast_var res2 t1) <2>))
                         (Var.mkV (cast_var res1 t1) :: nil) 
                         (map get_pos fresh1)) (Var.mkV (cast_var res2 t1) :: nil)
                      (map get_pos fresh2))) in HpostQ.
     generalize (tl (map get_pos fresh2)) HpostQ;clear HpostQ;simpl.
     revert mm2 H0;induction (pi_mod p0).
     intros mm2 Hgeeq2 _l1 W;apply forall_fresh_r_nil in W.
     clear _l1;revert W; generalize (tl (map get_pos fresh1));revert mm1 H.
     induction (pi_mod p);simpl.
     intros mm1 Hgeeq1 _lf W;apply forall_fresh_l_nil in W;unfold Q' in W.
     apply forall_fresh_r_cons with (v :=  E.eval_expr (proc_res E2 f2') m2') in W.
     apply forall_fresh_r_nil in W.
     apply forall_fresh_l_cons with (v :=  E.eval_expr (proc_res E1 f1') m1') in W.
     apply forall_fresh_l_nil in W.
     rewrite peval_pimplies, !cast_var_eq in W.
     assert
       ( peval (mm1 {!res1 <-- E.eval_expr (proc_res E1 f1') m1'!})
            (mm2 {!res2 <-- E.eval_expr (proc_res E2 f2') m2'!}) nil post).
      refine (pdepend_correct _ _ _ Hwppost);intros tx x Hin.
      destruct (Var.eq_dec x res1).
      inversion e;clear e;subst.
      apply T.inj_pair2 in H1;subst.
      rewrite !Mem.get_upd_same;trivial.
      rewrite !Mem.get_upd_diff;auto.
      symmetry;apply Hgeeq1;[ | discriminate].
      unfold only_global_or_res in Hpost.
      destruct (pdepend post);simpl in *.
      rewrite is_true_andb in Hpost;destruct Hpost.
      destruct x;trivial.
      assert (Hl:= get_locals_complete _ _ Hin (refl_equal _)).
      apply Vset.subset_correct with (x := Var.mkV (Var.Lvar t3 p1)) in H;trivial.
      apply Vset.singleton_complete in H;elim n.
      inversion H;trivial.
      destruct (Var.eq_dec x res2).
      inversion e;clear e;subst.
      apply T.inj_pair2 in H1;subst.
      rewrite !Mem.get_upd_same;trivial.
      rewrite !Mem.get_upd_diff;auto.
      symmetry;apply Hgeeq2;[ | discriminate].
      unfold only_global_or_res in Hpost.
      destruct (pdepend post);simpl in *.
      rewrite is_true_andb in Hpost;destruct Hpost.
      destruct x;trivial.
      assert (Hl:= get_locals_complete _ _ Hin (refl_equal _)).
      apply Vset.subset_correct with (x := Var.mkV (Var.Lvar t3 p1)) in H0;trivial.
      apply Vset.singleton_complete in H0;elim n.
      inversion H0;trivial.
     apply W in H;clear W.
     rewrite !psubst_correct in H.
     simpl in H.
     rewrite !Mem.get_upd_same in H.
     rewrite orb_false_iff in HmemQ;destruct HmemQ.
     apply HdepQ with (3:= H);simpl;red;intros.
     destruct (Var.eq_dec x1 x).
     inversion e;clear e;subst;rewrite !Mem.get_upd_same;trivial.
     rewrite !Mem.get_upd_diff;trivial.
     intros Heq;inversion Heq;clear Heq;subst.
     apply T.inj_pair2 in H5;subst.
     rewrite cast_var_eq, H2 in H0;discriminate.
     destruct (Var.eq_dec x2 x).
     inversion e;clear e;subst;rewrite !Mem.get_upd_same;trivial.
     rewrite !Mem.get_upd_diff;trivial.
     intros Heq;inversion Heq;clear Heq;subst.
     apply T.inj_pair2 in H5;subst.
     rewrite cast_var_eq, H2 in H1;discriminate.
     apply VsetP.disjoint_sym;unfold lfv;simpl;trivial.
     apply VsetP.disjoint_sym;unfold lfv;simpl;trivial.
     (* cons for mm1 *)
     intros mm1 Hgeeq1 l W.
     destruct a.
     apply forall_fresh_l_cons with (v:= m1' v) in W.
     apply IHt0 with (l := tl l);trivial.
     red;intros.
     destruct (Var.eq_dec v x).
     inversion e;clear e;subst.
     apply T.inj_pair2 in H3;subst;rewrite Mem.get_upd_same;trivial.
     rewrite Mem.get_upd_diff;trivial.
     apply Hgeeq1;[ trivial | ].
     simpl;generalize (VarP.Edec.eqb_spec x v);destruct (VarP.Edec.eqb x v);auto.
     (* cons for mm2 *)
     intros mm2 Hgeeq2 fresh W.
     destruct a;simpl.
     apply forall_fresh_r_cons with (v:= m2' v) in W.
     apply IHt0 with (l := tl fresh);trivial.
     red;intros.
     destruct (Var.eq_dec v x).
     inversion e;clear e;subst.
     apply T.inj_pair2 in H4;subst;rewrite Mem.get_upd_same;trivial.
     rewrite Mem.get_upd_diff;trivial.
     apply Hgeeq2;[ trivial | ].
     simpl;generalize (VarP.Edec.eqb_spec x v);destruct (VarP.Edec.eqb x v);auto.

    unfold Vset.disjoint; rewrite lfv_e2E; apply VsetP.disjoint_sym; auto with set.
    unfold Vset.disjoint; rewrite lfv_e2E; apply VsetP.disjoint_sym; auto with set.
   Qed.

   Lemma peval_notfv : forall k (m1 m2:Mem.t k) t (x:Var.var t) x0 l Q ,
    ~ Vset.mem x (pfv Q) ->
    (peval m1 m2 ({| t := t; var := x; val := x0 |} :: l) Q <-> peval m1 m2 l Q).
   Proof.
    intros; apply peval_eq_assoc; intros; assoc_case; subst.
    elim H; trivial.
   Qed.

   Lemma disjoint_pbind : forall t (x:Var.var t) Q,
    ~ Vset.mem x (pbind Q) ->
    Vset.disjoint (pbind Q) (lfv (VarLogic x)).
   Proof.
    intros; unfold lfv; simpl.
    apply VsetP.disjoint_sym.
    unfold Vset.disjoint; simpl.
    rewrite not_is_true_false in H; rewrite H; trivial.
   Qed.

   Lemma Equiv_random_l_weak : forall E E' t (x:Var.var t) (v:Var.var t) s Q, 
    ~Vset.mem x (pbind Q) ->
    ~Vset.mem x (pfv Q) ->
    Equiv (pforall x (psubst Q v <1> (VarLogic x))) 
    E [v <$- s] E' nil 
    Q.
   Proof.
    unfold Equiv, equiv; intros.
    exists (fun m1 m2 => Mlet (([[ [v <$- s] ]]) E m1)
     (fun m1' => Munit (m1',m2))); intros.
    constructor; intros; try rewrite Mlet_simpl.
    apply mu_stable_eq; refine (ford_eq_intro _ ); trivial.
    rewrite deno_nil_elim.
    transitivity  (mu ([[ [v<$-s] ]] E m1) (fcte _ (f m2))).
    apply mu_stable_eq; refine (ford_eq_intro _ ); trivial.
    apply mu_cte_eq; apply lossless_random.
    rewrite deno_random, Mcomp.
    apply range_Mlet with (fun v => True);[ apply range_True | ].
    intros x0 _; unfold range; intros; simpl.
    apply H2; red; simpl; clear H2; unfold ipred in *; simpl in H1.
    assert (W:= @psubst_correct k m1 m2 _ (v<1>) (VarLogic x) 
     Q ({| t := t0; var := x; val := x0 |} :: nil)).
    simpl in W; rewrite assoc_same in W;[ | apply veqb_refl].
    rewrite <- (peval_notfv (m1 {!v <-- x0!}) m2 x x0 nil Q H0), <- W; trivial.
    apply disjoint_pbind; trivial.
   Qed.

   Lemma Equiv_random_r_weak : forall E E' t (x:Var.var t) (v:Var.var t) s Q, 
    ~Vset.mem x (pbind Q) ->
    ~Vset.mem x (pfv Q) ->
    Equiv (pforall x (psubst Q v <2> (VarLogic x))) 
    E nil E' [v <$- s] 
    Q.
   Proof.
    unfold Equiv, equiv; intros.
    exists (fun m1 m2 => Mlet (([[ [v <$- s] ]]) E' m2)
     (fun m2' => Munit (m1,m2'))); intros.
    constructor; intros; try rewrite Mlet_simpl.
    rewrite deno_nil_elim.
    transitivity  (mu ([[ [v<$-s] ]] E' m2) (fcte _ (f m1))).
    apply mu_stable_eq; refine (ford_eq_intro _ ); trivial.
    apply mu_cte_eq; apply lossless_random.
    apply mu_stable_eq; refine (ford_eq_intro _ ); trivial.
    rewrite deno_random, Mcomp.
    apply range_Mlet with (fun v => True);[ apply range_True | ].
    intros x0 _; unfold range; intros; simpl.
    apply H2; red; simpl; clear H2; unfold ipred in *; simpl in H1.
    assert (W:= @psubst_correct k m1 m2 _ (v<2>) (VarLogic x) 
     Q ({| t := t0; var := x; val := x0 |} :: nil)).
    simpl in W; rewrite assoc_same in W;[ | apply veqb_refl].
    rewrite <- (peval_notfv m1 (m2 {!v <-- x0!}) x x0 nil Q H0), <- W; trivial.
    apply disjoint_pbind; trivial.
   Qed.

   Lemma Z_support_bounded : forall k (e1 e2:E.expr T.Zt) (m:Mem.t k) v, 
    In v (Z_support (E.eval_expr e1 m) (E.eval_expr e2 m)) ->
    (E.eval_expr e1 m <= E.eval_expr e2 m)%Z ->
    (E.eval_expr e1 m <= v <= E.eval_expr e2 m)%Z.
   Proof.
    unfold Z_support; intros.
    assert (W:= Zle_imp_le_bool _ _ H0); rewrite W in H.
    apply In_seqZ_le in H; clear W.
    rewrite inj_Zabs_nat in H.
    rewrite Zabs_eq in H; omega.
   Qed.

   Lemma wp_rnd_disj_correct : forall P x b c1 c2 Q c1' c2' Q',
    wp_rnd_disj x b c1 c2 Q = Tuple3 c1' c2' Q' ->
    Equiv P E1 c1' E2 c2' Q' ->
    Equiv P E1 c1 E2 c2 Q.
   Proof.
    unfold wp_rnd_disj; intros P x b c1 c2 Q c1' c2' Q'.
    case_eq (rev (if b then c1 else c2));[ discriminate | intros i tl Heqr].
    destruct i; try discriminate.
    destruct b0; try discriminate.
    case_eq (bound_random b s (VarLogic (cast_var x t0)) Ptrue); 
     intros cond bound Hbr.
    match goal with |- (if ?T then _ else _) = _ -> _ -> _ => 
     case_eq T;[ discriminate | ] end.
    intros Hmem Heq HE; injection Heq; clear Heq; intros; subst.
    assert ((if b then c1 else c2) = rev tl ++ [v <$- s]).
    rewrite <- (rev_involutive (if b then c1 else c2)), Heqr; trivial.
    rewrite orb_false_iff in Hmem; destruct Hmem as (Hmem1, Hmem2).
    rewrite <- not_is_true_false in Hmem1, Hmem2.
    clear Heqr; destruct b; subst;
     [rewrite (app_nil_end c2) | rewrite (app_nil_end c1)]; 
     apply equiv_app with (1:= HE); clear HE.
    (* b = side_left *)
    revert t0 s v Hbr Hmem1 Hmem2.
    unfold bound_random; destruct s; intros v Hbr Hmem1 Hmem2;
     injection Hbr; clear Hbr; intros; subst;
      try (rewrite pand_Ptrue, pimplies_Ptrue; apply Equiv_random_l_weak; trivial).
    (* bound for Z *)
    eapply equiv_strengthen;[ | apply equiv_random_l].
    unfold ipred; simpl; intros k m1 m2 (Hcond, Hf) v0 Hin.
    assert (W:= Hf v0); rewrite peval_pimplies in W.
    assert (W1:= @psubst_correct k m1 m2 _ (v<1>) (VarLogic (cast_var x T.Zt)) Q 
     ({| t := T.Zt; var := cast_var x T.Zt; val := v0 |} :: nil)).
    simpl in W1; rewrite assoc_same in W1; [ | apply veqb_refl].
    rewrite <- (peval_notfv (m1 {!v <-- v0!}) m2 (cast_var x T.Zt) v0 nil Q), 
            <- W1; 
     trivial; [ | apply disjoint_pbind]; trivial.
    apply W; revert Hcond; simpl; 
     rewrite assoc_same, !e2E_correct; simpl; intros;[ | apply veqb_refl].
    apply Z_support_bounded; trivial.
    (* b = side_right *)
    revert t0 s v Hbr Hmem1 Hmem2.
    unfold bound_random; destruct s; intros v Hbr Hmem1 Hmem2;
     injection Hbr; clear Hbr; intros; subst;
      try (rewrite pand_Ptrue, pimplies_Ptrue; apply Equiv_random_r_weak; trivial).
    (* bound for Z *)
    eapply equiv_strengthen;[ | apply equiv_random_r].
    unfold ipred; simpl; intros k m1 m2 (Hcond, Hf) v0 Hin.
    assert (W:= Hf v0); rewrite peval_pimplies in W.
    assert (W1:= @psubst_correct k m1 m2 _ (v<2>) (VarLogic (cast_var x T.Zt)) Q 
     ({| t := T.Zt; var := cast_var x T.Zt; val := v0 |} :: nil)).
    simpl in W1; rewrite assoc_same in W1;[ | apply veqb_refl].
    rewrite <- (peval_notfv m1 (m2 {!v <-- v0!}) (cast_var x T.Zt) v0 nil Q),
            <- W1; 
            trivial; [ | apply disjoint_pbind]; trivial.
    apply W; revert Hcond; simpl; rewrite assoc_same, !e2E_correct; 
     simpl; intros; [ | apply veqb_refl].
    apply Z_support_bounded; trivial.
   Qed.

   Lemma equiv_random_permut_r : forall (Q:mem_rel) E1 E2 t (x1 x2:Var.var t) 
    (f:forall k, Mem.t k -> Mem.t k -> T.interp k t -> T.interp k t) 
    (d1 d2:E.support t),
    equiv (transpR (permut_support (fun k m2 m1 v => f k m1 m2 v) d2 d1) /-\ 
     (fun k m1 m2 => 
      forall v, In v (E.eval_support d1 m1) -> 
       Q k (m1{!x1 <-- v!}) (m2{!x2 <-- f k m1 m2 v!})))
    E1 [x1 <$- d1] E2 [x2<$-d2] Q.
   Proof. 
    intros; apply equiv_sym_transp.
    eapply equiv_strengthen;
     [ | apply equiv_random_permut with (f:=fun k m1 m2 v => @f k m2 m1 v) ].
    unfold transpR; intros k m1 m2 (H1, H2); split; auto.
   Qed.

   Lemma peval_peq: forall (t:T.type) (e1 e2:Exp t) (k:nat) (m1 m2:Mem.t k) l,
    peval m1 m2 l (peq e1 e2) <-> eeval m1 m2 l e1 = eeval m1 m2 l e2.
   Proof.
    unfold peq; intros.
    generalize (exp_eqb_spec e1 e2); destruct (exp_eqb e1 e2); simpl; intros.
    inversion H; subst; apply inj_pair2_eq_dec in H2; subst; trivial; try tauto.
    apply Teq_dec.
    tauto.
   Qed.

   Lemma PermutP_NoDup_involutive : forall (T:Type) (f f_inv:T -> T) (l:list T),
    NoDup l ->
    (forall x : T, In x l -> f (f x) = x) ->
    (forall x : T, In x l -> In (f x) l) ->
    PermutP (fun v1 v2 : T => v1 = f v2) l l.
   Proof.
    intros.
    apply PermutP_NoDup with (f_inv := f); auto.
   Qed.

   Lemma wp_rnd_bij_correct : forall r d P c1 c2 Q c1' c2' Q',
    wp_rnd_bij r d c1 c2 Q = Tuple3 c1' c2' Q' ->
    Equiv P E1 c1' E2 c2' Q' -> 
    Equiv P E1 c1 E2 c2 Q.
   Proof.
    intros r d P c1 c2 Q c1' c2' Q'; unfold  wp_rnd_bij.
    case_eq (rev c1); [discriminate | intros i rc1' Heq1].
    destruct i; try discriminate.
    destruct b as [ | t1 y1 d1]; [ discriminate | ].
    case_eq (rev c2); [discriminate | intros i rc2' Heq2].
    destruct i; try discriminate.
    destruct b as [ | t2 y2 d2]; [ discriminate | ].
    case_eq (is_uniform d1); intros Hd1; simpl;[ | discriminate].
    case_eq (is_uniform d2); intros Hd2; simpl;[ | discriminate].
    destruct (T.eq_dec t1 t2); [subst | discriminate].
    case_eq (bound_random side_right d2 (VarLogic (cast_var r t2)) 
     (if is_full d2 then Ptrue else Pfalse)); 
     intros cond1 bound Hbound.
    case_eq (check_bij y2 (cast_var r t2) d2 d); intros cond finvx Hbij. 
    destruct cond as [cond fx].
    match goal with 
     |- (if ?T then _ else _) = _ -> _ -> _ => case_eq T; [ discriminate | ] 
    end. 
    intros Hmem Heq; inversion Heq; clear Heq; subst; intros.
    apply orb_false_iff in Hmem; destruct Hmem as [Hmem Hmem4].
    apply orb_false_iff in Hmem; destruct Hmem as [Hmem Hmem3].
    apply orb_false_iff in Hmem; destruct Hmem as [Hmem Hmem2].
    apply orb_false_iff in Hmem; destruct Hmem as [Hmem0 Hmem1].
    assert (c2 = rev rc2' ++ [ y2 <$- d2 ]).
    rewrite <- (rev_involutive c2), Heq2; trivial.
    assert (c1 = rev rc1' ++ [ y1 <$- d1 ]).
    rewrite <- (rev_involutive c1), Heq1; trivial.
    clear Heq1 Heq2; subst.
    apply equiv_app with (1:=H); clear H.
    rewrite !ipred_pand.
    eapply equiv_strengthen; [ | apply equiv_random_permut_r with 
     (f := fun k m1 m2 v => eeval m1 m2 (LVV k (cast_var r t2) v :: nil) fx)].
    intros k m1 m2 (Heqr, (Hcond1, Hforall)).
    unfold ipred in Hforall; simpl in Hforall.

    assert (forall t1 d1 t2 d2, ipred (wp_eq_random d1 d2) m1 m2 ->
     eq_dep T.type (fun t => list (T.interp k t)) t1 
     (E.eval_support d1 m1) t2 (E.eval_support d2 m2)).
    clear; destruct d1; destruct d2; simpl;
     match goal with 
      | |- ipred Pfalse m1 m2 -> _ => intros Hf; elim Hf
      | |- ipred Ptrue m1 m2 -> _ => intros _; trivial
      | _ => idtac end.
    match goal with 
     |- ipred (pand ?p1 ?p2) m1 m2 -> _ => destruct (ipred_pand p1 p2) 
    end; intros.
    unfold implMR in H; apply H in H1; clear H H0; destruct H1.
    rewrite ipred_peq, !e2E_correct in H, H0; 
     simpl in H, H0; rewrite H, H0; trivial.
    generalize (US.eqb_spec_dep u u0); destruct (US.eqb u u0);
     [ | intros _ Hf; elim Hf].
    intros Heq; inversion Heq; clear Heq; subst; trivial.

    assert (W:=H _ d1 _ d2 Heqr); inversion W; clear H W; subst.
    unfold transpR, andR, permut_support.
    apply T.inj_pair2 in H2; rewrite H2; clear Heqr H0 H2.
    assert (forall x, In x (E.eval_support d2 m2) -> 
     peval m1 m2 ({| t := t2; var := cast_var r t2; val := x |} :: nil) bound).
    revert Hbound Hcond1; clear.
    destruct d2; simpl; intros Heq; inversion Heq; clear Heq; subst; trivial;
    unfold ipred; simpl; intros Hcond v0 Hin; trivial.
    rewrite !e2E_correct in *; rewrite assoc_same;[ | apply  veqb_refl]; simpl.
    apply Z_support_bounded; trivial.   
    unfold transpR; split; intros.
    apply PermutP_sym.
    revert Hbij; destruct d as [ | t F | t F Finv]; simpl.

    (* id *)
    intros Hbij; inversion Hbij; clear Hbij; subst.
    apply PermutP_weaken with (@eq (T.interp k t2)).
    intros; simpl; rewrite assoc_same; [symmetry; trivial | apply veqb_refl].
    apply PermutP_eq.

    (* involutive *)
    intro W.
    set (f:=fun x => eeval m1 m2 ({|t:=t2; var:=cast_var r t2; val:=x|}::nil) fx).
    intros.
    apply PermutP_sym; apply (@PermutP_NoDup_involutive _ f); trivial.
    apply is_uniform_correct; trivial.
    intros x Hin; generalize (Hforall x); clear Hforall.
    rewrite peval_pimplies, peval_pand, peval_pand.
    intros W1; decompose [and] (W1 (H x Hin)); clear W1 H.
    destruct (T.eq_dec t t2); subst; inversion W; clear W; unfold f; subst.
    case_eq (Vset.mem (cast_var r t2) (lfv F)); intro Hmem;
     case_eq (Vset.mem (cast_var r t2) (lbind F)); intro Hmem';
      case_eq (Vset.disjoint (lfv (esubst y2<2> (VarLogic (cast_var r t2)) F))
       (lbind F)); intro Hdisj;
      rewrite Hmem, Hmem', Hdisj in H0; simpl in H0;
       injection H0; clear H0; intros; subst; try elim H3.

    rewrite peval_peq in H3; simpl in H3.
    rewrite assoc_same in H3; [ | apply veqb_refl].
    rewrite <- H3 at 2; clear H3.

    assert (Hbind:Vset.disjoint (lfv (VarLogic (cast_var r t2))) (lbind F)).
    apply VsetP.disjoint_sym.
    unfold lfv; simpl lfv_rec.
    apply disjoint_singleton; trivial.

    rewrite esubst_correct; simpl; [ | trivial].
    rewrite assoc_same; [ | apply veqb_refl].
    rewrite esubst_correct; simpl; [ | trivial].
    rewrite assoc_same; [ | apply veqb_refl].
    rewrite esubst_correct; simpl; [ | trivial].
    rewrite esubst_correct; simpl; [ | trivial].
    rewrite assoc_same; [ | apply veqb_refl]. 
    apply eeval_eq_assoc; intros.

    assert (Hneq:Var.veqb x0 (cast_var r t2) = false).
    generalize (Var.eqb_spec x0 (cast_var r t2)).
    case (Var.eqb x0 (cast_var r t2)); intro.
    rewrite H0 in H; rewrite H in Hmem; discriminate.
    rewrite <- Var_eqb_veqb.
    generalize (Var.eqb_spec x0 (cast_var r t2)).
    case (Var.eqb x0 (cast_var r t2)); intros; [ elim H0 | ]; trivial.

    rewrite assoc_diff, assoc_diff; trivial.
    elim H3.

    clear W; intros x Hin.
    generalize (Hforall x); clear Hforall.
    rewrite peval_pimplies, peval_pand, peval_pand; intros.
    destruct (H0 (H _ Hin)) as [ [? _] _ ]; clear H0.
    case_eq (is_full d2); intro Hfull; rewrite Hfull in Hbound.
    apply is_full_correct; trivial.

    destruct d2; try discriminate;
     injection Hbound; intros; subst; try (elim Hcond1; fail).
    apply In_Z_support.
    unfold ipred in Hcond1; simpl in Hcond1;
     rewrite e2E_correct, e2E_correct in Hcond1; trivial.
    rewrite peval_pand in H1; destruct H1 as [H1 _].
    rewrite psubst_correct in H1; simpl in H1.
    rewrite e2E_correct, e2E_correct in H1.
    rewrite assoc_same in H1; [trivial | apply veqb_refl].
    apply VsetP.disjoint_sym; apply negb_false_iff in Hmem3; trivial.

    (* Bijection *)
    intros W.
    set (f:=fun x => 
     eeval m1 m2 ({|t:=t2; var:=cast_var r t2; val:=x|}::nil) fx).
    set (finv:=fun x => 
     eeval m1 m2 ({|t:=t2; var:=cast_var r t2; val:=x|}::nil) finvx).
    apply PermutP_sym; eapply (@PermutP_NoDup _ f finv); trivial.
    apply is_uniform_correct; trivial.
    apply is_uniform_correct; trivial. 

    intros x Hin; generalize (Hforall x); clear Hforall.
    rewrite peval_pimplies, peval_pand, peval_pimplies, peval_pand.
    intros W1; decompose [and] (W1 (H x Hin)); clear W1 H. 
    unfold f, finv.

    destruct (T.eq_dec t t2); subst; inversion W; clear W; subst.
    revert H0.
    case_eq (Vset.mem (cast_var r t2) (lfv F)); intro Hmem5; simpl;
     [ intro H0; injection H0; intros; subst; elim H3 | ].
    case_eq (Vset.mem (cast_var r t2) (lfv Finv)); intro Hmem6; simpl;
     [ intro H0; injection H0; intros; subst; elim H3 | ].
    case_eq (Vset.mem (cast_var r t2) (lbind F)); intro Hmem7; simpl;
     [ intro H0; injection H0; intros; subst; elim H3 | ].
    case_eq (Vset.mem (cast_var r t2) (lbind Finv)); intro Hmem8; simpl;
     [ intro H0; injection H0; intros; subst; elim H3 | ].
    case_eq (Vset.disjoint (lfv (esubst y2<2> (VarLogic (cast_var r t2)) F)) 
     (lbind F)); intro Hdisj1; simpl;
     [ | intro H0; injection H0; intros; subst; elim H3 ].
    case_eq (Vset.disjoint (lfv (esubst y2<2> (VarLogic (cast_var r t2)) Finv)) 
     (lbind Finv)); intro Hdisj2; simpl;
     [ | intro H0; injection H0; intros; subst; elim H3 ].
    case_eq (Vset.disjoint (lfv (esubst y2<2> (VarLogic (cast_var r t2)) F)) 
     (lbind Finv)); intro Hdisj3; simpl;
     [ | intro H0; injection H0; intros; subst; elim H3 ].
    case_eq (Vset.disjoint (lfv (esubst y2<2> (VarLogic (cast_var r t2)) Finv)) 
     (lbind F)); intro Hdisj4; simpl;
     [ | intro H0; injection H0; intros; subst; elim H3 ].

    intro H0; injection H0; clear H0; intros; subst.

    assert (Hbind1:Vset.disjoint (lfv (VarLogic (cast_var r t2))) (lbind F)).
    apply VsetP.disjoint_sym.
    unfold lfv; simpl lfv_rec.
    apply disjoint_singleton; trivial.

    assert (Hbind2:Vset.disjoint (lfv (VarLogic (cast_var r t2))) (lbind Finv)).
    apply VsetP.disjoint_sym.
    unfold lfv; simpl lfv_rec.
    apply disjoint_singleton; trivial.

    rewrite peval_pand, peval_peq, peval_peq in H3.
    destruct H3 as [_ H]; generalize H.

    rewrite esubst_correct; simpl; [ | trivial].
    rewrite assoc_same; [ | apply veqb_refl].
    rewrite esubst_correct; simpl; [ | trivial].
    rewrite assoc_same; [ | apply veqb_refl].
    rewrite esubst_correct; simpl; [ | trivial].
    rewrite assoc_same; [ | apply veqb_refl].

    intro Heq; rewrite <- Heq at 5; clear Heq.
    apply eeval_eq_assoc; intros.

    assert (Hneq:Var.veqb x0 (cast_var r t2) = false).
    generalize (Var.eqb_spec x0 (cast_var r t2)).
    case (Var.eqb x0 (cast_var r t2)); intro.
    rewrite H3 in H0; rewrite H0 in Hmem5; discriminate.
    rewrite <- Var_eqb_veqb.
    generalize (Var.eqb_spec x0 (cast_var r t2)).
    case (Var.eqb x0 (cast_var r t2)); intros; [ elim H3 | ]; trivial.

    rewrite assoc_diff, assoc_diff; trivial.
    elim H3.

    (** ...and all over again *)
    intros x Hin; generalize (Hforall x); clear Hforall.
    rewrite peval_pimplies, peval_pand, peval_pimplies, peval_pand.
    intros W1; decompose [and] (W1 (H x Hin)); clear W1 H. 
    unfold f, finv.

    destruct (T.eq_dec t t2); subst; inversion W; clear W; subst.
    revert H0.
    case_eq (Vset.mem (cast_var r t2) (lfv F)); intro Hmem5; simpl;
     [ intro H0; injection H0; intros; subst; elim H3 | ].
    case_eq (Vset.mem (cast_var r t2) (lfv Finv)); intro Hmem6; simpl;
     [ intro H0; injection H0; intros; subst; elim H3 | ].
    case_eq (Vset.mem (cast_var r t2) (lbind F)); intro Hmem7; simpl;
     [ intro H0; injection H0; intros; subst; elim H3 | ].
    case_eq (Vset.mem (cast_var r t2) (lbind Finv)); intro Hmem8; simpl;
     [ intro H0; injection H0; intros; subst; elim H3 | ].
    case_eq (Vset.disjoint (lfv (esubst y2<2> (VarLogic (cast_var r t2)) F)) 
     (lbind F)); intro Hdisj1; simpl;
     [ | intro H0; injection H0; intros; subst; elim H3 ].
    case_eq (Vset.disjoint (lfv (esubst y2<2> (VarLogic (cast_var r t2)) Finv)) 
     (lbind Finv)); intro Hdisj2; simpl;
     [ | intro H0; injection H0; intros; subst; elim H3 ].
    case_eq (Vset.disjoint (lfv (esubst y2<2> (VarLogic (cast_var r t2)) F)) 
     (lbind Finv)); intro Hdisj3; simpl;
     [ | intro H0; injection H0; intros; subst; elim H3 ].
    case_eq (Vset.disjoint (lfv (esubst y2<2> (VarLogic (cast_var r t2)) Finv)) 
     (lbind F)); intro Hdisj4; simpl;
     [ | intro H0; injection H0; intros; subst; elim H3 ].

    intro H0; injection H0; clear H0; intros; subst.

    assert (Hbind1:Vset.disjoint (lfv (VarLogic (cast_var r t2))) (lbind F)).
    apply VsetP.disjoint_sym.
    unfold lfv; simpl lfv_rec.
    apply disjoint_singleton; trivial.

    assert (Hbind2:Vset.disjoint (lfv (VarLogic (cast_var r t2))) (lbind Finv)).
    apply VsetP.disjoint_sym.
    unfold lfv; simpl lfv_rec.
    apply disjoint_singleton; trivial.

    rewrite peval_pand, peval_peq, peval_peq in H3.
    destruct H3 as [H0 _]; generalize H0.
    rewrite esubst_correct; simpl; [ | trivial].
    rewrite assoc_same; [ | apply veqb_refl].
    rewrite esubst_correct; simpl; [ | trivial].
    rewrite assoc_same; [ | apply veqb_refl].
    rewrite esubst_correct; simpl; [ | trivial].
    rewrite assoc_same; [ | apply veqb_refl].

    intro Heq; rewrite <- Heq at 5; clear Heq.
    apply eeval_eq_assoc; intros.

    assert (Hneq:Var.veqb x0 (cast_var r t2) = false).
    generalize (Var.eqb_spec x0 (cast_var r t2)).
    case (Var.eqb x0 (cast_var r t2)); intro.
    rewrite H3 in H; rewrite H in Hmem6; discriminate.
    rewrite <- Var_eqb_veqb.
    generalize (Var.eqb_spec x0 (cast_var r t2)).
    case (Var.eqb x0 (cast_var r t2)); intros; [elim H3 | ]; trivial.

    rewrite assoc_diff, assoc_diff; trivial.
    elim H3.

    clear W; intros x Hin.
    generalize (Hforall x); clear Hforall.
    rewrite peval_pimplies, peval_pand, peval_pand; intros.
    destruct (H0 (H _ Hin)) as [ [? _] _ ]; clear H0.
    case_eq (is_full d2); intro Hfull; rewrite Hfull in Hbound.
    apply is_full_correct; trivial.

    destruct d2; try discriminate;
     injection Hbound; intros; subst; try (elim Hcond1; fail).
    apply In_Z_support.
    unfold ipred in Hcond1; simpl in Hcond1;
     rewrite e2E_correct, e2E_correct in Hcond1; trivial.
    rewrite peval_pand in H1; destruct H1 as [H1 _].
    rewrite psubst_correct in H1; simpl in H1.
    rewrite e2E_correct, e2E_correct in H1.
    rewrite assoc_same in H1; [trivial | apply veqb_refl].
    apply VsetP.disjoint_sym; apply negb_false_iff in Hmem3; trivial.

    clear W; intros x Hin.
    generalize (Hforall x); clear Hforall.
    rewrite peval_pimplies, peval_pand, peval_pand; intros.
    destruct (H0 (H _ Hin)) as [ [? _] _ ]; clear H0.
    case_eq (is_full d2); intro Hfull; rewrite Hfull in Hbound.
    apply is_full_correct; trivial.

    destruct d2; try discriminate;
     injection Hbound; intros; subst; try (elim Hcond1; fail).
    apply In_Z_support.
    unfold ipred in Hcond1; simpl in Hcond1;
     rewrite e2E_correct, e2E_correct in Hcond1; trivial.
    rewrite peval_pand in H1; destruct H1 as [_ H1].
    rewrite psubst_correct in H1; simpl in H1.
    rewrite e2E_correct, e2E_correct in H1.
    rewrite assoc_same in H1; [trivial | apply veqb_refl].
    apply VsetP.disjoint_sym; apply negb_false_iff in Hmem4; trivial.

    (* Q is valid *)
    generalize (Hforall v); clear Hforall.
    rewrite peval_pimplies, peval_pand; intros W1; destruct (W1 (H v H0));
     clear W1 H.
    rewrite peval_pimplies in H2; apply H2 in H1; clear H2.
    unfold ipred.
    rewrite psubst_correct in H1; simpl in H1.
    rewrite psubst_correct in H1; simpl in H1.
    rewrite assoc_same in H1; [ | apply veqb_refl].
    rewrite peval_notfv in H1.
    trivial.

    trivialb.
    unfold lfv; simpl.
    apply disjoint_singleton; trivial.  
    eapply VsetP.disjoint_subset_l; [ apply pbind_psubst | ].
    rewrite VsetP.disjoint_sym; trivial.

    apply disjoint_union.
    destruct (Vset.disjoint (lfv fx) (pbind Q)); [trivial | discriminate].
    unfold lbind; simpl; apply VsetP.disjoint_complete; intro; auto with set.
   Qed.

   Lemma check_proof_correct_aux : forall d P c1 c2 Q cond cond', 
    check_proof P c1 c2 Q d cond = DS_cond cond' ->
    interp_cond cond' ->
    interp_cond cond /\ Equiv P E1 c1 E2 c2 Q.
   Proof.
    induction d; simpl; intros.
    (* Rnil *)
    destruct c1; destruct c2; try discriminate;
      injection H; intros; subst; clear H.
    apply interp_cond_add in H0; destruct H0; split;[trivial | ].
    rewrite interp_pimplies in H; apply equiv_nil_impl; red; intros; auto.
    (* Rsub_pre : strengthening *)
    apply IHd in H;[ | trivial]; destruct H.
    apply interp_cond_add in H; destruct H; split;[trivial | ].
    apply equiv_strengthen with (ipred p);
     [rewrite <- interp_pimplies | ]; trivial.
    (* Rsub_post : weakening *)
    apply IHd in H;[ | trivial]; destruct H.
    apply interp_cond_add in H; destruct H; split;[trivial | ].
    apply equiv_weaken with (ipred p);[ rewrite <- interp_pimplies | ]; trivial.
    (* Rcase *)
    generalize H; clear H; case_eq (is_decMR p); intros;[ | discriminate].
    apply app_cond_DS_cond in H1; destruct H1 as (cond'',(H1,H2)).
    apply IHd2 in H2;[ | trivial]; destruct H2.
    apply IHd1 in H1;[ | trivial]; destruct H1.
    unfold Equiv in H4,H3.
    split;[ | apply Equiv_Case with p]; trivial.
    (* RcondLeft *) 
    generalize H; clear H; case_eq (destruct_cond c1); intros;[ | discriminate].
    apply destruct_cond_correct in H; subst.
    apply app_cond_DS_cond in H1; destruct H1 as (cond'',(H2,H3)).
    apply IHd2 in H3;[ | trivial]; destruct H3.
    apply IHd1 in H2;[ | trivial]; destruct H2; split;[trivial | ].
    apply Equiv_cond_l; trivial.
    (* RcondRight dt df *)
    generalize H; clear H; case_eq (destruct_cond c2); intros;[ | discriminate].
    apply destruct_cond_correct in H; subst.
    apply app_cond_DS_cond in H1; destruct H1 as (cond'',(H2,H3)).
    apply IHd2 in H3;[ | trivial]; destruct H3.
    apply IHd1 in H2;[ | trivial]; destruct H2; split;[trivial | ].
    apply Equiv_cond_r; trivial.
    (* RcondBoth dt df *)
    generalize H; clear H; case_eq (destruct_cond c1);[ | discriminate].
    case_eq (destruct_cond c2);[ | discriminate].
    intros e2 ct2 cf2 c2' H1 e1 ct1 cf1 c1' H H2.
    apply app_cond_DS_cond in H2; destruct H2 as (cond'',(H3,H4)).

    apply IHd2 in H4;[ | trivial]; destruct H4.
    apply IHd1 in H3;[ | trivial]; destruct H3.
    apply interp_cond_add in H3; destruct H3.
    apply destruct_cond_correct in H; apply destruct_cond_correct in H1; subst.
    split;[ |apply Equiv_cond]; trivial.
    rewrite interp_pimplies in H3; intros k m1 m2 W; apply H3 in W.
    rewrite ipred_peq in W.
    rewrite e2E_correct, e2E_correct in W; trivial.
    (* Rapp *)
    apply app_cond_DS_cond in H; destruct H as (cond'',(H3,H4)).
    apply IHd2 in H4;[ | trivial]; destruct H4.  
    apply IHd1 in H3;[ | trivial]; destruct H3; split;[trivial | ].
    rewrite <- (firstn_skipn n c1), <- (firstn_skipn n0 c2).
    apply equiv_app with (1:= H3) (2:= H1); trivial.
    (* Rwp_asgn *)
    revert H; case_eq (wp_asgn side_left c1 Q); intros Q1 c1' Heq1.
    case_eq (wp_asgn side_right c2 Q1); intros Q2 c2' Heq2 Hcond.
    apply IHd in Hcond;[ destruct Hcond; split | ]; trivial.
    apply wp_asgn_correct with (E:=E1) in Heq1; destruct Heq1 as (Hl1,(Heq1,Hr1)).
    apply wp_asgn_correct with (E:=E2) in Heq2; destruct Heq2 as (Hl2,(Heq2,Hr2)).
    rewrite <- (firstn_skipn (length c2') c2), 
            <- (firstn_skipn (length c1') c1), <- Heq1, <- Heq2.
    apply equiv_app with (1:= H1).
    change (skipn (length c1') c1) with (nil ++ (skipn (length c1') c1)).
    rewrite (app_nil_end (skipn (length c2') c2)).
    apply equiv_app with (ipred Q1).
    apply range_equiv_r; trivial.
    apply range_equiv_l; trivial.
    (* Rwp_simpl *)
    revert H; case_eq (wp_cond side_left c1 Q); intros Q1 c1' Heq1.
    case_eq (wp_cond side_right c2 Q1); intros Q2 c2' Heq2 Hcond.
    apply IHd in Hcond;[ destruct Hcond; split | ]; trivial.
    apply wp_cond_correct with (E:=E1) in Heq1; destruct Heq1 as (Hl1,(Heq1,Hr1)).
    apply wp_cond_correct with (E:=E2) in Heq2; destruct Heq2 as (Hl2,(Heq2,Hr2)).
    rewrite <- (firstn_skipn (length c2') c2), 
            <- (firstn_skipn (length c1') c1), <- Heq1, <- Heq2.
    apply equiv_app with (1:= H1).
    change (skipn (length c1') c1) with (nil ++ (skipn (length c1') c1)).
    rewrite (app_nil_end (skipn (length c2') c2)).
    apply equiv_app with (ipred Q1).
    apply range_equiv_r; trivial.
    apply range_equiv_l; trivial.
    (* Rwp_call *)
    revert H; case_eq (wp_call l l0 e c1 c2 Q); intros;[ | discriminate].
    apply IHd in H1;[destruct H1; split | ]; trivial.
    apply wp_call_correct with (1:= H); trivial.
    (* Rrand_bij *)
    revert H; case_eq (wp_rnd_bij t0 t1 c1 c2 Q);
     [intros c1' c2' Q' Heq Hch| discriminate].
    destruct (IHd _ _ _ _ _ _ Hch H0); split; [ trivial | ].
    apply wp_rnd_bij_correct with (1:=Heq) (2:=H1).
    (* Rrand_disj *)
    revert H; case_eq (wp_rnd_disj t0 b c1 c2 Q);
     [intros c1' c2' Q' Heq Hch| discriminate].
    destruct (IHd _ _ _ _ _ _ Hch H0); split;[ trivial | ].
    apply wp_rnd_disj_correct with (1:= Heq) (2:= H1).
    (* Rpre_false *)
    inversion H; clear H; intros.
    subst; apply interp_cond_add in H0; destruct H0; split; trivial.
    apply equiv_strengthen with falseR.
    rewrite interp_pimplies in H; auto.
    apply equiv_False; trivial.
    (* Rpost_true *)
    generalize H; clear H.
    case_eq (is_lossless pi1 c1 && is_lossless pi2 c2)%bool;[ | discriminate].
    rewrite andb_true_iff; intros (H1,H2) H.
    inversion H; clear H; subst.
    apply interp_cond_add in H0; destruct H0; split; trivial.
    apply equiv_weaken with trueR.
    intros; apply H.
    apply equiv_True.
    apply is_lossless_correct with pi1; trivial.
    apply is_lossless_correct with pi2; trivial.
    (* Rnot_modify *)
    generalize H; clear H; unfold check_notmodify.
    case_eq (modify pi1 Vset.empty c1);[ intros X1 HX1| discriminate].
    case_eq (modify pi2 Vset.empty c2);[ intros X2 HX2| discriminate].
    case_eq (pdepend p); intros M1 M2 Hp.    
    match goal with |- (if ?t then _ else _) = _ -> _ =>
     case_eq t;[ | discriminate] end.
    repeat rewrite andb_true_iff; intros (H3,H4) Hd.
    apply IHd in Hd;[ destruct Hd | trivial].
    apply interp_cond_add in H; destruct H.
    apply interp_cond_add in H2; destruct H2; split; trivial.
    apply equiv_sub with (ipred P /-\ ipred p) (ipred p0 /-\ ipred p).
    intros; rewrite interp_pimplies in H; split; auto.
    intros k m1 m2 (W1,W2); rewrite interp_pimplies in H2; apply H2 in W2.
    apply ipred_pimplies in W2; auto.
    apply equiv_and_NotModify with M1 M2 X1 X2; auto.
    apply modify_correct with pi1 Vset.empty; trivial.
    apply modify_correct with pi2 Vset.empty; trivial.
    change (depend_only_rel (ipred p) (fst (M1, M2)) (snd (M1,M2))).
    rewrite <- Hp; apply pdepend_correct; trivial.
    (* RinlineLeft *)
    admit.
    (* RinlineRight *)
    admit.
    (* Rderandomize *)
    admit.
    (* Rswap *)
    generalize H; clear H.
    case_eq (check_swap b (if b then c1 else c2) n n0 b0 n1); intros;
     [ | discriminate].
    apply check_swap_correct in H.
    apply IHd in H1;[ destruct H1; split | ]; trivial.
    destruct b.
    apply equiv_trans_eq_mem_l with trueR E1 l; trivial.
    rewrite proj1_MR; trivial.
    red; intros; red; trivial.
    apply equiv_trans_eq_mem_r with trueR E2 l; trivial.
    rewrite proj1_MR; trivial.
    red; intros; red; trivial.
   Qed.

   Transparent pimplies forall_fresh_l forall_fresh_r.

   Lemma check_proof_correct : forall (d:RhlRule) (P:pred) (c1 c2:cmd) (Q:pred)
    (cond:list pred),
    check_proof P c1 c2 Q d nil = DS_cond cond ->
    interp_cond cond -> Equiv P E1 c1 E2 c2 Q.
   Proof.
    intros d P c1 c2 Q cond H H0; 
    apply check_proof_correct_aux in H;[destruct H | ]; auto.
   Qed.

  End RANDOM.

 End CHECK_PROOF.


 (* Fixpoint eq_param t1 (d1:dlist Var.var t1) t2 (d2:dlist Var.var t2) {struct d1} := *)
 (*  match d1, d2 with *)
 (*  | dnil , dnil  => Ptrue *)
 (*  | dcons t1 l1 x1 dnil, dcons t2 l2 x2 dnil => peq (x1<1>) (cast_var x2 t1)<2> *)
 (*  | dcons t1 l1 x1 d1', dcons t2 l2 x2 d2' => *)
 (*    pand (peq (x1<1>) (cast_var x2 t1)<2>) (eq_param d1' d2') *)
 (*  | _, _ => Pfalse *)
 (*  end. *)

Definition eq_param t1 (d1:dlist Var.var t1) t2 (d2:dlist Var.var t2) : pred.
induction 1; intros.
destruct d2.
exact Ptrue.
exact Pfalse.
destruct d2.
exact Pfalse.
destruct d1.
destruct d2.
exact (peq (p<1>) (cast_var v a)<2>).
exact Pfalse.
exact (pand (peq (p<1>) (cast_var v a)<2>) (IHd1 _ d2)).
Defined.




 Definition preq_mem X : pred :=
  Vset.fold (fun (x:VarP.Edec.t) (P:pred) => ((x<1>) === (x<2>) /_\ P)) X Ptrue.  

 Lemma req_mem_add : forall k t (x:Var.var t) (X:Vset.t) (m1 m2:Mem.t k),
  req_mem X m1 m2 ->
  m1 x = m2 x ->
  req_mem (Vset.add x X) m1 m2.
 Proof.
  intros k t x X m1 m2 Hreq Heq t' y Hin.
  generalize (Var.eqb_spec x y); case_eq (Var.eqb x y); intros H0 H1;
   [ injection H1; clear H1; intros H1 ?; subst;
     pose proof (@T.inj_pair2 _ _ _ _ H1) as Heq'
   | pose proof (@Vset.add_inversion _ _ _ H1 Hin) as Heq' ]; clear H1 H0 Hin.
  subst; trivial.
  auto.
 Qed.  

 Lemma preq_mem_correct_aux : forall X k (m1 m2:Mem.t k) (Q:pred),
  peval m1 m2 nil
  (Vset.fold (fun (x : VarP.Edec.t) (P : pred) => x<1> === x<2> /_\ P) X Q) <-> 
  peval m1 m2 nil Q /\ 
  forall t (x:Var.var t), InA VarP.Edec.eq x (Vset.elements X) -> m1 x = m2 x.
 Proof.
  intros.
  rewrite Vset.fold_spec; revert Q; induction (Vset.elements X); intros.
  
  simpl; repeat split; intros; try tauto; inversion H0.
 
  simpl; split; intros.
  destruct (IHl (a<1> === a<2> /_\ Q)); destruct (H0 H).
  rewrite peval_pand in H2.
  simpl in H2; destruct H2; split; trivial.
  intros; inversion H5; subst.
  
  unfold VarP.Edec.eq in H7; rewrite <- H7 in H2; trivial.
  apply H3; trivial.

  destruct H; apply IHl.
  rewrite peval_pand, peval_peq.
  simpl; repeat split; trivial.
  apply H0; apply InA_cons_hd; destruct a; trivial.
  intros; apply H0; apply InA_cons_tl; destruct a; trivial.
 Qed.

 Lemma preq_mem_correct : forall X k (m1 m2:Mem.t k),
  peval m1 m2 nil (preq_mem X) <-> kreq_mem X m1 m2.
 Proof.
  intros; unfold preq_mem.
  rewrite preq_mem_correct_aux; split.
  intros [_ H] t x Hin; apply Vset.elements_correct in Hin; auto.
  intros; split; [simpl; trivial | ].
  intros; apply H; apply Vset.elements_complete; trivial.
 Qed.

 Lemma eq_param_same : forall k (m1 m2 : Mem.t k) E lt (f : Proc.proc lt),
  m1 =={Vset_of_var_decl (proc_params E f)} m2 <->
  peval m1 m2 nil (eq_param (proc_params E f) (proc_params E f)).
 Proof.
  intros; induction (proc_params E f); simpl in *; 
   intros; auto; split; intros; auto.
  destruct v; simpl.
  apply peval_peq; simpl.
  rewrite (H _ p); auto with set.
  destruct p; simpl; auto.
  apply peval_pand; split.
  apply peval_peq; simpl.
  rewrite (H _ p); auto with set.
  destruct p; simpl; auto.
  apply IHv; red; intros.
  apply H; auto with set.
  red; intros.
  destruct v; simpl in *.
  apply peval_peq in H; simpl in H.
  unfold  VarP.Edec.eqb in H0.
  generalize (Var.eqb_spec x p).
  destruct (Var.eqb x p); intros.
  injection H1; intros; subst.
  apply T.inj_pair2 in H2; subst.
  destruct p; simpl in *; auto.
  discriminate.
  apply VsetP.add_spec in H0; destruct H0.
  unfold Vset.E.eq in H0.
  injection H0; intros; subst.
  apply T.inj_pair2 in H1; subst.
  apply peval_pand in H; simpl in H; destruct H.
  apply peval_peq in H; simpl in H.
  destruct x; simpl in *; tauto.
  apply IHv; auto.
  apply peval_pand in H; simpl in H; destruct H; trivial.
 Qed.

 Lemma equiv_adv_c : forall (PrOrcl PrPriv : PrSet.t) (Gadv Gcomm : Vset.t),
  (forall x : VarP.Edec.t, Vset.mem x Gadv -> Var.is_global x) ->
  (forall x : VarP.Edec.t, Vset.mem x Gcomm -> Var.is_global x) ->
  forall (inv : pred) (E1 E2 : env) (X1 X2 : Vset.t),
    pdepend inv = (X1, X2) ->
  (forall x : VarP.Edec.t,
    Vset.mem x (Vset.union X1 X2) -> Var.is_global x) ->
  Gcomm [=] Vset.empty ->
  Vset.disjoint X1 Gadv ->
  Vset.disjoint X2 Gadv ->
  Eq_adv_decl PrOrcl PrPriv E1 E2 ->
  Eq_orcl_params PrOrcl E1 E2 ->
  (forall o : ProcD.t,
   PrSet.mem o PrOrcl ->
   Equiv (pand (preq_mem Gadv) 
    (pand (eq_param (proc_params E1 (BProc.p_name o))  
                    (proc_params E2 (BProc.p_name o))) inv))
   E1 (proc_body E1 (BProc.p_name o)) 
   E2 (proc_body E2 (BProc.p_name o))
   (pand (preq_mem Gadv) 
    (pand (peq (e2E side_left (proc_res E1 (BProc.p_name o))) 
               (e2E side_right (proc_res E2 (BProc.p_name o)))) inv))) ->
  forall I c O,
   WFAdv_c PrOrcl PrPriv Gadv Gcomm E1 I c O->
   (forall x, Vset.mem x I -> Var.is_local x) -> 
   Equiv (pand (preq_mem (Vset.union Gadv I)) inv) E1 c E2 c 
   (pand (preq_mem (Vset.union Gadv O)) inv).
 Proof.
  intros PrOrcl PrPriv Gadv Gcomm Ga_global Gc_global inv.
  intros E1 E2 X1 X2 inv_dep inv_glob Gcomm_empty disjoint_Orcl1 disjoint_Orcl2.
  intros Heq_adv_decl Heq_orcl_params Ho.
  unfold Equiv, ipred.
  induction 1 using WFAdv_c_prop with
    (P0 := fun I i O (_:WFAdv_i PrOrcl PrPriv Gadv Gcomm E1 I i O)  =>
     (forall x, Vset.mem x I -> Var.is_local x) -> 
      equiv (fun (k : nat) (m1 m2 : Mem.t k) => 
        (peval m1 m2 nil (preq_mem (Vset.union Gadv I) /_\ inv)))
      E1 [i] E2 [i] 
      (fun (k : nat) (m1 m2 : Mem.t k) => 
        (peval m1 m2 nil (preq_mem (Vset.union Gadv O) /_\ inv)))); intros HI.
  
  (* nil*)
  apply equiv_nil.

  (* cons *)
  eapply equiv_cons.
  apply IHWFAdv_c; auto.
  apply IHWFAdv_c0; eauto using WFAdv_i_local.

  (* assign *)
  unfold Equiv.
  apply equiv_sub with 
   (P := kreq_mem (Vset.union Gadv I) /-\ ipred inv)
   (Q := kreq_mem (Vset.union Gadv (add_read x I)) /-\ ipred inv).
  intros k m1 m2 H; simpl in H.
  rewrite peval_pand in H.
  split;[ | tauto ].
  apply preq_mem_correct.
  tauto.
  intros k m1 m2 [H1 H2].
  rewrite peval_pand.
  split; auto.
  apply preq_mem_correct; trivial.
  eapply equiv_strengthen;[ | apply equiv_assign].
  unfold upd_para, kreq_mem; intros k m1 m2 [H1 H2]; simpl.
  split.
  erewrite equiv_WFRead with (IA := Gadv) (m2 := m2) (1 := w0); auto with set.
  destruct x; apply equiv_WFWrite; trivial.
  rewrite Gcomm_empty; auto with set.
  unfold ipred.
  generalize (@pdepend_correct_aux k m1 
   (m1 {!x <-- E.eval_expr e m1!}) m2 (m2 {!x <-- E.eval_expr e m2!}) inv nil).
  rewrite inv_dep; simpl; intros.
  destruct H; auto.
  destruct x.
  red; intros; rewrite Mem.get_upd_diff; trivial; intro.
  assert (W: Var.is_global x) by auto with set.
  contradict H.
  apply VsetP.disjoint_mem_not_mem with
    (1:=VsetP.disjoint_sym disjoint_Orcl1).
  generalize w; rewrite <- H0 in *; destruct x; auto.
  destruct x.
  red; intros; rewrite Mem.get_upd_diff; trivial; intro.
  assert (W: Var.is_global x) by auto with set.
  contradict H.
  apply VsetP.disjoint_mem_not_mem with (1:=VsetP.disjoint_sym disjoint_Orcl2).
  generalize w; rewrite <- H0 in *; destruct x; auto.
  destruct x; auto.

  (* random *)
  eapply equiv_strengthen;[ | apply equiv_random].
  unfold forall_random,kreq_mem; intros; simpl.
  rewrite peval_pand in H.
  simpl in H; destruct H.
  apply preq_mem_correct in H; trivial.
  split.
  unfold eq_support.
  apply EqObs_d_fv_expr.
  apply req_mem_weaken with (2:= H).
  unfold WFReadD in w0; apply Vset.subset_complete; intros.
  repeat rewrite VsetP.union_spec; destruct (w0 _ H1); auto.
  destruct H2; auto.
  rewrite Gcomm_empty in H2.
  elim (Vset.empty_spec H2).
  destruct x; intros.
  rewrite peval_pand; split.
  apply preq_mem_correct.
  apply equiv_WFWrite; trivial.
  generalize (@pdepend_correct_aux k m1 (m1 {!v <-- v0!}) 
   m2 (m2 {!v <-- v0!}) inv nil).
  rewrite inv_dep; simpl; intros.
  destruct H2; auto.
  red; intros; rewrite Mem.get_upd_diff; trivial; intro.
  assert (W: Var.is_global x) by auto with set.
  contradict H2.
  apply VsetP.disjoint_mem_not_mem with  (1:=VsetP.disjoint_sym disjoint_Orcl1).
  generalize w; rewrite <- H3 in *; destruct x; auto.
  red; intros; rewrite Mem.get_upd_diff; trivial; intro.
  assert (W: Var.is_global x) by auto with set.
  contradict H2.
  apply VsetP.disjoint_mem_not_mem with
    (1:=VsetP.disjoint_sym disjoint_Orcl2).
  generalize w; rewrite <- H3 in *; destruct x; auto.

  (* cond *)
  apply equiv_cond; simpl; try rewrite app_nil_r.
  eapply equiv_strengthen; [ | eapply equiv_weaken; [ | apply IHWFAdv_c1; auto ] ].
  intros k m1 m2 (W, _); trivial.
  unfold ipred; simpl; intros k m1 m2.
  rewrite !peval_pand.
  intros (W, W0); split; trivial.
  apply preq_mem_correct.
  apply preq_mem_correct in W.
  apply req_mem_weaken with (2:= W).
  apply VsetP.subset_union_ctxt; auto with set.
  eapply equiv_strengthen; [ | eapply equiv_weaken; [ | apply IHWFAdv_c2; auto ] ].
  intros k m1 m2 (W, _); trivial.
  unfold ipred; simpl; intros k m1 m2.
  rewrite !peval_pand.
  intros (W, W0); split; trivial.
  apply preq_mem_correct.
  apply preq_mem_correct in W.
  apply req_mem_weaken with (2:= W).
  apply VsetP.subset_union_ctxt; auto with set.
  unfold ipred; simpl; intros k m1 m2.
  rewrite !peval_pand.
  intros (W,_).
  apply preq_mem_correct in W.
  erewrite equiv_WFRead with (IA := Gadv) (m2 := m2) (1 := w); auto with set.
  rewrite Gcomm_empty; auto with set.

  (* while *)
  eapply equiv_weaken; [ | apply equiv_while].
  simpl; intros k m1 m2.
  rewrite !peval_pand.
  intros (W, _).
  rewrite peval_pand in W; trivial.
  simpl; intros k m1 m2.
  rewrite !peval_pand.
  intros (W,W0).
  apply preq_mem_correct in W.
  erewrite equiv_WFRead with (IA := Gadv) (m2 := m2) (1 := w); auto with set.
  rewrite Gcomm_empty; auto with set.
  eapply equiv_strengthen;[ | apply equiv_weaken with (2:=IHWFAdv_c HI)].
  intros k m1 m2 (W, _); trivial.
  intros k m1 m2; rewrite !peval_pand.
  intros (W,W0); split; trivial.
  apply preq_mem_correct.
  apply preq_mem_correct in W.
  apply req_mem_weaken with (2:= W).
  apply VsetP.subset_union_ctxt; auto with set.
  eapply WFAdv_c_subset; eauto.

  (* Call Orcl *)
  generalize i; intro i2.
  apply Ho in i; simpl in i.
  eapply equiv_call;[ | | apply i].

  unfold ipred; simpl; intros k m1 m2; rewrite !peval_pand; intros (W3, W4).
  apply preq_mem_correct in W3.
  assert (HX1 : m1 =={ X1}init_mem E1 f args0 m1).
  red; intros; rewrite init_mem_global; trivial; auto with set.
  assert (HX2 : m2 =={ X2}init_mem E2 f args0 m2).
  red; intros; rewrite init_mem_global; trivial; auto with set.
  split.
  apply preq_mem_correct; red; red; intros.
  repeat rewrite init_mem_global; auto with set.
  split.
  rewrite <- (Heq_orcl_params); auto.
  apply eq_param_same.
  eapply req_mem_weaken; [ | apply EqObs_args_correct].

  Focus 2.
  red; intros.
  rewrite <- (Heq_orcl_params ); auto.
  assert (forall ta (args0:E.args ta), ta = (Proc.targs f) -> 
   exists e, get_arg x0 (proc_params E1 f) args0 = Some e).
  apply Vset_of_var_decl_ind with (P:= fun t0 x0 => 
   forall ta (args0:E.args ta), ta = (Proc.targs f) ->
    exists e0 : E.expr t0, get_arg x0 (proc_params E1 f) args0 = Some e0)
  (lv:= proc_params E1 f) .
  generalize (Proc.targs f) (proc_params E1 f). 
  induction v; simpl; intros.
  elim H0.
  destruct args1; try discriminate.
  injection H1; clear H1; intros; subst.
  destruct H0.
  inversion H0; subst.
  assert (W:= T.inj_pair2 H4); clear H0 H3 H4; subst.
  destruct (get_arg p v args1); eauto.
  generalize (Var.veqb_spec p p); destruct (Var.veqb p p); intros.
  case_eq (T.eq_dec a a); intros.
  rewrite (T.UIP_refl e0); eauto.
  elim (T.eq_dec_r H1); trivial.
  elim H0; trivial.
  destruct (IHv _ _ H0 _ args1 (refl_equal _)).
  rewrite H1; eauto.
  apply H.
  simpl; destruct (H0 _ args0 (refl_equal _)) as (e0, Heq); rewrite Heq.
  red; intros.
  assert (W:= get_arg_some _ _ _ Heq).   
  apply equiv_WFRead with (IA:=Gadv) (1:= w _ _ W); auto.
  rewrite Gcomm_empty; auto with set.
  auto with set.
  apply H1.
  auto with set.
  auto.

  generalize (@pdepend_correct_aux k m1 (
   init_mem E1 f args0 m1) m2 (init_mem E2 f args0 m2) inv nil).
  rewrite inv_dep; simpl; intros.
  destruct H; auto.

  unfold ipred; simpl; intros k m1 m1' m2 m2'; rewrite !peval_pand, !peval_peq; intros (W3, W4).
  apply preq_mem_correct in W3.

  intros (W5, (W6, W7)); split.
  apply preq_mem_correct.
  red; red; intros.
  destruct (Vset.ET.eq_dec x x0).
  inversion e; subst; simpl.
  apply inj_pair2_eq_dec in H2; subst; trivial.
  repeat rewrite return_mem_dest; trivial.
  rewrite !e2E_correct in W6; simpl in W6; trivial.
  apply Teq_dec.
  change (Var.mkV x <> x0) in n.
  case_eq (Var.is_global x0); intros.
  rewrite VsetP.union_spec in H; destruct H.
  repeat rewrite return_mem_global; trivial.
  apply preq_mem_correct in W5.
  apply W5; auto with set.
  apply add_read_local in H.
  unfold Var.is_local in H.
  rewrite H0 in H; discriminate.
  auto.
  assert (Var.is_local x0) by (unfold Var.is_local; rewrite H0; trivial).
  repeat rewrite return_mem_local; trivial.
  apply W3.
  rewrite VsetP.union_spec in H |- *; destruct H; auto.
  unfold add_read in H.
  destruct (Var.is_global x); auto.
  rewrite VsetP.add_spec in H; destruct H; auto.
  elim (n H).
  assert (HX1 : m1' =={ X1}return_mem E1 x f m1 m1').
  red; intros; rewrite return_mem_global; trivial.
  assert (W: Var.is_global x0) by auto with set.
  contradict H.
  apply VsetP.disjoint_mem_not_mem with
    (1:=VsetP.disjoint_sym disjoint_Orcl1).
  generalize w; rewrite <- H in *; destruct x; auto.
  auto with set.
  assert (HX2 : m2' =={ X2}return_mem E2 x f m2 m2').
  red; intros; rewrite return_mem_global; trivial.
  assert (W: Var.is_global x0) by auto with set.
  contradict H.
  apply VsetP.disjoint_mem_not_mem with
    (1:=VsetP.disjoint_sym disjoint_Orcl2).
  generalize w; rewrite <- H in *; destruct x; auto.
  auto with set.
  generalize (@pdepend_correct_aux k m1' 
   (return_mem E1 x f m1 m1') m2' (return_mem E2 x f m2 m2') inv nil).
  rewrite inv_dep; simpl; intros.
  destruct H; auto.

  (* Call Adv *)
  destruct (Heq_adv_decl _ f) as (Heq1, (Heq2, Heq3)); trivial.

  assert (W:forall t (x:Var.var t),  Vset.mem x 
   (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x).
  intros; apply Vset_of_var_decl_ind with 
    (P:= fun t (x:Var.var t) => Var.is_local x) (lv:= proc_params E1 f); auto.
  intros; change (Var.vis_local x1).
  eapply proc_params_local; eauto.
  assert (forall x, Vset.mem x 
    (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x). 
  intros (t',x'); auto.
  clear W.
  generalize (IHWFAdv_c H0).
  pattern (proc_body E1 f) at 2; rewrite Heq2; intros.
  eapply equiv_call; eauto.
  unfold ipred; simpl; intros k m1 m2; rewrite !peval_pand; intros (W1, W2); split.
  apply preq_mem_correct in W1.
  apply preq_mem_correct.
  red; red; intros.
  rewrite (init_mem_eq2 E1 E2 f args0 args0 m1 Heq1); trivial.
  rewrite VsetP.union_spec in H2; destruct H2.
  repeat rewrite init_mem_global; auto with set.
  apply init_mem_local; auto.
  generalize args0 w0.
  generalize (Proc.targs f). induction args1; simpl; auto; intros.
  rewrite IHargs1; auto.
  rewrite (@equiv_WFRead Gadv Gcomm Gadv _ _ I _ _ m2); auto with set.
  rewrite Gcomm_empty; auto with set.
  apply preq_mem_correct in W1.
  assert (HX1 : m1 =={ X1}init_mem E1 f args0 m1).
  red; intros; rewrite init_mem_global; trivial; auto with set.
  assert (HX2 : m2 =={ X2}init_mem E2 f args0 m2).
  red; intros; rewrite init_mem_global; trivial; auto with set.
  generalize (@pdepend_correct_aux k m1 
   (init_mem E1 f args0 m1) m2 (init_mem E2 f args0 m2) inv nil).
  rewrite inv_dep; simpl; intros.
  destruct H2; auto.
  unfold ipred; simpl.
  intros k m1 m1' m2 m2'; rewrite !peval_pand; 
    intros (W1, W2) (W3, W4); split; unfold kreq_mem in *.
  apply preq_mem_correct in W1.
  apply preq_mem_correct in W3.
  apply preq_mem_correct.
  red;red; intros. 
  destruct (Var.eq_dec x x0).
  inversion e; simpl.
  repeat rewrite return_mem_dest.
  rewrite <- Heq3.
  apply equiv_WFRead with (IA:= Gadv) (1 := w); auto with set.
  rewrite Gcomm_empty; auto with set.
  rewrite VsetP.union_spec in H2; destruct H2.
  repeat rewrite return_mem_global; trivial; auto with set.
  assert (Vset.mem x0 I). 
  unfold add_read in H2; destruct (Var.is_global x); auto.
  rewrite VsetP.add_spec in H2; destruct H2; trivial.
  elim (n1 H2).
  repeat rewrite return_mem_local; auto with set. 
  assert (HX1 : m1' =={ X1}return_mem E1 x f m1 m1').
  red; intros; rewrite return_mem_global; trivial.
  assert (W: Var.is_global x0) by auto with set.
  contradict H2.
  apply VsetP.disjoint_mem_not_mem with
    (1:=VsetP.disjoint_sym disjoint_Orcl1).
  generalize w; rewrite <- H2 in *; destruct x; auto.
  auto with set.
  assert (HX2 : m2' =={ X2}return_mem E2 x f m2 m2').
  red; intros; rewrite return_mem_global; trivial.
  assert (W: Var.is_global x0) by auto with set.
  contradict H2.
  apply VsetP.disjoint_mem_not_mem with
    (1:=VsetP.disjoint_sym disjoint_Orcl2).
  generalize w; rewrite <- H2 in *; destruct x; auto.
  auto with set.
  generalize (@pdepend_correct_aux k m1' 
   (return_mem E1 x f m1 m1') m2' (return_mem E2 x f m2 m2') inv nil).
  rewrite inv_dep; simpl; intros.
  destruct H2; auto.
 Qed.

 Lemma equiv_adv : forall (PrOrcl PrPriv : PrSet.t) (Gadv Gcomm : Vset.t),
  (forall x : VarP.Edec.t, Vset.mem x Gadv -> Var.is_global x) ->
  (forall x : VarP.Edec.t, Vset.mem x Gcomm -> Var.is_global x) ->
  forall (inv : pred) (E1 E2 : env) (X1 X2 : Vset.t),
   pdepend inv = (X1, X2) ->
   (forall x : VarP.Edec.t, Vset.mem x (Vset.union X1 X2) -> Var.is_global x) ->
   Gcomm[=]Vset.empty ->
   Vset.disjoint X1 Gadv ->
   Vset.disjoint X2 Gadv ->
   Eq_adv_decl PrOrcl PrPriv E1 E2 ->
   Eq_orcl_params PrOrcl E1 E2 ->
   (forall o : ProcD.t,
    PrSet.mem o PrOrcl ->
    Equiv (preq_mem Gadv /_\ 
     (pand (eq_param (proc_params E1 (BProc.p_name o)) 
                     (proc_params E2 (BProc.p_name o))) inv))
   E1 (proc_body E1 (BProc.p_name o)) 
   E2 (proc_body E2 (BProc.p_name o))
   (preq_mem Gadv /_\ 
    (pand (peq (e2E side_left (proc_res E1 (BProc.p_name o))) 
               (e2E side_right (proc_res E2 (BProc.p_name o)))) inv))) ->
   forall t (f:Proc.proc t),
   WFAdv PrOrcl PrPriv Gadv Gcomm E1 f ->
   ~ PrSet.mem {| BProc.p_type := t; BProc.p_name := f |} PrOrcl ->
   ~ PrSet.mem {| BProc.p_type := t; BProc.p_name := f |} PrPriv ->
   (forall x0 : VarP.Edec.t, 
    Vset.mem x0 (Vset_of_var_decl (proc_params E1 f)) -> Var.is_local x0) -> 
   Equiv (preq_mem Gadv /_\ 
    (pand (eq_param (proc_params E1 f) (proc_params E2 f)) inv)) 
   E1 (proc_body E1 f) 
   E2 (proc_body E2 f) 
   (preq_mem Gadv /_\ 
    (pand (peq (e2E side_left (proc_res E1 f)) 
               (e2E side_right (proc_res E2 f))) inv)).
 Proof.
  intros PrOrcl PrPriv Gadv Gcomm Ga_global Gc_global inv.
  intros E1 E2 X1 X2 inv_dep inv_glob Gcomm_empty disjoint_Orcl1 disjoint_Orcl2.
  intros Heq_adv_decl Heq_orcl_params Ho.
  intros t A WFA Hf_orcl Hf_priv Hlocal.

  unfold WFAdv in WFA.
  destruct WFA.
  destruct H.
  unfold Eq_adv_decl in Heq_adv_decl.
  destruct (Heq_adv_decl t A) as [H1 [ H2 H3 ] ]; trivial.
  rewrite H2 in *.
  eapply equiv_adv_c in H; eauto.

  apply Equiv_Sub' with (3 := H).

  unfold ipred; simpl.
  simpl.
  intros k m1 m2; rewrite !peval_pand; intros [W1 [ W2 W3 ] ].
  split; trivial.
  apply preq_mem_correct in W1.
  apply preq_mem_correct.
  red; red; intros.
  apply Vset.union_correct in H4; destruct H4; trivial.
  apply W1; auto.
  rewrite <- H1 in W2.
  rewrite <- eq_param_same in W2.
  apply W2; trivial.

  unfold ipred; simpl.
  intros k m1 m2; rewrite !peval_pand, !peval_peq; intros [ W1 W2 ].
  split.
  apply preq_mem_correct in W1.
  apply preq_mem_correct.
  red; red; intros.
  apply W1; auto with set.
  split; trivial.
  rewrite !e2E_correct; simpl.
  rewrite <- H3.
  eapply equiv_WFRead with (IA := Gadv).
  apply H0.
  rewrite Gcomm_empty; auto with set.
  auto with set.
  apply preq_mem_correct in W1; auto.
 Qed.

 Definition check_equiv_adv Gadv Gcomm inv t0 A PrPriv PrOrcl E1 :=
   (Vset.forallb Var.is_local (Vset_of_var_decl (proc_params E1 A)) &&
     Vset.forallb Var.is_global (Vset.union (fst (pdepend inv)) (snd (pdepend inv))) &&
  Vset.disjoint (fst (pdepend inv)) Gadv &&
  Vset.disjoint (snd (pdepend inv)) Gadv &&
 (Gcomm [=?] Vset.empty) &&
  (Gadv [=?] Vset.empty) &&
  negb (PrSet.mem {| BProc.p_type := t0; BProc.p_name := A |} PrOrcl) &&
   negb (PrSet.mem {| BProc.p_type := t0; BProc.p_name := A |} PrPriv))%bool.

 Lemma check_equiv_adv_correct : forall E1 E2 t
  (A:Proc.proc t) (inv:pred) (PrOrcl PrPriv:PrSet.t) (Gadv Gcomm:Vset.t),
  Eq_adv_decl PrOrcl PrPriv E1 E2 ->
  Eq_orcl_params PrOrcl E1 E2 ->
  (forall o : ProcD.t, PrSet.mem o PrOrcl ->
   Equiv (eq_param (proc_params E1 (BProc.p_name o))
        (proc_params E2 (BProc.p_name o)) /_\ inv)
   E1 (proc_body E1 (BProc.p_name o)) E2 (proc_body E2 (BProc.p_name o))
   (e2E side_left (proc_res E1 (BProc.p_name o)) ===
     e2E side_right (proc_res E2 (BProc.p_name o)) /_\ inv)) ->
  WFAdv PrOrcl PrPriv Gadv Gcomm E1 A ->
  check_equiv_adv Gadv Gcomm inv A PrPriv PrOrcl E1 = true ->
  Equiv (eq_param (proc_params E1 A) (proc_params E2 A) /_\ inv) 
  E1 (proc_body E1 A) 
  E2 (proc_body E2 A)
  (e2E side_left (proc_res E1 A) === e2E side_right (proc_res E2 A) /_\ inv).
 Proof.
  intros.
  unfold Equiv.
  unfold check_equiv_adv in H3.
  repeat (rewrite andb_true_iff in H3).
  decompose [and] H3; clear H3.
  apply VsetP.eqb_eq in H8.
  apply VsetP.eqb_eq in H9.
  eapply equiv_sub.
  3:apply equiv_adv with 
   (PrOrcl := PrOrcl) (PrPriv := PrPriv) (Gadv := Gadv) 
   (Gcomm := Gcomm) (inv := inv)
    (X1 := fst (pdepend inv)) (X2 := snd (pdepend inv)); intros; simpl; auto.
  intros k m1 m2.
  unfold ipred; simpl; rewrite !peval_pand; intros.
  split.
  apply preq_mem_correct.
  red; rewrite H8; auto.
  trivial.
  intros k m1 m2.
  unfold ipred; simpl; rewrite !peval_pand, !peval_peq; intros.
  tauto.
  rewrite H8 in H3.
  elim (Vset.empty_spec H3).
  rewrite H9 in H3.
  elim (Vset.empty_spec H3).
  destruct (pdepend inv); auto.
  eapply Vset.forallb_correct; eauto.
  intros ? ? H6; unfold VarP.Edec.eq in H6; subst; trivial.
  eapply equiv_sub.
  3: apply (H1 _ H3).
  intros k m1 m2.
  unfold ipred; simpl; rewrite !peval_pand; intros.
  tauto.
  intros k m1 m2.
  unfold ipred; simpl; rewrite !peval_pand, !peval_peq; intros.
  split.
  apply preq_mem_correct.
  red; rewrite H8; auto.
  trivial.
  apply is_true_negb; trivial.
  apply is_true_negb; trivial.
  eapply Vset.forallb_correct; eauto.
  intros ? ? H6; unfold VarP.Edec.eq in H6; subst; trivial.
Qed.
     

 Definition eq_exp t1 (d1:dlist E.expr t1) t2 (d2:dlist E.expr t2) : pred.
 induction 1; simpl; intros.
 destruct d2.
 exact Ptrue.
 exact Pfalse.
 destruct d2.
 exact Pfalse.

 destruct d1.
 destruct d2.
 destruct (T.eq_dec a a0); subst.
 exact (peq (e2E side_left p) (e2E side_right e)).
 exact Pfalse.
 exact Pfalse.
 destruct (T.eq_dec a a0); subst.
 exact (pand (Peq (e2E side_left p) (e2E side_right e)) (IHd1 _ d2)).
 exact Pfalse.
 Defined.

Lemma Equiv_wrapper : forall E1 t (f1 : Proc.proc t) (r1 : Var.var t) (d1 : E.args (Proc.targs f1))
  E2 (f2 : Proc.proc t) (r2 : Var.var t) (d2 : E.args (Proc.targs f2)) P Q
  (W : EquivFun P E1 f1 E2 f2 Q) (Hr1 : Var.is_local r1)  (Hr2 : Var.is_local r2),
  let s :=  make_assoc_var_exp side_left (proc_params E1 f1) d1 
             (make_assoc_var_exp side_right (proc_params E2 f2) d2 nil) in
  Equiv (psubst_para P s) E1 [r1 <c- f1 with d1] E2 [r2 <c- f2 with d2] 
  (psubst (psubst Q (VarLeft (eqf_res1 W)) (VarLeft r1))
      (VarRight (eqf_res2 W)) (VarRight r2)).
Proof.
  intros.
  destruct W.
  simpl.
  apply equiv_call with (3 := eqf_equiv0).
  unfold ipred; intros.
  rewrite psubst_para_correct in H.
  unfold s in H.
  rewrite !mem_upd_paral_make_assoc in H;unfold mem_upd_paral in H;simpl in H.
  unfold only_params_or_global in eqf_pre0.
  refine (pdepend_correct P _ _ H).

    destruct (pdepend P) as (X1,X2); rewrite is_true_andb in eqf_pre0;destruct eqf_pre0;simpl.
    red;intros; case_eq (Var.is_global x);intros.
    rewrite init_mem_global;trivial.
    rewrite make_assoc_not_in;trivial.
    rewrite mem_upd_para1_make_assoc2;trivial.
    unfold proc_params; destruct (E1 _ f1);simpl.
    intros Hin;apply d_all_local0 in Hin.
    unfold Var.is_global in H3; unfold Var.vis_local in Hin.
    simpl in H3, Hin;rewrite H3 in Hin;discriminate.
    rewrite <- negb_true_iff in H3;assert (W:= get_locals_complete _ _ H2 H3).
    assert (Hin := Vset.subset_correct H0 _ W);clear W.
    destruct (get_arg_make_assoc m1 m2 nil x (proc_params E1 f1) d1
       (make_assoc_var_exp side_right (proc_params E2 f2) d2 nil)) as (e1,(Hget,He1));trivial.
    rewrite <- He1.
    generalize (lookup_init_mem E1 f1 d1 m1 x);rewrite Hget;auto.

    destruct (pdepend P) as (X1,X2); rewrite is_true_andb in eqf_pre0;destruct eqf_pre0;simpl.
    red;intros; case_eq (Var.is_global x);intros.
    rewrite mem_upd_para2_make_assoc1.
    rewrite init_mem_global;trivial.
    rewrite make_assoc_not_in2;trivial.
    unfold proc_params;destruct (E2 _ f2);simpl.
    intros Hin;apply d_all_local0 in Hin.
    unfold Var.is_global in H3; unfold Var.vis_local in Hin.
    simpl in H3, Hin;rewrite H3 in Hin;discriminate.
    rewrite <- negb_true_iff in H3;assert (W:= get_locals_complete _ _ H2 H3).
    assert (Hin := Vset.subset_correct H1 _ W);clear W.
    rewrite mem_upd_para2_make_assoc1. 
    destruct (get_arg_make_assoc2 m1 m2 nil x (proc_params E2 f2) d2 nil) as (e1,(Hget,He1));trivial.
    rewrite <- He1.
    generalize (lookup_init_mem E2 f2 d2 m2 x);rewrite Hget;auto.

    unfold s; apply disjoint_subset_r with Vset.empty.
    rewrite !sfv_make_assoc;compute;trivial.
    apply VsetP.disjoint_sym;trivial.
    unfold ipred, wp_return; intros; simpl.

    apply psubst_correct.
    apply disjoint_subset_r with Vset.empty.
    reflexivity.
    apply VsetP.disjoint_sym;trivial.
    simpl.
    apply psubst_correct.
    apply disjoint_subset_r with Vset.empty.
    reflexivity.
    apply VsetP.disjoint_sym;trivial.
    simpl.
    apply psubst_correct in H0; simpl in H0.

    apply psubst_correct in H0; simpl in H0.
    rewrite pdepend_correct_aux.
    apply H0.
    rewrite !e2E_correct; simpl.
    red; intros.
    unfold only_global_or_res in eqf_post0.
    destruct (Var.eq_dec x eqf_res3).
    inversion e; clear e; subst.
    apply T.inj_pair2 in H4; subst.
    rewrite !Mem.get_upd_same.
    rewrite return_mem_dest; trivial.
    rewrite !Mem.get_upd_diff; auto.
    assert (Var.is_global x).
    destruct (pdepend Q).
    rewrite is_true_andb in eqf_post0;destruct eqf_post0.
      destruct x;trivial.
      assert (Hl:= get_locals_complete _ _ H1 (refl_equal _)).
      apply Vset.subset_correct with (x := Var.mkV (Var.Lvar t1 p)) in H2;trivial.
      assert (W := Vset.singleton_complete _ _ H2).
      elim n.
      auto.
    rewrite return_mem_global; trivial.
    intro Heq.
    clear H.
    inversion Heq; subst.
    apply T.inj_pair2 in H4; subst.
    unfold Var.is_local in Hr1.
    rewrite H2 in Hr1; discriminate.

    rewrite !e2E_correct; simpl.
    red; intros.
    unfold only_global_or_res in eqf_post0.
    destruct (Var.eq_dec x eqf_res4).
    inversion e; clear e; subst.
    apply T.inj_pair2 in H4; subst.
    rewrite !Mem.get_upd_same.
    rewrite return_mem_dest; trivial.
    rewrite !Mem.get_upd_diff; auto.
    assert (Var.is_global x).
    destruct (pdepend Q).
    rewrite is_true_andb in eqf_post0;destruct eqf_post0.
      destruct x;trivial.
      assert (Hl:= get_locals_complete _ _ H1 (refl_equal _)).
      apply Vset.subset_correct with (x := Var.mkV (Var.Lvar t1 p)) in H3;trivial.
      assert (W := Vset.singleton_complete _ _ H3).
      elim n.
      auto.
    rewrite return_mem_global; trivial.
    intro Heq.
    clear H.
    inversion Heq; subst.
    apply T.inj_pair2 in H4; subst.
    unfold Var.is_local in Hr2.
    rewrite H2 in Hr2; discriminate.
  
    apply disjoint_subset_r with Vset.empty.
    rewrite lfv_e2E.
    reflexivity.
    apply VsetP.disjoint_sym;trivial.
    apply disjoint_subset_r with Vset.empty.
    rewrite lfv_e2E.
    reflexivity.
    apply VsetP.disjoint_sym;trivial.
Qed.




 Definition mk_lvar t (v : Var.var t) (side : bool) :=
  if side then VarLeft v else VarRight v.

 
 Definition add_pi_info E (info:eq_refl_info E) 
  (fr:T.type) (f:Proc.proc fr) (p:proc_eq_refl_info E f) : eq_refl_info E :=
  fun gr : T.type =>
   match T.eq_dec fr gr with
   | left Heqr => 
     match Heqr in (_ = y0) return
      (forall g : Proc.proc y0, option (proc_eq_refl_info E g))
     with
     | eq_refl => fun g : Proc.proc fr =>
       match Proc.eq_dec f g with
        | left Heqf =>  
          match Heqf in (_ = y0) return (option (proc_eq_refl_info E y0)) 
          with
          | eq_refl => Some p
          end
        | right _ => info fr g
       end
     end
    | right _ => fun g : Proc.proc gr => info gr g
   end.

  Definition build_refl_info E (info:eq_refl_info E) 
   (t:T.type) (f:Proc.proc t) : eq_refl_info E :=
  match build_refl_info_rm 100 info f Vset.empty with
   | Some i => add_pi_info info i
   | None => info
  end.
 
 Ltac check_proof pi1 pi2 is_uniform His_uniform is_full His_full rule :=
  match goal with
   [ |- Equiv ?P ?E1 ?c1 ?E2 ?c2 ?Q ] =>
   let Heq := fresh "Heq" in
   let cond := fresh "cond" in
    compute_assertion Heq cond 
    (@check_proof E1 E2 pi1 pi2 is_uniform is_full P c1 c2 Q rule nil);
    apply check_proof_correct with (1:=His_uniform) (2:=His_full) (3:=Heq); 
     clear Heq cond
  end.
 
 Ltac check_proof_check pi1 pi2 is_uniform is_full rule :=
  match goal with
   [ |- Equiv ?P ?E1 ?c1 ?E2 ?c2 ?Q ] =>
   let Heq := fresh "Heq" in
   let cond := fresh "cond" in
    compute_assertion Heq cond 
    (@check_proof E1 E2 pi1 pi2 is_uniform is_full P c1 c2 Q rule nil)
  end.

 Ltac simpl_goal := 
  (apply Forall_cons; [ unfold interp_cond1, ipred; simpl | simpl_goal]) || 
  apply Forall_nil.

 Definition empty_refl_info E : eq_refl_info E := (fun _ _ => None).
 
 Definition build_adv_info_lossless E (pi:eq_refl_info E) 
  (PrOrcl PrPriv:PrSet.t) (Gadv Gcomm:Vset.t) (t:T.type) (f:Proc.proc t)
  (W:WFAdv PrOrcl PrPriv Gadv Gcomm E f) (L:lossless E (proc_body E f)) :=
  @build_adv_info  E pi PrOrcl PrPriv Gadv Gcomm t f W true (fun _ => L).

 Definition build_adv_refl_info E (info:eq_refl_info E) (PrOrcl PrPriv:PrSet.t) 
  (Gadv Gcomm:Vset.t) (t:T.type) (f:Proc.proc t) 
  (W:WFAdv PrOrcl PrPriv Gadv Gcomm E f) 
  (L:lossless E (proc_body E f)) : eq_refl_info E :=
  match build_adv_info_lossless info W L with
   | Some i => add_pi_info info i
   | None => info
  end.

 Definition print_refl_info := 
  fun (E : env) (pii : eq_refl_info E) (fr : T.type) (f : Proc.proc fr) =>
   match pii _ f with
    | Some pif => Some (dpi pif)
    | None => None
   end.

Definition hoare k (m1 m2 : Mem.t k) (E : env) (P : pred) (c : cmd) (Q : pred) :=
  ipred P m1 m2 -> range (fun m' => @ipred Q k m' m2) (([[ c ]]) E m1).

Lemma hoare_nil : forall k (m1 m2 : Mem.t k) E (P Q : pred),
  (@ipred P k m1 m2 -> @ipred Q k m1 m2) ->
  hoare m1 m2 E P nil Q.
Proof.
  intros; unfold hoare.
  rewrite deno_nil; intros.
  unfold range, mu; simpl; intros; auto.
Qed.

Lemma hoare_false : forall k (m1 m2 : Mem.t k) E c (Q : pred),
  hoare m1 m2 E Pfalse c Q.
Proof.
  intros; unfold hoare, ipred; simpl; intros. 
  elim H.
Qed.

Lemma hoare_assign : forall k (m1 m2 : Mem.t k) E Q t (x:Var.var t) (e : E.expr t),
  hoare m1 m2 E (psubst Q (VarLeft x) (e2E side_left e)) [ x <- e ] Q.
Proof.
  intros; unfold hoare; rewrite deno_assign; simpl.
  unfold range, mu; simpl; intros.
  apply H0.
  apply psubst_correct in H; simpl in H.
  rewrite e2E_correct in H; simpl in H.
  apply H.
  apply disjoint_subset_r with Vset.empty.
  rewrite lfv_e2E; auto with set.
  apply VsetP.disjoint_sym; auto with set.
Qed.

Lemma hoare_strengthen : forall (k : nat) (m1 m2 : Mem.t k) (E : env) (c : cmd) (P Q R : pred),
  (@ipred P k m1 m2-> @ipred R k m1 m2) -> 
  hoare m1 m2 E R c Q -> hoare m1 m2 E P c Q.
Proof.
 unfold hoare; intros; apply H0; auto.
Qed.

Lemma hoare_weaken : forall (k : nat) (m1 m2 : Mem.t k) (E : env) (c : cmd) (P Q R : pred),
  (forall m1' m2': Mem.t k, @ipred R k m1' m2' -> @ipred Q k m1' m2') ->
  hoare m1 m2 E P c R -> hoare m1 m2 E P c Q.
Proof.
 unfold hoare; intros.
 apply H0 in H1.
 eapply range_weaken; eauto; simpl; auto.
Qed.

Lemma hoare_sub : forall (k : nat) (m1 m2 : Mem.t k) (E : env) (c : cmd) (P Q P' Q' : pred),
 (@ipred P k m1 m2 -> @ipred P' k m1 m2) ->  
 (forall m1' m2': Mem.t k, @ipred Q' k m1' m2' -> @ipred Q k m1' m2') ->  
  hoare m1 m2 E P' c Q' -> hoare m1 m2 E P c Q.
Proof.
 intros.
 apply hoare_weaken with Q'; trivial.
 apply hoare_strengthen with P'; trivial.
Qed.

Lemma hoare_cond : forall k (m1 m2 : Mem.t k) E P Q c1 c2 (b : E.expr T.Bool),
  hoare m1 m2 E (pand P (pexp (e2E side_left b))) c1 Q ->
  hoare m1 m2 E (pand P (pnot (pexp (e2E side_left b)))) c2 Q ->
  hoare m1 m2 E P [If b then c1 else c2] Q.
Proof.
 unfold hoare, range, ipred, pexp; intros.
 rewrite deno_cond_elim.
 case_eq (E.eval_expr b m1); intros He.
 apply H; auto.
 apply peval_pand; split; trivial; simpl.
 rewrite e2E_correct; simpl; trivial.
 apply H0; auto.
 apply peval_pand; split; trivial; simpl.
 rewrite e2E_correct; simpl; trivial; intro.
 rewrite He in H3; discriminate.
Qed.

Lemma hoare_cons : forall k (m1 m2 : Mem.t k) E P Q R i c,
  hoare m1 m2 E P [i] R ->
  (forall (m1 : Mem.t k), hoare m1 m2 E R c Q) ->
  hoare m1 m2 E P (i :: c) Q.
Proof.
 unfold hoare, range; intros.
 rewrite deno_cons_elim, Mlet_simpl.
 apply H; trivial.
 intros.
 apply H0; trivial.
Qed.

Lemma hoare_app : forall k (m1 m2 : Mem.t k) E P Q R c1 c2,
  hoare m1 m2 E P c1 R ->
  (forall (m1 : Mem.t k), hoare m1 m2 E R c2 Q) ->
  hoare m1 m2 E P (c1 ++ c2) Q.
Proof.
 unfold hoare, range; intros.
 rewrite deno_app_elim.
 apply H; trivial.
 intros.
 apply H0; trivial.
Qed.

Lemma hoare_wp_asgn : forall k (m1 m2 : Mem.t k) E c c' P Q Q',
  wp_asgn side_left c Q = (Q', c') ->
  hoare m1 m2 E P c' Q' ->
  hoare m1 m2 E P c Q.
Proof.
  intros.
  assert (W := @wp_asgn_correct side_left E c c' Q Q' H).
  decompose [and] W; clear W; simpl in *.
  rewrite <- (firstn_skipn (length c') c).
  eapply hoare_app.
  rewrite <- H3; eauto.
  intros.
  unfold hoare; intros.
  auto.
Qed.

Lemma Hoare_random_forall : forall k (m1 m2 : Mem.t k) E Q t (x v : Var.var t) (s:E.support t),
  ~ Vset.mem x (pbind Q) ->
  ~ Vset.mem x (pfv Q) ->
  hoare m1 m2 E (pforall x (psubst Q v <1> (VarLogic x))) [ v <$- s ] Q.
Proof.
  intros; unfold hoare.
  unfold ipred; simpl; intros.
  rewrite deno_random; simpl.
  eapply range_Mlet.
  apply range_True.
  intros x0 _.
  unfold range; simpl; intros.
  apply H2.
  assert (W:= @psubst_correct k m1 m2 _ (v<1>) (VarLogic x) 
    Q ({| t := t0; var := x; val := x0 |} :: nil)).
  simpl in W; rewrite assoc_same in W;[ | apply veqb_refl].
  rewrite <- (peval_notfv (m1 {!v <-- x0!}) m2 x x0 nil Q H0), <- W; trivial.
  apply disjoint_pbind; trivial.
Qed.
  
Definition hoare_rnd_disj Q t (y : Var.var t) (d:E.support t) (x : Var.t) :=
  let fv := pfv Q in
  let bind := pbind Q in
  let vq := cast_var x t in
  let q := VarLogic vq in
  let y1 := y <1> in
  let (cond, bound) := bound_random side_left d q Ptrue in
  let P := pand cond (pforall vq (pimplies bound (psubst Q y1 q))) in
    if Vset.mem vq fv || Vset.mem vq bind
      then None else Some P.

Lemma hoare_random k (m1 m2 : Mem.t k) E P Q t (y : Var.var t) (s:E.support t) (x : Var.t) :
  hoare_rnd_disj Q y s x = Some P ->
  hoare m1 m2 E P [ I.Instr (I.Random y s) ] Q.
Proof.
  intros k m1 m2 E P Q t y s x; unfold hoare_rnd_disj.
  case_eq (bound_random side_left s (VarLogic (cast_var x t)) Ptrue); intros cond bound Hbr.
  match goal with |- (if ?T then _ else _) = _ -> _ =>
    case_eq T;[ discriminate | ] end.
  intros Hmem Heq; injection Heq; clear Heq; intros; subst.
  rewrite orb_false_iff in Hmem; destruct Hmem as (Hmem1, Hmem2).
  rewrite <- not_is_true_false in Hmem1, Hmem2.
  revert t s y Hbr Hmem1 Hmem2.
  unfold bound_random; destruct s; intros v Hbr Hmem1 Hmem2;
    injection Hbr; clear Hbr; intros; subst;
      try (rewrite pand_Ptrue, pimplies_Ptrue); try apply Hoare_random_forall; trivial.
  unfold hoare, ipred, pforall, ple; intros.
  apply peval_pand in H; destruct H.
  Opaque pimplies.
  simpl in H0, H.
  Transparent pimplies.
  assert (forall x, In x (E.eval_support [e,,e0] m1) -> ipred Q (m1 {!v <-- x!}) m2).
  unfold ipred; simpl; intros.
  assert (W:= H0 x0); rewrite peval_pimplies in W.
  assert (W1:= @psubst_correct k m1 m2 _ (v<1>) (VarLogic (cast_var x T.Zt)) Q 
    ({| t := T.Zt; var := cast_var x T.Zt; val := x0 |} :: nil)).
  simpl in W1; rewrite assoc_same in W1; [ | apply veqb_refl].
  rewrite <- (peval_notfv (m1 {!v <-- x0!}) m2 (cast_var x T.Zt) x0 nil Q), 
    <- W1; trivial; [ | apply disjoint_pbind]; trivial.
  apply W; revert H; simpl; 
    rewrite assoc_same, !e2E_correct; simpl; intros;[ | apply veqb_refl].
  apply Z_support_bounded; trivial.
  unfold range; intros.
  rewrite deno_random_elim; simpl.
  set (d := Z_support (E.eval_expr e m1) (E.eval_expr e0 m1)).
  assert (forall n, (n <= (length d))%nat ->
    0 ==
    comp Uplus 0
    (fun n : nat =>
     [1/]1+Peano.pred (length d) * f (m1 {!v <-- nth n d 0%Z!})) n)%U; auto with arith.
  induction n; simpl; intros; trivial. 
  assert (W := H2 (m1 {!v <-- nth n d 0%Z!})).
  rewrite <- W.
  repeat Usimpl; apply IHn; auto with arith.
  apply H1.
  apply nth_In; auto with arith.
Qed.

Lemma hoare_call : forall (k : nat) (m1 m2 : Mem.t k) E (P Q pre post : pred) 
  (t : T.type) (x : Var.var t) (f : Proc.proc t) (la : E.args (Proc.targs f)),
  (ipred P m1 m2 -> ipred pre (init_mem E f la m1) (init_mem E f la m2)) ->
  (forall m1' m2' : Mem.t k, ipred P m1 m2 -> ipred post m1' m2' -> ipred Q (return_mem E x f m1 m1') m2) ->
  hoare (init_mem E f la m1) (init_mem E f la m2) E pre (proc_body E f) post ->
  hoare m1 m2 E P [x <c- f with la] Q.
 Proof.
  unfold hoare, range; intros.
  rewrite deno_call_elim.
  apply H1; auto.
  intros.
  apply H3.
  eapply H0; trivial.
  apply H4.
Qed.

Section CHECK_PROOF_HOARE.

Variable E : env. 

 Definition hwp_asgn (i:I.instr) (Q:pred) : option pred :=
  match i with
   | I.Instr (I.Assign t v e) => Some (wp_ass side_left v e Q)
   | _ => None
  end.

  Lemma hwp_asgn_correct : forall k (m1 m2 : Mem.t k) E Q Q' i,
    hwp_asgn i Q = Some Q' ->
    (lossless E [i] /\ hoare m1 m2 E Q' [i] Q).
  Proof.
   intros; destruct i; simpl in *; try discriminate.
   destruct b; simpl in *; split; try discriminate.
   apply lossless_assign.
   injection H; intros; subst.
   unfold wp_ass; simpl; apply hoare_assign.
 Qed.
    
  Fixpoint hwp (c:cmd) (Q:pred) : pred * cmd :=
   match c with
    | nil => (Q, nil)
    | i :: c' => 
     match hwp c' Q with
      | (Q', c'') =>
       match c'' with
        | nil => 
         match hwp_asgn i Q' with
          | None => (Q', i :: nil)
          | Some Q'' => (Q'', nil)
         end
        | _ :: _ => (Q', i :: c'')
       end
     end
   end.

  Lemma hwp_correct : forall (c c':cmd) (Q Q':pred) k (m1 m2 : Mem.t k),
   hwp c Q = (Q', c') ->
   lossless E (skipn (length c') c) /\
   c' = firstn (length c') c /\
   hoare m1 m2 E Q' (skipn (length c') c) Q.
  Proof.
   induction c; simpl; intros.
   injection H; clear H; intros; subst.
   split; [apply lossless_nil | split; intros; trivial].
   apply hoare_nil; intros; auto.
   revert H.
   case_eq (hwp c Q).
   intros p [ | i0 l0] Heq.
   case_eq (hwp_asgn a p); intros.
   inversion H0; clear H0; subst; simpl in *; auto.
   destruct (hwp_asgn_correct m1 m2 E _ _ H) as (Hli, Hr).
   split; [apply lossless_cons | split ]; trivial.
   apply IHc with (k := k) (m1 := m1) (m2 := m2) in Heq; trivial.
   simpl in *; tauto.
   apply hoare_cons with (R := p); intros; trivial.
   apply IHc with (k := k) (m1 := m0) (m2 := m2) in Heq; trivial.
   tauto.
   inversion H0; clear H0; subst; simpl in *; auto.
   apply IHc with (k := k) (m1 := m1)  (m2 := m2) in Heq.
   split; [ | split ]; trivial; tauto.
   intros H3; injection H3; clear H3; intros; subst.
   set (c1:= i0::l0) in *.
   revert Heq; generalize c1; clear c1; intros.
   apply IHc with (k := k) (m1 := m1)  (m2 := m2) in Heq.
   split; [ | split]; trivial; simpl; try tauto.
   simpl; f_equal; tauto.
  Qed.

  Record HoareFun t P (f : Proc.proc t) Q :=
    { 
      hf_res : Var.var t;
      hf_hoare : forall k (m1 m2 : Mem.t k), hoare m1 m2 E P (proc_body E f) (wp_return E f E f Q hf_res hf_res);
      hf_pre   : only_params_or_global E f E f P;
      hf_post  : only_global_or_res f f Q hf_res hf_res
    }.

  Inductive HoareFun_info := 
  | Mk_HoareFun_info : forall t pre (f:Proc.proc t) post,  
    HoareFun pre f post -> HoareFun_info.


Lemma hoare_wrapper : forall (k : nat) (m1 m2 : Mem.t k) (P Q : pred) 
  (t : T.type) (x : Var.var t) (f : Proc.proc t) (la : E.args (Proc.targs f)) (Hx : Var.is_local x)
  (W : HoareFun P f Q)
  (WQ : snd (pdepend Q) [=] Vset.empty),
  let s :=  make_assoc_var_exp side_left (proc_params E f) la
    (make_assoc_var_exp side_right (proc_params E f) la nil) in
  hoare m1 m2 E (psubst_para P s) [x <c- f with la] 
  (psubst (psubst Q (VarLeft (hf_res W)) (VarLeft x))
      (VarRight (hf_res W)) (VarRight x)).
 Proof.
   intros; destruct W; simpl.
   apply hoare_call with (3 := @hf_hoare0 k (init_mem E f la m1) (init_mem E f la m2)).

   unfold ipred; intros.
   rewrite psubst_para_correct in H.
   unfold s in H.
   rewrite !mem_upd_paral_make_assoc in H;unfold mem_upd_paral in H;simpl in H.
   unfold only_params_or_global in hf_pre0.
   refine (pdepend_correct P _ _ H).

    destruct (pdepend P) as (X1,X2); rewrite is_true_andb in hf_pre0;destruct hf_pre0;simpl.
    red;intros; case_eq (Var.is_global x0);intros.
    rewrite init_mem_global;trivial.
    rewrite make_assoc_not_in;trivial.
    rewrite mem_upd_para1_make_assoc2;trivial.
    unfold proc_params; destruct (E f);simpl.
    intros Hin;apply d_all_local0 in Hin.
    unfold Var.is_global in H3; unfold Var.vis_local in Hin.
    simpl in H3, Hin;rewrite H3 in Hin;discriminate.
    rewrite <- negb_true_iff in H3;assert (W:= get_locals_complete _ _ H2 H3).
    assert (Hin := Vset.subset_correct H0 _ W);clear W.
    destruct (get_arg_make_assoc m1 m2 nil x0 (proc_params E f) la
       (make_assoc_var_exp side_right (proc_params E f) la nil)) as (e1,(Hget,He1));trivial.
    rewrite <- He1.
    generalize (lookup_init_mem E f la m1 x0);rewrite Hget;auto.

    destruct (pdepend P) as (X1,X2); rewrite is_true_andb in hf_pre0;destruct hf_pre0;simpl.
    red;intros; case_eq (Var.is_global x0);intros.
    rewrite mem_upd_para2_make_assoc1.
    rewrite init_mem_global;trivial.
    rewrite make_assoc_not_in2;trivial.
    unfold proc_params;destruct (E f);simpl.
    intros Hin;apply d_all_local0 in Hin.
    unfold Var.is_global in H3; unfold Var.vis_local in Hin.
    simpl in H3, Hin;rewrite H3 in Hin;discriminate.
    rewrite <- negb_true_iff in H3;assert (W:= get_locals_complete _ _ H2 H3).
    assert (Hin := Vset.subset_correct H1 _ W);clear W.
    rewrite mem_upd_para2_make_assoc1. 
    destruct (get_arg_make_assoc2 m1 m2 nil x0 (proc_params E f) la nil) as (e1,(Hget,He1));trivial.
    rewrite <- He1.
    generalize (lookup_init_mem E f la m2 x0);rewrite Hget;auto.

    unfold s; apply disjoint_subset_r with Vset.empty.
    rewrite !sfv_make_assoc;compute;trivial.
    apply VsetP.disjoint_sym;trivial.
    unfold ipred, wp_return; intros; simpl.

    apply psubst_correct.
    apply disjoint_subset_r with Vset.empty.
    reflexivity.
    apply VsetP.disjoint_sym;trivial.
    simpl.
    apply psubst_correct.
    apply disjoint_subset_r with Vset.empty.
    reflexivity.
    apply VsetP.disjoint_sym;trivial.
    simpl.
    apply psubst_correct in H0; simpl in H0.
    apply psubst_correct in H0; simpl in H0.
    rewrite pdepend_correct_aux.
    apply H0.
    rewrite !e2E_correct; simpl.
    red; intros.
    unfold only_global_or_res in hf_post0.
    destruct (Var.eq_dec x0 hf_res0).
    inversion e; clear e; subst.
    apply T.inj_pair2 in H4; subst.
    rewrite !Mem.get_upd_same.
    rewrite return_mem_dest; trivial.
    rewrite !Mem.get_upd_diff; auto.
    assert (Var.is_global x0).
    destruct (pdepend Q).
    rewrite is_true_andb in hf_post0;destruct hf_post0.
      destruct x0;trivial.
      assert (Hl:= get_locals_complete _ _ H1 (refl_equal _)).
      apply Vset.subset_correct with (x := Var.mkV (Var.Lvar t1 p)) in H2;trivial.
      assert (W := Vset.singleton_complete _ _ H2).
      elim n.
      auto.
    rewrite return_mem_global; trivial.
    intro Heq.
    clear H.
    inversion Heq; subst.
    apply T.inj_pair2 in H4; subst.
    unfold Var.is_local in Hx.
    rewrite H2 in Hx; discriminate.

    rewrite !e2E_correct; simpl.
    red; intros.
    rewrite WQ in H1.
    elim (Vset.empty_spec H1).
  
    apply disjoint_subset_r with Vset.empty.
    rewrite lfv_e2E.
    reflexivity.
    apply VsetP.disjoint_sym;trivial.
    apply disjoint_subset_r with Vset.empty.
    rewrite lfv_e2E.
    reflexivity.
    apply VsetP.disjoint_sym;trivial.
Qed.

Inductive HlRule : Type :=
| Cempty : HlRule
| Crandom : Var.t -> HlRule -> HlRule
| Ccond : HlRule -> HlRule -> HlRule -> HlRule
| Ccall : list Var.t ->  HoareFun_info -> HlRule -> HlRule.

Variable pi : eq_refl_info E.

Fixpoint wp_hl (c : cmd) (Q:pred) (d:HlRule) {struct d} : pred :=
  let (Q,c) := hwp c Q in
    match (rev c), d with
      |  (If e then c1 else c2) :: c', Ccond d1 d2 d' =>
         let Q1 := wp_hl c1 Q d1 in
         let Q2 := wp_hl c2 Q d2 in
           wp_hl (rev c') (pif (e2E side_left e) Q1 Q2) d'
      |  I.Instr (I.Random t v d) :: c', Crandom v' d' => 
        match hoare_rnd_disj Q v d v' with
          | Some Q' =>  wp_hl (rev c') Q' d'
          | None => Pfalse
        end
     | I.Call t' x f' args :: c', Ccall fresh i d' => 
        let (t,pre,f,post,equ) := i in
          if snd (pdepend pre) [=?] Vset.empty then
          if snd (pdepend post) [=?] Vset.empty then
          if (Proc.eqb f f')%bool then
            match pi f' with
              | None => Pfalse
              | Some i =>
                let f_modify := pi_mod i in
                let s :=  make_assoc_var_exp side_left (proc_params E f') args 
                  (make_assoc_var_exp side_right (proc_params E f') args nil) in
                let pre0 := psubst_para pre s in
                let res := cast_var (hf_res equ) t' in
                let p := psubst Q x <1> res <1> in
                let p1 := pimplies post p in
                let p2 := forall_fresh_l p1 (Var.mkV res :: nil) (map get_pos fresh) in
                let p3 := forall_fresh_l p2 f_modify (tl (map get_pos fresh)) in
                let (X1, X2) := pdepend Q in
                if Vset.mem res X1
                  then Pfalse
                  else wp_hl (rev c') (pand pre0 p3) d'
               end
            else Pfalse
            else Pfalse
            else Pfalse
      | nil, _ => Q  
      | _, _ => Pfalse
    end.

Lemma hoare_m2 : forall k (m1 m2 m2' : Mem.t k) P Q c X,
  m1 =={ X}m1 ->
  pdepend P = (X, Vset.empty) ->
  pdepend Q = (X, Vset.empty) ->
  hoare m1 m2' E P c Q ->
  hoare m1 m2 E P c Q.
Proof.
 unfold hoare, range; intros k m1 m2 m2' P Q c x Hm1 HdepP HdepQ H Hp f Hq.
 unfold ipred in *.
 apply H.
 rewrite pdepend_correct_aux.
 apply Hp.
 rewrite HdepP; simpl; trivial.
 rewrite HdepP; simpl; trivial.
 intros m HmQ.
 apply Hq.
 rewrite pdepend_correct_aux.
 apply HmQ.
 rewrite HdepQ; simpl; trivial.
 rewrite HdepQ; simpl; trivial.
Qed.

    Lemma equiv_rel_pred : forall (P1 P2 Q1 Q2: mem_pred) (P: mem_rel) c1 E1 c2 E2,
     lossless E1 c1 -> lossless E2 c2 -> 
     (forall k (m:Mem.t k), Hoare m E1 P1 c1 Q1) ->
     (forall k (m:Mem.t k), Hoare m E2 P2 c2 Q2) ->
     (forall k (m1 m2:Mem.t k), P k m1 m2 -> (P1 k m1 /\ P2 k m2)) ->
     (forall k (m1:Mem.t k), sumbool (Q1 k m1) (~ Q1 k m1)) ->
     (forall k (m2:Mem.t k), sumbool (Q2 k m2) (~ Q2 k m2)) ->
     (equiv P E1 c1 E2 c2 ((rel_pred1 Q1) /-\ (rel_pred2 Q2))).
    Proof.
    intros.
    intro k.
     exists (fun m1 m2 => prod_distr ([[ c1 ]] E1 m1) ([[ c2 ]] E2 m2)); intros.
     apply H3 in H4; destruct H4.
     constructor; intros.
     rewrite prod_distr_fst; unfold lossless in H0; rewrite H0; auto.
     rewrite prod_distr_snd; unfold lossless in H; rewrite H; auto.
     unfold range, prod_distr; intros.
     rewrite Mlet_simpl.
     rewrite (@range_cover _ (Q1 k)  (([[ c1 ]]) E1 m1) (carac (X k))); auto.
     rewrite <- mu_0.
     apply mu_stable_eq.
     refine (@ford_eq_intro _ _ _ _ _); intros.
     unfold carac.
     case (X k n); intros; Usimpl; trivial.
     rewrite Mlet_simpl.
     rewrite (@range_cover _ (Q2 k)  (([[ c2 ]]) E2 m2) (carac (X0 k))); auto.
     rewrite <- mu_0.
     apply mu_stable_eq.
     refine (@ford_eq_intro _ _ _ _ _); intros.
     unfold carac.
     case (X0 k n0); intros; Usimpl; trivial.
     simpl.
     apply H6.
     split; trivial.
     apply H2; trivial.
     apply cover_dec.
     apply H1; trivial.
     apply cover_dec.
    Qed.


Lemma range_Modify : forall E X c k (m : Mem.t k) P,
  Modify E X c -> 
  range P (([[ c ]]) E m) ->
  range (fun m' : Mem.t k => P m' /\ eeq_mem X m m') (([[ c ]]) E m).
Proof.
 unfold Modify; intros.
 unfold range; intros.
 rewrite range_cover.
 2: apply H.
 2: apply ceeq_mem.
 apply H0.
 intros.
 unfold eeq_mem_dec.
 generalize (Mem.eqb_spec m (x {!X <<- m!})).
 destruct  (Mem.eqb m (x {!X <<- m!})); intros; Usimpl; auto.
 apply H1; split; trivial.
 unfold eeq_mem; intros.
 rewrite H3.
 rewrite update_mem_notin; trivial.
Qed.

Opaque forall_fresh_l.

Lemma eeq_mem_geeq_mem : forall X k (m1 m2 : Mem.t k),
  eeq_mem X m1 m2 ->
  geeq_mem (get_globals X) m1 m2.
Proof.
 unfold eeq_mem, geeq_mem; intros.
 apply H.
 intro Heq; elim H1.
 apply get_globals_complete; auto.
Qed.

Lemma wp_hl_correct : forall  d c Q Q' k (m1 m2 : Mem.t k),  
  (ipred Q' m1 m2 -> ipred (wp_hl c Q d) m1 m2) ->
  hoare m1 m2 E Q' c Q.
Proof.
  induction d; simpl; intros.

  (* Cempty *)
  revert H; case_eq (hwp c Q); intros.
  rewrite <- (rev_involutive l) in H.
  apply hwp_correct with (k := k) (m1 := m1) (m2 := m2) in H; simpl in H.
  destruct (rev l); subst; simpl in *.
  apply hoare_strengthen with (1 := H0); tauto.
  destruct i; try destruct b;
    apply hoare_strengthen with (1 := H0); 
      apply hoare_false.

  (* Crandom *)
  revert H; case_eq (hwp c Q); intros.
  rewrite <- (rev_involutive l) in H.
  destruct (rev l); subst; simpl in *.
  apply hoare_strengthen with (1 := H0).
  apply hwp_correct with (k := k) (m1 := m1) (m2 := m2) in H; simpl in H.
  tauto.
  destruct i; try destruct b; 
    try (apply hoare_strengthen with (1 := H0); apply hoare_false).
  revert H0.
  case_eq (hoare_rnd_disj p v s t0); intros.
  generalize H0; intros.
  apply hoare_random with (k := k) (m1 := m1) (m2 := m2) (E := E) in H0.
  rewrite <- (firstn_skipn (length (rev l0 ++ [v <$- s])) c).
  apply hoare_app with p.
  apply hwp_correct with (k := k) (m1 := m1) (m2 := m2) in H; simpl in H.
  decompose [and] H; clear H.
  rewrite <- H5.
  apply hoare_app with p0.
  apply IHd; trivial.
  intros.
  apply hoare_random with (k := k) (m1 := m0) (m2 := m2) (E := E) in H2; trivial.
  intros.
  apply hwp_correct with (k := k) (m1 := m0) (m2 := m2) in H; simpl in H; tauto.
  apply hoare_strengthen with (1 := H1);  apply hoare_false.

  (* Ccond *)
  revert H; case_eq (hwp c Q); intros.
  rewrite <- (rev_involutive l) in H.
  destruct (rev l); subst; simpl in *.
  apply hwp_correct with (k := k) (m1 := m1) (m2 := m2) in H; simpl in H.
  apply hoare_strengthen with (1 := H0); tauto.
  destruct i; try destruct b; 
    try (apply hoare_strengthen with (1 := H0); apply hoare_false).
  generalize H; intros.
  apply hwp_correct with (k := k) (m1 := m1) (m2 := m2) in H; simpl in H.
  rewrite <- (firstn_skipn (length (rev l0 ++ [If e then l1 else l2])) c).
  apply hoare_app with p.
  decompose [and] H; clear H.
  rewrite <- H4.
  apply hoare_app with (pif (e2E side_left e) (wp_hl l1 p d1) (wp_hl l2 p d2)).
  apply IHd3; trivial.
  intros.
  apply hoare_cond.
  apply IHd1; intros.
  apply peval_pand in H; destruct H.
  apply peval_pif in H; unfold pexp in H3; simpl in H, H3.
  rewrite H3 in H; trivial.
  apply IHd2; intros.
  apply peval_pand in H; destruct H.
  apply peval_pif in H; unfold pexp in H3; simpl in H, H3.
  apply not_true_is_false in H3.
  rewrite H3 in H; trivial.
  intros.
  apply hwp_correct with (k := k) (m1 := m0) (m2 := m2) in H1; simpl in H1; tauto.

  (* Ccall *)
  revert H; case_eq (hwp c Q); intros Qass c' H.
  rewrite <- (rev_involutive c') in H.
  rewrite <- (firstn_skipn (length c') c).
  intros.
  apply hoare_app with Qass.

  apply hwp_correct with (k := k) (m1 := m1) (m2 := m2) in H; simpl in H.

  revert H0.
  case_eq (rev c'); subst; simpl in *.
  destruct c'; intros; simpl in *; try discriminate.
  apply hoare_nil; auto.
  apply f_equal with (f := @rev _) in H0.
  rewrite rev_app_distr in H0.
  discriminate H0.
  intros i c'' H1.
  destruct i; try destruct b; intros;
    try (apply hoare_strengthen with (1 := H0); apply hoare_false).
  destruct h as (t, pre, f1, post, equ).
  generalize (Proc.eqb_spec_dep f1 f); destruct (Proc.eqb f1 f); intros Heq.
  inversion Heq; clear Heq; subst.
  clear H4; apply T.inj_pair2 in H5; subst.
  destruct (pi f).
  generalize (pdepend_correct Qass);destruct (pdepend Qass) as (PX1, PX2); intros HdepQ.
  revert H0.
  match goal with |- context [if ?test then _ else _] => case_eq test;intros Hsnd1 end;simpl.
  match goal with |- context [if ?test then _ else _] => case_eq test;intros Hsnd2 end;simpl.
  match goal with |- context [if ?test then _ else _] => case_eq test;intros HmemQ end;simpl.
  intros; intro.
  elim (H0 H2).
  intros.
  destruct H as [_ [H _] ].
  rewrite H1 in H at 1.
  rewrite (rev_involutive c') in H at 1.
  rewrite <- H.
  clear H H1.
  simpl.
  eapply hoare_app.
  apply IHd.
  apply H0.

  intros.
  destruct equ; simpl in *.
  unfold hoare; intros.
  rewrite deno_call.
  unfold hoare in hf_hoare0.
  apply range_Mlet with (P := (fun m' : Mem.t k =>
    ipred (wp_return E f E f post hf_res0 hf_res0) m' m2 /\
    geeq_mem (pi_mod p) (init_mem E f a m0) m')).
  destruct (mod_spec p) as [X [Hx1 Hx2] ].
  apply range_weaken with (fun m' : Mem.t k => 
    ipred (wp_return E f E f post hf_res0 hf_res0) m' m2 /\
    geeq_mem (get_globals (Vset.union X (pi_mod p))) (init_mem E f a m0) m').

  unfold geeq_mem, get_globals; intros m [W1 W2].
  split;[ trivial | ]; intros.
  apply W2; trivial.
  intro; elim H2.
  apply Vset.filter_correct in H3.
  destruct H3.
  apply VsetP.union_spec in H3; destruct H3; trivial.
  apply Hx1 in H3.
  unfold Var.is_local in H3.
  rewrite H4 in H3; discriminate.
  intros ? ? H6; unfold VarP.Edec.eq in H6; subst; trivial.

  apply range_weaken with (fun m' : Mem.t k =>
    ipred (wp_return E f E f post hf_res0 hf_res0) m' m2 /\
    eeq_mem (Vset.union X (pi_mod p)) (init_mem E f a m0) m').
  intros x [H1 H2]; split; trivial.
  apply eeq_mem_geeq_mem; trivial.
  apply range_Modify; auto.

  unfold ipred in H0; simpl in H0.
  revert hf_hoare0.
  unfold hoare, ipred, range, wp_return; intros.
  apply hf_hoare0 with (m2 := m2).
  unfold ipred in H.
  rewrite peval_pand in H; destruct H.
  rewrite psubst_para_correct in H; simpl in H.
  rewrite !mem_upd_paral_make_assoc in H; unfold mem_upd_paral in H;simpl in H0.
  unfold only_params_or_global in hf_pre0.
  refine (pdepend_correct pre _ _ H).

    destruct (pdepend pre) as (X1,X2); rewrite is_true_andb in hf_pre0;destruct hf_pre0;simpl.
    red; intros; case_eq (Var.is_global x);intros.
    rewrite init_mem_global;trivial.
    rewrite make_assoc_not_in;trivial.
    rewrite mem_upd_para1_make_assoc2;trivial.
    unfold proc_params; destruct (E f);simpl.
    intros Hin;apply d_all_local0 in Hin.
    unfold Var.is_global in H6; unfold Var.vis_local in Hin.
    simpl in H6, Hin; rewrite H6 in Hin;discriminate.
    rewrite <- negb_true_iff in H6;assert (W:= get_locals_complete _ _ H5 H6).
    assert (Hin := Vset.subset_correct H3 _ W);clear W.
    destruct (get_arg_make_assoc m0 m2 nil x (proc_params E f) a
       (make_assoc_var_exp side_right (proc_params E f) a nil)) as (e1,(Hget,He1));trivial.
    rewrite <- He1.
    generalize (lookup_init_mem E f a m0 x);rewrite Hget;auto.
    apply VsetP.eqb_eq in Hsnd1.
    rewrite Hsnd1; auto.

  apply disjoint_subset_r with Vset.empty.
  rewrite !sfv_make_assoc;compute;trivial.
  apply VsetP.disjoint_sym;trivial.

  auto.

  intros m0' [H1 H2].
 
  clear c .
  set (c := proc_body E f) in *.
  assert (Gmod := mod_global p).
  assert (Hmod := mod_spec p).
  destruct Hmod as (L, (HL, Hmod)).
  set (X:= Vset.union L (pi_mod p)) in *.

  unfold ipred in H.
  rewrite peval_pand in H; destruct H.

  clear H0.
  unfold wp_return in H1.
  apply psubst_correct in H1; simpl in H1.
  apply psubst_correct in H1; simpl in H1.
  rewrite !e2E_correct in H1; simpl in H1.

  unfold range; intros.
  rewrite Munit_eq.
  apply H0.
  unfold ipred.

  assert (geeq_mem (pi_mod p) m0 m0').
  revert H2.
  unfold geeq_mem; intros.
  rewrite <- H2; trivial.
  rewrite init_mem_global; trivial.

  assert (return_mem E v f m0 m0' = m0{!pi_mod p <<- m0'!}{!v <-- E.eval_expr (proc_res E f) m0'!}).
      apply Mem.eq_leibniz;red;intros.
      destruct (Var.eq_dec v x);subst.
      rewrite return_mem_dest, Mem.get_upd_same;trivial.
      destruct x; rewrite Mem.get_upd_diff;trivial.
      case_eq (Var.is_global v0);intros.
      rewrite return_mem_global;trivial.
      case_eq (Vset.mem v0 (pi_mod p));intros.
      rewrite update_mem_in;trivial.
      assert (~ Vset.mem v0 (pi_mod p)) by (rewrite H6; discriminate).
      symmetry;rewrite update_mem_notin;trivial.
      apply H4; trivial.
      rewrite return_mem_local;trivial.
      rewrite update_mem_notin;trivial.
      intros Hin; apply mod_global in Hin; rewrite H5 in Hin; discriminate.
      unfold Var.is_local; rewrite H5; trivial.
   rewrite H5;clear H5.

   generalize (tl (map get_pos l)) H3;clear H3;simpl.
   clear Gmod Hmod X.
   clear H H0 H2.
   revert H4.
   revert m0.
   induction (pi_mod p); intros.
   apply forall_fresh_l_nil in H3.
   apply forall_fresh_l_cons with (v :=  E.eval_expr (proc_res E f) m0') in H3.
   apply forall_fresh_l_nil in H3.
   rewrite peval_pimplies, !cast_var_eq in H3.
   assert (peval (m0 {!hf_res0 <-- E.eval_expr (proc_res E f) m0'!}) m2 nil post).
   refine (pdepend_correct _ _ _ H1);intros tx x Hin.

   destruct (Var.eq_dec x hf_res0).
   inversion e;clear e;subst.
   apply T.inj_pair2 in H2;subst.
   rewrite !Mem.get_upd_same;trivial.
   rewrite !Mem.get_upd_diff;auto.
   symmetry;apply H4;[ | discriminate].
   unfold only_global_or_res in hf_post0.
   destruct (pdepend post);simpl in *.
   rewrite is_true_andb in hf_post0;destruct hf_post0.
   destruct x;trivial.
   assert (Hl:= get_locals_complete _ _ Hin (refl_equal _)).
   apply Vset.subset_correct with (x := Var.mkV (Var.Lvar t3 p0)) in H;trivial.
   apply Vset.singleton_complete in H;elim n.
   inversion H;trivial.
   apply VsetP.eqb_eq in Hsnd2.
   rewrite Hsnd2 in Hin; auto.
   elim (Vset.empty_spec Hin).

   apply H3 in H.
   rewrite !psubst_correct in H.
   simpl in H.
   rewrite !Mem.get_upd_same in H.
   apply HdepQ with (3:= H);simpl;red;intros.
   destruct (Var.eq_dec v x).
   inversion e;clear e.
   subst t1.
   subst;rewrite !Mem.get_upd_same;trivial.
   rewrite !Mem.get_upd_diff;trivial.
   intros Heq;inversion Heq;clear Heq; subst t1.
   apply T.inj_pair2 in H6;subst.
   rewrite cast_var_eq, H0 in HmemQ;discriminate.
   trivial.
   apply VsetP.disjoint_sym;unfold lfv;simpl;trivial.
   simpl.
   destruct a0.
   apply forall_fresh_l_cons with (v:= m0' v0) in H3.
   apply IHt1 with (l0 := tl l0);trivial.
   red;intros.
   destruct (Var.eq_dec v0 x).
   inversion e; clear e; subst.
   apply T.inj_pair2 in H6;subst;rewrite Mem.get_upd_same;trivial.
   rewrite Mem.get_upd_diff;trivial.
   apply H4;[ trivial | ].
   simpl;generalize (VarP.Edec.eqb_spec x v0);destruct (VarP.Edec.eqb x v0);auto.

   unfold Vset.disjoint; rewrite lfv_e2E; apply VsetP.disjoint_sym; auto with set.
   unfold Vset.disjoint; rewrite lfv_e2E; apply VsetP.disjoint_sym; auto with set.

   intros H0; apply hoare_strengthen with (1 := H0); apply hoare_false.
   intros H0; apply hoare_strengthen with (1 := H0); apply hoare_false.

   revert H0.
   match goal with |- context [if ?test then _ else _] => case_eq test;intros H3 end;simpl.
   match goal with |- context [if ?test then _ else _] => case_eq test;intros H4 end;simpl.
   intros H0; apply hoare_strengthen with (1 := H0); apply hoare_false.
   intros H0; apply hoare_strengthen with (1 := H0); apply hoare_false.
   intros H0; apply hoare_strengthen with (1 := H0); apply hoare_false.

   revert H0.
   match goal with |- context [if ?test then _ else _] => case_eq test;intros H3 end;simpl.
   match goal with |- context [if ?test then _ else _] => case_eq test;intros H4 end;simpl.
   intros H0; apply hoare_strengthen with (1 := H0); apply hoare_false.
   intros H0; apply hoare_strengthen with (1 := H0); apply hoare_false.
   intros H0; apply hoare_strengthen with (1 := H0); apply hoare_false.

   intros.
   apply hwp_correct with (m1 := m0) (m2 := m2) in H.
   rewrite rev_involutive in H; tauto.
Qed.

End CHECK_PROOF_HOARE.

(* Eq_orcl_params *)

Definition eqb_param t (d1:dlist Var.var t) (d2:dlist Var.var t) : bool.
intros.
induction d1.
exact true.
inversion_clear d2.
case_eq (Var.veqb p X); intros.
exact (IHd1 X0).
exact false.
Defined.

Lemma eqb_param_correct : forall t (d1:dlist Var.var t) (d2:dlist Var.var t),
  eqb_param d1 d2 = true -> d1 = d2.
Proof.
refine (@dlist_ind2 _ _ _ _ _ _ _); simpl; intros; auto.
apply Teq_dec.
generalize (Var.veqb_spec p1 p2).
destruct (Var.veqb p1 p2); intros.
rewrite (H H0), H1; trivial.
discriminate.
Qed.

Definition check_Eq_orcl_params (s : PrSet.t) (E1 E2 : env) : bool :=
  PrSet.forallb (fun o => eqb_param (proc_params E1 (BProc.p_name o)) (proc_params E2 (BProc.p_name o))) s.

Lemma check_Eq_orcl_params_correct : forall (s : PrSet.t) (E1 E2 : env),
  check_Eq_orcl_params s E1 E2 = true -> 
  Eq_orcl_params s E1 E2.
Proof.
  unfold Eq_orcl_params; intros. 
  induction s; simpl in *.
  discriminate.
  generalize (PrSet.E.eqb_spec {| BProc.p_type := t0; BProc.p_name := o |} a).
  case_eq (ProcD.eqb {| BProc.p_type := t0; BProc.p_name := o |} a); intros H1 Heq; rewrite H1 in H0.
  unfold PrSet.E.eq in Heq.
  destruct a; simpl in *.
  injection Heq; intros; subst.
  apply inj_pair2_eq_dec in H2; subst.
  case_eq (eqb_param (proc_params E1 p_name) (proc_params E2 p_name)); intros H3; rewrite H3 in H.
  apply eqb_param_correct in H3; trivial.
  discriminate.
  apply Teq_dec.
  case_eq (eqb_param (proc_params E1 (BProc.p_name a)) (proc_params E2 (BProc.p_name a))); intros H3; rewrite H3 in H.
  apply IHs; trivial.
  discriminate.
Qed.

(* enviromenent *) 

Notation "l ':[{' x '}]' '<<-' v":= (l <- l.[{x<<-v}]) (at level 65).

Definition my_add_decl (fr : T.type) (f : Proc.proc fr)
   (params:var_decl(Proc.targs f)) (Hl:dforallb Var.vis_local params)
    (body:cmd) (res:E.expr fr) (E:env) : env :=
    @add_decl E fr f params Hl body res.

Record decl :=
  { decl_type : T.type;
    decl_f : Proc.proc decl_type;
    decl_params : var_decl (Proc.targs decl_f);
    decl_local : dforallb Var.vis_local decl_params;
    decl_body : cmd;
    decl_res : E.expr decl_type}.

Definition my_add_decl' (d : decl) (E:env) : env :=
    @add_decl E (decl_type d) (decl_f d) (decl_params d) (decl_local d) (decl_body d) (decl_res d).

Fixpoint my_add_decls (d : list decl) (E : env) : env :=
  match d with
    | nil => E
    | i :: d' => my_add_decl' i (my_add_decls d' E)
end.

Definition my_build_refl_info E t (f:Proc.proc t) pi :=
    @build_refl_info E pi t f.

Definition my_build_adv_refl_info E PrOrcl PrPriv Gadv Gcomm
    t (f:Proc.proc t) Hwf Hloss pi :=
    @build_adv_refl_info E pi PrOrcl PrPriv Gadv Gcomm t f Hwf Hloss.

Definition eqb_param_t t1 (d1:dlist Var.var t1) t2 (d2:dlist Var.var t2) : bool.
intros t1 d1.
induction d1; intros t2 d2.
destruct d2.
exact true.
exact false.
destruct d2.
exact false.
case_eq (Var.veqb p v); intros.
exact (IHd1 _ d2).
exact false.
Defined.

Lemma eqb_param_t_correct : forall (t1 : list T.type) (d1:dlist Var.var t1) t2 (d2:dlist Var.var t2),
  eqb_param_t d1 d2 = true <-> eq_dep _ (dlist Var.var) t1 d1 t2 d2.
Proof.
  induction d1; simpl; intros.
  destruct d2; split; intros; try constructor; try discriminate.
  inversion H.
  destruct d2; split; intros; try constructor; try discriminate.
  inversion H.
  generalize (Var.veqb_spec_dep p v).
  destruct (Var.veqb p v); intros.
  apply IHd1 in H.
  inversion H0; subst.
  apply T.inj_pair2 in H4; subst.
  inversion H; subst.
  apply T.l_inj_pair2 in H5; subst.
  constructor.
  discriminate.
  generalize (Var.veqb_spec_dep p v).
  destruct (Var.veqb p v); intros.
  inversion H; subst.
  apply IHd1.
  constructor.
  inversion H; subst.
  elim H0.
  apply T.inj_pair2 in H8; subst.
  constructor.
Qed.

Lemma eqb_param_t_refl : forall t (d : dlist Var.var t),
  eqb_param_t d d = true.
Proof.
 intros.
 apply eqb_param_t_correct.
 constructor.
Qed.

Fixpoint find_decl t (f : Proc.proc t) (l : list decl) :=
  match l with
    | nil => None
    | d' :: l' =>
      if Proc.eqb f (decl_f d') 
        then Some d'
        else find_decl f l' 
  end.

Lemma find_decl_correct : forall l t (f : Proc.proc t) d' E,
  find_decl f l = Some d' ->
  (eqb_param_t (decl_params d') (proc_params (my_add_decls l E) f) = true) /\
    decl_body d' = proc_body (my_add_decls l E) f /\
    E.eqb (decl_res d') (proc_res (my_add_decls l E) f).
Proof.
 induction l; simpl; [ discriminate | ].
 intros t f d' E.
 generalize (Proc.eqb_spec_dep f (decl_f a)).
 destruct (Proc.eqb f (decl_f a)); intros.
 injection H0; intros; subst; clear H0.
 inversion H; subst.
 apply T.inj_pair2 in H3; subst.
 destruct d'; simpl in *.
 unfold my_add_decl'; simpl.
 unfold proc_params, d_params, proc_body, d_body, proc_res, d_res.
 rewrite add_decl_same_mk; trivial.
 rewrite eqb_param_t_refl, Eeqb_refl; auto.
 unfold proc_params, d_params, proc_body, d_body, proc_res, d_res.
 unfold my_add_decl'; simpl.
 rewrite add_decl_other_mk.
 apply IHl; trivial.
 intro; elim H.
 injection H1; intros.
 destruct a; simpl in *; subst.
 apply T.inj_pair2 in H2; subst.
 constructor.
Qed.

Lemma find_decl_correct_none : forall l t (f : Proc.proc t)  E,
  find_decl f l = None ->
  (my_add_decls l E) _ f = E _ f.
Proof.
  induction l; simpl; intros; auto.
  revert H.
  generalize (Proc.eqb_spec_dep f (decl_f a)).
  destruct (Proc.eqb f (decl_f a)); intros.
  discriminate.
  unfold my_add_decl'; simpl.
  rewrite add_decl_other_mk.
  auto.
  intro; elim H.
  injection H1; intros.
  destruct a; simpl in *; subst.
  apply T.inj_pair2 in H2; subst.
  constructor.
Qed.

Fixpoint check_eq_adv_decl_aux (l1 l2 : list decl) : bool :=
  match l1 with
    | nil => true
    | d :: l1' => 
      match find_decl (decl_f d) l2 with
        | None => false
        | Some d' =>
          (eqb_param_t (decl_params d) (decl_params d') &&
            Sem.I.ceqb (decl_body d) (decl_body d') &&
            Sem.E.eqb (decl_res d) (decl_res d') &&
            check_eq_adv_decl_aux l1' l2)%bool
      end
  end.

Lemma check_eq_adv_decl_aux_correct : forall (l1 l2  : list decl),
  check_eq_adv_decl_aux l1 l2 = true ->
  (forall t (f : Proc.proc t) d1 , find_decl f l1 = Some d1 ->
    exists d2, find_decl f l2 = Some d2 /\
      (eqb_param_t (decl_params d1) (decl_params d2) &&
        Sem.I.ceqb (decl_body d1) (decl_body d2) &&
        Sem.E.eqb (decl_res d1) (decl_res d2)) = true)%bool.
Proof.
 induction l1; simpl; intros.
 discriminate.
 revert H0.
 generalize (Proc.eqb_spec_dep f (decl_f a)).
 destruct (Proc.eqb f (decl_f a)); intros.
 injection H1; intros; subst; clear H1.
 revert H.
 case_eq (find_decl (decl_f d1) l2); [ | discriminate]; intros.
 inversion H0.
 repeat (apply andb_true_iff in H1; destruct H1).
 destruct d1; simpl in *; subst.
 apply T.inj_pair2 in H5; subst.
 exists d; split; trivial.
 repeat (apply andb_true_iff; split); auto.
 revert H; destruct (find_decl (decl_f a) l2); intros.
 repeat (apply andb_true_iff in H; destruct H).
 eapply IHl1; eauto.
 discriminate.
Qed.

Lemma Proc_eqb_refl : forall t (f : Proc.proc t),
  Proc.eqb f f.
Proof.
 intros.
 generalize (Proc.eqb_spec_dep f f).
 destruct (Proc.eqb f f); intros; auto.
 elim H; auto.
Qed.

Lemma Proc_eqb_sym : forall t1 (f1 : Proc.proc t1) t2 (f2 : Proc.proc t2),
  Proc.eqb f2 f1 = Proc.eqb f1 f2.
Proof.
 intros.
 generalize (Proc.eqb_spec_dep f1 f2).
 generalize (Proc.eqb_spec_dep f2 f1).
 destruct (Proc.eqb f1 f2); destruct (Proc.eqb f2 f1); auto; intros.
 elim H0.
 apply eq_dep_sym; trivial.
Qed.

Lemma check_eq_adv_decl_aux_correct_none : forall (l1 l2 : list decl) t (f : Proc.proc t),
check_eq_adv_decl_aux l2 l1 = true ->
find_decl f l1 = None ->
find_decl f l2 = None.
Proof.
 intros.
 case_eq (find_decl f l2); intros; auto.
 apply check_eq_adv_decl_aux_correct with (l2 := l1) in H1.
 destruct H1 as (W1, (W2, W3) ).
 rewrite H0 in W2; discriminate.
 trivial.
Qed.

Lemma eq_adv_decl_trans : forall s1 s2 E1 E2 E3,
  Eq_adv_decl s1 s2 E1 E2 ->
  Eq_adv_decl s1 s2 E2 E3 ->
  Eq_adv_decl s1 s2 E1 E3.
Proof.
  unfold Eq_adv_decl; intros.
  assert (W0 := H _ f H1 H2).
  decompose [and] W0.
  assert (W1 := H0 _ f H1 H2).
  decompose [and] W1.
  rewrite H3, H5, H6, <- H4, <- H8, H9; auto.
Qed.

Definition check_eq_adv_decl (s1 s2 : PrSet.t) (l1 l2 : list decl) : bool :=
  let l1' := filter (fun f => negb (PrSet.mem (BProc.mkP (decl_f f)) s1) && negb (PrSet.mem (BProc.mkP (decl_f f)) s2))%bool l1 in
  let l2' := filter (fun f => negb (PrSet.mem (BProc.mkP (decl_f f)) s1) && negb (PrSet.mem (BProc.mkP (decl_f f)) s2))%bool l2 in
    ((check_eq_adv_decl_aux l1' l2' && check_eq_adv_decl_aux l2' l1'))%bool.

Lemma Eq_adv_decl_my_add_decl' : forall s1 s2 a l1 E l2 E1 E2,
  Eq_adv_decl s1 s2 (my_add_decls l1 E) (my_add_decls l2 E) ->
  eqb_param_t (proc_params E1 (decl_f a)) (proc_params E2 (decl_f a)) = true ->
  Sem.I.ceqb (proc_body E1 (decl_f a)) (proc_body E2 (decl_f a)) = true ->
  Sem.E.eqb (proc_res E1 (decl_f a)) (proc_res E2 (decl_f a)) = true ->
   Eq_adv_decl s1 s2 (my_add_decl' a (my_add_decls l1 E))
     (my_add_decl' a (my_add_decls l2 E)).
 Proof.
  unfold Eq_adv_decl, my_add_decl'; simpl; intros.
  apply eqb_param_t_correct in H0.
  generalize (I.ceqb_spec (proc_body E1 (decl_f a)) (proc_body E2 (decl_f a))).
  rewrite H1; intros; clear H1.
  generalize (E.eqb_spec_dep (proc_res E1 (decl_f a)) (proc_res E2 (decl_f a))).
  rewrite H2; intros; clear H2.
  inversion H1; subst; clear H1.
  destruct a; simpl in *.
  apply T.inj_pair2 in H2; subst.
  generalize (Proc.eqb_spec_dep decl_f0 f).
  destruct (Proc.eqb decl_f0 f); intros.
  inversion H1; subst.
  apply T.inj_pair2 in H9; subst.
  destruct (add_decl_same  (my_add_decls l1 E) f decl_params0 decl_local0 decl_body0 decl_res0) as (W1, (W2, W3)).
  rewrite W1, W2, W3; clear W1 W2 W3.
  destruct (add_decl_same  (my_add_decls l2 E) f decl_params0 decl_local0 decl_body0 decl_res0) as (W1, (W2, W3)).
  rewrite W1, W2, W3; clear W1 W2 W3; auto.
  generalize H1; intro.
  eapply add_decl_other in H1.
  decompose [and] H1; clear H1.
  rewrite H7, H9, H10.
  eapply add_decl_other in H6.
  decompose [and] H6; clear H6.
  rewrite H1, H11, H12.
  apply H; auto.
Qed.

Lemma eq_adv_decl_refl : forall s1 s2 E,
  Eq_adv_decl s1 s2 E E.
Proof.
 unfold Eq_adv_decl; simpl; intros; auto.
Qed.

Lemma eq_adv_decl_sym : forall s1 s2 E1 E2,
  Eq_adv_decl s1 s2 E2 E1 ->
  Eq_adv_decl s1 s2 E1 E2.
Proof.
 unfold Eq_adv_decl; simpl; intros; auto.
 destruct (H _ f) as (W1, (W2, W3)); auto.
Qed.

Lemma eq_adv_decl_diff : forall s1 s2 E E2 l a,
  (negb (PrSet.mem (BProc.mkP (decl_f a)) s1) && negb (PrSet.mem (BProc.mkP (decl_f a)) s2) = false)%bool ->
  Eq_adv_decl s1 s2 (my_add_decls l E) E2 ->
  Eq_adv_decl s1 s2 (my_add_decl' a (my_add_decls l E)) E2.
Proof.
 unfold Eq_adv_decl; intros.
 unfold my_add_decl'.
 generalize (Proc.eqb_spec_dep (decl_f a) f).
 destruct (Proc.eqb (decl_f a) f); intros.
 inversion H3; destruct a; subst; simpl in *.
 apply T.inj_pair2 in H7; subst.
 apply andb_false_iff in H; destruct H.
 elim H1.
 apply negb_false_iff; trivial.
 elim H2.
 apply negb_false_iff; trivial.
 destruct (H0 _ f) as [W1 [W2 W3] ] ; trivial.
 rewrite <- W1, <- W2, <- W3.
 apply add_decl_other; trivial.
Qed.

Lemma eq_adv_decl_filter1 :forall s1 s2 l E,
  let l' := filter (fun f => negb (PrSet.mem (BProc.mkP (decl_f f)) s1) && negb (PrSet.mem (BProc.mkP (decl_f f)) s2))%bool l in
    Eq_adv_decl s1 s2 (my_add_decls l E) (my_add_decls l' E).
Proof.
 induction l; simpl; intros.
 apply eq_adv_decl_refl.
 case_eq (negb (PrSet.mem {| BProc.p_type := decl_type a; BProc.p_name := decl_f a |} s1) &&
   negb (PrSet.mem {| BProc.p_type := decl_type a; BProc.p_name := decl_f a |} s2))%bool; intros.
 apply andb_true_iff in H; destruct H.
 simpl.
 apply Eq_adv_decl_my_add_decl' with (E1 := E) (E2 := E).
 apply IHl.
 apply eqb_param_t_refl.
 generalize (I.ceqb_spec (proc_body E (decl_f a)) (proc_body E (decl_f a))).
 destruct (I.ceqb (proc_body E (decl_f a)) (proc_body E (decl_f a))); intros; auto.
 apply Eeqb_refl.
 apply eq_adv_decl_diff; auto.
Qed.

Lemma eq_adv_decl_filter : forall s1 s2 l1 l2 E,
  let l1' := filter (fun f => negb (PrSet.mem (BProc.mkP (decl_f f)) s1) && negb (PrSet.mem (BProc.mkP (decl_f f)) s2))%bool l1 in
  let l2' := filter (fun f => negb (PrSet.mem (BProc.mkP (decl_f f)) s1) && negb (PrSet.mem (BProc.mkP (decl_f f)) s2))%bool l2 in
  Eq_adv_decl s1 s2 (my_add_decls l1' E) (my_add_decls l2' E) ->
  Eq_adv_decl s1 s2 (my_add_decls l1 E) (my_add_decls l2 E).
Proof.
  intros.
  eapply eq_adv_decl_trans.
  eapply eq_adv_decl_trans.
  2: apply H.
  apply eq_adv_decl_filter1.
  apply eq_adv_decl_sym.
  apply eq_adv_decl_filter1.
Qed.

Lemma check_Eq_adv_decl_correct : forall s1 s2 l1 l2 E, 
  check_eq_adv_decl s1 s2 l1 l2 = true ->
  Eq_adv_decl s1 s2 (my_add_decls l1 E) (my_add_decls l2 E).
Proof.
  unfold check_eq_adv_decl.
  intros; apply eq_adv_decl_filter.
  unfold Eq_adv_decl; intros.
 apply andb_true_iff in H; destruct H.
 case_eq (find_decl f (filter
   (fun f : decl => negb (PrSet.mem {| BProc.p_type := decl_type f; BProc.p_name := decl_f f |} s1) &&
     negb (PrSet.mem {| BProc.p_type := decl_type f; BProc.p_name := decl_f f |} s2))%bool l1)); intros.
 assert (W0 := @find_decl_correct _ _ _ _ E H3).
 decompose [and] W0; clear W0.
 rewrite <- H6; clear H6.
 generalize (E.eqb_spec_dep (decl_res d)
   (proc_res (my_add_decls (filter (fun f : decl =>
     negb (PrSet.mem {| BProc.p_type := decl_type f; BProc.p_name := decl_f f |} s1) &&
     negb (PrSet.mem {| BProc.p_type := decl_type f; BProc.p_name := decl_f f |} s2))%bool l1) E) f)).
 rewrite H7; clear H7; intros.
 inversion H5; subst; clear H5.
 apply T.inj_pair2 in H9; subst.
 rewrite <- H9; clear H9.
 apply eqb_param_t_correct in H4.
 inversion H4; simpl in *; clear H4.
 destruct d; simpl in *; subst.
 unfold Proc.targs in *.
 destruct f, decl_f0; subst.
 apply inj_pair2_eq_dec in H9.
 rewrite <- H9; clear H9.
 eapply check_eq_adv_decl_aux_correct in H3.
 2: apply H.
 simpl in *.
 destruct H3 as [d2 [W1 W2] ].
 assert (W0 := @find_decl_correct _ _ _ _ E W1).
 decompose [and] W0; clear W0.
 rewrite <- H5; clear H5.
 generalize (E.eqb_spec_dep (decl_res d2)
   (proc_res (my_add_decls (filter (fun f : decl =>
     negb (PrSet.mem {| BProc.p_type := decl_type f; BProc.p_name := decl_f f |} s1) &&
     negb (PrSet.mem {| BProc.p_type := decl_type f; BProc.p_name := decl_f f |} s2))%bool l2) E) (Proc.mkP pname targs tres))).
 rewrite H6; clear H6; intros.
 inversion H4; subst; clear H4.
 apply T.inj_pair2 in H10; subst.
 rewrite <- H10; clear H10.
 apply eqb_param_t_correct in H3.
 inversion H3; simpl in *; clear H3; subst.
 apply inj_pair2_eq_dec in H10.
 rewrite <- H10; clear H10.
 apply andb_true_iff in W2; destruct W2.
 apply andb_true_iff in H3; destruct H3.
 apply eqb_param_t_correct in H3.
 inversion H3; subst.
 apply inj_pair2_eq_dec in H10; subst.
 generalize (E.eqb_spec_dep decl_res0 (decl_res d2)).
 rewrite H4; intros.
 inversion H10; subst.
 apply T.inj_pair2 in H11; subst.
 generalize (I.ceqb_spec decl_body0 (decl_body d2)).
 rewrite H5; intros; subst; auto.
 apply Tlist_eq_dec.
 apply Tlist_eq_dec.
 apply Tlist_eq_dec.
 apply check_eq_adv_decl_aux_correct_none with (f := f) in H2.
 apply find_decl_correct_none with (E := E) in H3.
 apply find_decl_correct_none with (E := E) in H2.
 unfold proc_params, d_params, proc_body, d_body, proc_res, d_res.
 rewrite H3, H2; auto.
 trivial.
Qed.


 Section UPTO.

  Variable PrOrcl PrPriv : PrSet.t.
  Variable Gadv Gcomm : Vset.t.

  Hypothesis Gadv_global : forall x, Vset.mem x Gadv -> Var.is_global x.

  Hypothesis Gcomm_global : forall x, Vset.mem x Gcomm -> Var.is_global x.

  Variable inv : pred.
  Variable E1 E2 : env.
  Variable X1 X2 : Vset.t.

  Hypothesis inv_dep1 : fst (pdepend inv) [<=] X1.
  Hypothesis inv_dep2 : snd (pdepend inv) [<=] X2.

  Hypothesis inv_global : 
   forall x, Vset.mem x (Vset.union X1 X2) -> Var.is_global x.

  Hypothesis Gcomm_empty: Gcomm [=] Vset.empty.

  Hypothesis disjoint_X1 :  Vset.disjoint X1 Gadv.

  Hypothesis disjoint_X2 :  Vset.disjoint X2 Gadv.

  Hypothesis Heq_adv_decl : Eq_adv_decl PrOrcl PrPriv E1 E2.

  Hypothesis Heq_orcl_params : Eq_orcl_params  PrOrcl E1 E2.

  Lemma pexp_rel_pred1 : forall inv k (m1 m2:Mem.t k),
   ipred (pexp (e2E side_left inv)) m1 m2 <-> rel_pred1 (EPp inv) m1 m2.
  Proof. 
   unfold rel_pred1, EPp; intros; simpl; split; intros.
   apply ipred_pexp_left in H.
   apply H.
   apply ipred_pexp_left.
   apply H.
  Qed.

  Lemma pexp_rel_pred2 : forall inv k (m1 m2:Mem.t k),
   ipred (pexp (e2E side_right inv)) m1 m2 <-> rel_pred2 (EPp inv) m1 m2.
  Proof. 
   unfold rel_pred1, EPp; intros; simpl; split; intros.
   apply ipred_pexp_right in H.
   apply H.
   apply ipred_pexp_right.
   apply H.
  Qed.
      
  Lemma equiv_adv_upto_aux : forall (bad1 bad2:E.expr T.Bool),
    (forall x, Vset.mem x (fv_expr bad1) -> Var.is_global x) ->
    (forall x, Vset.mem x (fv_expr bad2) -> Var.is_global x) ->
    Vset.disjoint (fv_expr bad1) Gadv ->
    Vset.disjoint (fv_expr bad2) Gadv ->
   is_decMR (pexp (e2E side_left bad1)) ->
   is_decMR (pexp (e2E side_right bad1)) ->

   (forall (k : nat) (m1 m2 : Mem.t k) (t0 : T.type) (f : Proc.proc t0),
    PrSet.mem {| BProc.p_type := t0; BProc.p_name := f |} PrOrcl ->
    hoare m1 m2 E1 (pexp (e2E side_left bad1)) (proc_body E1 f) (pexp (e2E side_left bad1))) ->

   (forall (k : nat) (m1 m2 : Mem.t k) (t0 : T.type) (f : Proc.proc t0),
    PrSet.mem {| BProc.p_type := t0; BProc.p_name := f |} PrOrcl ->
    hoare m1 m2 E2 (pexp (e2E side_left bad2)) (proc_body E2 f) (pexp (e2E side_left bad2))) ->

   (forall o : ProcD.t,
    PrSet.mem o PrOrcl ->
    Equiv ((pnot (pexp (e2E side_left bad1))) /_\ 
           (pnot (pexp (e2E side_right bad2))) /_\
           (eq_param (proc_params E1 (BProc.p_name o)) 
                     (proc_params E2 (BProc.p_name o))) /_\ inv)
    E1 (proc_body E1 (BProc.p_name o)) E2 (proc_body E2 (BProc.p_name o))
    ((piff (pexp (e2E side_left bad1)) (pexp (e2E side_right bad2))) /_\
     (pnot (pexp (e2E side_left bad1)) |_> 
      (inv /_\ preq_mem Gadv /_\ 
       (peq (e2E side_left (proc_res E1 (BProc.p_name o))) 
            (e2E side_right (proc_res E2 (BProc.p_name o)))))))) ->

    forall I c O,
     WFAdv_c PrOrcl PrPriv Gadv Gcomm E1 I c O ->
     (forall x, Vset.mem x I -> Var.is_local x) ->
     slossless_c E1 c ->
     slossless_c E2 c ->
     Equiv (piff (pexp (e2E side_left bad1)) (pexp (e2E side_right bad2)) /_\
      (pnot (pexp (e2E side_left bad1)) |_> 
       (preq_mem (Vset.union Gadv I) /_\ inv)))
     E1 c E2 c
     (piff (pexp (e2E side_left bad1)) (pexp (e2E side_right bad2)) /_\
      (pnot (pexp (e2E side_left bad1)) |_> 
       (preq_mem (Vset.union Gadv O) /_\ inv))).
  Proof.
   intros.
   eapply (equiv_sub
    (ipred
     ((Pexp (e2E side_left bad3) <--> Pexp (e2E side_right bad4)) /_\
      ~_ Pexp (e2E side_left bad3)
      |_> preq_mem (Vset.union Gadv I) /_\ inv))
    (ipred
     ((Pexp (e2E side_left bad3) <--> Pexp (e2E side_right bad4)) /_\
      ~_ Pexp (e2E side_left bad3)
      |_> preq_mem (Vset.union Gadv O) /_\ inv))); 
    [ | | 
     apply equiv_bad_inv with 
       (PrOrcl:=PrOrcl) (PrPriv:=PrPriv) (Gcomm:=Gcomm) (Gadv:=Gadv) 
       (I:=I) (O:=O) (Inv:=ipred inv)
       (bad1_expr:=bad3) (bad2_expr:=bad4) (X1:=X1) (X2:=X2); trivial ].

   unfold ipred; unfold eqR, rel_pred1, rel_pred2, bad1, bad2, EPp.
   intros k m1 m2.
   rewrite !peval_pand.
   rewrite peval_pimplies.
   rewrite peval_pnot.
   rewrite !peval_pand.
   unfold piff.
   rewrite peval_peq.
   intros (W1, W2).
   rewrite !e2E_correct in *.
   simpl smem in *.
   split.
   split; intro.
   rewrite <- W1; trivial.
   rewrite W1; trivial.
   intro.
   destruct W2.
   simpl; intro.
   elim H12.
   rewrite !e2E_correct in *.
   simpl in H13; trivial.
   simpl; split; auto.
   apply preq_mem_correct in H13; trivial.

   unfold ipred; unfold eqR, rel_pred1, rel_pred2, bad1, bad2, EPp.
   intros k m1 m2 [ [ W1 W2 ] W3 ].
   rewrite !peval_pand.
   rewrite peval_pimplies.
   rewrite peval_pnot.
   rewrite !peval_pand.
   unfold piff.
   rewrite peval_peq.
   split.   
   rewrite !e2E_correct; simpl.
   case_eq (E.eval_expr bad3 m1); intros.
   apply W1 in H12; auto.
   case_eq (E.eval_expr bad4 m2); intros.
   apply W2 in H13; auto.
   simpl in H13.
   rewrite H12 in H13; discriminate.
   auto.
   intros.
   destruct W3.
   intro; elim H12.
   simpl;rewrite e2E_correct; simpl; auto.
   split; auto.
   apply preq_mem_correct; trivial.

   eapply depend_only_rel_weaken; [apply inv_dep1 | apply inv_dep2 | ].
   apply (pdepend_correct inv).

   unfold bad1, rel_pred1, EPp; intros.
   destruct (E.eval_expr bad3 m1); auto.
   right; intros; discriminate.
  
   intros; unfold bad2, rel_pred2, EPp.
   destruct (E.eval_expr bad4 m2); auto.
   right; intros; discriminate.

   intros; unfold bad1, Hoare, hoare, EPp in *; intros.
   apply H5 with (k := k) (m1 := m) (m2 := m) in H12.
   eapply range_weaken.
   2: apply H12.
   simpl; intros; trivial.
   unfold ipred, pexp in H14; simpl in H14.
   rewrite !e2E_correct in *; simpl in *; auto.
   unfold ipred, pexp; simpl.
   rewrite !e2E_correct in *; simpl in *; auto.

   intros; unfold bad2, Hoare, hoare, EPp in *; intros.
   apply H6 with (k := k) (m1 := m) (m2 := m) in H12.
   eapply range_weaken.
   2: apply H12.
   simpl; intros; trivial.
   unfold ipred, pexp in H14; simpl in H14.
   rewrite !e2E_correct in *; simpl in *; auto.
   unfold ipred, pexp; simpl.
   rewrite !e2E_correct in *; simpl in *; auto.

   intros.
   eapply equiv_sub; [ | | apply (H7 _ H12)].

   unfold ipred, eqR, rel_pred1, rel_pred2.
   unfold bad1, bad2, EPp, impR, andR, notR.   
   intros k m1 m2 [ [ W1 W2 ] [ W3 W4 ] ].
   rewrite !peval_pand, !peval_pnot.
   unfold pexp; simpl.
   rewrite !e2E_correct; simpl.
   repeat split; try tauto.
   rewrite <- H15; apply eq_param_same; trivial.

   unfold ipred, eqR, rel_pred1, rel_pred2.
   unfold bad1, bad2, EPp, impR, andR, notR.   
   intros k m1 m2.
   rewrite !peval_pand.
   rewrite !peval_pimplies.
   rewrite peval_pnot.
   rewrite !peval_pand.
   intros [ W1 W2 ].
   simpl in W1.
   rewrite peval_peq in W1.
   rewrite !e2E_correct in W1; simpl in W1.
   rewrite W1.
   split; auto; intros.
   destruct W2.
   simpl; rewrite e2E_correct; simpl.
   rewrite W1; tauto.
   split; try tauto.
   decompose [and] H18; clear H18; trivial.
   apply preq_mem_correct in H19; trivial.
   split; trivial.
   simpl in H20.
   rewrite peval_peq in H20.
   rewrite !e2E_correct in H20; simpl in H20; trivial.
  Qed.

 End UPTO.

 Definition check_equiv_adv_upto Gadv Gcomm inv t0 A PrPriv PrOrcl E1 
  (bad1 bad2:E.expr T.Bool) :=
  (Vset.forallb Var.is_global Gadv &&
  Vset.forallb  Var.is_global Gcomm &&
  Vset.forallb Var.is_global (fv_expr bad1) &&
  Vset.forallb Var.is_global (fv_expr bad2) &&
  Vset.forallb Var.is_local (Vset_of_var_decl (proc_params E1 A)) &&
  Vset.forallb Var.is_global (Vset.union (fst (pdepend inv)) (snd (pdepend inv))) &&
  Vset.disjoint (fv_expr bad1) Gadv &&
  Vset.disjoint (fv_expr bad2) Gadv &&
  Vset.disjoint (fst (pdepend inv)) Gadv &&
  Vset.disjoint (snd (pdepend inv)) Gadv &&
  (Gcomm [=?] Vset.empty) &&
  (Gadv [=?] Vset.empty) &&
  negb (PrSet.mem {| BProc.p_type := t0; BProc.p_name := A |} PrOrcl) &&
  negb (PrSet.mem {| BProc.p_type := t0; BProc.p_name := A |} PrPriv))%bool.


 Lemma equiv_adv_upto_correct : forall PrOrcl PrPriv Gcomm Gadv E1 E2 t 
  (A:Proc.proc t)  (bad1 bad2:E.expr T.Bool) inv,
  Eq_adv_decl PrOrcl PrPriv E1 E2 ->
  Eq_orcl_params PrOrcl E1 E2 ->
  (forall o : ProcD.t,
   PrSet.mem o PrOrcl ->
   Equiv
     (~_ (e2E side_left bad1) === true /_\
      ~_ (e2E side_right bad2) === true /_\
      eq_param (proc_params E1 (BProc.p_name o))
        (proc_params E2 (BProc.p_name o)) /_\ inv) E1
     (proc_body E1 (BProc.p_name o)) E2 (proc_body E2 (BProc.p_name o))
     (((e2E side_left bad1) === true <--> (e2E side_right bad2) === true) /_\
      ~_ (e2E side_left bad1) === true 
      |_> (e2E side_left (proc_res E1 (BProc.p_name o)) ===
        e2E side_right (proc_res E2 (BProc.p_name o))) /_\ inv)) ->
  
  WFAdv PrOrcl PrPriv Gadv Gcomm E1 A ->
  check_equiv_adv_upto Gadv Gcomm inv A PrPriv PrOrcl E1 bad1 bad2  = true ->
  slossless_c E1 (proc_body E1 A) ->
  slossless_c E2 (proc_body E2 A) ->

   (forall (k : nat) (m1 m2 : Mem.t k) (t0 : T.type) (f : Proc.proc t0),
    PrSet.mem {| BProc.p_type := t0; BProc.p_name := f |} PrOrcl ->
    hoare m1 m2 E1 (pexp (e2E side_left bad1)) (proc_body E1 f) (pexp (e2E side_left bad1))) ->

   (forall (k : nat) (m1 m2 : Mem.t k) (t0 : T.type) (f : Proc.proc t0),
    PrSet.mem {| BProc.p_type := t0; BProc.p_name := f |} PrOrcl ->
    hoare m1 m2 E2 (pexp (e2E side_left bad2)) (proc_body E2 f) (pexp (e2E side_left bad2))) ->

   Equiv 
   ((((e2E side_left bad1) === true <--> (e2E side_right bad2) === true)) /_\
    ~_ (e2E side_left bad1) === true
    |_> (eq_param (proc_params E1 A) (proc_params E2 A) /_\ inv))
     E1 (proc_body E1 A) E2 (proc_body E2 A)    
     (((e2E side_left bad1) === true <--> (e2E side_right bad2) === true) /_\
     ~_ (e2E side_left bad1) === true |_> 
       (e2E side_left (proc_res E1 A) === e2E side_right (proc_res E2 A) /_\ inv)).
Proof.
 intros.

  unfold check_equiv_adv_upto in H3.
  repeat (rewrite andb_true_iff in H3).
  decompose [and] H3; clear H3.

 unfold WFAdv in H2.
 destruct H2.
 destruct H2.
 unfold Eq_adv_decl in H.
 destruct (H _ A) as [W1 [ W2 W3 ] ]; trivial.
 apply is_true_negb; trivial.
 apply is_true_negb; trivial.

  assert (Hgcomm : Gcomm [=] Vset.empty) by auto.
  assert (Hadv : Gadv [=] Vset.empty) by auto.
  rewrite <- W2.

  eapply Equiv_Sub; [ | | 
    apply equiv_adv_upto_aux with 
      (PrOrcl := PrOrcl) (PrPriv := PrPriv) (Gcomm := Gcomm) (inv := inv) (bad1 := bad3) (bad2 := bad4)
      (X1:=(fst (pdepend inv))) (X2:=(snd (pdepend inv))) ]; eauto.

  intros k m1 m2.
  rewrite !peval_pand.
  rewrite !peval_pimplies.
  rewrite !peval_pnot.
  rewrite !peval_pand.
  rewrite !peval_piff.
  simpl.
  rewrite !peval_peq.
  simpl; intros.
  decompose [and] H10; clear H10.
  split; trivial; intros.
  split; [ | tauto ].
  apply preq_mem_correct.
  apply req_mem_union.
  rewrite Hadv; auto.
  apply eq_param_same.
  rewrite  <- W1 in H24.
  tauto.

  intros k m1 m2.
  rewrite !peval_pand.
  rewrite !peval_pimplies.
  rewrite !peval_pnot.
  rewrite !peval_pand.
  rewrite !peval_piff.
  simpl.
  rewrite !peval_peq.
  simpl; intros.
  decompose [and] H10; clear H10.
  split; trivial; intros.
  split; [ | tauto].
  rewrite !e2E_correct; simpl.
  rewrite <- W3.
  eapply equiv_WFRead with (IA := Gadv).
  apply H3.
  rewrite Hgcomm; auto with set.
  auto with set.
  apply preq_mem_correct; tauto.

  eapply Vset.forallb_correct; auto.
  intros ? ? WW; unfold VarP.Edec.eq in WW; subst; trivial.
  auto with set.
  auto with set.
  eapply Vset.forallb_correct; auto.
  intros ? ? WW; unfold VarP.Edec.eq in WW; subst; trivial.
  eapply Vset.forallb_correct; auto.
  intros ? ? WW; unfold VarP.Edec.eq in WW; subst; trivial.
  eapply Vset.forallb_correct; auto.
  intros ? ? WW; unfold VarP.Edec.eq in WW; subst; trivial.

  intros.
  eapply Equiv_Sub; [ | | apply H1]; trivial.
  intros k m1 m2.
  rewrite !peval_pand.
  rewrite !peval_pnot.
  rewrite !peval_peq.
  unfold pexp; simpl.
  tauto.
  intros k m1 m2.
  rewrite !peval_pand.
  rewrite !peval_pimplies.
  rewrite !peval_pnot.
  rewrite !peval_pand.
  rewrite !peval_piff.
  simpl.
  rewrite !peval_peq.
  simpl; intros.
  decompose [and] H23; clear H23.
  split; trivial; intros.
  split; [ tauto | ].
  split; [ | tauto].
  apply preq_mem_correct.
  red; rewrite Hadv; auto.
  eapply Vset.forallb_correct; auto.  
  intros ? ? WW; unfold VarP.Edec.eq in WW; subst; trivial.
  rewrite W2; trivial.
Qed.

         
 Definition subst_res k E1 t (f1:Proc.proc t) 
  (e:E.expr T.Bool) (res:Var.var t) : Mem.t k -o> boolO := 
  fun m => 
   eeval m m nil (esubst (VarLeft res)
    (e2E side_left (proc_res E1 f1)) 
    (e2E side_left e)).

 Lemma Pr_equiv : forall P E1 t1 (f1:Proc.proc t1) E2 t2 (f2:Proc.proc t2)
  Q k (m:Mem.t k) (e1 e2: E.expr T.Bool) (r1:Var.var t1) (r2:Var.var t2),
  Equiv P E1 (proc_body E1 f1) E2 (proc_body E2 f2)
  (wp_return E1 f1 E2 f2 Q r1 r2) ->
  ipred P m m ->
  (forall k (m1 m2:Mem.t k),
    ipred (wp_return E1 f1 E2 f2 Q r1 r2) m1 m2 -> 
    subst_res E1 f1 e1 r1 m1 = subst_res E2 f2 e2 r2 m2) ->
  Pr E1 (proc_body E1 f1) m (subst_res E1 f1 e1 r1) == 
  Pr E2 (proc_body E2 f2) m (subst_res E2 f2 e2 r2).
 Proof.
  unfold EP, Pr, Equiv; intros.
  apply equiv_deno with (ipred P) (ipred (wp_return E1 f1 E2 f2 Q r1 r2)); trivial.
  intros; unfold charfun, restr, fone; rewrite (H1 _ _ m2); auto.
 Qed.

 Lemma Pr_equiv_le : forall P E1 t1 (f1:Proc.proc t1) E2 t2 (f2:Proc.proc t2)
  Q k (m:Mem.t k) (e1 e2: E.expr T.Bool) (r1:Var.var t1) (r2:Var.var t2),
  Equiv P E1 (proc_body E1 f1) E2 (proc_body E2 f2) 
  (wp_return E1 f1 E2 f2 Q r1 r2) ->
  ipred P m m ->
  (forall k (m1 m2:Mem.t k),
    ipred (wp_return E1 f1 E2 f2 Q r1 r2) m1 m2 -> 
    subst_res E1 f1 e1 r1 m1 -> subst_res E2 f2 e2 r2 m2) ->
  Pr E1 (proc_body E1 f1) m (subst_res E1 f1 e1 r1) <=  
  Pr E2 (proc_body E2 f2) m (subst_res E2 f2 e2 r2).
 Proof.
  unfold EP, Pr, Equiv; intros.
  apply equiv_deno_le with (ipred P) 
   (ipred (wp_return E1 f1 E2 f2 Q r1 r2)); trivial.
  intros; unfold charfun, restr, fone.
  generalize (H1 k m1 m2 H2).
  destruct (subst_res E1 f1 e1 r1 m1 ).
  intros; rewrite H3; trivial.
  trivial.
 Qed.

 Ltac apply_Pr_equiv := first [eapply Pr_equiv_le | eapply Pr_equiv].

 Fixpoint subst_var t' (v:Var.var t') (e':E.expr t') t (e:E.expr t) : E.expr t :=
  match e in E.expr t0 return E.expr t0 with
   | E.Ecte t1 c => (E.Ecte c)
   | E.Evar t1 v1 =>
     if Var.veqb v v1 then 
       match T.eq_dec t' t1 with
         | left H => match H in (_ = t2) return E.expr t2 with
                       | eq_refl => e'
                     end
         | _ => (E.Evar v1)
       end
       else (E.Evar v1)
    | E.Eop op larg => E.Eop op (dmap E.expr (@subst_var t' v e') larg)
    | e => e
  end.

Lemma EP_negP : forall k (e : E.expr T.Bool),
  negP (EP k e) = EP k (! e).
Proof.
 intros; unfold negP, EP; simpl.
 unfold O.eval_op; simpl; trivial.
Qed.

Close Scope bool_scope.

Lemma EP_andP : forall k E c (m : Mem.t k) (e1 e2 : E.expr T.Bool),
  Pr E c m (EP k e1[&&]EP k e2) = Pr E c m (EP k (e1 && e2)).
Proof.
 intros; unfold andP, EP; simpl.
 unfold O.eval_op; simpl; trivial.
Qed.


Lemma Fundamental_Lemma_aux : 
   forall E1 E2 c1 c2 k (m:Mem.t k) A B F1 F2,
      Pr E1 c1 m (A [&&] negP F1) == Pr E2 c2 m (B [&&] negP F2) -> 
      Pr E1 c1 m F1 == Pr E2 c2 m F2 ->
      Uabs_diff (Pr E1 c1 m A) (Pr E2 c2 m B) <= Pr E2 c2 m F2.
 Proof.
  intros.
  apply (Ule_total (Pr E1 c1 m A) (Pr E2 c2 m B)); trivial; intros.
  rewrite (Uabs_diff_compat_le (Pr E1 c1 m A) (Pr E2 c2 m B) H1).
  apply Uplus_le_perm_left.
  rewrite (Pr_split E1 c1 m F1 A), (Pr_split E2 c2 m F2 B).
  rewrite H,proj2_BP, Uplus_sym, <- Uplus_assoc; trivial.
  rewrite Uabs_diff_sym. 
  rewrite (Uabs_diff_compat_le (Pr E2 c2 m B) (Pr E1 c1 m A) H1).
  rewrite <- H0.
  apply Uplus_le_perm_left.
  rewrite (Pr_split E1 c1 m F1 A), (Pr_split E2 c2 m F2 B).
  rewrite H,proj2_BP, Uplus_sym, <- Uplus_assoc; trivial.
 Qed.

Lemma ECFundamentalLemma : forall P E1 t (f1:Proc.proc t) E2 (f2:Proc.proc t)
  Q k (m:Mem.t k) (r1:Var.var t) (r2:Var.var t) A B F1 F2
  (W : Equiv P E1 (proc_body E1 f1) E2 (proc_body E2 f2)
  (wp_return E1 f1 E2 f2 Q r1 r2)),

  ipred P m m ->

  (forall k (m1 m2 : Mem.t k),
    ipred (wp_return E1 f1 E2 f2 Q r1 r2) m1 m2 ->

    ipred (wp_return E1 f1 E2 f2
      (Pand (Peq (e2E side_left F1) (e2E side_right F2))
        (Pimplies (Pnot (Peq (e2E side_left F1) true)) (Peq (e2E side_left A) (e2E side_right B)))) r1 r2) m1 m2) ->

  Uabs_diff
  (Pr E1 (proc_body E1 f1) m (subst_res E1 f1 A r1))
  (Pr E2 (proc_body E2 f2) m (subst_res E2 f2 B r2)) <=
  Pr E2 (proc_body E2 f2) m (subst_res E2 f2 F2 r2).
Proof.
  unfold Equiv.
  intros P E1 t f1 E2 f2 Q k m r1 r2 A B F1 F2 W WP WQ.
  apply Fundamental_Lemma_aux with (F1 := (subst_res E1 f1 F1 r1)).

  apply equiv_deno with (1 := W); trivial.
  intros m1 m2 H.
  apply WQ in H.
  generalize H; clear H.
  unfold charfun, restr, fone, negP, andP, subst_res, ipred, wp_return; simpl.
  repeat (rewrite esubst_correct; simpl); 
    try (  apply VsetP.disjoint_complete; intros X; rewrite lfv_e2E; discriminate ).
  repeat (rewrite e2E_correct; simpl); trivial.
  case (E.eval_expr F1 (m1 {!r1 <-- E.eval_expr (proc_res E1 f1) m1!})).
  intros [H _]; rewrite <- H, !andb_false_r; auto.
  intros [H1 H2]; rewrite <- H1, H2; auto.
  apply equiv_deno with (1 := W); trivial.
  intros m1 m2 H.
  apply WQ in H.
  generalize H; clear H.
  unfold charfun, restr, fone, subst_res, ipred, wp_return; simpl.
  repeat (rewrite esubst_correct; simpl);
    try (  apply VsetP.disjoint_complete; intros X; rewrite lfv_e2E; discriminate ).
  repeat (rewrite e2E_correct; simpl); trivial.
  intros [H _]; rewrite H; auto.
Qed.
  
End Make.
