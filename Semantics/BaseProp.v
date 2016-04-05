(** * BaseProp.v : Basic properties of programs and expressions *)

Set Implicit Arguments.

Require Export RelationClasses.
Require Tree.
Require Export MakeSem.

Module Type SEM_THEORY (Sem:SEM).

 Import Sem.
 
 (** Set of variables and free variables of expressions *)

 Declare Module Vset : SET with Definition E.t := Var.t with Definition E.eq := @eq Var.t.

 Notation "{{ x , .. , y }}" := (Vset.add x .. (Vset.add y Vset.empty) ..).

 Fixpoint fv_expr_rec (t:T.type) (res:Vset.t) (e:E.expr t) {struct e} : Vset.t :=
  match e with 
  | E.Ecte _ _ => res 
  | E.Evar t x => Vset.add x res 
  | E.Eop op args => dfold_left fv_expr_rec args res
  | E.Eexists t x e1 e2 => 
    Vset.union 
    (Vset.remove x (fv_expr_rec Vset.empty e1)) 
    (fv_expr_rec res e2)
  | E.Eforall t x e1 e2 => 
    Vset.union 
    (Vset.remove x (fv_expr_rec Vset.empty e1))
    (fv_expr_rec res e2)
  | E.Efind t x e1 e2 => 
    Vset.union 
    (Vset.remove x (fv_expr_rec Vset.empty e1))
    (fv_expr_rec res e2)
  end.

 Definition fv_expr t := @fv_expr_rec t Vset.empty.

 Parameter fv_expr_rec_subset : forall t (e:E.expr t) res, 
  Vset.subset res (fv_expr_rec res e).

 Definition fv_expr_extend t (e:E.expr t) X := fv_expr_rec X e.

 Parameter union_fv_expr_spec : forall t (e:E.expr t) X, 
  Vset.eq (fv_expr_extend e X) (Vset.union (fv_expr e) X).

 Fixpoint fv_distr t (d:E.support t) :=
  match d with
  | E.Dnat e => fv_expr e 
  | E.DZ e1 e2 => Vset.union (fv_expr e1) (fv_expr e2)
  | E.Dprod t1 t2 s1 s2  => Vset.union (fv_distr s1) (fv_distr s2) 
  | _ => Vset.empty
  end.

 Definition eeq_mem X k (m1 m2:Mem.t k) :=
  forall t (x:Var.var t), ~Vset.mem x X -> m1 x = m2 x.

 Definition Modify E X c := forall k (m:Mem.t k), range (eeq_mem X m) ([[c]] E m).

 Definition lossless E c := 
  forall k (m:Mem.t k), mu ([[c]] E m) (fun _ => 1) == 1.

 Definition Pr k (E:env) (c:cmd) (m:Mem.t k) (P:Mem.t k -o> boolO) :=
  mu ([[c]] E m) (charfun P).
 
 Definition EP k (e:E.expr T.Bool) : Mem.t k -o> boolO := @E.eval_expr k _ e.
 Implicit Arguments EP [].
 
 (** Relations over memories *) 
 Definition mem_rel := forall k, Mem.t k -> Mem.t k -> Prop.
  
 Definition andR (P1 P2:mem_rel) : mem_rel := fun k x y => P1 k x y /\ P2 k x y.

 Notation "P1 /-\ P2" := (@andR P1 P2) (at level 80, right associativity).

 Definition req_mem k X (m1 m2:Mem.t k) := 
  forall t (x:Var.var t), Vset.mem x X -> m1 x = m2 x.

 Notation "m1 '=={' X '}' m2" := 
  (req_mem X m1 m2) (at level 70, no associativity).

 Definition kreq_mem X : mem_rel := fun k => @req_mem k X.

 Definition req_mem_rel X P : mem_rel := (kreq_mem X) /-\ P.
 Implicit Arguments req_mem_rel [].

 Definition decMR (P:mem_rel) := forall k x y, sumbool (P k x y) (~P k x y).
 
 Definition equiv (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) :=
  forall k, 
   exists d : Mem.t k -> Mem.t k -> Distr (Mem.t k * Mem.t k),
    forall m1 m2, 
     P k m1 m2 -> 
     lift (Q k) (d m1 m2) ([[c1]] E1 m1) ([[c2]] E2 m2).

 Definition EqObs I E1 c1 E2 c2 O :=
  equiv (kreq_mem I) E1 c1 E2 c2 (kreq_mem O).

 Definition Vset_of_var_decl (lt:list T.type) (lv:var_decl lt) : Vset.t :=
  dfold_right (fun t (x:Var.var t) r => Vset.add x r) Vset.empty lv.

 Record info (pt:list T.type) (parms:var_decl pt) 
  (body:cmd) (t:T.type) (re:E.expr t) : Type := 
  mkInfo
  { 
     info_X : Vset.t ;
     info_lossless : forall E, lossless E body;
     info_modify   : forall E, Modify E info_X body; 
     info_modify_local : forall x, Vset.mem x info_X -> Var.is_local x;
     info_re_local : forall x, Vset.mem x (fv_expr re) -> Var.is_local x;
     info_eqobs : forall E E', 
      EqObs (Vset_of_var_decl parms) E body E' body (fv_expr re)
  }.

End SEM_THEORY.


Module Make (S:SEM). (* <: SEM_THEORY S. *)

 Export S.

 Lemma Teq_dep_refl : forall t, T.eq_dec t t = left _ (refl_equal t).
 Proof.
  intros t; case_eq (T.eq_dec t t); intros.
  rewrite (T.UIP_refl e); trivial.
  elim (T.eq_dec_r H); trivial.
 Qed.
 
 Lemma UTi_eqb_refl : forall k t v, @UT.i_eqb k t v v = true.
 Proof.
  intros k t v; generalize (UT.i_eqb_spec v v); destruct (UT.i_eqb v v);
   trivial.
  intros H; elim H; trivial.
 Qed.
 
 Lemma Ti_eqb_refl : forall k t v, T.i_eqb k t v v = true.
 Proof.
  intros k t v; generalize (T.i_eqb_spec k t v v); destruct (T.i_eqb k t v v);
   trivial.
  intros H; elim H; trivial.
 Qed.
 
 Lemma Eeqb_refl : forall t (e:E.expr t), E.eqb e e = true.
 Proof.
  intros; generalize (E.eqb_spec e e); destruct E.eqb; intros; trivial.
  elim H; trivial.
 Qed.

 Lemma is_true_Ti_eqb : forall k t v1 v2, T.i_eqb k t v1 v2 <-> v1 = v2.
 Proof.
  split; intros.
  generalize (T.i_eqb_spec k t v1 v2); rewrite H; trivial.
  rewrite H; exact (Ti_eqb_refl k t v2).
 Qed.

 Lemma is_true_UTi_eqb : forall k t v1 v2, @UT.i_eqb k t v1 v2 <-> v1 = v2.
 Proof.
  split; intros.
  generalize (@UT.i_eqb_spec k t v1 v2); rewrite H; trivial.
  rewrite H; exact (@UTi_eqb_refl k t v2).
 Qed.

 Lemma Ieqb_comm : forall i1 i2, I.eqb i1 i2 = I.eqb i2 i1.
 Proof.
  intros i1 i2; generalize (I.eqb_spec i1 i2); destruct (I.eqb i1 i2); intros;
    generalize (I.eqb_spec i2 i1); destruct (I.eqb i2 i1); intros; trivial.
  elim H0; auto.
  elim H; auto.
 Qed.

 Lemma Eeqb_comm : forall t (e1 e2:E.expr t), E.eqb e1 e2 = E.eqb e2 e1.
 Proof.
  intros t e1 e2; generalize (E.eqb_spec e1 e2); destruct (E.eqb e1 e2); intros;
    generalize (E.eqb_spec e2 e1); destruct (E.eqb e2 e1); intros; trivial.
  elim H0; auto.
  elim H; auto.
 Qed. 

 (** Sets of variables *)

 Module VarP := MkEqBool_Leibniz_Theory Var.
 Module Vset := MkListSet VarP.Edec.
 Module VsetP := MkSet_Theory Vset.

 Ltac Vset_mem_inversion H :=
  match type of H with
  | is_true (Vset.mem _ Vset.empty)  =>
    discriminate H

  | is_true (Vset.mem ?x (Vset.singleton ?y))  =>
    change (is_true (Vset.mem x (Vset.add y Vset.empty))) in H;
    Vset_mem_inversion H

  | is_true (Vset.mem (Var.mkV ?x) (Vset.add (Var.mkV ?y) ?X))  =>
    let H0 := fresh "H" in
    let H1 := fresh "H" in
    let Heq := fresh "Heq" in
     generalize (Var.eqb_spec y x);
     case_eq (Var.eqb y x); intros H0 H1;
     [ injection H1; clear H1; intros H1 ?; subst;
        assert (Heq:=T.inj_pair2 H1) |
       assert (Heq:=Vset.add_inversion _ H1 H); Vset_mem_inversion Heq ];
     clear H1 H0 H
  end.

 Notation "s [=] t" := (Vset.eq s t) (at level 70, no associativity).
 Notation "s [<=] t" := (Vset.subset s t) (at level 70, no associativity).
 Notation "s [=?] t" := (Vset.eqb s t) (at level 70, no associativity).
 Notation "s [<=?] t" := (Vset.subsetb s t) (at level 70, no associativity).
 Notation "{{ x , .. , y }}" := (Vset.add x .. (Vset.add y Vset.empty) ..).

 Definition get_globals := Vset.filter Var.is_global.

 Definition get_locals := Vset.filter Var.is_local.

 Lemma get_globals_spec : forall X x, 
  Vset.mem x (get_globals X) -> Var.is_global x.
 Proof.
  unfold get_globals; intros.
  apply Vset.filter_correct in H; intuition.
  rewrite (H0:x0 = y); trivial. 
 Qed.

 Lemma get_locals_spec : forall X x, 
  Vset.mem x (get_locals X) -> Var.is_local x.
 Proof.
  unfold get_locals; intros.
  apply Vset.filter_correct in H; intuition.
  rewrite (H0:x0 = y); trivial. 
 Qed.

 Lemma union_locals_globals : forall X, 
  Vset.union (get_locals X) (get_globals X) [=] X.
 Proof.
  unfold get_locals, Var.is_local, get_globals; intros.
  rewrite VsetP.union_sym.
  symmetry; apply VsetP.filter_union.
  intros x y H; rewrite (H:x = y); trivial.
 Qed.

 Lemma get_globals_complete : forall x X, 
  Vset.mem x X -> Var.is_global x -> Vset.mem x (get_globals X).
 Proof.
  intros; assert (W:= union_locals_globals X).
  rewrite <- W in H; rewrite VsetP.union_spec in H; destruct H; trivial.
  apply get_locals_spec in H.
  unfold Var.is_local in H; rewrite H0 in H; discriminate.
 Qed.

 Lemma get_locals_complete : forall x X, 
  Vset.mem x X -> Var.is_local x -> Vset.mem x (get_locals X).
 Proof.
  intros; assert (W:= union_locals_globals X).
  rewrite <- W in H; rewrite VsetP.union_spec in H; destruct H; trivial.
  apply get_globals_spec in H.
  unfold Var.is_local in H0; rewrite H in H0; discriminate.
 Qed.

 Lemma get_globals_subset : forall X, get_globals X [<=] X.
 Proof.
  intros X; set (Y:= get_globals X); rewrite <- (union_locals_globals X).
  auto with set.
 Qed.

 Lemma get_locals_subset : forall X, get_locals X [<=] X.
 Proof.
  intros X; set (Y:= get_locals X); rewrite <- (union_locals_globals X).
  auto with set.
 Qed.


 (** Dependent variable mapping *)
 Module VM.

  Section DEF.

   Variable A : T.type -> Type.
   
   Record elem : Type := mkE {
    e_t : T.type;
    e_A : A e_t
   }.

   Definition t := (Tree.tree (list elem) * Tree.tree (list elem))%type.
   
   Fixpoint assoc  (t:T.type) (l:list elem) : option (A t) :=
    match l with
    | nil => None
    | e::l =>
      match T.eq_dec (e_t e) t with
      | left Heq => 
         match Heq in (_ = y0) return option (A y0) with
         | refl_equal => Some (e_A e)
         end
      | _ => assoc t l 
      end
    end.

   Definition get (m:t) (tx:T.type) (x:Var.var tx) : option (A tx) := 
    match x, m with
    | Var.Gvar _ x, (tg, tl) => assoc tx (Tree.get nil tg x)
    | Var.Lvar _ x, (tg, tl) => assoc tx (Tree.get nil tl x)
    end.

   Definition remove_t (t:T.type) :=
    List.filter (fun p : elem => negb (T.eqb t (e_t p))).

   Definition eq_def  (l:list elem) :=
    match l with
    | nil => true
    | _ => false
    end.

   Lemma eq_def_spec : forall a0 : list elem, 
    if eq_def a0 then a0 = nil else a0 <> nil.
   Proof.
    destruct a0; simpl; trivial.
    intro; discriminate.
   Qed.

   Hint Resolve eq_def_spec.

   Definition upd (m:t) (tx:T.type) (x:Var.var tx) (a:A tx) : t :=
    match x, m with
    | Var.Gvar _ x, (tg, tl) => 
      (Tree.upd nil eq_def tg x (fun l => mkE a::remove_t tx l) , tl)
    | Var.Lvar _ x, (tg, tl) => 
      (tg, Tree.upd nil eq_def tl x (fun l => mkE a ::remove_t tx l))
    end.
   
   Definition empty : t := (Tree.Empty _, Tree.Empty _). 

   Lemma get_upd_same : forall m t (x:Var.var t) a, get (upd m x a) x = Some a.
   Proof.
    destruct x; destruct m; simpl; intros.
    rewrite Tree.get_upd_same; intros; auto.
    simpl; case_eq (T.eq_dec t0 t0); intros.
    clear H; rewrite (T.UIP_refl e); trivial.
    elim (T.eq_dec_r H (refl_equal _)).
    apply eq_def_spec.
    rewrite Tree.get_upd_same; intros; auto.
    simpl; case_eq (T.eq_dec t0 t0); intros.
    clear H; rewrite (T.UIP_refl e); trivial.
    elim (T.eq_dec_r H (refl_equal _)).
    apply eq_def_spec.
   Qed.

   Lemma find_remove : forall t0 t1, 
    t0 <> t1 -> 
    forall l, assoc t1 (remove_t t0 l) = assoc t1 l.
   Proof. 
    induction l; simpl; intros; trivial.
    generalize (T.eqb_spec t0 (e_t a)).
    destruct (T.eqb t0 (e_t a)); intros; subst; simpl; trivial.
    case_eq (T.eq_dec (e_t a) t1); intros; auto.
    elim (H e).
    case_eq (T.eq_dec (e_t a) t1); intros; auto.
   Qed.
   
   Lemma get_upd_diff : forall m tx (x:Var.var tx) ty (y:Var.var ty) a, 
    Var.mkV x <> y -> get (upd m x a) y = get m y.
   Proof. 
    destruct x; destruct y; destruct m; simpl; intros; trivial.
    generalize (PosEq.eqb_spec p p0).
    destruct (PosEq.eqb p p0); intros; subst; trivial.
    rewrite Tree.get_upd_same; intros; auto.
    simpl; case_eq (T.eq_dec t0 t1); intros.
    rewrite e in H; elim H; trivial.
    apply find_remove.
    apply T.eq_dec_r with (1:= H0).
    apply eq_def_spec.
    rewrite Tree.get_upd_diff; auto.
    apply eq_def_spec.
    generalize (PosEq.eqb_spec p p0).
    destruct (PosEq.eqb p p0); intros; subst; trivial.
    rewrite Tree.get_upd_same; intros; auto.
    simpl; case_eq (T.eq_dec t0 t1); intros.
    rewrite e in H; elim H; trivial.
    apply find_remove.
    apply T.eq_dec_r with (1:= H0).
    apply eq_def_spec.
    rewrite Tree.get_upd_diff; auto.
    apply eq_def_spec.
   Qed.
   
   Lemma empty_spec : forall tx (x:Var.var tx), get empty x = None.
   Proof.
    destruct x; trivial.
   Qed.

   Definition remove tx (x:Var.var tx) (m:t) : t :=
    match x, m with
    | Var.Gvar _ x, (tg, tl) => 
      (Tree.upd nil eq_def tg x (remove_t tx) , tl)
    | Var.Lvar _ x, (tg, tl) => 
      (tg, Tree.upd nil eq_def tl x (remove_t tx))
    end.

   Lemma assoc_remove : forall t0 l, 
    assoc t0 (remove_t t0 l) = None.
   Proof.
    induction l; simpl; trivial.
    generalize (T.eqb_spec t0 (e_t a)).
    destruct (T.eqb t0 (e_t a)); intros; subst; simpl; auto.
    case_eq (T.eq_dec (e_t a) t0); intros; trivial.
    elim H; auto.
   Qed.

   Lemma get_remove_same : forall m tx (x:Var.var tx), 
    get (remove x m) x = None.
   Proof.
    destruct x; destruct m; simpl; intros.
    rewrite Tree.get_upd_same.
    apply assoc_remove.
    apply eq_def_spec.
    rewrite Tree.get_upd_same.
    apply assoc_remove.
    apply eq_def_spec.
   Qed.

   Lemma get_remove_diff : forall m tx (x:Var.var tx) ty (y:Var.var ty), 
    Var.mkV x <> y -> 
    get (remove x m) y = get m y.
   Proof. 
    destruct x; destruct y; destruct m; simpl; intros; trivial.
    generalize (PosEq.eqb_spec p p0).
    destruct (PosEq.eqb p p0); intros; subst; trivial.
    rewrite Tree.get_upd_same; intros; auto.
    rewrite find_remove; trivial.
    intros Heq; apply H; rewrite Heq; trivial.
    apply eq_def_spec.
    rewrite Tree.get_upd_diff; trivial.
    apply eq_def_spec.
    generalize (PosEq.eqb_spec p p0).
    destruct (PosEq.eqb p p0); intros; subst; trivial.
    rewrite Tree.get_upd_same; intros; auto.
    rewrite find_remove; trivial.
    intros Heq; apply H; rewrite Heq; trivial.
    apply eq_def_spec.
    rewrite Tree.get_upd_diff; trivial.
    apply eq_def_spec.
   Qed. 

   Fixpoint rfilter (f:elem->bool) (l:list elem) {struct l} : list elem := 
    match l with 
    | nil => nil 
    | p::l => 
      if f p then 
       rfilter (fun p' => if T.eqb (e_t p) (e_t p') then true else f p') l
       else p :: rfilter f l
    end.

   Definition filter (f:forall t, A t->bool) (m:t) : t :=
    (Tree.map eq_def 
     (rfilter (fun (p:elem) => negb (f (e_t p) (e_A p)))) (fst m), 
     Tree.map eq_def 
     (rfilter (fun (p:elem) => negb (f (e_t p) (e_A p)))) (snd m)).
  
   Lemma rfilter_None : forall t l f, 
    (forall (a:A t), f (mkE a) = true) ->
    assoc t (rfilter f l) = None.
   Proof.
    induction l; simpl; intros; trivial.
    case_eq (f a); intros; simpl; auto.
    apply IHl; simpl; intros.
    rewrite H; destruct (T.eqb (e_t a) t0); trivial.
    case_eq (T.eq_dec (e_t a) t0); intros; auto.
    elimtype False; destruct a; simpl in e.
    generalize e_A0 H0; rewrite e; intro; rewrite H; intro; discriminate.
   Qed.

   Lemma assoc_filter :  forall t0 a l f,
    assoc t0 (rfilter f l) = Some a <-> 
    assoc t0 l = Some a /\ f (mkE  a) = false.
   Proof.
    induction l; simpl; split; intros.
    discriminate.
    destruct H; trivial.
    case_eq (f a0); intros Heq; rewrite Heq in H; simpl in H.
    case_eq (T.eq_dec (e_t a0) t0); intros. 
    rewrite  rfilter_None in H; try discriminate.
    simpl; intros.
    rewrite e; generalize (T.eqb_spec t0 t0).
    destruct (T.eqb t0 t0); auto; intros; subst.
    rewrite IHl in H; simpl in H.
    generalize (T.eqb_spec (e_t a0) t0).
    destruct (T.eqb (e_t a0) t0); auto; intros; subst.
    elim (T.eq_dec_r H0); trivial.
    generalize H; case_eq (T.eq_dec (e_t a0) t0); clear H.
    intros e _; generalize e a; rewrite <- e; intros e'.
    rewrite (T.UIP_refl e'); intros.
    inversion H; subst; destruct a0; simpl; auto.
    intros t1 W H; rewrite IHl in H; auto.
    case_eq (f a0); intros Heq.
    rewrite IHl; simpl.
    generalize (T.eqb_spec (e_t a0) t0).
    destruct (T.eqb (e_t a0) t0); auto; intros; subst.
    generalize H; clear H; case_eq (T.eq_dec (e_t a0) (e_t a0)); intros.
    rewrite (T.UIP_refl e) in H0; destruct H0; destruct a0; simpl in *.
    inversion H0; subst; rewrite H1 in Heq; discriminate.
    elim (T.eq_dec_r H); trivial.
    generalize H; clear H; case_eq (T.eq_dec (e_t a0) t0); intros; trivial.
    elim (H0 e).
    generalize H; clear H; simpl.
    case_eq (T.eq_dec (e_t a0) t0); intros; trivial.
    destruct H0; trivial.
    rewrite IHl; auto.
   Qed.

   Lemma filter_spec :  forall f tx (x:Var.var tx) a m,
    get (filter f m) x = Some a <-> 
    get m x = Some a /\ f tx a = true.
   Proof.
    destruct x; destruct m; simpl; intros.
    rewrite (@Tree.map_spec (list elem) (list elem) nil); trivial.
    rewrite assoc_filter; simpl; trivial.
    intuition.
    destruct (f t0 a); trivial; discriminate.
    rewrite H1; trivial.
    apply eq_def_spec.
    rewrite (@Tree.map_spec (list elem) (list elem) nil); trivial.
    rewrite assoc_filter; simpl; trivial.
    intuition.
    destruct (f t0 a); trivial; discriminate.
    rewrite H1; trivial.
    apply eq_def_spec.
   Qed.

  End DEF.

  Section MAP2.
   
   Variables A B C: T.type -> Type. 
   Variable f : forall t,  A t -> B t -> option (C t).

   Definition f_opt2 t o1 o2 :=
    match o1, o2 with
    | Some a, Some b => @f t a b
    | _, _ => None
    end.

   Section MAP2_ASSOC.
    
    Fixpoint map2_list (test:T.type -> bool) 
     (la:list (elem A)) (lb : list (elem B)) : list (elem C) :=
     match lb with
     | nil => nil
     | (mkE t b) :: lb =>
       if test t then 
       match assoc t la with
       | None => 
         map2_list (fun t' => if T.eqb t t' then false else test t') la lb 
       | Some a => 
         match f a b with
         | None => 
           map2_list (fun t' => if T.eqb t t' then false else test t') la lb 
         | Some c => 
           mkE C t c :: map2_list (fun t' => if T.eqb t t' then false else test t') la lb 
         end
       end
       else map2_list (fun t' => if T.eqb t t' then false else test t') la lb 
     end.

    Lemma map2_list_None : forall t la lb (test:T.type -> bool), 
     test t = false -> 
     assoc t (map2_list test la lb) = None.
    Proof.
     induction lb; simpl; intros; trivial.
     destruct a as (t1, b).
     case_eq (test t1); intros.
     case_eq (assoc t1 la); intros.
     case_eq (f a b); intros.
     simpl.
     case_eq (T.eq_dec t1 t0); intros.
     rewrite e in H0; rewrite H0 in H; discriminate.
     apply IHlb; destruct (T.eqb t1 t0); trivial.
     apply IHlb; destruct (T.eqb t1 t0); trivial.
     apply IHlb; destruct (T.eqb t1 t0); trivial.
     apply IHlb; destruct (T.eqb t1 t0); trivial.
    Qed.

    Lemma map2_list_spec : forall t la lb (test:T.type -> bool), 
     test t -> 
     assoc t (map2_list test la lb) = f_opt2 (assoc t la) (assoc t lb).
    Proof.
     induction lb; simpl; intros; trivial.
     destruct  (assoc t0 la); trivial.
     destruct a as (t1, b).
     case_eq (test t1); intro.
     case_eq (assoc t1 la); intros; simpl.
     case_eq (T.eq_dec t1 t0); intros; trivial.
     generalize e; rewrite <- e, H1; intros e'; rewrite (T.UIP_refl e'); trivial.
     simpl.
     case_eq (f a b); intros.
     simpl.
     case_eq (T.eq_dec t1 t1); intros.
     rewrite (T.UIP_refl e0); trivial.
     elim (T.eq_dec_r H4 (refl_equal _)).
     apply map2_list_None.
     generalize (T.eqb_spec t1 t1); destruct (T.eqb t1 t1); trivial.
     intro K; elim K; trivial.
     case_eq (f a b); intros; simpl.
     rewrite H2; apply IHlb.
     generalize (T.eqb_spec t1 t0); destruct (T.eqb t1 t0); trivial.
     intro K; elim (T.eq_dec_r H2 K).
     apply IHlb.
     generalize (T.eqb_spec t1 t0); destruct (T.eqb t1 t0); trivial.
     intro K; elim (T.eq_dec_r H2 K).
     case_eq (T.eq_dec t1 t0); intros; trivial.
     generalize e; rewrite <- e; intros e'; rewrite (T.UIP_refl e'); trivial.
     rewrite H1; simpl.
     apply map2_list_None.
     generalize (T.eqb_spec t1 t1); destruct (T.eqb t1 t1); trivial.
     intro K; elim K; trivial.
     apply IHlb.
     generalize (T.eqb_spec t1 t0); destruct (T.eqb t1 t0); trivial.
     intro K; elim (T.eq_dec_r H2 K).
     simpl.
     case_eq (T.eq_dec t1 t0); intros; trivial.
     rewrite e in H0; rewrite H0 in H; discriminate. 
     apply IHlb.
     generalize (T.eqb_spec t1 t0); destruct (T.eqb t1 t0); trivial.
     intro K; elim (T.eq_dec_r H1 K).
    Qed.

   End MAP2_ASSOC.

   Definition map2 (m1:t A) (m2:t B) : t C :=
    let (g1, l1) := m1 in
    let (g2, l2) := m2 in
     (Tree.map2 nil nil (@eq_def C) (map2_list (fun _ => true)) g1 g2, 
      Tree.map2 nil nil (@eq_def C) (map2_list (fun _ => true)) l1 l2).

   Lemma map2_spec : forall m1 m2 tx (x:Var.var tx),
    get (map2 m1 m2) x = f_opt2 (get m1 x) (get m2 x).
   Proof.
    intros (g1,l1) (g2,l2) tx x; destruct x; simpl.
    rewrite Tree.map2_spec; trivial.
    apply map2_list_spec; trivial.
    apply eq_def_spec.
    rewrite Tree.map2_spec; trivial.
    apply map2_list_spec; trivial.
    apply eq_def_spec.
   Qed.
  
  End MAP2.

  Section FORALLB_I.

   Variable A : T.type -> Type.
   Variable f : forall t, Var.var t -> A t -> bool.

   Fixpoint forallb_assoc (l:list (elem A)) (f : forall t, A t -> bool) :=
    match l with
    | nil => true
    | (mkE t a)::l => 
      if f t a then 
       forallb_assoc l (fun t' a => if T.eqb t' t then true else f t' a)
       else false
    end.
   
   Lemma forallb_assoc_spec : forall l f, 
    forallb_assoc l f <-> forall t a, assoc t l = Some a -> f t a.
   Proof.
    induction l; simpl; intros.
    split; intros; trivial.
    discriminate.
    destruct a as (ta, a).
    case_eq (f0 ta a); intros.
    rewrite IHl; split.
    simpl; intros H1 t0 a0.
    case_eq (T.eq_dec ta t0).
    intros e; generalize e a H; rewrite e; intros e'.
    rewrite (T.UIP_refl e'); intros.
    inversion H3; subst; trivial.
    intros.
    generalize (T.eqb_spec t0 ta) (H1 t0).
    destruct (T.eqb t0 ta); simpl; intros; auto.
    elim (T.eq_dec_r H0); auto.
    simpl; intros.
    generalize (T.eqb_spec t0 ta); destruct (T.eqb t0 ta); simpl; intros; auto.
    generalize (H0 t0 a0); clear H0; case_eq (T.eq_dec ta t0); auto.
    intros e; elim H2; auto.
    split; intros; trivialb.
    rewrite <- H; apply H0; simpl.
    case_eq (T.eq_dec ta ta); intros; auto.
    rewrite (T.UIP_refl e); trivial.
    elim (T.eq_dec_r H1); trivial.
   Qed.

   Definition forallb_i (m:t A) :=
    let (g, l) := m in
     if Tree.forallb_i (fun k l => forallb_assoc l (fun t a => f (Var.Gvar t k) a)) g then
      Tree.forallb_i (fun k l => forallb_assoc l (fun t a => f (Var.Lvar t k) a)) l
     else false.
   
   Lemma forallb_i_spec : forall m, 
    forallb_i m <-> forall tx (x:Var.var tx) e, get m x = Some e -> f x e.
   Proof.
    intros (g, l); simpl.
    set (F:= (fun (k : positive) (l0 : list (elem A)) =>
     forallb_assoc l0 (fun (t0 : T.type) (a : A t0) => f (Var.Gvar t0 k) a))).
    set (Fl:= (fun (k : positive) (l0 : list (elem A)) =>
     forallb_assoc l0 (fun (t0 : T.type) (a : A t0) => f (Var.Lvar t0 k) a))).
    assert (forall k : positive, F k nil = true) by trivial.
    assert (forall k : positive, Fl k nil = true) by trivial.
    generalize (Tree.forallb_i_spec  nil F H g).
    destruct (Tree.forallb_i F g).
    rewrite (Tree.forallb_i_spec  nil Fl H0 l); intros (H1, H2); split; intros.
    destruct x; simpl in H4.
    assert (W:= H1 (refl_equal _) p); unfold F in W.
    change (is_true (forallb_assoc (Tree.get nil g p)
     (fun (t0 : T.type) (a : A t0) => f (Var.Gvar t0 p) a))) in W.
    rewrite forallb_assoc_spec in W; auto.
    assert (W:= H3 p); unfold Fl in W.
    change (is_true (forallb_assoc (Tree.get nil l p)
     (fun (t0 : T.type) (a : A t0) => f (Var.Lvar t0 p) a))) in W.
    rewrite forallb_assoc_spec in W; auto.
    change (is_true (Fl k (Tree.get nil l k))); unfold Fl.
    rewrite forallb_assoc_spec.
    intros; apply H3; trivial.
    intros; split; intros; trivialb.
    unfold is_true; rewrite H1; intros.
    change (is_true (F k (Tree.get nil g k))); unfold F.
    rewrite forallb_assoc_spec. 
    intros; apply H2; auto.
   Qed.

  End FORALLB_I.


  Section EQ.

   Variable A : T.type -> Type.
   Variable Aeqb : forall t, A t -> A t -> bool.
   Variable Aeq : forall t, A t -> A t -> Prop.

   Hypothesis Aeq_refl : forall t (x:A t), Aeq x x.
   Hypothesis Aeq_trans : forall t (x y z:A t), Aeq x y -> Aeq y z -> Aeq x z.
   Hypothesis Aeq_sym : forall t (x y:A t), Aeq x y -> Aeq y x.
   Hypothesis Aeqb_spec : forall t (x y:A t), 
    if Aeqb x y then Aeq x y else ~Aeq x y.

   Definition oeq t (x y:option (A t)) := 
    match x, y with
    | Some a1, Some a2 => Aeq a1 a2
    | None, None => True
    | _, _ => False
    end. 
  
   Lemma oeq_refl : forall t (x:option (A t)), oeq x x.
   Proof.
    destruct x; simpl; auto. 
   Qed.

   Lemma oeq_sym : forall t (x y:option (A t)), oeq x y -> oeq y x.
   Proof. 
    destruct x; destruct y; simpl; auto. 
   Qed.

   Lemma oeq_trans : forall t (x y z:option (A t)), oeq x y -> oeq y z -> oeq x z.
   Proof.
    destruct x; destruct y; destruct z; simpl; eauto.
    intros H; elim H.
   Qed.
  
   Definition oeqb t (x y:option (A t)) := 
    match x, y with
    | Some a1, Some a2 => Aeqb a1 a2
    | None, None => true
    | _, _ => false
    end. 

   Lemma oeqb_spec : forall t (x y:option (A t)), 
    if oeqb x y then oeq x y else ~oeq x y.
   Proof.
    destruct x; destruct y; auto; simpl; auto.
    apply Aeqb_spec.
   Qed.

   Definition eq (m1 m2:t A) :=
    forall tx (x:Var.var tx), oeq (get m1 x) (get m2 x).  
   
   Lemma eq_refl : forall x, eq x x.
   Proof. 
    unfold eq; intros; apply oeq_refl; trivial. 
   Qed.

   Lemma eq_sym : forall x y, eq x y -> eq y x.
   Proof. 
    unfold eq; intros; apply oeq_sym; trivial.
   Qed.
   
   Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
   Proof. 
    unfold eq; intros; eapply oeq_trans; eauto. 
   Qed.

   Definition leb_assoc (l1 l2 : list (elem A)) : bool :=
    forallb_assoc l1 (fun t a1 => 
     match assoc t l2 with
     | None => false
     | Some a2 => Aeqb a1 a2
     end).

   Definition eqb_assoc l1 l2 := 
    if leb_assoc l1 l2 then leb_assoc l2 l1 else false.

   Definition eqb (m1 m2 : t A) :=
    let (tl1, tr1) := m1 in
    let (tl2, tr2) := m2 in
     if Tree.eqb nil eqb_assoc tl1 tl2 
      then Tree.eqb nil eqb_assoc tr1 tr2 
      else false.

   Lemma eqb_assoc_nil : eqb_assoc nil nil.
   Proof. 
    trivial. 
   Qed.
  
   Lemma eqb_assoc_comm: forall l1 l2, eqb_assoc l2 l1 = eqb_assoc l1 l2.
   Proof.
    unfold eqb_assoc; intros.
    destruct (leb_assoc l2 l1); destruct (leb_assoc l1 l2); trivial.
   Qed.
  
   Definition eq_assoc l1 l2 := forall t, oeq (t:=t) (assoc t l1) (assoc t l2).
  
   Definition le_assoc l1 l2 := forall t,
    match assoc t l1, assoc t l2 with
    | None, _ => True
    | Some a1, Some a2 => Aeq (t:=t) a1 a2
    | _, _ => False
    end.

   Lemma leb_le_assoc : forall l1 l2, 
    if leb_assoc l1 l2 then le_assoc l1 l2 else ~le_assoc l1 l2.
   Proof. 
    intros l1 l2; unfold leb_assoc.
    set (F:= fun (t0 : T.type) (a1 : A t0) =>
     match assoc t0 l2 with
     | Some a2 => Aeqb a1 a2
     | None => false
     end).
    generalize (forallb_assoc_spec l1 F).
    destruct (forallb_assoc l1 F); intros.
    destruct H; red; intros.
    assert (W:= H (refl_equal _) t0); unfold F in W.
    destruct (assoc t0 l1); auto.
    destruct (assoc t0 l2); auto.
    generalize (Aeqb_spec a a0); rewrite W; trivial.
    assert (W' := W _ (refl_equal _)); discriminate.
    intro; assert (forall (t : T.type) (a : A t), assoc t l1 = Some a -> F t a).
    intros.
    assert (W:= H0 t0); rewrite H1 in W.
    unfold F; destruct (assoc t0 l2).
    generalize (Aeqb_spec a a0); destruct (Aeqb a a0); intros; trivial.
    elim H2; trivial.
    elim W.
    destruct H as (_, H); assert (W:= H H1); discriminate.
   Qed.

   Lemma eqb_eq_assoc : forall l1 l2, 
    if eqb_assoc l1 l2 then eq_assoc l1 l2 else ~eq_assoc l1 l2.
   Proof.
    unfold eqb_assoc; intros.
    generalize (leb_le_assoc l1 l2); destruct (leb_assoc l1 l2); intros.
    generalize (leb_le_assoc l2 l1); destruct (leb_assoc l2 l1); intros.
    unfold eq_assoc, le_assoc in *; intros.
    assert (H1 := H t0); assert (H2 := H0 t0).
    destruct (assoc t0 l1); destruct (assoc t0 l2); auto.
    intros H1; apply H0; intro.
    assert (W:= H1 t0).
    destruct (assoc t0 l1); destruct (assoc t0 l2); auto.
    intros H1; apply H; intro.
    assert (W:= H1 t0).
    destruct (assoc t0 l1); destruct (assoc t0 l2); auto.
   Qed.
   
   Lemma eqb_spec : forall m1 m2, 
    if eqb m1 m2 then eq m1 m2 else ~eq m1 m2.
   Proof.
    intros (tl1, tr1) (tl2,tr2); simpl.
    generalize (Tree.eqb_spec nil eqb_assoc eqb_assoc_nil 
     (eqb_assoc_comm nil) eq_assoc 
     eqb_eq_assoc tl1 tl2).
    destruct (Tree.eqb nil eqb_assoc tl1 tl2).
    generalize (Tree.eqb_spec nil eqb_assoc eqb_assoc_nil 
     (eqb_assoc_comm nil) eq_assoc 
     eqb_eq_assoc tr1 tr2).
    destruct (Tree.eqb nil eqb_assoc tr1 tr2).
    intros; intro; destruct x; simpl; auto.
    exact (H0 p t0).
    exact (H p t0).
    intros H _ H1; apply H; intros k t0.
    exact (H1 t0 (Var.Lvar t0 k)).
    intros H H1; apply H; intros k t0.
    exact (H1 t0 (Var.Gvar t0 k)). 
   Qed.

  End EQ.

 End VM.


 (** Memory *)

 Definition mem_eqU k (x y:Mem.t k) := if Mem.eqb x y then 1 else 0.
 
 Lemma mem_eqU_spec : forall k (x:Mem.t k), cover (fun y => x = y) (mem_eqU x).
 Proof.
  unfold cover, mem_eqU; intros.
  assert (X:=Mem.eqb_spec  x x0).
  destruct (Mem.eqb x x0); split; intros; trivial; elimtype False; auto.
 Qed.

 (* Order over memory relation *)

 Definition mem_rel := forall k, Mem.t k -> Mem.t k -> Prop.

 Definition implMR (P1 P2 : mem_rel) : Prop := forall k m1 m2,
   P1 k m1 m2 -> P2 k m1 m2.
 
 Lemma implMR_refl : reflexive _ implMR.
 Proof. red; red; trivial. Qed.
   
 Lemma implMR_trans: transitive _ implMR.
 Proof.
  red; unfold implMR; auto.
 Qed.
 
 Add Relation mem_rel implMR
  reflexivity proved by implMR_refl
  transitivity proved by implMR_trans
 as implMR_relation.

 (* equality over memory relation *)
 Definition iffMR (P1 P2 : mem_rel) : Prop := 
   implMR P1 P2 /\ implMR P2 P1.
 
 Lemma iffMR_refl : reflexive _ iffMR.
 Proof. red; red; auto using implMR_refl. Qed.

 Lemma iffMR_sym : symmetric _ iffMR.
 Proof. 
  red; unfold iffMR; intros; tauto.
 Qed.

 Lemma iffMR_trans : transitive _ iffMR.
 Proof.
  red; unfold iffMR; intros; intuition; eauto using implMR_trans.
 Qed.

 Add Relation mem_rel iffMR
  reflexivity proved by iffMR_refl
  symmetry proved by iffMR_sym
  transitivity proved by iffMR_trans
 as iffMR_relation.
 
 Add Morphism implMR with signature iffMR ==> iffMR ==> iff as implMR_iff.
 Proof. 
   unfold iffMR, implMR; intuition; eauto.
 Qed.

 Hint Resolve iffMR_refl implMR_refl.

 Definition Meq : mem_rel := fun k (x y:Mem.t k) => x = y.
 Implicit Arguments Meq [ ].
 
 Lemma Meq_refl : forall k (m:Mem.t k), Meq k m m.
 Proof. 
  unfold Meq; trivial. 
 Qed.

 Hint Resolve Meq_refl.

 Lemma Meq_sym : forall k (m1 m2:Mem.t k), 
  Meq k m1 m2 -> Meq k m2 m1.
 Proof. 
  unfold Meq; auto. 
 Qed. 

 Lemma Meq_trans : forall k (m1 m2 m3:Mem.t k), 
  Meq k m1 m2 -> Meq k m2 m3 -> Meq k m1 m3.
 Proof. 
  unfold Meq; eauto using trans_eq. 
 Qed.

 Hint Immediate Meq_sym.

 Add Parametric Relation (k:nat) : (Mem.t k) (@Meq k)
  reflexivity proved by (@Meq_refl k)
  symmetry proved by (@Meq_sym k)
  transitivity proved by (@Meq_trans k)
  as Meq_rel.

 (** ** Sub equality of memories *)

 Definition req_mem k X (m1 m2:Mem.t k) := 
  forall t (x:Var.var t), Vset.mem x X -> m1 x = m2 x.

 Notation " m1 '=={' X '}' m2 " := 
  (req_mem X m1 m2) (at level 70, no associativity).  

 Lemma req_mem_refl : forall k X (m:Mem.t k), m =={X} m.
 Proof. 
  unfold reflexive, req_mem; trivial. 
 Qed.

 Hint Resolve req_mem_refl.

 Lemma req_mem_sym : forall X k (m1 m2:Mem.t k), m1 =={X} m2 -> m2 =={X} m1.
 Proof. 
  red; firstorder. 
 Qed.

 Hint Immediate req_mem_sym.

 Lemma req_mem_trans : forall X k (m1 m2 m3:Mem.t k), m1 =={X} m2 -> m2 =={X} m3 -> m1 =={X} m3.
 Proof.
  unfold req_mem; intros; eauto using trans_eq.
 Qed.


 Lemma req_mem_PER: forall (X:Vset.t) (k: nat), @RelationClasses.PER (Mem.t k) (@req_mem k X).
 Proof.
  intros X k; constructor.
  intros m1 m2; apply req_mem_sym.
  intros m1 m2 m3; apply req_mem_trans.
 Qed.

 Lemma req_mem_weaken : forall k X X',
  X [<=] X' -> forall (m m':Mem.t k), m =={X'} m' -> m =={X} m'.
 Proof.
  unfold req_mem; intros; eauto using Vset.subset_correct.
 Qed.

 Add Parametric Morphism (k:nat) : (req_mem (k:=k)) 
  with signature Vset.subset ==> (@Meq k) ==> (@Meq k) ==> inverse impl 
  as req_mem_weaken_morph.
 Proof.
  unfold flip; red; intros.
  rewrite H0, H1; eapply req_mem_weaken; eauto.
 Qed.

 Hint Unfold flip.

 Add Parametric Morphism (k:nat) : (req_mem (k:=k)) with 
  signature Vset.eq ==> (@Meq k) ==> (@Meq k) ==> iff 
  as req_mem_weaken_iff_morph.
 Proof. 
  split; intros.
  rewrite <- H0, <- H1.
  apply req_mem_weaken with x; auto with set.
  rewrite H0, H1.
  apply req_mem_weaken with y; auto with set.
 Qed.

 Definition kreq_mem X : mem_rel := fun k => @req_mem k X.

 Add Morphism kreq_mem 
  with signature Vset.subset --> implMR 
  as req_mem_subsetMR_morph.
 Proof.
  unfold flip, implMR, kreq_mem; intros.
  eapply req_mem_weaken_morph.
  unfold flip; eexact H.
  apply Meq_refl.
  apply Meq_refl.
  trivial.
 Qed.

 Add Morphism kreq_mem 
  with signature Vset.eq ==> iffMR 
  as req_mem_eqMR_morph.
 Proof.
  unfold iffMR; split; intros;
  apply req_mem_subsetMR_morph; unfold Basics.flip; auto with set.
 Qed.

 Lemma kreq_mem_refl : forall X k (m:Mem.t k), kreq_mem X m m.
 Proof. 
  unfold kreq_mem; trivial. 
 Qed.

 Lemma kreq_mem_sym : forall X k (m1 m2:Mem.t k), 
  kreq_mem X m1 m2 -> kreq_mem X m2 m1. 
 Proof. 
  unfold kreq_mem; intros; auto. 
 Qed.

 Hint Resolve kreq_mem_refl.
 Hint Immediate kreq_mem_sym.
   
 Lemma req_mem_empty : forall k (m m':Mem.t k), m =={Vset.empty} m'.
 Proof.
  unfold req_mem; intros.
  elim (Vset.empty_spec H).
 Qed.

 Hint Resolve req_mem_empty.
  
 Lemma req_mem_union : forall k O1 O2 (m m' : Mem.t k),
  m =={O1} m' -> m =={O2} m' -> 
  m =={Vset.union O1 O2} m'.
 Proof.
  unfold req_mem; intros.
  destruct (Vset.union_correct _ _ _ H1); auto.
 Qed.
  
 Lemma req_mem_update : forall k X (m m':Mem.t k) t (d:Var.var t) v,
  m =={X} m' -> 
  m{!d<-- v!} =={Vset.add d X} m'{!d<--v!}.
 Proof.
  intros k X m m' td d v H t x0 Hmem.
  destruct (VarP.eq_dec d x0).
  inversion e; simpl.
  repeat rewrite Mem.get_upd_same; auto.
  repeat rewrite Mem.get_upd_diff; trivial.
  eauto using Vset.add_inversion. 
 Qed. 

 Lemma req_mem_upd_disjoint : forall t (x:Var.var t) k (m:Mem.t k) v X, 
   Vset.mem x X = false -> m =={ X}m {!x <-- v!}.
 Proof.
  unfold req_mem; intros.
  destruct (Vset.ET.eq_dec x x0).
  rewrite (e: Var.mkV x = x0) in H; rewrite H in H0; trivialb.
  rewrite Mem.get_upd_diff; trivial.
 Qed.

 
 Definition update_mem k (m1:Mem.t k) (X:Vset.t) (m2:Mem.t k) : Mem.t k := 
  Vset.fold (fun x m => m {! x <-- m2 x!}) X m1.
 
 Notation "m1 '{!' X '<<-' m2 '!}'" := (update_mem m1 X m2) (at level 60).
 
 Lemma update_mem_aux : forall k l (m1 m2:Mem.t k), 
  (forall t (x:Var.var t), InA (@Logic.eq Var.t) x l -> 
   (fold_left (fun m (x:Var.t) => 
    m {! x <-- m2 x !}) l m1) x = m2 x) /\
  (forall t (x:Var.var t), ~ InA (@Logic.eq Var.t) x l -> 
   (fold_left (fun m (x:Var.t) => 
    m {! x <-- m2 x !}) l m1) x = m1 x).
 Proof.
  induction l; intros; split; intros; simpl; auto.
  inversion H.
  inversion H; subst; clear H.
  destruct (IHl (m1 {! x <-- m2 x !}) m2).
  destruct (InA_dec (@Logic.eq Var.t) VarP.eq_dec x l).
  apply H; trivial. 
  rewrite H0; trivial.
  apply Mem.get_upd_same.
  destruct (IHl (m1 {! a <-- m2 a!}) m2); auto.
  rewrite H; trivial.
  destruct (IHl (m1 {! a <-- m2 a!}) m2); auto.
  rewrite H1.
  destruct a; rewrite Mem.get_upd_diff; trivial.
  intuition.
  intuition.
 Qed.
 
 Lemma update_mem_in : forall k (m1:Mem.t k) X m2 t (x:Var.var t), 
  Vset.mem x X ->
  (m1{!X <<- m2!}) x = m2 x.
 Proof.
  unfold update_mem; intros.
  destruct (update_mem_aux (Vset.elements X) m1 m2).
  rewrite Vset.fold_spec.
  apply H0.
  apply Vset.elements_correct; trivial.
 Qed.

 Lemma update_mem_notin : forall k (m1:Mem.t k) X m2 t (x:Var.var t), 
  ~Vset.mem x X ->
  (m1{!X <<- m2!}) x = m1 x.
 Proof.
  unfold update_mem; intros.
  destruct (update_mem_aux (Vset.elements X) m1 m2).
  rewrite Vset.fold_spec. 
  apply H1. 
  intros Hin.
  apply H; apply Vset.elements_complete; trivial.
 Qed.

 Add Parametric Morphism (k:nat) : (update_mem (k:=k))
  with signature @Meq k ==> Vset.eq ==> @Meq k ==> @Meq k
  as update_mem_morphism.
 Proof.
  unfold Meq; intros; subst.
  apply Mem.eq_leibniz; red; intros.
  destruct (VsetP.mem_dec x y0).
  destruct x; repeat rewrite update_mem_in; trivial.
  rewrite H0; trivial.	 
  destruct x; repeat rewrite update_mem_notin; trivial. 
  rewrite H0; trivial.
 Qed.

 Lemma update_update_mem_subset_l :  forall k (m m1 m2:Mem.t k) X Y,
  X [<=] Y ->
  m1 =={X} m2 ->
  m {!Y<<-m1!} = m {!Y<<-m1!}{!X<<- m2!}.
 Proof.
  intros; apply Mem.eq_leibniz.
  rewrite VsetP.subset_iff in H; intros (t, x).
  destruct (VsetP.mem_dec x X).
  repeat rewrite update_mem_in; auto.
  symmetry;rewrite update_mem_notin; auto.
 Qed.

 Lemma update_mem_same : forall k (m:Mem.t k) X, m = m {!X <<- m!}.
 Proof.
  intros k m X; apply Mem.eq_leibniz; intros (t,y).
  destruct (VsetP.mem_dec y X).
  rewrite update_mem_in; auto.
  rewrite update_mem_notin; auto.
 Qed.
 
 Lemma update_mem_union : forall k (m m':Mem.t k) X Y,
  m{!Vset.union X Y <<- m'!} = m{!X <<- m'!}{!Y <<- m'!}.
 Proof.
  intros k m m' X Y; apply Mem.eq_leibniz; intros (t,x).
  case (VsetP.mem_dec x Y); intro HY.
  repeat rewrite update_mem_in; auto with set.
  case (VsetP.mem_dec x X); intro HX.
  rewrite update_mem_in; auto with set. 
  rewrite update_mem_notin; trivial.
  rewrite update_mem_in; auto. 
  repeat rewrite update_mem_notin; auto. 
  intro H; destruct (Vset.union_correct _ _ x H); auto.
 Qed.

 Lemma req_mem_update_mem : forall k X1 X2 (m1 m2 m1' m2':Mem.t k), 
  m1 =={X1} m1' ->  m2 =={X2} m2' -> 
  m1{!X2 <<-m2!} =={Vset.union X1 X2} m1'{!X2<<-m2'!}.
 Proof.
  unfold req_mem; intros.
  case_eq (Vset.mem x X2); intros.
  repeat rewrite update_mem_in; auto.
  assert (~Vset.mem x X2) by (intros Heq; rewrite Heq in H2; discriminate).
  repeat rewrite update_mem_notin; auto.
  rewrite VsetP.union_spec in H1. destruct H1; auto.
  elim H3; trivial.
 Qed.

 Lemma req_mem_update_same: forall k O (m m':Mem.t k), 
  m =={O} m' ->
  forall t t', t {!O <<- m!} =={O} t' {!O <<- m'!}.
 Proof.
  intros. set (O' := O); unfold O' at 1.
  rewrite <- (VsetP.union_empty O).
  unfold O'; apply req_mem_update_mem; trivial.
 Qed.

 Lemma req_mem_update_mem_l : forall k O (m:Mem.t k) t, m {!O <<- t!} =={O} t.
 Proof.
  unfold req_mem; intros; rewrite update_mem_in; auto.
 Qed.

 Lemma req_mem_update_eq : forall k (m1 m2:Mem.t k) O, 
  m1 =={O} m2 ->
  forall m O', (m1 {! O' <<- m!}) =={O} (m2 {! O' <<- m!}).
 Proof. 
  unfold req_mem; intros.
  destruct (VsetP.mem_dec x O').
  repeat rewrite update_mem_in; auto.
  repeat rewrite update_mem_notin; auto.
 Qed.

 Lemma req_mem_update_disjoint : forall k O1 O2 (t:Mem.t k), 
  Vset.disjoint O1 O2 ->
  forall (m:Mem.t k), t {!O2 <<- m!} =={O1} t.
 Proof.
  unfold req_mem; intros.
  rewrite update_mem_notin; auto.
  apply VsetP.disjoint_mem_not_mem with O1; trivial.
 Qed.
 
 Lemma update_update_mem : forall k (m:Mem.t k) x X v, 
  ~Vset.mem x X -> m {!x <-- v!} = m {!x <--v!} {!X <<- m!}.
 Proof.
  intros k m x X v H; apply Mem.eq_leibniz; intros (t, x0).
  destruct (VsetP.mem_dec x0 X).
  rewrite update_mem_in; auto.
  destruct x; simpl. rewrite Mem.get_upd_diff; trivial.
  eauto using VsetP.mem_diff.
  rewrite update_mem_notin; auto.
 Qed.

 Lemma upd_upd k (m : Mem.t k) t1 t2 (v1 : Var.var t1) (v2 : Var.var t2)
   (e1 : T.interp k t1) (e2 : T.interp k t2) :
   ~ Var.eqb v1 v2 ->
   ((m {!v1 <-- e1!}) {!v2 <-- e2!}) = ((m {!v2 <-- e2!}) {!v1 <-- e1!}).
Proof.
  intros.
  apply Mem.eq_leibniz.
  unfold Mem.eq; intros (t, v).
  apply VarP.neq_neqb_r in H.
  generalize (VarP.Edec.eqb_spec v1 v).
  destruct (VarP.Edec.eqb v1 v); intro.
  rewrite <- H0, Mem.get_upd_same, Mem.get_upd_diff, Mem.get_upd_same; auto.
  generalize (VarP.Edec.eqb_spec v2 v).
  destruct (VarP.Edec.eqb v2 v); intro.
  rewrite <- H1, Mem.get_upd_same, Mem.get_upd_diff, Mem.get_upd_same; auto.
  repeat rewrite Mem.get_upd_diff; auto.
 Qed.

 Definition req_memb k X (m1 m2:Mem.t k) :=
  Vset.forallb 
  (fun x => T.i_eqb k (Var.btype x) (m1 x) (m2 x)) X.
 
 Lemma req_memb_spec : forall k X (m1 m2:Mem.t k),
  if req_memb X m1 m2 then m1 =={X} m2 else ~m1 =={X} m2.
 Proof.
  unfold req_memb; intros.
  assert (forall x y, 
   x = y -> T.i_eqb k (Var.btype x) (m1 x) (m2  x) =  
   T.i_eqb k (Var.btype y) (m1 y) (m2 y)).
  intros; subst; trivial.
  case_eq (Vset.forallb (fun x : VarP.Edec.t => 
   T.i_eqb k (Var.btype x) (m1 x) (m2 x)) X); intros.
  red; intros.
  assert (W:= Vset.forallb_correct _ H X H0 x H1); simpl in W.
  assert (W':= T.i_eqb_spec  k t (m1 x) (m2 x)); rewrite W in W'; trivial.
  intro.
  rewrite (Vset.forallb_complete 
   (fun x : Vset.E.t => 
    T.i_eqb k (Var.btype x) (m1 x) (m2 x)) H X) in H0.
  discriminate.
  intros.
  assert (W:= T.i_eqb_spec k (Var.btype x) (m1 x) (m2 x)).
  destruct (T.i_eqb k (Var.btype x) (m1 x) (m2 x)); trivial.
  destruct x; elim W; apply H1; trivial.
 Qed.
 
 Definition reqmemU k X mm := if @req_memb k X (fst mm) (snd mm) then 1 else 0.
 
 Lemma cover_reqmem : forall k X, cover (prodP (@req_mem k X)) (@reqmemU k X).
 Proof.
  intros k X (m1,m2); split; unfold prodP; simpl; intros;
   unfold reqmemU; simpl;
   assert (W:=req_memb_spec X m1 m2); destruct (req_memb X m1 m2); trivial;
   absurd (m1 =={X} m2); trivial.
 Qed.

 Lemma req_mem_eq : forall k X (m m1 m2:Mem.t k), 
  m1 =={X} m2 -> m{!X<<- m1!} = m{!X<<-m2!}.
 Proof.
  intros; apply Mem.eq_leibniz; intros (t, x).
  destruct (VsetP.mem_dec x X).
  repeat rewrite update_mem_in; trivial.
  apply H; trivial.
  repeat rewrite update_mem_notin; trivial.
 Qed.

 Lemma req_mem_dec : forall X k (m1 m2:Mem.t k), sumbool (m1 =={X} m2) (~m1=={X} m2).
 Proof.
  intros; assert (W:= req_memb_spec X m1 m2);
   destruct (req_memb X m1 m2); auto.
 Qed.   

 Hint Resolve req_mem_refl req_mem_sym req_mem_trans req_mem_weaken.
 
 
 (** Memory equality excepting a set of variables *) 

 Definition eeq_mem X k (m1 m2:Mem.t k) :=
  forall t (x:Var.var t), ~Vset.mem x X -> m1 x = m2 x.
 
 Lemma eeq_mem_trans : forall X k (m1 m2 m3 : Mem.t k),
  eeq_mem X m1 m2 -> eeq_mem X m2 m3 -> eeq_mem X m1 m3.
 Proof.
  unfold eeq_mem; intros.
  transitivity (m2 x); auto.
 Qed.

 Lemma eeq_mem_refl : forall X k (m:Mem.t k), eeq_mem X m m.
 Proof. red; trivial. Qed.
 
 Definition eeq_mem_dec X k (m1 m2:Mem.t k) :=
   if Mem.eqb m1 (m2 {!X<<-m1!}) then 1 else 0.

 Lemma ceeq_mem : forall X k (m:Mem.t k), cover (eeq_mem X m) (eeq_mem_dec X m).
 Proof.
  intros; red; intros; unfold eeq_mem_dec.
  generalize (Mem.eqb_spec m (x {!X <<- m!})); destruct (Mem.eqb m (x {!X <<- m!})); split; intros;
  trivial.
  elim H0; red; intros.
  rewrite H; rewrite update_mem_notin; trivial.
  elim H; apply Mem.eq_leibniz; red; intros (t,x0).
  destruct (VsetP.mem_dec x0 X).
  rewrite update_mem_in; trivial.
  rewrite update_mem_notin; auto.
 Qed.

 Lemma eeq_mem_update_mem : forall X k (m1 m2 : Mem.t k),
   Mem.eq m1 (update_mem m2 X m1) <-> eeq_mem X m1 m2.
 Proof.
  intros; split; intros; unfold Mem.eq, eeq_mem in *; intros.
  rewrite H,  update_mem_notin; trivial.
  destruct x; destruct (VsetP.mem_dec v X).
  rewrite update_mem_in; trivial.
  rewrite update_mem_notin; auto.
 Qed.

 Lemma eeq_mem_dec' k X (m1 m2 : Mem.t k) :
   sumbool (eeq_mem X m1 m2) (~ (eeq_mem X m1 m2)).
 Proof.
  intros.
  generalize (Mem.eqb_spec m1 (update_mem m2 X m1)).
  destruct (Mem.eqb m1 (update_mem m2 X m1)); intros; [ left | right ].
  apply eeq_mem_update_mem; rewrite <- H; unfold Mem.eq; auto.
  contradict H.
  apply eeq_mem_update_mem in H.
  apply Mem.eq_leibniz; red; auto.
 Qed.

 (** Free variables of expressions *)

 Fixpoint fv_expr_rec (t:T.type) (res:Vset.t) (e:E.expr t) {struct e} : Vset.t :=
  match e with 
  | E.Ecte _ _ => res 
  | E.Evar t x => Vset.add x res 
  | E.Eop op args => dfold_left fv_expr_rec args res
  | E.Eexists t x e1 e2 => 
    Vset.union 
    (Vset.remove x (fv_expr_rec Vset.empty e1)) 
    (fv_expr_rec res e2)
  | E.Eforall t x e1 e2 => 
    Vset.union 
    (Vset.remove x (fv_expr_rec Vset.empty e1))
    (fv_expr_rec res e2)
  | E.Efind t x e1 e2 => 
    Vset.union 
    (Vset.remove x (fv_expr_rec Vset.empty e1))
    (fv_expr_rec res e2)
  end.

 Definition fv_expr t := @fv_expr_rec t Vset.empty.
 
 Definition fv_args lt (args:E.args lt) := dfold_left fv_expr_rec args Vset.empty.

 Lemma fv_expr_var : forall t (v:Var.var t), fv_expr v = Vset.singleton v.
 Proof. 
  trivial. 
 Qed.

 Lemma fv_expr_rec_subset_and : 
  (forall t (e:E.expr t) res, res [<=] fv_expr_rec res e) /\
  (forall lt (args:E.args lt) res, res [<=] dfold_left fv_expr_rec args res).
 Proof.
  apply E.expr_ind_and; simpl; intros; auto with set.
  apply VsetP.subset_trans with (fv_expr_rec res e2); auto with set.
  apply VsetP.subset_trans with (fv_expr_rec res e2); auto with set.
  apply VsetP.subset_trans with (fv_expr_rec res e2); auto with set.
  apply VsetP.subset_trans with (fv_expr_rec res e); auto with set.
 Qed.

 Lemma fv_expr_rec_subset : forall t (e:E.expr t) res, 
  res [<=] fv_expr_rec res e.
 Proof.
  destruct fv_expr_rec_subset_and; trivial.
 Qed.

 Definition depend_only (X:Vset.t) t (e:E.expr t) := 
  forall k (m1 m2:Mem.t k), m1 =={X} m2 -> E.eval_expr e m1 = E.eval_expr e m2.

 Hint Unfold depend_only.
 
 Lemma depend_only_fv_expr_rec_and : 
  (forall t (e:E.expr t) res k (m1 m2 : Mem.t k),
   m1 =={fv_expr_rec res e} m2 ->
   E.eval_expr e m1 = E.eval_expr e m2) /\
  (forall lt (args:E.args lt) res k (m1 m2 : Mem.t k),
   m1 =={dfold_left fv_expr_rec args res} m2 ->
   E.eval_args args m1 = E.eval_args args m2).
 Proof.
  apply E.expr_ind_and; simpl; intros; auto.
  apply H; auto with set.
  unfold E.eval_args in H.
  rewrite (H res k m1 m2 H0); trivial.
  (* Eexists *)
  rewrite (H0 res k m1 m2). 
  assert (m1 =={Vset.remove v (fv_expr_rec Vset.empty e1)} m2).
  apply req_mem_weaken with (2:= H1); auto with set.
  clear H1; generalize (E.eval_expr e2 m2).
  induction i; simpl; trivial.
  rewrite IHi, (H Vset.empty k (m1 {!v <-- a!}) (m2 {!v <-- a!})); trivial.
  intros tx x Hin.
  destruct (Var.eq_dec v x); subst.
  inversion e; simpl.
  repeat rewrite Mem.get_upd_same; trivial. 
  repeat rewrite Mem.get_upd_diff; trivial.
  apply H2; rewrite VsetP.remove_spec; auto.
  apply req_mem_weaken with (2:= H1); auto with set. 
  (* Eforall *)
  rewrite (H0 res k m1 m2). 
  assert (m1 =={Vset.remove v (fv_expr_rec Vset.empty e1)} m2).
  apply req_mem_weaken with (2:= H1); auto with set.
  clear H1; generalize (E.eval_expr e2 m2).
  induction i; simpl; trivial.
  rewrite IHi, (H Vset.empty k (m1 {!v <-- a!}) (m2 {!v <-- a!})); trivial.
  intros tx x Hin.
  destruct (Var.eq_dec v x); subst.
  inversion e; simpl.
  repeat rewrite Mem.get_upd_same; trivial.
  repeat rewrite Mem.get_upd_diff; trivial.
  apply H2; rewrite VsetP.remove_spec; auto.
  apply req_mem_weaken with (2:=H1); auto with set. 
  (* Efind *)
  rewrite (H0 res k m1 m2). 
  assert (m1 =={Vset.remove v (fv_expr_rec Vset.empty e1)} m2).
  apply req_mem_weaken with (2:= H1); auto with set.
  unfold find_default.
  replace (find (fun v0 : T.interp k t => E.eval_expr e1 (m1 {!v <-- v0!})) (E.eval_expr e2 m2))
  with (find (fun v0 : T.interp k t => E.eval_expr e1 (m2 {!v <-- v0!})) (E.eval_expr e2 m2));
  trivial.
  clear H1; generalize (E.eval_expr e2 m2).
  induction i; simpl; trivial.
  rewrite IHi, (H Vset.empty k (m1 {!v <-- a!}) (m2 {!v <-- a!})); trivial.
  intros tx x Hin.
  destruct (Var.eq_dec v x); subst.
  inversion e; simpl.
  repeat rewrite Mem.get_upd_same; trivial. 
  repeat rewrite Mem.get_upd_diff; trivial.
  apply H2; rewrite VsetP.remove_spec; auto.
  apply req_mem_weaken with (2:= H1); auto with set. 
  (* dcons *)
  rewrite (H res k m1 m2).
  rewrite (H0 _ k m1 m2 H1); trivial.
  apply req_mem_weaken with (2:= H1).
  destruct fv_expr_rec_subset_and; auto.
 Qed.

 Lemma depend_only_fv_expr_rec : forall t (e:E.expr t) res, 
  depend_only (fv_expr_rec res e) e.
 Proof.
  destruct depend_only_fv_expr_rec_and; trivial.
 Qed.
 
 Lemma depend_only_fv_expr : forall t (e:E.expr t), 
  depend_only (fv_expr e) e.
 Proof.
  unfold depend_only; intros.
  apply (depend_only_fv_expr_rec e Vset.empty); trivial.
 Qed.

 Lemma depend_only_fv_expr_subset : forall t (e:E.expr t) (X:Vset.t),
  fv_expr e [<=] X -> 
  forall k (m1 m2:Mem.t k), m1 =={X} m2 -> E.eval_expr e m1 = E.eval_expr e m2.
 Proof.
  intros; apply depend_only_fv_expr.
  eapply req_mem_weaken; eauto.
 Qed.

 Lemma depend_only_fv_args : forall lt (args:E.args lt) t (e:E.expr t), 
  DIn t e args -> depend_only (fv_args args) e.
 Proof.
  unfold depend_only,fv_args; intros.
  destruct depend_only_fv_expr_rec_and.
  generalize H (H2 _ args _ k m1 m2 H0).
  clear H H0 H1 H2; induction args; simpl.
  intros HF; elim HF.
  intros [ H | H] Heq.
  inversion H; subst.
  assert (W:= T.inj_pair2 H3); clear H2 H3; subst.
  inversion Heq.
  apply (T.inj_pair2 H1).
  apply IHargs; auto.
  inversion Heq.
  apply (T.l_inj_pair2 H2).
 Qed.

 Definition fv_expr_extend t (e:E.expr t) X := fv_expr_rec X e.

 Definition Eeq t (e1 e2 : E.expr t) := e1 = e2.

 Lemma Eeq_refl : forall t, reflexive _ (@Eeq t).
 Proof. 
  unfold reflexive, Eeq; trivial. 
 Qed.

 Lemma Eeq_sym : forall t, symmetric _ (@Eeq t).
 Proof. 
  unfold symmetric, Eeq; auto. 
 Qed.

 Lemma Eeq_trans : forall t, transitive _ (@Eeq t).
 Proof. 
  unfold transitive, Eeq; eauto using trans_eq. 
 Qed.

 Add Parametric Relation (t:T.type) : (E.expr t) (Eeq (t:=t))
  reflexivity proved by (@Eeq_refl t)
  symmetry proved by (@Eeq_sym t)
  transitivity proved by (@Eeq_trans t)
  as Eeq_rel.

 Add Parametric Morphism (t:T.type) : (@fv_expr_rec t) 
  with signature Vset.eq ==> Eeq (t:=t) ==> Vset.eq
  as fv_expr_rec_morph.
 Proof.
  intros.
  rewrite (H0:x0 = y0).
  generalize x y H; clear x y H H0 x0.
  apply E.expr_ind2 with
   (P:=fun t (e:E.expr t) => 
    forall x1 x2, x1[=]x2 -> fv_expr_rec x1 e[=]fv_expr_rec x2 e)
   (Pl:= fun lt args => 
    forall x1 x2, x1[=]x2 ->
    dfold_left fv_expr_rec args x1 [=] dfold_left fv_expr_rec args x2);
   simpl; intros; auto with set.
  rewrite H; auto with set.
  rewrite (H0 _ _ H1); auto with set.
  rewrite (H0 _ _ H1); auto with set.
  rewrite (H0 _ _ H1); auto with set.
 Qed.

 Lemma union_fv_expr_spec : forall t (e:E.expr t) X, 
  fv_expr_extend e X [=] Vset.union (fv_expr e) X.
 Proof.
  unfold fv_expr_extend, fv_expr.
  assert (forall t (e:E.expr t) X1 X2,
   Vset.union (fv_expr_rec X1 e) X2 [=] fv_expr_rec (Vset.union X1 X2) e). 
  intros t e; apply E.expr_ind2 with 
   (P := fun t (e:E.expr t) => forall X1 X2, 
    Vset.union (fv_expr_rec X1 e) X2 [=] fv_expr_rec (Vset.union X1 X2) e)
   (Pl:= fun lt (args:E.args lt) => forall X1 X2,
    Vset.union (dfold_left fv_expr_rec args X1) X2  [=]
         dfold_left fv_expr_rec args (Vset.union X1 X2) );
   simpl; intros; auto with set.
  symmetry; apply VsetP.add_union_comm.
  rewrite VsetP.union_assoc; rewrite H0; auto with set.
  rewrite VsetP.union_assoc; rewrite H0; auto with set.
  rewrite VsetP.union_assoc; rewrite H0; auto with set.
  rewrite H0; clear H0.
  generalize (Vset.union (fv_expr_rec X1 e0) X2) 
   (fv_expr_rec (Vset.union X1 X2) e0) (H X1 X2); clear H X1 X2 e0 t0 e t.
  induction le; simpl; intros; auto.
  apply IHle; rewrite H; auto with set.
  intros; rewrite H.
  apply fv_expr_rec_morph; unfold Eeq; auto with set.
 Qed.


 Lemma fv_args_fv_expr : 
    forall lt (args:E.args lt) x, Vset.mem x (fv_args args) -> 
      exists te, exists e:E.expr te,
       DIn te e args /\ Vset.mem x (fv_expr e).
 Proof.
  unfold fv_args.
  assert (forall (lt : list T.type) (args : E.args lt) (x : Vset.E.t) res,
     Vset.mem x (dfold_left fv_expr_rec args res) ->
     Vset.mem x res \/ 
     exists te : T.type,
       exists e : E.expr te, DIn te e args /\ Vset.mem x (fv_expr e)).
  induction args; simpl; intros; auto.
  destruct (IHargs _ _ H).
  change (is_true (Vset.mem x (fv_expr_extend p res))) in H0.
  rewrite union_fv_expr_spec,VsetP.union_spec in H0; destruct H0; auto.
  right; exists a; exists p; split; auto.
  destruct H0 as (te, (e, (H1, H2))); right.
  exists te; exists e; split; auto.
  intros lt args x H1; destruct (H _ _ _ _ H1); auto.
  elim (Vset.empty_spec H0).
 Qed.


 (** Free variables of a support used for random assignment *)

 Fixpoint fv_distr t (d:E.support t) :=
  match d with
  | E.Dnat e => fv_expr e 
  | E.DZ e1 e2 => Vset.union (fv_expr e1) (fv_expr e2)
  | E.Dprod t1 t2 s1 s2  => Vset.union (fv_distr s1) (fv_distr s2) 
  | _ => Vset.empty
  end.

 Definition depend_only_distr (X:Vset.t) t (d:E.support t) :=
  forall k (m1 m2:Mem.t k), 
   m1 =={X} m2 -> E.eval_support d m1 = E.eval_support d m2.

 Lemma depend_only_fv_distr : forall t (d:E.support t), 
  depend_only_distr (fv_distr d) d.
 Proof.
  unfold depend_only_distr; induction d; simpl; intros; trivial.
  rewrite (depend_only_fv_expr e H); trivial.
  red in H.
  f_equal.
  rewrite (depend_only_fv_expr e);[ auto | ].
  red; intros.
  apply H.
  auto with set.
  rewrite (depend_only_fv_expr e0);[ auto | ].
  red; intros.
  apply H.
  auto with set.
  rewrite (IHd1 _ _ m2), (IHd2 _ _ m2); trivial; 
    try (eapply req_mem_weaken;[ | apply H]; auto with set).
 Qed.

 Lemma support_eq_fv_empty k t (s : E.support t) (m1 m2 : Mem.t k) :
   fv_distr s [=] Vset.empty ->
   E.eval_support s m1 = E.eval_support s m2.
 Proof.
  induction s; simpl; intros; auto.
  apply f_equal; apply f_equal.
  refine (depend_only_fv_expr_subset e _ _); try rewrite H; auto with set.
  apply VsetP.empty_union in H.
  destruct H; f_equal.
  refine (depend_only_fv_expr_subset e _ _); try rewrite H; auto with set.
  refine (depend_only_fv_expr_subset e0 _ _); try rewrite H; auto with set.
  rewrite H0; auto with set.
  apply VsetP.empty_union in H.
  erewrite IHs1, IHs2; eauto; tauto.
 Qed.

 (** Lossless programs *)

 Definition lossless E c := 
  forall k (m:Mem.t k), mu ([[c]] E m) (fun _ => 1) == 1.
 
 Hint Unfold lossless.
 
 Lemma lossless_nil : forall E, lossless E nil.
 Proof. 
  intros E k m; rewrite deno_nil_elim; auto.
 Qed.
 
 Lemma lossless_app : forall E c1 c2, 
  lossless E c1 -> lossless E c2 -> lossless E (c1++c2).
 Proof.
  unfold lossless; intros E c1 c2 H H0 k m; rewrite deno_app_elim; simpl.
  eapply Oeq_trans; [ | apply (H k m)].
  apply (mu_stable_eq (([[c1]]) E m)).
  simpl; apply ford_eq_intro; exact (H0 k).
 Qed.
 
 Lemma lossless_cons : forall E i c, 
  lossless E [i] -> lossless E c -> lossless E (i::c).
 Proof.
  intros E i c H H0; exact (lossless_app H H0).
 Qed.

 Lemma lossless_assign : forall E t (x:Var.var t) e, lossless E [x <- e].
 Proof.
  intros E t x e k m; rewrite deno_assign_elim; trivial.
 Qed.

 Lemma lossless_random : forall E t (x:Var.var t) d, lossless E [x <$- d].
 Proof.
  intros E t x d k m; rewrite deno_random_elim.
  exact (sum_support_lossless d m).
 Qed.

 Lemma lossless_cond : forall E e c1 c2, 
  lossless E c1 -> lossless E c2 -> lossless E [If e then c1 else c2].
 Proof.
  intros E e c1 c2 H H0 k m; rewrite deno_cond_elim.
  destruct (E.eval_expr e m); auto.
 Qed.

 Lemma lossless_call : forall E t (x:Var.var t) p la,
  lossless E (proc_body E p) ->
  lossless E [x <c- p with la].
 Proof.
  intros E t x p la H k m; rewrite deno_call_elim; simpl; auto.
  apply (H k).
 Qed. 


 (** The [Modify] predicate *) 
 
 Definition Modify E X c := forall k (m:Mem.t k), range (eeq_mem X m) ([[c]] E m).

 Definition Modify_pre (P:forall k, Mem.t k->Prop) E X c :=
  forall k (m:Mem.t k), P k m ->  range (eeq_mem X m) ([[c]] E m).
 
 Lemma Modify_Modify_pre : forall P E X c,
  Modify E X c -> Modify_pre P E X c.
 Proof.
  unfold Modify, Modify_pre; auto.
 Qed.
 
 Lemma Modify_deno : forall E X c, 
  Modify E X c ->
  forall k (m:Mem.t k), 
   [[c]] E m == Mlet ([[c]] E m) (fun m' => Munit (m {!X <<- m' !})).
 Proof.
  unfold Modify; intros.
  apply eq_distr_intro; intros f; simpl.
  apply range_eq with (eeq_mem X m); trivial.
  intros; replace (m {!X<<-a!}) with a; trivial.
  apply Mem.eq_leibniz; intros (t, x).
  destruct (VsetP.mem_dec x X).
  symmetry; rewrite update_mem_in; auto.
  symmetry; rewrite update_mem_notin; trivial.
  apply H0; trivial.
 Qed.

 Lemma Modify_deno_elim : forall E X c, 
  Modify E X c ->
  forall k (m:Mem.t k) f, 
   mu ([[c]] E m) f == mu ([[c]] E m) (fun m' => f (m {!X <<- m' !})).
 Proof.
  intros; refine (eq_distr_elim (Modify_deno H m) f). 
 Qed.

 Lemma Modify_pre_deno : forall P E X c, 
  Modify_pre P E X c ->
  forall k (m:Mem.t k), 
   P k m -> [[c]] E m == Mlet ([[c]] E m) (fun m' => Munit (m {!X <<- m' !})).
 Proof.
  unfold Modify_pre; intros.
  apply eq_distr_intro; intros f; simpl.
  apply range_eq with (eeq_mem X m); auto.
  intros; replace (m {!X<<-a!}) with a; trivial.
  apply Mem.eq_leibniz; intros (t, x).
  destruct (VsetP.mem_dec x X).
  symmetry; rewrite update_mem_in; auto.
  symmetry; rewrite update_mem_notin; trivial.
  apply H1; trivial.
 Qed.

 Lemma Modify_pre_deno_elim : forall P E X c, 
  Modify_pre P E X c ->
  forall k m f, 
   P k m -> mu ([[c]] E m) f == mu ([[c]] E m) (fun m' => f (m {!X <<- m' !})).
 Proof.
  intros; refine (eq_distr_elim (Modify_pre_deno H m H0) f). 
 Qed.
 
 Lemma Modify_weaken : forall E X Y c, 
  Modify E X c -> 
  X [<=] Y -> 
  Modify E Y c.
 Proof.
  unfold Modify; intros; apply range_weaken with (eeq_mem X m); trivial.
  unfold eeq_mem; intros.
  apply H1; intro; apply H2.
  apply Vset.subset_correct with X; trivial.
 Qed. 

 Add Morphism Modify
  with signature @eq env ==> Vset.eq ==> @eq cmd ==> iff
  as Modify_morphism.
 Proof.
  split; intros; eauto using Modify_weaken with set.
 Qed.

 Lemma Modify_nil : forall E, Modify E Vset.empty nil.
 Proof.
  unfold Modify; intros.
  rewrite deno_nil.
  unfold eeq_mem; red; simpl; intros; auto.
 Qed.

 Lemma Modify_app :  forall E Xi Xc i c, 
  Modify E Xi i -> 
  Modify E Xc c ->
  Modify E (Vset.union Xi Xc) (i++c).
 Proof.
  intros; unfold Modify; intros.
  rewrite deno_app.
  apply range_Mlet with (eeq_mem Xi m); trivial.
  red; intros m' Hm f Hf; apply H0; intros; apply Hf.
  unfold eeq_mem in Hm,H1|-*; intros.
  rewrite VsetP.union_spec in H2.
  transitivity (m' x0). 
  apply Hm; tauto.
  apply H1; tauto.
 Qed.

 Lemma Modify_cons : forall E Xi Xc i c, 
  Modify E Xi [i] -> 
  Modify E Xc c ->
  Modify E (Vset.union Xi Xc) (i::c).
 Proof.
  intros E Xi Xc i.
  exact (@Modify_app E Xi Xc [i]).
 Qed.

 Lemma Modify_assign : forall E t (x:Var.var t) e, 
  Modify E (Vset.singleton x) [x <- e].
 Proof.
  unfold Modify,range,eeq_mem; intros.
  rewrite deno_assign_elim; apply H; intros.
  rewrite Mem.get_upd_diff; trivial.  
  apply VsetP.mem_singleton_diff; trivial.
 Qed.
 
 Lemma Modify_assign_same : forall E t (x:Var.var t), 
  Modify E Vset.empty [x <- x].
 Proof.
  unfold Modify,range,eeq_mem; intros.
  rewrite deno_assign_elim; apply H; intros.
  destruct (VarP.eq_dec x x0).
  inversion e; simpl.
  rewrite Mem.get_upd_same; trivial.
  rewrite Mem.get_upd_diff; trivial.
 Qed.

 Lemma Modify_random : forall E t (x:Var.var t), 
  forall d, Modify E (Vset.singleton x) [x <$- d].
 Proof.
  unfold Modify,range,eeq_mem; intros.
  rewrite deno_random_elim.
  transitivity 
   (mu (sum_support (T.default k t) (E.eval_support d m)) (fun _ => 0)).
  symmetry; apply mu_0.
  apply mu_stable_eq; simpl; apply ford_eq_intro; intro v.
  apply H; intros.
  rewrite Mem.get_upd_diff; trivial.  
  apply VsetP.mem_singleton_diff; trivial.
 Qed.

 Lemma Modify_cond : forall E e c1 c2 X1 X2,
  Modify E X1 c1->
  Modify E X2 c2 ->
  Modify E (Vset.union X1 X2) [If e then c1 else c2].
 Proof.
  intros; unfold Modify; intros.
  rewrite deno_cond; destruct (E.eval_expr e m);
   [apply Modify_weaken with X1 | apply Modify_weaken with X2]; auto with set.
 Qed.

 Lemma Modify_while : forall E e c X,
  Modify E X c ->
  Modify E X [while e do c].
 Proof.
  intros E e c X H k m.
  apply range_weaken with 
   (fun m' : Mem.t k =>  eeq_mem X m m' /\ E.eval_expr e m' = false).
  intuition.  
  apply while_ind0; intros.
  apply range_weaken with (eeq_mem X m0); auto.
  intros m' H2; apply eeq_mem_trans with m0; auto.
  intro; trivial.
 Qed.
 
 Lemma Modify_call : forall E t (x:Var.var t) f args X,
  Modify E X (proc_body E f) ->
  Modify E (Vset.add x (get_globals X)) [x <c- f with args].
 Proof.
  unfold Modify; intros; rewrite deno_call.
  unfold range in *; simpl; intros.
  apply (H k); intros.
  apply H0; unfold eeq_mem in H1 |- *; intros.
  rewrite VsetP.add_spec in H2.
  assert (Var.mkV x <> x1 /\ ~Vset.mem x1 (get_globals X)) by tauto.
  clear H2; destruct H3. 
  case_eq (Var.is_global x1); intros.
  rewrite return_mem_global; trivial.
  transitivity (init_mem E f args m x1).
  symmetry; apply init_mem_global; trivial.
  apply H1.
  intros Hin; apply H3.
  apply get_globals_complete; trivial.
  rewrite return_mem_local; trivial.
  unfold Var.is_local; rewrite H4; trivial.
 Qed.


(** ** Observationnal equivalence of expressions *)

 Definition EqObs_e t X (e1 e2:E.expr t) :=
  forall k (m1 m2:Mem.t k), m1 =={X} m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2.

 Lemma EqObs_e_sym : forall t X (e1 e2:E.expr t), 
  EqObs_e X e1 e2 -> EqObs_e X e2 e1.
 Proof.
  unfold EqObs_e; intros; symmetry; apply H; apply req_mem_sym; auto.
 Qed.
 
 Lemma EqObs_e_trans : forall t X (e1 e2 e3:E.expr t), 
  EqObs_e X e1 e2 -> EqObs_e X e2 e3 -> EqObs_e X e1 e3.
 Proof.
  unfold EqObs_e; intros.
  transitivity (E.eval_expr e2 m1); auto.
 Qed.

 Lemma EqObs_e_strengthen : forall I1 I2, 
  I1 [<=] I2 -> 
  forall t (e1 e2:E.expr t), EqObs_e I1 e1 e2 -> EqObs_e I2 e1 e2.
 Proof.
  unfold EqObs_e; intros; eauto using req_mem_weaken.
 Qed.

 Add Parametric Morphism t : (EqObs_e (t:=t))
  with signature Vset.eq ==> Eeq (t:=t) ==> Eeq (t:=t) ==> iff
  as EqObs_e_morphism.
 Proof.
  unfold Eeq; intros; subst.
  split; intros; eauto using EqObs_e_strengthen with set.
 Qed.
 
 Lemma EqObs_e_fv_expr : forall t (e:E.expr t), EqObs_e (fv_expr e) e e.
 Proof depend_only_fv_expr.

 Hint Resolve EqObs_e_fv_expr.
 
 Lemma EqObs_e_refl : forall t (e:E.expr t) X, 
  fv_expr e [<=] X -> EqObs_e X e e.
 Proof.
  intros e X H; eauto using EqObs_e_strengthen.
 Qed.
 
 Hint Resolve EqObs_e_refl.
 

 (** Observationnal equivalence of a support used for random assignment *)

 Definition EqObs_d t X (d1 d2:E.support t) := 
  forall k (m1 m2:Mem.t k), 
   m1 =={X} m2 -> E.eval_support d1 m1 = E.eval_support d2 m2.

 Lemma EqObs_d_strengthen : forall I1 I2,
  I1 [<=] I2 ->
  forall t (d d':E.support t), EqObs_d I1 d d' -> EqObs_d I2 d d'.
 Proof.
  unfold EqObs_d; intros; eauto using req_mem_weaken.
 Qed.
 
 Definition Deq t (d1 d2 : E.support t) := d1 = d2.

 Lemma Deq_refl : forall t, reflexive _ (@Deq t).
 Proof. 
  unfold reflexive, Deq; trivial. 
 Qed.

 Lemma Deq_sym : forall t, symmetric _ (@Deq t).
 Proof. 
  unfold symmetric, Deq; auto. 
 Qed.

 Lemma Deq_trans : forall t, transitive _ (@Deq t).
 Proof. 
  unfold transitive, Deq; eauto using trans_eq. 
 Qed.

 Add Parametric Relation t : (E.support t) (Deq (t:=t)) 
  reflexivity proved by (@Deq_refl t)
  symmetry proved by (@Deq_sym t)
  transitivity proved by (@Deq_trans t)
  as Deq_rel.

 Add Parametric Morphism t : (EqObs_d (t:=t))
  with signature Vset.eq ==> Deq (t:=t) ==> Deq (t:=t) ==> iff
  as EqObs_d_morphism.
 Proof.
  unfold Deq; intros; subst.
  split; intros; eauto using EqObs_d_strengthen with set.
 Qed.

 Lemma EqObs_d_fv_expr : forall t (d:E.support t), EqObs_d (fv_distr d) d d.
 Proof depend_only_fv_distr.

 Hint Resolve EqObs_d_fv_expr.

 Lemma EqObs_d_refl : forall t (d:E.support t) X, 
  fv_distr d [<=] X -> EqObs_d X d d.
 Proof.
  intros t e X H; eauto using EqObs_d_strengthen.
 Qed.
 
 Hint Resolve EqObs_d_refl.


 (** ** Observationnal equivalence of a list of expressions *)

 Definition EqObs_args ltv1 (lv1:var_decl ltv1) 
  lt1 (la1:E.args lt1) ltv2 (lv2:var_decl ltv2) lt2 (la2:E.args lt2) X I :=
  forall t (x:Var.var t), Vset.mem x X -> 
   match get_arg x lv1 la1, get_arg x lv2 la2 with
   | Some e1, Some e2 => EqObs_e I e1 e2
   | _, _ => False
   end.
 
 Lemma EqObs_args_strengthen : forall I I',
  I [<=] I' -> 
  forall lvt1 (lv1:var_decl lvt1) 
   lt1 (la1:E.args lt1) lvt2 (lv2:var_decl lvt2) lt2 (la2:E.args lt2) X,
   EqObs_args lv1 la1 lv2 la2 X I ->
   EqObs_args lv1 la1 lv2 la2 X I'.
 Proof.
  unfold EqObs_args; intros.
  apply H0 in H1; clear H0.
  destruct (get_arg x lv1 la1); auto; 
   destruct (get_arg x lv2 la2); eauto using EqObs_e_strengthen.
 Qed.
 
 Lemma EqObs_args_correct : forall E1 t1 (f1:Proc.proc t1) 
  E2 t2 (f2:Proc.proc t2) (la1:E.args (Proc.targs f1)) 
  (la2:E.args (Proc.targs f2)) X I k (m1 m2:Mem.t k),
  EqObs_args (proc_params E1 f1) la1 (proc_params E2 f2) la2 X I -> 
  m1 =={I} m2 ->
  init_mem E1 f1 la1 m1 =={Vset.union X (get_globals I)} init_mem E2 f2 la2 m2.
 Proof.
  intros; intros t x Hin.
  apply Vset.union_correct in Hin; destruct Hin.
  apply H in H1; generalize H1 (lookup_init_mem E1 f1 la1 m1 x) 
   (lookup_init_mem E2 f2 la2 m2 x); clear H H1.
  destruct (get_arg x (proc_params E1 f1) la1); try tauto.
  destruct (get_arg x (proc_params E2 f2) la2); intros; try tauto.
  rewrite H; rewrite H2; exact (H1 _ _ _ H0). 
  apply req_mem_weaken with (1:= get_globals_subset I) in H0.
  assert (H2 := get_globals_spec _ _ H1); repeat rewrite init_mem_global; auto.
 Qed.


(*** Probability *)


Definition Pr k (E:env) (c:cmd) (m:Mem.t k) (P:Mem.t k -o> boolO) :=
 mu ([[c]] E m) (charfun P).

Definition EP k (e:E.expr T.Bool) : Mem.t k -o> boolO := @E.eval_expr k _ e.

Implicit Arguments EP [].

Add Parametric Morphism k : (Pr (k:=k))
 with signature @eq env ==> @eq cmd ==> @eq (Mem.t k) ==> 
  Oeq (O:=Mem.t k -o> boolO) ==> Oeq (O:=U)
 as Pr_eq_compat.
Proof.
 unfold Pr; intros.
 apply mu_stable_eq.
 apply (charfun_eq_compat H).
Qed.

Add Parametric Morphism k : (Pr (k:=k))
 with signature @eq env ==> @eq cmd ==> @eq (Mem.t k) ==> 
  Ole (o:=Mem.t k -o> boolO) ++> Ole (o:=U) 
 as Pr_le_compat.
Proof.
  unfold Pr; intros.
  apply mu_le_compat; trivial.
  apply charfun_le_compat; trivial.
Qed.

Lemma Pr_split : forall k E c (m:Mem.t k) P Q,
 Pr E c m Q == Pr E c m (Q [&&] P) + Pr E c m (Q [&&] negP P).
Proof.
 unfold Pr; intros.
 rewrite (mu_restr_split ([[ c ]] E m) P (charfun Q)).
 apply Uplus_eq_compat; apply mu_stable_eq;
 rewrite restr_charfun, andP_comm, charfun_and; trivial.
Qed.

Lemma Pr_or : forall k E c (m:Mem.t k) P Q,
 Pr E c m (P [||] Q) <= Pr E c m P + Pr E c m Q.
Proof.
 unfold Pr; intros; apply distr_OR_charfun.
Qed.

Lemma Pr_or_disj : forall k E c (m:Mem.t k) P Q, disjoint P Q ->
 Pr E c m (P [||] Q) == Pr E c m P + Pr E c m Q.
Proof.
 unfold Pr; intros; apply distr_OR_charfun_disj; trivial.
Qed.

Lemma Pr_range : forall k E c (m:Mem.t k) (P Q:Mem.t k -o> boolO),
 range P ([[c]] E m) ->
 Pr E c m Q == Pr E c m (P [&&] Q).
Proof.
 unfold Pr; intros; apply mu_range_strenghten; trivial.
Qed.

Lemma Pr_neg : forall k E c (m:Mem.t k) (P:Mem.t k -o> boolO),
 lossless E c ->
 Pr E c m (negP P) == [1-] Pr E c m P.
Proof.
 unfold Pr; intros.
 rewrite mu_neg_charfun, (H k m); trivial.
Qed.

Lemma Pr_and : forall k E (m:Mem.t k) c P Q,
 Pr E c m P == 1 ->
 Pr E c m Q == 1 ->
 Pr E c m (P [&&] Q) == 1.
Proof.
 intros k E' m c P Q HP HQ.
 apply mu_range in HP.
 rewrite <- Pr_range; trivial.
Qed.

Lemma Pr_d_eq : forall E c k m (d:Var.var T.Bool) (e:E.expr T.Bool),
  Pr E c m (EP k e) == Pr E (c ++ [d <- e]) m (EP k d).
Proof.
  unfold Pr; intros; rewrite deno_app_elim.
  apply mu_stable_eq.
  refine (ford_eq_intro _); intro n. 
  rewrite deno_assign_elim.
  unfold charfun, restr, EP; simpl.
  rewrite Mem.get_upd_same; trivial. 
Qed.

Lemma Pr_sample_bool : forall k E c (m:Mem.t k) (b b':Var.var T.Bool),
  Var.mkV b <> b' ->
  lossless E c ->
  Pr E (c ++ [b <$-{0,1}]) m (EP k (b =?= b')) == [1/2].
Proof.
 intros; unfold Pr.
 rewrite deno_app_elim.
 transitivity (mu ([[c]] E m) (fcte _ [1/2])).
 apply mu_stable_eq.
 refine (@ford_eq_intro _ _ _ _ _); intro m'.
 unfold fcte; rewrite deno_random_elim; simpl.
 unfold charfun, EP, restr; simpl; unfold O.eval_op; simpl.
 repeat rewrite Mem.get_upd_same. 
 repeat (rewrite Mem.get_upd_diff;[ | trivial]).
 destruct (m' b'); rewrite Ti_eqb_refl.
 generalize (T.i_eqb_spec k T.Bool false true).
 destruct (T.i_eqb k T.Bool false true); intros Heq;
   [discriminate | repeat Usimpl; auto].
 generalize (T.i_eqb_spec k T.Bool true false).
 destruct (T.i_eqb k T.Bool true false); intros Heq;
  [discriminate | repeat Usimpl; auto].
 apply mu_cte_eq; unfold fone; auto.
Qed.

 (** Relations over memories *) 
 Section RELATIONS.

  Variables P1 P2 : mem_rel.
  
  Definition andR : mem_rel := fun k x y => P1 x y /\ P2 x y.
  Definition orR : mem_rel := fun k x y => P1 x y \/ P2 x y.
  Definition trueR : mem_rel := fun k x y => True.
  Definition falseR : mem_rel := fun k x y => False.
  Definition notR : mem_rel := fun k x y => ~P1 x y.
  Definition impR : mem_rel := fun k x y => P1 x y -> P2 x y.
  Definition transpR : mem_rel := fun k x y => P1 y x.

 End RELATIONS.

 Notation "P1 /-\ P2" := (@andR P1 P2) (at level 80, right associativity).
 Notation "P1 \-/ P2" := (@orR P1 P2) (at level 80, right associativity).
 Notation "P1 |-> P2" := (@impR P1 P2) (at level 85, right associativity).
 Notation "'~-' P" := (@notR P) (at level 75, right associativity). 

 (* Basic memory relations *)
 Definition EP1 (e:E.expr T.Bool) : mem_rel := 
  fun k m1 m2 => is_true (E.eval_expr e m1).

 Definition EP2 (e:E.expr T.Bool) : mem_rel := 
  fun k m1 m2 => is_true (E.eval_expr e m2).

 Implicit Arguments EP1 [].
 Implicit Arguments EP2 [].

 Definition eq_support t (d1:E.support t) (d2:E.support t) : mem_rel :=
  fun k (m1 m2:Mem.t k)  => E.eval_support d1 m1 = E.eval_support d2 m2.

 Definition permut_support t1 t2 
  (f:forall k, Mem.t k -> Mem.t k -> T.interp k t2 -> T.interp k t1) 
  (d1:E.support t1) (d2:E.support t2) : mem_rel :=
  fun k (m1 m2:Mem.t k) =>
   PermutP (fun  v1 v2 => v1 = f k m1 m2 v2) 
   (E.eval_support d1 m1) (E.eval_support d2 m2).


 (* Memory relation operators *)
 Definition upd1 (P:mem_rel) t (x:Var.var t) (e:E.expr t) : mem_rel :=
  fun k m1 m2 => P k (m1 {! x <-- E.eval_expr e m1 !}) m2.
 
 Definition upd2 (P:mem_rel) t (x:Var.var t) (e:E.expr t) : mem_rel :=
  fun k m1 m2 => P k m1 (m2{! x <-- E.eval_expr e m2 !}).
 
 Definition upd_para (P:mem_rel) t1 (x1:Var.var t1) (e1:E.expr t1)
  t2 (x2:Var.var t2) (e2:E.expr t2) :=
  fun k m1 m2 => 
   P k (m1 {! x1 <-- E.eval_expr e1 m1 !}) (m2 {! x2 <-- E.eval_expr e2 m2 !}).

 Definition forall_random (Q:mem_rel) t (x1 x2:Var.var t) d : mem_rel :=
  fun k m1 m2 => forall v, In v (E.eval_support d m1) -> 
   Q k (m1{!x1 <-- v!}) (m2{!x2 <-- v!}).

 Definition req_mem_rel X P : mem_rel := (kreq_mem X) /-\ P.

 Implicit Arguments req_mem_rel [].

 Definition eq_assoc_except t1 t2 (v:Var.var t1) 
  (l:Var.var (T.List (T.Pair t1 t2))) : mem_rel :=
  fun k m1 m2 =>
   forall r,  
    r <> m1 v ->
    O.interp_op k (O.Oin_dom _ _) r (m1 l) =
    O.interp_op k (O.Oin_dom _ _) r (m2 l) /\
    O.interp_op k (O.Oimg _ _) r (m1 l) =
    O.interp_op k (O.Oimg _ _) r (m2 l).

 (* Morphism on logical operators *)
 
 Add Morphism andR with signature implMR ++> implMR ++> implMR as andR_impl_morph.
 Proof.
  unfold implMR, andR; intuition.
 Qed.

 Add Morphism andR with signature iffMR ==> iffMR ==> iffMR as andR_iff_morph.
 Proof.
  intros x1 x2 Heq1 x3 x4 Heq2; unfold iffMR; split.
  apply andR_impl_morph; rewrite Heq1 || rewrite Heq2; trivial.
  apply andR_impl_morph; rewrite Heq1 || rewrite Heq2; trivial.
 Qed.

 Add Morphism orR with signature implMR ++> implMR ++> implMR as orR_impl_morph.
 Proof.
  unfold implMR, orR; intuition.
 Qed.

 Add Morphism orR with signature iffMR ==> iffMR ==> iffMR as orR_iff_morph.
 Proof.
  intros x1 x2 Heq1 x3 x4 Heq2; unfold iffMR; split.
  apply orR_impl_morph; rewrite Heq1 || rewrite Heq2; trivial.
  apply orR_impl_morph; rewrite Heq1 || rewrite Heq2; trivial.
 Qed.

 Add Morphism notR with signature implMR --> implMR as notR_impl_morph.
 Proof.
  unfold implMR, notR; intuition.
 Qed.

 Add Morphism notR with signature iffMR ==> iffMR as notR_iff_morph.
 Proof.
  intros x1 x2 Heq1; unfold iffMR; split.
  apply notR_impl_morph; unfold Basics.flip; rewrite Heq1; auto.
  apply notR_impl_morph; unfold Basics.flip; rewrite Heq1; auto.
 Qed.

 Add Morphism impR with signature implMR --> implMR ++> implMR as impR_impl_morph.
  unfold implMR, impR; intuition.
 Qed.

 Add Morphism impR with signature iffMR ==> iffMR ==> iffMR as impR_iff_morph.
 Proof.
  intros x1 x2 Heq1 x3 x4 Heq2; unfold iffMR; split.
  apply impR_impl_morph; unfold Basics.flip; rewrite Heq1 || rewrite Heq2; auto.
  apply impR_impl_morph; unfold Basics.flip; rewrite Heq1 || rewrite Heq2; auto.
 Qed.

 Add Morphism transpR with signature implMR ++> implMR as transpR_impl_morph.
 Proof.
  unfold implMR, transpR; intuition.
 Qed.

 Add Morphism transpR with signature iffMR ==> iffMR as transpR_iff_morph.
 Proof.
  intros x1 x2 Heq1; unfold iffMR; split.
  apply transpR_impl_morph; unfold Basics.flip; rewrite Heq1; trivial.
  apply transpR_impl_morph; unfold Basics.flip; rewrite Heq1; trivial.
 Qed.

 Add Morphism req_mem_rel 
  with signature Vset.subset ++> implMR --> Basics.flip implMR 
  as req_mem_rel_weaken.
 Proof.
  unfold Basics.flip, req_mem_rel; intros.
  rewrite <- H, H0; trivial.
 Qed.

(* TODO: Check why this behaves different than the above morphism (bug in Coq 8.2?) 
 Add Morphism req_mem_rel 
  with signature Vset.subset --> implMR ++> implMR 
  as req_mem_rel_impl_morph.
 Proof.
  unfold req_mem_rel; intros.
  rewrite <- H, H0; trivial.
 Qed.
*)

 Add Morphism req_mem_rel 
  with signature Vset.eq ==> iffMR ==> iffMR 
  as req_mem_rel_iff_morph.
 Proof.
  unfold req_mem_rel; intros.
  rewrite H, H0; auto.
 Qed.

 (* Simplification of logical operators *)

 Lemma proj1_MR : forall P1 P2, implMR (P1 /-\ P2) P1.
 Proof. 
  intros P1 P2 k m1 m2 (H1, H2); trivial.
 Qed.

 Lemma proj2_MR : forall P1 P2, implMR (P1 /-\ P2) P2.
 Proof. 
  intros P1 P2 k m1 m2 (H1, H2); trivial.
 Qed.

 Lemma andR_comm : forall P1 P2, iffMR (P1 /-\ P2) (P2 /-\ P1).
 Proof. 
  unfold iffMR, implMR,andR; intuition.
 Qed.

 Lemma andR_assoc : forall P1 P2 P3, iffMR ((P1 /-\ P2) /-\ P3) (P1 /-\ (P2 /-\P3)).
 Proof.
  unfold iffMR,implMR,andR; intuition. 
 Qed.

 Lemma andR_trueR_r : forall P, iffMR (P /-\ trueR) P.
 Proof.
  unfold iffMR,implMR, andR,trueR; intuition.
 Qed.

 Lemma andR_trueR_l : forall P, iffMR (trueR /-\ P) P.
 Proof.
  unfold iffMR,implMR, andR,trueR; intuition.
 Qed.

 Lemma andR_falseR_r : forall P, iffMR (P /-\ falseR) falseR.
 Proof.
  unfold iffMR,implMR, andR,falseR; intuition.
 Qed.

 Lemma andR_falseR_l : forall P, iffMR (falseR /-\ P) falseR.
 Proof.
  unfold iffMR,implMR, andR,falseR; intuition.
 Qed.

 Lemma req_mem_rel_assoc : forall X P1 P2, 
   iffMR ((req_mem_rel X P1) /-\ P2) (req_mem_rel X (P1 /-\ P2)).
 Proof.
  unfold req_mem_rel; intros; apply andR_assoc.
 Qed.

 Lemma req_mem_rel_trueR : forall X, iffMR (req_mem_rel X trueR) (kreq_mem X).
 Proof.
  unfold req_mem_rel; intros; apply andR_trueR_r.
 Qed.

 Lemma req_mem_rel_req_mem : forall X P, 
  implMR (req_mem_rel X P) (kreq_mem X).
 Proof.
  intros X P k m1 m2 [H1 _]; trivial.
 Qed.

 Lemma req_mem_rel_falseR : forall X, iffMR (req_mem_rel X falseR) falseR.
 Proof.
  unfold req_mem_rel; intros; apply andR_falseR_r.
 Qed.

 Lemma impR_trueR_l : forall P, iffMR (trueR |-> P) P.
 Proof.
  unfold iffMR,implMR, impR,trueR; intuition.
 Qed.

 Lemma impR_trueR_r : forall P, iffMR (P |-> trueR) trueR.
 Proof.
  unfold iffMR,implMR, impR,trueR; intuition. 
 Qed.

 Lemma impR_falseR_l : forall P, iffMR (falseR |-> P) trueR.
 Proof. 
  unfold iffMR,implMR, impR,falseR, trueR; intuition. 
 Qed.

 Lemma impR_falseR_r : forall P, iffMR (P |-> falseR) (~- P).
 Proof. 
  unfold iffMR,implMR, impR,falseR,notR; intuition. 
 Qed.

 Lemma transpR_transpR : forall P, iffMR (transpR (transpR P)) P.
 Proof.
  unfold iffMR,implMR, transpR; intuition. 
 Qed.

 Lemma transpR_Meq : iffMR (transpR Meq) Meq.
 Proof.
  unfold transpR, Meq, iffMR, implMR; intuition.
 Qed.

 Lemma transpR_kreq_mem : forall X, iffMR (transpR (kreq_mem X)) (kreq_mem X).
 Proof.
  unfold transpR, Meq, iffMR, implMR, kreq_mem; intuition;
   apply req_mem_sym; trivial.
 Qed.

 Lemma transpR_eeq_mem : forall X, iffMR (transpR (eeq_mem X)) (eeq_mem X).
 Proof.
  unfold transpR, Meq, iffMR, implMR, eeq_mem; intuition;
    rewrite H; trivial.
 Qed.

 Lemma transpR_EP1 : forall e, iffMR (transpR (EP1 e)) (EP2 e).
 Proof.
  unfold transpR, iffMR, implMR,EP1, EP2; intuition.
 Qed.
 
 Lemma transpR_EP2 : forall e, iffMR (transpR (EP2 e)) (EP1 e).
 Proof.
  unfold transpR, iffMR, implMR, EP1, EP2; intuition.
 Qed.

 Lemma transpR_and : forall P1 P2, 
  iffMR (transpR (P1 /-\ P2)) (transpR P1 /-\ transpR P2).
 Proof.
  unfold transpR, iffMR, implMR,andR; intuition.
 Qed.

 Lemma transpR_or : forall P1 P2, 
  iffMR (transpR (P1 \-/ P2)) (transpR P1 \-/ transpR P2).
 Proof.
   unfold transpR, iffMR, implMR,orR; intuition.
 Qed.

 Lemma transpR_imp : forall P1 P2, 
  iffMR (transpR (P1 |-> P2)) (transpR P1 |-> transpR P2).
 Proof.
   unfold transpR, iffMR, implMR,impR; intuition.
 Qed.

 Lemma transpR_not : forall P, 
  iffMR (transpR (~- P)) (~- transpR P).
 Proof.
  unfold transpR, iffMR, implMR,notR; intuition.
 Qed.

 Lemma transpR_req_mem_rel : forall X P,
  iffMR (transpR (req_mem_rel X P)) (req_mem_rel X (transpR P)).
 Proof.
  unfold req_mem_rel; intros.
  rewrite transpR_and, transpR_kreq_mem; trivial.
 Qed.

 Lemma EP1_bool : forall b:bool, iffMR (EP1 b) (if b then trueR else falseR).
 Proof.
  unfold EP1, iffMR, implMR,falseR, trueR; destruct b; simpl; split; intros; trivialb.
 Qed.

 Lemma EP2_bool : forall b:bool, iffMR (EP2 b) (if b then trueR else falseR).
 Proof.
  unfold EP2, iffMR, implMR,falseR, trueR; destruct b; simpl; split; intros; trivialb.
 Qed.

 Lemma notR_trueR : iffMR (~- trueR) falseR.
 Proof. 
  unfold notR, iffMR, implMR, trueR, falseR; tauto.
 Qed.

 Lemma notR_falseR : iffMR (~- falseR) trueR.
 Proof. 
  unfold notR, iffMR, implMR, trueR, falseR; tauto. 
 Qed.

 Hint Rewrite andR_assoc
  andR_trueR_r andR_trueR_l
  andR_falseR_r andR_falseR_l
  req_mem_rel_assoc
  req_mem_rel_trueR req_mem_rel_falseR
  impR_trueR_l impR_trueR_r
  impR_falseR_l impR_falseR_r 
  transpR_transpR transpR_Meq transpR_kreq_mem
  transpR_EP1 transpR_EP2
  transpR_and transpR_or transpR_imp transpR_not
  transpR_req_mem_rel
  transpR_eeq_mem
  EP1_bool EP2_bool notR_trueR notR_falseR: simplMR_base.

 Ltac simplMR := autorewrite with simplMR_base.
 
 (* Decidability of memory relations *)

 Definition decMR (P:mem_rel) := forall k x y, sumbool (P k x y) (~P k x y).

 Lemma decMR_EP1 : forall e, decMR (EP1 e).
 Proof.
  unfold decMR, EP1; intros.
  destruct (E.eval_expr e x); auto.
  right; intros; discriminate.
 Qed.

 Lemma decMR_EP2 : forall e, decMR (EP2 e).
 Proof.
  unfold decMR, EP2; intros.
  destruct (E.eval_expr e y); auto.
  right; intros; discriminate.
 Qed.

 Lemma decMR_Meq : decMR Meq.
 Proof. 
  unfold decMR, Meq; intros.
  generalize (Mem.eqb_spec x y); destruct (Mem.eqb x y); auto.
 Qed.

 Lemma decMR_kreq_mem : forall X, decMR (kreq_mem X).
 Proof.
  unfold decMR, kreq_mem; intros; apply req_mem_dec.
 Qed.

 Lemma decMR_eeq_mem : forall X, decMR (eeq_mem X).
 Proof.
  unfold decMR; intros; apply eeq_mem_dec'.
 Qed.

 Lemma decMR_and : forall P1 P2, decMR P1 -> decMR P2 -> decMR (P1 /-\ P2).
 Proof.
  unfold decMR, andR; intros.
  destruct (X _ x y).
  destruct (X0 _ x y).
  auto.
  right; tauto.
  right; tauto.
 Qed.

 Lemma decMR_req_mem_rel : forall X P, decMR P -> decMR (req_mem_rel X P).
 Proof.
  unfold req_mem_rel; intros; apply decMR_and; auto using decMR_kreq_mem.
 Qed.

 Lemma decMR_or : forall P1 P2, decMR P1 -> decMR P2 -> decMR (P1 \-/ P2).
 Proof.
  unfold decMR, orR; intros.
  destruct (X _ x y).
  auto.
  destruct (X0 _ x y).
  auto.
  right; tauto.
 Qed.

 Lemma decMR_imp : forall P1 P2, decMR P1 -> decMR P2 -> decMR (P1 |-> P2).
 Proof.
  unfold decMR, impR; intros.
  destruct (X0 _ x y).
  auto.
  destruct (X _ x y).
  right; tauto.
  left; tauto.
 Qed.

 Lemma decMR_not : forall P1, decMR P1 -> decMR ( ~-P1).
 Proof.
  unfold decMR, notR; intros.
  destruct (X _ x y); auto.
 Qed.

 Lemma decMR_transp : forall P1, decMR P1 -> decMR (transpR P1).
 Proof.
  unfold decMR, transpR; intros.
  destruct (X _ x y); auto.
 Qed.

 Lemma decMR_true : decMR trueR.
 Proof.
  unfold decMR, trueR; auto.
 Qed.

 Lemma decMR_false : decMR falseR.
 Proof.
  unfold decMR, falseR; auto.
 Qed.

 Lemma decMR_eq_assoc_except : 
  forall t1 t2 (v:Var.var t1) (l:Var.var (T.List (T.Pair t1 t2))),
   decMR (eq_assoc_except v l).
 Proof.
   unfold decMR; intros t1 t2 v l k m1 m2.
   set (f := fun (p:T.interp k (T.Pair t1 t2)) => 
        orb (T.i_eqb k _  (fst p) (m1 v))
         (andb (T.i_eqb k _ (O.interp_op k (O.Oin_dom _ _) (fst p) (m1 l))
                          (O.interp_op k (O.Oin_dom _ _) (fst p) (m2 l))) 
               (T.i_eqb k _ (O.interp_op k (O.Oimg _ _) (fst p) (m1 l))
                          (O.interp_op k (O.Oimg _ _) (fst p) (m2 l))))).
   case_eq (forallb f (m1 l)); intros.
   change (is_true (forallb f (m1 l))) in H;
   rewrite is_true_forallb in H.
   case_eq (forallb f (m2 l)); intros.
   change (is_true (forallb f (m2 l))) in H0;
   rewrite is_true_forallb in H0.
   left; red; intros.
   match goal with
   |- ?x = ?y /\ _ =>  pose (Y:= y); case_eq Y;
    [change (Y= true)with(is_true Y) | ]; unfold Y; clear Y; intros end.
   unfold O.interp_op in H2; simpl in H2; rewrite is_true_existsb in H2;
   destruct H2 as (x, (Hin, Heq)); rewrite is_true_Ti_eqb in Heq; subst.
   assert (W:= H0 _ Hin); unfold f in W.
   rewrite is_true_orb,is_true_andb in W; repeat rewrite is_true_Ti_eqb  in W.
   destruct W; trivial.
   elim H1; trivial.
   match goal with
   |- ?x = ?y /\ _ =>  pose (Y:= x); case_eq Y;
    [change (Y= true)with(is_true Y) | ]; unfold Y; clear Y; intros end.
   unfold O.interp_op in H3; simpl in H3; rewrite is_true_existsb in H3;
   destruct H3 as (x, (Hin, Heq)); rewrite is_true_Ti_eqb in Heq; subst.
   assert (W:= H _ Hin); unfold f in W.
   rewrite is_true_orb,is_true_andb in W; repeat rewrite is_true_Ti_eqb  in W.
   destruct W; trivial.
   elim H1; trivial.
   rewrite H2, H3; split; trivial.     
   rewrite <- not_is_true_false in H2, H3.
   unfold O.interp_op, O.assoc; simpl.
   match goal with
   |- match find ?F1 ?x1 with Some _ => _ | None => _ end = 
      match find ?F2 ?x2 with Some _ => _ | None => _ end => 
     generalize (find_In F1 x1) (find_In F2 x2);
     destruct (find F1 x1);[intros|destruct (find F2 x2); intros; trivial]
    end.
   destruct (H4 _ (refl_equal _)).
   elim H3; unfold O.interp_op; simpl; rewrite is_true_existsb; exists p; auto.
   destruct (H5 _ (refl_equal _)).
   elim H2; unfold O.interp_op; simpl; rewrite is_true_existsb; exists p; auto.

   rewrite <- not_is_true_false in H0; right; intro; apply H0.
   rewrite is_true_forallb; unfold f; intros.
   generalize (T.i_eqb_spec k t1 (fst x) (m1 v));
   destruct (T.i_eqb k t1 (fst x) (m1 v)); intros; simpl; trivial.
   rewrite is_true_andb; repeat rewrite is_true_Ti_eqb.
   exact (H1 _ H3).

   rewrite <- not_is_true_false in H; right; intro; apply H.
   rewrite is_true_forallb; unfold f; intros.
   generalize (T.i_eqb_spec k t1 (fst x) (m1 v));
   destruct (T.i_eqb k t1 (fst x) (m1 v)); intros; simpl; trivial.
   rewrite is_true_andb; repeat rewrite is_true_Ti_eqb.
   exact (H0 _ H2).
  Qed.
 
 Hint Resolve decMR_EP1 decMR_EP2 decMR_Meq decMR_kreq_mem decMR_req_mem_rel
  decMR_and decMR_or decMR_imp decMR_not decMR_transp decMR_true decMR_false
  decMR_eq_assoc_except decMR_eeq_mem.

 (** Dependence *)
 Definition depend_only_f k (f:Mem.t k -> U) (X:Vset.t) := 
  forall m1 m2:Mem.t k, m1 =={X} m2 -> f m1 == f m2.
 
 Definition depend_only_rel (P:mem_rel) (X1 X2:Vset.t) :=
  forall k (m1 m2 m1' m2':Mem.t k), 
   m1 =={X1} m1' -> m2 =={X2} m2' -> P k m1 m2 -> P k m1' m2'.

 Lemma depend_only_rel_weaken : forall P X1 X1' X2 X2',
  X1 [<=] X1' -> 
  X2 [<=] X2' ->
  depend_only_rel P X1 X2 ->
  depend_only_rel P X1' X2'.
 Proof.
  unfold depend_only_rel; intros.
  apply H1 with (3:=H4).
  rewrite H; trivial.
  rewrite H0; trivial.
 Qed.

 Lemma depend_only_kreq_mem : forall X, depend_only_rel (kreq_mem X) X X.
 Proof.
  unfold depend_only_rel, kreq_mem; intros.
  apply req_mem_trans with m1.
  apply req_mem_sym; trivial.
  apply req_mem_trans with m2; trivial.
 Qed.

 Lemma depend_only_andR : forall P X1 X2 Q Y1 Y2,
  depend_only_rel P X1 X2 ->
  depend_only_rel Q Y1 Y2 ->
  depend_only_rel (P /-\ Q) (Vset.union X1 Y1) (Vset.union X2 Y2).
 Proof.
  unfold depend_only_rel, andR; intros.
  destruct H3 as (H3, H4); split;[ apply H with (3:= H3) | apply H0 with (3:= H4)];
  eapply req_mem_weaken; eauto; auto with set.
 Qed.
  
 Lemma depend_only_req_mem_rel : forall X P X1 X2,
  depend_only_rel P X1 X2 ->
  depend_only_rel (req_mem_rel X P) (Vset.union X X1) (Vset.union X X2).
 Proof.
  unfold req_mem_rel; intros; apply depend_only_andR; auto using depend_only_kreq_mem.
 Qed.

 Lemma depend_only_orR : forall P X1 X2 Q Y1 Y2,
  depend_only_rel P X1 X2 ->
  depend_only_rel Q Y1 Y2 ->
  depend_only_rel (P \-/ Q) (Vset.union X1 Y1) (Vset.union X2 Y2).
 Proof.
  unfold depend_only_rel, orR; intros.
  destruct H3 as [H3 | H3];[left; apply H with (3:= H3) | right; apply H0 with (3:= H3)];
  eapply req_mem_weaken; eauto; auto with set.
 Qed.

 Lemma depend_only_impR : forall P X1 X2 Q Y1 Y2,
  depend_only_rel P X1 X2 ->
  depend_only_rel Q Y1 Y2 ->
  depend_only_rel (P |-> Q) (Vset.union X1 Y1) (Vset.union X2 Y2).
 Proof.
  unfold depend_only_rel, impR; intros.
  apply H0 with m1 m2.
  eapply req_mem_weaken; eauto; auto with set.
  eapply req_mem_weaken; eauto; auto with set.
  apply H3; apply H with (3:= H4); apply req_mem_sym;
  eapply req_mem_weaken; eauto; auto with set.
 Qed.

 Lemma depend_only_notR : forall P X1 X2,
  depend_only_rel P X1 X2 ->
   depend_only_rel (~-P) X1 X2.
 Proof.
  unfold depend_only_rel, notR; intros; intro.
  apply H2; apply H with (3:= H3); apply req_mem_sym;
  eapply req_mem_weaken; eauto; auto with set.
 Qed.

 Lemma depend_only_transpR : forall P X1 X2,
  depend_only_rel P X1 X2 ->
  depend_only_rel (transpR P) X2 X1.
 Proof.
  unfold depend_only_rel, transpR; intros.
  apply H with (3:= H2); trivial.
 Qed.

 Lemma depend_only_EP1 : forall (e:E.expr T.Bool), 
  depend_only_rel (EP1 e) (fv_expr e) Vset.empty.
 Proof.
  unfold depend_only_rel, EP1, is_true; intros.
  rewrite <- H1; symmetry.
  apply (@EqObs_e_fv_expr _ e k); trivial.
 Qed.

 Lemma depend_only_EP2 : forall (e:E.expr T.Bool), 
  depend_only_rel (EP2 e) Vset.empty (fv_expr e).
 Proof.
  unfold depend_only_rel, EP2, is_true; intros.
  rewrite <- H1; symmetry.
  apply (@EqObs_e_fv_expr _ e k); trivial.
 Qed.

 Lemma depend_only_trueR : depend_only_rel trueR Vset.empty Vset.empty.
 Proof.
  red; red; trivial.
 Qed.
 
 Lemma depend_only_falseR : depend_only_rel falseR Vset.empty Vset.empty.
 Proof.
  red; red; trivial.
 Qed.

 Lemma depend_only_eq_assoc_except : 
  forall t1 t2 (v:Var.var t1) (l:Var.var (T.List (T.Pair t1 t2))),
   depend_only_rel (eq_assoc_except v l) 
   (Vset.add v (Vset.singleton l)) (Vset.singleton l).
 Proof.
  red; red; intros.
  rewrite <- (H _ l); auto with set.
  rewrite <- (H0 _ l); auto with set.
  apply H1.
  rewrite (H _ v); auto with set.
 Qed.

 Hint Resolve depend_only_kreq_mem depend_only_andR 
  depend_only_req_mem_rel depend_only_orR depend_only_impR
  depend_only_notR depend_only_transpR depend_only_EP1 depend_only_EP2
  depend_only_trueR depend_only_falseR depend_only_eq_assoc_except.
 
 Ltac build_depend_only_rel_tac H P :=
  match type of H with
  | depend_only_rel ?PP1 _ _ =>
    let rec aux P :=
      match P with
      | trueR => constr:(@depend_only_trueR)
      | falseR => constr:(@depend_only_falseR)
      | EP1 ?e => constr:(@depend_only_EP1 e)
      | EP2 ?e => constr:(@depend_only_EP2 e)
      | kreq_mem ?X => constr:(@depend_only_kreq_mem X)
      | req_mem_rel ?X ?P1 =>
        let H := aux P1 in constr:(@depend_only_req_mem_rel X P1 _ _ H)
      | ?P1 /-\ ?P2 => 
        let H1 := aux P1 in
        let H2 := aux P2 in
        constr:(@depend_only_andR P1 _ _ P2 _ _ H1 H2)
      | ?P1 \-/ ?P2 => 
        let H1 := aux P1 in
        let H2 := aux P2 in
        constr:(@depend_only_orR P1 _ _ P2 _ _ H1 H2)
      | ?P1 |-> ?P2 => 
        let H1 := aux P1 in
        let H2 := aux P2 in
        constr:(@depend_only_impR P1 _ _ P2 _ _ H1 H2)
      | ~- ?P1 => let H := aux P1 in constr:(depend_only_notR H)
      | eq_assoc_except ?v ?l => constr:(@depend_only_eq_assoc_except _ _ v l)
      | transpR ?P1 => let H := aux P1 in constr:(@depend_only_transpR P1 _ _ H)
      | PP1 => constr:(H)
      end 
     in aux P 
  end.

 
 (** Symmetric relations *) 
 Definition symMR (P:mem_rel) := iffMR (transpR P) P.

 Lemma symMR_Meq : symMR Meq.
 Proof.
  unfold symMR; simplMR; trivial.
 Qed.

 Lemma symMR_kreq_mem : forall X, symMR (kreq_mem X).
 Proof.
  unfold symMR; intros; simplMR; trivial.
 Qed.

 Lemma symMR_eeq_mem : forall X, symMR (eeq_mem X).
 Proof.
  unfold symMR; intros; simplMR; trivial.
 Qed.

 Lemma symMR_and : forall P1 P2, symMR P1 -> symMR P2 -> symMR (P1 /-\ P2).
 Proof.
  unfold symMR; intros; simplMR.
  rewrite H, H0; trivial.
 Qed.

 Lemma symMR_req_mem_rel : forall X P, symMR P -> symMR (req_mem_rel X P).
 Proof.
  unfold symMR; intros; simplMR.
  rewrite H; trivial.
 Qed.

 Lemma symMR_or : forall P1 P2, symMR P1 -> symMR P2 -> symMR (P1 \-/ P2).
 Proof.
  unfold symMR; intros; simplMR.
  rewrite H, H0; trivial.
 Qed.

 Lemma symMR_imp : forall P1 P2, symMR P1 -> symMR P2 -> symMR (P1 |-> P2).
 Proof.
  unfold symMR; intros; simplMR.
  rewrite H, H0; trivial.
 Qed.

 Lemma symMR_not : forall P1, symMR P1 -> symMR (~- P1).
 Proof.
  unfold symMR; intros; simplMR.
  rewrite H; trivial.
 Qed.

 Lemma symMR_EP1_EP2 : forall e, symMR (EP1 e /-\ EP2 e).
 Proof.
  unfold symMR; intros; simplMR.
  rewrite andR_comm; trivial.
 Qed.

 Lemma symMR_EP2_EP1 : forall e, symMR (EP1 e /-\ EP2 e).
 Proof.
  unfold symMR; intros; simplMR.
  rewrite andR_comm; trivial.
 Qed.

 Lemma symMR_not_EP1_EP2 : forall e, symMR (~-EP1 e /-\ ~-EP2 e).
 Proof.
  unfold symMR; intros; simplMR.
  rewrite andR_comm; trivial.
 Qed.

 Lemma symMR_not_EP2_EP1 : forall e, symMR (~-EP1 e /-\ ~-EP2 e).
 Proof.
  unfold symMR; intros; simplMR.
  rewrite andR_comm; trivial.
 Qed.

 Lemma symMR_transp : forall P1, symMR P1 -> symMR (transpR P1).
 Proof.
  unfold symMR; intros; simplMR.
  symmetry; trivial.
 Qed.

 Hint Resolve symMR_Meq symMR_kreq_mem symMR_and symMR_req_mem_rel symMR_or 
  symMR_imp symMR_not symMR_EP1_EP2 symMR_EP2_EP1 symMR_not_EP1_EP2 
  symMR_not_EP2_EP1 symMR_transp symMR_eeq_mem.

 (* Reflexive relation on its support *)
 Definition refl_supMR2 (P1 P2:mem_rel) := 
  forall k (m1 m2:Mem.t k), P1 k m1 m2 -> P2 k m1 m1.
 
 Definition refl_supMR (P:mem_rel) := refl_supMR2 P P.

 Lemma refl_supMR_true : refl_supMR trueR.
 Proof. 
  red; red; trivial. 
 Qed.

 Lemma refl_supMR_Meq : refl_supMR Meq.
 Proof.
  red; red; intros; trivial.
 Qed.

 Lemma refl_supMR_kreq_mem : forall X, refl_supMR (kreq_mem X).
 Proof.
  red; red; intros; trivial.
 Qed.

 Lemma refl_supMR_eeq_mem : forall X, refl_supMR (eeq_mem X).
 Proof.
  red; red; intros; trivial; apply eeq_mem_refl.
 Qed.

 Hint Resolve refl_supMR_Meq refl_supMR_kreq_mem refl_supMR_true refl_supMR_eeq_mem.

 Lemma refl_supMR_Meq_impl : forall P, implMR P Meq -> refl_supMR P.
 Proof.
  unfold implMR, refl_supMR, refl_supMR2, Meq; intros.
  rewrite <- (H _ _ _ H0) in H0; trivial.
 Qed.
 
 Lemma refl_supMR_req_mem_rel : forall P X X1 X2,
  depend_only_rel P X1 X2 ->
  X2 [<=] X ->
  refl_supMR (req_mem_rel X P).
 Proof.
  red; red; red; intros.
  destruct H1; split.  
  apply (refl_supMR_kreq_mem H1).  
  apply H with m1 m2; trivial.
  apply req_mem_sym; apply req_mem_weaken with X; trivial.
 Qed.

 Ltac implMR_Meq :=
  apply implMR_refl 
  || (rewrite proj1_MR; implMR_Meq)
  || (rewrite proj2_MR; implMR_Meq).

 Ltac refl_support_tac H := 
  match goal with 
  | |- refl_supMR trueR => exact refl_supMR_true
  | |- refl_supMR (kreq_mem ?X) => exact (refl_supMR_kreq_mem X)
  | |- refl_supMR (req_mem_rel ?X ?P) =>
    (
      let H1 := build_depend_only_rel_tac H P in
      match type of H1 with
      | depend_only_rel _ ?X1 ?X2 =>
        refine (@refl_supMR_req_mem_rel P X X1 X2 H1 _);
        vm_compute; reflexivity
      end
     || fail 1)
   | |-  refl_supMR ?P =>
     match P with
     | context X [Meq] =>
       apply refl_supMR_Meq_impl; try implMR_Meq
     | _ => fail 2
     end
   end.

 Tactic Notation "refl_support" "["constr(H)"]"  := refl_support_tac H.

 Tactic Notation "refl_support" := refl_support_tac depend_only_trueR.

 (* Transitivity *)
 Definition transMR (P:mem_rel) := forall k, transitive _ (P k).

 Lemma transMR_Meq : transMR Meq.
 Proof.
  unfold transMR, transitive; intros; eapply Meq_trans; eauto.
 Qed.

 Lemma transMR_kreq_mem : forall X, transMR (kreq_mem X).
 Proof.
  unfold transMR, transitive, kreq_mem; intros; eapply req_mem_trans; eauto.
 Qed.

 Lemma transMR_eeq_mem : forall X, transMR (eeq_mem X).
 Proof.
  unfold transMR, transitive; intros; eapply eeq_mem_trans; eauto.
 Qed.

 Hint Resolve transMR_Meq transMR_kreq_mem transMR_eeq_mem.

 Lemma transMR_Meq_impl : forall P, implMR P Meq -> transMR P.
 Proof.
  unfold implMR, transMR, Meq, transitive; intros.
  rewrite (H _ _ _ H0); trivial.
 Qed.
 
 Lemma transMR_req_mem_rel : forall P X X1 X2,
  depend_only_rel P X1 X2 ->
  X1 [<=] X -> 
  X2 [<=] X ->
  transMR (req_mem_rel X P).
 Proof.
  unfold req_mem_rel, andR, transMR, transitive, kreq_mem; intros.
  destruct H2; destruct H3; split.
  eapply req_mem_trans; eauto.
  apply H with (3:= H5);[rewrite H0 | rewrite H1]; auto.
 Qed.

 (* TODO: verify implicit arguments *)
 Ltac transMR_tac H := 
  match goal with 
  | |- transMR (kreq_mem ?X) => apply transMR_kreq_mem
  | |- transMR (req_mem_rel ?X ?P) =>
    (
      let H1 := build_depend_only_rel_tac H P in
      match type of H1 with
      | depend_only_rel _ ?X1 ?X2 =>
        refine (@transMR_req_mem_rel P X X1 X2 H1 _ _);
        [vm_compute; reflexivity
        |vm_compute; reflexivity]
      end
     || fail 1)
   | |-  transMR ?P =>
     match P with
     | context X [Meq] =>
       apply transMR_Meq_impl; try implMR_Meq
     | _ => fail 2
     end
   end.

 Tactic Notation "transMR" "["constr(H)"]" := transMR_tac H.

 Tactic Notation "transMR" := transMR_tac depend_only_trueR.

 (** Observational equivalence *)
 Definition equiv (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) :=
  forall k, 
   exists d: Mem.t k -> Mem.t k -> Distr (Mem.t k * Mem.t k),
    forall m1 m2, 
     P k m1 m2 -> 
     lift (Q k) (d m1 m2) ([[c1]] E1 m1) ([[c2]] E2 m2).

 Definition EqObs I E1 c1 E2 c2 O :=
  equiv (kreq_mem I) E1 c1 E2 c2 (kreq_mem O).

 Definition Vset_of_var_decl (lt:list T.type) (lv:var_decl lt) : Vset.t :=
  dfold_right (fun t (x:Var.var t) r => Vset.add x r) Vset.empty lv.

 Record info (pt:list T.type) (parms:var_decl pt) 
  (body:cmd) (t:T.type) (re:E.expr t) : Type := 
  mkInfo
  { 
   info_X : Vset.t ;
   info_lossless : forall E, lossless E body;
   info_modify   : forall E, Modify E info_X body; 
   info_modify_local : forall x, Vset.mem x info_X -> Var.is_local x;
   info_re_local : forall x, Vset.mem x (fv_expr re) -> Var.is_local x;
   info_eqobs : forall E E', 
    EqObs (Vset_of_var_decl parms) E body E' body (fv_expr re)
  }.

End Make.
