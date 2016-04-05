(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

Require Export PPT.
Require Export BuildTac.
Require Export Padding.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope nat_scope.

(* Max number of queries to oracles *)
(* TODO: replace with a single bound *)
Parameter q1_poly : polynomial.
Parameter q2_poly : polynomial.

(* Max number of attempts to invert a random [a \in A] *)
Parameter T_poly : polynomial.

Module SEM_PADDING (A:FINITE_TYPE) (R:FINITE_TYPE) (P:FINITE_TYPE)
 (PA:PADDING_ALGEBRA P R) (ENC:ENCODING A R).

 Inductive ut : Type :=
 | P_
 | R_
 | A_.

 Module Ut <: UTYPE.

  Definition t := ut. 

  Scheme Equality for ut.
  Definition eqb := ut_beq.

  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   intros x y; case x; case y; simpl; trivial; intro; try discriminate.
  Qed.

  Definition eq_dec (x y:t) : {x = y} + {True}.
  Proof.
   intros x y; case x; case y; try (solve [left; trivial]); right; trivial.
  Defined.
  
  Lemma eq_dec_r : forall x y i, eq_dec x y = right _ i -> x <> y.
  Proof.
   intros x y i H; destruct x; destruct y; try discriminate. 
  Qed.
  
  Definition interp k T : Type :=
   match T with
    | P_ => P.t k
    | R_ => R.t k
    | A_ => A.t k
   end.

  Definition size k (x:t) (_:interp k x) : nat := 
   match x with
    | P_ => S (size_nat (length (P.elems k))) 
    | R_ => S (size_nat (length (R.elems k))) 
    | A_ => S (size_nat (length (A.elems k)))
   end.

  Definition default k T : interp k T := 
   match T with
    | P_ => P.default k
    | R_ => R.default k
    | A_ => A.default k
   end.

  Definition default_poly (x:t) : polynomial := 
   match x with
    | P_ => pplus 1 P.elems_poly 
    | R_ => pplus 1 R.elems_poly
    | A_ => pplus 1 A.elems_poly
   end.

  Lemma size_positive: forall k (x:t) r, 0 < @size k x r.
  Proof.
   intros k x r; destruct x; unfold size; auto with arith.
  Qed.

  Lemma default_poly_spec: forall k t,
   @size k t (default k t) <= default_poly t k.
  Proof.
   intros k t0.
   unfold default, default_poly, size.
   destruct t0.
   rewrite pplus_spec, pcst_spec.
   apply (le_n_S _ _ (P.elems_size_nat k)).
   rewrite pplus_spec, pcst_spec.
   apply (le_n_S _ _ (R.elems_size_nat k)).
   rewrite pplus_spec, pcst_spec.
   apply (le_n_S _ _ (A.elems_size_nat k)).
  Qed.

  Definition i_eqb k t (x y:interp k t) :=
   match t return interp k t -> interp k t -> bool with
    | P_ => @P.eqb k
    | R_ => @R.eqb k
    | A_ => @A.eqb k
   end x y.
  
  Lemma i_eqb_spec : forall k t (x y:interp k t), 
   if i_eqb x y then x = y else x <> y.
  Proof.
   intros k T'; destruct T'; simpl; intros.
   refine (P.eqb_spec _ _).
   refine (R.eqb_spec _ _).
   refine (A.eqb_spec _ _).
  Qed.

 End Ut.

 Module T := MakeType Ut.
 
 Inductive uop (ut:Type) : Type :=
 | OAdef
 | OPdef
 | ORdef 
 | Opad
 | Ounpad
 | Opadinv
 | OT
 | Of
 | Ofinv
 | Ofinv_len
 | OqQ1
 | OqQ2.
 
 Module Entries.
  
  Module Uop <: UOP Ut T.
   
   Definition t := uop Ut.t.
   
   Definition eqb (x y:t) := 
    match x, y with
     | OAdef, OAdef
     | OPdef, OPdef
     | ORdef, ORdef
     | Opad, Opad
     | Ounpad, Ounpad
     | Opadinv, Opadinv
     | OT, OT
     | Of, Of 
     | Ofinv, Ofinv
     | Ofinv_len, Ofinv_len
     | OqQ1, OqQ1
     | OqQ2, OqQ2 => true
     | _,_ => false
    end.

   Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
   Proof.
    intros.
    case x; case y; simpl; try constructor; intro H; inversion H.
   Qed.

   Definition targs (op:t) : list T.type :=
    match op with
     | OAdef => nil
     | OPdef => nil
     | ORdef => nil
     | Ounpad => T.User P_ :: T.User R_ :: nil
     | Opadinv => T.User R_ :: T.User R_ :: nil
     | Opad => T.User P_ :: T.User R_ :: nil
     | OT => nil
     | Of => T.User A_ :: nil
     | Ofinv => T.User R_ :: nil
     | Ofinv_len => nil
     | OqQ1 => nil
     | OqQ2 => nil
    end.
   
   Definition tres (op:t) : T.type :=
    match op with
     | OAdef => T.User A_
     | OPdef => T.User P_
     | ORdef => T.User R_
     | Opad => T.User R_
     | Ounpad => T.User R_
     | Opadinv => T.User P_
     | OT => T.Nat
     | Of => T.User R_
     | Ofinv => T.List (T.User A_)
     | Ofinv_len => T.Nat
     | OqQ1 => T.Nat
     | OqQ2 => T.Nat
    end. 

   Definition interp_op (k:nat) (op:t) : T.type_op k (targs op) (tres op) :=
    match op as op0 return T.type_op k (targs op0) (tres op0) with
     | OAdef => T.default k (T.User A_)
     | OPdef => T.default k (T.User P_)
     | ORdef => T.default k (T.User R_)
     | Opad => @PA.pad k
     | Ounpad => @PA.unpad k
     | Opadinv => @PA.pad_inv k
     | OT  => T_poly k 
     | Of => @ENC.f_def k
     | Ofinv => @ENC.finv_def k
     | Ofinv_len => ENC.finv_len
     | OqQ1 => q1_poly k
     | OqQ2 => q2_poly k
    end.
   
   Definition cinterp_op (k:nat) (op:t) : T.ctype_op k (targs op) (tres op) :=
    match op as op0 return T.ctype_op k (targs op0) (tres op0) with
     | OAdef => (A.default k, 1)
     | OPdef => (P.default k, 1)
     | ORdef => (R.default k, 1)
     | Opad => fun p r => (PA.pad p r, PA.cost_pad p r)
     | Ounpad => fun p r => (PA.unpad p r, PA.cost_unpad p r)
     | Opadinv => fun r1 r2 => (PA.pad_inv r1 r2, PA.cost_padinv r1 r2) 
     | OT => (T_poly k, 1)
     | Of => fun x => (ENC.f_def x, ENC.cost_f x)
     | Ofinv => fun x => (ENC.finv_def x, ENC.cost_finv x)
     | Ofinv_len => (ENC.finv_len, 1)
     | OqQ1 => (q1_poly k, 1)
     | OqQ2 => (q2_poly k, 1)
    end.

   Implicit Arguments cinterp_op [k].
   
   Definition eval_op k
    (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) :=
    @T.app_op k (targs op) (tres op) (interp_op k op) args.

   Definition ceval_op k 
    (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) * nat :=
    @T.capp_op k (targs op) (tres op) (cinterp_op op) args.
   
   Lemma ceval_op_spec : forall k op args,
    @eval_op k op args = fst (@ceval_op k op args).
   Proof.
    intros k o args; destruct o; simpl in args;
     T.dlist_inversion args; subst; trivial.
   Qed.

  End Uop.


  Inductive usupport_ (Ttype:Type) (Tuser:ut -> Ttype) : Ttype -> Type :=
  | UA : usupport_ Tuser (Tuser A_)
  | UR : usupport_ Tuser (Tuser R_) 
  | UP : usupport_ Tuser (Tuser P_).

  Module Us <: USUPPORT Ut T.

   Definition usupport : T.type -> Type := usupport_ T.User.

   Definition eval k t (s:usupport t) : list (T.interp k t) :=
    match s in usupport_ _ t0 return list (T.interp k t0) with
     | UA => A.elems k
     | UR => R.elems k
     | UP => P.elems k
    end.

   Definition ceval k t (s:usupport t) : list (T.interp k t) * nat := 
    match s in usupport_ _ t0 return list (T.interp k t0) * nat with
     | UA => (A.elems k, 1)
     | UR => (R.elems k, 1)
     | UP => (P.elems k, 1)
    end.

   Lemma eval_usupport_nil : forall k t (s:usupport t), eval k s <> nil.
   Proof.
    intros; case s.
    apply A.elems_notnil.
    apply R.elems_notnil.
    apply P.elems_notnil.
   Qed.

   Lemma ceval_spec : forall k t (s:usupport t), eval k s = fst (ceval k s).
   Proof.
    intros k t s; case s; trivial.
   Qed.

   Definition eqb (t1 t2:T.type) (s1:usupport t1) (s2:usupport t2) : bool :=
    match s1, s2 with
     | UA, UA
     | UR, UR
     | UP, UP => true
     | _, _ => false
    end.

   Lemma eqb_spec_dep :  forall t1 (e1:usupport t1) t2 (e2:usupport t2),
    if eqb e1 e2 then eq_dep T.type usupport t1 e1 t2 e2
    else ~eq_dep T.type usupport t1 e1 t2 e2.
   Proof.
    intros.
    case e1; case e2; simpl; try constructor; intros; (try (intro H; inversion H)).
   Qed.

   Lemma eqb_spec : forall t (e1 e2:usupport t),
    if eqb e1 e2 then e1 = e2 else e1 <> e2.
   Proof.
    intros t e1 e2.
    generalize (eqb_spec_dep e1 e2).
    case (eqb e1 e2); intro H.
    apply T.eq_dep_eq; trivial.
    intro Heq; apply H; rewrite Heq; constructor.
   Qed.

  End Us.


  (** Semantics with optimizations *)
  Module SemO <: SEM_OPT.

   Module Sem := MakeSem.Make Ut T Uop Us.
   Export Sem.

   Definition simpl_op (op:Uop.t) : 
    E.args (Uop.targs op) -> E.expr (Uop.tres op) :=
    match op as op0 return E.args (Uop.targs op0) -> E.expr (Uop.tres op0) with
     | op => fun args => E.Eop (O.Ouser op) args
    end.

   Implicit Arguments simpl_op [].

   Lemma simpl_op_spec : forall k op args (m:Mem.t k),
    E.eval_expr (simpl_op op args) m = E.eval_expr (E.Eop (O.Ouser op) args) m.
   Proof.
    trivial.
   Qed.

  End SemO.

  Module BP := BaseProp.Make SemO.Sem.


  Module Uppt.

   Import BP.

   Implicit Arguments T.size [k t].

   (** PPT expression *)
   Definition PPT_expr (t:T.type) (e:E.expr t) 
    (F:polynomial -> polynomial) 
    (G:polynomial -> polynomial) : Prop :=
    forall k (m:Mem.t k) p,
     (forall t (x:Var.var t), 
      BP.Vset.mem x (BP.fv_expr e) -> T.size (m x) <= peval p k)  ->
     let (v,n) := E.ceval_expr e m in
      T.size v <= peval (F p) k /\
      n <= peval (G p) k.

   (** PPT support *)
   Definition PPT_support t (s:E.support t)
    (F:polynomial -> polynomial) 
    (G:polynomial -> polynomial) : Prop :=
    forall k (m:Mem.t k) p,
     (forall t (x:Var.var t), 
      BP.Vset.mem x (BP.fv_distr s) -> T.size (m x) <= peval p k)  ->
     let (l,n) := E.ceval_support s m in
      (forall v, In v l -> T.size v <= peval (F p) k) /\
      n <= peval (G p) k.


   Definition utsize (x:UT.t) := 1.

   Definition utsize_default_poly (k:nat) : polynomial :=  
    pplus (pplus 1 A.elems_poly) 
          (pplus (pplus 1 P.elems_poly) (pplus 1 R.elems_poly)).

   Ltac unfold_p := 
    repeat (rewrite pplus_spec || rewrite pcst_spec ||
            rewrite pmult_spec || rewrite pvar_spec).

   Lemma utsize_default_poly_spec : forall r ut,
    utsize ut <= r -> 
    forall k, 
     UT.size (t:=ut) (UT.default k ut) <= peval (utsize_default_poly r) k.
   Proof.
    intros r ut_ ? k.
    case ut_; simpl; unfold utsize_default_poly.
    unfold_p.
    apply le_trans with (S (P.elems_poly k)).
    apply (le_n_S _ _ (P.elems_size_nat k)).
    omega.
    unfold_p.
    apply le_trans with (S (R.elems_poly k)).
    apply (le_n_S _ _ (R.elems_size_nat k)).
    omega.
    unfold_p.
    apply le_trans with (S (A.elems_poly k)).
    apply (le_n_S _ _ (A.elems_size_nat k)).
    omega.
   Qed.

   Definition uop_poly (o:Uop.t) : bool :=
    match o with
     | Opadinv  => false
     | Ounpad  => false
     | _ => true
    end.

   Ltac prove_Din :=
    match goal with
     | |- DIn _ ?a {?a} => left; apply eq_dep_refl
     | |- _ => (left; apply eq_dep_refl) || (right; prove_Din)
    end.

   Ltac destruct_Hla Hla x :=
    let F := fresh "F" in
    let G := fresh "G" in
    let H := fresh "H" in
     destruct (Hla _ x) as [F [G H] ]; [ prove_Din | ]. 

   Lemma sub_fv_expr_rec_1 : forall t (e:E.expr t) (s:Vset.t),
    fv_expr_rec Vset.empty e [<=] (fv_expr_rec s e).
   Proof.
    intros; fold (fv_expr_extend e s).
    rewrite union_fv_expr_spec.
    apply VsetP.subset_union_l.     
   Qed.

   Lemma sub_fv_expr_rec_2 : forall t t' (e:E.expr t) (e':E.expr t') (s:Vset.t),
    fv_expr_rec Vset.empty e[<=] s -> 
    fv_expr_rec Vset.empty e[<=] fv_expr_rec s e'.
   Proof.
    intros; fold (fv_expr_extend e' s).
    rewrite union_fv_expr_spec, H.
    apply VsetP.subset_union_r.
   Qed.

   Ltac prove_fv_expr_subset := unfold fv_expr; simpl; 
    match goal with
     | |- fv_expr_rec Vset.empty ?e[<=] (fv_expr_rec ?s ?e) =>
      apply sub_fv_expr_rec_1; prove_fv_expr_subset
     | |-  fv_expr_rec Vset.empty ?e[<=] (fv_expr_rec ?s ?e') =>
      apply sub_fv_expr_rec_2; prove_fv_expr_subset
    end.

   Ltac destruct_eval_expr k m p Hm :=
    match goal with 
     | [ H : PPT_expr ?x ?F ?G |- _] => 
      generalize (H k m p); clear H;
       case_eq (E.ceval_expr x m); simpl;
        let i := fresh "i" in
        let n := fresh "n" in
        let Heqi := fresh "Heqi" in
        let Hi := fresh "Hi" in
         intros i n Heqi Hi;
         destruct Hi;
         intros; try apply Hm; simpl;
         try apply Vset.subset_correct with (fv_expr x); trivial;
         unfold fv_expr; simpl; try prove_fv_expr_subset;
         try destruct_eval_expr k m p Hm
     | _ => idtac
    end.

   Lemma uop_poly_spec : forall o (la:dlist E.expr (O.targs (O.Ouser o))),
    uop_poly o ->
    (forall t (e:E.expr t), @DIn _ E.expr _ e _ la -> 
     exists F, exists G, PPT_expr e F G) ->
    exists F, exists G, PPT_expr (E.Eop (O.Ouser o) la) F G.
   Proof.
    intros o la H Hla.
    destruct o; T.dlist_inversion la; rewrite Heq in Hla |- *.

    (* OAdef *)
    exists (fun _ => pplus 1 A.elems_poly).
    exists (fun _ => 1).
    intros k m p Hm.
    simpl; split; unfold_p; trivial.
    apply le_n_S.
    apply A.elems_size_nat.

    (* OPdef *)
    exists (fun _ => pplus 1 P.elems_poly).
    exists (fun _ => 1).
    intros k m p Hm.
    simpl; split; unfold_p; trivial.
    apply le_n_S.
    apply P.elems_size_nat.

    (* ORdef *)
    exists (fun _ => pplus 1 R.elems_poly).
    exists (fun _ => 1).
    intros k m p Hm.
    simpl; split; unfold_p; trivial.
    apply le_n_S.
    apply R.elems_size_nat.

    (* Opad *)
    destruct_Hla Hla x.
    destruct_Hla Hla x0.
    exists (fun _ => pplus 1 R.elems_poly).
    eexists (fun p => pplus PA.cost_pad_poly (pplus (G0 p) (G1 p))).
    intros k m p Hm; simpl; split; unfold_p.
    apply le_n_S; apply R.elems_size_nat.
    repeat  apply plus_le_compat.
    apply PA.cost_pad_poly_spec.
    destruct_eval_expr k m p Hm. 
    destruct_eval_expr k m p Hm; omega.

    (* Ounpad *)
    discriminate.

    (* Opad_inv *)
    discriminate.

    (* T *)
    exists (fun _ => pplus 1 T_poly).
    exists (fun _ => 1). 
    simpl; split.
    rewrite pplus_spec, pcst_spec; case (peval T_poly k).
    trivial.
    intro n; apply le_trans with (S n); [apply size_nat_le | ]; auto with arith.
    rewrite pcst_spec; trivial.

    (* f *)
    destruct_Hla Hla x.
    exists (fun _ => pplus 1 R.elems_poly).
    exists (fun p => pplus ENC.cost_f_poly (G0 p)).
    intros k m p Hm.
    split; unfold_p; trivial.
    simpl; apply le_n_S; apply R.elems_size_nat.
    apply plus_le_compat; trivial; simpl.
    apply ENC.cost_f_poly_spec.
    destruct_eval_expr k m p Hm; omega.

    (* finv *)
    destruct_Hla Hla x.
    exists (fun _ => pplus 1 (pmult ENC.finv_len_poly (pplus 2 A.elems_poly))).
    exists (fun p => pplus ENC.cost_finv_poly (G0 p)).
    intros k m p Hm. 
    split; trivial; simpl; unfold_p.
    eapply le_trans.
    2:apply le_n_S.
    2:apply mult_le_compat.
    2:eapply le_trans.
    3:apply ENC.finv_len_poly_spec.
    2:apply (ENC.finv_len_spec (E.eval_expr x m)).
    2:apply le_refl.
    induction (ENC.finv_def (E.eval_expr x m)); simpl; auto.
    apply le_n_S.
    apply le_n_S.
    rewrite plus_n_Sm.
    apply plus_le_compat; trivial.
    apply A.elems_size_nat.   
    apply plus_le_compat.
    apply ENC.cost_finv_poly_spec.
    destruct_eval_expr k m p Hm; omega.

    (* size *)
    exists (fun _ => pplus 1 ENC.finv_len_poly).
    exists (fun _ => 1). 
    simpl; split; unfold_p; simpl.
    eapply le_trans; [apply size_nat_le | ]; auto with arith.
    apply ENC.finv_len_not_0.
    unfold_p; apply le_S; apply ENC.finv_len_poly_spec.
    unfold_p; trivial.
    
    (* q1 *)
    exists (fun _ => pplus 1 q1_poly).
    exists (fun _ => 1). 
    simpl; split.
    rewrite pplus_spec, pcst_spec; case (peval q1_poly k).
    trivial.
    intro n; apply le_trans with (S n); [apply size_nat_le | ]; auto with arith.
    rewrite pcst_spec; trivial.

    (* q2 *)
    exists (fun _ => pplus 1 q2_poly).
    exists (fun _ => 1). 
    simpl; split.
    rewrite pplus_spec, pcst_spec; case (peval q2_poly k).
    trivial.
    intro n; apply le_trans with (S n); [apply size_nat_le | ]; auto with arith.
    rewrite pcst_spec; trivial.
   Qed.

   Definition usupport_poly t (us:US.usupport t) : bool := true.

   Lemma usupport_poly_spec : forall t (us:US.usupport t),
    usupport_poly us ->
    exists F, exists G, PPT_support (E.Duser us) F G.
   Proof.
    intros t us; case us; intros.

    (* A *)
    exists (fun _ => pplus 1 A.elems_poly).
    exists (fun _ => 1).
    intros k m p Hm.
    simpl; split; unfold_p; trivial.
    intros.
    apply le_n_S.
    apply A.elems_size_nat.

    (* R *)
    exists (fun _ => pplus 1 R.elems_poly).
    exists (fun _ => 1).
    intros k m p Hm.
    simpl; split; unfold_p; trivial.
    intros.
    apply le_n_S.
    apply R.elems_size_nat.

    (* P *)
    exists (fun _ => pplus 1 P.elems_poly).
    exists (fun _ => 1).
    intros k m p Hm.
    simpl; split; unfold_p; trivial.
    intros.
    apply le_n_S.
    apply P.elems_size_nat.
   Qed.

  End Uppt.

 End Entries.

 Module Tactics := BuildTac.Make Entries.
 Export Tactics.

 (** * Notations *)
 Notation "'f_' x" := (E.Eop (O.Ouser (Of _)) { x }) (at level 42).
 Notation "'finv_' x" := (E.Eop (O.Ouser (Ofinv _)) { x }) (at level 42).

 Notation "'Adef'" := (E.Eop (O.Ouser (OAdef _)) (@dnil T.type E.expr)).
 Notation "'Pdef'" := (E.Eop (O.Ouser (OPdef _)) (@dnil T.type E.expr)).
 Notation "'Rdef'" := (E.Eop (O.Ouser (ORdef _)) (@dnil T.type E.expr)).

 Notation "'N'"   := (E.Eop (O.Ouser (Ofinv_len _)) (@dnil T.type E.expr)).
 Notation "'qQ1'" := (E.Eop (O.Ouser (OqQ1 _)) (@dnil T.type E.expr)).
 Notation "'qQ2'" := (E.Eop (O.Ouser (OqQ2 _)) (@dnil T.type E.expr)).
 
 (* Some countable infinite type (bitstrings in the literature) *)
 Notation Msg := T.Nat.
 Notation "'TMax'" := (E.Eop (O.Ouser (OT _)) (@dnil T.type E.expr)).

 (* Sampling *)
 Notation "x '<$-' 'P'"  := 
  (I.Instr (I.Random x (E.Duser (UP T.User)))) (at level 65) .
 Notation "x '<$-' 'A'"  := 
  (I.Instr (I.Random x (E.Duser (UA T.User)))) (at level 65).
 Notation "x '<$-' 'R'"  :=
  (I.Instr (I.Random x (E.Duser (UR T.User)))) (at level 65).

 (* Padding *)
 Notation "p '|+->|' r"   := (E.Eop (O.Ouser (Opad _)) {p,r}) (at level 42).
 Notation "p '|-->|' r"   := (E.Eop (O.Ouser (Ounpad _)) {p,r}) (at level 42).
 Notation "r1 '|-/-|' r2" := (E.Eop (O.Ouser (Opadinv _)) {r1,r2}) (at level 44).

End SEM_PADDING.
