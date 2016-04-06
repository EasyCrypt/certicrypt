(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * GenOpt.v : Generic abstract analysis signatures and algorithms *)

Require Import While_loop.
Require Import SetInterface.
Require Export EqThInv.

Set Implicit Arguments.
Set Asymmetric Patterns.

Module Type SEM_OPT.

 Declare Module Sem : SEM.
 Export Sem.

 Parameter simpl_op : forall op : Uop.t, 
  dlist E.expr (Uop.targs op) -> E.expr (Uop.tres op).

 Implicit Arguments simpl_op [].

 Parameter simpl_op_spec : forall k op args (m:Mem.t k),
  E.eval_expr (simpl_op op args) m = E.eval_expr (E.Eop (O.Ouser op) args) m.

End SEM_OPT.

 
Module Make (SemO:SEM_OPT).

 Export SemO.
 Module EqObsInvDec := EqThInv.Make Sem.
 Export EqObsInvDec.
 
 Module Type OPT_ENTRIES.
 
  (** A.t is the result type of the analysis *) 
  Declare Module A : EQDEC.

  (** The smallest element of A.t *)
  Parameter Abot : A.t. 
  
  (** A partial order over  A.t *)
  Parameter Ale : A.t -> A.t -> Prop.
  
  (** [valid a m] specifies the correctness of the result of the analysis *) 
  Parameter valid : forall k, A.t -> Mem.t k -> Prop.
  
  (** Validity is decidable *) 
  Parameter is_valid : forall k, A.t -> Mem.t k -> bool.
  
  (** Given an expression and a valid analysis [eval_e] optimize expression *)
  Parameter eval_e : forall t, E.expr t -> A.t -> E.expr t.
  Parameter eval_be : E.expr T.Bool -> A.t -> E.expr T.Bool.
  
  (** [add_assign x e a] enriches the analysis [a] with the fact that [x <- e] *)
  Parameter add_assign : forall t, Var.var t -> E.expr t -> A.t -> A.t.
  
  (** [add_test e b a] enrich the analysis [a] with the fact that [eval_bexp e = b] *)
  Parameter add_test : E.expr T.Bool -> bool -> A.t -> A.t.
  
  (* Parameter get_vars : A.t -> Vset.t. *)
  
  Parameter remove : forall t, Var.var t -> A.t -> A.t.
  
  Parameter remove_set : Vset.t -> A.t -> A.t.
  
  Parameter lub : A.t -> A.t -> A.t.
  
  (** Specification *)

  Parameter Ale_morph : forall x y : A.t,
   A.eq x y -> forall x0 y0 : A.t, A.eq x0 y0 -> (Ale x x0 <-> Ale y y0).
 
  Add Morphism Ale 
  with signature A.eq ==> A.eq ==> iff
  as Ale_morph_. 
   apply Ale_morph.
  Qed.  

  Parameter Ale_refl : forall a, Ale a a.
   
  Parameter Ale_trans : forall a1 a2 a3, Ale a1 a2 -> Ale a2 a3 -> Ale a1 a3.
  
  Parameter valid_morph : forall k (x y : A.t),
   A.eq x y ->
   forall x0 y0 : Mem.t k, Meq k x0 y0 -> (valid x x0 <-> valid y y0).
  
  Add Parametric Morphism k : (valid (k:=k))
   with signature A.eq ==> @Meq k ==> iff as valid_morph_.
   apply valid_morph.
  Qed.

  Parameter valid_le : forall k a1 a2 (m:Mem.t k),
   Ale a1 a2 -> valid a2 m -> valid a1 m.
   
  Parameter is_valid_spec : forall k a (m:Mem.t k), is_valid a m <-> valid a m.
  
  Parameter le_bot : forall a, Ale Abot a.
  
  Parameter valid_bot : forall k (m:Mem.t k), valid Abot m.
  
  Parameter le_lub_l : forall a1 a2, Ale (lub a1 a2) a1.
  Parameter le_lub_r : forall a1 a2, Ale (lub a1 a2) a2.
  
  Parameter valid_eval_e : forall k a (m:Mem.t k) t (e:E.expr t), 
   valid a m -> 
   E.eval_expr e m = E.eval_expr (eval_e e a) m.
  
  Parameter valid_eval_be : forall k a (m:Mem.t k) (e:E.expr T.Bool), 
   valid a m -> 
   E.eval_expr e m = E.eval_expr (eval_be e a) m.
  
  Parameter remove_update : forall k a t (x:Var.var t) (m:Mem.t k) v, 
   valid a m -> valid (remove x a) (Mem.upd m x v).
  
  Parameter remove_set_le : forall X a, Ale (remove_set X a) a. 
  
  Parameter valid_remove_set_update : forall k X a (m m':Mem.t k),
   valid (remove_set X a) m -> valid (remove_set X a) (m {!X <<- m'!}).
  
  Parameter valid_assign : forall k t (x:Var.var t) e a (m:Mem.t k),
   valid a m ->
   valid (add_assign x e (remove x a)) (Mem.upd m x (E.eval_expr e m)).
  
  Parameter add_test_morph : forall x y : E.expr T.Bool,
   Eeq x y ->
   forall (y0 : bool) (x0 y1 : A.t),
   A.eq x0 y1 -> A.eq (add_test x y0 x0) (add_test y y0 y1).

  Add Parametric Morphism : add_test
  with signature Eeq (t:=T.Bool) ==> @eq bool ==> A.eq ==> A.eq
  as add_test_morph_. 
   apply add_test_morph.
  Qed.

  Parameter valid_add_test : forall k a (m:Mem.t k) e b, valid a m -> 
   E.eval_expr e m = b -> valid (add_test e b a) m.
  
  Parameter le_add_test : forall a e b, Ale a (add_test e b a).
 
 End OPT_ENTRIES.


 Definition is_bool_expr t (e:E.expr t) :=
  match t with
  | T.Bool => true
  | _ => false
  end.

 Lemma is_bool_expr_correct : forall t (e:E.expr t), 
  is_bool_expr e -> 
  forall k (m:Mem.t k), exists b, 
   eq_dep T.type (T.interp k) t (E.eval_expr e m) T.Bool b.
 Proof.
  intros t; destruct t; simpl; intros; trivialb.
  exists (E.eval_expr e m); constructor.
 Qed.
 
 Module MakeOpt (OE:OPT_ENTRIES).

  Import OE.

  Definition valid_eq a k (m m':Mem.t k) := valid a m /\ m = m'.
  
  Lemma valid_eq_sym : forall k a, symmetric (Mem.t k) (@valid_eq a k).
  Proof.
   unfold valid_eq, symmetric.
   intros a k x y (H1,H2); split; auto.
   rewrite <- H2; auto.
  Qed.
  
  Lemma valid_eq_trans :  forall k a, transitive (Mem.t k) (@valid_eq a k).
  Proof.
   unfold valid_eq, transitive.
   intros a k x y z (H1,H2) (H3,H4); split; auto.
   rewrite H2; auto.
  Qed.
  
  Hint Resolve valid_eq_sym valid_eq_trans.
  
  Lemma le_valid_eq : forall a1 a2 k (m m':Mem.t k), 
   Ale a1 a2 -> valid_eq a2 m m' -> valid_eq a1 m m'.
  Proof.
   intros a1 a2 k m m' H (H1,H2); split; auto.
   apply valid_le with a2; auto.
  Qed.
  
  Fixpoint eval_d t (d:E.support t) a :=  
   match d in (E.support t0) return (E.support t0) with 
   | E.Dbool => E.Dbool
   | E.Dnat e  => E.Dnat (eval_e e a)
   | E.DZ e1 e2  => E.DZ (eval_e e1 a) (eval_e e2 a)
   | E.Duser t us => E.Duser us
   | E.Dprod t1 t2 s1 s2 => E.Dprod (eval_d s1 a) (eval_d s2 a)
   end.
  
  Definition opt_bi (bi:I.baseInstr) (a:A.t) : cmd * A.t :=
   match bi with
   | I.Assign t x e =>
     let r := eval_e e a in
     let rx := eval_e x a in
      if E.eqb r rx then (nil, a)
      else ([ x <- r ], add_assign x e (remove x a))
   | I.Random t x d =>
     let r := eval_d d a in
     let a' := remove x a in
      ([ x <$- r ], a')
   end.


  Section OPT_CODE.
   
   Variable opt_i: I.instr -> A.t -> cmd * A.t.
  
   Fixpoint opt_aux  (c:cmd) (a:A.t) {struct c} : cmd*A.t :=
    match c with
    | nil => (nil, a)
    | i::c => 
      let (i',ai) := opt_i i a in
      let (c', ac) := opt_aux c ai in
       (i'++c', ac)
    end.

  End OPT_CODE.


  Section OPT_I.
   
   Variable n : positive.
   Variable E : env.
   Variable pi : eq_refl_info E.
   
   Definition get_bool t (e:E.expr t) :=
    match e return option bool with
    | E.Ecte _ (E.Cbool b) => Some b
    | _ => None
    end.

   Definition is_false_bool t (e:E.expr t) :=
    match get_bool e with
    | Some b => negb b 
    | _ => false
    end.

   
   Fixpoint opt_i (i:I.instr) (a:A.t) {struct i} : cmd*A.t :=
    match i with
    | I.Instr bi => opt_bi bi a
    | I.Cond e c1 c2 =>
      let e' := eval_be e a in
       match get_bool e' with
       | Some b =>
         if b then opt_aux opt_i c1 a else opt_aux opt_i c2 a
       | _ => 
        let (c1',a1) := opt_aux opt_i c1 (add_test e true a) in
        let (c2',a2) := opt_aux opt_i c2 (add_test e false a) in
         ([ If e' then c1' else c2' ], lub a1 a2)
       end
    | I.While e c =>
      (* TODO: Remove the instruction if the precondition implies e = false *)
      let e' := eval_be e a in
      if is_false_bool e' then (nil, a)
      else
      
      let loop a :=
       let r := opt_aux opt_i c (add_test e true a) in
       let a' := snd r in
        if A.eqb a' a then Result A.t r else Continue _ (lub a' a)
      in match While_loop.while loop n a with
         | Continue _ =>   
           let a' :=
            match modify_i pi Vset.empty i with
            | Some X => remove_set X a
            | None => Abot
            end in
           let c' := fst (opt_aux opt_i c (add_test e true a')) in
            ([ while (eval_e e a') do c'], add_test e false a')
         | Result (c',a') => 
           ([ while (eval_be e a') do c'], add_test e false a')
         end  
    | I.Call t d f args =>
      let args' := dmap _ (fun t (e:E.expr t) => eval_e e a) args in
      let a' := 
       match modify_i pi Vset.empty i with
       | Some X => remove_set X a 
       | None => Abot
       end 
      in ([ d <c- f with args' ], a')
    end.

   (** Proof of the algorithm *)
   Lemma valid_eval_d :  forall (a:A.t) k (m:Mem.t k) t (d:E.support t),
    valid a m -> E.eval_support d m = E.eval_support (eval_d d a) m.
   Proof.
    induction d; simpl; intros; auto.
    rewrite <- valid_eval_e; trivial.
    rewrite <- valid_eval_e; trivial.
    rewrite <- valid_eval_e; trivial.
    rewrite IHd1, IHd2; trivial.
   Qed.
   
   Lemma get_bool_correct_aux : forall k (m:Mem.t k) t (e:E.expr t) b,
    get_bool e = Some b ->
    eq_dep _ (T.interp k) t (E.eval_expr e m) T.Bool b.
   Proof.
    destruct e; simpl; try (intros; discriminate).
    destruct c; simpl; intros b1 H; inversion H.
    constructor.
   Qed.

   Lemma get_bool_correct : forall k (m:Mem.t k) (e:E.expr T.Bool) b,
    get_bool e = Some b ->
    E.eval_expr e m = b.
   Proof.
    intros k m e b Heq; rewrite (T.eq_dep_eq (get_bool_correct_aux m e Heq)); trivial.
   Qed.

   Lemma is_true_bool_correct : forall k (m:Mem.t k) (e:E.expr T.Bool), is_false_bool e ->
    E.eval_expr e m = false.
   Proof.
    intros k m e;unfold is_false_bool.
    generalize (get_bool_correct m e).
    destruct (get_bool e);try (intros;discriminate).
    destruct b;auto; intros; discriminate.
   Qed.

   Lemma opt_correct_aux :
    (forall i a, let (i',a') := opt_i i a in
     equiv (valid_eq a) E [i] E i' (valid_eq a')) /\
    (forall c a, let (c',a') := opt_aux opt_i c a in
     equiv (valid_eq a) E c E c' (valid_eq a')).
   Proof.
    apply I.cmd_ind2; simpl; intros.
    
    (* baseInstr *)
    destruct i; simpl; intros.
   
    (* Assign *)
    case_eq (E.eqb (eval_e e a) (eval_e v a)); intros.
    eapply equiv_strengthen; [ | eapply equiv_assign_l].
    unfold valid_eq; simpl; intros k m m' (H1,H2).
    subst m'; assert (m {!v <-- E.eval_expr e m!} = m).
    assert (X:= E.eqb_spec (eval_e e a) (eval_e v a)); rewrite H in X.
    assert (W:= valid_eval_e e H1); assert (W':=valid_eval_e v H1).
    rewrite W; rewrite X; rewrite <- W'.   
    simpl; apply Mem.eq_leibniz; intros (tx,x). 
    destruct (Var.eq_dec v x).
    inversion e0; simpl.
    rewrite Mem.get_upd_same; trivial.
    apply Mem.get_upd_diff; trivial.
    red; rewrite H0; auto.
    eapply equiv_strengthen; [ | eapply equiv_assign].
    intros k m1 m2 (H1,H2); split.
    apply valid_assign; trivial.
    rewrite <- H2; rewrite <- valid_eval_e; auto.

    (* Random *)
    eapply equiv_strengthen; [ | eapply equiv_random].
    unfold valid_eq; simpl; intros k m m' (H1,H2).
    rewrite <- H2; split.
    red; apply valid_eval_d; trivial.
    split; trivial.
    apply remove_update; auto.

    (* Cond *)
    case_eq (get_bool (eval_be b a)); intros.
    (* know branch *)
    assert (W:=fun k (m:Mem.t k) => get_bool_correct m _ H1).
    destruct b0.
    assert (X:= H a).
    destruct (opt_aux opt_i c1 a).
    intros k; destruct (X k) as (d,Hd); exists d; intros.
    rewrite deno_cond.
    rewrite (@valid_eval_be k a m1 b).
    rewrite W; auto.
    destruct H2; trivial.
    assert (X:= H0 a).
    destruct (opt_aux opt_i c2 a).
    intros k; destruct (X k) as (d,Hd); exists d; intros.
    rewrite deno_cond.
    rewrite (@valid_eval_be k a m1 b).
    rewrite W; auto.
    destruct H2; trivial.

    (* unknown branch *)
    assert (X1:= H (add_test b true a)); assert (X2:= H0 (add_test b false a));
     destruct (opt_aux opt_i c1 (add_test b true a)) as (c1',a1);
      destruct (opt_aux opt_i c2 (add_test b false a)) as (c2',a2).
    apply equiv_cond.
    apply equiv_weaken with (valid_eq a1).
    intros; apply le_valid_eq with a1; auto.
    apply le_lub_l.
    apply equiv_strengthen with (2:= X1).
    unfold valid_eq, andP, andR; intuition.
    apply valid_add_test; auto.
    apply equiv_weaken with (valid_eq a2).
    intros; apply le_valid_eq with a2; auto.
    apply le_lub_r.
    apply equiv_strengthen with (2:= X2).
    unfold valid_eq, andR,notR, EP1, EP2; intuition.
    apply valid_add_test; auto.
    destruct (E.eval_expr b m1); intuition.
    elim H3; trivial.
    intros k m1 m2 (Hv,Heq); subst.
    rewrite (valid_eval_be b Hv); trivial.

    (* While *)
    case_eq (is_false_bool (eval_be b a)).
    (* known branch *)
      intros;apply equiv_trans_eq_mem_l with (valid_eq a) E nil.
      apply equiv_eq_sem_pre. 
      intros k m (Hv, Heq);rewrite deno_while, deno_cond.
      rewrite (valid_eval_be b Hv),is_true_bool_correct;trivial.
      apply equiv_nil.
      intros k m1 m2 (H1, H2);split;trivial.
    (* Else *)
    intros _.
    set (P1 := fun a0 => Ale a0 a).
    set (P2 := fun (r:iter_res A.t (cmd*A.t)) => 
     match r with
     | Result (c',a') =>
       Ale a' a /\ equiv (valid_eq (add_test b true a')) E c E c' (valid_eq a')
     | Continue a0 => P1 a0
     end).
    assert (P2 (While_loop.while 
     (fun a0 : A.t =>
      if A.eqb (snd (opt_aux opt_i c (add_test b true a0))) a0
       then Result A.t (opt_aux opt_i c (add_test b true a0))
       else
        Continue (cmd * A.t) (lub (snd (opt_aux opt_i c (add_test b true a0))) a0))
     n a)).
    apply while_P with P1; auto.
    intros a0 HP1.
    assert (V:= H (add_test b true a0)); clear H; destruct (opt_aux opt_i c (add_test b true a0)) as (c',a0'); simpl.
    case_eq (A.eqb a0' a0); unfold P2; intros.
    assert (XX := A.eqb_spec a0' a0); rewrite H in XX.
    split;[apply Ale_trans with a0;[rewrite XX; apply Ale_refl|exact HP1]| ].
    apply equiv_strengthen with (valid_eq (add_test b true a0)); auto.
    intros k m1 m2 (H3,H4); split; auto.
    rewrite <- XX; auto.
    unfold P1; apply Ale_trans with a0; auto.
    apply le_lub_r.
    unfold P1; apply Ale_refl. 
    destruct  (While_loop.while 
     (fun a0 : A.t =>
      if A.eqb (snd (opt_aux opt_i c (add_test b true a0))) a0
       then Result A.t (opt_aux opt_i c (add_test b true a0))
       else
        Continue (cmd * A.t) (lub (snd (opt_aux opt_i c (add_test b true a0))) a0))
     n a) as [(c',a') | _a_ ].
    destruct H0.
    apply equiv_strengthen with (valid_eq a').
    intros; apply le_valid_eq with a; auto.
    apply equiv_weaken with (valid_eq a' /-\ ~-EP1 b /-\ ~-EP2 (eval_be b a')).
    intros k m1 m2 ((W1,W4), (W2, W3)); split; auto using valid_add_test.
    apply valid_add_test; auto.
    unfold notR,EP1 in W2; destruct (E.eval_expr b m1); trivial.
    elim W2; trivial.
    apply equiv_while.
    intros k m1 m2 [H2 H3]; rewrite <- H3; rewrite <- valid_eval_be; auto.
    apply equiv_strengthen with (valid_eq (add_test b true a')); auto.
    intros k m1 m2 ((W1,W4), (W2, W3)); split; auto using valid_add_test.

    (* case : Continue (i.e. no fixpoint found) *)
    clear P1 P2 H0 _a_.
    fold (modify pi Vset.empty c).
    set (a' := match modify pi Vset.empty c with
               | Some X => remove_set X a
               | None => Abot
               end).
    assert (H1 := H (add_test b true a')); clear H.
    destruct (opt_aux opt_i c (add_test b true a')); simpl.
    apply equiv_strengthen with (valid_eq a').
    intros; apply le_valid_eq with a; auto.
    unfold a'.
    destruct ( modify pi Vset.empty c).
    apply remove_set_le. apply le_bot.
    apply equiv_weaken with (valid_eq a' /-\ ~-EP1 b /-\ ~-EP2 (eval_e b a')).
    intros k m1 m2 ((W1,W4), (W2, W3)); split; auto.
    apply valid_add_test; auto.
    unfold notR,EP1 in W2; destruct (E.eval_expr b m1); trivial.
    elim W2; trivial.
    apply equiv_while.
    intros k m m' (H3,H4).
    rewrite <- H4; rewrite <- valid_eval_e; auto.
    apply equiv_strengthen with (valid_eq (add_test b true a')).
    intros k m1 m2 ((W1,W4), (W2, W3)); split; auto using valid_add_test.

    assert (W:= modify_correct pi c Vset.empty).
    destruct (modify pi Vset.empty c).
    apply equiv_union_Modify_pre with t0 t0 (valid_eq t) (fun k => valid (k:=k) (add_test b true a'))
     (fun k => valid (k:=k) (add_test b true a'));
     try tauto; auto using Modify_Modify_pre; intros.
    destruct H; subst; auto.
    destruct H; destruct H0; subst; split; trivial.
    unfold a'; apply valid_remove_set_update.
    apply valid_le with (add_test b true a'); trivial.
    apply le_add_test; trivial.
    unfold Modify_pre, range; intros.
    rewrite <- (fun H => @equiv_deno _ _ _ _ _ _ H1 k f f H m m); auto.    
    rewrite (Modify_deno_elim (W _ (refl_equal _))).
    transitivity (mu ([[c]] E m) (fun _:Mem.t k => 0)).
    symmetry; apply mu_0.
    apply mu_stable_eq.
    simpl; apply ford_eq_intro; intros; apply H0; red; intros.
    rewrite update_mem_notin; trivial.
    intros m1 m2 (Hv, Heq); rewrite Heq; trivial.
    split; trivial.
    apply equiv_weaken with (valid_eq t); trivial.
    intros k m1 m2 (_, Heq); split; trivial.
    unfold a'; apply valid_bot.
 
    (* Call *)
    change (match pi_to_mod_info pi f with
       | Some GM => Some (Vset.add x (Vset.union GM Vset.empty))
       | None => None
       end) with (modify_i pi Vset.empty (x<c- f with a)).
    set (a':= match modify_i pi Vset.empty (x <c- f with a) with
              | Some X => remove_set X a0
              | None => Abot
     end).
    assert (forall k (m:Mem.t k), valid a0 m ->
     init_mem E f a m = init_mem E f (dmap _ (fun t0 (e : E.expr t0)=> eval_e e a0) a) m).
    intros; apply init_mem_eq. 
    clear a'; induction a; simpl; trivial. 
    rewrite IHa, (valid_eval_e p H); trivial.
    assert (forall k (m:Mem.t k) g, valid a0 m ->
     mu ([[ [x <c- f with a] ]] E m) g ==
     mu ([[ [x <c- f with dmap _ (fun t (e : E.expr t) => eval_e e a0) a] ]] E m) g).
    intros; repeat rewrite deno_call_elim; rewrite H; trivial.
    assert (equiv (valid_eq a0) E [x <c- f with a] E
     [x <c- f with dmap _ (fun t (e : E.expr t) => eval_e e a0) a] Meq).
    intros k; destruct (equiv_eq_mem E [x <c- f with a] k) as (d,Hd);
     exists d; intros m1 m2 (Hv,Heq); constructor.
    apply (Hd _ _ Heq).(l_fst).
    intros; rewrite <- H0; rewrite <- Heq; trivial.
    apply (Hd _ _ (refl_equal m1)).(l_snd).
    apply (Hd _ _ Heq).(l_range).
    clear H; assert (W':= modify_i_correct pi (x <c- f with a) Vset.empty).
    destruct (modify_i pi Vset.empty (x <c- f with a)).
    apply equiv_union_Modify_pre with t0 t0 Meq (fun k => valid (k:=k) a0) (fun k => valid (k:=k) a0); auto.
    intros k m1 m2 (Hv,Heq); rewrite <- Heq; auto.
    unfold Meq; intros k m1 m2 m1' m2' (H4,H2) H3; subst; split; trivial.
    unfold a'; apply valid_remove_set_update.
    apply valid_le with a0; auto using remove_set_le.
    apply Modify_Modify_pre; auto.
    unfold Modify_pre,range; intros.
    rewrite <- H0; auto.
    rewrite (Modify_deno_elim (W' _ (refl_equal _))).
    transitivity ( mu (([[ [x <c- f with a] ]]) E m) (fun _:Mem.t k => 0)).
    symmetry; apply mu_0.
    apply mu_stable_eq.
    simpl; apply ford_eq_intro; intros; apply H2; red; intros.
    rewrite update_mem_notin; trivial.
    eapply equiv_weaken; [ | apply H1].
    intros; unfold a'; split; trivial; apply valid_bot.

    (* Nil *)
    apply equiv_nil.
    
    (* Cons *)
    assert (V:=H a); clear H; destruct (opt_i i a) as (i',ai).
    assert (V':= H0 ai); clear H0; destruct (opt_aux opt_i c ai) as (c',a').
    change (i::c) with ([i]++c); apply equiv_app with (valid_eq ai); auto.
   Qed.

   Add Parametric Morphism k : (is_valid (k:=k))
   with signature A.eq ==> @Meq k ==> @eq bool
   as is_valid_morph_.
   Proof.
    unfold Meq; intros x y H m m0 H0; subst.
    assert (W :=is_valid_spec x m0).
    assert (W':=is_valid_spec y m0).
    destruct (is_valid x m0); destruct (is_valid y m0); auto.
    rewrite H in W; rewrite <- W' in W; destruct W; autob.
    rewrite H in W; rewrite <- W' in W; destruct W; autob.
   Qed.

   Lemma opt_correct : forall c a, 
    equiv (valid_eq a) E c E (fst (opt_aux opt_i c a)) 
          (valid_eq (snd (opt_aux opt_i c a))).
   Proof.
    destruct opt_correct_aux; intros.
    assert (H1 := H0 c a); destruct (opt_aux opt_i c a); trivial.
   Qed.
  
  End OPT_I.


  Definition optimize_pre n E (pi:eq_refl_info E) a c := 
   fst (opt_aux (opt_i n pi) c a).

  Lemma optimize_pre_l : forall n (I:mem_rel) E1 (pi:eq_refl_info E1) c1 c1' E2 c2
   (O:mem_rel) a,
   (forall k m1 m2, I k m1 m2 -> valid a m1) ->
   optimize_pre n pi a c1 = c1' ->
   equiv I E1 c1' E2 c2 O ->
   equiv I E1 c1 E2 c2 O.
  Proof.
   intros.
   apply equiv_trans_eq_mem_l with (fun k (m1 m2:Mem.t k) => valid a m1) E1 c1'; auto.
   apply equiv_strengthen with (valid_eq a).
   intros k m1 m2 (H2,H3); split; trivial.
   apply equiv_weaken with (valid_eq (snd (opt_aux (opt_i n pi) c1 a))).
   intros k m1 m2 (H2, H3); trivial.
   rewrite <- H0.
   exact (@opt_correct n E1 pi c1 a).
  Qed.

  Lemma optimize_pre_r : forall n (I:mem_rel) E1 c1 E2 (pi:eq_refl_info E2) c2 c2'
   (O:mem_rel) a,
   (forall k m1 m2, I k m1 m2 -> valid a m2) ->
   optimize_pre n pi a c2 = c2' ->
   equiv I E1 c1 E2 c2' O ->
   equiv I E1 c1 E2 c2 O.
  Proof.
   intros; apply equiv_trans_eq_mem_r with (fun k m1 m2 => valid a m1) E2 c2'; auto.
   apply equiv_strengthen with (valid_eq a).
   intros k m1 m2 (H2, H3); split; trivial.
   apply equiv_weaken with (valid_eq (snd (opt_aux (opt_i n pi) c2 a))).
   intros k m1 m2 (H2, H3); trivial.
   rewrite <- H0.
   exact (@opt_correct n E2 pi c2 a).
   unfold transpR; red; eauto.
  Qed.
  
  Lemma optimize_pre_para : forall n (I:mem_rel) 
   E1 (pi1:eq_refl_info E1) c1 c1'
   E2 (pi2:eq_refl_info E2) c2 c2' 
   (O:mem_rel) a,
   (forall k m1 m2, I k m1 m2 -> valid a m1 /\ valid a m2) ->
   optimize_pre n pi1 a c1 = c1' ->
   optimize_pre n pi2 a c2 = c2' ->
   equiv I E1 c1' E2 c2' O ->
   equiv I E1 c1 E2 c2 O.
  Proof.
   intros.
   apply optimize_pre_l with (2:= H0).
   intros k m1 m2 H3; destruct (H k m1 m2 H3); trivial.
   apply optimize_pre_r with (2:= H1); trivial.
   intros k m1 m2 H3; destruct (H k m1 m2 H3); trivial.
  Qed.

  Definition optimize n E (pi:eq_refl_info E) := optimize_pre n pi Abot.

  Lemma optimize_l : forall n (I:mem_rel) E1 (pi:eq_refl_info E1) c1 c1' E2 c2
   (O:mem_rel),
   optimize n pi c1 = c1' ->
   equiv I E1 c1' E2 c2 O ->
   equiv I E1 c1 E2 c2 O.
  Proof.
   unfold optimize; intros.
   apply optimize_pre_l with (2:= H); auto using valid_bot.
  Qed.

  Lemma optimize_r : forall n (I:mem_rel) E1 c1 E2 (pi:eq_refl_info E2) c2 c2'
   (O:mem_rel),
   optimize n pi c2 = c2' ->
   equiv I E1 c1 E2 c2' O ->
   equiv I E1 c1 E2 c2 O.
  Proof.
   unfold optimize; intros.
   apply optimize_pre_r with (2:= H); auto using valid_bot.
  Qed.

  Lemma optimize_para : forall n (I:mem_rel) E1 (pi1:eq_refl_info E1) c1 c1' E2 (pi2:eq_refl_info E2) c2 c2' 
   (O:mem_rel),
   optimize n pi1 c1 = c1' ->
   optimize n pi2 c2 = c2' ->
   equiv I E1 c1' E2 c2' O ->
   equiv I E1 c1 E2 c2 O.
  Proof.
   unfold optimize; intros.
   apply optimize_pre_para with (2:= H) (3:= H0); auto using valid_bot.
  Qed.
 
 End MakeOpt.
 

 Module ET.
  
  Record bexpr : Type := mkE {
   btype : T.type;
   b_expr :> E.expr btype
  }.

  Definition t := bexpr.

  Definition eqb (x y:t) := 
   let (tx, ex) := x in
   let (ty, ey) := y in
    if T.eqb tx ty then E.eqb ex ey else false.
  
  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   intros (tx, ex) (ty, ey); simpl.
   generalize (T.eqb_spec tx ty); destruct (T.eqb tx ty); intros; subst.
   generalize (E.eqb_spec ex ey); destruct (E.eqb ex ey); intros; subst; trivial.
   intros Heq; apply H; inversion Heq.
   apply (T.inj_pair2 H1).
   intros Heq; apply H; inversion Heq; trivial.
  Qed.
 
 End ET.

 Module EP := MkEqBool_Leibniz ET.
 
 Module Eset := MkListSet EP.

 Module EsetP := MkSet_Theory Eset.


 (** Simplification of expressions upto known test *)

 Fixpoint tapp_expr (lt:list T.type) (tr:Type) : Type:= 
  match lt with
  | nil => tr
  | cons t lt => E.expr t -> tapp_expr lt tr
  end.
 
 Fixpoint app_expr (lt:list T.type) (tr:Type) (args :E.args lt) : tapp_expr lt tr -> tr :=
  match args in (dlist _ lt0) return tapp_expr lt0 tr -> tr with
  | dnil => fun e => e
  | dcons t lt e l =>fun op => app_expr tr l (op e)
  end.

 Definition get_bool t (e:E.expr t) : option bool :=
  match e with
  | E.Ecte _ (E.Cbool b) => Some b 
  | _ => None
  end.

 Definition get_nat t (e:E.expr t) : option nat :=
  match e with
  | E.Ecte _ (E.Cnat n) => Some n
  | _ => None
  end.
 
 Definition is_nil_expr t (e:E.expr t) : bool :=
  match e with
  | E.Ecte _ (E.Cnil _) => true
  | _ => false
  end.

 Definition is_cons_expr_dep t (e:E.expr t) : 
  option (sigT (fun t => E.expr t * E.expr (T.List t)))%type :=
  match e with
  | E.Eop (O.Ocons t0) args =>
    Some 
    (existT 
     (fun t => E.expr t * E.expr (T.List t))%type t0 
     (app_expr (E.expr t0 * E.expr (T.List t0)) args (fun e1 l => (e1, l))))
  | _ => None
  end.

 Definition is_cons_expr t (e:E.expr (T.List t)) : option (E.expr t * E.expr (T.List t)) :=
  match is_cons_expr_dep e with
  | Some (existT t0 (e1, l)) =>
    match T.eq_dec t0 t with
    | left H => 
      match H in (_ = y0) return option (E.expr y0 * E.expr (T.List y0)) with
      | refl_equal => Some (e1, l)
      end
    | right _ => None
    end
  | _ => None
  end.

 Definition is_append_expr_dep t (e:E.expr t) : 
  option (sigT (fun t => E.expr (T.List t) * E.expr (T.List t)))%type :=
  match e with
  | E.Eop (O.Oappend t0) args =>
    Some 
    (existT 
     (fun t => E.expr (T.List t) * E.expr (T.List t))%type t0 
     (app_expr (E.expr (T.List t0) * E.expr (T.List t0)) args (fun e1 l => (e1, l))))
  | _ => None
  end.

 Definition is_append_expr t (e:E.expr (T.List t)) : option (E.expr (T.List t) * E.expr (T.List t)) :=
  match is_append_expr_dep e with
  | Some (existT t0 (e1, l)) =>
    match T.eq_dec t0 t with
    | left H => 
      match H in (_ = y0) return option (E.expr (T.List y0) * E.expr (T.List y0)) with
      | refl_equal => Some (e1, l)
      end
    | right _ => None
    end
  | _ => None
  end.
   
 Definition is_pair_expr_dep t (e:E.expr t) : 
  option (sigT (fun t1 => sigT (fun t2 => E.expr t1 * E.expr t2)))%type :=
  match e with
  | E.Eop (O.Opair t1 t2) args =>
    Some 
    (existT 
     (fun t1 => sigT (fun t2 => E.expr t1 * E.expr t2)%type) t1 
     (existT 
      (fun t2 => E.expr t1 * E.expr t2)%type t2 
      (app_expr _ args (fun e1 e2 => (e1, e2)))))
  | _ => None
  end.
 
 Definition is_pair_expr t1 t2 (e:E.expr (T.Pair t1 t2)) : option (E.expr t1 * E.expr t2) :=
  match is_pair_expr_dep e with
  | Some (existT t1' (existT t2' (e1, e2))) =>
    match T.eq_dec t1' t1 with
    | left H1 => 
      match H1 in (_ = y0) return option (E.expr y0 * E.expr t2) with
      | refl_equal =>
        match T.eq_dec t2' t2 with
        | left H2 =>
          match H2 in (_ = y0) return option (E.expr t1' * E.expr y0) with
          | refl_equal => Some (e1, e2)
          end
        | _ => None
        end
      end
    | _ => None
    end
  | _ => None
  end.

 Definition is_split_expr_dep t (e:E.expr t) : 
  option (sigT (fun t1 => sigT (fun t2 => E.expr t1 * E.expr (T.List (T.Pair t1 t2)))))%type :=
  match e with
  | E.Eop (O.Osplit t1 t2) args =>
    Some 
    (existT 
     (fun t1 => sigT (fun t2 => E.expr t1 * E.expr (T.List (T.Pair t1 t2)))%type) t1 
     (existT 
      (fun t2 => E.expr t1 * E.expr (T.List (T.Pair t1 t2)))%type t2 
      (app_expr _ args (fun e1 e2 => (e1, e2)))))
  | _ => None
  end.

 Definition is_split_expr t1 t2 (e:E.expr (T.List (T.Pair t1 t2))) : 
    option (E.expr t1 * E.expr (T.List (T.Pair t1 t2))) :=
  match is_split_expr_dep e with
  | Some (existT t1' (existT t2' (e1, e2))) =>
     match T.eq_dec t1' t1 with
     | left H1 => 
        match H1 in (_ = y0) return option (E.expr y0 * E.expr (T.List (T.Pair y0 t2))) with
        | refl_equal =>
          match T.eq_dec t2' t2 with
          | left H2 =>
             match H2 in (_ = y0) return option (E.expr t1' * E.expr (T.List (T.Pair t1' y0))) with
             | refl_equal => Some (e1, e2)
             end
          | _ => None
          end
        end
     | _ => None
     end
  | _ => None
  end.

 Definition is_fst_expr_dep t (e:E.expr t) : 
   option (sigT (fun t1 => sigT (fun t2 => E.expr (T.Pair t1 t2)))) :=
  match e with
  | E.Eop (O.Ofst t1 t2) args =>
    Some 
    (existT 
     (fun t1 => sigT (fun t2 => E.expr (T.Pair t1 t2))) t1 
     (existT 
      (fun t2 => E.expr (T.Pair t1 t2)) t2 
      (app_expr _ args (fun e1 => e1))))
  | _ => None
  end.

 Definition is_fst_split t1 t2 (r:E.expr t1) (e:E.expr t2) :=
  match is_fst_expr_dep e with
  | Some (existT t1' (existT t2' e1)) =>
    match is_split_expr_dep e1 with
    | Some (existT t1' (existT t2' (r', e2))) => E.eqb r r'
    | _ => false  
    end
  | _ => false
  end.

 Definition is_sum_expr_dep t (e:E.expr t) : 
  option (sigT (fun t1 => sigT (fun t2 => E.expr t1 + E.expr t2)))%type :=
  match e with
  | E.Eop (O.Oinl t1 t2) args =>
    Some 
    (existT 
     (fun t1 => sigT (fun t2 => E.expr t1 + E.expr t2)%type) t1 
     (existT 
      (fun t2 => E.expr t1 + E.expr t2)%type t2 
      (app_expr _ args (fun e1 => inl (E.expr t2) e1))))
  | E.Eop (O.Oinr t1 t2) args =>
    Some 
    (existT 
     (fun t1 => sigT (fun t2 => E.expr t1 + E.expr t2)%type) t1 
     (existT 
      (fun t2 => E.expr t1 + E.expr t2)%type t2 
      (app_expr _ args (fun e2 => inr (E.expr t1) e2))))
  | _ => None
  end.
 
 Definition is_sum_expr t1 t2 (e:E.expr (T.Sum t1 t2)) : option (E.expr t1 + E.expr t2) :=
  match is_sum_expr_dep e with
  | Some (existT t1' (existT t2' (inl e1))) =>
    match T.eq_dec t1' t1 with
    | left H1 => 
      match H1 in (_ = y0) return option (E.expr y0 + E.expr t2) with
      | refl_equal =>
        match T.eq_dec t2' t2 with
        | left H2 =>
          match H2 in (_ = y0) return option (E.expr t1' + E.expr y0) with
          | refl_equal => Some (inl (E.expr t2') e1)
          end
        | _ => None
        end
      end
    | _ => None
    end
  | Some (existT t1' (existT t2' (inr e2))) =>
    match T.eq_dec t1' t1 with
    | left H1 => 
      match H1 in (_ = y0) return option (E.expr y0 + E.expr t2) with
      | refl_equal =>
        match T.eq_dec t2' t2 with
        | left H2 =>
          match H2 in (_ = y0) return option (E.expr t1' + E.expr y0) with
          | refl_equal => Some (inr (E.expr t1') e2)
          end
        | _ => None
        end
      end
    | _ => None
    end
  | _ => None
  end.

 Definition build_eq t (e1 e2 : E.expr t) : E.expr T.Bool := 
  if E.eqb e1 e2 then E.Ecte true else e1 =?= e2.
 
 Definition build_or (e1 e2 : E.expr T.Bool) : E.expr T.Bool :=
  match get_bool e1, get_bool e2 with    
  | Some b1, Some b2 => E.Ecte (orb b1 b2)
  | Some b1, _ =>  if b1 then (E.Ecte true) else e2
  | _, Some b2 => if b2 then (E.Ecte true) else e1
  | _, _ => e1 || e2
  end.

 Definition build_and (e1 e2 : E.expr T.Bool) : E.expr T.Bool :=
  match get_bool e1, get_bool e2 with    
  | Some b1, Some b2 => E.Ecte (andb b1 b2)
  | Some b1, _ =>  if b1 then e2 else E.Ecte false
  | _, Some b2 => if b2 then e1 else E.Ecte false
  | _, _ => e1 && e2
  end.

 Definition build_imp (e1 e2 : E.expr T.Bool) : E.expr T.Bool :=
  match get_bool e1, get_bool e2 with    
  | Some b1, Some b2 => E.Ecte (impb b1 b2)
  | Some b1, _ =>  if b1 then e2 else E.Ecte true
  | _, Some b2 => if b2 then E.Ecte true else !e1
  | _, _ => e1 ==> e2
  end.
 
 Definition build_not (e:E.expr T.Bool) : E.expr T.Bool :=
  match get_bool e with
  | Some b => E.Ecte (negb b)
  | _ => !e
  end.
 
 Definition build_Oif t (e:E.expr T.Bool) (e1 e2 : E.expr t) := 
  match get_bool e with
  | Some b => if b then e1 else e2
  | _ => (e ? e1 ?: e2)
  end.

 Definition build_fst t1 t2 (e:E.expr (T.Pair t1 t2)) : E.expr t1 :=
  match is_pair_expr e with
  | Some (e1, e2) => e1
  | None => Efst e
  end.

 Definition build_snd t1 t2 (e:E.expr (T.Pair t1 t2)) : E.expr t2 :=
  match is_pair_expr e with
  | Some (e1, e2) => e2
  | None => Esnd e
  end.

 Notation "'Einl' e" := (E.Eop (O.Oinl _ _) (dcons _ e (dnil))) (at level 30).
 Notation "'Einr' e" := (E.Eop (O.Oinr _ _) (dcons _ e (dnil))) (at level 30).
 Notation "'Eisl' s" := (E.Eop (O.Oisl _ _) (dcons _ s (dnil))) (at level 30).
 Notation "'Eprojl' s" := (E.Eop (O.Oprojl _ _) (dcons _ s (dnil))) (at level 30).
 Notation "'Eprojr' s" := (E.Eop (O.Oprojr _ _) (dcons _ s (dnil))) (at level 30).
 

 Definition build_isl t1 t2 (e:E.expr (T.Sum t1 t2)) : E.expr T.Bool :=
  match is_sum_expr e with
  | Some (inl _) => true
  | Some (inr _) => false
  | None => Eisl e
  end.

 Definition build_projl t1 t2 (e:E.expr (T.Sum t1 t2)) : E.expr t1 :=
  match is_sum_expr e with
  | Some (inl e1) => e1
  | _ => Eprojl e
  end.

 Definition build_projr t1 t2 (e:E.expr (T.Sum t1 t2)) : E.expr t2 :=
  match is_sum_expr e with
  | Some (inr e1) => e1
  | _ => Eprojr e 
  end.
 
 Fixpoint build_in_dom_aux (n:nat) t1 t2 (e1:E.expr t1) (e2:E.expr (T.List (T.Pair t1 t2))) : E.expr T.Bool :=  
  if is_nil_expr e2 then E.Ecte false
  else 
   match is_cons_expr e2 with
   | Some (h,t) =>
     let in_t := 
      match n with 
      | O => e1 in_dom t
      | S n => build_in_dom_aux n e1 t
      end in
      build_or (build_eq e1 (build_fst h)) in_t
   | None => 
      match is_append_expr e2 with
      | Some (l1, l2) => 
        let (in_l1, in_l2) := 
          match n with 
          | O => (e1 in_dom l1, e1 in_dom l2)
          | S n => (build_in_dom_aux n e1 l1, build_in_dom_aux n e1 l2)
          end in
          build_or in_l1 in_l2
      | None => 
        if is_fst_split e1 e2 then false 
        else e1 in_dom e2
      end
   end.

 Definition build_in_dom := build_in_dom_aux 100%nat.
 
 Fixpoint build_img_aux (n:nat) t1 t2 (e1:E.expr t1) (e2:E.expr (T.List (T.Pair t1 t2))) : E.expr t2 :=
  match is_cons_expr e2 with
  | Some (h,t) =>
    let img_t := 
     match n with 
     | O => t [{ e1 }]
     | S n => build_img_aux n e1 t
     end in
     build_Oif (build_eq e1 (build_fst h)) (build_snd h) img_t
  | None => 
    match is_append_expr e2 with
    | Some (l1, l2) => 
      let (img_l1, img_l2) := 
       match n with 
       | O => (l1 [{ e1 }], l2 [{ e1 }])
       | S n => (build_img_aux n e1 l1, build_img_aux n e1 l2)
       end in
      let in_l1 := build_in_dom e1 l1 in
      build_Oif in_l1 img_l1 img_l2
    | None => e2 [{ e1 }]
    end
  end.

 Definition build_img := build_img_aux 100%nat.

 Fixpoint build_append_aux (n:nat) t (e1 e2 : E.expr (T.List t)) : E.expr (T.List t) :=
  if is_nil_expr e1 then e2
  else 
   match is_cons_expr e1 with
   | Some (h, tl) => 
     let tle2 := 
     match n with
     | O => E.Eop (O.Oappend t) {tl, e2}
     | S n => build_append_aux n tl e2
     end in
     h |::| tle2
   | _ =>  E.Eop (O.Oappend t) {e1, e2}     
   end.

 Definition build_append t (e1 e2 : E.expr (T.List t)) := 
  if is_nil_expr e2 then e1 else build_append_aux 100%nat e1 e2.

 Fixpoint build_split_aux (n:nat) t1 t2 (e1:E.expr t1) (e2:E.expr (T.List (T.Pair t1 t2))) : 
    E.expr (T.Pair (T.List (T.Pair t1 t2)) (T.Pair t2 (T.List (T.Pair t1 t2)))) :=
  match is_cons_expr e2 with
  | Some (h,t) =>
    let img_l2 := 
     match n with 
     | O =>  E.Eop (O.Osplit t1 t2) {e1, t}
     | S n => build_split_aux n e1 t
     end in
     let snd2 := build_snd img_l2 in
     build_Oif (build_eq e1 (build_fst h)) ( (E.Cnil _) | (build_snd h | t) ) 
          ( (h |::| (build_fst img_l2)) | snd2)
  | None => 
    match is_append_expr e2 with
    | Some (l1, l2) => 
      let (img_l1, img_l2) := 
       match n with 
       | O => (E.Eop (O.Osplit t1 t2) {e1, l1}, E.Eop (O.Osplit t1 t2) {e1, l2})
       | S n => (build_split_aux n e1 l1, build_split_aux n e1 l2)
       end in
      let in_l1 := build_in_dom e1 l1 in
      let snd1 := build_snd img_l1 in
      let snd2 := build_snd img_l2 in
      build_Oif in_l1 
         (build_fst img_l1 | (build_fst snd1 | build_append (build_snd snd1) l2))
         (build_append l1 (build_fst img_l2) | snd2)
    | None => E.Eop (O.Osplit t1 t2) {e1, e2}
    end
  end.

 Definition build_split := build_split_aux 100%nat.

 Fixpoint build_upd_aux (n:nat) t1 t2 (e1:E.expr t1) (e2:E.expr t2)(e3:E.expr (T.List (T.Pair t1 t2))) : 
    E.expr (T.List (T.Pair t1 t2)) :=
  match is_cons_expr e3 with
  | Some (h,t) =>
    let img_t := 
     match n with 
     | O =>  E.Eop (O.Oupd t1 t2) {e1, e2, t}
     | S n => build_upd_aux n e1 e2 t
     end in
     let hfst := build_fst h in
     build_Oif (build_eq e1 hfst) (( hfst | e2) |::| t) (h|::|img_t)
  | None => 
    match is_append_expr e3 with
    | Some (l1, l2) => 
      let (img_l1, img_l2) := 
       match n with 
       | O => (E.Eop (O.Oupd t1 t2) {e1, e2, l1}, E.Eop (O.Oupd t1 t2) {e1, e2, l2})
       | S n => (build_upd_aux n e1 e2 l1, build_upd_aux n e1 e2 l2)
       end in
      let in_l1 := build_in_dom e1 l1 in
      build_Oif in_l1
         (build_append img_l1 l2)
         (build_append l1 img_l2)
    | None => E.Eop (O.Oupd t1 t2) {e1, e2, e3}
    end
  end.

 Definition build_upd := build_upd_aux 100%nat.

 
 Fixpoint build_in_range_aux (n:nat) t1 t2 (e1:E.expr t2) (e2:E.expr (T.List (T.Pair t1 t2))) : E.expr T.Bool :=
  if is_nil_expr e2 then E.Ecte false
  else 
   match is_cons_expr e2 with
   | Some (h,t) =>
     let in_t := 
      match n with 
      | O => e1 in_range t
      | S n => build_in_range_aux n e1 t
      end in
      build_or (build_eq e1 (build_snd h)) in_t
   | None => 
      match is_append_expr e2 with
      | Some (l1, l2) => 
        let (in_l1, in_l2) := 
          match n with 
          | O => (e1 in_range l1, e1 in_range l2)
          | S n => (build_in_range_aux n e1 l1, build_in_range_aux n e1 l2)
          end in
          build_or in_l1 in_l2
      | None => e1 in_range e2
      end
   end.

 Definition build_in_range := build_in_range_aux 100%nat.
 
 Definition build_head t (e:E.expr (T.List t)) : E.expr t :=
  match is_cons_expr e with
  | Some (h, t) => h
  | None => E.Eop (O.Ohd t) {e}
  end.

 Definition build_tl t (e:E.expr (T.List t)) : E.expr (T.List t) :=
  match is_cons_expr e with
  | Some (h, t) => t
  | _ => E.Eop (O.Otl t) {e}
  end.
 
 Fixpoint build_mem_aux (n:nat) t (e1:E.expr t) (e2:E.expr (T.List t)) : E.expr T.Bool :=
  if is_nil_expr e2 then E.Ecte false
  else 
   match is_cons_expr e2 with
   | Some (h,t) =>
     let in_t := 
      match n with 
      | O => e1 is_in t
      | S n => build_mem_aux n e1 t
      end in
      build_or (build_eq e1 h) in_t
   | None => e1 is_in e2
   end.

 Definition build_mem := build_mem_aux 100%nat.

 Definition build_le (e1 e2:E.expr T.Nat) :=
  match get_nat e1, get_nat e2 with
  | Some n1, Some n2 => E.Ecte (leb n1 n2)
  | _, _ => if E.eqb e1 e2 then E.Ecte true else e1 <=! e2
  end.
 
  
 Definition build_add (e1 e2: E.expr T.Nat) :=
  match get_nat e1, get_nat e2 with
  | Some n1, Some n2 => E.Ecte (n1+n2)%nat
  | Some n1, _ => if nat_eqb n1 O then e2 else e1 +! e2
  | _, Some n2 => if nat_eqb n2 O then e1 else e1 +! e2
  | _, _ => e1 +! e2
  end.
 
 Definition build_sub (e1 e2: E.expr T.Nat) :=
  match get_nat e1, get_nat e2 with
  | Some n1, Some n2 => E.Ecte (n1-n2)%nat
  | Some n1, _ => if nat_eqb n1 O then E.Ecte O else e1 -! e2
  | _, Some n2 => if nat_eqb n2 O then e1 else e1 -! e2
  | _, _ => if E.eqb e1 e2 then E.Ecte O else e1 -! e2
  end.
 
 Definition build_mul (e1 e2: E.expr T.Nat) :=
  match get_nat e1, get_nat e2 with
  | Some n1, Some n2 => E.Ecte (n1*n2)%nat
  | Some n1, _ => 
    if nat_eqb n1 O then E.Ecte O 
    else if nat_eqb n1 1%nat then e2 else e1 *! e2
  | _, Some n2 => 
    if nat_eqb n2 O then E.Ecte O else
     if nat_eqb n2 1%nat then e1 else e1 *! e2
  | _, _ => e1 *! e2
  end.

 Definition build_op (op:O.op) (args:E.args (O.targs op)) : E.expr (O.tres op) :=
  match op as op0 return E.args (O.targs op0) -> E.expr (O.tres op0) with  
  | O.Ohd t => fun args => app_expr _ args (@build_head t) 
  | O.Otl t => fun args => app_expr _ args (@build_tl t) 
  | O.Oappend t => fun args => app_expr _ args (@build_append t)
  | O.Omem t => fun args => app_expr _ args (@build_mem t)
  | O.Oin_dom t1 t2 => fun args => app_expr _ args (@build_in_dom t1 t2)
  | O.Oin_range t1 t2 => fun args => app_expr _ args (@build_in_range t1 t2)
  | O.Osplit t1 t2 => fun args => app_expr _ args (@build_split t1 t2)
  | O.Oupd t1 t2 => fun args => app_expr _ args (@build_upd t1 t2)
  | O.Oimg t1 t2 => fun args => app_expr _ args (@build_img t1 t2)
  | O.Ofst t1 t2 => fun args => app_expr _ args (@build_fst t1 t2)
  | O.Osnd t1 t2 => fun args => app_expr _ args (@build_snd t1 t2)
  | O.Oisl t1 t2 => fun args => app_expr _ args (@build_isl t1 t2)
  | O.Oprojl t1 t2 => fun args => app_expr _ args (@build_projl t1 t2)
  | O.Oprojr t1 t2 => fun args => app_expr _ args (@build_projr t1 t2)
  | O.Oeq_ t => fun args => app_expr _ args (@build_eq t)
  | O.Oadd => fun args => app_expr _ args build_add
  | O.Osub => fun args => app_expr _ args build_sub
  | O.Omul => fun args => app_expr _ args build_mul
  | O.Ole  => fun args => app_expr _ args build_le
  | O.Onot => fun args => app_expr _ args build_not
  | O.Oand => fun args => app_expr _ args build_and
  | O.Oor => fun args => app_expr _ args build_or 
  | O.Oimp => fun args => app_expr _ args build_imp
  | O.Oif t => fun args => app_expr _ args (@build_Oif t)
  | O.Ouser op => simpl_op op 
  | op0 => fun args => E.Eop op0 args
  end args.
 
 (* TODO: we can do better with Oif and substitution for the cons case *)
 Definition build_exists t (x:Var.var t) e l :=
  if is_nil_expr l then E.Ecte false
  else E.Eexists x e l.
 
 Definition build_forall t (x:Var.var t) e l :=
  if is_nil_expr l then E.Ecte true
  else E.Eforall x e l. 
  
 Fixpoint simplify_expr (t:T.type) (e:E.expr t) : E.expr t :=
  match e in E.expr t0 return E.expr t0 with
  | E.Ecte t c => E.Ecte c
  | E.Evar t x => E.Evar x
  | E.Eop op args => 
    build_op op (dmap _ simplify_expr args)
  | E.Eexists t x e l =>
    build_exists x (simplify_expr e) (simplify_expr l)
  | E.Eforall t x e l => 
    build_forall x (simplify_expr e) (simplify_expr l)
  | E.Efind t x e l => 
    E.Efind x (simplify_expr e) (simplify_expr l)
  end.

 Lemma get_bool_spec_dep : forall t (e:E.expr t) b, 
  get_bool e = Some b -> eq_dep _ _ _ e T.Bool (E.Ecte b).
 Proof.
  intros t e; destruct e; simpl; try (intros; discriminate).
  destruct c; simpl; intros b0 H; inversion H; trivial.
 Qed.
 
 Lemma get_bool_spec : forall (e:E.expr T.Bool) b, 
  get_bool e = Some b -> e = E.Ecte b.
 Proof.
  intros e b Heq.
  apply T.eq_dep_eq; apply get_bool_spec_dep; trivial.
 Qed.
 
 Lemma get_nat_spec_dep : forall t (e:E.expr t) n, 
  get_nat e = Some n -> eq_dep _ _ _ e T.Nat (E.Ecte n).
 Proof.
  intros t e; destruct e; simpl; try (intros; discriminate).
  destruct c; simpl; intros b0 H; inversion H; trivial.
 Qed.

 Lemma get_nat_spec :forall (e:E.expr T.Nat) n, 
  get_nat e = Some n -> e = E.Ecte n.
 Proof. 
  intros e n Heq.
  apply T.eq_dep_eq; apply get_nat_spec_dep; trivial.
 Qed.

 Lemma is_nil_expr_spec_dep : forall t (e:E.expr t), 
  is_nil_expr e -> exists t', eq_dep T.type _ _ e _ (E.Ecte (E.Cnil t')).
 Proof.
  destruct e; simpl; intros; trivialb.
  destruct c; trivialb.
  exists t; trivial.
 Qed.

 Lemma is_nil_expr_spec : forall t (e:E.expr (T.List t)), 
  is_nil_expr e -> e = E.Ecte (E.Cnil t).
 Proof.
  intros; apply T.eq_dep_eq.
  destruct (is_nil_expr_spec_dep e H) as (t', Heq).
  inversion Heq; subst; trivial.
 Qed.

 Lemma is_cons_expr_dep_spec : forall t (e:E.expr t) t' (h:E.expr t') (tl:E.expr (T.List t')),
  is_cons_expr_dep e = Some (existT _ t' (h, tl)) ->
  eq_dep T.type _ _ e _ (h |::| tl).
 Proof.
  destruct e; simpl; intros; try discriminate.
  destruct op; try discriminate.
  T.dlist_inversion d; subst.
  inversion H; subst.
  rewrite (T.inj_pair2 H2), (T.inj_pair2 H3); trivial.
 Qed.

 Lemma is_cons_expr_spec : forall t (e:E.expr (T.List t)) h tl,
  is_cons_expr e = Some (h, tl) -> e = h |::| tl.
 Proof.
  intros t e h tl; unfold is_cons_expr.
  generalize (is_cons_expr_dep_spec e); destruct (is_cons_expr_dep e)
   as [ (t', (h', tl')) | ]; intros Heq.
  assert (W:= Heq _ _ _ (refl_equal _)); clear Heq; inversion W; subst.
  rewrite Teq_dep_refl, (T.inj_pair2 H2); intros Heq; inversion Heq; trivial.
  intros; discriminate.
 Qed.

 Lemma is_pair_expr_dep_spec : forall t (e:E.expr t) t1 (e1:E.expr t1) t2 (e2:E.expr t2),
  is_pair_expr_dep e = Some (existT _ t1 (existT _ t2 (e1, e2))) ->
  eq_dep T.type _ _ e _ (e1 | e2).
 Proof.
  destruct e; simpl; intros; try discriminate.
  destruct op; try discriminate.
  T.dlist_inversion d; subst.
  inversion H; subst; trivial.
 Qed.

 Lemma is_pair_expr_spec : forall t1 t2 (e:E.expr (T.Pair t1 t2)) e1 e2,
  is_pair_expr e = Some (e1, e2) ->
  e = (e1 | e2).
 Proof.
  intros t1 t2 e e1 e2; unfold is_pair_expr.
  generalize (is_pair_expr_dep_spec e); destruct (is_pair_expr_dep e)
   as [ (t1', (t2', (e1', e2'))) | ]; intros Heq.
  assert (W:= Heq _ _ _ _ (refl_equal _)); clear Heq; inversion W; subst.
  rewrite Teq_dep_refl, Teq_dep_refl, (T.inj_pair2 H4).
  intros Heq; inversion Heq; trivial.
  intros; discriminate.
 Qed.

 Lemma is_append_expr_dep_spec : forall t (e:E.expr t) t' (e1:E.expr (T.List t')) (e2:E.expr (T.List t')),
  is_append_expr_dep e = Some (existT _ t' (e1, e2)) ->
  eq_dep T.type _ _ e _ ( E.Eop (O.Oappend t') {e1, e2}).
 Proof.
  destruct e; simpl; intros; try discriminate.
  destruct op; try discriminate.
  T.dlist_inversion d; subst.
  inversion H; subst.
  rewrite (T.inj_pair2 H2), (T.inj_pair2 H3); trivial.
 Qed.

 Lemma is_append_expr_spec : forall t (e:E.expr (T.List t)) e1 e2,
  is_append_expr e = Some (e1, e2) ->
  e = ( E.Eop (O.Oappend t) {e1, e2}).
 Proof.
  intros t e e1 e2; unfold is_append_expr.
  generalize (is_append_expr_dep_spec e); destruct (is_append_expr_dep e)
   as [ (t1', (e1', e2')) | ]; intros Heq.
  assert (W:= Heq  _ _ _ (refl_equal _)); clear Heq; inversion W; subst.
  rewrite Teq_dep_refl, (T.inj_pair2 H2); intros Heq; inversion Heq; trivial.
  intros; discriminate.
 Qed.

 Lemma is_sum_expr_dep_spec_l : forall t (e:E.expr t) t1 (e1:E.expr t1) t2,
  is_sum_expr_dep e = Some (existT _ t1 (existT _ t2 (inl _ e1))) ->
  eq_dep T.type _ _ e (T.Sum t1 t2) (Einl e1).
 Proof.
  destruct e; simpl; intros; try discriminate.
  destruct op; try discriminate.
  T.dlist_inversion d; subst.
  inversion H; subst; trivial.
  T.dlist_inversion d; subst.
  inversion H.
 Qed.

 Lemma is_sum_expr_spec_l : forall t1 t2 (e:E.expr (T.Sum t1 t2)) e1,
  is_sum_expr e = Some (inl _ e1) ->
  e = (Einl e1).
 Proof.
  intros t1 t2 e e1; unfold is_sum_expr.
  generalize (is_sum_expr_dep_spec_l e); destruct (is_sum_expr_dep e)
   as [ (t1', (t2', [e' | e'])) | ]; intros Heq.
  assert (W:= Heq _ _ _ (refl_equal _)); clear Heq; inversion W; subst.
  rewrite Teq_dep_refl, Teq_dep_refl, (T.inj_pair2 H4).
  intros Heq; inversion Heq; trivial.
 
  clear.
  destruct (T.eq_dec t1' t1).
  generalize e0; rewrite e0.
  intro e2; rewrite (T.UIP_refl e2).
  destruct (T.eq_dec t2' t2).
  clear.
  generalize e3 e'; clear e'; rewrite e3.
  intro e4; rewrite (T.UIP_refl e4).
  intros e' H; inversion H.

  intros; discriminate.
  intros; discriminate.
  intros; discriminate.
 Qed.

 Lemma is_sum_expr_dep_spec_r : forall t (e:E.expr t) t1 t2 (e2:E.expr t2),
  is_sum_expr_dep e = Some (existT _ t1 (existT _ t2 (inr _ e2))) ->
  eq_dep T.type _ _ e (T.Sum t1 t2) (Einr e2).
 Proof.
  destruct e; simpl; intros; try discriminate.
  destruct op; try discriminate.
  T.dlist_inversion d; subst.
  inversion H.
  T.dlist_inversion d; subst.
  inversion H; subst; trivial.
 Qed.

 Lemma is_sum_expr_spec_r : forall t1 t2 (e:E.expr (T.Sum t1 t2)) e2,
  is_sum_expr e = Some (inr _ e2) ->
  e = (Einr e2).
 Proof.
  intros t1 t2 e e2; unfold is_sum_expr.
  generalize (is_sum_expr_dep_spec_r e); destruct (is_sum_expr_dep e)
   as [ (t1', (t2', [e' | e'])) | ]; intros Heq.
  clear.
  destruct (T.eq_dec t1' t1).
  generalize e0 e'; clear e'; rewrite e0.
  intro e1; rewrite (T.UIP_refl e1).
  destruct (T.eq_dec t2' t2).
  clear.
  generalize e3; rewrite e3.
  intro e4; rewrite (T.UIP_refl e4).
  intros e' H; inversion H.
  
  intros; discriminate.
  intros; discriminate.

  assert (W:= Heq _ _ _ (refl_equal _)); clear Heq; inversion W; subst.
  rewrite Teq_dep_refl, Teq_dep_refl, (T.inj_pair2 H4).
  intros Heq; inversion Heq; trivial.

  intros; discriminate.
 Qed.

 Lemma build_eq_spec : forall k (m:Mem.t k) t (e1 e2:E.expr t),
  E.eval_expr (build_eq e1 e2) m =
  E.eval_expr (e1 =?= e2) m.
 Proof.
  unfold build_eq; intros.
  generalize (E.eqb_spec e1 e2); destruct (E.eqb e1 e2); intros; trivial.
  subst; simpl; unfold O.eval_op; simpl.
  symmetry; apply Ti_eqb_refl.
 Qed.
 
 Lemma build_or_spec : forall k (m:Mem.t k) e1 e2,
  E.eval_expr (build_or e1 e2) m = 
  E.eval_expr (e1 || e2) m.
 Proof.
  unfold build_or; intros.
  generalize (get_bool_spec e1) (get_bool_spec e2);
   destruct (get_bool e1); destruct (get_bool e2); intros H H0;
    try rewrite (H _ (refl_equal _)); try rewrite (H0 _ (refl_equal _)); trivial.
  destruct b; trivial.
  destruct b; simpl; unfold O.eval_op; simpl.
  symmetry; apply orb_true_r.
  symmetry; apply orb_false_r.
 Qed.

 Lemma build_and_spec : forall k (m:Mem.t k) e1 e2,
  E.eval_expr (build_and e1 e2) m = 
  E.eval_expr (e1 && e2) m.
 Proof.
  unfold build_and; intros.
  generalize (get_bool_spec e1) (get_bool_spec e2);
   destruct (get_bool e1); destruct (get_bool e2); intros H H0;
    try rewrite (H _ (refl_equal _)); try rewrite (H0 _ (refl_equal _)); trivial.
  destruct b; trivial.
  destruct b; simpl; unfold O.eval_op; simpl.
  symmetry; apply andb_true_r.
  symmetry; apply andb_false_r.
 Qed.

 Lemma build_imp_spec : forall k (m:Mem.t k) e1 e2,
  E.eval_expr (build_imp e1 e2) m = 
  E.eval_expr (e1 ==> e2) m.
 Proof.
  unfold build_imp; intros.
  generalize (get_bool_spec e1) (get_bool_spec e2);
   destruct (get_bool e1); destruct (get_bool e2); intros H H0;
    try rewrite (H _ (refl_equal _)); try rewrite (H0 _ (refl_equal _)); trivial.
  destruct b; trivial.
  destruct b; simpl; unfold O.eval_op; simpl;
   destruct (E.eval_expr e1 m); trivial.
 Qed.

 Lemma build_not_spec : forall k (m:Mem.t k) e,
  E.eval_expr (build_not e) m = E.eval_expr (!e) m.
 Proof.
  unfold build_not; intros.
  generalize (get_bool_spec e); destruct (get_bool e); intros H;
   try rewrite (H _ (refl_equal _)); trivial.
 Qed.

 Lemma build_Oif_spec : forall k (m:Mem.t k) t e (e1 e2:E.expr t),
  E.eval_expr (build_Oif e e1 e2) m = E.eval_expr (e ? e1 ?: e2) m.
 Proof.
  unfold build_Oif; intros.
  generalize (get_bool_spec e); destruct (get_bool e); intros H; trivial.
  rewrite (H _ (refl_equal _)); clear H; destruct b; trivial.
 Qed.

 Lemma build_fst_spec : forall k (m:Mem.t k) t1 t2 (e:E.expr (T.Pair t1 t2)),
  E.eval_expr (build_fst e) m = E.eval_expr (Efst e) m.
 Proof.
  unfold build_fst; intros.
  generalize (is_pair_expr_spec e); destruct (is_pair_expr e); intros H; trivial.
  destruct p; rewrite (H _ _ (refl_equal _)); trivial.
 Qed.

 Lemma build_snd_spec : forall k (m:Mem.t k) t1 t2 (e:E.expr (T.Pair t1 t2)),
  E.eval_expr (build_snd e) m = E.eval_expr (Esnd e) m.
 Proof.
  unfold build_snd; intros.
  generalize (is_pair_expr_spec e); destruct (is_pair_expr e); intros H; trivial.
  destruct p; rewrite (H _ _ (refl_equal _)); trivial.
 Qed.

 Lemma is_fst_split_spec_dep : forall t1 t2 (r:E.expr t1) (e:E.expr t2),
  is_fst_split r e = true ->
  exists t4, exists l:E.expr (T.List (T.Pair t1 t4)),
   eq_dep T.type _ _ e _ (Efst (E.Eop (O.Osplit t1 t4) {r,l})).
 Proof.
  unfold is_fst_split.
  intros t1 t2 r e; destruct e; simpl; intro; try discriminate.
  generalize H; generalize d; clear H; clear d; destruct op; intros; try discriminate;simpl.
  T.dlist_inversion d; subst; simpl.
 generalize H; clear H.
 assert (forall t' t0' (e:E.expr (T.Pair t' t0')), 
     eq_dep T.type E.expr _ x _ e ->
     match is_split_expr_dep x with
     | Some (existT t1' (existT t2' (pair r' _))) => E.eqb r r'
     | None => false
     end = true ->
     exists t4 : T.type,
     exists l : E.expr (T.List (T.Pair t1 t4)),
      eq_dep T.type E.expr _ (Efst e) (T.List (T.Pair t1 t4))
         Efst (E.Eop (O.Osplit t1 t4) {r, l})).
  destruct x; simpl; intros; try discriminate.
  simpl in *.
  case_eq op; intros; subst; try discriminate; simpl in *.
  T.dlist_inversion d; subst; simpl in *.
  generalize (E.eqb_spec_dep r x) H; rewrite H0; clear H H0.
  intros H0; inversion H0.
  subst; clear H0; rewrite (T.inj_pair2 H3); clear H3; intros H0.
  exists t3; exists x0.
  inversion H0; clear H0; subst.
  rewrite (T.inj_pair2 H6); trivial.
  apply H; trivial.
 Qed.

 Lemma existsb_fst_split : forall k t1 t4 
  (i:T.interp k t1) (i0:T.interp k (T.List (T.Pair t1 t4))),
  existsb (fun p:T.interp k t1 * T.interp k t4 => T.i_eqb k t1 i (fst p))
  (fst (O.split_assoc (T.i_eqb k t1 i) (T.default k t4) i0)) = false.
 Proof.
  induction i0; simpl; trivial.
  case_eq (T.i_eqb k t1 i (@fst (T.interp k t1) (T.interp k t4) a)); 
   intros; trivial.
  simpl; rewrite H; trivial.
 Qed.

 Lemma build_isl_spec : forall k (m:Mem.t k) t1 t2 (e:E.expr (T.Sum t1 t2)),
  E.eval_expr (build_isl e) m = E.eval_expr (Eisl e) m.
 Proof.
  unfold build_isl; intros.
  generalize (is_sum_expr_spec_l e); generalize (is_sum_expr_spec_r e). 
  destruct (is_sum_expr e); intros H1 H2; trivial.
  destruct s.
  rewrite (H2 _ (refl_equal _)); trivial.
  rewrite (H1 _ (refl_equal _)); trivial.
 Qed.

 Lemma build_projl_spec : forall k (m:Mem.t k) t1 t2 (e:E.expr (T.Sum t1 t2)),
  E.eval_expr (build_projl e) m = E.eval_expr (Eprojl e) m.
 Proof.
  unfold build_projl; intros.
  generalize (is_sum_expr_spec_l e). 
  destruct (is_sum_expr e); intros H; trivial.
  destruct s.
  rewrite (H _ (refl_equal _)); trivial.
  trivial.
 Qed.

 Lemma build_projr_spec : forall k (m:Mem.t k) t1 t2 (e:E.expr (T.Sum t1 t2)),
  E.eval_expr (build_projr e) m = E.eval_expr (Eprojr e) m.
 Proof.
  unfold build_projr; intros.
  generalize (is_sum_expr_spec_r e). 
  destruct (is_sum_expr e); intros H; trivial.
  destruct s.
  trivial.  
  rewrite (H _ (refl_equal _)); trivial.
 Qed.

 Lemma build_in_dom_aux_spec : forall k (m:Mem.t k) n t1 t2 e1 e2,
  E.eval_expr (@build_in_dom_aux n t1 t2 e1 e2) m = E.eval_expr (e1 in_dom e2) m.
 Proof.
  induction n; simpl; intros.
  generalize (is_nil_expr_spec e2); destruct (is_nil_expr e2); intros.
  rewrite H; trivial.
  generalize (is_cons_expr_spec e2); destruct (is_cons_expr e2); intros.
  destruct p; rewrite (H0 _ _ (refl_equal _)).
  rewrite build_or_spec; simpl; unfold O.eval_op; simpl.
  rewrite build_eq_spec; simpl; unfold O.eval_op; simpl.
  rewrite (build_fst_spec m e); trivial.
  generalize (is_append_expr_spec e2); destruct (is_append_expr e2); intros.
  destruct p; rewrite (H1 _ _ (refl_equal _)).
  rewrite build_or_spec; simpl; unfold O.eval_op; simpl.
  rewrite existsb_app;trivial.
  generalize (is_fst_split_spec_dep e1 e2).
   destruct (is_fst_split e1 e2).
   intros H2;destruct (H2 (refl_equal _)) as (t4, (l, Heq)).
   inversion Heq;clear Heq;subst.
   rewrite (T.inj_pair2 H6);simpl;unfold O.eval_op;simpl.
   symmetry;apply existsb_fst_split.
   trivial.
  generalize (is_nil_expr_spec e2); destruct (is_nil_expr e2); intros.
  rewrite H; trivial.
  generalize (is_cons_expr_spec e2); destruct (is_cons_expr e2); intros.
  destruct p; rewrite (H0 _ _ (refl_equal _)).
  rewrite build_or_spec; simpl; unfold O.eval_op; simpl.
  rewrite IHn, build_eq_spec; simpl; unfold O.eval_op; simpl.
  rewrite (build_fst_spec m e); trivial.
  generalize (is_append_expr_spec e2); destruct (is_append_expr e2); intros.
  destruct p; rewrite (H1 _ _ (refl_equal _)).
  rewrite build_or_spec;simpl; unfold O.eval_op; simpl.
  repeat rewrite IHn;rewrite existsb_app;trivial.
  generalize (is_fst_split_spec_dep e1 e2).
   destruct (is_fst_split e1 e2).
   intros H2;destruct (H2 (refl_equal _)) as (t4, (l, Heq)).
   inversion Heq;clear Heq;subst.
   rewrite (T.inj_pair2 H6);simpl;unfold O.eval_op;simpl.
   symmetry;apply existsb_fst_split.
   trivial.
 Qed.

 Lemma build_in_dom_spec : forall k (m:Mem.t k) t1 t2 e1 e2,
  E.eval_expr (@build_in_dom t1 t2 e1 e2) m = E.eval_expr (e1 in_dom e2) m.
 Proof.
  unfold build_in_dom; intros; apply build_in_dom_aux_spec.
 Qed.

 Lemma eval_if_expr : forall k (m:Mem.t k) b t (e1 e2:E.expr t),
   E.eval_expr (b ? e1 ?: e2) m = if E.eval_expr b m then E.eval_expr e1 m else E.eval_expr e2 m.
 Proof. 
  trivial. 
 Qed.

 Lemma eval_cons : forall k (m:Mem.t k) t (e:E.expr t) l,
    E.eval_expr (e|::|l) m = E.eval_expr e m :: E.eval_expr l m.
 Proof. 
  trivial. 
 Qed.

 Lemma eval_expr_append : forall k (m:Mem.t k) t (l1 l2:E.expr (T.List t)),
    E.eval_expr (E.Eop (O.Oappend t) {l1, l2}) m = E.eval_expr l1 m ++ E.eval_expr l2 m.
 Proof. 
  trivial. 
 Qed.

 Lemma eval_assoc : forall k (m:Mem.t k) t1 t2 e1 (e2:E.expr (T.List (T.Pair t1 t2))), 
  E.eval_expr (e2[{e1}]) m = O.assoc (T.i_eqb k t1 (E.eval_expr e1 m)) (T.default k t2) (E.eval_expr e2 m).
 Proof. 
  trivial.
 Qed.

 Lemma eval_fst : forall k (m:Mem.t k) t1 t2 (e:E.expr (T.Pair t1 t2)),
   E.eval_expr (Efst e) m = @fst (T.interp k t1) (T.interp k t2) (E.eval_expr e m).
 Proof. 
  trivial. 
 Qed.

 Lemma eval_negb : forall (e:E.expr T.Bool) k (m:Mem.t k),
  E.eval_expr (!e) m = negb (E.eval_expr e m).
 Proof.
  trivial.
 Qed.

 Lemma eval_andb: forall (e1 e2:E.expr T.Bool) k (m:Mem.t k),
  E.eval_expr (e1 && e2) m = andb (E.eval_expr e1 m) (E.eval_expr e2 m).
 Proof.
  trivial.
 Qed.

 Lemma eval_eq : forall k (m:Mem.t k) t e1 e2,
  E.eval_expr (e1 =?= e2) m = T.i_eqb k t (E.eval_expr e1 m) (E.eval_expr e2 m).
 Proof.
  trivial.
 Qed.

 Lemma eval_lt : forall k (m:Mem.t k)  (e1 e2: E.expr T.Nat),
  (E.eval_expr e1 m < E.eval_expr e2 m)%nat <-> 
  E.eval_expr (e1 <! e2) m.
 Proof.
  intros; split; intros.
  change (is_true (leb ((E.eval_expr e1 m)+1) (E.eval_expr e2 m))).
  apply leb_correct; rewrite plus_comm; apply gt_le_S.
  assumption.
  change (is_true (leb ((E.eval_expr e1 m) + 1) (E.eval_expr e2 m))) in H.
  apply leb_complete in H; rewrite plus_comm in H; apply le_S_gt in H.
  assumption.
 Qed.

 Lemma eval_le : forall k (m:Mem.t k) (e1 e2:E.expr T.Nat),
  (E.eval_expr e1 m <= E.eval_expr e2 m)%nat <->
  E.eval_expr (e1 <=! e2) m.
 Proof.
  intros; simpl; unfold O.eval_op; simpl; split; intro.
  apply leb_correct; omega.
  apply leb_complete in H; omega.
 Qed.


 Lemma build_img_aux_spec : forall k (m:Mem.t k) n t1 t2 e1 e2,
  E.eval_expr (@build_img_aux n t1 t2 e1 e2) m = E.eval_expr (e2 [{ e1 }]) m.
 Proof.
  induction n; simpl; intros.
  generalize (is_cons_expr_spec e2); destruct (is_cons_expr e2); intros.
  destruct p; rewrite (H e e0); trivial.
  rewrite build_Oif_spec; simpl; unfold O.eval_op; simpl.
  rewrite build_eq_spec; simpl; unfold O.eval_op; simpl.
  rewrite (build_fst_spec m e), (build_snd_spec m e).
  simpl; unfold O.eval_op; simpl.
  unfold O.assoc; simpl.
  match goal with 
   |- (if ?t then _ else _) = _ => destruct t 
  end; trivial.
  generalize (is_append_expr_spec e2).
  destruct (is_append_expr e2); intros; [ | trivial].
  destruct p; rewrite (H0 e e0); trivial.
  rewrite build_Oif_spec, eval_if_expr, build_in_dom_spec.
  simpl; unfold O.eval_op; simpl.
  unfold O.assoc.
  induction (E.eval_expr e m); simpl; trivial;
  case (T.i_eqb k t1 (E.eval_expr e1 m) 
   (@fst (T.interp k t1) (T.interp k t2) a)); intros; simpl; trivial.
  generalize (is_cons_expr_spec e2); destruct (is_cons_expr e2); intros.
  destruct p; rewrite (H e e0); trivial. 
  rewrite build_Oif_spec.
  simpl; unfold O.eval_op; simpl.
  rewrite build_eq_spec; simpl; unfold O.eval_op; simpl.
  rewrite (build_fst_spec m e), (build_snd_spec m e).
  simpl; unfold O.eval_op; simpl.
  unfold O.assoc; simpl.
  match goal with 
   |- (if ?t then _ else _) = _ => destruct t end; trivial.
  rewrite IHn; trivial.
  generalize (is_append_expr_spec e2).
  destruct (is_append_expr e2); intros; [ | trivial].
  destruct p; rewrite (H0 e e0); trivial.
  rewrite build_Oif_spec, eval_if_expr.
  simpl; unfold O.eval_op; simpl.
  rewrite IHn, IHn, build_in_dom_spec;simpl; unfold O.eval_op; simpl.
  unfold O.assoc; induction (E.eval_expr e m); simpl; trivial;
  case (T.i_eqb k t1 (E.eval_expr e1 m) 
   (@fst (T.interp k t1) (T.interp k t2) a)); intros; simpl; trivial. 
 Qed.
 
 Lemma build_img_spec : forall k (m:Mem.t k)  t1 t2 e1 e2,
  E.eval_expr (@build_img t1 t2 e1 e2) m = E.eval_expr (e2 [{ e1 }]) m.
 Proof.
  unfold build_img; intros; apply build_img_aux_spec.
 Qed.

 Lemma build_append_aux_spec : forall k (m:Mem.t k) n t e1 e2,
  E.eval_expr (@build_append_aux n t e1 e2) m = E.eval_expr (E.Eop (O.Oappend t) {e1, e2}) m.
 Proof.
  induction n; simpl; intros.
  generalize (is_nil_expr_spec e1); destruct (is_nil_expr e1); intros.
  rewrite H; trivial.
  generalize (is_cons_expr_spec e1); destruct (is_cons_expr e1); intros.
  destruct p; rewrite (H0 _ _ (refl_equal _)); trivial.
  trivial.
  generalize (is_nil_expr_spec e1); destruct (is_nil_expr e1); intros.
  rewrite H; trivial.
  generalize (is_cons_expr_spec e1); destruct (is_cons_expr e1); intros.
  destruct p; rewrite (H0 _ _ (refl_equal _)).
  simpl; unfold O.eval_op; simpl.
  rewrite (IHn _ e0 e2); trivial.
  trivial.
 Qed.

 Lemma build_append_spec : forall k (m:Mem.t k) t e1 e2,
  E.eval_expr (@build_append t e1 e2) m = E.eval_expr (E.Eop (O.Oappend t) {e1, e2}) m.
 Proof.
  unfold build_append; intros.
  generalize (is_nil_expr_spec e2); destruct (is_nil_expr e2); intros.
  rewrite H; trivial.
  simpl; unfold O.eval_op; simpl.
  apply app_nil_end.
  apply build_append_aux_spec.
 Qed.

 Lemma upd_app : forall k t1 t2 (x : T.interp k t1) (v : T.interp k t2)
  (l1 l2 : T.interp k (T.List (T.Pair t1 t2))),
  O.upd (T.i_eqb k t1) x v (l1 ++ l2) =
  (if existsb (fun p : T.interp k t1 * T.interp k t2 => T.i_eqb k t1 x (fst p)) l1
   then O.upd (T.i_eqb k t1) x v l1 ++ l2
   else l1 ++ O.upd (T.i_eqb k t1) x v l2).
 Proof.
  induction l1;simpl;intros;trivial.
  destruct a;simpl.
  destruct (T.i_eqb k t1 x i);simpl;trivial.
  rewrite IHl1;destruct (existsb (fun p : T.interp k t1 * T.interp k t2 => T.i_eqb k t1 x (fst p)) l1);trivial.
 Qed.

 Lemma build_upd_aux_spec : forall k (m:Mem.t k) n t1 t2 e1 e2 e3,
  E.eval_expr (@build_upd_aux n t1 t2 e1 e2 e3) m = E.eval_expr (E.Eop (O.Oupd t1 t2) {e1, e2, e3}) m.
 Proof.
  induction n;simpl;intros.
  generalize (is_cons_expr_spec e3); destruct (is_cons_expr e3); intros.
  destruct p; rewrite (H _ _ (refl_equal _)).
  rewrite build_Oif_spec; simpl; unfold O.eval_op; simpl.
  rewrite build_eq_spec; simpl; unfold O.eval_op; simpl.
  rewrite build_fst_spec.
  simpl; unfold O.eval_op; simpl.
  destruct (E.eval_expr e m);simpl;trivial.
  generalize (is_append_expr_spec e3); destruct (is_append_expr e3); intros;[ | trivial].
  destruct p; rewrite (H0 _ _ (refl_equal _)).
  rewrite build_Oif_spec, eval_if_expr.
  simpl; unfold O.eval_op; simpl.
  rewrite build_in_dom_spec;simpl; unfold O.eval_op; simpl.
  repeat rewrite build_append_spec;simpl; unfold O.eval_op; simpl.
  symmetry;apply upd_app.
  generalize (is_cons_expr_spec e3); destruct (is_cons_expr e3); intros.
  destruct p; rewrite (H _ _ (refl_equal _)).
  rewrite build_Oif_spec; simpl; unfold O.eval_op; simpl.
  rewrite build_eq_spec; simpl; unfold O.eval_op; simpl.
  rewrite build_fst_spec, IHn.
  simpl; unfold O.eval_op; simpl.
  destruct (E.eval_expr e m);simpl;trivial.
  generalize (is_append_expr_spec e3).
  destruct (is_append_expr e3); intros; [ | trivial].
  destruct p; rewrite (H0 _ _ (refl_equal _)).
  rewrite build_Oif_spec, eval_if_expr; simpl; unfold O.eval_op; simpl.
  rewrite build_in_dom_spec;simpl; unfold O.eval_op; simpl.
  repeat rewrite build_append_spec;simpl; unfold O.eval_op; simpl.
  repeat rewrite IHn;simpl;unfold O.eval_op;simpl.
  symmetry;apply upd_app.
 Qed.

 Lemma build_upd_spec : forall k (m:Mem.t k) t1 t2 e1 e2 e3,
  E.eval_expr (@build_upd t1 t2 e1 e2 e3) m = E.eval_expr (E.Eop (O.Oupd t1 t2) {e1, e2, e3}) m.
 Proof.
  unfold build_upd; intros;apply build_upd_aux_spec.
 Qed.

 Lemma split_assoc_app : 
  forall k t1 t2 (i : T.interp k t1) (i0 i1 : T.interp k (T.List (T.Pair t1 t2))),
  (if existsb (fun p : T.interp k t1 * T.interp k t2 => T.i_eqb k t1 i (fst p))
      i0
   then
  (fst (O.split_assoc (T.i_eqb k t1 i) (T.default k t2) i0),
  (fst (snd (O.split_assoc (T.i_eqb k t1 i) (T.default k t2) i0)),
  snd (snd (O.split_assoc (T.i_eqb k t1 i) (T.default k t2) i0)) ++ i1))
  else
  (i0 ++ fst (O.split_assoc (T.i_eqb k t1 i) (T.default k t2) i1),
  snd (O.split_assoc (T.i_eqb k t1 i) (T.default k t2) i1))) =
  O.split_assoc (T.i_eqb k t1 i) (T.default k t2) (i0 ++ i1).
 Proof.
  induction i0;simpl;intros.
  destruct (O.split_assoc (T.i_eqb k t1 i) (T.default k t2) i1);trivial.
  destruct (T.i_eqb k t1 i (@fst (T.interp k t1) (T.interp k t2) a));simpl;trivial.
  destruct (existsb
   (fun p : T.interp k t1 * T.interp k t2 => T.i_eqb k t1 i (fst p)) i0);
  rewrite <- IHi0;trivial.
 Qed.

 Lemma build_split_aux_spec : forall k (m:Mem.t k) n t1 t2 e1 e2,
  E.eval_expr (@build_split_aux n t1 t2 e1 e2) m = E.eval_expr (E.Eop (O.Osplit t1 t2) {e1, e2}) m.
 Proof.
  induction n;simpl;intros.
  generalize (is_cons_expr_spec e2); destruct (is_cons_expr e2); intros.
  destruct p; rewrite (H _ _ (refl_equal _)).
  rewrite build_Oif_spec;simpl; unfold O.eval_op; simpl.
  rewrite build_eq_spec; simpl; unfold O.eval_op; simpl.
  rewrite (build_fst_spec m e), (build_snd_spec m e).
  simpl; unfold O.eval_op; simpl.
  match goal with 
   |- (if ?t then _ else _) = _ => destruct t end; trivial.
  generalize (is_append_expr_spec e2); destruct (is_append_expr e2); intros;[ | trivial].
  destruct p; rewrite (H0 _ _ (refl_equal _)).
  rewrite build_Oif_spec, eval_if_expr.
  simpl; unfold O.eval_op; simpl.
  rewrite build_in_dom_spec;simpl; unfold O.eval_op; simpl.
  repeat rewrite build_append_spec;simpl;unfold O.eval_op;simpl.
  apply split_assoc_app.
  
  generalize (is_cons_expr_spec e2); destruct (is_cons_expr e2); intros.
  destruct p; rewrite (H _ _ (refl_equal _)).
  rewrite build_Oif_spec;simpl; unfold O.eval_op; simpl.
  rewrite build_eq_spec; simpl; unfold O.eval_op; simpl.
  rewrite build_fst_spec, build_fst_spec, build_snd_spec, build_snd_spec.
  simpl; unfold O.eval_op; simpl.
  rewrite IHn.
  match goal with 
   |- (if ?t then _ else _) = _ => destruct t end;trivial.
  generalize (is_append_expr_spec e2); destruct (is_append_expr e2); intros;[ | trivial].
  destruct p; rewrite (H0 _ _ (refl_equal _)).
  rewrite build_Oif_spec, eval_if_expr.
  simpl; unfold O.eval_op; simpl.
  rewrite build_in_dom_spec;simpl; unfold O.eval_op; simpl.
  repeat rewrite build_append_spec;simpl;unfold O.eval_op;simpl.
  repeat ((rewrite build_fst_spec || rewrite build_snd_spec);simpl;unfold O.eval_op;simpl).
  rewrite IHn, IHn; apply split_assoc_app.
 Qed.
 
 Lemma build_split_spec : forall k (m:Mem.t k) t1 t2 e1 e2,
  E.eval_expr (@build_split t1 t2 e1 e2) m = E.eval_expr (E.Eop (O.Osplit t1 t2) {e1, e2}) m.
 Proof.
  intros;apply build_split_aux_spec.
 Qed.

 Lemma build_in_range_aux_spec : forall k (m:Mem.t k) n t1 t2 e1 e2,
  E.eval_expr (@build_in_range_aux n t1 t2 e1 e2) m = E.eval_expr (e1 in_range e2) m.
 Proof.
  induction n; simpl; intros.
  generalize (is_nil_expr_spec e2); destruct (is_nil_expr e2); intros.
  rewrite H; trivial.
  generalize (is_cons_expr_spec e2); destruct (is_cons_expr e2); intros.
  destruct p; rewrite (H0 _ _ (refl_equal _)).
  rewrite build_or_spec; simpl; unfold O.eval_op; simpl.
  rewrite build_eq_spec; simpl; unfold O.eval_op; simpl.
  rewrite (build_snd_spec m e); trivial. 
  generalize (is_append_expr_spec e2); destruct (is_append_expr e2); intros.
  destruct p; rewrite (H1 _ _ (refl_equal _)).
  rewrite build_or_spec; simpl; unfold O.eval_op; simpl.
  symmetry;apply existsb_app.
  trivial.
  generalize (is_nil_expr_spec e2); destruct (is_nil_expr e2); intros.
  rewrite H; trivial.
  generalize (is_cons_expr_spec e2); destruct (is_cons_expr e2); intros.
  destruct p; rewrite (H0 _ _ (refl_equal _)).
  rewrite build_or_spec; simpl; unfold O.eval_op; simpl.
  rewrite build_eq_spec; simpl; unfold O.eval_op; simpl.
  rewrite (build_snd_spec m e), (IHn _ _ e1 e0); trivial.
  generalize (is_append_expr_spec e2); destruct (is_append_expr e2); intros.
  destruct p; rewrite (H1 _ _ (refl_equal _)).
  rewrite build_or_spec; simpl; unfold O.eval_op; simpl.
  symmetry;rewrite IHn, IHn;apply existsb_app.
  trivial.
 Qed.

 Lemma build_in_range_spec : forall k (m:Mem.t k) t1 t2 e1 e2,
  E.eval_expr (@build_in_range t1 t2 e1 e2) m = E.eval_expr (e1 in_range e2) m.
 Proof.
  unfold build_in_range; intros; apply build_in_range_aux_spec.
 Qed.

 Lemma build_head_spec : forall k (m:Mem.t k) t e,
  E.eval_expr (@build_head t e) m = E.eval_expr (E.Eop (O.Ohd t) {e}) m.
 Proof.
  unfold build_head; intros.
  generalize (is_cons_expr_spec e); destruct (is_cons_expr e); intros.
  destruct p; rewrite (H _ _ (refl_equal _)); trivial.
  trivial.   
 Qed.

 Lemma build_tl_spec : forall k (m:Mem.t k) t e,
  E.eval_expr (@build_tl t e) m = E.eval_expr (E.Eop (O.Otl t) {e}) m.
 Proof.
  unfold build_tl; intros.
  generalize (is_cons_expr_spec e); destruct (is_cons_expr e); intros.
  destruct p; rewrite (H _ _ (refl_equal _)); trivial.
  trivial.   
 Qed.

 Lemma build_mem_aux_spec : forall k (m:Mem.t k) n t e1 e2,
  E.eval_expr (@build_mem_aux n t e1 e2) m = E.eval_expr (e1 is_in e2) m.
 Proof.
  induction n; simpl; intros.
  generalize (is_nil_expr_spec e2); destruct (is_nil_expr e2); intros.
  rewrite H; trivial.
  generalize (is_cons_expr_spec e2); destruct (is_cons_expr e2); intros.
  destruct p; rewrite (H0 _ _ (refl_equal _)).
  rewrite build_or_spec; simpl; unfold O.eval_op; simpl.
  rewrite build_eq_spec; trivial.
  trivial.
  generalize (is_nil_expr_spec e2); destruct (is_nil_expr e2); intros.
  rewrite H; trivial.
  generalize (is_cons_expr_spec e2); destruct (is_cons_expr e2); intros.
  destruct p; rewrite (H0 _ _ (refl_equal _)).
  rewrite build_or_spec; simpl; unfold O.eval_op; simpl.
  rewrite build_eq_spec, (IHn _ e1 e0); trivial.
  trivial.
 Qed.

 Lemma build_mem_spec : forall k (m:Mem.t k) t e1 e2,
  E.eval_expr (@build_mem t e1 e2) m = E.eval_expr (e1 is_in e2) m.
 Proof.
  unfold build_mem; intros; apply build_mem_aux_spec.
 Qed.

 Lemma build_le_spec : forall k (m:Mem.t k) e1 e2,
  E.eval_expr (build_le e1 e2) m = E.eval_expr (e1 <=! e2) m.
 Proof.
  unfold build_le; intros.
  generalize (get_nat_spec e1); destruct (get_nat e1); intros.
  rewrite (H _ (refl_equal _)).
  generalize (get_nat_spec e2); destruct (get_nat e2); intros.
  rewrite (H0 _ (refl_equal _)); trivial.
  generalize (E.eqb_spec n e2); destruct (E.eqb n e2); intros; trivial.
  rewrite <- H1; simpl; unfold O.eval_op; simpl.
  symmetry; apply leb_correct; trivial.
  generalize (E.eqb_spec e1 e2); destruct (E.eqb e1 e2); intros; trivial.
  rewrite <- H0; simpl; unfold O.eval_op; simpl.
  symmetry; apply leb_correct; trivial.
 Qed.

 Lemma build_add_spec : forall k (m:Mem.t k) e1 e2,
  E.eval_expr (build_add e1 e2) m = E.eval_expr (e1 +! e2) m.
 Proof.
  unfold build_add; intros.
  generalize (get_nat_spec e1) (get_nat_spec e2); destruct (get_nat e1);
   destruct (get_nat e2); intros H H0; try rewrite (H _ (refl_equal _));
    try rewrite (H0 _ (refl_equal _)); trivial.
  generalize (nat_eqb_spec n 0); destruct nat_eqb; intros; subst; trivial.
  generalize (nat_eqb_spec n 0); destruct nat_eqb; intros; subst; trivial.
  simpl; unfold O.eval_op; simpl; rewrite plus_0_r; trivial.
 Qed.

 Lemma build_mul_spec : forall k (m:Mem.t k) e1 e2,
  E.eval_expr (build_mul e1 e2) m = E.eval_expr (e1 *! e2) m.
 Proof.
  unfold build_mul; intros.
  generalize (get_nat_spec e1) (get_nat_spec e2); destruct (get_nat e1);
   destruct (get_nat e2); intros H H0; try rewrite (H _ (refl_equal _));
    try rewrite (H0 _ (refl_equal _)); trivial.
  generalize (nat_eqb_spec n 0); destruct nat_eqb; intros; subst; trivial.
  generalize (nat_eqb_spec n 1); destruct nat_eqb; intros; subst; trivial.
  simpl; unfold O.eval_op; simpl; rewrite plus_0_r; trivial.
  generalize (nat_eqb_spec n 0); destruct nat_eqb; intros; subst; trivial.
  simpl; unfold O.eval_op; simpl; rewrite mult_0_r; trivial.
  generalize (nat_eqb_spec n 1); destruct nat_eqb; intros; subst; trivial.
  simpl; unfold O.eval_op; simpl; rewrite mult_1_r; trivial.
 Qed.

 Lemma build_sub_spec : forall k (m:Mem.t k) e1 e2,
  E.eval_expr (build_sub e1 e2) m = E.eval_expr (e1 -! e2) m.
 Proof.
  unfold build_sub; intros.
  generalize (get_nat_spec e1) (get_nat_spec e2); destruct (get_nat e1);
   destruct (get_nat e2); intros H H0; try rewrite (H _ (refl_equal _));
    try rewrite (H0 _ (refl_equal _)); trivial.
  generalize (nat_eqb_spec n 0); destruct nat_eqb; intros; subst; trivial.
  generalize (nat_eqb_spec n 0); destruct nat_eqb; intros; subst; trivial.
  simpl; unfold O.eval_op; simpl; apply minus_n_O.
  generalize (E.eqb_spec e1 e2); destruct E.eqb; intros; subst; trivial.
  simpl; unfold O.eval_op; simpl; apply minus_n_n.
 Qed.

 Lemma build_op_spec : forall k (m:Mem.t k) op args,
  E.eval_expr (build_op op args) m = E.eval_expr (E.Eop op args) m.
 Proof.
  destruct op; intros args; trivial; try T.dlist_inversion args; subst;
   unfold build_op, app_expr.
  apply build_head_spec.
  refine (build_tl_spec m x).
  refine (build_append_spec m x x0).
  refine (build_mem_spec m x x0).
  refine (build_upd_spec m x x0 x1).
  refine (build_in_dom_spec m x x0).
  refine (build_in_range_spec m x x0).
  refine (build_split_spec m x x0).
  refine (build_img_spec m x x0).
  refine (build_fst_spec m x).
  refine (build_snd_spec m x).
  refine (build_isl_spec m x).
  refine (build_projl_spec m x).
  refine (build_projr_spec m x). 
  refine (build_eq_spec m x x0).
  refine (build_add_spec m x x0).
  refine (build_sub_spec m x x0).
  refine (build_mul_spec m x x0).
  refine (build_le_spec m x x0).
  refine (build_not_spec m x).
  refine (build_and_spec m x x0).
  refine (build_or_spec m x x0).
  refine (build_imp_spec m x x0).
  refine (build_Oif_spec m x x0 x1).
  exact (simpl_op_spec args m).
 Qed.
 
 Lemma simplify_expr_spec : forall  t (e:E.expr t) k (m:Mem.t k),
  E.eval_expr (simplify_expr e) m = E.eval_expr e m.
 Proof.
  induction e using E.expr_ind2 with (Pl:= fun lt args => forall k (m:Mem.t k),
   dmap (P1:= E.expr) _ (fun t e => E.eval_expr e m) (dmap E.expr simplify_expr args) = 
   dmap (P1:=E.expr) _ (fun t e => E.eval_expr e m) args); simpl; intros; trivial.
  rewrite <- IHe; apply (build_op_spec m op (dmap E.expr simplify_expr args)).
  (* exists *)
  rewrite <- IHe2; generalize (simplify_expr e2); unfold build_exists.
  intros e; assert (W:= is_nil_expr_spec e); destruct (is_nil_expr e); trivial.
  rewrite W; trivial.
  simpl; induction (E.eval_expr e m); simpl; trivial.
  rewrite IHi, IHe1; trivial.
  (* forall *)
  rewrite <- IHe2; generalize (simplify_expr e2); unfold build_forall.
  intros e; assert (W:= is_nil_expr_spec e); destruct (is_nil_expr e); trivial.
  rewrite W; trivial.
  simpl; induction (E.eval_expr e m); simpl; trivial.
  rewrite IHi, IHe1; trivial.
  (* find *)
  rewrite <- IHe2; generalize (simplify_expr e2).
  unfold find_default; simpl; intros e.
  replace (find (fun v0 : T.interp k t => E.eval_expr (simplify_expr e1) (m {!v <-- v0!})) (E.eval_expr e m))
  with (find (fun v0 : T.interp k t => E.eval_expr e1 (m {!v <-- v0!})) (E.eval_expr e m)); trivial.
  induction (E.eval_expr e m); simpl; trivial.
  rewrite IHi, IHe1; trivial.
  (* dcons *)
  rewrite IHe, IHe0; trivial.
 Qed.


 Lemma expr_modus_ponens : forall k (m:Mem.t k) e1 e2,
   E.eval_expr (e1 ==> e2) m ->
   E.eval_expr e1 m ->
   E.eval_expr e2 m.
 Proof.
   intros.
   unfold E.eval_expr, O.eval_op in H, H0; simpl in H, H0.
   rewrite H0 in H; trivial.
 Qed.
 
 Lemma expr_eval_eq : forall k (m:Mem.t k) (t:T.type) e1 e2,
  @E.eval_expr k t e1 m = E.eval_expr e2 m <-> 
  E.eval_expr (e1 =?= e2) m.
 Proof.
  intros; unfold E.eval_expr, O.eval_op; simpl.
  split.
  intro H; rewrite H.
  apply Ti_eqb_refl.
  intros H.
  rewrite is_true_Ti_eqb in H.
  apply H.
 Qed.


 (** Constant propagation *) 
 Module EpEntries <: OPT_ENTRIES.
 
  Definition oce t := option (E.expr t).
  
  Definition oeeq t (o1 o2 : oce t) := o1 = o2.
  
  Lemma oeeq_refl : forall t, reflexive _ (@oeeq t).
  Proof. 
   unfold reflexive, oeeq; trivial. 
  Qed.
  
  Lemma oeeq_sym : forall t, symmetric _ (@oeeq t).
  Proof. 
   unfold symmetric, oeeq; auto. 
  Qed.

  Lemma oeeq_trans : forall t, transitive _ (@oeeq t).
  Proof. 
   unfold transitive, oeeq; eauto using trans_eq. 
  Qed.

  Add Parametric Relation t : (oce t) (oeeq (t:=t))
   reflexivity proved by (@oeeq_refl t)
   symmetry proved by (@oeeq_sym t)
   transitivity proved by (@oeeq_trans t)
  as oeeq_rel.

 
  Module ABool.

   Record res : Type :=
    mkR {
     r_t : T.type;
     r_e : E.expr r_t;
     r_c : E.expr r_t
    }.
    
   Definition t := list res.
   
   Definition assoc te (e:E.expr te) (a:t) : oce te :=
    match find (fun r => E.eqb e (r_e r))  a with
    | Some ev => 
      let (r_t, r_e, r_c) := ev in
       match T.eq_dec r_t te with
       | left H => 
         match H in (_ = t0) return option (E.expr t0) with
         | refl_equal => Some r_c 
         end
       | right _ => None (* never appear *)
       end
    | _ => None
    end.

   Definition oeeqb t (o1 o2 : oce t) :=
    match o1, o2 with
    | Some e1, Some e2 => E.eqb e1 e2
    | None, None => true
    | _, _ => false
    end.

   Lemma oeeqb_sym : forall t (o1 o2: oce t),
    oeeqb o1 o2 = oeeqb o2 o1.
   Proof.
    destruct o1; destruct o2; trivial.
    simpl; generalize (E.eqb_spec e e0); destruct (E.eqb e e0); intros; subst.
    generalize (E.eqb_spec e0 e0); destruct (E.eqb e0 e0); intros; trivial.
    elim H; trivial.
    simpl; generalize (E.eqb_spec e0 e); destruct (E.eqb e0 e); intros; subst; trivial.
    elim H; trivial.
   Qed.

   Lemma oeeqb_refl : forall t (o: oce t), oeeqb o o.
   Proof.
    destruct o; trivial.
    simpl; generalize (E.eqb_spec e e); destruct (E.eqb e e); intros; subst; trivial.
    elim H; trivial.
   Qed.

   Lemma oeeqb_trans : forall t (o1 o2 o3: oce t),
    oeeqb o1 o2 -> oeeqb o2 o3 -> oeeqb o1 o3.
   Proof.
    destruct o1; destruct o2; simpl; intros o3 H; trivialb.
    destruct o3; trivialb.
    intros.
    generalize (E.eqb_spec e e0); destruct (E.eqb e e0); intros; subst; trivialb.
   Qed.    

   Definition eq_assoc a1 a2 (e:ET.t) := oeeqb (assoc e a1) (assoc e a2).

   Definition get_exprs (a:t) :=
    fold_left (fun E (ev:res) => Eset.add (ET.mkE (r_e ev)) E) a Eset.empty.

   Lemma get_exprs_assoc : forall e a, ~Eset.mem e (get_exprs a) -> assoc e a = None.
   Proof.
    unfold get_exprs.
    assert (forall e a r, 
     ~Eset.mem e
     (fold_left (fun (E : Eset.t) (ev : res) => Eset.add (ET.mkE (r_e ev)) E) a r) -> 
     assoc e a = None /\ ~Eset.mem e r).
    induction a; simpl; auto.
    intros r H; destruct (IHa _ H); clear IHa H; split.
    unfold assoc; simpl.
    assert (W:=E.eqb_spec_dep e (r_e a)); destruct (E.eqb e (r_e a)); intros; auto.
    elim H1; apply Eset.add_correct; auto.
    unfold Eset.E.eq.
    inversion W; simpl; destruct e; trivial.
    intro; apply H1; auto with set.
    intros e a H1; destruct (H _ _ _ H1); auto.
   Qed.

   Lemma get_expr_aux : forall e a r,
    Eset.mem e (fold_left (fun E ev => Eset.add  (ET.mkE (r_e ev)) E) a r) <->
    Eset.mem e r \/ Eset.mem e (get_exprs a).
   Proof.
    induction a; simpl; intros; auto.
    split; intros; auto. destruct H; autob.
    Opaque Eset.add.
    unfold get_exprs; simpl fold_left; repeat rewrite IHa.
    Transparent Eset.add.
    repeat rewrite EsetP.add_spec.
    clear IHa; assert (XX:= @Eset.empty_spec e); intuition.
   Qed.

   Definition eqb a1 a2 :=
    Eset.forallb (eq_assoc a1 a2)
    (Eset.union (get_exprs a1) (get_exprs a2)).

   Lemma eq_assoc_sym : forall a1 a2 x, 
    eq_assoc a1 a2 x -> eq_assoc a2 a1 x.
   Proof. 
    unfold eq_assoc; intros.
    rewrite oeeqb_sym; trivial.
   Qed.

   Lemma eq_assoc_trans : forall a1 a2 a3 x, 
    eq_assoc a1 a2 x -> eq_assoc a2 a3 x -> eq_assoc a1 a3 x.
   Proof.
    unfold eq_assoc; intros.
    apply oeeqb_trans with (assoc x a2); auto.
   Qed.

   Lemma eqb_refl : forall a, eqb a a.
   Proof.
    unfold eqb; intros a.
    apply Eset.forallb_complete.
    intros x y H ; rewrite (H:x = y); trivial.
    unfold eq_assoc; intros; apply oeeqb_refl.
   Qed.

   Lemma eqb_sym : forall a1 a2, eqb a1 a2 -> eqb a2 a1.
   Proof.
    unfold eqb; intros a1 a2 H.
    apply Eset.forallb_complete; intros.
    rewrite (H0:x = y); trivial. 
    apply eq_assoc_sym.
    apply Eset.forallb_correct with (Eset.union (get_exprs a1) (get_exprs a2)); trivial.
    intros x0 y X; rewrite (X:x0 = y); trivial.
    rewrite EsetP.union_sym; trivial.
   Qed.

   Lemma eqb_trans : forall a1 a2 a3, eqb a1 a2 -> eqb a2 a3 -> eqb a1 a3.
   Proof.
    unfold eqb; intros.
    assert (WW:forall a1 a2 x y, x = y -> eq_assoc a1 a2 x = eq_assoc a1 a2 y) by (intros; subst; trivial).
    assert (H1 := Eset.forallb_correct _ (WW a1 a2) _ H).
    assert (H2 := Eset.forallb_correct _ (WW a2 a3) _ H0).
    apply Eset.forallb_complete; auto.
    intros.
    rewrite EsetP.union_spec in H3; destruct H3.
    destruct (is_true_dec (Eset.mem x (get_exprs a2))).
    apply eq_assoc_trans with a2; auto with set.
    destruct (is_true_dec (Eset.mem x (get_exprs a3))).
    apply eq_assoc_trans with a2; auto with set.
    unfold eq_assoc.
    rewrite (get_exprs_assoc _ _ H5). 
    rewrite <- (get_exprs_assoc _ _ H4).
    refine (H1 x _); auto with set.
    destruct (is_true_dec (Eset.mem x (get_exprs a2))).
    apply eq_assoc_trans with a2; auto with set.
    destruct (is_true_dec (Eset.mem x (get_exprs a1))).
    apply eq_assoc_trans with a2; auto with set.
    unfold eq_assoc.
    rewrite (get_exprs_assoc _ _ H5). 
    rewrite <- (get_exprs_assoc _ _ H4).
    refine (H2 x _); auto with set.
   Qed.

  End ABool.

  Module A :=  MkEqBool ABool.   
  

  (** The smallest element of A.t *)
  Definition Abot := @nil ABool.res. 
  
  Definition oele t (av1 av2:oce t) :=
   match av2, av1 with
   | _, None => true
   | Some v2, Some v1 => E.eqb v1 v2
   | _, _ => false
   end.

  Lemma oele_refl : forall t (av:oce t), oele av av.
  Proof.
   destruct av; simpl; auto.
   assert (X:= E.eqb_spec e e); destruct (E.eqb e e); trivial.
   elim X; trivial.
  Qed.

  Lemma oele_trans : forall t (av1 av2 av3:oce t), oele av1 av2 -> oele av2 av3 -> oele av1 av3.
  Proof.
   intros t [v1|] [v2|] [v3|]; simpl; intros; autob.
   assert (X1:= E.eqb_spec v1 v2); rewrite H in X1; rewrite X1; trivial.
  Qed.

  Definition merge_aval t (av1 av2:oce t) : oce t :=
   match av1, av2 with
   | None, _ => None
   | _, None => None
   | Some v1, Some v2 =>
     if E.eqb v1 v2 then Some v1 else None
   end.

  Definition valid_A k t (av:oce t) (v:T.interp k t) (m:Mem.t k):=
   match av with
   | Some e =>  v = E.eval_expr e m
   | _ => True
   end.
  
  Definition is_valid_A k t (av:oce t) (v:T.interp k t) (m:Mem.t k) :=
   match av with
   | Some e => T.i_eqb k t v (E.eval_expr e m)
   | _ => true
   end.

  Lemma is_valid_A_spec : forall k t (av:oce t) v (m:Mem.t k),
   valid_A av v m <-> is_valid_A av v m.
  Proof.
   unfold valid_A, is_valid_A; destruct av; split; intros; auto.
   rewrite <- H; assert (X1:= T.i_eqb_spec k t v v); destruct (T.i_eqb k t v v); auto.
   elim X1; trivial.
   assert (X1:= T.i_eqb_spec k t v (E.eval_expr e m)); rewrite H in X1; trivial.
  Qed.


  (** A partial order over  A.t *)
  Definition Ale (a1 a2:A.t) :=
      forall t (e:E.expr t), oele (ABool.assoc e a1) (ABool.assoc e a2).
 
  (** [valid a m] specify the correctness of the result of the analysis *)
  Definition valid k a (m:Mem.t k) := 
   forall t (e:E.expr t), valid_A (ABool.assoc e a) (E.eval_expr e m) m.
  

  (** The validity is decidable *)
  Definition is_valid k (a:A.t) (m:Mem.t k) := 
   Eset.forallb
   (fun e => is_valid_A (ABool.assoc e a) (E.eval_expr e m) m) 
   (ABool.get_exprs a).
  
  Fixpoint remove_aux (test : ABool.res -> bool) (a:A.t) : A.t :=
    match a with
    | nil => nil
    | ev :: a =>
      if test ev then 
       remove_aux (fun ev' => 
         if test ev' then true 
         else E.eqb (ABool.r_e ev) (ABool.r_e ev')) a
       else ev :: remove_aux test a
    end.

  Lemma remove_aux_spec : forall a test t (e:E.expr t) v,
   ABool.assoc e (remove_aux test a) = Some v ->
   ABool.assoc e a = Some v /\ ~ test (ABool.mkR e v).
  Proof.
   induction a; simpl; intros.
   discriminate H.
   case_eq (test a); intros Heq; rewrite Heq in H.
   destruct (IHa _ _ _ _ H).
   case_eq (test (ABool.mkR e v)); intros H2; rewrite H2 in H1.
   elim H1; trivial.
   simpl in H1; unfold ABool.assoc; simpl.
   assert (W:=E.eqb_spec_dep e (ABool.r_e a)); destruct (E.eqb e (ABool.r_e a)).
   apply eq_dep_sym in W.
   generalize (E.eqb_spec_dep (ABool.r_e a) e); destruct (E.eqb (ABool.r_e a) e); intros.
   elim H1; trivial.
   elim (H3 W).
   split;[exact H0 | intro; discriminate].
   unfold ABool.assoc in *; simpl in *.
   generalize (E.eqb_spec_dep e (ABool.r_e a)); destruct (E.eqb e (ABool.r_e a)); intros.
   destruct a.
   inversion H0; clear H0; subst; simpl in *.
   generalize H; clear H; case_eq (T.eq_dec r_t r_t); intros Heq1.
   rewrite (T.UIP_refl Heq1); intros.
   inversion H0; subst; simpl.
   rewrite (T.inj_pair2 H4), Heq; split;[trivial|intro; discriminate].
   intros Heq2; elim (T.eq_dec_r Heq2); trivial.
   exact (IHa _ _ _ _ H).
  Qed.
      
  Definition remove t (x:Var.var t) (a:A.t) : A.t :=
   remove_aux (fun (ev:ABool.res) => 
    if Vset.mem x (fv_expr (ABool.r_e ev)) then true
    else Vset.mem x (fv_expr (ABool.r_c ev))) a.
  
  Definition remove_set X (a:A.t) :=  
   remove_aux (fun (ev:ABool.res) => 
    if Vset.disjoint (fv_expr (ABool.r_e ev)) X then
     negb (Vset.disjoint (fv_expr (ABool.r_c ev)) X)
    else true) a.
 
  Fixpoint norm_expr (a:A.t) t (e:E.expr t)  :=
   match ABool.assoc e a with
   | Some v => v
   | None =>
     match e in (E.expr t0) return E.expr t0 with   
     | E.Ecte t c => E.Ecte c
     | E.Evar t x => E.Evar x
     | E.Eop op args => E.Eop op (dmap _ (norm_expr a) args)
     | E.Eexists t x e l => E.Eexists x (norm_expr (remove x a) e) (norm_expr a l)
     | E.Eforall t x e l => E.Eforall x (norm_expr (remove x a) e) (norm_expr a l)
     | E.Efind t x e l => E.Efind x (norm_expr (remove x a) e) (norm_expr a l)
     end
   end.

  Definition eval_e t (e:E.expr t) a := simplify_expr (norm_expr a e).

  (** [add_assign x e a] enrich the analysis [a] with the fact that x <- e *)
  Definition add_assign t (x:Var.var t) (e:E.expr t) a :=
    let e' := eval_e e a in
    if Vset.mem x (fv_expr e') then a 
    else ABool.mkR (E.Evar x) e' :: a.

  Definition get_eq_op (b:bool) (op:O.op) : E.args (O.targs op) -> option ABool.res :=
   if b then 
    match op as op0 return E.args (O.targs op0) -> option ABool.res with
    | O.Oeq_ t => fun args =>
      Some (app_expr ABool.res args (@ABool.mkR t))
    | _ => fun args => None
    end
   else fun _ => None.

  Fixpoint get_eq_expr (b:bool) t (e : E.expr t) {struct e} : option (ABool.res) :=
   match e with
   | E.Eop op args => 
     match op with
     | O.Onot => 
       match args with
       | dcons t _ e dnil => get_eq_expr (negb b) e
       | _ => None
       end
     | _ => get_eq_op b op args
     end
   | _ => None
   end.

  Definition add_test (e:E.expr T.Bool) (b:bool) (a:A.t) := 
   match ABool.assoc e a with
   | Some _ => a
   | None => 
     let a':= (ABool.mkR e (E.Cbool b))::a in
      match get_eq_expr b e with 
      | Some v => 
        match ABool.assoc v.(ABool.r_e) a' with
        | Some _ => a'
        | _ => v:: a'
        end
      | _ => a'
      end
   end.
 
  Definition lub (a1 a2:A.t) : A.t :=
   let E1 := ABool.get_exprs a1 in
   let E2 := ABool.get_exprs a2 in
   let I := Eset.inter E1 E2 in
    Eset.fold (fun e a =>
     match merge_aval (ABool.assoc e a1) (ABool.assoc e a2) with
     | Some v => (ABool.mkR e v)::a
     | None => a
     end) I nil.

  (** Specification *)
  Lemma oeeqb_oeeq : forall t (x y:oce t),  ABool.oeeqb x y <-> oeeq x y.
  Proof.
   destruct x; destruct y; simpl; split; intros; trivialb; try discriminate.
   assert (W:= E.eqb_spec e e0); rewrite H in W; rewrite W; red; trivial.
   inversion H; assert (W:=E.eqb_spec e0 e0); destruct (E.eqb e0 e0); trivial.
   elim W; trivial.
   red; trivial.
  Qed.

  Add Parametric Morphism t : (@ABool.assoc t)
  with signature @Eeq t ==> A.eq ==> oeeq (t:=t)
  as assoc_morph.
  Proof.
   unfold A.eq, ABool.eqb, Eeq; intros; subst.
   assert (WW:forall x1 x2 x y, x = y -> ABool.eq_assoc x1 x2 x = ABool.eq_assoc x1 x2 y).
     intros; subst; trivial.
   assert (X:= Eset.forallb_correct _ (WW x0 y0) _ H0 (ET.mkE y)); clear H0.
   unfold ABool.eq_assoc in X; simpl in X.
   rewrite <- oeeqb_oeeq.
   destruct (is_true_dec (Eset.mem (ET.mkE y) (ABool.get_exprs x0))); auto with set.
   destruct (is_true_dec (Eset.mem (ET.mkE y) (ABool.get_exprs y0))); auto with set.
   assert (W:=ABool.get_exprs_assoc _ _  H); simpl in W; rewrite W.
   assert (W':=ABool.get_exprs_assoc _ _ H0); simpl in W'; rewrite W'; trivial.
  Qed.

  Add Parametric Morphism t : (oele (t:=t))
  with signature oeeq (t:=t) ==> oeeq (t:=t) ==> @eq bool
  as oele_morph.
  Proof.
   unfold oeeq; intros; subst; trivial.
  Qed.
   
  Lemma Ale_morph : forall x y : A.t,
   A.eq x y -> forall x0 y0 : A.t, A.eq x0 y0 -> (Ale x x0 <-> Ale y y0).
  Proof.
   unfold Ale; split; intros.
   rewrite <- H; rewrite <- H0; trivial.
   rewrite H; rewrite H0; trivial.
  Qed.  
  
  Add Morphism Ale 
  with signature A.eq ==> A.eq ==> iff
  as Ale_morph_.
  Proof.
   apply Ale_morph.
  Qed.

  Lemma Ale_refl : forall a, Ale a a.
  Proof.
   unfold Ale; intros.
   destruct (ABool.assoc e a); simpl; auto.
   assert (X:=E.eqb_spec e0 e0); destruct (E.eqb e0 e0); trivial.
   elim X; trivial.
  Qed.

  Lemma Ale_trans : forall a1 a2 a3, Ale a1 a2 -> Ale a2 a3 -> Ale a1 a3.
  Proof.
   unfold Ale; intros a1 a2 a3 H H0 t e.
   apply oele_trans with (ABool.assoc e a2); auto.
  Qed.

  Lemma valid_morph : forall k (x y : A.t),
   A.eq x y ->
   forall x0 y0 : Mem.t k, Meq k x0 y0 -> (valid x x0 <-> valid y y0).
  Proof.
   unfold valid, is_valid.
   unfold Meq,valid_A; intros; subst; split; intros.
   assert (X:= H0 _ e); clear H0.
   assert (W:=assoc_morph (refl_equal e) H); unfold oeeq in W; rewrite <- W; trivial.
   assert (W:=assoc_morph (refl_equal e) H); unfold oeeq in W; rewrite W; apply H0.
  Qed.

  Add Parametric Morphism k : (valid (k:=k))
  with signature A.eq ==> @Meq k ==> iff
  as valid_morph_.
  Proof.
   apply valid_morph.
  Qed.

  Lemma valid_le : forall k a1 a2 (m:Mem.t k),  Ale a1 a2 -> valid a2 m -> valid a1 m.
  Proof.
   unfold Ale, valid; intros.
   assert (X1 := H _ e); assert (X2 := H0 _ e).
   destruct (ABool.assoc e a1) as [v1|]; autob.
   destruct (ABool.assoc e a2) as [v2|]; simpl in X1,X2; autob.
   rewrite X2. 
   assert (X:=E.eqb_spec v1 v2); rewrite X1 in X; trivial; rewrite X; trivial.
  Qed. 
 
  Lemma is_valid_spec : forall k a (m:Mem.t k), is_valid a m <-> valid a m.
  Proof.
   unfold is_valid,valid; split; intros.
   destruct (is_true_dec (Eset.mem (ET.mkE e) (ABool.get_exprs a))).
   match goal with [H:is_true (Eset.forallb ?f ?s) |- _ ] =>
    assert  (YY: forall x y, x = y -> f x = f y)
     by (intros x y Heq; rewrite (Heq:x = y); trivial);
     assert (XX:= Eset.forallb_correct _ YY s H _ H0); clear YY H
   end.
   rewrite is_valid_A_spec; trivial.
   assert (W:= ABool.get_exprs_assoc (ET.mkE e) a); simpl in W; rewrite W; simpl; trivial.
   apply Eset.forallb_complete; intros.
   rewrite (H0:x=y); trivial.
   rewrite <- is_valid_A_spec; auto.
  Qed.

  Lemma le_bot : forall a, Ale Abot a.
  Proof.
   unfold Ale, Abot, oele; simpl; intros.
   destruct (ABool.assoc e a); trivial.
  Qed.

  Lemma valid_bot : forall k (m:Mem.t k), valid Abot m.
  Proof. 
   unfold valid, Abot; simpl; auto. 
  Qed.

  Lemma le_merge_aval_l : forall t (av1 av2:oce t), oele (merge_aval av1 av2) av1.
  Proof.
   destruct av1; auto.
   destruct av2; simpl; auto.
   assert (X:= E.eqb_spec e e0); destruct (E.eqb e e0); trivial.
   intros; assert (X':=E.eqb_spec e e); destruct (E.eqb e e); trivial.
   elim X'; trivial.
  Qed.
 
  Lemma le_merge_aval_r : forall t (av1 av2:oce t), oele (merge_aval av1 av2) av2.
  Proof.
   destruct av1; destruct av2; simpl; auto.
   case_eq (E.eqb e e0); auto.
  Qed.

  Lemma le_lub_l : forall a1 a2, Ale (lub a1 a2) a1.
  Proof. 
   unfold Ale,lub; intros.
   rewrite Eset.fold_spec.
   match goal with
   | |- is_true (oele (ABool.assoc e (fold_left ?f _ _)) _) =>
     assert (forall l, (forall e1, InA (@eq _) e1 l -> Eset.mem e1 (ABool.get_exprs a1)) ->
      forall r, oele (ABool.assoc e r) (ABool.assoc e a1) ->
      oele (ABool.assoc e (fold_left f l r)) (ABool.assoc e a1))
   end.
    induction l; simpl; intros; auto.
    apply IHl; clear IHl.
    intuition.
    case_eq (merge_aval (ABool.assoc a a1) (ABool.assoc a a2)); intros; auto.
    unfold ABool.assoc at 1; simpl.
    destruct a as (ta,a); simpl.
    assert (UU:= E.eqb_spec_dep e a); destruct (E.eqb e a); auto.
    inversion UU; subst.
    case_eq (T.eq_dec ta ta); intros.
    rewrite (T.UIP_refl e1).
    simpl in *; rewrite <- H1; rewrite (T.inj_pair2 H5); apply le_merge_aval_l.
    destruct (ABool.assoc e a1); trivial.
   apply H; clear H.
   intros e1 H1; assert (UU:= Eset.elements_complete H1).
   rewrite EsetP.inter_spec in UU; intuition.
   unfold ABool.assoc at 1; simpl; unfold oele.
   destruct (ABool.assoc e a1); trivial.
  Qed.

  Lemma le_lub_r : forall a1 a2, Ale (lub a1 a2) a2.
  Proof.
   unfold Ale,lub; intros.
   rewrite Eset.fold_spec.
   match goal with
   | |- is_true (oele (ABool.assoc e (fold_left ?f _ _)) _) =>
     assert (forall l, (forall e1, InA (@eq _) e1 l -> Eset.mem e1 (ABool.get_exprs a2)) ->
      forall r, oele (ABool.assoc e r) (ABool.assoc e a2) ->
       oele (ABool.assoc e (fold_left f l r)) (ABool.assoc e a2))
   end.
    induction l; simpl; intros; auto.
    apply IHl; clear IHl.
    intuition.
    case_eq (merge_aval (ABool.assoc a a1) (ABool.assoc a a2)); intros; auto.
    unfold ABool.assoc at 1; simpl.
    assert (UU:= E.eqb_spec_dep e a); destruct (E.eqb e a); auto.
    destruct a as (ta,a); simpl in *.
    inversion UU; subst.
    case_eq (T.eq_dec ta ta); intros.
    rewrite (T.UIP_refl e1).
    simpl in *; rewrite <- H1; rewrite (T.inj_pair2 H5); apply le_merge_aval_r.
    destruct (ABool.assoc e a2); trivial.
   apply H; clear H.
   intros e1 H1; assert (UU:= Eset.elements_complete H1).
   rewrite EsetP.inter_spec in UU; intuition.
   unfold ABool.assoc at 1; simpl; unfold oele.
   destruct (ABool.assoc e a2); trivial.
  Qed.

  Lemma remove_le : forall t (x:Var.var t) a, Ale (remove x a) a.
  Proof.
   unfold remove; intros.
   unfold Ale; intros.
   match goal with
    |- is_true (oele ?f _) => case_eq f; intros
   end.
   destruct (remove_aux_spec _ _ _ H). 
   rewrite H0; apply oele_refl.
   destruct (ABool.assoc e a); trivial.
  Qed.
  
  Lemma remove_update : forall k a t (x:Var.var t) (m:Mem.t k) v, 
   valid a m -> valid (remove x a) (Mem.upd m x v).
  Proof.
   unfold valid; intros.
   case_eq (ABool.assoc e (remove x a)); intros; simpl; auto.
   destruct (remove_aux_spec _ _ _ H0).
   generalize H2; clear H2; simpl.
   case_eq (Vset.mem x (fv_expr e)); intros.
   elim H3; trivial.
   rewrite <-(@depend_only_fv_expr _ e _ m (m {!x <--v!})).
   rewrite <-(@depend_only_fv_expr _ e0 _ m (m {!x <--v!})).
   assert (XX:=H _ e); rewrite H1 in XX; exact XX.
   apply req_mem_upd_disjoint.
   destruct (Vset.mem x (fv_expr e0)); trivial.
   elim H3; trivial. 
   apply req_mem_upd_disjoint; trivial.
  Qed.
  
  Lemma remove_set_le : forall X a, Ale (remove_set X a) a.
  Proof.
   unfold remove_set; intros.
   unfold Ale; intros.
   match goal with
    |- is_true (oele ?f _) => case_eq f; intros
   end.
   destruct (remove_aux_spec _ _ _ H). 
   rewrite H0; apply oele_refl.
   destruct (ABool.assoc e a); trivial.
  Qed.

  Lemma valid_remove_set_update : forall k X a (m m':Mem.t k),
   valid (remove_set X a) m -> valid (remove_set X a) (m {!X <<- m'!}).
  Proof.
   unfold valid; intros.
   case_eq (ABool.assoc e (remove_set X a)); intros; simpl; auto.
   destruct (remove_aux_spec _ _ _ H0). 
   generalize H2; clear H2; case_eq (Vset.disjoint (fv_expr (ABool.r_e (ABool.mkR e e0))) X); intros.
   rewrite <- (@depend_only_fv_expr _ e _ m  (m {!X <<- m'!})).
   rewrite <- (@depend_only_fv_expr _ e0 _ m  (m {!X <<- m'!})).
   assert (XXX:=H _ e); rewrite H0 in XXX; exact XXX.
   apply req_mem_sym; apply req_mem_update_disjoint.
   simpl in H3; destruct (Vset.disjoint (fv_expr e0) X); trivial.
   elim H3; trivial.
   apply req_mem_sym; apply req_mem_update_disjoint; exact H2.
   elim H3; trivial.
  Qed.

  Lemma valid_eval_e : forall k a (m:Mem.t k) t (e:E.expr t), 
   valid a m -> 
   E.eval_expr e m = E.eval_expr (eval_e e a) m.
  Proof.
   intros k a m t e H; unfold eval_e.
   rewrite simplify_expr_spec.
   assert (forall t (e x:E.expr t) a k (m:Mem.t k), valid a m -> 
    E.eval_expr e m = E.eval_expr x m ->
    E.eval_expr e m = E.eval_expr (match ABool.assoc e a with Some v => v | _ => x end) m).
   intros; unfold valid in *.
   assert (X:= H0 _ e0); destruct (ABool.assoc e0 a0); simpl in *; trivial.

   generalize a m H; clear H a m; induction e using E.expr_ind2 with 
    (Pl := fun lt args =>
     forall a (m:Mem.t k),
      valid a m ->
      E.eval_args (dmap _ (norm_expr a) args) m = E.eval_args args m);
    simpl; intros; trivial; try 
     match goal with
      |- _ = E.eval_expr (match _ with Some _ => _ | None => ?e end) _ =>
       refine (H0 _ e e _ _ _ _ (refl_equal _)) end; trivial.
   refine (H0 _ (E.Eop op args) (E.Eop op (dmap E.expr (norm_expr a) args))  a k m H _).
   simpl; unfold E.eval_args in IHe; rewrite <- (IHe a); trivial.
   refine (H0 _ (E.Eexists v e1 e2) (E.Eexists v (norm_expr (remove v a) e1) (norm_expr a e2))  a k m H _).
   simpl; rewrite <- IHe2; clear IHe2 H0; trivial.
   induction (E.eval_expr e2 m); simpl; trivial.
   rewrite <- IHi, <- IHe1; trivial.
   apply remove_update; trivial.
   refine (H0 _ (E.Eforall v e1 e2) (E.Eforall v (norm_expr (remove v a) e1) (norm_expr a e2))  a k m H _).
   simpl; rewrite <- IHe2; clear IHe2 H0; trivial.
   induction (E.eval_expr e2 m); simpl; trivial.
   rewrite <- IHi, <- IHe1; trivial.
   apply remove_update; trivial.
   refine (H0 _ (E.Efind v e1 e2) (E.Efind v (norm_expr (remove v a) e1) (norm_expr a e2))  a k m H _).
   simpl; rewrite <- IHe2; clear IHe2 H0; trivial.
   unfold find_default.
   replace (find (fun v0 : T.interp k t => E.eval_expr e1 (m {!v <-- v0!})) (E.eval_expr e2 m))
   with (find (fun v0 : T.interp k t => E.eval_expr (norm_expr (remove v a) e1) (m {!v <-- v0!})) (E.eval_expr e2 m)).
   trivial.
   induction (E.eval_expr e2 m); simpl; trivial.
   rewrite <- IHi, <- IHe1; trivial.
   apply remove_update; trivial.
   rewrite <- IHe; trivial; rewrite IHe0; trivial.
  Qed.

  Lemma valid_assign : forall k t (x:Var.var t) e a (m:Mem.t k), 
   valid a m ->
   valid (add_assign x e (remove x a))
   (m {! x <-- E.eval_expr e m !}).
  Proof.
   unfold add_assign; intros.
   assert (UU: valid (remove x a) m)
    by (apply valid_le with a; auto using remove_le).
   case_eq (Vset.mem x (fv_expr (eval_e e (remove x a)))).
   intros; apply remove_update; trivial.
   unfold valid; simpl; intros.
   unfold ABool.assoc; simpl.
   assert (X:=E.eqb_spec_dep e0 x); destruct (E.eqb e0 x).
   inversion X; subst.
   rewrite (T.inj_pair2 H4); simpl.
   case_eq (T.eq_dec t t); intros.
   rewrite (T.UIP_refl e1); simpl.
   rewrite Mem.get_upd_same.
   rewrite (valid_eval_e e UU).
   apply EqObs_e_fv_expr.
   apply req_mem_upd_disjoint; trivial.
   simpl; trivial.
   refine (remove_update _ _ H e0).
  Qed.

  Lemma add_test_morph : forall x y : E.expr T.Bool,
   Eeq x y ->
   forall (y0 : bool) (x0 y1 : A.t),
   A.eq x0 y1 -> A.eq (add_test x y0 x0) (add_test y y0 y1).  
  Proof.
   unfold Eeq, add_test; intros e1 e2 H b a1 a2 H0; subst.
   assert (R:A.eq (ABool.mkR e2 b :: a1) (ABool.mkR e2 b :: a2)).
   unfold A.eq, ABool.eqb.
   apply Eset.forallb_complete; intros; unfold ABool.eq_assoc,ABool.assoc; simpl.
   rewrite (H:x = y).
   case_eq (E.eqb y e2); intros; trivial.
   case_eq (E.eqb x e2); intros.
   apply ABool.oeeqb_refl.
   rewrite oeeqb_oeeq. 
   change (oeeq (ABool.assoc x a1) (ABool.assoc x a2)).    
   rewrite H0; apply oeeq_refl.

   unfold A.eq, ABool.eqb in H0.
   destruct (is_true_dec (Eset.mem (ET.mkE e2) (Eset.union (ABool.get_exprs a1) (ABool.get_exprs a2)))).
   assert (WW: forall x y, x = y -> ABool.eq_assoc a1 a2 x = ABool.eq_assoc a1 a2 y).
   intros; subst; trivial.
   assert (XX:= Eset.forallb_correct _ WW _ H0 (ET.mkE e2) H).
   unfold ABool.eq_assoc in XX; simpl in XX.
   destruct (ABool.assoc e2 a1); destruct (ABool.assoc e2 a2); trivial;
    try discriminate XX.
   case_eq (get_eq_expr b e2); intros; trivial.
   assert (ABool.assoc (ABool.r_e r) (ABool.mkR e2 b :: a1) = 
    ABool.assoc (ABool.r_e r) (ABool.mkR e2 b :: a2)).
   apply assoc_morph; trivial.
   red; trivial.
   rewrite H2; clear H2.
   destruct (ABool.assoc (ABool.r_e r) (ABool.mkR e2 b :: a2)); trivial.

   unfold A.eq, ABool.eqb.
   generalize (ABool.mkR e2 b :: a1) (ABool.mkR e2 b :: a2) R; intros.
   apply Eset.forallb_complete; intros; unfold ABool.eq_assoc,ABool.assoc; simpl.
   rewrite (H2:x = y).
   case_eq (E.eqb y (ABool.r_e r)); intros; trivial.
   case_eq (E.eqb x (ABool.r_e r)); intros.
   apply ABool.oeeqb_refl.
   rewrite oeeqb_oeeq. 
   change (oeeq (ABool.assoc x l) (ABool.assoc x l0)).    
   rewrite R0; apply oeeq_refl.

   assert (W:=ABool.get_exprs_assoc (ET.mkE e2) a1); simpl in W; rewrite W; clear W.
   assert (W:=ABool.get_exprs_assoc (ET.mkE e2) a2); simpl in W; rewrite W; clear W; trivial.
   case_eq (get_eq_expr b e2); intros; trivial.
   assert (ABool.assoc (ABool.r_e r) (ABool.mkR e2 b :: a1) = 
    ABool.assoc (ABool.r_e r) (ABool.mkR e2 b :: a2)).
   apply assoc_morph; trivial.
   red; trivial.
   rewrite H2; clear H2.
   destruct (ABool.assoc (ABool.r_e r) (ABool.mkR e2 b :: a2)); trivial.
   unfold A.eq, ABool.eqb.
   generalize (ABool.mkR e2 b :: a1) (ABool.mkR e2 b :: a2) R; intros.
   apply Eset.forallb_complete; intros; unfold ABool.eq_assoc,ABool.assoc; simpl.
   rewrite (H2:x = y).
   case_eq (E.eqb y (ABool.r_e r)); intros; trivial.
   case_eq (E.eqb x (ABool.r_e r)); intros.
   apply ABool.oeeqb_refl.
   rewrite oeeqb_oeeq. 
   change (oeeq (ABool.assoc x l) (ABool.assoc x l0)).    
   rewrite R0; apply oeeq_refl.

   intro Heq; apply H; auto with set.
   intro Heq; apply H; auto with set.
  Qed.

  Add Parametric Morphism : add_test
  with signature Eeq (t:=T.Bool) ==> @eq bool ==> A.eq ==> A.eq
  as add_test_morph_. 
  Proof.
   apply add_test_morph.
  Qed.

  Lemma get_eq_op_spec : forall k (m:Mem.t k) op args b r,
   get_eq_op b op args = Some r ->    
   eq_dep T.type (T.interp k) _ (E.eval_expr (E.Eop op args) m) T.Bool b ->
   E.eval_expr r.(ABool.r_e) m = E.eval_expr r.(ABool.r_c) m.
  Proof.
   intros k m op args b r H.
   destruct b; try discriminate H.
   destruct op; try discriminate H.
   simpl in H.
   T.dlist_inversion args; subst.
   injection H; clear H; intros; subst; simpl in *.
   unfold O.eval_op in H0; simpl in H0.
   assert (W:= T.i_eqb_spec k t (E.eval_expr x m) (E.eval_expr x0 m)).
   rewrite (T.eq_dep_eq H0) in W; trivial.
  Qed.

  Lemma get_eq_expr_spec : forall k (m:Mem.t k) t (e:E.expr t) b r,
   get_eq_expr b e = Some r ->
   eq_dep T.type (T.interp k) _ (E.eval_expr e m) T.Bool b ->
   E.eval_expr r.(ABool.r_e) m = E.eval_expr r.(ABool.r_c) m.
  Proof.
   intros k m; induction e using E.expr_ind2 with (Pl :=
    fun lt args =>
     forall ta (a:E.expr ta), @DIn _ E.expr ta a lt args ->
      forall b r, get_eq_expr b a = Some r ->
       eq_dep T.type (T.interp k) _ (E.eval_expr a m) T.Bool b ->
       E.eval_expr r.(ABool.r_e) m = E.eval_expr r.(ABool.r_c) m);
   simpl; intros; try discriminate.
   destruct op; try (eapply get_eq_op_spec; eauto; fail).
   T.dlist_inversion args; subst.
   unfold O.eval_op in H0; simpl in *.
   eapply IHe; eauto 3.
   rewrite <- (T.eq_dep_eq H0).
   destruct (E.eval_expr x m); constructor.
   elim H.
   destruct H; eauto.
   inversion H; clear H; subst.
   rewrite (T.inj_pair2 H5) in H0, H1.
   eapply IHe; eauto.
  Qed.

  Lemma valid_add_test : forall k a (m:Mem.t k) e b, 
   valid a m -> 
   E.eval_expr e m = b -> 
   valid (add_test e b a) m.
  Proof.
   unfold add_test; simpl; intros.
   destruct (ABool.assoc e a); auto.
   assert (valid (ABool.mkR e b :: a) m).
     unfold valid, ABool.assoc; simpl; intros.
     assert (XX:= E.eqb_spec_dep e0 e); destruct (E.eqb e0 e).
     inversion XX; subst.
     rewrite (T.inj_pair2 H4).
     case_eq (T.eq_dec T.Bool T.Bool); intros.
     rewrite (T.UIP_refl e1); simpl; trivial.
     simpl; trivial.
     apply (H _ e0).
   generalize (ABool.mkR e b :: a) H1; intros.
   generalize (@get_eq_expr_spec k m _ e b).
   case_eq (get_eq_expr b e); trivial.
    intros; case_eq (ABool.assoc (ABool.r_e r) l); trivial.
    intros; unfold valid, ABool.assoc; simpl; intros.
    assert (XX:= E.eqb_spec_dep e0  (ABool.r_e r)); destruct (E.eqb e0 (ABool.r_e r)).
    assert (WW := H4 _ (refl_equal _)); clear H4.
    destruct r; simpl in *; inversion XX; subst.
    rewrite (T.inj_pair2 H8).
    case_eq (T.eq_dec r_t r_t); intros.
    rewrite (T.UIP_refl e1); simpl; trivial.
    apply WW; trivial.
   simpl; trivial.
   apply (H2 _ e0).
  Qed.

  Lemma le_add_test : forall a e b, Ale a (add_test e b a).
  Proof.
   unfold add_test; intros.
   case_eq (ABool.assoc e a); intros; auto.
   apply Ale_refl.
   assert (Ale a (ABool.mkR e b :: a)).
   unfold Ale; intros.
   unfold ABool.assoc at 2; simpl.
   assert (XX:= E.eqb_spec_dep e0 e); destruct (E.eqb e0 e).
   inversion XX; subst.
   rewrite <- (T.inj_pair2 H3) in H.
   rewrite H; match goal with |- is_true (oele None ?x) => destruct x end; trivial. 
   apply oele_refl.
   generalize (ABool.mkR e b :: a) H0; intros.
   apply Ale_trans with l; trivial.
   case_eq (get_eq_expr b e); intros.
   case_eq (ABool.assoc (ABool.r_e r) l); intros.
   apply Ale_refl.
   unfold Ale; intros.
   unfold ABool.assoc at 2; simpl.
   assert (XX:= E.eqb_spec_dep e0 (ABool.r_e r)); destruct (E.eqb e0 (ABool.r_e r)).
   destruct r; simpl in *.
   inversion XX; subst.
   rewrite (T.inj_pair2 H7); rewrite H3; simpl.
   match goal with |- is_true (oele None ?x) => destruct x end; trivial. 
   apply oele_refl.
   apply Ale_refl.
  Qed.

  Definition eval_be := @eval_e T.Bool.

  Lemma valid_eval_be :  forall k (a:ABool.t) (m:Mem.t k) (e:E.expr T.Bool),
   valid a m -> E.eval_expr e m = E.eval_expr (eval_be e a) m.
  Proof.
   unfold eval_be; intros; rewrite <- valid_eval_e; auto.
  Qed.

 End EpEntries.

 Module Ep := MakeOpt EpEntries.

 Definition cp_test n E (pi:eq_refl_info E) e c :=
  let aT := EpEntries.add_test e true EpEntries.Abot in
  let aF := EpEntries.add_test e false EpEntries.Abot in
  let ct := Ep.optimize_pre n pi aT c in
  let cf := Ep.optimize_pre n pi aF c in
   (ct, cf).

 Lemma cp_test_correct_l : forall n E1 E2 (pi:eq_refl_info E1) e P c1 c2 Q c1t c1f,
  cp_test n pi e c1 = (c1t, c1f) ->
  equiv (P /-\ EP1 e) E1 c1t E2 c2 Q ->
  equiv (P /-\ ~-EP1 e) E1 c1f E2 c2 Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold cp_test; intros.
  injection H; clear H; intros.
  apply equiv_case1 with (EP1 e).
  unfold EP1; intros.
  destruct (E.eval_expr e x);[auto | right; autob].
  apply Ep.optimize_pre_l with (2:= H2); auto.
  unfold EP1; intros k m1 m2 (w1,w2); apply EpEntries.valid_add_test;
   [apply EpEntries.valid_bot | trivial ]. 
  apply Ep.optimize_pre_l with (2:= H); auto.
  unfold notR,EP1; intros k m1 m2 (w1,w2); apply EpEntries.valid_add_test;
   [apply EpEntries.valid_bot | autob ]. 
 Qed.
 
 Lemma cp_test_correct_r : forall n E1 E2 
(pi:eq_refl_info E2) e P c1 c2 Q c2t c2f,
  cp_test n pi e c2 = (c2t, c2f) ->
  equiv (P /-\ EP2 e) E1 c1 E2 c2t Q ->
  equiv (P /-\ ~-EP2 e) E1 c1 E2 c2f Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold cp_test; intros.
  injection H; clear H; intros.
  apply equiv_case1 with (EP2 e).
  unfold EP2; intros.
  destruct (E.eval_expr e y); [auto | right; autob].
  apply Ep.optimize_pre_r with (2:= H2); auto.
  unfold EP2; intros k m1 m2 (w1,w2); apply EpEntries.valid_add_test;
   [apply EpEntries.valid_bot | trivial ]. 
  apply Ep.optimize_pre_r with (2:= H); auto.
  unfold notR,EP2; intros k m1 m2 (w1,w2); apply EpEntries.valid_add_test;
   [apply EpEntries.valid_bot | autob ]. 
 Qed.

 Lemma cp_test_correct : forall n inv E1 E2 
  (pi:eq_inv_info inv E1 E2) (P:mem_rel) e c1 c2 Q c1t c2t c1f c2f, 
  cp_test n (refl1_info pi) e c1 = (c1t, c1f) ->
  cp_test n (refl2_info pi) e c2 = (c2t, c2f) ->
  (forall k (m1 m2:Mem.t k), P k m1 m2 -> E.eval_expr e m1 = E.eval_expr e m2) ->
  equiv (P /-\ EP1 e /-\ EP2 e) E1 c1t E2 c2t Q ->
  equiv (P /-\ ~-EP1 e /-\ ~-EP2 e) E1 c1f E2 c2f Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  intros.
  apply cp_test_correct_l with (1:= H);
   apply cp_test_correct_r with (1:= H0).
  eapply equiv_strengthen; [ | apply H2].
  unfold EP1, EP2, andR; intuition.
  apply equiv_False.
  unfold EP1, EP2, andR; intros k m1 m2 ((w1,w2),w3);
   apply w3; rewrite <-(H1 _ _ _ w1); trivial.
  apply equiv_False.
  unfold EP1, EP2, andR; intros k m1 m2 ((w1,w2),w3);
   apply w2; rewrite (H1 _ _ _ w1); trivial.
  rewrite andR_assoc; trivial.
 Qed.
 
 Lemma cp_test_correct_rem : forall n inv E1 E2 
  (pi:eq_inv_info inv E1 E2) I (P:mem_rel) e c1 c2 Q c1t c2t c1f c2f, 
  cp_test n (refl1_info pi) e c1 = (c1t, c1f) ->
  cp_test n (refl2_info pi) e c2 = (c2t, c2f) ->
  fv_expr e [<=] I ->
  equiv (req_mem_rel I P /-\ EP1 e /-\ EP2 e) E1 c1t E2 c2t Q ->
  equiv (req_mem_rel I P /-\ ~-EP1 e /-\ ~-EP2 e) E1 c1f E2 c2f Q ->
  equiv (req_mem_rel I P) E1 c1 E2 c2 Q.
 Proof.
  intros; eapply cp_test_correct; eauto 3.
  intros k m1 m2 (w1,w2); apply EqObs_e_fv_expr.
  apply req_mem_weaken with (2:= w1); trivial.
 Qed.

 Definition ep_eq n E (pi:eq_refl_info E) t (e1 e2:E.expr t) c :=
  let a := EpEntries.add_test (e1 =?= e2) true EpEntries.Abot in
   Ep.optimize_pre n pi a c.

 Lemma ep_correct_l : forall n E1 E2 (pi:eq_refl_info E1) t (e1 e2:E.expr t) (P:mem_rel) c1 c2 Q c1',
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m1) ->
  ep_eq n pi e1 e2 c1 = c1' ->
  equiv P E1 c1' E2 c2 Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold ep_eq; intros.
  apply Ep.optimize_pre_l with (2:= H0); auto.
  intros; apply EpEntries.valid_add_test.
  apply EpEntries.valid_bot.
  simpl; unfold O.eval_op; simpl.
  generalize (T.i_eqb_spec k t (E.eval_expr e1 m1) (E.eval_expr e2 m1));
   destruct (T.i_eqb k t (E.eval_expr e1 m1) (E.eval_expr e2 m1)); intros; trivial.
  elim H3; eapply H; eauto.
 Qed.
 
 Lemma ep_correct_r : forall n E1 E2 
  (pi:eq_refl_info E2) t (e1 e2:E.expr t) (P:mem_rel) c1 c2 Q c2',
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m2 = E.eval_expr e2 m2) ->
  ep_eq n pi e1 e2 c2 = c2' ->
  equiv P E1 c1 E2 c2' Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold ep_eq; intros.
  apply Ep.optimize_pre_r with (2:= H0); auto.
  intros; apply EpEntries.valid_add_test.
  apply EpEntries.valid_bot.
  simpl; unfold O.eval_op; simpl.
  generalize (T.i_eqb_spec k t (E.eval_expr e1 m2) (E.eval_expr e2 m2));
   destruct (T.i_eqb k t (E.eval_expr e1 m2) (E.eval_expr e2 m2)); intros; trivial.
  elim H3; eapply H; eauto.
 Qed.

 Lemma ep_correct_para : forall n inv E1 E2 
  (pi:eq_inv_info inv E1 E2) t (e1 e2:E.expr t) (P:mem_rel) c1 c2 Q c1' c2',
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m1 /\
   E.eval_expr e1 m2 = E.eval_expr e2 m2) ->
  ep_eq n (refl1_info pi) e1 e2 c1 = c1' ->
  ep_eq n (refl2_info pi) e1 e2 c2 = c2' ->
  equiv P E1 c1' E2 c2' Q ->
  equiv P E1 c1 E2 c2 Q.
 Proof.
  intros.
  apply ep_correct_l with (2:= H0).
  intros k m1 m2 HP; destruct (H _ _ _ HP); trivial.
  apply ep_correct_r with (2:= H1); trivial.
  intros k m1 m2 HP; destruct (H _ _ _ HP); trivial.
 Qed.

End Make.