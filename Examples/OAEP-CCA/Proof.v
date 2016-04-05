(** * Proof.v: Exact IND-CCA security of the OAEP padding scheme *)

Set Implicit Arguments.

Require Export Extension.
Require Import Bitstrings.
Require Import ClassicalChoice.

Ltac omega' :=
 change Ent.T.List with T.List in *;
  change Ent.T.Pair with T.Pair in *;
   change Ent.T.User with T.User in *;
    change Ent.T.Nat  with T.Nat in *; 
     change Ent.T.Bool with T.Bool in *;
     omega.

Close Scope nat_scope.

(* TODO: Move these generic lemmas somewhere else *)
Lemma Uabs_diff_le_plus : forall a b c, 
 Uabs_diff a b <= c -> a <= b + c.
Proof.
 intros.
 apply (Ule_total a b); [auto | | ]; intros.
 apply Ole_trans with (1:=H0); auto.
 rewrite Uabs_diff_sym, Uabs_diff_compat_le in H; [ | trivial].
 intros; apply Ole_trans with (b + (a - b)); auto.
Qed.

Lemma Uabs_diff_0_eq : forall a b, 
 Uabs_diff a b <= 0 -> a == b.
Proof.
 intros.
 apply (Ule_total a b); [auto | | ]; intros; 
  [ | rewrite Uabs_diff_sym in H];
  (split; trivial;
   rewrite Uabs_diff_compat_le in H; [ | trivial];
    apply Uminus_zero_le; split; trivial).
Qed.

Lemma BVxor_eq : forall (n : nat) (v1 v2 : vector bool n), 
 BVxor n v1 v2 = Bvect_false n -> v1 = v2.
Proof.
 intros.
 rewrite <- (BVxor_0_r v2), <- H, BVxor_comm.
 rewrite BVxor_assoc, BVxor_nilpotent, BVxor_0_r; trivial.
Qed.

Lemma split_append_mem : forall k t t0 (i:T.interp k t) (i0:T.interp k t0) i1,
 fst (O.split_assoc (T.i_eqb k t i) i0 i1) ++
 (if existsb (fun p => T.i_eqb k t i (fst p)) i1 
  then (i, fst (snd (O.split_assoc (T.i_eqb k t i) i0 i1))) :: 
           snd (snd (O.split_assoc (T.i_eqb k t i) i0 i1))
  else snd (snd (O.split_assoc (T.i_eqb k t i) i0 i1))) = i1.
Proof.
 induction i1; simpl; intros; trivial.
 case_eq (T.i_eqb k t i (fst a)); simpl; intros.
 apply is_true_Ti_eqb in H; rewrite H; destruct a; trivial.
 rewrite IHi1; trivial.
Qed.

Lemma not_mem_snd_split : forall k t t0 (i:T.interp k t0) (i0:T.interp k t) i1,
 ~existsb (fun p => T.i_eqb k t i0 (fst p)) i1 ->
 snd (snd (O.split_assoc (T.i_eqb k t i0) i i1)) = nil.
Proof.
 induction i1; simpl; intros; trivial.
 destruct (T.i_eqb k t i0 (fst a)). 
 elim H; trivial.
 simpl; apply IHi1; trivial.
Qed.

Lemma not_mem_fst_split : forall k t t0 (i:T.interp k t0) (i0:T.interp k t) i1,
 ~existsb (fun p => T.i_eqb k t i0 (fst p)) i1 ->
 fst (O.split_assoc (T.i_eqb k t i0) i i1) = i1.
Proof.
 induction i1; simpl; intros; trivial.
 destruct (T.i_eqb k t i0 (fst a)).
 elim H; trivial.
 simpl; rewrite IHi1; trivial.
Qed.

Lemma assoc_app : forall k tr tv (v:T.interp k tv) r l1 l2, 
 O.assoc (T.i_eqb k tr r) v (l1 ++ l2) =
 if existsb (fun p => (T.i_eqb k tr r (fst p))) l1 
 then O.assoc (T.i_eqb k tr r) v l1 else O.assoc (T.i_eqb k tr r) v l2.
Proof.
 unfold O.assoc; induction l1; simpl; intros; trivial.
 destruct (T.i_eqb k tr r (fst a)); trivial.
Qed.

Lemma assoc_upd_same : forall k t t0 (i:T.interp k t) (i0 p:T.interp k t0) i1,
 O.assoc (T.i_eqb k t i) i0 (O.upd (T.i_eqb k t) i p i1) = p.
Proof. 
 unfold O.assoc; induction i1; simpl.
 rewrite Ti_eqb_refl; trivial.
 destruct a.
 case_eq (T.i_eqb k t i i2); intros Heq; simpl; rewrite Heq; trivial.
Qed.

Lemma assoc_upd_diff : forall k t t0 (i i':T.interp k t),
 i <> i' ->
 forall (i0 p:T.interp k t0) i1,
  O.assoc (T.i_eqb k t i) i0 (O.upd (T.i_eqb k t) i' p i1) =
  O.assoc (T.i_eqb k t i) i0 i1.
Proof. 
 unfold O.assoc; intros k t t0 i i' H;
 rewrite <- is_true_Ti_eqb, not_is_true_false in H.
 induction i1; simpl. 
 rewrite H; trivial.
 destruct a; simpl.
 case_eq (T.i_eqb k t i i2); intros Heq; simpl.
 change (is_true (T.i_eqb k t i i2)) in Heq.
 rewrite is_true_Ti_eqb in Heq; subst.
 case_eq (T.i_eqb k t i' i2); intros Heq1; simpl.
 change (is_true (T.i_eqb k t i' i2)) in Heq1.
 rewrite is_true_Ti_eqb in Heq1; subst.
 rewrite Ti_eqb_refl in H; discriminate.
 rewrite Ti_eqb_refl; trivial.
 case_eq (T.i_eqb k t i' i2); intros Heq1; simpl; rewrite Heq; trivial.
Qed.

Lemma filter_morph : forall A (f1 f2:A->bool),
 (forall a, f1 a = f2 a) ->
 forall l, filter f1 l = filter f2 l.
Proof.
 induction l; simpl; intros; trivial.
 rewrite IHl, H; trivial.
Qed.

Lemma existsb_assoc : forall k t1 t2 x 
 (def:T.interp k t2) (l: list (T.interp k t1 * T.interp k t2)),
 existsb (fun p : T.interp k t1 * T.interp k t2 => T.i_eqb k t1 x (fst p)) l ->
 In (x, O.assoc (T.i_eqb k t1 x) def l) l.
Proof.
 induction l; simpl; intros.
 discriminate.
 unfold O.assoc; simpl.
 match type of H with 
  is_true (orb ?x _) => 
  generalize H; clear H; case_eq x; intros Heq H; [change (is_true x) in Heq | ] 
 end.
 rewrite is_true_Ti_eqb in Heq; subst; destruct a; auto.
 right; apply IHl; trivial.
Qed.

Lemma existsb_find_default : forall k t1 t2 x 
 (def:T.interp k t2) (def':T.interp k (T.Pair t1 t2)) 
 f (l: list (T.interp k t1 * T.interp k t2)),
 existsb (fun p : T.interp k t1 * T.interp k t2 => T.i_eqb k t1 x (fst p)) l ->
 is_true (f (x, O.assoc (T.i_eqb k t1 x) def l)) ->
 (forall a, x <> (fst a) -> f a = false) ->
 find_default f l def' = (x, O.assoc (T.i_eqb k t1 x) def l).
Proof.
 unfold find_default; induction l; simpl; intros.
 discriminate.
 unfold O.assoc in *; simpl in *.
 match type of H with 
  is_true (orb ?x _) => 
  generalize H H0; clear H H0; case_eq x; intros Heq H H0; 
   [change (is_true x) in Heq | ] 
 end.
 rewrite is_true_Ti_eqb in Heq; subst; destruct a; simpl in *.
 rewrite H0; trivial.
 rewrite <- not_is_true_false, is_true_Ti_eqb in Heq.
 rewrite (H1 _ Heq).
 apply IHl; auto.
Qed.

Lemma existsb_morph : forall A (f1 f2:A -> bool),
 (forall a, f1 a = f2 a) ->
 forall l, existsb f1 l = existsb f2 l.
Proof.
 induction l; simpl; intros; trivial.
 rewrite IHl, H; trivial.
Qed.

Lemma existsb_upd_same : forall k t t0 (i:T.interp k t) (i0:T.interp k t0) i1,
 existsb (fun p => T.i_eqb k t i (fst p)) (O.upd (T.i_eqb k t) i i0 i1).
Proof.
 induction i1; simpl.
 rewrite Ti_eqb_refl; trivial.
 destruct a.
 case_eq (T.i_eqb k t i i2); intros Heq; simpl; rewrite Heq; trivial.
Qed.

Lemma existsb_upd_diff : forall k t t0 (i i':T.interp k t),
 i <> i' ->
 forall (i0:T.interp k t0) i1,
  existsb (fun p => T.i_eqb k t i (fst p)) (O.upd (T.i_eqb k t) i' i0 i1) =
  existsb (fun p => T.i_eqb k t i (fst p)) i1.
Proof.
 intros k t t0 i i' H;
 rewrite <- is_true_Ti_eqb, not_is_true_false in H.
 induction i1; simpl. 
 rewrite H; trivial.
 destruct a; simpl.
 case_eq (T.i_eqb k t i i2); intros Heq; simpl.
 change (is_true (T.i_eqb k t i i2)) in Heq.
 rewrite is_true_Ti_eqb in Heq; subst.
 case_eq (T.i_eqb k t i' i2); intros Heq1; simpl.
 change (is_true (T.i_eqb k t i' i2)) in Heq1.
 rewrite is_true_Ti_eqb in Heq1; subst.
 rewrite Ti_eqb_refl in H; discriminate.
 rewrite Ti_eqb_refl; trivial.
 case_eq (T.i_eqb k t i' i2); intros Heq1; simpl; rewrite Heq; trivial.
Qed.

Lemma length_upd : forall k t t0 (i:T.interp k t) (i0:T.interp k t0) i1,
 existsb (fun p => T.i_eqb k t i (fst p)) i1 ->
 length (O.upd (T.i_eqb k t) i i0 i1) = length i1.
Proof.
 induction i1; simpl; intros.
 discriminate.
 destruct a; simpl in *.
 destruct (T.i_eqb k t i i2); trivial.
 rewrite <- IHi1; trivial.
Qed.

Lemma add2_swap : forall x y z, 
 Vset.add x (Vset.add y z) [=] Vset.add y (Vset.add x z).
Proof.
 intros.
 rewrite VsetP.eq_spec; split;
  apply Vset.subset_complete; intro; repeat rewrite VsetP.add_spec; tauto.
Qed.

Lemma EqObs_post_trans_l : forall I E1 c1 E2 c2 E3 c3 O R X1 X2,
 depend_only_rel R X1 X2 ->
 EqObs I E1 c1 E2 c2 (Vset.union O X1) ->
 equiv (kreq_mem I) E2 c2 E3 c3 (req_mem_rel O R) ->
 equiv (kreq_mem I) E1 c1 E3 c3 (req_mem_rel O R).
Proof.
 intros.
 apply equiv_trans with (4:=H0) (5:=H1); auto.
 red; trivial.
 assert (W:=depend_only_req_mem_rel (X:=O) H).
 intros k2 x y z HH; apply W; [apply req_mem_sym | ]; trivial.
Qed.

Lemma EqObs_post_trans_r : forall I E1 c1 E2 c2 E3 c3 O R X1 X2,
 depend_only_rel R X1 X2 ->
 equiv (kreq_mem I) E1 c1 E2 c2 (req_mem_rel O R) ->
 EqObs I E2 c2 E3 c3 (Vset.union O X2) ->
 equiv (kreq_mem I) E1 c1 E3 c3 (req_mem_rel O R).
Proof.
 intros.
 apply equiv_trans with (4:=H0) (5:=H1); auto.
 red; trivial.
 assert (W:=depend_only_req_mem_rel (X:=O) H).
 intros k2 x y z HH HH'; red in W.
 apply W with (3:=HH); trivial.
Qed.

Lemma set_bad : forall k (m:Mem.t k) E Ev c (bad:Var.var T.Bool),
 Pr E c (m{!bad <-- false!}) Ev == Pr E ((bad <- false)::c) m Ev.
Proof.
 unfold Pr; intros.
 rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim; trivial.
Qed.

Lemma equiv_Meq_inv_Modify : forall E1 c1 E2 c2 (P:mem_rel) (M0 X1 X2:Vset.t),
 Modify E1 M0 c1 -> 
 Modify E2 M0 c2 ->
 depend_only_rel P X1 X2 -> 
 Vset.disjoint X1 M0 -> 
 Vset.disjoint X2 M0 ->
 equiv (Meq /-\ P) E1 c1 E2 c2 (kreq_mem M0) ->
 equiv (Meq /-\ P) E1 c1 E2 c2 (Meq /-\ P).
Proof.
 intros.
 apply equiv_union_Modify_pre with 
  (P1:=fun k m => True) (P2:=fun k m => True)
  (Q:=kreq_mem M0) (X1:=M0) (X2:=M0).
 split; trivial.
 unfold Meq; intros k m1 m2 m1' m2' (Heq, W1) W2; subst; split.
 apply req_mem_eq; trivial.
 apply H1 with m2 m2; trivial.
 apply req_mem_sym; apply req_mem_update_disjoint; trivial.
 apply req_mem_sym; apply req_mem_update_disjoint; trivial.
 apply Modify_Modify_pre; trivial.
 apply Modify_Modify_pre; trivial.
 trivial.
Qed.

Lemma zero_mu : forall (A:Type) (d:Distr A) f, 
 (forall x, 0 == f x) -> 0 == mu d f.
Proof.
 intros; rewrite <- (mu_0 d).
 apply mu_stable_eq; apply (ford_eq_intro H).
Qed.

Lemma req_mem_rel_upd_in : forall k (m1 m2:Mem.t k) I P X1 X2,
 req_mem_rel I P k m1 m2 ->
 depend_only_rel P X1 X2 ->
 forall t (x:Var.var t) v1 v2, v1 = v2 ->
  negb (Vset.mem x X1) -> negb (Vset.mem x X2) ->
  req_mem_rel (Vset.add x I) P k (m1 {!x <-- v1!}) (m2 {!x <-- v2!}).
Proof.
 intros k m1 m2 I P X1 X2 (H1, H2) H3 t x v1 v2 H4 H5 H6; rewrite H4; split.
 apply req_mem_update; trivial.
 apply (H3 k m1 m2); [ | | trivial];
 apply req_mem_upd_disjoint; rewrite <- is_true_negb_false; trivial.
Qed.


Definition my_build_dinv_info_rm (n:positive) inv (E1 E2:env) 
 (piit1:eq_inv_info trueR E1 E1) 
 (piit2:eq_inv_info trueR E2 E2)
 (pii:eq_inv_info inv E1 E2) 
 t (f:Proc.proc t) I O R1 R2 :
 option (dproc_eq_inv_info E1 E2 f) :=
 match build_refl_info_rm n (refl1_info piit1) f R1,
  build_refl_info_rm n (refl1_info piit2) f R2 with
  | Some eqr1, Some eqr2 => 
    let res1 := proc_res E1 f in
    let res2 := proc_res E2 f in
     if E.eqb res1 res2 then 
      let fv := fv_expr res1 in
      let output := get_globals O in
      let input := get_globals I in
      let local := get_locals I in
      if fv [<=?] O then
       if local [<=?] Vset_of_var_decl (proc_params E1 f) then
        if local [<=?] Vset_of_var_decl (proc_params E2 f) then
         Some (Build_dproc_eq_inv_info eqr1 eqr2 input local output)
        else None
       else None
      else None
     else None
  | _, _ => None
 end.

Lemma my_build_sinv_info_rm : forall (n:positive) inv (E1 E2:env) 
 (piit1:eq_inv_info trueR E1 E1) 
 (piit2:eq_inv_info trueR E2 E2)
 (pii:eq_inv_info inv E1 E2)
 t (f:Proc.proc t) I O R1 R2 d,
 EqObsInv inv I E1 (proc_body E1 f) E2 (proc_body E2 f) O ->
 my_build_dinv_info_rm n piit1 piit2 pii f I O R1 R2 = Some d ->
 sproc_eq_inv_info inv d.
Proof.
 intros n0 inv E1' E2' piit1 piit2 pii t f1 I O R1 R2 d HEO.
 unfold my_build_dinv_info_rm.
 case_opt; intros eqr1 _.
 case_opt; intros eqr2 _.
 case_opt; intros Hres.
 case_opt; intros Hfv.
 case_opt; intros Hp1.  
 case_opt; intros Hp2.
 intros Heq; injection Heq; clear Heq; intros; subst. 
 constructor; simpl; trivial.
 apply get_globals_spec.
 apply get_globals_spec.
 exists (get_locals O); split; [apply get_locals_spec | split].
 rewrite VsetP.union_sym; repeat rewrite union_locals_globals; trivial.
 generalize (E.eqb_spec (proc_res E1' f1) (proc_res E2' f1));
  rewrite Hres; intros Heq; rewrite <- Heq.
 rewrite union_locals_globals.
 eapply EqObs_e_strengthen; auto using EqObs_e_fv_expr;
  apply VsetP.subset_trans with (1:= Hfv); auto with set.
Qed.

Definition my_build_inv_info_rm (n:positive) inv (E1 E2:env) 
 (piit1:eq_inv_info trueR E1 E1) 
 (piit2:eq_inv_info trueR E2 E2) 
 (pii:eq_inv_info inv E1 E2) 
 t (f:Proc.proc t) (I O R1 R2:Vset.t) 
 (HEO:EqObsInv inv I E1 (proc_body E1 f) E2 (proc_body E2 f) O) :
 option (proc_eq_inv_info inv E1 E2 f).
 intros n0 inv E1' E2' piit1 piit2 pii t0 f1 I O R1 R2 HEO.
 generalize (fun d => 
  @my_build_sinv_info_rm n0 inv E1' E2' piit1 piit2 pii t0 f1 I O R1 R2 d HEO).
 destruct (my_build_dinv_info_rm n0 piit1 piit2 pii f1 I O R1 R2);
 intros; [ | exact None].
 exact (Some (@Build_proc_eq_inv_info inv E1' E2' t0 f1 d (H _ (refl_equal _)))).
Defined.

Definition my_add_info inv E1 E2 fr (f:Proc.proc fr) R1 R2 
 (piit1:eq_inv_info trueR E1 E1) 
 (piit2:eq_inv_info trueR E2 E2)
 (pii:eq_inv_info inv E1 E2)
 I O 
 (HEO: EqObsInv inv I E1 (proc_body E1 f) E2 (proc_body E2 f) O) :=
 match @my_build_inv_info_rm 
  100%positive inv E1 E2 piit1 piit2 pii fr f I O R1 R2 HEO with
  | Some i => @add_pii_info inv E1 E2 fr f i pii
  | _ => pii
 end.

Lemma equiv_inv_bad : forall k (E:env) ebad count max f c c',
 equiv Meq E c' E c 
 (req_mem_rel (fv_expr (count <=! max)) ((EP1 ebad) |-> (EP2 ebad))) ->
 inv_bad E (@bad_K k ebad count max f) c -> 
 inv_bad E (@bad_K k ebad count max f) c'.
Proof.
 unfold inv_bad; intros.
 eapply Ole_trans; [ | apply H0].
 apply equiv_deno_le with (1:=H) (m1:=m) (m2:=m); [ | trivial].
 unfold bad_K, Fmult, req_mem_rel, andR, impR, Bad, T, 
  EP1, EP2, EP, fplus, charfun, restr, UP.finv, fone.
 intros m1 m2 (Heq, Himp).
 simpl in Heq; rewrite (depend_only_fv_expr _ Heq).
 destruct (E.eval_expr ebad m1).
 rewrite Himp; repeat Usimpl; auto.
 assert (W: m1 =={ fv_expr count} m2).
 eapply req_mem_weaken; eauto.
 unfold fv_expr; simpl; apply fv_expr_rec_subset.
 rewrite (depend_only_fv_expr (t:=T.Nat) count W); clear W.
 assert (W: m1 =={ fv_expr max0} m2).
 eapply req_mem_weaken; eauto.
 unfold fv_expr; simpl.
 fold (fv_expr_extend max0 (fv_expr_rec Vset.empty count)).
 rewrite union_fv_expr_spec; unfold fv_expr; auto with set.
 rewrite (depend_only_fv_expr (t:=T.Nat) max0 W); trivial.
 destruct (E.eval_expr ebad m2); repeat Usimpl; auto.
Qed.

Open Scope nat_scope.

Lemma nth_existsb : forall (A:Type) (f:A-> bool) def l,
 existsb f l -> exists i, i < length l /\ f (nth i l def).
Proof.
 induction l; simpl; intros.
 discriminate.
 rewrite is_true_orb in H; destruct H.
 exists 0; auto with arith.
 destruct (IHl H) as (i, (H1, H2)); exists (Datatypes.S i); auto with arith.
Qed.

Lemma is_true_leb : forall n m, leb n m <-> n <= m.
Proof.
 split; unfold is_true; auto using leb_complete, leb_correct.
Qed.
(***)


Notation BS_n        := (T.User Bitstring_n).
Notation BS_k1       := (T.User Bitstring_k1).
Notation BS_k0       := (T.User Bitstring_k0).
Notation BS_nk1      := (T.Pair BS_n BS_k1).
Notation BS_k        := (T.Pair BS_nk1 BS_k0).
Notation Tbnk1       := (T.Pair T.Bool BS_nk1).
Notation Tk0bnk1     := (T.Pair BS_k0 Tbnk1).
Notation T_assoc_b   := (T.List Tk0bnk1).
Notation Tbk0        := (T.Pair T.Bool BS_k0).
Notation Tnk1bk0     := (T.Pair (T.Pair BS_n BS_k1) Tbk0).
Notation T_assoc_b_H := (T.List Tnk1bk0).

Notation "'Etl' p"          := (E.Eop (O.Otl _) {p}) (at level 40).
Notation "'Ehd' p"          := (E.Eop (O.Ohd _) {p}) (at level 40).
Notation "x 'Esplit' p"     := (E.Eop (O.Osplit _ _) {x, p}) (at level 40).
Notation "c 'Upd' a '<|' b" := (E.Eop (O.Oupd _ _) {a,b,c}) (at level 40).
Notation " x '|x2|' y "     := ( ((Efst x |x| Efst y) | (Esnd x |x| Esnd y)))
 (at level 50, left associativity).


Section OPTIMISTIC_SAMPLING.

 Variable bs : Ut.t.
 Variable x : Var.var (T.User bs).
 Variable y : Var.var (T.User bs).
 Variable z : E.expr (T.User bs).

 Hypothesis x_y : Var.mkV x <> y.
 Hypothesis x_z : Vset.mem x (fv_expr z) = false.
 Hypothesis y_z : Vset.mem y (fv_expr z) = false.
 
 Local Notation "'{0,1}^bs'" := (E.Duser (Usupport T.User bs)).

 Lemma optimistic_sampling : forall E, 
  EqObs (fv_expr z)
  E [x <$- {0,1}^bs; y <- x |x| z] 
  E [y <$- {0,1}^bs; x <- y |x| z]
  (Vset.add x (Vset.add y (fv_expr z))).
 Proof.
  intros E.
  apply equiv_cons with
   (kreq_mem (fv_expr z) /-\ fun _ m1 m2 => m1 x = E.eval_expr (y |x| z) m2).

  eapply equiv_strengthen;
  [ | apply equiv_random_permut with 
   (f:=fun k (m1 m2:Mem.t k) v => BVxor _ (E.eval_expr z m2) v)].
  unfold kreq_mem, andR; split.

  apply PermutP_weaken with 
   (fun v1 v2 => v1 = BVxor (Ut.len k bs) v2 (E.eval_expr z m2)).
  intros; subst; apply BVxor_comm.

  apply PermutP_bs_support_xor.
  intros; split.
  apply req_mem_trans with m1.
  apply req_mem_sym; apply req_mem_upd_disjoint; trivial.
  apply req_mem_trans with m2; trivial.
  apply req_mem_upd_disjoint; trivial. 
 
  rewrite Mem.get_upd_same, BVxor_comm.
  simpl; unfold O.eval_op; simpl.
  rewrite Mem.get_upd_same.
  assert (H1:m2 =={fv_expr z} m2{!y <-- v!}).
  apply req_mem_upd_disjoint; trivial.
  rewrite depend_only_fv_expr_subset with (2:=H1); trivial.
  apply VsetP.subset_refl.

  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold upd_para, Meq, andR; intros k m1 m2 (H1, H2).
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op. 
  intros ? ? Hn.
  rewrite VsetP.add_spec in Hn. 
  rewrite VsetP.add_spec in Hn.
  decompose [or] Hn; clear Hn.
  inversion H; simpl. 
  rewrite Mem.get_upd_diff, Mem.get_upd_same; auto.
  inversion H0; simpl. 
  rewrite Mem.get_upd_same, Mem.get_upd_diff; auto.
  rewrite H2.
  simpl; unfold O.eval_op; simpl.
  
  rewrite BVxor_assoc.
  rewrite depend_only_fv_expr_subset with (2:=H1); [ | apply VsetP.subset_refl].
  rewrite BVxor_nilpotent, BVxor_0_r; trivial. 
  repeat rewrite Mem.get_upd_diff.
  auto.
  intro Heq; rewrite <- Heq in H0; rewrite H0 in x_z; discriminate.
  intro Heq; rewrite <- Heq in H0; rewrite H0 in y_z; discriminate.
 Qed.

 Lemma optimistic_sampling_inv : forall E, 
  EqObs (fv_expr z)
  E [x <$- {0,1}^bs; y <- z |x| x] 
  E [y <$- {0,1}^bs; x <- z |x| y]
  (Vset.add x (Vset.add y (fv_expr z))).
 Proof.
  intros E; eapply EqObs_trans; 
   [eapply EqObs_trans; [ | apply (optimistic_sampling E)] | ].
  apply equiv_cons with (kreq_mem (Vset.add x (fv_expr z))).
  eapply equiv_strengthen; [ | apply equiv_random].
  split; [red; trivial | red; red; intros].
  apply req_mem_update; trivial.
  eapply equiv_strengthen; [ | apply equiv_assign].
  red; red; intros.
  replace (E.eval_expr (t:=T.User bs) (z |x| x) m1) with 
   (E.eval_expr (x |x| z) m2).
  rewrite add2_swap; apply req_mem_update; trivial.
  simpl; unfold O.eval_op; simpl; rewrite BVxor_comm.
  rewrite (@depend_only_fv_expr _ z k m1 m2), (H _ x); auto with set.
  eapply req_mem_weaken; eauto with set.
  apply equiv_cons with (kreq_mem (Vset.add y (fv_expr z))).
  eapply equiv_strengthen; [ | apply equiv_random].
  split; [red; trivial | red; red; intros].
  apply req_mem_update; trivial.
 eapply equiv_strengthen; [ | apply equiv_assign].
  red; red; intros.
  replace (E.eval_expr (t:=T.User bs) (y |x| z) m1) with 
   (E.eval_expr (z |x| y) m2).
  apply req_mem_update; trivial.
  simpl; unfold O.eval_op; simpl; rewrite BVxor_comm.
  rewrite depend_only_fv_expr, (H _ y); auto with set.
  eapply req_mem_weaken; eauto with set.
 Qed.

End OPTIMISTIC_SAMPLING.


(** ** Global Variables *)
Notation g_a       := (Var.Gvar T.Nat 1).
Notation R'        := (Var.Gvar BS_k0 2). 
Notation GR'       := (Var.Gvar BS_nk1 3).
Notation LH        := (Var.Gvar (T.List (T.Pair BS_nk1 BS_k0)) 4).
Notation S'        := (Var.Gvar BS_nk1 5).
Notation HS'       := (Var.Gvar BS_k0 6).
Notation LG        := (Var.Gvar (T.List (T.Pair BS_k0 BS_nk1)) 7).
Notation LD        := (Var.Gvar (T.List (T.Pair T.Bool BS_k)) 8).
Notation Ydef      := (Var.Gvar T.Bool 9).
Notation bad       := (Var.Gvar T.Bool 11).
Notation bad1      := (Var.Gvar T.Bool 12).
Notation bad2      := (Var.Gvar T.Bool 13).
Notation bad3      := (Var.Gvar T.Bool 14).
Notation bad4      := (Var.Gvar T.Bool 15).
Notation Y'        := (Var.Gvar BS_k 16).
Notation T'        := (Var.Gvar BS_k0 17).
Notation ST'       := (Var.Gvar BS_k 18).
Notation Dc        := (Var.Gvar T.Nat 19). 
Notation Gc        := (Var.Gvar T.Nat 20). 
Notation GR'n      := (Var.Gvar BS_n 21).
Notation GR'k1     := (Var.Gvar BS_k1 22).
Notation LG'       := (Var.Gvar (T.List (T.Pair BS_k0 BS_nk1)) 23).
Notation aux       := (Var.Gvar Tk0bnk1 24).
Notation rGn_aux   := (Var.Gvar BS_n 25).
Notation rGk1_aux  := (Var.Gvar BS_k1 26).
Notation rGn_aux1  := (Var.Gvar BS_n 27).
Notation rGk1_aux1 := (Var.Gvar BS_k1 28).
Notation LGb       := (Var.Gvar T_assoc_b 29).
Notation LGb_hd    := (Var.Gvar T_assoc_b 30).
Notation LGb_tl    := (Var.Gvar T_assoc_b 31).
Notation LGb_hd_hd := (Var.Gvar T_assoc_b 32).
Notation LGb_hd_tl := (Var.Gvar T_assoc_b 33).
Notation LGb_tl_hd := (Var.Gvar T_assoc_b 34).
Notation LGb_tl_tl := (Var.Gvar T_assoc_b 35).
Notation LGb1      := (Var.Gvar T_assoc_b 36).
Notation LGbR1     := (Var.Gvar Tbnk1 37).
Notation LGbR2     := (Var.Gvar Tbnk1 38).
Notation auxH      := (Var.Gvar Tnk1bk0 39).
Notation rH_aux    := (Var.Gvar BS_k0 40).
Notation LHb       := (Var.Gvar T_assoc_b_H 41).
Notation LHb_hd    := (Var.Gvar T_assoc_b_H 42).
Notation LHb_tl    := (Var.Gvar T_assoc_b_H 43).
Notation LHb_hd_hd := (Var.Gvar T_assoc_b_H 44).
Notation LHb_hd_tl := (Var.Gvar T_assoc_b_H 45).
Notation LHb_tl_hd := (Var.Gvar T_assoc_b_H 46).
Notation LHb_tl_tl := (Var.Gvar T_assoc_b_H 47).
Notation LHb1      := (Var.Gvar T_assoc_b_H 48).
Notation rH_aux1   := (Var.Gvar BS_k0 49).
Notation LHbS      := (Var.Gvar (T.Pair T.Bool BS_k0) 50).
Notation HS'def    := (Var.Gvar T.Bool 51).
Notation LH'       := (Var.Gvar 
 (T.List (T.Pair (T.Pair (T.User Bitstring_n)
  (T.User Bitstring_k1)) (T.User Bitstring_k0))) 52).


(** ** Local Variables *)
Notation M         := (Var.Lvar (T.Pair BS_n BS_n) 1).
Notation Mb        := (Var.Lvar BS_n 2).
Notation b         := (Var.Lvar T.Bool 3).
Notation b'        := (Var.Lvar T.Bool 4).
Notation R         := (Var.Lvar BS_k0 5). 
Notation rG        := (Var.Lvar BS_nk1 6).
Notation S         := (Var.Lvar BS_nk1 7).
Notation rH        := (Var.Lvar BS_k0 8). 
Notation Me        := (Var.Lvar BS_n 9).
Notation Re        := (Var.Lvar BS_k0 10).
Notation Se        := (Var.Lvar BS_nk1 11).
Notation Te        := (Var.Lvar BS_k0 12).
Notation He        := (Var.Lvar BS_k0 13).
Notation Ge        := (Var.Lvar BS_nk1 14).
Notation Ye        := (Var.Lvar BS_k 15).
Notation st        := (Var.Lvar (T.Pair BS_nk1 BS_k0) 16).
Notation s         := (Var.Lvar BS_nk1 17).
Notation t         := (Var.Lvar BS_k0 18).
Notation h         := (Var.Lvar BS_k0 19).
Notation r         := (Var.Lvar BS_k0 20).
Notation g         := (Var.Lvar BS_nk1 21).
Notation m         := (Var.Lvar BS_nk1 22).
Notation mn        := (Var.Lvar (T.Pair T.Bool BS_n) 23).
Notation c         := (Var.Lvar BS_k 24).
Notation rGn       := (Var.Lvar BS_n 25).
Notation rGk1      := (Var.Lvar BS_k1 26).
Notation Radv      := (Var.Lvar BS_k0 27).
Notation rGadv     := (Var.Lvar BS_nk1 28).
Notation mnadv     := (Var.Lvar (T.Pair T.Bool BS_n) 29).
Notation cadv      := (Var.Lvar BS_k 30).
Notation bY        := (Var.Lvar (T.Pair T.Bool BS_k) 31).
Notation alpha     := (Var.Lvar BS_k 32).
Notation tc        := (Var.Lvar (T.Pair T.Bool BS_k) 33).
Notation sh        := (Var.Lvar (T.Pair BS_nk1 BS_k0) 34).
Notation rg        := (Var.Lvar (T.Pair BS_k0 BS_nk1) 35).
Notation sn        := (Var.Lvar BS_n 36).
Notation sk1       := (Var.Lvar BS_k1 37).
Notation lI        := (Var.Lvar
 (T.List (T.Pair (T.Pair (T.User Bitstring_n) (T.User Bitstring_k1))
  (T.User Bitstring_k0))) 38).


(** G oracle *)
Notation G := (Proc.mkP 1 (BS_k0 :: nil) BS_nk1).

Definition G_params : var_decl (Proc.targs G) := dcons _ R (dnil _).

Definition G_body0 :=
 [ 
  If !(R in_dom LG) 
  then [ rGn <$- {0,1}^n; rGk1 <$- {0,1}^k1; LG <- (R | (rGn|rGk1)) |::| LG ]
  else [ rGn <- Efst (LG[{R}]); rGk1 <- Esnd (LG[{R}]) ]
 ].
 
Definition G_res := (rGn | rGk1).


(** Wrapper for the G oracle for the adversary *)
Notation GAdv := (Proc.mkP 2 (BS_k0 :: nil) BS_nk1).

Definition GAdv_params : var_decl (Proc.targs GAdv) := dcons _ Radv (dnil _).

Definition GAdv_body0 := [ Gc <- 1 +! Gc; rGadv <c- G with {Radv} ].
 
Definition GAdv_res := rGadv.


(** H oracle *)
Notation H := (Proc.mkP 3 (BS_nk1 :: nil) BS_k0).

Definition H_params : var_decl (Proc.targs H) := dcons _ S (dnil _).

Definition H_body0 :=
 [ 
  If !(S in_dom LH) 
  then [ rH <$- {0,1}^k0; LH <- (S | rH) |::| LH ]
  else [ rH <- LH[{S}] ]
 ].

Definition H_res := rH.


(** Decryption oracle *)
Notation Dec := (Proc.mkP 4 (BS_k :: nil) (T.Pair T.Bool BS_n)).

Definition Dec_params : var_decl (Proc.targs Dec) := dcons _ c (dnil _).

Definition Dec_body0 :=
 [
  LD <- (Ydef | c) |::| LD;
  Dc <- 1 +! Dc;
  st <- ap_finv c;
  s <- Efst st;
  t <- Esnd st;
  h <c- H with {s};
  r <- t |x| h;
  g <c- G with {r};
  m <- s |x2| g;
  If Esnd m =?= zero_k1 
  then [ mn <- (true  | Efst m) ]
  else [ mn <- (false | one_n) ]
 ].

Definition Dec_res := mn.


(** Encryption algorithm *)
Notation Enc := (Proc.mkP 5 (BS_n :: nil) BS_k).

Definition Enc_params : var_decl (Proc.targs Enc) := dcons _ Me (dnil _).

Definition Enc_body :=
 [ 
  Re <$- {0,1}^k0;
  Ge <c- G with {Re};
  Se <- Ge |x2| (Me | zero_k1);
  He <c- H with {Se};
  Te <- He |x| Re;
  Ye <- ap_f (Se | Te)
 ].

Definition Enc_res := Ye.


(** Inverter (its body is given later) *) 
Notation Inverter := (Proc.mkP 6 (BS_k :: nil) (T.List (T.Pair BS_nk1 BS_k0))).

Definition I_params : var_decl (Proc.targs Inverter) := dcons _ Ye (dnil _).


(** Set Partial-Domain One-Wayness *)
Section SET_PARTIAL_DOMAIN_ONEWAY.

 Variable L   : Var.var (T.List (T.Pair BS_nk1 BS_k0)).
 Variable sh  : Var.var (T.Pair BS_nk1 BS_k0).
 Variable sn  : Var.var BS_n.
 Variable sk1 : Var.var BS_k1.
 Variable t   : Var.var BS_k0.
  
 Definition Gf :=
  [ 
   sn  <$- {0,1}^n;
   sk1 <$- {0,1}^k1;
   t   <$- {0,1}^k0;
   L <c- Inverter with {ap_f ((sn | sk1) | t)}
  ].

 Definition f_set_pd_ow := forall (m:forall k, Mem.t k) E, 
  Var.is_local sn  ->
  Var.is_local sk1 ->
  Var.is_local t   ->
  PPT_proc E Inverter ->
  lossless E (proc_body E Inverter) ->
  negligible (fun k => Pr E Gf (m k) (EP k ((sn|sk1) in_dom L))).

End SET_PARTIAL_DOMAIN_ONEWAY.


Section ADVERSARY_AND_PROOF.
 
 (** Specification of the adversary *)
 Variable env_adv : env.

 Notation A  := (Proc.mkP 7 nil (T.Pair BS_n BS_n)).
 Notation A' := (Proc.mkP 8 (BS_k :: nil) T.Bool).

 Definition A_params  : var_decl (Proc.targs A) := dnil _.
 Definition A'_params : var_decl (Proc.targs A') := dcons _ alpha (dnil _).

 Variable A_body  : cmd.
 Variable A'_body : cmd.

 Variable A_res  : E.expr (T.Pair BS_n BS_n).
 Variable A'_res : E.expr T.Bool.

 Definition mkENV H_body G_body Dec_body GA_body := 
  let EH := add_decl env_adv H H_params (refl_equal true) H_body H_res in
  let EG := add_decl EH G G_params (refl_equal true) G_body G_res in
  let ED := add_decl EG Dec Dec_params (refl_equal true) Dec_body Dec_res in
  let EGA := add_decl ED GAdv GAdv_params (refl_equal true) GA_body GAdv_res in
  let EE := add_decl EGA Enc Enc_params (refl_equal true) Enc_body Enc_res in
  let EA := add_decl EE A A_params (refl_equal true) A_body A_res in
   add_decl EA A' A'_params (refl_equal true) A'_body A'_res.

 (** IND-CCA game *)
 Definition G0 :=
  [
   Ydef <- false;
   LG <- Nil _;
   LH <- Nil _;
   LD <- Nil _;
   Dc <- 0;
   Gc <- 0;
   M <c- A with {};
   b <$- {0,1};
   If b then [ Mb <- Efst M ] else [ Mb <- Esnd M ];
   Y' <c- Enc with {Mb};
   Ydef <- true;
   b' <c- A' with {Y'}
  ].

 Definition E0 := mkENV H_body0 G_body0 Dec_body0 GAdv_body0.

 (** The adversary makes at most [qG] queries to the hash oracle [G],
     and [qD] queries to the decryption oracle [Dec] *)
 Hypothesis range_query : forall k (m:Mem.t k),
  range (EP k ((Gc <=! qG) && (Dc <=! qD) && !((true | Y') is_in LD))) 
  ([[G0]] E0 m).

 (** Oracles *)
 Definition PrOrcl := 
  PrSet.add (BProc.mkP Dec) 
  (PrSet.add (BProc.mkP GAdv) 
   (PrSet.singleton (BProc.mkP H))).

 (** Private procedures, not accessible to the adversary *)
 Definition PrPriv := 
  PrSet.add (BProc.mkP G) 
  (PrSet.add (BProc.mkP Inverter) 
   (PrSet.singleton (BProc.mkP Enc))).

 (** *** Global variables shared between adversaries, oracles and game *)
 Definition Gcomm := Vset.empty.

 (** Global variables shared between the adversaries [A] and [A'] *)
 Definition Gadv := {{g_a}}.

 (** The adversary is well-formed in [E0], i.e. it only reads or writes 
    variables it has access to and only calls oracles and its own procedures *)
 Hypothesis A_wf  : WFAdv PrOrcl PrPriv Gadv Gcomm E0 A.
 Hypothesis A'_wf : WFAdv PrOrcl PrPriv Gadv Gcomm E0 A'.

 (** The adversary runs in PPT as long as its oracles do so and
    are defined as in [E0] *)
 Hypothesis A_PPT : forall E,
  Eq_adv_decl PrOrcl PrPriv E0 E ->
  (forall O, PrSet.mem O PrOrcl -> PPT_proc E (BProc.p_name O)) ->
  PPT_proc E A.

 Hypothesis A'_PPT : forall E,
  Eq_adv_decl PrOrcl PrPriv E0 E ->
  (forall O, PrSet.mem O PrOrcl -> PPT_proc E (BProc.p_name O)) ->
  PPT_proc E A'.
 
 (** The adversary is lossless as long as the [G] and [H] oracles are so *)
 Hypothesis A_lossless : forall Hbody Gbody Dbody GAbody,
  (forall O, PrSet.mem O PrOrcl -> 
   lossless (mkENV Hbody Gbody Dbody GAbody)
   (proc_body (mkENV Hbody Gbody Dbody GAbody) (BProc.p_name O))) -> 
  lossless (mkENV Hbody Gbody Dbody GAbody) A_body.

 Hypothesis A'_lossless : forall Hbody Gbody Dbody GAbody,
  (forall O, PrSet.mem O PrOrcl -> 
   lossless (mkENV Hbody Gbody Dbody GAbody)
   (proc_body (mkENV Hbody Gbody Dbody GAbody) (BProc.p_name O))) -> 
  lossless (mkENV Hbody Gbody Dbody GAbody) A'_body.


 Lemma EqAD : forall H_body1 G_body1 Dbody1 GAbody1 
  H_body2 G_body2 Dbody2 GAbody2,
  Eq_adv_decl PrOrcl PrPriv 
  (mkENV H_body1 G_body1 Dbody1 GAbody1) (mkENV H_body2 G_body2 Dbody2 GAbody2).
 Proof.
  unfold Eq_adv_decl, mkENV; intros ? ? ? ? ? ? ? ? ? f0. 
  unfold proc_params, proc_body, proc_res.
  generalize (BProc.eqb_spec (BProc.mkP A') (BProc.mkP f0)).
  destruct (BProc.eqb (BProc.mkP A') (BProc.mkP f0)); intros.
  inversion H; simpl; auto.
  generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f0)).
  destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f0)); intros.
  inversion H2; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto;
  intros Heq;
   (apply H0; rewrite <- Heq; vm_compute; reflexivity) || 
   (apply H1; rewrite <- Heq; vm_compute; reflexivity).
 Qed.
 
 Lemma EqOP : forall H_body1 G_body1 Dbody1 GAbody1 
  H_body2 G_body2 Dbody2 GAbody2, 
  Eq_orcl_params PrOrcl 
  (mkENV H_body1 G_body1 Dbody1 GAbody1) (mkENV H_body2 G_body2 Dbody2 GAbody2).
 Proof.
  unfold Eq_orcl_params, mkENV; intros.
  unfold PrOrcl in H.
  rewrite PrSetP.add_spec in H; destruct H.
  inversion H; simpl.
  vm_compute; trivial.
  rewrite PrSetP.add_spec in H; destruct H.
  inversion H; simpl.
  vm_compute; trivial.
  apply PrSet.singleton_complete in H; inversion H; simpl.
  vm_compute; trivial.
 Qed.

 (** The adversary is well-formed in any environment constructred with [mkENV].
     This follows from the adversary being well-formed in [E0] *)
 Lemma A_wf_E : forall H_body G_body Dbody GAbody,
  WFAdv PrOrcl PrPriv Gadv Gcomm (mkENV H_body G_body Dbody GAbody) A.
 Proof.
  intros; apply WFAdv_trans with (5:=A_wf).
  unfold E0; apply EqOP.
  unfold E0; apply EqAD.
  vm_compute; intro; discriminate.
  vm_compute; intro; discriminate.
 Qed. 

 Lemma A'_wf_E : forall H_body G_body Dbody GAbody,
  WFAdv PrOrcl PrPriv Gadv Gcomm (mkENV H_body G_body Dbody GAbody) A'.
 Proof.
  intros; apply WFAdv_trans with (5:=A'_wf).
  unfold E0; apply EqOP.
  unfold E0; apply EqAD.
  vm_compute; intro; discriminate.
  vm_compute; intro; discriminate.
 Qed. 

 (** Helper functions to build info *)
 Definition i_Upto bad Hbody Gbody Dbody GAbody Hbody' Gbody' Dbody' GAbody' :=
  let E := mkENV Hbody Gbody Dbody GAbody in
  let E' := mkENV Hbody' Gbody' Dbody' GAbody' in
  let i0 : upto_info bad E E' := empty_upto_info bad E E' in
  let iH : upto_info bad E E' := add_upto_info i0 H in
  let iG : upto_info bad E E' := add_upto_info iH G in
  let iD : upto_info bad E E' := add_upto_info iG Dec in
  let iEnc : upto_info bad E E' := add_upto_info iD Enc in
  let iGA : upto_info bad E E' := add_upto_info iEnc GAdv in
  let eqad := EqAD Hbody Gbody Dbody GAbody Hbody' Gbody' Dbody' GAbody' in
  let eqop := EqOP Hbody Gbody Dbody GAbody Hbody' Gbody' Dbody' GAbody' in
  let iA : upto_info bad E E' := add_adv_upto_info iGA eqad eqop
   (A_wf_E Hbody Gbody Dbody GAbody) in
  let iA' : upto_info bad E E' := add_adv_upto_info iA eqad eqop
   (A'_wf_E Hbody Gbody Dbody GAbody) in iA'.

 Definition adv_info Hbody Hbody' Gbody Gbody' Dbody Dbody' GAbody GAbody' inv
  (pi:eq_inv_info inv (mkENV Hbody Gbody Dbody GAbody) 
   (mkENV Hbody' Gbody' Dbody' GAbody')) :=
  let E := mkENV Hbody Gbody Dbody GAbody in
  let E' := mkENV Hbody' Gbody' Dbody' GAbody' in
  let piEnc : eq_inv_info inv E E' := add_refl_info Enc pi in 
  let A'loss := @A'_lossless Hbody Gbody Dbody GAbody in
  let A'loss' := @A'_lossless Hbody' Gbody' Dbody' GAbody' in
  let Aloss := @A_lossless Hbody Gbody Dbody GAbody in
  let Aloss' := @A_lossless Hbody' Gbody' Dbody' GAbody' in
  let eqad := EqAD Hbody Gbody Dbody GAbody Hbody' Gbody' Dbody' GAbody' in
  let piA : eq_inv_info inv E E' := add_adv_info_lossless eqad 
   (A_wf_E Hbody Gbody Dbody GAbody) Aloss Aloss' piEnc in
  let piA' : eq_inv_info inv E E' := add_adv_info_lossless eqad 
   (A'_wf_E Hbody Gbody Dbody GAbody) A'loss A'loss' piA in piA'.

 Definition my_add_refl_info inv E E' (pi:eq_inv_info inv E E')
  t (f:Proc.proc t) :=
  match modify2 pi (proc_body E f) (proc_body E' f) with
  | Some (M1, M2) =>
     let R1 := Vset.diff M1 M2 in
     let R2 := Vset.diff M2 M1 in
     let O := Vset.union (fv_expr (proc_res E f)) 
                         (get_globals (Vset.inter M1 M2)) in
      add_refl_info_O f O R1 R2 pi 
  | None => pi
  end.

 Definition I_refl Hbody Hbody' Gbody Gbody' Dbody Dbody' GAbody GAbody' :=
  let pie := empty_info (mkENV Hbody Gbody Dbody GAbody) 
                        (mkENV Hbody' Gbody' Dbody' GAbody') in
  let piH := my_add_refl_info pie H in
  let piG := my_add_refl_info piH G in
  let piD := my_add_refl_info piG Dec in
  let piGA := my_add_refl_info piD GAdv in adv_info piGA.


 (**************************************************************)
 (* In this first transition we replace [GAdv] and [Dec]       *)
 (* in [E0] by versions returning a default value when the     *)
 (* number of queries is greater than the allowed one.         *)
 (* Both programs are equivalent since they are identical until*)
 (* bad and the probability of bad is 0                        *)
 (**************************************************************)

 Definition GAdv_body0_gen c := [ If qG <=! Gc then c else GAdv_body0 ].

 Definition GAdv_body0_bad := GAdv_body0_gen ((bad <- true) :: GAdv_body0).

 Definition GAdv_body1_bad := 
  GAdv_body0_gen [ bad <- true; rGadv <- (one_n | zero_k1) ].

 Definition GAdv_body1 :=  GAdv_body0_gen [rGadv <- (one_n | zero_k1)].

 Definition mkEnv H_body G_body Dec_body := 
  mkENV H_body G_body Dec_body GAdv_body1.

 Definition Dec_body0_gen test c := [ If test then c else Dec_body0 ].

 Definition testD := (qD <=! Dc || ((Ydef =?= true) && (Y' =?= c))).

 Definition Dec_body0_bad := 
  Dec_body0_gen testD ((bad <- true)::Dec_body0).

 Definition Dec_body1_bad := 
  Dec_body0_gen testD [bad <- true; mn <- (false | one_n)].

 Definition Dec_body1 :=  Dec_body0_gen testD [mn <- (false | one_n)].

 Definition E0b := mkENV H_body0 G_body0 Dec_body0_bad GAdv_body0_bad.

 Definition E1b := mkENV H_body0 G_body0 Dec_body1_bad GAdv_body1_bad.

 Definition E1 := mkEnv H_body0 G_body0 Dec_body1.


 Definition inv_q1 : mem_rel := 
  EP2 ((Ydef =?= false) && (bad ==> ((1 +! qG <=! Gc) || (1 +! qD <=! Dc)))).

 Lemma dec_inv_q1 : decMR inv_q1.
 Proof.
  unfold inv_q1; auto.
 Qed.

 Lemma dep_inv_q1 : depend_only_rel inv_q1 Vset.empty 
  (fv_expr ((Ydef =?= false) && (bad ==> ((1 +! qG <=! Gc) || (1 +! qD <=! Dc))))).
 Proof.
  unfold inv_q1; auto.
 Qed.

 Definition inv_q : mem_rel := 
  EP2 (bad ==> ((1 +! qG <=! Gc) || (1 +! qD <=! Dc) || ((true | Y') is_in LD))).

 Lemma dec_inv_q : decMR inv_q.
 Proof.
  unfold inv_q; auto.
 Qed.

 Lemma dep_inv_q : depend_only_rel inv_q Vset.empty 
  (fv_expr (bad ==> 
   ((1 +! qG <=! Gc) || (1 +! qD <=! Dc) || ((true | Y') is_in LD)))).
 Proof.
  unfold inv_q; auto.
 Qed.

 Definition eE0E0b1 : eq_inv_info inv_q1 E0 E0b :=
  let ie := 
   @empty_inv_info inv_q1 _ _ dep_inv_q1 (refl_equal _) dec_inv_q1 E0 E0b in
  let piH : eq_inv_info inv_q1 E0 E0b := add_refl_info H ie in
  let piG : eq_inv_info inv_q1 E0 E0b := add_refl_info G piH in piG.

 Definition eE0E0b : eq_inv_info inv_q E0 E0b :=
  let ie := 
   @empty_inv_info inv_q _ _ dep_inv_q (refl_equal _) dec_inv_q E0 E0b in
  let piH : eq_inv_info inv_q E0 E0b := add_refl_info H ie in
  let piG : eq_inv_info inv_q E0 E0b := add_refl_info G piH in piG.

 Hint Resolve dec_inv_q dec_inv_q1.
 
 Opaque leb.

 Lemma GA0_0b1 : EqObsInv inv_q1 
  {{LG, Gc, Radv}} 
  E0  GAdv_body0 
  E0b GAdv_body0_bad
  {{LG, Gc, rGadv}}.
 Proof.
  cp_test (qG <=! Gc);
  eqobs_tl eE0E0b1; unfold inv_q1; eqobsrel_tail;
  unfold implMR, EP1, EP2, andR, notR; simpl; unfold O.eval_op; simpl;
  intros k m1 m2; bprop; intro H; decompose [and] H; clear H.
  auto.
  split; [ trivial | ].
  intro Hbad; destruct (H4 Hbad) as [H | H]; auto.
  left; apply leb_complete in H; apply leb_correct; auto.
 Qed.

 Opaque T.i_eqb.

 Lemma Dec0_0b1 : EqObsInv inv_q1 
  {{Ydef, LD, Y', LG, LH, Dc, c}}
  E0  Dec_body0 
  E0b Dec_body0_bad
  {{LD, LG, LH, Dc, mn}}.
 Proof.
  unfold Dec_body0_bad, testD.
  ep_eq Ydef false.
   unfold inv_q1; intros k m1 m2.
   unfold EP2; simpl; unfold O.eval_op; simpl.
   intros [H1 H2].
   rewrite (H1 _ Ydef); trivial.
   apply andb_prop in H2; destruct H2.
   change (is_true (T.i_eqb k T.Bool (m2 Ydef) false)) in H.
   rewrite is_true_Ti_eqb in H; split; trivial.
  ep_eq_r (false =?= true) false.
   intros; reflexivity.
  cp_test (qD <=! Dc); eqobs_tl eE0E0b1; unfold inv_q1; eqobsrel_tail;
  unfold implMR, EP1, EP2, andR, notR; simpl; unfold O.eval_op; simpl; 
   intros k m1 m2; bprop; intros H; 
   decompose [and] H; clear H; repeat split; trivial.
  right; apply leb_complete in H5; apply leb_correct; omega'.
  intro Hbad; destruct (H4 Hbad); auto.
  right; apply leb_complete in H; apply leb_correct; omega'.
 Qed.

 Lemma GA0_0b : EqObsInv inv_q
  {{LG, Gc, Radv}}
  E0  GAdv_body0 
  E0b GAdv_body0_bad
  {{LG, Gc, rGadv}}.
 Proof.
  cp_test (qG <=! Gc);
  eqobs_tl eE0E0b; unfold inv_q; eqobsrel_tail;
  unfold implMR, EP1, EP2, andR, notR; simpl; unfold O.eval_op; simpl;
   intros k m1 m2; bprop; intros H; decompose [and] H.
  intro; auto.
  intro Hbad; decompose [or] (H2 Hbad); [ | auto | auto ].
  left; left; apply leb_correct; apply leb_complete in H5; auto.
 Qed.

 Lemma Dec0_0b : EqObsInv inv_q 
  {{Ydef, LD, Y', LG, LH, Dc, c}}
  E0  Dec_body0 
  E0b Dec_body0_bad
  {{LD, LG, LH, Dc, mn}}.
 Proof.
  cp_test testD; eqobs_tl eE0E0b; unfold inv_q; eqobsrel_tail;
  unfold implMR, EP1, EP2, andR, notR; simpl; unfold O.eval_op; simpl;
   intros k m1 m2; bprop; intros H; decompose [and] H.
  intros _.
  destruct H4 as [H4 | [H4 H5] ].
  auto.
  destruct H1.
  left; right; apply leb_complete in H1; apply leb_correct.
  rewrite <- (H0 _ Dc); auto with arith.
  right; left.
  rewrite is_true_Ti_eqb in H4, H5; rewrite H4, H5; apply Ti_eqb_refl.
  intro Hbad; destruct (H2 Hbad) as [ [HH | HH] | HH]; auto.
  left; right.
  apply leb_correct; apply leb_complete in HH; omega'.
 Qed.

 Definition iE0E0b1 : eq_inv_info inv_q1 E0 E0b :=
  let piGA := add_info GAdv Vset.empty {{bad}} eE0E0b1 GA0_0b1 in
  let piDA := add_info Dec Vset.empty {{bad}} piGA Dec0_0b1 in
   adv_info piDA.

 Definition iE0E0b : eq_inv_info inv_q E0 E0b :=
  let piGA := add_info GAdv Vset.empty {{bad}} eE0E0b GA0_0b in
  let piDA := add_info Dec Vset.empty {{bad}} piGA Dec0_0b in
   adv_info piDA.

 Definition iE1bE1 : eq_inv_info trueR E1b E1 := 
  I_refl H_body0 H_body0 G_body0 G_body0 Dec_body1_bad 
  Dec_body1 GAdv_body1_bad GAdv_body1.

 (**************************************************************) 
 (* We inline the encryption of [mb]. The randomness used in   *)
 (* the encryption is sampled at the beginning of the game and *)
 (* stored in the global variable [R']                         *)
 (**************************************************************) 

 Definition init1 :=
  [
   Ydef <- false;
   LG <- Nil _;
   LH <- Nil _;
   LD <- Nil _;
   Dc <- 0;
   Gc <- 0;
   R' <$- {0,1}^k0
  ].

 Definition tail1 :=
  [
   M <c- A with {};
   b <$- {0,1};
   If b then [Mb <- Efst M] else [Mb <- Esnd M];
   Ge <c- G with {R'};
   S' <- Ge |x2| (Mb | zero_k1);
   He <c- H with {S'};
   T' <- He |x| R';
   Y' <- ap_f (S' | T');
   Ydef <- true;
   b' <c- A' with {Y'}
  ].

 Definition G1 := init1 ++ tail1.

 Lemma PrG0_G1 : forall k (m:Mem.t k), 
  Pr E0 G0 m (EP k (b =?= b')) == Pr E1 G1 m (EP k (b =?= b')).
 Proof.
  intros k m; apply Uabs_diff_0_eq.
  assert (Pr E0b G0 (m{!bad<--false!}) (EP k bad) == 0).
  transitivity (Pr E0b ((bad <- false)::G0) m (EP k bad)).
  symmetry.
  unfold Pr; rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim; trivial.
  split; [ | trivial].
  transitivity (Pr E0 G0 m 
   (EP k ((1 +! qG <=! Gc) || (1 +! qD <=! Dc) || ((true | Y') is_in LD)))).
  apply equiv_deno_le with (kreq_mem {{Y', g_a}})
   (req_mem_rel {{Y', LD, Ydef, Gc, Dc}} (transpR inv_q)); trivial.
  apply equiv_sym_transp.
  rewrite transpR_kreq_mem, transpR_req_mem_rel, transpR_transpR.
  eqobs_tl iE0E0b.
  match goal with 
   |- equiv _ _ _ _ _ (req_mem_rel ?O _) => 
    apply equiv_weaken with (req_mem_rel O inv_q1) 
  end.
  intros k2 m1 m2 (H1, H2); split; [trivial | unfold inv_q, inv_q1 in *].
  generalize H2; clear H2; unfold EP2; simpl; unfold O.eval_op; simpl.
  rewrite is_true_andb, is_true_impb, is_true_impb.
  intros (H2, H3) H4. rewrite (H3 H4); trivial.
  eqobs_tl iE0E0b1.
  unfold inv_q1. 
  eqobsrel_tail; simpl; unfold O.eval_op; simpl; intros k2 m1 m2 H; reflexivity.
  unfold charfun, restr, transpR, inv_q, EP, EP2; simpl; unfold O.eval_op; simpl.
  intros m1 m2 (H1, H2). 
  destruct (m1 bad); [ | trivial].
  unfold impb in H2; simpl in H2.
  rewrite (H1 _ Gc), (H1 _ Dc), (H1 _ LD), (H1 _ Y') in H2; trivial.
  rewrite H2; trivial.
  apply Oeq_le; symmetry; apply range_query.
  unfold charfun,EP, restr; simpl; unfold O.eval_op; simpl; intros m1 H.
  repeat rewrite is_true_andb in H; destruct H as ((H1, H2), H3).
  rewrite is_true_negb, not_is_true_false in H3; rewrite H3, orb_false_r.
  change (0 == (if orb (leb (Datatypes.S (qG_poly k)) (m1 Gc)) 
   (leb (Datatypes.S (qD_poly k)) (m1 Dc))
   then fone _ m1 else 0)).
  apply leb_complete in H1; apply leb_complete in H2.
  rewrite leb_correct_conv, leb_correct_conv; trivial; omega'.
  rewrite <- H.
  transitivity (Uabs_diff (Pr E0b G0 (m{!bad<--false!}) (EP k (b =?= b')))
   (Pr E1b G0 (m{!bad<--false!}) (EP k (b =?= b')))).
  apply Oeq_le; apply Uabs_diff_morphism.
  transitivity (Pr E0b ((bad<-false)::G0) m  (EP k (b =?= b'))).
  apply EqObs_Pr with {{Y', g_a}}.
  apply equiv_weaken with (req_mem_rel (fv_expr (b =?= b')) inv_q).
  intros k2 m1 m2 (H1, _); trivial.
  eqobs_tl iE0E0b.
  match goal with 
   |- equiv _ _ _ _ _ (req_mem_rel ?O _) => 
    apply equiv_weaken with (req_mem_rel O inv_q1) 
  end.
  intros k2 m1 m2 (H1, H2); split; [trivial | unfold inv_q, inv_q1 in *].
  generalize H2; clear H2; unfold EP2; simpl; unfold O.eval_op; simpl.
  rewrite is_true_andb, is_true_impb, is_true_impb.
  intros (H2, H3) H4. rewrite (H3 H4); trivial.
  eqobs_tl iE0E0b1.
  unfold inv_q1. eqobsrel_tail; simpl; unfold O.eval_op; simpl;
  intros k2 m1 m2 H1; reflexivity.
  unfold Pr; rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim; trivial.
  transitivity (Pr E1b ((bad<-false)::G0) m  (EP k (b =?= b'))).
  apply EqObs_Pr with {{Y', g_a}}; apply EqObs_sym.
  inline_l iE1bE1 Enc; alloc_r iE1bE1 R' Re; ep iE1bE1; deadcode iE1bE1.
  eqobs_ctxt iE1bE1; swap iE1bE1; eqobs_in iE1bE1.
  unfold Pr; rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim; trivial.
  rewrite Uabs_diff_sym.
  apply upto_bad_Uabs_diff with 
   (i_Upto bad H_body0 G_body0 Dec_body1_bad GAdv_body1_bad
   H_body0 G_body0 Dec_body0_bad GAdv_body0_bad).
  trivial.
  vm_compute; trivial.
  apply is_lossless_correct with (refl2_info iE0E0b); vm_compute; trivial.
 Qed.

 (*********************************************************)
 (* We can now start the proof.                           *)
 (* [GAdv] won't change from now on, so we specialize the *)
 (* functions to build specifications                     *)
 (*********************************************************)

 Definition i_upto bad Hbody Gbody Dbody Hbody' Gbody' Dbody' :=
  i_Upto bad Hbody Gbody Dbody GAdv_body1 Hbody' Gbody' Dbody' GAdv_body1.

 Definition i_refl Hbody Hbody' Gbody Gbody' Dbody Dbody' :=
  I_refl Hbody Hbody' Gbody Gbody' Dbody Dbody' GAdv_body1 GAdv_body1.

 Definition iEiEi Hbody Gbody Dbody :=
  I_refl Hbody Hbody Gbody Gbody Dbody Dbody GAdv_body1 GAdv_body1.
 
 Definition iEi_G Hbody Gbody Gbody' Dbody :=
  i_refl Hbody Hbody Gbody Gbody' Dbody Dbody.

 Definition iEi_H Hbody Hbody' Gbody Dbody :=
  i_refl Hbody Hbody' Gbody Gbody Dbody Dbody.

 Definition iEi_D Hbody Gbody Dbody Dbody' :=
  i_refl Hbody Hbody Gbody Gbody Dbody Dbody'.
 
 Definition iEinv_GG' Hbody Gbody Gbody' Dbody inv 
  (ie:eq_inv_info inv (mkEnv Hbody Gbody Dbody) (mkEnv Hbody Gbody' Dbody)) 
    I O  
    (Gbody_Gbody': 
     EqObsInv inv I 
     (mkEnv Hbody Gbody Dbody) Gbody 
     (mkEnv Hbody Gbody' Dbody) Gbody' O) :=
    let E := mkEnv Hbody Gbody Dbody in
    let E' := mkEnv Hbody Gbody' Dbody in 
    let piH : eq_inv_info inv E E' := add_refl_info H ie in
    match modify2 piH (proc_body E G) (proc_body E' G) with
    | Some (M1, M2) =>
      let R1 := get_globals (Vset.diff M1 M2) in
      let R2 := get_globals (Vset.diff M2 M1) in
      let piG : eq_inv_info inv E E' := add_info G R1 R2 piH Gbody_Gbody' in
      match pii_info piG H, pii_info piG G with
      | Some pih, Some pig =>
        let Og := pii_output pig in
        let Ohg := Vset.union (pii_output pih) Og in
        let piD : eq_inv_info inv E E' := 
         add_refl_info_O Dec (Vset.add Dc (Vset.add mn Ohg)) R1 R2 piG in
        let piGA : eq_inv_info inv E E' := 
         add_refl_info_O GAdv (Vset.add Gc (Vset.add rGadv Og)) R1 R2 piD in
        adv_info piGA 
      | _, _ => piH
      end
    | None => piH
    end.

 (***********************************************)
 (* Second Transition: E1, G1 -> E2, G2         *) 
 (*  + Eagerly sample G(R')                     *)
 (*  + inline G in the game                     *)
 (*  + apply fundamental lemma                  *)
 (***********************************************)

 Definition G_body1_gen c :=
  [
   If !(R in_dom LG) 
   then [ 
    If R' =?= R then c
    else [rGn <$- {0,1}^n; rGk1 <$- {0,1}^k1];
    LG <- (R | (rGn | rGk1)) |::| LG
   ] 
   else [ rGn <- Efst (LG[{R}]); rGk1 <- Esnd (LG[{R}]) ]
  ].

 Definition G_body1_f := G_body1_gen [rGn <- GR'n; rGk1 <- GR'k1].
 Definition E1f := mkEnv H_body0 G_body1_f Dec_body1.

 (* E1 --> E1f by lazy sampling *)
 Definition G_body1_u :=
  [ If R' =?= R then [rGn <- GR'n; rGk1 <- GR'k1] else G_body0 ].

 Definition E1u := mkEnv H_body0 G_body1_u Dec_body1.

 (* E1f --> E1u : we use an invariant, 
    E1u allows to inline G without adding R' to the list *)

 (* After inlining we revert to [E1f] using the previous invariant *)
 Definition tail1_u :=  
  [
   M <c- A with{};
   b <$- {0,1};
   If b then [ Mb <- Efst M] else [ Mb <- Esnd M ];
   S' <- (GR'n|GR'k1) |x2| (Mb | zero_k1);
   He <c- H with {S'};
   T' <- He |x| R';
   Y' <- ap_f (S' | T');
   Ydef <- true;
   b' <c- A' with {Y'}
  ].

 Definition SGR' := [ GR'n <$- {0,1}^n; GR'k1 <$- {0,1}^k1 ].

 Definition G1_u := init1 ++ SGR' ++ tail1_u.

 Definition G_body1_bad := G_body1_gen [bad <- true; rGn <- GR'n; rGk1 <- GR'k1].

 Definition E1B := mkEnv H_body0 G_body1_bad Dec_body1.
 
 (* E1f --> E1B trivial *)

 Definition G_body2_bad := 
  G_body1_gen [bad <- true; rGn <$- {0,1}^n; rGk1 <$- {0,1}^k1].

 Definition E2B := mkEnv H_body0 G_body2_bad Dec_body1.

 (* E1B --> E2B by fundamental lemma *)

 Definition G_body2 := 
  [
   If !(R in_dom LG) 
   then [ 
    If R' =?= R _then [bad <- true];
    rGn <$- {0,1}^n; rGk1 <$- {0,1}^k1;
    LG <- (R | (rGn | rGk1)) |::| LG
   ] 
   else [ rGn <- Efst (LG[{R}]); rGk1 <- Esnd (LG[{R}]) ]
  ].

 Definition E2 := mkEnv H_body0 G_body2 Dec_body1.

 (* E2b --> E2: trivial reorganization of code *)
 Definition tail2 := 
  [
   M <c- A with {};
   He <c- H with {S'};
   T' <- He |x| R';
   Y' <- ap_f (S' | T'); 
   Ydef <- true;
   b' <c- A' with {Y'}
  ].

 Definition G2_ := init1 ++ SGR' ++ [S' <- (GR'n|GR'k1)] ++ tail2.

 Definition G2 := (bad <- false) :: G2_.

 (* E1 --> E1f *)
 Definition SG:=
  [ 
   If !(R' in_dom LG) then SGR'  
   else [ GR'n <- Efst (LG[{R'}]); GR'k1 <- Esnd  (LG[{R'}]) ] 
  ].

 Lemma Modify_S : forall E, Modify E {{GR'n, GR'k1}} SG.
 Proof.
  intros E.
  compute_assertion X t1 (modify (refl1_info (empty_info E E)) Vset.empty SG).
  apply modify_correct in X; eapply Modify_weaken; [eauto | ].
  vm_compute; trivial.
 Qed.

 Lemma EqObs_S : EqObs (Vset.union {{R', LG}} {{GR'n, GR'k1}}) E1 SG E1f SG {{GR'n, GR'k1}}.
 Proof.
  eqobs_in. 
 Qed.

 Lemma IXSG_global : forall x : VarP.Edec.t, 
  Vset.mem x (Vset.union {{R', LG}} {{GR'n, GR'k1}}) -> Var.is_global x.
 Proof.
  apply Vset.forallb_correct.
  intros x y Heq; rewrite Heq; trivial.
  vm_compute; trivial.
 Qed.

 Lemma swap_equiv_G :
  equiv Meq E1 (proc_body E1 G ++ SG) E1f (SG ++ proc_body E1f G) Meq.
 Proof.
  change (proc_body E1 G) with G_body0; change (proc_body E1f G) with G_body1_f; 
   unfold G_body0, G_body1_f, G_body1_gen.
  apply swap_sample_if2.
  intros b.
  apply equiv_Meq_inv_Modify with {{GR'n, GR'k1}} (fv_expr (!(R in_dom LG) =?= b)) Vset.empty.
  apply Modify_S.
  apply Modify_S. 
  apply depend_only_EP1.
  vm_compute; trivial.  
  vm_compute; trivial.
  rewrite proj1_MR; eqobs_in.
  union_mod; [rewrite proj1_MR; trivial | ].
  alloc_l LG LG'; ep. 
  match goal with 
   |- equiv _ _ [?i1; ?i2; ?i3; ?i4; ?i5] _ _ _ => 
    apply equiv_trans_eq_mem_l with trueR E1 [i1; i2; i3; i5; i4] 
  end.
  rewrite proj1_MR; swap; union_mod; [trivial | eqobs_in].
  ep; cp_test (R' =?= R).
  ep_eq_r (!(R in_dom LG)) true.
  intros k m1 m2 ((H1, H2), _); rewrite <- H1; exact H2.
  alloc_l rGn GR'n; alloc_l rGk1 GR'k1; ep; deadcode; swap; eqobs_in.
  deadcode; swap; eqobs_in.
  red; red; trivial.
  rewrite proj1_MR.
  apply check_swap_c_correct with (I:= {{R', LG}}) (X:= {{GR'n, GR'k1}}) (pi:= fun _ _ => None).
  apply Modify_S.
  apply Modify_S. 
  apply EqObs_S.  
  vm_compute; trivial.
  intros k m1 m2 Heq; rewrite Heq; trivial.
 Qed.

 Definition swi_G : forall tg g, option (sw_info SG {{GR'n, GR'k1}} {{R', LG}} E1 E1f tg g) :=
  let swiH := add_sw_info_refl SG {{GR'n, GR'k1}} {{R', LG}} E1 E1f (Modify_S E1) (Modify_S E1f) 
   EqObs_S IXSG_global (fun t f => None) _ H in
  let swiG := add_sw_info SG {{GR'n, GR'k1}} {{R', LG}} E1 E1f (Modify_S E1) (Modify_S E1f) 
   EqObs_S IXSG_global swiH _ _ swap_equiv_G in
  let swiD := add_sw_info_refl SG {{GR'n, GR'k1}} {{R', LG}} E1 E1f (Modify_S E1) (Modify_S E1f) 
   EqObs_S IXSG_global swiG _ Dec in
  let swiGA := add_sw_info_refl SG {{GR'n, GR'k1}} {{R', LG}} E1 E1f (Modify_S E1) (Modify_S E1f) 
   EqObs_S IXSG_global swiD _ GAdv in
  let swiA := add_sw_info_Adv SG {{GR'n, GR'k1}} {{R', LG}} E1 E1f (Modify_S E1) (Modify_S E1f) 
   EqObs_S 
   IXSG_global swiGA _ A PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _ _ _ _ _) 
   (A_wf_E _ _ _ _) in
  let swiA' := add_sw_info_Adv SG {{GR'n, GR'k1}} {{R', LG}} E1 E1f (Modify_S E1) (Modify_S E1f) 
   EqObs_S 
   IXSG_global swiA _ A' PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _ _ _ _ _) 
   (A'_wf_E _ _ _ _) in swiA'.

 (** E1f --> E1u *)
 Definition inv_Gfu : mem_rel := 
  EP1 ((R' in_dom LG) ==> (LG[{R'}] =?= (GR'n|GR'k1))) /-\
  eq_assoc_except R' LG.
 
 Lemma dec_inv_Gfu : decMR inv_Gfu.
 Proof.
  unfold inv_Gfu; auto.
 Qed.
 
 Lemma dep_inv_Gfu : depend_only_rel inv_Gfu
  (Vset.union 
   (fv_expr ((R' in_dom LG) ==> (LG[{R'}] =?= (GR'n|GR'k1))))
   (Vset.add R' (Vset.singleton LG)))
  (Vset.union Vset.empty (Vset.singleton LG)).
 Proof.
  unfold inv_Gfu; auto.
 Qed.
 
 Definition eE1fE1u : eq_inv_info inv_Gfu E1f E1u.
  refine (@empty_inv_info inv_Gfu _ _ dep_inv_Gfu _ dec_inv_Gfu E1f E1u).
  vm_compute; trivial.
 Defined.

 (** The two oracles are equivalent under the invariant *)
 Lemma G_body1f_G_body1u :
  EqObsInv inv_Gfu 
  {{R, GR'n, GR'k1, R'}}
  E1f G_body1_f 
  E1u G_body1_u 
  {{rGn, rGk1}}.
 Proof.
  unfold G_body1_f, G_body1_u,G_body1_gen, G_body0.
  cp_test (R' =?= R).
  ep_eq R R'.
  unfold req_mem_rel, andR; intuition; symmetry; rewrite expr_eval_eq; trivial.
  cp_test_l (R' in_dom LG).
  ep_eq_l (LG [{R'}]) (GR'n|GR'k1).
  unfold inv_Gfu,req_mem_rel, andR; intuition.
  rewrite expr_eval_eq; apply expr_modus_ponens with (R' in_dom LG); trivial.
  eqobs_in eE1fE1u.
  rewrite proj2_MR; apply proj1_MR.
  unfold inv_Gfu; eqobsrel_tail.
  unfold EP1, EP2, andR, kreq_mem, notR, implMR; simpl; unfold O.eval_op; simpl;
   unfold O.assoc; simpl; intros.
  repeat rewrite Ti_eqb_refl; simpl; split; trivial.
  intros r Hd; generalize Hd.
  rewrite <- is_true_UTi_eqb, not_is_true_false in Hd.
  rewrite (Hd:T.i_eqb k BS_k0 r (m1 R') = false); simpl.
  decompose [and] H; clear H. 
  intros Hd'; exact (H4 _ Hd').
  cp_test (R in_dom LG).
  unfold inv_Gfu,req_mem_rel, andR, eq_assoc_except; intros.
  decompose [and] H; clear H.
  destruct (H4 (m1 R)).
  apply sym_not_eq; rewrite <- is_true_Ti_eqb; exact H3.
  apply trans_eq with (1:=H); rewrite (H2 _ R); trivial.
  assert (W:= depend_only_req_mem_rel (X:={{rGn, rGk1}}) dep_inv_Gfu).
  apply equiv_depend_only_l with (2:=W) (E1':=E1f) 
   (c1':=[ GR'<-LG [{R}]; rGn <- Efst GR'; rGk1 <- Esnd GR' ]).
  decMR_tac eE1fE1u.
  ep; deadcode; eqobs_in.
  apply equiv_depend_only_r with (2:=W) (E2':=E1u) 
   (c2':=[ GR'<-LG [{R}]; rGn <- Efst GR'; rGk1 <- Esnd GR' ]).
  decMR_tac eE1fE1u.
  ep; deadcode; eqobs_in.
  eqobs_tl_n eE1fE1u 2%nat.
  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold req_mem_rel,upd_para, andR; intros.
  decompose [and] H; clear H; split.
  unfold kreq_mem; red; intros.
  assert (W1:=Vset.singleton_complete _ _ H).
  inversion W1; simpl projT1; simpl projT2; repeat rewrite Mem.get_upd_same.
  clear H8 H7 W1 H5 H x t.
  destruct H4 as (H4, H5); destruct (H5 (m1 R)) as (H7, H8).
  apply sym_not_eq; rewrite <- is_true_Ti_eqb; exact H2.
  eapply trans_eq; [ apply H8 | ]. 
  rewrite (H0 _ R); trivial.
  apply dep_inv_Gfu with m1 m2; [ | | trivial]; 
   apply req_mem_upd_disjoint; vm_compute; trivial.
  unfold inv_Gfu; eqobsrel_tail.
  unfold EP1, EP2, andR, kreq_mem, notR, implMR.
  simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl; intros.
  decompose [and] H; clear H.
  rewrite not_is_true_false in H5; rewrite H5; simpl.
  split; trivial.
  intros r Hd.
  rewrite <- (H2 _ R); trivial.
  generalize (T.i_eqb_spec k BS_k0 r (m1 R)).
  destruct (T.i_eqb k BS_k0 r (m1 R)); simpl; auto.
  intros HH; exact (H6 _ Hd).
 Qed.

 Definition iE1fE1u : eq_inv_info inv_Gfu E1f E1u := 
  iEinv_GG' eE1fE1u G_body1f_G_body1u.

 Lemma G1_G1_u :
  EqObs {{Y', g_a}} 
  E1  G1 
  E1B ((bad <- false) :: G1_u) 
  (fv_expr (b =?= b')).
 Proof.
  (* E1 --> E1f *)
  apply EqObs_trans with E1 (G1 ++ SG).
  set (iE1:=iEiEi H_body0 G_body0 Dec_body1); deadcode iE1; eqobs_in iE1.
  apply equiv_trans_eq_mem_l with trueR E1f (init1++SG++tail1); 
   [ | | red; red; trivial].
  rewrite proj1_MR; unfold G1; rewrite app_ass; apply equiv_app with Meq.
  union_mod; [auto with * | eqobs_in].
  apply check_swap_c_correct with (I:={{R', LG}}) (pi:=swi_G).
  apply Modify_S.
  apply Modify_S.
  apply EqObs_S.
  vm_compute; trivial.
  (* E1f --> E1u *)
  apply EqObs_trans with E1u (init1 ++ SG ++ tail1).
  eqobs_tl iE1fE1u.
  ep; unfold inv_Gfu; eqobsrel_tail; 
   unfold EP1, EP2, andR, kreq_mem, notR, implMR; simpl; 
    unfold O.eval_op; simpl; unfold O.assoc; simpl; intros; unfold impb; auto.
  (* inlining *)
  apply EqObs_trans with E1u G1_u.
  set (iE1u:=iEiEi H_body0 G_body1_u Dec_body1); sinline_l iE1u G; eqobs_in iE1u.
  (* E1u --> E1f *)
  apply EqObs_trans with E1f G1_u.
  apply EqObs_sym; eqobs_tl iE1fE1u.
  unfold inv_Gfu; eqobsrel_tail; 
   unfold EP1, EP2, andR, kreq_mem, notR, implMR; simpl; unfold O.eval_op; simpl;
    unfold O.assoc; simpl; intros; unfold impb; auto.
  (* E1f --> E1B *)
  set (i:=iEi_G H_body0 G_body1_f G_body1_bad Dec_body1).
  deadcode i; eqobs_in i.
 Qed.

 Lemma G_body2_bad_G_body2 : 
  EqObsInv trueR 
  {{R, R', bad, LG}}
  E2B G_body2_bad 
  E2  G_body2 
  {{bad, LG, rGn, rGk1}}.
 Proof.
  cp_test (R' =?= R); eqobs_in.
 Qed.

 Definition iE2BE2 := iEinv_GG' (empty_info E2B E2) G_body2_bad_G_body2.
 Definition iE2B := iEiEi H_body0 G_body2_bad Dec_body1.
 Definition iE2 := iEiEi H_body0 G_body2 Dec_body1.

 Lemma G1_u_G2_ : 
  EqObs {{bad, Y', g_a}} 
  E2B G1_u 
  E2  (G2_ ++ [b<$-{0,1}])
  (Vset.union (fv_expr bad) (fv_expr (b=?=b'))).
 Proof.
  swap iE2BE2.
  eqobs_hd_n iE2BE2 7.
  eqobs_tl iE2BE2.
  apply EqObs_trans with E2B [ 
   M <c- A with{};
   b <$- {0,1};
   If b then [Mb <- Efst M] else [Mb <- Esnd M];
   GR'n <$- {0,1}^n; rGn <- GR'n |x| Mb;
   GR'k1 <$- {0,1}^k1; rGk1 <- GR'k1 |x| zero_k1;
   S' <- (rGn | rGk1)
   ]; [ep iE2B; deadcode iE2B; swap iE2B; eqobs_in iE2B | ].
  apply EqObs_trans with E2 [
   M <c- A with{};
   b <$- {0,1};
   GR'n <$- {0,1}^n; rGn <- GR'n;
   GR'k1 <$- {0,1}^k1; rGk1 <- GR'k1;
   S' <- (rGn | rGk1)
  ]; [ | ep iE2; deadcode iE2; swap iE2; eqobs_in iE2].
  eqobs_ctxt iE2BE2.
  union_mod.
  match goal with |- EqObs ?I _ (?i::_) _ _ _ => set (I1:= I); set (ib := i) end.
  apply EqObs_trans with E2B
   (ib::([rGn <$- {0,1}^n; GR'n <- rGn |x| Mb] ++ [rGk1 <$- {0,1}^k1; GR'k1 <- rGk1 |x| zero_k1])).
  match goal with|- EqObs ?I _ ?c _ _ _ => 
    change c with (ib::([GR'n <$- {0,1}^n; rGn <- GR'n |x| Mb] ++ [GR'k1 <$- {0,1}^k1; rGk1 <- GR'k1 |x| zero_k1]))
  end.
  apply equiv_cons with (kreq_mem (Vset.add Mb I1)); [eqobs_in | ].
  apply equiv_app with (kreq_mem {{rGn}}).
  eapply equiv_strengthen; [ | eapply equiv_weaken; [ | apply optimistic_sampling; trivial; discriminate ] ].
  simpl; intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  union_mod.
  eapply equiv_strengthen; [ | eapply equiv_weaken; [ | apply optimistic_sampling; trivial; discriminate ] ].
  simpl; intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  alloc_r GR'n rGn; alloc_r GR'k1 rGk1; ep; deadcode; eqobs_in.
 Qed.

 Definition i_bad12 : upto_info bad E1B E2B := 
  i_upto bad H_body0 G_body1_bad Dec_body1 H_body0 G_body2_bad Dec_body1.

 Lemma PrG0_bad : forall k (m:Mem.t k),
  (Uabs_diff (Pr E0 G0 m (EP k (b=?=b'))) [1/2] <= 
   Pr E2 G2 m (EP k bad))%tord.
 Proof.
  intros k m; set (mb:=m{!bad <-- false!}).
  transitivity (Uabs_diff (Pr E1B G1_u mb (EP k (b =?= b'))) (Pr E2B G1_u mb (EP k (b =?= b')))).
  apply Oeq_le; apply Uabs_diff_morphism.
  unfold mb; rewrite PrG0_G1, set_bad.
  apply EqObs_Pr with {{Y', g_a}}; apply G1_G1_u.
  symmetry.
  transitivity (Pr E2 (G2_ ++ [b<$-{0,1}]) mb (EP k (b =?= b'))).
  apply EqObs_Pr with {{bad, Y', g_a}}.
  eapply equiv_weaken; [ | apply G1_u_G2_].
  intros k2 m1 m2 H; apply req_mem_weaken with (2:=H); vm_compute; trivial.
  apply Pr_sample_bool; [discriminate | ].
  apply is_lossless_correct with (refl1_info iE2); vm_compute; trivial.
  transitivity (Pr E2B G1_u mb (EP k bad)).
  apply upto_bad_Uabs_diff with i_bad12.
  trivial.
  vm_compute; trivial.
  apply is_lossless_correct with (refl1_info iE2B); vm_compute; trivial.
  unfold G2; apply Oeq_le; rewrite <- set_bad.
  apply EqObs_Pr with {{bad, Y', g_a}}.
  apply EqObs_trans with E2 (G2_ ++ [b <$- {0,1}]).
  eapply equiv_weaken; [ | apply G1_u_G2_].
  intros k2 m1 m2 H; apply req_mem_weaken with (2:=H); vm_compute; trivial.
  deadcode iE2; eqobs_in iE2.
 Qed.

 (*****************************************)
 (* In E2 G2, G is no more called in      *)
 (* the main, so |LG| <= Gc + Dc.         *)
 (* And so |LG| <= qG + qD.               *)
 (* The Dec oracle can safely reject      *)
 (* when qG + qD < |LG|                   *)
 (*****************************************)

 Definition Dec_body3_gen c := 
  [ If (qD +! qG) <! Elen LG then c else Dec_body1 ].

 Definition Dec_body1_bad1 := Dec_body3_gen ((bad1 <- true)::Dec_body1).

 Definition Dec_body3_bad1 := Dec_body3_gen [bad1 <- true; mn <- (false | one_n)].

 Definition Dec_body3 := 
  Dec_body0_gen (testD || ((qD +! qG) <! Elen LG)) [ mn <- (false | one_n)].

 Definition E2B1 := mkEnv H_body0 G_body2 Dec_body1_bad1.
 Definition E3B1 := mkEnv H_body0 G_body2 Dec_body3_bad1.
 Definition E3   := mkEnv H_body0 G_body2 Dec_body3.

 Definition iE2E2B1 := iEi_D H_body0 G_body2 Dec_body1 Dec_body1_bad1.

 Definition i_bad23 : upto_info bad1 E2B1 E3B1 := 
  i_upto bad1 H_body0 G_body2 Dec_body1_bad1 H_body0 G_body2 Dec_body3_bad1.

 Definition i_reflD Dbody Dbody' :=
  let pie := 
   empty_info (mkENV H_body0 G_body2 Dbody GAdv_body1) 
              (mkENV H_body0 G_body2 Dbody' GAdv_body1) in
  let piH := my_add_refl_info pie H in my_add_refl_info piH G.

 Definition iE3B1G := i_reflD Dec_body3_bad1 Dec_body3.

 Lemma Dec_body3_bad1_Dec_body3 : 
  EqObsInv trueR 
  {{Ydef, Y', c, bad, LG, R', LH, Dc, Gc}}
  E3B1 Dec_body3_bad1 
  E3   Dec_body3
  {{Dc, LH, bad, LG, mn}}.
 Proof.
  cp_test testD.
  deadcode; eqobs_in.
  deadcode iE3B1G; eqobs_in iE3B1G.
 Qed.

 Definition iEinv_DD' Hbody Gbody Dbody Dbody' inv 
  (piG:eq_inv_info inv (mkEnv Hbody Gbody Dbody) (mkEnv Hbody Gbody Dbody')) 
  I O  
  (Dbody_Dbody': 
   EqObsInv inv I (mkEnv Hbody Gbody Dbody) Dbody (mkEnv Hbody Gbody Dbody') Dbody' O):=
    let E := mkEnv Hbody Gbody Dbody in
    let E' := mkEnv Hbody Gbody Dbody' in 
    match modify2 piG (proc_body E Dec) (proc_body E' Dec) with
    | Some (M1, M2) =>
      let R1 := get_globals (Vset.diff M1 M2) in
      let R2 := get_globals (Vset.diff M2 M1) in
      let piD : eq_inv_info inv E E' := add_info Dec R1 R2 piG Dbody_Dbody' in
      match pii_info piG G with
      | Some pig =>
        let Og := pii_output pig in
        let piGA : eq_inv_info inv E E' := 
         add_refl_info_O GAdv (Vset.add Gc (Vset.add rGadv Og)) R1 R2 piD in
        adv_info piGA 
      | _ => piG
      end
    | None => piG
    end.

 Definition iE3B1E3 := iEinv_DD' iE3B1G Dec_body3_bad1_Dec_body3.

 Definition e_inv3 := (bad1 ==> ((qD +! qG) <! Elen LG)) &&
                      ((Elen LG) <=! (Dc +! Gc)) &&
                      (Dc <=! qD) &&
                      (Gc <=! qG).

 Definition inv3 := (EP1 e_inv3).

 Lemma dec_inv3 : decMR inv3.
 Proof.
  unfold inv3; auto.
 Qed.

 Lemma dep_inv3 : depend_only_rel inv3 (fv_expr e_inv3) (Vset.empty).
 Proof.
  unfold inv3; auto.
 Qed.

 Definition eE3B1 : eq_inv_info inv3 E3B1 E3B1.
  refine (@empty_inv_info inv3 _ _ dep_inv3 _ dec_inv3 E3B1 E3B1).
  vm_compute; trivial.
 Defined.

 Lemma GAdv_body1_inv3 :
  EqObsInv inv3 
  {{bad1, Radv, R', Gc, bad, LG}}
  E3B1 GAdv_body1 
  E3B1 GAdv_body1 
  {{Gc, bad1, bad, LG,  rGadv}}.
 Proof.
  unfold GAdv_body1,GAdv_body0_gen,GAdv_body0.
  inline eE3B1 G.
  decMR_tac eE3B1.
  Opaque leb.
  unfold inv3; eqobsrel_tail; unfold implMR, req_mem_rel, EP1, andR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2; bprop; intros H; decompose [and] H; clear H.
  rewrite H3, H4, H5; repeat split; intros.
  auto.
  bprop; repeat split.
  intros; apply leb_correct; apply leb_complete in H2; auto.
  apply leb_correct; apply leb_complete in H5; omega'.
  destruct H as [H _]; apply not_is_true_false in H; apply leb_complete_conv in H.
  apply leb_correct; omega'.
  
  bprop;  repeat split.
  intros; apply leb_correct; apply leb_complete in H2; auto.
  apply leb_correct; apply leb_complete in H5; omega'.
  destruct H as [H _]; apply not_is_true_false in H; apply leb_complete_conv in H.
  apply leb_correct; omega'.

  bprop; repeat split.
  intros; apply leb_correct; apply leb_complete in H2; auto.
  apply leb_correct; apply leb_complete in H5; omega'.
  destruct H as [H _]; apply not_is_true_false in H; apply leb_complete_conv in H.
  apply leb_correct; omega'.
 Qed.

 Definition iE3B1 := iEiEi H_body0 G_body2 Dec_body3_bad1.

 Definition iE3B1GA :=
  let piH := my_add_refl_info eE3B1 H in
   my_add_info GAdv Vset.empty Vset.empty iE3B1 iE3B1 piH GAdv_body1_inv3.

 Lemma Dec_body3_bad1_inv3 :
  EqObsInv inv3 
  {{Ydef, Y', bad1, c, LH, R', Dc, bad, LG}}
  E3B1 Dec_body3_bad1 
  E3B1 Dec_body3_bad1
  {{bad1, Dc, LH, bad, LG, mn}}.
 Proof.
  inline iE3B1GA G.
  decMR_tac iE3B1GA.
  cp_test ((qD +! qG) <! (Elen LG)).
  unfold inv3; eqobsrel_tail; unfold implMR, req_mem_rel, EP1, andR.
  simpl; unfold O.eval_op; simpl.
  intros k m1 m2 (H1, H2).
  repeat rewrite is_true_andb in H2.
  decompose [and] H2; clear H2.
  rewrite  H6, H, H4, H5; trivial.
  cp_test testD.
  rewrite proj1_MR, proj1_MR; eqobs_in iE3B1GA.
  eqobs_tl iE3B1GA.
  inline iE3B1GA H.
  decMR_tac iE3B1GA.
  Opaque leb.
  unfold inv3; eqobsrel_tail; unfold implMR, req_mem_rel, EP1, andR, notR.
  simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H1 H2].
  repeat rewrite is_true_andb in H2; decompose [and] H2; clear H2.

  assert (WW:impb (m1 bad1)
   (leb (qD_poly k + qG_poly k + 1) (Datatypes.S (length (m1 LG))))).
   rewrite is_true_impb in H3 |- *.
   intro Hbad; apply leb_correct; apply leb_complete in H3; auto.
  rewrite WW, H4, H3; clear WW.
  rewrite <- is_true_negb, negb_orb, is_true_andb, is_true_negb, is_true_negb in H; destruct H.
  assert (WW:leb (Datatypes.S (m1 Dc)) (qD_poly k)).
   rewrite not_is_true_false in H; apply leb_complete_conv in H.
   apply leb_correct; omega'.
  rewrite WW; clear WW.
  assert (WW:leb (length (m1 LG)) (m1 Dc + m1 Gc)).
   apply leb_complete in H6; apply leb_correct; omega'.
  assert (WW':leb (length (m1 LG)) (Datatypes.S (m1 Dc + m1 Gc))).
  apply leb_complete in WW; apply leb_correct; omega'.
  rewrite WW'.
  Transparent leb.
  simpl; rewrite WW; simpl.
  repeat split.
  Opaque leb.
 Qed.

 Definition iE3B1_inv :=
  adv_info (my_add_info Dec Vset.empty Vset.empty iE3B1 iE3B1 iE3B1GA 
   Dec_body3_bad1_inv3).

 Lemma PrG2_2_G2_3 : forall k (m:Mem.t k), 
  Pr E2 G2 m (EP k bad) == Pr E3 G2 m (EP k bad).
 Proof.
  intros k m; set (mb := m{!bad1 <-- false!}).
  transitivity (Pr E2B1 G2 mb (EP k bad)).
   unfold mb; rewrite set_bad; apply EqObs_Pr with {{Y', g_a}}.
   deadcode iE2E2B1; eqobs_in iE2E2B1.
  transitivity (Pr E3B1 G2 mb (EP k bad));
   [ | unfold mb; rewrite set_bad; apply EqObs_Pr with {{Y', g_a}}; 
    deadcode iE3B1E3; eqobs_in iE3B1E3].
  apply Uabs_diff_0_eq.
  transitivity (Pr E3B1 G2 mb (EP k bad1)).
  apply upto_bad_Uabs_diff with i_bad23.
  trivial.
  vm_compute; trivial.
  apply is_lossless_correct with (refl1_info iE3B1E3); vm_compute; trivial.
  apply Oeq_le.
  unfold mb; rewrite set_bad.
  unfold Pr.
  rewrite <- (mu_0 ([[ (bad1 <- false) :: G2 ]] E3B1 m)).
  apply equiv_deno with 
   (kreq_mem {{Y', g_a}}) 
   (req_mem_rel (fv_expr e_inv3) inv3); trivial.
  eqobs_tl iE3B1_inv; unfold inv3; eqobsrel_tail; simpl; unfold O.eval_op; simpl; red; trivial.
  unfold req_mem_rel, andR, inv3, charfun, EP, EP1, restr; simpl; unfold O.eval_op; simpl.
  intros m1 m2 (Heq, Hand); repeat rewrite is_true_andb in Hand; decompose [and] Hand; clear Hand.
  destruct (m1 bad1); trivial.
  unfold impb in H; simpl in H.
  elimtype False.
  repeat match goal with
  | H : is_true (leb _ _) |- _ => apply leb_complete in H
  end.
  omega'.
 Qed.


 (*********************************************)
 (* We now focus on the probability of bad    *)
 (* in E3 G3_                                 *)
 (* We start the modification of the          *)
 (* decryption oracle                         *)
 (*********************************************)

 Definition Dec_body_gen C := 
  [
   If testD || ((qD +! qG) <! (Elen LG)) then 
    [ mn <- (false | one_n) ]
   else
    ([
      LD <- (Ydef | c) |::| LD;
      Dc <- 1 +! Dc;
      st <- ap_finv c;
      s <- Efst st;
      t <- Esnd st 
     ] ++ C)
  ].

 Definition Dec_body4_gen C := 
  Dec_body_gen 
   [ 
    h <c- H with {s};
    r <- t |x| h;
    If (r in_dom LG) then
     [
       g <c- G with {r};
       m <- s |x2| g;
       If Esnd m =?= zero_k1
       then [ mn <- (true | Efst m) ]
       else [ mn <- (false | one_n) ]
     ]
    else 
     ([ g <c- G with {r}; m <- s |x2| g] ++ C)
   ].

 Definition end4 e :=
  [
   If Esnd m =?= zero_k1
   then [ bad2 <- true; mn <- e]
   else [ mn <- (false | one_n) ]
  ].

 Definition Dec_body3_bad2 := Dec_body4_gen (end4 (true | Efst m)).

 Definition Dec_body4_bad2 := Dec_body4_gen (end4 (false | one_n)).

 Definition Dec_body4 := Dec_body4_gen [mn <- (false | one_n)].

 Definition E3B2 := mkEnv H_body0 G_body2 Dec_body3_bad2.
 Definition E4B2 := mkEnv H_body0 G_body2 Dec_body4_bad2.
 Definition E4 := mkEnv H_body0 G_body2 Dec_body4.

 Definition iE3E3B2 := iEi_D H_body0 G_body2 Dec_body3 Dec_body3_bad2.
 Definition iE4B2E4 := iEi_D H_body0 G_body2 Dec_body4_bad2 Dec_body4.

 Lemma PR_3_bad : forall k (m:Mem.t k),
  (Pr E3 G2 m (EP k bad) <= 
   Pr E4 G2 m (EP k bad) + Pr E4B2 G2 (m{!bad2 <-- false!}) (EP k bad2))%U%tord.
 Proof.
   intros k m ; set (mb:= m{!bad2 <-- false!}).
   transitivity (Pr E3B2 G2 mb (EP k bad)).
    unfold mb; rewrite set_bad; apply Oeq_le; apply EqObs_Pr with {{Y', g_a}}.
    deadcode iE3E3B2; eqobs_in iE3E3B2.
   setoid_replace (Pr E4 G2 m (EP k bad)) with (Pr E4B2 G2 mb (EP k bad));
    [ | symmetry; unfold mb; rewrite set_bad; apply EqObs_Pr with {{Y', g_a}}; 
     deadcode iE4B2E4; eqobs_in iE4B2E4].
   apply Uabs_diff_le_plus.
   apply upto_bad_Uabs_diff with 
     (i_upto bad2 H_body0 G_body2 Dec_body3_bad2 H_body0 G_body2 Dec_body4_bad2).
   trivial.
   vm_compute; trivial.
   apply is_lossless_correct with (refl1_info iE4B2E4); vm_compute; trivial.
 Qed.


 (******************************************)
 (* We bound the probability of bad2 in    *)
 (* E4B2, G2                               *)
 (******************************************)

 Definition inv_Dc := EP1 (Dc <=! qD).

 Lemma dec_Dc : decMR inv_Dc.
 Proof.
  unfold inv_Dc; auto.
 Qed.

 Lemma dep_inv_Dc : depend_only_rel inv_Dc (fv_expr (Dc <=! qD)) Vset.empty.
 Proof.
  unfold inv_Dc; auto.
 Qed.

 Definition iGA_Dc Hbody Gbody Dbody : 
  eq_inv_info inv_Dc (mkEnv Hbody Gbody Dbody) (mkEnv Hbody Gbody Dbody) :=
   let E := mkEnv Hbody Gbody Dbody in
   let ie := @empty_inv_info inv_Dc _ _ dep_inv_Dc (refl_equal true) dec_Dc E E in
   let piH : eq_inv_info inv_Dc E E := add_refl_info H ie in
   let piG : eq_inv_info inv_Dc E E := add_refl_info G piH in
   let piGA : eq_inv_info inv_Dc E E := add_refl_info GAdv piG in
   piGA.

 Definition ID := {{Y', Ydef, bad, R', LG, LH, Gc, Dc, c}}.
 Definition OD := {{bad, LG, LH, Dc, mn}}.

 Definition IDc Hbody Gbody Dbody Other 
   (HD: EqObsInv inv_Dc
          (Vset.union Other ID)
          (mkEnv Hbody Gbody Dbody) Dbody
          (mkEnv Hbody Gbody Dbody) Dbody
          (Vset.union Other OD)) :=
   let E := mkEnv Hbody Gbody Dbody in
   let piGA : eq_inv_info inv_Dc E E := iGA_Dc Hbody Gbody Dbody in
   let piD : eq_inv_info inv_Dc E E := add_info Dec Vset.empty Vset.empty piGA HD in
   adv_info piD.

 Section Pr_4_Bad2.

  Variable k : nat.

  Let bad_K := @bad_K k bad2 Dc qD (fcte nat ([1/2]^k1 k))%U.

  Definition epr : PrBad_info E4B2 bad_K.
   unfold bad_K; apply empty_bad_K.
   vm_compute; trivial.
  Defined.

  Definition ipr4 :=
   let prH := add_prbad_comp epr H in
   let prG := add_prbad_comp prH G in
    add_prbad_comp prG GAdv.

  Definition iE4B2 := iEiEi H_body0 G_body2 Dec_body4_bad2.

  Lemma inv_bad4_Dec : inv_bad E4B2 bad_K Dec_body4_bad2.
  Proof.
   apply inv_bad_if.
   apply check_inv_bad_c_correct with ipr4; trivial.
   apply EqObs_inv_bad with (1:=prb_dep_correct ipr4) (I:=Vset.add bad2 ID)
    (c:=
     [ 
      h <c- H with {Efst (ap_finv c)};
      If !(Esnd (ap_finv c) |x| h in_dom LG)
      _then [ rGk1 <$- {0,1}^k1;
      If rGk1 =?= zero_k1 _then [ bad2 <- true]
     ];
     Dc <- 1 +! Dc
    ]).
   (* Equivalence *)
   ep iE4B2; deadcode iE4B2; swap iE4B2.
   sinline_r iE4B2 G.
   eqobs_ctxt iE4B2.
   cp_test (Esnd (ap_finv c) |x| h in_dom LG); [eqobs_in | rewrite proj1_MR].
   apply EqObs_trans with E4B2
   [ rGk1 <$- {0,1}^k1; GR'k1 <- Esnd (Efst (ap_finv c)) |x| rGk1;
     If GR'k1 =?= zero_k1 _then [bad2 <- true]  ].
   apply EqObs_trans with E4B2
   [ GR'k1 <$- {0,1}^k1; rGk1 <- Esnd (Efst (ap_finv c)) |x| GR'k1;
     If GR'k1 =?= zero_k1 _then [bad2 <- true]  ].
   deadcode; alloc_r GR'k1 rGk1; ep; deadcode; eqobs_in.
   eqobs_tl; union_mod.
   eapply equiv_strengthen; 
    [ | eapply equiv_weaken; [ | apply optimistic_sampling_inv; trivial] ].
   simpl; intros; eapply req_mem_weaken; eauto.
   vm_compute; trivial.
   simpl; intros; eapply req_mem_weaken; eauto.
   vm_compute; trivial.
   discriminate.
   ep; deadcode; eqobs_in.
   (* inv_bad *)
   apply inv_bad_cons.
   apply check_inv_bad_c_correct with ipr4; trivial.
   apply inv_bad_c.
   (* range *)
   unfold range; intros.
   rewrite deno_cons_elim, Mlet_simpl.
   compute_assertion HH XX (modify (refl1_info iE4B2) Vset.empty 
    [
     If !(Esnd (ap_finv c) |x| h in_dom LG)
     _then [rGk1 <$- {0,1}^k1; If rGk1 =?= zero_k1 _then [bad2 <- true] ]
    ]); apply modify_correct in HH.
   rewrite (Modify_deno_elim HH); apply zero_mu.
   intros m1; rewrite deno_assign_elim; apply H; split; [ | trivial].
   simpl; unfold O.eval_op; simpl.
   mem_upd_simpl; trivial.
   rewrite plus_comm; trivial.
   (* Pr *)
   unfold Pr; intros.
   rewrite deno_cons_elim, Mlet_simpl, deno_cond_elim.
   case (@E.eval_expr _ T.Bool (!(Esnd (ap_finv c) |x| h in_dom LG)) m).
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   set (F:= fun zero => (charfun (fun v => T.i_eqb k BS_k1 v zero))).
   apply Ole_trans with (mu (sum_support (T.default k BS_k1)
    (E.eval_support {0,1}^k1 m)) (F (E.eval_expr zero_k1 m))).
   apply mu_le_compat; [trivial | intros v].
 Opaque deno.
   generalize H; rewrite deno_cond_elim; unfold F, EP, charfun, restr; 
   simpl; unfold O.eval_op; simpl; 
   rewrite Mem.get_upd_same; clear H; intros H.
   destruct (T.i_eqb k _ v (Bvect_false (k1 k))); [auto | ].
   rewrite (deno_nil_elim E4B2 (m {!rGk1 <-- v!})).
   rewrite (deno_assign_elim E4B2 Dc (1+!Dc) (m {!rGk1 <-- v!})).
   repeat (rewrite Mem.get_upd_diff; [ | discriminate]); rewrite H; auto.
   rewrite (@Pr_bs_support _ (T.default k BS_k1) (E.eval_expr zero_k1 m) F).
   trivial.
   intros x Hdiff; unfold F,charfun, restr.
   case_eq (T.i_eqb k BS_k1 x (E.eval_expr zero_k1 m)); [ | trivial].
   simpl; unfold O.eval_op; simpl.
   rewrite (is_true_Ti_eqb k BS_k1 x (Bvect_false (k1 k))).
   intros Heq; elim (Hdiff Heq).
   unfold F,charfun, restr; simpl; unfold O.eval_op; simpl.
   rewrite Ti_eqb_refl; trivial.
   rewrite deno_nil_elim, deno_assign_elim.
   generalize H; unfold charfun,restr, EP; 
    simpl; unfold O.eval_op; simpl; intros H1.
   rewrite Mem.get_upd_diff, H1; [trivial | discriminate].
  Qed.

  Definition ipR4 :=
   let prDA := add_prbad ipr4 Dec inv_bad4_Dec in
   let prA := 
    add_prbad_adv prDA (A_wf_E H_body0 G_body2 Dec_body4_bad2 GAdv_body1) in
    add_prbad_adv prA (A'_wf_E H_body0 G_body2 Dec_body4_bad2 GAdv_body1).

  Lemma Pr_4_bad2 : forall m, 
   (Pr E4B2 G2 (m{!bad2 <-- false!}) (EP k bad2) <= qD_poly k /2^k1 k)%tord.
  Proof.
   intros m.
   assert (range (EP k (Dc <=! qD)) ([[G2]] E4B2 (m {!bad2 <-- false!}))).
   apply mu_range.
   transitivity (mu ([[G2]] E4B2 (m {!bad2 <-- false!})) (fun a : Mem.t k => 1%U)).
   apply equiv_deno with (kreq_mem {{bad2, Y', g_a}}) (req_mem_rel {{Dc}} inv_Dc).
   trivial.
    
   assert (W:EqObsInv inv_Dc (Vset.add bad2 ID) 
    E4B2 Dec_body4_bad2 E4B2 Dec_body4_bad2 (Vset.add bad2 OD)).
   set (iGA:=iGA_Dc H_body0 G_body2 Dec_body4_bad2).
   cp_test iGA (testD || ((qD +! qG) <! (Elen LG))).
   rewrite proj1_MR; eqobs_in iGA.
   eqobs_tl iGA;
   unfold inv_Dc; eqobsrel_tail; unfold implMR, andR, notR, EP1; 
    simpl; unfold O.eval_op; simpl.
   intros k' m1 m2 (_,(H1, (H2, _))).
   apply leb_complete in H1; apply leb_correct.
   apply not_is_true_false in H2; apply orb_false_elim in H2; destruct H2.
   apply orb_false_elim in H; destruct H.
   apply leb_complete_conv in H; omega'.
   
   set (iDc:=IDc {{bad2}} W).
   eqobs_tl iDc.
   unfold inv_Dc; eqobsrel_tail; unfold implMR; intros; reflexivity.
   
   unfold EP; intros m1 m2 (H1, H2).
   unfold inv_Dc, EP1 in H2; rewrite H2; trivial.
   trivial. 
   apply is_lossless_correct with (refl1_info iE4B2); vm_compute; trivial.
   rewrite (Pr_range _ (EP k bad2) H), andP_comm.
   unfold Pr, G2, G2_; simpl app.
   repeat rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
   eapply Ole_trans; [apply PrBad_cte with (u:= ([1/2]^k1 k)%U);
    [ apply check_inv_bad_c_correct with ipR4; vm_compute; trivial | | ] | ];
   simpl; unfold O.eval_op; simpl; unfold O.eval_op; simpl; mem_upd_simpl.
  Qed.

 End Pr_4_Bad2.

 (** We resume the proof *)

 Lemma PrG0_bad_4 : forall k (m:Mem.t k),
  (Uabs_diff (Pr E0 G0 m (EP k (b=?=b'))) [1/2] <= 
  Pr E4 G2 m (EP k bad) + qD_poly k/2^k1 k)%U%tord.
 Proof.
  intros k m; rewrite PrG0_bad.
  eapply Ole_trans; [apply Oeq_le; apply (PrG2_2_G2_3 m) | ].
  eapply Ole_trans; [apply PR_3_bad | ].
  apply Uplus_le_compat; [trivial | ].
  apply Pr_4_bad2.
 Qed.


 (*********************************************)
 (* We now focus on the probability of bad    *)
 (* in E4 G2                                  *)
 (* We continue the modification of the       *)
 (* decryption oracle                         *)
 (*********************************************)

 Definition Dec_body5_aux C Cg :=
  [
   h <c- H with {s};
   r <- t |x| h;
   If r in_dom LG
   then [
    g <c- G with {r};
    m <- s |x2| g;
    If Esnd m =?= zero_k1
    then C
    else [mn <- (false | one_n)]
   ]
   else (Cg ++ [mn <- (false | one_n)])
  ].

 Definition callG := [ g <c- G with {r} ].

 Definition callG2 C :=
  C ++
  [ 
   rGn <$- {0,1}^n;
   rGk1 <$- {0,1}^k1;
   LG <- (r | (rGn | rGk1)) |::| LG
  ].

 Definition Dec_body5_gen C1 C2 :=
  Dec_body_gen 
  [
   If s in_dom LH then Dec_body5_aux [mn <- (true | Efst m)] callG
   else Dec_body5_aux C1 (callG2 C2)
  ].

 Definition Dec_body4_bad1 := 
  Dec_body5_gen
   [bad1 <- true; mn <- (true | Efst m)]                                  
   [If R' =?= r _then [bad1 <- true; bad <- true] ]. 

 Definition Dec_body5_bad1 := 
  Dec_body5_gen
   [bad1 <- true; mn <- (false | one_n)]  
   [If R' =?= r _then [bad1 <- true] ].

 Definition Dec_body5 := Dec_body5_gen [mn <- (false | one_n)] nil.

 Definition E4B1 := mkEnv H_body0 G_body2 Dec_body4_bad1.
 Definition E5B1 := mkEnv H_body0 G_body2 Dec_body5_bad1.
 Definition E5 := mkEnv H_body0 G_body2 Dec_body5.

 Definition iE4E4B1_pre := iEi_D H_body0 G_body2 Dec_body4 Dec_body4_bad1.

 Lemma EqObs_Dec4_Dec4b1 :
  EqObsInv trueR ID E4 Dec_body4 E4B1 Dec_body4_bad1 OD.
 Proof.
  sinline iE4E4B1_pre G. 
  ep iE4E4B1_pre.
  deadcode iE4E4B1_pre.
  eqobs_in iE4E4B1_pre.
 Qed. 

 Definition iE4E4B1 := 
  adv_info (add_info Dec Vset.empty {{bad1}} iE4E4B1_pre EqObs_Dec4_Dec4b1).

 Definition iE5B1E5 := iEi_D H_body0 G_body2 Dec_body5_bad1 Dec_body5.

 Lemma PR_4_bad : forall k (m:Mem.t k),
  (Pr E4 G2 m (EP k bad) <= 
  Pr E5 G2 m (EP k bad) + Pr E5B1 G2 (m{!bad1 <-- false!}) (EP k bad1))%U%tord.
 Proof.
  intros k m; set (mb:= m{!bad1 <-- false!}).
  transitivity (Pr E4B1 G2 mb (EP k bad)).
  unfold mb; rewrite set_bad; apply Oeq_le; apply EqObs_Pr with {{Y', g_a}}.
  unfold G2, G2_. 
  deadcode iE4E4B1. 
  eqobs_in iE4E4B1.
  setoid_replace (Pr E5 G2 m (EP k bad)) with (Pr E5B1 G2 mb (EP k bad));
   [ | symmetry; unfold mb; rewrite set_bad; apply EqObs_Pr with {{Y', g_a}}; 
    deadcode iE5B1E5; eqobs_in iE5B1E5].
  apply Uabs_diff_le_plus.
  apply upto_bad_Uabs_diff with 
   (i_upto bad1 H_body0 G_body2 Dec_body4_bad1 H_body0 G_body2 Dec_body5_bad1).
  trivial.
  vm_compute; trivial.
  apply is_lossless_correct with (refl1_info iE5B1E5); vm_compute; trivial.
 Qed.
 
 Section Pr_5_Bad1.

  Variable k : nat.

  Let bad_K := @bad_K k bad1 Dc qD 
   (fcte nat (((qD_poly k + qG_poly k) /2^k0 k) + [1/2]^k0 k))%U.

  Definition epr5 : PrBad_info E5B1 bad_K.
   unfold bad_K; apply empty_bad_K.
   vm_compute; trivial.
  Defined.

  Definition ipr5 :=
   let prH := add_prbad_comp epr5 H in
   let prG := add_prbad_comp prH G in add_prbad_comp prG GAdv.

  Definition iE5B1 := iEiEi H_body0 G_body2 Dec_body5_bad1.

  Definition inv_bad1 := (EP1 bad1) |-> (EP2 bad1).

  Lemma dec_inv_bad1 : decMR inv_bad1.
  Proof.
   unfold inv_bad1; auto.
  Qed.

  Lemma dep_inv_bad1 : depend_only_rel inv_bad1 
   (Vset.union (fv_expr bad1) Vset.empty) (Vset.union Vset.empty (fv_expr bad1)).
  Proof.
   unfold inv_bad1; auto.
  Qed.

  Definition eE5B1 : eq_inv_info inv_bad1 E5B1 E5B1 :=
   let ie := @empty_inv_info inv_bad1 _ _ dep_inv_bad1 (refl_equal true) 
    dec_inv_bad1 E5B1 E5B1 in
   let piH : eq_inv_info inv_bad1 E5B1 E5B1 := add_refl_info H ie in
   let piG : eq_inv_info inv_bad1 E5B1 E5B1 := add_refl_info G piH in
   piG.
  
 Lemma inv_bad5_Dec : inv_bad E5B1 bad_K Dec_body5_bad1.
 Proof.
  apply equiv_inv_bad with 
   [
     If testD || ((qD +! qG) <! (Elen LG)) then nil
     else [
        Dc <- 1 +! Dc;
        If !((qD +! qG) <! (Elen LG)) _then [
           h <$- {0,1}^k0;
           If (h in_dom LG) || (R' =?= h) _then [ bad1 <- true ]
        ]
     ]
   ].
  sinline eE5B1 H; sinline eE5B1 G.
  ep eE5B1; deadcode eE5B1.
  cp_test ((qD +! qG) <! (Elen LG)); rewrite proj1_MR.
  eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl; intros k2 m1 m2 Heq;
   rewrite Heq; trivial.
  cp_test (E.Eop O.Oor {qD <=! Dc, E.Eop O.Oand {Ydef =?= true, Y' =?= c} }); rewrite proj1_MR.
  eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl; intros k2 m1 m2 Heq;
   rewrite Heq; trivial.
  cp_test ( Efst (ap_finv c) in_dom LH); rewrite proj1_MR.
  apply equiv_strengthen with (kreq_mem {{R',Dc,LG,bad1}}).
   intros k2 m1 m2 Heq; rewrite Heq; trivial.
  apply EqObs_post_trans_l with (1:= dep_inv_bad1) (E2 := E5B1) 
    (c2:= [Dc <- 1 +! Dc; h <$- {0,1}^k0; If (h in_dom LG) || (R' =?= h) _then nil]).
  deadcode; eqobs_in.
  eqobs_hd.
  cp_test ( E.Eop O.Oor {h in_dom LG, R' =?= h}); rewrite proj1_MR;
  unfold inv_bad1; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl;
    intros k2 m1 m2 H; trivial.
    rewrite (H _ bad1); trivial.
  apply equiv_strengthen with (kreq_mem {{c,R',Dc,LG,bad1}}).
   intros k2 m1 m2 Heq; rewrite Heq; trivial.
  eqobs_hd_n 1.
  apply EqObs_post_trans_l with (1:= dep_inv_bad1) (E2 := E5B1) 
    (c2:= [h <$- {0,1}^k0; rH <- Esnd (ap_finv c) |x| h;
           If (rH in_dom LG) then [
              If (Esnd (Efst (ap_finv c)) |x| Esnd (LG [{rH}]) =?= zero_k1) _then [ bad1 <- true ]
           ] else [ If (R' =?= rH) _then [bad1 <- true] ] ]).
  ep; deadcode; eqobs_in.
  apply EqObs_post_trans_l with (1:= dep_inv_bad1) (E2 := E5B1) 
    (c2:= [rH <$- {0,1}^k0; h <- Esnd (ap_finv c) |x| rH;
           If (rH in_dom LG) then [
              If (Esnd (Efst (ap_finv c)) |x| Esnd (LG [{rH}]) =?= zero_k1) _then [ bad1 <- true ]
           ] else [ If (R' =?= rH) _then [bad1 <- true] ] ]).
  eqobs_tl; union_mod.
  eapply equiv_strengthen; [ | eapply equiv_weaken; [ | apply optimistic_sampling_inv; trivial] ].
  simpl; intros; eapply req_mem_weaken; eauto.
  vm_compute; trivial.
  simpl; intros; eapply req_mem_weaken; eauto. 
  vm_compute; trivial.
  discriminate.
  ep; deadcode eE5B1. alloc_l eE5B1 rH h; ep eE5B1; deadcode eE5B1; eqobs_hd.
  cp_test (h in_dom LG); rewrite proj1_MR.
  cp_test (Esnd (Efst (ap_finv c)) |x| Esnd (LG [{h}]) =?= zero_k1); rewrite proj1_MR.
  unfold inv_bad1; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl;
    intros k2 m1 m2 H; trivial.
  unfold inv_bad1; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl;
    intros k2 m1 m2 H; trivial.
  unfold inv_bad1; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl;
    intros k2 m1 m2 H; split; trivial.
    rewrite (H _ bad1); trivial.
  apply inv_bad_if.
  apply check_inv_bad_c_correct with ipr5; trivial.
  apply inv_bad_c.
  (* range *)
  unfold range; intros.
  rewrite deno_cons_elim,Mlet_simpl, deno_assign_elim, deno_cond_elim.
  match goal with |- context  [E.eval_expr ?e ?m] => set (m1:= m); destruct (@E.eval_expr k T.Bool e m1) end.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  transitivity (mu  (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m1))
                 (fun _ => D0)).
  symmetry; apply mu_zero.
  apply mu_stable_eq; refine (ford_eq_intro _); intros v.
  rewrite deno_cond_elim.
  match goal with |- context  [E.eval_expr ?e ?m] => destruct (@E.eval_expr k T.Bool e m) end.
  rewrite deno_assign_elim; apply H; split; [ | trivial].
  unfold m1; simpl; unfold O.eval_op; simpl;
   mem_upd_simpl; trivial.
  rewrite plus_comm; trivial.
  rewrite deno_nil_elim; apply H; split; [ | trivial].
  unfold m1; simpl; unfold O.eval_op; simpl;
   mem_upd_simpl; trivial.
   rewrite plus_comm; trivial.
  rewrite deno_nil_elim; apply H; split; [ | trivial].
  unfold m1; simpl; unfold O.eval_op; simpl;
   mem_upd_simpl; trivial.
   rewrite plus_comm; trivial.
  (* Pr *)
  unfold Pr; intros m Heq.
  rewrite deno_cons_elim,Mlet_simpl,deno_assign_elim,deno_cond_elim.
  match goal with |- context  [E.eval_expr ?e ?m] => set (m1:= m); case_eq (@E.eval_expr k T.Bool e m1); intros Heq1; [change (is_true (@E.eval_expr k T.Bool e m1)) in Heq1 | ] end.
  set (def := T.default k (T.Pair BS_k0 BS_nk1)).
  simpl in Heq1; unfold O.eval_op in Heq1; simpl in Heq1.
  rewrite is_true_negb, is_true_leb in Heq1.
  assert (W:length (m1 LG) <= qD_poly k + qG_poly k) by omega'.
  transitivity 
    (mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))
     (fplus (sigma_fun 
               (fun i v => charfun  (T.i_eqb k BS_k0 v) (fst (nth i (m1 LG) def)))
               (length (m1 LG)))
            (charfun (T.i_eqb k BS_k0 (m1 R'))))).
   rewrite deno_cons_elim, Mlet_simpl,deno_random_elim.
   apply mu_monotonic; intro v; unfold fplus,sigma_fun.
   rewrite (sigma_finite_sum def
    (fun w : T.interp k (T.Pair BS_k0 BS_nk1) =>
     charfun (T.i_eqb k BS_k0 v) (fst w))).
   rewrite deno_cond_elim.
   match goal with |- context  [E.eval_expr ?e ?m] => case_eq (@E.eval_expr k T.Bool e m); intros Heq2; [change (is_true (@E.eval_expr k T.Bool e m)) in Heq2 | ] end.
   change (is_true (orb (E.eval_expr (h in_dom LG) (m1 {!h <-- v!})) 
                        (E.eval_expr (R' =?= h) (m1{!h <-- v!})))) in Heq2.
   rewrite is_true_orb in Heq2; destruct Heq2.
   match goal with |- (_ <= Uplus ?x1 ?x2)%tord => transitivity x1; [ | trivial] end.
   rewrite deno_assign_elim.
   generalize H; clear H; unfold charfun, EP, restr, fone, m1; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   generalize (m LG).
   induction i; simpl; intros; try discriminate.
   destruct (@T.i_eqb k BS_k0 v
        (@fst (Ut.interp k Bitstring_k0)
           (Ut.interp k Bitstring_n * Ut.interp k Bitstring_k1) a));Usimpl; auto.
   match goal with |- (_ <= Uplus ?x1 ?x2)%tord => transitivity x2; [ | trivial ] end.
   rewrite deno_assign_elim.
   generalize H; clear H; unfold charfun, EP, restr, fone, m1; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   intros H; rewrite H; trivial.
   rewrite deno_nil_elim; generalize Heq; unfold charfun, EP, restr, fone, m1; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   intros H; rewrite H; trivial.
   rewrite mu_le_plus; unfold fcte.
   apply Uplus_le_compat.
   rewrite mu_sigma_le, Nmult_sigma.
   eapply Ole_trans; [| eapply sigma_incr; apply W].
   apply sigma_le_compat.
   intros i Hi.
   set (li := fst (nth i (m1 LG) def)); simpl in li; fold li.
   apply (@Pr_bs_support (k0 k) (T.default k BS_k0) li
    (fun e v => if T.i_eqb k BS_k0 v e then 1 else @D0 _))%U.
   intros x; rewrite <- (is_true_Ti_eqb k BS_k0 x).
   destruct (T.i_eqb k BS_k0 x li); intros H; [ elim H | ]; trivial.
   rewrite Ti_eqb_refl; trivial.
     apply (@Pr_bs_support (k0 k) (T.default k BS_k0) (m1 R')
    (fun e v => if T.i_eqb k BS_k0 e v then 1 else @D0 _))%U.
   intros x Hdiff. apply sym_not_eq in Hdiff.
   rewrite <- (@is_true_Ti_eqb k BS_k0), not_is_true_false in Hdiff; rewrite Hdiff; trivial.
   rewrite Ti_eqb_refl; trivial.
   rewrite deno_nil_elim; generalize Heq; unfold m1, charfun, restr, EP; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  intros H; rewrite H; trivial.
 Qed. 

 
 Definition ipR5 :=
  let prDA := add_prbad ipr5 Dec inv_bad5_Dec in
  let prA := 
   add_prbad_adv prDA (A_wf_E H_body0 G_body2 Dec_body5_bad1 GAdv_body1) in
   add_prbad_adv prA (A'_wf_E H_body0 G_body2 Dec_body5_bad1 GAdv_body1).

 Lemma Pr_5_bad1 : forall m, 
  (Pr E5B1 G2 (m{!bad1 <-- false!}) (EP k bad1) <= 
   (qD_poly k) */ ((qD_poly k + qG_poly k)/2^k0 k) + [1/2]^k0 k)%U%tord.
 Proof.
   intros m.
   assert (range (EP k (Dc <=! qD)) ([[G2]] E5B1 (m {!bad1 <-- false!}))).
   apply mu_range.
   transitivity (mu ([[G2]] E5B1 (m {!bad1 <-- false!})) (fun a : Mem.t k => 1%U)).
   apply equiv_deno with 
    (kreq_mem {{bad1, Y', g_a}}) 
    (req_mem_rel {{Dc}} inv_Dc); trivial.
   assert (W:EqObsInv inv_Dc (Vset.add bad1 ID) 
    E5B1 Dec_body5_bad1 E5B1 Dec_body5_bad1 (Vset.add bad1 OD)).
   set (iGA:=iGA_Dc H_body0 G_body2 Dec_body5_bad1).
   cp_test iGA (testD || ((qD +! qG) <! (Elen LG))).
   rewrite proj1_MR; eqobs_in iGA.
   eqobs_tl iGA;
   unfold inv_Dc; eqobsrel_tail; unfold implMR, andR, notR, EP1; 
    simpl; unfold O.eval_op; simpl.
   intros k' m1 m2 (_,(H1, (H2, _))).
   apply leb_complete in H1; apply leb_correct.
   apply not_is_true_false in H2; apply orb_false_elim in H2; destruct H2.
   apply orb_false_elim in H; destruct H.
   apply leb_complete_conv in H; omega'.
   
   set (iDc:=IDc {{bad1}} W).
   eqobs_tl iDc.
   unfold inv_Dc; eqobsrel_tail; unfold implMR; intros; reflexivity.
   
   unfold EP; intros m1 m2 (H1, H2).
   unfold inv_Dc, EP1 in H2; rewrite H2; trivial.
   apply is_lossless_correct with (refl1_info iE5B1); vm_compute; trivial.
   rewrite  (Pr_range _ (EP k bad1) H), andP_comm.
   unfold Pr, G2, G2_; simpl app.
   repeat rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  eapply Ole_trans; [
    apply PrBad_cte with (u:=((qD_poly k + qG_poly k)/2^k0 k + [1/2]^k0 k)%U);
     [ apply check_inv_bad_c_correct with ipR5; vm_compute; trivial | | ] | ];
   simpl; unfold O.eval_op; simpl; unfold O.eval_op; simpl; mem_upd_simpl.
  Qed.

 End Pr_5_Bad1.

 (** We resume the proof *)

 Lemma PrG0_bad_5 : forall k (m:Mem.t k),
  (Uabs_diff (Pr E0 G0 m (EP k (b=?=b'))) [1/2] <= 
   Pr E5 G2 m (EP k bad) + 
   ((qD_poly k) */ (qD_poly k + qG_poly k)/2^k0 k + [1/2]^k0 k) + 
   qD_poly k/2^k1 k)%U%tord.
 Proof.
  intros k m; rewrite PrG0_bad_4.
  apply Uplus_le_compat; [ | trivial].
  eapply Ole_trans; [apply PR_4_bad | apply Uplus_le_compat; trivial].
  apply Pr_5_bad1.
 Qed.


 (****************************************)
 (* We want to remove the call to H when *)
 (* s is not in dom LH, we start by      *)
 (* removing the call to G               *)
 (****************************************)

 Definition Gbaddr b r0 :=
  [ 
   rGn <$- {0,1}^n;
   rGk1 <$- {0,1}^k1;
   LGb <- (r0 | (b | (rGn | rGk1))) |::| LGb 
  ].

 Definition G_body2b_gen CrG Cbad2:= 
  [
   If !(R in_dom LGb) then ([If R' =?= R _then [bad <- true] ] ++ Gbaddr false R)
   else [
    If Efst (LGb[{R}]) 
    then CrG ++ Cbad2 ++ [LGb <- LGb Upd R <| (false | (rGn | rGk1)) ]
    else [ rGn <- Efst (Esnd (LGb [{R}])); rGk1 <- Esnd (Esnd (LGb [{R}])) ]
   ]
  ].

Definition Dec_body_gen_b test_bad1 :=
 [
  If E.Eop O.Oor {testD, (qD +! qG) <! (Elen LGb)} then [mn <- (false | one_n)]
  else [
   LD <- (Ydef | c) |::| LD;
   Dc <- 1 +! Dc;
   st <- ap_finv c;
   s <- Efst (st);
   t <- Esnd (st);
   If s in_dom LH then 
    [
     h <c- H with {s};
     r <- t |x| h;
     If r in_dom LGb then 
      [
       If Efst (LGb[{r}]) then 
        [
         g <- Esnd (LGb[{r}]);
         m <- s |x2| g 
        ] ++ test_bad1
       else 
        [
         g <- Esnd (LGb[{r}]);
         m <- s |x2| g;
         If Esnd m =?= zero_k1 then [mn <- (true | Efst m)]
         else [mn <- (false | one_n)]                
        ] 
       ] 
      else 
       [ 
        If R' =?= r _then [bad <- true];
        rGn <$- {0,1}^n;
        rGk1 <$- {0,1}^k1;
        LGb <- (r | (true | (rGn | rGk1))) |::| LGb;
        mn <- (false | one_n)
       ]
      ] 
     else 
      [
       h <c- H with {s};
       r <- t |x| h;
       If !(r in_dom LGb) _then 
        [
         rGn <$- {0,1}^n;
         rGk1 <$- {0,1}^k1;
         LGb <- (r | (true | (rGn | rGk1))) |::| LGb
        ];
       mn <- (false | one_n)
      ]
    ]
  ].

 Definition test_bad1_5b := 
  [
   If Esnd m =?= zero_k1 then [bad1 <- true; mn <- (true | Efst m)]
   else [mn <- (false | one_n)]
  ].

 Definition test_bad1_6b := 
  [
   If Esnd m =?= zero_k1 then [bad1 <- true; mn <- (false | one_n)]
   else [mn <- (false | one_n)]
  ].

 Definition test_bad1_nothing := [ mn <- (false | one_n) ].

 Definition G_body2b := 
  G_body2b_gen
  [ rGn <- Efst (Esnd (LGb [{R}])); rGk1 <- Esnd (Esnd (LGb [{R}])) ]
  nil.

 Definition Dec_body5b := Dec_body_gen_b test_bad1_5b.

 Definition E5b := mkEnv H_body0 G_body2b Dec_body5b.

 Definition Dec_body6b := Dec_body_gen_b test_bad1_6b.

 Definition E6b := mkEnv H_body0 G_body2b Dec_body6b.

 Definition test_exists :=
  E.Eexists tc (   
   let c := Esnd tc in     
   let s := Efst (ap_finv c) in
   let t := Esnd (ap_finv c) in
   let h := LH[{s}] in
   let r := t |x| h in
   let g := (rGn | rGk1) in
   let m := s |x2| g in
   (r =?= R) && (s in_dom LH) &&  (Esnd m =?= zero_k1)
  ) LD.

 Definition G_body2b_bad2 :=
  G_body2b_gen
  [ rGn <- Efst (Esnd (LGb [{R}])); rGk1 <- Esnd (Esnd (LGb [{R}])) ]
  [ If test_exists _then [bad2 <- true] ].

 Definition Dec_body7 := Dec_body_gen_b test_bad1_nothing.

 Definition E7 := mkEnv H_body0 G_body2b_bad2 Dec_body7.

 Definition G_body2r_bad2 := 
  G_body2b_gen
  [ rGn <$- {0,1}^n; rGk1 <$- {0,1}^k1]
  [ If test_exists _then [bad2 <- true] ].

 Definition Dec_body7r := Dec_body_gen_b test_bad1_nothing.

 Definition E7r := mkEnv H_body0 G_body2r_bad2 Dec_body7r.

 Definition Bad1 := 
  E.Eexists tc ( 
   let c := Esnd tc in
   let s := Efst (ap_finv c) in
   let t := Esnd (ap_finv c) in
   let h := LH[{s}] in
   let r := t |x| h in  
   let g := Esnd (LGb[{r}]) in
   let m := s |x2| g in
   (s in_dom LH) && (r in_dom LGb) && Efst (LGb[{r}]) && (Esnd m =?= zero_k1)
  ) LD.

 Definition sample_body (LGhd LGtl : Var.var T_assoc_b) :=
  [ 
   aux <- Ehd LGtl;
   LGtl <- Etl LGtl;
   If Efst (Esnd aux) _then [
    rGn_aux <$- {0,1}^n;
    rGk1_aux <$- {0,1}^k1;
    aux <- (Efst aux | (true | (rGn_aux | rGk1_aux)))
   ];
   LGhd <- LGhd |++| aux |::| Nil _
  ].

 Definition sample_while (LGhd LGtl : Var.var T_assoc_b) :=
  while !(LGtl =?= Nil _) do sample_body LGhd LGtl.

 Definition sample_true (LGhd LGtl :Var.var T_assoc_b) (LG : E.expr T_assoc_b):= 
  [
   LGhd <- Nil _;
   LGtl <- LG;
   sample_while LGhd LGtl
  ].

 Definition SLGb :=
  sample_true LGb_hd LGb_tl LGb ++
  [ 
   LGb <- LGb_hd; 
   (* This part resets the auxiliary variables *)
   LGb_hd <- Nil _;
   rGn_aux <$- {0,1}^n;
   rGk1_aux <$- {0,1}^k1;
   aux <- (R' | (true | (rGn_aux | rGk1_aux)))
  ].

 (*******************************************************************************)
 (*   E5 ---> E5b:                                                              *)
 (*   inlining of G in Dec, invariant LG = map (fun (x, p) => (x,snd p) LGb)    *)
 (*   E5b ---> E6b:                                                             *)
 (*   FL bad1                                                                   *)
 (*   E6b ---> E7:                                                              *)
 (*   invariant EP1 bad1  ==> EP2 (bad2 || Bad1)                                *) 
 (*   E7 ---> E7r:                                                              *)
 (*   lazy sampling using SLGb                                                  *)
 (*   E7, G2b == E7, SLGb ++ G2b == E7r, G2b ++ SLGb                            *)
 (*   We should prove Pr E7r (G2b ++ SLGb) (EP (bad2 || Bad1))                  *)
 (*   Remark : once we are not focusing on bad2 we can remove the assignment    *)
 (*   true in LGb                                                               *)
 (*******************************************************************************)

 (** E5 ---> E5b **)
 Fixpoint forall2b (A B:Type) (f : A -> B -> bool) 
  (la:list A) (lb:list B) {struct la} : bool :=
  match la, lb with
  | nil, nil => true
  | a1::la, b1::lb => andb (f a1 b1) (forall2b f la lb)
  | _, _ => false
  end.

 Definition eq_LG_LGb k 
  (v1:T.interp k (T.Pair BS_k0 BS_nk1)) 
  (v2:T.interp k (T.Pair BS_k0 (T.Pair T.Bool BS_nk1))) :=
  andb (T.i_eqb k BS_k0 (fst v1) (fst v2)) 
  (T.i_eqb k BS_nk1 (snd v1) (snd (snd v2))).

 Definition inv_LGLGb : mem_rel :=
  fun k m1 m2 => forall2b (@eq_LG_LGb k) (m1 LG) (m2 LGb).

 Lemma dec_LGLGb : decMR inv_LGLGb.
 Proof.
  unfold inv_LGLGb; red; intros.
  match goal with |- sumbool (is_true ?X) _ => destruct X end; auto.
  right; discriminate.
 Qed.

 Lemma dep_inv_LGLGb : depend_only_rel inv_LGLGb {{LG}} {{LGb}}.
 Proof.
  unfold inv_Dc; red.
  intros k m1 m2 m1' m2' H1 H2 H3.
  unfold inv_LGLGb; rewrite <- (H1 _ LG), <- (H2 _ LGb); trivial.
 Qed.

 Definition e_b E1 E2 : eq_inv_info inv_LGLGb E1 E2 := 
  @empty_inv_info inv_LGLGb _ _ dep_inv_LGLGb (refl_equal true) dec_LGLGb E1 E2.

 Lemma inv_LGLGb_assoc : forall k (m1 m2:Mem.t k) e,
  E.eval_expr e m1 = E.eval_expr e m2 ->
  inv_LGLGb m1 m2 ->
  E.eval_expr (LG[{e}]) m1 = snd (E.eval_expr (LGb[{e}]) m2).
 Proof. 
  unfold inv_LGLGb; simpl; unfold O.eval_op; simpl; unfold O.assoc.
  intros k m1 m2 e Heq; rewrite <- Heq.
  generalize (E.eval_expr e m1) (m1 LG) (m2 LGb).
  intros v l1 l2; generalize l1 l2; clear l1 l2; induction l1; destruct l2; trivial;
   try discriminate; simpl; intros.
  rewrite is_true_andb in H; destruct H.
  unfold eq_LG_LGb in H.
  rewrite is_true_andb, is_true_Ti_eqb, is_true_Ti_eqb in H; destruct H.
  rewrite H; destruct (T.i_eqb k BS_k0 v (fst i)); auto.
 Qed.

 Lemma inv_LGLGb_dom : forall k (m1 m2:Mem.t k) e,
  E.eval_expr e m1 = E.eval_expr e m2 ->
  inv_LGLGb m1 m2 ->
  E.eval_expr (e in_dom LG) m1 = E.eval_expr (e in_dom LGb) m2.
 Proof.
  unfold inv_LGLGb; intros k m1 m2 e; simpl; unfold O.eval_op; simpl; intros Heq; rewrite <- Heq.
  generalize (E.eval_expr e m1) (m1 LG) (m2 LGb).
  intros v l1 l2; generalize l1 l2; clear l1 l2; induction l1; destruct l2; trivial;
   try discriminate; simpl; intros.
  rewrite is_true_andb in H; destruct H.
  unfold eq_LG_LGb in H; rewrite is_true_andb in H; destruct H.
  rewrite is_true_Ti_eqb in H; rewrite H, IHl1 with l2; trivial.
 Qed.

 Lemma G_body2_G_body2b : forall E1 E2,
  EqObsInv inv_LGLGb 
  {{R, R', bad}} 
  E1 G_body2 
  E2 G_body2b 
  {{rGn, rGk1, bad}}.
 Proof.
  intros Ev1 Ev2; set (ie:= e_b Ev1 Ev2).
  match goal with |- EqObsInv _ ?I _ _ _ _ _ =>
  assert (H0:forall (k : nat) (m1 m2 : Mem.t k),
      req_mem_rel I inv_LGLGb k m1 m2 ->
      E.eval_expr (R in_dom LG) m1 =
      E.eval_expr (R in_dom LGb) m2);
   [intros k m1 m2 (H1, H2);
    apply inv_LGLGb_dom; trivial;
    apply depend_only_fv_expr; eapply req_mem_weaken; [ | apply H1]; reflexivity 
   | cp_test_l (R in_dom LG);
     [ ep_eq_r (R in_dom LGb) true
     | ep_eq_r (R in_dom LGb) false];
     [ intros k m1 m2 (H1, H2); rewrite <-(H0 k m1 m2 H1); trivial
     | idtac 
     | intros k m1 m2 (H1, H2); rewrite <- (H0 k m1 m2 H1), <- not_is_true_false; trivial
     | rewrite proj1_MR; eqobs_hd ie
     ]
   ]
  end.
  cp_test_r (Efst (LGb [{R}])); rewrite proj1_MR.
  rewrite req_mem_rel_assoc.
  set (P:= inv_LGLGb /-\ EP1 (R in_dom LG)); set (I:={{R, R', bad}}).
  assert (depend_only_rel P (Vset.union {{LG}} (fv_expr (R in_dom LG)))
   (Vset.union {{LGb}} Vset.empty)).
  unfold P; auto using dep_inv_LGLGb.
  apply equiv_cons with (req_mem_rel (Vset.add rGn I) P);
     [ eapply equiv_strengthen; [ | apply equiv_assign] | ].
  unfold upd_para; intros; apply req_mem_rel_upd_in with (2:= H); trivial.
  change (fst (E.eval_expr(LG [{R}]) m1) = fst (snd (E.eval_expr (LGb [{R}]) m2))).
  destruct H1 as (H2, (H3, H4)); rewrite inv_LGLGb_assoc with (2:= H3); trivial.
  apply (H2 _ R); trivial.
  apply equiv_cons with (req_mem_rel (Vset.add rGk1 (Vset.add rGn I)) P);
     [ eapply equiv_strengthen; [ | apply equiv_assign] | ].
  unfold upd_para; intros; apply req_mem_rel_upd_in with (2:= H); trivial.
  change (snd (E.eval_expr(LG [{R}]) m1) = snd (snd (E.eval_expr (LGb [{R}]) m2))).
  destruct H1 as (H2, (H3, H4)); rewrite inv_LGLGb_assoc with (2:= H3); trivial.
  apply (H2 _ R); trivial.
  unfold P, I; clear P I H.
  eqobsrel_tail; simpl; unfold implMR, O.eval_op; simpl; unfold inv_LGLGb.
  intros k m1 m2 (H1, (H2, H3)).
  rewrite Mem.get_upd_same, <- (H1 _ R); [ | trivial].
  generalize H2 H3; unfold EP1; simpl; unfold O.eval_op; simpl.
  generalize (m1 R) (m1 LG) (m2 LGb); intros v l1 l2; generalize l1 l2;
  clear H1 H2 H3 m1 m2 l1 l2.
  unfold O.assoc; induction l1; destruct l2; simpl; trivial; try (intros; discriminate).
  unfold eq_LG_LGb.
  repeat (rewrite is_true_andb || rewrite is_true_Ti_eqb).
  destruct i as (i1, i2); simpl; intros ((H1,H2),H3); rewrite H1.
  destruct (T.i_eqb k BS_k0 v i1); intros; simpl.
  rewrite H2, H3; destruct i2 as (p1,p2); destruct p2; simpl; repeat rewrite Ti_eqb_refl; trivial.
  rewrite H2; repeat rewrite Ti_eqb_refl; simpl; apply IHl1; trivial.
  rewrite proj1_MR; set (I:={{R, R', bad}}).
  apply equiv_cons with (req_mem_rel (Vset.add rGn I) inv_LGLGb);
     [ eapply equiv_strengthen; [ | apply equiv_assign] | ].
  unfold upd_para; intros; apply req_mem_rel_upd_in with (2:= dep_inv_LGLGb); trivial.
  change (fst (E.eval_expr(LG [{R}]) m1) = fst (snd (E.eval_expr (LGb [{R}]) m2))).
  destruct H as (H2, H3); rewrite inv_LGLGb_assoc with (2:= H3); trivial.
  apply (H2 _ R); trivial.
  apply equiv_cons with (req_mem_rel (Vset.add rGk1 (Vset.add rGn I)) inv_LGLGb);
     [ eapply equiv_strengthen; [ | apply equiv_assign] | ].
  unfold upd_para; intros; apply req_mem_rel_upd_in with (2:= dep_inv_LGLGb); trivial.
  change (snd (E.eval_expr(LG [{R}]) m1) = snd (snd (E.eval_expr (LGb [{R}]) m2))).
  destruct H as (H2, H3); rewrite inv_LGLGb_assoc with (2:= H3); trivial.
  apply (H2 _ R); trivial.
  eqobs_in ie.
  eqobsrel_tail; simpl; unfold implMR, O.eval_op, inv_LGLGb; simpl; intros k m1 m2 (H1, H2).
  repeat rewrite Mem.get_upd_same; simpl; unfold eq_LG_LGb at 1.
  rewrite (H1 _ R), (H1 _ rGn), (H1 _ rGk1); trivial.
  simpl; repeat rewrite Ti_eqb_refl; trivial.
 Qed.

 Definition eE5E5b : eq_inv_info inv_LGLGb E5 E5b :=
  let ie := e_b E5 E5b in
  let piH : eq_inv_info inv_LGLGb E5 E5b := add_refl_info H ie in
  let piG : eq_inv_info inv_LGLGb E5 E5b := 
   add_info G Vset.empty Vset.empty piH (G_body2_G_body2b _ _) in
  piG.

 Lemma GAdv_body5_GAdv_body5b :
  EqObsInv inv_LGLGb 
  {{Gc, Radv, R', bad}}
  E5  GAdv_body1 
  E5b GAdv_body1 
  {{Gc, rGadv, bad}}.
 Proof. 
  eqobs_in eE5E5b. 
 Qed.

 Lemma forall2b_length : forall A B (f:A -> B -> bool) l1 l2,
  forall2b f l1 l2 ->
  length l1 = length l2.
 Proof.
  induction l1; destruct l2; simpl; trivial; intros; try discriminate.
  rewrite is_true_andb in H; destruct H; rewrite (IHl1 l2); trivial.
 Qed.

 Lemma Dec_body5_Dec_body5b :
  EqObsInv inv_LGLGb 
  (Vset.remove LG ID)
  E5  Dec_body5 
  E5b Dec_body5b 
  (Vset.remove LG OD).
 Proof.
   assert (forall (k : nat) (m1 m2 : Mem.t k),
      req_mem_rel (Vset.remove LG ID) inv_LGLGb k m1 m2 ->
      E.eval_expr (E.Eop O.Oor {testD, (qD +! qG) <! (Elen LG)}) m1 =
      E.eval_expr (E.Eop O.Oor {testD, (qD +! qG) <! (Elen LGb)}) m2).
    intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
    rewrite (H1 _ Dc), (H1 _ Y'), (H1 _ Ydef), (H1 _ c); trivial.
    assert (W:= forall2b_length _ _ _ H2); simpl in W; rewrite W; trivial.
  cp_test_l (E.Eop O.Oor {testD, (qD +! qG) <! (Elen LG)});
  [ ep_eq_r (E.Eop O.Oor {testD, (qD +! qG) <! (Elen LGb)}) true
  | ep_eq_r (E.Eop O.Oor {testD, (qD +! qG) <! (Elen LGb)}) false].
    intros k m1 m2 (H1, H2); rewrite <- (H k m1 m2 H1); trivial.
 
  rewrite proj1_MR; eqobs_in eE5E5b.
  intros k m1 m2 (H1,H2); rewrite <- (H k m1 m2 H1), <- not_is_true_false; trivial.
  rewrite proj1_MR; eqobs_hd eE5E5b.

  cp_test eE5E5b (Efst (ap_finv c) in_dom LH); rewrite proj1_MR; eqobs_hd eE5E5b;
  match goal with |- EqObsInv _ ?I _ _ _ _ _ =>
  assert (forall (k : nat) (m1 m2 : Mem.t k),
   req_mem_rel I inv_LGLGb k m1 m2 ->
   E.eval_expr (t |x| h in_dom LG) m1 = E.eval_expr (t |x| h in_dom LGb) m2);
  [ intros k m1 m2 (H1, H2);
   apply inv_LGLGb_dom; trivial;
    apply depend_only_fv_expr; eapply req_mem_weaken; [ | apply H1]; reflexivity
   | ]
  end.
  inline eE5E5b G.
  auto using dec_LGLGb.
  ep; deadcode eE5E5b.
  cp_test_l (t |x| h in_dom LG);
     [ ep_eq_r (t |x| h in_dom LGb) true
     | ep_eq_r (t |x| h in_dom LGb) false];
     [ intros k m1 m2 (H1, H2); rewrite <-(H0 k m1 m2 H1); trivial
     | 
     | intros k m1 m2 (H1, H2); rewrite <- (H0 k m1 m2 H1), <- not_is_true_false; trivial
     | 
     ]; rewrite proj1_MR.
   deadcode eE5E5b.
   match goal with |- EqObsInv _ ?I _ _ _ _ _ =>
    assert (forall (k : nat) (m1 m2 : Mem.t k),
      req_mem_rel I inv_LGLGb k m1 m2 ->
      E.eval_expr (Esnd (s) |x| Esnd (LG [{t |x| h}]) =?= zero_k1) m1 =
      E.eval_expr (Esnd (s) |x| Esnd (Esnd (LGb [{t |x| h}])) =?= zero_k1) m2)
   end.
    intros k m1 m2 (H1, H2).
    assert (E.eval_expr (t |x| h) m1 = E.eval_expr (t |x| h) m2).
          apply depend_only_fv_expr; eapply req_mem_weaken; [ | apply H1]; reflexivity.
    generalize (@inv_LGLGb_assoc k m1 m2 (t |x| h) H3 H2).
    simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq, (H1 _ s); trivial.
   cp_test_l (Esnd (s) |x| Esnd (LG [{t |x| h}]) =?= zero_k1);
   [ ep_eq_r (Esnd (s) |x| Esnd (Esnd (LGb [{t |x| h}])) =?= zero_k1) true
   | ep_eq_r (Esnd (s) |x| Esnd (Esnd (LGb [{t |x| h}])) =?= zero_k1) false
   ].
   intros k m1 m2 (H2, H3); rewrite <- (H1 k m1 m2 H2); trivial.
   rewrite proj1_MR.
  eapply equiv_strengthen; [ | apply equiv_assign].
  intros k m1 m2 H4; case H4; intros H2 H3; split.
  match goal with |- kreq_mem _ (_ {! _ <-- ?x1!}) (_ {! _ <-- ?x2!}) => replace x1 with x2 end.
  unfold kreq_mem; eapply req_mem_weaken; [ | apply req_mem_update with (1:= H2)].
  vm_compute; trivial.
  assert (E.eval_expr (t |x| h) m1 = E.eval_expr (t |x| h) m2).
          apply depend_only_fv_expr; eapply req_mem_weaken; [ | apply H2]; reflexivity.
    generalize (@inv_LGLGb_assoc k m1 m2 (t |x| h) H5 H3).
    simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq, (H2 _ s); trivial.
  unfold inv_LGLGb; repeat rewrite Mem.get_upd_diff; try discriminate.
  exact H3.
  intros k m1 m2 (H2, H3); rewrite <- (H1 k m1 m2 H2).
  unfold notR,EP1 in H3; rewrite not_is_true_false in H3; trivial.
  rewrite proj1_MR; eqobs_in eE5E5b.
  eqobs_ctxt eE5E5b.
  eqobsrel_tail; simpl; unfold inv_LGLGb, O.eval_op; simpl.
  intros k m1 m2 (H1, H2); repeat rewrite Mem.get_upd_same.
  simpl; rewrite H2; unfold eq_LG_LGb; simpl.
  rewrite (H1 _ t), (H1 _ h), (H1 _ rGn), (H1 _ rGk1); trivial.
  repeat rewrite Ti_eqb_refl; trivial.

  inline eE5E5b G.
  auto using dec_LGLGb.
  ep; deadcode eE5E5b.
  cp_test_l (t |x| h in_dom LG);
     [ ep_eq_r (t |x| h in_dom LGb) true
     | ep_eq_r (t |x| h in_dom LGb) false];
     [ intros k m1 m2 (H1, H2); rewrite <-(H0 k m1 m2 H1); trivial
     | 
     | intros k m1 m2 (H1, H2); rewrite <- (H0 k m1 m2 H1), <- not_is_true_false; trivial
     | 
     ]; rewrite proj1_MR.
   eqobs_in eE5E5b.
   eqobs_ctxt eE5E5b.
   eqobsrel_tail; simpl; unfold inv_LGLGb,O.eval_op; simpl.
   intros k m1 m2 (H1, H2); repeat rewrite Mem.get_upd_same.
   simpl; rewrite H2; unfold eq_LG_LGb; simpl.
   rewrite (H1 _ t), (H1 _ h), (H1 _ rGn), (H1 _ rGk1); trivial.
   repeat rewrite Ti_eqb_refl; trivial.
 Qed.

 Definition iE5E5b : eq_inv_info inv_LGLGb E5 E5b :=
   let piGA : eq_inv_info inv_LGLGb E5 E5b := add_info GAdv Vset.empty Vset.empty eE5E5b GAdv_body5_GAdv_body5b in
   let piD : eq_inv_info inv_LGLGb E5 E5b := add_info Dec Vset.empty Vset.empty piGA Dec_body5_Dec_body5b in
   adv_info piD.

 Definition init1b :=
  [
   Ydef <- false;
   LGb <- Nil _;
   LH <- Nil _;
   LD <- Nil _;
   Dc <- 0;
   Gc <- 0;
   R' <$- {0,1}^k0
  ].

 Definition G2b := 
  [bad <- false] ++ init1b ++ SGR' ++ [S' <- (GR'n | GR'k1)] ++ tail2.

 Lemma PR_5_bad : forall k (m:Mem.t k),
  Pr E5 G2 m (EP k bad) == Pr E5b G2b (m{! bad1 <-- false !}) (EP k bad).
 Proof.
  intros k m; rewrite set_bad.
  intros; apply EqObs_Pr with {{Y', g_a}}.
  apply equiv_weaken with (req_mem_rel (fv_expr bad) inv_LGLGb).
  intros k2 m1 m2 (H1, H2); trivial.
  eqobs_tl iE5E5b.
  eqobsrel_tail.
  unfold implMR, inv_LGLGb; simpl; unfold O.eval_op; simpl.
  intros; mem_upd_simpl.
 Qed.

 (* E5b --> E6b: upto bad1               *)

 Definition iE6b := iEiEi H_body0 G_body2b Dec_body6b.

 Lemma PR_5b_bad : forall k (m:Mem.t k),
  (Pr E5b G2b (m{! bad1 <-- false !}) (EP k bad) <= 
   Pr E6b G2b (m{! bad1 <-- false !}) (EP k bad) + 
   Pr E6b G2b (m{!bad1 <-- false!}) (EP k bad1))%U%tord.
 Proof.
  intros k m ; set (mb:= m{!bad1 <-- false!}).
  apply Uabs_diff_le_plus.
  apply upto_bad_Uabs_diff with 
   (i_upto bad1 H_body0 G_body2b Dec_body5b H_body0 G_body2b Dec_body6b).
  trivial.
  vm_compute; trivial.
  apply is_lossless_correct with (refl1_info iE6b); vm_compute; trivial.
 Qed.

 (* E6b --> E7b : invariant EP1 bad1  ==> EP2 (bad2 || Bad1)  *)

 Definition inv6_7 := impR (EP1 bad1) (EP2 (bad2 || Bad1)).

 Lemma dec_inv6_7 : decMR inv6_7.
 Proof. 
  unfold inv6_7; auto. 
 Qed.

 Lemma dep_inv6_7 : depend_only_rel inv6_7 
  (Vset.union (fv_expr bad1) Vset.empty)
  (Vset.union Vset.empty (fv_expr (bad2 || Bad1))).
 Proof. 
  unfold inv6_7; auto. 
 Qed.

 Definition eE6bE7 : eq_inv_info inv6_7 E6b E7 := 
  @empty_inv_info inv6_7 _ _ dep_inv6_7 (refl_equal true) dec_inv6_7 E6b E7.

 Lemma G_body2b_G_body2b_bad2 : 
  EqObsInv inv6_7 
  {{LGb, R, R', bad}}
  E6b G_body2b E7 G_body2b_bad2 
  {{LGb, rGn, rGk1, bad}}.
 Proof.
  unfold G_body2b_bad2, G_body2b, G_body2b_gen.
  cp_test (R in_dom LGb).
  cp_test (Efst (LGb[{R}])).
 
  cp_test_r (E.Eexists tc
        (E.Eop O.Oand
           {E.Eop O.Oand
              {Esnd (ap_finv Esnd (tc)) |x| (LH [{Efst (ap_finv Esnd (tc))}]) =?=
               R, Efst (ap_finv Esnd (tc)) in_dom LH},
           Esnd (Efst (ap_finv Esnd (tc))) |x| Esnd (Esnd (LGb [{R}])) =?=
           zero_k1}) LD).
  unfold inv6_7, Bad1; eqobsrel_tail; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; trivial.
  unfold inv6_7, Bad1; eqobsrel_tail; unfold implMR, EP1, EP2, andR, notR, impR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; intros; clear H.
  apply H2 in H1; clear H2; rewrite is_true_orb in H1; destruct H1.
  rewrite H; trivial.
  rewrite is_true_orb; right.
  rewrite is_true_existsb in H |- *; destruct H as (X, (H1, H2)); exists X; split; [trivial | ].
  repeat (rewrite Mem.get_upd_same in H2 || (rewrite Mem.get_upd_diff in H2; [ | discriminate])).
  rewrite is_true_andb in H2; destruct H2.
  rewrite is_true_Ti_eqb in H2; rewrite is_true_andb in H; destruct H.
  rewrite is_true_andb in H; destruct H.
  rewrite is_true_existsb in H, H9.
  change UOp.Tnk1 with BS_nk1.
  destruct X as (bY, C). simpl snd in *.
  apply BVxor_eq in H2.
  set (sC := (@fst (Ut.interp k Bitstring_n * Ut.interp k Bitstring_k1)
                     (Ut.interp k Bitstring_k0) (@finv k C))) in *.
  set (tC := (@snd (Ut.interp k Bitstring_n * Ut.interp k Bitstring_k1)
                     (Ut.interp k Bitstring_k0) (@finv k C))) in *.
  repeat (rewrite Mem.get_upd_same in H6 || (rewrite Mem.get_upd_diff in H6; [ | discriminate])).
  set (hC := (@O.assoc
   (Ut.interp k Bitstring_n * Ut.interp k Bitstring_k1)
   (Ut.interp k Bitstring_k0)
   (T.i_eqb k UOp.Tnk1 sC)
   (Ut.default k Bitstring_k0)
   (m2 LH))) in *.
  set (rC := (BVxor (k0 k) tC hC)) in *.
  set (rG := (@O.assoc (Ut.interp k Bitstring_k0)
           (bool * (Ut.interp k Bitstring_n * Ut.interp k Bitstring_k1))
           (T.i_eqb k BS_k0 rC)
           (false, (Ut.default k Bitstring_n, Ut.default k Bitstring_k1))
           (m2 LGb))) in *.
  assert (rC <> m2 R).
    intros Heq; elim H6.
    rewrite is_true_existsb; exists (bY,C); split; [trivial | ].
    mem_upd_simpl.
   
    simpl snd; fold sC; rewrite <- Heq, is_true_andb.
    fold rG; rewrite H2, BVxor_nilpotent, Ti_eqb_refl, Ti_eqb_refl.
    split; [ | trivial].
    rewrite is_true_andb; split; [trivial | ].
    rewrite is_true_existsb; exact H.
    rewrite (@assoc_upd_diff k BS_k0 Tbnk1); trivial.
    rewrite H2; trivial.
  rewrite <- is_true_existsb in H.
  change UOp.Tnk1 with BS_nk1 in H; rewrite H.
  change UOp.Tnk1 with BS_nk1 in hC; fold hC; fold rC.
  repeat rewrite is_true_andb; split.
  split; trivial.
  split; trivial.
  rewrite (@existsb_upd_diff k BS_k0 Tbnk1); trivial.
  rewrite is_true_existsb; trivial.
  rewrite is_true_Ti_eqb; apply BVxor_nilpotent.

  repeat rewrite proj1_MR; eqobs_in eE6bE7.
  repeat rewrite req_mem_rel_assoc.
  rewrite <- andR_assoc, proj1_MR.
  match goal with
  |- equiv (req_mem_rel ?I ?P) _ [?i1; ?i2; ?i3; ?i4] _ _ _ =>
      change [i1; i2; i3; i4] with ([i1; i2; i3]++[i4]);
      apply equiv_app with (req_mem_rel (Vset.add rGn (Vset.add rGk1 I)) P)
  end.
  union_mod.
  auto using dec_inv6_7.
  assert (W:= depend_only_andR dep_inv6_7 (depend_only_notR (@depend_only_EP1 (R in_dom LGb)))).
  set (c1 := [If R' =?= R _then [bad <- true]; rGn <$- {0,1}^n; rGk1 <$- {0,1}^k1]).
  compute_assertion Heq res (modify2 eE6bE7 c1 c1).
  apply modify2_correct in Heq; destruct Heq.
  apply equiv_inv_Modify with (1:= W) (2:= H) (3:= H0). 
  vm_compute; trivial.
  vm_compute; trivial.
  vm_compute; trivial.
  eqobs_in.
  unfold inv6_7; eqobsrel_tail; unfold EP1, EP2, notR, andR, impR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 (H1, (H2, H3)) H4.
  rewrite is_true_orb in H2 |- *; destruct H2; auto.
  right.
  rewrite is_true_existsb in *.
  destruct H as ((b,c), (H2, H5)).
  exists (b,c); split; trivial.
  repeat rewrite is_true_andb in H5; decompose [and] H5; clear H5.
  repeat rewrite Mem.get_upd_same in *.
  repeat rewrite is_true_andb; repeat split.
  repeat (rewrite Mem.get_upd_diff in H; [ | discriminate]); trivial.
  rewrite is_true_orb; right.
  repeat (rewrite Mem.get_upd_diff in H8; [ | discriminate]); trivial.
  unfold O.assoc; simpl.
  repeat (rewrite Mem.get_upd_diff in H7; [ | discriminate]).
  match goal with
  |- context [T.i_eqb k BS_k0 ?x1 ?x2] => 
     case_eq (T.i_eqb k BS_k0 x1 x2); intros Heq;
     [ change (is_true (T.i_eqb k BS_k0 x1 x2)) in Heq | trivial ]
  end.
  rewrite is_true_Ti_eqb in Heq; elim H3.
  rewrite is_true_existsb in H8.
  repeat (rewrite Mem.get_upd_diff in H8; [ | discriminate]).
  rewrite (H1 _ LGb), (H1 _ R); trivial.
  destruct H8 as (x, (W1, W2)); exists x; split; trivial.
  rewrite <- Heq; trivial.
  unfold O.assoc; simpl.
  repeat (rewrite Mem.get_upd_diff in H7; [ | discriminate]).
  repeat (rewrite Mem.get_upd_diff in H0; [ | discriminate]).
  match goal with
  |- context [T.i_eqb k BS_k0 ?x1 ?x2] => 
     case_eq (T.i_eqb k BS_k0 x1 x2); intros Heq;
     [ change (is_true (T.i_eqb k BS_k0 x1 x2)) in Heq | trivial ]
  end.
  rewrite is_true_Ti_eqb in Heq; elim H3.
  rewrite is_true_existsb in H8.
  repeat (rewrite Mem.get_upd_diff in H8; [ | discriminate]).
  rewrite (H1 _ LGb), (H1 _ R); trivial.
  destruct H8 as (x, (W1, W2)); exists x; split; trivial.
  rewrite <- Heq; trivial.
 Qed.

 Lemma H_body0_inv6_7 : 
  EqObsInv inv6_7 
  {{LH, S}}
  E6b H_body0 
  E7 H_body0 
  {{LH, rH}}.
 Proof.
  unfold H_body0.
  cp_test (S in_dom LH).
  rewrite proj1_MR; eqobs_in eE6bE7.
  unfold inv6_7, Bad1; eqobsrel_tail; unfold impR, andR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H; intros.
  apply H2 in H3; clear H2; rewrite is_true_orb in H3; destruct H3.
  rewrite H2; trivial.
  rewrite is_true_orb; right.
  change UOp.Tnk1 with BS_nk1 in H2; rewrite is_true_existsb in H2; destruct H2 as ((bC,C), (Hin, H2)).
  rewrite is_true_existsb; exists (bC,C); split; trivial.
  repeat (rewrite Mem.get_upd_same in H2 || (rewrite Mem.get_upd_diff in H2; [ | discriminate])); trivial.
  repeat rewrite is_true_andb in H2; decompose [and] H2; clear H2.
  rewrite H3, orb_true_r; simpl.
  unfold O.assoc; simpl.
  case_eq (T.i_eqb k BS_nk1 (@fst (Ut.interp k Bitstring_n * Ut.interp k Bitstring_k1)
   (Ut.interp k Bitstring_k0) (@finv k C)) (m2 S)); intros.
  change (is_true (T.i_eqb k BS_nk1 (fst (finv (k:=k) C)) (m2 S))) in H2;
   rewrite is_true_Ti_eqb in H2.
  elim H4; rewrite <- H2; trivial.
  repeat rewrite is_true_andb; repeat split; trivial.
 Qed.

 Definition iE6bE7_d : eq_inv_info inv6_7 E6b E7 :=
  let piH : eq_inv_info inv6_7 E6b E7:= 
   add_info H Vset.empty Vset.empty eE6bE7 H_body0_inv6_7 in
  let piG : eq_inv_info inv6_7 E6b E7 := 
   add_info G {{bad1}} {{bad2}} piH G_body2b_G_body2b_bad2 in
  piG.

 Lemma Dec_body6b_Dec_body7 : 
  EqObsInv inv6_7 
  (Vset.add LD (Vset.add LGb (Vset.remove LG ID)))
  E6b Dec_body6b 
  E7 Dec_body7 
  (Vset.add LD (Vset.add LGb (Vset.remove LG OD))).
 Proof.
  unfold Dec_body6b, Dec_body_gen_b.
  cp_test (E.Eop O.Oor {testD, (qD +! qG) <! (Elen LGb)}).
  rewrite proj1_MR; eqobs_in iE6bE7_d.
  inline iE6bE7_d H.
   auto using dec_inv6_7.
  ep iE6bE7_d; deadcode iE6bE7_d.
  cp_test (Efst (ap_finv c) in_dom LH).
 
  cp_test (Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}]) in_dom LGb).
  cp_test (Efst (LGb [{Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}])}])).
  cp_test (Esnd (Efst (ap_finv c))
      |x| Esnd (Esnd (LGb [{Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}])}])) =?=
      zero_k1).
 
  unfold inv6_7, Bad1; eqobsrel_tail; unfold impR, andR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H; intros.
  rewrite is_true_orb; right.
  change UOp.Tnk1 with BS_nk1 in H7; rewrite H7.
  change UOp.Tnk1 with BS_nk1 in H11; rewrite H11.
  change UOp.Tnk1 with BS_nk1 in H9; rewrite H9.
  change UOp.Tnk1 with BS_nk1 in H12; rewrite H12; trivial.
 
  unfold inv6_7, Bad1; eqobsrel_tail; unfold impR, andR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H; intros.
  apply H2 in H; rewrite is_true_orb in H; destruct H as [H | H].
  rewrite H; trivial.
  rewrite is_true_existsb in H; destruct H as ((bC,C), (Hin,H)).
  rewrite is_true_orb; right.
  rewrite is_true_orb; right.
  rewrite is_true_existsb; exists (bC,C); split; trivial.
  repeat (rewrite Mem.get_upd_same in H || (rewrite Mem.get_upd_diff in H; [ | discriminate])); trivial.
 
  cp_test (Esnd (Efst (ap_finv c))
      |x| Esnd (Esnd (LGb [{Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}])}])) =?=
      zero_k1).

  unfold inv6_7, Bad1; eqobsrel_tail; unfold impR, andR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H; intros.
  apply H2 in H; rewrite is_true_orb in H; destruct H as [H | H].
  rewrite H; trivial.
  rewrite is_true_existsb in H; destruct H as ((bC,C), (Hin,H)).
  rewrite is_true_orb; right.
  rewrite is_true_orb; right.
  rewrite is_true_existsb; exists (bC,C); split; trivial.
  repeat (rewrite Mem.get_upd_same in H || (rewrite Mem.get_upd_diff in H; [ | discriminate])); trivial.

  unfold inv6_7, Bad1; eqobsrel_tail; unfold impR, andR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H; intros.
  apply H2 in H; rewrite is_true_orb in H; destruct H as [H | H].
  rewrite H; trivial.
  rewrite is_true_existsb in H; destruct H as ((bC,C), (Hin,H)).
  rewrite is_true_orb; right.
  rewrite is_true_orb; right.
  rewrite is_true_existsb; exists (bC,C); split; trivial.
  repeat (rewrite Mem.get_upd_same in H || (rewrite Mem.get_upd_diff in H; [ | discriminate])); trivial.

  unfold inv6_7, Bad1; eqobsrel_tail; unfold impR, andR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H; intros.
  split; intros.
  apply H2 in H10; clear H2; rewrite is_true_orb in H10; destruct H10 as [H10 | H10].
  rewrite H10; trivial.
  rewrite is_true_existsb in H10; destruct H10 as ((bC,C), (Hin,H10)).
  rewrite is_true_orb; right.
  rewrite is_true_orb; right.
  rewrite is_true_existsb; exists (bC,C); split; trivial.
  repeat (rewrite Mem.get_upd_same in H10 || (rewrite Mem.get_upd_diff in H10; [ | discriminate])); trivial.
  change UOp.Tnk1 with BS_nk1 in H10; repeat rewrite is_true_andb in H10; decompose [and] H10; clear H10.
  rewrite H2, H14, orb_true_r; simpl.
  change UOp.Tnk1 with BS_nk1 in H8; match goal with
  |- is_true (fst (O.assoc (T.i_eqb k BS_k0 ?X) _ ((?Y,_)::_)) && _) => 
    set (xorC:= X); set (xorc:=Y) in * end.
  unfold O.assoc; simpl.
  case_eq (T.i_eqb k BS_k0 xorC xorc); intros.
  change (is_true (T.i_eqb k BS_k0 xorC xorc)) in H10; rewrite is_true_Ti_eqb in H10.
  elim H8; rewrite <- H10; trivial.
  rewrite is_true_andb; split; trivial.

  apply H2 in H10; clear H2; rewrite is_true_orb in H10; destruct H10 as [H10 | H10].
  rewrite H10; trivial.
  rewrite is_true_existsb in H10; destruct H10 as ((bC,C), (Hin,H10)).
  rewrite is_true_orb; right.
  rewrite is_true_orb; right.
  rewrite is_true_existsb; exists (bC,C); split; trivial.
  repeat (rewrite Mem.get_upd_same in H10 || (rewrite Mem.get_upd_diff in H10; [ | discriminate])); trivial.
  change UOp.Tnk1 with BS_nk1 in H10; repeat rewrite is_true_andb in H10; decompose [and] H10; clear H10.
  rewrite H2, H14, orb_true_r; simpl.
  change UOp.Tnk1 with BS_nk1 in H8; match goal with
  |- is_true (fst (O.assoc (T.i_eqb k BS_k0 ?X) _ ((?Y,_)::_)) && _) => 
    set (xorC:= X); set (xorc:=Y) in * end.
  unfold O.assoc; simpl.
  case_eq (T.i_eqb k BS_k0 xorC xorc); intros.
  change (is_true (T.i_eqb k BS_k0 xorC xorc)) in H10; rewrite is_true_Ti_eqb in H10.
  elim H8; rewrite <- H10; trivial.
  rewrite is_true_andb; split; trivial.

  unfold inv6_7, Bad1; eqobsrel_tail; unfold impR, andR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H; intros; split; intros.

  apply H2 in H9; clear H2.
  rewrite is_true_orb in H9; destruct H9 as [H10 | H10].
  rewrite H10; trivial. 
  rewrite is_true_orb; right.
  rewrite Ti_eqb_refl; simpl.
  unfold O.assoc; simpl; rewrite Ti_eqb_refl; simpl; rewrite Ti_eqb_refl; simpl.
  rewrite is_true_existsb in H10; destruct H10 as ((bC, C), H10).
  rewrite is_true_orb; right.
  rewrite is_true_existsb; exists (bC,C).
  repeat (rewrite Mem.get_upd_same in H10 || (rewrite Mem.get_upd_diff in H10; [ | discriminate])); trivial.
  repeat rewrite is_true_andb in H10; decompose [and] H10; clear H10.
  change UOp.Tnk1 with BS_nk1 in H11; rewrite H11, orb_true_r; simpl; split; [trivial | ].
  rewrite is_true_Ti_eqb in H12; apply BVxor_eq in H12; simpl in *.
  set (sC := (@fst (Ut.interp k Bitstring_n * Ut.interp k Bitstring_k1)
                  (Ut.interp k Bitstring_k0) (@finv k C))) in *.
  set (sc := (@fst (Ut.interp k Bitstring_n * Ut.interp k Bitstring_k1)
                  (Ut.interp k Bitstring_k0) (@finv k (m2 c)))) in *.
  case_eq (T.i_eqb k BS_nk1 sC sc); intros.
  change (is_true (T.i_eqb k BS_nk1 sC sc)) in H9; rewrite is_true_Ti_eqb in H9; rewrite H9 in *.
  elim (H6 H11).
  rewrite is_true_andb; split.
  rewrite is_true_andb; split.
  rewrite is_true_orb; right.
  apply H14.
  match goal with 
   |- is_true (fst (match (if ?x then _ else _) with Some _ => _ | None => _ end)) => case_eq x; intros; simpl; trivial end.
  rewrite is_true_Ti_eqb.
  rewrite H12.
  match goal with |- BVxor _ ?XX ?YY = _ => replace XX with YY end.
  apply BVxor_nilpotent.
  match goal with |- snd (snd (match (if ?x then _ else _) with | Some _ => _ | None => _ end)) = _ => 
   case_eq x; intros; trivial end.
  destruct H4 as (_, H4).
  match type of H10 with ?XX = true => change (is_true XX) in H10 end.
  rewrite is_true_Ti_eqb in H10.
  rewrite <- H10, is_true_negb in H4; elim H4; trivial.
 
  apply H2 in H7; clear H2.
  rewrite is_true_orb in H7; destruct H7 as [H7 | H7].
  rewrite H7; trivial. 
  rewrite is_true_orb; right.
  rewrite Ti_eqb_refl; simpl.
  unfold O.assoc; simpl; rewrite Ti_eqb_refl; simpl.
  rewrite is_true_existsb in H7; destruct H7 as ((bC, C), H7).
  repeat (rewrite Mem.get_upd_same in H7 || (rewrite Mem.get_upd_diff in H7; [ | discriminate])); trivial.
  repeat rewrite is_true_andb in H7; decompose [and] H7; clear H7.
  rewrite is_true_orb; right.
  rewrite is_true_existsb; exists (bC, C); split; trivial.
  change UOp.Tnk1 with BS_nk1 in H9; rewrite H9, orb_true_r; simpl.
  rewrite is_true_Ti_eqb in H10; apply BVxor_eq in H10; simpl in *.
  set (sC := (@fst (Ut.interp k Bitstring_n * Ut.interp k Bitstring_k1)
                  (Ut.interp k Bitstring_k0) (@finv k C))) in *.
  set (sc := (@fst (Ut.interp k Bitstring_n * Ut.interp k Bitstring_k1)
                  (Ut.interp k Bitstring_k0) (@finv k (m2 c)))) in *.
  case_eq (T.i_eqb k BS_nk1 sC sc); intros.
  change (is_true (T.i_eqb k BS_nk1 sC sc)) in H7; rewrite is_true_Ti_eqb in H7; rewrite H7 in *.
  elim (H6 H9).
  rewrite is_true_andb; split.
  rewrite is_true_andb; split; trivial.
  rewrite is_true_Ti_eqb.
  rewrite H10; apply BVxor_nilpotent.
 Qed. 

 Definition iE6bE7 : eq_inv_info inv6_7 E6b E7 :=
  let piD : eq_inv_info inv6_7 E6b E7 := 
   add_info Dec {{bad1}} {{bad2}} iE6bE7_d Dec_body6b_Dec_body7 in
  let piGA : eq_inv_info inv6_7 E6b E7 := 
   add_refl_info_rm GAdv {{bad1}} {{bad2}} piD in
   adv_info piGA. 

 Lemma EqObs_E6b_E7 :
  equiv (kreq_mem {{Y',g_a}}) 
  E6b ((bad1 <- false) :: G2b) 
  E7 ((bad2 <- false) :: G2b)
  (req_mem_rel {{bad}} inv6_7).
 Proof.
  eqobs_tl iE6bE7.
  unfold inv6_7, Bad1; eqobsrel_tail; unfold impR, andR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2; auto.
 Qed.

 Lemma PR_5b_bad_7 : forall k m,
  (Pr E5b G2b (m{! bad1 <-- false !}) (EP k bad) <= 
   Pr E7 G2b (m{! bad2 <-- false !}) (EP k bad) +  
   Pr E7 G2b (m{!bad2 <-- false!}) (EP k (bad2 || Bad1)))%U%tord.
 Proof.
  intros k m; eapply Ole_trans; [apply PR_5b_bad | ].
  repeat rewrite set_bad.
  apply Uplus_le_compat.
  apply Oeq_le; apply equiv_deno with (1:= EqObs_E6b_E7); trivial.
  intros m1 m2 (H1, H2).
  unfold charfun, EP, restr, fone; simpl; rewrite (H1 _ bad); trivial.
  apply equiv_deno_le with (1:= EqObs_E6b_E7); trivial.
  unfold inv6_7, EP1, EP2, impR; intros m1 m2 (H1, H2).
  unfold charfun, EP, restr, fone.
  destruct (E.eval_expr bad1 m1); [ | trivial].
  rewrite H2; trivial.
 Qed.


 (* E7 ---> E7r:                                              *)
 (*       lazy sampling using SLGb                            *)
 (*         E7, G2b == E7, SLGb ++ G2b == E7r, G2b ++ SLGb    *)

 Definition XSLGb := {{LGb_hd, LGb_tl, LGb, rGn_aux, rGk1_aux, aux}}.

 Definition ISLGb := {{R'}}.

 Lemma Modify_SLGb : forall E, Modify E XSLGb SLGb.
 Proof.
  intro E. 
  compute_assertion X t1 (modify (refl1_info (empty_info E E)) Vset.empty SLGb).
  apply modify_correct in X; eapply Modify_weaken; [eauto | ].
  vm_compute; trivial.
 Qed.

 Lemma EqObs_SLGb : forall E1 E2, 
  EqObs (Vset.union ISLGb XSLGb) E1 SLGb E2 SLGb XSLGb.
 Proof. 
  intros; eqobs_in. 
 Qed.

 Lemma IXSLGb_global : forall x : VarP.Edec.t, 
  Vset.mem x (Vset.union ISLGb XSLGb) -> Var.is_global x.
 Proof.
  apply Vset.forallb_correct.
  intros x y Heq; rewrite Heq; trivial.
  vm_compute; trivial.
 Qed.

 Hint Resolve Modify_SLGb IXSLGb_global EqObs_SLGb.

 Lemma SLGb_dom : forall E (b : bool),
  equiv (Meq /-\ EP1 (!(R in_dom LGb) =?= b)) 
  E SLGb
  E SLGb 
  (Meq /-\ EP1 (!(R in_dom LGb) =?= b)).
 Proof.
  unfold SLGb; intros.
  apply equiv_app with (Meq /-\ EP1 (!(R in_dom LGb_hd) =?= b)).
  unfold sample_true.
  match goal with |- equiv ?P _ [?i1; ?i2; ?i3] _ _ _ =>
   change [i1; i2; i3] with ([i1; i2]++[i3]); apply equiv_app with 
    (Meq /-\ (EP1 (!(R in_dom LGb) =?= b) /-\ EP1 ((R in_dom LGb) =?= ((R in_dom LGb_hd) || (R in_dom LGb_tl))))) end.
  union_mod; [ rewrite proj1_MR; auto | ].
  eqobsrel_tail; intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
  split; [exact H2 | apply Ti_eqb_refl].
  eapply equiv_weaken; [ | apply equiv_while].
  intros k m1 m2 ((H1, (H2, H3)), (H4, _)); split; trivial.
  unfold notR, EP1, EP2 in *.
  change (~ negb (E.eval_expr (LGb_tl =?= Nil _) m1)) in H4.
  rewrite <- is_true_negb, negb_involutive in H4.
  rewrite <- (expr_eval_eq m1 (!(R in_dom LGb))) in H2.
  rewrite <- (expr_eval_eq m1 (R in_dom LGb)) in H3.
  rewrite <- (expr_eval_eq m1 LGb_tl) in H4.
  rewrite <- (expr_eval_eq m1 (!(R in_dom LGb_hd))).
  rewrite <- H2.
  change (negb (E.eval_expr (R in_dom LGb_hd) m1) = negb (E.eval_expr (R in_dom LGb) m1)).
  rewrite H3; generalize H4; simpl; unfold O.eval_op; simpl; intros H5; rewrite H5; simpl;
  rewrite orb_false_r; trivial.
  intros k m1 m2 (H1, _); rewrite H1; trivial.
  union_mod; [ rewrite proj1_MR, proj1_MR; auto | ].
  eqobsrel_tail; unfold implMR, EP1, EP2,Meq, andR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H.
  rewrite H1; rewrite is_true_Ti_eqb in H4; rewrite H4; subst; clear H1 H4.
  destruct (m2 LGb_tl); [discriminate | simpl].
  split; intros; (split; [trivial | ]);
  rewrite existsb_app, orb_assoc; simpl; rewrite orb_false_r; apply Ti_eqb_refl.
  union_mod; [ rewrite proj1_MR; auto | ].
  eqobsrel_tail; intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
  intros; exact H2.
 Qed.

 Definition split_sample := 
  (sample_true LGb_hd_hd LGb_hd_tl (Efst (R Esplit LGb)) ++
   [ If Efst (Efst (Esnd (R Esplit LGb))) then 
    [rGn_aux1 <$- {0,1}^n; rGk1_aux1 <$- {0,1}^k1; LGbR2 <- (true | (rGn_aux1 | rGk1_aux1)) ]
    else [ LGbR2 <- Efst (Esnd (R Esplit LGb)) ] ] ++
   sample_true LGb_tl_hd LGb_tl_tl (Esnd (Esnd (R Esplit LGb))) ++
   [ LGb_hd <- LGb_hd_hd |++| (R | LGbR2) |::| LGb_tl_hd; LGb_tl <- Nil _]).

 Lemma sample_split : forall E ,
  equiv (req_mem_rel {{R, LGb}} (EP1 (R in_dom LGb)))
  E (sample_true LGb_hd LGb_tl LGb)
  E split_sample
  (kreq_mem {{LGb_tl, LGb_hd}}).
 Proof.
  unfold sample_true; intros.
  set (QQ:=kreq_mem {{LGb_tl, LGb_hd}}).
  apply equiv_trans_r with Meq QQ QQ E
    ([ LGb_hd_hd <- Nil _;
       LGb_hd_tl <- Efst (R Esplit LGb) ] ++
     [ sample_while LGb_hd_hd LGb_hd_tl;
       If Efst (Efst (Esnd (R Esplit LGb))) then [
         rGn_aux1 <$- {0,1}^n;
         rGk1_aux1 <$- {0,1}^k1;
         LGbR2 <- (true | (rGn_aux1 | rGk1_aux1))
       ] else [LGbR2 <- Efst (Esnd (R Esplit LGb))];
      LGb_tl_hd <- Nil _;
      LGb_tl_tl <- Esnd (Esnd (R Esplit LGb));
      sample_while LGb_tl_hd LGb_tl_tl;
      LGb_hd <- LGb_hd_hd |++| (R | LGbR2) |::| LGb_tl_hd;
      LGb_tl <- Nil _ 
    ]); unfold QQ.
  auto. red; red; trivial. apply req_mem_trans.
  2: swap; eqobs_in.
  change [LGb_hd <- Nil _; LGb_tl <- LGb; sample_while LGb_hd LGb_tl] with
   ([LGb_hd <- Nil _; LGb_tl <- LGb] ++ [sample_while LGb_hd LGb_tl]).
  apply equiv_app with
    (req_mem_rel {{R, LGb}} 
       (fun k m1 m2 => E.eval_expr LGb_hd m1 = E.eval_expr LGb_hd_hd m2 /\
          E.eval_expr LGb_tl m1 = 
            E.eval_expr (LGb_hd_tl |++| (R | Efst (Esnd (R Esplit LGb))) |::| Esnd (Esnd (R Esplit LGb))) m2)).
  ep_eq_l LGb (Efst (R Esplit LGb) |++| (R | Efst (Esnd (R Esplit LGb))) |::| Esnd (Esnd (R Esplit LGb))).
    intros k m1 m2 (Heq, H1).
    simpl; unfold O.eval_op; simpl.
    rewrite <- (split_append_mem k (T.User Bitstring_k0) 
     (T.Pair T.Bool (T.Pair BS_n BS_k1)) (m1 R) 
     (false, (Ut.default k Bitstring_n, Ut.default k Bitstring_k1))
     (m1 LGb)) at 1.
  unfold EP1 in H1; simpl in H1; unfold O.eval_op in H1; simpl in H1; simpl.
  rewrite H1; trivial.
  eqobsrel_tail; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 (H1, _);
   mem_upd_simpl.
  rewrite (H1 _ R), (H1 _ LGb); auto.
  match goal with 
  |- equiv (req_mem_rel ?I ?P) E ?c1 E ?c2 ?Q => 
   assert (forall n:nat, 
    equiv (req_mem_rel I (P /-\ EP2 (Elen LGb_hd_tl =?= n))) E c1 E c2 Q) 
  end.
  
  induction n0.
  (**** Case n0 = 0 *****)
  ep_eq_r LGb_hd_tl (Nil Tk0bnk1).
  unfold EP2; intros k m1 m2 (H1, (H2, H3)); generalize H3; clear H3.
  simpl; unfold O.eval_op; simpl; destruct (m2 LGb_hd_tl); 
   [trivial | intro; discriminate].
  apply equiv_trans_eq_mem_l with (EP1 (! (LGb_tl =?= Nil _))) E
   (sample_body LGb_hd LGb_tl ++ [sample_while LGb_hd LGb_tl]).
 
  apply equiv_eq_sem_pre; unfold sample_while, EP1; intros k m H.
  rewrite deno_while, deno_cond, H; trivial.
  unfold sample_body at 1.
  match goal with 
   |- equiv _ _ _ _ (?i1::?i2::?i3::?c) ?Q => 
    change (i1::i2::i3::c) with ([i1; i2; i3]++c);
    apply equiv_trans with (Meq /-\ 
     (EP1 (LGb_tl =?= 
      ((R | Efst (Esnd (R Esplit LGb))) |::| Esnd (Esnd (R Esplit LGb))))))
     Q Q E
     ([ 
      i1; LGb_hd <- LGb_hd |++| (R | LGbR2) |::| Nil _; 
       LGb_tl <- Esnd (Esnd (R Esplit LGb)) 
     ] ++ 
     [sample_while LGb_hd LGb_tl]) 
  end.
  unfold req_mem_rel; repeat apply decMR_and; auto.
  intros k m1 m2.
  match goal with 
   |- sumbool (?x1 = ?x2) _  => 
    assert (W:=T.i_eqb_spec k (Var.btype LGb_hd) x1 x2);
     destruct (T.i_eqb k (Var.btype LGb_hd) x1 x2); auto
  end.
  intros k m1 m2.
  match goal with 
   |- sumbool (?x1 = ?x2) _  => 
    assert (W:= T.i_eqb_spec k (Var.btype LGb_tl) x1 x2); 
     destruct (T.i_eqb k (Var.btype LGb_tl) x1 x2); auto 
  end.
  unfold req_mem_rel, andR, EP1, EP2.
  intros k m1 m2 H; decompose [and] H; clear H; split; [trivial | ].
  rewrite <- (expr_eval_eq m1 LGb_tl), H4.
  generalize H3; simpl; unfold O.eval_op; simpl.
  rewrite (H0 _ LGb), (H0 _ R); trivial.
  destruct (m2 LGb_hd_tl); [trivial | intro; discriminate].
  apply req_mem_trans.
  eqobs_tl. 
  ep_eq_l LGb_tl ((R | Efst (Esnd (R Esplit LGb))) |::| Esnd (Esnd (R Esplit LGb))).
  intros k m1 m2 (H1, H2); rewrite expr_eval_eq; trivial.
  rewrite proj1_MR; cp_test (Efst (Efst (Esnd (R Esplit LGb)))); deadcode.
  alloc_l rGn_aux rGn_aux1; alloc_l rGk1_aux rGk1_aux1.
  ep; deadcode; swap; eqobs_in.
  swap; eqobs_in.
  apply equiv_app with
   (req_mem_rel {{LGbR2, R, LGb}}
    ((fun k (m1 m2 : Mem.t k) =>
     E.eval_expr LGb_hd m1 = 
     E.eval_expr (LGb_hd_hd |++| (R | LGbR2) |::| LGb_tl_hd) m2 /\
     E.eval_expr LGb_tl m1 = E.eval_expr LGb_tl_tl m2))).
  eqobsrel_tail; unfold implMR, req_mem_rel, EP2, andR; 
   simpl; unfold O.eval_op; simpl; intros k m1 m2 H; decompose [and] H; clear H.
  rewrite (H0 _ LGb), (H0 _ R), H1; trivial.
  split; intros; mem_upd_simpl; auto.
  eapply equiv_cons; [apply equiv_while | ].
  unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H.
  generalize H3; simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq; trivial.
  eqobsrel_tail.
  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold req_mem_rel, EP1, EP2, andR, notR, upd_para.
  simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H; split.
  mem_upd_simpl.
  rewrite H4. 
  refine (req_mem_update aux _ H2).
  split; intros; mem_upd_simpl.
  rewrite H0, H4; repeat rewrite app_ass; simpl; auto.
  rewrite H0, H4; repeat rewrite app_ass; simpl; auto.
  apply equiv_trans_eq_mem_l with 
   (EP2 (LGb_tl =?= Nil _)) E (nil ++ [LGb_tl <- Nil _]).
  ep_eq_r LGb_tl (Nil Tk0bnk1).
  intros k m1 m2 (H1, H2); rewrite expr_eval_eq; trivial.
  rewrite proj1_MR; apply equiv_nil.
  eqobs_tl.
  eapply equiv_strengthen; [ | apply equiv_assign_r].
  unfold req_mem_rel, notR, EP1, EP2, upd2, andR; simpl; unfold O.eval_op; simpl;
   intros k m1 m2 H; decompose [and] H; clear H.
  intros ty y; simpl.
  generalize (VarP.Edec.eqb_spec y LGb_hd); destruct (VarP.Edec.eqb y LGb_hd);
   intros; [ | discriminate].
  inversion H; subst. 
  rewrite (T.inj_pair2 H8), Mem.get_upd_same; trivial.
  unfold req_mem_rel, andR, notR, EP1, EP2.
  intros k m1 m2 H; decompose [and] H; clear H.
  rewrite <- negb_involutive, is_true_negb; trivial.
 
  unfold req_mem_rel, EP1, EP2, andR; intros k m1 m2 H; decompose [and] H; clear H.
  change (is_true (negb (E.eval_expr (LGb_tl =?= Nil _) m1))).
  rewrite is_true_negb, <- expr_eval_eq, H4.
  simpl; unfold O.eval_op; simpl; destruct (m2 LGb_hd_tl); discriminate.


  (**** Case n0 = S _ *****)
  apply equiv_trans_eq_mem_l with (EP1 (! (LGb_tl =?= Nil _))) E
   (sample_body LGb_hd LGb_tl ++ [sample_while LGb_hd LGb_tl]).

  apply equiv_eq_sem_pre; unfold sample_while, EP1; intros k m H.
  rewrite deno_while, deno_cond, H; trivial.
  match goal with 
   |- equiv ?P _ _ _ ?c _ =>
   apply equiv_trans_eq_mem_r with (EP1 (! (LGb_hd_tl =?= Nil _))) E
    (sample_body LGb_hd_hd LGb_hd_tl ++ c) 
  end.
  apply equiv_eq_sem_pre; unfold sample_while, EP1; intros k m H.
  rewrite deno_cons, deno_while, deno_cond, H, <- deno_app; trivial.
  apply equiv_app with (2:=IHn0).
  eqobsrel_tail.
  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold req_mem_rel, EP1, EP2, andR, notR, upd_para.
  simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H; split.
  mem_upd_simpl.
  rewrite H4. 
  destruct (m2 LGb_hd_tl); [discriminate H3 | simpl].
  refine (req_mem_update aux _ H0).
  split; intros; mem_upd_simpl;
  (destruct (m2 LGb_hd_tl); 
  [discriminate H3 | rewrite is_true_Ti_eqb in H3; inversion H3; clear H3; subst]).
  rewrite H1, H4; simpl; repeat split; trivial. 
  apply Ti_eqb_refl.
  rewrite H1, H4; simpl; repeat split; trivial. 
  apply Ti_eqb_refl.

  unfold req_mem_rel, EP1, EP2, andR, transpR.
  intros k m1 m2 H; decompose [and] H; clear H.
  generalize H3; simpl; unfold O.eval_op; simpl.
  destruct (m1 LGb_hd_tl); [ | trivial].
  intros W; discriminate W.

  unfold req_mem_rel, EP1, EP2, andR; intros k m1 m2 H; decompose [and] H; clear H.
  change (is_true (negb (E.eval_expr (LGb_tl =?= Nil _) m1))).
  rewrite is_true_negb, <- expr_eval_eq, H4.
  simpl; unfold O.eval_op; simpl; destruct (m2 LGb_hd_tl); discriminate.

  intros k; assert (W1:=fun n => H n k); clear H.
  apply choice in W1; destruct W1 as (f1, H).
  exists (fun m1 m2 => f1 (E.eval_expr (Elen LGb_hd_tl) m2) m1 m2).
  intros m1 m2 (H1, H2); apply (H (E.eval_expr (Elen LGb_hd_tl) m2) m1 m2).
  split; [trivial | split; [trivial | ] ].
  unfold EP2; simpl; unfold O.eval_op; simpl; apply Ti_eqb_refl.
 Qed.

 Lemma swap_equiv_SLGb_G :
  equiv Meq 
  E7r (G_body2r_bad2 ++ SLGb) 
  E7 (SLGb ++ G_body2b_bad2) 
  Meq.
 Proof.
  unfold G_body2r_bad2, G_body2b_bad2, G_body2b_gen.
  apply swap_sample_if2.
  apply SLGb_dom.
  (** Not in dom *)
  rewrite proj1_MR.
  apply swap_sample_app with XSLGb ISLGb.
  apply Modify_SLGb. apply Modify_SLGb. apply EqObs_SLGb.
  swap; union_mod; [trivial | eqobs_in].
  union_mod; [trivial | swap; eqobs_tl].
  apply equiv_strengthen with (kreq_mem {{R, R', LGb}}).
  intros k m1 m2 H; rewrite H; trivial.
  match goal with
  |- equiv _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8] _ _ _ => 
    change [i1; i2; i3; i4; i5; i6; i7; i8] with 
          ([i1; i2; i3] ++ ([i4; i5; i6; i7; i8]));
    apply EqObs_trans with E7r ([i1; i2; i3] ++ (split_sample ++ [i7; i8])) 
  end.
  apply equiv_app with 
   (req_mem_rel {{rGn, rGk1, R, R', LGb}} (EP1 (R in_dom LGb))).
  eqobsrel_tail; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; rewrite Ti_eqb_refl; trivial.
  eqobs_tl_n 2.
  match goal with
  |- equiv _ _ _ _ _ (kreq_mem ?O) => 
   apply equiv_weaken with (req_mem_rel O trueR) 
  end.
  intros k m1 m2 (H1, H2); trivial.
  union_mod.
  eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply sample_split] ].
  intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  intros k m1 m2 (H1, H2); split; [apply req_mem_weaken with (2:= H1); 
   vm_compute | ]; trivial.
  alloc LGb LGb1; ep; deadcode; ep; deadcode.
  match goal with 
   |- EqObs _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8] _ _ _ =>
    change [i1; i2; i3; i4; i5; i6; i7; i8] with 
          ([i1; i2; i3; i4] ++ ([i5; i6; i7; i8]));
    apply EqObs_trans with E7r
     ([i1; i2; LGb_hd <- Nil _; LGb_tl <- LGb ] ++
      [ 
       sample_while LGb_hd LGb_tl;
       LGb <- (R | (false | (rGn | rGk1))) |::| LGb_hd;
       LGb_hd <- Nil _ 
      ]) 
  end.
  apply equiv_app with
   (req_mem_rel {{rGn, rGk1, R, R', LGb}}
    (fun k m1 m2 => m1 LGb_tl_tl = m2 LGb_tl /\ m1 LGb_tl_hd = m2 LGb_hd)).
  eqobsrel_tail; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; intros;
  mem_upd_simpl.
  split; [apply (H _ LGb) | ]; trivial.
  eapply equiv_cons; [apply equiv_while | ].
  intros k m1 m2 (H1, (H2, H3)).
  simpl; unfold O.eval_op; simpl; rewrite H2; trivial.
  eqobsrel_tail; eapply equiv_strengthen; [ | apply equiv_assign].
  unfold EP1, EP2, upd_para; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 ((H1, (H2, H3)), (H4, H5)).
  red; split.
  rewrite H2; apply req_mem_update with (d:=aux) (1:= H1).
  split; intros; mem_upd_simpl;
    rewrite H2, H3; auto.
  eqobs_tl_n 1.
  match goal with 
   |- equiv ((req_mem_rel ?I _) /-\ _)  _ [?i1; ?i2] _ ?c _ => 
   change c with (nil ++ c); change [i1; i2] with ([i1]++[i2]);
   apply equiv_app with (req_mem_rel (Vset.add LGb_tl I) 
    (fun k m1 m2 => m1 LGb_tl_hd = m2 LGb_hd))
  end.
  eapply equiv_strengthen; [ | apply equiv_assign_l].
  intros k m1 m2 ((H1, (H2, H3)), (H4, H5)); split.
  replace m2 with (m2 {! LGb_tl <-- E.eval_expr (Nil _) m1!}).
  apply req_mem_update; trivial.
  apply Mem.eq_leibniz; intros (ty,y); destruct (Var.eq_dec LGb_tl y).
  inversion e; simpl; rewrite Mem.get_upd_same; symmetry.
  unfold notR, EP2 in H5; simpl in H5; unfold O.eval_op in H5; simpl in H5.
  rewrite <- is_true_negb, negb_involutive, is_true_Ti_eqb in H5; trivial.
  rewrite Mem.get_upd_diff; trivial; discriminate.
  rewrite Mem.get_upd_diff; trivial; discriminate.
  eapply equiv_strengthen; [ | apply equiv_assign ].
  intros k m1 m2 (H1, H2); red.
  match goal with
   |- kreq_mem _ (_{! _ <-- ?x!}) (_{! _ <-- ?y!}) => replace x with y 
  end.
  eapply req_mem_weaken; [ | apply req_mem_update with (1:= H1) ].
  vm_compute; trivial.
  simpl; unfold O.eval_op; simpl. rewrite (H1 _ R), (H1 _ rGn), (H1 _ rGk1), H2; trivial.
  match goal with 
  |- EqObs _ _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8] _ =>
   apply EqObs_trans with E7 [i1; i2; i3; i4; i6; i7; i8; i5] 
  end.
  eqobs_tl; ep; deadcode; swap; eqobs_in.
  eqobs_hd; swap; eqobs_in.
 
  (* R in Dom *)
  union_mod; [rewrite proj1_MR; trivial | ].
  ep; swap; eqobs_tl.
  apply equiv_strengthen with (Meq /-\ EP1 (R in_dom LGb)).
  unfold notR, EP1; intros k m1 m2 (H1, H2); split; trivial.
  rewrite <- is_true_negb in H2; rewrite <- negb_involutive; trivial.
  match goal with 
   |- equiv ?P _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6] _ _ ?Q =>
    apply equiv_trans with P Q Q E7r ([i1] ++ split_sample ++ [i5; i6]) 
  end.
  auto. 
  intros k m1 m2 (H1, H2); split; trivial. 
  apply req_mem_trans. 
  apply equiv_cons with
   (req_mem_rel {{bad2, rGn, rGk1, R, R', LGb}} (EP1 (R in_dom LGb))).
  eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl; 
   intros k m1 m2 (H1, H2); split; intros; trivial.
  generalize H2; clear. 
  induction (m1 LGb); simpl; [intro; discriminate | ].
  destruct a; simpl.
  case_eq (T.i_eqb k BS_k0 (m1 R) i0); simpl; intros H2 H4; rewrite H2; auto.
  eqobs_tl_n 2.
  match goal with
  |- equiv _ _ _ _ _ (kreq_mem ?O) => 
   apply equiv_weaken with (req_mem_rel O trueR) 
  end.
  intros k m1 m2 (H1, H2); trivial.
  union_mod.
  eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply sample_split] ].
  intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  intros k m1 m2 (H1, H2); split; 
   [apply req_mem_weaken with (2:= H1); vm_compute | ]; trivial.
  match goal with 
   |- equiv ?P _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6] ?Q =>
    apply equiv_trans_r with P Q Q E7 (split_sample ++ [i4; i5; i6]) 
  end.
  auto. 
  intros k m1 m2 (H1, H2); split; trivial. rewrite <- H1; trivial. 
  apply req_mem_trans.
 
 Focus 2.
 eqobs_tl.
 match goal with 
  |- equiv _ _ _ _ _ (kreq_mem ?O) => 
   apply equiv_weaken with (req_mem_rel O trueR) 
 end.
 intros k m1 m2 (H1, H2); trivial.
 apply equiv_strengthen with 
  (req_mem_rel {{LD,LH,bad2,R,R',LGb}} (EP1 (R in_dom LGb))).
 intros k m1 m2 (H1, H2); rewrite <- H1; split; auto.
 union_mod.
 apply equiv_sym; auto.
 unfold EP1; split; intros k m1 m2 (H1, H2); 
  (split; [apply req_mem_sym; trivial | ]);
  unfold is_true; rewrite <- H2; simpl; unfold O.eval_op; simpl; rewrite (H1 _ R), (H1 _ LGb); trivial.
 eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply sample_split] ].
 intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
 intros k m1 m2 (H1, H2); split; [apply req_mem_weaken with (2:= H1); vm_compute | ]; trivial.
 ep_eq LGb (Efst (R Esplit LGb) |++| (R | Efst (Esnd (R Esplit LGb))) |::| Esnd (Esnd (R Esplit LGb))).
 intros k m1 m2 (Heq, H1); rewrite <- Heq.
 simpl; unfold O.eval_op; simpl.
 rewrite <- (split_append_mem k (Var.btype R) Tbnk1 (m1 R) 
  (false, (Ut.default k Bitstring_n, Ut.default k Bitstring_k1)) (m1 LGb)) at 1 5.
 unfold EP1 in H1; simpl in H1; unfold O.eval_op in H1; simpl in H1; simpl; rewrite H1; auto.
 match goal with |- equiv _ _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8; ?i9; ?i10; ?i11; ?i12] _ =>
  change [i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12] with (([i1; i2] ++ [i3]) ++[i4; i5; i6; i7; i8; i9; i10; i11; i12]);
   apply equiv_trans_eq_mem_r with trueR E7 
    ( ([ LGb_hd_hd <- Nil _; LGb_hd_tl <- Efst (R Esplit LGb)] ++
     [sample_while LGb_hd_hd LGb_hd_tl])  ++
    [i4] ++ 
     sample_true LGb_tl_hd LGb_tl_tl (Esnd (Esnd (R Esplit LGb))) ++
     [i8; i9; i11;
      If Efst (LGbR2) then [
       rGn <- Efst (Esnd LGbR2);
       rGk1 <- Esnd (Esnd LGbR2);
       If E.Eexists tc
       (E.Eop O.Oand
        {E.Eop O.Oand
         {Esnd (ap_finv Esnd (tc))
          |x| (LH [{Efst (ap_finv Esnd (tc))}]) =?= R,
           Efst (ap_finv Esnd (tc)) in_dom LH},
                Esnd (Efst (ap_finv Esnd (tc)))
         |x| Esnd (Esnd LGbR2) =?= zero_k1}) LD
       _then [bad2 <- true];
        LGb <- LGb_hd_hd |++| (R | (false | (Efst (Esnd LGbR2) | Esnd (Esnd LGbR2)))) |::| LGb_tl_hd
       ] else [
        rGn <- Efst (Esnd LGbR2);
        rGk1 <- Esnd (Esnd LGbR2);
        i10
       ]
     ]) 
  end.
   3:red; red; trivial.
   apply equiv_app with (Meq /-\ ~-EP1 (R in_dom LGb_hd_hd)).
   apply equiv_app with (Meq /-\ ~-EP1 (R in_dom LGb_hd_hd) /-\ ~-EP1 (R in_dom LGb_hd_tl)).
   rewrite proj1_MR; union_mod; trivial.
   eqobsrel_tail; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; split.
   rewrite <- is_true_negb; trivial.
   rewrite not_is_true_false; refine (@existsb_fst_split k BS_k0 Tbnk1 _ _).
   eapply equiv_weaken; [ | apply equiv_while].
   unfold andR; intuition.  intros k m1 m2 (Heq, _); rewrite Heq; trivial.
   union_mod. rewrite proj1_MR, proj1_MR; trivial.
   eqobsrel_tail; unfold EP1, EP2, andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
    decompose [and] H; clear H.
   red in H0; subst. destruct (m2 LGb_hd_tl); [discriminate | simpl in *].
   apply not_is_true_false in H1.
   destruct i; split; intros; rewrite existsb_app, H1; simpl in *;
    destruct (T.i_eqb k BS_k0 (m2 R) i); simpl in *; split; trivial.
   elim H4; trivial. discriminate. elim H4; trivial. discriminate.
   ep_eq_l (R in_dom LGb_hd_hd) false.
   unfold notR, EP1; intros k m1 m2 (H1, H2).
   rewrite not_is_true_false in H2; trivial.
   rewrite proj1_MR; union_mod; trivial.
   apply equiv_strengthen with  
    (kreq_mem {{bad2,LD,LH,LGb,R,rGn_aux1,rGk1_aux1,LGb_tl_hd, 
     LGb_tl_tl,aux,rGn_aux,rGk1_aux,LGb_tl,LGb_hd_hd}}). 
   intros k m1 m2 H; rewrite H; trivial.
   eqobs_hd.
   cp_test (Efst LGbR2); ep; deadcode; swap; eqobs_in.
   alloc LGb LGb1.
   swap; eqobs_tl.
   cp_test Efst (Efst (Esnd (R Esplit LGb))); ep; deadcode; ep; deadcode.
   alloc_r rGn_aux1 rGn; alloc_r rGk1_aux1 rGk1; ep; deadcode.
   swap; eqobs_in.
   ep_eq_r (Efst (Efst (Esnd (R Esplit LGb)))) false.
   unfold notR, EP2; intros k m1 m2 (H1, (H2, H3)).
   rewrite not_is_true_false in H3; trivial.
   swap; eqobs_in.
   
   intros k m1 m2 H; rewrite H; trivial.
 Qed.

 Definition swi7_G : forall tg g, option (sw_info SLGb XSLGb ISLGb E7r E7 tg g) :=
  let i := 
   add_sw_info_refl SLGb XSLGb ISLGb E7r E7 (Modify_SLGb E7r) (Modify_SLGb E7) 
   (EqObs_SLGb E7r E7) IXSLGb_global (fun t f => None) _ H in
   add_sw_info SLGb XSLGb ISLGb E7r E7 (Modify_SLGb E7r) (Modify_SLGb E7) 
   (EqObs_SLGb E7r E7) IXSLGb_global i _ G swap_equiv_SLGb_G.

 Definition iE7r := iEiEi H_body0 G_body2r_bad2 Dec_body7r.

 Definition iE7 := iEiEi H_body0 G_body2b_bad2 Dec_body7.

 Definition get_option o := match o with Some X => X | _ => Vset.empty end.

 Definition M7 := Eval vm_compute in 
  get_option (modify (refl1_info iE7r) Vset.empty Dec_body7r).

 Lemma M7_E7 : Modify E7 M7 Dec_body7.
 Proof. 
  apply modify_correct with (refl1_info iE7) Vset.empty.
  vm_compute; trivial. 
 Qed.

 Lemma M7_E7r : Modify E7r M7 Dec_body7r.
 Proof. 
  apply modify_correct with (refl1_info iE7r) Vset.empty.
  vm_compute; trivial. 
 Qed.

 Lemma swap_equiv_Gbaddr : forall E1 E2, equiv Meq E1
  ((Gbaddr true r ++ [mn <- (false | one_n)]) ++ SLGb) E2
  (SLGb ++ (Gbaddr true r ++ [mn <- (false | one_n)]))
  (kreq_mem
   (Vset.union (Vset.union (get_globals (Vset.union M7 M7)) XSLGb)
    (fv_expr (proc_res E7r Dec)))).
 Proof.
  intros EE1 EE2; ep; swap; eqobs_tl.
  apply equiv_strengthen with (kreq_mem {{LD,LH,Dc,bad,r,R',LGb}}).
  intros k m1 m2 H; rewrite H; trivial.
  match goal with
  |- equiv _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8] _ _ _ =>
    apply EqObs_trans with EE1 
      [R <- r; i1; i2; LGb <- (R | (true | (rGn | rGk1))) |::| LGb; i4; i5; i6; i7; i8] end.
  ep; deadcode; eqobs_in.
  match goal with
  |- EqObs _ _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8] _ =>
    apply EqObs_trans with EE2 
      [R <- r; i1; i2; i3; i4; i5; i6; i7; LGb <- (R | (true | (rGn | rGk1))) |::| LGb] end.
  2: ep; deadcode; eqobs_in.
  eqobs_hd_n 1.
  match goal with
  |- EqObs ?I _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8] _ _ _ =>
    change [i1; i2; i3; i4; i5; i6; i7; i8] with ([i1; i2; i3] ++ ([i4; i5; i6; i7; i8]));
    apply EqObs_trans with EE1 ([i1; i2; i3] ++ (split_sample ++ [i7; i8]));
    [ apply equiv_app with (req_mem_rel (Vset.add rGn (Vset.add rGk1 I)) (EP1 (R in_dom LGb)))
    | ]
  end.
  eqobsrel_tail; simpl; unfold O.eval_op; simpl.
   intros k m1 m2 H; rewrite Ti_eqb_refl; trivial.
  eqobs_tl_n 2.
  match goal with
  |- equiv _ _ _ _ _ (kreq_mem ?O) => apply equiv_weaken with (req_mem_rel O trueR) end.
  intros k m1 m2 (H1, H2); trivial.
  union_mod.
  eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply sample_split] ].
  intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  intros k m1 m2 (H1, H2); split; [apply req_mem_weaken with (2:= H1); vm_compute | ]; trivial.
  alloc LGb LGb1; ep; deadcode; ep; deadcode.
  alloc_l rGn_aux1 rGn; alloc_l rGk1_aux1 rGk1; ep; deadcode. 
  match goal with |- EqObs ?I _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8] _ _ _ =>
    change [i1; i2; i3; i4; i5; i6; i7; i8] with ([i1; i2; i3; i4] ++ ([i5; i6; i7; i8]));
    apply EqObs_trans with EE1 
       ([ i1; i2; LGb_hd <- Nil _; LGb_tl <- LGb ] ++
        [ sample_while LGb_hd LGb_tl;
          LGb <- (R | (true | (rGn | rGk1))) |::| LGb_hd;
          LGb_hd <- Nil _ ]);
    [ apply equiv_app with
     (req_mem_rel (Vset.add rGn (Vset.add rGk1 I))
       (fun k m1 m2 => m1 LGb_tl_tl = m2 LGb_tl /\ m1 LGb_tl_hd = m2 LGb_hd))
    | ]
  end.
  eqobsrel_tail; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; intros;
  mem_upd_simpl.
  split; [apply (H _ LGb) | ]; trivial.
  eapply equiv_cons; [apply equiv_while | ].
  intros k m1 m2 (H1, (H2, H3)); simpl; unfold O.eval_op; simpl; rewrite H2; trivial.
  eqobsrel_tail; eapply equiv_strengthen; [ | apply equiv_assign].
  unfold EP1, EP2, upd_para; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 ((H1, (H2, H3)), (H4, H5)).
  red; split.
  rewrite H2; apply req_mem_update with (d:=aux) (1:= H1).
  split; intros; mem_upd_simpl;
    rewrite H2, H3; auto.
  eqobs_tl_n 1.
  match goal with |- equiv ((req_mem_rel ?I _) /-\ _)  _ [?i1; ?i2] _ ?c _ => 
   change c with (nil ++ c); change [i1; i2] with ([i1]++[i2]);
   apply equiv_app with (req_mem_rel (Vset.add LGb_tl I) 
        (fun k m1 m2 => m1 LGb_tl_hd = m2 LGb_hd))
  end.
  eapply equiv_strengthen; [ | apply equiv_assign_l].
    intros k m1 m2 ((H1, (H2, H3)), (H4, H5)); split.
    replace m2 with (m2 {! LGb_tl <-- E.eval_expr (Nil _) m1!}).
    apply req_mem_update; trivial.
    apply Mem.eq_leibniz; intros (ty,y); destruct (Var.eq_dec LGb_tl y).
    inversion e; simpl; rewrite Mem.get_upd_same; symmetry.
    unfold notR, EP2 in H5; simpl in H5; unfold O.eval_op in H5; simpl in H5.
    rewrite <- is_true_negb, negb_involutive, is_true_Ti_eqb in H5; trivial.
    rewrite Mem.get_upd_diff; trivial.
    rewrite Mem.get_upd_diff; trivial; discriminate.
  eapply equiv_strengthen; [ | apply equiv_assign ].
    intros k m1 m2 (H1, H2); red.
    match goal with |- kreq_mem _ (_{! _ <-- ?x!})(_{! _ <-- ?y!}) => replace x with y end.
    eapply req_mem_weaken; [ | apply req_mem_update with (1:= H1) ].
    vm_compute; trivial.
  simpl; unfold O.eval_op; simpl. rewrite (H1 _ R), (H1 _ rGn), (H1 _ rGk1), H2; trivial.
  match goal with |- EqObs _ _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8] _ =>
   apply EqObs_trans with EE2 [i1; i2; i3; i4; i6; i7; i8; i5] end.
  eqobs_tl; ep; deadcode; swap; eqobs_in.
  eqobs_hd; swap; eqobs_in.
 Qed.

 Definition iE7rE7 := add_refl_info H (empty_info E7r E7).

 Lemma SLGb_length : forall E (b : bool), equiv
   (Meq /-\ EP1 (E.Eop O.Oor {testD, (qD +! qG) <! (Elen LGb)} =?= b))
   E SLGb E SLGb
   (Meq /-\ EP1 (E.Eop O.Oor {testD, (qD +! qG) <! (Elen LGb)} =?= b)).
 Proof.
  unfold SLGb; intros.
  apply equiv_app with (Meq /-\ EP1 (E.Eop O.Oor {testD, (qD +! qG) <! (Elen LGb_hd)} =?= b)).
  unfold sample_true.
  match goal with |- equiv ?P _ [?i1; ?i2; ?i3] _ _ _ =>
   change [i1; i2; i3] with ([i1; i2]++[i3]); apply equiv_app with 
    (Meq /-\   EP1 (E.Eop O.Oor {testD, (qD +! qG) <! ((Elen LGb_hd) +! Elen LGb_tl)} =?= b)) end.
  union_mod; [ rewrite proj1_MR; auto | ].
  eqobsrel_tail; intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl; trivial.
  eapply equiv_weaken; [ | apply equiv_while].
  intros k m1 m2 ((H1, H2), (H4, _)); split; trivial.
  unfold notR, EP1, EP2 in *.
  change (~ negb (E.eval_expr (LGb_tl =?= Nil _) m1)) in H4.
  rewrite <- is_true_negb, negb_involutive in H4.
  rewrite <- (expr_eval_eq m1 LGb_tl) in H4.
  generalize H2 H4; clear H2 H4; simpl; unfold O.eval_op; simpl; intros.
  rewrite H4 in H2; simpl in H2; rewrite plus_0_r in H2; trivial.
  intros k m1 m2 (H1, _); rewrite H1; trivial.
  union_mod; [ rewrite proj1_MR, proj1_MR; auto | ].
  eqobsrel_tail; unfold implMR, EP1, EP2,Meq, andR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H.
  destruct (m1 LGb_tl); [discriminate | simpl].
  simpl in *; split; intros; rewrite app_length; simpl; rewrite <- (plus_assoc (length (m1 LGb_hd))); trivial.
  union_mod; [ rewrite proj1_MR; auto | ].
  eqobsrel_tail; intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
  intros; exact H2.
 Qed.

 Lemma SLGb_dom_r : forall E (b : bool),
  equiv (Meq /-\ EP1 ((r in_dom LGb) =?= b)) 
  E SLGb 
  E SLGb 
  (Meq /-\ EP1 ((r in_dom LGb) =?= b)).
 Proof.
  unfold SLGb; intros.
  apply equiv_app with (Meq /-\ EP1 ((r in_dom LGb_hd) =?= b)).
  unfold sample_true.
  match goal with |- equiv ?P _ [?i1; ?i2; ?i3] _ _ _ =>
   change [i1; i2; i3] with ([i1; i2]++[i3]); apply equiv_app with 
    (Meq /-\ (EP1 ((r in_dom LGb) =?= b) /-\ EP1 ((r in_dom LGb) =?= ((r in_dom LGb_hd) || (r in_dom LGb_tl))))) end.
  union_mod; [ rewrite proj1_MR; auto | ].
  eqobsrel_tail; intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
  split; [exact H2 | apply Ti_eqb_refl].
  eapply equiv_weaken; [ | apply equiv_while].
  intros k m1 m2 ((H1, (H2, H3)), (H4, _)); split; trivial.
  unfold notR, EP1, EP2 in *.
  change (~ negb (E.eval_expr (LGb_tl =?= Nil _) m1)) in H4.
  rewrite <- is_true_negb, negb_involutive in H4.
  rewrite <- (expr_eval_eq m1 ((r in_dom LGb))) in H2.
  rewrite <- (expr_eval_eq m1 (r in_dom LGb)) in H3.
  rewrite <- (expr_eval_eq m1 LGb_tl) in H4.
  rewrite <- (expr_eval_eq m1 ((r in_dom LGb_hd))).
  rewrite <- H2.
  rewrite H3; generalize H4; simpl; unfold O.eval_op; simpl; intros H5; rewrite H5; simpl;
  rewrite orb_false_r; trivial.
  intros k m1 m2 (H1, _); rewrite H1; trivial.
  union_mod; [ rewrite proj1_MR, proj1_MR; auto | ].
  eqobsrel_tail; unfold implMR, EP1, EP2,Meq, andR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H.
  rewrite H1; rewrite is_true_Ti_eqb in H4; rewrite H4; subst; clear H1 H4.
  destruct (m2 LGb_tl); [discriminate | simpl].
  split; intros; (split; [trivial | ]);
  rewrite existsb_app, orb_assoc; simpl; rewrite orb_false_r; apply Ti_eqb_refl.
  union_mod; [ rewrite proj1_MR; auto | ].
  eqobsrel_tail; intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
  intros; exact H2.
 Qed.

 Lemma SLGb_fst : forall E (b : bool),
  equiv (Meq /-\ EP1 (Efst (LGb [{r}]) =?= b)) 
  E SLGb 
  E SLGb
  (Meq /-\ EP1 (Efst (LGb [{r}]) =?= b)).
 Proof.
  unfold SLGb; intros.
  apply equiv_app with (Meq /-\ EP1 (Efst (LGb_hd[{r}]) =?= b)).
  unfold sample_true.
  match goal with |- equiv ?P _ [?i1; ?i2; ?i3] _ _ _ =>
   change [i1; i2; i3] with ([i1; i2]++[i3]); apply equiv_app with 
    (Meq /-\ (EP1 (Efst ((LGb_hd |++| LGb_tl)[{r}]) =?= b))) end.
  union_mod; [ rewrite proj1_MR; auto | ].
  eqobsrel_tail; intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
  exact H2.
  eapply equiv_weaken; [ | apply equiv_while].
  intros k m1 m2 ((H1, H2), (H4, _)); split; trivial.
  unfold notR, EP1, EP2 in *.
  change (~ negb (E.eval_expr (LGb_tl =?= Nil _) m1)) in H4.
  rewrite <- is_true_negb, negb_involutive in H4.
  rewrite <- (expr_eval_eq m1 (Efst ((LGb_hd |++| LGb_tl) [{r}]))) in H2.
  rewrite <- (expr_eval_eq m1 LGb_tl) in H4.
  rewrite <- (expr_eval_eq m1 (Efst (LGb_hd [{r}]))).
  rewrite <- H2.
  generalize H4; simpl; unfold O.eval_op; simpl; intros H5; rewrite H5; simpl;
  rewrite <- app_nil_end; trivial.
  intros k m1 m2 (H1, _); rewrite H1; trivial.
  union_mod; [ rewrite proj1_MR, proj1_MR; auto | ].
  eqobsrel_tail; unfold implMR, EP1, EP2,Meq, andR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H.
  rewrite is_true_Ti_eqb in H2; subst.
  destruct (m2 LGb_tl); [discriminate | simpl].
  split; intros.
  change (i::i0) with ((i::nil) ++ i0).
  rewrite is_true_Ti_eqb, app_ass; repeat rewrite (@assoc_app k BS_k0 Tbnk1).
  match goal with |- fst (if ?x then _ else _) = _ => destruct x; trivial end.
  unfold O.assoc at 1 3; simpl; destruct H.
  match goal with |- fst (if (orb ?x _) then _ else _) = _ => destruct x; simpl; auto end.
  rewrite app_ass; simpl; apply Ti_eqb_refl.
  union_mod; [ rewrite proj1_MR; auto | ].
  eqobsrel_tail; intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
  intros; exact H2.
 Qed.

 Lemma swap_equiv_SLGb_Dec :
  equiv Meq 
  E7r (Dec_body7r ++ SLGb) 
  E7 (SLGb ++ Dec_body7) 
  (kreq_mem (Vset.union (Vset.union (get_globals (Vset.union M7 M7)) XSLGb)
   (fv_expr (proc_res E7r Dec)))).
 Proof.
  unfold Dec_body7, Dec_body7r, Dec_body_gen_b.
  apply swap_sample_if2.
  apply SLGb_length. 3: unfold Meq; intros k m1 m2 Heq; subst; trivial.
  rewrite proj1_MR; apply equiv_weaken with Meq.
    intros k m1 m2 H; rewrite H; trivial.
  apply check_swap_c_correct with (I:= ISLGb) (pi:= swi7_G).
  apply Modify_SLGb. apply Modify_SLGb. apply EqObs_SLGb.
  vm_compute; trivial.
  rewrite proj1_MR; match goal with |- 
    equiv _ _ ((?i1::?i2::?i3::?i4::?i5::?c1) ++ _) _ (SLGb ++ (?i1::?i2::?i3::?i4::?i5::?c2)) _ =>
    change (i1::i2::i3::i4::i5::c1) with ([i1; i2; i3; i4; i5]++c1);
    change (i1::i2::i3::i4::i5::c2) with ([i1; i2; i3; i4; i5]++c2) end.
  apply swap_sample_app2.
  swap; union_mod. trivial. eqobs_in.
  union_mod. trivial. eqobs_in.
  apply swap_sample_if_Q with XSLGb. apply Modify_SLGb.
  vm_compute; trivial.
  match goal with |- equiv _ _ ([?i1; ?i2; ?i3] ++ _) _ (_ ++ [?i1; ?i2; ?i4]) _ => 
      change [i1; i2; i3] with ([i1; i2]++[i3]); change [i1; i2; i4] with ([i1; i2]++[i4]) end.
  apply swap_sample_app2.
  swap iE7. union_mod iE7. trivial. eqobs_in iE7.
  union_mod iE7rE7. trivial. eqobs_in iE7rE7.
  apply swap_sample_if2; [ apply SLGb_dom_r | | | intros k m1 m2 H; rewrite H; trivial].
  
  (****** The difficult case *****) 
  ep; deadcode; swap; eqobs_tl.
  match goal with |- equiv ?P _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6] _ _ ?Q =>
    change [i1; i2; i3; i4; i5; i6] with ([i1]++[i2; i3; i4; i5; i6]);
    apply equiv_trans with P Q Q E7r ([i1; R <- r] ++ (sample_true LGb_hd LGb_tl LGb ++ [i5; i6]))
  end.
  auto. intros k m1 m2 (H1, H2); split; trivial. apply req_mem_trans.
  deadcode. eqobs_in. 
  match goal with |- equiv ?P _ ([?i1; _]++ _ ++[?i5; ?i6]) _ _ ?Q => 
    apply equiv_trans with P Q Q E7r ([i1; R <- r] ++ split_sample ++ [i5; i6])
  end.
  auto. intros k m1 m2 (H1, H2); split; trivial. apply req_mem_trans.
  apply equiv_app with (req_mem_rel {{mn,r,R,rGn,rGk1,LD,LH,Dc,bad,R',LGb}}
   (EP1 (R in_dom LGb))).
  eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; 
   simpl; intros k m1 m2 (H1, H2); repeat split; intros; trivial.
  match goal with |- equiv _ _ _ _ _ (kreq_mem ?O) => 
   apply equiv_app with (req_mem_rel (Vset.remove LGb O) trueR); [ | eqobs_in] end.
  union_mod.
  eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply sample_split] ].
  intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  intros k m1 m2 (H1, H2); split; [apply req_mem_weaken with (2:= H1); vm_compute | ]; trivial.

  match goal with |- equiv ?P _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6] ?Q =>
    change [i1; i2; i3; i4; i5; i6] with (nil ++ ([i1; i2; i3; i4; i5]++[i6]));
    apply equiv_trans with P Q Q E7 ([R <- r] ++ ((sample_true LGb_hd LGb_tl LGb ++ [i4; i5])++[i6]))
  end.
  auto. intros k m1 m2 (H1, H2); split; trivial. apply req_mem_trans.
  2:deadcode; eqobs_in. 
  match goal with |- equiv ?P _ _ _ (?C0 ++ (_ ++ ?C1) ++ ?C2) ?Q => 
    apply equiv_trans with P Q Q E7 (C0 ++ (split_sample ++ C1) ++ C2)
  end.
  auto. intros k m1 m2 (H1, H2); split; trivial. apply req_mem_trans.
  Focus 2.
  apply equiv_app with (req_mem_rel {{s,r,R,rGn,rGk1,LD,LH,Dc,bad,R',LGb}}
   (EP1 (R in_dom LGb))).
    eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl; intros k m1 m2 (H1, H2); intros; trivial.
    eqobs_tl_n 3.
    match goal with |- equiv _ _ _ _ _ (kreq_mem ?O) => apply equiv_weaken with (req_mem_rel O trueR) end.
      intros k m1 m2 (H1, H2); trivial.
    union_mod;  apply equiv_sym; auto.
      unfold EP1; split; intros k m1 m2 (H1, H2); (split; [apply req_mem_sym; trivial | ]);
      unfold is_true; rewrite <- H2; simpl; unfold O.eval_op; simpl; rewrite (H1 _ R), (H1 _ LGb); trivial.
    eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply sample_split] ].
    intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
    intros k m1 m2 (H1, H2); split; [apply req_mem_weaken with (2:= H1); vm_compute | ]; trivial.
  ep_eq LGb (Efst (r Esplit LGb) |++| (r | Efst (Esnd (r Esplit LGb))) |::| Esnd (Esnd (r Esplit LGb))).
    intros k m1 m2 (Heq, H1); rewrite <- Heq.
    simpl; unfold O.eval_op; simpl.
    rewrite <- (split_append_mem k (Var.btype r) Tbnk1 (m1 r) 
      (false, (Ut.default k Bitstring_n, Ut.default k Bitstring_k1)) (m1 LGb)) at 1 5.
    unfold EP1 in H1; simpl in H1; unfold O.eval_op in H1; simpl in H1; simpl; rewrite H1; auto.
  deadcode.
  match goal with |- equiv _ _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8; ?i9; ?i10; ?i11] _ => 
    change [i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11] with (([i1; i2] ++ [i3]) ++[i4; i5; i6; i7; i8; i9; i10; i11]);
    apply equiv_trans_eq_mem_r with trueR E7 
    ( ([ i1; i2] ++
       [sample_while LGb_hd_hd LGb_hd_tl])  ++
     [i4] ++ 
     sample_true LGb_tl_hd LGb_tl_tl (Esnd (Esnd (r Esplit LGb))) ++
     [i8;
      If Efst LGbR2 then [mn <- (false | one_n)]
      else [ If Esnd (s) |x| Esnd (Esnd LGbR2) =?= zero_k1 then [
                 mn <- (true | Efst s |x| Efst (Esnd LGbR2))
             ] else [mn <- (false | one_n)]
      ];
      i9; i10
     ]) end.
   3: red; red; trivial.
   apply equiv_app with (Meq /-\ ~-EP1 (r in_dom LGb_hd_hd)).
   apply equiv_app with (Meq /-\ ~-EP1 (r in_dom LGb_hd_hd) /-\ ~-EP1 (r in_dom LGb_hd_tl)).
   rewrite proj1_MR; union_mod; trivial.
   eqobsrel_tail; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; split.
   rewrite <- is_true_negb; trivial.
   rewrite not_is_true_false; refine (@existsb_fst_split k BS_k0 Tbnk1 _ _).
   eapply equiv_weaken; [ | apply equiv_while].
   unfold andR; intuition.  intros k m1 m2 (Heq, _); rewrite Heq; trivial.
   union_mod. rewrite proj1_MR, proj1_MR; trivial.
   eqobsrel_tail; unfold EP1, EP2, andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
    decompose [and] H; clear H.
   red in H0; subst. destruct (m2 LGb_hd_tl); [discriminate | simpl in *].
   apply not_is_true_false in H1.
   destruct i; split; intros; rewrite existsb_app, H1; simpl in *;
    destruct (T.i_eqb k BS_k0 (m2 r) i); simpl in *; split; trivial.
   elim H4; trivial. discriminate. elim H4; trivial. discriminate.
   ep_eq_l (r in_dom LGb_hd_hd) false.
    unfold notR, EP1; intros k m1 m2 (H1, H2); rewrite not_is_true_false in H2; trivial.
   rewrite proj1_MR; union_mod; trivial.
   apply equiv_strengthen with  
    (kreq_mem {{s,r,LD,LH,LGb,R,rGn_aux1,rGk1_aux1,LGb_tl_hd,LGb,R,rGn_aux1,
     rGk1_aux1,LGb_tl_hd,LGb_tl_tl,aux,rGn_aux,rGk1_aux,LGb_tl,LGb_hd_hd}}).
     intros k m1 m2 H; rewrite H; trivial.
   eqobs_hd; swap; eqobs_in.
   cp_test (Efst (Efst (Esnd (r Esplit LGb)))).
   alloc_l LGb LGb1.
   ep; deadcode. ep; deadcode.
   swap. repeat rewrite proj1_MR; eqobs_in.
   swap. eqobs_tl.
   ep_eq_r (Efst (Efst (Esnd (r Esplit LGb)))) false.
     intros k m1 m2 (_, (_, H2)); unfold notR, EP2 in H2.
     apply not_is_true_false in H2; exact H2.
   rewrite proj1_MR; eqobs_in.
 
  rewrite proj1_MR.
  match goal with |- equiv _ _ ([?i1; ?i2; ?i3; ?i4; ?i5] ++ _) _ _ _ =>
     change [i1; i2; i3; i4; i5] with ([i1]++[i2; i3; i4; i5]) end.
  apply swap_sample_app2.
  swap. union_mod. trivial. eqobs_in.
  union_mod. trivial. eqobs_in.
  apply swap_equiv_Gbaddr.
 
  match goal with
   |- equiv _ _ ([?i1; ?i2; ?i3; ?i4]++ _) _ _ _ => 
    change [i1; i2; i3; i4] with ([i1; i2]++[i3; i4]) 
  end.
  apply swap_sample_app2.
  swap iE7. union_mod iE7. trivial. eqobs_in iE7.
  union_mod iE7rE7. trivial. eqobs_in iE7rE7.
  apply equiv_trans_eq_mem_l with (P1:= trueR) (E1':=E7r) 
   (c1':= [ If !(r in_dom LGb) then [
                rGn <$- {0,1}^n;
                rGk1 <$- {0,1}^k1;
                LGb <- (r | (true | (rGn | rGk1))) |::| LGb;
                mn <- (false | one_n) ]
            else [mn <- (false | one_n) ] 
          ] ++ SLGb).
  rewrite proj1_MR.
  cp_test (r in_dom LGb); rewrite proj1_MR; union_mod; trivial; eqobs_in.
  apply equiv_trans_eq_mem_r with (P2:= trueR) (E2':=E7) 
   (c2':= (SLGb ++ [ If !(r in_dom LGb) then [
                rGn <$- {0,1}^n;
                rGk1 <$- {0,1}^k1;
                LGb <- (r | (true | (rGn | rGk1))) |::| LGb;
                mn <- (false | one_n) ]
            else [mn <- (false | one_n) ] 
          ])).
  rewrite proj1_MR.
  apply equiv_app with Meq. apply equiv_eq_mem.
  cp_test (r in_dom LGb); rewrite proj1_MR; union_mod; trivial; eqobs_in.
  apply swap_sample_if2.
  intros b; eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply (SLGb_dom_r _ (negb b))] ].
  unfold EP1; intros k m1 m2 (H1, H2); split; [trivial | ].
  generalize H2; simpl; unfold O.eval_op; simpl; intros Heq.
  rewrite is_true_Ti_eqb in Heq; rewrite Heq; rewrite negb_involutive; apply Ti_eqb_refl.
  unfold EP1; intros k m1 m2 (H1, H2); split; [trivial | ].
  generalize H2; simpl; unfold O.eval_op; simpl; intros Heq.
  rewrite is_true_Ti_eqb in Heq; rewrite <- Heq; rewrite negb_involutive; apply Ti_eqb_refl.
  rewrite proj1_MR.
  apply swap_equiv_Gbaddr.
  rewrite proj1_MR; apply equiv_weaken with Meq.
  intros k m1 m2 H; rewrite H; trivial.
  apply check_swap_c_correct with (I:= ISLGb) (pi:= swi7_G).
  apply Modify_SLGb. 
  apply Modify_SLGb. 
  apply EqObs_SLGb.
  vm_compute; trivial.
  intros k m1 m2 Heq; rewrite Heq; trivial.
  red; red; trivial.
  red; red; trivial.
 Qed.

 Definition swi7 : forall tg g, option (sw_info SLGb XSLGb ISLGb E7r E7 tg g) :=
  let swiD := add_sw_info2 SLGb XSLGb ISLGb E7r E7 (Modify_SLGb E7r) (Modify_SLGb E7) 
     (EqObs_SLGb E7r E7) IXSLGb_global swi7_G _ Dec M7 M7 M7_E7r M7_E7 swap_equiv_SLGb_Dec in
   let swiGA := add_sw_info_refl SLGb XSLGb ISLGb E7r E7 (Modify_SLGb E7r) (Modify_SLGb E7) (EqObs_SLGb _ _) 
            IXSLGb_global swiD _ GAdv in
   let swiA := add_sw_info_Adv SLGb XSLGb ISLGb E7r E7 (Modify_SLGb E7r) (Modify_SLGb E7) (EqObs_SLGb _ _)
            IXSLGb_global swiGA _ A PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _ _ _ _ _) (A_wf_E _ _ _ _) in
   let swiA' := add_sw_info_Adv SLGb XSLGb ISLGb E7r E7 (Modify_SLGb E7r) (Modify_SLGb E7) (EqObs_SLGb _ _)
            IXSLGb_global swiA _ A' PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _ _ _ _ _) (A'_wf_E _ _ _ _) in
    swiA'.

 Lemma equiv_E7_E7r :
  EqObs 
  {{Y', bad2, g_a}}
  E7  G2b 
  E7r (G2b ++ SLGb) 
  {{bad, bad2, LD, LH, LGb}}.
 Proof.
  apply equiv_trans_eq_mem_r with trueR E7
    (([bad <- false] ++ init1b) ++ (SLGb ++ (SGR' ++ [S' <- (GR'n | GR'k1)] ++ tail2))).
  2:ep; deadcode iE7; eqobs_in iE7.
  2: red; red; trivial.
  unfold G2b.
  replace (([bad <- false] ++ init1b ++ SGR' ++ [S' <- (GR'n | GR'k1)] ++ tail2) ++ SLGb) with
   (([bad <- false] ++ init1b) ++ ((SGR' ++ [S' <- (GR'n | GR'k1)] ++ tail2) ++ SLGb)).
  2: repeat rewrite app_ass; trivial.
  apply equiv_app with Meq.
  rewrite proj1_MR; union_mod; trivial. eqobs_in.
  apply check_swap_c_correct with (I:= ISLGb) (pi:= swi7).
  apply Modify_SLGb. apply Modify_SLGb. apply EqObs_SLGb.
  vm_compute; trivial.
 Qed.


 Definition G_body2r_bad2' :=
  [ 
   If Elen LD <=! qD then G_body2r_bad2
   else [rGn <- one_n; rGk1 <- zero_k1] 
  ].

 Definition E7r' := mkEnv H_body0 G_body2r_bad2' Dec_body7r.

 Fixpoint no_double k (l:T.interp k T_assoc_b) :=
  match l with
  | nil => true
  | a :: l =>
    andb (negb (existsb (fun b => T.i_eqb k BS_k0 (fst a) (fst b)) l))
         (no_double l)
  end.

 Lemma no_double_upd : forall k v v0 v1 i b, 
  no_double (O.upd (T.i_eqb k BS_k0) v1 (b, (v, v0)) i) =
  no_double i.
 Proof.
  induction i; simpl no_double; intros; trivial.
  destruct a.
  case_eq (T.i_eqb k BS_k0 v1 i0); simpl; trivial.
  intros; apply f_equal2; [apply f_equal | trivial].
  refine (@existsb_upd_diff k BS_k0 Tbnk1 _ _ _ _ _).
  rewrite <- not_is_true_false, is_true_Ti_eqb in H; auto.
 Qed.


 Definition inv_qD := EP2 ((Elen LD <=! qD) && (Elen LD =?= Dc)).

 Definition No_double_LGb : mem_rel := fun k m1 m2 => no_double (m2 LGb).

 Definition inv_qD_LGb := inv_qD /-\ No_double_LGb.

 Lemma dec_No_double_LGb : decMR No_double_LGb.
 Proof.
  red; intros; unfold No_double_LGb.
  destruct (no_double (y LGb)); [left; trivial | right; discriminate].
 Qed.

 Lemma dep_No_double_LGb : depend_only_rel No_double_LGb Vset.empty {{LGb}}.
 Proof.
  red; intros; unfold No_double_LGb.
  rewrite <- (H0 _ LGb); trivial.
 Qed.
 
 Lemma dec_inv_qD : decMR inv_qD_LGb.
 Proof.
  unfold inv_qD_LGb, inv_qD; auto using dec_No_double_LGb.
 Qed.

 Lemma dep_inv_qD : depend_only_rel inv_qD_LGb (Vset.union Vset.empty Vset.empty)
  (Vset.union (fv_expr ((Elen LD <=! qD) && (Elen LD =?= Dc))) {{LGb}}).
 Proof.
  unfold inv_qD_LGb, inv_qD; auto using dep_No_double_LGb.
 Qed.

 Definition eE7rE7r' :=
  add_refl_info H 
   (@empty_inv_info inv_qD_LGb 
    _ _ dep_inv_qD (refl_equal true) dec_inv_qD E7r E7r').

 Lemma EqObs_G_7r_7r' :
  EqObsInv inv_qD_LGb 
  {{R,R',LD,LH,bad,bad2,LGb}}
  E7r G_body2r_bad2 
  E7r' G_body2r_bad2' 
  {{bad,bad2,rGn,rGk1,LGb}}.
 Proof.
  ep_eq_r (Elen LD <=! qD) true.
    unfold inv_qD_LGb, inv_qD, EP2; simpl; unfold O.eval_op; simpl.
    intros k m1 m2 (_, (H, H0)); rewrite is_true_andb in H; destruct H; trivial.
  ep.
  unfold inv_qD_LGb, inv_qD; eqobsrel_tail; unfold andR, notR; simpl; unfold O.eval_op; simpl;
    intros k m1 m2 H; decompose [and] H.
  unfold No_double_LGb in *; repeat split; intros; trivial;
  mem_upd_simpl; trivial.
  simpl. destruct H1 as (W1, W2); rewrite W2; trivial.
  simpl. destruct H1 as (W1, W2); rewrite W2; trivial.
  unfold is_true; rewrite <- H3; apply no_double_upd.
  unfold is_true; rewrite <- H3; apply no_double_upd.
 Qed. 

 Lemma EqObs_Dec_7r_7r' :
  EqObsInv inv_qD_LGb 
  (Vset.add LD (Vset.add LGb (Vset.remove LG ID)))
  E7r Dec_body7r 
  E7r' Dec_body7r
  (Vset.add LD (Vset.add LGb (Vset.remove LG OD))).
 Proof.
  unfold Dec_body7r, Dec_body_gen_b.  
  cp_test (E.Eop O.Oor {testD, (qD +! qG) <! (Elen LGb)}).
  rewrite proj1_MR; eqobs_in eE7rE7r'.
  match goal with |- equiv _ _ (?i1::?i2::?c) _ _ _ =>
   change (i1::i2::c) with ([i1; i2]++c) end.
  apply equiv_app with (req_mem_rel (Vset.add LD (Vset.add LGb (Vset.remove LG ID))) inv_qD_LGb).
  rewrite req_mem_rel_assoc; unfold inv_qD_LGb, inv_qD; eqobsrel_tail.
  Opaque leb.
   unfold EP2, testD, andR, notR; simpl; unfold O.eval_op; simpl.
   intros k m1 m2 H; decompose [and] H; split.
   repeat rewrite is_true_orb in H5; rewrite is_true_leb in *.
   rewrite is_true_andb in H1; rewrite is_true_Ti_eqb in H1.
   destruct H1.
   rewrite H3, Ti_eqb_refl, andb_true_r.
   rewrite is_true_leb; omega'.
   unfold No_double_LGb in *; mem_upd_simpl; trivial.
  cp_test (Efst (ap_finv c) in_dom LH); rewrite proj1_MR; eqobs_hd eE7rE7r'.
  cp_test (t |x| h in_dom LGb).
  cp_test (Efst (LGb [{t |x| h}])); rewrite proj1_MR; [ | eqobs_in eE7rE7r'].
  rewrite req_mem_rel_assoc; unfold inv_qD_LGb, inv_qD; eqobsrel_tail;
   unfold andR, EP2, notR; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; 
   decompose [and] H.
  unfold No_double_LGb in *; repeat split; trivial; mem_upd_simpl; trivial.
  unfold implMR, andR; tauto.

  rewrite req_mem_rel_assoc; unfold inv_qD_LGb, inv_qD; eqobsrel_tail;
   unfold andR, EP2, notR; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; decompose [and] H.
  unfold No_double_LGb in *; repeat split; trivial; mem_upd_simpl; trivial.
  rewrite not_is_true_false in H5; simpl; rewrite H5; trivial.
  rewrite not_is_true_false in H5; simpl; rewrite H5; trivial.

  cp_test (t |x| h in_dom LGb).
  rewrite proj1_MR; eqobs_in eE7rE7r'.
  rewrite req_mem_rel_assoc; unfold inv_qD_LGb, inv_qD; eqobsrel_tail;
   unfold andR, EP2, notR; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; decompose [and] H.
  unfold No_double_LGb in *; repeat split; trivial; mem_upd_simpl; trivial.
  rewrite not_is_true_false in H5; simpl; rewrite H5; trivial.
 Qed. 

 Definition iE7rE7r' :=  
  let RM := Vset.empty in
  let piG := add_info G RM RM eE7rE7r' EqObs_G_7r_7r' in
  let piD := add_info Dec RM RM piG EqObs_Dec_7r_7r' in
  let piGA := add_refl_info GAdv piD in
   adv_info piGA. 

 Section PR_7_bad2.
 
  Variable k : nat.

  Definition testLGb (m:Mem.t k) (v:T.interp k (T.Pair T.Bool BS_k)) : bool :=
   EP k 
   (let c := Esnd (tc) in
    let s := Efst (ap_finv c) in
    let t := Esnd (ap_finv c) in
    let h := LH [{s}] in
    let r := t |x| h in
    let g := Esnd (LGb [{r}]) in
    let m := s |x2| g in
     ((s in_dom LH) && (r in_dom LGb)) && !(Efst (LGb [{r}])))
     (m{!tc <-- v!}).

  Definition testR (m:Mem.t k) (v:T.interp k (T.Pair T.Bool BS_k)) : bool := 
    EP k
    (let c := Esnd (tc) in
     let s := Efst (ap_finv c) in
     let t := Esnd (ap_finv c) in
     let h := LH [{s}] in
     let r := t |x| h in
     let g := (rGn | rGk1) in
     let m := s |x2| g in
      (r =?= R) && (s in_dom LH))
      (m{!tc <-- v!}).

  Definition bad2_K (mn':Mem.t k) :=
   (charfun (EP k bad2) mn' +
    (qD_poly k - length (filter (testLGb mn') (mn' LD)))/2^k1 k)%U.

  Definition dep_bad2_K := {{bad2, LGb, LH, LD}}.

  Lemma dep_bad2_K_correct : depend_only_f bad2_K dep_bad2_K.
  Proof.
   intros m1 m2 H.
   unfold bad2_K, testLGb, charfun, restr, EP; simpl; unfold O.eval_op; simpl.
   rewrite (H _ bad2); trivial. apply Uplus_eq_compat; trivial.
   apply Nmult_eq_compat_left; trivial.
   apply f_equal. apply f_equal.
   rewrite (H _ LD); trivial; generalize (m2 LD).
   induction i; simpl; trivial.
   rewrite IHi;   
   mem_upd_simpl;
   try rewrite (H _ LGb); trivial; try rewrite (H _ LH); trivial.
  Qed.

  Definition epr7 : PrBad_info E7r' bad2_K.
   refine (@Build_PrBad_info k E7r' bad2_K _ dep_bad2_K_correct _ 
    (fun _ _ => false) _).
   abstract (apply Vset.forallb_correct; 
    [ intros x y Heq; rewrite Heq; trivial | vm_compute; trivial]).
   abstract (intros; discriminate).
  Defined.

  Lemma inv_bad7r_H : inv_bad E7r' bad2_K H_body0.
  Proof.
   unfold H_body0, inv_bad; intros.
   rewrite deno_cond_elim.
   match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Heq;
     [ change (is_true x) in Heq | ] end.
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   transitivity 
      (mu
        (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))
        (fcte _ (bad2_K m))).
   apply mu_monotonic; intros v.
   rewrite deno_assign_elim; unfold fcte, bad2_K, fplus, Fmult.
   apply Uplus_le_compat.
   unfold charfun, restr, EP; simpl; unfold O.eval_op; simpl;
   mem_upd_simpl;
   trivial.
   apply Nmult_le_compat; trivial.
   refine (minus_le_compat_l _ _ _ _).
   mem_upd_simpl.
   generalize (m LD).
   Opaque E.eval_expr.
   induction i; simpl; trivial.
   case_eq (testLGb m a); intros.
   match goal with |- context [(if ?x then _ else _)] => 
     replace x with true end.
    simpl; apply le_n_S; trivial.
    symmetry; match goal with |- ?x = true =>
      change (is_true x); change (is_true (testLGb m a)) in H end.
  Transparent E.eval_expr.
    generalize H; clear H; unfold testLGb, EP; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
    intros H; repeat rewrite is_true_andb in H; decompose [and] H.
    simpl. rewrite H2, orb_true_r.
    unfold O.assoc at 1 3; simpl.
    match goal with |- context [(if ?x then _ else _)] => case_eq x; intros end.
    match type of H0 with ?x = _ => change (is_true x) in H0 end.
    rewrite is_true_Ti_eqb in H0; rewrite H0 in *.
    generalize Heq; simpl; unfold O.eval_op; simpl.
    rewrite is_true_negb; intros F; elim F; trivial.
    rewrite is_true_andb; split; trivial.
   match goal with |- context [(if ?x then _ else _)] => destruct x end;
   simpl; auto using le_S. 
   apply mu_cte_le.
   assert (inv_bad E7r' bad2_K [rH <- LH[{S}] ]).
   apply inv_bad_ass with dep_bad2_K. apply dep_bad2_K_correct.
   discriminate.
   apply H.
  Qed. 

  Lemma inv_bad7r_G : inv_bad E7r' bad2_K G_body2r_bad2'.
  Proof.
   unfold G_body2r_bad2', G_body2r_bad2, G_body2b_gen.
   apply EqObs_inv_bad with (1:= dep_bad2_K_correct) (I:= Vset.add R dep_bad2_K)
    (c:= [
     If Elen LD <=! qD _then [
     If !(R in_dom LGb)  then Gbaddr false R
     else [
        If Efst (LGb [{R}]) _then 
           [rGn <$- {0,1}^n; rGk1 <$- {0,1}^k1] ++
           [If test_exists _then [bad2 <- true] ] ++
           [LGb <- LGb Upd R <| (false | (rGn | rGk1))]
     ] ] ]).
   deadcode; eqobs_in.
   unfold inv_bad; intros; rewrite deno_cond_elim.
   match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Hl end.
   2: rewrite deno_nil_elim; trivial.
   rewrite deno_cond_elim.
   match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Heq end.
   unfold Gbaddr.
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   transitivity 
    (mu (sum_support (T.default k BS_n) (E.eval_support {0,1}^n m))
        (fcte _ (bad2_K m))); [apply mu_monotonic; intros v1| apply mu_cte_le].
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   transitivity 
     (mu
       (sum_support (T.default k BS_k1)
          (E.eval_support {0,1}^k1 (m {!rGn <-- v1!})))
        (fcte _ (bad2_K m))); [apply mu_monotonic; intros v2| apply mu_cte_le].
   rewrite deno_assign_elim; unfold fcte, bad2_K, fplus, Fmult.
   apply Uplus_le_compat.
   unfold charfun, restr, EP; simpl; unfold O.eval_op; simpl;
   mem_upd_simpl;
   trivial. 
   apply Nmult_le_compat; trivial.
   refine (minus_le_compat_l _ _ _ _).
   mem_upd_simpl.
   generalize (m LD).
   Opaque E.eval_expr.
   induction i; simpl; trivial.
   case_eq (testLGb m a); intros.
   match goal with |- context [(if ?x then _ else _)] => 
     replace x with true end.
    simpl; apply le_n_S; trivial.
    symmetry; match goal with |- ?x = true =>
      change (is_true x); change (is_true (testLGb m a)) in H end.
   Transparent E.eval_expr.
    generalize H; clear H; unfold testLGb, EP; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
    intros H; repeat rewrite is_true_andb in H; decompose [and] H.
    simpl. rewrite H2.
    unfold O.assoc at 2 3; simpl.
    match goal with |- context [(if ?x then _ else _)] => case_eq x; intros end.
    match type of H0 with ?x = _ => change (is_true x) in H0 end.
    rewrite is_true_Ti_eqb in H0; rewrite H0 in *.
    change (is_true (E.eval_expr (!(R in_dom LGb)) m)) in Heq.
    generalize Heq; simpl; unfold O.eval_op; simpl.
    rewrite is_true_negb; intros F; elim F; trivial.
    rewrite is_true_andb; split; trivial.
  match goal with |- context [(if ?x then _ else _)] => destruct x end;
   simpl; auto using le_S. 
  rewrite deno_cond_elim.
  match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Heq0 end.
  simpl app.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  transitivity 
     (mu (sum_support (T.default k BS_n) (E.eval_support {0,1}^n m))
        (fcte _ (bad2_K m))); [apply mu_monotonic; intros v1| apply mu_cte_le].
  unfold fcte, bad2_K, charfun, restr, fone.
  case_eq (EP k bad2 m); intros Heq1; repeat Usimpl; trivial.
 
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  set (m1 := m{!rGn <-- v1!}).
  transitivity
    (mu
      (sum_support (T.default k BS_k1) (E.eval_support {0,1}^k1 m1))
      (fplus
         (fun v2 => charfun (EP k test_exists) (m1{!rGk1<--v2!}))
         (fcte _ 
           ((qD_poly k - ((length (filter (testLGb m) (m LD)) + 
                     length (filter (testR m) (m LD)))))/2^k1 k)%U))).
  apply mu_monotonic; intros v2; unfold fplus, fcte.
  rewrite deno_cons_elim, Mlet_simpl, deno_cond_elim.
  match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Heq2 end.
  rewrite deno_assign_elim, deno_assign_elim.
  apply Uplus_le_compat; trivial.
  unfold charfun, restr, EP; rewrite Heq2; trivial.
  apply Nmult_le_compat_left; trivial.
  refine (minus_le_compat_l _ _ _ _).
  unfold m1; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
  generalize (m LD). 
  induction i; simpl; trivial.
  match goal with |- _ <= length (if ?x then _ else _) => 
      case_eq x; intros Heq3; [change (is_true x) in Heq3 | ] end.
  case_eq (testLGb m a); intros Heq4; [change (is_true (testLGb m a)) in Heq4 | ].
  replace (testR m a) with false.
  simpl; omega'.
  symmetry; rewrite <- not_is_true_false; generalize Heq4 Heq0 Heq; clear Heq4 Heq0 Heq.
  unfold testLGb, testR, EP; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  repeat rewrite is_true_andb; rewrite is_true_Ti_eqb; intros ((W1,W2),W3) W4 W7 (W5,W6).
  rewrite W5, W4 in W3; discriminate W3.
  case_eq (testR m a); intros; simpl; omega'.
  assert (~(testLGb m a \/ testR m a)).
    generalize Heq3 Heq0 Heq; clear IHi Heq3 Heq0 Heq; rewrite <- not_is_true_false.
     unfold testLGb, testR, EP; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
     repeat rewrite is_true_andb; rewrite is_true_Ti_eqb; intros W1 W2 W8.
     intros [((W3,W4), W5) | (W6,W7)]; apply W1.
     match type of W5 with (is_true (negb (fst (O.assoc (T.i_eqb _ _ ?x) _ _)))) =>
      case_eq (T.i_eqb k BS_k0 x (m R)); intros HH;
      [change (is_true (T.i_eqb k BS_k0 x (m R))) in HH 
      | rewrite <- not_is_true_false in HH]; rewrite is_true_Ti_eqb in HH end.
     rewrite HH in *; repeat split; trivial.
     apply (@existsb_upd_same k BS_k0 Tbnk1).
     rewrite (@assoc_upd_same k BS_k0 Tbnk1); trivial.  
     repeat split; trivial.
     rewrite (@existsb_upd_diff k BS_k0 Tbnk1); trivial.
     rewrite (@assoc_upd_diff k BS_k0 Tbnk1); trivial.  
     rewrite W6 in *; repeat split; trivial.
     apply (@existsb_upd_same k BS_k0 Tbnk1).
     rewrite (@assoc_upd_same k BS_k0 Tbnk1); trivial.  
  replace (testLGb m a) with false; [ replace (testR m a) with false; trivial | ];
  symmetry; rewrite <- not_is_true_false; intros W; apply H; auto.
  rewrite deno_nil_elim, deno_assign_elim.
  apply Uplus_le_compat.
  generalize Heq1; unfold EP at 1 2; unfold m1; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  intros HH; rewrite HH; trivial.
  apply Nmult_le_compat_left; trivial.
  refine (minus_le_compat_l _ _ _ _). 
 unfold m1; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
  generalize (m LD). 
  induction i; simpl; trivial.
  match goal with |- _ <= length (if ?x then _ else _) => 
      case_eq x; intros Heq3; [change (is_true x) in Heq3 | ] end.
  case_eq (testLGb m a); intros Heq4; [change (is_true (testLGb m a)) in Heq4 | ].
  replace (testR m a) with false.
  simpl; omega'.
  symmetry; rewrite <- not_is_true_false; generalize Heq4 Heq0 Heq; clear Heq4 Heq0 Heq.
  unfold testLGb, testR, EP; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  repeat rewrite is_true_andb; rewrite is_true_Ti_eqb; intros ((W1,W2),W3) W4 W7 (W5,W6).
  rewrite W5, W4 in W3; discriminate W3.
  case_eq (testR m a); intros; simpl; omega'.
  assert (~(testLGb m a \/ testR m a)).
    generalize Heq3 Heq0 Heq; clear IHi Heq3 Heq0 Heq; rewrite <- not_is_true_false.
     unfold testLGb, testR, EP; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
     repeat rewrite is_true_andb; rewrite is_true_Ti_eqb; intros W1 W2 W8.
     intros [((W3,W4), W5) | (W6,W7)]; apply W1.
     match type of W5 with (is_true (negb (fst (O.assoc (T.i_eqb _ _ ?x) _ _)))) =>
      case_eq (T.i_eqb k BS_k0 x (m R)); intros HH;
      [change (is_true (T.i_eqb k BS_k0 x (m R))) in HH 
      | rewrite <- not_is_true_false in HH]; rewrite is_true_Ti_eqb in HH end.
     rewrite HH in *; repeat split; trivial.
     apply (@existsb_upd_same k BS_k0 Tbnk1).
     rewrite (@assoc_upd_same k BS_k0 Tbnk1); trivial.  
     repeat split; trivial.
     rewrite (@existsb_upd_diff k BS_k0 Tbnk1); trivial.
     rewrite (@assoc_upd_diff k BS_k0 Tbnk1); trivial.  
     rewrite W6 in *; repeat split; trivial.
     apply (@existsb_upd_same k BS_k0 Tbnk1).
     rewrite (@assoc_upd_same k BS_k0 Tbnk1); trivial.  
  replace (testLGb m a) with false; [ replace (testR m a) with false; trivial | ];
  symmetry; rewrite <- not_is_true_false; intros W; apply H; auto.
  set (QD:= qD_poly k).
  set (FR := filter (testR m) (m LD)).
  set (FGb := filter (testLGb m) (m LD)).
  set (LL := length FGb + length FR).
  rewrite mu_le_plus, mu_cte_le. 
  transitivity ((length FR /2^k1 k) + (QD - LL)/2^k1 k)%U.
  apply Uplus_le_compat; trivial.
 
  set (def:= T.default k (T.Pair T.Bool BS_k)).
  transitivity 
    (mu (sum_support (T.default k BS_k1) (E.eval_support {0,1}^k1 m))
         (sigma_fun 
               (fun i v => charfun (T.i_eqb k BS_k1 v) 
                               (snd (fst (finv (snd (nth i FR def))))))
               (length FR))).
   apply mu_monotonic; intro v; unfold fplus,sigma_fun.
   unfold charfun at 1; unfold restr.
   match goal with |- context [if ?x then _ else _] =>
     case_eq x; intros Heq2; [change (is_true x) in Heq2 | trivial] end.
   set (ff:= (fun k2 : nat =>
       charfun (T.i_eqb k BS_k1 v)
         (snd (fst (finv (k:=k) (snd (nth k2 FR def))))))).
   assert (exists i, i < (length FR) /\ 
                        (T.i_eqb k BS_k1 v 
                            (snd (fst (finv (k:=k) (snd (nth i FR def))))))).
   apply nth_existsb with (f :=
     fun w =>  T.i_eqb k BS_k1 v (snd (fst (finv (k:=k) (snd w))))).
   generalize Heq2; unfold FR, test_exists; clear.
   unfold EP, m1; simpl; unfold O.eval_op; simpl;
   mem_upd_simpl.
   generalize (m LD); intros mLD; repeat rewrite is_true_existsb.
   intros (x, (H1, H2)); generalize H2; clear H2;
    mem_upd_simpl;
    repeat rewrite is_true_andb; intros ((H2, H3), H4).
    exists x; split.
    rewrite filter_In; split; trivial.
    unfold testR, EP; simpl; unfold O.eval_op; simpl.
    mem_upd_simpl.
    rewrite H2; trivial.
    rewrite is_true_Ti_eqb in H4; apply BVxor_eq in H4.
    rewrite <- H4; apply Ti_eqb_refl.
  
  destruct H as (i, (H1, H2)).
   apply Ole_trans with (2:= sigma_le ff H1).
   unfold ff, charfun, restr, EP; rewrite H2; trivial.
   rewrite mu_sigma_le, Nmult_sigma; apply sigma_le_compat.
   intros k2 Hlt; apply Oeq_le.
   apply Pr_bs_support with
    (v:= (snd (fst (finv (k:=k) (snd (nth k2 FR def))))))
    (f := fun v1 v2 => charfun (T.i_eqb k BS_k1 v2) v1).
   intros x Hd; unfold charfun,restr.
   rewrite <- (is_true_Ti_eqb k BS_k1), not_is_true_false in Hd.
   rewrite Hd; trivial.
   unfold charfun,restr; rewrite Ti_eqb_refl; trivial.
 
  rewrite Uplus_sym, <- plus_Nmult_distr.
  apply Nmult_le_compat; trivial.
  change  (QD - LL + length FR <= QD - length FGb); unfold LL.
  assert ((length FGb + length FR) <= QD); [ | omega'].
  apply le_trans with (length (m LD)).
  unfold FR, FGb; generalize (m LD).
  induction i; simpl; trivial.
  case_eq (testLGb m a); intros.
  replace (testR m a) with false.
  simpl; apply le_n_S; trivial.
  symmetry; rewrite <- not_is_true_false; change (is_true (testLGb m a)) in H;
    generalize H Heq0; clear H Heq0.
  unfold testLGb, testR, EP; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  repeat rewrite is_true_andb; rewrite is_true_Ti_eqb; intros H1 Heq0 H2;
   decompose [and] H1; decompose [and] H2; clear H1 H2.
  rewrite H in *; clear H. rewrite Heq0 in H0; discriminate.
  destruct (testR m a).
   simpl; rewrite <- plus_n_Sm; apply le_n_S; trivial.
   apply le_S; trivial.
  match type of Hl with ?x = true => change (is_true x) in Hl end.
  generalize Hl; simpl; unfold O.eval_op; simpl; rewrite is_true_leb; trivial.
  rewrite deno_nil_elim; trivial.
  Qed. 

  Definition ipr7H := add_prbad epr7 H inv_bad7r_H.

  Definition iE7r' := iEiEi H_body0 G_body2r_bad2' Dec_body7r.

  Lemma inv_bad7r_Dec : inv_bad E7r' bad2_K Dec_body7r.
  Proof.
   unfold Dec_body7r, Dec_body_gen_b.
   apply inv_bad_if.
    apply check_inv_bad_c_correct with epr7. vm_compute; trivial.
    apply EqObs_inv_bad with (1:=dep_bad2_K_correct) 
     (I:=Vset.add R' (Vset.add c (Vset.add Ydef dep_bad2_K)))
    (c:= [
     st <- ap_finv c;
     s <- Efst (st);
     t <- Esnd (st);
     h <c- H with {s};
     r <- t |x| h] ++
     [ If r in_dom LGb then [ LD <- (Ydef | c) |::| LD ]
       else [
          rGn <$- {0,1}^n;
          rGk1 <$- {0,1}^k1;
          LGb <- (r | (true | (rGn | rGk1))) |::| LGb;
          LD <- (Ydef | c) |::| LD
        ]
     ]).
  match goal with |- EqObs _ _ _ _ (?i::?c) _ => 
    apply EqObs_trans with E7r' (c ++ [i]) end.  
  2: swap iE7r'; eqobs_in iE7r'.
  ep iE7r'; deadcode iE7r'.
  cp_test (Efst (ap_finv c) in_dom LH); rewrite proj1_MR;
  eqobs_hd iE7r'; cp_test (Esnd (ap_finv c) |x| h in_dom LGb);
  rewrite proj1_MR; eqobs_in.
 
  apply inv_bad_app.
  apply check_inv_bad_c_correct with ipr7H. vm_compute; trivial.
  red; intros; rewrite deno_cond_elim.
  match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Heq end.
  rewrite deno_assign_elim; unfold bad2_K.
  apply Uplus_le_compat.
  unfold charfun, restr, fone, EP; simpl; unfold O.eval_op; simpl;
  mem_upd_simpl;
  trivial.
  apply Nmult_le_compat; trivial.
  refine (minus_le_compat_l _ _ _ _).
  rewrite Mem.get_upd_same.
  assert (forall v, (testLGb (m {!LD <-- E.eval_expr ((Ydef | c) |::| LD) m!})) v =
                    (testLGb m) v).
   intros; unfold testLGb, EP; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl; trivial.
  rewrite (filter_morph _ _ H); clear H.
  simpl; unfold O.eval_op; simpl;
   mem_upd_simpl.
  match goal with |- context [(if ?x then _ else _)] => destruct x; trivial end.
  simpl; apply le_S; trivial.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   transitivity 
    (mu (sum_support (T.default k BS_n) (E.eval_support {0,1}^n m))
        (fcte _ (bad2_K m))); [apply mu_monotonic; intros v1| apply mu_cte_le].
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   transitivity 
     (mu
       (sum_support (T.default k BS_k1)
          (E.eval_support {0,1}^k1 (m {!rGn <-- v1!})))
        (fcte _ (bad2_K m))); [apply mu_monotonic; intros v2| apply mu_cte_le].
   rewrite deno_cons_elim,Mlet_simpl,deno_assign_elim, deno_assign_elim;
    unfold fcte, bad2_K, fplus, Fmult.
   apply Uplus_le_compat.
   unfold charfun, restr, EP; simpl; unfold O.eval_op; simpl;
   mem_upd_simpl;
   trivial.
   apply Nmult_le_compat; trivial.
   refine (minus_le_compat_l _ _ _ _).
   simpl; unfold O.eval_op; simpl;
   mem_upd_simpl.
   match goal with |- length (filter ?f1 _) <= length (filter ?f2 _) => 
     assert (forall a, f2 a = f1 a) end.
     intros; unfold testLGb, EP; simpl; unfold O.eval_op; simpl.
     mem_upd_simpl.
     unfold O.assoc at 2; simpl.
     match goal with |- context [orb ?x _] => case_eq x; intros Heq1;
       [change (is_true x) in Heq1 | trivial ] end.
     simpl.
     rewrite is_true_Ti_eqb in Heq1; rewrite Heq1.
     generalize Heq; clear Heq; simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq.
     rewrite andb_false_r, andb_false_r; trivial.
     rewrite (filter_morph _ _ H); simpl.
     match goal with |- context [(if ?x then _ else _)] => destruct x; trivial end.
     simpl; apply le_S; trivial.
  Qed. 

  Definition ipr7 :=
   let prG := add_prbad ipr7H G inv_bad7r_G in
   let prD := add_prbad prG Dec inv_bad7r_Dec in
   let prGA := add_prbad_comp prD GAdv in
   let prA := 
     add_prbad_adv prGA (A_wf_E H_body0 G_body2r_bad2' Dec_body7r GAdv_body1) in
     add_prbad_adv prA (A'_wf_E H_body0 G_body2r_bad2' Dec_body7r GAdv_body1).

 End PR_7_bad2.

 Definition test_exists_aux := 
  E.Eexists tc
  (let c := Esnd (tc) in
   let s := Efst (ap_finv c) in
   let t := Esnd (ap_finv c) in
   let h := LH [{s}] in
   let r := t |x| h in
   let g := (rGn_aux | rGk1_aux) in
   let m := s |x2| g in
   E.Eop O.Oand {E.Eop O.Oand {r =?= Efst aux, s in_dom LH}, Esnd m =?= zero_k1})
  LD.

 Definition sample_while_bad2 := 
  [  
   while !(LGb_tl =?= Nil _) do 
    [
      If !(LGb_tl =?= Nil _) _then [    
        aux <- Ehd LGb_tl;
        If Efst (Esnd aux) _then [
         rGn_aux <$- {0,1}^n;
         rGk1_aux <$- {0,1}^k1;
         If test_exists_aux _then [bad2 <- true];
         aux <- (Efst aux | (true | (rGn_aux | rGk1_aux)))
      ];
      LGb_hd <- LGb_hd |++| aux |::| Nil _;
      LGb_tl <- Etl LGb_tl
      ]
    ] 
  ].

 Definition sample_true_bad2 :=
  [ LGb_hd <- Nil _; LGb_tl <- LGb ] ++ sample_while_bad2.

 Definition Bad1_hd := 
   E.Eexists tc
  (let c := Esnd (tc) in
   let s := Efst (ap_finv c) in
   let t := Esnd (ap_finv c) in
   let h := LH [{s}] in
   let r := t |x| h in
   let g := Esnd (LGb_hd [{r}]) in
   let m := s |x2| g in
   E.Eop O.Oand
     {E.Eop O.Oand
        {E.Eop O.Oand {s in_dom LH, r in_dom LGb_hd}, Efst (LGb_hd [{r}])},
     Esnd m =?= zero_k1}) LD.

 Lemma SLGb_Bad1_bad2 : 
  equiv
  (kreq_mem {{LD,LH,bad2,LGb}})
  E7r SLGb 
  E7r (sample_true_bad2 ++ [LGb <- LGb_hd])
  (req_mem_rel {{LD,LH,LGb}}
   (EP1 (E.Eop O.Oor {bad2, Bad1}) |-> EP2 bad2)).
 Proof.
  unfold SLGb, sample_true_bad2, sample_while_bad2.
  apply equiv_app with
   (req_mem_rel {{LGb_tl,LD,LH,LGb_hd}} (EP1 (bad2 || Bad1_hd) |-> EP2 bad2)).
  assert (depend_only_rel (EP1 (bad2 || Bad1_hd) |-> EP2 bad2)
           (Vset.union (fv_expr (bad2 || Bad1_hd)) Vset.empty)
           (Vset.union Vset.empty (fv_expr bad2))) by auto.
  assert (decMR (EP1 (bad2 || Bad1_hd) |-> EP2 bad2)) by auto.
 set (i:= empty_inv_info H (refl_equal true) X E7r E7r).
 ep.
 match goal with |- equiv _ _ [?i1;?i2;?i3] _ [?i4;?i5;?i6] ?Q => 
   change [i1; i2; i3] with ( [i1; i2] ++ [i3] );
   change [i4; i5; i6] with ( [i4; i5] ++ [i6] );
   apply equiv_app with Q end.
 eqobsrel_tail; simpl; unfold O.eval_op; simpl.
 intros k2 m1 m2 H2 H1; rewrite is_true_orb in H1; destruct H1.
 rewrite <- (H2 _ bad2); trivial.
 contradict H0; rewrite is_true_existsb; intros (x, (_, H3)).
 repeat rewrite andb_false_r in H3; discriminate.
 unfold sample_while.
 eapply equiv_weaken; [ | apply equiv_while].
  intros k2 m1 m2 (H1, H2); trivial.
  intros k2 m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
  rewrite (H1 _ LGb_tl); trivial.
 swap; ep.
 rewrite proj1_MR; cp_test (Efst (Esnd (Ehd LGb_tl))).
 deadcode.
 rewrite req_mem_rel_assoc; match goal with 
  |- equiv (req_mem_rel ?I ?P) _ [?i1;?i2;?i3;?i4;?i5] _ [?i6;?i7;?i8;?i9;?i10;?i11] ?Q => 
    change [i1; i2; i3; i4; i5] with ([i1; i2]++[i3; i4; i5]);
    change [i6; i7; i8; i9; i10; i11] with ([i6; i7]++[i8; i9; i10; i11]);
    apply equiv_app with (req_mem_rel (Vset.add rGn_aux (Vset.add rGk1_aux I)) P) 
 end.
 eqobsrel_tail; unfold EP1,EP2, andR, impR; simpl; unfold O.eval_op; simpl;
   intros k2 m1 m2 W; decompose [and] W; clear W; split; auto.
 intros W; apply H2; clear H2; rewrite is_true_orb in W |- *; destruct W; auto.
 right; rewrite is_true_existsb in H2 |- *; destruct H2 as (x, (Hin, W));
  exists x; split; trivial.
 mem_upd_simpl;
  trivial.
 match goal with |- equiv _ _ _ _ [If ?e _then _;_;_;_] _ => cp_test_r e end;
 eqobsrel_tail; unfold EP1, EP2, andR, impR; simpl; unfold O.eval_op; simpl;
     intros k2 m1 m2 W; decompose [and] W; clear W; trivial.
 intros W; apply H1; clear H1; rewrite is_true_orb in W |- *; destruct W; auto.
 right; rewrite is_true_existsb in H1 |- *; destruct H1 as (x, (Hin, W));
  exists x; split; trivial.
 mem_upd_simpl.
 repeat rewrite is_true_andb in W; decompose [and] W; clear W.
 rewrite existsb_app in H8.
 match type of H8 with is_true (orb ?x _) => 
   generalize H8; clear H8; case_eq x; intros Heq H8 end; trivial.
   generalize H4 H7; rewrite (@assoc_app k2 BS_k0 Tbnk1).
   match goal with |- context [if ?e then _ else _] => replace e with true; trivial end.
   repeat rewrite is_true_andb; repeat split; trivial.
 simpl in H8; rewrite orb_false_r in H8; rewrite is_true_Ti_eqb in *.
 elim H3; rewrite is_true_existsb; exists x; split; trivial.
  rewrite <- (H0 _ LD); trivial.
  mem_upd_simpl.
  rewrite <- (H0 _ LGb_tl), <- (H0 _ LH), H8, H1; trivial.
  rewrite (@assoc_app k2 BS_k0 Tbnk1) in H4; generalize H4.
  match goal with |- context [if ?e then _ else _] => replace e with false; trivial end.
  unfold O.assoc at 1; simpl.
  rewrite H8, Ti_eqb_refl; simpl; intros.
  rewrite <- (H0 _ rGk1_aux),H6, Ti_eqb_refl; trivial.
  eqobsrel_tail; unfold EP1, EP2, andR, impR; simpl; unfold O.eval_op; simpl;
     intros k2 m1 m2 W; decompose [and] W; clear W; trivial.
 intros W; apply H2; clear H2; rewrite is_true_orb in W |- *; destruct W; auto.
 right; rewrite is_true_existsb in H2 |- *; destruct H2 as (x, (Hin, W));
  exists x; split; trivial.
 mem_upd_simpl.
 repeat rewrite is_true_andb in W; decompose [and] W; clear W.
 rewrite existsb_app in H7.
 match type of H7 with is_true (orb ?x _) => 
   generalize H7; clear H7; case_eq x; intros Heq H7 end; trivial.
   generalize H3 H6; rewrite (@assoc_app k2 BS_k0 Tbnk1).
   match goal with |- context [if ?e then _ else _] => replace e with true; trivial end.
   repeat rewrite is_true_andb; repeat split; trivial.
 simpl in H7; rewrite orb_false_r in H7; rewrite is_true_Ti_eqb in *.
 elim H1; generalize H6; rewrite (@assoc_app k2 BS_k0 Tbnk1).
 match goal with |- context [if ?e then _ else _] => replace e with false; trivial end.
 unfold O.assoc at 1; simpl.
 rewrite H7, Ti_eqb_refl; simpl; trivial.
 assert (depend_only_rel (EP1 (bad2 || Bad1) |-> EP2 bad2)
           (Vset.union (fv_expr (bad2 || Bad1)) Vset.empty)
           (Vset.union Vset.empty (fv_expr bad2))) by auto.
 assert (decMR (EP1 (bad2 || Bad1) |-> EP2 bad2)) by auto.
 set (i:= empty_inv_info H (refl_equal true) X E7r E7r).
 deadcode i. eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
 intros k2 m1 m2 (_, HH).
 intros; apply HH.
  rewrite is_true_orb, is_true_existsb in H0 |- *.
  destruct H0; auto.
  right; destruct H0 as (x, (Hin, H0)); exists x; split; trivial.
  mem_upd_simpl; trivial.
 Qed. 

Section bad2_SLGb.

 Variable k : nat.

 Definition testR_aux (m : Mem.t k)
  (v : T.interp k (T.Pair T.Bool BS_k)) :=
  EP k
  (let c := Esnd (tc) in
   let s := Efst (ap_finv c) in
   let t := Esnd (ap_finv c) in
   let h := LH [{s}] in
   let r := t |x| h in
   let g := (rGn_aux | rGk1_aux) in
   let m0 := s |x2| g in 
      (r =?= Efst aux) && (s in_dom LH))
  (m {!tc <-- v!}).

 Definition testLGb_tl (m : Mem.t k)
  (v : T.interp k (T.Pair T.Bool BS_k)) := 
  EP k
  (let c := Esnd (tc) in
   let s := Efst (ap_finv c) in
   let t := Esnd (ap_finv c) in
   let h := LH [{s}] in
   let r := t |x| h in
   let g := Esnd (LGb_tl [{r}]) in
   let m0 := s |x2| g in
   (s in_dom LH) && (r in_dom (LGb_tl)) && Efst ((LGb_tl) [{r}]))
  (m {!tc <-- v!}).

 Definition bad2_K_tl (mn' : Mem.t k) :=
  ((charfun (EP k bad2) mn' +
    ((length (filter (testLGb_tl mn') (mn' LD))))/2^ k1 k) + 
  [1-] (charfun (fun mn':Mem.t k => no_double (mn' LGb_tl)) mn'))%U.
   
 Definition dep_bad2_K_tl := {{bad2,LGb_tl,LH,LD}}.

 Lemma dep_bad2_K_tl_correct : depend_only_f bad2_K_tl dep_bad2_K_tl.
 Proof.
  intros m1 m2 H.
  unfold bad2_K_tl, testLGb_tl, charfun, restr, EP; simpl; unfold O.eval_op; simpl.
  rewrite (H _ bad2), (H _ LGb_tl); trivial. 
  apply Uplus_eq_compat; trivial.
  apply Uplus_eq_compat; trivial.
  apply Nmult_eq_compat_left; trivial.
  apply f_equal. 
  rewrite (H _ LD); trivial.
  apply filter_morph; intros.
  mem_upd_simpl.
  rewrite (H _ LGb_tl); trivial; try rewrite (H _ LH); trivial.
 Qed. 

 Lemma inv_bad_K_tl : inv_bad E7r bad2_K_tl sample_while_bad2.
 Proof.
  unfold sample_while_bad2.
  apply inv_bad_while.
  apply EqObs_inv_bad with (1 := dep_bad2_K_tl_correct)
   (c :=[
        If !(LGb_tl =?= E.Cnil Tk0bnk1) _then [
           aux <- Ehd LGb_tl;
           If Efst (Esnd (aux)) _then [
              rGk1_aux <$- {0,1}^k1;
              If test_exists_aux  _then [bad2 <- true]
           ];
           LGb_tl <- Etl LGb_tl
        ]
        ]) (I:={{LD,LGb_tl,LH,bad2}}).
  ep; deadcode; eqobs_in.
 intros m.
 unfold bad2_K_tl at 2.
 unfold charfun, restr, fone.
 match goal with |- ( _ <= ((if ?x then _ else _)+ _ + [1-] (if ?y then _ else _))%U)%tord => 
  case_eq x; [ | case_eq y]; repeat Usimpl; trivial end.
 intros HDD; change (is_true (no_double (m LGb_tl))) in HDD. 
 intros Heq1.
 rewrite deno_cond_elim. 
 match goal with |- context [if ?e then _ else _] => 
  case_eq e; intros Hcons;
  [change (is_true e) in Hcons | ] end.
 rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim, deno_cons_elim, Mlet_simpl, deno_cond_elim.
 match goal with |- context [ if E.eval_expr _ ?m then _ else _ ] => set (m1 := m) end.
 match goal with |- context [if ?e then _ else _] => 
  case_eq e; intros Heq0;
  [change (is_true e) in Heq0 | ] end.
 rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
 transitivity
    (mu
      (sum_support (T.default k BS_k1) (E.eval_support {0,1}^k1 m1))
      (fplus
         (fun v2 => charfun (EP k test_exists_aux) (m1{!rGk1_aux<--v2!}))
         (fcte _ 
           ((
               length 
                 (filter (testLGb_tl (m1{!LGb_tl <-- E.eval_expr (Etl LGb_tl) m1!}))
                      (m1 LD)))/2^k1 k))%U)).
  apply mu_monotonic; intros v2; unfold fplus, fcte.
  rewrite deno_cond_elim.
  match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Heq2 end.
  rewrite deno_assign_elim, deno_assign_elim.
  unfold bad2_K_tl.
  unfold charfun at 2; unfold restr.
  match goal with |- context [if ?e then _ else _] =>
   replace e with true; [repeat Usimpl | ] end.
    Focus 2.
    generalize Hcons; unfold m1; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
    destruct (m LGb_tl).
    rewrite Ti_eqb_refl; intros; discriminate.
    change (is_true (no_double (i::i0))) in HDD; simpl in HDD.
    rewrite is_true_andb in HDD; destruct HDD; simpl; symmetry; trivial.
   unfold fone; repeat Usimpl; trivial.
  apply Uplus_le_compat; trivial.
  unfold charfun, restr, EP; rewrite Heq2; trivial.
  apply Nmult_le_compat_left; trivial.
  simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
  match goal with |- ?x <= ?y => replace x with y; trivial end.
  apply f_equal;  apply filter_morph; intros a.
  unfold m1, testLGb_tl, EP; simpl; unfold O.eval_op; simpl;
  mem_upd_simpl.
  trivial.
  rewrite deno_nil_elim, deno_assign_elim.
  unfold bad2_K_tl.
  unfold charfun at 2; unfold restr.
  match goal with |- context [if ?e then _ else _] =>
   replace e with true; [repeat Usimpl | ] end.
    Focus 2.
    generalize Hcons; unfold m1; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
    destruct (m LGb_tl).
    rewrite Ti_eqb_refl; intros; discriminate.
    change (is_true (no_double (i::i0))) in HDD; simpl in HDD.
    rewrite is_true_andb in HDD; destruct HDD; simpl; symmetry; trivial.
   unfold fone; repeat Usimpl; trivial.
  apply Uplus_le_compat; trivial.
  generalize Heq1; clear Heq1; unfold m1, charfun, restr, EP; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
  intros Heq1; rewrite Heq1; trivial.
  apply Nmult_le_compat_left; trivial.
  simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
  match goal with |- ?x <= ?y => replace x with y; trivial end.
  apply f_equal;  apply filter_morph; intros a.
  unfold m1, testLGb_tl, EP; simpl; unfold O.eval_op; simpl;
  mem_upd_simpl;
  trivial.
  transitivity 
    ((length (filter (testR_aux m1) (m1 LD)) + 
 (
              length
                (filter
                   (testLGb_tl
                      (m1 {!LGb_tl <-- E.eval_expr (Etl LGb_tl) m1!}))
                   (m1 LD)))
     )/2^k1 k)%U.
  rewrite mu_le_plus, plus_Nmult_distr, mu_cte_le; apply Uplus_le_compat; trivial.
  set (FR := filter (testR_aux m1) (m1 LD)).
  set (def:= T.default k (T.Pair T.Bool BS_k)).
  transitivity 
    (mu (sum_support (T.default k BS_k1) (E.eval_support {0,1}^k1 m))
         (sigma_fun 
               (fun i v => charfun (T.i_eqb k BS_k1 v) 
                               (snd (fst (finv (snd (nth i FR def))))))
               (length FR))).
   apply mu_monotonic; intro v; unfold fplus,sigma_fun.
   unfold charfun at 1; unfold restr.
   match goal with |- context [if ?x then _ else _] =>
     case_eq x; intros Heq2; [change (is_true x) in Heq2 | trivial] end.
   set (ff:= (fun k2 : nat =>
       charfun (T.i_eqb k BS_k1 v)
         (snd (fst (finv (k:=k) (snd (nth k2 FR def))))))).
   assert (exists i, i < (length FR) /\ 
                        (T.i_eqb k BS_k1 v 
                            (snd (fst (finv (k:=k) (snd (nth i FR def))))))).
   apply nth_existsb with (f :=
     fun w =>  T.i_eqb k BS_k1 v (snd (fst (finv (k:=k) (snd w))))).
   generalize Heq2; unfold FR, test_exists_aux; clear.
   unfold EP, m1; simpl; unfold O.eval_op; simpl;
   mem_upd_simpl.
   generalize (m LD); intros mLD; repeat rewrite is_true_existsb.
   intros (x, (H1, H2)); generalize H2; clear H2;
    mem_upd_simpl;
    repeat rewrite is_true_andb; intros ((H2, H3), H4).
    exists x; split.
    rewrite filter_In; split; trivial.
    unfold testR_aux, EP; simpl; unfold O.eval_op; simpl.
    mem_upd_simpl.
    rewrite H2; trivial.
    rewrite is_true_Ti_eqb in H4; apply BVxor_eq in H4.
    rewrite <- H4; apply Ti_eqb_refl.
   destruct H as (i, (H1, H2)).
   apply Ole_trans with (2:= sigma_le ff H1).
   unfold ff, charfun, restr, EP; rewrite H2; trivial.
   rewrite mu_sigma_le, Nmult_sigma; apply sigma_le_compat.
   intros k2 Hlt; apply Oeq_le.
   apply Pr_bs_support with
    (v:= (snd (fst (finv (k:=k) (snd (nth k2 FR def))))))
    (f := fun v1 v2 => charfun (T.i_eqb k BS_k1 v2) v1).
   intros x Hd; unfold charfun,restr.
   rewrite <- (is_true_Ti_eqb k BS_k1), not_is_true_false in Hd.
   rewrite Hd; trivial.
   unfold charfun,restr; rewrite Ti_eqb_refl; trivial.

  apply Nmult_le_compat; trivial.
  unfold m1;
    mem_upd_simpl.
  generalize (m LD).
  induction i; simpl; trivial.
  case_eq (testLGb_tl m a); intros.
  match goal with |- context [if ?e then _ else _] =>
    case_eq e; intros HH1; [change (is_true e) in HH1 | ] end.
  match goal with |- context [if ?e then _ else _] =>
    replace e with false end.
  simpl; apply le_n_S; trivial.
  change (is_true (testLGb_tl m a)) in H.
  generalize Heq0 Hcons H HH1; unfold m1, testLGb_tl, testR_aux, EP; simpl; unfold O.eval_op; simpl;
    mem_upd_simpl.
  destruct (m LGb_tl); simpl.
  rewrite Ti_eqb_refl; intros; discriminate.
  simpl; repeat rewrite is_true_andb in *.
  intros WW _ H1 H2; decompose [and] H2; decompose [and] H1; clear H2 H1.
  rewrite H0 in *. clear H7.
  rewrite is_true_Ti_eqb in H0; rewrite H0 in *.
  symmetry; rewrite <- not_is_true_false.
  repeat rewrite is_true_andb; intros H7; decompose [and] H7; clear H7.
  generalize HDD; simpl; rewrite H8; intros; discriminate.
  match goal with |- context [if ?e then _ else _] =>
    case_eq e; intros end.
  simpl; rewrite <- plus_n_Sm; apply le_n_S; trivial.
  simpl; apply le_S; trivial.
  match goal with |- context [if ?e then _ else _] =>
    replace e with false end.
  match goal with |- context [if ?e then _ else _] =>
    replace e with false end.
  trivial.
  generalize Hcons Heq0 H; unfold m1, testLGb_tl, EP; simpl; unfold O.eval_op; simpl;
    mem_upd_simpl.
  destruct (m LGb_tl); simpl.
  intros; discriminate.
  clear Hcons Heq0 H; intros _ Heq0 H; symmetry; rewrite <- not_is_true_false in H |- *.
  repeat rewrite is_true_andb; intros H1; decompose [and] H1; elim H; clear H H1.
  rewrite H3; unfold O.assoc at 3; simpl.
  match goal with |- context [orb ?x _] => case_eq x; intros end.
  rewrite Heq0; trivial.
  simpl; rewrite H4; trivial.
  generalize Hcons Heq0 H; unfold m1, testLGb_tl, testR_aux, EP; simpl; unfold O.eval_op; simpl;
    mem_upd_simpl.
  destruct (m LGb_tl); simpl.
  intros; discriminate.
  clear Hcons Heq0 H; intros _ Heq0 H; symmetry; rewrite <- not_is_true_false in H |- *.
  repeat rewrite is_true_andb; intros H1; decompose [and] H1; elim H; clear H H1.
  rewrite H2; unfold O.assoc at 3; simpl.
  rewrite H0; trivial.
  rewrite deno_nil_elim; rewrite deno_assign_elim.
  generalize Heq1 Hcons; unfold bad2_K_tl, m1, charfun,restr, EP; simpl; unfold O.eval_op; simpl;
    mem_upd_simpl.
  clear Heq1; intros Heq1; rewrite Heq1; intros; repeat Usimpl.
  match goal with |- context [if ?e then _ else _] => replace e with true end.
   2:destruct (m LGb_tl); simpl.
   2:rewrite Ti_eqb_refl in Hcons0; discriminate.
   2:change (is_true (no_double (i::i0))) in HDD.
   2:simpl in HDD; rewrite is_true_andb in HDD; destruct HDD; auto.
  unfold fone; repeat Usimpl; apply Nmult_le_compat_left; trivial.
  generalize (m LD).
  induction i; simpl; trivial.
  case_eq (testLGb_tl m a); intros Heq2; [change (is_true (testLGb_tl m a)) in Heq2 | ].
  match goal with |- context [if ?e then _ else _] =>
    destruct e; simpl; [apply le_n_S | apply le_S]; trivial end.
  match goal with |- context [if ?e then _ else _] => replace e with false; trivial end.
  change (is_true (no_double (m LGb_tl))) in HDD.
  symmetry; generalize Heq2 Hcons HDD Heq0; repeat rewrite <- not_is_true_false;
    unfold m1, testLGb_tl,EP; simpl; unfold O.eval_op; simpl;
    mem_upd_simpl.
  destruct (m LGb_tl); intros.
  rewrite Ti_eqb_refl in H0; elim H0; trivial.
  simpl; repeat rewrite is_true_andb; clear H0; intros H0; decompose [and] H0;
   apply H; clear H H0.
  rewrite H5; clear H5.
  unfold O.assoc at 2; simpl.
  rewrite H6; match goal with |- context [orb ?x _] => case_eq x; intros Heq3;
    [change (is_true x) in Heq3 | trivial] end.
  rewrite is_true_Ti_eqb in Heq3; rewrite Heq3 in *.
  simpl in H1; rewrite H6 in H1; discriminate.
  rewrite deno_nil_elim; unfold bad2_K_tl, charfun, restr, fone.
  rewrite Heq1, HDD; repeat Usimpl; trivial.
 Qed. 

End bad2_SLGb.

Lemma PR_7_bad2_Bad1 : forall k (m:Mem.t k), 
 (Pr E7r (G2b ++ SLGb) (m{!bad2 <-- false!}) (EP k (bad2 || Bad1)) <= 
 qD_poly k/2^k1 k)%U%tord.
Proof.
 unfold Pr; intros.
 rewrite deno_app_elim.
 transitivity
   (mu (([[G2b]]) E7r' (m {!bad2 <-- false!}))
      (@bad2_K k)).
 apply equiv_deno_le with Meq (Meq /-\ inv_qD_LGb); trivial.
 union_mod iE7rE7r'. trivial.
 eqobs_tl iE7rE7r'; unfold inv_qD_LGb, inv_qD; eqobsrel_tail; simpl; unfold O.eval_op; simpl.
  intros k2 m1 m2 Heq; split.
  reflexivity.
  red; mem_upd_simpl; trivial.

 unfold inv_qD, Meq; intros m1 m2 (Heq, (HqD, HDD)); subst.
 clear m; rename m2 into m.
 transitivity (mu ([[sample_true_bad2 ++[LGb <- LGb_hd] ]] E7r m) 
   (charfun (EP k bad2))).
 apply equiv_deno_le with (1:= SLGb_Bad1_bad2).
 intros m1 m2 (H1, H2).
 unfold impR, EP1,EP2 in H2; unfold charfun, restr, EP.
 match goal with |- ((if ?x then _ else _)<= _)%tord => destruct x; trivial end.
 rewrite H2; trivial.

 split; trivial.
 rewrite deno_app_elim.
 transitivity  (mu (([[sample_true_bad2]]) E7r m) (@bad2_K_tl k)).
  apply mu_monotonic; intros m1.
  rewrite deno_assign_elim.
  unfold bad2_K_tl, charfun, EP, restr, fone; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  destruct (m1 bad2); trivial.
  repeat Usimpl; trivial.
  unfold sample_true_bad2.
  rewrite deno_app_elim, deno_cons_elim, Mlet_simpl, deno_assign_elim, deno_assign_elim.
  rewrite inv_bad_K_tl.
  generalize HqD, HDD; unfold No_double_LGb,inv_qD,EP2,bad2_K, bad2_K_tl, 
    charfun,restr, EP, fone; simpl; unfold O.eval_op; simpl;
  mem_upd_simpl; intros.
  rewrite HDD0; repeat Usimpl.
  apply Nmult_le_compat; trivial.
  simpl; match goal with |- (?x <= ?y - ?z) => assert (x + z <= y); [ | omega'] end.
  rewrite is_true_andb, is_true_leb in HqD0; destruct HqD0 as (W, _).
  apply le_trans with (2:= W).
  generalize (m LD).
   induction i; simpl; intros; trivial.
   match goal with |- context [(if ?b then _ else _)] => case_eq b; intros end.
   match goal with |- context [(if ?b then _ else _)] => replace b with false end.
   simpl; apply le_n_S; trivial.
   symmetry; rewrite <- not_is_true_false.
   generalize H; clear H; unfold testLGb, testLGb_tl, EP; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   match goal with |- ?x = true -> ?y => change ((is_true x) -> y) end.
   repeat rewrite is_true_andb; rewrite is_true_negb; intuition.
   match goal with |- context [(if ?b then _ else _)] => case_eq b; intros; simpl end.
   rewrite <- plus_n_Sm; apply le_n_S; trivial.
   apply le_S; trivial.

 change G2b with 
   ([bad <- false;Ydef <- false; LGb <- E.Cnil Tk0bnk1;
      LH <- E.Cnil _; LD <- E.Cnil _] ++ 
    ([Dc <- O; Gc <- O;R' <$- {0,1}^k0] ++ (SGR' ++ [S' <- (GR'n | GR'k1)] ++ tail2))).
 rewrite deno_app_elim.
 transitivity 
   (mu (([[ [bad <- false;Ydef <- false; LGb <- E.Cnil Tk0bnk1;
             LH <- E.Cnil _; LD <- E.Cnil _] ]] E7r' (m {!bad2 <-- false!})))
       (@bad2_K k)).
 apply mu_monotonic; intros m1.
 apply check_inv_bad_c_correct with (ipr7 k). vm_compute; trivial.
 repeat rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
 rewrite deno_nil_elim; unfold bad2_K, charfun, restr, EP; simpl; unfold O.eval_op; simpl;
  mem_upd_simpl.
 simpl; rewrite <- minus_n_O; Usimpl; trivial.
 Qed. 

 Lemma PR_7r_bad : forall k m,
  (Pr E5b G2b (m{! bad1 <-- false !}) (EP k bad) <= 
   Pr E7r ((bad2 <- false) :: G2b) m (EP k bad) + qD_poly k/2^k1 k)%U%tord.
 Proof.
  intros k m; eapply Ole_trans; [apply PR_5b_bad_7 | ].
  apply Uplus_le_compat.
  apply Oeq_le.
  rewrite set_bad; apply EqObs_Pr with {{Y',g_a}}.
  eqobs_hd_n 1.
  apply EqObs_trans with E7r (G2b ++ SLGb).
  eapply equiv_strengthen; [ | eapply equiv_weaken; [ | apply equiv_E7_E7r ] ].
   intros k2 m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
   intros k2 m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  eqobs_hd iE7r. deadcode.
  apply equiv_strengthen with (kreq_mem (fv_expr bad)).
   intros k2 m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
   apply EqObs_lossless_Modify with {{LGb_hd,rGk1_aux,rGn_aux,aux,LGb_tl}} Vset.empty.
  2:apply lossless_nil.
  apply lossless_cons; [ apply lossless_assign | ].
  red; intros.
  rewrite deno_while_unfold_elim.
  assert (forall n m1, n = E.eval_expr (Elen LGb_tl) m1 ->
     ((Mu (Mem.t k2) @
      unroll_while_sem E7r (!(LGb_tl =?= Nil _))
        [
        aux <- Ehd LGb_tl;
        LGb_tl <- Etl LGb_tl;
        If Efst (Esnd aux)
        _then [
              rGn_aux <$- {0,1}^n;
              rGk1_aux <$- {0,1}^k1;
              aux <- (Efst aux | (true | (rGn_aux | rGk1_aux)))
              ];
        LGb_hd <- LGb_hd |++| aux |::| Nil _
        ] m1) <_> (fun _ : Mem.t k2 => 1%U)) n == 1%U)%tord.
 Opaque deno app.
   induction n0; simpl; unfold O.eval_op; simpl.
   intros; rewrite (deno_cond_elim E7r (!(LGb_tl =?= Nil _)) nil nil m1).
   unfold negP; simpl; unfold O.eval_op; simpl.
   case_eq (T.i_eqb k2 T_assoc_b (m1 LGb_tl) (@nil (Ut.interp k2 Bitstring_k0 *
                 (bool *
                  (Ut.interp k2 Bitstring_n * Ut.interp k2 Bitstring_k1))))); simpl; intros Heq.
   rewrite (deno_nil_elim E7r m1); rewrite Heq; trivial.
   rewrite <- not_is_true_false, is_true_Ti_eqb in Heq.
   destruct (m1 LGb_tl); [ elim Heq; trivial | discriminate].
   intros; rewrite (fun c1 c2 => deno_cond_elim E7r (!(LGb_tl =?= Nil _)) c1 c2 m1).
   simpl; unfold O.eval_op; simpl.
   case_eq (T.i_eqb k2 T_assoc_b (m1 LGb_tl) (@nil (Ut.interp k2 Bitstring_k0 *
                 (bool *
                  (Ut.interp k2 Bitstring_n * Ut.interp k2 Bitstring_k1))))); simpl; intros Heq.
   destruct (m1 LGb_tl); discriminate.
   change (mu ([[ sample_body LGb_hd LGb_tl ++ 
                  unroll_while (!(LGb_tl =?= Nil _)) (sample_body LGb_hd LGb_tl) n0]] E7r m1)
             (fun x : Mem.t k2 =>
             (mu
       (if negP
             (fun m2 : Mem.t k2 =>
              negb (T.i_eqb k2 T_assoc_b (m2 LGb_tl) nil))
             x
        then Munit x
        else distr0 (Mem.t k2))) (fun _ : Mem.t k2 => 1%U)) == 1%U).
   rewrite deno_app_elim.
   transitivity (mu ([[sample_body LGb_hd LGb_tl]] E7r m1) (fun _ => 1%U)).
   apply equiv_deno with (Meq /-\ EP1 (Datatypes.S n0 =?= Elen LGb_tl)) 
       (Meq /-\ EP1 (n0 =?= Elen LGb_tl)).
   union_mod. rewrite proj1_MR; trivial.
   eqobsrel_tail; unfold Meq, EP1, implMR, andR; simpl; unfold O.eval_op; simpl; intros k3 m3 m4 (H1, H2); subst.
   destruct (m4 LGb_tl); [discriminate | ].
   simpl in H2 |- *; rewrite is_true_Ti_eqb in H2. 
   inversion H2; split; intros; apply Ti_eqb_refl.
   unfold Meq, EP1; intros m2 m3 (H1, H2); subst.
   refine (IHn0 m3 _).
   rewrite <- (expr_eval_eq m3 n0) in H2; trivial.
   split; [trivial | unfold EP1; rewrite <- (expr_eval_eq m1 (Datatypes.S n0)); trivial].
   assert (lossless E7r (sample_body LGb_hd LGb_tl)).
    apply is_lossless_correct with (refl1_info iE7r).
    vm_compute; trivial.
   apply H0.
   split; trivial.
   match goal with |- (1%U <= lub (c:=U) ?F)%tord => 
   transitivity (F (E.eval_expr (Elen LGb_tl) m0)) end.
   rewrite H; trivial.
   apply le_lub.
   apply modify_correct with (refl1_info iE7r) Vset.empty.
   vm_compute; trivial.
   apply Modify_nil.
   vm_compute; trivial.
   vm_compute; trivial.
  apply Ole_trans with  (Pr E7r (G2b++SLGb) (m {!bad2 <-- false!}) (EP k (E.Eop O.Oor {bad2, Bad1}))).
  apply Oeq_le; apply EqObs_Pr with {{Y',bad2,g_a}}.
  eapply equiv_weaken; [ | apply equiv_E7_E7r].
     intros k2 m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  apply PR_7_bad2_Bad1.
 Qed.


 Definition Dec_body9 :=
  [
   If E.Eop O.Oor {testD, qG <! (Elen LG)} then [mn <- (false | one_n)]
   else 
    [
     LD <- (Ydef | c) |::| LD;
     Dc <- 1 +! Dc;
     st <- ap_finv c;
     s <- Efst (st);
     t <- Esnd (st);
     If s in_dom LH then 
      [
       h <c- H with {s};
       r <- t |x| h;
       If r in_dom LG then 
        [
         g <- LG [{r}];
         m <- s |x2| g;
         If Esnd m =?= zero_k1 then [mn <- (true | Efst m)
        ]
       else [ mn <- (false | one_n) ]
     ] 
    else 
     [
      If R' =?= r _then [bad <- true];
      mn <- (false | one_n)
     ]
    ] 
   else 
    [
     h <c- H with {s};
     mn <- (false | one_n)
    ]
   ]
  ].

 Definition E9 := mkEnv H_body0 G_body2 Dec_body9.

 Definition inv7 : mem_rel := 
  fun k m1 m2 => (forall v, 
   andb (@List.existsb (T.interp k BS_k0 * T.interp k Tbnk1)%type (fun p => T.i_eqb k BS_k0 v (fst p)) (m1 LGb))
   (negb (fst (@O.assoc (T.interp k BS_k0) (T.interp k Tbnk1) (T.i_eqb k BS_k0 v) (T.default k Tbnk1) (m1 LGb)))) = 
   (@List.existsb (T.interp k BS_k0 * T.interp k (T.Pair BS_n BS_k1))%type (fun p => T.i_eqb k BS_k0 v (fst p))
    (m2 LG)) /\
   (@List.existsb (T.interp k BS_k0 * T.interp k (T.Pair BS_n BS_k1))%type (fun p => T.i_eqb k BS_k0 v (fst p))
    (m2 LG) ->
      snd (@O.assoc (T.interp k BS_k0) (T.interp k Tbnk1) (T.i_eqb k BS_k0 v) (T.default k Tbnk1) 
       (m1 LGb)) =
      (@O.assoc (T.interp k BS_k0) (T.interp k (T.Pair BS_n BS_k1)) (T.i_eqb k BS_k0 v) (T.default k (T.Pair BS_n BS_k1))
       (m2 LG)))) /\
  E.eval_expr (Elen LGb) m1 <= E.eval_expr ((Elen LG) +! Dc) m2.

 Lemma dep_inv7 : depend_only_rel inv7 {{LGb}} {{Dc,LG}}.
 Proof.
  unfold inv7; red; intros; simpl; unfold O.eval_op; simpl.
  rewrite <- (H _ LGb), <- (H0 _ LG), <- (H0 _ Dc); trivial.
 Qed.

 Lemma dec_inv7 : decMR inv7.
 Proof.
 red; unfold inv7; intros k m1 m2.
  destruct (le_gt_dec (E.eval_expr (Elen LGb) m1) (E.eval_expr (Elen LG +! Dc) m2)).
  2:right; intros (H1, H2); omega'.
  set (F1 := fun p : T.interp k BS_k0 * T.interp k BS_nk1 =>
       andb (T.i_eqb k  BS_nk1 (snd (O.assoc (T.i_eqb k BS_k0 (fst p)) (T.default k Tbnk1) (m1 LGb)))
       (O.assoc (T.i_eqb k BS_k0 (fst p)) (T.default k BS_nk1)
            (m2 LG)))
       (andb (existsb
           (fun p1 : T.interp k BS_k0 * T.interp k Tbnk1 =>
                T.i_eqb k BS_k0 (fst p) (fst p1)) (m1 LGb))
       (negb
        (fst (O.assoc (T.i_eqb k BS_k0 (fst p)) (T.default k Tbnk1) (m1 LGb)))))).
  set (F2 := fun p : T.interp k BS_k0 * T.interp k Tbnk1 =>
       orb (fst
              (O.assoc (T.i_eqb k BS_k0 (fst p)) (T.default k Tbnk1)
              (m1 LGb))) 
            (existsb
                (fun p1 : T.interp k BS_k0 * T.interp k BS_nk1 =>
                   T.i_eqb k BS_k0 (fst p) (fst p1))
                 (m2 LG))).
  case_eq (andb (List.forallb F1 (m2 LG)) (List.forallb F2 (m1 LGb))).
  left; split; trivial.
  rewrite andb_true_iff, forallb_forall, forallb_forall in H; destruct H; intros v.
  match goal with |- _ = ?x /\ _ => case_eq x; intros Heq end.
  rewrite existsb_exists in Heq; destruct Heq as (p, (H1, H2)).
  apply H in H1; unfold F1 in H1.
  change (is_true (T.i_eqb k BS_k0 v (fst p))) in H2; rewrite is_true_Ti_eqb in H2; subst.
  rewrite andb_true_iff in H1; destruct H1.
  rewrite H2.
  match type of H1 with ?x = true => change (is_true x) in H1 end.
  rewrite is_true_Ti_eqb in H1; rewrite H1; auto.
  split; [ | intro; discriminate].
  match goal with |-  (andb ?x _) = _ => case_eq x; intros Heq1; [ | trivial]end.
  rewrite existsb_exists in Heq1; destruct Heq1 as (p, (H1, H2)).
  match type of H2 with  ?x = true => change (is_true x) in H2 end.
  rewrite is_true_Ti_eqb in H2; subst.
  apply H0 in H1; unfold F2 in H1.
  apply orb_prop in H1; destruct H1.
  rewrite H1; trivial.
  rewrite H1 in Heq; discriminate.
  intros Heq; right; intros (H, _).
  destruct (andb_false_elim _ _ Heq) as [H1 | H1]; clear Heq; rewrite <- not_is_true_false in H1.
  assert (existsb (negP F1) (m2 LG)).
    match goal with |- is_true ?x => case_eq x; intros; trivial end.
  elim H1; rewrite is_true_forallb; intros.
  case_eq (F1 x); intros; trivial.
  rewrite <- H0, is_true_existsb; exists x; split; [ | unfold negP; rewrite H3]; trivial.
  rewrite is_true_existsb in H0; destruct H0 as (x, (Hin, H2)).
  unfold negP, F1 in H2.
  destruct (H (fst x)).
  rewrite H0, negb_andb, is_true_orb, is_true_negb, is_true_Ti_eqb in H2; destruct H2.
  elim H2; apply H3.
  rewrite is_true_existsb; exists x; rewrite Ti_eqb_refl; auto.
  rewrite is_true_negb in H2; elim H2; rewrite is_true_existsb; exists x; rewrite Ti_eqb_refl; auto.
  assert (existsb (negP F2) (m1 LGb)).
    match goal with |- is_true ?x => case_eq x; intros; trivial end.
  elim H1; rewrite is_true_forallb; intros.
  case_eq (F2 x); intros; trivial.
  rewrite <- H0, is_true_existsb; exists x; split; [ | unfold negP; rewrite H3]; trivial.
  rewrite is_true_existsb in H0; destruct H0 as (x, (Hin, H2)).
  unfold negP, F2 in H2.
  destruct (H (fst x)).
  rewrite negb_orb, is_true_andb in H2; destruct H2.
  rewrite H2 in *. rewrite andb_true_r in H0; rewrite <- H0 in *.
  rewrite is_true_negb in H4; apply H4.
  rewrite is_true_existsb; exists x; rewrite Ti_eqb_refl; auto.
 Qed. 

 Definition inv7_bad := 
  (inv7 /-\ (EP1 bad |-> EP2 bad)) /-\ (EP2 ((Elen LG <=! Gc) && (Gc <=! qG))).

 Lemma dep_inv7_bad : depend_only_rel inv7_bad 
  (Vset.union
   (Vset.union {{LGb}}
    ((Vset.union (fv_expr bad) Vset.empty))) Vset.empty)
  (Vset.union
   (Vset.union {{Dc,LG}}
    (Vset.union Vset.empty (fv_expr bad)))
   (fv_expr (E.Eop O.Oand {Elen LG <=! Gc, Gc <=! qG}))).
 Proof.
  unfold inv7_bad; auto using dep_inv7.
 Qed.

 Lemma dec_inv7_bad : decMR inv7_bad.
 Proof.
  unfold inv7_bad; auto using dec_inv7. 
 Qed.

 Definition eE7rE9 := 
  empty_inv_info dep_inv7_bad (refl_equal true) dec_inv7_bad E7r E9.

 Opaque T.interp T.default.

 Lemma GAdv_body_inv7_bad : 
  EqObsInv inv7_bad {{Gc,Radv,R'}}
  E7r GAdv_body1 
  E9 GAdv_body1 
  {{rGadv,Gc}}.
 Proof.
 unfold GAdv_body1, GAdv_body0_gen, GAdv_body0.
 cp_test (qG <=! Gc).
 rewrite proj1_MR; eqobs_in eE7rE9.
 inline eE7rE9 G.
  auto using dec_inv7_bad.
 ep; deadcode eE7rE9.
 cp_test_r eE7rE9 (Radv in_dom LG).
 ep_eq_l eE7rE9 (Radv in_dom LGb) true.
  unfold inv7_bad, inv7, req_mem_rel, andR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
   decompose [and] H; clear H.
  destruct (H2 (m1 Radv)); clear H2.
  rewrite <- (H0 _ Radv) in *; trivial.
  rewrite H1, andb_true_iff in H; destruct H; trivial.
 ep_eq_l eE7rE9 (Efst (LGb [{Radv}])) false.
  unfold inv7_bad, inv7, req_mem_rel, andR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
   decompose [and] H; clear H.
  destruct (H2 (m1 Radv)); clear H2.
  rewrite <- (H0 _ Radv) in *; trivial.
  rewrite H1, andb_true_iff in H; destruct H; rewrite <- is_true_negb_false; trivial.
 repeat rewrite req_mem_rel_assoc.
 apply equiv_cons with
  (req_mem_rel {{Gc,Radv,R'}} (inv7_bad /-\  EP2 (Radv in_dom LG))).
 unfold inv7_bad, inv7; eqobsrel_tail; unfold req_mem_rel, EP1, EP2, notR, andR; simpl; unfold O.eval_op; simpl;
 intros k m1 m2 H; decompose [and] H; clear H.
 repeat split; intros; mem_upd_simpl; simpl; auto with zarith.
 destruct (H2 v); trivial.
 rewrite Mem.get_upd_diff in H; [ | discriminate]; destruct (H2 v); auto.
 apply H6; trivial.
 match goal with |- is_true (andb _ ?x) => change x with (leb (Datatypes.S (m2 Gc)) (qG_poly k)) end.
 rewrite is_true_andb, is_true_leb in *; rewrite is_true_leb; omega'.
 deadcode eE7rE9.
 eapply equiv_strengthen; [ | apply equiv_assign].
  unfold upd_para; intros k m1 m2 (H1, (H2, H3)).
  split.
  match goal with |- kreq_mem _ (m1 {! _ <-- ?x !}) (m2 {! _ <-- ?y!}) => replace x with y end.
  apply req_mem_update; apply req_mem_weaken with (2:= H1); vm_compute; trivial.
  generalize H3 H2; clear H3 H2; unfold inv7_bad, inv7, EP1, EP2, notR, andR; simpl; unfold O.eval_op; simpl.
  intros H3 H2; decompose [and] H2; clear H2.
  rewrite <- (H1 _ Radv) in *; trivial.
  destruct (H (m1 Radv)); clear H.
  rewrite <- (H4 H3); trivial.
  apply dep_inv7_bad with m1 m2; trivial; apply req_mem_upd_disjoint; trivial.

  cp_test_l (Radv in_dom LGb).
  ep_eq_l (Efst (LGb [{Radv}])) true.
   unfold inv7_bad, inv7, req_mem_rel, andR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
   decompose [and] H; clear H.
   destruct (H0 (m1 Radv)); clear H0.
   rewrite <- (H2 _ Radv) in *; trivial.
   rewrite <- H, H1 in H3; simpl in H3.
   rewrite <- is_true_negb, negb_involutive in H3; trivial.
  cp_test (R' =?= Radv).

  repeat rewrite req_mem_rel_assoc.
  unfold inv7_bad, inv7,andR, notR, impR; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  mem_upd_simpl; simpl.
  split; intros; mem_upd_simpl; simpl.
  rewrite <- (H0 _ Radv) in *; trivial.
  split; [split | ].
  intros v1; case_eq (T.i_eqb k BS_k0 v1 (m1 Radv)); intros; simpl.
  change (is_true (T.i_eqb k BS_k0 v1 (m1 Radv))) in H12.
  rewrite is_true_Ti_eqb in H12; subst; simpl.
  rewrite assoc_upd_same, existsb_upd_same; unfold O.assoc; simpl; rewrite Ti_eqb_refl; auto.
  unfold O.assoc at 3; simpl; rewrite H12.
  rewrite <- not_is_true_false, is_true_Ti_eqb in H12.
  rewrite assoc_upd_diff, existsb_upd_diff; trivial.
  apply (H2 v1). 
  change T.interp with Ent.T.interp.
  change Ent.T.i_eqb with T.i_eqb.
  rewrite (length_upd k BS_k0 (T.Pair T.Bool (T.Pair BS_n BS_k1))).
  apply le_trans with (1:=H9); omega'.
  trivial.
  trivial.
  match goal with 
   |- is_true (andb _ ?x) => change x with (leb (Datatypes.S (m2 Gc)) (qG_poly k)) end.
  rewrite is_true_andb, is_true_leb in *; rewrite is_true_leb; omega'.
  repeat rewrite req_mem_rel_assoc.
  unfold inv7_bad, inv7,andR, notR, impR; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  mem_upd_simpl; simpl.
  split; intros; mem_upd_simpl; simpl.
  rewrite <- (H0 _ Radv) in *; trivial.
  split; [split | ].
  intros v1; case_eq (T.i_eqb k BS_k0 v1 (m1 Radv)); intros; simpl.
  change (is_true (T.i_eqb k BS_k0 v1 (m1 Radv))) in H12.
  rewrite is_true_Ti_eqb in H12; subst; simpl.
  rewrite assoc_upd_same, existsb_upd_same; unfold O.assoc; simpl; rewrite Ti_eqb_refl; auto.
  unfold O.assoc at 3; simpl; rewrite H12.
  rewrite <- not_is_true_false, is_true_Ti_eqb in H12.
  rewrite assoc_upd_diff, existsb_upd_diff; trivial.
  apply (H2 v1).
  change Ent.T.interp with T.interp in H4.
  rewrite (length_upd _ _ _ _ _ _ H4).
  apply le_trans with (1:= H9); omega'.
  trivial.
  match goal with |- is_true (andb _ ?x) => change x with (leb (Datatypes.S (m2 Gc)) (qG_poly k)) end.
  rewrite is_true_andb, is_true_leb in *; rewrite is_true_leb; omega'.
  repeat rewrite req_mem_rel_assoc.
  unfold inv7_bad, inv7,andR, notR, impR; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  mem_upd_simpl; simpl.
  split; intros; mem_upd_simpl; simpl.
  rewrite <- (H0 _ Radv) in *; trivial.
  split; [split | ].
  split.
  intros v1; case_eq (T.i_eqb k BS_k0 v1 (m1 Radv)); intros; simpl.
  change (is_true (T.i_eqb k BS_k0 v1 (m1 Radv))) in H11.
  rewrite is_true_Ti_eqb in H11; subst; unfold O.assoc; simpl; rewrite Ti_eqb_refl; auto.
  unfold O.assoc; simpl; rewrite H11.
  apply (H1 v1).
  omega'.
  trivial.
  match goal with |- is_true (andb _ ?x) => change x with (leb (Datatypes.S (m2 Gc)) (qG_poly k)) end.
  rewrite is_true_andb, is_true_leb in *; rewrite is_true_leb.
  match goal with
   |- Datatypes.S ?x <= Datatypes.S ?y <= _ => 
    set (X:=x) in *; set (Y:=y) in *; omega'
  end. 
  rewrite <- (H0 _ Radv) in *; trivial.
  split; [split | ].
  split.
  intros v1; case_eq (T.i_eqb k BS_k0 v1 (m1 Radv)); intros; simpl.
  change (is_true (T.i_eqb k BS_k0 v1 (m1 Radv))) in H11.
  rewrite is_true_Ti_eqb in H11; subst; unfold O.assoc; simpl; rewrite Ti_eqb_refl; auto.
  unfold O.assoc; simpl; rewrite H11.
  apply (H1 v1).
  omega'.
  trivial.
  match goal with |- is_true (andb _ ?x) => change x with (leb (Datatypes.S (m2 Gc)) (qG_poly k)) end.
  rewrite is_true_andb, is_true_leb in *; rewrite is_true_leb; omega'.
 Qed. 

 Definition iE9 := iEiEi H_body0 G_body2 Dec_body9.

 Definition iE7rE9pre :=
  let piH := my_add_refl_info eE7rE9 H in 
  let piGA := 
   my_add_info GAdv {{bad1,bad2}} Vset.empty iE7r iE9 piH GAdv_body_inv7_bad in
   piGA.

 Lemma Dec_body_inv7_bad : 
  EqObsInv inv7_bad (Vset.remove bad (Vset.remove LG ID))
  E7r Dec_body7r 
  E9 Dec_body9
  (Vset.remove bad (Vset.remove LG OD)).
 Proof.
  cp_test (qD <=! Dc).
  rewrite proj1_MR; eqobs_in iE7rE9pre.
  ep_eq_r (qG <! (Elen LG)) false.
    unfold req_mem_rel, inv7_bad, andR, EP1, EP2; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
    decompose [and] H; clear H.
    rewrite is_true_andb in H4; repeat rewrite is_true_leb in H4.
    rewrite <- not_is_true_false, is_true_leb; omega'.
  ep_eq_l ((qD +! qG) <! (Elen LGb)) false.
    unfold req_mem_rel, inv7_bad, inv7, andR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
    decompose [and] H; clear H.
    rewrite is_true_andb in H4; rewrite <- not_is_true_false; repeat rewrite is_true_leb in *; omega'.
  cp_test (E.Eop O.Oand {Ydef =?= true, Y' =?= c}).
  repeat rewrite proj1_MR; eqobs_in iE7rE9pre.

  repeat rewrite proj1_MR.
  ep iE7rE9pre; deadcode iE7rE9pre.
  cp_test (Efst (ap_finv c) in_dom LH); rewrite proj1_MR.
  swap iE7rE9pre.
  eqobs_hd iE7rE9pre.

  cp_test_r (Esnd (ap_finv c) |x| h in_dom LG).
  ep_eq_l eE7rE9 (Esnd (ap_finv c) |x| h in_dom LGb) true.
   generalize (depend_only_fv_expr (Esnd (ap_finv c) |x| h)).
   unfold fv_expr; simpl fv_expr_rec; generalize (Esnd (ap_finv c) |x| h).
   unfold inv7_bad, inv7, req_mem_rel, andR, notR, impR, EP1, EP2; simpl; unfold O.eval_op; simpl;
     intros e Hdep k m1 m2 H; decompose [and] H; clear H.
   rewrite <- (Hdep k m1 m2) in *; [ | apply req_mem_weaken with (2:= H2); vm_compute; trivial].
   destruct (H0 (E.eval_expr e m1)).
   rewrite H1, andb_true_iff in H; destruct H; trivial.
  ep_eq_l eE7rE9 (Efst (LGb [{Esnd (ap_finv c) |x| h}])) false.
   generalize (depend_only_fv_expr (Esnd (ap_finv c) |x| h)).
   unfold fv_expr; simpl fv_expr_rec; generalize (Esnd (ap_finv c) |x| h).
   unfold inv7_bad, inv7, req_mem_rel, andR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl; intros e Hdep k m1 m2 H;
    decompose [and] H; clear H.
   rewrite <- (Hdep k m1 m2) in *; [ | apply req_mem_weaken with (2:= H2); vm_compute; trivial].
   destruct (H0 (E.eval_expr e m1)).
   rewrite H1, andb_true_iff in H; destruct H; rewrite <- is_true_negb_false; trivial.
  match goal with |- equiv ?P _ _ _ _ _ => 
  assert (forall (k : nat) (m1 m2 : Mem.t k), P k m1 m2 ->
     E.eval_expr (Esnd (LGb [{Esnd (ap_finv c) |x| h}])) m1 =
     E.eval_expr (LG [{Esnd (ap_finv c) |x| h}]) m2) end.
   generalize (depend_only_fv_expr (Esnd (ap_finv c) |x| h)).
   unfold fv_expr; simpl fv_expr_rec; generalize (Esnd (ap_finv c) |x| h).
   unfold inv7_bad, inv7, req_mem_rel, andR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl; intros e Hdep k m1 m2 H;
    decompose [and] H; clear H.
   rewrite <- (Hdep k m1 m2) in *; try (apply req_mem_weaken with (2:= H2); vm_compute; trivial).
   destruct (H0 (E.eval_expr e m1)).
   apply H3; trivial.
  cp_test_r (Esnd (Efst (ap_finv c)) |x| Esnd (LG [{Esnd (ap_finv c) |x| h}]) =?= zero_k1).
  ep_eq_l eE7rE9 (Esnd (Efst (ap_finv c)) |x| Esnd (Esnd (LGb [{Esnd (ap_finv c) |x| h}])) =?= zero_k1) true.
    intros k m1 m2 (H1, H2); generalize (H k m1 m2 H1) H2; unfold EP2.
    simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq.
    destruct H1 as ((H1, _), _); rewrite (H1 _ c); trivial.
  rewrite proj1_MR.
  match goal with |- equiv ((req_mem_rel ?I ?P) /-\ _) _ _ _ _ _ =>
   apply equiv_cons with (req_mem_rel (Vset.add mn I) inv7_bad)
  end.
  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold upd_para; intros k m1 m2 H1.
  generalize H1; intros ((H2,H3), _); split.
  match goal with |- kreq_mem _ (m1 {! _ <-- ?x !}) (m2 {! _ <-- ?y!}) => replace x with y end.
  apply req_mem_update; apply req_mem_weaken with (2:= H2); vm_compute; trivial.
  generalize (H k m1 m2 H1).
 Transparent T.interp.
  simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq, (H2 _ c); trivial.
  apply dep_inv7_bad with m1 m2; trivial; apply req_mem_upd_disjoint; trivial.
  clear H.
  unfold inv7_bad, inv7; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  mem_upd_simpl; simpl.
  repeat (split; auto).
  apply le_trans with (1:=H5); auto with arith.
   ep_eq_l eE7rE9 (Esnd (Efst (ap_finv c)) |x| Esnd (Esnd (LGb [{Esnd (ap_finv c) |x| h}])) =?= zero_k1) false.
    unfold notR; intros k m1 m2 (H1, H2); generalize (H k m1 m2 H1) H2; unfold EP2.
    simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq.
    destruct H1 as ((H1, _), _); rewrite (H1 _ c); trivial; intros.
    rewrite <- not_is_true_false; trivial.
  clear H; unfold inv7_bad, inv7; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  mem_upd_simpl; simpl.
  repeat (split; auto).
  apply le_trans with (1:=H6); auto with arith.

  cp_test_l (Esnd (ap_finv c) |x| h in_dom LGb).
  ep_eq_l (Efst (LGb [{Esnd (ap_finv c) |x| h}])) true.
   generalize (depend_only_fv_expr (Esnd (ap_finv c) |x| h)).
   unfold fv_expr; simpl fv_expr_rec; generalize (Esnd (ap_finv c) |x| h).
   unfold inv7_bad, inv7, req_mem_rel, andR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl; intros e Hdep k m1 m2 H;
    decompose [and] H; clear H.
   rewrite <- (Hdep k m1 m2) in *; try (apply req_mem_weaken with (2:= H0); vm_compute; trivial).
   destruct (H2 (E.eval_expr e m1)).
   rewrite not_is_true_false in H3; rewrite H1, H3 in H; simpl in H.
   rewrite <- not_is_true_false, <- is_true_negb, negb_involutive in H; trivial.

  apply equiv_trans_eq_mem_l with trueR
    E7r [
      If R' =?= Esnd (ap_finv c) |x| h then [
        mn <- (false | one_n);
        Dc <- 1 +! Dc
      ] else [
        mn <- (false | one_n);
        Dc <- 1 +! Dc
      ]
    ].
  rewrite proj1_MR; union_mod.  auto. 
  deadcode; eqobs_in.
  apply equiv_trans_eq_mem_r with trueR
    E7r [
      If R' =?= Esnd (ap_finv c) |x| h then [
        bad <- true;
        mn <- (false | one_n);
        Dc <- 1 +! Dc
      ] else [
        mn <- (false | one_n);
        Dc <- 1 +! Dc
      ]
    ].
  rewrite proj1_MR; union_mod.  auto. 
  cp_test ( R' =?= Esnd (ap_finv c) |x| h); rewrite proj1_MR; eqobs_in.
  cp_test ( R' =?= Esnd (ap_finv c) |x| h); repeat rewrite proj1_MR.
  unfold inv7_bad, inv7; eqobsrel_tail; unfold EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  mem_upd_simpl.
  repeat (split; auto).
  apply le_trans with (1:=H5); auto with arith.
  unfold inv7_bad, inv7; eqobsrel_tail; unfold EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  mem_upd_simpl.
  repeat (split; auto).
  apply le_trans with (1:=H5); auto with arith.
  red; red; trivial.
  red; red; trivial.

 Opaque T.interp.
  apply equiv_trans_r with (P2 := Meq) (Q1 := req_mem_rel (Vset.remove bad (Vset.remove LG OD)) inv7_bad)
    (Q2 := kreq_mem (Vset.add Gc OD)) (E2:=E7) (c2:=[
   If R' =?= Esnd (ap_finv c) |x| h _then [bad <- true]; 
   rGn <$- {0,1}^n;
   rGk1 <$- {0,1}^k1;
   mn <- (false | one_n);
   Dc <- 1 +! Dc
   ]).
  auto using dec_inv7_bad. red; red; trivial.
  intros. 
  apply (@depend_only_req_mem_rel  (Vset.remove bad (Vset.remove LG OD)) _ _ _ dep_inv7_bad) with x y; trivial.
  apply req_mem_weaken with (2:= H0); vm_compute; trivial.
  unfold inv7_bad, inv7; eqobsrel_tail; unfold EP1, EP2, impR, notR; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR, notR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  split; intros; mem_upd_simpl; simpl.
  rewrite H4; simpl; split; trivial.
  split; [split; [intros v1 | ] | trivial].
  destruct (H1 v1) as (W1, W2); rewrite <- W1.
  unfold O.assoc at 1 4; simpl.
  match goal with |- (andb (orb ?b _) _) = _ /\ _ => case_eq b; intros Heq; simpl end.
  change (is_true (T.i_eqb k BS_k0 v1
         (BVxor (k0 k) (snd (finv (k:=k) (m1 c))) (m1 h)))) in Heq; rewrite is_true_Ti_eqb in Heq; subst.
  rewrite not_is_true_false in H7.
  change (Bvector (n k) * Bvector (k1 k))%type with (T.interp k BS_nk1).
  change (Bvector (k0 k)) with (T.interp k BS_k0).
  change (T.interp k UOp.Tnk1) with (T.interp k BS_nk1) in H7.
  rewrite H7; simpl; split; [trivial | intros; discriminate].
  split; [trivial | intros; apply W2; rewrite <- W1; trivial].
  match goal with
   |- Datatypes.S ?x <= ?y + Datatypes.S ?z => 
    set (X:=x) in *; set (Y:=y) in *; set (Z:=z) in *; try omega'
  end.
  split; trivial.
  split; trivial.
  split.
  intros; destruct (H1 v1) as (W1, W2); rewrite <- W1.
  unfold O.assoc at 1 4; simpl.
  match goal with |- (andb (orb ?b _) _) = _ /\ _ => case_eq b; intros Heq; simpl end.
  change (is_true (T.i_eqb k BS_k0 v1
         (BVxor (k0 k) (snd (finv (k:=k) (m1 c))) (m1 h)))) in Heq; rewrite is_true_Ti_eqb in Heq; subst.
  rewrite not_is_true_false in H7.
  change (Bvector (n k) * Bvector (k1 k))%type with (T.interp k BS_nk1).
  change (Bvector (k0 k)) with (T.interp k BS_k0).
  change (T.interp k UOp.Tnk1) with (T.interp k BS_nk1) in H7.
  rewrite H7; simpl; split; [trivial | intros; discriminate].
  split; [trivial | intros; apply W2; rewrite <- W1; trivial]. 
  match goal with
   |- Datatypes.S ?x <= ?y + Datatypes.S ?z => 
    set (X:=x) in *; set (Y:=y) in *; set (Z:=z) in *; try omega' 
  end.
  deadcode; eqobs_in.

  swap iE7rE9pre; eqobs_hd iE7rE9pre.
  cp_test_l (Esnd (ap_finv c) |x| h in_dom LGb).
  rewrite proj1_MR; unfold inv7_bad, inv7; eqobsrel_tail; unfold EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H; intros. 
  mem_upd_simpl.
  repeat (split; auto).
  apply le_trans with (1:=H5); auto with arith.

  apply equiv_trans_r with (P2 := Meq) (Q1 := req_mem_rel (Vset.remove bad (Vset.remove LG OD)) inv7_bad)
    (Q2 := kreq_mem (Vset.add Gc OD)) (E2:=E7) (c2:=[
   rGn <$- {0,1}^n;
   rGk1 <$- {0,1}^k1;
   Dc <- 1 +! Dc;
   mn <- (false | one_n)
   ]).
  auto using dec_inv7_bad. 
  red; red; trivial.
  intros. 
  apply (@depend_only_req_mem_rel  (Vset.remove bad (Vset.remove LG OD)) _ _ _ dep_inv7_bad) with x y; trivial.
  apply req_mem_weaken with (2:= H0); vm_compute; trivial.
  unfold inv7_bad, inv7; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR, notR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  split; intros; mem_upd_simpl; simpl.

  split; [split; [intros v1 | ] | trivial].
  destruct (H1 v1) as (W1, W2); rewrite <- W1.
  unfold O.assoc at 1 4; simpl.
  match goal with |- (andb (orb ?b _) _) = _ /\ _ => case_eq b; intros Heq; simpl end.
  change (is_true (T.i_eqb k BS_k0 v1
         (BVxor (k0 k) (snd (finv (k:=k) (m1 c))) (m1 h)))) in Heq; rewrite is_true_Ti_eqb in Heq; subst.
  rewrite not_is_true_false in H3.
  change (Bvector (n k) * Bvector (k1 k))%type with (T.interp k BS_nk1).
  change (Bvector (k0 k)) with (T.interp k BS_k0).
  change (T.interp k UOp.Tnk1) with (T.interp k BS_nk1) in H3.
  rewrite H3; simpl; split; [trivial | intros; discriminate].
  split; [trivial | intros; apply W2; rewrite <- W1; trivial].
  match goal with
   |- Datatypes.S ?x <= ?y + Datatypes.S ?z => 
    set (X:=x) in *; set (Y:=y) in *; set (Z:=z) in *; try omega'
  end.
  trivial.
  deadcode; eqobs_in.
 Qed. 

 Definition iE7r_aux :=
  let RM := {{bad2,bad1}} in
  let pie : eq_inv_info trueR E7r E7r := 
   empty_info (mkENV H_body0 G_body2r_bad2 Dec_body7r GAdv_body1)
              (mkENV H_body0 G_body2r_bad2 Dec_body7r GAdv_body1) in
  let piH := add_refl_info_rm H RM RM pie in
  let piG := add_refl_info_rm G RM RM piH in
  let piD := add_refl_info_rm Dec RM RM piG in
  let piGA := add_refl_info_rm GAdv RM RM piD in
    piGA.

 Definition iE7rE9 :=
  let RM := {{bad1,bad2}} in
  let piH := my_add_refl_info eE7rE9 H in 
  let piGA := my_add_info GAdv RM RM iE7r_aux iE9 piH GAdv_body_inv7_bad in
  let piD := my_add_info Dec RM RM iE7r_aux iE9 piGA Dec_body_inv7_bad in
   adv_info piD.

 Lemma Pr_E7r_E9_bad : forall k (m:Mem.t k),
  (Pr E7r ((bad2 <- false)::G2b) m (EP k bad) <= Pr E9 G2 m (EP k bad))%tord.
 Proof.
  intros k m.
  unfold Pr; apply equiv_deno_le with (kreq_mem {{Y',g_a}})
    (req_mem_rel Vset.empty inv7_bad).
  deadcode iE7rE9.
  eqobs_tl iE7rE9.
  unfold inv7_bad, inv7; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR, notR; intros k2 m1 m2 H; decompose [and] H; clear H; intros.
  split; intros; mem_upd_simpl; simpl; auto.
  intros m1 m2 (_, ((_, H), _)); unfold EP1, EP2, impR in H.
  unfold charfun, restr, EP, fone.
  destruct (E.eval_expr bad m1); auto.
  rewrite H; trivial.
  apply kreq_mem_refl.
 Qed. 

 (* We resume the proof *)

 Lemma PrG0_bad_9 : forall k (m:Mem.t k),
  (Uabs_diff (Pr E0 G0 m (EP k (b=?=b'))) [1/2] <= 
   Pr E9 G2 m (EP k bad) + 
   qD_poly k/2^k1 k +
   (qD_poly k */ ((qD_poly k + qG_poly k)/2^k0 k + [1/2]^k0 k)) + 
   (qD_poly k/2^k1 k))%U%tord.
 Proof.
  intros k m.
  apply Ole_trans with (1:=PrG0_bad_5 m).
  apply Uplus_le_compat; [ | trivial].
  apply Uplus_le_compat; [ | trivial].
  eapply Ole_trans; [ apply Oeq_le; apply PR_5_bad | ].
  apply Ole_trans with (1:= PR_7r_bad m).
  apply Uplus_le_compat; [ | trivial].
  apply Pr_E7r_E9_bad.
 Qed. 


 (*********************************************************)
 (* The Dec Oracle does not call G anymore                *)
 (* We use the same transitions, to remove the call to H  *)
 (*********************************************************)
 Definition Hbaddr b s0 :=
  [     
   rH <$- {0,1}^k0;
   LHb <- (s0 | (b | rH)) |::| LHb 
  ].

 Definition H_body2b_gen CrH Cbad2:= 
  [
   If !(S in_dom LHb) then (Hbaddr false S)
   else 
    [
     If Efst (LHb[{S}]) then CrH ++ Cbad2 ++ [LHb <- LHb Upd S <| (false | rH) ]
     else [ rH <- (Esnd (LHb[{S}])) ]
    ]
  ].

 Definition in_dom_LG := 
  [
    g <- LG [{r}];
    m <- s |x2| g;
    If Esnd m =?= zero_k1 then [mn <- (true | Efst m)]
    else [mn <- (false | one_n)]
  ].

 Definition Dec_body_gen_b_H test_bad1 :=
  [
   If E.Eop O.Oor {testD, qG <! (Elen LG)} then [
      mn <- (false | one_n)
   ] else [
      LD <- (Ydef | c) |::| LD;
      Dc <- 1 +! Dc;
      st <- ap_finv c;
      s <- Efst st;
      t <- Esnd st;
      If s in_dom LHb then [
         If Efst (LHb[{s}]) then (
          [ 
           h <- Esnd (LHb[{s}]);
           r <- t |x| h
          ] ++
          test_bad1) 
       else [
           h <- Esnd (LHb[{s}]);
           r <- t |x| h;
           If r in_dom LG then in_dom_LG 
           else [ If R' =?= r _then [bad <- true]; mn <- (false | one_n) ]
         ]
      ] else Hbaddr true s ++ [ mn <- (false | one_n)]
   ]
 ].

 Definition test_bad1_9b := 
  [ 
   If r in_dom LG then [bad1 <- true] ++ in_dom_LG
   else [ If R' =?= r _then [bad1 <- true; bad <- true]; mn <- (false | one_n) ]
  ].

 Definition test_bad1_10b := 
  [ 
   If r in_dom LG then [bad1 <- true; mn <- (false | one_n)]
   else [ If R' =?= r _then [bad1 <- true]; mn <- (false | one_n) ]
  ].

 Definition Sample_h_nothing := @nil I.instr.

 Definition H_body2b := H_body2b_gen [ rH <- Esnd (LHb [{S}])] nil.

 Definition Dec_body9b := Dec_body_gen_b_H test_bad1_9b.

 Definition E9b := mkEnv H_body2b G_body2 Dec_body9b.

 Definition Dec_body10b := Dec_body_gen_b_H test_bad1_10b.

 Definition E10b := mkEnv H_body2b G_body2 Dec_body10b.

 Definition test_exists_H :=
   E.Eexists tc (   
     let c := Esnd tc in     
     let s := (Efst (ap_finv c)) in
     let t := (Esnd (ap_finv c)) in
     let h := rH in
     let r := t |x| h in
     (S =?= s) && ((r in_dom LG) || (R' =?= r))) LD.

 Definition H_body2b_bad2 :=
    H_body2b_gen
      [ rH <- Esnd (LHb [{S}]) ]
      [ If test_exists_H _then [bad2 <- true] ].

 Definition Dec_body10 := 
   Dec_body_gen_b_H test_bad1_nothing.

 Definition E10 := mkEnv H_body2b_bad2 G_body2 Dec_body10.

 Definition H_body2r_bad2 := 
   H_body2b_gen
   [ rH <$- {0,1}^k0]
   [ If test_exists_H _then [bad2 <- true] ].

 Definition Dec_body10r := 
  Dec_body_gen_b_H test_bad1_nothing.

 Definition E10r := mkEnv H_body2r_bad2 G_body2 Dec_body10r.

 Definition Bad1_H := 
   E.Eexists tc ( 
     let c := Esnd tc in
     let s := (Efst (ap_finv c)) in
     let t := (Esnd (ap_finv c)) in
     let h := Esnd (LHb[{s}]) in
     let r := t |x| h in  
     (s in_dom LHb) && Efst (LHb[{s}]) && ((r in_dom LG) || (R' =?= r))
   ) LD.

 Definition sample_body_H (LHhd LHtl : Var.var T_assoc_b_H) :=
  [ 
   auxH <- Ehd LHtl;
   LHtl <- Etl LHtl;
   If Efst (Esnd auxH) _then [
    rH_aux <$- {0,1}^k0;
    auxH <- (Efst auxH | (true | rH_aux))
   ];
   LHhd <- LHhd |++| auxH |::| Nil _
  ].

 Definition sample_while_H (LHhd LHtl : Var.var T_assoc_b_H) :=
  while !(LHtl =?= Nil _) do sample_body_H LHhd LHtl.

 Definition sample_true_H (LHhd LHtl:Var.var T_assoc_b_H) (LH:E.expr T_assoc_b_H) := 
  [
   LHhd <- Nil _;
   LHtl <- LH;
   sample_while_H LHhd LHtl
  ].

 Definition SLHb :=
   sample_true_H LHb_hd LHb_tl LHb ++
   [ 
    LHb <- LHb_hd; 
    (* This part resets the auxiliary variables *)
    LHb_hd <- Nil _;
    rH_aux <$- {0,1}^k0;
    auxH <- (S' | (true | rH_aux))
   ].

 (***************************************************************************************)
 (*   E9 ---> E9b:                                                                      *)
 (*        inlining of H in Dec, invariant LH = map (fun (x, p) => (x,snd p) LHb)       *)
 (*   E9b ---> E10b:                                                                    *)
 (*       updto bad1                                                                    *)
 (*   E10b ---> E10:                                                                    *)
 (*       invariant (EP1 (bad1)  ==> EP2 (bad2 || Bad1_H)                               *)
 (*   E10 ---> E10r:                                                                    *)
 (*       lazy sampling using SLHb                                                      *)
 (*   Then we should prove Pr E11r (G3b ++ SLHb) (EP (bad2 || Bad1))                    *)
 (*   Remark : once we are not focusing on bad2 we can remove the assignment            *)
 (*   true in LHb                                                                       *)
 (***************************************************************************************)


 (** E9 ---> E9b **)

 Definition eq_LH_LHb k 
   (v1 : T.interp k (T.Pair BS_nk1 BS_k0)) 
   (v2 : T.interp k (T.Pair BS_nk1 (T.Pair T.Bool BS_k0))) :=
   andb (T.i_eqb k BS_nk1 (fst v1) (fst v2)) (T.i_eqb k BS_k0 (snd v1) (snd (snd v2))).

 Definition inv_LHLHb : mem_rel :=
   fun k m1 m2 => forall2b (@eq_LH_LHb k) (m1 LH) (m2 LHb).

 Lemma dec_LHLHb : decMR inv_LHLHb.
 Proof.
    unfold inv_LHLHb; red; intros.
    match goal with |- sumbool (is_true ?X) _ => destruct X end; auto.
    right; discriminate.
 Qed.

 Lemma dep_inv_LHLHb : depend_only_rel inv_LHLHb {{LH}} {{LHb}}.
 Proof.
    red.
    intros k m1 m2 m1' m2' H1 H2 H3; unfold inv_LHLHb; rewrite <- (H1 _ LH), <- (H2 _ LHb); trivial.
 Qed.

 Definition e_b_H E1 E2 : eq_inv_info inv_LHLHb E1 E2 := 
   @empty_inv_info inv_LHLHb _ _ dep_inv_LHLHb (refl_equal true) dec_LHLHb E1 E2.

 Lemma inv_LHLHb_assoc : forall k (m1 m2:Mem.t k) e,
  E.eval_expr e m1 = E.eval_expr e m2 ->
  inv_LHLHb m1 m2 ->
  E.eval_expr (LH [{e}]) m1 = snd (E.eval_expr (LHb [{e}]) m2).
 Proof. 
  unfold inv_LHLHb; simpl; unfold O.eval_op; simpl; unfold O.assoc.
  intros k m1 m2 e Heq; rewrite <- Heq.
  generalize (E.eval_expr e m1) (m1 LH) (m2 LHb).
  intros v l1 l2; generalize l1 l2; clear l1 l2; 
   induction l1; destruct l2; trivial; try discriminate; simpl; intros.
  rewrite is_true_andb in H; destruct H.
  unfold eq_LH_LHb in H.
  rewrite is_true_andb, is_true_Ti_eqb, is_true_Ti_eqb in H; destruct H.
  match type of H with
   | ?X = ?Y => 
     match goal with |- 
     (match (if Ent.T.i_eqb k BS_nk1 v ?X' then _ else _) with Some _ => _ | None => _ end) = 
     snd (match (if Ent.T.i_eqb k BS_nk1 v ?Y' then _ else _) with Some _ => _ | None => _ end) =>
      change X' with X; change Y' with Y end
     end.
   rewrite H.
   destruct (T.i_eqb k BS_nk1 v (fst i)); auto.
 Qed.

 Lemma inv_LHLHb_dom : forall k (m1 m2:Mem.t k) e,
  E.eval_expr e m1 = E.eval_expr e m2 ->
  inv_LHLHb m1 m2 ->
  E.eval_expr (e in_dom LH) m1 = E.eval_expr (e in_dom LHb) m2.
 Proof.
  unfold inv_LHLHb; intros k m1 m2 e; simpl; unfold O.eval_op; simpl; intros Heq; rewrite <- Heq.
  generalize (E.eval_expr e m1) (m1 LH) (m2 LHb).
  intros v l1 l2; generalize l1 l2; clear l1 l2; induction l1; destruct l2; trivial;
   simpl; intros; try discriminate.
  rewrite is_true_andb in H; destruct H.
  unfold eq_LH_LHb in H; rewrite is_true_andb in H; destruct H.
  rewrite is_true_Ti_eqb in H.
  match type of H with
   | ?X = ?Y =>
     match goal with |- (orb (T.i_eqb k BS_nk1 v ?X') _) = (orb (T.i_eqb k BS_nk1 v ?Y') _)  =>
      change X' with X; change Y' with Y end
     end.
  rewrite H, IHl1 with l2; trivial.
 Qed.

 Lemma H_body0_H_body2b : forall E1 E2,
  EqObsInv 
  inv_LHLHb {{S}}
  E1 H_body0 
  E2 H_body2b 
  {{rH}}.
 Proof.
  intros Ev1 Ev2; set (ie:= e_b_H Ev1 Ev2).
  match goal with |- EqObsInv _ ?I _ _ _ _ _ =>
  assert (H0:forall (k : nat) (m1 m2 : Mem.t k),
      req_mem_rel I inv_LHLHb k m1 m2 ->
      E.eval_expr (S in_dom LH) m1 =
      E.eval_expr (S in_dom LHb) m2);
   [intros k m1 m2 (H1, H2);
    apply inv_LHLHb_dom; trivial;
    apply depend_only_fv_expr; eapply req_mem_weaken; [ | apply H1]; reflexivity 
   | cp_test_l (S in_dom LH);
     [ ep_eq_r (S in_dom LHb) true
     | ep_eq_r (S in_dom LHb) false];
     [ intros k m1 m2 (H1, H2); rewrite <-(H0 k m1 m2 H1); trivial
     | idtac
     | intros k m1 m2 (H1, H2); rewrite <- (H0 k m1 m2 H1), <- not_is_true_false; trivial
     | rewrite proj1_MR; eqobs_hd ie
     ]
   ]
  end.
  cp_test_r (Efst (LHb [{S}])); rewrite proj1_MR.
  rewrite req_mem_rel_assoc.
  apply equiv_weaken with
    (req_mem_rel Vset.empty ((fun k m1 m2 => m1 rH = m2 rH) /-\ inv_LHLHb)).
    intros k m1 m2 (_, (H1, H2)); split; [ | trivial].
    intros t x Hin.
    Vset_mem_inversion Hin; subst; trivial.
  set (Q:= (fun (k : nat) (m1 m2 : Mem.t k) => m1 rH = m2 rH) /-\ inv_LHLHb).
  eqobsrel_tail; unfold Q, EP1; simpl; unfold implMR, O.eval_op; simpl; unfold inv_LHLHb, andR.
    intros k m1 m2 (H1, (H2, H3)).
  mem_upd_simpl; split.
  refine (inv_LHLHb_assoc S _ H2). apply (H1 _ S); trivial.
  rewrite <- (H1 _ S); trivial.
  generalize (m1 S) (m1 LH) (m2 LHb) H2 H3; intros v l1 l2; generalize l1 l2.
  clear H1 H2 H3 m1 m2 l1 l2.
  unfold O.assoc; induction l1; destruct l2; simpl; trivial; 
   try (intros; discriminate).
  unfold eq_LH_LHb; repeat (rewrite is_true_andb || rewrite is_true_Ti_eqb).
  destruct i as (i1, i2); simpl; intros ((H1, H2),H3); rewrite H1.
  case_eq (T.i_eqb k BS_nk1 v i1); intros; simpl.
  rewrite H2; repeat rewrite Ti_eqb_refl; trivial.
  rewrite H2; repeat rewrite Ti_eqb_refl; simpl.
  rewrite <- H1 in H. match type of H with ?X = _ =>
   match type of H4 with is_true (orb ?Y _) => change Y with X in H4 end end.
  rewrite H in H4; simpl in H4; apply IHl1; trivial.
  apply equiv_weaken with
    (req_mem_rel Vset.empty ((fun k m1 m2 => m1 rH = m2 rH) /-\ inv_LHLHb)).
    intros k m1 m2 (_, (H1, H2)); split; [ | trivial].
    intros t x Hin; Vset_mem_inversion Hin; subst; trivial.
    set (Q:= (fun (k : nat) (m1 m2 : Mem.t k) => m1 rH = m2 rH) /-\ inv_LHLHb).
  eqobsrel_tail; unfold Q, EP1; simpl; unfold implMR, O.eval_op; simpl; unfold inv_LHLHb, andR.
    intros k m1 m2 (H1, (H2, H3)).
  mem_upd_simpl; split; [ | trivial].
  refine (inv_LHLHb_assoc S _ H2). apply (H1 _ S); trivial.
  eqobsrel_tail; simpl; unfold implMR, O.eval_op, inv_LHLHb; simpl; intros k m1 m2 (H1, H2).
  repeat rewrite Mem.get_upd_same; simpl; unfold eq_LH_LHb at 1.
  rewrite (H1 _ S), (H1 _ rH); trivial.
  simpl; repeat rewrite Ti_eqb_refl; trivial.
 Qed.

 Definition eE9E9b : eq_inv_info inv_LHLHb E9 E9b :=
  let ie := e_b_H E9 E9b in
  let piH : eq_inv_info inv_LHLHb E9 E9b := add_info H Vset.empty Vset.empty ie (H_body0_H_body2b _ _) in
  let piG : eq_inv_info inv_LHLHb E9 E9b := add_refl_info G piH in
   add_refl_info GAdv piG.

 Lemma Dec_body9_Dec_body9b :
  EqObsInv 
  inv_LHLHb (Vset.remove LH ID)
  E9 Dec_body9 
  E9b Dec_body9b 
  (Vset.remove LH OD).
 Proof.
  unfold Dec_body9.
  cp_test (E.Eop O.Oor {testD, qG <! (Elen LG)}); rewrite proj1_MR.
   eqobs_in eE9E9b.
  inline eE9E9b H.
  auto using dec_LHLHb.
  ep; deadcode eE9E9b.

  match goal with |- EqObsInv _ ?I _ _ _ _ _ =>
  assert (forall (k : nat) (m1 m2 : Mem.t k),
      req_mem_rel I inv_LHLHb k m1 m2 ->
      E.eval_expr (Efst (ap_finv c) in_dom LH) m1 = E.eval_expr (Efst (ap_finv c) in_dom LHb) m2);
    [ intros k m1 m2 (H1, H2);
      apply inv_LHLHb_dom; trivial;
      apply depend_only_fv_expr; eapply req_mem_weaken; [ | apply H1]; reflexivity
    | ]
   end.
  cp_test_l (Efst (ap_finv c) in_dom LH);
     [ ep_eq_r (Efst (ap_finv c) in_dom LHb) true
     | ep_eq_r (Efst (ap_finv c) in_dom LHb) false];
     [ intros k m1 m2 (H1, H2); rewrite <-(H k m1 m2 H1); trivial
     | 
     | intros k m1 m2 (H1, H2); rewrite <- (H k m1 m2 H1), <- not_is_true_false; trivial
     | 
     ].
   deadcode eE9E9b.
   match goal with |- equiv ((req_mem_rel ?I ?P) /-\ _) _ _ _ _ _ =>
    assert (forall (k : nat) (m1 m2 : Mem.t k),
      req_mem_rel I inv_LHLHb k m1 m2 ->
      E.eval_expr (LH [{Efst (ap_finv c)}]) m1 =
      E.eval_expr (Esnd (LHb [{Efst (ap_finv c)}])) m2)
   end.
    intros k m1 m2 (H1, H2).
    refine (inv_LHLHb_assoc _ _ H2).
    apply depend_only_fv_expr; eapply req_mem_weaken; [ | apply H1]; reflexivity.
   cp_test_l (Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}]) in_dom LG);
   [ ep_eq_r (Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}]) in_dom LG) true
   | ep_eq_r (Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}]) in_dom LG) false
   ].
   intros k m1 m2 ((H1,H2), H3).
   generalize (LH [{Efst (ap_finv c)}]) (Esnd (LHb [{Efst (ap_finv c)}])) (H0 k m1 m2 H1) H3.
   unfold EP1; simpl; unfold O.eval_op; simpl.
   destruct H1 as (H1, H1'); intros e e0 Heq; rewrite Heq, (H1 _ LG), (H1 _ c); trivial.
   cp_test_l (Esnd (Efst (ap_finv c)) |x| Esnd (LG [{Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}])}]) =?= zero_k1);
   [ ep_eq_r (Esnd (Efst (ap_finv c)) |x| Esnd (LG [{Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}])}]) =?= zero_k1) true
   | ep_eq_r (Esnd (Efst (ap_finv c)) |x| Esnd (LG [{Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}])}]) =?= zero_k1) false
   ].
   intros k m1 m2 (((H1,H2), H3), H4).
   generalize (LH [{Efst (ap_finv c)}]) (Esnd (LHb [{Efst (ap_finv c)}])) (H0 k m1 m2 H1) H4.
   unfold EP1; simpl; unfold O.eval_op; simpl.
   destruct H1 as (H1, H1'); intros e e0 Heq; rewrite Heq, (H1 _ LG), (H1 _ c); trivial.
   apply equiv_weaken with (req_mem_rel (Vset.remove mn (Vset.remove LH OD)) 
           ((fun k m1 m2 => m1 mn = m2 mn) /-\ inv_LHLHb)).
   intros k m1 m2 (H1, (H2, H3)); split; [ | trivial].
   apply req_mem_weaken with (Vset.add mn (Vset.remove mn (Vset.remove LH OD))).
     vm_compute; trivial.
     intros t x Hin; rewrite VsetP.add_spec in Hin; destruct Hin; [ | apply H1; trivial].
     inversion H4; trivial.
   set (Q:= (fun (k : nat) (m1 m2 : Mem.t k) => m1 mn = m2 mn) /-\ inv_LHLHb).
   repeat rewrite req_mem_rel_assoc.
   eqobsrel_tail; unfold Q, EP1; simpl; unfold implMR, O.eval_op; simpl; unfold inv_LHLHb, andR.
    intros k m1 m2 H1; decompose [and] H1; clear H1.
   mem_upd_simpl; split; [ | trivial].
   generalize (H0 k m1 m2 (conj H2 H4)); simpl; unfold O.eval_op, UOp.Tnk1; simpl; intros Heq; rewrite Heq, (H2 _ c), (H2 _ LG); trivial.
   intros k m1 m2 (((H1,H2), H3), H4).
   generalize (LH [{Efst (ap_finv c)}]) (Esnd (LHb [{Efst (ap_finv c)}])) (H0 k m1 m2 H1) H4.
   unfold EP1, notR; simpl; unfold O.eval_op; simpl. 
   destruct H1 as (H1, H1'); intros e e0 Heq; rewrite Heq, not_is_true_false, (H1 _ LG), (H1 _ c); trivial.
   eqobsrel_tail; unfold EP1; simpl; unfold implMR, O.eval_op; simpl; unfold inv_LHLHb, andR.
    intros k m1 m2 H1; decompose [and] H1; clear H1.
   mem_upd_simpl.
   intros k m1 m2 ((H1, H3), H4).
   generalize (LH [{Efst (ap_finv c)}]) (Esnd (LHb [{Efst (ap_finv c)}])) (H0 k m1 m2 H1) H4.
   unfold EP1, notR; simpl; unfold O.eval_op; simpl. 
   destruct H1 as (H1, H1'); intros e e0 Heq; rewrite Heq, not_is_true_false, (H1 _ LG), (H1 _ c); trivial.
   cp_test_l (R' =?= Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}]));
   [ ep_eq_r (R' =?= Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}])) true
   | ep_eq_r (R' =?= Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}])) false
   ].
   intros k m1 m2 (((H1, H2), H3), H4).
   generalize (LH [{Efst (ap_finv c)}]) (Esnd (LHb [{Efst (ap_finv c)}])) (H0 k m1 m2 H1) H4.
   unfold EP1, notR; simpl; unfold O.eval_op; simpl. 
   destruct H1 as (H1, H1'); intros e e0 Heq; rewrite Heq, (H1 _ R'), (H1 _ c); trivial.
   repeat rewrite proj1_MR; eqobs_in eE9E9b.
   intros k m1 m2 (((H1, H2), H3), H4).
   generalize (LH [{Efst (ap_finv c)}]) (Esnd (LHb [{Efst (ap_finv c)}])) (H0 k m1 m2 H1) H4.
   unfold EP1, notR; simpl; unfold O.eval_op; simpl. 
   destruct H1 as (H1, H1'); intros e e0 Heq; rewrite Heq, not_is_true_false, (H1 _ R'), (H1 _ c); trivial.
   repeat rewrite proj1_MR; eqobs_in eE9E9b.
   alloc_l eE9E9b h rH; ep; deadcode eE9E9b.
   eqobsrel_tail; unfold EP1; simpl; unfold implMR, O.eval_op; simpl; unfold inv_LHLHb, andR.
    intros k m1 m2 H1; decompose [and] H1; clear H1.
   intros; mem_upd_simpl.
   simpl; unfold eq_LH_LHb at 1; simpl.
   rewrite (H0 _ c), Ti_eqb_refl, Ti_eqb_refl; trivial.
 Qed.

 Definition iE9E9b : eq_inv_info inv_LHLHb E9 E9b :=
  let piD : eq_inv_info inv_LHLHb E9 E9b := 
   add_info Dec Vset.empty {{bad1}} eE9E9b Dec_body9_Dec_body9b in
  adv_info piD.

 Definition init1b_H := 
  [ 
   Ydef <- false;
   LG <- Nil _;
   LHb <- Nil _;
   LD <- Nil _;
   Dc <- 0;
   Gc <- 0;
   R' <$- {0,1}^k0
  ].

 Definition G2b_H := 
  [bad <- false] ++ init1b_H ++ SGR' ++ [S' <- (GR'n | GR'k1)] ++ tail2.

 Lemma Pr_9_bad : forall k (m:Mem.t k), 
  Pr E9 G2 m (EP k bad) == Pr E9b G2b_H (m{!bad1 <-- false!}) (EP k bad).
 Proof.
  intros k m; rewrite set_bad.
  apply EqObs_Pr with {{Y',g_a}}.
  apply equiv_weaken with (req_mem_rel (fv_expr bad) inv_LHLHb).
   intros k2 m1 m2 (H1, H2); trivial.
  deadcode iE9E9b.
  eqobs_tl iE9E9b.
  eqobsrel_tail; simpl; unfold implMR, O.eval_op; simpl; unfold inv_LHLHb, andR.
  intros; mem_upd_simpl.
 Qed.

 (* E9b --> E10b: FL w/bad1 *)

 Definition iE10b := iEiEi H_body2b G_body2 Dec_body10b.

 Lemma PR_9b_bad : forall k (m:Mem.t k),
  (Pr E9b G2b_H (m{! bad1 <-- false !}) (EP k bad) <= 
   Pr E10b G2b_H (m{! bad1 <-- false !}) (EP k bad) + 
   Pr E10b G2b_H (m{!bad1 <-- false!}) (EP k bad1))%U%tord.
 Proof.
   intros k m ; set (mb:= m{!bad1 <-- false!}).
   apply Uabs_diff_le_plus.
   apply upto_bad_Uabs_diff with 
     (i_upto bad1 H_body2b G_body2 Dec_body9b H_body2b G_body2 Dec_body10b).
    trivial.
    vm_compute; trivial.
    apply is_lossless_correct with (refl1_info iE10b); vm_compute; trivial.
 Qed.

 (* E10b --> E10 : invariant EP1 bad1  ==> EP2 (bad2 || Bad1_H) *)

 Definition inv10b_10 := impR (EP1 bad1) (EP2 (bad2 || Bad1_H)).

 Lemma dec_inv10b_10 : decMR inv10b_10.
 Proof. 
  unfold inv10b_10; auto. 
 Qed.

 Lemma dep_inv10b_10 : depend_only_rel inv10b_10 
  (Vset.union (fv_expr bad1) Vset.empty)
  (Vset.union Vset.empty (fv_expr (bad2 || Bad1_H))).
 Proof.
  unfold inv10b_10; auto.
 Qed.

 Definition eE10bE10 : eq_inv_info inv10b_10 E10b E10 := 
  @empty_inv_info inv10b_10 _ _ dep_inv10b_10 (refl_equal true) 
  dec_inv10b_10 E10b E10.

 Lemma G_body2_inv10b_10 : 
  EqObsInv 
  inv10b_10 {{LG,R,R',bad}}
  E10b G_body2 
  E10 G_body2 
  {{LG,rGn,rGk1,bad}}.
 Proof.
  unfold G_body2.
  cp_test (R in_dom LG).
   rewrite proj1_MR; eqobs_in eE10bE10.
  rewrite proj1_MR; eqobs_hd eE10bE10.
  unfold inv10b_10; eqobsrel_tail; unfold EP1, EP2, impR,andR; simpl; unfold O.eval_op; simpl; intros k m1 m2 (H1, H2).
  intros Hbad; apply H2 in Hbad; rewrite is_true_orb in Hbad; destruct Hbad.
  rewrite H; trivial.
  simpl; rewrite is_true_existsb in H; rewrite is_true_orb; right; rewrite is_true_existsb.
  destruct H as (x, (Hin, H)).
  repeat (rewrite Mem.get_upd_same in H || (rewrite Mem.get_upd_diff in H; [ | discriminate])).
  exists x; split; trivial.
  rewrite is_true_andb in H |- *; destruct H; split; trivial.
  rewrite <- orb_assoc, is_true_orb; right; exact H0.
 Qed.

 Lemma H_body2b_inv10b_10 : 
  EqObsInv 
  inv10b_10 {{LHb,S}}
  E10b H_body2b 
  E10 H_body2b_bad2 
  {{LHb, rH}}.
 Proof.
  unfold H_body2b, H_body2b_bad2, H_body2b_gen.
  cp_test (S in_dom LHb).
  cp_test (Efst (LHb [{S}])).
  match goal with |- equiv _ _ _ _ [_; If ?e _then _; _] _ => 
   cp_test_r e end.
  unfold inv10b_10; eqobsrel_tail; unfold EP1, EP2, impR,andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2
   (H1, H2); trivial.
  unfold inv10b_10; eqobsrel_tail; unfold EP1, EP2, impR,andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2
   (H1, (H2, H3)); decompose [and] H3; clear H3.
  intros Hbad; apply H2 in Hbad; clear H2; rewrite is_true_orb in Hbad; destruct Hbad as [Hbad | Hbad].
  rewrite Hbad; trivial.
  rewrite is_true_existsb in Hbad; destruct Hbad as (x, (Hin, Hbad)).
  rewrite is_true_orb; right.
  rewrite is_true_existsb; exists x; split; trivial.
  repeat (rewrite Mem.get_upd_same in Hbad || (rewrite Mem.get_upd_diff in Hbad; [ | discriminate])).
  repeat rewrite is_true_andb in Hbad; decompose [and] Hbad.
  assert (fst (finv (k:=k) (snd x)) <> m2 S).
   intros Heq; apply H6.
    rewrite is_true_existsb.
    exists x; split; trivial.
    mem_upd_simpl.
    rewrite <- Heq.
    rewrite Ti_eqb_refl; simpl; trivial.
  rewrite existsb_upd_diff, assoc_upd_diff; trivial.
  change UOp.Tnk1 with BS_nk1 in H8; change UOp.Tnk1 with BS_nk1 in H3; rewrite H3, H8; trivial.
  repeat rewrite proj1_MR; eqobs_in eE10bE10.
  unfold inv10b_10; eqobsrel_tail; unfold EP1, EP2, impR,andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2
   (H1, (H2, H3)).
  intros v _ Hbad; apply H2 in Hbad; rewrite is_true_orb in Hbad; destruct Hbad.
  rewrite H; trivial.
  rewrite is_true_orb; right.
  rewrite is_true_existsb in H |- *; destruct H as (x, (Hin, Hbad)); exists x; split; trivial.
  clear H2; repeat (rewrite Mem.get_upd_same in Hbad || (rewrite Mem.get_upd_diff in Hbad; [ | discriminate])).
  unfold O.assoc; simpl.
  match goal with |- is_true (andb (andb (orb ?x _) _) _) => case_eq x; intros Heq end.
  repeat rewrite is_true_andb in Hbad; decompose [and] Hbad.
  destruct H3 as (_, H3); elim H3.
  change (is_true (T.i_eqb k BS_nk1 (fst (finv (k:=k) (snd x))) (m2 S))) in Heq.
  rewrite is_true_Ti_eqb in Heq; rewrite <- Heq; trivial.
  trivial.
 Qed.

 Definition iE10bE10_d : eq_inv_info inv10b_10 E10b E10 :=
  let piH : eq_inv_info inv10b_10 E10b E10:= 
   add_info H Vset.empty Vset.empty eE10bE10 H_body2b_inv10b_10 in
  let piG : eq_inv_info inv10b_10 E10b E10 := 
   add_info G {{bad1}} {{bad2}} piH G_body2_inv10b_10 in
   piG.

 Lemma Dec_body10b_Dec_body10 : 
  EqObsInv inv10b_10 
  (Vset.add LD (Vset.add LHb (Vset.remove LH ID)))
  E10b Dec_body10b 
  E10  Dec_body10 
  (Vset.add LD (Vset.add LHb (Vset.remove LH OD))).
 Proof.
  unfold Dec_body10b, Dec_body10, Dec_body_gen_b_H.
  cp_test (E.Eop O.Oor {testD, qG <! (Elen LG)}).
   rewrite proj1_MR; eqobs_in iE10bE10_d.
  ep; deadcode iE10bE10_d.
  cp_test (Efst (ap_finv c) in_dom LHb).
  cp_test (Efst (LHb [{Efst (ap_finv c)}])).
  cp_test (Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}]) in_dom LG).
  unfold inv10b_10; eqobsrel_tail; unfold EP1, EP2, impR,andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2
   (H1, (H2, H3)); decompose [and] H3; clear H3.
  change UOp.Tnk1 with BS_nk1 in H7; change UOp.Tnk1 with BS_nk1 in H9; change UOp.Tnk1 with BS_nk1 in H10.
  intros _; rewrite H7, H9, H10; simpl; rewrite orb_true_r; trivial.
  cp_test (R' =?= Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}])).
  unfold inv10b_10; eqobsrel_tail; unfold EP1, EP2, impR,andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2
   (H1, (H2, H3)); decompose [and] H3; clear H3.
  change UOp.Tnk1 with BS_nk1 in H7; change UOp.Tnk1 with BS_nk1 in H9; change UOp.Tnk1 with BS_nk1 in H12.
  intros _; rewrite H7, H9, H12; simpl; rewrite orb_true_r; simpl; rewrite orb_true_r; trivial.
  eqobs_tl iE10bE10_d.
  unfold inv10b_10; eqobsrel_tail; unfold EP1, EP2, impR,andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2
   (H1, (H2, H3)); decompose [and] H3; clear H3.
  intros Hbad; apply H2 in Hbad; rewrite is_true_orb in Hbad; destruct Hbad.
  rewrite H3; trivial.
  rewrite is_true_orb; right; repeat rewrite is_true_existsb in H3; destruct H3 as (x, (Hin, Hbad)).
  change UOp.Tnk1 with BS_nk1 in H7; change UOp.Tnk1 with BS_nk1 in H9; rewrite H7, H9; simpl.
  rewrite is_true_orb; right.
  clear H2; repeat (rewrite Mem.get_upd_same in Hbad || (rewrite Mem.get_upd_diff in Hbad; [ | discriminate])).
  rewrite is_true_existsb; exists x; split; trivial.
  cp_test (Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}]) in_dom LG).
  cp_test (Esnd (Efst (ap_finv c)) |x| Esnd (LG [{Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}])}]) =?= zero_k1).
  unfold inv10b_10; eqobsrel_tail; unfold EP1, EP2, impR,andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2
   (H1, (H2, H3)); decompose [and] H3; clear H3.
  intros Hbad; apply H2 in Hbad; clear H2; rewrite is_true_orb in Hbad; destruct Hbad.
  rewrite H2; trivial.
  rewrite is_true_orb; right; repeat rewrite is_true_existsb in H2; destruct H2 as (x, (Hin, Hbad)).
  repeat (rewrite Mem.get_upd_same in Hbad || (rewrite Mem.get_upd_diff in Hbad; [ | discriminate])).
  rewrite is_true_orb; right; rewrite is_true_existsb; exists x; split; trivial.
  unfold inv10b_10; eqobsrel_tail; unfold EP1, EP2, impR,andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2
   (H1, (H2, H3)); decompose [and] H3; clear H3.
  intros Hbad; apply H2 in Hbad; clear H2; rewrite is_true_orb in Hbad; destruct Hbad.
  rewrite H2; trivial.
  rewrite is_true_orb; right; repeat rewrite is_true_existsb in H2; destruct H2 as (x, (Hin, Hbad)).
  repeat (rewrite Mem.get_upd_same in Hbad || (rewrite Mem.get_upd_diff in Hbad; [ | discriminate])).
  rewrite is_true_orb; right; rewrite is_true_existsb; exists x; split; trivial.
  cp_test (R' =?= Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}])).
  unfold inv10b_10; eqobsrel_tail; unfold EP1, EP2, impR,andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2
   (H1, (H2, H3)); decompose [and] H3; clear H3.
  intros Hbad; apply H2 in Hbad; clear H2; rewrite is_true_orb in Hbad; destruct Hbad.
  rewrite H2; trivial.
  rewrite is_true_orb; right; repeat rewrite is_true_existsb in H2; destruct H2 as (x, (Hin, Hbad)).
  repeat (rewrite Mem.get_upd_same in Hbad || (rewrite Mem.get_upd_diff in Hbad; [ | discriminate])).
  rewrite is_true_orb; right; rewrite is_true_existsb; exists x; split; trivial.
  unfold inv10b_10; eqobsrel_tail; unfold EP1, EP2, impR,andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2
   (H1, (H2, H3)); decompose [and] H3; clear H3.
  intros Hbad; apply H2 in Hbad; clear H2; rewrite is_true_orb in Hbad; destruct Hbad.
  rewrite H2; trivial.
  rewrite is_true_orb; right; repeat rewrite is_true_existsb in H2; destruct H2 as (x, (Hin, Hbad)).
  repeat (rewrite Mem.get_upd_same in Hbad || (rewrite Mem.get_upd_diff in Hbad; [ | discriminate])).
  rewrite is_true_orb; right; rewrite is_true_existsb; exists x; split; trivial.

  unfold inv10b_10; eqobsrel_tail; unfold EP1, EP2, impR,andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2
   (H1, (H2, H3)); decompose [and] H3; clear H3.
  intros v _ Hbad; apply H2 in Hbad; clear H2; rewrite is_true_orb in Hbad; destruct Hbad.
  rewrite H0; trivial.
  rewrite is_true_orb; right; repeat rewrite is_true_existsb in H0; destruct H0 as (x, (Hin, Hbad)).
  repeat (rewrite Mem.get_upd_same in Hbad || (rewrite Mem.get_upd_diff in Hbad; [ | discriminate])).
  rewrite is_true_orb; right; rewrite is_true_existsb; exists x; split; trivial.
  unfold O.assoc; simpl.
  match goal with |- is_true (andb (andb (orb ?x _) _) _) => case_eq x; intros Heq end.
  simpl.
  repeat rewrite is_true_andb in Hbad; decompose [and] Hbad.
  elim H6.
  change (is_true (T.i_eqb k BS_nk1 (fst (finv (k:=k) (snd x)))
         (fst (finv (k:=k) (m2 c))))) in Heq. 
  rewrite is_true_Ti_eqb in Heq; simpl in Heq.
  change (Bvector (n k) * Bvector (k1 k))%type with (T.interp k UOp.Tnk1) in Heq.
  change (Bvector (k0 k)) with (T.interp k BS_k0) in Heq; rewrite <- Heq; trivial.
  trivial.
 Qed.

 Definition iE10bE10 : eq_inv_info inv10b_10 E10b E10 :=
  let piD : eq_inv_info inv10b_10 E10b E10 := 
   add_info Dec {{bad1}} {{bad2}} iE10bE10_d Dec_body10b_Dec_body10 in
  let piGA : eq_inv_info inv10b_10 E10b E10 := 
   add_refl_info_rm GAdv {{bad1}} {{bad2}} piD in
  adv_info piGA. 

 Lemma EqObs_E10b_E10 :
  equiv (kreq_mem {{Y',g_a}}) 
  E10b ((bad1 <- false) :: G2b_H) 
  E10  ((bad2 <- false) :: G2b_H)
  (req_mem_rel {{bad}} inv10b_10).
 Proof.
  eqobs_tl iE10bE10.
  unfold inv10b_10; eqobsrel_tail; unfold impR, andR, EP1, EP2, notR; 
   simpl; unfold O.eval_op; simpl.
  intros k m1 m2; auto.
 Qed.

 Lemma PR_9_bad_10 : forall k m,
  (Pr E9 G2 m (EP k bad) <= 
   Pr E10 G2b_H (m{!bad2 <-- false !}) (EP k bad) +  
   Pr E10 G2b_H (m{!bad2 <-- false!}) (EP k (bad2 || Bad1_H)))%U%tord.
 Proof.
  intros k m; rewrite Pr_9_bad; eapply Ole_trans; [apply PR_9b_bad | ].
  repeat rewrite set_bad.
  apply Uplus_le_compat.
  apply Oeq_le; apply equiv_deno with (1:= EqObs_E10b_E10); trivial.
  intros m1 m2 (H1, H2).
  unfold charfun, EP, restr, fone; simpl; rewrite (H1 _ bad); trivial.
  apply equiv_deno_le with (1:= EqObs_E10b_E10); trivial.
  unfold inv10b_10, EP1, EP2, impR; intros m1 m2 (H1, H2).
  unfold charfun, EP, restr, fone.
  destruct (E.eval_expr bad1 m1); [ | trivial].
  rewrite H2; trivial.
 Qed.

 (* E10 ---> E10r:                                                             *)
 (*       lazy sampling using SLGb                                             *)
 (*         E10, G2b_H == E10, SLHb ++ G2b_H == E10r, G2b_H ++ SLGb            *)

 Definition XSLHb:= {{LHb_hd,LHb_tl,LHb,rH_aux,auxH}}.

 Definition ISLHb:= {{S'}}.

 Lemma Modify_SLHb : forall E, Modify E XSLHb SLHb.
 Proof.
  intro E.
  compute_assertion X t1 (modify (refl1_info (empty_info E E)) Vset.empty SLHb).
  apply modify_correct in X; eapply Modify_weaken; [eauto | ].
  vm_compute; trivial.
 Qed.

 Lemma EqObs_SLHb : forall E1 E2, EqObs (Vset.union ISLHb XSLHb) E1 SLHb E2 SLHb XSLHb.
 Proof. 
  intros; eqobs_in. 
 Qed.

 Lemma IXSLHb_global : forall x : VarP.Edec.t, 
  Vset.mem x (Vset.union ISLHb XSLHb) -> Var.is_global x.
 Proof.
  apply Vset.forallb_correct.
  intros x y Heq; rewrite Heq; trivial.
  vm_compute; trivial.
 Qed.

 Hint Resolve Modify_SLHb IXSLHb_global EqObs_SLHb.

 Lemma SLHb_dom : forall E (b : bool),
  equiv (Meq /-\ EP1 (!(S in_dom LHb) =?= b)) 
  E SLHb 
  E SLHb 
  (Meq /-\ EP1 (!(S in_dom LHb) =?= b)).
 Proof.
  unfold SLHb; intros.
  apply equiv_app with (Meq /-\ EP1 (!(S in_dom LHb_hd) =?= b)).
  unfold sample_true_H.
  match goal with |- equiv ?P _ [?i1; ?i2; ?i3] _ _ _ =>
   change [i1; i2; i3] with ([i1; i2]++[i3]); apply equiv_app with 
    (Meq /-\ (EP1 (!(S in_dom LHb) =?= b) /-\ EP1 ((S in_dom LHb) =?= ((S in_dom LHb_hd) || (S in_dom LHb_tl))))) end.
  union_mod; [ rewrite proj1_MR; auto | ].
  eqobsrel_tail; intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
  split; [exact H2 | apply Ti_eqb_refl].
  eapply equiv_weaken; [ | apply equiv_while].
  intros k m1 m2 ((H1, (H2, H3)), (H4, _)); split; trivial.
  unfold notR, EP1, EP2 in *.
  change (~ negb (E.eval_expr (LHb_tl =?= Nil _) m1)) in H4.
  rewrite <- is_true_negb, negb_involutive in H4.
  rewrite <- (expr_eval_eq m1 (!(S in_dom LHb))) in H2.
  rewrite <- (expr_eval_eq m1 (S in_dom LHb)) in H3.
  rewrite <- (expr_eval_eq m1 LHb_tl) in H4.
  rewrite <- (expr_eval_eq m1 (!(S in_dom LHb_hd))).
  rewrite <- H2.
  change (negb (E.eval_expr (S in_dom LHb_hd) m1) = negb (E.eval_expr (S in_dom LHb) m1)).
  rewrite H3; generalize H4; simpl; unfold O.eval_op; simpl; intros H5; rewrite H5; simpl;
  rewrite orb_false_r; trivial.
  intros k m1 m2 (H1, _); rewrite H1; trivial.
  union_mod; [ rewrite proj1_MR, proj1_MR; auto | ].
  eqobsrel_tail; unfold implMR, EP1, EP2,Meq, andR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H.
  rewrite H1; rewrite is_true_Ti_eqb in H4; rewrite H4; subst; clear H1 H4.
  destruct (m2 LHb_tl); [discriminate | simpl].
  split; intros; (split; [trivial | ]);
  rewrite existsb_app, orb_assoc; simpl; rewrite orb_false_r; apply Ti_eqb_refl.
  union_mod; [ rewrite proj1_MR; auto | ].
  eqobsrel_tail; intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
  intros; exact H2.
 Qed.

 Definition split_sample_H := 
  (sample_true_H LHb_hd_hd LHb_hd_tl (Efst (S Esplit LHb)) ++
   [ If Efst (Efst (Esnd (S Esplit LHb))) then 
    [rH_aux1 <$- {0,1}^k0; LHbS <- (true | rH_aux1 ) ]
    else [ LHbS <- Efst (Esnd (S Esplit LHb)) ] ] ++
   sample_true_H LHb_tl_hd LHb_tl_tl (Esnd (Esnd (S Esplit LHb))) ++
   [ LHb_hd <- LHb_hd_hd |++| (S | LHbS) |::| LHb_tl_hd; LHb_tl <- Nil _]).
 
 Lemma sample_split_H : forall E ,
  equiv (req_mem_rel {{S,LHb}} (EP1 (S in_dom LHb)))
  E (sample_true_H LHb_hd LHb_tl LHb)
  E split_sample_H
  (kreq_mem {{LHb_tl,LHb_hd}}).
 Proof.
  unfold sample_true_H; intros.
  set (QQ:=kreq_mem {{LHb_tl,LHb_hd}}).
  apply equiv_trans_r with Meq QQ QQ E
    ([ LHb_hd_hd <- Nil _;
       LHb_hd_tl <- Efst (S Esplit LHb) ] ++
     [ sample_while_H LHb_hd_hd LHb_hd_tl;
       If Efst (Efst (Esnd (S Esplit LHb))) then [
         rH_aux1 <$- {0,1}^k0;
         LHbS <- (true | rH_aux1)
       ] else [LHbS <- Efst (Esnd (S Esplit LHb))];
      LHb_tl_hd <- Nil _;
      LHb_tl_tl <- Esnd (Esnd (S Esplit LHb));
      sample_while_H LHb_tl_hd LHb_tl_tl;
      LHb_hd <- LHb_hd_hd |++| (S | LHbS) |::| LHb_tl_hd;
      LHb_tl <- Nil _
    ]); unfold QQ.
  auto. red; red; trivial. apply req_mem_trans.
  2: swap; eqobs_in.
  change [LHb_hd <- Nil _; LHb_tl <- LHb; sample_while_H LHb_hd LHb_tl] with
   ([LHb_hd <- Nil _; LHb_tl <- LHb] ++ [sample_while_H LHb_hd LHb_tl]).
  apply equiv_app with
   (req_mem_rel {{S,LHb}} 
    (fun k m1 m2 => E.eval_expr LHb_hd m1 = E.eval_expr LHb_hd_hd m2 /\
     E.eval_expr LHb_tl m1 = 
     E.eval_expr (LHb_hd_tl |++| (S | Efst (Esnd (S Esplit LHb))) |::| Esnd (Esnd (S Esplit LHb))) m2)).
  ep_eq_l LHb 
  (Efst (S Esplit LHb) |++| (S | Efst (Esnd (S Esplit LHb))) |::| Esnd (Esnd (S Esplit LHb))).
    intros k m1 m2 (Heq, H1).
    simpl; unfold O.eval_op; simpl.
    rewrite <- (@split_append_mem k (Var.btype S) Tbk0 (m1 S) 
     (false, Ut.default k Bitstring_k0) (m1 LHb)) at 1.
    unfold EP1 in H1; simpl in H1; unfold O.eval_op in H1; simpl in H1.
    simpl; rewrite H1; trivial.
  eqobsrel_tail; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 (H1, _);
   mem_upd_simpl.
   rewrite (H1 _ S), (H1 _ LHb); auto.
  match goal with |- equiv (req_mem_rel ?I ?P) E ?c1 E ?c2 ?Q => 
   assert (forall n:nat, equiv (req_mem_rel I (P /-\ EP2 (Elen LHb_hd_tl =?= n))) E c1 E c2 Q) end.
  Focus 2.
    intros k; assert (W1 := fun n => H n k); clear H.
    apply choice in W1; destruct W1 as (f1, H).
    exists (fun m1 m2 => f1 (E.eval_expr (Elen LHb_hd_tl) m2) m1 m2).
    intros m1 m2 (H1, H2); apply (H (E.eval_expr (Elen LHb_hd_tl) m2) m1 m2).
    split; [trivial | split; [trivial | ] ].
    unfold EP2; simpl; unfold O.eval_op; simpl; apply Ti_eqb_refl.

  induction n0.
  (**** Case n0 = 0 *****)
  ep_eq_r LHb_hd_tl (Nil Tnk1bk0).
    unfold EP2; intros k m1 m2 (H1, (H2, H3)); generalize H3; clear H3.
    simpl; unfold O.eval_op; simpl; destruct (m2 LHb_hd_tl); [trivial | intro; discriminate].
  apply equiv_trans_eq_mem_l with (EP1 (! (LHb_tl =?= Nil _))) E
    (sample_body_H LHb_hd LHb_tl ++ [sample_while_H LHb_hd LHb_tl]).
   Focus 3.
     unfold req_mem_rel, EP1, EP2, andR; intros k m1 m2 H; decompose [and] H; clear H.
     change (is_true (negb (E.eval_expr (LHb_tl =?= Nil _) m1))).
     rewrite is_true_negb, <- expr_eval_eq, H4.
     simpl; unfold O.eval_op; simpl; destruct (m2 LHb_hd_tl); discriminate.
  apply equiv_eq_sem_pre; unfold sample_while_H, EP1; intros k m H.
    rewrite deno_while, deno_cond, H; trivial.
  unfold sample_body_H at 1.
  match goal with |- equiv _ _ _ _ (?i1::?i2::?i3::?c) ?Q => change (i1::i2::i3::c) with ([i1; i2; i3]++c);
    apply equiv_trans with (Meq /-\ 
     (EP1 (LHb_tl =?= ((S | Efst (Esnd (S Esplit LHb))) |::| Esnd (Esnd (S Esplit LHb))))))
     Q Q E
     ([ i1; LHb_hd <- LHb_hd |++| (S | LHbS) |::| Nil _; LHb_tl <- Esnd (Esnd (S Esplit LHb)) ] ++ 
      [sample_while_H LHb_hd LHb_tl]) end.
  unfold req_mem_rel; repeat apply decMR_and; auto.
    intros k m1 m2.
    match goal with 
     |- sumbool (?x1 = ?x2) _  => 
      assert (W:=T.i_eqb_spec k (Var.btype LHb_hd) x1 x2); 
       destruct (T.i_eqb k (Var.btype LHb_hd) x1 x2); auto 
    end.
    intros k m1 m2.
    match goal with 
     |- sumbool (?x1 = ?x2) _  => 
      assert (W:=T.i_eqb_spec k (Var.btype LHb_tl) x1 x2); 
       destruct (T.i_eqb k (Var.btype LHb_tl) x1 x2); auto 
    end.
    unfold req_mem_rel, andR, EP1, EP2; intros k m1 m2 H; decompose [and] H; clear H; split; [trivial | ].
    rewrite <- (expr_eval_eq m1 LHb_tl), H4.
    generalize H3; simpl; unfold O.eval_op; simpl.
    rewrite (H0 _ LHb), (H0 _ S); trivial.
    destruct (m2 LHb_hd_tl); [trivial | intro; discriminate].
    apply req_mem_trans.
  eqobs_tl. 
  ep_eq_l LHb_tl ((S | Efst (Esnd (S Esplit LHb))) |::| Esnd (Esnd (S Esplit LHb))).
    intros k m1 m2 (H1, H2); rewrite expr_eval_eq; trivial.
  rewrite proj1_MR; cp_test (Efst (Efst (Esnd (S Esplit LHb)))); deadcode.
  alloc_l rH_aux rH_aux1; ep; deadcode; swap; eqobs_in.
  swap; eqobs_in.
  apply equiv_app with
   (req_mem_rel {{LHbS,S,LHb}}
    ((fun (k : nat) (m1 m2 : Mem.t k) =>
     E.eval_expr LHb_hd m1 = E.eval_expr (LHb_hd_hd |++| (S | LHbS) |::| LHb_tl_hd) m2 /\
     E.eval_expr LHb_tl m1 = E.eval_expr LHb_tl_tl m2))).
  eqobsrel_tail; unfold implMR, req_mem_rel, EP2, andR; simpl; unfold O.eval_op; simpl;
   intros k m1 m2 H; decompose [and] H; clear H.
   rewrite (H0 _ LHb), (H0 _ S), H1; trivial.
   split; intros; mem_upd_simpl; auto.
  eapply equiv_cons; [apply equiv_while | ].
   unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H.
   generalize H3; simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq; trivial.
  eqobsrel_tail.
  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold req_mem_rel, EP1, EP2, andR, notR, upd_para; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H; split.
  mem_upd_simpl.
  rewrite H4. refine (req_mem_update auxH _ H2).
  split; intros; mem_upd_simpl.
  rewrite H0, H4; repeat rewrite app_ass; simpl; auto.
  rewrite H0, H4; repeat rewrite app_ass; simpl; auto.
  apply equiv_trans_eq_mem_l with (EP2 (LHb_tl =?= Nil _)) E (nil ++ [LHb_tl <- Nil _]).
  ep_eq_r LHb_tl (Nil Tnk1bk0).
   intros k m1 m2 (H1, H2); rewrite expr_eval_eq; trivial.
  rewrite proj1_MR; apply equiv_nil.
  eqobs_tl.
  eapply equiv_strengthen; [ | apply equiv_assign_r].
  unfold req_mem_rel, notR, EP1, EP2, upd2, andR; simpl; unfold O.eval_op; simpl;
   intros k m1 m2 H; decompose [and] H; clear H.
  intros ty y; simpl.
  generalize (VarP.Edec.eqb_spec y LHb_hd); destruct (VarP.Edec.eqb y LHb_hd); intros; [ | discriminate].
  inversion H; subst. rewrite (T.inj_pair2 H8), Mem.get_upd_same; trivial.
  unfold req_mem_rel, andR, notR, EP1, EP2; intros k m1 m2 H; decompose [and] H; clear H.
  rewrite <- negb_involutive, is_true_negb; trivial.

  (**** Case n0 = S _ *****)
  apply equiv_trans_eq_mem_l with (EP1 (! (LHb_tl =?= Nil _))) E
    (sample_body_H LHb_hd LHb_tl ++ [sample_while_H LHb_hd LHb_tl]).
   Focus 3.
     unfold req_mem_rel, EP1, EP2, andR; intros k m1 m2 H; decompose [and] H; clear H.
     change (is_true (negb (E.eval_expr (LHb_tl =?= Nil _) m1))).
     rewrite is_true_negb, <- expr_eval_eq, H4.
     simpl; unfold O.eval_op; simpl; destruct (m2 LHb_hd_tl); discriminate.
  apply equiv_eq_sem_pre; unfold sample_while_H, EP1; intros k m H.
    rewrite deno_while, deno_cond, H; trivial.
  match goal with |- equiv ?P _ _ _ ?c _ =>
   apply equiv_trans_eq_mem_r with (EP1 (! (LHb_hd_tl =?= Nil _))) E
    (sample_body_H LHb_hd_hd LHb_hd_tl ++ c) end.
   Focus 3.
     unfold req_mem_rel, EP1, EP2, andR, transpR; intros k m1 m2 H; decompose [and] H; clear H.
     generalize H3; simpl; unfold O.eval_op; simpl; destruct (m1 LHb_hd_tl); [ | trivial].
     intros W; discriminate W.
  apply equiv_eq_sem_pre; unfold sample_while_H, EP1; intros k m H.
    rewrite deno_cons, deno_while, deno_cond, H, <- deno_app; trivial.
  apply equiv_app with (2:= IHn0).
  eqobsrel_tail.
  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold req_mem_rel, EP1, EP2, andR, notR, upd_para; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H; split.
  mem_upd_simpl.
  rewrite H4. 
   destruct (m2 LHb_hd_tl); [discriminate H3 | simpl].
   refine (req_mem_update auxH _ H0).
  split; intros; mem_upd_simpl;
  (destruct (m2 LHb_hd_tl); [discriminate H3 | rewrite is_true_Ti_eqb in H3; inversion H3; clear H3; subst]).
  rewrite H1, H4; simpl; repeat split; trivial. apply Ti_eqb_refl.
  rewrite H1, H4; simpl; repeat split; trivial. apply Ti_eqb_refl.
 Qed.

 Lemma swap_equiv_SLHb_H : equiv Meq E10r (H_body2r_bad2 ++ SLHb) E10 (SLHb ++ H_body2b_bad2) Meq.
 Proof.
   Transparent app.
  unfold H_body2r_bad2, H_body2b_bad2, H_body2b_gen.
  apply swap_sample_if2.
  apply SLHb_dom.
  (** Not in dom *)
  rewrite proj1_MR.
  union_mod; [trivial | swap; eqobs_tl].
  apply equiv_strengthen with (kreq_mem {{S,S',LHb}}).
  intros k m1 m2 H; rewrite H; trivial.
  match goal with
  |- equiv _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7] _ _ _ => 
    change [i1; i2; i3; i4; i5; i6; i7] with ([i1; i2] ++ ([i3; i4; i5; i6; i7]));
    apply EqObs_trans with E10r ([i1; i2] ++ (split_sample_H ++ [i6; i7])) end.
  apply equiv_app with (req_mem_rel {{rH,S,S',LHb}} (EP1 (S in_dom LHb))).
  eqobsrel_tail; simpl; unfold O.eval_op; simpl.
   intros k m1 m2 H; rewrite Ti_eqb_refl; trivial.
  eqobs_tl_n 2.
  match goal with
  |- equiv _ _ _ _ _ (kreq_mem ?O) => apply equiv_weaken with (req_mem_rel O trueR) end.
  intros k m1 m2 (H1, H2); trivial.
  union_mod.
  eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply sample_split_H] ].
  intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  intros k m1 m2 (H1, H2); split; [apply req_mem_weaken with (2:= H1); vm_compute | ]; trivial.
  alloc LHb LHb1; ep; deadcode; ep; deadcode.
  match goal with |- EqObs _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7] _ _ _ =>
    change [i1; i2; i3; i4; i5; i6; i7] with ([i1; i2; i3] ++ ([i4; i5; i6; i7]));
    apply EqObs_trans with E10r
       ([ i1; LHb_hd <- Nil _; LHb_tl <- LHb ] ++
        [ sample_while_H LHb_hd LHb_tl;
          LHb <- (S | (false | rH)) |::| LHb_hd;
          LHb_hd <- Nil _]) end.
  apply equiv_app with
   (req_mem_rel {{rH,S,S',LHb}}
    (fun k m1 m2 => m1 LHb_tl_tl = m2 LHb_tl /\ m1 LHb_tl_hd = m2 LHb_hd)).
  eqobsrel_tail; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; intros;
  mem_upd_simpl.
  split; [apply (H _ LHb) | ]; trivial.
  eapply equiv_cons; [apply equiv_while | ].
  intros k m1 m2 (H1, (H2, H3)); simpl; unfold O.eval_op; simpl; rewrite H2; trivial.
  eqobsrel_tail; eapply equiv_strengthen; [ | apply equiv_assign].
  unfold EP1, EP2, upd_para; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 ((H1, (H2, H3)), (H4, H5)).
  red; split.
  rewrite H2; apply req_mem_update with (d:=auxH) (1:= H1).
  split; intros; mem_upd_simpl;
    rewrite H2, H3; auto.
  eqobs_tl_n 1.
  match goal with |- equiv ((req_mem_rel ?I _) /-\ _)  _ [?i1; ?i2] _ ?c _ => 
   change c with (nil ++ c); change [i1; i2] with ([i1]++[i2]);
   apply equiv_app with (req_mem_rel (Vset.add LHb_tl I) 
        (fun k m1 m2 => m1 LHb_tl_hd = m2 LHb_hd))
  end.
  eapply equiv_strengthen; [ | apply equiv_assign_l].
    intros k m1 m2 ((H1, (H2, H3)), (H4, H5)); split.
    replace m2 with (m2 {! LHb_tl <-- E.eval_expr (Nil _) m1!}).
    apply req_mem_update; trivial.
    apply Mem.eq_leibniz; intros (ty,y); destruct (Var.eq_dec LHb_tl y).
    inversion e; simpl; rewrite Mem.get_upd_same; symmetry.
    unfold notR, EP2 in H5; simpl in H5; unfold O.eval_op in H5; simpl in H5.
    rewrite <- is_true_negb, negb_involutive, is_true_Ti_eqb in H5; trivial.
    rewrite Mem.get_upd_diff; trivial.
    rewrite Mem.get_upd_diff; trivial; discriminate.
  eapply equiv_strengthen; [ | apply equiv_assign ].
    intros k m1 m2 (H1, H2); red.
    match goal with |- kreq_mem _ (_{! _ <-- ?x!})(_{! _ <-- ?y!}) => replace x with y end.
    eapply req_mem_weaken; [ | apply req_mem_update with (1:= H1) ].
    vm_compute; trivial.
  simpl; unfold O.eval_op; simpl. rewrite (H1 _ S), (H1 _ rH), H2; trivial.
  match goal with |- EqObs _ _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7] _ =>
   apply EqObs_trans with E7 [i1; i2; i3; i4; i6; i7; i5] end.
  eqobs_tl; ep; deadcode; swap; eqobs_in.
  eqobs_hd; swap; eqobs_in.
  2: intros k m1 m2 H; rewrite H; trivial.
  (* R in Dom *)
  union_mod; [rewrite proj1_MR; trivial | ].
  ep; swap; eqobs_tl.
  apply equiv_strengthen with (Meq /-\ EP1 (S in_dom LHb)).
    unfold notR, EP1; intros k m1 m2 (H1, H2); split; trivial.
    rewrite <- is_true_negb in H2; rewrite <- negb_involutive; trivial.
  match goal with |- equiv ?P _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6] _ _ ?Q =>
    apply equiv_trans with P Q Q E10r ([i1] ++ split_sample_H ++ [i5; i6]) end.
  auto. intros k m1 m2 (H1, H2); split; trivial. apply req_mem_trans. 
  apply equiv_cons with (req_mem_rel {{bad2,rH,S,S',LHb}} (EP1 (S in_dom LHb))).
  eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl; intros k m1 m2 (H1, H2); split; intros; trivial.
  generalize H2; clear.
  induction (m1 LHb); simpl; [intro; discriminate | ].
  destruct a; simpl.
  case_eq (T.i_eqb k (Var.btype S) (m1 S) p); simpl; 
   intros H2 H4; rewrite H2; auto.
  repeat split; intros; simpl; rewrite existsb_upd_same; trivialb.
  eqobs_tl_n 2.
  match goal with
  |- equiv _ _ _ _ _ (kreq_mem ?O) => 
   apply equiv_weaken with (req_mem_rel O trueR) 
  end.
  intros k m1 m2 (H1, H2); trivial.
  union_mod.
  eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply sample_split_H] ].
  intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  intros k m1 m2 (H1, H2); split; [apply req_mem_weaken with (2:= H1); vm_compute | ]; trivial.
  match goal with |- equiv ?P _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6] ?Q =>
    apply equiv_trans_r with P Q Q E10 (split_sample_H ++ [i4; i5; i6]) end.
  auto. intros k m1 m2 (H1, H2); split; trivial. rewrite <- H1; trivial. apply req_mem_trans.
  Focus 2.
    eqobs_tl.
    match goal with |- equiv _ _ _ _ _ (kreq_mem ?O) => apply equiv_weaken with (req_mem_rel O trueR) end.
    intros k m1 m2 (H1, H2); trivial.
    apply equiv_strengthen with (req_mem_rel {{LD,LG,bad2,S,S',R',LHb}} (EP1 (S in_dom LHb))).
    intros k m1 m2 (H1, H2); rewrite <- H1; split; auto.
    union_mod.
    apply equiv_sym; auto.
    unfold EP1; split; intros k m1 m2 (H1, H2); (split; [apply req_mem_sym; trivial | ]);
    unfold is_true; rewrite <- H2; simpl; unfold O.eval_op; simpl; rewrite (H1 _ S), (H1 _ LHb); trivial.
    eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply sample_split_H] ].
    intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
    intros k m1 m2 (H1, H2); split; [apply req_mem_weaken with (2:= H1); vm_compute | ]; trivial.
  ep_eq LHb (Efst (S Esplit LHb) |++| (S | Efst (Esnd (S Esplit LHb))) |::| Esnd (Esnd (S Esplit LHb))).
    intros k m1 m2 (Heq, H1); rewrite <- Heq.
    simpl; unfold O.eval_op; simpl.
    rewrite <- (@split_append_mem _ (Var.btype S) Tbk0 (m1 S) 
      (false, (Ut.default k Bitstring_k0)) (m1 LHb)) at 1 5.
    unfold EP1 in H1; simpl in H1; unfold O.eval_op in H1; simpl in H1; simpl; rewrite H1; auto.
  match goal with |- equiv _ _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8; ?i9; ?i10; ?i11; ?i12] _ => 
    change [i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12] with (([i1; i2] ++ [i3]) ++[i4; i5; i6; i7; i8; i9; i10; i11; i12]);
    apply equiv_trans_eq_mem_r with trueR E10 
    ( ([ LHb_hd_hd <- Nil _; LHb_hd_tl <- Efst (S Esplit LHb)] ++
       [sample_while_H LHb_hd_hd LHb_hd_tl])  ++
     [i4] ++ 
     sample_true_H LHb_tl_hd LHb_tl_tl (Esnd (Esnd (S Esplit LHb))) ++
     [i8; i9; i11;
       If Efst LHbS then [
        rH <- Esnd LHbS;
        If E.Eexists tc
             (E.Eop O.Oand
                {S =?= Efst (ap_finv Esnd (tc)),
                E.Eop O.Oor
                  {Esnd (ap_finv Esnd (tc))
                   |x| Esnd (LHbS)
                   in_dom LG,
                  R' =?=
                  Esnd (ap_finv Esnd (tc))
                  |x| Esnd (LHbS)} })
             LD
        _then [bad2 <- true];
        LHb <- LHb_hd_hd |++| (S | (false | Esnd LHbS)) |::| LHb_tl_hd
       ] else [
        rH <- Esnd LHbS;
        i10
       ]
     ]) end.
   3: red; red; trivial.
   apply equiv_app with (Meq /-\ ~-EP1 (S in_dom LHb_hd_hd)).
   apply equiv_app with (Meq /-\ ~-EP1 (S in_dom LHb_hd_hd) /-\ ~-EP1 (S in_dom LHb_hd_tl)).
   rewrite proj1_MR; union_mod; trivial.
   eqobsrel_tail; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; split.
   rewrite <- is_true_negb; trivial.
   rewrite not_is_true_false; refine (@existsb_fst_split k BS_nk1 Tbk0 _ _).
   eapply equiv_weaken; [ | apply equiv_while].
   unfold andR; intuition.  intros k m1 m2 (Heq, _); rewrite Heq; trivial.
   union_mod. rewrite proj1_MR, proj1_MR; trivial.
   eqobsrel_tail; unfold EP1, EP2, andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
    decompose [and] H; clear H.
   red in H0; subst. destruct (m2 LHb_hd_tl); [discriminate | simpl in *].
   apply not_is_true_false in H1.
   destruct i; split; intros; rewrite existsb_app;
   change (T.interp k Tnk1bk0) with 
    (T.interp k BS_nk1 *T.interp k Tbk0)%type;
   rewrite H1; simpl in *;
    destruct (T.i_eqb k BS_nk1 (m2 S) p); simpl in *; split; trivial.
   elim H4; trivial. discriminate. elim H4; trivial. discriminate.
   ep_eq_l (S in_dom LHb_hd_hd) false.
    unfold notR, EP1; intros k m1 m2 (H1, H2); rewrite not_is_true_false in H2; trivial.
   rewrite proj1_MR; union_mod; trivial.
   apply equiv_strengthen with  
     (kreq_mem {{bad2,LD,LG,LHb,S,rH_aux1,LHb_tl_hd,LHb_tl_tl,auxH,rH_aux,R',LHb_tl,LHb_hd_hd}}).
   intros k m1 m2 H; rewrite H; trivial.
   eqobs_hd.
   cp_test (Efst LHbS); ep; deadcode; swap; eqobs_in.
   alloc LHb LHb1.
   swap; eqobs_tl.
   cp_test Efst (Efst (Esnd (S Esplit LHb))); ep; deadcode; ep; deadcode.
   alloc_r rH_aux1 rH; ep; deadcode.
   swap; eqobs_in.
   ep_eq_r (Efst (Efst (Esnd (S Esplit LHb)))) false.
     unfold notR, EP2; intros k m1 m2 (H1, (H2, H3)); rewrite not_is_true_false in H3; trivial.
   swap; eqobs_in.
 Qed.

 Definition swi10_G : forall tg g, 
  option (sw_info SLHb XSLHb ISLHb E10r E10 tg g) :=
  let i := add_sw_info_refl SLHb XSLHb ISLHb E10r E10 
   (Modify_SLHb E10r) (Modify_SLHb E10) 
   (EqObs_SLHb E10r E10) IXSLHb_global (fun t f => None) _ G in
   add_sw_info SLHb XSLHb ISLHb E10r E10 (Modify_SLHb E10r) (Modify_SLHb E10) 
     (EqObs_SLHb E10r E10) IXSLHb_global i _ H swap_equiv_SLHb_H.

 Definition iE10r := iEiEi H_body2r_bad2 G_body2 Dec_body10r.

 Definition iE10 := iEiEi H_body2b_bad2 G_body2 Dec_body10.

 Definition M10 := Eval vm_compute in 
  get_option (modify (refl1_info iE10r) Vset.empty Dec_body10r).

 Lemma M10_E10 : Modify E10 M10 Dec_body10.
 Proof. apply modify_correct with (refl1_info iE10) Vset.empty; vm_compute; trivial. Qed.

 Lemma M10_E10r : Modify E10r M10 Dec_body10r.
 Proof. apply modify_correct with (refl1_info iE10r) Vset.empty; vm_compute; trivial. Qed.

 Lemma swap_equiv_Hbaddr : forall E1 E2, equiv Meq E1
   ((Hbaddr true s ++ [mn <- (false | one_n)])++ SLHb) E2
   (SLHb ++ (Hbaddr true s++ [mn <- (false | one_n)]))
   (kreq_mem
      (Vset.union (Vset.union (get_globals (Vset.union M10 M10)) XSLHb)
         (fv_expr (proc_res E10r Dec)))).
 Proof.
  intros EE1 EE2; ep; swap; eqobs_tl.
  apply equiv_strengthen with (kreq_mem {{LD,LG,Dc,bad,s,S',LHb}}).
  intros k m1 m2 H; rewrite H; trivial.
  match goal with
  |- equiv _ _ [?i1; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8] _ _ _ =>
    apply EqObs_trans with EE1 
      [S <- s; i1; LHb <- (S | (true | rH)) |::| LHb; i4; i5; i6; i7; i8] end.
  ep; deadcode; eqobs_in.
  match goal with
  |- EqObs _ _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7] _ =>
    apply EqObs_trans with EE2 
      [S <- s; i1; i2; i3; i4; i5; i6; LHb <- (S | (true | rH)) |::| LHb] end.
  2: ep; deadcode; eqobs_in.
  eqobs_hd_n 1.
  match goal with
  |- EqObs ?I _ [?i1; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8] _ _ _ =>
    change [i1; i3; i4; i5; i6; i7; i8] with ([i1; i3] ++ ([i4; i5; i6; i7; i8]));
    apply EqObs_trans with EE1 ([i1; i3] ++ (split_sample_H ++ [i7; i8]));
    [ apply equiv_app with (req_mem_rel (Vset.add rH I) (EP1 (S in_dom LHb)))
    | ]
  end.
  eqobsrel_tail; simpl; unfold O.eval_op; simpl.
   intros k m1 m2 H; rewrite Ti_eqb_refl; trivial.
  eqobs_tl_n 2.
  match goal with
  |- equiv _ _ _ _ _ (kreq_mem ?O) => apply equiv_weaken with (req_mem_rel O trueR) end.
  intros k m1 m2 (H1, H2); trivial.
  union_mod.
  eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply sample_split_H] ].
  intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  intros k m1 m2 (H1, H2); split; [apply req_mem_weaken with (2:= H1); vm_compute | ]; trivial.
  alloc LHb LHb1; ep; deadcode; ep; deadcode.
  alloc_l rH_aux1 rH; ep; deadcode. 
  match goal with |- EqObs ?I _ [?i1; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8] _ _ _ =>
    change [i1; i3; i4; i5; i6; i7; i8] with ([i1; i3; i4] ++ ([i5; i6; i7; i8]));
    apply EqObs_trans with EE1 
       ([ i1; LHb_hd <- Nil _; LHb_tl <- LHb ] ++
        [ sample_while_H LHb_hd LHb_tl;
          LHb <- (S | (true | rH)) |::| LHb_hd;
          LHb_hd <- Nil _]);
    [ apply equiv_app with
     (req_mem_rel (Vset.add rH I)
       (fun k m1 m2 => m1 LHb_tl_tl = m2 LHb_tl /\ m1 LHb_tl_hd = m2 LHb_hd))
    | ]
  end.
  eqobsrel_tail; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; intros;
  mem_upd_simpl.
  split; [apply (H _ LHb) | ]; trivial.
  eapply equiv_cons; [apply equiv_while | ].
  intros k m1 m2 (H1, (H2, H3)); simpl; unfold O.eval_op; simpl; rewrite H2; trivial.
  eqobsrel_tail; eapply equiv_strengthen; [ | apply equiv_assign].
  unfold EP1, EP2, upd_para; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 ((H1, (H2, H3)), (H4, H5)).
  red; split.
  rewrite H2; apply req_mem_update with (d:=auxH) (1:= H1).
  split; intros; mem_upd_simpl;
    rewrite H2, H3; auto.
  eqobs_tl_n 1.
  match goal with |- equiv ((req_mem_rel ?I _) /-\ _)  _ [?i1; ?i2] _ ?c _ => 
   change c with (nil ++ c); change [i1; i2] with ([i1]++[i2]);
   apply equiv_app with (req_mem_rel (Vset.add LHb_tl I) 
        (fun k m1 m2 => m1 LHb_tl_hd = m2 LHb_hd))
  end.
  eapply equiv_strengthen; [ | apply equiv_assign_l].
    intros k m1 m2 ((H1, (H2, H3)), (H4, H5)); split.
    replace m2 with (m2 {! LHb_tl <-- E.eval_expr (Nil _) m1!}).
    apply req_mem_update; trivial.
    apply Mem.eq_leibniz; intros (ty,y); destruct (Var.eq_dec LHb_tl y).
    inversion e; simpl; rewrite Mem.get_upd_same; symmetry.
    unfold notR, EP2 in H5; simpl in H5; unfold O.eval_op in H5; simpl in H5.
    rewrite <- is_true_negb, negb_involutive, is_true_Ti_eqb in H5; trivial.
    rewrite Mem.get_upd_diff; trivial.
    rewrite Mem.get_upd_diff; trivial; discriminate.
  eapply equiv_strengthen; [ | apply equiv_assign ].
    intros k m1 m2 (H1, H2); red.
    match goal with |- kreq_mem _ (_{! _ <-- ?x!})(_{! _ <-- ?y!}) => replace x with y end.
    eapply req_mem_weaken; [ | apply req_mem_update with (1:= H1) ].
    vm_compute; trivial.
  simpl; unfold O.eval_op; simpl. rewrite (H1 _ S), (H1 _ rH), H2; trivial.
  match goal with |- EqObs _ _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i8] _ =>
   apply EqObs_trans with EE2 [i1; i2; i3; i4; i6; i8; i5] end.
  eqobs_tl; ep; deadcode; swap; eqobs_in.
  eqobs_hd; swap; eqobs_in.
 Qed.

 Definition iE10rE10 := empty_info E10r E10.

 Lemma SLHb_dom_r : forall E (b : bool),
  equiv (Meq /-\ EP1 ((s in_dom LHb) =?= b)) 
  E SLHb 
  E SLHb 
  (Meq /-\ EP1 ((s in_dom LHb) =?= b)).
 Proof.
  unfold SLHb; intros.
  apply equiv_app with (Meq /-\ EP1 ((s in_dom LHb_hd) =?= b)).
  unfold sample_true_H.
  match goal with |- equiv ?P _ [?i1; ?i2; ?i3] _ _ _ =>
   change [i1; i2; i3] with ([i1; i2]++[i3]); apply equiv_app with 
    (Meq /-\ (EP1 ((s in_dom LHb) =?= b) /-\ EP1 ((s in_dom LHb) =?= ((s in_dom LHb_hd) || (s in_dom LHb_tl))))) end.
  union_mod; [ rewrite proj1_MR; auto | ].
  eqobsrel_tail; intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
  split; [exact H2 | apply Ti_eqb_refl].
  eapply equiv_weaken; [ | apply equiv_while].
  intros k m1 m2 ((H1, (H2, H3)), (H4, _)); split; trivial.
  unfold notR, EP1, EP2 in *.
  change (~ negb (E.eval_expr (LHb_tl =?= Nil _) m1)) in H4.
  rewrite <- is_true_negb, negb_involutive in H4.
  rewrite <- (expr_eval_eq m1 ((s in_dom LHb))) in H2.
  rewrite <- (expr_eval_eq m1 (s in_dom LHb)) in H3.
  rewrite <- (expr_eval_eq m1 LHb_tl) in H4.
  rewrite <- (expr_eval_eq m1 ((s in_dom LHb_hd))).
  rewrite <- H2.
  rewrite H3; generalize H4; simpl; unfold O.eval_op; simpl; intros H5; rewrite H5; simpl;
  rewrite orb_false_r; trivial.
  intros k m1 m2 (H1, _); rewrite H1; trivial.
  union_mod; [ rewrite proj1_MR, proj1_MR; auto | ].
  eqobsrel_tail; unfold implMR, EP1, EP2,Meq, andR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; decompose [and] H; clear H.
  rewrite H1; rewrite is_true_Ti_eqb in H4; rewrite H4; subst; clear H1 H4.
  destruct (m2 LHb_tl); [discriminate | simpl].
  split; intros; (split; [trivial | ]);
  rewrite existsb_app, orb_assoc; simpl; rewrite orb_false_r; apply Ti_eqb_refl.
  union_mod; [ rewrite proj1_MR; auto | ].
  eqobsrel_tail; intros k m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
  intros; exact H2.
 Qed.

 Lemma swap_equiv_SLHb_Dec : 
  equiv Meq 
  E10r (Dec_body10r ++ SLHb) 
  E10 (SLHb ++ Dec_body10 ) 
  (kreq_mem
   (Vset.union (Vset.union (get_globals (Vset.union M10 M10)) XSLHb)
    (fv_expr (proc_res E10r Dec)))).
 Proof.
  unfold Dec_body10, Dec_body10r, Dec_body_gen_b_H.
  apply swap_sample_if_Q with XSLHb.
   apply Modify_SLHb. vm_compute; trivial.
  apply equiv_weaken with Meq.
    intros k m1 m2 H; rewrite H; trivial.
  apply check_swap_c_correct with (I:= ISLHb) (pi:= swi10_G).
  apply Modify_SLHb. apply Modify_SLHb. apply EqObs_SLHb.
  vm_compute; trivial.
  match goal with |- 
    equiv _ _ ((?i1::?i2::?i3::?i4::?i5::?c1) ++ _) _ (SLHb ++ (?i1::?i2::?i3::?i4::?i5::?c2)) _ =>
    change (i1::i2::i3::i4::i5::c1) with ([i1; i2; i3; i4; i5]++c1);
    change (i1::i2::i3::i4::i5::c2) with ([i1; i2; i3; i4; i5]++c2) end.
  apply swap_sample_app2.
  swap; union_mod. trivial. eqobs_in.
  union_mod. trivial. eqobs_in.
  apply swap_sample_if2.
  apply SLHb_dom_r.
  ep; deadcode; swap; eqobs_tl.

  (****** The difficult case *****) 
  match goal with |- equiv ?P _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6] _ _ ?Q =>
    change [i1; i2; i3; i4; i5; i6] with ([i1]++[i2; i3; i4; i5; i6]);
    apply equiv_trans with P Q Q E10r ([i1; S <- s] ++ (sample_true_H LHb_hd LHb_tl LHb ++ [i5; i6]))
  end.
  auto. intros k m1 m2 (H1, H2); split; trivial. apply req_mem_trans.
  deadcode. eqobs_in. 
  match goal with |- equiv ?P _ ([?i1; _]++ _ ++[?i5; ?i6]) _ _ ?Q => 
    apply equiv_trans with P Q Q E10r ([i1; S <- s] ++ split_sample_H ++ [i5; i6])
  end.
  auto. intros k m1 m2 (H1, H2); split; trivial. apply req_mem_trans.
  apply equiv_app with 
   (req_mem_rel {{mn,s,S,rH,LD,LG,Dc,bad,S',LHb}} (EP1 (S in_dom LHb))).
  eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; 
   simpl; intros k m1 m2 (H1, H2); repeat split; intros; trivial.
  match goal with |- 
   equiv _ _ _ _ _ (kreq_mem ?O) => 
   apply equiv_app with (req_mem_rel (Vset.remove LHb O) trueR); [ | eqobs_in] 
  end.
  union_mod.
  eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply sample_split_H] ].
  intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  intros k m1 m2 (H1, H2); split; [apply req_mem_weaken with (2:= H1); vm_compute | ]; trivial.

  match goal with |- equiv ?P _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6] ?Q =>
    change [i1; i2; i3; i4; i5; i6] with (nil ++ ([i1; i2; i3; i4; i5]++[i6]));
    apply equiv_trans with P Q Q E10 ([S <- s] ++ ((sample_true_H LHb_hd LHb_tl LHb ++ [i4; i5])++[i6]))
  end.
  auto. intros k m1 m2 (H1, H2); split; trivial. apply req_mem_trans.
  2:deadcode; eqobs_in. 
  match goal with |- equiv ?P _ _ _ (?C0 ++ (_ ++ ?C1) ++ ?C2) ?Q => 
    apply equiv_trans with P Q Q E10 (C0 ++ (split_sample_H ++ C1) ++ C2)
  end.
  auto. intros k m1 m2 (H1, H2); split; trivial. apply req_mem_trans.
  Focus 2.
    apply equiv_app with 
     (req_mem_rel {{s,t,S,rH,LD,LG,Dc,bad,S',R',LHb}} (EP1 (S in_dom LHb))).
    eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl; intros k m1 m2 (H1, H2); intros; trivial.
    eqobs_tl_n 3.
    match goal with |- equiv _ _ _ _ _ (kreq_mem ?O) => apply equiv_weaken with (req_mem_rel O trueR) end.
      intros k m1 m2 (H1, H2); trivial.
    union_mod;  apply equiv_sym; auto.
      unfold EP1; split; intros k m1 m2 (H1, H2); (split; [apply req_mem_sym; trivial | ]);
      unfold is_true; rewrite <- H2; simpl; unfold O.eval_op; simpl; rewrite (H1 _ S), (H1 _ LHb); trivial.
    eapply equiv_weaken; [ | eapply equiv_strengthen; [ | apply sample_split_H] ].
    intros k m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
    intros k m1 m2 (H1, H2); split; [apply req_mem_weaken with (2:= H1); vm_compute | ]; trivial.
  ep_eq LHb (Efst (s Esplit LHb) |++| (s | Efst (Esnd (s Esplit LHb))) |::| Esnd (Esnd (s Esplit LHb))).
    intros k m1 m2 (Heq, H1); rewrite <- Heq.
    simpl; unfold O.eval_op; simpl.
    rewrite <- (@split_append_mem _ (Var.btype s) Tbk0 (m1 s) 
      (false, Ut.default k Bitstring_k0) (m1 LHb)) at 1 5.
    unfold EP1 in H1; simpl in H1; unfold O.eval_op in H1; simpl in H1; simpl; rewrite H1; auto.
  deadcode.
  match goal with |- equiv _ _ _ _ [?i1; ?i2; ?i3; ?i4; ?i5; ?i6; ?i7; ?i8; ?i9; ?i10; ?i11] _ => 
    change [i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11] with (([i1; i2] ++ [i3]) ++[i4; i5; i6; i7; i8; i9; i10; i11]);
    apply equiv_trans_eq_mem_r with trueR E10 
    ( ([ i1; i2] ++
       [sample_while_H LHb_hd_hd LHb_hd_tl])  ++
     [i4] ++ 
     sample_true_H LHb_tl_hd LHb_tl_tl (Esnd (Esnd (s Esplit LHb))) ++
     [i8;
      If Efst LHbS then [mn <- (false | one_n)]
      else [
         If t |x| Esnd (LHbS) in_dom LG then [
            If Esnd (s) |x| Esnd (LG [{t |x| Esnd (LHbS)}]) =?= zero_k1 then [
                  mn <- (true | Efst s |x| Efst (LG[{ t |x| Esnd (LHbS)}]))
            ] else [mn <- (false | one_n)]
         ] else [
           If R' =?= t |x| Esnd (LHbS) _then [bad <- true];
           mn <- (false | one_n)
         ]
      ];
      i9; i10
     ]) end.
   3: red; red; trivial.
   apply equiv_app with (Meq /-\ ~-EP1 (s in_dom LHb_hd_hd)).
   apply equiv_app with (Meq /-\ ~-EP1 (s in_dom LHb_hd_hd) /-\ ~-EP1 (s in_dom LHb_hd_tl)).
   rewrite proj1_MR; union_mod; trivial.
   eqobsrel_tail; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; split.
   rewrite <- is_true_negb; trivial.
   rewrite not_is_true_false; refine (@existsb_fst_split k BS_nk1 Tbk0 _ _).
   eapply equiv_weaken; [ | apply equiv_while].
   unfold andR; intuition.  intros k m1 m2 (Heq, _); rewrite Heq; trivial.
   union_mod. rewrite proj1_MR, proj1_MR; trivial.
   eqobsrel_tail; unfold EP1, EP2, andR,notR; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
    decompose [and] H; clear H.
   red in H0; subst. destruct (m2 LHb_hd_tl); [discriminate | simpl in *].
   apply not_is_true_false in H1.
   destruct i; split; intros; rewrite existsb_app;
   change  (T.interp k Tnk1bk0) with (T.interp k BS_nk1 *T.interp k Tbk0)%type;
   rewrite H1; simpl in *;
    destruct (T.i_eqb k BS_nk1 (m2 s) p); simpl in *; split; trivial.
   elim H4; trivial. discriminate. elim H4; trivial. discriminate.
   ep_eq_l (s in_dom LHb_hd_hd) false.
    unfold notR, EP1; intros k m1 m2 (H1, H2); rewrite not_is_true_false in H2; trivial.
   rewrite proj1_MR; union_mod; trivial.
   apply equiv_strengthen with  
     (kreq_mem {{bad,R',s,r,LD,LG,t,LHb,R,rH_aux1,LHb_tl_hd,LHb_tl_tl,auxH,rH_aux,LHb_tl,LHb_hd_hd}}).
   intros k m1 m2 H; rewrite H; trivial.
   eqobs_hd; swap; eqobs_in.
   cp_test (Efst (Efst (Esnd (s Esplit LHb)))).
   alloc_l LHb LHb1.
   ep; deadcode. ep; deadcode.
   swap. repeat rewrite proj1_MR; eqobs_in.
   swap. eqobs_tl.
   ep_eq_r (Efst (Efst (Esnd (s Esplit LHb)))) false.
     intros k m1 m2 (_, (_, H2)); unfold notR, EP2 in H2.
     apply not_is_true_false in H2; exact H2.
   rewrite proj1_MR; eqobs_in.

  rewrite proj1_MR; apply swap_equiv_Hbaddr.
  intros k m1 m2 Heq; rewrite Heq; trivial.
 Qed.

 Definition swi10 : forall tg g, option (sw_info SLHb XSLHb ISLHb E10r E10 tg g) :=
  let swiD := add_sw_info2 SLHb XSLHb ISLHb E10r E10 (Modify_SLHb E10r) (Modify_SLHb E10) 
    (EqObs_SLHb E10r E10) IXSLHb_global swi10_G _ Dec M10 M10 M10_E10r M10_E10 swap_equiv_SLHb_Dec in
   let swiGA := add_sw_info_refl SLHb XSLHb ISLHb E10r E10 (Modify_SLHb E10r) (Modify_SLHb E10) (EqObs_SLHb _ _) 
            IXSLHb_global swiD _ GAdv in
   let swiA := add_sw_info_Adv SLHb XSLHb ISLHb E10r E10 (Modify_SLHb E10r) (Modify_SLHb E10) (EqObs_SLHb _ _)
            IXSLHb_global swiGA _ A PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _ _ _ _ _) (A_wf_E _ _ _ _) in
   let swiA' := add_sw_info_Adv SLHb XSLHb ISLHb E10r E10 (Modify_SLHb E10r) (Modify_SLHb E10) (EqObs_SLHb _ _)
            IXSLHb_global swiA _ A' PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _ _ _ _ _) (A'_wf_E _ _ _ _) in
    swiA'.

 Lemma equiv_E10_E10r :
  EqObs {{Y',bad2,g_a}} 
  E10 G2b_H 
  E10r (G2b_H ++ SLHb) 
  {{R',bad,bad2,LD,LG,LHb}}.
 Proof.
  apply equiv_trans_eq_mem_r with trueR E10
   (([bad <- false] ++ init1b_H ++ SGR' ++ [S' <- (GR'n | GR'k1)]) ++ (SLHb ++ tail2)).
  2:ep; deadcode iE10; eqobs_in iE10.
  2:red; red; trivial.
  unfold G2b_H.
  replace (([bad <- false] ++ init1b_H ++ SGR' ++ [S' <- (GR'n | GR'k1)] ++ tail2) ++ SLHb) with
   (([bad <- false] ++ init1b_H ++ SGR' ++ [S' <- (GR'n | GR'k1)]) ++ (tail2 ++ SLHb)).
  2: repeat rewrite app_ass; trivial.
  apply equiv_app with Meq.
  rewrite proj1_MR; union_mod; trivial. eqobs_in.
  apply check_swap_c_correct with (I:= ISLHb) (pi:= swi10).
  apply Modify_SLHb. apply Modify_SLHb. apply EqObs_SLHb.
  vm_compute; trivial.
 Qed.

 Definition H_body2r_bad2' :=
  [ 
   If (Elen LD <=! qD) && (Elen LG <=! qG) then H_body2r_bad2
   else [rH <$- {0,1}^k0] 
  ].

 Definition E10r' := mkEnv H_body2r_bad2' G_body2 Dec_body10r.

 Fixpoint no_double_H k (l:T.interp k T_assoc_b_H) :=
  match l with
  | nil => true
  | a :: l =>
    andb
    (negb (existsb (fun b => T.i_eqb k BS_nk1 (fst a) (fst b)) l)) 
    (no_double_H l)
  end.

 Lemma no_double_upd_H : forall k v v1 i, 
  no_double_H (O.upd (T.i_eqb k BS_nk1) v1 (false, v) i) =
  no_double_H i.
 Proof.
  induction i; simpl no_double_H; intros; trivial.
  destruct a.
  case_eq (T.i_eqb k BS_nk1 v1 i0); simpl; trivial.
  intros; apply f_equal2; [apply f_equal | trivial].
  refine (@existsb_upd_diff k BS_nk1 Tbk0 _ _ _ _ _).
  rewrite <- not_is_true_false, is_true_Ti_eqb in H; auto.
 Qed.


 Definition No_double_LHb : mem_rel := 
  fun k m1 m2 => no_double_H (m2 LHb).

 Definition inv_qD_qG := EP2 (((Elen LD <=! qD) && (Elen LD =?= Dc)) &&
                             ((Gc <=! qG) && (Elen LG <=! Gc))). 

 Definition inv_qD_LHb := inv_qD_qG  /-\ No_double_LHb.

 Lemma dec_No_double_LHb : decMR No_double_LHb.
 Proof.
  red; intros; unfold No_double_LHb.
  destruct (no_double_H (y LHb)); [left; trivial | right; discriminate].
 Qed.

 Lemma dep_No_double_LHb : depend_only_rel No_double_LHb Vset.empty {{LHb}}.
 Proof.
  red; intros; unfold No_double_LHb.
  rewrite <- (H0 _ LHb); trivial.
 Qed.
 
 Lemma dec_inv_qD_H : decMR inv_qD_LHb.
 Proof.
  unfold inv_qD_LHb, inv_qD_qG; auto using dec_No_double_LHb.
 Qed.

 Lemma dep_inv_qD_H : depend_only_rel inv_qD_LHb (Vset.union Vset.empty Vset.empty)
  (Vset.union (fv_expr (((Elen LD <=! qD) && (Elen LD =?= Dc)) &&
   ((Gc <=! qG) && (Elen LG <=! Gc))))
  {{LHb}}).
 Proof.
  unfold inv_qD_LHb, inv_qD_qG; auto using dep_No_double_LHb.
 Qed.

 Definition eE10rE10r' :=
  @empty_inv_info inv_qD_LHb _ _ dep_inv_qD_H (refl_equal true) 
  dec_inv_qD_H E10r E10r'.

 Lemma EqObs_GAdv_10r_10r' :
  EqObsInv inv_qD_LHb 
  {{Gc,Radv,R',LD,bad,LG}}
  E10r GAdv_body1 
  E10r' GAdv_body1 
  {{Gc,bad,rGadv,LG}}.
 Proof. 
  inline eE10rE10r' G. auto using dec_inv_qD_H.
  ep; deadcode eE10rE10r'.
  cp_test (qG <=! Gc).
  rewrite proj1_MR; eqobs_in eE10rE10r'.
  cp_test (Radv in_dom LG).
  eqobs_tl eE10rE10r'.
  Opaque leb.
  unfold inv_qD_LHb, inv_qD_qG; eqobsrel_tail; unfold EP1, EP2, andR, notR, No_double_LHb; simpl;
   unfold O.eval_op; simpl; intros k m1 m2 H; decompose [and] H; clear H.
   mem_upd_simpl.
   split; [ | trivial].
  repeat rewrite is_true_andb in *; decompose [and] H1; clear H1; repeat split; trivial.
  rewrite is_true_leb in H6 |- *; omega'.
  rewrite is_true_leb in H10 |- *; omega'.
  eqobs_tl eE10rE10r'.
  unfold inv_qD_LHb, inv_qD_qG; eqobsrel_tail; unfold EP1, EP2, andR, notR, No_double_LHb; simpl;
   unfold O.eval_op; simpl; intros k m1 m2 H; decompose [and] H; clear H.
   split; intros; mem_upd_simpl;
   (split; [ | trivial]).
  repeat rewrite is_true_andb in *; decompose [and] H1; clear H1; repeat split; trivial.
  rewrite is_true_leb in H6 |- *; omega'.
  repeat rewrite is_true_andb in *; decompose [and] H1; clear H1; repeat split; trivial.
  rewrite is_true_leb in H6 |- *; omega'.
 Qed. 

 Lemma EqObs_H_10r_10r' :
  EqObsInv inv_qD_LHb 
  {{S,R',LD,LHb,bad2,LG}}
  E10r H_body2r_bad2 
  E10r' H_body2r_bad2' 
  {{bad2,rH,LHb}}.
 Proof.
   ep_eq_r  ((Elen LD <=! qD) && (Elen LG <=! qG))true.
     unfold inv_qD_LHb, inv_qD_qG, EP2; simpl; unfold O.eval_op; simpl.
     intros k m1 m2 (_, (H, H0)); repeat rewrite is_true_andb in H; decompose [and] H; clear H.
     rewrite H3; simpl; match goal with |- ?x = _ => change (is_true x) end.
     rewrite is_true_leb in H1, H5 |- *; omega'.
   unfold inv_qD_LHb, inv_qD_qG; eqobsrel_tail; unfold andR, notR; simpl; unfold O.eval_op; simpl;
     intros k m1 m2 H; decompose [and] H.
   unfold No_double_LHb in *; repeat split; intros; trivial;
   mem_upd_simpl; trivial.
   simpl. rewrite H3, andb_true_r; destruct H1; trivial.
   unfold is_true; rewrite <- H3; apply no_double_upd_H.
   unfold is_true; rewrite <- H3; apply no_double_upd_H.
 Qed.  

 Lemma EqObs_Dec_10r_10r' :
  EqObsInv inv_qD_LHb 
  (Vset.add LD (Vset.add LHb (Vset.remove LH ID)))
  E10r Dec_body10r
  E10r' Dec_body10r
  (Vset.add LD (Vset.add LHb (Vset.remove LH OD))).
 Proof.
  unfold Dec_body10r, Dec_body_gen_b_H.  
  cp_test (E.Eop O.Oor {testD, qG <! (Elen LG)}).
  rewrite proj1_MR; eqobs_in eE10rE10r'.
  match goal with |- equiv _ _ (?i1::?i2::?c) _ _ _ =>
   change (i1::i2::c) with ([i1; i2]++c) end.
  apply equiv_app with (req_mem_rel (Vset.add LD (Vset.add LHb (Vset.remove LH ID))) inv_qD_LHb).
  rewrite req_mem_rel_assoc; unfold inv_qD_LHb, inv_qD_qG; eqobsrel_tail.
  Opaque leb.
   unfold EP2, testD, andR, notR; simpl; unfold O.eval_op; simpl.
   intros k m1 m2 H; decompose [and] H; split.
   repeat rewrite is_true_orb in H5; repeat rewrite is_true_leb in *.
   repeat rewrite is_true_andb in H1; rewrite is_true_Ti_eqb in H1.
   decompose [and] H1; clear H1.
   rewrite H3, H9, H8, Ti_eqb_refl, andb_true_r, andb_true_r.
   rewrite is_true_leb; omega'.
   unfold No_double_LHb in *;
   mem_upd_simpl; trivial.
   cp_test (Efst (ap_finv c) in_dom LHb).
   rewrite proj1_MR; eqobs_in eE10rE10r'.
   ep; deadcode eE10rE10r'; eqobs_tl eE10rE10r'.
   rewrite req_mem_rel_assoc; unfold inv_qD_LHb, inv_qD_qG; eqobsrel_tail.
   unfold andR, EP2, notR; simpl; unfold O.eval_op;
    simpl; intros k m1 m2 H; decompose [and] H.
   unfold  No_double_LHb in *; split; trivial;
     mem_upd_simpl; trivial.
   rewrite not_is_true_false in H5. simpl.
   rewrite H4, andb_true_r, is_true_negb, not_is_true_false; trivial.
 Qed.  

 Definition iE10r' := iEiEi H_body2r_bad2' G_body2 Dec_body10r.

 Definition iE10rE10r' :=
  let RM := Vset.empty in
  let piGA := my_add_info GAdv RM RM iE10r iE10r' eE10rE10r'
   EqObs_GAdv_10r_10r' in 
  let piH := my_add_info H RM RM iE10r iE10r' piGA EqObs_H_10r_10r' in
  let piD := my_add_info Dec RM RM iE10r iE10r' piH EqObs_Dec_10r_10r' in
   adv_info piD.

 Section PR_10_bad2.

  Variable k : nat.

  Definition testLHb (m:Mem.t k) (v:T.interp k (T.Pair T.Bool BS_k)) : bool :=
   EP k 
    (let c := Esnd (tc) in
     let s := Efst (ap_finv c) in
      ((s in_dom LHb) && !(Efst (LHb [{s}]))))
    (m{!tc <-- v!}).

  Definition testR_H (m:Mem.t k) (v:T.interp k (T.Pair T.Bool BS_k)) : bool := 
    EP k
    (let c := Esnd (tc) in
     let s := Efst (ap_finv c) in
      (S =?= s))
    (m{!tc <-- v!}).

  Definition bad2_K_H (mn':Mem.t k) :=
   (charfun (EP k bad2) mn' +
   (qD_poly k - length (filter (testLHb mn') (mn' LD)) */ 
    ((qG_poly k+1)/2^k0 k)))%U.

  Definition dep_bad2_K_H := {{bad2,LHb,LD}}.

  Lemma dep_bad2_K_H_correct : depend_only_f bad2_K_H dep_bad2_K_H.
  Proof.
   intros m1 m2 H.
   unfold bad2_K_H, testLHb, charfun, restr, EP; simpl; unfold O.eval_op; simpl.
   rewrite (H _ bad2); trivial. apply Uplus_eq_compat; trivial.
   apply Nmult_eq_compat_left; trivial.
   apply f_equal. apply f_equal.
   rewrite (H _ LD); trivial; apply filter_morph; intros.
   mem_upd_simpl;
   rewrite (H _ LHb); trivial.
  Qed.

  Definition epr10 : PrBad_info E10r' bad2_K_H.
   refine (@Build_PrBad_info k E10r' bad2_K_H _ dep_bad2_K_H_correct _ 
    (fun _ _ => false) _).
   abstract (apply Vset.forallb_correct; 
    [ intros x y Heq; rewrite Heq; trivial | vm_compute; trivial]).
   abstract (intros; discriminate).
  Defined.

  Lemma inv_bad10r_H : inv_bad E10r' bad2_K_H H_body2r_bad2'.
  Proof.
   unfold H_body2r_bad2', H_body2r_bad2, H_body2b_gen.
   apply EqObs_inv_bad with (1:= dep_bad2_K_H_correct) 
    (I:= Vset.add R' (Vset.add S (Vset.add LG dep_bad2_K_H)))
    (c:= [
     If (Elen LD <=! qD) && (Elen LG <=! qG) _then [
     If !(S in_dom LHb)  then Hbaddr false S
     else [
        If Efst (LHb [{S}]) _then 
           [rH <$- {0,1}^k0] ++
           [If test_exists_H _then [bad2 <- true] ] ++
           [LHb <- LHb Upd S <| (false | rH)]
     ] ] ]).
   deadcode. eqobs_in.
   unfold inv_bad; intros; rewrite deno_cond_elim.
   match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Hl end.
   2: rewrite deno_nil_elim; trivial.
   rewrite deno_cond_elim.
   match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Heq end.
   unfold Hbaddr.
   rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   transitivity 
    (mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))
        (fcte _ (bad2_K_H m))); [apply mu_monotonic; intros v1| apply mu_cte_le].
   rewrite deno_assign_elim; unfold fcte, bad2_K_H, fplus, Fmult.
   apply Uplus_le_compat.
   unfold charfun, restr, EP; simpl; unfold O.eval_op; simpl;
   mem_upd_simpl;
   trivial. 
   apply Nmult_le_compat; trivial.
   refine (minus_le_compat_l _ _ _ _).
   mem_upd_simpl.
   generalize (m LD).
   Opaque E.eval_expr.
   induction i; simpl; trivial.
   case_eq (testLHb m a); intros.
   match goal with |- context [(if ?x then _ else _)] => 
     replace x with true end.
    simpl; apply le_n_S; trivial.
    symmetry; match goal with |- ?x = true =>
      change (is_true x); change (is_true (testLHb m a)) in H end.
  Transparent E.eval_expr.
    generalize H; clear H; unfold testLHb, EP; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
    intros H; repeat rewrite is_true_andb in H; decompose [and] H.
    simpl. rewrite H0.
    unfold O.assoc at 1; simpl.
    match goal with |- context [(if ?x then _ else _)] => case_eq x; intros end; trivial.
  match goal with |- context [(if ?x then _ else _)] => destruct x end;
   simpl; auto using le_S. 
  rewrite deno_cond_elim.
  match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Heq0 end.
  simpl app.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  case_eq (EP k bad2 m); intros Heq1; repeat Usimpl; trivial.
  unfold bad2_K_H, charfun, restr, fone; rewrite Heq1; repeat Usimpl; trivial.
  transitivity
    (mu
      (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))
      (fplus
         (fun v2 => charfun (EP k test_exists_H) (m{!rH<--v2!}))
         (fcte _ 
           ((qD_poly k - ((length (filter (testLHb m) (m LD)) + 
                     length (filter (testR_H m) (m LD)))))*/(qG_poly k + 1)/2^k0 k)%U))).
  apply mu_monotonic; intros v2; unfold fplus, fcte.
  rewrite deno_cons_elim, Mlet_simpl, deno_cond_elim.
  match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Heq2 end.
  unfold charfun, restr, fone, EP. rewrite Heq2; repeat Usimpl; trivial.
  rewrite deno_nil_elim, deno_assign_elim; unfold bad2_K_H.
  apply Uplus_le_compat; trivial.
  generalize Heq1; unfold charfun, restr, EP; simpl; unfold O.eval_op; simpl.
    mem_upd_simpl.
   intros W; rewrite W; trivial.
  apply Nmult_le_compat_left; trivial.
  refine (minus_le_compat_l _ _ _ _).
  simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
  generalize (m LD). 
  induction i; simpl; trivial.
  match goal with |- _ <= length (if ?x then _ else _) => 
      case_eq x; intros Heq3; [change (is_true x) in Heq3 | ] end.
  case_eq (testLHb m a); intros Heq4; [change (is_true (testLHb m a)) in Heq4 | ].
  replace (testR_H m a) with false.
  simpl; omega'.
  symmetry; rewrite <- not_is_true_false; generalize Heq4 Heq0 Heq; clear Heq4 Heq0 Heq.
  unfold testLHb, testR_H, EP; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  repeat rewrite is_true_andb; rewrite is_true_Ti_eqb; intros (W1,W2) W4 W7 W5.
  rewrite <- W5, is_true_negb in W2. apply W2; trivial.
  case_eq (testR_H m a); intros; simpl; omega'.
  assert (~(testLHb m a \/ testR_H m a)).
    generalize Heq3 Heq0 Heq; clear IHi Heq3 Heq0 Heq; rewrite <- not_is_true_false.
     unfold testLHb, testR_H, EP; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
     repeat rewrite is_true_andb; rewrite is_true_Ti_eqb; intros W1 W2 W8.
     intros [(W3,W4) | W6]; apply W1.
     match type of W4 with (is_true (negb (fst (O.assoc (T.i_eqb k ?t ?x) _ _)))) =>
      case_eq (T.i_eqb k t x (m S)); intros HH;
      [change (is_true (T.i_eqb k t x (m S))) in HH 
      | rewrite <- not_is_true_false in HH]; rewrite is_true_Ti_eqb in HH end.
     rewrite HH in *; split.
     apply (@existsb_upd_same k BS_nk1 Tbk0).
     rewrite (@assoc_upd_same k UOp.Tnk1 Tbk0); trivial.  
     split.
     rewrite (@existsb_upd_diff k BS_nk1 Tbk0); trivial.
     rewrite (@assoc_upd_diff k BS_nk1 Tbk0); trivial.  
     rewrite W6 in *; split; trivial.
     apply (@existsb_upd_same k BS_nk1 Tbk0).
     rewrite (@assoc_upd_same k BS_nk1 Tbk0); trivial.  
  replace (testLHb m a) with false; [ replace (testR_H m a) with false; trivial | ];
  symmetry; rewrite <- not_is_true_false; intros W; apply H; auto.
  set (QD:= qD_poly k).
  set (FR := filter (testR_H m) (m LD)).
  set (FGb := filter (testLHb m) (m LD)).
  set (LL := length FGb + length FR).
  rewrite mu_le_plus, mu_cte_le. 
  transitivity ((length FR */ (qG_poly k + 1)/2^k0 k) + ((QD - LL)*/ (qG_poly k + 1) /2^k0 k))%U.
  apply Uplus_le_compat; trivial.

  set (def:= T.default k (T.Pair T.Bool BS_k)).
  set (test_exists_body := let c := Esnd (tc) in
   let s := Efst (ap_finv c) in
   let t := Esnd (ap_finv c) in
   let h := rH in
   let r := t |x| h in
   E.Eop O.Oand {S =?= s, E.Eop O.Oor {r in_dom LG, R' =?= r} }).
  transitivity 
    (mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))
         (sigma_fun 
               (fun i v => 
                   charfun (EP k test_exists_body) (m{!tc<--nth i FR def!}{!rH <-- v!}))
               (length FR))).
   apply mu_monotonic; intro v; unfold fplus,sigma_fun.
   unfold charfun at 1; unfold restr.
   match goal with |- context [if ?x then _ else _] =>
     case_eq x; intros Heq2; [change (is_true x) in Heq2 | trivial] end.
   set (ff:= (fun k2 : nat =>
                   charfun (EP k test_exists_body) (m{!tc<--nth k2 FR def!}{!rH <-- v!}))).
   assert (exists i, i < (length FR) /\ 
                        (EP k test_exists_body (m{!tc<--nth i FR def!}{!rH <-- v!}))).
   apply nth_existsb with (f :=
     fun w => EP k test_exists_body (m{!tc<--w!}{!rH <-- v!})). 
   generalize Heq2; unfold FR, test_exists_body; clear.
   unfold EP; simpl; unfold O.eval_op; simpl;
   mem_upd_simpl.
   repeat rewrite is_true_existsb.
   intros (x, (H1, H2)); generalize H2; clear H2;
    mem_upd_simpl.
    repeat rewrite is_true_andb; intros (H2, H3).
    exists x; split.
    rewrite filter_In; split; trivial.
    unfold testR_H, EP; simpl; unfold O.eval_op; simpl.
    mem_upd_simpl; trivial.
    mem_upd_simpl.
    rewrite H2; trivial.

   destruct H as (i, (H1, H2)).
   apply Ole_trans with (2:= sigma_le ff H1).
   unfold ff, charfun, restr. rewrite H2; trivial.
   rewrite mu_sigma_le, Nmult_sigma; apply sigma_le_compat.
   intros k2 Hlt; set (nth2 := nth k2 FR def); rewrite plus_Nmult_distr.
   set (def0:= T.default k (T.Pair BS_k0 BS_nk1)).
   transitivity
    ((mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m)))
      (fplus (sigma_fun (fun i v => charfun (T.i_eqb k BS_k0 v)
                (BVxor (k0 k) (snd (finv (snd nth2))) (fst (nth i (m LG) def0))))
                        (length (m LG)))
             (fun v => charfun (T.i_eqb k BS_k0 v) (BVxor (k0 k) (snd (finv (snd nth2))) (m R'))))).
   apply mu_monotonic; intros v.
   unfold charfun, EP, restr, test_exists_H, fplus; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   match goal with |- context [if ?e then _ else _] =>
     case_eq e; intros Heq2; [change (is_true e) in Heq2 | trivial ] end.
   rewrite is_true_andb, is_true_orb in Heq2; destruct Heq2 as (H1, [H2 | H2]).
   match goal with |- ((_ <= ?x + _)%U)%tord => setoid_replace x with 1%U; [trivial | ] end.
   split; trivial.
   unfold fone; set (ff:= (fun k2 : nat =>
                   charfun (T.i_eqb k BS_k0 v)
                              (BVxor (k0 k) (snd (finv (k:=k) (snd nth2))) (fst (nth k2 (m LG) def0))))).
   assert (exists i, i < (length (m LG)) /\ (T.i_eqb k BS_k0 v
                              (BVxor (k0 k) (snd (finv (k:=k) (snd nth2))) (fst (nth i (m LG) def0))))).
   apply nth_existsb with (f :=
     fun w => (T.i_eqb k BS_k0 v
                              (BVxor (k0 k) (snd (finv (k:=k) (snd nth2))) (fst w)))).
   rewrite is_true_existsb in H2 |- *; destruct H2 as (x, (H2, H3)); exists x; split; trivial.
   rewrite is_true_Ti_eqb in H3; match goal with |- is_true (T.i_eqb _ _ _ (BVxor _ _ ?x)) => 
        match type of H3 with ?y = _ => replace x with y; trivial end end.
   match goal with |- context [BVxor ?k ?x _] =>
     repeat rewrite (@BVxor_comm k x) end. rewrite BVxor_bij; apply Ti_eqb_refl.
   destruct H as (i, (H3, H4)).
   apply Ole_trans with (2:= sigma_le ff H3).
   unfold ff, charfun, restr. rewrite H4; trivial.
   match goal with |-  ((_ <= _ + (if ?x then _ else _))%U)%tord => 
       replace x with true end; unfold fone; trivial.
   rewrite is_true_Ti_eqb in H2; rewrite H2.
   symmetry; match goal with |- context [BVxor ?k ?x _] =>
     repeat rewrite (@BVxor_comm k x) end. rewrite BVxor_bij; apply Ti_eqb_refl.
   rewrite mu_le_plus; apply Uplus_le_compat.
   rewrite mu_sigma_le, Nmult_sigma.
   transitivity (sigma (fun _ : nat => ([1/2] ^ k0 k)%U) (length (m LG))).
   apply sigma_le_compat.
   intros k3 Hlt3.
   apply Oeq_le; apply Pr_bs_support with
    (v:= (BVxor (k0 k) (snd (finv (k:=k) (snd nth2))) (fst (nth k3 (m LG) def0))))
    (f := fun v1 v2 => charfun (T.i_eqb k BS_k0 v2) v1).
   intros x Hdiff; unfold charfun, restr.
   match goal with |- context [(if ?e then _ else _)] => case_eq e; intros Heq4;
    [change (is_true e) in Heq4 | trivial]  end.
   elim Hdiff; rewrite is_true_Ti_eqb in Heq4; trivial.
   unfold charfun, restr; rewrite Ti_eqb_refl; trivial.
   apply sigma_incr.
   generalize Hl; simpl; unfold O.eval_op; simpl.
   match goal with |- ?x = true -> ?y => change ((is_true x) -> y) end.
   rewrite is_true_andb, is_true_leb, is_true_leb. intros (W1, W2); trivial.
 
  apply Oeq_le; apply Pr_bs_support with
    (v:= (BVxor (k0 k) (snd (finv (k:=k) (snd nth2))) (m R')))
    (f := fun v1 v2 => charfun (T.i_eqb k BS_k0 v2) v1).
   intros x Hdiff; unfold charfun, restr.
   match goal with |- context [(if ?e then _ else _)] => case_eq e; intros Heq4;
    [change (is_true e) in Heq4 | trivial]  end.
   elim Hdiff; rewrite is_true_Ti_eqb in Heq4; trivial.
   unfold charfun, restr; rewrite Ti_eqb_refl; trivial.
 
  rewrite Uplus_sym, <- plus_Nmult_distr.
  unfold bad2_K_H,charfun, restr; rewrite Heq1;Usimpl.
  apply Nmult_le_compat; trivial.
  change  (QD - LL + length FR <= QD - length FGb); unfold LL.
  assert ((length FGb + length FR) <= QD); [ | omega'].
  apply le_trans with (length (m LD)).
  unfold FR, FGb; generalize (m LD).
  induction i; simpl; trivial.
  case_eq (testLHb m a); intros.
  replace (testR_H m a) with false.
  simpl; apply le_n_S; trivial.
  symmetry; rewrite <- not_is_true_false; change (is_true (testLHb m a)) in H;
    generalize H Heq0; clear H Heq0.
  unfold testLHb, testR_H, EP; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  repeat rewrite is_true_andb; rewrite is_true_Ti_eqb; intros H1 Heq0 H2;
   decompose [and] H1; clear H1.
  rewrite is_true_negb in H0; apply H0; rewrite <- H2; trivial.
  destruct (testR_H m a).
   simpl; rewrite <- plus_n_Sm; apply le_n_S; trivial.
   apply le_S; trivial.
  match type of Hl with ?x = true => change (is_true x) in Hl end.
  generalize Hl; simpl; unfold O.eval_op; simpl; rewrite is_true_andb, is_true_leb; intuition.
  rewrite deno_nil_elim; trivial.
 Qed.  

  Definition ipr10H := add_prbad (add_prbad_comp epr10 G) H inv_bad10r_H.

  Lemma inv_bad10r_Dec : inv_bad E10r' bad2_K_H Dec_body10r.
  Proof.
   unfold Dec_body10r, Dec_body_gen_b_H.
   apply inv_bad_if.
    apply check_inv_bad_c_correct with epr10. vm_compute; trivial.
   apply EqObs_inv_bad with (1:= dep_bad2_K_H_correct) 
      (I:= Vset.add R' (Vset.add c (Vset.add Ydef dep_bad2_K_H)))
    (c:= [
     st <- ap_finv c;
     s <- Efst (st);
     t <- Esnd (st) ] ++
     [ If s in_dom LHb then [ LD <- (Ydef | c) |::| LD ]
       else [
          rH <$- {0,1}^k0;
          LHb <- (s | (true | rH)) |::| LHb;
          LD <- (Ydef | c) |::| LD
        ]
     ]).
  ep; deadcode.
  cp_test (Efst (ap_finv c) in_dom LHb); rewrite proj1_MR; swap; eqobs_in.
  apply inv_bad_app.
  apply check_inv_bad_c_correct with ipr10H. vm_compute; trivial.
  red; intros; rewrite deno_cond_elim.
  match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Heq end.
  rewrite deno_assign_elim; unfold bad2_K.
  apply Uplus_le_compat.
  unfold charfun, restr, fone, EP; simpl; unfold O.eval_op; simpl;
  mem_upd_simpl;
  trivial.
  apply Nmult_le_compat; trivial.
  refine (minus_le_compat_l _ _ _ _).
  rewrite Mem.get_upd_same.
  assert (forall v, (testLHb (m {!LD <-- E.eval_expr ((Ydef | c) |::| LD) m!})) v =
                    (testLHb m) v).
   intros; unfold testLHb, EP; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl;
   trivial.
  rewrite (filter_morph _ _ H); clear H.
  simpl; unfold O.eval_op; simpl;
   mem_upd_simpl.
  match goal with |- context [(if ?x then _ else _)] => destruct x; trivial end.
  simpl; apply le_S; trivial.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
   transitivity 
    (mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))
        (fcte _ (bad2_K_H m))); [apply mu_monotonic; intros v1| apply mu_cte_le].
   rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim, deno_assign_elim.
   unfold fcte, bad2_K_H, fplus, Fmult.
   apply Uplus_le_compat.
   unfold charfun, restr, EP; simpl; unfold O.eval_op; simpl;
   mem_upd_simpl;
   trivial.
   apply Nmult_le_compat; trivial.
   refine (minus_le_compat_l _ _ _ _).
   simpl; unfold O.eval_op; simpl;
   mem_upd_simpl.
   match goal with |- length (filter ?f1 _) <= length (filter ?f2 _) => 
     assert (forall a, f2 a = f1 a) end.
     intros; unfold testLHb, EP; simpl; unfold O.eval_op; simpl.
     mem_upd_simpl.
     unfold O.assoc at 1; simpl.
     match goal with |- context [orb ?x _] => case_eq x; intros Heq1;
       [change (is_true x) in Heq1 | trivial ] end.
     simpl.
     rewrite is_true_Ti_eqb in Heq1; rewrite Heq1.
     generalize Heq; clear Heq; simpl; unfold O.eval_op; simpl; intros Heq.
     change UOp.Tnk1 with BS_nk1; rewrite Heq; trivial.
     rewrite (filter_morph _ _ H); simpl.
     match goal with |- context [(if ?x then _ else _)] => destruct x; trivial end.
     simpl; apply le_S; trivial.
  Qed.  

  Definition ipr10 :=
   let prD := add_prbad ipr10H Dec inv_bad10r_Dec in
   let prGA := add_prbad_comp prD GAdv in
   let prA := 
    add_prbad_adv prGA (A_wf_E H_body2r_bad2' G_body2 Dec_body10r GAdv_body1) in
    add_prbad_adv prA (A'_wf_E H_body2r_bad2' G_body2 Dec_body10r GAdv_body1).

 End PR_10_bad2.

 Definition test_exists_H_aux := 
  E.Eexists tc
   (let c := Esnd (tc) in
    let s := Efst (ap_finv c) in
    let t := Esnd (ap_finv c) in
    let h := rH_aux in
    let r := t |x| h in
    E.Eop O.Oand {Efst auxH =?= s, E.Eop O.Oor {r in_dom LG, R' =?= r} })
   LD.

 Definition sample_while_H_bad2 := 
  [ while !(LHb_tl =?= Nil _) do [ 
      If Elen LG <=! qG _then [ 
         If !(LHb_tl =?= Nil _) _then [    
            auxH <- Ehd LHb_tl;
            If Efst (Esnd (auxH)) _then [
               rH_aux <$- {0,1}^k0;
               If test_exists_H_aux _then [bad2 <- true];
               auxH <- (Efst auxH | (true | rH_aux))
            ];
            LHb_hd <- LHb_hd |++| auxH |::| Nil _;
            LHb_tl <- Etl LHb_tl
         ]
      ] 
    ]
   ].

 Definition sample_true_H_bad2 :=
  [ LHb_hd <- Nil _; LHb_tl <- LHb ] ++ sample_while_H_bad2.

 Definition Bad1_H_hd := 
   E.Eexists tc
  (let c := Esnd (tc) in
   let s := Efst (ap_finv c) in
   let t := Esnd (ap_finv c) in
   let h := Esnd (LHb_hd [{s}]) in
   let r := t |x| h in
   E.Eop O.Oand
     {E.Eop O.Oand {s in_dom LHb_hd, Efst (LHb_hd [{s}])},
     E.Eop O.Oor {r in_dom LG, R' =?= r} }) LD.

 Lemma SLHb_Bad1_bad2 : 
  equiv
  (req_mem_rel {{R',LD,LHb,bad2,LG}} (EP2 (Elen LG <=! qG)))
  E10r SLHb 
  E10r (sample_true_H_bad2 ++ [LHb <- LHb_hd])
  (req_mem_rel {{LD,LHb,LG}} (EP1 (E.Eop O.Oor {bad2, Bad1_H}) |-> EP2 bad2)).
 Proof.
  ep_eq_r (Elen LG <=! qG) true.
   intros k m1 m2 (_, H); trivial.
  unfold EqObsRel; unfold req_mem_rel at 1; rewrite proj1_MR.
  unfold SLHb.
  match goal with |- equiv _ _ _ _ [?i1;?i2;?i3;?i4] _ => 
   change [i1; i2; i3; i4] with (([i1; i2]++[i3])++ [i4]) end.
  apply equiv_app with 
   (req_mem_rel {{R',LHb_tl,LD,LG,LHb_hd}} (EP1 (bad2 || Bad1_H_hd) |-> EP2 bad2)).
  assert (depend_only_rel (EP1 (bad2 || Bad1_H_hd) |-> EP2 bad2)
   (Vset.union (fv_expr (bad2 || Bad1_H_hd)) Vset.empty)
   (Vset.union Vset.empty (fv_expr bad2))) by auto.
  assert (decMR (EP1 (bad2 || Bad1_H_hd) |-> EP2 bad2)) by auto.
  set (i:= empty_inv_info H (refl_equal true) X E10r E10r).
  ep.
  match goal with |- equiv _ _ [?i1;?i2;?i3] _ [?i4;?i5;?i6] ?Q => 
    change [i1; i2; i3] with ( [i1; i2] ++ [i3] );
    change [i4; i5; i6] with ( [i4; i5] ++ [i6] );
    apply equiv_app with Q end.
  eqobsrel_tail; simpl; unfold O.eval_op; simpl.
  intros k2 m1 m2 H2 H1; rewrite is_true_orb in H1; destruct H1.
  rewrite <- (H2 _ bad2); trivial.
  contradict H0; rewrite is_true_existsb; intros (x, (_, H3)).
  repeat rewrite andb_false_r in H3; discriminate.
  unfold sample_while_H.
  eapply equiv_weaken; [ | apply equiv_while].
   intros k2 m1 m2 (H1, H2); trivial.
   intros k2 m1 m2 (H1, H2); simpl; unfold O.eval_op; simpl.
   rewrite (H1 _ LHb_tl); trivial.
  swap; ep.
  rewrite proj1_MR; cp_test (Efst (Esnd (Ehd LHb_tl))).
  deadcode.
  rewrite req_mem_rel_assoc; match goal with 
   |- equiv (req_mem_rel ?I ?P) _ [?i1;?i2;?i3;?i4] _ [?i6;?i7;?i8;?i9;?i10] ?Q => 
     change [i1; i2; i3; i4] with ([i1]++[i2; i3; i4]);
     change [i6; i7; i8; i9; i10] with ([i6]++[i7; i8; i9; i10]);
     apply equiv_app with (req_mem_rel (Vset.add rH_aux I) P) 
  end.
  eqobsrel_tail; unfold EP1,EP2, andR, impR; simpl; unfold O.eval_op; simpl;
    intros k2 m1 m2 W; decompose [and] W; clear W; split; auto.
  intros W; apply H2; clear H2; rewrite is_true_orb in W |- *; destruct W; auto.
  right; rewrite is_true_existsb in H2 |- *; destruct H2 as (x, (Hin, W));
   exists x; split; trivial.
  mem_upd_simpl;
   trivial.
  match goal with |- equiv _ _ _ _ [If ?e _then _;_;_;_] _ => cp_test_r e end;
  eqobsrel_tail; unfold EP1, EP2, andR, impR; simpl; unfold O.eval_op; simpl;
      intros k2 m1 m2 W; decompose [and] W; clear W; trivial.
  intros W; apply H1; clear H1; rewrite is_true_orb in W |- *; destruct W; auto.
  right; rewrite is_true_existsb in H1 |- *; destruct H1 as (x, (Hin, W));
   exists x; split; trivial.
  mem_upd_simpl.
  repeat rewrite is_true_andb in W; decompose [and] W; clear W.
  rewrite existsb_app in H6.
  match type of H6 with is_true (orb ?x _) => 
    generalize H6; clear H6; case_eq x; intros Heq H6 end; trivial.
    generalize H4 H7; rewrite (@assoc_app k2 BS_nk1 Tbk0).
    match goal with |- context [if ?e then _ else _] => replace e with true; trivial end.
    repeat rewrite is_true_andb; repeat split; trivial.
  simpl in H6; rewrite orb_false_r in H6; rewrite is_true_Ti_eqb in *.
  elim H3; rewrite is_true_existsb; exists x; split; trivial.
   rewrite <- (H0 _ LD); trivial.
   mem_upd_simpl.
   rewrite <- (H0 _ LHb_tl), <- (H0 _ LG), H6, Ti_eqb_refl; trivial.
   rewrite (@assoc_app k2 BS_nk1 Tbk0) in H4; generalize H4.
   match goal with |- context [if ?e then _ else _] => replace e with false; trivial end.
   unfold O.assoc at 1 2; simpl.
   rewrite H6, Ti_eqb_refl; simpl; intros; trivial.
   rewrite <- (H0 _ rH_aux), <- (H0 _ R'); trivial.
   eqobsrel_tail; unfold EP1, EP2, andR, impR; simpl; unfold O.eval_op; simpl;
      intros k2 m1 m2 W; decompose [and] W; clear W; trivial.
  intros W; apply H2; clear H2; rewrite is_true_orb in W |- *; destruct W; auto.
  right; rewrite is_true_existsb in H2 |- *; destruct H2 as (x, (Hin, W));
   exists x; split; trivial.
  mem_upd_simpl.
  repeat rewrite is_true_andb in W; decompose [and] W; clear W.
  rewrite existsb_app in H5.
  match type of H5 with is_true (orb ?x _) => 
    generalize H5; clear H5; case_eq x; intros Heq H5 end; trivial.
    generalize H3 H6; rewrite (@assoc_app k2 BS_nk1 Tbk0).
    match goal with |- context [if ?e then _ else _] => replace e with true; trivial end.
    repeat rewrite is_true_andb; repeat split; trivial.
  simpl in H5; rewrite orb_false_r in H5.
  elim H1; generalize H6; rewrite (@assoc_app k2 BS_nk1 Tbk0).
  match goal with |- context [if ?e then _ else _] => replace e with false; trivial end.
  unfold O.assoc at 1; simpl.
  rewrite H5; simpl; trivial.
  assert (depend_only_rel (EP1 (bad2 || Bad1_H) |-> EP2 bad2)
            (Vset.union (fv_expr (bad2 || Bad1_H)) Vset.empty)
            (Vset.union Vset.empty (fv_expr bad2))) by auto.
  assert (decMR (EP1 (bad2 || Bad1_H) |-> EP2 bad2)) by auto.
  set (i:= empty_inv_info H (refl_equal true) X E10r E10r).
  deadcode i. eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  intros k2 m1 m2 (_, HH).
  intros; apply HH.
  rewrite is_true_orb, is_true_existsb in H0 |- *.
  destruct H0; auto.
  right; destruct H0 as (x, (Hin, H0)); exists x; split; trivial.
  mem_upd_simpl; trivial.
 Qed.  

 Section bad2_SLHb.

  Variable k : nat.

  Definition testR_H_aux (m : Mem.t k) (v : T.interp k (T.Pair T.Bool BS_k)) :=
   EP k (Efst auxH =?=Efst (ap_finv (Esnd tc))) (m {!tc <-- v!}).

  Definition testLHb_tl (m : Mem.t k) (v : T.interp k (T.Pair T.Bool BS_k)) := 
   EP k (let c := Esnd (tc) in
         let s := Efst (ap_finv c) in
         (s in_dom (LHb_tl)) && Efst (LHb_tl[{s}]))
   (m {!tc <-- v!}).

  Definition bad2_K_H_tl (mn' : Mem.t k) :=
   (charfun (EP k bad2) mn' +
    ((length
       (filter (testLHb_tl mn')
       (mn' LD))) */
     (qG_poly k + 1)/2^ k0 k) + [1-] (charfun (fun mn':Mem.t k => no_double_H (mn' LHb_tl)) mn'))%U.
   
  Definition dep_bad2_K_H_tl := {{bad2,LHb_tl,LD}}.

  Lemma dep_bad2_K_H_tl_correct : depend_only_f bad2_K_H_tl dep_bad2_K_H_tl.
  Proof. 
   intros m1 m2 H.
   unfold bad2_K_H_tl, testLHb_tl, charfun, restr, EP; simpl; unfold O.eval_op; simpl.
    rewrite (H _ bad2), (H _ LHb_tl); trivial. 
    apply Uplus_eq_compat; trivial.
    apply Uplus_eq_compat; trivial.
    apply Nmult_eq_compat_left; trivial.
    apply f_equal. 
    rewrite (H _ LD); trivial.
    apply filter_morph; intros.
    mem_upd_simpl.
    rewrite (H _ LHb_tl); trivial.
  Qed.  

  Lemma inv_bad_K_H_tl : inv_bad E10r bad2_K_H_tl sample_while_H_bad2.
  Proof.
   clear; unfold sample_while_H_bad2.
   apply inv_bad_while.
   apply EqObs_inv_bad with (1 := dep_bad2_K_H_tl_correct)
   (c :=[ If Elen LG <=! qG _then [
            If !(LHb_tl =?= E.Cnil Tnk1bk0) _then [
              auxH <- Ehd LHb_tl;
              If Efst (Esnd (auxH))_then [
                 rH_aux <$- {0,1}^k0;
                 If test_exists_H_aux _then [bad2 <- true]
              ];
              LHb_tl <- Etl LHb_tl
            ]
         ] ]) 
   (I:={{R',LD,LHb_tl,LG,bad2}}).
 ep; deadcode; eqobs_in.
 intros m.
 unfold bad2_K_H_tl at 2.
 unfold charfun, restr, fone.
 match goal with |- ( _ <= ((if ?x then _ else _)+ _ + [1-] (if ?y then _ else _))%U)%tord => 
  case_eq x; [ | case_eq y]; repeat Usimpl; trivial end.
 intros HDD; change (is_true (no_double_H (m LHb_tl))) in HDD. 
 intros Heq1.
 rewrite deno_cond_elim; match goal with |- context [if ?e then _ else _] => 
  case_eq e; intros Hle;
  [change (is_true e) in Hle | ] end.
 rewrite deno_cond_elim; match goal with |- context [if ?e then _ else _] => 
  case_eq e; intros Hcons;
  [change (is_true e) in Hcons | ] end.
 rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim, deno_cons_elim, Mlet_simpl, deno_cond_elim.
 match goal with |- context [ if E.eval_expr _ ?m then _ else _ ] => set (m1 := m) end.
 match goal with |- context [if ?e then _ else _] => 
  case_eq e; intros Heq0;
  [change (is_true e) in Heq0 | ] end.
 rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
 transitivity
    (mu
      (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m1))
      (fplus
         (fun v2 => charfun (EP k test_exists_H_aux) (m1{!rH_aux<--v2!}))
         (fcte _ 
           ((
               length 
                 (filter (testLHb_tl (m1{!LHb_tl <-- E.eval_expr (Etl LHb_tl) m1!}))
                      (m1 LD))) */ (qG_poly k + 1) /2^k0 k))%U)).
  apply mu_monotonic; intros v2; unfold fplus, fcte.
  rewrite deno_cond_elim.
  match goal with |- context [(if ?x then _ else _)] => case_eq x; intros Heq2 end.
  rewrite deno_assign_elim, deno_assign_elim.
  unfold bad2_K_H_tl.
  unfold charfun at 2; unfold restr.
  match goal with |- context [if ?e then _ else _] =>
   replace e with true; [repeat Usimpl | ] end.
    Focus 2.
    generalize Hcons; unfold m1; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
    destruct (m LHb_tl).
    rewrite Ti_eqb_refl; intros; discriminate.
    change (is_true (no_double_H (i::i0))) in HDD; simpl in HDD.
    rewrite is_true_andb in HDD; destruct HDD; simpl; symmetry; trivial.
   unfold fone; repeat Usimpl; trivial.
  apply Uplus_le_compat; trivial.
  unfold charfun, restr, EP; rewrite Heq2; trivial.
  apply Nmult_le_compat_left; trivial.
  simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
  match goal with |- ?x <= ?y => replace x with y; trivial end.
  apply f_equal;  apply filter_morph; intros a.
  unfold m1, testLHb_tl, EP; simpl; unfold O.eval_op; simpl;
  mem_upd_simpl.
  trivial.
  rewrite deno_nil_elim, deno_assign_elim.
  unfold bad2_K_H_tl.
  unfold charfun at 2; unfold restr.
  match goal with |- context [if ?e then _ else _] =>
   replace e with true; [repeat Usimpl | ] end.
    Focus 2.
    generalize Hcons; unfold m1; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
    destruct (m LHb_tl).
    rewrite Ti_eqb_refl; intros; discriminate.
    change (is_true (no_double_H (i::i0))) in HDD; simpl in HDD.
    rewrite is_true_andb in HDD; destruct HDD; simpl; symmetry; trivial.
   unfold fone; repeat Usimpl; trivial.
  apply Uplus_le_compat; trivial.
  generalize Heq1; clear Heq1; unfold m1, charfun, restr, EP; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
  intros Heq1; rewrite Heq1; trivial.
  apply Nmult_le_compat_left; trivial.
  simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
  match goal with |- ?x <= ?y => replace x with y; trivial end.
  apply f_equal;  apply filter_morph; intros a.
  unfold m1, testLHb_tl, EP; simpl; unfold O.eval_op; simpl;
  mem_upd_simpl;
  trivial.
  transitivity 
    ((length (filter (testR_H_aux m1) (m1 LD)) + 
     (length
                (filter
                   (testLHb_tl
                      (m1 {!LHb_tl <-- E.eval_expr (Etl LHb_tl) m1!}))
                   (m1 LD)))
     ) */ ((qG_poly k + 1) /2^k0 k))%U.
  rewrite mu_le_plus.
  match goal with |- ( _ <= ((?x + ?y)*/ _)%U)%tord => 
    assert (W:= plus_Nmult_distr x y); rewrite W; clear W end.
  rewrite mu_cte_le; apply Uplus_le_compat; trivial.
  set (FR := filter (testR_H_aux m1) (m1 LD)).
  set (def:= T.default k (T.Pair T.Bool BS_k)).
 set (test_exists_body := let c := Esnd (tc) in
   let s := Efst (ap_finv c) in
   let t := Esnd (ap_finv c) in
   let h := rH_aux in
   let r := t |x| h in
   E.Eop O.Oand {Efst auxH =?= s, E.Eop O.Oor {r in_dom LG, R' =?= r} }).
  transitivity 
    (mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m1))
         (sigma_fun 
               (fun i v => 
                   charfun (EP k test_exists_body) (m1{!tc<--nth i FR def!}{!rH_aux <-- v!}))
               (length FR))).
   apply mu_monotonic; intro v; unfold fplus,sigma_fun.
   unfold charfun at 1; unfold restr.
   match goal with |- context [if ?x then _ else _] =>
     case_eq x; intros Heq2; [change (is_true x) in Heq2 | trivial] end.
   set (ff:= (fun k2 : nat =>
                   charfun (EP k test_exists_body) (m1{!tc<--nth k2 FR def!}{!rH_aux <-- v!}))).
   assert (exists i, i < (length FR) /\ 
                        (EP k test_exists_body (m1{!tc<--nth i FR def!}{!rH_aux <-- v!}))).
   apply nth_existsb with (f :=
     fun w => EP k test_exists_body (m1{!tc<--w!}{!rH_aux <-- v!})). 
   generalize Heq2; unfold FR, test_exists_body, m1; clear.
   unfold EP; simpl; unfold O.eval_op; simpl;
   mem_upd_simpl.
   repeat rewrite is_true_existsb.
   intros (x, (H1, H2)); generalize H2; clear H2;
    mem_upd_simpl.
    repeat rewrite is_true_andb; intros (H2, H3).
    exists x; split.
    rewrite filter_In; split; trivial.
    unfold testR_H_aux, EP; simpl; unfold O.eval_op; simpl.
    mem_upd_simpl; trivial.
    mem_upd_simpl.
    rewrite H2; trivial.

   destruct H as (i, (H1, H2)).
   apply Ole_trans with (2:= sigma_le ff H1).
   unfold ff, charfun, restr. rewrite H2; trivial.
   rewrite mu_sigma_le, Nmult_sigma; apply sigma_le_compat.
   intros k2 Hlt; set (nth2 := nth k2 FR def); rewrite plus_Nmult_distr.
   set (def0:= T.default k (T.Pair BS_k0 BS_nk1)).
   transitivity
    ((mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m)))
      (fplus (sigma_fun (fun i v => charfun (T.i_eqb k BS_k0 v)
                (BVxor (k0 k) (snd (finv (snd nth2))) (fst (nth i (m1 LG) def0))))
                        (length (m1 LG)))
             (fun v => charfun (T.i_eqb k BS_k0 v) (BVxor (k0 k) (snd (finv (snd nth2))) (m1 R'))))).
   apply mu_monotonic; intros v.
   unfold charfun, EP, restr, test_exists_body, fplus; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   match goal with |- context [if ?e then _ else _] =>
     case_eq e; intros Heq2; [change (is_true e) in Heq2 | trivial ] end.
   rewrite is_true_andb, is_true_orb in Heq2; destruct Heq2 as (H1, [H2 | H2]).
   match goal with |- ((_ <= ?x + _)%U)%tord => setoid_replace x with 1%U; [trivial | ] end.
   split; trivial.
   unfold fone; set (ff:= (fun k2 : nat =>
                   charfun (T.i_eqb k BS_k0 v)
                              (BVxor (k0 k) (snd (finv (k:=k) (snd nth2))) (fst (nth k2 (m1 LG) def0))))).
   assert (exists i, i < (length (m1 LG)) /\ (T.i_eqb k BS_k0 v
                              (BVxor (k0 k) (snd (finv (k:=k) (snd nth2))) (fst (nth i (m1 LG) def0))))).
   apply nth_existsb with (f :=
     fun w => (T.i_eqb k BS_k0 v
                              (BVxor (k0 k) (snd (finv (k:=k) (snd nth2))) (fst w)))).
   rewrite is_true_existsb in H2 |- *; destruct H2 as (x, (H2, H3)); exists x; split; trivial.
   rewrite is_true_Ti_eqb in H3; match goal with |- is_true (T.i_eqb _ _ _ (BVxor _ _ ?x)) => 
        match type of H3 with ?y = _ => replace x with y; trivial end end.
   match goal with |- context [BVxor ?k ?x _] =>
     repeat rewrite (@BVxor_comm k x) end. rewrite BVxor_bij; apply Ti_eqb_refl.
   destruct H as (i, (H3, H4)).
   apply Ole_trans with (2:= sigma_le ff H3).
   unfold ff, charfun, restr. rewrite H4; trivial.
   match goal with |-  ((_ <= _ + (if ?x then _ else _))%U)%tord => 
       replace x with true end; unfold fone; trivial.
   rewrite is_true_Ti_eqb in H2; rewrite H2.
   symmetry; match goal with |- context [BVxor ?k ?x _] =>
     repeat rewrite (@BVxor_comm k x) end. rewrite BVxor_bij; apply Ti_eqb_refl.
   rewrite mu_le_plus; apply Uplus_le_compat.
   rewrite mu_sigma_le, Nmult_sigma.
   transitivity (sigma (fun _ : nat => ([1/2] ^ k0 k)%U) (length (m1 LG))).
   apply sigma_le_compat.
   intros k3 Hlt3.
   apply Oeq_le; apply Pr_bs_support with
    (v:= (BVxor (k0 k) (snd (finv (k:=k) (snd nth2))) (fst (nth k3 (m1 LG) def0))))
    (f := fun v1 v2 => charfun (T.i_eqb k BS_k0 v2) v1).
   intros x Hdiff; unfold charfun, restr.
   match goal with |- context [(if ?e then _ else _)] => case_eq e; intros Heq4;
    [change (is_true e) in Heq4 | trivial]  end.
   elim Hdiff; rewrite is_true_Ti_eqb in Heq4; trivial.
   unfold charfun, restr; rewrite Ti_eqb_refl; trivial.
   apply sigma_incr.
   generalize Hle; unfold m1; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   rewrite is_true_leb; trivial.
 
  apply Oeq_le; apply Pr_bs_support with
    (v:= (BVxor (k0 k) (snd (finv (k:=k) (snd nth2))) (m1 R')))
    (f := fun v1 v2 => charfun (T.i_eqb k BS_k0 v2) v1).
   intros x Hdiff; unfold charfun, restr.
   match goal with |- context [(if ?e then _ else _)] => case_eq e; intros Heq4;
    [change (is_true e) in Heq4 | trivial]  end.
   elim Hdiff; rewrite is_true_Ti_eqb in Heq4; trivial.
   unfold charfun, restr; rewrite Ti_eqb_refl; trivial.
   apply Nmult_le_compat; trivial.
   unfold m1;
    mem_upd_simpl.
   generalize (m LD).
   induction i; simpl; trivial.
   case_eq (testLHb_tl m a); intros.
   match goal with |- context [if ?e then _ else _] =>
    case_eq e; intros HH1; [change (is_true e) in HH1 | ] end.
   match goal with |- context [if ?e then _ else _] =>
    replace e with false end.
   simpl; apply le_n_S; trivial.
   change (is_true (testLHb_tl m a)) in H.
   generalize Heq0 Hcons H HH1; unfold m1, testLHb_tl, testR_H_aux, EP; simpl; unfold O.eval_op; simpl;
    mem_upd_simpl.
   destruct (m LHb_tl); simpl.
   rewrite Ti_eqb_refl; intros; discriminate.
   simpl; repeat rewrite is_true_andb in *.
   intros WW _ _ H2.
   rewrite is_true_Ti_eqb in H2.
   symmetry; rewrite <- not_is_true_false.
   repeat rewrite is_true_andb; intros (H3, H4).
   simpl in HDD; rewrite is_true_andb, is_true_negb in HDD; destruct HDD.
   elim H0; rewrite <- H2 in H3; trivial.
   match goal with |- context [if ?e then _ else _] =>
    case_eq e; intros end.
   simpl; rewrite <- plus_n_Sm; apply le_n_S; trivial.
   simpl; apply le_S; trivial.
   match goal with |- context [if ?e then _ else _] =>
    replace e with false end.
   match goal with |- context [if ?e then _ else _] =>
    replace e with false end.
   trivial.
   generalize Hcons Heq0 H; unfold m1, testLHb_tl, EP; simpl; unfold O.eval_op; simpl;
    mem_upd_simpl.
   destruct (m LHb_tl); simpl.
   intros; discriminate.
   clear Hcons Heq0 H; intros _ Heq0 H; symmetry; rewrite <- not_is_true_false in H |- *.
   repeat rewrite is_true_andb; intros H1; decompose [and] H1; elim H; clear H H1.
   rewrite H0, orb_true_r; unfold O.assoc at 1; simpl.
   match goal with |- context [if ?x then _ else _] => case_eq x; intros; trivial end.
   generalize Hcons Heq0 H; unfold m1, testLHb_tl, testR_H_aux, EP; simpl; unfold O.eval_op; simpl;
    mem_upd_simpl.
   destruct (m LHb_tl); simpl.
   intros; discriminate.
   clear Hcons Heq0 H; intros _ Heq0 H; symmetry; rewrite <- not_is_true_false in H |- *.
   repeat rewrite is_true_andb; intros H1; elim H; clear H.
   unfold O.assoc; simpl; rewrite is_true_Ti_eqb in H1; rewrite <- H1, Ti_eqb_refl; simpl; trivial.
   rewrite deno_nil_elim; rewrite deno_assign_elim.
   generalize Heq1 Hcons; unfold bad2_K_H_tl, m1, charfun,restr, EP; simpl; unfold O.eval_op; simpl;
    mem_upd_simpl.
   clear Heq1; intros Heq1; rewrite Heq1; intros; repeat Usimpl.
   match goal with |- context [if ?e then _ else _] => replace e with true end.
   2:destruct (m LHb_tl); simpl.
   2:rewrite Ti_eqb_refl in Hcons0; discriminate.
   2:change (is_true (no_double_H (i::i0))) in HDD.
   2:simpl in HDD; rewrite is_true_andb in HDD; destruct HDD; auto.
   unfold fone; repeat Usimpl; apply Nmult_le_compat_left; trivial.
   generalize (m LD).
   induction i; simpl; trivial.
   case_eq (testLHb_tl m a); intros Heq2; [change (is_true (testLHb_tl m a)) in Heq2 | ].
   match goal with |- context [if ?e then _ else _] =>
    destruct e; simpl; [apply le_n_S | apply le_S]; trivial end.
   match goal with |- context [if ?e then _ else _] => replace e with false; trivial end.
   change (is_true (no_double_H (m LHb_tl))) in HDD.
   symmetry; generalize Heq2 Hcons HDD Heq0; repeat rewrite <- not_is_true_false;
    unfold m1, testLHb_tl,EP; simpl; unfold O.eval_op; simpl;
     mem_upd_simpl.
   destruct (m LHb_tl); intros.
   rewrite Ti_eqb_refl in H0; elim H0; trivial.
   simpl; repeat rewrite is_true_andb; clear H0; intros H0; decompose [and] H0;
    apply H; clear H H0.
   simpl; rewrite H3.
   unfold O.assoc at 1; simpl.
   match goal with |- context [orb ?x _] => case_eq x; intros Heq3;
    [change (is_true x) in Heq3 | trivial] end.
   rewrite is_true_Ti_eqb in Heq3; rewrite Heq3 in *.
   simpl in H1. rewrite is_true_andb, is_true_negb in H1; destruct H1.
   elim H; trivial.
   rewrite deno_nil_elim; unfold bad2_K_H_tl, charfun, restr, fone.
   rewrite Heq1, HDD; repeat Usimpl; trivial.
   rewrite deno_nil_elim; unfold bad2_K_H_tl, charfun, restr, fone.
   rewrite Heq1, HDD; repeat Usimpl; trivial.
  Qed.  

End bad2_SLHb.

Lemma PR_10_bad2_Bad1 : forall k (m:Mem.t k), 
 (Pr E10r (G2b_H++SLHb) (m{!bad2 <-- false!}) (EP k (bad2 || Bad1_H)) <= 
  (qD_poly k */ ((qG_poly k + 1)/2^k0 k)))%tord.
Proof.
 unfold Pr; intros.
 rewrite deno_app_elim.
 transitivity
   (mu (([[G2b_H]]) E10r' (m {!bad2 <-- false!}))
      (@bad2_K_H k)).
 apply equiv_deno_le with Meq (Meq /-\ inv_qD_LHb); trivial.
 union_mod iE10rE10r'. trivial.
 eqobs_tl iE10rE10r'; unfold inv_qD_LHb, inv_qD_qG; eqobsrel_tail; simpl; unfold O.eval_op; simpl.
  intros k2 m1 m2 Heq; split; [trivial | ].
  red; mem_upd_simpl; trivial.

 unfold inv_qD_LHb, Meq; intros m1 m2 (Heq, (HqD, HDD)); subst.
 clear m; rename m2 into m.
 transitivity (mu ([[sample_true_H_bad2 ++[LHb <- LHb_hd] ]] E10r m) 
   (charfun (EP k bad2))).
 apply equiv_deno_le with (1:= SLHb_Bad1_bad2).
 intros m1 m2 (H1, H2).
 unfold impR, EP1,EP2 in H2; unfold charfun, restr, EP.
 match goal with |- ((if ?x then _ else _)<= _)%tord => destruct x; trivial end.
 rewrite H2; trivial.
 split; trivial.
 generalize HqD; unfold inv_qD_qG, EP2; simpl; unfold O.eval_op; simpl.
   repeat rewrite is_true_andb; repeat rewrite is_true_leb; omega'. 

 rewrite deno_app_elim.
 transitivity  (mu (([[sample_true_H_bad2]]) E10r m) (@bad2_K_H_tl k)).
  apply mu_monotonic; intros m1.
  rewrite deno_assign_elim.
  unfold bad2_K_H_tl, charfun, EP, restr, fone; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  destruct (m1 bad2); trivial.
  repeat Usimpl; trivial.
  unfold sample_true_H_bad2.
  rewrite deno_app_elim, deno_cons_elim, Mlet_simpl, deno_assign_elim, deno_assign_elim.
  rewrite inv_bad_K_H_tl.
  generalize HqD, HDD; unfold No_double_LHb,inv_qD_qG,EP2,bad2_K_H, bad2_K_H_tl, 
    charfun,restr, EP, fone; simpl; unfold O.eval_op; simpl;
  mem_upd_simpl; intros.
  rewrite HDD0; repeat Usimpl.
  apply Nmult_le_compat; trivial.
  simpl; match goal with |- (?x <= ?y - ?z) => assert (x + z <= y); [ | omega'] end.
  repeat rewrite is_true_andb in HqD0; repeat rewrite is_true_leb in HqD0; decompose [and] HqD0; clear HqD0.
  apply le_trans with (2:= H1).
  generalize (m LD).
   induction i; simpl; intros; trivial.
   match goal with |- context [(if ?b then _ else _)] => case_eq b; intros end.
   match goal with |- context [(if ?b then _ else _)] => replace b with false end.
   simpl; apply le_n_S; trivial.
   symmetry; rewrite <- not_is_true_false.
   generalize H0; clear H0; unfold testLHb, testLHb_tl, EP; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   match goal with |- ?x = true -> ?y => change ((is_true x) -> y) end.
   repeat rewrite is_true_andb; rewrite is_true_negb; intuition.
   match goal with |- context [(if ?b then _ else _)] => case_eq b; intros; simpl end.
   rewrite <- plus_n_Sm; apply le_n_S; trivial.
   apply le_S; trivial.

 change G2b_H with 
   ([bad <- false;Ydef <- false; LG <- E.Cnil _;
      LHb <- E.Cnil _; LD <- E.Cnil _] ++ 
    ([Dc <- O; Gc <- O;R' <$- {0,1}^k0] ++ (SGR' ++ [S' <- (GR'n | GR'k1)] ++ tail2))).
 rewrite deno_app_elim.
 transitivity 
   (mu (([[ [bad <- false;Ydef <- false; LG <- E.Cnil _;
             LHb <- E.Cnil _; LD <- E.Cnil _] ]] E10r' (m {!bad2 <-- false!})))
       (@bad2_K_H k)).
 apply mu_monotonic; intros m1.
 apply check_inv_bad_c_correct with (ipr10 k). vm_compute; trivial.
 repeat rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
 rewrite deno_nil_elim; unfold bad2_K_H, charfun, restr, EP; simpl; unfold O.eval_op; simpl;
  mem_upd_simpl.
 simpl; rewrite <- minus_n_O; Usimpl; trivial.
 Qed. 


 Lemma PR_9_bad_10r : forall k m,
   (Pr E9 G2 m (EP k bad) <= 
     (Pr E10r G2b_H (m{! bad2 <-- false !}) (EP k bad) 
      + ((qD_poly k) */ ((qG_poly k + 1)/2^k0 k)))%U)%tord.
 Proof.
  intros k m; eapply Ole_trans; [apply PR_9_bad_10 | ].
  apply Uplus_le_compat.
  apply Oeq_le.
  apply EqObs_Pr with {{Y',bad2,g_a}}.
  apply EqObs_trans with E10r (G2b_H ++ SLHb).
  eapply equiv_strengthen; [ | eapply equiv_weaken; [ | apply equiv_E10_E10r ] ].
   intros k2 m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
   intros k2 m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  eqobs_hd iE10r. deadcode.
  apply equiv_strengthen with (kreq_mem (fv_expr bad)).
   intros k2 m1 m2 H; apply req_mem_weaken with (2:= H); vm_compute; trivial.
  apply EqObs_lossless_Modify with {{LHb_hd,rH_aux,auxH,LHb_tl}} Vset.empty.
  2:apply lossless_nil.
  apply lossless_cons; [ apply lossless_assign | ].
  red; intros.
  rewrite deno_while_unfold_elim.
  assert (forall n m1, n = E.eval_expr (Elen LHb_tl) m1 ->
     ((Mu (Mem.t k2) @
      unroll_while_sem E10r (!(LHb_tl =?= Nil _))
        [
        auxH <- Ehd LHb_tl;
        LHb_tl <- Etl LHb_tl;
        If Efst (Esnd auxH)
        _then [
              rH_aux <$- {0,1}^k0;
              auxH <- (Efst auxH | (true | rH_aux))
              ];
        LHb_hd <- LHb_hd |++| auxH |::| Nil _
        ] m1) <_> (fun _ : Mem.t k2 => 1%U)) n == 1%U)%tord.
 Opaque deno app.
   induction n0; simpl; unfold O.eval_op; simpl.
   intros; rewrite (deno_cond_elim E10r (!(LHb_tl =?= Nil _)) nil nil m1).
   unfold negP; simpl; unfold O.eval_op; simpl.
   case_eq (Ent.T.i_eqb k2 _ (m1 LHb_tl) (@nil (T.interp k2 Tnk1bk0))); simpl; intros Heq; rewrite Heq; simpl.
   rewrite (deno_nil_elim E10r m1); rewrite Heq; trivial.
   rewrite <- not_is_true_false, is_true_Ti_eqb in Heq.
   destruct (m1 LHb_tl); [ elim Heq; trivial | discriminate].
   intros; rewrite (fun c1 c2 => deno_cond_elim E10r (!(LHb_tl =?= Nil _)) c1 c2 m1).
   simpl; unfold O.eval_op; simpl.
   case_eq (T.i_eqb k2 (Var.btype LHb_tl) (m1 LHb_tl) (@nil (T.interp k2 Tnk1bk0))); 
    simpl; intros Heq; rewrite Heq.
   destruct (m1 LHb_tl); discriminate.
   change (mu ([[ sample_body_H LHb_hd LHb_tl ++ 
                  unroll_while (!(LHb_tl =?= Nil _)) (sample_body_H LHb_hd LHb_tl) n0]] E10r m1)
             (fun x : Mem.t k2 =>
             (mu
       (if negP
             (fun m2 : Mem.t k2 =>
              negb (T.i_eqb k2 (Var.btype LHb_tl) (m2 LHb_tl) nil))
             x
        then Munit x
        else distr0 (Mem.t k2))) (fun _ : Mem.t k2 => 1%U)) == 1%U).
   rewrite deno_app_elim.
   transitivity (mu ([[sample_body_H LHb_hd LHb_tl]] E10r m1) (fun _ => 1%U)).
   apply equiv_deno with (Meq /-\ EP1 (Datatypes.S n0 =?= Elen LHb_tl)) 
       (Meq /-\ EP1 (n0 =?= Elen LHb_tl)).
   union_mod. rewrite proj1_MR; trivial.
   eqobsrel_tail; unfold Meq, EP1, implMR, andR; simpl; unfold O.eval_op; simpl; intros k3 m3 m4 (H1, H2); subst.
   destruct (m4 LHb_tl); [discriminate | ].
   simpl in H2 |- *; rewrite is_true_Ti_eqb in H2. 
   inversion H2; split; intros; apply Ti_eqb_refl.
   unfold Meq, EP1; intros m2 m3 (H1, H2); subst.
   refine (IHn0 m3 _).
   rewrite <- (expr_eval_eq m3 n0) in H2; trivial.
   split; [trivial | unfold EP1; rewrite <- (expr_eval_eq m1 (Datatypes.S n0)); trivial].
   assert (lossless E10r (sample_body_H LHb_hd LHb_tl)).
    apply is_lossless_correct with (refl1_info iE10r).
    vm_compute; trivial.
   apply H0.
   split; trivial.
   match goal with |- (1%U <= lub (c:=U) ?F)%tord => 
   transitivity (F (E.eval_expr (Elen LHb_tl) m0)) end.
   rewrite H; trivial.
   apply le_lub.
   apply modify_correct with (refl1_info iE10r) Vset.empty.
   vm_compute; trivial.
   apply Modify_nil.
   vm_compute; trivial.
   vm_compute; trivial.

  apply Ole_trans with  (Pr E10r (G2b_H++SLHb) (m {!bad2 <-- false!}) (EP k (E.Eop O.Oor {bad2, Bad1_H}))).
  apply Oeq_le; apply EqObs_Pr with {{Y',bad2,g_a}}.
  eapply equiv_weaken; [ | apply equiv_E10_E10r].
     intros k2 m1 m2 H; apply req_mem_weaken with (2:=H); vm_compute; trivial.
  apply PR_10_bad2_Bad1.
 Qed.


 Definition Dec_body11 :=
  [
    If E.Eop O.Oor {testD, qG <! (Elen LG)} then [mn <- (false | one_n)]
    else [
       LD <- (Ydef | c) |::| LD;
       Dc <- 1 +! Dc;
       st <- ap_finv c;
       s <- Efst st;
       t <- Esnd st;
       If s in_dom LH then [
          h <- LH [{s}];
          r <- t |x| h;
          If r in_dom LG then [
             g <- LG [{r}];
             m <- s |x2| g;
             If Esnd m =?= zero_k1 then [mn <- (true | Efst m)]
             else [mn <- (false | one_n)]
          ] else [
            If R' =?= r _then [bad <- true];
            mn <- (false | one_n)
          ]
       ] else [ mn <- (false | one_n) ]
    ]
  ].

 Definition E11 := mkEnv H_body0 G_body2 Dec_body11.

 Definition inv11 : mem_rel := 
  fun k m1 m2 => (forall v, 
   andb (@List.existsb (T.interp k BS_nk1 * T.interp k Tbk0)%type (fun p => T.i_eqb k BS_nk1 v (fst p))
    (m1 LHb))
   (negb (fst (@O.assoc (T.interp k BS_nk1) (T.interp k Tbk0) (T.i_eqb k BS_nk1 v) (T.default k Tbk0) 
    (m1 LHb)))) = 
   (@List.existsb (T.interp k BS_nk1 * T.interp k BS_k0)%type (fun p => T.i_eqb k BS_nk1 v (fst p))
    (m2 LH)) /\
   (@List.existsb (T.interp k BS_nk1 * T.interp k BS_k0)%type (fun p => T.i_eqb k BS_nk1 v (fst p))
    (m2 LH) ->
    snd (@O.assoc (T.interp k BS_nk1) (T.interp k Tbk0) (T.i_eqb k BS_nk1 v) (T.default k Tbk0) 
     (m1 LHb)) =
    (@O.assoc (T.interp k BS_nk1) (T.interp k BS_k0) (T.i_eqb k BS_nk1 v) (T.default k BS_k0)
     (m2 LH)))).

 Lemma dep_inv11 : depend_only_rel inv11 {{LHb}} {{LH}}.
 Proof.
  unfold inv11; red; intros; simpl; unfold O.eval_op; simpl.
  rewrite <- (H _ LHb), <- (H0 _ LH); trivial.
 Qed.

 Lemma dec_inv11 : decMR inv11.
 Proof.
  red; unfold inv11; intros k m1 m2.
  set (F1 := fun p:T.interp k BS_nk1 * T.interp k BS_k0 =>
   andb (T.i_eqb k  BS_k0 (snd (O.assoc (T.i_eqb k BS_nk1 (fst p)) (T.default k Tbk0) (m1 LHb)))
       (O.assoc (T.i_eqb k BS_nk1 (fst p)) (T.default k BS_k0)
            (m2 LH)))
       (andb (existsb
           (fun p1:T.interp k BS_nk1 * T.interp k Tbk0 =>
               T.i_eqb k BS_nk1 (fst p) (fst p1)) (m1 LHb))
       (negb
        (fst (O.assoc (T.i_eqb k BS_nk1 (fst p)) (T.default k Tbk0) (m1 LHb)))))).
  set (F2 := fun p:T.interp k BS_nk1 * T.interp k Tbk0 =>
       orb (fst
              (O.assoc (T.i_eqb k BS_nk1 (fst p)) (T.default k Tbk0)
              (m1 LHb))) 
            (existsb
                (fun p1:T.interp k BS_nk1 * T.interp k BS_k0 =>
                  T.i_eqb k BS_nk1 (fst p) (fst p1))
                 (m2 LH))).
  case_eq (andb (List.forallb F1 (m2 LH)) (List.forallb F2 (m1 LHb))).
  left; rewrite andb_true_iff, forallb_forall, forallb_forall in H; destruct H; intros v.
  match goal with |- _ = ?x /\ _ => case_eq x; intros Heq end.
  rewrite existsb_exists in Heq; destruct Heq as (p, (H1, H2)).
  apply H in H1; unfold F1 in H1.
  change (is_true (T.i_eqb k BS_nk1 v (fst p))) in H2; rewrite is_true_Ti_eqb in H2; subst.
  rewrite andb_true_iff in H1; destruct H1.
  rewrite H2.
  match type of H1 with ?x = true => change (is_true x) in H1 end.
  rewrite is_true_Ti_eqb in H1; rewrite H1; auto.
  split; [ | intro;  discriminate].
  match goal with |-  (andb ?x _) = _ => case_eq x; intros Heq1; [ | trivial]end.
  rewrite existsb_exists in Heq1; destruct Heq1 as (p, (H1, H2)).
  match type of H2 with  ?x = true => change (is_true x) in H2 end.
  rewrite is_true_Ti_eqb in H2; subst.
  apply H0 in H1; unfold F2 in H1.
  apply orb_prop in H1; destruct H1.
  rewrite H1; trivial.
  rewrite H1 in Heq; discriminate.
  intros Heq; right; intros H.
  destruct (andb_false_elim _ _ Heq) as [H1 | H1]; clear Heq; rewrite <- not_is_true_false in H1.
  assert (existsb (negP F1) (m2 LH)).
    match goal with |- is_true ?x => case_eq x; intros; trivial end.
  elim H1; rewrite is_true_forallb; intros.
  case_eq (F1 x); intros; trivial.
  rewrite <- H0, is_true_existsb; exists x; split; [ | unfold negP; rewrite H3]; trivial.
  rewrite is_true_existsb in H0; destruct H0 as (x, (Hin, H2)).
  unfold negP, F1 in H2.
  destruct (H (fst x)).
  rewrite H0, negb_andb, is_true_orb, is_true_negb, is_true_Ti_eqb in H2; destruct H2.
  elim H2; apply H3.
  rewrite is_true_existsb; exists x; rewrite Ti_eqb_refl; auto.
  rewrite is_true_negb in H2; elim H2; rewrite is_true_existsb; exists x; rewrite Ti_eqb_refl; auto.
  assert (existsb (negP F2) (m1 LHb)).
    match goal with |- is_true ?x => case_eq x; intros; trivial end.
  elim H1; rewrite is_true_forallb; intros.
  case_eq (F2 x); intros; trivial.
  rewrite <- H0, is_true_existsb; exists x; split; [ | unfold negP; rewrite H3]; trivial.
  rewrite is_true_existsb in H0; destruct H0 as (x, (Hin, H2)).
  unfold negP, F2 in H2.
  destruct (H (fst x)).
  rewrite negb_orb, is_true_andb in H2; destruct H2.
  rewrite H2 in *. rewrite andb_true_r in H0; rewrite <- H0 in *.
  rewrite is_true_negb in H4; apply H4.
  rewrite is_true_existsb; exists x; rewrite Ti_eqb_refl; auto.
 Qed.

 Definition eE10rE11 := 
  empty_inv_info dep_inv11 (refl_equal true) dec_inv11 E10r E11.

 Opaque T.interp T.default.

 Lemma H_body_inv11 : 
  EqObsInv inv11 {{S}} E10r H_body2r_bad2 E11 H_body0 {{rH}}.
 Proof.
  unfold H_body2r_bad2, H_body0, H_body2b_gen.
  cp_test_r eE10rE11 (S in_dom LH).
  ep_eq_l eE10rE11 (S in_dom LHb) true.
   unfold inv11, req_mem_rel, andR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
    decompose [and] H; clear H.
   destruct (H3 (m1 S)); clear H3.
   rewrite <- (H2 _ S) in *; trivial.
   rewrite H1, andb_true_iff in H; destruct H; trivial.
  ep_eq_l eE10rE11 (Efst (LHb[{S}])) false.
   unfold inv11, req_mem_rel, andR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
    decompose [and] H; clear H.
   destruct (H3 (m1 S)); clear H3.
   rewrite <- (H2 _ S) in *; trivial.
   rewrite H1, andb_true_iff in H; destruct H; rewrite <- is_true_negb_false; trivial.
  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold upd_para; intros k m1 m2 ((H1, H2), H3).
  split.
  match goal with |- kreq_mem _ (m1 {! _ <-- ?x !}) (m2 {! _ <-- ?y!}) => replace x with y end.
  unfold kreq_mem.
  apply req_mem_update; apply req_mem_weaken with (2:= H1); vm_compute; trivial.
  generalize H3 H2; clear H3 H2; unfold inv11, EP1, EP2, notR, andR; simpl; unfold O.eval_op; simpl.
  intros H3 H2; rewrite <- (H1 _ S) in *; trivial.
  destruct (H2 (m1 S)); clear H2.
  rewrite <- (H0 H3); trivial.
  apply dep_inv11 with m1 m2; trivial; apply req_mem_upd_disjoint; trivial.

  cp_test_l (S in_dom LHb).
  ep_eq_l (Efst (LHb [{S}])) true.
   unfold inv11, req_mem_rel, andR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
   decompose [and] H; clear H.
   destruct (H4 (m1 S)); clear H4.
   rewrite <- (H0 _ S) in *; trivial.
   rewrite <- H, H1 in H3; simpl in H3.
   rewrite <- is_true_negb, negb_involutive in H3; trivial.

  deadcode eE10rE11.
  eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  unfold inv11,notR,andR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  mem_upd_simpl; simpl.
  rewrite (H0 _ S); trivial.
  case_eq (T.i_eqb k BS_nk1 v0 (m2 S)); intros; simpl.
  change (is_true (T.i_eqb k BS_nk1 v0 (m2 S))) in H3.
  rewrite is_true_Ti_eqb in H3; subst; simpl.
  rewrite assoc_upd_same, existsb_upd_same; unfold O.assoc; simpl; rewrite (Ti_eqb_refl k BS_nk1); auto.
  unfold O.assoc at 3; simpl; rewrite H3.
  rewrite <- not_is_true_false, is_true_Ti_eqb in H3.
  rewrite assoc_upd_diff, existsb_upd_diff; trivial.
  apply (H2 v0).
  repeat rewrite req_mem_rel_assoc.
  unfold inv11,andR, notR, impR; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  mem_upd_simpl; simpl.
  rewrite <- (H0 _ S); trivial.
  rename v0 into v1; case_eq (T.i_eqb k BS_nk1 v1 (m1 S)); intros; simpl.
  change (is_true (T.i_eqb k BS_nk1 v1 (m1 S))) in H2.
  rewrite is_true_Ti_eqb in H2; subst; simpl.
  unfold O.assoc; simpl; rewrite Ti_eqb_refl; auto.
  unfold O.assoc; simpl; rewrite H2.
  apply (H1 v1).
 Qed.

 Definition iE11 := iEiEi H_body0 G_body2 Dec_body11.

 Lemma Dec_body_inv11 : 
  EqObsInv inv11 (Vset.remove LH ID)
      E10r Dec_body10r E11 Dec_body11 (Vset.remove LH OD).
 Proof.
  unfold Dec_body10r, Dec_body11, Dec_body_gen_b_H.
  cp_test (E.Eop O.Oor {testD, qG <! (Elen LG)}); rewrite proj1_MR.
   eqobs_in eE10rE11.
  eqobs_hd eE10rE11.

  cp_test_r (Efst (ap_finv c) in_dom LH).

  ep_eq_l eE10rE11 (Efst (ap_finv c) in_dom LHb) true.
   generalize (depend_only_fv_expr  (Efst (ap_finv c))).
   unfold fv_expr; simpl fv_expr_rec; generalize (Efst (ap_finv c)).
   unfold inv11, req_mem_rel, andR, notR, impR, EP1, EP2; simpl; unfold O.eval_op; simpl;
     intros e Hdep k m1 m2 H; decompose [and] H; clear H.
   rewrite <- (Hdep k m1 m2) in *; [ | apply req_mem_weaken with (2:= H2); vm_compute; trivial].
   destruct (H3 (E.eval_expr e m1)).
   change UOp.Tnk1 with BS_nk1 in H1; change UOp.Tnk1 with BS_nk1 in H.
   rewrite H1, andb_true_iff in H; destruct H; trivial.
  ep_eq_l eE10rE11 (Efst (LHb [{Efst (ap_finv c)}])) false.
   generalize (depend_only_fv_expr  (Efst (ap_finv c))).
   unfold fv_expr; simpl fv_expr_rec; generalize (Efst (ap_finv c)).
   unfold inv11, req_mem_rel, andR, notR, impR, EP1, EP2; simpl; unfold O.eval_op; simpl;
     intros e Hdep k m1 m2 H; decompose [and] H; clear H.
   rewrite <- (Hdep k m1 m2) in *; [ | apply req_mem_weaken with (2:= H2); vm_compute; trivial].
   destruct (H3 (E.eval_expr e m1)).
   change UOp.Tnk1 with BS_nk1 in H1; change UOp.Tnk1 with BS_nk1 in H.
   rewrite H1, andb_true_iff in H; destruct H; rewrite <- is_true_negb_false; trivial.
  ep; deadcode eE10rE11.

  match goal with |- equiv ?P _ _ _ _ _ => 
  assert (forall (k : nat) (m1 m2 : Mem.t k), P k m1 m2 ->
     E.eval_expr (Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}])) m1 =
     E.eval_expr (Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}])) m2) end.
   unfold inv11, req_mem_rel, andR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl; intros k m1 m2 H;
    decompose [and] H; clear H.
   rewrite <- (H2 _ c) in *; trivial.
   destruct (H3 (fst (finv (k:=k) (m1 c)))).
   match type of H0 with _ -> ?x = _ =>
    match goal with |- BVxor _ _ ?y = _ => change y with x; rewrite H0; trivial end
   end.
  cp_test_r (Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}]) in_dom LG).
  ep_eq_l (Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}]) in_dom LG) true.
    intros k m1 m2 (H1, H2); generalize (H k m1 m2 H1) H2; unfold EP2.
    simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq.
    destruct H1 as ((H1, _), _); rewrite (H1 _ LG); trivial.
  rewrite proj1_MR.
  cp_test_r (Esnd (Efst (ap_finv c)) |x| Esnd (LG [{Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}])}]) =?= zero_k1).
  ep_eq_l (Esnd (Efst (ap_finv c)) |x| Esnd (LG [{Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}])}]) =?= zero_k1) true.
    intros k m1 m2 (H1, H2); generalize (H k m1 m2 H1) H2; unfold EP2.
    simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq.
    destruct H1 as ((H1, _), _); rewrite (H1 _ c), (H1 _ LG); trivial.
  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold upd_para; intros k m1 m2 (H1, _).
  generalize H1; intros ((H2 ,H3), _); split.
  match goal with |- kreq_mem _ (m1 {! _ <-- ?x !}) (m2 {! _ <-- ?y!}) => replace x with y end.
  unfold kreq_mem; setoid_replace (Vset.remove LH OD) with (Vset.add mn (Vset.remove mn (Vset.remove LH OD))); [ | reflexivity].
  apply req_mem_update. apply req_mem_weaken with (2:= H2); vm_compute; trivial.
  generalize (H k m1 m2 H1).
  simpl; unfold O.eval_op; simpl; intros Heq.
  match type of Heq with _ = ?x =>
    match goal with |- (_, BVxor _ _ (fst (O.assoc (T.i_eqb k BS_k0 ?y) _ _))) = _ => change y with x;
      rewrite <- Heq end
   end.
  rewrite (H2 _ c), (H2 _ LG); trivial.
  apply dep_inv11 with m1 m2; trivial; apply req_mem_upd_disjoint; trivial.
  ep_eq_l (Esnd (Efst (ap_finv c)) |x| Esnd (LG [{Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}])}]) =?= zero_k1) false.
    intros k m1 m2 (H1, H2); generalize (H k m1 m2 H1) H2; unfold notR,EP2.
    simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq.
    destruct H1 as ((H1, _), _); rewrite (H1 _ c), (H1 _ LG); trivial.
    intros H3; apply not_is_true_false in H3; trivial.
  rewrite proj1_MR, proj1_MR; eqobs_in eE10rE11.
  ep_eq_l (Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}]) in_dom LG) false.
    intros k m1 m2 (H1, H2); generalize (H k m1 m2 H1) H2; unfold notR,EP2.
    simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq.
    destruct H1 as ((H1, _), _); rewrite (H1 _ LG); trivial.
    intros H3; apply not_is_true_false in H3; trivial.
  cp_test_r (R' =?= Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}])).
  ep_eq_l (R' =?= Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}])) true.
    intros k m1 m2 ((H1, _), H2); generalize (H k m1 m2 H1) H2; unfold notR,EP2.
    simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq.
    destruct H1 as ((H1, _), _); rewrite (H1 _ R'); trivial.
  rewrite proj1_MR, proj1_MR, proj1_MR; eqobs_in eE10rE11.
  ep_eq_l (R' =?= Esnd (ap_finv c) |x| Esnd (LHb [{Efst (ap_finv c)}])) false.
    intros k m1 m2 ((H1, _), H2); generalize (H k m1 m2 H1) H2; unfold notR,EP2.
    simpl; unfold O.eval_op; simpl; intros Heq; rewrite Heq.
    destruct H1 as ((H1, _), _); rewrite (H1 _ R'); trivial.
    intros H3; apply not_is_true_false in H3; trivial.
  rewrite proj1_MR, proj1_MR, proj1_MR; eqobs_in eE10rE11.

  cp_test_l (Efst (ap_finv c) in_dom LHb).
  ep_eq_l (Efst (LHb [{Efst (ap_finv c)}])) true.
   generalize (depend_only_fv_expr  (Efst (ap_finv c))).
   unfold fv_expr; simpl fv_expr_rec; generalize (Efst (ap_finv c)).
   unfold inv11, req_mem_rel, andR, notR, impR, EP1, EP2; simpl; unfold O.eval_op; simpl;
     intros e Hdep k m1 m2 H; decompose [and] H; clear H.
   rewrite <- (Hdep k m1 m2) in *; [ | apply req_mem_weaken with (2:= H0); vm_compute; trivial].
   destruct (H4 (E.eval_expr e m1)).
   change UOp.Tnk1 with BS_nk1 in H1; change UOp.Tnk1 with BS_nk1 in H.
   rewrite H1 in H; simpl in H.
   match type of H with _ = ?x => change (~ (is_true x)) in H3; rewrite <- H in H3 end.
   rewrite <- is_true_negb, negb_involutive in H3; trivial.
  deadcode eE10rE11.
  eqobs_tl eE10rE11.
  match goal with |- equiv _ _ _ _ _ ?Q =>
    apply equiv_trans_r with (P2 := Meq) (Q1 := Q)
    (Q2 := kreq_mem OD) (E2:=E11) (c2:=[rH <$- {0,1}^k0]) end.
  auto using dec_inv11. red; red; trivial.
  intros. 
  match goal with |- req_mem_rel ?X _ _ _ _ =>
  apply (@depend_only_req_mem_rel X _ _ _ dep_inv11) with x y; trivial end.
  apply req_mem_weaken with (2:= H0); vm_compute; trivial.
  repeat rewrite req_mem_rel_assoc.
  deadcode eE10rE11.
  unfold inv11; eqobsrel_tail; unfold EP1, EP2, notR; 
   simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  mem_upd_simpl.
 deadcode; eqobs_in.
 
(*
rename v0 into v1; case_eq (T.i_eqb k BS_nk1 v1 (fst (finv (k:=k) (m1 c)))); intros Heq.
  change (is_true (T.i_eqb k BS_nk1 v1 (fst (finv (k:=k) (m1 c))))) in Heq.
  rewrite is_true_Ti_eqb in Heq; subst; simpl.
  rewrite assoc_upd_same, existsb_upd_same; simpl.
  rewrite not_is_true_false in H4.
  rewrite (H0 _ c); trivial.
  match type of H4 with ?x = _ =>
   match goal with |- (_ = ?y) /\ _ => change y with x; rewrite H4; split; [trivial | intros; discriminate] end end.
  rewrite <- not_is_true_false, is_true_Ti_eqb in Heq.
  rewrite assoc_upd_diff, existsb_upd_diff; trivial.
  deadcode; eqobs_in.
*)

  eqobs_tl eE10rE11.
  match goal with |- equiv _ _ _ _ _ ?Q =>
    apply equiv_trans_r with (P2 := Meq) (Q1 := Q)
    (Q2 := kreq_mem OD) (E2:=E11) (c2:=[rH <$- {0,1}^k0]) end.
  auto using dec_inv11. red; red; trivial.
  intros. 
  match goal with |- req_mem_rel ?X _ _ _ _ =>
  apply (@depend_only_req_mem_rel X _ _ _ dep_inv11) with x y; trivial end.
  apply req_mem_weaken with (2:= H0); vm_compute; trivial.
  repeat rewrite req_mem_rel_assoc.
  unfold inv11; eqobsrel_tail; unfold EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  mem_upd_simpl.
  rename v0 into v1; unfold O.assoc at 1 2; simpl.
  match goal with |- (andb (orb ?x _) _ = _) /\ _ => case_eq x; intros Heq end.
  change (is_true (T.i_eqb k BS_nk1 v1 (fst (finv (k:=k) (m1 c))))) in Heq.
  rewrite is_true_Ti_eqb in Heq; subst; simpl.
  simpl; split.
   apply not_is_true_false in H4; symmetry; rewrite (H0 _ c); trivial.
   intros W; elim H4; rewrite <- (H0 _ c); trivial.
  refine (H1 v1).
  deadcode; eqobs_in.
 Qed.

 Definition iE10rE11 :=
  let RM := {{bad2}} in
  let piH := add_info H RM Vset.empty eE10rE11 H_body_inv11 in
  let piG := add_refl_info G piH in
  let piGA := add_refl_info GAdv piG in
  let piD := add_info Dec RM Vset.empty piGA Dec_body_inv11 in
   adv_info piD.

 Lemma Pr_E10r_E11_bad : forall k (m:Mem.t k),
  (Pr E10r G2b_H (m{!bad2 <-- false!}) (EP k bad) == Pr E11 G2 m (EP k bad))%tord.
 Proof.
  intros k m; rewrite set_bad.
  unfold Pr.
  apply equiv_deno with (kreq_mem {{Y',g_a}}) (req_mem_rel {{bad}} inv11).
  deadcode iE10rE11.
  eqobs_tl iE10rE11.
  unfold inv11; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  unfold req_mem_rel, andR, notR; intros k2 m1 m2 H; 
   decompose [and] H; clear H; intros.
  mem_upd_simpl; simpl; auto.
  intros m1 m2 (H,_); unfold charfun, restr, EP, fone; simpl; rewrite (H _ bad); trivial.
  apply kreq_mem_refl.
 Qed.

 (* We resume the proof *)
 
 Lemma PrG0_bad_11 : forall k (m:Mem.t k),
  (Uabs_diff (Pr E0 G0 m (EP k (b=?=b'))) [1/2] <= 
   Pr E11 G2 m (EP k bad) +
   ((qD_poly k) */ ((qG_poly k + 1)/2^k0 k)) + 
   qD_poly k/2^k1 k + 
   ((qD_poly k) */ ((qD_poly k + qG_poly k)/2^k0 k + [1/2]^k0 k)) + 
   (qD_poly k/2^k1 k))%U%tord.
 Proof.
  intros k m.
  apply Ole_trans with (1:= PrG0_bad_9 m).
  apply Uplus_le_compat; [ | trivial].
  apply Uplus_le_compat; [ | trivial].
  apply Uplus_le_compat; [ | trivial].
  eapply Ole_trans; [ apply (PR_9_bad_10r  m) | ].
  apply Uplus_le_compat; [ | trivial].
  apply Oeq_le; apply Pr_E10r_E11_bad.
 Qed.

 (*************************************************)
 (* Fixing H(S')                                 **)
 (*************************************************)

 Definition H_body1_gen c :=
  [
   If !(S in_dom LH) 
   then [ 
    If S' =?= S then c
    else [rH <$- {0,1}^k0];
    LH <- (S | rH) |::| LH
   ] 
   else [ rH <- LH[{S}] ]
  ].

 Definition H_body1_f := H_body1_gen [rH <- HS'].

 Definition E11f := mkEnv H_body1_f G_body2 Dec_body11.
 (* E11 --> E11f by lazy sampling *)

 Definition SHS' := [ HS'<$- {0,1}^k0 ].

 Definition SH:=
  [ 
   If !(S' in_dom LH) then SHS'  
   else [HS' <- LH[{S'}] ] 
  ].

 Lemma Modify_SH : forall E, Modify E {{HS'}} SH.
 Proof.
   intros E; compute_assertion X t1 (modify (refl1_info (empty_info E E)) Vset.empty SH).
   apply modify_correct in X; eapply Modify_weaken; [eauto | ].
   vm_compute; trivial.
 Qed.

 Lemma EqObs_SH : EqObs (Vset.union {{S',LH}} {{HS'}}) E11 SH E11f SH {{HS'}}.
 Proof.
  eqobs_in.
 Qed.

 Lemma IXSH_global : forall x : VarP.Edec.t, Vset.mem x (Vset.union {{S',LH}} {{HS'}}) -> Var.is_global x.
 Proof.
  apply Vset.forallb_correct.
  intros x y Heq; rewrite Heq; trivial.
  vm_compute; trivial.
 Qed.

 Lemma swap_equiv_H : equiv Meq E11 (proc_body E11 H ++ SH) E11f (SH ++ proc_body E11f H) Meq.
 Proof.
  change (proc_body E11 H) with H_body0; change (proc_body E11f H) with H_body1_f; 
   unfold H_body0, H_body1_f, H_body1_gen.
  Transparent app.
  apply swap_sample_if2.
  4: intros k m1 m2 Heq; rewrite Heq; trivial.
  intros b; apply equiv_Meq_inv_Modify with {{HS'}} (fv_expr (!(S in_dom LH) =?= b)) Vset.empty.
    apply Modify_SH. apply Modify_SH. apply depend_only_EP1.
    vm_compute; trivial.  vm_compute; trivial.
    rewrite proj1_MR; eqobs_in.
  union_mod; [rewrite proj1_MR; trivial | ].
  alloc_l LH LH'; ep. 
  match goal with |- equiv _ _ [?i1; ?i2; ?i3; ?i4] _ _ _ => 
   apply equiv_trans_eq_mem_l with trueR E1 [i1; i2; i4; i3] end.
   rewrite proj1_MR; swap; union_mod; [trivial | eqobs_in].
  ep; cp_test (S' =?= S).
  ep_eq_r (!(S in_dom LH)) true.
    intros k m1 m2 ((H1, H2), _); rewrite <- H1; exact H2.
  alloc_l rH HS'; ep; deadcode; swap; eqobs_in.
  deadcode; swap; eqobs_in.
  red; red; trivial.
  rewrite proj1_MR; apply check_swap_c_correct with (I:= {{S',LH}}) (X:= {{HS'}}) (pi:= fun _ _ => None).
  apply Modify_SH. apply Modify_SH. apply EqObs_SH.  vm_compute; trivial.
 Qed.

 Definition swi_H : forall tg g, option (sw_info SH {{HS'}} {{S',LH}} E11 E11f tg g) :=
    let swiG := add_sw_info_refl SH {{HS'}} {{S',LH}} E11 E11f (Modify_SH E11) (Modify_SH E11f) EqObs_SH IXSH_global (fun t f => None) _ G in
    let swiH := add_sw_info SH {{HS'}} {{S',LH}} E11 E11f (Modify_SH E11) (Modify_SH E11f) EqObs_SH IXSH_global swiG _ _ swap_equiv_H in
    let swiD := add_sw_info_refl SH {{HS'}} {{S',LH}} E11 E11f (Modify_SH E11) (Modify_SH E11f) EqObs_SH IXSH_global swiH _ Dec in
    let swiGA := add_sw_info_refl SH {{HS'}} {{S',LH}} E11 E11f (Modify_SH E11) (Modify_SH E11f) EqObs_SH IXSH_global swiD _ GAdv in
    let swiA := add_sw_info_Adv SH {{HS'}} {{S',LH}} E11 E11f (Modify_SH E11) (Modify_SH E11f) EqObs_SH 
            IXSH_global swiGA _ A PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _ _ _ _ _) (A_wf_E _ _ _ _) in
    let swiA' := add_sw_info_Adv SH {{HS'}} {{S',LH}} E11 E11f (Modify_SH E11) (Modify_SH E11f) EqObs_SH 
            IXSH_global swiA _ A' PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _ _ _ _ _) (A'_wf_E _ _ _ _) in
    swiA'.

 Definition G2f := ([bad <- false] ++ init1 ++ SGR' ++ [S' <- (GR'n | GR'k1)]) ++ (SH ++ tail2).

 Lemma EqObs_E11_E11f : 
  EqObs {{Y',g_a}} E11 G2 E11f G2f {{bad}}.
 Proof.
  apply equiv_trans_eq_mem_r with trueR E11 (G2 ++ SH).
  3: red; red; trivial.
  rewrite proj1_MR; apply equiv_sym; auto.
  unfold G2, G2_, G2f.
  replace (((bad <- false) :: init1 ++ SGR' ++ [S' <- (GR'n | GR'k1)] ++ tail2) ++ SH) with
    (((bad <- false) :: init1 ++ SGR' ++ [S' <- (GR'n | GR'k1)]) ++ (tail2 ++ SH)).
  apply equiv_app with Meq.
  union_mod; [trivial | eqobs_in].
  apply check_swap_c_correct with (I:= {{S',LH}}) (X:= {{HS'}}) (pi:= swi_H).
  apply Modify_SH. apply Modify_SH. apply EqObs_SH.  vm_compute; trivial.
  repeat rewrite app_ass; trivial.
  deadcode iE11; eqobs_in iE11.
 Qed.

 (* Inlining of H in the main *)
 Definition H_body1_u :=
  [ If S' =?= S then [HS'def <- true; rH <- HS'] else H_body0 ]. 

 Definition tail3 := 
  [ 
   T' <- HS' |x| R';
   M <c- A with {};
   HS'def <- true;
   Y' <- ap_f (S' | T');
   Ydef <- true;
   b' <c- A' with {Y'} 
  ].

 Definition G3 := 
  [bad2 <- false; bad3 <- false; HS'def <- false; bad <- false] ++ 
  init1 ++ 
  SGR' ++
  [S' <- (GR'n | GR'k1)] ++ (SHS'++ tail3).

 Definition Dec_body11_gen c1 c2 := 
 [
   If E.Eop O.Oor {testD, qG <! (Elen LG)} then [mn <- (false | one_n)]
   else [
      LD <- (Ydef | c) |::| LD;
      Dc <- 1 +! Dc;
      st <- ap_finv c;
      s <- Efst st;
      t <- Esnd st;
      If s in_dom LH then [
         h <- LH [{s}];
         r <- t |x| h;
         If r in_dom LG then [
            g <- LG [{r}];
            m <- s |x2| g;
            If Esnd m =?= zero_k1 then [mn <- (true | Efst m)]
            else [mn <- (false | one_n)]
         ] else [If R' =?= r _then [bad <- true]; mn <- (false | one_n)]
      ] else [
        If ((S' =?= s) && HS'def) then [
           h <- HS';
           r <- t |x| h;
           If r in_dom LG then [bad1 <- true; bad3 <- true] ++ c1
           else [If R' =?= r _then [bad1 <- true; bad3 <- true] ++ c2; mn <- (false | one_n)]
        ] else [ mn <- (false | one_n) ]
      ]
   ]
 ].

 Definition Dec_body11_u := Dec_body11_gen 
     [g <- LG [{r}];
      m <- s |x2| g;
      If Esnd m =?= zero_k1 then [mn <- (true | Efst m)]
      else [mn <- (false | one_n)]
     ]
     [bad <- true].

 Definition E11u := mkEnv H_body1_u G_body2 Dec_body11_u.
 (* E1f --> E1u : we use an invariant, E1u allows to inline G without adding R' to the list *)
 (* after inlining we revert to E1f' using the previous invariant *)

 Definition eq_dom_def : mem_rel := 
  fun k m1 m2 => E.eval_expr (S' in_dom LH) m1 = E.eval_expr HS'def m2.

 Lemma dec_eq_dom_def : decMR eq_dom_def.
 Proof. 
  unfold eq_dom_def; red; intros.
  assert (W:=T.i_eqb_spec k T.Bool (E.eval_expr (S' in_dom LH) x) (E.eval_expr HS'def y)).
  destruct (T.i_eqb k T.Bool (E.eval_expr (S' in_dom LH) x) (E.eval_expr HS'def y)); auto.
 Qed.

 Lemma dep_eq_dom_def : depend_only_rel eq_dom_def {{S',LH}} {{HS'def}}.
 Proof.
  unfold eq_dom_def; red; simpl; unfold O.eval_op; simpl; intros.
  rewrite <- (H _ LH), <- (H _ S'), <- (H0 _ HS'def); trivial.
 Qed.

 Hint Resolve dec_eq_dom_def dep_eq_dom_def.


 Definition inv_Hfu : mem_rel := 
  (EP1 (S' in_dom LH) |-> EP1 (LH[{S'}] =?= HS')) /-\
  ~- (EP2 (S' in_dom LH)) /-\
  eq_assoc_except S' LH /-\
  eq_dom_def.

 Lemma dec_inv_Hfu : decMR inv_Hfu.
 Proof.
  unfold inv_Hfu; auto 100.
 Qed.

 Lemma dep_inv_Hfu : depend_only_rel inv_Hfu
  (Vset.union
   (Vset.union (fv_expr (S' in_dom LH))
    (fv_expr (LH[{S'}] =?= HS')))
   (Vset.union Vset.empty
    (Vset.union (Vset.add S' (Vset.singleton LH))
     (Vset.add S' (Vset.singleton LH)))))
  (Vset.union (Vset.union Vset.empty Vset.empty)
   (Vset.union (fv_expr (S' in_dom LH))
    (Vset.union (Vset.singleton LH) (Vset.singleton HS'def)))).
  unfold inv_Hfu; auto.
 Qed.

 Definition eE11fE11u : eq_inv_info inv_Hfu E11f E11u.
  refine (@empty_inv_info inv_Hfu _ _ dep_inv_Hfu _ dec_inv_Hfu E11f E11u).
  vm_compute; trivial.
 Defined.

 (* The two oracles are equivalent under the invariant *)
 Lemma H_body1f_H_body1u :
  EqObsInv inv_Hfu {{S,HS',S'}}
  E11f H_body1_f 
  E11u H_body1_u
  {{rH}}.
 Proof.
    unfold H_body1_f, H_body1_u,H_body1_gen.
    cp_test (S' =?= S).
    ep_eq S S'.
      unfold req_mem_rel, andR; intuition; symmetry; rewrite expr_eval_eq; trivial.
    cp_test_l (S' in_dom LH).
    ep_eq_l (LH [{S'}]) HS'.
     unfold inv_Hfu,req_mem_rel, andR, impR; intuition.
    rewrite expr_eval_eq; trivial.
    unfold inv_Hfu; eqobsrel_tail; unfold EP1, EP2, andR, kreq_mem, notR, impR,implMR; simpl; unfold O.eval_op; simpl;
     intros; intuition.
     unfold eq_dom_def; simpl; unfold O.eval_op; simpl.
     mem_upd_simpl.
    unfold inv_Hfu; eqobsrel_tail; unfold EP1, EP2, andR, kreq_mem, notR, impR,implMR; simpl; unfold O.eval_op; simpl;
     unfold O.assoc; simpl; intros.
     decompose [and] H; clear H.
     repeat rewrite Ti_eqb_refl; simpl; split; auto.
     split; auto.
     split.
     intros r Hd; generalize Hd.
     rewrite <- is_true_Ti_eqb, not_is_true_false in Hd.
     rewrite Hd; simpl; decompose [and] H.
     intros Hd'; exact (H4 _ Hd').
     unfold eq_dom_def; simpl; unfold O.eval_op; simpl.
     mem_upd_simpl.
     simpl; rewrite Ti_eqb_refl; trivial.
    cp_test (S in_dom LH).
      unfold inv_Hfu,req_mem_rel, andR, eq_assoc_except; intros.
      decompose [and] H.
      destruct (H4 (m1 S)).
      apply sym_not_eq; rewrite <- is_true_Ti_eqb. exact H5.
      apply trans_eq with (1:= H1); rewrite (H2 _ S); trivial.
    eapply equiv_strengthen; [ | apply equiv_assign].
     unfold req_mem_rel,upd_para, andR; intros.
     decompose [and] H; split.
     unfold kreq_mem; red; intros.
     assert (W1:=Vset.singleton_complete _ _ H1).
     inversion W1; simpl projT1; simpl projT2; repeat rewrite Mem.get_upd_same.
     clear H8 H9 W1 H1 x t.
     destruct H4 as (H4, (H8, (H7, H9))).
     destruct (H7 (m1 S)) as (H10, H11).
     apply sym_not_eq; rewrite <- is_true_Ti_eqb; exact H2.
     eapply trans_eq; [ apply H11 | ]. rewrite (H0 _ S (refl_equal _)); trivial.
     apply dep_inv_Hfu with m1 m2; [ | | trivial]; apply req_mem_upd_disjoint; vm_compute; trivial.
    unfold inv_Hfu, eq_dom_def; eqobsrel_tail; unfold EP1, EP2, andR, kreq_mem, notR, implMR; simpl; unfold O.eval_op; simpl;
     unfold O.assoc; simpl; intros.
     decompose [and] H; clear H.
     mem_upd_simpl.
     rewrite not_is_true_false in H4; rewrite H4; simpl.
     rewrite not_is_true_false in H9; rewrite H9; simpl.
     split; auto.
     split; auto.
     split.
     intros r Hd.
     rewrite <- (H1 _ S); trivial.
     generalize (T.i_eqb_spec k BS_nk1 r (m1 S)); destruct (T.i_eqb k BS_nk1 r (m1 S)); simpl; auto.
     intros HH; exact (H5 _ Hd).
     rewrite H4; trivial.
 Qed.

 Lemma Dec_body11_Dec_body1u :
    EqObsInv inv_Hfu (Vset.add HS' (Vset.add S' (Vset.remove LH ID)))
    E11f Dec_body11 
    E11u Dec_body11_u 
    (Vset.remove LH OD).
 Proof.
  unfold Dec_body11, Dec_body11_u,  Dec_body11_gen.
  cp_test (E.Eop O.Oor {testD, qG <! (Elen LG)}); rewrite proj1_MR.
  eqobs_in eE11fE11u.
  cp_test_l (Efst (ap_finv c) in_dom LH).
  cp_test_r (Efst (ap_finv c) in_dom LH).
  set (C := [
      h <- LH [{Efst (ap_finv c)}];
      LD <- (Ydef | c) |::| LD;
      Dc <- 1 +! Dc;
      st <- ap_finv c;
      s <- Efst st;
      t <- Esnd st;
      r <- t |x| h;
      If r in_dom LG then [
         g <- LG [{r}];
         m <- s |x2| g;
         If Esnd m =?= zero_k1 then [mn <- (true | Efst m)]
         else [mn <- (false | one_n)]
      ] else [If R' =?= r _then [bad <- true]; mn <- (false | one_n)]
   ]).
  apply equiv_trans_eq_mem_l with trueR E11f C.
   rewrite proj1_MR; union_mod; trivial.
   ep; swap; eqobs_in.
  apply equiv_trans_eq_mem_r with trueR E11u C.
   rewrite proj1_MR; union_mod; trivial.
   ep; swap; eqobs_in.
  unfold C; repeat rewrite req_mem_rel_assoc; match goal with |- equiv (req_mem_rel ?I ?P) _ _ _ _ _ =>
   apply equiv_cons with (req_mem_rel (Vset.add h I) inv_Hfu) end.
  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold req_mem_rel,upd_para; intros k m1 m2 (H1, H2); split.
    match goal with 
     |- kreq_mem _  (m1 {!_ <-- ?x!}) (m2 {!_ <-- ?y!}) => replace x with y 
    end.
    apply req_mem_update; trivial.
    unfold inv_Hfu, eq_dom_def, andR  in H2; decompose [and] H2; clear H2.
    destruct (H5 (E.eval_expr (Efst (ap_finv c)) m1)).
    generalize H0 H3; unfold notR, EP2; simpl; unfold O.eval_op; simpl.
    intros W1 W2 Heq; elim W2; rewrite <- (H1 _ S'), <- Heq, (H1 _ c); trivial.
    symmetry; apply trans_eq with (1:= H6).
    simpl; unfold O.eval_op; rewrite (H1 _ c); trivial.
    apply dep_inv_Hfu with m1 m2.
    apply req_mem_upd_disjoint; vm_compute; trivial.
    apply req_mem_upd_disjoint; vm_compute; trivial.
    destruct H2 as ((H2, _), _); trivial.
  eqobs_in eE11fE11u.
   red; red; trivial.
   red; red; trivial.
  ep_eq_r (E.Eop O.Oand {S' =?= Efst (ap_finv c), HS'def}) true.
    unfold inv_Hfu, andR; intros k m1 m2 H; decompose [and] H; clear H.
    unfold eq_dom_def, impR in H2; destruct H2 as (H2, (H4, (H5, (H6, H7)))).
    simpl; unfold O.eval_op; simpl.
    match goal with |- (andb ?x _) = _ => case_eq x; intros Heq; [change (is_true x) in Heq | ] end.
    rewrite is_true_Ti_eqb in Heq; simpl.
    simpl in H7; unfold O.eval_op in H7; simpl in H7; rewrite <- H7, (H2 _ S'), Heq, <- (H2 _ c); trivial.
    apply not_is_true_false in Heq; rewrite is_true_Ti_eqb in Heq.
    apply sym_not_eq in Heq; rewrite <- (H2 _ S') in Heq; trivial.
    destruct (H6 _ Heq).
    elim H1; generalize H3 H; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
    unfold is_true; intros W1 W2; rewrite <- W1; symmetry; rewrite (H2 _ c); trivial.
   set (C1 := [
      LD <- (Ydef | c) |::| LD;
      Dc <- 1 +! Dc;
      st <- ap_finv c;
      s <- Efst st;
      t <- Esnd st;
      r <- t |x| h;
      If r in_dom LG then [
         g <- LG [{r}];
         m <- s |x2| g;
         If Esnd m =?= zero_k1 then [mn <- (true | Efst m)]
         else [mn <- (false | one_n)]
      ] else [If R' =?= r _then [bad <- true]; mn <- (false | one_n)]
   ]).
  apply equiv_trans_eq_mem_l with trueR E11f ((h <- LH [{Efst (ap_finv c)}])::C1).
   rewrite proj1_MR; union_mod; trivial.
   ep; swap; eqobs_in.
  set (C2 := [
      LD <- (Ydef | c) |::| LD;
      Dc <- 1 +! Dc;
      st <- ap_finv c;
      s <- Efst st;
      t <- Esnd st;
      r <- t |x| h;
      If r in_dom LG then [
         bad1 <- true;
         bad3 <- true;
         g <- LG [{r}];
         m <- s |x2| g;
         If Esnd m =?= zero_k1 then [mn <- (true | Efst m)]
         else [mn <- (false | one_n)]
      ] else [If R' =?= r _then [bad1 <- true; bad3 <- true; bad <- true]; mn <- (false | one_n)]
   ]).
  apply equiv_trans_eq_mem_r with trueR E11u ((h <- HS')::C2).
   rewrite proj1_MR; union_mod; trivial.
   ep; swap; eqobs_in.
  unfold C1, C2; repeat rewrite req_mem_rel_assoc; match goal with |- equiv (req_mem_rel ?I ?P) _ _ _ _ _ =>
   apply equiv_cons with (req_mem_rel (Vset.add h I) inv_Hfu) end.
  eapply equiv_strengthen; [ | apply equiv_assign].
    unfold req_mem_rel,upd_para; intros k m1 m2 (H1, H2); split.
    match goal with 
     |- kreq_mem _ (m1 {!_ <-- ?x!}) (m2 {!_ <-- ?y!}) => replace x with y 
    end.
    apply req_mem_update; trivial.
    unfold inv_Hfu, eq_dom_def, andR  in H2; decompose [and] H2; clear H2.
    generalize H H0 H4; unfold EP1, notR,impR, EP2; simpl; unfold O.eval_op; simpl; intros.
    assert (W:=T.i_eqb_spec _ BS_nk1 (E.eval_expr S' m1) (E.eval_expr (Efst (ap_finv c)) m2)).
     destruct (T.i_eqb k BS_nk1 (E.eval_expr S' m1) (E.eval_expr Efst (ap_finv c) m2)).
    simpl in W; unfold O.eval_op in W; simpl in W.
    rewrite is_true_Ti_eqb in H2; rewrite <- (H1 _ HS'), <- H2, W, (H1 _ c); trivial.
    rewrite W, <- (H1 _ c); trivial.
    apply sym_not_eq in W; destruct (H5 _ W).
    elim H0; generalize H4 H9; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
    unfold is_true; intros W1 W2; rewrite <- W1; symmetry; rewrite (H1 _ c); trivial.
    apply dep_inv_Hfu with m1 m2.
    apply req_mem_upd_disjoint; vm_compute; trivial.
    apply req_mem_upd_disjoint; vm_compute; trivial.
    destruct H2 as ((H2, _), _); trivial.
  ep; deadcode eE11fE11u. eqobs_in eE11fE11u.
  red; red; trivial.
  red; red; trivial.
  ep_eq_r (Efst (ap_finv c) in_dom LH) false.
    unfold inv_Hfu, andR, impR, notR; intros k m1 m2 ((H1, H2), H3); decompose [and] H2; clear H2.
    assert (W:= T.i_eqb_spec _ BS_nk1 (E.eval_expr S' m1) (E.eval_expr (Efst (ap_finv c)) m2)).
    destruct (T.i_eqb k BS_nk1 (E.eval_expr S' m1) (E.eval_expr Efst (ap_finv c) m2)).
    apply not_is_true_false in H4; generalize W H4; simpl; unfold O.eval_op; simpl.
    rewrite (H1 _ S'); trivial; intros Heq; rewrite Heq; trivial.
    apply sym_not_eq in W; destruct (H0 _ W).
    apply not_is_true_false in H3; generalize H2 H3; simpl; unfold O.eval_op; simpl.
    rewrite (H1 _ c); trivial; intros W1 W2; rewrite <- W2; symmetry; trivial.
  ep_eq_r (E.Eop O.Oand {S' =?= Efst (ap_finv c), HS'def}) false.
    unfold inv_Hfu, andR, impR, notR; intros k m1 m2 ((H1, H2), H3); decompose [and] H2; clear H2.
    simpl; unfold O.eval_op; simpl.
    match goal with |- (andb ?x _) = _ => case_eq x; intros Heq; [change (is_true x) in Heq | trivial] end.
    rewrite is_true_Ti_eqb in Heq.
    unfold eq_dom_def in H6; simpl; simpl in H6; unfold O.eval_op in H6; simpl in H6.
    rewrite <- H6; rewrite <- not_is_true_false.
    rewrite (H1 _ S'), Heq, <- (H1 _ c); trivial.
  repeat rewrite proj1_MR; eqobs_in eE11fE11u.
 Qed.

 Definition iE11fE11u : eq_inv_info inv_Hfu E11f E11u :=  
   let RM := {{bad1,bad2,bad3}} in
   let piH := add_info H Vset.empty RM eE11fE11u H_body1f_H_body1u in
   let piG := add_refl_info G piH in
   let piGA := add_refl_info GAdv piG in
   let piD := add_info Dec Vset.empty RM piGA Dec_body11_Dec_body1u in
   adv_info piD.

 (******************)
 (** E11u -> E11f' *)
 (******************)

 Definition H_body1_f' := H_body1_gen [bad1 <- true; bad2 <- true; HS'def <- true; rH <- HS'].
 Definition E11f' := mkEnv H_body1_f' G_body2 Dec_body11_u.

 Definition inv_Hf'u : mem_rel := 
  (EP1 (S' in_dom LH) |-> (EP1 (LH[{S'}] =?= HS') /-\ EP1 HS'def)) /-\
    ~- (EP2 (S' in_dom LH)) /-\
    eq_assoc_except S' LH.

 Lemma dec_inv_Hf'u : decMR inv_Hf'u.
 Proof.
  unfold inv_Hf'u; auto 100.
 Qed.

 Lemma dep_inv_Hf'u : depend_only_rel inv_Hf'u 
  (Vset.union
   (Vset.union (fv_expr (S' in_dom LH))
    (Vset.union (fv_expr (LH[{S'}] =?= HS')) (fv_expr HS'def)))
   (Vset.union Vset.empty (Vset.add S' (Vset.singleton LH))))
  (Vset.union
   (Vset.union Vset.empty (Vset.union Vset.empty Vset.empty))
   (Vset.union (fv_expr (S' in_dom LH)) (Vset.singleton LH))).
 Proof.
  unfold inv_Hf'u; auto.
 Qed.

 Definition eE11f'E11u : eq_inv_info inv_Hf'u E11f' E11u.
  refine (@empty_inv_info inv_Hf'u _ _ dep_inv_Hf'u _ dec_inv_Hf'u E11f' E11u).
  vm_compute; trivial.
 Defined.

 (* The two oracles are equivalent under the invariant *)
 Lemma H_body1f'_H_body1u :
  EqObsInv inv_Hf'u {{HS'def,S,HS',S'}}
  E11f' H_body1_f' 
  E11u H_body1_u 
  {{HS'def,rH}}.
 Proof.
    unfold H_body1_f', H_body1_u,H_body1_gen.
    cp_test (S' =?= S).
    ep_eq S S'.
      unfold req_mem_rel, andR; intuition; symmetry; rewrite expr_eval_eq; trivial.
    cp_test_l (S' in_dom LH).
    ep_eq_r HS'def true.
     unfold inv_Hf'u, eq_dom_def,andR, impR; intros k m1 m2 (((H1, H2), _), H3); decompose [and] H2; clear H2.
     destruct (H H3); simpl; unfold O.eval_op; simpl; rewrite <- (H1 _ HS'def); trivial.
    ep_eq_l (LH [{S'}]) HS'.
     unfold inv_Hf'u,req_mem_rel, andR, impR; intuition.
     rewrite expr_eval_eq; trivial.
    unfold inv_Hf'u; eqobsrel_tail; unfold EP1, EP2, andR, kreq_mem, notR, impR,implMR; simpl; unfold O.eval_op; simpl;
     intros; intuition.
    unfold inv_Hf'u; eqobsrel_tail; unfold EP1, EP2, andR, kreq_mem, notR, impR,implMR; simpl; unfold O.eval_op; simpl;
     unfold O.assoc; simpl; intros.
     decompose [and] H; clear H.
     repeat rewrite Ti_eqb_refl; simpl; split; auto.
     split; auto.
     intros r Hd; generalize Hd.
     rewrite <- is_true_Ti_eqb, not_is_true_false in Hd.
     rewrite Hd; simpl; decompose [and] H.
     intros Hd'; exact (H5 _ Hd').
    cp_test (S in_dom LH).
      unfold inv_Hf'u,req_mem_rel, andR, eq_assoc_except; intros.
      decompose [and] H.
      destruct (H5 (m1 S)).
      apply sym_not_eq; rewrite <- is_true_Ti_eqb. exact H4.
      apply trans_eq with (1:= H1); rewrite (H2 _ S); trivial.
    eapply equiv_strengthen; [ | apply equiv_assign].
     unfold req_mem_rel,upd_para, andR; intros.
     decompose [and] H; split.
     apply req_mem_weaken with {{rH,HS'def}}.
     vm_compute; trivial.
     match goal with 
      |- _ {!_ <-- ?v1!} =={_} m2 {!_ <-- ?v2!} => replace v1 with v2 
     end.
     apply req_mem_update.
     apply req_mem_weaken with (2:= H0); vm_compute; trivial.
     symmetry; unfold notR,EP1 in H2; simpl in H2; unfold O.eval_op in H2; simpl in H2.
      rewrite is_true_Ti_eqb in H2; apply sym_not_eq in H2.
      unfold inv_Hf'u, andR in H4; decompose [and] H4; clear H4.
      elim (H9 _ H2); simpl; unfold O.eval_op; simpl; intros.
      rewrite H7, (H0 _ S); trivial.
     apply dep_inv_Hf'u with m1 m2; [ | | trivial]; apply req_mem_upd_disjoint; vm_compute; trivial.
    unfold inv_Hf'u; eqobsrel_tail; unfold EP1, EP2, andR, kreq_mem, notR, implMR; simpl; unfold O.eval_op; simpl;
     unfold O.assoc; simpl; intros.
     decompose [and] H; clear H.
     rewrite not_is_true_false in H4; rewrite H4; simpl.
     rewrite not_is_true_false in H8; rewrite H8; simpl.
     split; auto.
     split; auto.
     intros r Hd.
     rewrite <- (H1 _ S); trivial.
     generalize (T.i_eqb_spec k BS_nk1 r (m1 S)); destruct (T.i_eqb k BS_nk1 r (m1 S)); simpl; auto.
     intros HH; exact (H6 _ Hd).
 Qed.

 Lemma Dec_body11u_Dec_body11u :
    EqObsInv inv_Hf'u (Vset.add HS'def (Vset.add HS' (Vset.add S' (Vset.remove LH ID))))
    E11f' Dec_body11_u 
    E11u Dec_body11_u 
    (Vset.remove LH OD).
 Proof.
  unfold Dec_body11_u,  Dec_body11_gen.
  cp_test (E.Eop O.Oor {testD, qG <! (Elen LG)}); rewrite proj1_MR.
  eqobs_in eE11f'E11u.
  cp_test_l (Efst (ap_finv c) in_dom LH).
  cp_test_r (Efst (ap_finv c) in_dom LH).
  set (C := [
      h <- LH [{Efst (ap_finv c)}];
      LD <- (Ydef | c) |::| LD;
      Dc <- 1 +! Dc;
      st <- ap_finv c;
      s <- Efst st;
      t <- Esnd st;
      r <- t |x| h;
      If r in_dom LG then [
         g <- LG [{r}];
         m <- s |x2| g;
         If Esnd m =?= zero_k1 then [mn <- (true | Efst m)]
         else [mn <- (false | one_n)]
      ] else [If R' =?= r _then [bad <- true]; mn <- (false | one_n)]
   ]).
  apply equiv_trans_eq_mem_l with trueR E11f' C.
   rewrite proj1_MR; union_mod; trivial.
   ep; swap; eqobs_in.
  apply equiv_trans_eq_mem_r with trueR E11u C.
   rewrite proj1_MR; union_mod; trivial.
   ep; swap; eqobs_in.
  unfold C; repeat rewrite req_mem_rel_assoc; match goal with |- equiv (req_mem_rel ?I ?P) _ _ _ _ _ =>
   apply equiv_cons with (req_mem_rel (Vset.add h I) inv_Hf'u) end.
  eapply equiv_strengthen; [ | apply equiv_assign].
    unfold req_mem_rel,upd_para; intros k m1 m2 (H1, H2); split.
    match goal with 
     |- kreq_mem _ (m1 {!_ <-- ?x!}) (m2 {!_ <-- ?y!}) => replace x with y 
    end.
    apply req_mem_update; trivial.
    unfold inv_Hf'u, andR  in H2; decompose [and] H2; clear H2.
    destruct (H6 (E.eval_expr (Efst (ap_finv c)) m1)).
    generalize H0 H3; unfold notR, EP2; simpl; unfold O.eval_op; simpl.
    intros W1 W2 Heq; elim W2; rewrite <- (H1 _ S'), <- Heq, (H1 _ c); trivial.
    symmetry; apply trans_eq with (1:= H5).
    simpl; unfold O.eval_op; rewrite (H1 _ c); trivial.
    apply dep_inv_Hf'u with m1 m2.
    apply req_mem_upd_disjoint; vm_compute; trivial.
    apply req_mem_upd_disjoint; vm_compute; trivial.
    destruct H2 as ((H2, _), _); trivial.
  eqobs_in eE11f'E11u.
   red; red; trivial.
   red; red; trivial.
  ep_eq_r (E.Eop O.Oand {S' =?= Efst (ap_finv c), HS'def}) true.
    unfold inv_Hf'u, andR; intros k m1 m2 H; decompose [and] H; clear H.
    unfold impR in H2; destruct H2 as (H2, (H4, (H5, H6))).
    simpl; unfold O.eval_op; simpl.
    match goal with |- (andb ?x _) = _ => case_eq x; intros Heq; [change (is_true x) in Heq | ] end.
    rewrite is_true_Ti_eqb in Heq; simpl.
    generalize H4 H3; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
    rewrite <- (H2 _ HS'def), (H2 _ S'), (H2 _ c), Heq; trivial.
    intros W1 W2; destruct (W1 W2); trivial.
    apply not_is_true_false in Heq; rewrite is_true_Ti_eqb in Heq.
    apply sym_not_eq in Heq; rewrite <- (H2 _ S') in Heq; trivial.
    destruct (H6 _ Heq).
    elim H1; generalize H3 H; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
    unfold is_true; intros W1 W2; rewrite <- W1; symmetry; rewrite (H2 _ c); trivial.
   set (C1 := [
      LD <- (Ydef | c) |::| LD;
      Dc <- 1 +! Dc;
      st <- ap_finv c;
      s <- Efst st;
      t <- Esnd st;
      r <- t |x| h;
      If r in_dom LG then [
         g <- LG [{r}];
         m <- s |x2| g;
         If Esnd m =?= zero_k1 then [mn <- (true | Efst m)]
         else [mn <- (false | one_n)]
      ] else [If R' =?= r _then [bad <- true]; mn <- (false | one_n)]
   ]).
  apply equiv_trans_eq_mem_l with trueR E11f' ((h <- LH [{Efst (ap_finv c)}])::C1).
   rewrite proj1_MR; union_mod; trivial.
   ep; swap; eqobs_in.
  set (C2 := [
      LD <- (Ydef | c) |::| LD;
      Dc <- 1 +! Dc;
      st <- ap_finv c;
      s <- Efst (st);
      t <- Esnd (st);
      r <- t |x| h;
      If r in_dom LG then [
         bad1 <- true;
         bad3 <- true;
         g <- LG [{r}];
         m <- s |x2| g;
         If Esnd m =?= zero_k1 then [mn <- (true | Efst m)]
         else [mn <- (false | one_n)]
      ] else [If R' =?= r _then [bad1 <- true; bad3 <- true; bad <- true]; mn <- (false | one_n)]
   ]).
  apply equiv_trans_eq_mem_r with trueR E11u ((h <- HS')::C2).
   rewrite proj1_MR; union_mod; trivial.
   ep; swap; eqobs_in.
  unfold C1, C2; repeat rewrite req_mem_rel_assoc; match goal with |- equiv (req_mem_rel ?I ?P) _ _ _ _ _ =>
   apply equiv_cons with (req_mem_rel (Vset.add h I) inv_Hf'u) end.
  eapply equiv_strengthen; [ | apply equiv_assign].
    unfold req_mem_rel,upd_para; intros k m1 m2 (H1, H2); split.
    match goal with 
     |- kreq_mem _ (m1 {!_ <-- ?x!}) (m2 {!_ <-- ?y!}) => replace x with y 
    end.
    apply req_mem_update; trivial.
    unfold inv_Hf'u, eq_dom_def, andR  in H2; decompose [and] H2; clear H2.
    generalize H H0 H4; unfold EP1, notR,impR, EP2; simpl; unfold O.eval_op; simpl; intros.
    assert (W:= T.i_eqb_spec _ BS_nk1 (E.eval_expr S' m1) (E.eval_expr (Efst (ap_finv c)) m2)).
     destruct (T.i_eqb k BS_nk1 (E.eval_expr S' m1) (E.eval_expr Efst (ap_finv c) m2)).
    simpl in W; unfold O.eval_op in W; simpl in W.
    rewrite W, <- (H1 _ c)in H2; trivial. destruct (H2 H7).
    rewrite is_true_Ti_eqb in H8; rewrite <- (H1 _ HS'), <- H8; trivial.
    apply sym_not_eq in W; destruct (H6 _ W).
    elim H0; generalize H4 H8; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
    unfold is_true; intros W1 W2; rewrite <- W1; symmetry; rewrite (H1 _ c); trivial.
    apply dep_inv_Hf'u with m1 m2.
    apply req_mem_upd_disjoint; vm_compute; trivial.
    apply req_mem_upd_disjoint; vm_compute; trivial.
    destruct H2 as ((H2, _), _); trivial.
  ep; deadcode eE11f'E11u. eqobs_in eE11f'E11u.
  red; red; trivial.
  red; red; trivial.
  ep_eq_r (Efst (ap_finv c) in_dom LH) false.
    unfold inv_Hf'u, andR, impR, notR; intros k m1 m2 ((H1, H2), H3); decompose [and] H2; clear H2.
    assert (W:= T.i_eqb_spec _ BS_nk1 (E.eval_expr S' m1) (E.eval_expr (Efst (ap_finv c)) m2)).
    destruct (T.i_eqb k BS_nk1 (E.eval_expr S' m1) (E.eval_expr Efst (ap_finv c) m2)).
    apply not_is_true_false in H4; generalize W H4; simpl; unfold O.eval_op; simpl.
    rewrite (H1 _ S'); trivial; intros Heq; rewrite Heq; trivial.
    apply sym_not_eq in W; destruct (H5 _ W).
    apply not_is_true_false in H3; generalize H0 H3; simpl; unfold O.eval_op; simpl.
    rewrite (H1 _ c); trivial; intros W1 W2; rewrite <- W2; symmetry; trivial.
  repeat rewrite proj1_MR; eqobs_in eE11f'E11u.
 Qed.

 Definition iE11f'E11u : eq_inv_info inv_Hf'u E11f' E11u :=  
  let RM := {{bad1,bad2,bad3}} in
  let piH := add_info H Vset.empty RM eE11f'E11u H_body1f'_H_body1u in
  let piG := add_refl_info G piH in
  let piGA := add_refl_info GAdv piG in
  let piD := add_info Dec Vset.empty RM piGA Dec_body11u_Dec_body11u in
   adv_info piD.

 Definition iE11u := iEiEi H_body1_u G_body2 Dec_body11_u.

 Lemma EqObs_E11_E11f' : 
  EqObs {{Y',g_a}} 
  E11 G2 
  E11f' ((bad1 <- false)::G3) 
  {{bad}}.
 Proof.
  apply EqObs_trans with (1:= EqObs_E11_E11f).
  apply EqObs_trans with E11u ((bad1 <- false)::G3).
  apply EqObs_trans with E11u ([bad1 <- false; bad2<- false; bad3<- false; HS'def<-false] ++ G2f).
  apply equiv_weaken with (req_mem_rel {{bad}} inv_Hfu).
    intros k m1 m2 (H1, H2); trivial.
  eqobs_tl iE11fE11u.
  ep; deadcode iE11fE11u.
  unfold inv_Hfu, eq_dom_def; eqobsrel_tail; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; intros. 
  mem_upd_simpl.
  simpl; intuition. discriminate.
  ep iE11u.
  sinline_l iE11u H.
  eqobs_in iE11u.
  apply EqObs_sym.
  eqobs_tl iE11f'E11u.
   match goal with
  |- equiv _ _ [?i1;?i2;?i3;?i4;?i5;?i6;?i7;?i8;?i9;?i10;?i11;?i12;?i13;?i14;?i15;?i16;?i17;?i18;?i19] _ _ (req_mem_rel ?X _) => 
     change [i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15; i16; i17; i18; i19] with
       ([i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15; i16; i17; i18]++[i19]);
   apply equiv_app with (req_mem_rel (Vset.add HS'def X) inv_Hf'u) 
   end.
  eqobs_tl iE11f'E11u.
   unfold inv_Hf'u, eq_dom_def; eqobsrel_tail; simpl; unfold O.eval_op; simpl.
   intros k m1 m2 H; intros. 
   simpl; intuition. discriminate.
  unfold inv_Hf'u; eqobsrel_tail; simpl; unfold O.eval_op; simpl.
   unfold andR; intros k m1 m2 H; decompose [and] H; clear H; intros. 
   simpl; intuition.
   destruct (H2 H); trivial.
 Qed.


 Definition H_body1_r := H_body1_gen [bad1 <- true; bad2 <- true; rH <$- {0,1}^k0].
 Definition Dec_body11_r := Dec_body11_gen [mn <- (false | one_n)] (@nil _).

 Definition E11r := mkEnv H_body1_r G_body2 Dec_body11_r.
 (* E11f' --> E11r fundamental lemma *)
 Definition iE11r := iEiEi H_body1_r G_body2 Dec_body11_r.

 Lemma PR_11_bad : forall k (m:Mem.t k),
    (Pr E11 G2 m (EP k bad) <= 
       (Pr E11r G3 (m{! bad1 <-- false !}) (EP k bad) + Pr E11r G3 (m{!bad1 <-- false!}) (EP k bad1))%U)%tord.
 Proof.
   intros k m ; set (mb:= m{!bad1 <-- false!}).
   transitivity (Pr E11f' G3 mb (EP k bad)).
    apply Oeq_le; unfold mb; rewrite set_bad.
    apply EqObs_Pr with {{Y',g_a}}.
    apply EqObs_E11_E11f'.
   apply Uabs_diff_le_plus.
   apply upto_bad_Uabs_diff with 
     (i_upto bad1 H_body1_f' G_body2 Dec_body11_u H_body1_r G_body2 Dec_body11_r).
    trivial.
    vm_compute; trivial.
    apply is_lossless_correct with (refl1_info iE11r); vm_compute; trivial.
 Qed.

 (***************************)
 (** bad1 --> bad2 \/ bad3 **)
 (***************************)

 Definition inv_bad1_23 := EP1 bad1 |-> EP2 (bad2 || bad3).

 Lemma dec_inv_bad1_23 : decMR inv_bad1_23.
 Proof.
  unfold inv_bad1_23; auto 100.
 Qed.

 Lemma dep_inv_bad1_23 : depend_only_rel inv_bad1_23 
  (Vset.union (fv_expr bad1) Vset.empty)
  (Vset.union Vset.empty (fv_expr (E.Eop O.Oor {bad2, bad3}))).
 Proof.
  unfold inv_bad1_23; auto.
 Qed.

 Definition eE11r : eq_inv_info inv_bad1_23 E11r E11r.
  refine (@empty_inv_info inv_bad1_23 _ _ dep_inv_bad1_23 _ dec_inv_bad1_23 E11r E11r).
  vm_compute; trivial.
 Defined.

 Lemma H_body1_r_1_23 :
  EqObsInv inv_bad1_23 
  {{bad1,bad2,bad3,LH,HS'def,S,HS',S'}}
  E11r H_body1_r 
  E11r H_body1_r 
  {{LH,bad1,bad2,HS'def,rH}}.
 Proof.
  unfold H_body1_r, H_body1_gen.
  cp_test (S in_dom LH); rewrite proj1_MR.
   eqobs_in eE11r.
  cp_test (S' =?= S); rewrite proj1_MR.
   unfold inv_bad1_23; eqobsrel_tail; simpl; unfold O.eval_op; simpl; red; intros; trivial.
  eqobs_in eE11r.
 Qed.

 Lemma Dec_body11r_1_23 :
  EqObsInv inv_bad1_23 (Vset.add bad1 (Vset.add bad2 (Vset.add bad3 
   (Vset.add HS'def (Vset.add HS' (Vset.add S' ID))))))
  E11r Dec_body11_r 
  E11r Dec_body11_r 
  (Vset.add bad1 (Vset.add bad2 (Vset.add bad3 OD))).
 Proof.
  unfold Dec_body11_r, Dec_body11_gen.
  cp_test (E.Eop O.Oor {testD, qG <! (Elen LG)}); rewrite proj1_MR.
  eqobs_in eE11r.
  cp_test (Efst (ap_finv c) in_dom LH); rewrite proj1_MR.
  eqobs_in eE11r.
  cp_test (E.Eop O.Oand {S' =?= Efst (ap_finv c), HS'def}); rewrite proj1_MR.
  cp_test (Esnd (ap_finv c) |x| HS' in_dom LG); rewrite proj1_MR.
    unfold inv_bad1_23; eqobsrel_tail; simpl; unfold O.eval_op; simpl; red; intros; trivial.
    rewrite orb_true_r; trivial.
  cp_test (R' =?= Esnd (ap_finv c) |x| HS'); rewrite proj1_MR.
    unfold inv_bad1_23; eqobsrel_tail; simpl; unfold O.eval_op; simpl; red; intros; trivial.
    rewrite orb_true_r; trivial.
  eqobs_in eE11r.
  eqobs_in eE11r.
 Qed.

 Definition iE11r_1_23 : eq_inv_info inv_bad1_23 E11r E11r :=  
   let RM := Vset.empty in
   let piH := add_info H Vset.empty RM eE11r H_body1_r_1_23 in
   let piG := add_refl_info G piH in
   let piGA := add_refl_info GAdv piG in
   let piD := add_info Dec Vset.empty RM piGA Dec_body11r_1_23 in
   adv_info piD.

 Lemma PR_11r_bad1 : forall k m,
   ((Pr E11r G3 (m{!bad1 <-- false!}) (EP k bad1) 
     <= Pr E11r G3 (m{!bad1 <-- false!}) (EP k bad2) + Pr E11r G3 (m{!bad1 <-- false!}) (EP k bad3))%U)%tord.
 Proof.
  intros k m; transitivity 
   (Pr E11r G3 (m{!bad1 <-- false!}) (EP k (bad2 || bad3))).
  repeat rewrite set_bad.
  apply equiv_deno_le with 
   (kreq_mem {{bad1,Y',g_a}})
   (req_mem_rel Vset.empty inv_bad1_23).
  eqobs_tl iE11r_1_23.
  unfold inv_bad1_23; eqobsrel_tail; simpl; unfold O.eval_op; simpl; red; intros; trivial.
  unfold inv_bad1_23, impR,EP1, EP2, EP, charfun, restr, fone; simpl; unfold O.eval_op; simpl; intros m1 m2 (_, H).
  destruct (m1 bad1); [ rewrite H| ]; trivial.
  trivial.
  transitivity (Pr E11r G3 (m {!bad1 <-- false!}) ((EP k bad2) [||] (EP k bad3))).
  unfold Pr; apply mu_le_compat; [ trivial | ].
  unfold charfun, EP, orP, restr; simpl; unfold O.eval_op; simpl; trivial.
  apply Pr_or.
 Qed.

 (*************************************************)
 (* We focus on the probability of bad in E11r G3 *)
 (*************************************************)

 Definition Dec_body12 :=
 [
   If E.Eop O.Oor {testD, qG <! (Elen LG)} then [mn <- (false | one_n)]
   else [
      LD <- (Ydef | c) |::| LD;
      Dc <- 1 +! Dc;
      st <- ap_finv c;
      s <- Efst (st);
      t <- Esnd (st);
      If s in_dom LH then [
         h <- LH [{s}];
         r <- t |x| h;
         If r in_dom LG then [
            g <- LG [{r}];
            m <- s |x2| g;
            If Esnd m =?= zero_k1 then [ mn <- (true | Efst m) ]
            else [ mn <- (false | one_n) ]
         ] else [ mn <- (false | one_n) ]
      ] else [ mn <- (false | one_n) ]
   ]
 ].

 Definition E12 := mkEnv H_body0 G_body0 Dec_body12.

 Definition Bad :=
  E.Eexists tc
   (let c := Esnd (tc) in
    let s := Efst (ap_finv c) in
    let t := Esnd (ap_finv c) in
    let h := LH [{s}] in
    let r := t |x| h in
    E.Eop O.Oand {s in_dom LH, R' =?= r}) LD.

 Definition inv_bad := 
   (EP1 bad |-> EP2 ((R' in_dom LG) || Bad)) /-\
   (EP2 ((Gc <=! qG) && (Dc <=! qD) && 
             ((Elen LG) <=! Gc) && ((Elen LD) <=! Dc))).

 Lemma dec_inv_bad : decMR inv_bad.
 Proof.
   unfold inv_bad; auto 100.
 Qed.

 Lemma dep_inv_bad : depend_only_rel inv_bad   
  (Vset.union (Vset.union (fv_expr bad) Vset.empty) Vset.empty)
  (Vset.union
   (Vset.union Vset.empty
    (fv_expr (E.Eop O.Oor {R' in_dom LG, Bad})))
   (fv_expr (E.Eop O.Oand
    {E.Eop O.Oand {E.Eop O.Oand {Gc <=! qG, Dc <=! qD}, Elen LG <=! Gc}, 
     Elen LD <=! Dc}))).
 Proof.
  unfold inv_bad; auto.
 Qed.

 Definition eE11rE12 : eq_inv_info inv_bad E11r E12.
  refine (@empty_inv_info inv_bad _ _ dep_inv_bad _ dec_inv_bad E11r E12).
  vm_compute; trivial.
 Defined.

 Hint Resolve dec_inv_bad dep_inv_bad.

 Lemma Gadv_body2_Gadv_body0 :
  EqObsInv inv_bad 
  {{R',Gc,Radv,LG}}
  E11r GAdv_body1
  E12 GAdv_body1
  {{LG,Gc,rGadv}}.
 Proof.
 Opaque leb.
  unfold GAdv_body1.
  cp_test (qG <=! Gc).
   rewrite proj1_MR; eqobs_in eE11rE12.
  inline eE11rE12 G.
  ep; deadcode eE11rE12.
  cp_test (Radv in_dom LG).
  rewrite proj1_MR; eqobs_tl eE11rE12.
   unfold inv_bad; eqobsrel_tail; simpl; unfold O.eval_op; simpl; red; intros; trivial.
   unfold andR, EP2, notR in H; decompose [and] H; clear H.
   split; intros.
   assert (W:= H1 H); simpl in W; unfold O.eval_op in W; simpl in W.
   rewrite is_true_orb in W |- *; destruct W; auto.
   right; rewrite is_true_existsb in H3 |- *; destruct H3 as (x, (Hin, H3)); exists x; split; trivial.
   repeat (rewrite Mem.get_upd_same in H3|| (rewrite Mem.get_upd_diff in H3; [ | discriminate])); trivial.
   generalize H4 H5; simpl; unfold O.eval_op; simpl.
   repeat rewrite is_true_andb; repeat rewrite is_true_leb; intros; omega'.
  cp_test (R' =?= Radv).
   unfold inv_bad; eqobsrel_tail; simpl; unfold O.eval_op; simpl; red; intros; trivial.
   unfold andR, EP1, EP2 in H; decompose [and] H; clear H.
   simpl in H11; unfold O.eval_op in H11; simpl in H11; rewrite H11; simpl; split; trivial.
   generalize H6 H8; unfold notR; simpl; unfold O.eval_op; simpl.
   repeat rewrite is_true_andb; repeat rewrite is_true_leb; intros; omega'.
  unfold inv_bad; eqobsrel_tail; simpl; unfold O.eval_op; simpl; red; intros; trivial.
   unfold andR, impR, notR, EP2, EP1 in H; decompose [and] H; clear H; split; intros.
   assert (H12 := H3 H); simpl in H12; unfold O.eval_op in H12; simpl in H12.
   rewrite <- orb_assoc, is_true_orb; right; trivial.
   rewrite is_true_orb in H12 |- *; destruct H12; auto.
   right; rewrite is_true_existsb in H9 |- *; destruct H9 as (x, (Hin, H9)); exists x; split; trivial.
   repeat (rewrite Mem.get_upd_same in H9|| (rewrite Mem.get_upd_diff in H9; [ | discriminate])); trivial.
   generalize H6 H8; unfold notR; simpl; unfold O.eval_op; simpl.
   repeat rewrite is_true_andb; repeat rewrite is_true_leb; intros; omega'.
 Qed.

 Lemma H_body1_r_H_body0 : 
  EqObsInv inv_bad {{S,LH}}
  E11r H_body1_r
  E12 H_body0 
  {{LH,rH}}.
 Proof.
  unfold H_body1_r, H_body0, H_body1_gen.
  deadcode eE11rE12. 
  cp_test (S in_dom LH).
  rewrite proj1_MR; eqobs_in eE11rE12.
  unfold inv_bad; eqobsrel_tail; unfold impR, EP1, EP2; simpl; unfold O.eval_op; simpl; red; intros.
  unfold andR in H; decompose [and] H; clear H; split; intros; trivial.
  assert (W := H2 H); rewrite is_true_orb in W |- *; destruct W; auto.
  right; rewrite is_true_existsb in H4 |- *; destruct H4 as (x, (Hin, H4)); exists x; split; trivial.
  unfold O.assoc; simpl.
  repeat (rewrite Mem.get_upd_same in H4|| (rewrite Mem.get_upd_diff in H4; [ | discriminate])).
  match goal with
   |- is_true (andb (orb ?x _) _) => case_eq x; intros Heq; [change (is_true x) in Heq | trivial] end.
  elim H6; rewrite is_true_Ti_eqb in Heq; rewrite <- Heq.
  rewrite is_true_andb in H4; destruct H4 as (H4, _); trivial.
 Qed.

 Lemma Dec_body11_r_Dec_body12 :
  EqObsInv inv_bad (Vset.add R' (Vset.add LD (Vset.remove bad ID)))
    E11r Dec_body11_r
    E12 Dec_body12 
    (Vset.add LD (Vset.remove bad OD)).
 Proof.
  unfold Dec_body11_r, Dec_body12.
  cp_test (E.Eop O.Oor {testD, qG <! (Elen LG)}).
  rewrite proj1_MR; eqobs_in eE11rE12. 
  deadcode eE11rE12. 
  cp_test (Efst (ap_finv c) in_dom LH).
  cp_test (Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}]) in_dom LG).
  eqobs_tl eE11rE12.
  unfold inv_bad; eqobsrel_tail; unfold EP1,EP2; simpl; unfold O.eval_op; simpl;
   unfold andR, impR, notR; intros k m1 m2 H; decompose [and] H; clear H; split; intros.
  rewrite is_true_orb in H1 |- *; destruct (H1 H); auto.
  right; rewrite is_true_existsb in H7 ; destruct H7 as (x, (Hin, H7)).
  repeat (rewrite Mem.get_upd_same in H7|| (rewrite Mem.get_upd_diff in H7; [ | discriminate])).
  rewrite is_true_orb; right; rewrite is_true_existsb; exists x; split; auto.
   generalize H4 H6; repeat (rewrite is_true_andb || rewrite is_true_orb || rewrite is_true_leb); omega'.
  cp_test_l (R' =?= Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}])).
  unfold inv_bad; eqobsrel_tail; unfold EP1,EP2; simpl; unfold O.eval_op; simpl.
   unfold andR, impR, notR; intros k m1 m2 H; decompose [and] H; clear H; intros.
  change UOp.Tnk1 with BS_nk1 in H8; change UOp.Tnk1 with BS_nk1 in H9; rewrite H8.
  rewrite <- (H0 _ c), <- (H0 _ R'), <- (H0 _ LH), H9; simpl; trivial.
  split; [intros; apply orb_true_r|].
   generalize H4 H6; repeat (rewrite is_true_andb || rewrite is_true_orb || rewrite is_true_leb); omega'.
  unfold inv_bad; eqobsrel_tail; unfold EP1,EP2; simpl; unfold O.eval_op; simpl;
   unfold andR, impR, notR; intros k m1 m2 H; decompose [and] H; clear H; split; intros.
  rewrite is_true_orb in H1 |- *; destruct (H1 H); auto.
  right; rewrite is_true_existsb in H2 ; destruct H2 as (x, (Hin, H2)).
  repeat (rewrite Mem.get_upd_same in H2|| (rewrite Mem.get_upd_diff in H2; [ | discriminate])).
  rewrite is_true_orb; right; rewrite is_true_existsb; exists x; split; auto.
   generalize H4 H6; repeat (rewrite is_true_andb || rewrite is_true_orb || rewrite is_true_leb); omega'.
  unfold inv_bad; eqobsrel_tail; unfold EP1,EP2; simpl; unfold O.eval_op; simpl;
   unfold andR, impR, notR; intros k m1 m2 H; decompose [and] H; clear H; split; intros.
  rewrite is_true_orb in H1 |- *; destruct (H1 H); auto.
  right; rewrite is_true_existsb in H5 ; destruct H5 as (x, (Hin, H5)).
  repeat (rewrite Mem.get_upd_same in H5|| (rewrite Mem.get_upd_diff in H5; [ | discriminate])).
  rewrite is_true_orb; right; rewrite is_true_existsb; exists x; split; auto.
    generalize H4 H6; repeat (rewrite is_true_andb || rewrite is_true_orb || rewrite is_true_leb); omega'.
 Qed.

 Definition iE12 := iEiEi H_body0 G_body0 Dec_body12.

 Definition iE11rE12 :=
   let RM := Vset.empty in
   let piH := my_add_info H RM RM iE11r iE12 eE11rE12 H_body1_r_H_body0 in 
   let piGA := my_add_info GAdv RM RM iE11r iE12 piH Gadv_body2_Gadv_body0 in
   let piD := my_add_info Dec RM RM iE11r iE12 piGA Dec_body11_r_Dec_body12 in
   adv_info piD.

 Lemma Pr_E11r_bad : forall k m, 
  ((Pr E11r G3 (m{! bad1 <-- false !}) (EP k bad) <=
   (qG_poly k /2^k0 k) + (qD_poly k /2^k0 k))%U)%tord.
 Proof.
  intros k m.
  transitivity 
   (Pr E12 G3 (m{! bad1 <-- false !}) (EP k 
    (((Elen LG) <=! qG) && ((Elen LD) <=! qD) &&
     ((R' in_dom LG) || Bad)))).
  unfold Pr.
  apply equiv_deno_le with (kreq_mem {{Y',g_a}}) (req_mem_rel Vset.empty inv_bad).
  eqobs_tl iE11rE12.
  unfold inv_bad; eqobsrel_tail; unfold EP1, EP2;
   simpl; unfold O.eval_op; simpl; red; intros.
  Transparent leb.
  simpl; auto.
  unfold inv_bad, impR, EP1, EP2, EP, charfun, restr, fone.
  simpl; unfold O.eval_op; simpl; intros m1 m2 (_, (H1, H2)).
  destruct (m1 bad); trivial.
  rewrite H1; trivial.
  rewrite andb_true_r.
  match goal with
  |- (_ <= (if ?X then _ else _))%tord => case_eq X; intros Heq; trivial
  end.
  apply not_is_true_false in Heq.
  elimtype False.
  generalize H2 Heq; repeat (rewrite is_true_andb || rewrite is_true_leb); omega'.
  trivial.
  set (C:=[
   Ydef <- false;
   LG <- E.Cnil (T.Pair BS_k0 BS_nk1);
   LH <- E.Cnil BS_k;
   LD <- E.Cnil (T.Pair T.Bool BS_k);
   Dc <- 0;
   Gc <- 0;
   GR'n <$- {0,1}^n; GR'k1 <$- {0,1}^k1;
   S' <- (GR'n | GR'k1);
   M <c- A with{};
   HS'def <- true;
   T' <$- {0,1}^k0;
   Y' <- ap_f (S' | T');
   Ydef <- true;
   b' <c- A' with {Y'}
  ]).
  transitivity (Pr E12 (C ++ [R' <$- {0,1}^k0]) (m {!bad1 <-- false!})
   (EP k
    (E.Eop O.Oand
     {E.Eop O.Oand {Elen LG <=! qG, Elen LD <=! qD},
      E.Eop O.Oor {R' in_dom LG, Bad} }))).
  apply Oeq_le; apply EqObs_Pr with {{Y',g_a}}.
  deadcode iE12; swap iE12.
  eqobs_tl iE12.
  union_mod.
  apply EqObs_trans with E12
   [R' <$- {0,1}^k0; T' <$- {0,1}^k0; HS' <- T' |x| R'].
  eqobs_hd.
  eapply equiv_weaken; 
   [ |eapply equiv_strengthen; [ | apply optimistic_sampling] ].
  intros k2 m1 m2 H; apply req_mem_weaken with (2:= H).
  vm_compute; trivial.
  simpl; intros k2 m1 m2 H; apply req_mem_weaken with (2:= H).
  vm_compute; trivial.
  discriminate.
  vm_compute; trivial.
  vm_compute; trivial.
  deadcode; swap; eqobs_in.
  unfold Pr; rewrite deno_app_elim.
  transitivity (mu ([[C]] E12 (m{!bad1 <-- false!})) 
   (fcte _ (qG_poly k /2^ k0 k + qD_poly k /2^ k0 k))%U); [ | apply mu_cte_le].
  apply mu_le_compat; [trivial | clear C m; intros m].
 
  unfold fcte.
  transitivity 
   ((mu ([[ [R' <$- {0,1}^k0] ]] E12 m))
    (fplus (charfun (EP k (E.Eop O.Oand {Elen LG <=! qG, R' in_dom LG} )))
     (charfun (EP k (E.Eop O.Oand {Elen LD <=! qD, Bad} ))))).
  apply mu_le_compat; trivial.
  unfold charfun, EP, fplus,restr,fone; intros m1; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  match goal with |- ((if ?b then _ else _) <= _)%tord => 
   case_eq b; intros Heq; [change (is_true b) in Heq | trivial] end.
  repeat rewrite is_true_andb in Heq; decompose [and] Heq; clear Heq.
  rewrite H1, H2; simpl.
  rewrite is_true_orb in H0; destruct H0 as [H0 | H0]; rewrite H0; auto.
  transitivity 
   ( (mu (([[ [R' <$- {0,1}^k0] ]]) E12 m)) (charfun (EP k (E.Eop O.Oand {Elen LG <=! qG, R' in_dom LG}))) +
    (mu (([[ [R' <$- {0,1}^k0] ]]) E12 m)) (charfun (EP k (E.Eop O.Oand {Elen LD <=! qD, Bad}))))%U.
  apply mu_le_plus.
  apply Uplus_le_compat.
  set (def := T.default k (T.Pair BS_k0 BS_nk1)).
  case_eq (@E.eval_expr k T.Bool ((Elen LG) <=! qG) m); intros Heq1.
  change (is_true (E.eval_expr (Elen LG <=! qG) m)) in Heq1.
  simpl in Heq1; unfold O.eval_op in Heq1; simpl in Heq1; rewrite is_true_leb in Heq1.
  transitivity 
   (mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))
    (sigma_fun 
     (fun i v =>
      charfun 
      (T.i_eqb k BS_k0 v) (fst (nth i (m LG) def)))
     (length (m LG)))).
  rewrite deno_random_elim.
  apply mu_monotonic; intro v; unfold sigma_fun.
  rewrite (sigma_finite_sum def
   (fun w : T.interp k (T.Pair BS_k0 BS_nk1) =>
    charfun (T.i_eqb k BS_k0 v) (fst w))).
  unfold charfun, restr, EP, fone; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  match goal with |- ((if ?x then _ else _) <= _)%tord =>
   case_eq x; intros Heq; [change (is_true x) in Heq | trivial] end.
  rewrite is_true_andb in Heq; destruct Heq.
  generalize (m LG) H0.
  induction i; simpl; intros; try discriminate.
  match goal with |- (_ <= ((if ?x then _ else _) + _)%U)%tord => 
   match type of H1 with is_true (orb ?y _) => 
    change y with x in H1;
     destruct x; auto end end.
  rewrite mu_sigma_le, Nmult_sigma.
  eapply Ole_trans; [| eapply sigma_incr; apply Heq1].
  apply sigma_le_compat.
  intros i Hi.
  set (li := fst (nth i (m LG) def)); simpl in li; fold li.
  apply (@Pr_bs_support (k0 k) (T.default k BS_k0) li
   (fun e v => if T.i_eqb k BS_k0 v e then 1 else @D0 _))%U.
  intros x; rewrite <- (is_true_Ti_eqb k BS_k0 x).
  destruct (T.i_eqb k BS_k0 x li); intros H; [ elim H | ]; trivial.
  rewrite Ti_eqb_refl; trivial.
  rewrite deno_random_elim.
  transitivity ((mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))) (fun _ => D0)).
  apply mu_le_compat; [trivial | intros v].
  generalize Heq1; unfold charfun, EP, restr; simpl; unfold O.eval_op; simpl; intros H.
  mem_upd_simpl.
  rewrite H; simpl; trivial.
  rewrite mu_0; trivial.

  case_eq (@E.eval_expr k T.Bool ((Elen LD) <=! qD) m); intros Heq1.
  change (is_true (E.eval_expr (Elen LD <=! qD) m)) in Heq1.
  simpl in Heq1; unfold O.eval_op in Heq1; simpl in Heq1; rewrite is_true_leb in Heq1.
  set (def := T.default k (T.Pair T.Bool BS_k)).
  transitivity 
   (mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))
    (sigma_fun 
     (fun i v =>
      charfun 
      (T.i_eqb k BS_k0 v) (E.eval_expr (let c := Esnd tc in 
       let s := Efst (ap_finv c) in
        let t := Esnd (ap_finv c) in
         let h := LH [{s}] in
          t |x| h) (m {!tc <-- (nth i (m LD) def) !})))
     (length (m LD)))).
  rewrite deno_random_elim.
  apply mu_monotonic; intro v; unfold sigma_fun.
  rewrite (sigma_finite_sum def
   (fun w =>
    charfun (T.i_eqb k BS_k0 v) (E.eval_expr (let c := Esnd tc in 
     let s := Efst (ap_finv c) in
      let t := Esnd (ap_finv c) in
       let h := LH [{s}] in
        t |x| h) (m {!tc <-- w !})))).
  unfold charfun, restr, EP, fone; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  match goal with |- ((if ?x then _ else _) <= _)%tord =>
   case_eq x; intros Heq; [change (is_true x) in Heq | trivial] end.
  rewrite is_true_andb in Heq; destruct Heq.
  generalize (m LD) H0.
  induction i; simpl; intros; try discriminate.
  mem_upd_simpl.
  repeat (rewrite Mem.get_upd_same in H1 || (rewrite Mem.get_upd_diff in H1; [ | discriminate])).
  match goal with |- (_ <= ((if ?x then _ else _) + _)%U)%tord =>      
   match type of H1 with is_true (orb (andb _ ?y)  _) => 
    change y with x in H1;
     destruct x; [ auto | ] end end.
  rewrite andb_false_r in H1; simpl in H1; auto.
  rewrite mu_sigma_le, Nmult_sigma.
  eapply Ole_trans; [| eapply sigma_incr; apply Heq1].
  apply sigma_le_compat.
  intros i Hi.
  set (li := (E.eval_expr (let c := Esnd tc in 
   let s := Efst (ap_finv c) in
    let t := Esnd (ap_finv c) in
     let h := LH [{s}] in
      t |x| h) (m {!tc <-- (nth i (m LD) def) !}))).
  apply (@Pr_bs_support (k0 k) (T.default k BS_k0) li
   (fun e v => if T.i_eqb k BS_k0 v e then 1 else @D0 _))%U.
  intros x; rewrite <- (is_true_Ti_eqb k BS_k0 x).
  destruct (T.i_eqb k BS_k0 x li); intros H; [ elim H | ]; trivial.
  rewrite Ti_eqb_refl; trivial.
  rewrite deno_random_elim.
  transitivity ((mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))) (fun _ => D0)).
  apply mu_le_compat; [trivial | intros v].
  generalize Heq1; unfold charfun, EP, restr; simpl; unfold O.eval_op; simpl; intros H.
  mem_upd_simpl.
  rewrite H; simpl; trivial.
  rewrite mu_0; trivial.
 Qed.

 (*****************************************************)
 (* We focus on the probability of bad3               *)
 (*****************************************************)

 Definition Bad3_1 :=
  E.Eexists tc
  (let c := Esnd (tc) in
   let s := Efst (ap_finv c) in
   let t := Esnd (ap_finv c) in
   let h := HS' in
   let r := t |x| h in
   r in_dom LG) LD.

 Definition Bad3_2 :=
  E.Eexists tc
  (let c := Esnd (tc) in
   let t := Esnd (ap_finv c) in
   (!(Efst tc)) && (HS' |x| R' =?= t)) LD.

 Definition inv_bad3 := 
  ((EP1 bad3 |-> EP2 Bad3_1 \-/ EP2 Bad3_2) /-\
   (EP2 Ydef |-> EP2 (Y' =?= ap_f (S' | (HS' |x| R'))))) /-\
  (EP2 ((Gc <=! qG) && (Dc <=! qD) && 
   ((Elen LG) <=! Gc) && ((Elen LD) <=! Dc))).
 
 Lemma dec_inv_bad3 : decMR inv_bad3.
 Proof.
  unfold inv_bad3; auto 100.
 Qed.
         
 Lemma dep_inv_bad3 : depend_only_rel inv_bad3  
  (Vset.union
   (Vset.union
    (Vset.union (fv_expr bad3) (Vset.union Vset.empty Vset.empty))
    (Vset.union Vset.empty Vset.empty)) Vset.empty)
  (Vset.union
   (Vset.union
    (Vset.union Vset.empty
     (Vset.union (fv_expr Bad3_1) (fv_expr Bad3_2)))
    (Vset.union (fv_expr Ydef) (fv_expr ( (Y' =?= ap_f (S' | (HS' |x| R')))))))
   (fv_expr
    (E.Eop O.Oand
     {E.Eop O.Oand
      {E.Eop O.Oand {Gc <=! qG, Dc <=! qD}, Elen LG <=! Gc},
      Elen LD <=! Dc}))).
 Proof.
  unfold inv_bad3; auto.
 Qed.

 Definition eE11rE12_3 : eq_inv_info inv_bad3 E11r E12.
  refine (@empty_inv_info inv_bad3 _ _ dep_inv_bad3 _ dec_inv_bad3 E11r E12).
  vm_compute; trivial.
 Defined.

 Hint Resolve dec_inv_bad3 dep_inv_bad3.

 Lemma Gadv_body2_Gadv_body0_3 :
  EqObsInv inv_bad3 
  {{R', Gc, Radv, LG}}
  E11r GAdv_body1
  E12  GAdv_body1
  {{LG, Gc, rGadv}}.
 Proof.
  unfold GAdv_body1.
  cp_test (qG <=! Gc).
  rewrite proj1_MR; eqobs_in eE11rE12_3.
  inline eE11rE12_3 G.
  ep; deadcode eE11rE12_3.
  cp_test (Radv in_dom LG).
  rewrite proj1_MR; eqobs_tl eE11rE12_3.
Opaque leb.
  unfold inv_bad3; eqobsrel_tail; 
   simpl; unfold O.eval_op; simpl; red; intros; trivial.
  unfold andR, EP2, notR, orR, impR in H; decompose [and] H; clear H.
  split; [split; intros; auto| ].
  assert (W:=H2 H); simpl in W; unfold O.eval_op in W; simpl in W.
  destruct W as [W | W]; [left | right]; unfold is_true; 
   rewrite <- W; apply existsb_morph; intros; mem_upd_simpl; trivial.
  generalize H4 H6; simpl; unfold O.eval_op; simpl.
  repeat rewrite is_true_andb; repeat rewrite is_true_leb; omega'.
  unfold inv_bad3; eqobsrel_tail; simpl; unfold O.eval_op; simpl; red; intros; trivial.
  unfold andR, impR, notR, EP2, EP1, orR in H; decompose [and] H; clear H; split; [split; intros; auto | ].
  assert (H12 := H4 H); simpl in H12; unfold O.eval_op in H12; simpl in H12.
  destruct H12 as [H12|H12]; [left | right];
   (rewrite is_true_existsb in H12 |- *; destruct H12 as (x, (Hin, H12)); exists x; split; trivial;
    repeat (rewrite Mem.get_upd_same in H12|| (rewrite Mem.get_upd_diff in H12; [ | discriminate])); trivial).
  rewrite is_true_orb; right; trivial.
  generalize H6 H9; unfold notR; simpl; unfold O.eval_op; simpl.
  repeat rewrite is_true_andb; repeat rewrite is_true_leb; intros; omega'.
 Qed.

 Lemma H_body1_r_H_body0_3 : 
  EqObsInv inv_bad3 
  {{S, LH}}
  E11r H_body1_r
  E12  H_body0 
  {{LH, rH}}.
 Proof.
  unfold H_body1_r, H_body0, H_body1_gen.
  deadcode eE11rE12_3.
  eqobs_in eE11rE12_3.
 Qed.

 Lemma Dec_body11_r_Dec_body12_3 :
  EqObsInv inv_bad3 (Vset.add HS'def (Vset.add S' (Vset.add HS' (Vset.add R' (Vset.add LD (Vset.remove bad ID))))))
   E11r Dec_body11_r
   E12 Dec_body12 
   (Vset.add LD (Vset.remove bad OD)).
 Proof.
  unfold Dec_body11_r, Dec_body12.
  cp_test (E.Eop O.Oor {testD, qG <! (Elen LG)}).
  rewrite proj1_MR; eqobs_in eE11rE12_3. 
  deadcode eE11rE12_3. 
  cp_test (Efst (ap_finv c) in_dom LH).
  eqobs_tl eE11rE12_3.
  unfold inv_bad3; eqobsrel_tail; unfold EP1,EP2; simpl; unfold O.eval_op; simpl;
    unfold andR, impR, notR, orR; intros k m1 m2 H; decompose [and] H; clear H.
  split; [split; intros; auto | ].
  assert (W:= H2 H); clear H2.
  destruct W as [W | W]; [left | right];
  (rewrite is_true_existsb in W ; destruct W as (x, (Hin, W));
   repeat (rewrite Mem.get_upd_same in W|| (rewrite Mem.get_upd_diff in W; [ | discriminate]));
  rewrite is_true_orb; right; rewrite is_true_existsb; exists x; split; auto).
  generalize H4 H7; repeat (rewrite is_true_andb || rewrite is_true_orb || rewrite is_true_leb); omega'.
  cp_test (E.Eop O.Oand {S' =?= Efst (ap_finv c), HS'def}).
  cp_test (Esnd (ap_finv c) |x| HS' in_dom LG).
   eqobs_tl eE11rE12_3.
   unfold inv_bad3; eqobsrel_tail; unfold EP1,EP2; simpl; unfold O.eval_op; simpl;
    unfold andR, impR, notR; intros k m1 m2 H; decompose [and] H; clear H; split; [split; intros; auto | ].
  left; rewrite is_true_orb; left; trivial.
  generalize H4 H7; repeat (rewrite is_true_andb || rewrite is_true_orb || rewrite is_true_leb); omega'.
 cp_test (R' =?= Esnd (ap_finv c) |x| HS').
   eqobs_tl eE11rE12_3.
   unfold inv_bad3; eqobsrel_tail; unfold EP1,EP2; simpl; unfold O.eval_op; simpl;
    unfold andR, impR, notR; intros k m1 m2 H; decompose [and] H; clear H; split; [split; intros; auto | ].
   right.
   destruct (m2 Ydef); simpl.
   elim H7; repeat rewrite is_true_orb; left; right; rewrite Ti_eqb_refl; simpl.
   rewrite is_true_andb in H11; destruct H11 as (H11, _); trivial.
   rewrite is_true_Ti_eqb in *.
   rewrite H5, H11, H14, BVxor_comm, BVxor_bij; trivial.
   case_eq (finv (k:=k) (m2 c)); intros; simpl. 
   match goal with |- (f (k:=k) ?x) = _ =>
    match type of H12 with _ = ?y => change x with y end end.
   rewrite <- H12, finv_spec; trivial.
   rewrite is_true_andb in H11; destruct H11 as (H11, _).
   rewrite is_true_Ti_eqb in *.
   rewrite H14, BVxor_comm, BVxor_bij, Ti_eqb_refl; trivial.
  generalize H4 H7; repeat (rewrite is_true_andb || rewrite is_true_orb || rewrite is_true_leb); omega'.
  eqobs_tl eE11rE12_3.
  unfold inv_bad3; eqobsrel_tail; unfold EP1,EP2; simpl; unfold O.eval_op; simpl;
    unfold andR, impR, notR, orR; intros k m1 m2 H; decompose [and] H; clear H.
  split; [split; intros; auto | ].
  assert (W:= H2 H); clear H2.
  destruct W as [W | W]; [left | right];
  (rewrite is_true_existsb in W ; destruct W as (x, (Hin, W));
   repeat (rewrite Mem.get_upd_same in W|| (rewrite Mem.get_upd_diff in W; [ | discriminate]));
  rewrite is_true_orb; right; rewrite is_true_existsb; exists x; split; auto).
  generalize H4 H7; repeat (rewrite is_true_andb || rewrite is_true_orb || rewrite is_true_leb); omega'.
  eqobs_tl eE11rE12_3.
  unfold inv_bad3; eqobsrel_tail; unfold EP1,EP2; simpl; unfold O.eval_op; simpl;
    unfold andR, impR, notR, orR; intros k m1 m2 H; decompose [and] H; clear H.
  split; [split; intros; auto | ].
  assert (W:= H2 H); clear H2.
  destruct W as [W | W]; [left | right];
  (rewrite is_true_existsb in W ; destruct W as (x, (Hin, W));
   repeat (rewrite Mem.get_upd_same in W|| (rewrite Mem.get_upd_diff in W; [ | discriminate]));
  rewrite is_true_orb; right; rewrite is_true_existsb; exists x; split; auto).
  generalize H4 H7; repeat (rewrite is_true_andb || rewrite is_true_orb || rewrite is_true_leb); omega'.
 Qed.

 Definition iE11rE12_3 :=
  let RM := Vset.empty in
  let piH := my_add_info H RM RM iE11r iE12 eE11rE12_3 H_body1_r_H_body0_3 in 
  let piGA := my_add_info GAdv RM RM iE11r iE12 piH Gadv_body2_Gadv_body0_3 in
  let piD := my_add_info Dec RM RM iE11r iE12 piGA Dec_body11_r_Dec_body12_3 in
  adv_info piD.

Section INV_BAD3_b.

 Variable b : bool.
 Variable n : nat.

 Definition inv_bad3_b := 
  (EP2 Ydef /-\ EP2 (Bad3_2 =?= b)) /-\ EP2 (n <=! Elen LD).

 Lemma dec_inv_bad3_b : decMR inv_bad3_b.
 Proof.
  unfold inv_bad3_b; auto 100.
 Qed.

 Lemma dep_inv_bad3_b : depend_only_rel inv_bad3_b
  (Vset.union (Vset.union Vset.empty Vset.empty) Vset.empty)
  (Vset.union (Vset.union (fv_expr Ydef) (fv_expr (Bad3_2 =?= b))) 
   (fv_expr (n <=! Elen LD))).
 Proof.
  unfold inv_bad3_b; auto.
 Qed.
  
 Hint Resolve dec_inv_bad3_b dep_inv_bad3_b.

 Definition eE12_3_b : eq_inv_info inv_bad3_b E12 E12.
  refine (@empty_inv_info inv_bad3_b _ _ dep_inv_bad3_b _ dec_inv_bad3_b E12 E12).
  vm_compute; trivial.
 Defined.

 Lemma Dec_body12_3b :
  EqObsInv inv_bad3_b (Vset.add HS'def (Vset.add S' (Vset.add HS' (Vset.add R' (Vset.add LD (Vset.remove bad ID))))))
  E12 Dec_body12
  E12 Dec_body12 
  (Vset.add LD (Vset.remove bad OD)).
 Proof.
 unfold Dec_body12.
  cp_test (E.Eop O.Oor {testD, qG <! (Elen LG)}).
  rewrite proj1_MR; eqobs_in eE12_3_b. 
  deadcode eE12_3_b. 
  cp_test (Efst (ap_finv c) in_dom LH).
   eqobs_tl eE12_3_b.
   unfold inv_bad3_b; eqobsrel_tail; unfold EP1,EP2; simpl; unfold O.eval_op; simpl;
     unfold andR, impR, notR, orR; intros k m1 m2 H; decompose [and] H; clear H; intros.
   split; [split | ]; trivial.
   rewrite H2; simpl.
   rewrite is_true_Ti_eqb in *; rewrite <- H5; apply existsb_morph; intros.
   repeat (rewrite Mem.get_upd_same|| (rewrite Mem.get_upd_diff; [ | discriminate])); trivial.
   rewrite is_true_leb in H4 |- *; omega'.
  eqobs_tl eE12_3_b.
   unfold inv_bad3_b; eqobsrel_tail; unfold EP1,EP2; simpl; unfold O.eval_op; simpl;
     unfold andR, impR, notR, orR; intros k m1 m2 H; decompose [and] H; clear H; intros.
   split; [split | ]; trivial.
   rewrite H2; simpl.
   rewrite is_true_Ti_eqb in *; rewrite <- H5; apply existsb_morph; intros.
   repeat (rewrite Mem.get_upd_same|| (rewrite Mem.get_upd_diff; [ | discriminate])); trivial.
   rewrite is_true_leb in H4 |- *; omega'.
 Qed.

 Definition iE12_3b :=
  let RM := {{bad,bad1,bad2,bad3}} in
  let piH := add_refl_info H eE12_3_b in 
  let piG := add_refl_info G piH in 
  let piGA := add_refl_info GAdv piG in
  let piD := add_info Dec RM RM piGA Dec_body12_3b in
   adv_info piD.

End INV_BAD3_b.

Lemma Pr_E11r_bad3 : forall k m, 
 ((Pr E11r G3 (m{! bad1 <-- false !}) (EP k bad3) <=
  ((qD_poly k) */ (qG_poly k /2^k0 k)) + (qD_poly k /2^k0 k))%U)%tord.
Proof.
 intros k m.
 transitivity 
   (Pr E12 G3 (m{! bad1 <-- false !}) (EP k (((Elen LG) <=! qG) && ((Elen LD) <=! qD) && (Bad3_1 || Bad3_2)))).
 unfold Pr; apply equiv_deno_le with (kreq_mem {{Y',g_a}}) (req_mem_rel Vset.empty inv_bad3).
 eqobs_tl iE11rE12_3.
 match goal with
  |- equiv _ _ [?i1;?i2;?i3;?i4;?i5;?i6;?i7;?i8;?i9;?i10;?i11;?i12;?i13;?i14;?i15;?i16;?i17;?i18;?i19;?i20] _ _ _ => 
    apply equiv_trans_eq_mem_l with trueR E11r
      [i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15; i16; i17; i18;Y' <- ap_f (S' | HS' |x| R'); i20];
    [ 
    | apply equiv_trans_eq_mem_r with trueR E12
       [i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15; i16; i17; i18;Y' <- ap_f (S' | HS' |x| R'); i20]
    |
    ] end.
 rewrite proj1_MR. union_mod iE11r; trivial.
 ep iE11r; eqobs_in iE11r.
 rewrite proj1_MR. union_mod iE12; trivial.
 ep iE12; eqobs_in iE12.
 2: red; red; trivial. 2: red; red; trivial.
 match goal with
  |- equiv _ _ [?i1;?i2;?i3;?i4;?i5;?i6;?i7;?i8;?i9;?i10;?i11;?i12;?i13;?i14;?i15;?i16;?i17;?i18;?i19;?i20] _ _ (req_mem_rel ?X _) => 
     change [i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15; i16; i17; i18; i19; i20] with
       ([i1; i2; i3; i4; i5; i6; i7; i8; i9; i10; i11; i12; i13; i14; i15; i16; i17]++[i18; i19; i20]);
      apply equiv_app with (req_mem_rel 
        (Vset.add GR'n (Vset.add GR'k1 (Vset.add Ydef (Vset.add Y' (Vset.add HS'def X))))) inv_bad3) end.
 eqobs_tl iE11rE12_3.
 unfold inv_bad3; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl; red; intros.
 Transparent leb.
 simpl; intuition. discriminate.
 unfold inv_bad3; eqobsrel_tail; unfold req_mem_rel, EP1, EP2, andR, orR, impR; simpl; unfold O.eval_op; simpl;
  intros k2 m1 m2 H; decompose [and] H; clear H.
 split; [split; intros | ]; auto.
 destruct (H1 H) as [W|W]; clear H1; [left | right]; unfold is_true; rewrite <- W; apply existsb_morph; intros;
     mem_upd_simpl; trivial.
 apply Ti_eqb_refl.
 unfold inv_bad3, impR, andR; intros m1 m2 (_, H); decompose [and] H.
 unfold charfun, EP, restr, fone.
 case_eq (E.eval_expr bad3 m1); intros Heq; trivial.
 generalize (H2 Heq) H1; clear H2 H1; unfold EP2, orR; simpl; unfold O.eval_op; simpl; intros.
 match goal with |- (_ <= (if ?x then _ else _))%tord => replace x with true; [trivial | symmetry; change (is_true x)] end.
 rewrite <- is_true_orb in H0; rewrite H0, andb_true_r.
 generalize H1; clear; repeat (rewrite is_true_andb || rewrite is_true_leb); omega'.
 trivial.
 unfold Pr.
 transitivity
   (((mu (([[G3]]) E12 (m {!bad1 <-- false!})))
     (charfun
      (EP k (((Elen LG <=! qG) && (Elen LD <=! qD)) && Bad3_1)))) + 
   ((mu (([[G3]]) E12 (m {!bad1 <-- false!})))
     (charfun (EP k ((Elen LD <=! qD) && Bad3_2)))))%U.
  rewrite <- mu_le_plus; apply mu_monotonic.
  intros m1.
   unfold charfun, EP, fplus,restr,fone; simpl; unfold O.eval_op; simpl.
   match goal with |- ((if ?b then _ else _) <= _)%tord => 
    case_eq b; intros Heq; [change (is_true b) in Heq | trivial] end.
   repeat rewrite is_true_andb in Heq; decompose [and] Heq; clear Heq.
   rewrite H1, H2; simpl.
   rewrite is_true_orb in H0; destruct H0 as [H0 | H0]; rewrite H0; auto.
  apply Uplus_le_compat.
 
 (* HS' in LG *)
 set (C:=[
       Ydef <- false;
       LG <- E.Cnil (T.Pair BS_k0 BS_nk1);
       LH <- E.Cnil BS_k;
       LD <- E.Cnil (T.Pair T.Bool BS_k);
       Dc <- 0;
       Gc <- 0;
       GR'n <$- {0,1}^n; 
       GR'k1 <$- {0,1}^k1;
       S' <- (GR'n | GR'k1);       
       M <c- A with{};
       HS'def <- true;
       T' <$- {0,1}^k0;
       Y' <- ap_f (S' | T');
       Ydef <- true;
       b' <c- A' with {Y'}
       ]).
  transitivity (Pr E12 (C ++ [HS' <$- {0,1}^k0]) (m {!bad1 <-- false!})
    (EP k (((Elen LG <=! qG) && (Elen LD <=! qD)) && Bad3_1))).
  apply Oeq_le; apply EqObs_Pr with {{Y',g_a}}.
  deadcode iE12; swap iE12.
  eqobs_tl iE12.
  union_mod.
  apply EqObs_trans with E12
  [HS' <$- {0,1}^k0; R' <$- {0,1}^k0; T' <- HS' |x| R'].
  swap; eqobs_in.
  apply EqObs_trans with E12
  [HS' <$- {0,1}^k0; T' <$- {0,1}^k0; R' <- HS' |x| T'].
  2:deadcode; swap; eqobs_in.
  eqobs_hd.
  eapply equiv_weaken; 
   [ |eapply equiv_strengthen; [ | apply optimistic_sampling_inv] ].
   intros k2 m1 m2 H; apply req_mem_weaken with (2:= H). 
   vm_compute; trivial.
   simpl; intros k2 m1 m2 H; apply req_mem_weaken with (2:= H).
   vm_compute; trivial.
   discriminate.
   vm_compute; trivial.
   vm_compute; trivial.

   unfold Pr; rewrite deno_app_elim.
  transitivity ((mu (([[C]]) E12 (m {!bad1 <-- false!}))) 
        (fcte _ (qD_poly k */ qG_poly k /2^ k0 k))).
  2:apply mu_cte_le.
  apply mu_le_compat; [trivial | clear C m; intros m].
 
  set (def := T.default k (T.Pair BS_k0 BS_nk1)).
   set (def1 := T.default k (T.Pair T.Bool BS_k)).
   case_eq (@E.eval_expr k T.Bool (E.Eop O.Oand {Elen LG <=! qG, Elen LD <=! qD}) m); intros Heq1.
   change (is_true (E.eval_expr ((Elen LG <=! qG) &&  (Elen LD <=! qD)) m)) in Heq1.
   simpl in Heq1; unfold O.eval_op in Heq1; simpl in Heq1; rewrite is_true_andb, is_true_leb, is_true_leb in Heq1.
   destruct Heq1 as (Heq1, Heq2).
   set (e:= (let c := Esnd (tc) in
             let s := Efst (ap_finv c) in
             let t := Esnd (ap_finv c) in
             let h := HS' in let r := t |x| h in r in_dom LG)).
  transitivity 
    (mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))
     (sigma_fun 
      (fun i v => charfun (fun v1 => E.eval_expr e (m{!HS' <-- v!}{!tc<--v1!})) (nth i (m LD) def1))
           (length (m LD)))).
   rewrite deno_random_elim.
   apply mu_monotonic; intro v; unfold sigma_fun.
   rewrite (sigma_finite_sum def1
    (fun w => charfun (fun v1 => E.eval_expr e (m{!HS' <-- v!}{!tc<--v1!})) w)).
   unfold charfun, restr, EP, fone; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   match goal with |- ((if ?x then _ else _) <= _)%tord =>
     case_eq x; intros Heq; [change (is_true x) in Heq | trivial] end.
   repeat rewrite is_true_andb in Heq; decompose [and] Heq; clear Heq.
   generalize (m LD) H0.
    induction i; simpl; intros; try discriminate.
    mem_upd_simpl.
    repeat (rewrite Mem.get_upd_same in H3 || (rewrite Mem.get_upd_diff in H3; [ | discriminate])).
  match goal with |- (_ <= ((if ?x then _ else _) + _)%U)%tord => 
     match type of H3 with is_true (orb ?y _) => 
       change y with x in H3;
      destruct x; auto end end.
   rewrite mu_sigma_le.
   unfold fcte; rewrite Nmult_sigma.
   eapply Ole_trans; [| eapply sigma_incr; apply Heq2].
   apply sigma_le_compat.
   intros i Hi.
   set (li := (nth i (m LD) def1)); simpl in li; fold li.
   set (e1 :=  let c := Esnd (tc) in
     let s := Efst (ap_finv c) in
     let t := Esnd (ap_finv c) in
     let h := HS' in t |x| h).
   transitivity 
    (mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))
     (sigma_fun 
      (fun i v =>
       charfun 
       (T.i_eqb k BS_k0 (E.eval_expr e1 ((m {!HS' <-- v!}) {!tc <-- li!}))) (fst (nth i (m LG) def)))
      (length (m LG)))).
   apply mu_monotonic; intro v; unfold sigma_fun.
   rewrite (sigma_finite_sum def
    (fun w : T.interp k (T.Pair BS_k0 BS_nk1) =>
     charfun 
       (T.i_eqb k BS_k0 (E.eval_expr e1 ((m {!HS' <-- v!}) {!tc <-- li!}))) (fst w))).
   unfold charfun, restr, EP, fone; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   match goal with |- ((if ?x then _ else _) <= _)%tord =>
     case_eq x; intros Heq; [change (is_true x) in Heq | trivial] end.
   generalize (m LG) Heq.
    induction i0; simpl; intros; try discriminate.
    match goal with |- (_ <= ((if ?x then _ else _) + _)%U)%tord => 
     match type of Heq0 with is_true (orb ?y _) => 
       change y with x in Heq0;
      destruct x; auto end end.
   rewrite mu_sigma_le, Nmult_sigma.
   eapply Ole_trans; [| eapply sigma_incr; apply Heq1].
   apply sigma_le_compat.
   intros i0 Hi0.
   set (li0 := fst (nth i0 (m LG) def)); simpl in li0; fold li0.
   apply (@Pr_bs_support (k0 k) (T.default k BS_k0) (BVxor (k0 k) (snd (finv (k:=k) (snd li))) li0)
    (fun e v => if T.i_eqb k BS_k0 (E.eval_expr e1 ((m {!HS' <-- v!}) {!tc <-- li!})) li0 then 1 else @D0 _))%U.
    simpl; unfold O.eval_op; simpl; intros.
    mem_upd_simpl.
   match goal with |- ((if ?x then _ else _) == _) =>
     case_eq x; intros Heq; [change (is_true x) in Heq | trivial] end.
   rewrite is_true_Ti_eqb in Heq; elim H; rewrite <- Heq.
   match goal with |- _ = BVxor _ ?x _ => 
   rewrite  BVxor_comm, (BVxor_comm x), BVxor_bij; trivial end.
   simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   match goal with |- (if T.i_eqb _ _ (BVxor _ ?x _) _ then _ else _) == _  => 
   rewrite  BVxor_comm, (BVxor_comm x), BVxor_bij, Ti_eqb_refl; trivial end.
   rewrite deno_random_elim.
   transitivity ((mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))) (fun _ => D0)).
   apply mu_le_compat; [trivial | intros v].
   generalize Heq1; unfold charfun, EP, restr; simpl; unfold O.eval_op; simpl; intros H.
   mem_upd_simpl.
   rewrite H; simpl; trivial.
   rewrite mu_0; trivial.
  
  (* T' is in LD *)
  set (C1 := [
       HS'def <- false;
       Ydef <- false;
       LG <- E.Cnil (T.Pair BS_k0 BS_nk1);
       LH <- E.Cnil BS_k;
       LD <- E.Cnil (T.Pair T.Bool BS_k);
       Dc <- 0;
       Gc <- 0;
       R' <$- {0,1}^k0;
       GR'n <$- {0,1}^n;
       GR'k1 <$- {0,1}^k1;
       S' <- (GR'n | GR'k1);
       M <c- A with{}]
      ).
   set (C2 := [
       T' <- HS' |x| R';
       HS'def <- true;
       Y' <- ap_f (S' | T');
       Ydef <- true;
       b' <c- A' with {Y'}
       ]).
   transitivity 
    (mu ([[ C1 ++ ([HS' <$- {0,1}^k0] ++ C2) ]] E12 (m {!bad1 <-- false!}))
        (charfun (EP k (E.Eop O.Oand {Elen LD <=! qD, Bad3_2})))).
   apply Oeq_le; apply EqObs_Pr with {{Y',g_a}}.
   ep iE12; deadcode iE12; swap iE12; eqobs_in iE12.
   rewrite deno_app_elim.
   transitivity ((mu (([[C1]]) E12 (m {!bad1 <-- false!}))) 
        (fcte _ (qD_poly k /2^ k0 k))).
   2:apply mu_cte_le.
   apply mu_le_compat; [trivial | clear C1 m; intros m].
   rewrite deno_app_elim.
   transitivity 
    ((mu (([[ [HS' <$- {0,1}^k0] ]]) E12 m)) 
      (charfun (EP k (E.Eop O.Oand {Elen LD <=! qD, Bad3_2})))).
   apply mu_monotonic; clear m; intros m.
   transitivity (mu (([[C2]]) E12 m)
      (fcte _ (charfun (EP k (E.Eop O.Oand {Elen LD <=! qD, Bad3_2})) m))).
   2 : apply mu_cte_le.
   assert (forall (b:bool) (N:nat),
      equiv (Meq /-\ EP2 (Bad3_2 =?= b) /-\ EP2 (N <=! Elen LD)) E12 C2 E12
         C2 (req_mem_rel (fv_expr Bad3_2) (inv_bad3_b b N))).
   intros b N; eqobs_tl (iE12_3b b N).
   unfold inv_bad3_b; eqobsrel_tail; unfold EP1, EP2, andR; simpl; unfold O.eval_op; simpl; intros k2 m1 m2 H; intros.
   decompose [and] H; clear H.
   split; [split | ]; trivial.
   rewrite is_true_Ti_eqb in *; rewrite <- H2; apply existsb_morph; intros.
     mem_upd_simpl; trivial.
   apply equiv_deno_le with (1:= H (E.eval_expr Bad3_2 m) (E.eval_expr (Elen LD) m)).
   unfold req_mem_rel, inv_bad3_b, andR, impR; intros.
   decompose [and] H0; clear H0 H C2.
   generalize H4 H5; clear H4 H5 H2.
   unfold EP2, charfun, restr, fcte, fone, EP; simpl; unfold O.eval_op; simpl; intros.
   match goal with |- ((if ?x then _ else _) <= (if ?y then _ else _))%tord =>
     case_eq x; intros Heq;
     [change (is_true x) in Heq; replace y with true; [trivial | symmetry; change (is_true y)]
     | trivial] end.
   rewrite is_true_andb in Heq; destruct Heq.
   match goal with |- is_true (andb ?x _) => replace x with true; [ | symmetry; change (is_true x)] end.
   simpl; unfold is_true; rewrite <- H0.
   rewrite is_true_Ti_eqb in H5; apply sym_eq in H5.
   eapply trans_eq; [ | eapply trans_eq; [ apply H5 | ] ].
   apply existsb_morph; intros; mem_upd_simpl; trivial.
   rewrite (H1 _ LD); trivial.
   apply existsb_morph; intros; mem_upd_simpl; trivial.
   rewrite (H1 _ HS'), (H1 _ R'); trivial.
   rewrite is_true_leb in H, H4 |- *; rewrite (H1 _ LD) in H; trivial; omega'.
   unfold andR, EP2; simpl; unfold O.eval_op; simpl; repeat split; trivial.
   apply Ti_eqb_refl.
   rewrite is_true_leb; omega'.

   case_eq (@E.eval_expr k T.Bool ((Elen LD) <=! qD) m); intros Heq1.
   change (is_true (E.eval_expr (Elen LD <=! qD) m)) in Heq1.
   simpl in Heq1; unfold O.eval_op in Heq1; simpl in Heq1; rewrite is_true_leb in Heq1.
   set (def := T.default k (T.Pair T.Bool BS_k)).
   set (e:=  let c := Esnd (tc) in
             let t := Esnd (ap_finv c) in
             HS' |x| R' =?= t).
   transitivity 
    (mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))
     (sigma_fun 
      (fun i v =>
       charfun (fun v1 => E.eval_expr e (m{!HS'<--v!}{!tc<-- v1!})) (nth i (m LD) def))
      (length (m LD)))).
   rewrite deno_random_elim.
   apply mu_monotonic; intro v; unfold sigma_fun.
   rewrite (sigma_finite_sum def
    (fun w => charfun (fun v1 => E.eval_expr e (m{!HS'<--v!}{!tc<-- v1!})) w)).
   unfold charfun, restr, EP, fone; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   match goal with |- ((if ?x then _ else _) <= _)%tord =>
     case_eq x; intros Heq; [change (is_true x) in Heq | trivial] end.
   rewrite is_true_andb in Heq; destruct Heq.
   generalize (m LD) H0.
    induction i; simpl; intros; try discriminate.
    mem_upd_simpl.
    repeat (rewrite Mem.get_upd_same in H1 || (rewrite Mem.get_upd_diff in H1; [ | discriminate])).
    match type of H1 with (is_true (orb (andb ?x _) _)) => destruct x; simpl in H1 end.
    match goal with |- (_ <= ((if ?x then _ else _) + _)%U)%tord =>      
     match type of H1 with is_true (orb ?y _) => 
       change y with x in H1;
      destruct x; auto end end.
   match goal with |- (_ <= (?x + _)%U)%tord => transitivity (x + 1)%U end.
   auto.
   apply Uplus_le_compat; auto.
   rewrite mu_sigma_le; unfold fcte; rewrite Nmult_sigma.
   eapply Ole_trans; [| eapply sigma_incr; apply Heq1].
   apply sigma_le_compat.
   intros i Hi.
   set (e2 := (let c := Esnd (tc) in let t := Esnd (ap_finv c) in t |x| R')).
   transitivity
     ((mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m)))
       (fun v => if T.i_eqb k BS_k0 (E.eval_expr e2 (m{!tc<-- nth i (m LD) def!})) v then 1%U else D0)).
   apply mu_monotonic; intros v.
   unfold charfun, restr, fone; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   match goal with |- ((if ?x then _ else _) <= (if ?y then _ else _))%tord =>
     case_eq x; intros Heq;
     [change (is_true x) in Heq; replace y with true; [trivial | symmetry; change (is_true y)]
     | trivial] end.
  rewrite is_true_Ti_eqb in *.
  rewrite <- Heq, BVxor_bij; trivial.
  set (li:=E.eval_expr e2 (m {!tc <-- nth i (m LD) def!})).
  apply (@Pr_bs_support (k0 k) (T.default k BS_k0) li
   (fun e1 v =>  if T.i_eqb k BS_k0 e1 v then 1%U else D0)).
    intros x Heq.
    apply sym_not_eq in Heq.
    rewrite <- (is_true_Ti_eqb k BS_k0 li x) in Heq.
    apply not_true_is_false in Heq; rewrite Heq; trivial.
   rewrite Ti_eqb_refl; trivial.
   rewrite deno_random_elim.
   transitivity ((mu (sum_support (T.default k BS_k0) (E.eval_support {0,1}^k0 m))) (fun _ => D0)).
   apply mu_le_compat; [trivial | intros v].
   generalize Heq1; unfold charfun, EP, restr; simpl; unfold O.eval_op; simpl; intros H.
   mem_upd_simpl.
   rewrite H; simpl; trivial.
   rewrite mu_0; trivial.
 Qed.

 (** We focus on bad2, this is the inverter unfolded *)

 Definition G4 := 
  [
   Ydef <- false;
   LG <- Nil _;
   LH <- Nil _;
   LD <- Nil _;
   Dc <- 0;
   Gc <- 0;
   GR'n <$- {0,1}^n;
   GR'k1 <$- {0,1}^k1;
   T' <$- {0,1}^k0;
   M <c- A with{};
   Y' <- ap_f ((GR'n | GR'k1) | T');
   Ydef <- true;
   b' <c- A' with {Y'}
  ].

 Definition inv_bad2 :=
  EP1 (S' =?= (GR'n | GR'k1)) /-\
  (EP1 bad2 |-> EP2 (E.Eexists sh (Efst sh =?= (GR'n | GR'k1)) LH)).

 Lemma dec_bad2 : decMR inv_bad2.
 Proof. 
  unfold inv_bad2; auto. 
 Qed.

 Lemma dep_bad2 : depend_only_rel inv_bad2 
  (Vset.union (fv_expr (S' =?= (GR'n | GR'k1)))
   (Vset.union (fv_expr bad2) Vset.empty))
  (Vset.union Vset.empty
   (Vset.union Vset.empty
    (fv_expr (E.Eexists sh (Efst sh =?= (GR'n | GR'k1)) LH)))).
 Proof. 
  unfold inv_bad2; auto. 
 Qed.
  
 Definition eE11rE12_bad2 : eq_inv_info inv_bad2 E11r E12.
  refine (@empty_inv_info inv_bad2 _ _ dep_bad2 _ dec_bad2 E11r E12).
  vm_compute; trivial.
 Defined.

 Lemma H_body1_r_inv_bad2 : EqObsInv inv_bad2 
  {{S',GR'n,GR'k1,S,LH}}
  E11r H_body1_r
  E12 H_body0 
  {{LH,rH}}.
 Proof.
  unfold H_body1_r, H_body0, H_body1_gen.
  cp_test (S in_dom LH).
  rewrite proj1_MR ; eqobs_in eE11rE12_bad2.
  cp_test (S' =?= S).
  ep_eq S (GR'n | GR'k1).
  unfold req_mem_rel, inv_bad2, andR, impR, EP1, EP2, notR.
  simpl; unfold O.eval_op; simpl; intros k m1 m2 H; decompose [and] H; clear H.
  rewrite is_true_Ti_eqb in H2, H3, H7; rewrite <- H3, <- H7.
  rewrite <- (H0 _ S'), <- (H0 _ GR'n), <- (H0 _ GR'k1); auto.
  unfold inv_bad2; eqobsrel_tail; unfold EP1, EP2, impR,andR, notR; 
   simpl; unfold O.eval_op; simpl;
   intros k m1 m2 H; decompose [and] H; clear H; intros.
  rewrite Ti_eqb_refl; simpl; auto.
  unfold inv_bad2; eqobsrel_tail; unfold EP1, EP2, impR,andR, notR; 
   simpl; unfold O.eval_op; simpl;
   intros k m1 m2 H; decompose [and] H; clear H; intros.
  split; [trivial | intros Hb; apply H4 in Hb].
  rewrite is_true_orb; right.
  rewrite is_true_existsb in Hb |- *.
  destruct Hb as (x, (Hin, Hb)); exists x; split; trivial.
  repeat (rewrite Mem.get_upd_same in Hb || 
         (rewrite Mem.get_upd_diff in Hb; [ | discriminate])); trivial.
 Qed.

 Lemma G_body2_inv_bad2 : EqObsInv 
  inv_bad2 {{R,LG}}
  E11r G_body2 
  E12 G_body0 
  {{rGn, rGk1, LG}}.
 Proof.
  deadcode eE11rE12_bad2; eqobs_in eE11rE12_bad2.
 Qed.

 Lemma Dec_body11r_inv_bad2 :
  EqObsInv inv_bad2 (Vset.remove R' (Vset.remove bad ID)) 
  E11r Dec_body11_r 
  E12 Dec_body12 
  (Vset.remove bad OD).
 Proof.
  deadcode eE11rE12_bad2; eqobs_in eE11rE12_bad2.
 Qed.

 Definition iE11rE12_bad2 :=
  let RM := {{bad3,bad,bad1,bad2}} in
  let piH := add_info H RM RM eE11rE12_bad2 H_body1_r_inv_bad2 in 
  let piG := add_info G RM RM piH G_body2_inv_bad2 in
  let piGA := add_refl_info_rm GAdv RM RM piG in
  let piD := add_info Dec RM RM piGA Dec_body11r_inv_bad2 in
   adv_info piD.

 Lemma Pr_11r_bad2 : forall k m,
  (Pr E11r G3 (m{!bad1 <-- false!}) (EP k bad2) <=
   Pr E12 G4 m (EP k (E.Eexists sh (Efst sh =?= (GR'n | GR'k1)) LH)))%tord.
 Proof.
  intros k m.
  set (C:= 
      [bad2 <- false; bad3 <- false; HS'def <- false; bad <- false] ++
     [
     Ydef <- false;
     LG <- Nil _;
     LH <- Nil _;
     LD <- Nil _;
     Dc <- 0;
     Gc <- 0;
     R' <$- {0,1}^k0
     ] ++
     [GR'n <$- {0,1}^n; GR'k1 <$- {0,1}^k1] ++
     [S' <- (GR'n | GR'k1)] ++
     [T' <$- {0,1}^k0;
     HS' <- T' |x| R'] ++
     [
     M <c- A with{};
     HS'def <- true;
     Y' <- ap_f (S' | T');
     Ydef <- true;
     b' <c- A' with {Y'}
     ]).
  transitivity  (Pr E11r C (m {!bad1 <-- false!}) (EP k bad2)).
  apply Oeq_le; apply EqObs_Pr with {{bad1,Y',g_a}}.
  swap iE11r; eqobs_ctxt iE11r.
  union_mod.
  eapply equiv_weaken; 
   [ |eapply equiv_strengthen; [ | apply optimistic_sampling] ].
    intros k2 m1 m2 H; apply req_mem_weaken with (2:= H).
    vm_compute; trivial.
    simpl; intros k2 m1 m2 H; apply req_mem_weaken with (2:= H). 
    vm_compute; trivial.
    discriminate.   
    vm_compute; trivial.
    vm_compute; trivial.

  transitivity (Pr E12 C (m {!bad1 <-- false!}) (EP k (E.Eexists sh (Efst (sh) =?= (GR'n | GR'k1)) LH))).
  apply equiv_deno_le with 
   (kreq_mem {{bad1,Y',g_a}})
   (req_mem_rel Vset.empty inv_bad2).
   eqobs_tl iE11rE12_bad2.
   unfold inv_bad2; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl; red; intros.
   rewrite Ti_eqb_refl; auto.
  intros m1 m2 (_, (H1, H2)).
  unfold EP1, EP2, EP, charfun, impR, restr, fone in *.
  destruct (E.eval_expr bad2 m1); [rewrite H2 | ]; trivial.
  trivial.
  apply Oeq_le; rewrite set_bad; apply EqObs_Pr with {{Y',g_a}}.
  ep iE12; deadcode iE12; eqobs_in iE12.
 Qed.

 Definition test_Dec :=
  let s := Efst sh in
  let h := Esnd sh in
  let r := Efst rg in
  let g := Esnd rg in
  let t := r |x| h in
  let m := s |x2| g in (c =?= ap_f (s | t)) && (Esnd m =?= zero_k1).

 Definition Dec_body13 :=
  [
   If E.Eop O.Oor {testD, qG <! (Elen LG)} then [mn <- (false | one_n)]
   else [
    LD <- (Ydef | c) |::| LD;
    Dc <- 1 +! Dc;
    If E.Eexists sh (E.Eexists rg test_Dec LG) LH then 
     [
      sh <- E.Efind sh (E.Eexists rg test_Dec LG) LH;
      rg <- E.Efind rg test_Dec LG;
      mn <- (true | Efst ( (Efst sh) |x2| (Esnd rg)))
     ] else [ mn <- (false | one_n) ]
   ]
  ].

 Definition E13 := mkEnv H_body0 G_body0 Dec_body13.

 Definition wf_LH := E.Eforall sh (Esnd sh =?= LH[{Efst sh}]) LH.
 
 Definition wf_LG := E.Eforall rg (Esnd rg =?= LG[{Efst rg}]) LG.

 Definition inv13 := EP2 (wf_LH && wf_LG).

 Lemma dec_inv13 : decMR inv13.
 Proof. 
  unfold inv13; auto. 
 Qed.

 Lemma dep_inv13 : depend_only_rel inv13 Vset.empty (fv_expr (wf_LH && wf_LG)).
 Proof. 
  unfold inv13; auto. 
 Qed.

 Definition eE12E13 : eq_inv_info inv13 E12 E13.
  refine (@empty_inv_info inv13 _ _ dep_inv13 _ dec_inv13 E12 E13).
  vm_compute; trivial.
 Defined.

 Lemma H_body0_inv13 : 
  EqObsInv inv13 {{S, LH}}
  E12 H_body0
  E13 H_body0
  {{LH,rH}}.
 Proof.
  unfold H_body0.
  cp_test (S in_dom LH).
  rewrite proj1_MR; eqobs_in eE12E13.
  unfold inv13; eqobsrel_tail; unfold EP1, EP2, notR,req_mem_rel, andR; simpl; unfold O.eval_op; simpl;
    intros k m1 m2 H; decompose [and] H; clear H; intros.
  unfold O.assoc at 1; simpl.
  rewrite Ti_eqb_refl; simpl; rewrite Ti_eqb_refl.
  simpl.
  rewrite is_true_andb, is_true_forallb, is_true_forallb in H2 |- *; destruct H2; split; intros.
  unfold O.assoc; simpl.
  match goal with |- is_true (T.i_eqb _ _ _ (match (if ?x then _ else _) with Some _ => _ | None => _ end)) =>
   case_eq x; intros Heq; [ change (is_true x) in Heq | ] end.
  elim H4; rewrite is_true_existsb; exists x; split; trivial.
  rewrite is_true_Ti_eqb in Heq; rewrite <- Heq; apply Ti_eqb_refl.
  assert (W := H2 _ H5);
   repeat (rewrite Mem.get_upd_same in W|| (rewrite Mem.get_upd_diff in W; [ | discriminate])); trivial.
  assert (W:= H3 _ H5);
   repeat (rewrite Mem.get_upd_same in W|| (rewrite Mem.get_upd_diff in W; [ | discriminate])); trivial.
 Qed.

 Lemma G_body0_inv13 : 
  EqObsInv inv13 
  {{R,LG}}
  E12 G_body0
  E13 G_body0 
  {{LG,rGk1,rGn}}.
 Proof.
  unfold G_body0.
  cp_test (R in_dom LG).
  rewrite proj1_MR; eqobs_in eE12E13.
  unfold inv13; eqobsrel_tail; unfold EP1, EP2, notR,req_mem_rel, andR; simpl; unfold O.eval_op; simpl;
    intros k m1 m2 H; decompose [and] H; clear H; intros.
  unfold O.assoc at 2; simpl.
  rewrite Ti_eqb_refl; simpl; rewrite Ti_eqb_refl; simpl.
  rewrite is_true_andb, is_true_forallb, is_true_forallb in H2 |- *; destruct H2; split; intros.
  assert (W:= H2 _ H6);
   repeat (rewrite Mem.get_upd_same in W|| (rewrite Mem.get_upd_diff in W; [ | discriminate])); trivial.
  unfold O.assoc; simpl.
  match goal with |- is_true (T.i_eqb _ _ _ (match (if ?x then _ else _) with Some _ => _ | None => _ end)) =>
   case_eq x; intros Heq; [ change (is_true x) in Heq | ] end.
  elim H4; rewrite is_true_existsb; exists x; split; trivial.
  rewrite is_true_Ti_eqb in Heq; rewrite <- Heq; apply Ti_eqb_refl.
  assert (W := H5 _ H6);
   repeat (rewrite Mem.get_upd_same in W|| (rewrite Mem.get_upd_diff in W; [ | discriminate])); trivial.
 Qed.

 Lemma EqObs_Dec12_Dec13 :
  EqObsInv inv13 
  (Vset.remove R' (Vset.remove bad ID)) 
  E12 Dec_body12 
  E13 Dec_body13 
  (Vset.remove bad OD).
 Proof.
  unfold Dec_body12, Dec_body13.
  cp_test (E.Eop O.Oor {testD, qG <! (Elen LG)}); rewrite proj1_MR.
  eqobs_in eE12E13.
  ep; deadcode eE12E13.
  eqobs_hd eE12E13.
  cp_test (Efst (ap_finv c) in_dom LH).
  cp_test (Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}]) in_dom LG).
  cp_test (Esnd (Efst (ap_finv c))|x| Esnd (LG [{Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}])}]) =?= zero_k1).
  match goal with |- equiv _ _ _ _ [If ?e then _ else _] _ =>
     ep_eq_r e true end.
    unfold EP1, EP2, andR; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; decompose [and] H; clear H.
    clear H2 H3 H4.
    match type of H5 with is_true (existsb (fun p => T.i_eqb _ _ ?x (fst p)) _) => set (s:= x) in * end.
    match type of H6 with is_true (existsb (fun p => T.i_eqb _ _ (BVxor _ ?x ?y) (fst p)) _) => 
      set (t:= x) in *; set (h := y) in *; set (r := BVxor (k0 k) t h) in * end.
    match type of H7 with is_true (T.i_eqb _ _ (BVxor _ _ (snd ?x)) _) => set (g := x) in *;
      set (m := (BVxor (k1 k) (snd s) (snd g))) in * end.
    match goal with |- ?x = true => change (is_true x) end.
    rewrite is_true_existsb; exists (s,h); split.
    change Ent.T.interp with T.interp in H5.
    apply (existsb_assoc k _ _ _ _ _ H5).
    rewrite is_true_existsb; exists (r,g); split.
    rewrite Mem.get_upd_diff; [ | discriminate].
    change Ent.T.interp with T.interp in H6. 
    apply (existsb_assoc k _ _ _ _ _ H6).
    mem_upd_simpl; simpl.
    rewrite H7, andb_true_r.
    unfold r; rewrite BVxor_bij.
    match goal with |- is_true (T.i_eqb k BS_k _ (f (k:=k) ?x)) => 
    replace x with (finv (k:=k) (m2 c)) end.
    rewrite finv_spec, Ti_eqb_refl; trivial.
    unfold s, t; destruct (finv (k:=k) (m2 c) ); trivial.
    ep_eq_r (E.Efind sh (E.Eexists rg
                      (E.Eop O.Oand
                         {c =?= ap_f (Efst (sh) | Efst (rg) |x| Esnd (sh)),
                         Esnd (Efst (sh)) |x| Esnd (Esnd (rg)) =?= zero_k1})
                      LG) LH)
           (Efst (ap_finv c) | LH [{Efst (ap_finv c)}]).
    unfold EP1, EP2, andR; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; decompose [and] H; clear H.
    clear H2 H3 H4.
    match type of H5 with is_true (existsb (fun p => T.i_eqb _ _ ?x (fst p)) _) => set (s:= x) in * end.
    match type of H6 with is_true (existsb (fun p => T.i_eqb _ _ (BVxor _ ?x ?y) (fst p)) _) => 
      set (t:= x) in *; set (h := y) in *; set (r := BVxor (k0 k) t h) in * end.
    match type of H7 with is_true (T.i_eqb _ _ (BVxor _ _ (snd ?x)) _) => set (g := x) in *;
     set (m := (BVxor (k1 k) (snd s) (snd g))) in * end.
    change Ent.T.interp with T.interp in H5, s.
    unfold h; refine (@existsb_find_default k _ _ s _ _ _ _ H5 _ _).
     rewrite is_true_existsb; exists (r,g); split.
     rewrite Mem.get_upd_diff; [ | discriminate].
     change Ent.T.interp with T.interp in H6. 
     apply (existsb_assoc k _ _ _ _ _ H6).
     mem_upd_simpl; simpl.
     rewrite H7, andb_true_r.
     unfold r; rewrite BVxor_bij.
     match goal with |- is_true (T.i_eqb k BS_k _ (f (k:=k) ?x)) => replace x with (finv (k:=k) (m2 c)) end.
     rewrite finv_spec, Ti_eqb_refl; trivial.
     unfold s, t; destruct (finv (k:=k) (m2 c) ); trivial.
    intros a Hdiff; rewrite <- not_is_true_false, is_true_existsb.
     intros (x, (Hin, Ht)).
     repeat (rewrite Mem.get_upd_same in Ht || (rewrite Mem.get_upd_diff in Ht; [ | discriminate])); simpl.
     rewrite is_true_andb in Ht; destruct Ht.
     rewrite is_true_Ti_eqb in H.
     apply Hdiff; unfold s; rewrite H,f_spec; trivial.
  ep_eq_r (E.Efind rg
   (E.Eop O.Oand
    {c =?= ap_f (Efst (ap_finv c) | Efst rg |x| (LH [{Efst (ap_finv c)}])),
     Esnd (Efst (ap_finv c)) |x| Esnd (Esnd rg) =?= zero_k1}) LG) 
  ((Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}])) | 
       LG [{Esnd (ap_finv c) |x| (LH [{Efst (ap_finv c)}])}]).
    unfold EP1, EP2, andR; simpl; unfold O.eval_op; simpl; intros k m1 m2 H; decompose [and] H; clear H.
    clear H2 H3 H4.
    match type of H5 with is_true (existsb (fun p => T.i_eqb _ _ ?x (fst p)) _) => set (s:= x) in * end.
    match type of H6 with is_true (existsb (fun p => T.i_eqb _ _ (BVxor _ ?x ?y) (fst p)) _) => 
      set (t:= x) in *; set (h := y) in *; set (r := BVxor (k0 k) t h) in * end.
    match type of H7 with is_true (T.i_eqb _ _ (BVxor _ _ (snd ?x)) _) => set (g := x) in *;
     set (m := (BVxor (k1 k) (snd s) (snd g))) in * end.
    refine (@existsb_find_default k BS_k0 BS_nk1 r _ _ _ _ H6 _ _).
     mem_upd_simpl; simpl.
     rewrite is_true_andb; split; [ | apply H7].
     unfold r; rewrite BVxor_bij.
     match goal with |- is_true (T.i_eqb k BS_k _ (f (k:=k) ?x)) => replace x with (finv (k:=k) (m2 c)) end.
     rewrite finv_spec, Ti_eqb_refl; trivial.
     unfold s, t; destruct (finv (k:=k) (m2 c) ); trivial.
    intros a Hdiff; rewrite <- not_is_true_false, is_true_andb.
     repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff ; [ | discriminate])); simpl.
     rewrite is_true_Ti_eqb; intros (H1, H2).
     apply Hdiff; unfold r, t.
     rewrite H1, f_spec; simpl.
     unfold h; rewrite BVxor_bij; trivial.
  repeat rewrite proj1_MR. eqobs_in eE12E13.
  match goal with |- equiv _ _ _ _ [If ?e then _ else _] _ =>
     ep_eq_r e false; [ | repeat rewrite proj1_MR; eqobs_in eE12E13] end.
    unfold req_mem_rel, inv13, EP1, EP2, notR, andR; simpl; unfold O.eval_op; simpl;
       intros k m1 m2 H; decompose [and] H; clear H.
   clear H0 H3 H4.
    match type of H6 with is_true (existsb (fun p => T.i_eqb _ _ ?x (fst p)) _) => set (s:= x) in * end.
    match type of H7 with is_true (existsb (fun p => T.i_eqb _ _ (BVxor _ ?x ?y) (fst p)) _) => 
      set (t:= x) in *; set (h := y) in *; set (r := BVxor (k0 k) t h) in * end.
    match type of H8 with ~ (is_true (T.i_eqb _ _ (BVxor _ _ (snd ?x)) _)) => set (g := x) in * end.
   rewrite is_true_andb, is_true_forallb, is_true_forallb in H5; destruct H5.
   rewrite <- not_is_true_false.
   rewrite is_true_existsb; intros (sh, (Hin, Hex)).
   assert (W:= H _ Hin); rewrite is_true_Ti_eqb in W.
     repeat (rewrite Mem.get_upd_same in W|| (rewrite Mem.get_upd_diff in W; [ | discriminate])).
   rewrite is_true_existsb in Hex; destruct Hex as (rg,(Hin', Ht)).
     repeat (rewrite Mem.get_upd_same in Hin'|| (rewrite Mem.get_upd_diff in Hin'; [ | discriminate])).
     repeat (rewrite Mem.get_upd_same in Ht|| (rewrite Mem.get_upd_diff in Ht; [ | discriminate])).
   assert (W':= H0 _ Hin'); rewrite is_true_Ti_eqb in W'.
     repeat (rewrite Mem.get_upd_same in W'|| (rewrite Mem.get_upd_diff in W'; [ | discriminate])).
   rewrite is_true_andb in Ht; destruct Ht.
   elim H8; rewrite W' in H3.
   unfold g, r, h, s, t.
   rewrite is_true_Ti_eqb in H1; rewrite H1, f_spec; simpl.
   change UOp.Tnk1 with BS_nk1; rewrite <- W, BVxor_bij; trivial.
  match goal with |- equiv _ _ _ _ [If ?e then _ else _] _ =>
     ep_eq_r e false; [ | repeat rewrite proj1_MR; eqobs_in eE12E13] end.
   unfold req_mem_rel, inv13, EP1, EP2, notR, andR; simpl; unfold O.eval_op; simpl;
       intros k m1 m2 H; decompose [and] H; clear H.
   clear H2 H3.
    match type of H5 with is_true (existsb (fun p => T.i_eqb _ _ ?x (fst p)) _) => set (s:= x) in * end.
    match type of H6 with ~ is_true (existsb (fun p => T.i_eqb _ _ (BVxor _ ?x ?y) (fst p)) _) => 
      set (t:= x) in *; set (h := y) in *; set (r := BVxor (k0 k) t h) in * end.
   rewrite is_true_andb, is_true_forallb, is_true_forallb in H4; destruct H4.
   rewrite <- not_is_true_false.
   rewrite is_true_existsb; intros (sh, (Hin, Hex)).
   assert (W:= H _ Hin); rewrite is_true_Ti_eqb in W.
     repeat (rewrite Mem.get_upd_same in W|| (rewrite Mem.get_upd_diff in W; [ | discriminate])).
   rewrite is_true_existsb in Hex; destruct Hex as (rg,(Hin', Ht)).
     repeat (rewrite Mem.get_upd_same in Hin'|| (rewrite Mem.get_upd_diff in Hin'; [ | discriminate])).
     repeat (rewrite Mem.get_upd_same in Ht|| (rewrite Mem.get_upd_diff in Ht; [ | discriminate])).
   elim H6; rewrite is_true_existsb; exists rg; split; trivial.
   unfold r, t, h, s.
   rewrite is_true_andb in Ht; destruct Ht.
   rewrite is_true_Ti_eqb in H2; rewrite H2, f_spec; simpl.
   rewrite W; change UOp.Tnk1 with BS_nk1; rewrite BVxor_bij, Ti_eqb_refl; trivial.
  match goal with |- equiv _ _ _ _ [If ?e then _ else _] _ =>
     ep_eq_r e false; [ | repeat rewrite proj1_MR; eqobs_in eE12E13] end.
   unfold req_mem_rel, inv13, EP1, EP2, notR, andR; simpl; unfold O.eval_op; simpl;
       intros k m1 m2 H; decompose [and] H; clear H.
   clear H0.
    match type of H4 with ~ is_true (existsb (fun p => T.i_eqb _ _ ?x (fst p)) _) => set (s:= x) in * end.
   rewrite is_true_andb, is_true_forallb, is_true_forallb in H3; destruct H3.
   rewrite <- not_is_true_false.
   rewrite is_true_existsb; intros (sh, (Hin, Hex)).
   assert (W:= H _ Hin); rewrite is_true_Ti_eqb in W.
     repeat (rewrite Mem.get_upd_same in W|| (rewrite Mem.get_upd_diff in W; [ | discriminate])).
   rewrite is_true_existsb in Hex; destruct Hex as (rg,(Hin', Ht)).
     repeat (rewrite Mem.get_upd_same in Hin'|| (rewrite Mem.get_upd_diff in Hin'; [ | discriminate])).
     repeat (rewrite Mem.get_upd_same in Ht|| (rewrite Mem.get_upd_diff in Ht; [ | discriminate])).
   elim H4; rewrite is_true_existsb; exists sh; split; trivial.
   unfold s.
   rewrite is_true_andb in Ht; destruct Ht.
   rewrite is_true_Ti_eqb in H1; rewrite H1, f_spec; simpl.
   rewrite Ti_eqb_refl; trivial.
 Qed.

 Definition iE12E13 :=
  let RM := Vset.empty in
  let piH := add_info H RM RM eE12E13 H_body0_inv13 in 
  let piG := add_info G RM RM piH G_body0_inv13 in
  let piGA := add_refl_info GAdv piG in
  let piD := add_info Dec RM RM piGA EqObs_Dec12_Dec13 in
   adv_info piD.

 Definition Inverter_body :=
  [
   Ydef <- false;
   LG <- Nil _; 
   LH <- Nil _;
   LD <- Nil _;
   Dc <- 0;
   Gc <- 0;
   M <c- A with{};
   Y' <- Ye;
   Ydef <- true;
   b' <c- A' with {Y'}
  ].

 Definition I_res := LH.

 Definition EI :=
  add_decl (mkEnv H_body0 G_body0 Dec_body13)
  Inverter I_params (refl_equal true) Inverter_body I_res.

 Lemma EqADII : Eq_adv_decl PrOrcl PrPriv EI EI.
 Proof.
  red; intros; auto.
 Qed.

 Lemma EqAD13I : Eq_adv_decl PrOrcl PrPriv E13 EI.
 Proof.
  red; intros.
  unfold E13, EI, proc_params, proc_body, proc_res.
  generalize (BProc.eqb_spec (BProc.mkP Inverter) (BProc.mkP f0)).
  destruct (BProc.eqb (BProc.mkP Inverter) (BProc.mkP f0)); intros.
  elim H0; rewrite <- H1; simpl; trivial.
  rewrite add_decl_other_mk; trivial.
  auto.
 Qed.

 Lemma A_wf_EI : WFAdv PrOrcl PrPriv Gadv Gcomm EI A.
 Proof.
  apply WFAdv_trans with E13.
  red; intros; unfold EI, proc_params.
  rewrite add_decl_other_mk; trivial.
  intro Heq; rewrite <- Heq in H; discriminate H.    
  apply EqAD13I.
  intros H; discriminate H.
  intros H; discriminate H.
  unfold E13; apply A_wf_E.
 Qed.

 Lemma A'_wf_EI : WFAdv PrOrcl PrPriv Gadv Gcomm EI A'.
 Proof.
  apply WFAdv_trans with E13.
  red; intros; unfold EI, proc_params.
  rewrite add_decl_other_mk; trivial.
  intro Heq; rewrite <- Heq in H; discriminate H.    
  apply EqAD13I.
  intros H; discriminate H.
  intros H; discriminate H.
  unfold E13; apply A'_wf_E.
 Qed.

 Lemma EqObs_Dec_body13 : forall E1 E2,
  EqObsInv trueR (Vset.remove bad (Vset.remove R' ID))  
  E1 Dec_body13 
  E2 Dec_body13 
  {{Dc,mn}}.
 Proof.
  intros E1' E2'; eqobs_in.
 Qed. 

 Definition iE13EI : eq_inv_info trueR E13 EI :=
  let piH := add_refl_info H (empty_info E13 EI) in
  let piG := add_refl_info G piH in
  let piGA := add_refl_info GAdv piG in
  let piD := add_info Dec Vset.empty Vset.empty piGA (EqObs_Dec_body13 E13 EI) in
  let piA := add_adv_info_false EqAD13I (A_wf_E _ _ _ _) piD in
  let piA' := add_adv_info_false EqAD13I (A'_wf_E _ _ _ _) piA in
   piA'.

 Definition iEI_pre : eq_inv_info trueR EI EI :=
  let piH := add_refl_info H (empty_info EI EI) in
  let piG := add_refl_info G piH in
  let piGA := add_refl_info GAdv piG in
  let piD := add_info Dec Vset.empty Vset.empty piGA (EqObs_Dec_body13 EI EI) in
  let piA := add_adv_info_false EqADII A_wf_EI piD in
  let piA' := add_adv_info_false EqADII A'_wf_EI piA in
   piA'.

 Lemma EqObs_Inverter : 
  EqObsInv trueR {{Ye,Y',g_a}}
  EI Inverter_body 
  EI Inverter_body 
  {{LH}}.
 Proof.
  eqobs_in iEI_pre.
 Qed. 

 Definition iEI : eq_inv_info trueR EI EI :=
  add_info Inverter Vset.empty Vset.empty iEI_pre EqObs_Inverter.

 Definition Gow := Gf lI sn sk1 t.

 Lemma Pr_12_bad2 : forall k m,
  Pr E12 G4 m (EP k (E.Eexists sh (Efst sh =?= (GR'n | GR'k1)) LH)) ==
  Pr EI Gow m (EP k ((sn | sk1) in_dom lI)).
 Proof.
  intros k m.
  transitivity
    (Pr EI 
    ([ 
    GR'n <$- {0,1}^n;
    GR'k1 <$- {0,1}^k1;
    T' <$- {0,1}^k0;
    lI <c- Inverter with {ap_f ((GR'n|GR'k1)| T')}
    ] ++
    [sn <- GR'n;
    sk1 <- GR'k1;
    t <- T']) m (EP k ((sn|sk1) in_dom lI))).
  
Focus 2.
   apply EqObs_Pr with {{Y',g_a}}.
   unfold Gf.
   alloc_r iEI sn GR'n.
   alloc_r iEI sk1 GR'k1.
   alloc_r iEI t T'.
   ep iEI; swap iEI; eqobs_in iEI.

  transitivity 
   (Pr EI 
    (([ 
      GR'n <$- {0,1}^n;
      GR'k1 <$- {0,1}^k1;
      T' <$- {0,1}^k0;
      Ye <- ap_f ((GR'n|GR'k1)| T')
     ] ++ Inverter_body) ++ [lI <- LH ])
     m (EP k (E.Eexists sh (Efst sh =?= (GR'n|GR'k1)) LH))).
  
Focus 2.
   unfold Pr at 2; rewrite deno_app_elim.
   transitivity 
    (Pr EI 
     ([
       GR'n <$- {0,1}^n;
       GR'k1 <$- {0,1}^k1;
       T' <$- {0,1}^k0;
       lI <c- Inverter with {ap_f ((GR'n | GR'k1) | T')} ] ++
       [ LH <- lI ]) 
     m (EP k (E.Eexists sh (Efst (sh) =?= (GR'n | GR'k1)) LH))).

Focus 2.
   unfold Pr; rewrite deno_app_elim. apply mu_stable_eq.
    refine (ford_eq_intro _); intros m'.
    repeat (rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim).
    repeat rewrite deno_nil_elim.
    unfold charfun, EP, restr; simpl; unfold O.eval_op; simpl.
    mem_upd_simpl.
    match goal with 
     |- (if ?x then _ else _) == (if ?y then _ else _) =>
       case_eq x; intros Heq;
       [change (is_true x) in Heq; replace y with true | 
        rewrite <- not_is_true_false in Heq; replace y with false]; trivial 
    end.
    symmetry.
    match goal with 
     |- ?x = true => change (is_true x) 
    end.
    rewrite is_true_existsb in Heq |- *.
    destruct Heq as (x, (Hin, Heq)); exists x; split; trivial.
    generalize Heq; clear Heq; mem_upd_simpl.
    intros.
    apply is_true_Ti_eqb.    
    rewrite is_true_Ti_eqb in Heq; auto.
    symmetry; rewrite <- not_is_true_false.
    rewrite is_true_existsb in Heq |- *; intros H.
    apply Heq; clear Heq; destruct H as (x, (Hin, Heq)); exists x; split; trivial.
    generalize Heq; clear Heq; mem_upd_simpl.
    intros.
    rewrite is_true_Ti_eqb.    
    rewrite is_true_Ti_eqb in Heq; auto.
   
    apply EqObs_Pr with {{Y',g_a}}.
    apply EqObs_trans with E13 G4.
    apply equiv_weaken with 
     (req_mem_rel 
      (fv_expr (E.Eexists sh (Efst (sh) =?= (GR'n | GR'k1)) LH)) inv13).
    intros k2 m1 m2 (H1, H2); trivial.
    eqobs_tl iE12E13.
    unfold inv13; eqobsrel_tail; simpl; unfold O.eval_op; simpl; red; trivial.
    apply EqObs_trans with EI G4.
    eqobs_in iE13EI.
    ep iEI; deadcode iEI; swap iEI; eqobs_in iEI.
    apply EqObs_Pr with {{Y',g_a}}.
   inline_r iEI Inverter.
   ep iEI; deadcode iEI; swap iEI; eqobs_in iEI.
 Qed.

 Close Scope nat_scope.

 Lemma exact_security : forall k m,
  Uabs_diff (Pr E0 G0 m (EP k (b =?= b'))) [1/2] <=
  Pr EI Gow m (EP k ((sn | sk1) in_dom lI)) +
  (3 * qD_poly k */ qG_poly k /2^k0 k) + 
  (qD_poly k */ qD_poly k /2^k0 k) +
  (4 */ qD_poly k /2^k0 k) + 
  qG_poly k /2^k0 k +
  (2 */ qD_poly k /2^k1 k).
 Proof.
  intros; simpl.
  rewrite PrG0_bad_11.
  rewrite PR_11_bad.
  rewrite Pr_E11r_bad.
  rewrite PR_11r_bad1.
  rewrite Pr_11r_bad2.
  rewrite Pr_12_bad2.
  rewrite Pr_E11r_bad3.

  repeat rewrite plus_Nmult_distr.
  repeat rewrite Nmult_Uplus_distr.
  repeat rewrite Uplus_assoc.
  rewrite Nmult_0; Usimpl. 
  apply Uplus_le_compat; trivial.

  repeat rewrite <- (Uplus_sym (qD_poly k/2^k1 k)).
  repeat rewrite <- Uplus_assoc. 
  apply Uplus_le_compat; trivial.

  rewrite Uplus_sym, <- Uplus_assoc, Uplus_sym.
  repeat rewrite <- Uplus_assoc. 
  apply Uplus_le_compat; trivial.
  apply Uplus_le_compat; trivial.
 
  repeat rewrite (Uplus_sym (qD_poly k/2^k0 k)).
  repeat rewrite <- Uplus_assoc. 
  apply Uplus_le_compat; trivial.

  repeat rewrite (Uplus_sym (qD_poly k/2^k0 k)).
  repeat rewrite Uplus_assoc.
  rewrite (Uplus_sym (qD_poly k */ qD_poly k/2^k0 k)).  
  trivial.  
 Qed.

End ADVERSARY_AND_PROOF.
