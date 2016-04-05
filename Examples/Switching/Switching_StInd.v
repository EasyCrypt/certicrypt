Require Import SwitchingSem.

Set Implicit Arguments.


(* ***************************** SOME AUXILIARY STUFF  ***************************** *)

 Lemma lossless_while : forall E (b:E.expr T.Bool) c (variant:E.expr T.Nat),
    lossless E c ->
    (forall k (m:Mem.t k), E.eval_expr b m -> 
       range (EP k (variant <! (E.eval_expr variant m))) ([[c]] E m)) ->  
    lossless E [while b do c].
 Proof.
  intros E b C variant Hloss Hvar k.
  assert (forall (n:nat) (m : Mem.t k), E.eval_expr variant m = n ->
     (mu (([[ [while b do C] ]]) E m)) (fun _ : Mem.t k => 1) == 1).
   induction n using lt_wf_ind;intros.
   rewrite deno_while_elim, deno_cond_elim.
   case_eq (E.eval_expr b m);intros Heq;[ | rewrite deno_nil_elim;trivial].
   rewrite deno_app_elim, <- (Hloss k m).
   apply range_eq with (1:= Hvar k m Heq).
   intros m' Hlt;apply (H (E.eval_expr variant m'));trivial.
   rewrite <- H0;unfold EP in Hlt;simpl in Hlt;unfold O.eval_op in Hlt;simpl in Hlt.
   apply leb_complete in Hlt; omega.
  intros m;apply (H (E.eval_expr variant m) m (refl_equal _)).
 Qed.

 Lemma range_EP_equiv_EP1 : forall E c (pre post:E.expr T.Bool),
    equiv (Meq /-\ EP1 pre) E c E c (EP1 post) ->
    forall k (m:Mem.t k), E.eval_expr pre m -> range (EP k post) ([[ c ]] E m).
 Proof.
  intros E C pre post Hequiv k m Hpre f Hf.
  rewrite <- (mu_zero ([[C]] E m)).
  symmetry;apply equiv_deno with (1:= Hequiv);[intros m1 m2 Hpost | split;trivial].
  symmetry;apply (Hf m1 Hpost).
 Qed.

 (* Instanciation *)
 Lemma lossless_while_equiv : forall E (b:E.expr T.Bool) c (variant:E.expr T.Nat),
     lossless E c ->
     (forall (n:nat), equiv (Meq /-\ EP1 (b && (variant =?= n))) E c E c 
          (req_mem_rel Vset.empty (EP1 (variant <! n)))) ->
     lossless E [while b do c].
 Proof.
  intros E b C variant Hloss Hequiv.
  apply lossless_while with (variant := variant);[trivial | ].
  intros k m Hb;apply range_EP_equiv_EP1 with (pre:= (b && (variant =?= (E.eval_expr variant m)))).
    apply equiv_weaken with (2:= Hequiv (E.eval_expr variant m)).
    intros k1 m1 m2 (H1, H2);trivial.
    simpl;unfold O.eval_op;simpl;rewrite Hb;apply nat_eqb_refl.
 Qed.

 Lemma minus_lt_compat_l: forall n m p : nat, (n < m)%nat -> (p - m < p - n)%nat.
 Proof.
  intros.
 Admitted.

 Definition get_option (o:option Vset.t) :=
  match o with 
  | Some s => s 
  | None => Vset.empty
  end.

(* ********************************************************************************* *)


Notation bad := (Var.Gvar T.Bool 1).
Notation L := (Var.Gvar (T.List (T.Pair (T.User BS_k) (T.User BS_k))) 2).
Notation R := (Var.Gvar (T.List (T.User BS_k)) 3).
Notation R' := (Var.Gvar (T.List (T.User BS_k)) 4).
Notation x := (Var.Lvar (T.User BS_k) 5).
Notation y := (Var.Lvar (T.User BS_k) 6).
Notation b := (Var.Lvar T.Bool 7).
Notation yR := (Var.Gvar (T.User BS_k) 8).
Notation used := (Var.Gvar T.Bool 9).
Notation N := (Var.Lvar T.Nat 10).
Notation Rinit := (Var.Gvar (T.List (T.User BS_k)) 11).
Notation F := (Proc.mkP 1 ((T.User BS_k):: nil) (T.User BS_k)).


Definition F_params : var_decl (Proc.targs F) := dcons _ x (dnil _).
Definition F_res := y.


Section ADVERSARY.

 Variable env_adv : env.

 Notation A  := (Proc.mkP 2 nil T.Bool).

 Definition A_params : var_decl (Proc.targs A) := dnil _.
 Variable A_body : cmd.
 Variable A_res : E.expr T.Bool.

 Definition mkEnv F_body := 
  let Ef := add_decl env_adv F F_params (refl_equal true) F_body F_res in
   add_decl Ef A A_params (refl_equal true) A_body A_res.



 (* *********************************************************************** *)
 (* ************** GAME 0: random function with lazy sampling ************* *)
 (* *********************************************************************** *)

 Definition G0 :=
  [ 
   L <- Nil _;
   b <c- A with {}
  ].

 Definition O0 :=
 [ 
  If !(x in_dom L) _then 
  [ 
   y <$- {0,1}^k; 
   L <- (x|y) |::| L
  ];
  y <- L[{x}]
 ].

 Definition E0 := mkEnv O0.




 Definition PrOrcl := PrSet.singleton (BProc.mkP F).
 Definition PrPriv := PrSet.empty.

 Definition Gadv := Vset.empty.
 Definition Gcomm := Vset.empty.

 Hypothesis A_wf : WFAdv PrOrcl PrPriv Gadv Gcomm E0 A.
 
 Hypothesis A_lossless : forall Fbody,
  (forall O, PrSet.mem O PrOrcl -> 
   lossless (mkEnv Fbody) (proc_body (mkEnv Fbody) (BProc.p_name O))) -> 
  lossless (mkEnv Fbody) A_body.

 Hypothesis A_range :forall k m, 
  range (EP k (Elength L <=! q)) ([[G0]] E0 m).

 Lemma EqAD : forall F_body1 F_body2, 
  Eq_adv_decl PrOrcl PrPriv (mkEnv F_body1) (mkEnv F_body2).
 Proof.
  unfold Eq_adv_decl, mkEnv; intros.
  unfold proc_params, proc_body, proc_res.
  generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto;
   intros Heq; 
    (apply H; rewrite <- Heq; vm_compute; reflexivity)
    || (apply H0; rewrite <- Heq; vm_compute; reflexivity).
 Qed.
 
 Lemma EqOP : forall F_body1 F_body2, 
  Eq_orcl_params PrOrcl (mkEnv F_body1) (mkEnv F_body2).
 Proof.
  unfold Eq_orcl_params, mkEnv; intros.
  unfold PrOrcl in H.
  apply PrSet.singleton_complete in H; inversion H; simpl.
  vm_compute; trivial.
 Qed.

 (** The adversary is well-formed in any environment constructed with [mkEnv].
     This follows from the adversary being well-formed in [E0] *)
 Lemma A_wf_E : forall F_body,
  WFAdv PrOrcl PrPriv Gadv Gcomm (mkEnv F_body) A.
 Proof.
  intros; apply WFAdv_trans with (5:=A_wf).
  unfold E0; apply EqOP.
  unfold E0; apply EqAD.
  vm_compute; intro; discriminate.
  vm_compute; intro; discriminate.
 Qed.


 (* Functions to build [eq_inv_info] *)
 Definition i_refl Fbody Fbody' Fr Fr' :=
  let E := mkEnv Fbody in
   let E' := mkEnv Fbody' in
    let piF := add_refl_info_rm F Fr Fr' (empty_info E E') in
     add_adv_info_lossless (EqAD _ _ ) (A_wf_E _) (@A_lossless _) (@A_lossless _) piF.

 Definition iEiEi Fbody := i_refl Fbody Fbody Vset.empty Vset.empty.

 Definition iEinv Fbody Fbody' inv 
  (ie:eq_inv_info inv (mkEnv Fbody) (mkEnv Fbody')) 
  R1 R2 I O
  (Fbody_Fbody': EqObsInv inv I (mkEnv Fbody) Fbody (mkEnv Fbody') Fbody' O):=
  let E := mkEnv Fbody in
   let E' := mkEnv Fbody' in 
    let piF := add_info F R1 R2 ie Fbody_Fbody' in
     add_adv_info_lossless (EqAD _ _ ) (A_wf_E _) (@A_lossless _) (@A_lossless _) piF.

 (* Function to build [upto_bad_info] *)
 Definition i_upto bad Fbody Fbody' :=
  let E := mkEnv Fbody in
   let E' := mkEnv Fbody' in
    let i0 := empty_upto_info bad E E' in
     let iH := add_upto_info i0 F in
      add_adv_upto_info iH (EqAD _ _ ) (EqOP _ _) (A_wf_E _).



 (* *********************************************************************** *)
 (* ************* GAME 1: random function with eager sampling ************* *)
 (* *********************************************************************** *)

 Definition G1 :=
 [
   R <- E.Cnil (T.User BS_k);
   while Elength (R) <! q do 
   [
     yR <$- {0,1}^k; 
     R <- R |++| yR |::| Nil _
   ];
   R' <- R;
   L <- Nil _;
   b <c- A with{}
 ].

 Definition O1 :=
 [ 
   If !(x in_dom L) _then 
   [ 
     If !(R =?= (Nil _)) then 
       [ y <- Ehd R; R <- Etl R ]
                         else 
       [ y <$- {0,1}^k ];
     L <- (x|y) |::| L
   ];
   y <- L[{x}]
 ].

 Definition E1 := mkEnv O1.


 Definition G2_prefix := 
 [
   R <- Nil _;
   while (Elength L +! Elength R <! q) do 
   [
     yR <$-{0,1}^k; 
     R <- R |++| (yR |::| Nil _)
   ];
   yR <$-{0,1}^k
 ].

 Definition iE0 := i_refl O0 O0 Vset.empty Vset.empty.

 
 Lemma lossless_G2_prefix: lossless E0 (removelast G2_prefix).
 Proof.
  simpl.
  apply lossless_cons; [apply lossless_assign | ].
  apply lossless_while_equiv with (variant := (q -! Elength R)).
  apply is_lossless_correct with (pi := refl1_info iE0); vm_compute; trivial.
  intros n; eqobsrel_tail; unfold EP1,implMR,Meq; simpl; unfold O.eval_op; simpl;
    intros k1 m1 m2 (Heq, H1); subst.
  rewrite is_true_andb in H1; destruct H1 as [_ H]; apply nat_eqb_true in H.
  intros v _; apply leb_correct.
  rewrite plus_comm, <-H; apply lt_le_S; apply minus_lt_compat_l.
  rewrite app_length; simpl length.
  generalize (length (m2 R)); intros; omega.
 Qed.

 Notation L1 := (Var.Gvar (T.List (T.Pair (T.User BS_k) (T.User BS_k))) 12).

 Lemma G2_prefix_swaps_Or : equiv Meq E0 (O0 ++ G2_prefix) E1 (G2_prefix ++ O1) Meq.
 Proof.
  unfold O0, O1.
  union_mod; [ trivial | ].
  swap; eqobs_tl.
  cp_test (x in_dom L);rewrite proj1_MR.
    (* case [ x in_dom L ] *)
    eqobs_in.
    cp_test (Elength (L) <! q).
      (* case [ |L| < q ] *)
      alloc_l L L1; ep.
      match goal with |- equiv _ _ (?i1::?i2::?i3::?c) _ _ _ =>
        apply equiv_trans_eq_mem_l with trueR E0 ((i1::i2::c)++[i3]) 
      end.
      rewrite proj1_MR; union_mod; [trivial | swap; eqobs_in ].
      eqobs_tl; ep; deadcode.
      match goal with |- equiv ?P _ _ ?E2 (?i1::(while ?e do ?C)::?T) ?Q => 
        change (i1::(while e do C)::T) with ([i1] ++ ([while e do C] ++ T));
        apply equiv_trans_eq_mem_r with trueR E2 ([i1]++([If e _then C ++ [while e do C] ]++ T)) 
      end.
      rewrite proj1_MR; apply equiv_eq_sem; intros k m.
      rewrite deno_app, deno_app; apply Mlet_eq_compat;[trivial | ].
      apply ford_eq_intro; clear m;intros m.
      rewrite deno_app, deno_app;apply Mlet_eq_compat;[|trivial].
      apply deno_while.
      ep. ep_eq_r (Elength (Nil (SwitchingSem.Sem.T.User BS_k))) 0%nat;[ trivial | ].
  ep_eq_r (Elength (L) <! q) true.
    intros k m1 m2 (H1, (_, H2));exact H2.
  rewrite proj1_MR.
  match goal with |- equiv ?P _ [?i1;?i2;?i3] _ [?i4;?i5;?i6;?i7;?i8] ?Q => 
    change [i1;i2;i3] with ([i1;i2]++([i3] ++ nil));
    change [i4;i5;i6;i7;i8] with ([i4;i5;i6] ++ ([i7] ++[i8])) end.
  apply equiv_app with (req_mem_rel (Vset.add x (Vset.singleton L))
                          (fun k m1 m2 => E.eval_expr R m2 = E.eval_expr (y |::| R) m1)).
   set (P:= (fun (k : nat) (m1 m2 : Mem.t k) =>
      E.eval_expr R m2 = E.eval_expr (y |::| R) m1)).
   assert (Hdep : depend_only_rel P (fv_expr (y |::| R)) (fv_expr R)).
       red;intros;red.
       rewrite <- (depend_only_fv_expr _ H), <- (depend_only_fv_expr _ H0);trivial.
   assert (Hdep1 := @depend_only_req_mem_rel (Vset.add x (Vset.singleton L)) _ _ _ Hdep).
   assert (Hdec : decMR Meq) by auto.
   match type of Hdep1 with depend_only_rel ?p ?x1 ?x2 => set (P1 := p);set (X1 := x1); set (X2:= x2) end.
   set (c1 := [y <$- {0,1}^k; R <- Nil _]).
   set (c2 := [R <- Nil _;yR <$- {0,1}^k;R <- yR |::| Nil _]).
   compute_assertion Heq1 res1 (alloc_c_out (refl1_info (empty_info E0 E1)) y yR c1 X1).
   refine (@alloc_c_out_equiv_l _ y yR _ E0 (refl1_info (empty_info E0 E1)) c1 res1 E1 c2 
                 X1 X2 P1 Hdec Hdep1 Heq1 _).
    ep;unfold P1, P.
    eqobsrel_tail;intros k m1 m2 Heq;unfold Meq in Heq;subst;simpl;unfold O.eval_op;simpl.
    intros;repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff;[ | discriminate]));trivial.
   apply equiv_app with (req_mem_rel (Vset.add x (Vset.singleton L))
                          (fun k m1 m2 => E.eval_expr R m2 = E.eval_expr (y |::| R) m1)).
   eapply equiv_weaken;[ | apply equiv_while].
    intros k m1 m2 (H1, _);trivial.
    intros k m1 m2 (H1, H2);generalize H2;clear H2.
(* Opaque leb.    *)
    simpl;unfold O.eval_op;simpl;intros Heq;rewrite Heq, (H1 _ L);trivial.
    simpl length. repeat rewrite <- plus_Snm_nSm;trivial.
   eqobsrel_tail;intros k m1 m2;simpl;unfold O.eval_op;simpl; intros (H1, (H2, _)).
   intros;repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff;[ | discriminate]));trivial.
   rewrite H2;trivial.
  ep_eq_r (R =?= Nil _) false.
  simpl;unfold O.eval_op;simpl;intros k m1 m2 (H1, H2);rewrite H2;trivial.
  apply equiv_weaken with
     (req_mem_rel (Vset.add x (Vset.singleton L)) 
         (fun k m1 m2 => E.eval_expr R m1 = E.eval_expr R m2 /\  E.eval_expr y m1 = E.eval_expr y m2)).
     intros k m1 m2 (H1, (H2, H3)).
     change (kreq_mem (Vset.add L (Vset.add y (Vset.add x (Vset.singleton R)))) m1 m2).
     intros t v;repeat rewrite VsetP.add_spec.
     intros [H | [ H | [ H | H ] ] ];
      try (apply Vset.singleton_complete in H);
      inversion H;simpl;trivial;(apply (H1 _ L)|| apply (H1 _ x));trivial.
   eqobsrel_tail;unfold EP1;simpl;unfold O.eval_op;simpl;intros k m1 m2 (H1, H2).
   repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff;[ | discriminate])).
   rewrite H2;auto.
  red;red;trivial.
  red;red;trivial.

    (* case [ x not_in_dom L ] *)
  match goal with |- equiv _ _ [?i1;?i2;?i3;?i4] _ _ _ =>
    change [i1;i2;i3;i4] with ([i1;i2;i3]++[i4]);
    apply equiv_trans_eq_mem_l with (~- EP1 (Elength (L) <! q)) E0 ([i1;i2;i3] ++ nil) end.
  union_mod;[rewrite proj1_MR;trivial | ].
  apply equiv_app with (req_mem_rel (Vset.add y (Vset.add L (Vset.add R (Vset.singleton yR)))) 
                         (~-EP1 ((Elength (L) +! Elength (R)) <! q))).
    Opaque leb. 
    eqobsrel_tail;unfold EP1, notR;simpl;unfold O.eval_op;simpl;intros k m1 m2 (H1, H2).
   apply not_is_true_false in H2;apply leb_complete_conv in H2.
   intros v _ Hleb; apply leb_complete in Hleb.
   rewrite <-plus_n_O in Hleb; generalize H2 Hleb; 
   match goal with |- (lt _ (?x + _) ) -> _ -> _ => generalize x; intros end;
   omega.
  ep_eq_l ((Elength (L) +! Elength (R)) <! q) false.
  unfold notR, EP1;intros k m1 m2 (_, H);apply not_is_true_false in H;trivial.
  eqobs_in.
  match goal with |- equiv _ _ _ _ [?i1;?i2;?i3;?i4] _ =>
    change [i1;i2;i3;i4] with (([i1]++[i2])++[i3;i4]);
    apply equiv_trans_eq_mem_r with (~- EP1 (Elength (L) <! q)) E1 (([i1] ++ nil) ++[i3;i4]) end.
  union_mod;[rewrite proj1_MR;trivial | ].
  apply equiv_app with (kreq_mem (Vset.add x (Vset.add y (Vset.add L (Vset.add R (Vset.singleton yR)))))).
  apply equiv_app with (req_mem_rel (Vset.add x (Vset.add y (Vset.add L (Vset.add R (Vset.singleton yR))))) 
                         (~-EP1 ((Elength (L) +! Elength (R)) <! q))).
   eqobsrel_tail;unfold EP1, notR;simpl;unfold O.eval_op;simpl;intros k m1 m2 (H1, H2).
   apply not_is_true_false in H2;apply leb_complete_conv in H2.
   intros Hleb;apply leb_complete in Hleb. 
   rewrite <-plus_n_O in Hleb; generalize H2 Hleb; 
   match goal with |- (lt _ (?x + _) ) -> _ -> _ => generalize x; intros end;
   omega.
   ep_eq_l ((Elength (L) +! Elength (R)) <! q) false.
   unfold notR, EP1;intros k m1 m2 (_, H);apply not_is_true_false in H;trivial.
   eqobs_in.
   eqobs_in.
  ep;swap;eqobs_in.
  intros k m1 m2 (H1, (H2, H3));trivial.
  intros k m1 m2 (H1, (H2, H3));trivial.
 Qed.


 Definition XG2_prefix : Vset.t := 
  Eval vm_compute in get_option (modify (refl1_info (empty_info E0 E0)) Vset.empty G2_prefix).

 Lemma G2_prefix_Modify : forall E, Modify E XG2_prefix G2_prefix.
 Proof.
  intros E;apply modify_correct with (refl1_info (empty_info E E)) Vset.empty.
  vm_compute;trivial.
 Qed.

 Definition IG2_prefix := Vset.singleton L.

 Lemma EqObs_G2_prefix : EqObs (Vset.union IG2_prefix XG2_prefix) E0 G2_prefix E1 G2_prefix XG2_prefix.
 Proof. eqobs_in. Qed.

 Lemma IX_glob :  forall x : VarP.Edec.t, Vset.mem x (Vset.union IG2_prefix XG2_prefix) -> Var.is_global x.
 Proof.
  apply Vset.forallb_correct.
  intros x y Heq;rewrite Heq;trivial.
  vm_compute;trivial.
 Qed.

 Definition sw_i := @add_sw_info_Adv
  G2_prefix XG2_prefix IG2_prefix E0 E1 (G2_prefix_Modify _) (G2_prefix_Modify _) EqObs_G2_prefix IX_glob
  (@add_sw_info G2_prefix XG2_prefix IG2_prefix E0 E1 (G2_prefix_Modify _) (G2_prefix_Modify _) EqObs_G2_prefix IX_glob
    (fun _ _ => None) _ F G2_prefix_swaps_Or) _ A _ _ _ _ (EqAD _ _) (A_wf_E _).

 Lemma G2_prefix_swaps_Adv: equiv 
  Meq 
  E0 ([b <c- A with{}] ++ G2_prefix) 
  E1 (G2_prefix ++ [b <c- A with{}]) 
  Meq. 
 Proof.
   apply check_swap_c_correct with XG2_prefix IG2_prefix sw_i.
   apply G2_prefix_Modify. 
   apply G2_prefix_Modify. 
   apply EqObs_G2_prefix. 
   vm_compute; trivial.
 Qed.


 Definition iE1 := i_refl O1 O1 Vset.empty Vset.empty.

 Lemma EqObs_G0_G1: equiv Meq E0 G0 E1 G1 (kreq_mem {{L,b}}).
 Proof.
  apply equiv_trans with Meq (kreq_mem {{L,b}}) (kreq_mem {{L,b}}) E0 (G0 ++ G2_prefix);
    [ auto | red; trivial | apply req_mem_trans | | ].
    rewrite (app_nil_end G0) at 1; apply equiv_app with (kreq_mem {{L,b}}); [ eqobs_in iE0 | ].
      deadcode; union_mod.
      apply equiv_strengthen with (kreq_mem Vset.empty).
        intros k1 m1 m2 H1;apply req_mem_weaken with (2:= H1); vm_compute; trivial.
      apply equiv_lossless_Modify with Vset.empty Vset.empty Vset.empty {{yR, R}}; auto.
        apply lossless_nil.
        apply lossless_G2_prefix.
        apply modify_correct with (refl1_info iE0) Vset.empty;vm_compute;trivial.
        apply modify_correct with (refl1_info iE0) Vset.empty;vm_compute;trivial.
    change (G0 ++ G2_prefix) with (([L<-Nil _] ++ [b <c- A with {}])++G2_prefix); rewrite app_ass.
    apply equiv_trans_eq_mem_l with trueR E1 ([L<-Nil _] ++ (G2_prefix ++ [b <c- A with {}])).
      rewrite proj1_MR;apply equiv_app with Meq.
        union_mod;[trivial | eqobs_in].
        apply G2_prefix_swaps_Adv.
        eqobs_tl iE1;ep.
          ep_eq_l (Elength (Nil (SwitchingSem.Sem.T.Pair (SwitchingSem.Sem.T.User BS_k)
                     (SwitchingSem.Sem.T.User BS_k)))) 0%nat;trivial.
          deadcode;swap;eqobs_in.
          red; red; trivial.
 Qed.



 (* *********************************************************************** *)
 (* *********** GAME 2: random permutation with eager sampling ************ *)
 (* *********************************************************************** *)

 Definition G2 :=
 [
   R <- E.Cnil (T.User BS_k);
   while Elength (R) <! q do 
   [
     yR <$- {0,1}^k; 
     while y is_in R do [ y <$- {0,1}^k ];
     R <- R |++| yR |::| Nil _
   ];
   R' <- R;
   L <- Nil _;
   b <c- A with{}
 ].

 Definition O2 := O1.

 Definition E2 := mkEnv O2.

 Definition iE2 := i_refl O2 O2 Vset.empty Vset.empty.





 (* *********************************************************************** *)
 (* ************ GAME 3: random permutation with lazy sampling ************ *)
 (* *********************************************************************** *)

 Definition G3 := G0.
  
 Definition O3 :=
 [ 
   If !(x in_dom L) _then 
   [ 
     y <$- {0,1}^k; 
     while y in_range L do [ y <$- {0,1}^k ];
     L <- (x|y) |::| L
   ];
   y <- L[{x}]
 ].

 Definition E3 := mkEnv O3.

 Definition iE3 := i_refl O3 O3 Vset.empty Vset.empty.

 Definition G3_prefix := 
 [
   R <- Nil _;
   while (Elength L +! Elength R <! q) do 
   [
     yR <$-{0,1}^k; 
     while yR is_in R do [yR <$- {0,1}^k]; 
     R <- R |++| (yR |::| Nil _)
   ];
   yR <$-{0,1}^k
 ].

 Lemma lossless_G3_prefix: lossless E3 (removelast G3_prefix).
 Proof.
  simpl.
  assert (H' : forall k (m:Mem.t k) f E,  
    (length (m R) < length (E.eval_support ({0,1}^k) m))%nat -> 
    mu ([[ [while y is_in R do [y <$- {0,1}^k] ] ]] E m) f == 1).
    admit.
  apply lossless_cons; [apply lossless_assign | ].
 Admitted.
 (*
  apply lossless_while_equiv with (variant := (q -! Elength R)).
  apply lossless_cons; [apply lossless_random | ].
  apply lossless_cons; [apply H' | ].
  apply lossless_assign.
  intro n.
    match goal with |- equiv _ _ [?i1;?i2;?i3] _ [?i1;?i2;?i3] _ => 
      change [?i1;?i2;?i3] with ([i1;i2] ++ [i3]);
      apply equiv_app with (EP1 (q -! Elength (R) =?= n)) 
    end.
    deadcode.
    eapply equiv_strengthen; [ | apply equiv_lossless_Modify with 
      (X1:={{R}}) (X2:=Vset.empty) (M1:={{y}}) (M2:={{y}}) ]; auto.
    intros k m1 m2 [_ H]; generalize H; 
    unfold EP1, E.eval_expr; simpl; unfold O.eval_op, is_true; simpl;
    rewrite andb_true_iff; tauto.
    apply depend_only_EP1.
    apply modify_correct with (refl1_info iE3) Vset.empty;vm_compute;trivial.
    apply modify_correct with (refl1_info iE3) Vset.empty;vm_compute;trivial.
    eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl; intros k1 m1 m2 H; split.
      apply req_mem_empty.
      apply leb_correct; apply nat_eqb_true in H.
      rewrite plus_comm, <-H; apply lt_le_S; apply minus_lt_compat_l.
      rewrite app_length; simpl length.
      generalize (length (m1 R)); intros; omega.
 Qed.
 *)
 

 Lemma G3_prefix_swaps_Or : equiv Meq E3 (O3 ++ G3_prefix) E2 (G3_prefix ++ O2) Meq.
 Proof.
 Admitted.
 (*
  unfold O3, O2, O1, G3_prefix.
  union_mod; [ trivial | ].
  swap; eqobs_tl.
  cp_test (x in_dom L);rewrite proj1_MR.
    (* case [ x in_dom L ] *)
    eqobs_in.
    (* case [ x not_in_dom L ] *)
      cp_test (Elength (L) <! q).
        (* case [ |L| < q ] *)
        alloc_l L L1; ep.
        match goal with |- equiv _ _ (?i1::?i2::?i3::?i4::?c) _ _ _ =>
          apply equiv_trans_eq_mem_l with trueR E3 ((i1::i2::i3::c)++[i4]) 
        end.
        rewrite proj1_MR; union_mod; [trivial | swap; eqobs_in ].
        eqobs_tl; ep; deadcode.
        match goal with |- equiv ?P _ _ ?E2 (?i1::(while ?e do ?C)::?T) ?Q => 
          change (i1::(while e do C)::T) with ([i1] ++ ([while e do C] ++ T));
            apply equiv_trans_eq_mem_r with trueR E2 ([i1]++([If e _then C ++ [while e do C] ]++ T)) 
        end.
        rewrite proj1_MR; apply equiv_eq_sem; intros k m.
        rewrite deno_app, deno_app; apply Mlet_eq_compat;[trivial | ].
        apply ford_eq_intro; clear m;intros m.
        rewrite deno_app, deno_app;apply Mlet_eq_compat;[|trivial].
        apply deno_while.
        ep. ep_eq_r (Elength (Nil (SwitchingSem.Sem.T.User BS_k))) 0%nat;[ trivial | ].
        ep_eq_r (Elength (L) <! q) true.
        intros k m1 m2 (H1, (_, H2));exact H2.
        rewrite proj1_MR.
        match goal with |- equiv ?P _ [?i1;?i2;?i3;?i4] _ [?i5;?i6;?i7;?i8;?i9] ?Q => 
          change [i1;i2;i3;i4] with ([i1;i2;i3]++([i4] ++ nil));
            change [i5;i6;i7;i8;i9] with ([i5;i6;i7] ++ ([i8] ++[i9])) 
        end.
        apply equiv_app with (req_mem_rel (Vset.add x (Vset.singleton L))
                          (fun k m1 m2 => E.eval_expr R m2 = E.eval_expr (y |::| R) m1)).
        set (P:= (fun (k : nat) (m1 m2 : Mem.t k) =>
          E.eval_expr R m2 = E.eval_expr (y |::| R) m1)).
        assert (Hdep : depend_only_rel P (fv_expr (y |::| R)) (fv_expr R)).
        red;intros;red.
        rewrite <- (depend_only_fv_expr _ H), <- (depend_only_fv_expr _ H0);trivial.
        assert (Hdep1 := @depend_only_req_mem_rel (Vset.add x (Vset.singleton L)) _ _ _ Hdep).
        assert (Hdec : decMR Meq) by auto.
   match type of Hdep1 with depend_only_rel ?p ?x1 ?x2 => set (P1 := p);set (X1 := x1); set (X2:= x2) end.
   set (c1 := [y <$- {0,1}^k; while y in_range L do [y <$- {0,1}^k]; R <- Nil _]).
   set (c2 := [R <- Nil _;yR <$- {0,1}^k;R <- yR |::| Nil _]).
   compute_assertion Heq1 res1 (alloc_c_out (refl1_info (empty_info E3 E2)) y yR c1 X1).
   refine (@alloc_c_out_equiv_l _ y yR _ E3 (refl1_info (empty_info E3 E2)) c1 res1 E2 c2 
                 X1 X2 P1 Hdec Hdep1 Heq1 _).
    ep;unfold P1, P.
    admit.
   apply equiv_app with (req_mem_rel (Vset.add x (Vset.singleton L))
                          (fun k m1 m2 => E.eval_expr R m2 = E.eval_expr (y |::| R) m1)).
   eapply equiv_weaken;[ | apply equiv_while].
    intros k m1 m2 (H1, _);trivial.
    intros k m1 m2 (H1, H2);generalize H2;clear H2.
(* Opaque leb.    *)
    simpl;unfold O.eval_op;simpl;intros Heq;rewrite Heq, (H1 _ L);trivial.
    simpl length. repeat rewrite <- plus_Snm_nSm;trivial.
   eqobsrel_tail;intros k m1 m2;simpl;unfold O.eval_op;simpl; intros (H1, (H2, _)).
   intros;repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff;[ | discriminate]));trivial.
   rewrite H2;trivial.
  ep_eq_r (R =?= Nil _) false.
  simpl;unfold O.eval_op;simpl;intros k m1 m2 (H1, H2);rewrite H2;trivial.
  apply equiv_weaken with
     (req_mem_rel (Vset.add x (Vset.singleton L)) 
         (fun k m1 m2 => E.eval_expr R m1 = E.eval_expr R m2 /\  E.eval_expr y m1 = E.eval_expr y m2)).
     intros k m1 m2 (H1, (H2, H3)).
     change (kreq_mem (Vset.add L (Vset.add y (Vset.add x (Vset.singleton R)))) m1 m2).
     intros t v;repeat rewrite VsetP.add_spec.
     intros [H | [ H | [ H | H ] ] ];
      try (apply Vset.singleton_complete in H);
      inversion H;simpl;trivial;(apply (H1 _ L)|| apply (H1 _ x));trivial.
   eqobsrel_tail;unfold EP1;simpl;unfold O.eval_op;simpl;intros k m1 m2 (H1, H2).
   repeat (rewrite Mem.get_upd_same || (rewrite Mem.get_upd_diff;[ | discriminate])).
   rewrite H2;auto.
  red;red;trivial.
  red;red;trivial.

    (* case [ x not_in_dom L ] *)
  match goal with |- equiv _ _ [?i1;?i2;?i3;?i4] _ _ _ =>
    change [i1;i2;i3;i4] with ([i1;i2;i3]++[i4]);
    apply equiv_trans_eq_mem_l with (~- EP1 (Elength (L) <! q)) E3 ([i1;i2;i3] ++ nil) end.
  union_mod;[rewrite proj1_MR;trivial | ].
  apply equiv_app with (req_mem_rel (Vset.add y (Vset.add L (Vset.add R (Vset.singleton yR)))) 
                         (~-EP1 ((Elength (L) +! Elength (R)) <! q))).
    Opaque leb. 
    eqobsrel_tail;unfold EP1, notR;simpl;unfold O.eval_op;simpl;intros k m1 m2 (H1, H2).
   apply not_is_true_false in H2;apply leb_complete_conv in H2.
   intros v _ Hleb; apply leb_complete in Hleb.
   rewrite <-plus_n_O in Hleb; generalize H2 Hleb; 
   match goal with |- (lt _ (?x + _) ) -> _ -> _ => generalize x; intros end;
   omega.
  ep_eq_l ((Elength (L) +! Elength (R)) <! q) false.
  unfold notR, EP1;intros k m1 m2 (_, H);apply not_is_true_false in H;trivial.
  eqobs_in.
  match goal with |- equiv _ _ _ _ [?i1;?i2;?i3;?i4] _ =>
    change [i1;i2;i3;i4] with (([i1]++[i2])++[i3;i4]);
    apply equiv_trans_eq_mem_r with (~- EP1 (Elength (L) <! q)) E2 (([i1] ++ nil) ++[i3;i4]) end.
  union_mod;[rewrite proj1_MR;trivial | ].
  apply equiv_app with (kreq_mem (Vset.add x (Vset.add y (Vset.add L (Vset.add R (Vset.singleton yR)))))).
  apply equiv_app with (req_mem_rel (Vset.add x (Vset.add y (Vset.add L (Vset.add R (Vset.singleton yR))))) 
                         (~-EP1 ((Elength (L) +! Elength (R)) <! q))).
   eqobsrel_tail;unfold EP1, notR;simpl;unfold O.eval_op;simpl;intros k m1 m2 (H1, H2).
   apply not_is_true_false in H2;apply leb_complete_conv in H2.
   intros Hleb;apply leb_complete in Hleb. 
   rewrite <-plus_n_O in Hleb; generalize H2 Hleb; 
   match goal with |- (lt _ (?x + _) ) -> _ -> _ => generalize x; intros end;
   omega.
   ep_eq_l ((Elength (L) +! Elength (R)) <! q) false.
   unfold notR, EP1;intros k m1 m2 (_, H);apply not_is_true_false in H;trivial.
   eqobs_in.
   eqobs_in.
  ep;swap;eqobs_in.
  intros k m1 m2 (H1, (H2, H3));trivial.
  intros k m1 m2 (H1, (H2, H3));trivial.
 *)

 Definition XG3_prefix : Vset.t := 
  Eval vm_compute in get_option (modify (refl1_info (empty_info E3 E3)) Vset.empty G3_prefix).

 Lemma G3_prefix_Modify : forall E, Modify E XG3_prefix G3_prefix.
 Proof.
  intros E;apply modify_correct with (refl1_info (empty_info E E)) Vset.empty.
  vm_compute;trivial.
 Qed.

 Definition IG3_prefix := Vset.singleton L.

 Lemma EqObs_G3_prefix : EqObs (Vset.union IG3_prefix XG3_prefix) E3 G3_prefix E2 G3_prefix XG3_prefix.
 Proof. eqobs_in. Qed.

 Lemma IX'_glob :  forall x : VarP.Edec.t, Vset.mem x (Vset.union IG3_prefix XG3_prefix) -> Var.is_global x.
 Proof.
  apply Vset.forallb_correct.
  intros x y Heq;rewrite Heq;trivial.
  vm_compute;trivial.
 Qed.

 Definition sw_i' := @add_sw_info_Adv
  G3_prefix XG3_prefix IG3_prefix E3 E2 (G3_prefix_Modify _) (G3_prefix_Modify _) EqObs_G3_prefix IX'_glob
  (@add_sw_info G3_prefix XG3_prefix IG3_prefix E3 E2 (G3_prefix_Modify _) (G3_prefix_Modify _) EqObs_G3_prefix IX'_glob
    (fun _ _ => None) _ F G3_prefix_swaps_Or) _ A _ _ _ _ (EqAD _ _) (A_wf_E _).

 Lemma G3_prefix_swaps: equiv 
   Meq 
   E3 ([b <c- A with{}] ++ G3_prefix) 
   E2 (G3_prefix ++ [b <c- A with{}]) 
   Meq.
 Proof.
  apply check_swap_c_correct with XG3_prefix IG3_prefix sw_i'.
    apply G3_prefix_Modify. 
    apply G3_prefix_Modify. 
    apply EqObs_G3_prefix. 
    vm_compute; trivial.
 Qed.


 Lemma EqObs_G3_G2: equiv Meq E3 G3 E2 G2 (kreq_mem {{L,b}}).
 Proof.
  apply equiv_trans with Meq (kreq_mem {{L,b}}) (kreq_mem {{L,b}}) E3 (G3 ++ G3_prefix);
    [ auto | red; trivial | apply req_mem_trans | | ].
    rewrite (app_nil_end G3) at 1; apply equiv_app with (kreq_mem {{L,b}}); [ eqobs_in iE3 | ].
      deadcode; union_mod.
      apply equiv_strengthen with (kreq_mem Vset.empty).
        intros k1 m1 m2 H1;apply req_mem_weaken with (2:= H1); vm_compute; trivial.
      apply equiv_lossless_Modify with Vset.empty Vset.empty Vset.empty {{yR, R}}; auto.
        apply lossless_nil.
        apply lossless_G3_prefix.
        apply modify_correct with (refl1_info iE3) Vset.empty;vm_compute;trivial.
        apply modify_correct with (refl1_info iE3) Vset.empty;vm_compute;trivial.
      change (G3 ++ G3_prefix) with (([L<-Nil _] ++ [b <c- A with {}])++G3_prefix); rewrite app_ass.
      apply equiv_trans_eq_mem_l with trueR E2 ([L<-Nil _] ++ (G3_prefix ++ [b <c- A with {}])).
        rewrite proj1_MR;apply equiv_app with Meq.
          union_mod;[trivial | eqobs_in].
          apply G3_prefix_swaps.
        eqobs_tl iE2; ep.
        ep_eq_l (Elength (Nil (SwitchingSem.Sem.T.Pair (SwitchingSem.Sem.T.User BS_k)
            (SwitchingSem.Sem.T.User BS_k)))) 0%nat;trivial.
        deadcode;swap; eqobs_tl. 
        admit.
        red; red; trivial.
 Qed.




End ADVERSARY.
