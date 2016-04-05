(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * OAEP.v: Exact security of the OAEP padding scheme *)

Set Implicit Arguments.

Require Export OAEPsem.


Module Make (ENT:OAEP_ENTRIES).

 Module OAEPS := OAEPsem.Make ENT.
 Export OAEPS.

 Notation bsp := (T.User BS_p).
 Notation bskmp := (T.User BS_kmp).
 Notation bsk := (T.User BS_k).

 Opaque BVxor.
 Opaque bs_support.
 Opaque Vextend.


 Section OPTIMISTIC_SAMPLING.

  Variables GR' S' Mb : Var.var bskmp.

  Hypothesis GR'_S': Var.mkV GR' <> S'.
  Hypothesis S'_Mb : Var.mkV S' <> Mb.
  Hypothesis GR'_Mb : Var.mkV GR' <> Mb.

  Lemma optim_sampl_kmp : forall E, 
   equiv Meq 
   E [GR' <$- {0,1}^k-p; S' <- GR' |x| Mb] 
   E [S' <$- {0,1}^k-p; GR' <- S' |x| Mb] 
   Meq.
  Proof.
   intros E; apply equiv_cons with
    (eeq_mem (Vset.add GR' (Vset.singleton S')) /-\ 
     fun k m1 m2 => m1 GR' = BVxor _ (m2 S') (m2 Mb)).
   
   eapply equiv_strengthen;
    [ | apply equiv_random_permut with 
     (f:=fun k (m1 m2:Mem.t k) (v:T.interp k bskmp) => BVxor _ v (m2 Mb))].
   unfold Meq, andR; split.
   unfold permut_support; simpl.
   exact (PermutP_bs_support_xor (m2 Mb)).
   rewrite H; intros; split.
   intros tx x Hn.
   repeat (rewrite Mem.get_upd_diff;[ trivial| intro Heq; apply Hn; rewrite Heq; auto with set]).
   repeat rewrite Mem.get_upd_same.
   rewrite Mem.get_upd_diff; trivial.

   eapply equiv_strengthen;[ | apply equiv_assign].
   unfold upd_para, Meq, andR; intros k m1 m2 (H1, H2).
   simpl; unfold O.eval_op; simpl.
   apply Mem.eq_leibniz; intros (tz,z).
   destruct (VsetP.mem_dec z (Vset.add GR' (Vset.singleton S'))).
   rewrite VsetP.add_spec in i; destruct i.
   inversion H; simpl.
   rewrite Mem.get_upd_same, Mem.get_upd_diff; auto.
   apply Vset.singleton_complete in H; inversion H; simpl.
   rewrite Mem.get_upd_same, Mem.get_upd_diff; trivial.
   rewrite H2, (H1 _ Mb).
   refine (BVxor_bij _ _).
   rewrite VsetP.add_spec; intros [ Hin | Hin];[auto | ].
   apply Vset.singleton_complete in Hin; apply S'_Mb; trivial.
   rewrite Mem.get_upd_diff, Mem.get_upd_diff.
   apply H1; trivial.
   intro Heq; apply n; rewrite Heq; auto with set.
   intro Heq; apply n; rewrite Heq; auto with set.
  Qed.
 
  Variables R' T' HS': Var.var bsp.

  Hypothesis R'_T' : Var.mkV R' <> T'.
  Hypothesis R'_HS' : Var.mkV R' <> HS'.
  Hypothesis T'_HS' : Var.mkV T' <> HS'.

  Lemma optim_sampl_p : forall E, 
   equiv Meq 
   E [R' <$- {0,1}^p; T' <- HS' |x| R'] 
   E [T' <$- {0,1}^p; R' <- HS' |x| T'] 
   Meq.
  Proof.
   intros E; apply equiv_cons with
    (eeq_mem (Vset.add R' (Vset.singleton T')) /-\ 
     fun k m1 m2 => m1 R' = BVxor _ (m2 HS') (m2 T')).

   eapply equiv_strengthen;
    [ | apply equiv_random_permut with 
     (f:=fun k (m1 m2:Mem.t k) (v:T.interp k bsp) => BVxor _ (m2 HS') v)].
   unfold Meq, andR; split.
   unfold permut_support; simpl.
   apply PermutP_weaken with (fun v1 v2 : UT.interp k BS_p => v1 = BVxor (k_p k) v2 (m2 HS')).
   intros; subst; refine (BVxor_comm _ _).
   exact (PermutP_bs_support_xor (m2 HS')).
   rewrite H; intros; split.
   intros tx x Hn.
   repeat (rewrite Mem.get_upd_diff;[ trivial| intro Heq; apply Hn; rewrite Heq; auto with set]).
   repeat rewrite Mem.get_upd_same.
   rewrite Mem.get_upd_diff; trivial.

   eapply equiv_strengthen;[ | apply equiv_assign].
   unfold upd_para, Meq, andR; intros k m1 m2 (H1, H2).
   simpl; unfold O.eval_op; simpl.
   apply Mem.eq_leibniz; intros (tz,z).
   destruct (VsetP.mem_dec z (Vset.add R' (Vset.singleton T'))).
   rewrite VsetP.add_spec in i; destruct i.
   inversion H; simpl.
   rewrite Mem.get_upd_same, Mem.get_upd_diff; auto.
   apply Vset.singleton_complete in H; inversion H; simpl.
   rewrite Mem.get_upd_same, Mem.get_upd_diff; trivial.
   rewrite H2, (H1 _ HS').
   rewrite <- BVxor_assoc, BVxor_nilpotent, BVxor_0_l; trivial.
   rewrite VsetP.add_spec; intros [ Hin | Hin];[auto | ].
   apply Vset.singleton_complete in Hin; apply T'_HS'; trivial.
   repeat rewrite Mem.get_upd_diff.
   apply H1; trivial.
   intro Heq; apply n; rewrite Heq; auto with set.
   intro Heq; apply n; rewrite Heq; auto with set.
  Qed.

  Lemma equiv_random_concat : forall E E' Y' S' T',
   equiv trueR 
   E [Y' <$- {0,1}^k] 
   E' [S' <$- {0,1}^k-p; T' <$- {0,1}^p]
   (fun (k : nat) (m1 m2 : Mem.t k) => m1 Y' = E.eval_expr (S' @ T') m2).
  Proof.
   red; intros.
   exists (fun m1 m2 =>
    Mlet (([[ [S'0 <$- {0,1}^k-p; T'0 <$- {0,1}^p] ]]) E' m2)
    (fun m2' => Munit (m1 {!Y' <-- E.eval_expr (S'0 @ T'0) m2'!}, m2'))).
   intros m1 m2 _; constructor; intros.
   rewrite deno_random_elim.
   unfold E.eval_support, US.eval, T.default, UT.default, UT.length.
   rewrite (bs_support_sum (S (k_kmp k)) (k_p k)).
   rewrite Mlet_simpl, deno_cons_elim, Mlet_simpl, deno_random_elim.
   apply mu_stable_eq; refine (@ford_eq_intro _ _ _ _ _); intros v1.
   rewrite deno_random_elim; apply mu_stable_eq; refine (@ford_eq_intro _ _ _ _ _); intros v2.
   simpl; unfold O.eval_op; simpl.
   repeat (rewrite Mem.get_upd_same || rewrite Mem.get_upd_diff); trivial.
   intro; discriminate.
   rewrite Mlet_simpl; apply mu_stable_eq; refine (@ford_eq_intro _ _ _ _ _); trivial.
   apply range_Mlet with (P:= fun _ => True).
   apply range_True.
   intros m2' _ f0 Hf0; simpl; apply Hf0; red; simpl; rewrite Mem.get_upd_same; trivial.
  Qed.

  Lemma sampl_app : forall E E' Y' S' T',
   equiv trueR 
   E  [Y' <$- {0,1}^k] 
   E' [S' <$- {0,1}^k-p; T' <$- {0,1}^p; Y' <- apply_f S' @ T']
   (kreq_mem (Vset.singleton Y')).
  Proof.
   intros; equiv_trans E [Y' <$- {0,1}^k; Y' <- apply_f Y'].

   apply equiv_cons with (Q:=fun k (m1 m2:Mem.t k) => f_inv (m1 Y') = m2 Y').
   eapply equiv_strengthen; [ | apply equiv_random_permut with 
    (f:=fun k (m1 m2:Mem.t k) (v:T.interp k bsk) => f v)].
   unfold andR; intros k m1 m2 _.
   split;[red | ]; intros.
   apply PermutP_NoDup with (f_inv := @f_inv k); intros.
   apply (bs_support_NoDup (UT.length k BS_k)).
   apply (bs_support_NoDup (UT.length k BS_k)).
   apply (@f_inv_spec k x).
   apply (@f_spec k x).
   refine (@full_support (UT.length k BS_k) _).
   refine (@full_support (UT.length k BS_k) _).
   repeat rewrite Mem.get_upd_same; apply f_spec.
   eapply equiv_strengthen; [ | apply equiv_assign_r ].
   unfold upd2; intros; simpl; unfold O.eval_op; simpl.
   rewrite <- H, f_inv_spec; red; red; intros.
   apply Vset.singleton_complete in H0; inversion H0; simpl.
   rewrite Mem.get_upd_same; trivial.

   change (equiv trueR E ([Y' <$- {0,1}^k]++[Y' <- apply_f Y']) 
    E' ([S'0 <$- {0,1}^k-p; T'0 <$- {0,1}^p] ++ [Y' <- apply_f S'0 @ T'0])
    (kreq_mem (Vset.singleton Y'))).
   apply equiv_app with
    (fun k (m1 m2:Mem.t k) => m1 Y' = E.eval_expr (S'0 @ T'0) m2).
   apply equiv_random_concat.

   eapply equiv_strengthen; [ | apply equiv_assign ].     
   unfold upd_para; intros k m1 m2.
   simpl; unfold O.eval_op; simpl; intros.
   rewrite H; red; red; intros.
   apply Vset.singleton_complete in H0; inversion H0; simpl.
   repeat rewrite Mem.get_upd_same; trivial.
  Qed.

 End OPTIMISTIC_SAMPLING.
 

 (** ** Global Variables *)

 (** *** Global variables shared between the adversary, the oracles and the game *)
 Definition Gcomm := Vset.empty.

 (** Global variable shared between the adversaries [A] and [A'] *)
 Notation g_a := (Var.Gvar T.Nat 1).

 Definition Gadv := Vset.singleton g_a.

 (** Global variables not visible by the adversary *) 
 Notation R' := (Var.Gvar bsp 1). 
 Notation GR' := (Var.Gvar bskmp 2).
 Notation LH := (Var.Gvar (T.List (T.Pair bskmp bsp)) 3).
 Notation S' := (Var.Gvar bskmp 4).
 Notation HS' := (Var.Gvar bsp 5).
 Notation LG := (Var.Gvar (T.List (T.Pair bsp bskmp)) 6).

 Notation bad := (Var.Gvar T.Bool 7).
 Notation bad1 := (Var.Gvar T.Bool 8).
 Notation bad2 := (Var.Gvar T.Bool 9).
 Notation bad3 := (Var.Gvar T.Bool 20).
 Notation bad4 := (Var.Gvar T.Bool 21).
 Notation Y' := (Var.Gvar bsk 10).
 Notation T' := (Var.Gvar bsp 11).
 Notation ST' := (Var.Gvar bsk 22). 


 (** ** Local Variables *)
 Notation M := (Var.Lvar (T.Pair bskmp bskmp) 1).
 Notation Mb := (Var.Lvar bskmp 2).
 Notation b  := (Var.Lvar T.Bool 7).
 Notation b' := (Var.Lvar T.Bool 8).

 (** G oracle *)
 Notation G := (Proc.mkP 1 (bsp :: nil) bskmp).

 (* Local variables *)
 Notation R := (Var.Lvar bsp 3). 
 Notation rG := (Var.Lvar bskmp 6).

 Definition G_params : var_decl (Proc.targs G) := dcons _ R (dnil _).

 Definition G_body0 :=
  [ 
   If !(R in_dom LG) 
   then [ rG <$- {0,1}^k-p; LG <- ( R | rG) |::| LG ]
   else [ rG <- LG[{R}] ]
  ].
 
 Definition G_res := rG.

 (** H oracle *)
 Notation H := (Proc.mkP 2 (bskmp :: nil) bsp).

 (* Local variables *)
 Notation S := (Var.Lvar bskmp 4).
 Notation rH := (Var.Lvar bsp 5). 

 Definition H_params : var_decl (Proc.targs H) := dcons _ S (dnil _).

 Definition H_body0 :=
  [ 
   If !(S in_dom LH) 
   then [ rH <$- {0,1}^p; LH <- ( S | rH) |::| LH]
   else [rH <- LH[{S}] ]
  ].

 Definition H_res := rH.
 
 (** Encryption algorithm *)
 Notation Enc := (Proc.mkP 3 (bskmp :: nil) bsk).

 (* Local variables *)
 Notation Me := (Var.Lvar bskmp 9).
 Notation Re := (Var.Lvar bsp 10).
 Notation Se := (Var.Lvar bskmp 11).
 Notation Te := (Var.Lvar bsp 12).
 Notation He := (Var.Lvar bsp 13).
 Notation Ge := (Var.Lvar bskmp 14).
 Notation Ye := (Var.Lvar bsk 15).

 Definition Enc_params : var_decl (Proc.targs Enc) := dcons _ Me (dnil _).

 Definition Enc_body :=
  [ 
   Re <$- {0,1}^p;
   Ge <c- G with {Re};
   Se <- Ge |x| Me;
    He <c- H with {Se};
    Te <- He |x| Re;
     Ye <- apply_f (Se @ Te)
  ].

 Definition Enc_res := Ye.

 (* Inverter (its body is given later) *) 
 Notation Inverter := (Proc.mkP 10 (bsk :: nil) bsk).

 Definition I_params : var_decl (Proc.targs Inverter) := dcons _ Ye (dnil _).


 Section ONE_WAYNESS.

  Variables x y : Var.var bsk.
  
  Definition G_f :=
   [ 
    y <$- {0,1}^k;
    x <c- Inverter with {y}
   ].

  Definition oneway := forall (m:forall k, Mem.t k) E, 
   x <> y ->
   Var.is_local x ->
   Var.is_local y ->
   PPT_proc E Inverter ->
   lossless E (proc_body E Inverter) ->
   negligible (fun k => Pr E G_f (m k) (EP k (x =?= apply_finv y))).
 
 End ONE_WAYNESS.

 
 Section ADVERSARY_AND_PROOF.

  (** [f] is a one-way permutation *)
  Hypothesis f_oneway : forall x y, oneway x y.

  (** Specification of the adversary *)
  Variable env_adv : env.

  Notation A  := (Proc.mkP 4 nil (T.Pair bskmp bskmp)).

  Definition A_params : var_decl (Proc.targs A) := dnil _.
  Variable A_body : cmd.
  Variable A_res : E.expr (T.Pair bskmp bskmp).

  Notation A' := (Proc.mkP 5 (bsk :: nil) T.Bool).
  Notation alpha := (Var.Lvar bsk 16).

  Definition A'_params : var_decl (Proc.targs A') := dcons _ alpha (dnil _).
  Variable A'_body : cmd.
  Variable A'_res : E.expr T.Bool.

  Definition mkEnv H_body G_body := 
   (add_decl
    (add_decl
     (add_decl 
      (add_decl
       (add_decl 
        env_adv 
        H H_params (refl_equal true) H_body H_res)
       G G_params (refl_equal true) G_body G_res)
      Enc Enc_params (refl_equal true) Enc_body Enc_res)
     A A_params (refl_equal true) A_body A_res)
    A' A'_params (refl_equal true) A'_body A'_res).

  (** Initial game *)
  Definition Game0 :=
   [
     LG <- Nil _;
     LH <- Nil _;
     M <c- A with {};
     b <$- {0,1};
     If b then [ Mb <- Efst M ] else [ Mb <- Esnd M ];
     Y' <c- Enc with {Mb};
     b' <c- A' with {Y'}
   ].

  Definition E0 := mkEnv H_body0 G_body0.

  (** In the initial environment game, the maximun number of distinct queries
     the adversary makes to the G oracle is less than [qG_poly k], 
     independently of the value of [Y'] *)
  Definition Game12_ := 
   [
    LG <- Nil _;
    LH <- Nil _;
    M <c- A with{};
    b' <c- A' with {Y'}
   ].

  Hypothesis range_G_query : forall k (m:Mem.t k),
   range (fun (m':Mem.t k) => List.length (m' LG)  <= peval qG_poly k)%nat 
   ([[Game12_]] E0 m).

  (** Oracles *)
  Definition PrOrcl := PrSet.add (BProc.mkP H) (PrSet.singleton (BProc.mkP G)).

  (** Private procedures, not accessible to the adversary *)
  Definition PrPriv := 
   PrSet.add (BProc.mkP Inverter) (PrSet.singleton (BProc.mkP Enc)).

  (** The adversary is well-formed in [E0], i.e. it only reads or writes 
     variables it has access to, and only calls oracles and its own procedures. *)
  Hypothesis A_wf : WFAdv PrOrcl PrPriv Gadv Gcomm E0 A.
  Hypothesis A'_wf : WFAdv PrOrcl PrPriv Gadv Gcomm E0 A'.

  (** The adversary runs in PPT as long as the H and G oracles do so and
      are defined as in E0 *)
  Hypothesis A_PPT : forall E,
    Eq_adv_decl PrOrcl PrPriv E0 E ->
    (forall O, PrSet.mem O PrOrcl -> PPT_proc E (BProc.p_name O)) ->
    PPT_proc E A.

  Hypothesis A'_PPT : forall E,
    Eq_adv_decl PrOrcl PrPriv E0 E ->
    (forall O, PrSet.mem O PrOrcl -> PPT_proc E (BProc.p_name O)) ->
    PPT_proc E A'.

  Hypothesis negligible_qG_2p :
   negligible (fun k => peval qG_poly k/2^(k_p k)).
 
  (** The adversary is lossless as long as the G and H oracles are so *)
  Hypothesis A_lossless : forall Hbody Gbody,
    (forall O, PrSet.mem O PrOrcl -> 
     lossless (mkEnv Hbody Gbody)
     (proc_body (mkEnv Hbody Gbody) (BProc.p_name O))) -> 
    lossless (mkEnv Hbody Gbody) A_body.

  Hypothesis A'_lossless : forall Hbody Gbody,
   (forall O, PrSet.mem O PrOrcl -> 
    lossless (mkEnv Hbody Gbody)
    (proc_body (mkEnv Hbody Gbody) (BProc.p_name O))) -> 
   lossless (mkEnv Hbody Gbody) A'_body.
  
  Lemma EqAD : forall H_body1 G_body1 H_body2 G_body2, 
   Eq_adv_decl PrOrcl PrPriv (mkEnv H_body1 G_body1) (mkEnv H_body2 G_body2).
  Proof.
   unfold Eq_adv_decl, mkEnv; intros.
   unfold proc_params, proc_body, proc_res.
   generalize (BProc.eqb_spec (BProc.mkP A') (BProc.mkP f0)).
   destruct (BProc.eqb (BProc.mkP A') (BProc.mkP f0)); intros.
   inversion H1; simpl; auto.
   generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f0)).
   destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f0)); intros.
   inversion H2; simpl; auto.
   repeat rewrite add_decl_other_mk; try tauto;
    intros Heq; 
     (apply H; rewrite <- Heq; vm_compute; reflexivity)
     || (apply H0; rewrite <- Heq; vm_compute; reflexivity).
  Qed.
  
  Lemma EqOP : forall H_body1 G_body1 H_body2 G_body2, 
   Eq_orcl_params PrOrcl (mkEnv H_body1 G_body1) (mkEnv H_body2 G_body2).
  Proof.
   unfold Eq_orcl_params, mkEnv; intros.
   unfold PrOrcl in H.
   rewrite PrSetP.add_spec in H; destruct H.
   inversion H; simpl.
   vm_compute; trivial.
   apply PrSet.singleton_complete in H; inversion H; simpl.
   vm_compute; trivial.
  Qed.

  (** The adversary is well-formed in any environment constructred with [mkEnv].
     This follows from the adversary being well-formed in [E0] *)
  Lemma A_wf_E : forall H_body G_body,
   WFAdv PrOrcl PrPriv Gadv Gcomm (mkEnv H_body G_body) A.
  Proof.
   intros; apply WFAdv_trans with (5:=A_wf).
   unfold E0; apply EqOP.
   unfold E0; apply EqAD.
   vm_compute; intro; discriminate.
   vm_compute; intro; discriminate.
  Qed. 

  Lemma A'_wf_E : forall H_body G_body,
   WFAdv PrOrcl PrPriv Gadv Gcomm (mkEnv H_body G_body) A'.
  Proof.
   intros; apply WFAdv_trans with (5:=A'_wf).
   unfold E0; apply EqOP.
   unfold E0; apply EqAD.
   vm_compute; intro; discriminate.
   vm_compute; intro; discriminate.
  Qed. 

  (* Function to build context info *)
  Definition mkCi Hbody Hbody' Gbody Gbody' C1 C2 nR nW :=
   let E := mkEnv Hbody Gbody in
   let E' := mkEnv Hbody' Gbody' in
   let i0 := empty_context_info E E' C1 C2 nR nW in
   let iH := add_context_info E E' C1 C2 nR nW i0 _ H in
   let iG := add_context_info E E' C1 C2 nR nW iH _ G in
   let iA := add_adv_context_info E E' C1 C2 nR nW iG 
               PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _) _ A (A_wf_E _ _) in
    add_adv_context_info E E' C1 C2 nR nW iA
      PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _) _ A' (A'_wf_E _ _).

  (* Functions to build upto_bad info *)
  Definition i_upto bad Hbody Hbody' Gbody Gbody' :=
    let E := mkEnv Hbody Gbody in
    let E' := mkEnv Hbody' Gbody' in
    let i0 := empty_upto_info bad E E' in
    let iH := add_upto_info i0 H in
    let iG := add_upto_info iH G in
    let iA := add_adv_upto_info iG (EqAD _ _ _ _) (EqOP _ _ _ _) (A_wf_E _ _) in
    add_adv_upto_info iA (EqAD _ _ _ _) (EqOP _ _ _ _) (A'_wf_E _ _).

  (* Functions to build eq_inv_info *)
  Definition i_refl Hbody Hbody' Hr Hr' Gbody Gbody' Gr Gr':=
    let E := mkEnv Hbody Gbody in
    let E' := mkEnv Hbody' Gbody' in
    let A'loss := @A'_lossless Hbody Gbody in
    let A'loss' := @A'_lossless Hbody' Gbody' in
    let Aloss := @A_lossless Hbody Gbody in
    let Aloss' := @A_lossless Hbody' Gbody' in
    let piH := add_refl_info_rm H Hr Hr' (empty_info E E') in
    let piG := add_refl_info_rm G Gr Gr' piH in
    let piEnc := add_refl_info Enc piG in 
    let piA := add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _) Aloss Aloss' piEnc in
    add_adv_info_lossless (EqAD _ _ _ _) (A'_wf_E _ _) A'loss A'loss' piA.

  Definition iEiEi Hbody Gbody := 
   i_refl Hbody Hbody Vset.empty Vset.empty Gbody Gbody Vset.empty Vset.empty.

  Definition iEinv_GG' Hbody Gbody Gbody' inv 
   (ie:eq_inv_info inv (mkEnv Hbody Gbody) (mkEnv Hbody Gbody')) 
   R1 R2 I O  
   (Gbody_Gbody': 
    EqObsInv inv I (mkEnv Hbody Gbody) Gbody (mkEnv Hbody Gbody') Gbody' O):=
   let E := mkEnv Hbody Gbody in
   let E' := mkEnv Hbody Gbody' in 
   let A'loss := @A'_lossless Hbody Gbody in
   let A'loss' := @A'_lossless Hbody Gbody' in
   let Aloss := @A_lossless Hbody Gbody in
   let Aloss' := @A_lossless Hbody Gbody' in
   let piH := add_refl_info H ie in
   let piG := add_info G R1 R2 piH Gbody_Gbody' in
   let piEnc := add_refl_info Enc piG in 
   let piA := add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _) Aloss Aloss' piEnc in
   add_adv_info_lossless (EqAD _ _ _ _) (A'_wf_E _ _) A'loss A'loss' piA.

  Definition iE_GG' Hbody Gbody Gbody' I O  
   (Gbody_Gbody' : 
    EqObsInv trueR I (mkEnv Hbody Gbody) Gbody (mkEnv Hbody Gbody') Gbody' O):=
   iEinv_GG' (empty_info (mkEnv Hbody Gbody) (mkEnv Hbody Gbody'))
   Vset.empty Vset.empty Gbody_Gbody'.

  Definition iEinv_HH' Hbody Hbody' Gbody inv 
   (ie:eq_inv_info inv (mkEnv Hbody Gbody) (mkEnv Hbody' Gbody)) 
   R1 R2 I O  
   (Hbody_Hbody': 
    EqObsInv inv I (mkEnv Hbody Gbody) Hbody (mkEnv Hbody' Gbody) Hbody' O):=
   let E := mkEnv Hbody Gbody in
   let E' := mkEnv Hbody' Gbody in 
   let A'loss := @A'_lossless Hbody Gbody in
   let A'loss' := @A'_lossless Hbody' Gbody in
   let Aloss := @A_lossless Hbody Gbody in
   let Aloss' := @A_lossless Hbody' Gbody in
   let piH := add_info H R1 R2 ie Hbody_Hbody' in
   let piG := add_refl_info G piH in
   let piEnc := add_refl_info Enc piG in 
   let piA := add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _) Aloss Aloss' piEnc in
   add_adv_info_lossless (EqAD _ _ _ _) (A'_wf_E _ _) A'loss A'loss' piA.

  Definition iE_HH' Hbody Hbody' Gbody I O  
   (Hbody_Hbody' : 
    EqObsInv trueR I (mkEnv Hbody Gbody) Hbody (mkEnv Hbody' Gbody) Hbody' O):=
   iEinv_HH' (empty_info (mkEnv Hbody Gbody) (mkEnv Hbody' Gbody)) 
     Vset.empty Vset.empty Hbody_Hbody'.

  Definition iEinv Hbody Hbody' Gbody Gbody' inv
   (ie:eq_inv_info inv (mkEnv Hbody Gbody) (mkEnv Hbody' Gbody')) 
   HI HO   
   (Hbody_Hbody': 
    EqObsInv inv HI (mkEnv Hbody Gbody) Hbody (mkEnv Hbody' Gbody') Hbody' HO)
   GI GO   
    (Gbody_Gbody': 
       EqObsInv inv GI (mkEnv Hbody Gbody) Gbody (mkEnv Hbody' Gbody') Gbody' GO) :=
   let A'loss := @A'_lossless Hbody Gbody in
   let A'loss' := @A'_lossless Hbody' Gbody' in
   let Aloss := @A_lossless Hbody Gbody in
   let Aloss' := @A_lossless Hbody' Gbody' in
   let piH := add_info H Vset.empty Vset.empty ie Hbody_Hbody' in
   let piG := add_info G Vset.empty Vset.empty piH Gbody_Gbody' in
   let piEnc := add_refl_info Enc piG in 
   let piA := add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _) Aloss Aloss' piEnc in
   add_adv_info_lossless (EqAD _ _ _ _) (A'_wf_E _ _) A'loss A'loss' piA.

  (***********************************************)
  (** First Transition:  E0, Game0 -> E1, Game1  *) 
  (*  + Inlining of Enc in the main              *)
  (*  + Coin fixing of R' in G                   *)
  (***********************************************)

  Definition Game1 :=  
   [
    LG <- Nil _;
    LH <- Nil _;
    R' <$- {0,1}^p;
    GR' <$- {0,1}^k-p;
    M <c- A with {};
    b <$- {0,1};
    If b then [Mb <- Efst M] else [Mb <- Esnd M];
    Ge <c- G with {R'};
    S' <- Ge |x| Mb;
    He <c- H with {S'};
    T' <- He |x| R';
    Y' <- apply_f (S' @ T');
    b' <c- A' with {Y'}
   ].

  Definition G_body1 :=
   [
    If !(R in_dom LG) 
    then [ 
         If R =?= R' then [rG <- GR'] else [rG <$- {0,1}^k-p];
         LG <- (R | rG) |::| LG
         ] 
    else [ rG <- LG[{R}] ]
   ].
  
  Definition E1 := mkEnv H_body0 G_body1.

  Definition G_body0' := 
   [ If !(R' in_dom LG) then (GR'<$- {0,1}^k-p) :: G_body1 else G_body0].
  
  Definition G_body1' :=
   [ If !(R' in_dom LG) then G_body1 else G_body0].
  
  Definition E0' := mkEnv H_body0 G_body0'.
  Definition E1' := mkEnv H_body0 G_body1'.
  
  Lemma G_body0_G_body0' :
   EqObsInv trueR (Vset.add R (Vset.add R' (Vset.singleton LG)))
   E0 G_body0 
   E0' G_body0' 
   (Vset.add rG (Vset.add R (Vset.add R' (Vset.singleton LG)))). 
  Proof.
   unfold EqObsInv; fold_eqobs_tac.
   unfold G_body0', G_body0, G_body1.
   cp_test (R' in_dom LG).
   eqobs_in.
   cp_test (R in_dom LG).
   deadcode; eqobs_in.
   cp_test (R=?=R').
   alloc_r GR' rG.
   ep; deadcode; eqobs_in.
   deadcode; eqobs_in.
  Qed.

  Lemma G_body1'_G_body1 :
   EqObsInv trueR (Vset.add GR' (Vset.add R (Vset.add R' (Vset.singleton LG))))
   E1' G_body1' 
   E1 G_body1
   (Vset.add rG (Vset.add GR' (Vset.add R (Vset.add R' (Vset.singleton LG))))).
  Proof.
   unfold EqObsInv; fold_eqobs_tac.
   unfold G_body1', G_body0, G_body1.
   cp_test (R' in_dom LG).
   cp_test (R in_dom LG).
   eqobs_in.
   cp_test (R =?= R').
   apply equiv_False.
   unfold req_mem_rel, andR, notR,EP1,EP2; simpl; unfold O.eval_op; simpl.
   intros k m1 m2 (((H1, (H5, H7)), (H6, H4)), (H2, H3)).
   assert (W:= UT.i_eqb_spec (m1 R) (m1 R')); rewrite H2 in W.   
   apply H6; rewrite W; trivial.
   eqobs_in.
   eqobs_in.
  Qed.

  Definition iE0E0 : eq_inv_info trueR E0 E0 := iEiEi H_body0 G_body0.
  Definition iE0E0' : eq_inv_info trueR E0 E0' := iE_GG' G_body0_G_body0'.
  Definition iE1'E1 :eq_inv_info trueR E1' E1 := iE_GG' G_body1'_G_body1. 

  
  Lemma EqObs_Game0_Game1 : 
   EqObs Gadv E0 Game0 E1 Game1 (fv_expr (b =?= b')).
  Proof.
  (* Step 1 : inlining of Enc + code motion *)
   apply EqObs_trans with E0 Game1.
   sinline iE0E0 Enc.
   alloc_l iE0E0 Re R'. 
   ep iE0E0.
   deadcode iE0E0.
   swap iE0E0.
   eqobs_in iE0E0.
   
   (* Step 2 : replace G_body0 by G_body0', remove assignement to GR' at the begining,
      introduce assignement to GR' at the end under condition *)
   unfold Game1.
   match goal with
   |- EqObs _ _ (?i1::?i2::?i3::?iGR'::?c) _ _ _ =>
      apply EqObs_trans with E0' ([i1; i2; i3] ++ (c ++ [If !(R' in_dom LG) _then [iGR'] ]))  
   end.
   deadcode iE0E0'.
   eqobs_in iE0E0'.

   (* Step 3 : replace G_body1 by G_body1' *)
   apply EqObs_trans with E1' Game1;[ | eqobs_in iE1'E1 ].
    (* This is the main step : Coins fixing *)
   unfold Game1.
   match goal with 
   |- EqObs _ _ _ _ (?i1::?i2::?i3::?i4::?c) _ =>
     change (i1::i2::i3::i4::c) with ([i1; i2; i3] ++ (i4::c));
     set (C:= c); set (iGR':= i4)
   end.
   unfold EqObs; apply equiv_app with
    (req_mem_rel (Vset.add R' (Vset.add LG (Vset.add LH Gadv)))
      (EP1 (!(R' in_dom LG)))).
   eqobsrel_tail.
   unfold implMR; simpl; unfold O.eval_op; simpl; trivial.
   apply equiv_trans_eq_mem_l with (P1 := EP1 (!(R' in_dom LG)))
     (c1' := iGR'::C) (E1' :=  E1');
   [ | eqobs_in (iEiEi H_body0 G_body1') | intros k m1 m2 (H1, H2); exact H2].

   apply (@equiv_context_true E0' E1' G_body1 G_body0 _ GR' ({0,1}^k-p) (!(R' in_dom LG))).
   vm_compute; trivial.
   apply dcontext_correct with (ci := mkCi H_body0 H_body0 G_body0' G_body1'
     (If !(R' in_dom LG)then ((GR' <$- {0,1}^k-p) :: G_body1) else G_body0)
     (If !(R' in_dom LG)then G_body1 else G_body0)
     (Vset.singleton GR')
     (Vset.add GR' (Vset.union (fv_expr (!(R' in_dom LG))) (fv_distr {0,1}^k-p)))).
   vm_compute; trivial.

   (* G_body0 preserves the negation of the test *)
   unfold G_body0; union_mod.
   apply proj1_MR.
   eqobsrel_tail.
   unfold implMR,andR,notR,EP1; simpl; unfold O.eval_op; simpl.
   unfold Meq; intros k m1 m2 (Heq, Hin); subst; split; intros; trivial.
   destruct H.
   generalize (UT.i_eqb_spec (m2 R') (m2 R)).
   destruct (UT.i_eqb (m2 R') (m2 R)); intros.
   rewrite H2; simpl; trivialb.
   simpl; trivial.

   (* G_body1 uses only once GR' *)
   unfold G_body1; union_mod.
   apply proj1_MR.
   cp_test (R in_dom LG).
   ep_eq_l (!(R' in_dom LG)) true.
   unfold Meq; intros k m1 m2 ((H, H0), (H1, H2)); exact H0.
   swap; deadcode; eqobs_in.
   cp_test (R =?= R').
   match goal with
   |- equiv ?P ?E1 [?i1;?i2;?i3;?i4] ?E2 [?i1;?i2;?i3] (kreq_mem ?X) =>
     change (equiv P E1 ([i1; i2; i3] ++ [i4]) E2 ([i1; i2; i3]++nil) (kreq_mem X));
     apply equiv_app with (req_mem_rel X (EP1 (R' in_dom LG))) end.
   eqobsrel_tail.
   unfold implMR; simpl; unfold O.eval_op; simpl.
   intros; rewrite UTi_eqb_refl; trivial.
   ep_eq_l ((R' in_dom LG)) true.
   intros k m1 m2 (H1, H2); exact H2.
   eqobs_in.
   match goal with
   |- equiv ?P ?E1 [?i1;?i2;?i3;If ?e _then [?i4] ] ?E2 ?c (kreq_mem ?X) =>
     change [i1; i2; i3;If e _then [i4] ] with ([i1; i2; i3]++[If e _then [i4] ]);
     equiv_trans E1 ([i1; i2; i3] ++ [i4]);
     [apply equiv_app with (req_mem_rel X (EP1 e)) | ] end.
   eqobsrel_tail.
   unfold Meq, implMR, andR, EP1; simpl; unfold O.eval_op; simpl; intuition.
   unfold notR in H1, H2.
   generalize (UT.i_eqb_spec (m1 R') (m1 R));
    destruct (UT.i_eqb (m1 R') (m1 R)); trivial.
   intros W; elim H1; rewrite W, UTi_eqb_refl; trivial.
   ep_eq_l (!(R' in_dom LG)) true.
   intros k m1 m2 (H1, H2); exact H2.
   eqobs_in.
   deadcode; swap; eqobs_in.
  Qed.

  (******************************************************)
  (** Transition 2: E1, Game1 -> E2, Game2              *)
  (*  + Remove (R',GR') from the G_oracle memory        *)
  (*    and introduce the bad                           *)
  (*  + Inline G(R') in the main                        *)
  (******************************************************)

  Definition G_body2 :=
   [ If R =?= R' then [bad <- true; rG <- GR'] else G_body0 ].
  
  Definition E2 := mkEnv H_body0 G_body2.

  Definition Game2_ := 
   [
    LG <- Nil _;
    LH <- Nil _;
    R' <$- {0,1}^p;
    GR' <$- {0,1}^k-p;
    M <c- A with{};
    b <$- {0,1};
    If b then [Mb <- Efst (M)] else [Mb <- Esnd (M)];
    S' <- GR' |x| Mb;
    He <c- H with {S'};
    T' <- He |x| R';
    Y' <- apply_f S' @ T';
    b' <c- A' with {Y'}
   ].

  Definition Game2 := (bad <- false) :: Game2_.

  (** Invariant used for the transition :                          *)
  (*  - If R' is defined in LG then its value is GR' in Game1      *)
  (*  - R' is not defined in LG in Game2                           *)
  (*  - All defined entries in LG in Game2 are defined             *)
  (*    in LG in Game1 and have the same value associated          *)

  Definition inv_1_2 : mem_rel := 
   EP1 ((R' in_dom LG) ==> (LG[{R'}] =?= GR')) /-\
   eq_assoc_except R' LG.

  Lemma dec_inv_1_2 : decMR inv_1_2.
  Proof.
   unfold inv_1_2; auto.
  Qed.

  Lemma dep_inv_1_2 : depend_only_rel inv_1_2
   (Vset.union (fv_expr ((R' in_dom LG) ==> (LG [{R'}] =?= GR')))
    (Vset.add R' (Vset.singleton LG)))
   (Vset.union Vset.empty (Vset.singleton LG)).
  Proof.
   unfold inv_1_2; auto.
  Qed.
  
  Definition eE1E2 : eq_inv_info inv_1_2 E1 E2.
   refine (@empty_inv_info inv_1_2 _ _ dep_inv_1_2 _ dec_inv_1_2 E1 E2).
   vm_compute; trivial.
  Defined.

  (* The two oracles are equivalent under the invariant *)
  Lemma G_body1_Gbody2 :
   EqObsInv inv_1_2 (Vset.add R (Vset.add GR' (Vset.singleton R')))
   E1 G_body1 
   E2 G_body2 
   (Vset.add rG (Vset.singleton GR')).
  Proof.
   unfold G_body1, G_body2, G_body0, inv_1_2.
   cp_test (R =?= R').
   cp_test_l (R' in_dom LG).
   ep_eq_l (LG [{R'}]) GR'.
   unfold req_mem_rel, andR; intuition.
   generalize H1 H2; unfold EP1; simpl; unfold O.eval_op; simpl; intros.
   rewrite H3 in H6; unfold impb in H6; simpl in H6.
   rewrite <- is_true_UTi_eqb; trivial.
   deadcode eE1E2.
   fold inv_1_2; eqobs_in eE1E2.
   rewrite proj2_MR; apply proj1_MR.
   eqobsrel_tail.
   unfold inv_1_2, EP1, EP2, andR, kreq_mem, notR, implMR; simpl; unfold O.eval_op; simpl;
    unfold O.assoc; simpl; intros.
   repeat rewrite UTi_eqb_refl; simpl; split; trivial.
   intros r Hd; generalize Hd.
   rewrite <- is_true_UTi_eqb, not_is_true_false in Hd.
   rewrite (Hd:UT.i_eqb r (m1 R') = false); simpl.
   repeat match goal with H : _ /\ _ |- _ => destruct H end. 
   intros Hd'; exact (H4 _ Hd').
   cp_test (R in_dom LG).
   unfold req_mem_rel, andR, eq_assoc_except; intros.
   repeat match goal with H : _ /\ _ |- _ => destruct H end.
   destruct (H3 (m1 R)).
   rewrite <- is_true_Ti_eqb; exact H0.
   apply trans_eq with (1:= H4).
   rewrite (H _ R); trivial.
   fold inv_1_2.
   eapply equiv_strengthen;[ | apply equiv_assign].
   unfold req_mem_rel,upd_para, andR; intros.
   repeat match goal with H : _ /\ _ |- _ => destruct H end; split.
   unfold kreq_mem.
   match goal with 
    |- _{! _ <-- ?x1!} =={_} _{! _ <-- ?x2!} => replace x2 with x1 end.
   apply req_mem_update.
   apply req_mem_weaken with (2:= H); vm_compute; trivial.
   simpl; unfold O.eval_op; simpl.
   rewrite <- (H _ R);[ | vm_compute; trivial].
   destruct H4 as (H4, H5); destruct (H5 (m1 R)) as (H6, H7);[ | exact H7].
   rewrite <- is_true_Ti_eqb; exact H2.
   apply dep_inv_1_2 with (3:= H4); apply req_mem_upd_disjoint; vm_compute; trivial.
   eqobsrel_tail.
   unfold inv_1_2, EP1, EP2, andR, kreq_mem, notR, implMR; simpl; unfold O.eval_op; simpl;
    unfold O.assoc; simpl; intros.
   repeat match goal with H : _ /\ _ |- _ => destruct H end.
   rewrite is_true_UTi_eqb in H2; apply sym_not_eq in H2;
    rewrite <- is_true_UTi_eqb, not_is_true_false in H2;
    rewrite (H2:UT.i_eqb (m1 R') (m1 R)=false); simpl.
   split; trivial.
   intros r Hd.
   rewrite <- (H _ R); trivial.
   generalize (UT.i_eqb_spec r (m1 R)); destruct (UT.i_eqb r (m1 R)); simpl;
   [auto | intros; exact (H6 _ Hd)].
  Qed.

  Definition iE1E2 : eq_inv_info inv_1_2 E1 E2 :=  
   iEinv_GG' eE1E2 Vset.empty Vset.empty G_body1_Gbody2.

  Definition iE2E2 : eq_inv_info trueR E2 E2 := 
   i_refl H_body0 H_body0 Vset.empty Vset.empty
   G_body2 G_body2 (Vset.singleton bad) (Vset.singleton bad).
  
  Lemma EqObs_Game1_Game2 : EqObs Gadv E1 Game1 E2 Game2_ (fv_expr (b=?=b')).
  Proof.
   apply EqObs_trans with E2 Game1.
   eqobs_tl iE1E2.
   unfold inv_1_2; eqobsrel_tail.
   unfold implMR; simpl; unfold O.eval_op; simpl; auto.
   deadcode iE2E2.
   sinline iE2E2 G.
   eqobs_in iE2E2.
  Qed.


  (******************************************************)
  (** Transition 3: E2, Game2_ -> E3, Game2_            *)
  (*  + replace rG <- GR' in the G_oracle               *)
  (*    by rG <$-{0,1}^k-p                              *)
  (*  Apply the fundamental lemma                       *)
  (*  GR' is used only once for S'                      *)
  (* We are now interested by the probability           *)
  (* of (bad = true) and the probability of (b = b')    *)
  (******************************************************)

  Definition G_body3 :=
   [ If R =?= R' then (bad <- true)::G_body0 else G_body0 ].

  Definition E3 := mkEnv H_body0 G_body3.


  (******************************************************)
  (** Transition 4 : E3, Game2 -> E3, Game3             *)
  (*  + Since GR' is used only once, replace            *)
  (*     GR' <$- {0,1}^k-p; S' <- GR' |x| Mb;           *)
  (*    with                                            *) 
  (*     S' <$- {0,1}^k-p; GR' <- S' |x| Mb;            *)
  (*  + Thus GR' is not used any more --> remove it     *)
  (*  + thus Mb is not used any more --> remove it      *)
  (*  + code motion to prepare for next transition      *)
  (******************************************************)

  Definition Game3_ := 
   [
    bad <- false;
    LG <- Nil _;
    LH <- Nil _;
    S' <$- {0,1}^k-p;
    R' <$- {0,1}^p;
    M <c- A with{};
    He <c- H with {S'};
    T' <- He |x| R';
    Y' <- apply_f S' @ T';
    b' <c- A' with {Y'}
   ].

  Definition Game3 := Game3_ ++ [b <$- {0,1}].

  Definition iE3E3 := iEiEi H_body0 G_body3.
  
  Lemma EqObs_Game2_Game3 : 
   EqObs Gadv 
   E3 Game2 
   E3 Game3 
   (Vset.add bad (fv_expr (b=?=b'))).
  Proof.
   unfold Game2, Game2_, Game3, Game3_; simpl.
   swap iE3E3.
   eqobs_tl iE3E3.
   match goal with
    |- EqObs _ _ [?ibad;?iLG;?iLH;?iR';?iGR';?iM;?ib;?iMb;?iS'] _ _ _ =>
     apply EqObs_trans with E3 
      [ ibad; iLG; iLH; iR'; iM; ib; iMb; iGR'; iS'];
      [ swap iE3E3; eqobs_in iE3E3
       | apply EqObs_trans with E3
        [ ibad; iLG; iLH; iR'; iM; ib; iMb; S' <$-{0,1}^k-p;GR' <-  S' |x| Mb];
        [ | deadcode iE3E3; swap iE3E3; eqobs_in iE3E3]
      ]
   end.
   eqobs_hd iE3E3.
   unfold EqObs; apply equiv_trans_eq_mem_l with 
    trueR E3 [S' <$- {0,1}^k-p; GR' <- S' |x| Mb].
   rewrite proj1_MR; apply optim_sampl_kmp; intros; discriminate.
   eqobs_in iE3E3.
   red; red; trivial.
  Qed.


  (******************************************************)
  (** Remark : in Game3, the result of the adversary    *)
  (**  does not depend on b, so the probability         *)
  (**  of (b = b') is 1/2                               *)
  (** After this, in Game3 we are only interested by    *)
  (** in the probability of (bad = true)                *)
  (******************************************************)

  (***********************************************)
  (** Transition 5:  E3, Game3 -> E4, Game4      *) 
  (*  + Fixing answer to S' in H                 *)
  (***********************************************)

  Definition Game4 := 
   [
    bad <- false;   
    LG <- Nil _;
    LH <- Nil _;
    S' <$- {0,1}^k-p;
    HS' <$- {0,1}^p;
    R' <$- {0,1}^p;
    M <c- A with{};
    He <c- H with {S'};
    T' <- He |x| R';
    Y' <- apply_f S' @ T';
    b' <c- A' with {Y'}
   ].

  Definition H_body4 :=
   [
    If !(S in_dom LH) 
    then [
         If S =?= S' then [rH <- HS'] else [rH <$- {0,1}^p];
         LH <- (S | rH) |::| LH
         ] 
    else [ rH <- LH[{S}] ]
   ].

  Definition E4 := mkEnv H_body4 G_body3.

  Definition H_body0' := 
   [ If !(S' in_dom LH) then (HS'<$- {0,1}^p) :: H_body4 else H_body0].
  
  Definition H_body4' :=
   [ If !(S' in_dom LH) then H_body4 else H_body0].

  Definition E3' := mkEnv H_body0' G_body3.
  Definition E4' := mkEnv H_body4' G_body3.
  
  Lemma H_body0_H_body0' : forall E E',
   EqObsInv trueR (Vset.add S (Vset.add S' (Vset.singleton LH)))
   E  H_body0 
   E' H_body0' 
   (Vset.add rH (Vset.add S (Vset.add S' (Vset.singleton LH)))). 
  Proof. 
   intros; unfold EqObsInv; fold_eqobs_tac.
   unfold H_body0', H_body0, H_body4.
   cp_test (S' in_dom LH).
   eqobs_in.
   cp_test (S in_dom LH).
   deadcode; eqobs_in.
   cp_test (S=?=S').
   alloc_r HS' rH.
   ep; deadcode; eqobs_in.
   deadcode; eqobs_in.
  Qed.

  Lemma H_body4'_H_body4 : forall E E', 
   EqObsInv trueR (Vset.add HS' (Vset.add S (Vset.add S' (Vset.singleton LH))))
   E H_body4' 
   E' H_body4
   (Vset.add rH (Vset.add HS' (Vset.add S (Vset.add S' (Vset.singleton LH))))).
  Proof. 
   intros; unfold EqObsInv; fold_eqobs_tac.
   unfold H_body4', H_body0, H_body4.
   cp_test (S' in_dom LH).
   cp_test (S in_dom LH).
   eqobs_in.
   cp_test (S =?= S').
   apply equiv_False.
   unfold req_mem_rel, andR, notR,EP1,EP2; simpl; unfold O.eval_op; simpl.
   intros k m1 m2 (((H1, (H5, H7)), (H6, H4)), (H2, H3)).
   assert (W:= UT.i_eqb_spec (m1 S) (m1 S')); rewrite H2 in W.   
   apply H6; rewrite W; trivial.
   eqobs_in.
   eqobs_in.
  Qed.

  Definition iE3E3' : eq_inv_info trueR E3 E3' := iE_HH' (H_body0_H_body0' E3 E3').
  Definition iE4'E4 : eq_inv_info trueR E4' E4 := iE_HH' (H_body4'_H_body4 E4' E4). 

  (* H_body0 preserves the negation of the test *)
  Lemma H_body0_neg_test : forall E E',  
   equiv (Meq /-\ ~- EP1 (!(S' in_dom LH))) 
   E H_body0 
   E' H_body0
   (Meq /-\ ~- EP1 (!(S' in_dom LH))).
  Proof.
   intros; union_mod.
   apply proj1_MR.
   eqobsrel_tail.
   unfold implMR,andR,notR,EP1; simpl; unfold O.eval_op; simpl.
   unfold Meq; intros k m1 m2 (Heq, Hin); subst; split; intros; trivial.
   destruct H.
   generalize (UT.i_eqb_spec (m2 S') (m2 S));
   destruct (UT.i_eqb (m2 S') (m2 S)); intros.
   rewrite H2; simpl; trivialb.
   simpl; trivial.
  Qed. 

  (* H_body4 uses only once HS' *)
  Lemma H_body4_HS'_once : forall E E',
   equiv 
   (Meq /-\ EP1 (!(S' in_dom LH))) 
   E  ((HS' <$- {0,1}^p) :: H_body4 ++ [If !(S' in_dom LH) _then [HS' <$- {0,1}^p] ]) 
   E' ((HS' <$- {0,1}^p) :: H_body4) 
   Meq.
  Proof.
   intros; union_mod.
   apply proj1_MR.
   cp_test (S in_dom LH).
   ep_eq_l (!(S' in_dom LH)) true.
   unfold Meq; intros k m1 m2 ((H, H0), (H1, H2)); exact H0.
   swap; deadcode; eqobs_in.
   cp_test (S =?= S').
   match goal with
   |- equiv ?P ?E1 [?i1;?i2;?i3;?i4] ?E2 [?i1;?i2;?i3] (kreq_mem ?X) =>
     change (equiv P E1 ([i1; i2; i3] ++ [i4]) E2 ([i1; i2; i3]++nil) (kreq_mem X));
     apply equiv_app with (req_mem_rel X (EP1 (S' in_dom LH))) end.
   eqobsrel_tail.
   unfold implMR; simpl; unfold O.eval_op; simpl.
   intros; rewrite UTi_eqb_refl; trivial.
   ep_eq_l ((S' in_dom LH)) true.
   intros k m1 m2 (H1, H2); exact H2.
   eqobs_in.
   match goal with
   |- equiv ?P ?E1 [?i1;?i2;?i3;If ?e _then [?i4] ] ?E2 ?c (kreq_mem ?X) =>
     change [i1; i2; i3;If e _then [i4] ] with ([i1; i2; i3]++[If e _then [i4] ]);
     equiv_trans E1 ([i1; i2; i3] ++ [i4]);
     [apply equiv_app with (req_mem_rel X (EP1 e)) | ] end.
   eqobsrel_tail.
   unfold Meq, implMR, andR, EP1; simpl; unfold O.eval_op; simpl; intuition.
   unfold notR in H1, H2.
   generalize (UT.i_eqb_spec (m1 S') (m1 S));
    destruct (UT.i_eqb (m1 S') (m1 S)); trivial.
   intros W; elim H1; rewrite W, UTi_eqb_refl; trivial.
   ep_eq_l (!(S' in_dom LH)) true.
   intros k m1 m2 (H1, H2); exact H2.
   eqobs_in.
   deadcode; swap; eqobs_in.
  Qed.

  Lemma EqObs_Game3_Game4 : 
   EqObs Gadv 
   E3 Game3 
   E4 Game4 
   (Vset.singleton bad).
  Proof.
   apply EqObs_trans with E3' (Game3_ ++ [If !(S' in_dom LH) _then [HS' <$- {0,1}^p] ]);
   [deadcode iE3E3'; eqobs_in iE3E3' | ].
   apply EqObs_trans with E4' Game4;[ | eqobs_in iE4'E4].
   (* This is the main step: Coin fixing *)
   unfold Game3_, Game4.
   match goal with 
   |- EqObs _ _ ((?i1::?i2::?i3::?i4::?c)++?cif) _ (?i1::?i2::?i3::?i4::?c') _ =>
     change ((i1::i2::i3::i4::c)++cif) with ([i1; i2; i3; i4] ++ (c++cif));
     change (i1::i2::i3::i4::c') with ([i1; i2; i3; i4] ++ c')
   end.
   unfold EqObs; apply equiv_app with
    (req_mem_rel (Vset.add bad (Vset.add S' (Vset.add LG (Vset.add LH Gadv))))
      (EP1 (!(S' in_dom LH)))).
   eqobsrel_tail.
   unfold implMR; simpl; unfold O.eval_op; simpl; trivial.
   match goal with
   |- equiv _ _ _ ?E ?c _ =>
     apply equiv_trans_eq_mem_l with  (EP1 (!(S' in_dom LH))) E c;
     [ | eqobs_in (iEiEi H_body4' G_body3) | intros k m1 m2 (H1, H2); exact H2]
   end.
   apply (@equiv_context_true E3' E4' H_body4 H_body0 _ HS' ({0,1}^p) (!(S' in_dom LH))).
   vm_compute; trivial.
   apply dcontext_correct with (ci := mkCi H_body0' H_body4' G_body3 G_body3
     (If !(S' in_dom LH)then ((HS' <$- {0,1}^p) :: H_body4) else H_body0)
     (If !(S' in_dom LH)then H_body4 else H_body0)
     (Vset.singleton HS')
     (Vset.add HS' (Vset.union (fv_expr (!(S' in_dom LH))) (fv_distr {0,1}^p)))).
   vm_compute; trivial.
   apply H_body0_neg_test.
   apply H_body4_HS'_once.
  Qed.

  (******************************************************)
  (** Transition 6: E4, Game4 -> E4, Game4_             *)
  (*  We want to replace He <c- H with {S'} by He <- HS'*)
  (*  but without setting S' in LH                      *)
  (*  + remove (S',HS') from the H_oracle memory        *)
  (*  + inline H(S') in the main, re-introduce          *)
  (*    (S',HS') in the H_oracle memory                 *)
  (******************************************************)

  Definition H_body4_ :=
   [ If S =?= S' then [rH <- HS'] else H_body0 ].
  
  Definition E4_ := mkEnv H_body4_ G_body3.

  Definition Game4_ := 
   [
    bad <- false;
    LG <- Nil _;
    LH <- Nil _;
    S' <$- {0,1}^k-p;
    R' <$- {0,1}^p;
    HS' <$- {0,1}^p;
    T' <- HS' |x| R';
    Y' <- apply_f S' @ T';
    M <c- A with{};
    b' <c- A' with {Y'}
   ].
  
  (** Invariant used for the transition :                          *)
  (*  - If S' is defined in LH then its value is HS' in Game4      *)
  (*  - LG in Game4 and Game4' equivalent except for S'            *)

  Definition inv_4_4_ : mem_rel := 
   EP1 ((S' in_dom LH) ==> (LH[{S'}] =?= HS')) /-\
   eq_assoc_except S' LH.

  Lemma dec_inv_4_4_ : decMR inv_4_4_.
  Proof.
   unfold inv_4_4_; auto.
  Qed.

  Lemma dep_inv_4_4_ : depend_only_rel inv_4_4_ 
   (Vset.union (fv_expr ((S' in_dom LH) ==> (LH [{S'}] =?= HS')))
    (Vset.add S' (Vset.singleton LH)))
   (Vset.union Vset.empty (Vset.singleton LH)).
  Proof.
   unfold inv_4_4_; auto.
  Qed.

  Definition eE4E4_ : eq_inv_info inv_4_4_ E4 E4_.
   refine (@empty_inv_info inv_4_4_ _ _ dep_inv_4_4_ _ dec_inv_4_4_ E4 E4_).
   vm_compute; trivial.
  Defined.

  (* The two oracles are equivalent under the invariant *)
  Lemma H_body4_Hbody4_ :
   EqObsInv inv_4_4_ (Vset.add S (Vset.add HS' (Vset.singleton S')))
   E4 H_body4 
   E4_ H_body4_ 
   (Vset.singleton rH).
  Proof.
   unfold H_body4_, H_body4, H_body0, inv_4_4_.
   cp_test (S =?= S').
   cp_test_l (S' in_dom LH).
   ep_eq_l (LH [{S'}]) HS'.
   unfold req_mem_rel, andR; intuition.
   generalize H1 H2; unfold EP1; simpl; unfold O.eval_op; simpl; intros.
   rewrite H3 in H6; unfold impb in H6; simpl in H6.
   rewrite <- is_true_UTi_eqb; trivial.
   deadcode eE4E4_.
   fold inv_4_4_; eqobs_in eE4E4_.
   rewrite proj2_MR; apply proj1_MR.
   eqobsrel_tail.
   unfold inv_4_4_, EP1, EP2, andR, kreq_mem, notR, implMR; simpl; unfold O.eval_op; simpl;
    unfold O.assoc; simpl; intros.
   repeat rewrite UTi_eqb_refl; simpl; split; trivial.
   intros r Hd; generalize Hd.
   rewrite <- is_true_UTi_eqb, not_is_true_false in Hd.
   rewrite (Hd:UT.i_eqb r (m1 S') = false); simpl.
   repeat match goal with H : _ /\ _ |- _ => destruct H end.
   intros Hd'; exact (H4 _ Hd').
   cp_test (S in_dom LH).
   unfold req_mem_rel, andR, eq_assoc_except; intros.
   repeat match goal with H : _ /\ _ |- _ => destruct H end.
   destruct (H3 (m1 S)).
   rewrite <- is_true_Ti_eqb; exact H0.
   apply trans_eq with (1:= H4).
   rewrite (H _ S); trivial.
   fold inv_4_4_.
   eapply equiv_strengthen;[ | apply equiv_assign].
   unfold req_mem_rel,upd_para, andR; intros.
   repeat match goal with H : _ /\ _ |- _ => destruct H end; split.
   unfold kreq_mem.
   match goal with 
    |- _{! _ <-- ?x1!} =={_} _{! _ <-- ?x2!} => replace x2 with x1 end.
   change (Vset.singleton rH) with (Vset.add rH Vset.empty).
   apply req_mem_update.
   apply req_mem_weaken with (2:= H); vm_compute; trivial.
   simpl; unfold O.eval_op; simpl.
   rewrite <- (H _ S);[ | vm_compute; trivial].
   destruct H4 as (H4, H5); destruct (H5 (m1 S)) as (H6, H7);[ | exact H7].
   rewrite <- is_true_Ti_eqb; exact H2.
   apply dep_inv_4_4_ with (3:= H4); apply req_mem_upd_disjoint; vm_compute; trivial.
   eqobsrel_tail.
   unfold inv_4_4_, EP1, EP2, andR, kreq_mem, notR, implMR; simpl; unfold O.eval_op; simpl;
    unfold O.assoc; simpl; intros.
   repeat match goal with H : _ /\ _ |- _ => destruct H end.
   rewrite is_true_UTi_eqb in H2; apply sym_not_eq in H2;
    rewrite <- is_true_UTi_eqb, not_is_true_false in H2;
    rewrite (H2:UT.i_eqb (m1 S') (m1 S)=false); simpl.
   split; trivial.
   intros r Hd.
   rewrite <- (H _ S); trivial.
   generalize (UT.i_eqb_spec r (m1 S)); destruct (UT.i_eqb r (m1 S)); simpl;
   [auto | intros; exact (H6 _ Hd)].
  Qed.

  Definition iE4E4_ : eq_inv_info inv_4_4_ E4 E4_ :=  
   iEinv_HH' eE4E4_ Vset.empty Vset.empty H_body4_Hbody4_.

  Definition iE4_E4_ : eq_inv_info trueR E4_ E4_ := iEiEi H_body4_ G_body3.

  Lemma EqObs_Game4_Game4_ : 
   EqObs Gadv 
   E4 Game4 
   E4 Game4_ 
   (Vset.singleton bad).
  Proof.
   apply EqObs_trans with E4_ Game4.
   eqobs_tl iE4E4_.
   unfold inv_4_4_; eqobsrel_tail.
   unfold implMR; simpl; unfold O.eval_op; simpl; auto.
   apply EqObs_trans with E4_ Game4_.
   sinline iE4_E4_ H.
   swap iE4_E4_.
   eqobs_in iE4_E4_.
   apply EqObs_sym.
   eqobs_tl iE4E4_.
   unfold inv_4_4_; eqobsrel_tail.
   unfold implMR; simpl; unfold O.eval_op; simpl; auto.
  Qed.


  (******************************************************)
  (** Transition 7:  E4, Game4_ -> E5, Game5            *)
  (** We introduce two variables bad1 and bad2 in G     *)
  (**    bad1 := bad = true /\ S' in LH                 *)
  (**    bad2 := bad = true /\ !(S' in LH)              *)
  (**  since bad1 \/ bad2 => bad we can focus on the    *)
  (*   probability of bad1 and the probability of bad2  *)
  (*                                                    *)
  (******************************************************)

  Definition G_body5 :=
   (If R =?= R' 
    _then [
          If S' in_dom LH then [ bad1 <- true] else [bad2 <- true];
          bad <- true
          ]) 
   :: G_body0.

  Definition E5 := mkEnv H_body4 G_body5.

  Definition Game5 := (bad1 <- false) :: (bad2 <- false) :: Game4_.

  Lemma G_body3_G_body5 : 
   EqObsInv trueR (Vset.add R' (Vset.add S' (Vset.add R (Vset.add LH (Vset.add LG (Vset.singleton bad))))))
   E4 G_body3 
   E5 G_body5 
   (Vset.add rG (Vset.add LH (Vset.add LG (Vset.singleton bad)))).
  Proof.
   deadcode.
   cp_test (R =?= R'); eqobs_in.
  Qed.

  Definition iE4E5 : eq_inv_info trueR E4 E5 :=
   iEinv_GG' (empty_info (mkEnv H_body4 G_body3) (mkEnv H_body4 G_body5))
   Vset.empty (Vset.add bad1 (Vset.singleton bad2)) G_body3_G_body5.
  
  Lemma EqObs_Game4_Game5 : 
   EqObs Gadv 
   E4 Game4_ 
   E5 Game5 
   (Vset.singleton bad).
  Proof.
   deadcode iE4E5.
   eqobs_in iE4E5.
  Qed.

  Close Scope bool_scope. 
  Close Scope nat_scope.
 
  Definition inv_5_5 := EP1 (bad ==> (bad1 || bad2)).
  
  Lemma dep_inv_5_5 : depend_only_rel inv_5_5 
   (fv_expr (bad ==> (bad1 || bad2))) Vset.empty.
  Proof. 
   unfold inv_5_5; auto. 
  Qed.
  
  Lemma dec_inv_5_5 : decMR inv_5_5.
  Proof. 
   unfold inv_5_5; auto. 
  Qed.

  Definition eE5E5 : eq_inv_info inv_5_5 E5 E5.
   refine (@empty_inv_info inv_5_5 _ _ dep_inv_5_5 _ dec_inv_5_5 E5 E5).
   vm_compute; trivial.
  Defined.

  Lemma G_body5_G_body5 :
   EqObsInv inv_5_5 
   (Vset.add R' (Vset.add S' (Vset.add R (Vset.add LH (Vset.add LG
    (Vset.add bad1 (Vset.add bad2 (Vset.singleton bad))))))))
   E5 G_body5 
   E5 G_body5 
   (Vset.add rG (Vset.add bad1 (Vset.add bad2 (Vset.add LG (Vset.singleton bad))))).
  Proof.
   unfold inv_5_5; eqobsrel_tail; simpl; unfold O.eval_op; simpl.
   repeat split; intros; trivial; 
    try rewrite impb_true_r; try rewrite orb_true_r; simpl; trivial.
   destruct H as (W1,W2); exact W2.
   destruct H as (W1,W2); exact W2.
  Qed.

  Definition iE5E5 : eq_inv_info inv_5_5 E5 E5 :=
   iEinv_GG' eE5E5 Vset.empty Vset.empty G_body5_G_body5.
  
  Lemma split_bad : forall k (m:Mem.t k),
   Pr E5 Game5 m (EP k bad) <=
   Pr E5 Game5 m (EP k bad1) + Pr E5 Game5 m (EP k bad2).
  Proof.
   intros k m.
   unfold Pr; eapply Ole_trans;[ | apply distr_OR_charfun].
   apply equiv_deno_le with (kreq_mem Gadv)
    (req_mem_rel (Vset.add bad (Vset.add bad1 (Vset.add bad2 Gadv))) inv_5_5); trivial.
   eqobs_tl iE5E5.
   unfold inv_5_5; eqobsrel_tail.
   simpl; unfold implMR, O.eval_op; simpl; intros; trivial.
   unfold inv_5_5; intros m1 m2 (H1, H2); generalize H2; clear H2.
   unfold EP, EP1, charfun, restr; simpl; unfold O.eval_op; simpl; unfold impb, orP.
   destruct (m1 bad);[simpl; intros | trivial].
   rewrite <- (H1 _ bad1);[ | trivial].
   rewrite <- (H1 _ bad2);[ | trivial].
   rewrite H2; trivial.
  Qed.


  (**************************************************)
  (*  The probability of bad is split into the      *)
  (*  probability of bad1 and bad2                  *)
  (*  We focus now on the probalility of bad1       *)
  (**************************************************)

  (******************************************************)
  (** Transition 8: E5, Game5 -> E6, Game6              *)
  (*  + remove bad and bad2, not used anymore           *)
  (*  + apply optimistic sampling between : T' and R'   *)
  (*                                                    *)
  (******************************************************)

  Definition G_body6 := 
   (If R =?= R' _then [If S' in_dom LH _then [ bad1 <- true] ])
   ::G_body0.
  
  Definition E6 := mkEnv H_body4 G_body6.

  Definition iE5E6 : eq_inv_info trueR E5 E6 :=
   i_refl H_body4 H_body4 Vset.empty Vset.empty 
   G_body5 G_body6 (Vset.add bad (Vset.singleton bad2)) Vset.empty.
  
  Definition Game6 := 
   [
    bad1 <- false;
    LG <- Nil _;
    LH <- Nil _;
    S' <$- {0,1}^k-p;
    HS' <$- {0,1}^p;
    T' <$- {0,1}^p;
    R' <- HS' |x| T';
    Y' <- apply_f S' @ T';
    M <c- A with{};
    b' <c- A' with {Y'}
   ].

  Lemma EqObs_Game5_Game6 : 
   EqObs Gadv 
   E5 Game5 
   E6 Game6
   (Vset.singleton bad1).
  Proof.
   deadcode iE5E6.
   eqobs_ctxt iE5E6.
   unfold EqObsInv; fold_eqobs_tac.
   apply EqObs_trans with E5 [HS' <$- {0,1}^p;R' <$- {0,1}^p;  T' <- HS' |x| R'].
   swap; eqobs_in.
   eqobs_hd.
   unfold EqObs.
   apply equiv_trans_eq_mem_l with trueR E5 [T' <$- {0,1}^p; R' <- HS' |x| T'].
   rewrite proj1_MR; apply optim_sampl_p; intros; discriminate.
   eqobs_in.
   red; red; trivial.
  Qed.


  (******************************************************)
  (** Transition 9:  E6, Game6 -> E7, Game6             *)
  (*  + eliminate R' and S' from G                      *)
  (*  + use the following invariant :                   *)
  (*     - S' in LH => LH[{S'}] = HS'                   *)
  (*     - R' = HS' |x| T'                              *)
  (*     - Y' = f (S' @ T')                             *)
  (*  Since R' is no longer used, eliminate its         *)
  (*  definition                                        *)
  (******************************************************)

  Notation SHS := (Var.Lvar (T.Pair bskmp bsp) 17).

  Definition Game7 := 
   [
    bad1 <- false;
    LG <- Nil _;
    LH <- Nil _;
    S' <$- {0,1}^k-p;
    HS' <$- {0,1}^p;
    T' <$- {0,1}^p;
    Y' <- apply_f S' @ T';
    M <c- A with{};
    b' <c- A' with {Y'}
   ].

  Definition G_body7 := 
   (If (E.Eexists SHS (apply_f ((Efst SHS) @ (Esnd SHS |x| R)) =?= Y') LH)
    _then [ bad1 <- true])
    :: G_body0.
  
  Definition expr_6_7 : E.expr T.Bool := 
   (E.Eforall SHS ((Efst SHS =?= S') ==> (Esnd SHS =?= HS')) LH) &&
   (R' =?= HS' |x| T') &&
   (Y' =?= apply_f (S' @ T')).
  
  Definition inv_6_7 := EP1 (expr_6_7). 
  
  Lemma dep_inv_6_7 : depend_only_rel inv_6_7 (fv_expr expr_6_7) Vset.empty.
  Proof. 
   unfold inv_6_7; auto. 
  Qed.

  Lemma dec_inv_6_7 : decMR inv_6_7.
  Proof. 
   unfold inv_6_7; auto.
  Qed.

  Definition E7 := mkEnv H_body4 G_body7.

  Definition eE6E7 : eq_inv_info inv_6_7 E6 E7.
   refine (@empty_inv_info inv_6_7 _ _ dep_inv_6_7 _ dec_inv_6_7 E6 E7).
   vm_compute; trivial.
  Defined.


  (** G is equivalent in both games and preserves the invariant *)
  Lemma G_body6_G_body7 : 
   EqObsInv inv_6_7 
   (Vset.add bad1 (Vset.add R (Vset.add LG 
    (Vset.add S' (Vset.add LH (Vset.add HS' 
     (Vset.add R' (Vset.add T' (Vset.singleton Y')))))))))
   E6 G_body6 
   E7 G_body7
   (Vset.add bad1 (Vset.add rG (Vset.singleton LG))).
  Proof.
   eqobs_tl eE6E7.
   unfold EqObsInv; match goal with
                     |- equiv ?P1 _ _ _ _ _ => 
                      assert (implMR P1 
                       (fun k m1 m2 => 
                        E.eval_expr ((R =?= R') && (S' in_dom LH)) m1 =
                        E.eval_expr (E.Eexists SHS (apply_f Efst (SHS) @ (Esnd (SHS) |x| R) =?= Y') LH) m2)) end.
   unfold req_mem_rel, andR, inv_6_7, EP1; intros k m1 m2.
   simpl; unfold O.eval_op; simpl.
   intros (H1, H2).
   rewrite <- (H1 _ LH);[ | vm_compute; trivial].
   repeat rewrite is_true_andb in H2.
   destruct H2 as ((H2, H3), H4); generalize (m1 LH) H2; clear H2.
   induction i; simpl.
   intros; rewrite andb_false_r; trivial.
   repeat rewrite Mem.get_upd_same.
   repeat (rewrite Mem.get_upd_diff;[ | intro; discriminate]).
   rewrite <- (H1 _ R);[ | vm_compute; trivial].
   rewrite <- (H1 _ Y');[ | vm_compute; trivial].
   rewrite is_true_UTi_eqb in H4, H3; rewrite H4, H3.
   rewrite is_true_andb, is_true_impb,is_true_UTi_eqb.
   intros (H5, H6); generalize H5; clear H5.
   rewrite <- (IHi H6); clear IHi.
   generalize (UT.i_eqb_spec (m1 R) (m1 R'));
    destruct (UT.i_eqb (m1 R) (m1 R')); intro; simpl.
   rewrite H, H3, UTi_eqb_refl; simpl.
   generalize (UT.i_eqb_spec (m1 S') (fst a));
    destruct (UT.i_eqb (m1 S') (fst a)); intro; simpl.
   rewrite <- H0, is_true_UTi_eqb.
   intros H5; rewrite H5; trivial.
   rewrite <- BVxor_assoc, BVxor_nilpotent, BVxor_0_l, UTi_eqb_refl; trivial.
   intros; match goal with|- ?x = _ => case_eq x; intros; trivial end.
   rewrite orb_true_r; trivial.
   rewrite orb_false_r.
   symmetry; rewrite <- not_is_true_false, is_true_UTi_eqb, <- BVxor_assoc; intro.
   elim H0.
   destruct (@Vextend_inj (Datatypes.S (k_kmp k)) (k_p k) _ _ _ _ (f_inj H7)).
   elim H0; rewrite H8; trivial.
   rewrite orb_false_r, <- H3.
   generalize H; rewrite <-is_true_UTi_eqb in H.
   change (~ (is_true (UT.i_eqb (m1 R) (m1 R')))) in H; intros.
   rewrite not_is_true_false in H; rewrite H; simpl.
   symmetry; rewrite <- not_is_true_false, is_true_UTi_eqb; intro.
   destruct (@Vextend_inj (Datatypes.S (k_kmp k)) (k_p k) _ _ _ _ (f_inj H2)). 
   rewrite is_true_UTi_eqb in H5; rewrite H5 in H8; trivial.
   elim H0; rewrite H3, <- H8, <- BVxor_assoc, BVxor_nilpotent, BVxor_0_l; trivial.

   cp_test_l eE6E7 (R =?= R').
   cp_test_l eE6E7 (S' in_dom LH).
   ep_eq_r eE6E7 (E.Eexists SHS (apply_f Efst (SHS) @ (Esnd (SHS) |x| R) =?= Y') LH) true.
   intros k m1 m2 ((H1, H2), H4).
   assert (W:= H k m1 m2 H1); hnf in W; rewrite <- W.
   generalize H2 H4; unfold EP1; simpl; unfold O.eval_op; simpl.
   intros W1 W2; rewrite W1; trivial.
   rewrite proj1_MR, proj1_MR; eqobs_in eE6E7.
   ep_eq_r eE6E7 (E.Eexists SHS (apply_f Efst (SHS) @ (Esnd (SHS) |x| R) =?= Y') LH) false.
   intros k m1 m2 ((H1, H2), H4).
   assert (W:= H k m1 m2 H1); hnf in W; rewrite <- W.
   generalize H2 H4; unfold notR, EP1; simpl; unfold O.eval_op; simpl.
   intros W1 W2; rewrite W1; simpl; rewrite <- not_is_true_false; trivial.
   rewrite proj1_MR, proj1_MR; eqobs_in eE6E7.
   ep_eq_r eE6E7 (E.Eexists SHS (apply_f Efst (SHS) @ (Esnd (SHS) |x| R) =?= Y') LH) false.
   intros k m1 m2 (H1, H2).
   assert (W:= H k m1 m2 H1); hnf in W; rewrite <- W.
   generalize H2 ; unfold notR, EP1; simpl; unfold O.eval_op; simpl.
   rewrite not_is_true_false; intros W1; rewrite W1; trivial.
   rewrite proj1_MR; eqobs_in eE6E7.
  Qed.  

  Lemma H_body4_H_body4 : 
   EqObsInv inv_6_7 
   (Vset.add S (Vset.add LG 
    (Vset.add S' (Vset.add LH (Vset.add HS' 
     (Vset.add R' (Vset.add T' (Vset.singleton Y'))))))))
   E6 H_body4 
   E7 H_body4
   (Vset.add rH (Vset.singleton LH)).
  Proof.
   unfold inv_6_7, expr_6_7; eqobsrel_tail;
    unfold implMR, req_mem_rel, andR, EP1; simpl; unfold O.eval_op; simpl.
   intros k m1 m2 (H1, H2).
   repeat rewrite is_true_andb in H2; destruct H2 as ((H2, H3), H4).
   rewrite H3, H4; repeat rewrite andb_true_r.
   split; intros.
   split; intros.
   rewrite UTi_eqb_refl, impb_true_r; simpl.
   rewrite is_true_forallb in H2 |- *; intros.
   generalize (H2 _ H5).
   rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff;[ | intro; discriminate]); trivial.
   destruct H0 as (H0, _); rewrite not_is_true_false in H0; rewrite H0.
   repeat rewrite andb_true_r; unfold impb; simpl.
   rewrite is_true_forallb in H2 |- *; intros.
   generalize (H2 _ H6).
   rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff;[ | intro; discriminate]); trivial.
   rewrite is_true_forallb in H2 |- *; intros.
   generalize (H2 _ H0).
   rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff;[ | intro; discriminate]); trivial.
  Qed.

  Definition iE6E7 : eq_inv_info inv_6_7 E6 E7 :=
   iEinv eE6E7 H_body4_H_body4 G_body6_G_body7.

  Definition iE7E7 := iEiEi H_body4 G_body7.
  
  Lemma Game6_Game7 : 
   EqObs Gadv 
   E6 Game6 
   E7 Game7 
   (Vset.singleton bad1).
  Proof. 
   apply EqObs_trans with E7 Game6.  
   eqobs_tl iE6E7.
   unfold inv_6_7; eqobsrel_tail.
   red; simpl; unfold O.eval_op; simpl.
   intros; repeat rewrite UTi_eqb_refl; trivial.
   deadcode iE7E7; swap iE7E7; eqobs_in iE7E7.
  Qed.


  (******************************************************)
  (** Transition 10: E7, Game6 -> E8, Game8             *)
  (*   - R' is not used, we remove its assigment        *)
  (*   - HS' is used only once, revert coin fixing      *)
  (*   - S' and T' are used only once for the           *)
  (*     definition of Y', we replace their definition  *)
  (*     by a random assigment                          *)
  (******************************************************)

  Definition Game8 := 
   [
    bad1 <- false;
    LG <- Nil _;
    LH <- Nil _;
    Y' <$- {0,1}^k;
    M <c- A with{};
    b' <c- A' with {Y'}
   ].

  Definition E8 := mkEnv H_body0 G_body7.

  Definition E8' := mkEnv H_body0' G_body7.

  Definition E7' := mkEnv H_body4' G_body7.

  Definition iE8E8' : eq_inv_info trueR E8 E8' := iE_HH' (H_body0_H_body0' E8 E8').
  Definition iE7'E7 :eq_inv_info trueR E7' E7 := iE_HH' (H_body4'_H_body4 E7' E7). 
  Definition iE8E8 : eq_inv_info trueR E8 E8 := iEiEi H_body0 G_body7.

  Lemma EqObs_Game6_Game8 : 
     EqObs Gadv E7 Game7 E8 Game8 (Vset.singleton bad1).
  Proof.
   apply EqObs_sym; apply EqObs_trans with E8 Game7.
   eqobs_ctxt iE8E8; deadcode.
   union_mod.
   unfold EqObs; apply equiv_strengthen with trueR.
   red; trivial.
   refine (sampl_app E8 E8 Y' S' T').

   (* Undo coins fixing *)
   unfold Game7.
   match goal with
   |- EqObs _ _ (?ibad::?iLG::?iLH::?iS'::?iHS'::?c) _ _ _ => 
      apply EqObs_trans with 
       E8' ([ibad; iLG; iLH; iS'] ++ (c ++ [If !(S' in_dom LH) _then [HS' <$- {0,1}^p] ]));
       [ deadcode iE8E8'; eqobs_in iE8E8' 
       | change (ibad::iLG::iLH::iS'::iHS'::c) with ([ibad; iLG; iLH; iS'] ++ (iHS'::c)) ]
   end.
   unfold EqObs; apply equiv_app with
    (req_mem_rel (Vset.add bad1 (Vset.add S' (Vset.add LG (Vset.add LH Gadv))))
      (EP1 (!(S' in_dom LH)))).
   eqobsrel_tail.
   unfold implMR; simpl; unfold O.eval_op; simpl; trivial.
   match goal with
   |- equiv _ _ _ _ ?c _ =>
     apply equiv_trans_eq_mem_l with  (EP1 (!(S' in_dom LH))) E7' c;
     [ | eqobs_in iE7'E7 | intros k m1 m2 (H1, H2); exact H2]
   end.
   apply (@equiv_context_true E8' E7' H_body4 H_body0 _ HS' ({0,1}^p) (!(S' in_dom LH))).
   vm_compute; trivial.
   apply dcontext_correct with (ci := mkCi H_body0' H_body4' G_body7 G_body7
     (If !(S' in_dom LH)then ((HS' <$- {0,1}^p) :: H_body4) else H_body0)
     (If !(S' in_dom LH)then H_body4 else H_body0)
     (Vset.singleton HS')
     (Vset.add HS' (Vset.union (fv_expr (!(S' in_dom LH))) (fv_distr {0,1}^p)))).
   vm_compute; trivial.
   apply H_body0_neg_test.
   apply H_body4_HS'_once.
  Qed.


  (** We should build the adversary for the one way function *)

  Definition Inverter_body := 
   [
    LG <- Nil _;
    LH <- Nil _;
    Y' <- Ye;
    ST' <- Ye;
    M <c- A with{};
    b' <c- A' with {Y'};
    Ye <- ST' 
   ].

  Definition I_res := Ye.
  
  Notation PST' := (Var.Lvar (T.Pair bskmp bsp) 40).
  Notation x := (Var.Lvar bsk 41).
  Notation y := (Var.Lvar bsk 42).

  Definition G_body_Inverter :=
   (If (E.Eexists SHS (apply_f ((Efst SHS) @ (Esnd SHS |x| R)) =?= Y') LH) _then 
    [ PST' <- E.Efind SHS (apply_f ((Efst SHS) @ (Esnd SHS |x| R)) =?= Y') LH;
      ST' <- (Efst PST') @ (Esnd PST' |x| R)])
   :: G_body0.

  Definition EI :=
   add_decl (mkEnv H_body0 G_body_Inverter)
   Inverter I_params (refl_equal true) Inverter_body I_res.

  Definition inv_inverter := EP1 bad1 |-> EP2 (Y' =?= apply_f ST').

  Lemma dep_inv_inverter : 
   depend_only_rel inv_inverter (Vset.union (fv_expr bad1) Vset.empty)
   (Vset.union Vset.empty (fv_expr (Y' =?= apply_f ST'))).
  Proof. 
   unfold inv_inverter; auto. 
  Qed.

  Lemma dec_inv_inverter : decMR inv_inverter.
  Proof. 
   unfold inv_inverter; auto.
  Qed.

  Definition eE8EI : eq_inv_info inv_inverter E8 EI.
   refine (@empty_inv_info inv_inverter _ _ dep_inv_inverter _ dec_inv_inverter E8 EI).
   vm_compute; trivial.
  Defined.

  Lemma G_body_7_G_body_Inverter : 
   EqObsInv inv_inverter (Vset.add R (Vset.add Y' (Vset.add LG (Vset.singleton LH))))
   E8 G_body7 
   EI G_body_Inverter 
   (Vset.add rG (Vset.add LG (Vset.singleton LH))).
  Proof.
   unfold G_body7, G_body_Inverter, EqObsInv.
   apply equiv_cons with
     (req_mem_rel (Vset.add R (Vset.add Y' (Vset.add LG (Vset.singleton LH)))) inv_inverter).
   unfold inv_inverter; eqobsrel_tail.
   unfold implMR, andR, impR, EP1, EP2; simpl; unfold O.eval_op; simpl.
   intros k m1 m2 (H1, H2); split; intros;[ | auto].
   destruct H as (W1, W2); rewrite is_true_existsb in W2.
   unfold find_default.
   match goal with
   |- ?G => match G with context [find ?FF ?LL] => set (F:= FF); set (L:=LL) end end.
   generalize (find_In F L) (find_notIn F L); destruct (find F L); intros.
   rewrite is_true_UTi_eqb; symmetry; rewrite <- is_true_UTi_eqb.
   destruct (H p); trivial.
   destruct W2 as (x, (W2, W3)).
   unfold F in H3; rewrite H3 in W3;[discriminate | trivial | trivial].
   eqobs_in eE8EI.
  Qed.

  Lemma EqAD8I : Eq_adv_decl PrOrcl PrPriv E8 EI.
  Proof.
   red; intros.
   unfold E8, EI, proc_params, proc_body, proc_res.
   generalize (BProc.eqb_spec (BProc.mkP Inverter) (BProc.mkP f0)).
   destruct (BProc.eqb (BProc.mkP Inverter) (BProc.mkP f0)); intros.
   elim H0; rewrite <- H1; simpl; trivial.
   rewrite add_decl_other_mk; trivial.
   refine (EqAD H_body0 G_body7 H_body0 G_body_Inverter f0 H H0).
  Qed.

  Definition iE8EI : eq_inv_info inv_inverter E8 EI :=
   let piH := add_refl_info H eE8EI in
   let piG := add_info G Vset.empty Vset.empty piH G_body_7_G_body_Inverter in
   let piA := add_adv_info_false EqAD8I (A_wf_E _ _) piG in
   let piA' := add_adv_info_false EqAD8I (A'_wf_E _ _) piA in
   piA'.

  Lemma EqADII : Eq_adv_decl PrOrcl PrPriv EI EI.
  Proof.
   red; intros; auto.
  Qed.

  Lemma A_wf_EI : WFAdv PrOrcl PrPriv Gadv Gcomm EI A.
  Proof.
   apply WFAdv_trans with E8.
   red; intros; unfold EI, proc_params.
   rewrite add_decl_other_mk; trivial.
   refine (EqOP _ _ _ _ o H).
   intro Heq; rewrite <- Heq in H; discriminate H.    
   apply EqAD8I.
   intros H; discriminate H.
   intros H; discriminate H.
   unfold E8; apply A_wf_E.
  Qed.

  Lemma A'_wf_EI : WFAdv PrOrcl PrPriv Gadv Gcomm EI A'.
  Proof.
   apply WFAdv_trans with E8.
   red; intros; unfold EI, proc_params.
   rewrite add_decl_other_mk; trivial.
   refine (EqOP _ _ _ _ o H).
   intro Heq; rewrite <- Heq in H; discriminate H.    
   apply EqAD8I.
   intros H; discriminate H.
   intros H; discriminate H.
   unfold E8; apply A'_wf_E.
  Qed.

  Definition iEIEI : eq_inv_info trueR EI EI :=
   let piH := add_refl_info H (empty_info EI EI) in
   let piG := add_refl_info_O G (Vset.add rG (Vset.add ST' (Vset.singleton LG))) Vset.empty Vset.empty piH in
   let piA := add_adv_info_false EqADII A_wf_EI piG in
   let piA' := add_adv_info_false EqADII A'_wf_EI piA in
   piA'.

  Lemma EqObs_Game8_Inverter :
   EqObsRel Gadv trueR 
   E8 Game8 
   EI (G_f x y) 
   Vset.empty (EP1 bad1 |-> EP2 (x =?= apply_finv y)).
  Proof.
   unfold Game8, G_f.
   inline_r iE8EI Inverter.
   ep iE8EI. 
   deadcode iE8EI.
   alloc_r iE8EI y Y'.
   ep iE8EI.
   apply equiv_depend_only_r with
     (E2' := EI) (c2':= 
      [
       LG <- Nil _; 
       LH <- Nil _;
       Y' <$- {0,1}^k; 
       ST' <- Y';
       M <c- A with{}; 
       b' <c- A' with {Y'}
      ] ++ [ y <- Y'; x <- ST' ])
     (X1:=Vset.union Vset.empty (Vset.union (fv_expr bad1) Vset.empty))
     (X2:=Vset.union Vset.empty (Vset.union Vset.empty (fv_expr (x =?= apply_finv y)))); auto.
   swap iEIEI; eqobs_in iEIEI.
   match goal with |- equiv _ _ ?c _ _ _ => change c with (c ++ nil) end.
   apply equiv_app with (req_mem_rel Vset.empty inv_inverter).
   eqobs_tl iE8EI.
   unfold inv_inverter; eqobsrel_tail.
   unfold implMR, andR, impR, EP1, EP2; simpl; unfold O.eval_op; simpl.
   intros; discriminate.
   eqobsrel_tail.
   unfold inv_inverter, implMR, andR, impR, EP1, EP2; simpl; unfold O.eval_op; simpl.
   intros k m1 m2 (H1, H2) H3.
   rewrite is_true_UTi_eqb in H2; rewrite H2;[ | trivial].
   rewrite f_spec.
   refine (@UTi_eqb_refl k BS_k (m2 ST')).
  Qed.


  (**************************************************)
  (*  We now focus on the probalility of bad2       *)
  (*  in game 5                                     *)
  (**************************************************)

  (******************************************************)
  (** Transition 11:  E5, Game5 -> E9, Game9            *)
  (*   + remove bad and bad1, no longer used            *)
  (*   + introduce bad3 and bad4 in H                   *)
  (******************************************************)

  Definition H_body_gen i1 i2 :=
   [
    If !(S in_dom LH) 
    then [
         If S =?= S' 
         then [
              If bad2 
              then [bad3 <- true; bad2 <- true; i1]
              else [bad4 <- true; i2]
              ] 
         else [ rH <$- {0,1}^p ];
         LH <- (S | rH) |::| LH
         ] 
    else [ rH <- LH[{S}] ]
   ].

  Definition H_body9 := H_body_gen (rH <- HS') (rH <- HS').
  
  Definition G_body9 := 
   (If R =?= R'
    _then [If S' in_dom LH then nil else [bad2 <- true] ])
   :: G_body0.

  Definition E9 := mkEnv H_body9 G_body9.

  Definition iE5E9 :=
    let A'loss := @A'_lossless H_body4 G_body5 in
    let A'loss' := @A'_lossless H_body9 G_body9 in
    let Aloss := @A_lossless H_body4 G_body5 in
    let Aloss' := @A_lossless H_body9 G_body9 in
    let piH := add_refl_info_O H (Vset.add LH (Vset.add rH (Vset.singleton bad2))) 
     Vset.empty (Vset.add bad3 (Vset.singleton bad4)) (empty_info E5 E9) in
    let piG := add_refl_info_rm G (Vset.add bad1 (Vset.singleton bad)) Vset.empty piH in
    let piA := add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _) Aloss Aloss' piG in
    add_adv_info_lossless (EqAD _ _ _ _) (A'_wf_E _ _) A'loss A'loss' piA.

  Definition Game9_ :=
   [
    LG <- Nil _;
    LH <- Nil _;
    S' <$- {0,1}^k-p;
    R' <$- {0,1}^p;
    HS' <$- {0,1}^p;
    T' <- HS' |x| R';
    Y' <- apply_f S' @ T';
    M <c- A with{};
    b' <c- A' with {Y'}
   ].

  Definition Game9 :=
   (bad2 <- false) :: (bad3 <- false) :: (bad4 <- false) :: Game9_.

  Definition H_body10 := H_body_gen (rH <$- {0,1}^p) (rH <- HS').

  Definition E10 := mkEnv H_body10 G_body9.

  Definition inv_bad42 := EP1 (bad4 ==> ((S' in_dom LH) && !bad2)).
  
  Lemma dep_inv_bad42 : depend_only_rel inv_bad42 
   (fv_expr (bad4 ==> ((S' in_dom LH) && !bad2))) Vset.empty.
  Proof. 
   unfold inv_bad42; auto. 
  Qed.

  Lemma dec_inv_bad42 : decMR inv_bad42.
  Proof. 
   unfold inv_bad42; auto. 
  Qed.

  Lemma G_body9_bad42 : forall E E',
   EqObsInv inv_bad42 
   (Vset.add R (Vset.add R' (Vset.add S' (Vset.add LH (Vset.add LG (Vset.singleton bad2))))))
   E G_body9 
   E' G_body9 
   (Vset.add rG (Vset.add LG (Vset.singleton bad2))).
  Proof.
   intros; unfold inv_bad42; eqobsrel_tail.
   unfold implMR, andR, EP1; simpl; unfold O.eval_op; simpl;
   intros k m1 m2 (H1, H2); split; intros; auto.
   split; intros; auto.
   split; intros.
   rewrite is_true_impb; intros Heq.
   rewrite Heq in H2; unfold impb in H2; simpl in H2; rewrite is_true_andb in H2.
   destruct H2; destruct H0 as (H0, _); elim H0; trivial.
   rewrite is_true_impb; intros Heq.
   rewrite Heq in H2; unfold impb in H2; simpl in H2; rewrite is_true_andb in H2.
   destruct H2; destruct H0 as (H0, _); elim H0; trivial.
  Qed.
  
  Definition iE_bad42 Hbody I O 
   (Hbody_bad42 : EqObsInv inv_bad42 I(mkEnv Hbody G_body9) Hbody (mkEnv Hbody G_body9) Hbody O) :=
   let E := mkEnv Hbody G_body9 in
   let e_bad42 := 
     @empty_inv_info inv_bad42 _ _ dep_inv_bad42 (refl_equal true) dec_inv_bad42 E E in
   iEinv e_bad42 Hbody_bad42 (G_body9_bad42 E E).

  Lemma H_body10_bad42 :
   EqObsInv inv_bad42 
   (Vset.add HS' (Vset.add S (Vset.add S' (Vset.add LH 
    (Vset.add bad3 (Vset.add bad4 (Vset.singleton bad2)))))))
   E10 H_body10 
   E10 H_body10
   (Vset.add rH (Vset.add S' (Vset.add LH 
    (Vset.add bad3 (Vset.add bad4 (Vset.singleton bad2)))))).
  Proof.
   intros; unfold inv_bad42; eqobsrel_tail.
   unfold implMR, andR, EP1; simpl; unfold O.eval_op; simpl;
   intros k m1 m2 (H1, H2); split; intros; trivial.
   split; intros (H3, H4).
   rewrite is_true_UTi_eqb in H3; rewrite H3.
   rewrite UTi_eqb_refl; simpl.
   split; intros (H5, H6); intros.
   rewrite is_true_impb; intros Heq; rewrite Heq in H2; unfold impb in H2; simpl in H2.
   rewrite is_true_andb in H2; destruct H2; rewrite is_true_negb in H7.
   elim H7; trivial.
   unfold impb; simpl; rewrite is_true_negb; trivial.
   intros; rewrite is_true_impb; intros Heq; rewrite Heq in H2; unfold impb in H2; simpl in H2.
   rewrite is_true_andb in H2; destruct H2.
   rewrite H2, orb_true_r; trivial.
  Qed.

  Definition iE10_42 : eq_inv_info inv_bad42 E10 E10 := iE_bad42 H_body10_bad42.

  (*****************************************)

  Definition H_body11 := H_body_gen (rH <$- {0,1}^p) (rH <$- {0,1}^p).

  Definition E11 := mkEnv H_body11 G_body9.

  Lemma H_body11_bad42 : 
   EqObsInv inv_bad42 
   (Vset.add HS' (Vset.add S (Vset.add S' (Vset.add LH 
    (Vset.add bad3 (Vset.add bad4 (Vset.singleton bad2)))))))
   E11 H_body11 
   E11 H_body11
   (Vset.add rH (Vset.add S' (Vset.add LH 
    (Vset.add bad3 (Vset.add bad4 (Vset.singleton bad2)))))).
  Proof.
   intros; unfold inv_bad42; eqobsrel_tail.
   unfold implMR, andR, EP1; simpl; unfold O.eval_op; simpl;
    intros k m1 m2 (H1, H2); split; intros; trivial.
   split; intros (H3, H4).
   rewrite is_true_UTi_eqb in H3; rewrite H3.
   rewrite UTi_eqb_refl; simpl.
   split; intros (H5, H6); intros.
   rewrite is_true_impb; intros Heq; rewrite Heq in H2; unfold impb in H2; simpl in H2.
   rewrite is_true_andb in H2; destruct H2; rewrite is_true_negb in H7.
   elim H7; trivial.
   unfold impb; simpl; rewrite is_true_negb; trivial.
   intros; rewrite is_true_impb; intros Heq; rewrite Heq in H2; unfold impb in H2; simpl in H2.
   rewrite is_true_andb in H2; destruct H2.
   rewrite H2, orb_true_r; trivial.
  Qed.
  
  Definition iE11_42 : eq_inv_info inv_bad42 E11 E11 := iE_bad42 H_body11_bad42.

  Lemma bad2_Game5_Game11 : forall k (m:Mem.t k),
   Pr E5 Game5 m (EP k bad2) == Pr E11 Game9 m (EP k bad2).
  Proof.
   intros; transitivity (Pr E9 Game9 m (EP k bad2)).
   apply EqObs_Pr with Gadv.
   deadcode iE5E9; eqobs_in iE5E9.
   unfold Game9, Pr.
   repeat 
    (setoid_rewrite deno_cons_elim;
     setoid_rewrite Mlet_simpl;
     setoid_rewrite deno_assign_elim).
   unfold E.eval_expr, E.eval_cexpr.
   set (mbad:=m {!bad2 <-- false!} {!bad3 <-- false!} {!bad4 <-- false!}).
   change (Pr E9 Game9_ mbad (EP k bad2) == Pr E11 Game9_ mbad (EP k bad2)).

   setoid_rewrite (@upto_bad_bad bad2 (refl_equal true)  
    E9 E10 (i_upto bad2 H_body9 H_body10 G_body9 G_body9) Game9_ Game9_).

   (* We split the probability in E10 in two *)
   eapply Oeq_trans.
   apply (Pr_split E10 Game9_ mbad (EP k bad4) (EP k bad2)).
   (* Up to bad with E10 *)
   rewrite (@upto_bad_and_neg bad4 (refl_equal true)  
              E10 E11 (i_upto bad4 H_body10 H_body11 G_body9 G_body9) Game9_ Game9_).
   (* Since bad4 => ! bad2 in E10 we have : *)
   assert (Pr E10 Game9_ mbad (EP k bad2 [&&] EP k bad4) == 0).
     symmetry; unfold Pr.
     assert (range (fun m => EP k (bad4 ==> ((S' in_dom LH) && !bad2)) m) ([[Game9_]] E10 mbad)).
       apply charfun_range.
       apply equiv_deno with
       (req_mem_rel (Vset.add bad2 (Vset.add bad3 (Vset.add bad4 Gadv))) (EP1 (! bad4))) 
       (req_mem_rel (Vset.singleton bad4) inv_bad42).
       eqobs_tl iE10_42.
       eqobsrel_tail.
       unfold implMR,andR,impR, inv_bad42, EP1,EP2; simpl; unfold O.eval_op; simpl.
       intros k0 m1 m2 (H1, H2) v _;
       repeat (repeat rewrite Mem.get_upd_same; rewrite Mem.get_upd_diff;[ | intro; discriminate];
             repeat rewrite Mem.get_upd_same); trivial.
       rewrite is_true_negb_false in H2; rewrite H2; trivial.
       intros m1 m2; unfold req_mem_rel, inv_bad42, andR, charfun,restr, EP, EP1; intros (H1, H2).
       rewrite H2; trivial.
       split; trivial.
       red; simpl; unfold O.eval_op; simpl; unfold mbad; rewrite Mem.get_upd_same; trivial.
     apply H; unfold EP, charfun, restr, andP; simpl; unfold O.eval_op; simpl; intros.
     destruct (x bad4).
     unfold impb in H0; simpl in H0; rewrite is_true_andb in H0; destruct H0.
     rewrite is_true_negb_false in H1; rewrite H1; trivial.
     rewrite andb_false_r; trivial.
   rewrite H; clear H.

   (* Since bad4 => ! bad2 in E11 we have : *)
   assert (Pr E11 Game9_ mbad (EP k bad2 [&&] EP k bad4) == 0).
     symmetry; unfold Pr.
     assert (range (fun m => EP k (bad4 ==> ((S' in_dom LH) && !bad2)) m) ([[Game9_]] E11 mbad)).
       apply charfun_range.
       apply equiv_deno with
       (req_mem_rel (Vset.add bad2 (Vset.add bad3 (Vset.add bad4 Gadv))) (EP1 (! bad4))) 
       (req_mem_rel (Vset.singleton bad4) inv_bad42).
       eqobs_tl iE11_42.
       eqobsrel_tail.
       unfold implMR,andR,impR, inv_bad42, EP1,EP2; simpl; unfold O.eval_op; simpl.
       intros k0 m1 m2 (H1, H2) v _;
       repeat (repeat rewrite Mem.get_upd_same; rewrite Mem.get_upd_diff;[ | intro; discriminate];
             repeat rewrite Mem.get_upd_same); trivial.
       rewrite is_true_negb_false in H2; rewrite H2; trivial.
       intros m1 m2; unfold req_mem_rel, inv_bad42, andR, charfun,restr, EP, EP1; intros (H1, H2).
       rewrite H2; trivial.
       split; trivial.
       red; simpl; unfold O.eval_op; simpl; unfold mbad; rewrite Mem.get_upd_same; trivial.
     apply H; unfold EP, charfun, restr, andP; simpl; unfold O.eval_op; simpl; intros.
     destruct (x bad4).
     unfold impb in H0; simpl in H0; rewrite is_true_andb in H0; destruct H0.
     rewrite is_true_negb_false in H1; rewrite H1; trivial.
     rewrite andb_false_r; trivial.
   rewrite <- H; clear H.
   symmetry; apply Pr_split.
   vm_compute; trivial.
   vm_compute; trivial.
   apply is_lossless_correct with (refl2_info iE5E9); vm_compute; trivial.
   apply is_lossless_correct with (refl1_info iE10_42); vm_compute; trivial. 
  Qed.

  (**************************************)

  Definition inv_bad_in := EP1 (bad2) |-> EP2 (R' in_dom LG).

  Lemma dep_inv_bad_in : depend_only_rel inv_bad_in 
   (fv_expr bad2) (fv_expr (R' in_dom LG)).
  Proof. 
   unfold inv_bad_in.
   assert_depend_only (empty_info E0 E0) (EP1 (bad2) |-> EP2 (R' in_dom LG)).
   exact Hdep.
  Qed.

  Lemma dec_inv_bad_in : decMR inv_bad_in.
  Proof. 
   unfold inv_bad_in; auto. 
  Qed.

  Definition eE11E0 : eq_inv_info inv_bad_in E11 E0 :=
   @empty_inv_info inv_bad_in _ _ dep_inv_bad_in (refl_equal true) dec_inv_bad_in E11 E0.

  Lemma G_body9_G_body0 : 
   EqObsInv inv_bad_in 
   (Vset.add R (Vset.add R' (Vset.singleton LG)))
   E11 G_body9 
   E0 G_body0
   (Vset.add rG (Vset.singleton LG)).
  Proof.
   unfold G_body9.
   cp_test (R =?= R').
   cp_test_l (S' in_dom LH).
   repeat rewrite proj1_MR; unfold inv_bad_in; eqobsrel_tail.
   unfold implMR,andR,impR,EP1,EP2; simpl; unfold O.eval_op; simpl; intros.
   destruct H; split; intros;[ | auto].
   rewrite UTi_eqb_refl; trivial.
   repeat rewrite proj1_MR; unfold inv_bad_in; eqobsrel_tail.
   unfold implMR,andR,impR,EP1,EP2; simpl; unfold O.eval_op; simpl; intros.
   destruct H; split; intros.
   rewrite UTi_eqb_refl; trivial.
   destruct H1.
   rewrite <- is_true_negb, negb_involutive in H3; trivial.
   unfold inv_bad_in; eqobsrel_tail.
   unfold implMR,andR,impR,EP1,EP2; simpl; unfold O.eval_op; simpl; intros.
   destruct H; split; intros.
   destruct H0 as (H0, _); rewrite H0; trivial.
   rewrite orb_true_r; trivial.
   destruct H0 as (H0, _); rewrite H0; trivial.
  Qed.

  Definition iE11E0 : eq_inv_info inv_bad_in E11 E0 :=
   let A'loss := @A'_lossless H_body11 G_body9 in
   let A'loss' := @A'_lossless H_body0 G_body0 in
   let Aloss := @A_lossless H_body11 G_body9 in
   let Aloss' := @A_lossless H_body0 G_body0 in
   let piH := add_refl_info_O H (Vset.add LH (Vset.singleton rH)) (Vset.add bad3 (Vset.singleton bad4)) Vset.empty eE11E0 in
   let piG := add_info G Vset.empty Vset.empty piH G_body9_G_body0 in
   let piEnc := add_refl_info Enc piG in 
   let piA := add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _) Aloss Aloss' piEnc in
   add_adv_info_lossless (EqAD _ _ _ _) (A'_wf_E _ _) A'loss A'loss' piA.

  Definition Game12 :=
   [ 
     Y' <$- {0,1}^k;
     LG <- Nil _;
     LH <- Nil _;
     M <c- A with{};
     b' <c- A' with {Y'};
     R' <$- {0,1}^p 
   ].

  Lemma EqObs_Game9_Game12 : 
   EqObsRel Gadv trueR 
   E11 Game9 
   E0 Game12 
   Vset.empty inv_bad_in.
  Proof.
   unfold Game9, Game9_, Game12.
   deadcode iE11E0.
   apply equiv_depend_only_r with
    (E2' := E0) (c2':= Game9)
    (X1 := Vset.union Vset.empty (Vset.union (fv_expr bad2) Vset.empty))
    (X2 := Vset.union Vset.empty (Vset.union Vset.empty (fv_expr (R' in_dom LG)))); auto.
   unfold inv_bad_in; auto.
   unfold Game9, Game9_.
   deadcode iE0E0.
   swap iE0E0.
   eqobs_tl iE0E0.
   equiv_trans E0 [R' <$- {0,1}^p;Y' <$- {0,1}^k].
   swap; eqobs_in.
   equiv_trans E0 [R' <$- {0,1}^p; S' <$- {0,1}^k-p;
   T' <$- {0,1}^p; HS' <- T' |x| R'; Y' <- apply_f S' @ T' ].
   apply equiv_strengthen with (kreq_mem Gadv);[unfold Meq; intros; subst; trivial | ].
   eqobs_hd; deadcode.
   union_mod.
   unfold EqObs; apply equiv_strengthen with trueR; [red; trivial|]. 
   refine (sampl_app E0 E0 Y' S' T').
   swap.
   eqobs_tl.
   apply equiv_weaken with Meq.
   unfold Meq; intros; subst; trivial.
   apply equiv_cons with Meq;[ apply equiv_eq_mem | ].
   equiv_trans E0 [T' <$- {0,1}^p; HS' <- R' |x| T'].
   apply equiv_cons with Meq;[ apply equiv_eq_mem | ].
   ep_eq_l (T' |x| R') (R'|x| T').
   unfold Meq; intros; subst; simpl; unfold O.eval_op; simpl.
   refine (BVxor_comm _ _).
   union_mod; auto.
   eqobs_in.
   equiv_trans E0 [HS' <$- {0,1}^p; T' <- R' |x| HS'].
   apply optim_sampl_p; intro; discriminate.
   apply equiv_cons with Meq;[ apply equiv_eq_mem | ].
   ep_eq_l (R' |x| HS') (HS'|x| R').
   unfold Meq; intros; subst; simpl; unfold O.eval_op; simpl.
   refine (BVxor_comm _ _).
   union_mod; auto.
   eqobs_in.
   eqobs_tl iE11E0.
   unfold inv_bad_in; eqobsrel_tail.
   unfold implMR; simpl; unfold O.eval_op; simpl; trivial.
  Qed.

  Lemma Pr_12 : forall k m,
   Pr E0 Game12 m (EP k (R' in_dom LG)) <= peval qG_poly k */ [1/2]^(k_p k).
  Proof.
   intros k m.
   transitivity (sigma (fun _ => [1/2]^(k_p k)) (peval qG_poly k));
   [ | apply Oeq_le; symmetry; apply Nmult_sigma].
   change Game12 with  (((Y' <$- {0,1}^k)::Game12_) ++ [R' <$- {0,1}^p]).
   unfold Pr.
   rewrite deno_app_elim.
   transitivity 
    (mu (([[(Y' <$- {0,1}^k) :: Game12_]]) E0 m) 
     (fcte _ (sigma (fun _ : nat => [1/2] ^ k_p k) (peval qG_poly k)))).
   transitivity 
    (mu (([[(Y' <$- {0,1}^k) :: Game12_]]) E0 m)
     (fun mn' : Mem.t k =>
        if Compare_dec.leb (length (mn' LG)) (peval qG_poly k) 
        then mu (([[ [R' <$- {0,1}^p] ]]) E0 mn') (charfun (EP k (R' in_dom LG)))
        else 0)).
   assert (range (fun (m':Mem.t k) => List.length (m' LG)  <= peval qG_poly k)%nat 
                     ([[(Y' <$- {0,1}^k) ::Game12_]] E0 m)).
     rewrite deno_cons.
     apply range_Mlet with (fun _ => True).
     apply range_True.
     intros m' _; apply range_G_query.
   apply range_le with (1:= H).
   intros; rewrite leb_correct; trivial.
   apply mu_monotonic.
   clear m; intro m'.
   match goal with |- (if Compare_dec.leb ?X ?Y then _ else _) <= _ => 
     set (L:= X); case_eq (Compare_dec.leb L Y); intros; trivial end.
   apply Compare_dec.leb_complete in H; unfold fcte.
   transitivity 
    (mu (([[[R' <$- {0,1}^p] ]]) E0 m')
      (sigma_fun 
       (fun n => charfun 
         (fun (m:Mem.t k) => 
           UT.i_eqb (m R') (fst (nth n (m LG) (T.default k (T.Pair bsp bskmp)))))) 
       L)).
   assert (Modify E0 (Vset.singleton R') [R' <$- {0,1}^p] ).
   apply modify_correct with (refl1_info iE0E0) Vset.empty; trivial.
   rewrite (Modify_deno_elim H0).
   match goal with |- ?X <= _ => set (W:= X); rewrite (Modify_deno_elim H0); unfold W; clear W end.
   apply mu_monotonic; intro; simpl.
   unfold charfun, restr, EP.
   simpl; unfold O.eval_op; simpl.
   unfold sigma_fun, fone.
   rewrite Mem.get_upd_same, Mem.get_upd_diff; [ | intro; discriminate].
   unfold L; rewrite
    (sigma_finite_sum (UT.default k BS_p, UT.default k BS_kmp)
     (fun a => if UT.i_eqb (x R') (fst a) then 1 else 0)).
   clear H L; induction (m' LG); simpl; trivial.
   destruct (UT.i_eqb (x R') (fst a)); simpl; Usimpl; trivial.
   rewrite mu_sigma_le.
   transitivity (sigma (fun _ : nat => [1/2] ^ k_p k) L).
   apply sigma_le_compat.
   intros; rewrite deno_random_elim.
   unfold E.eval_support, US.eval.

   eapply Ole_eq_left with
    (mu (sum_support (T.default k bsp) (bs_support (UT.length k BS_p)))
     (fun v =>
      if OAEPS.UT.i_eqb v
       (fst (nth k0 (m' LG) (T.default k (T.Pair bsp bskmp))))
       then fone (Mem.t k) (m' {!R' <-- v!})
       else 0)).
   apply mu_stable_eq.
   refine (ford_eq_intro _); intro v.
   unfold charfun, restr.
   rewrite Mem.get_upd_same, Mem.get_upd_diff; [ trivial | discriminate].
   rewrite (@Pr_bs_support (UT.length k BS_p) (T.default k bsp)
    (fst (nth k0 (m' LG) (T.default k (T.Pair bsp bskmp))))
    (fun x v => if OAEPS.UT.i_eqb v x   
     then fone (Mem.t k) (m' {!R' <-- v!})
     else 0)); trivial.

   intros.
   match goal with 
    |- (if UT.i_eqb ?X ?Y then _ else _) == _ =>
      generalize (UT.i_eqb_spec X Y); destruct (UT.i_eqb X Y)
   end.
   intro; elim (H1 H2).   
   trivial.
   rewrite UTi_eqb_refl; trivial.
   apply sigma_incr; trivial.
   apply mu_cte_le.
  Qed.


  (**************************************************)
  (*             The final proof                    *)
  (**************************************************)
 
  Lemma OAEP_exact_security : forall k m, 
   Uabs_diff (Pr E0 Game0 m (EP k (b =?=b'))) [1/2] <=
   Pr EI (G_f x y) m (EP k (x =?= apply_finv y)) + (peval qG_poly k */ [1/2]^(k_p k)).
  Proof.
   intros.
   set (mbad:=m{!bad <-- false!}).
   assert (Hbad:forall E A, Pr E Game2 m A == Pr E Game2_ mbad A).
   unfold Pr at 1; unfold Game2; intros.
   rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim; trivial.
   
   transitivity (Pr E3 Game2_ mbad (EP k bad)).
    (* Apply upto_bad *)
   assert (Pr E0 Game0 m (EP k (b =?=b')) == Pr E2 Game2_ mbad (EP k (b =?=b'))).
     apply EqObs_Pr2 with Gadv (fv_expr (b=?=b')).
     apply EqObs_trans with (1:= EqObs_Game0_Game1) (2:=EqObs_Game1_Game2).
     auto with set.
     unfold Gadv, mbad; red; intros.
     apply Vset.singleton_complete in H; inversion H; simpl.
     rewrite Mem.get_upd_diff; trivial; intro; discriminate.
   rewrite H; clear H.
   assert (Pr E3 Game2_ mbad (EP k (b=?=b')) == [1/2]).
     rewrite <- Hbad.
     transitivity (Pr E3 Game3 m(EP k (b=?=b'))).
     apply EqObs_Pr2 with (1:= EqObs_Game2_Game3); auto with set.
     unfold Game3; apply Pr_sample_bool.
     intros; discriminate.
     apply is_lossless_correct with (refl1_info iE3E3); vm_compute; trivial.

   eapply Ole_eq_left.
   eapply Uabs_diff_morphism; [reflexivity | symmetry; eexact H]; clear H.
   apply upto_bad_Uabs_diff with (i_upto bad H_body0 H_body0 G_body2 G_body3).
   trivial.
   vm_compute; trivial.
   apply is_lossless_correct with (refl1_info iE3E3); vm_compute; trivial.
   rewrite <- Hbad; clear Hbad.
   (* Go to the split point : E5, Game5 *)
   assert (Pr E3 Game2 m (EP k bad) == Pr E5 Game5 m (EP k bad)).
     transitivity (Pr E3 Game3 m (EP k bad)).
     apply EqObs_Pr2 with (1:= EqObs_Game2_Game3); trivial.
     vm_compute; trivial.
     apply EqObs_Pr with Gadv.
     apply EqObs_trans with (1:= EqObs_Game3_Game4).
     apply EqObs_trans with (1:=EqObs_Game4_Game4_) (2:= EqObs_Game4_Game5).
   rewrite H; clear H.
   eapply Ole_trans; [apply split_bad | ].
   apply Uplus_le_compat.

   (* less than the probability of the inverter *)
   transitivity (Pr E8 Game8 m (EP k bad1)).
   apply Oeq_le.
   apply EqObs_Pr with Gadv.
   apply EqObs_trans with (1:=EqObs_Game5_Game6).
   apply EqObs_trans with (1:=Game6_Game7) (2:=EqObs_Game6_Game8).

   unfold Pr; apply equiv_deno_le with (1:= EqObs_Game8_Inverter).
   intros m1 m2; unfold req_mem_rel, andR, impR, EP1, EP2, EP, charfun, restr.
   intros (H1, H2); destruct (E.eval_expr bad1 m1); trivial.
   rewrite H2; trivial.
   unfold req_mem_rel, andR, trueR; auto.

   (* If bad is set only when S' is not in LH then *)
   eapply Ole_trans; [ | apply Pr_12 with (m:=m)].
   transitivity (Pr E11 Game9 m (EP k bad2)).
   apply Oeq_le; apply bad2_Game5_Game11.
   unfold Pr; apply equiv_deno_le with (1:= EqObs_Game9_Game12). 
   intros m1 m2; unfold req_mem_rel, inv_bad_in, andR, impR, EP1, EP2, EP, charfun, restr.
   intros (H1, H2); destruct (E.eval_expr bad2 m1); trivial.
   rewrite H2; trivial.
   unfold req_mem_rel, andR, trueR; auto.
  Qed.

  Lemma EqAD_0I : Eq_adv_decl PrOrcl PrPriv E0 EI.
  Proof.
   unfold Eq_adv_decl, EI, E0, mkEnv, proc_params, proc_body, proc_res; intros.
   generalize (BProc.eqb_spec (BProc.mkP A') (BProc.mkP f0)).
   destruct (BProc.eqb (BProc.mkP A') (BProc.mkP f0)); intros.
   inversion H1; simpl; auto.
   generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f0)).
   destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f0)); intros.
   inversion H2; simpl; auto.
   repeat rewrite add_decl_other_mk; try tauto; intro Heq;
    try (apply H; rewrite <- Heq; vm_compute; trivial; fail);
    apply H0; rewrite <- Heq; vm_compute; trivial.
  Qed.
 
  Definition pi : PPT_info EI :=
   PPT_add_adv_infob EqAD_0I A'_PPT
   (PPT_add_adv_infob EqAD_0I A_PPT
    (PPT_add_info 
     (PPT_add_info 
      (PPT_add_info (PPT_empty_info EI) H) G) Enc)).

  Lemma EqAD0I : Eq_adv_decl PrOrcl PrPriv E0 EI.
  Proof.
   red; intros.
   unfold E0, EI, proc_params, proc_body, proc_res.
   generalize (BProc.eqb_spec (BProc.mkP Inverter) (BProc.mkP f0)).
   destruct (BProc.eqb (BProc.mkP Inverter) (BProc.mkP f0)); intros.
   elim H0; rewrite <- H1; simpl; trivial.
   rewrite add_decl_other_mk; trivial.
   refine (EqAD H_body0 G_body0 H_body0 G_body_Inverter f0 H H0).
  Qed.

  Definition iE0EI : eq_inv_info trueR E0 EI :=
   let piH := add_refl_info H (empty_info _ _) in
   let piG := add_refl_info G piH in
   let piA := add_adv_info_false EqAD0I (A_wf_E _ _) piG in
   let piA' := add_adv_info_false EqAD0I (A'_wf_E _ _) piA in
   piA'.

  Lemma OAEP_semantic_security : forall m,
   negligible (fun k => Uabs_diff (Pr E0 Game0 (m k) (EP k (b =?=b'))) [1/2]).
  Proof.
   intro m.
   apply negligible_le_stable with 
    (fun k => Pr EI (G_f x y) (m k) (EP k (x =?= apply_finv y)) + (peval qG_poly k */ [1/2]^(k_p k))).
   intro n; apply OAEP_exact_security.
   apply negligible_plus_stable.
   apply f_oneway.
   discriminate. 
   trivial.
   trivial.
   PPT_proc_tac pi.
   red; intros.
   transitivity (mu ([[proc_body EI Inverter]] E0 m0) (fun _ => 1)).
   apply EqObs_deno with (Vset.add Ye (Vset.singleton g_a)) Vset.empty; trivial.
   apply EqObs_sym; eqobs_in iE0EI.
   apply is_lossless_correct with (refl1_info iE0E0); vm_compute; trivial.
   apply negligible_qG_2p.
  Qed.

 End ADVERSARY_AND_PROOF.

End Make.
