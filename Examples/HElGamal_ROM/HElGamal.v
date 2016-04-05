(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * HElGamal.v : Semantic security of the Hashed ElGamal encryption scheme 
   in the Random Oracle Model *)

Set Implicit Arguments.

Require Import SemHElGamal.


(** TODO: Move this somewhere else *)
Lemma CGK_eqb_refl : forall k v, (@CGK.eqb k v v) = true.
Proof.
 intros k v; generalize (CGK.eqb_spec v v); case (CGK.eqb v v).
 trivial.
 intro H; elim H; trivial.
Qed.

Lemma CGK_eqb_sym : forall k v1 v2, 
 @CGK.eqb k v1 v2 <-> @CGK.eqb k v2 v1.
Proof.
 intros k v1 v2.
 split;
  generalize (CGK.eqb_spec v1 v2); generalize (CGK.eqb_spec v2 v1);
  case (CGK.eqb v1 v2); case (CGK.eqb v2 v1);
  intros H1 H2; trivial.
 elim H1; symmetry; trivial.
 elim H2; symmetry; trivial.
Qed.

Lemma is_true_CGK_eqb : forall k v1 v2, 
 @CGK.eqb k v1 v2 <-> v1 = v2.
Proof.
 split; intros.
 generalize (CGK.eqb_spec v1 v2); rewrite H; trivial.
 rewrite H; apply CGK_eqb_refl.
Qed.

Lemma modus_ponens : forall k (m:Mem.t k) e1 e2,
 E.eval_expr (e1 ==> e2) m ->
 E.eval_expr e1 m ->
 E.eval_expr e2 m.
Proof.
 intros.
 unfold E.eval_expr, O.eval_op in H, H0; simpl in H, H0.
 rewrite H0 in H; trivial.
Qed.
(* TODO : This lemma is eval_expr_eq *)
Lemma eval_eq : forall k (m:Mem.t k) (t:T.type) e1 e2,
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


(** ** List CDH assumption *) 
Section LIST_CDH_ASSUMPTION.

 (** The list CDH assumption says that any efficient adversary [C] has a 
    negligible chance of outputting a list containing [g^xy] given 
    [g^x] and [g^y], where [x] and [y] are uniformly sampled. 
 *)

 Variables x y : Var.var T.Nat.
 Variable L : Var.var (T.List (T.Pair (T.User Group) (T.User Bitstring))).
 Variable Cname : positive.

 Notation Local C := (Proc.mkP Cname 
   (T.User Group :: T.User Group :: nil) 
   (T.List (T.Pair (T.User Group) (T.User Bitstring)))).

 Definition LCDH :=
  [
   x <$- [0..q-!1];
   y <$- [0..q-!1];
   L <c- C with {g^x, g^y}
  ].

 Definition LCDH_advantage E k (m:Mem.t k) := 
  Pr E LCDH m (EP k (g^(x *! y) in_dom L)).
 
 Axiom LCDH_assumption : forall (m:forall k, Mem.t k) E,
  x <> y ->
  Var.is_local x ->
  Var.is_local y ->
  lossless E (proc_body E C) ->
  PPT_proc E C ->
  negligible (fun k => LCDH_advantage E (m k)).

End LIST_CDH_ASSUMPTION.


Open Scope positive_scope.

(** ** Global Variables *)

Notation L   := (Var.Gvar (T.List (T.Pair (T.User Group) (T.User Bitstring))) 1).
Notation Lam := (Var.Gvar (T.User Group) 2).
Notation hp  := (Var.Gvar (T.User Bitstring) 3).
Notation bad := (Var.Gvar T.Bool 4).
Notation L'   := (Var.Gvar (T.List (T.Pair (T.User Group) (T.User Bitstring))) 5).

(** *** Global variables shared between the adversary, the oracles and 
  the game *)
Definition Gcomm := Vset.empty.

(** Global variable shared between [A] and [A'] *)
Notation g_a := (Var.Gvar T.Nat 5).

Definition Gadv := Vset.singleton g_a.


(** ** Local variables *)

(** Integer variables *)
Notation x := (Var.Lvar T.Nat 11).
Notation y := (Var.Lvar T.Nat 12).

(** Bitstrings *)
Notation h := (Var.Lvar (T.User Bitstring) 21).
Notation r := (Var.Lvar (T.User Bitstring) 22).
Notation v := (Var.Lvar (T.User Bitstring) 23).

(** Group elements *)
Notation alpha  := (Var.Lvar (T.User Group) 31).
Notation beta   := (Var.Lvar (T.User Group) 32).
Notation lambda := (Var.Lvar (T.User Group) 33).

(** Messages *)
Notation mm := (Var.Lvar (T.Pair (T.User Bitstring) (T.User Bitstring)) 41).
Notation mb := (Var.Lvar (T.User Bitstring) 42).

(** Bits *)
Notation b  := (Var.Gvar T.Bool 51).
Notation b' := (Var.Lvar T.Bool 52).

(** ** Procedures *)
Notation Hash := (Proc.mkP 1 
 (T.User Group :: nil) 
 (T.User Bitstring)).

Notation A    := (Proc.mkP 2 
 (T.User Group :: nil) 
 (T.Pair (T.User Bitstring) (T.User Bitstring))).

Notation A'   := (Proc.mkP 3 
 (T.User Group :: T.User Group :: T.User Bitstring :: nil) 
 T.Bool).

Notation C    := (Proc.mkP 4 
 (T.User Group :: T.User Group :: nil) 
 (T.List (T.Pair (T.User Group) (T.User Bitstring)))).

Close Scope positive_scope.


(** ** Adversary and proof *)
Section ADVERSARY_AND_PROOF.
 
 Variable env_adv : env.
 
 (** *** Specification of the adversary *)
 Definition A_params : var_decl (Proc.targs A) := dcons _ alpha (dnil _).

 Variable A_body : cmd.
 
 (** [A] returns a pair of messages *)
 Variable A_ret : E.expr (T.Pair (T.User Bitstring) (T.User Bitstring)).
  
 Definition A'_params : var_decl (Proc.targs A') :=
  dcons _ alpha (dcons _ beta (dcons _ v (dnil _))).

 Variable A'_body : cmd.

 (** [A'] returns a guess for [b], a boolean *)
 Variable A'_ret : E.expr T.Bool.
 
 Definition Hash_params : var_decl (Proc.targs Hash) := dcons _ lambda (dnil _).

 Definition Hash_ret := r.

 Definition makeEnv (Hash_body:cmd) :=  
  let EHash := add_decl env_adv Hash Hash_params (refl_equal true) 
   Hash_body Hash_ret in 
  let EA    := add_decl EHash A A_params (refl_equal true) A_body A_ret in
   add_decl EA A' A'_params (refl_equal true) A'_body A'_ret. 


 (** Initial game *)
 Definition G0 :=
  [
   L <- Nil _;
   x <$- [0..q-!1];
   y <$- [0..q-!1];
   mm <c- A with {g^x};
   b <$- {0,1};
   If b then [ mb <- Efst mm ] else [ mb <- Esnd mm ];  
   h <c- Hash with {g^(x *! y)};
   v <- h |x| mb;
   b' <c- A' with {g^x, g^y, v}
  ].

 Definition Hash0_body :=
  [ 
   If !(lambda in_dom L) then 
    [ 
     r <$- {0,1}^k; 
     L <- (lambda | r) |::| L
    ]
   else 
    [
     r <- L[{lambda}]
    ]
  ].

 Definition E0 := makeEnv Hash0_body.

 (** The set of oracles that can be called by [A] and [A'] *)
 Definition PrOrcl := PrSet.singleton (BProc.mkP Hash).

 (** Private procedures, not accessible to the adversary *)
 Definition PrPriv := PrSet.singleton (BProc.mkP C).

 (** The adversary is well-formed in [E0], i.e. it only reads or writes 
    variables it has access to, and only calls oracles and its own procedures *)
 Hypothesis A_wf  : WFAdv PrOrcl PrPriv Gadv Gcomm E0 A.
 Hypothesis A'_wf : WFAdv PrOrcl PrPriv Gadv Gcomm E0 A'.

 (** The adversary runs in PPT provided the hash oracle does *)
 Hypothesis A_PPT : forall E,
  Eq_adv_decl PrOrcl PrPriv E0 E ->
  (forall O, PrSet.mem O PrOrcl -> PPT_proc E (BProc.p_name O)) ->
  PPT_proc E A.
 
 Hypothesis A'_PPT : forall E,
  Eq_adv_decl PrOrcl PrPriv E0 E ->
  (forall O, PrSet.mem O PrOrcl -> PPT_proc E (BProc.p_name O)) ->
  PPT_proc E A'.
 
 (** The adversary is lossless (i.e. it always terminates) provided 
    the hash oracle is lossless *)
 Hypothesis A_lossless : forall E,
  Eq_adv_decl PrOrcl PrPriv E0 E ->
  (forall O, PrSet.mem O PrOrcl -> lossless E (proc_body E (BProc.p_name O))) ->
  lossless E A_body.

 Hypothesis A'_lossless : forall E,
  Eq_adv_decl PrOrcl PrPriv E0 E ->
  (forall O, PrSet.mem O PrOrcl -> lossless E (proc_body E (BProc.p_name O))) ->
  lossless E A'_body.
 
 Lemma EqAD : forall H_body1 H_body2, 
  Eq_adv_decl PrOrcl PrPriv (makeEnv H_body1) (makeEnv H_body2).
 Proof.
  unfold Eq_adv_decl, proc_params, proc_body, proc_res, makeEnv; intros.
  generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  generalize (BProc.eqb_spec (BProc.mkP A') (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A') (BProc.mkP f)); intros.
  inversion H2; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto; intro Heq;
   apply H; rewrite <- Heq; vm_compute; trivial.
 Qed.

 Lemma EqOP : forall H_body1 H_body2, 
  Eq_orcl_params PrOrcl (makeEnv H_body1) (makeEnv H_body2).
 Proof.
  unfold Eq_orcl_params,makeEnv; intros.
  unfold PrOrcl in H.
  apply PrSet.singleton_complete in H; inversion H; simpl.
  vm_compute; trivial.
 Qed.

 Lemma A_wf_E : forall H_body, 
  WFAdv PrOrcl PrPriv Gadv Gcomm (makeEnv H_body) A.
 Proof.
  intros; apply WFAdv_trans with (5:=A_wf); unfold E0; try discriminate.
  apply EqOP.
  apply EqAD.
 Qed.

 Lemma A'_wf_E : forall H_body,
  WFAdv PrOrcl PrPriv Gadv Gcomm (makeEnv H_body) A'.
 Proof.
  intros; apply WFAdv_trans with (5:=A'_wf); try discriminate.
  apply EqOP.
  apply EqAD.
 Qed.

 (** Helper functions to construct the information used by tactics *)
 Definition iEiEi Hbody Hr Hr' :=
  let E := makeEnv Hbody in
  let Aloss := @A_lossless E (EqAD _ _) in
  let A'loss := @A'_lossless E (EqAD _ _) in
  let piH := add_refl_info_rm Hash Hr Hr' (empty_info E E) in
  let piA := add_adv_info_lossless (EqAD _ _) (A_wf_E _) Aloss Aloss piH in
   add_adv_info_lossless (EqAD _ _) (A'_wf_E _) A'loss A'loss piA.

 Definition iEiEj Hbody Hbody' I O
  (Hequiv:EqObsInv trueR I (makeEnv Hbody) Hbody (makeEnv Hbody') Hbody' O) :=
  let E := makeEnv Hbody in    
  let E' := makeEnv Hbody' in
  let Aloss := @A_lossless E (EqAD _ _) in
  let A'loss := @A'_lossless E (EqAD _ _)  in
  let Aloss' := @A_lossless E' (EqAD _ _)  in
  let A'loss' := @A'_lossless E' (EqAD _ _)  in
  let piH := add_info Hash Vset.empty Vset.empty (empty_info E E') Hequiv in
  let piA := add_adv_info_lossless (EqAD _ _) (A_wf_E _) Aloss Aloss' piH in
   add_adv_info_lossless (EqAD _ _) (A'_wf_E _) A'loss A'loss' piA.
 

 (** Game one *)
 Definition G1 :=
  [
   hp <$- {0,1}^k;
   L <- Nil _;
   x <$- [0..q-!1];
   y <$- [0..q-!1];
   Lam <- g^(x *! y);
   mm <c- A with {g^x};
   b <$- {0,1};
   If b then [ mb <- Efst mm ] else [ mb <- Esnd mm ];
   h <c- Hash with {Lam};
   v <- h |x| mb;
   b' <c- A' with {g^x, g^y, v}
  ].

  Definition G1' :=
  [
   x <$- [0..q-!1];
   y <$- [0..q-!1];
   Lam <- g^(x *! y);
   L <- Nil _;
   hp <$- {0,1}^k;
   mm <c- A with {g^x};
   b <$- {0,1};
   If b then [ mb <- Efst mm ] else [ mb <- Esnd mm ];
   h <c- Hash with {Lam};
   v <- h |x| mb;
   b' <c- A' with {g^x, g^y, v}
  ].

 Definition Hash1'_body :=
  [ 
   If !(lambda in_dom L) then 
   [
    If Lam =?= lambda then
     [
      r <- hp
     ]
    else
     [
      r <$- {0,1}^k
     ];
    L <- (lambda | r) |::| L
   ]
   else [
    r <- L[{lambda}]
   ]
  ].

 Definition Hash1_body :=
  [ 
   If !(lambda in_dom L) then 
   [
    If Lam =?= lambda then
     [
      bad <- true; r <- hp
     ]
    else
     [
      r <$- {0,1}^k
     ];
    L <- (lambda | r) |::| L
   ]
   else [
    r <- L[{lambda}]
   ]
  ].

 Definition E1'  := makeEnv Hash1'_body.
 Definition E1  := makeEnv Hash1_body.

 Definition iE0E0   := iEiEi Hash0_body Vset.empty Vset.empty.
 Definition iE1E1   := iEiEi Hash1_body Vset.empty Vset.empty.

 Definition I_H := Vset.add lambda (Vset.add Lam (Vset.singleton L)).
 Definition O_H := Vset.add r (Vset.singleton L).
 
 Lemma Hash1'_Hash1 :
  EqObsInv trueR (Vset.add hp I_H)
  E1' Hash1'_body
  E1  Hash1_body
  (Vset.add hp O_H).
 Proof.
  deadcode;eqobs_in.
 Qed.

 Definition iE1'E1  := iEiEj Hash1'_Hash1.
 Definition iE1'E1' := iEiEi Hash1'_body Vset.empty Vset.empty.
 (* On doit pouvoir le faire automatiquement i.e sans la preuve Hash1'_Hash1*)

 Definition S:=
  [ If !(Lam in_dom L) then [hp <$- {0,1}^k] else [hp <- L[{Lam}] ] ].

 Definition XS:= Vset.add hp (Vset.add Lam (Vset.singleton L)).

 Lemma Modify_S : forall E, Modify E XS S.
 Proof.
  intros E;compute_assertion X t (modify (refl1_info (empty_info E E)) (Vset.add Lam (Vset.singleton L)) S).
  refine (modify_correct _ _ _ X).
 Qed.

 Lemma EqObs_S : EqObs XS E0 S E1' S XS.
 Proof. eqobs_in. Qed.

 Lemma XS_global : forall x : VarP.Edec.t, Vset.mem x XS -> Var.is_global x.
 Proof.
  unfold XS;intros x;repeat rewrite VsetP.add_spec;intros [H0 | [H0 | H0 ] ];
  try (rewrite <- H0;trivial).
  apply Vset.singleton_complete in H0;rewrite <- H0;trivial.
 Qed.

 Lemma swap_equiv : equiv Meq E0 (proc_body E0 Hash ++ S) E1' (S ++ proc_body E1' Hash) Meq.
 Proof.
  union_mod;auto with *.
  apply equiv_strengthen with (kreq_mem (Vset.add lambda (Vset.add L (Vset.singleton Lam)))).
  intros k m1 m2 Heq;rewrite Heq;apply req_mem_refl.
  apply EqObs_trans with (E2 := E0) (c2:= (L' <- L)::(proc_body E0 Hash ++ S));
   [deadcode;eqobs_in | ].
  apply EqObs_trans with (E2 := E1') (c2:= (L' <- L)::(S ++ proc_body E1' Hash));
   [ | deadcode;eqobs_in].
  apply equiv_cons with (req_mem_rel (Vset.add L' (Vset.add lambda (Vset.add L (Vset.singleton Lam))))
                            (EP1 (L =?= L'))).
  eqobsrel_tail;unfold implMR;simpl;unfold O.eval_op;simpl;intros.
  change (E.eval_expr (L =?= L) m1);rewrite <- eval_eq;trivial.
  ep_eq L L'.
  unfold EP1;intros k m1 m2 (Heq, H1);rewrite <- (eval_eq m1 L L') in H1.
  split;[trivial | transitivity (E.eval_expr L m1)].
  apply depend_only_fv_expr;apply req_mem_sym;apply req_mem_weaken with (2:= Heq);vm_compute;trivial.
  transitivity (E.eval_expr L' m1);[trivial | ].
  apply depend_only_fv_expr;apply req_mem_weaken with (2:= Heq);vm_compute;trivial.
  cp_test (lambda in_dom L').
  ep_eq_l L L';[unfold EP1;intros k m1 m2 ((_,H),_);rewrite eval_eq;trivial | ].
  swap;eqobs_in.
  cp_test (Lam in_dom L').
  ep_eq (Lam =?= lambda) false.
  unfold req_mem_rel, andR, EP1, EP2, notR; intros k m1 m2 H;decompose [and] H;clear H.
  split;refine (not_true_is_false _ _).
  rewrite <- (eval_eq m1 Lam lambda);intros Heq;apply H2.
  generalize H3 Heq;clear H3 Heq;simpl;unfold O.eval_op;simpl; intros H3 Heq;rewrite <- Heq;trivial.
  rewrite <- (eval_eq m2 Lam lambda);intros Heq;apply H5.
  generalize H6 Heq;clear H6 Heq;simpl;unfold O.eval_op;simpl; intros H6 Heq;rewrite <- Heq;trivial.
  swap;eqobs_in.
  cp_test (Lam =?=lambda).
  alloc_l r hp;ep;eqobs_in.
  swap;eqobs_in.
 Qed.
 
 Definition swi_H := 
  add_sw_info S XS Vset.empty E0 E1' (Modify_S E0) (Modify_S E1') EqObs_S 
  XS_global (fun t f => None) _ Hash swap_equiv.

 Definition swi : forall (tg : SemHElGamal.T.type) (g_ : Proc.proc tg),
  option (sw_info S XS Vset.empty E0 E1' tg g_).
  assert (swi_A : forall (tg : SemHElGamal.T.type) (g_ : Proc.proc tg), option (sw_info S XS Vset.empty E0 E1' tg g_)).
    refine (add_sw_info_Adv S XS Vset.empty E0 E1' (Modify_S E0) (Modify_S E1') 
           EqObs_S XS_global swi_H _ A PrOrcl PrPriv Gadv Gcomm _ _);[ apply EqAD | trivial].
  refine (add_sw_info_Adv S XS Vset.empty E0 E1' (Modify_S E0) (Modify_S E1') 
           EqObs_S XS_global swi_A _ A' PrOrcl PrPriv Gadv Gcomm _ _);[ apply EqAD | trivial].
 Defined.

 Lemma EqObs_G0_G1 : EqObs Gadv E0 G0 E1 G1 (fv_expr (b =?= b')).
 Proof.
  unfold G0, G1;match goal with 
  |- EqObs _ _ (?i1::?i2::?i3::?c) _ (?ihp::_::_::_::?iLam::_) _ => 
     apply EqObs_trans with E0 ([i2;i3;iLam;i1]++(c++S));
     [deadcode iE0E0;swap iE0E0;eqobs_in iE0E0 |
      apply EqObs_trans with E1' ([i2;i3;iLam;i1]++(S++c));
      [ | ep iE1'E1;swap iE1'E1;eqobs_in iE1'E1]
     ]
  end.
  apply equiv_app with (kreq_mem (Vset.add x (Vset.add y (Vset.add Lam (Vset.add L Gadv))))).
  eqobs_in.
  match goal with 
  |- equiv _ _ _ _ ?c _ => apply equiv_trans_eq_mem_l with (E1':= E1') (c1':= c) (P1:=trueR) end.
  apply equiv_strengthen with Meq;[intros k0 m1 m2 (H, _);trivial | ].
  apply check_swap_c_correct with (pi:= swi) (I:=Vset.empty).
   apply Modify_S. 
   apply Modify_S. 
   apply EqObs_S.
   vm_compute; trivial.
  eqobs_in iE1'E1'.
  red;intros;red;trivial.
 Qed.

 (** Game two *)
 Definition G2 :=
  [
   bad <- false;
   hp <$- {0,1}^k;
   L <- Nil _;
   x <$- [0..q-!1];
   y <$- [0..q-!1];
   Lam <- g^(x *! y);
   mm <c- A with {g^x};
   b <$- {0,1};
   If b then [ mb <- Efst mm ] else [ mb <- Esnd mm ];
   h <- hp;
   v <- h |x| mb;
   b' <c- A' with {g^x, g^y, v}
  ].

 Definition Hash2_body :=
  [ 
   If Lam =?= lambda then 
    [ 
     r <- hp
    ] 
   else 
    [
     If !(lambda in_dom L) then
      [
       r <$- {0,1}^k;
       L <- (lambda | r) |::| L
      ]
     else 
      [
       r <- L[{lambda}]
      ]
    ]
  ].

 Definition E2 := makeEnv Hash2_body.

 Definition I2 := 
  EP1 ((Lam in_dom L) ==> (L[{Lam}] =?= hp)) /-\
  eq_assoc_except Lam L.
 
 Lemma dec_I2 : decMR I2.
 Proof.
  unfold I2; auto.
 Qed.
 
 Lemma dep_I2 : depend_only_rel I2
  (Vset.union (fv_expr ((Lam in_dom L) ==> (L[{Lam}] =?= hp)))
    (Vset.add Lam (Vset.singleton L)))
  (Vset.union Vset.empty (Vset.singleton L)).
 Proof.
  unfold I2; auto.
 Qed.
 
 Definition eE1E2 : eq_inv_info I2 E1 E2.
  refine (@empty_inv_info _ _ _ dep_I2 _ dec_I2 _ _).
  vm_compute; trivial.
 Defined.

 Lemma Hash1_Hash2 :
  EqObsInv I2
  (Vset.add hp (Vset.add Lam (Vset.singleton lambda)))
  E1 Hash1_body 
  E2 Hash2_body
  (Vset.add r (Vset.singleton hp)).
 Proof.
  unfold Hash2_body, Hash1_body.
  cp_test (Lam =?= lambda).
  ep_eq lambda Lam.
  intros k m1 m2 (_,(H1,H2));split;symmetry;repeat rewrite eval_eq;trivial.
  cp_test_l (Lam in_dom L).

  ep_eq_l (L[{Lam}]) hp.
  unfold I2, req_mem_rel, andR, EP1, EP2; intros.
  decompose [and] H; clear H.
  rewrite eval_eq; apply modus_ponens with (e1:=Lam in_dom L); auto.
  eqobs_in eE1E2;unfold implMR, andR; tauto.

  rewrite proj1_MR, proj1_MR.
  unfold I2;eqobsrel_tail;
   unfold implMR, andR; simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros; rewrite CGK_eqb_refl; simpl.
  split;[rewrite Veqb_refl; trivial | intros r Hdiff].
  decompose [and] H;clear H.
  destruct (H3 _ Hdiff);clear H3.
  rewrite <- is_true_CGK_eqb in Hdiff;apply not_true_is_false in Hdiff;rewrite Hdiff.
  simpl;split;trivial.

  cp_test (lambda in_dom L).
  unfold I2;intros k m1 m2 ((H0,(W1,W2)), (H2, H3)).
  unfold notR, EP1 in H2; rewrite <- (eval_eq m1 Lam lambda) in H2; apply sym_not_eq in H2.
  destruct (W2 _ H2) as (W3,_);clear W2 H2.
  assert (E.eval_expr lambda m1 = E.eval_expr lambda m2).
    apply depend_only_fv_expr;apply req_mem_weaken with (2:= H0);vm_compute;trivial.
  generalize W3;rewrite H at 2;trivial.
 
  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold req_mem_rel, upd_para, andR; intros.
  decompose [and] H; clear H; split.
  unfold kreq_mem;match goal with
  |- _{! _ <-- ?x1!} =={_} _{! _ <-- ?x2!} => replace x2 with x1 
  end.
  apply req_mem_update.
  apply req_mem_weaken with (2:=H0); vm_compute; trivial.
  unfold notR, EP1 in H2;rewrite <- (eval_eq m1 Lam lambda) in H2;apply sym_not_eq in H2.
  destruct H4 as (W1, W2);destruct (W2 _ H2).
  assert (E.eval_expr lambda m1 = E.eval_expr lambda m2).
    apply depend_only_fv_expr;apply req_mem_weaken with (2:= H0);vm_compute;trivial.
  generalize H1;rewrite H4 at 2;trivial.
  apply (@dep_I2 k m1 m2);trivial.
  apply req_mem_upd_disjoint;vm_compute;trivial.
  apply req_mem_upd_disjoint;vm_compute;trivial.
  
  unfold I2;eqobsrel_tail;
    unfold implMR, andR; simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2 H v _;decompose [and] H;clear H.
  unfold notR, EP1 in H3;generalize H3;simpl;unfold O.eval_op;simpl;intros W.
  apply not_true_is_false in W;rewrite W;split;[exact H1 | ].
  intros r Hdiff;generalize (H4 _ Hdiff);simpl;unfold O.eval_op, O.assoc;simpl;intros (W1,W2).
  replace (m2 lambda) with (m1 lambda);
   [ | apply H0;trivial].
  split;[rewrite W1;trivial| ].
  destruct (CGK.eqb r (m1 lambda));trivial.
 Qed.

 Definition hE1E2 := add_info Hash Vset.empty Vset.empty eE1E2 Hash1_Hash2.

 Definition iE1E2inv :=
  add_adv_info_lossless (EqAD _ _) (A'_wf_E _)
  (@A'_lossless _ (EqAD _ _))
  (@A'_lossless _ (EqAD _ _))
  (add_adv_info_lossless (EqAD _ _) (A_wf_E _)
   (@A_lossless _ (EqAD _ _))
   (@A_lossless _ (EqAD _ _))
   hE1E2).

 Definition iE2E2 := iEiEi Hash2_body Vset.empty Vset.empty.

 Lemma EqObs_G1_G2 : EqObs Gadv E1 G1 E1 G2 (fv_expr (b =?= b')).
 Proof.
  unfold G1, G2.
  match goal with
  |- EqObs ?I ?E1 (?i1::?i2::?i3::?i4::?i5::?c1) 
              ?E2 (?i0::?i1::?i2::?i3::?i4::?i5::?c2) ?Q =>
     change (EqObs I E1 ((i1::i2::i3::i4::i5::nil) ++ c1)
                     E2 ((i0::i1::i2::i3::i4::i5::nil) ++ c2) Q)
  end.
  set (I:= (Vset.add L (Vset.add hp (Vset.add x (Vset.add y (Vset.add Lam Gadv)))))).
  set (O:= fv_expr (b =?= b')).
  apply equiv_app with (req_mem_rel I (EP1 (L =?= Nil _))).
  unfold I2; eqobsrel_tail; 
   simpl; unfold O.eval_op; simpl; unfold implMR; simpl; intuition.
  match goal with
  |- equiv _ _ ?c _ _ _ => 
     apply equiv_trans with (P1:=req_mem_rel I I2) (Q1:= kreq_mem O) (Q2:= kreq_mem O)
     (E2:= E2) (c2:=c) end.
  auto using dec_I2.
  intros k m1 m2 (H1, H2);split.
  apply req_mem_trans with m2;[ | apply req_mem_sym];trivial.
  generalize H2;unfold EP1.
  rewrite <- (eval_eq m1 L (Nil _)).
  unfold I2, eq_assoc_except, EP1, EP2, andR;simpl;unfold O.eval_op;simpl;intros Heq;rewrite Heq;auto.
  apply req_mem_trans.
  eqobs_in iE1E2inv.
  match goal with
  |- equiv _ _ _ _ ?c _ => 
     apply equiv_trans with (P1:=kreq_mem I) (Q1:= kreq_mem O) (Q2:= kreq_mem O)
     (E2:= E2) (c2:=c) end.
  auto using dec_I2.
  intros k m1 m2 _;apply req_mem_refl.
  apply req_mem_trans.
  sinline_l iE2E2 Hash;eqobs_in iE2E2.
  apply equiv_sym_transp.
  apply equiv_strengthen with (req_mem_rel I I2).
  intros k m1 m2 (H1, H2);split;[apply req_mem_sym;trivial | ].
  generalize H2;unfold EP1.
  rewrite <- (eval_eq m2 L (Nil _)).
  unfold I2, eq_assoc_except, EP1, EP2, andR;simpl;unfold O.eval_op;simpl;intros Heq.
  rewrite <- (H1 _ L), Heq;auto.
  apply equiv_weaken with (kreq_mem O);[exact (@req_mem_sym O) | ].
  eqobs_in iE1E2inv.
 Qed.



 (** Game three *)
 Definition G3 := G2.

 Definition Hash3_body :=
  [ 
   If !(lambda in_dom L) then 
   [
    If Lam =?= lambda then
     [
      bad <- true; r <$- {0,1}^k
     ]
    else
     [
      r <$- {0,1}^k
     ];
    L <- (lambda | r) |::| L
   ]
   else [
    r <- L[{lambda}]
   ]
  ].

 Definition E3 := makeEnv Hash3_body.

 Definition iE3E3 := iEiEi Hash3_body Vset.empty Vset.empty.

 Definition upto_info : upto_info bad E1 E3 :=
  add_adv_upto_info
   (add_adv_upto_info
    (add_upto_info (empty_upto_info bad _ _) Hash)
    (EqAD _ _) (EqOP _ _) (A_wf_E _))
   (EqAD _ _) (EqOP _ _) (A'_wf_E _). 

 Lemma Pr_G2_G3 : forall k (m:Mem.t k),
  Uabs_diff (Pr E1 G2 m (EP k (b =?= b'))) (Pr E3 G3 m (EP k (b =?= b'))) <= 
  Pr E3 G3 m (EP k bad).
 Proof.
  intros.
  unfold G3, G2, Pr.  
  setoid_rewrite deno_cons_elim.
  setoid_rewrite Mlet_simpl.
  setoid_rewrite deno_assign_elim.
  apply upto_bad_Uabs_diff with upto_info;
   [ | | apply is_lossless_correct with (refl1_info iE3E3)];
  vm_compute; trivial.
 Qed.

 Definition I3 := EP1 (bad ==> (Lam in_dom L)).

 Lemma dec_I3 : decMR I3.
 Proof.
  unfold I3; auto.
 Qed.
 
 Lemma dep_I3 : depend_only_rel I3
  (fv_expr (bad ==> (Lam in_dom L)))
  Vset.empty.
 Proof.
  unfold I3; auto.
 Qed.
  
 Definition eE3E3 : eq_inv_info I3 E3 E3.
  refine (@empty_inv_info _ _ _ dep_I3 _ dec_I3 _ _).
  vm_compute; trivial.
 Defined.

 Lemma Hash3_inv :
  EqObsInv I3
  (Vset.add hp (Vset.add bad (Vset.add L (Vset.add Lam (Vset.singleton lambda)))))
  E3 Hash3_body 
  E3 Hash3_body
  (Vset.add r (Vset.add bad (Vset.add L (Vset.singleton hp)))).
 Proof.
  unfold Hash3_body.
  cp_test (lambda in_dom L).
  eqobs_in eE3E3; unfold implMR, andR; tauto.
  cp_test (Lam =?= lambda).
  ep_eq lambda Lam.
  intros k m1 m2 (_, (H1,H2));split;symmetry;rewrite eval_eq;trivial.
  unfold I3; eqobsrel_tail; unfold implMR, EP1, andR; 
   simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [ _ [_ [ [H _] _] ] ].
  rewrite CGK_eqb_refl; trivial.

  unfold I3; eqobsrel_tail; unfold implMR, andR, EP1, notR; 
   simpl; unfold O.eval_op; simpl;intros k m1 m2 H;decompose [and] H;clear H;intros.
  rewrite not_is_true_false in H1;rewrite H1;trivial.
 Qed.

 Definition hE3E3 := add_info Hash Vset.empty Vset.empty eE3E3 Hash3_inv.

 Definition iE3E3inv :=
  add_adv_info_lossless (EqAD _ _) (A'_wf_E _)
  (@A'_lossless _ (EqAD _ _))
  (@A'_lossless _ (EqAD _ _))
  (add_adv_info_lossless (EqAD _ _) (A_wf_E _)
   (@A_lossless _ (EqAD _ _))
   (@A_lossless _ (EqAD _ _))
   hE3E3).

 Lemma Pr_G3_bad : forall k (m:Mem.t k),
  Pr E3 G3 m (EP k bad) <= Pr E3 G3 m (EP k (Lam in_dom L)).
 Proof.
  intros; unfold G3, G2, Pr.
  eapply equiv_deno_le with (req_mem_rel Gadv trueR) (req_mem_rel (Vset.add Lam (Vset.add bad (Vset.singleton L))) I3).  
  eqobs_tl iE3E3inv.
  unfold I3; eqobsrel_tail; unfold implMR, andR; 
   simpl; unfold O.eval_op; trivial.
  intros m1 m2 [H Hin]; unfold charfun, restr, EP, fone.
  rewrite <- depend_only_fv_expr_subset with (2:=H);
   unfold Vset.subset; trivial.
  case_eq (E.eval_expr bad m1); intro;[ | trivial].
  rewrite modus_ponens with (e1:=bad); trivial.
  unfold req_mem_rel, andR, trueR; auto.
 Qed.


 (** Game four *)
 Definition G4 :=
  [
   L <- Nil _;
   x <$- [0..q-!1];
   y <$- [0..q-!1];
   Lam <- g^(x *! y);
   mm <c- A with {g^x};
   b <$- {0,1};
   If b then [mb <- Efst (mm)] else [mb <- Esnd (mm)];   
   v <$- {0,1}^k;
   hp <- v |x| mb;
   b' <c- A' with {g^x, g^y, v}
  ].

 Definition Hash4_body := Hash0_body.

 Definition E4 := makeEnv Hash4_body.

 Definition iE4E4 := iEiEi Hash4_body Vset.empty Vset.empty.

 Lemma Pr_G4 : forall k (m:Mem.t k),
  Pr E4 G4 m (EP k (b =?= b')) == [1/2].
 Proof.
  intros.
  transitivity (Pr E4 (G4 ++ [b <$- {0,1}]) m (EP k (b =?= b'))).
  apply EqObs_Pr with Gadv.
  swap iE4E4; deadcode iE4E4; eqobs_in iE4E4.
  apply Pr_sample_bool; [discriminate | ].
  apply is_lossless_correct with (refl1_info iE4E4); vm_compute; trivial.  
 Qed.

 Lemma Hash3_Hash4 :
  EqObsInv trueR (Vset.add lambda (Vset.singleton L))
  E3 Hash3_body
  E4 Hash4_body
  (Vset.add r (Vset.add lambda (Vset.singleton L))).
 Proof.
  unfold Hash3_body, Hash4_body, Hash0_body.
  cp_test (lambda in_dom L);[eqobs_in | ].
  cp_test_l (Lam =?= lambda);[ | eqobs_in].
  ep_eq_l Lam lambda.
  intros k m1 m2 [_ H]; rewrite eval_eq; trivial.
  deadcode; eqobs_in.  
 Qed.

 Definition iE3E4 := iEiEj Hash3_Hash4.
  
 Lemma EqObs_G3_G4 : EqObs Gadv E3 G3 E4 G4 (Vset.add L (Vset.add Lam (fv_expr (b =?=b')))).
 Proof.
  unfold G4, G3, G2.
  apply EqObs_trans with E4
   [
     L <- E.Cnil (T.Pair (T.User Group) (T.User Bitstring));
     x <$- [0..q -! 1];
     y <$- [0..q -! 1];
     Lam <- g ^ (x *! y);
     mm <c- A with {g ^ x};
     b <$- {0,1};
     If b then [mb <- Efst (mm)] else [mb <- Esnd (mm)];
     hp <$- {0,1}^k;
     v <- hp |x| mb;
     b' <c- A' with {g ^ x, g ^ y, v}
   ].
  ep; swap iE3E4.
  eqobs_tl iE3E4.
  deadcode; eqobs_in.

  eqobs_ctxt iE4E4.
  union_mod.
  eapply equiv_sub; [ | | apply opt_sampling; discriminate].
  simpl; intros; apply req_mem_weaken with (2:=H); red; trivial. 
  simpl; intros; apply req_mem_weaken with (2:=H); red; trivial. 
 Qed.

 (** Game five *)
 Definition G5 := LCDH x y L 4.

 (** The adversary against list CDH *)
 Definition C_body :=
  [
   L <- Nil _;   
   mm <c- A with {alpha};
   v <$- {0,1}^k;
   b' <c- A' with {alpha, beta, v}
  ].

 Definition C_params : var_decl (Proc.targs C) := 
  dcons _ alpha (dcons _ beta (dnil _)).

 Definition C_ret := L.

 Definition E5 := add_decl E4 C C_params (refl_equal true) C_body C_ret.
 
 Lemma EqAD_5 : Eq_adv_decl PrOrcl PrPriv E5 E5.
 Proof.  
  unfold Eq_adv_decl; auto.
 Qed.

 Lemma EqAD_05 : Eq_adv_decl PrOrcl PrPriv E0 E5.
 Proof.
  unfold Eq_adv_decl, E0, E5, E4, makeEnv, proc_params, proc_body, proc_res.
  intros.
  generalize (BProc.eqb_spec (BProc.mkP A') (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A') (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
  inversion H2; simpl; auto.  
  repeat rewrite add_decl_other_mk; try tauto.
  intro Heq; apply H; rewrite <- Heq; vm_compute; trivial.
  intro Heq; apply H0; rewrite <- Heq; vm_compute; trivial.
  intro Heq; apply H; rewrite <- Heq; vm_compute; trivial.
 Qed.

 Definition iE4E5 := 
  let Aloss := @A_lossless E4 (EqAD _ _) in    
  let A'loss := @A'_lossless E4 (EqAD _ _) in
  let Aloss' := @A_lossless E5 EqAD_05 in    
  let A'loss' := @A'_lossless E5 EqAD_05 in
  let piH := add_refl_info Hash (empty_info E4 E5) in
  let piA := add_adv_info_lossless EqAD_05 (A_wf_E _) Aloss Aloss' piH in
   add_adv_info_lossless EqAD_05 (A'_wf_E _) A'loss A'loss' piA.

 Definition C_advantage := LCDH_advantage x y L 4 E5.

 Lemma security_bound : forall k (m:Mem.t k),
  Uabs_diff (Pr E0 G0 m (EP k (b =?= b'))) [1/2] <= C_advantage m.
 Proof.
  intros; unfold C_advantage, LCDH_advantage, LCDH.
  eapply Ole_trans;[apply Oeq_le | eapply Ole_trans;[ apply (Pr_G2_G3 m)| ] ].
  apply Uabs_diff_morphism.
  apply EqObs_Pr with Gadv.
  apply EqObs_trans with (1:=EqObs_G0_G1);apply EqObs_G1_G2.
  rewrite <- (Pr_G4 m);symmetry.
  apply EqObs_Pr with Gadv;apply equiv_weaken with (2:=EqObs_G3_G4).
  intros k0 m1 m2 H;apply req_mem_weaken with (2:=H);vm_compute;trivial.
  eapply Ole_trans;[apply Pr_G3_bad | apply Oeq_le].
  apply Oeq_trans with (Pr E4 G4 m (EP k (Lam in_dom L))).
  apply EqObs_Pr with Gadv.
  apply equiv_weaken with (2:=EqObs_G3_G4).
  intros k0 m1 m2 H;apply req_mem_weaken with (2:=H);vm_compute;trivial.
  setoid_rewrite (Pr_d_eq _ _ _ b);apply EqObs_Pr with Gadv.
  sinline_r iE4E5 C;swap iE4E5; eqobs_in iE4E5.
 Qed.

 Definition pi : PPT_info E5 :=
  PPT_add_adv_infob EqAD_05 A'_PPT
   (PPT_add_adv_infob EqAD_05 A_PPT
    (PPT_add_info (PPT_empty_info E5) Hash)).
   
 Lemma semantic_security : forall m,
  negligible (fun k => Uabs_diff (Pr E0 G0 (m k) (EP k (b =?= b'))) [1/2]).
 Proof.
  intro m.
  apply negligible_le_stable with 
   (fun k => LCDH_advantage x y L 4%positive E5 (m k)).
  intro; apply security_bound.
  apply LCDH_assumption.
  discriminate.
  trivial.
  trivial. 
  apply is_lossless_correct with (refl2_info iE4E5); vm_compute; trivial.
  PPT_proc_tac pi.
 Qed.

End ADVERSARY_AND_PROOF.
