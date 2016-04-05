(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * HElGamal.v : Semantic security of the Hashed ElGamal encryption scheme *)

Set Implicit Arguments.

Require Import SemHElGamal.


(** ** DDH assumption *) 
Section DDH_ASSUMPTION.

 (** The DDH assumption says that any efficient adversary [D] has a negligible
    chance of telling appart triples of the form (g^x, g^y, g^(x * y)) from 
    triples of the form (g^x, g^y, g^z), where [x], [y] and [z] are uniformly
    sampled 
 *)

 Variables x y z : Var.var T.Nat.
 Variable b : Var.var T.Bool.
 Variable Dname : positive.

 Notation Local D := 
  (Proc.mkP Dname (T.User Group :: T.User Group :: T.User Group :: nil) T.Bool).

 Definition DDH0 :=
  [ 
   x <$- [0..q-!1%nat];
   y <$- [0..q-!1%nat];
   b <c- D with {g^x, g^y, g^(x *! y)}
  ].

 Definition DDH1 :=
  [ 
   x <$- [0..q-!1%nat];
   y <$- [0..q-!1%nat];
   z <$- [0..q-!1%nat];
   b <c- D with {g^x, g^y, g^z}
  ].

 Definition DDH_advantage E k (m:Mem.t k) :=
  Uabs_diff (Pr E DDH0 m (EP k b)) (Pr E DDH1 m (EP k b)).

 Axiom DDH_assumption : forall (m:forall k, Mem.t k) E,
  x <> y ->
  x <> z ->
  y <> z ->
  Var.is_local x ->
  Var.is_local y ->
  Var.is_local z ->
  lossless E (proc_body E D) ->
  PPT_proc E D ->
  negligible (fun k => DDH_advantage E (m k)).

End DDH_ASSUMPTION.


(** ** ES assumption *)
Section ES_ASSUMPTION.

 (** The ES assumption says that the family of hash functions [Hash {k,.}] is
    entropy smoothing. This means intuitevely that any efficient adversary [D]
    has a negligible chance of distinguishing a pair of the form
    [(k,Hash {k,x})] from a pair of the form [(k,h)], where [k] is uniformly
    sampled from the parameter space of the hash family, and [h] is a uniformly
    sampled bitstring.
 *)

 Variables k x : Var.var T.Nat.
 Variable h : Var.var (T.User Bitstring).
 Variable b : Var.var T.Bool.
 Variable Dname : positive.

 Notation Local D := (Proc.mkP Dname (T.User Bitstring :: nil) T.Bool).

 Definition ES0 :=
  [
   k <$- K;
   h <$- {0,1}^k;
   b <c- D with {h}
  ].

 Definition ES1 :=
  [
   k <$- K;
   x <$- [0..q-!1%nat];
   b <c- D with { Hash {k, g^x} }
  ].

 Definition ES_advantage E n (m:Mem.t n) :=
  Uabs_diff (Pr E ES1 m (EP n b)) (Pr E ES0 m (EP n b)).

 Axiom ES_assumption : forall (m:forall n, Mem.t n) E,
  Var.is_global k ->
  Var.is_local x ->
  Var.is_local h ->
  lossless E (proc_body E D) ->
  PPT_proc E D ->
  negligible (fun n => ES_advantage E (m n)).

End ES_ASSUMPTION.


Open Scope positive_scope.

(** ** Global Variables *)

Notation k := (Var.Gvar T.Nat 1).

(** *** Global variables shared between the adversary, the oracles and
   the game *)
Definition Gcomm := Vset.singleton k.

(** Global variable shared between [A] and [A'] *)
Notation g_a := (Var.Gvar T.Nat 2).

Definition Gadv := Vset.singleton g_a.


(** ** Local variables *)

(** Integer variables *)
Notation x := (Var.Lvar T.Nat 11).
Notation y := (Var.Lvar T.Nat 12).
Notation z := (Var.Lvar T.Nat 13).

(** Bitstrings *)
Notation h  := (Var.Lvar (T.User Bitstring) 21).
Notation h' := (Var.Lvar (T.User Bitstring) 22).
Notation v  := (Var.Lvar (T.User Bitstring) 23).

(** Group elements *)
Notation alpha  := (Var.Lvar (T.User Group) 31).
Notation beta   := (Var.Lvar (T.User Group) 32).
Notation gamma  := (Var.Lvar (T.User Group) 33).
Notation xalpha := (Var.Lvar (T.Pair T.Nat (T.User Group)) 34).
Notation betav  := (Var.Lvar (T.Pair (T.User Group) (T.User Bitstring)) 35).

(** Messages *)
Notation mm := (Var.Lvar (T.Pair (T.User Bitstring) (T.User Bitstring)) 41).
Notation mb  := (Var.Lvar (T.User Bitstring) 42).
Notation m := (Var.Lvar (T.User Bitstring) 43).

(** Bits *)
Notation b  := (Var.Gvar T.Bool 51).
Notation b' := (Var.Lvar T.Bool 52).
Notation d  := (Var.Lvar T.Bool 53).

(** ** Procedures *)
Notation KG := (Proc.mkP 1 nil (T.Pair T.Nat (T.User Group))).
Notation Enc:= (Proc.mkP 2 (T.User Group :: T.User Bitstring :: nil) (T.Pair (T.User Group) (T.User Bitstring))).
Notation A  := (Proc.mkP 3 (T.User Group :: nil) (T.Pair (T.User Bitstring) (T.User Bitstring))).
Notation A' := (Proc.mkP 4 (T.User Group :: T.User Group :: T.User Bitstring :: nil) T.Bool).
Notation B  := (Proc.mkP 5 (T.User Group :: T.User Group :: T.User Group :: nil) T.Bool).
Notation D  := (Proc.mkP 6 (T.User Bitstring :: nil) T.Bool).

Close Scope positive_scope.


(** ** Key Generation *)
Definition KG_params : (var_decl (Proc.targs KG)) := dnil _.

Definition KG_body := 
 [
  k <$- K;
  x <$- [0..q-!1%nat]
 ].

Definition KG_res := (x | g^x).

(** ** Encryption *)
Definition Enc_params : (var_decl (Proc.targs Enc)) := 
 dcons _ alpha (dcons _ m (dnil _)).

Definition Enc_body :=
 [
  y <$- [0..q-!1%nat];
  h <- Hash {k, alpha^y}
 ].

Definition Enc_res := (g^y | h |x| m).


(** * Games *)

Definition G0 :=
 [
  xalpha <c- KG with {};
  x <- Efst xalpha; 
  alpha <- Esnd xalpha;
  mm <c- A with {alpha};
  b <$- {0,1};
  If b then [ mb <- Efst mm ] else [ mb <- Esnd mm ];
  betav <c- Enc with {alpha, mb};
  beta <- Efst betav; 
  v <- Esnd betav;
  b' <c- A' with {alpha, beta, v};
  d <- (b =?= b')
 ].

Definition G1 :=
 [  
  k <$- K;
  x <$- [0..q-!1%nat]; y <$- [0..q-!1%nat];
  mm <c- A with {g^x};
  b <$- {0,1};
  If b then [ mb <- Efst mm ] else [ mb <- Esnd mm ];
  h <- Hash {k, g^(x *! y)};
  v <- h |x| mb;  
  b' <c- A' with {g^x, g^y, v};
  d <- (b =?= b')
 ].

Definition G2 :=
 [
  k <$- K;
  x <$- [0..q-!1%nat]; y <$- [0..q-!1%nat];
  mm <c- A with {g^x};
  b <$- {0,1};
  If b then [ mb <- Efst mm ] else [ mb <- Esnd mm ];
  h <$- {0,1}^k;   
  v <- h |x| mb;
  b' <c- A' with {g^x, g^y, v};
  d <- (b =?= b')
 ].

Definition G3 :=
 [
  k <$- K;
  x <$- [0..q-!1%nat]; y <$- [0..q-!1%nat];
  mm <c- A with {g^x};
  b <$- {0,1};
  If b then [ mb <- Efst mm ] else [ mb <- Esnd mm ];
  v <$- {0,1}^k;   
  h <- v |x| mb;
  b' <c- A' with {g^x, g^y, v};
  d <- (b =?= b')
 ].


(** The adversary for DDH *)
Definition B_params : (var_decl (Proc.targs B)) :=  
 dcons _ alpha (dcons _ beta (dcons _ gamma (dnil _))).

Definition B_body :=
 [
  k <$- K;
  mm <c- A with {alpha};
  b <$- {0,1};
  If b then [ mb <- Efst mm ] else [ mb <- Esnd mm ];  
  h <- Hash {k, gamma};
  b' <c- A' with {alpha, beta, h |x| mb}
 ].

Definition B_res := b =?= b'.

Definition DDH0_B := DDH0 x y   d 5 (* B *).
Definition DDH1_B := DDH1 x y z d 5 (* B *).


(* The adversary for ES *)
Definition D_params : (var_decl (Proc.targs D)) := dcons _ h' (dnil _).

Definition D_body :=
 [
  x <$- [0..q-!1%nat];
  y <$- [0..q-!1%nat];
  mm <c- A with {g^x};
  b <$- {0,1};
  If b then [ mb <- Efst mm ] else [ mb <- Esnd mm ];  
  b' <c- A' with {g^x, g^y, h' |x| mb}
 ].

Definition D_res := b =?= b'.

Definition ES0_D := ES0 k h d 6 (* D *).
Definition ES1_D := ES1 k z d 6 (* D *).

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
 
 (** The initial environment *)
 Definition E := 
  let Ekg  := add_decl env_adv KG KG_params (refl_equal true) KG_body KG_res in 
  let Eenc := add_decl Ekg Enc Enc_params (refl_equal true) Enc_body Enc_res in
  let EA   := add_decl Eenc A A_params (refl_equal true) A_body A_ret in
   add_decl EA A' A'_params (refl_equal true) A'_body A'_ret. 

 (** Environment for the DDH and ES adversaries *) 
 Definition EBD := 
  let ED := add_decl E D D_params (refl_equal true) D_body D_res in
   add_decl ED B B_params (refl_equal true) B_body B_res.     

 (** The set of oracles that can be called by [A] and [A'] (there are none) *)
 Definition PrOrcl := PrSet.empty.

 (** Private procedures, not accessible to the adversary *)
 Definition PrPriv := PrSet.add (BProc.mkP B) (PrSet.singleton (BProc.mkP D)).
 
 (** The adversary is well-formed in [E], i.e. it only reads or writes 
    variables it has access to, and only calls oracles and its own procedures *)
 Hypothesis A_wf  : WFAdv PrOrcl PrPriv Gadv Gcomm E A.
 Hypothesis A'_wf : WFAdv PrOrcl PrPriv Gadv Gcomm E A'.

 (** The adversary runs in PPT *)
 Hypothesis A_PPT  : forall E', Eq_adv_decl PrOrcl PrPriv E E' -> PPT_proc E' A.
 Hypothesis A'_PPT : forall E', Eq_adv_decl PrOrcl PrPriv E E' -> PPT_proc E' A'.

 (** The adversary is lossless (i.e. it always terminates) *)
 Hypothesis A_lossless  : forall E, lossless E A_body.
 Hypothesis A'_lossless : forall E, lossless E A'_body.

 Lemma EqAD : Eq_adv_decl PrOrcl PrPriv E EBD.
 Proof.
  unfold Eq_adv_decl, proc_params, proc_body, proc_res; intros.
  generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  generalize (BProc.eqb_spec (BProc.mkP A') (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A') (BProc.mkP f)); intros.
  inversion H2; simpl; auto.
  unfold EBD.
  repeat rewrite add_decl_other_mk; try tauto.
  intro Heq; apply H0; rewrite <- Heq; trivial.
  intro Heq; apply H0; rewrite <- Heq; trivial.
 Qed.

 Lemma EqAD_BD : Eq_adv_decl PrOrcl PrPriv EBD EBD.
 Proof.
  unfold Eq_adv_decl; auto.
 Qed.

 Lemma EqOP_BD : Eq_orcl_params PrOrcl E EBD.
 Proof.
  unfold Eq_orcl_params; intros; discriminate.
 Qed.

 Lemma A_wf_BD : WFAdv PrOrcl PrPriv Gadv Gcomm EBD A.
 Proof.
  intros; apply WFAdv_trans with E.
  exact EqOP_BD.
  exact EqAD.
  discriminate.
  discriminate.
  trivial.
 Qed.

 Lemma A'_wf_BD : WFAdv PrOrcl PrPriv Gadv Gcomm EBD A'.
 Proof.
  intros; apply WFAdv_trans with E.
  exact EqOP_BD.
  exact EqAD.
  discriminate.
  discriminate.
  trivial.
 Qed.

 Definition iE_EBD :=
  let iKG  := add_refl_info KG (empty_info E EBD) in  
  let iEnc := add_refl_info_O Enc (fv_expr Enc_res) Vset.empty Vset.empty iKG in
  let iA   := add_adv_info_lossless EqAD A_wf 
   (fun _ => A_lossless _) (fun _ => A_lossless _) iEnc in
   add_adv_info_lossless EqAD A'_wf 
   (fun _ => A'_lossless _) (fun _ => A'_lossless _) iA.

 Definition iEBD_EBD :=
  let iKG  := add_refl_info KG (empty_info EBD EBD) in
  let iEnc := add_refl_info_O Enc (fv_expr Enc_res) Vset.empty Vset.empty iKG in
  let iA   := add_adv_info_lossless EqAD_BD A_wf_BD 
   (fun _ => A_lossless _) (fun _ => A_lossless _) iEnc in
   add_adv_info_lossless EqAD_BD A'_wf_BD 
   (fun _ => A'_lossless _) (fun _ => A'_lossless _) iA.

 (** Input variables *)
 Definition I := Gadv.

 Lemma Pr_G0 : forall k (m:Mem.t k),
  Pr E G0 m (EP k (b =?= b')) == Pr EBD G0 m (EP k d).
 Proof.
  intros.  
  rewrite Pr_d_eq.
  apply EqObs_Pr with I.
  deadcode iE_EBD; eqobs_in iE_EBD.
 Qed.

 Lemma EqObs_G0_G1 : forall k (m:Mem.t k),
  EqObs I EBD G0 EBD G1 (fv_expr d).
 Proof.
  unfold G0, G1; intros. 
  sinline_l iEBD_EBD KG.
  sinline_l iEBD_EBD Enc.
  swap iEBD_EBD; eqobs_in iEBD_EBD.
 Qed.

 Lemma EqObs_G1_DDH0 : forall k (m:Mem.t k),
  EqObs I EBD G1 EBD DDH0_B  (fv_expr d).
 Proof.
  unfold G1, DDH0_B, DDH0; intros. 
  sinline_r iEBD_EBD B.
  swap iEBD_EBD; eqobs_in iEBD_EBD.
 Qed.

 Lemma Pr_G0_DDH0 : forall k (m:Mem.t k),
  Pr EBD G0 m (EP k d) == Pr EBD DDH0_B m (EP k d).
 Proof.
  intros.
  apply EqObs_Pr with I.
  apply EqObs_trans with (1:=EqObs_G0_G1 m) (2:=EqObs_G1_DDH0 m).
 Qed.

 Lemma EqObs_DDH1_ES1 : forall k (m:Mem.t k),
  EqObs I EBD DDH1_B EBD ES1_D (fv_expr d).
 Proof.
  unfold DDH1_B, DDH1, ES1_D, ES1; intros.
  inline_l iEBD_EBD B; inline_r iEBD_EBD D.
  ep iEBD_EBD.
  deadcode iEBD_EBD.
  swap iEBD_EBD.
  eqobs_in iEBD_EBD.
 Qed.

 Lemma Pr_DDH1_ES1 : forall k (m:Mem.t k),
  Pr EBD DDH1_B m (EP k d) == Pr EBD ES1_D m (EP k d).
 Proof.
  intros.
  apply EqObs_Pr with I.
  apply (EqObs_DDH1_ES1 m).
 Qed.

 Lemma EqObs_ES0_G2 : forall k (m:Mem.t k),
  EqObs I EBD ES0_D EBD G2 (fv_expr d).
 Proof.
  unfold ES0_D, ES0, G2; intros. 
  sinline_l iEBD_EBD D.
  swap iEBD_EBD; eqobs_in iEBD_EBD.
 Qed.

 Lemma EqObs_G2_G3 : forall k (m:Mem.t k),
  EqObs I EBD G2 EBD G3 (fv_expr d).
 Proof.
  unfold G2, G3; intros.
  eqobs_ctxt iEBD_EBD. 
  union_mod iEBD_EBD.
  eapply equiv_sub; [ |  | apply opt_sampling; discriminate ].
  simpl; intros; apply req_mem_weaken with (2:=H); red; trivial.
  simpl; intros; apply req_mem_weaken with (2:=H); red; trivial.
 Qed.

 Lemma Pr_ES0_G3 : forall k (m:Mem.t k),
  Pr EBD ES0_D m (EP k d) == Pr EBD G3 m (EP k d).
 Proof.
  intros.
  apply EqObs_Pr with I.
  apply EqObs_trans with (1:=EqObs_ES0_G2 m) (2:=EqObs_G2_G3 m).
 Qed.

 Lemma Pr_G3 : forall k (m:Mem.t k), 
  Pr EBD G3 m (EP k d) == [1/2].
 Proof.
  intros.
  rewrite <- (Pr_d_eq EBD (rev (tail (rev G3))) m d (b =?= b')).
  transitivity (Pr EBD (G3 ++ [b <$- {0,1}]) m (EP k (b =?= b'))).
  apply EqObs_Pr with I.  
  deadcode iEBD_EBD.
  swap iEBD_EBD.
  eqobs_in iEBD_EBD.
  apply Pr_sample_bool.
  discriminate.
  apply is_lossless_correct with (refl1_info iEBD_EBD); vm_compute; trivial.
 Qed.


 Definition B_advantage := DDH_advantage x y z d 5 EBD.
 Definition D_advantage := ES_advantage k z h d 6 EBD.

 Close Scope nat_scope.

 Lemma security_bound : forall m k,
  Uabs_diff (Pr E G0 (m k) (EP k (b =?= b'))) [1/2] <=
  B_advantage (m k) + D_advantage (m k).
 Proof.
  intros m k.
  rewrite Pr_G0.
  rewrite Pr_G0_DDH0.
  rewrite <- (Pr_G3 (m k)).
  rewrite <- Pr_ES0_G3.  
  unfold B_advantage, DDH_advantage, D_advantage, ES_advantage.
  rewrite Pr_DDH1_ES1.
  apply Uabs_diff_triangle_ineq.
 Qed.

 Definition pi : PPT_info EBD :=
  PPT_add_adv_info 
  (PPT_add_adv_info (PPT_empty_info EBD) (A'_PPT EqAD)) (A_PPT EqAD).

 Lemma semantic_security : forall m, 
  negligible (fun k => Uabs_diff (Pr E G0 (m k) (EP k (b =?= b'))) [1/2]).
 Proof.
  intro m.
  eapply negligible_le_stable with
   (fun k => B_advantage (m k) + D_advantage (m k)).
  apply security_bound.
  apply negligible_plus_stable.

  unfold B_advantage.
  apply DDH_assumption; try discriminate; trivial.
  apply is_lossless_correct with (refl1_info iEBD_EBD); vm_compute; trivial.
  PPT_proc_tac pi.

  unfold D_advantage.
  apply ES_assumption; try discriminate; trivial.
  apply is_lossless_correct with (refl1_info iEBD_EBD); vm_compute; trivial.
  PPT_proc_tac pi.
 Qed.

End ADVERSARY_AND_PROOF.
