(** * ElGamal.v : Semantic security of the ElGamal encryption scheme *)

Set Implicit Arguments.

Require Import SemGroup.

Module SECURITY_PROOF (GCK : CYCLIC_GROUP_WITH_ORDER).

 Module SEM :=  MAKE_SEM_GROUP GCK.
 Import SEM.


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
  (Proc.mkP Dname (T.User Tg :: T.User Tg :: T.User Tg :: nil) T.Bool).

 Definition DDH0 :=
  [ 
   x <$- [0..q-!1];
   y <$- [0..q-!1];
   b <c- D with {g^x, g^y, g^(x *! y)}
  ].

 Definition DDH1 :=
  [ 
   x <$- [0..q-!1];
   y <$- [0..q-!1];
   z <$- [0..q-!1];
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


Open Scope positive_scope.

(** ** Global Variables *)

(** *** Global variables shared between the adversary, the oracles and the game *)
Definition Gcomm := Vset.empty.

(** Global variable shared between [A] and [A'] *)
Notation g_a := (Var.Gvar T.Nat 1).

Definition Gadv := {{g_a}}.

(** Coin tossed to choose the encrypted message *)
Notation b  := (Var.Gvar T.Bool 2).


(** ** Local variables *)

(** Integer variables *)
Notation x := (Var.Lvar T.Nat 11).
Notation y := (Var.Lvar T.Nat 12).
Notation z := (Var.Lvar T.Nat 13).

(** Group elements *)
Notation alpha    := (Var.Lvar (T.User Tg) 21).
Notation alpha'   := (Var.Lvar (T.User Tg) 22).
Notation beta     := (Var.Lvar (T.User Tg) 23).
Notation gamma    := (Var.Lvar (T.User Tg) 24).
Notation zeta     := (Var.Lvar (T.User Tg) 25).
Notation xalpha   := (Var.Lvar (T.Pair T.Nat (T.User Tg)) 26).
Notation betazeta := (Var.Lvar (T.Pair(T.User Tg) (T.User Tg)) 27).

(** Messages *)
Notation m   := (Var.Lvar (T.Pair (T.User Tg) (T.User Tg)) 31).
Notation mb  := (Var.Lvar (T.User Tg) 32).
Notation mb' := (Var.Lvar (T.User Tg) 33).

(** Bits *)
Notation b' := (Var.Lvar T.Bool 41).
Notation d  := (Var.Lvar T.Bool 42).

(** ** Procedures *)
Notation A  := (Proc.mkP 1 (T.User Tg :: nil) (T.Pair (T.User Tg) (T.User Tg))).
Notation A' := (Proc.mkP 2 (T.User Tg :: T.User Tg :: T.User Tg :: nil) T.Bool).
Notation B  := (Proc.mkP 3 (T.User Tg :: T.User Tg ::T.User Tg :: nil) T.Bool).
Notation KG := (Proc.mkP 4 nil (T.Pair T.Nat (T.User Tg))).
Notation Enc := (Proc.mkP 5 (T.User Tg :: T.User Tg :: nil) (T.Pair (T.User Tg) (T.User Tg))).

Close Scope positive_scope.


(** ** Key Generation *)
Definition KG_params : (var_decl (Proc.targs KG)) := dnil _.

Definition KG_body := 
 [
  x <$- [0..q-!1]
 ].

Definition KG_res := (x | g^x).

(** ** Encryption *)
Definition Enc_params : (var_decl (Proc.targs Enc)) :=  
 dcons _ alpha' (dcons _ mb' (dnil _)).

Definition Enc_body :=
 [
  y <$- [0..q-!1]
 ].

Definition Enc_res := (g^y | alpha'^y ** mb').


(** * Games *)

Definition ElGamal : cmd :=
 [
  xalpha <c- KG with {};
  x <- Efst xalpha; alpha <- Esnd xalpha;
  m <c- A with {alpha};
  b <$- {0,1};
  If b then [ mb <- Efst m ] else [ mb <- Esnd m ];
  betazeta <c- Enc with {alpha, mb};
  beta <- Efst betazeta; zeta <- Esnd betazeta;
  b' <c- A' with {alpha, beta, zeta}
 ].

Definition G0 : cmd :=
 [
  x <$- [0..q-!1]; y <$- [0..q-!1];
  m <c- A with {g^x};
  b <$- {0,1};
  If b then [ mb <- Efst m ] else [ mb <- Esnd m ];
  zeta <- g^(x *! y) ** mb;
  b' <c- A' with {g^x, g^y, zeta}
 ].

Definition G1 : cmd :=
 [
  x <$- [0..q-!1]; y <$- [0..q-!1];
  m <c- A with {g^x};
  b <$- {0,1};
  If b then [ mb <- Efst m ] else [ mb <- Esnd m ];
  z <$- [0..q-!1]; zeta <- g^z ** mb;
  b' <c- A' with {g^x, g^y, zeta}
 ].

Definition G2 : cmd :=
 [
  x <$- [0..q-!1]; y <$- [0..q-!1];
  m <c- A with {g^x};
  z <$- [0..q-!1]; zeta <- g^z;
  b' <c- A' with {g^x, g^y, zeta};
  b <$- {0,1}
 ].

(* The adversary for DDH *)
Definition B_params : (var_decl (Proc.targs B)) :=  
 dcons _ alpha (dcons _ beta (dcons _ gamma (dnil _))).

Definition B_body :=
 [
  m <c- A with {alpha};
  b <$- {0,1};
  If b then [ mb <- Efst m ] else [ mb <- Esnd m ];
  b' <c- A' with {alpha, beta, gamma ** mb}
 ].

Definition B_res := b =?= b'.

Definition DDH0_B := DDH0 x y   d 3 (* B *).
Definition DDH1_B := DDH1 x y z d 3 (* B *).

Close Scope positive_scope.


(** ** Adversary and proof *)
Section ADVERSARY_AND_PROOF.

 Variable env_adv : env.

 (** *** Specification of the adversary *)
 Definition A_params : var_decl (Proc.targs A) := dcons _ alpha (dnil _).

 Variable A_body : cmd.

 (** [A] returns a pair of messages *)
 Variable A_ret : E.expr (T.Pair (T.User Tg) (T.User Tg)).
  
 Definition A'_params : var_decl (Proc.targs A') :=
  dcons _ alpha (dcons _ beta (dcons _ zeta (dnil _))).

 Variable A'_body : cmd.

 (** [A'] returns a guess for [b], a boolean *)
 Variable A'_ret : E.expr T.Bool.

 (** The initial environment *)
 Definition E := 
  let Ekg := add_decl env_adv KG KG_params (refl_equal true) KG_body KG_res in
  let Eenc := add_decl Ekg Enc Enc_params (refl_equal true) Enc_body Enc_res in
  let EA' := add_decl Eenc A' A'_params (refl_equal true) A'_body A'_ret in
  add_decl EA' A A_params (refl_equal true) A_body A_ret.

 (** Environment for the DDH adversary *) 
 Definition EB := add_decl E B B_params (refl_equal true) B_body B_res.

 (** The set of oracles that can be called by [A] and [A'] (there are none) *)
 Definition PrOrcl := PrSet.empty.

 (** Private procedures, not accessible to the adversary *)
 Definition PrPriv := PrSet.singleton (BProc.mkP B).

 (** The adversary is well-formed in [E], i.e. it only reads or writes 
    variables it has access to, and only calls oracles and its own procedures *)
 Hypothesis A_wf  : WFAdv PrOrcl PrPriv Gadv Gcomm E A.
 Hypothesis A'_wf :  WFAdv PrOrcl PrPriv Gadv Gcomm E A'.

 (** The adversary runs in PPT *)
 Hypothesis A_PPT  : PPT_proc EB A.
 Hypothesis A'_PPT : PPT_proc EB A'.

 (** The adversary is lossless (i.e. it always terminates) *)
 Hypothesis A_lossless  : lossless EB A_body.
 Hypothesis A'_lossless : lossless EB A'_body.

 Lemma EqAD : Eq_adv_decl PrOrcl PrPriv E EB.
 Proof.
  unfold Eq_adv_decl, proc_params, proc_body, proc_res; intros.
  generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  generalize (BProc.eqb_spec (BProc.mkP A') (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A') (BProc.mkP f)); intros.
  inversion H2; simpl; auto.
  unfold EB.
  repeat rewrite add_decl_other_mk; try tauto.
  intro Heq; apply H0. rewrite <- Heq; trivial.
 Qed.

 Lemma EqADB : Eq_adv_decl PrOrcl PrPriv EB EB.
 Proof.
  unfold Eq_adv_decl; auto.
 Qed.

 Lemma EqOP : Eq_orcl_params PrOrcl E EB.
 Proof.
  unfold Eq_orcl_params; intros; discriminate.
 Qed.

 Lemma A_wf_EB : WFAdv PrOrcl PrPriv Gadv Gcomm EB A.
 Proof.
  unfold EB.
  intros; apply WFAdv_trans with E.
  exact EqOP.
  exact EqAD.
  discriminate.
  discriminate.
  trivial.
 Qed.

 Lemma A'_wf_EB : WFAdv PrOrcl PrPriv Gadv Gcomm EB A'.
 Proof.
  unfold EB.
  intros; apply WFAdv_trans with E.
  exact EqOP.
  exact EqAD.
  discriminate.
  discriminate.
  trivial.
 Qed.

 Definition iEEB :=
  let iKG := add_refl_info KG (empty_info E EB) in  
  let iEnc := add_refl_info_O Enc (fv_expr Enc_res) Vset.empty Vset.empty iKG in
  let iA := add_adv_info_false EqAD A_wf iEnc in
  add_adv_info_false EqAD A'_wf iA.

 Definition iEBEB :=
  let iKG := add_refl_info KG (empty_info EB EB) in
  let iEnc := add_refl_info_O Enc (fv_expr Enc_res) Vset.empty Vset.empty iKG in
  let iA := add_adv_info_lossless 
   EqADB A_wf_EB (fun _ => A_lossless) (fun _ => A_lossless) iEnc in
  let iA' := add_adv_info_lossless 
   EqADB A'_wf_EB (fun _ => A'_lossless) (fun _ => A'_lossless) iA in
  add_refl_info B iA'.

 (** Input variables *)
 Definition I := Gadv.

 Lemma EqObs_G1_bG2 :
  EqObs I EB G1 EB G2 (fv_expr (b =?= b')).
 Proof.
  unfold G1, G2.
  apply EqObs_trans with EB
   [
    x <$- [0..q-!1]; 
    y <$- [0..q-!1]; 
    m <c- A with {g ^ x};
    b <$- {0,1};
    If b then [ mb <- Efst (m) ] else [ mb <- Esnd (m) ];
    z <$- [0..q-!1];
    zeta <- g ^ z;
    b' <c- A' with {g ^ x, g ^ y, zeta}
   ].
  eqobs_hd_n iEBEB 5%nat.
  eqobs_tl iEBEB.
  union_mod iEBEB.
  apply mult_uniform; discriminate.

  deadcode iEBEB.
  swap iEBEB.
  eqobs_in iEBEB.
 Qed.

 Lemma claim_1 : forall k (m:Mem.t k),
  Pr EB G1 m (EP k (b =?= b')) == [1/2].
 Proof.
  intros.
  transitivity (Pr EB G2 m (EP k (b =?= b'))).
  apply EqObs_Pr with I; exact EqObs_G1_bG2.
  change G2 with (rev (tail (rev G2)) ++ [b <$- {0,1}]).
  apply Pr_sample_bool; [discriminate | ].
  apply is_lossless_correct with (refl1_info iEBEB); vm_compute; trivial.
 Qed.

 Lemma claim_2a : forall k (m:Mem.t k),
  Pr E ElGamal m (EP k (b =?= b')) == Pr EB DDH0_B m (EP k d).
 Proof.
  unfold ElGamal, DDH0_B, DDH0; intros k m0.  
  rewrite Pr_d_eq.
  apply EqObs_Pr with I.
  apply EqObs_trans with EB (G0 ++ [d <- (b =?= b')]).

  (* REMARK: we could use [sinline_l] instead *)
  inline_l iEEB KG.
  inline_l iEEB Enc.
  ep iEEB.
  deadcode iEEB.
  swap iEEB.
  eqobs_in iEEB.

  sinline_r iEBEB B.
  eqobs_in iEBEB.
 Qed.

 Lemma claim_2b : forall k (m:Mem.t k),
  Pr EB G1 m (EP k (b =?= b')) == Pr EB DDH1_B m (EP k d).
 Proof.
  unfold DDH1_B, DDH1; intros.
  rewrite Pr_d_eq.
  apply EqObs_Pr with I.
  sinline_r iEBEB B.
  swap iEBEB.
  eqobs_in iEBEB.
 Qed.
 
 Definition B_advantage := DDH_advantage x y z d 3 EB.

 Lemma claim_2 : forall k (m:Mem.t k), 
  Uabs_diff (Pr E ElGamal m (EP k (b =?= b'))) (Pr EB G1 m (EP k (b =?= b'))) ==
  B_advantage m.
 Proof.
  intros; apply Uabs_diff_morphism.
  apply claim_2a.  
  apply claim_2b.
 Qed.

 Lemma claim_3  : forall k m,
  Uabs_diff (Pr E ElGamal m (EP k (b =?= b'))) [1/2] == B_advantage m.
 Proof.
  intros; rewrite <- claim_2, claim_1; trivial.
 Qed.

 Definition pi : PPT_info EB :=
  PPT_add_adv_info (PPT_add_adv_info (PPT_empty_info EB) A'_PPT) A_PPT.

 Lemma ElGamal_semantic_security : forall m, 
  negligible (fun k => Uabs_diff (Pr E ElGamal (m k) (EP k (b =?= b'))) [1/2]).
 Proof.
  intro m.
  apply negligible_eq_stable with (fun k => B_advantage (m k)).
  intro; symmetry; apply claim_3.
  apply DDH_assumption; try discriminate; trivial.
  apply is_lossless_correct with (refl1_info iEBEB); vm_compute; trivial.
  PPT_proc_tac pi.
 Qed.

End ADVERSARY_AND_PROOF.

End SECURITY_PROOF.
