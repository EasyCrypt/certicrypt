(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** IBE.v : IND-ID-CPA security of Boneh-Franklin's BasicIdent scheme *)

Require Import Extension.

Set Implicit Arguments.

Open Scope nat_scope.

Hint Unfold is_true.
Hint Resolve nat_eqb_refl.


(** ** Bilinear Diffie-Hellma Assumption *)
Section BDH_ASSUMPTION.

 (** The BDH assumption holds for e(.,.) iff any efficient adversary
     [D] has a negligible probability of computing [e(P,P)^{a,b,c}],
     given [P], [aP], [bP] and [cP], where [P] and [a], [b], [c] are
     uniformly sampled from [G1^+] and [1...q-1] respectively (G1 is a
     cyclic group of primer order [q] and [e] is a bilinear map into
     [G2], another cyclic group of the same order).
 *)

 Variables a b c : Var.var T.Nat.
 Variable P : Var.var (T.User G1).
 Variable z : Var.var (T.User G2).

 Variable Dname : positive.

 Notation Local D := 
  (Proc.mkP Dname (T.User G1 :: T.User G1 ::T.User G1 :: T.User G1:: nil)
   (T.User G2)).

 Definition BDH :=
  [ 
   P <$- G1o;
   a <$- [1..q-1]; b <$- [1..q-1]; c <$- [1..q-1]; 
   z <c- D with {P, a |.| P, b |.| P, c |.| P}
  ].

 Definition BDH_advantage E k (m:Mem.t k) :=
  Pr E BDH m (EP k (z =?= e(P,P)|^|(a *! b *! c))).

 Axiom BDH_assumption : forall (m:forall k, Mem.t k) E,
  Var.is_local a ->
  Var.is_local b ->
  Var.is_local c ->
  Var.is_local z ->
  a <> b ->
  a <> c ->
  b <> c ->
  lossless E (proc_body E D) ->
  PPT_proc E D ->
  negligible (fun k => BDH_advantage E (m k)).

End BDH_ASSUMPTION.


(** Identities, some infinite type (bitstrings in the literature) *)
Notation ID := T.Nat.

(** ** Global Variables *)

(** TODO: Make Ppub a parameter to the adversary *)

(** *** Global variables shared between the adversary, the oracles and
    the game (RO for the adversary) *)
Notation P    := (Var.Gvar (T.User G1) 1).
Notation Ppub := (Var.Gvar (T.User G1) 2).

Definition Gcomm := {{P, Ppub}}.


(** *** Global variables shared between [A1] and [A2] *)
Notation g_a := (Var.Gvar T.Nat 3).

Definition Gadv := {{g_a}}.


(** *** Global variables shared between the oracles and the game
   (not accessible to the adversary) *)
Notation a    := (Var.Gvar T.Nat 11).
Notation b    := (Var.Gvar T.Nat 12).
Notation c    := (Var.Gvar T.Nat 13).
Notation L1   := (Var.Gvar (T.List (T.Pair ID (T.User G1))) 14).
Notation L2   := (Var.Gvar (T.List (T.Pair (T.User G2) (T.User Bitstring))) 15).
Notation L2'  := (Var.Gvar (T.List (T.Pair (T.User G2) (T.User Bitstring))) 16).
Notation L3   := (Var.Gvar (T.List ID) 17).
Notation V    := (Var.Gvar (T.List (T.Pair ID T.Nat)) 18).
Notation T    := (Var.Gvar (T.List T.Bool) 19).
Notation J1   := (Var.Gvar (T.List (T.Pair ID T.Nat)) 20).
Notation id_A := (Var.Gvar ID 21).
Notation bad  := (Var.Gvar T.Bool 22).
Notation X    := (Var.Gvar (T.User G2) 23).
Notation X_hv := (Var.Gvar (T.User Bitstring) 24).
Notation P''  := (Var.Gvar (T.User G1) 25).
Notation bP'' := (Var.Gvar (T.User G1) 26).


(** ** Local variables *)

(* *** Main *)
Notation r1   := (Var.Lvar (T.Pair (T.Pair (T.User Bitstring) (T.User Bitstring)) ID) 1).
Notation m0   := (Var.Lvar (T.User Bitstring) 2).
Notation m1   := (Var.Lvar (T.User Bitstring) 3).
Notation m_d  := (Var.Lvar (T.User Bitstring) 4).
Notation y    := (Var.Lvar (T.Pair (T.User G1) (T.User Bitstring)) 5).
Notation Q_A  := (Var.Lvar (T.User G1) 6).
Notation h2   := (Var.Lvar (T.User Bitstring) 7).
Notation h2'  := (Var.Lvar (T.User Bitstring) 8).
Notation t    := (Var.Lvar T.Bool 9).
Notation v'   := (Var.Lvar T.Nat 10).
Notation d    := (Var.Lvar T.Bool 11).
Notation d_A  := (Var.Lvar T.Bool 12).
Notation R    := (Var.Lvar (T.User Bitstring) 13).
Notation i    := (Var.Lvar T.Nat 14).


(* *** Setup algorithm *)
Notation s     := (Var.Lvar T.Nat 20).

(* *** Encryption algorithm *)
Notation id_en := (Var.Lvar ID 30).
Notation m_en  := (Var.Lvar (T.User Bitstring) 31).
Notation Q_en  := (Var.Lvar (T.User G1) 32).
Notation r     := (Var.Lvar T.Nat 33).
Notation g     := (Var.Lvar (T.User G2) 34).
Notation h2_en := (Var.Lvar (T.User Bitstring) 35).
Notation c_en  := (Var.Lvar (T.Pair (T.User G1) (T.User Bitstring)) 36).

(* *** Extraction oracle *)
Notation id_ex := (Var.Lvar ID 40).
Notation Q_ex  := (Var.Lvar (T.User G1) 41).
Notation d_ex  := (Var.Lvar (T.User G1) 42).

(* *** H1 oracle *)
Notation id_H  := (Var.Lvar ID 50).
Notation v     := (Var.Lvar T.Nat 51).
Notation P1    := (Var.Lvar (T.User G1) 52).


(* *** H2 oracle *)
Notation z_H   := (Var.Lvar (T.User G2) 60).
Notation hv    := (Var.Lvar (T.User Bitstring) 61).

(* *** Adversary [B] against the List BDH assumption *)
Notation P'    := (Var.Lvar (T.User G1) 70).
Notation aP'   := (Var.Lvar (T.User G1) 71).
Notation bP'   := (Var.Lvar (T.User G1) 72).
Notation cP'   := (Var.Lvar (T.User G1) 73).

(* *** Formal parameter of adversary [A2] *)
Notation cipher := (Var.Lvar (T.Pair (T.User G1) (T.User Bitstring)) 80).

(* *** Auxiliary variables *)
Notation z     := (Var.Lvar (T.Pair ID (T.User G1)) 90).
Notation z'    := (Var.Lvar ID 91).
Notation aux   := (Var.Lvar (T.User G1) 92).
Notation aux'  := (Var.Lvar (T.User G2) 93).
Notation aux'' := (Var.Lvar (T.User G2) 94).

(** *** Variables used to instantiate the BDH assumption *)
Notation a'    := (Var.Lvar T.Nat 100).
Notation b'    := (Var.Lvar T.Nat 101).
Notation c'    := (Var.Lvar T.Nat 102).
Notation ret   := (Var.Gvar T.Bool 103).
Notation w     := (Var.Lvar (T.User G2) 104).


(** ** Procedures *)
Notation Setup   := (Proc.mkP 1
                    nil
                    T.Nat).

Notation Encrypt := (Proc.mkP 2
                    (ID :: T.User Bitstring :: nil)
                    (T.Pair (T.User G1) (T.User Bitstring))).

Notation H1      := (Proc.mkP 3
                    (ID :: nil)
                    (T.User G1)).

Notation H2      := (Proc.mkP 4
                    (T.User G2 :: nil)
                    (T.User Bitstring)).

Notation Ex      := (Proc.mkP 5
                    (ID :: nil)
                    (T.User G1)).

Notation A1      := (Proc.mkP 6
                    nil
                    (T.Pair (T.Pair (T.User Bitstring) (T.User Bitstring)) ID)).

Notation A2      := (Proc.mkP 7
                    (T.Pair (T.User G1) (T.User Bitstring) :: nil)
                    T.Bool).

Notation B       := (Proc.mkP 8
                    (T.User G1 :: T.User G1 :: T.User G1 :: T.User G1 :: nil)
                   (T.User G2)).


(** ** Setup algorithm *)
Definition Setup_body :=
 [
  P <$- G1o;
  s <$- [1..q-1];
  Ppub <- s |.| P
 ].

Definition Setup_params : (var_decl (Proc.targs Setup)) := dnil _.

Definition Setup_re := s.


(** ** Encryption algorithm *)
Definition Encrypt_body :=
 [
  Q_en <c- H1 with {id_en};
  r <$- [1..q-1];
  g <- e(Q_en, Ppub);
  h2_en <c- H2 with { g |^| r };
  c_en <- (r |.| P | h2_en |x| m_en)
 ].

Definition Encrypt_params : (var_decl (Proc.targs Encrypt)) :=
 dcons _ id_en (dcons _ m_en (dnil _)).

Definition Encrypt_re := c_en.


(** ** H1 oracle *)
Definition H1_0 :=
 [
  If !(id_H in_dom L1) _then
  [
   P1 <$- G1o;
   L1 <- (id_H | P1) |::| L1
  ]
 ].

Definition H1_params : var_decl (Proc.targs H1) := dcons _ id_H (dnil _).

Definition H1_re := L1[{id_H}].


(** ** H2 oracle *)
Definition H2_0 :=
 [
  If !(z_H in_dom L2) then
   [
    hv <$- {0,1}^k;
    L2 <- (z_H | hv) |::| L2
   ]
  else
   [  hv <- L2[{z_H}] ]
 ].

Definition H2_params : var_decl (Proc.targs H2) := dcons _ z_H (dnil _).

Definition H2_re := hv.


(** ** Extraction Oracle *)
Definition Ex_0 :=
 [
  Q_ex <c- H1 with {id_ex};
  d_ex <- a |.| Q_ex;
  If id_ex not_in L3 _then [ L3 <- id_ex |::| L3 ]
 ].

Definition Ex_params : var_decl (Proc.targs Ex) := dcons _ id_ex (dnil _).

Definition Ex_re := d_ex.


(** ** Adversary [B] *)
Definition B_params : var_decl (Proc.targs B) :=
 dcons _ P' (dcons _ aP' (dcons _ bP' (dcons _ cP' (dnil _)))).

Definition B_re : E.expr (T.User G2) := Efst (Enth {i, L2}).


(** * Initial Game *)
Definition G0 :=
 [
  L1 <- Nil _; L2 <- Nil _; L3 <- Nil _;
  a <c- Setup with {};
  r1 <c- A1 with {};
  id_A <- Esnd r1;
  m0 <- Efst (Efst r1); m1 <- Esnd (Efst r1);
  d <$- {0,1};
  If d then [ m_d <- m0 ] else [ m_d <- m1 ];
  y <c- Encrypt with {id_A, m_d};
  d_A <c- A2 with {y}
 ].


(** ** Adversary and proof *)
Section ADVERSARY_AND_PROOF.

 Variable env_adv : env.

 (** *** Specification of the adversary *)
 Variable A1_body : cmd.
 Variable A1_re : E.expr 
  (T.Pair (T.Pair (T.User Bitstring) (T.User Bitstring)) ID).
 Definition A1_params : var_decl (Proc.targs A1) := dnil _.

 Variable A2_body : cmd.
 Variable A2_re : E.expr T.Bool.
 Definition A2_params : var_decl (Proc.targs A2) := dcons _ cipher (dnil _).

 (** The set of oracles, [H1], [H2] and [Ex] *)
 Definition PrOrcl :=
  PrSet.add (BProc.mkP Ex)
  (PrSet.add (BProc.mkP H2)
   (PrSet.singleton (BProc.mkP H1))).
 
 (** Private procedures, not accessible to the adversary *)
 Definition PrPriv :=
  PrSet.add (BProc.mkP Setup)
  (PrSet.add (BProc.mkP Encrypt)
   (PrSet.singleton (BProc.mkP B))).

 (** Environment constructor *)
 Definition make_env H1_body H2_body Ex_body :=
 let H1_env := add_decl env_adv H1 H1_params (refl_equal _) H1_body H1_re in
 let H2_env := add_decl H1_env  H2 H2_params (refl_equal _) H2_body H2_re in
 let EX_env := add_decl H2_env  Ex Ex_params (refl_equal _) Ex_body Ex_re in
 let SU_env := add_decl EX_env  Setup Setup_params (refl_equal _) Setup_body Setup_re in
 let En_env := add_decl SU_env  Encrypt Encrypt_params (refl_equal _) Encrypt_body Encrypt_re in
 let A1_env := add_decl En_env  A1 A1_params (refl_equal _) A1_body A1_re in
 let A2_env := add_decl A1_env  A2 A2_params (refl_equal _) A2_body A2_re in 
  A2_env.

 (** The inital environment *)
 Definition E0 := make_env H1_0 H2_0 Ex_0.


 (** Advantage of the adversary against the IBE scheme *) 
 Definition Success k := EP k (d =?= d_A).
 Definition A_advantage k (m:Mem.t k) := Uabs_diff (Pr E0 G0 m (@Success k)) [1/2].


 (** The adversary is well-formed in [E0], i.e. it only reads or writes
    variables it has access to, and only calls oracles and its own procedures. *)
 Hypothesis A1_wf : WFAdv PrOrcl PrPriv Gadv Gcomm E0 A1.
 Hypothesis A2_wf : WFAdv PrOrcl PrPriv Gadv Gcomm E0 A2.

 (** The adversary runs in PPT provided the hash and extraction oracles do so *)
 Hypothesis A1_PPT : forall E,
  Eq_adv_decl PrOrcl PrPriv E0 E ->
  (forall O, PrSet.mem O PrOrcl -> PPT_proc E (BProc.p_name O)) ->
  PPT_proc E A1.

 Hypothesis A2_PPT : forall E,
  Eq_adv_decl PrOrcl PrPriv E0 E ->
  (forall O, PrSet.mem O PrOrcl -> PPT_proc E (BProc.p_name O)) ->
  PPT_proc E A2.


 (** The adversary is lossless as long as the hash and extraction
    oracles are so *)
 Hypothesis A1_lossless : forall E,
  (forall O, PrSet.mem O PrOrcl -> lossless E (proc_body E (BProc.p_name O))) ->
  lossless E A1_body.

 Hypothesis A2_lossless : forall E,
  (forall O, PrSet.mem O PrOrcl -> lossless E (proc_body E (BProc.p_name O))) ->
  lossless E A2_body.

 (** The adversary does not query the extraction oracle with the
     challenge ID, makes at most [qH1] queries to the [H1] oracle
     (either directly or indirectly, through the extraction oracle),
     and exactly [qEx] extraction queries.
 *)
 Definition S k :=
  EP k (id_A not_in L3) [&&]
  EP k (Elen L1 <=! qH1) [&&]
  EP k (Elen L3 =?= qEX).

 Hypothesis A_hyp : forall k (m:Mem.t k), range (@S k) ([[G0]] E0 m).


 (** The adversary makes at most [qH2] queries to the [H2] oracle
     independently of the environment with which she interacts 
 *)
 Hypothesis A_hyp' : forall  (c1 c2 c3 H1 H2 ExOr:cmd) r1 r2 arg X1 X2 X3 X4 X5,
  let E := make_env H1 H2 ExOr in
  let G :=  (L2 <- Nil _) :: 
   (c1 ++ [ r1 <c- A1 with {} ] ++ c2 ++ [ r2 <c- A2 with {arg} ] ++ c3) in 
   Modify E X1 H1 ->
   Modify E X2 ExOr ->
   Modify E X3 c1 ->
   Modify E X4 c2 ->
   Modify E X5 c3 ->
   ~Vset.mem L2 X1 ->
   ~Vset.mem L2 X2 ->
   ~Vset.mem L2 X3 ->
   ~Vset.mem L2 X4 ->
   ~Vset.mem L2 X5 ->
   forall k (m:Mem.t k), range (EP k (Elen L2 <! qH2)) ([[G]] E m).

 (** Adversary's procedures are the same in environments constructed
    with [make_env] *)
 Lemma EqAD : forall H1_body1 H2_body1 Ex_body1 H1_body2 H2_body2 Ex_body2,
  Eq_adv_decl PrOrcl PrPriv
  (make_env H1_body1 H2_body1 Ex_body1)
  (make_env H1_body2 H2_body2 Ex_body2).
 Proof.
  unfold Eq_adv_decl, make_env, proc_params, proc_body, proc_res; intros.
  generalize (BProc.eqb_spec (BProc.mkP A1) (BProc.mkP f)).
  case (BProc.eqb (BProc.mkP A1) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  generalize (BProc.eqb_spec (BProc.mkP A2) (BProc.mkP f)).
  case (BProc.eqb (BProc.mkP A2) (BProc.mkP f)); intros.
  inversion H2; simpl; auto.
  generalize (BProc.eqb_spec (BProc.mkP Setup) (BProc.mkP f)).
  case (BProc.eqb (BProc.mkP Setup) (BProc.mkP f)); intros.
  inversion H3; simpl; auto.
  generalize (BProc.eqb_spec (BProc.mkP Encrypt) (BProc.mkP f)).
  case (BProc.eqb (BProc.mkP Encrypt) (BProc.mkP f)); intros.
  inversion H4; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto;
   intros Heq; apply H; rewrite <- Heq; vm_compute; trivial.
 Qed.

 (** Oracles have the same declarations in environments constructed
    with [make_env] *)
 Lemma EqOP : forall H1_body1 H2_body1 Ex_body1 H1_body2 H2_body2 Ex_body2,
  Eq_orcl_params PrOrcl
  (make_env H1_body1 H2_body1 Ex_body1)
  (make_env H1_body2 H2_body2 Ex_body2).
 Proof.
  unfold Eq_orcl_params, make_env, PrOrcl; intros.
  rewrite PrSetP.add_spec in H; destruct H.
  inversion H; vm_compute; trivial.
  rewrite PrSetP.add_spec in H; destruct H.
  inversion H; vm_compute; trivial.
  apply PrSet.singleton_complete in H; inversion H; vm_compute; trivial.
 Qed.


 (** The adversary is well-formed in any environment constructred using
    [make_env]. This follows from the adversary being well-formed in [E0] *)
 Lemma A1_wf_E : forall H1_body H2_body Ex_body,
  WFAdv PrOrcl PrPriv Gadv Gcomm (make_env H1_body H2_body Ex_body) A1.
 Proof.
  intros; apply WFAdv_trans with (5:=A1_wf).
  unfold E0; apply EqOP.
  unfold E0; apply EqAD.
  vm_compute; intro; discriminate.
  vm_compute; intro; discriminate.
 Qed.

 Lemma A2_wf_E : forall H1_body H2_body Ex_body,
  WFAdv PrOrcl PrPriv Gadv Gcomm (make_env H1_body H2_body Ex_body) A2.
 Proof.
  intros; apply WFAdv_trans with (5:=A2_wf).
  unfold E0; apply EqOP.
  unfold E0; apply EqAD.
  vm_compute; intro; discriminate.
  vm_compute; intro; discriminate.
 Qed.

 Definition I := Gadv.


 (** * G0 --> G1 *)

 (* CHANGES IN THE GAME:
    1) Inline [Setup], [Encrypt]
    2) Keep track of the order in which queries are made in
    the simulation of [H1]
    3) Perform the coin tosses for the simulation of [H1]
    coming in the next game

    RESULTS REGARDING PROBABILITY OF EVENTS:
    1) Probability of [Success] is preserved (games are
    observationally equivalent)
    2) Compute the probability that simulation succeeds
    (in terms of the outcome of coin tosses)
 *)
 
 Definition CoinTosses : cmd :=
  [
   T <- Nil _;
   while Elen T <! qH1 do [ t <$-{0,1}_p; T <- T |++| (t |::| Nil _) ]
  ].

 Definition G1_prefix :=
  [
   L1 <- Nil _; L2 <- Nil _; L3 <- Nil _; J1 <- Nil _;
   P <$- G1o;
   a <$- [1..q-1];
   Ppub <- a |.| P;
   b <$- [1..q-1];
   r1 <c- A1 with {};
   id_A <- Esnd r1;
   m0 <- Efst (Efst r1); m1 <- Esnd (Efst r1);
   d <$- {0,1};
   If d then [ m_d <- m0 ] else [ m_d <- m1 ];
   Q_A <c- H1 with {id_A};
   g <- e(Q_A,Ppub);
   c <$- [1..q-1];
   h2 <c- H2 with { g |^| c };
   y <- (c |.| P | h2 |x| m_d);
   d_A <c- A2 with {y}
  ].

 Definition G1 := G1_prefix ++ CoinTosses.

 Definition H1_1 :=
  [
   If !(id_H in_dom L1) _then
   [
    P1 <$- G1o;
    J1 <- (id_H | Elen L1) |::| J1;
    L1 <- (id_H | P1) |::| L1
   ]
  ].

 Definition E1 := make_env H1_1 H2_0 Ex_0.

 Definition GoodToss k :=
  EP k (Enth {J1[{id_A}], T}) [&&]
  EP k (E.Eforall z' (!(Enth {J1[{z'}], T})) L3).

 Definition S2 k := @Success k [&&] @GoodToss k.

 Open Scope U_scope.

 Lemma CoinTosses_lossless : forall E, lossless E CoinTosses.
 Proof.
  intro E; unfold lossless.
  apply lossless_cons.
  apply lossless_assign.
  assert (H:forall n k (m:Mem.t k),
   n = (qH1_poly k - length (m T))%nat ->
   mu ([[ tail CoinTosses ]] E m) (fone _) == 1).
  unfold tail, CoinTosses.
  induction n; intros; rewrite deno_while_elim, deno_cond_elim.
  assert (@E.eval_expr k T.Bool (Elen T <! qH1) m = false)
   by (simpl; unfold O.eval_op; simpl; apply leb_correct_conv; omega).
  rewrite H0; apply lossless_nil.
  assert (@E.eval_expr k T.Bool (Elen T <! qH1) m = true)
   by (simpl; unfold O.eval_op; simpl; apply leb_correct; omega).
  rewrite H0, deno_app_elim, deno_cons_elim, Mlet_simpl, deno_random_elim.
  transitivity
   (mu (sum_support (T.default k T.Bool) (E.eval_support {0,1}_p m)) (fone _)).
  apply mu_stable_eq; refine (ford_eq_intro _); intro v.
  rewrite deno_assign_elim; apply IHn.
  mem_upd_simpl.
  simpl; unfold O.eval_op; simpl.
  rewrite Mem.get_upd_diff, app_length; simpl; [ omega | discriminate ].
  apply sum_support_lossless.
  red; intros; eapply H; trivial.
 Qed.

 Definition I1 :=
  (fun k m1 m2 =>
   NoDup (m2 L3) /\
   map (@snd nat nat) (m2 J1) = rev (seq 0 (length (m2 L1)))) /-\
  (EP2 (E.Eforall z' (z' in_dom J1) L3)) /-\
  (EP2 (E.Eforall z ((Efst z) in_dom J1) L1)).

 Lemma dep_I1: depend_only_rel I1 Vset.empty {{L3, J1, L1}}.
 Proof.
  change {{L3, J1, L1}} with
   (Vset.union {{L3, J1, L1}} (Vset.union {{J1, L3}} {{J1, L1}})).
  change Vset.empty with
   (Vset.union Vset.empty (Vset.union Vset.empty Vset.empty)).
  repeat apply depend_only_andR.
  intros k m1 m2 m1' m2' _ H2 H.
  rewrite <- (H2 _ J1), <- (H2 _ L1), <- (H2 _ L3); trivial.
  apply depend_only_EP2.
  apply depend_only_EP2.
 Qed.

 Lemma dec_I1 : decMR I1.
 Proof.
  repeat apply decMR_and; auto.
  unfold decMR; intros.
  apply NoDup_dec.
  apply eq_nat_dec.
  unfold decMR; intros.
  match goal with
  |- sumbool (?X = ?Y) _ =>
     case_eq (eq_dec_list eq_dec_nat X Y); intros Heq H
  end.
  left; trivial.
  right; apply eq_dec_list_r with (2:=H); apply eq_dec_nat_r.
 Qed.

 Definition iE0E1_I1_empty : eq_inv_info I1 E0 E1.
  refine (@empty_inv_info I1 _ _ dep_I1 _ dec_I1 _ _).
  vm_compute; trivial.
 Defined.

 Lemma H1_E0E1_I1 : EqObsInv I1
  {{id_H, L1, P}}
  E0 H1_0
  E1 H1_1
  {{id_H, L1, P}}.
 Proof.
  cp_test (id_H in_dom L1).
  (* case [id_H in_dom L1] *)
  nil_nil_tac; intros k m1 m2 [_ [? _] ]; assumption.

  (* case [~(id_H in_dom L1)] *)
  unfold I1; eqobsrel_tail; unfold EP2, EP1; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [ [Hn H2] [H3 H4 ] ] _] ] v Hv; repeat split; mem_upd_simpl.
  simpl map; rewrite H2.
  simpl length; rewrite seq_S, rev_unit; trivial.
  bprop; intros x Hin; bprop; right.
  autorewrite with Ris_true in H3; generalize (H3 x Hin).
  mem_upd_simpl; bprop; trivial.
  rewrite nat_eqb_refl; simpl.
  bprop; intros x Hin; bprop; right.
  rewrite is_true_forallb in H4; generalize (H4 _ Hin).
  mem_upd_simpl;bprop; trivial.
 Qed.

 Lemma EX_E0E1_I1 : EqObsInv I1
  {{id_ex, L1, P, a,  L3}}
  E0 Ex_0
  E1 Ex_0
  {{id_ex, L1, P, a, L3, d_ex}}.
 Proof.
  inline (add_info H1 Vset.empty Vset.empty iE0E1_I1_empty H1_E0E1_I1) H1;
   [ apply (decMR_req_mem_rel _ dec_I1) | ].
  ep; deadcode iE0E1_I1_empty.
  unfold I1; eqobsrel_tail; unfold EP2, EP1, andR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2; mem_upd_simpl; rewrite nat_eqb_refl.
  intro H; decompose [and] H; clear H; repeat split; mem_upd_simpl; intros.


  constructor; [intro | assumption].
  destruct H6 as [_ H6]; autorewrite with Ris_true in H6; elim H6; eauto.

  simpl map; simpl length; rewrite H4, seq_S, rev_unit; trivial.

  simpl; bprop; intros x Hx.
  rewrite is_true_forallb in H2.
  generalize (H2 x Hx); mem_upd_simpl; bprop; auto.

  simpl; bprop; intros x Hx.
  rewrite is_true_forallb in H5.
  generalize (H5 x Hx); mem_upd_simpl; bprop; auto.

  simpl map; simpl length; rewrite H4, seq_S, rev_unit; trivial.

  simpl; bprop; intros x Hx.
  rewrite is_true_forallb in H2.
  generalize (H2 x Hx); mem_upd_simpl; bprop; auto.

  simpl; bprop; intros x Hx.
  rewrite is_true_forallb in H5.
  generalize (H5 x Hx); mem_upd_simpl; bprop; auto.

  constructor; [intro | assumption].
  destruct H3 as [_ H3]; rewrite is_true_negb in H3; elim H3.
  apply is_true_existsb; eauto.

  apply is_true_andb; split.
  destruct H as [_ H].
  rewrite <- is_true_negb, negb_involutive, is_true_existsb in H.
  destruct H as [ (?,?) [? ?] ].
  rewrite is_true_forallb in H5.
  apply nat_eqb_true in H6.
  rewrite H6; generalize (H5 _ H); mem_upd_simpl.

  rewrite is_true_forallb in H2 |- *.
  intros x Hx; generalize (H2 _ Hx); mem_upd_simpl.

  rewrite is_true_forallb in H5 |- *.
  intros x Hx; generalize (H5 _ Hx); mem_upd_simpl.

  rewrite is_true_forallb in H2 |- *.
  intros x Hx; generalize (H2 _ Hx); mem_upd_simpl.

  rewrite is_true_forallb in H5 |- *.
  intros x Hx; generalize (H5 _ Hx); mem_upd_simpl.
 Qed.

 Definition iE0E1_I1 :=
  let iH1 := add_info H1 {{V}} {{V}} iE0E1_I1_empty H1_E0E1_I1 in
  let iH2 := add_refl_info H2 iH1 in
  let iEx := add_info Ex {{V}} {{V}}  iH2  EX_E0E1_I1 in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) A1_wf (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) A2_wf (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Definition iE0E0 :=
  let iSetup := add_refl_info Setup (empty_info E0 E0) in
  let iH1 := add_refl_info_O H1 {{L1, id_H}} Vset.empty Vset.empty iSetup in
  let iH2 := add_refl_info_O H2 {{L2, hv}} Vset.empty Vset.empty iH1 in
  let iEncrypt := add_refl_info Encrypt iH2 in
  let iEx := add_refl_info Ex iEncrypt in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) A1_wf (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) A2_wf (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Definition iE0E1 :=
  let iH1 := add_refl_info_O H1 {{L1, id_H}} Vset.empty {{J1}} (empty_info E0 E1) in
  let iH2 := add_refl_info_O H2 {{L2, hv}} Vset.empty Vset.empty iH1 in
  let iEx := add_refl_info Ex iH2 in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) A1_wf (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) A2_wf (@A2_lossless _) (@A2_lossless _) iA1 in iA2.


 (* Postcondition used to prove [G1_prefix_post1] *)
 Lemma EqObs_G0_G1_prefix_I1:
  EqObsRel I trueR E0 G0 E1 G1_prefix {{d, d_A, id_A, L1, L2, L3}} I1.
 Proof.
  apply equiv_trans with
   (kreq_mem I)
   (kreq_mem {{d, d_A, id_A, L1, L2, L3}})
   (req_mem_rel {{d, d_A, id_A, L1, L2, L3}} I1)
   E0 G1_prefix.
  auto.
  unfold refl_supMR2, trueR; trivial.
  intros k m1 m2 m3 H1 [H2 H3]; split.
  apply req_mem_trans with m2; assumption.
  assumption.

  inline_l iE0E0 Setup; inline_l iE0E0 Encrypt.
  alloc_l iE0E0 Q_en Q_A; alloc_l iE0E0 h2_en h2; alloc_l iE0E0 r c.
  ep iE0E0; deadcode iE0E0; eqobs_in iE0E0.

  eqobs_tl iE0E1_I1.
  unfold I1; eqobsrel_tail; simpl; unfold O.eval_op; simpl.
  red; intros; repeat split; mem_upd_simpl.
 Qed.

 Lemma EqObs_G0_G1: EqObs I E0 G0 E1 G1 {{d, d_A, L2}}.
 Proof.
  rewrite (app_nil_end G0); unfold G1.
  eapply equiv_app.
  eapply equiv_sub; [ | | apply EqObs_G0_G1_prefix_I1].
  apply (proj2 (req_mem_rel_trueR I)).
  apply proj1_MR.

  apply equiv_strengthen with (kreq_mem {{d, d_A, L2}});
   [ intro k; apply req_mem_weaken; vm_compute; trivial | ].
  eapply equiv_lossless_Modify with (M1 := Vset.empty) (M2 := {{t, T}}).
  apply depend_only_kreq_mem.
  apply lossless_nil.
  apply CoinTosses_lossless.
  apply Modify_nil.
  apply modify_correct with (refl2_info (empty_info E0 E1)) Vset.empty; trivial.
  trivial.
  trivial.
 Qed.

 Lemma Pr_G0_G1_SA : forall k (m:Mem.t k),
  Pr E0 G0  m (@Success k) == Pr E1 G1 m (@Success k).
 Proof.
  intros.
  apply (equiv_deno EqObs_G0_G1); [ | trivial].
  intros m1 m2 H; unfold Success, charfun, restr, andP, EP.
  repeat (rewrite depend_only_fv_expr_subset with (2:=H);
   [ | vm_compute]; trivial).
 Qed.


 Definition I1' := EP2 (id_A in_dom L1).

 Lemma dep_I1': depend_only_rel I1' Vset.empty {{L1, id_A}}.
 Proof.
  apply depend_only_EP2.
 Qed.

 Lemma dec_I1' : decMR I1'.
 Proof.
  unfold I1'; auto.
 Qed.

 Definition iE0E1_I1'_empty : eq_inv_info I1' E0 E1.
  refine (@empty_inv_info I1' _ _ dep_I1' _ dec_I1' _ _).
  vm_compute; trivial.
 Defined.

 Lemma H1_E0E1_I1' : EqObsInv I1'
  {{id_H, L1, P}}
  E0 H1_0
  E1 H1_1
  {{id_H, L1, P}}.
 Proof.
  cp_test (id_H in_dom L1).
  nil_nil_tac; intros k m1 m2 [_ [? _] ]; assumption.
  unfold I1'; eqobsrel_tail; unfold EP2, EP1; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [H1 _] ] v Hv.
  rewrite H1, orb_true_r; trivial.
 Qed.

 Definition iE0E1_I1' :=
  let iH1 := add_info H1 {{V}} {{V}} iE0E1_I1'_empty H1_E0E1_I1' in
  let iH2 := add_refl_info H2 iH1 in
  let iEx := add_refl_info_O Ex {{id_ex, L1, P, a, L3, d_ex}} Vset.empty Vset.empty iH2 in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 (* Postcondition is used to prove [G1_prefix_post3] *)
 Lemma EqObs_G0_G1_prefix_I1': EqObsRel 
  I trueR
  E0 G0
  E1 G1_prefix
  {{d, d_A, id_A, L1, L2, L3}} I1'.
 Proof.
  apply equiv_trans with
   (kreq_mem I)
   (kreq_mem {{d, d_A, id_A, L1, L2, L3}})
   (req_mem_rel {{d, d_A, id_A, L1, L2, L3}} I1')
   E0 G1_prefix.
  auto.
  unfold refl_supMR2, trueR; trivial.
  intros k m1 m2 m3 H1 [H2 H3]; split.
  apply req_mem_trans with m2; assumption.
  assumption.

  inline_l iE0E0 Setup; inline_l iE0E0 Encrypt.
  alloc_l iE0E0 Q_en Q_A; alloc_l iE0E0 h2_en h2; alloc_l iE0E0 r c.
  ep iE0E0; deadcode iE0E0; eqobs_in iE0E0.

  eqobs_hd_n iE0E1 14%nat.
  eqobs_tl_n iE0E1_I1' 5%nat.
  inline iE0E1_I1' H1.
  ep; deadcode iE0E1_I1'.
  unfold I1'; eqobsrel_tail; simpl; unfold O.eval_op; simpl.
  split.
  intros; rewrite nat_eqb_refl; trivial.
  intros [_ H1]; rewrite is_true_negb_false in H1.
  apply (not_false_is_true _ H1).
 Qed.

 Close Scope nat_scope.
 Open Scope U_scope.

 Lemma G1_prefix_post1 : forall k (m:Mem.t k),
  range (@S k) ([[G1_prefix]] E1 m).
 Proof.
  intros; apply mu_range.
  transitivity (mu ([[G0]] E0 m) (charfun (@S k))).
  symmetry; apply (equiv_deno EqObs_G0_G1_prefix_I1).
  intros m1 m2 [H _]; unfold S, EP, charfun, restr, andP.
  repeat (rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | vm_compute]; trivial).
  split; unfold trueR; trivial.
  transitivity (mu ([[G0]] E0 m) (fone _)).
  apply range_mu; apply A_hyp.
  apply is_lossless_correct with (refl1_info iE0E0); vm_compute; trivial.
 Qed.


 Definition post2 k :=
  (fun m:Mem.t k => if NoDup_dec eq_nat_dec (m L3) then true else false) [&&]
  (fun m:Mem.t k => eqb_list nat_eqb
   (map (@snd nat nat) (m J1)) (rev (seq 0 (length (m L1))))) [&&]
  EP k (E.Eforall z' (z' in_dom J1) L3) [&&]
  EP k (E.Eforall z (Efst z in_dom J1) L1).

 Lemma G1_prefix_post2 : forall k (m:Mem.t k),
  range (@post2 k) ([[G1_prefix]] E1 m).
 Proof.
  intros; apply mu_range.
  transitivity (mu ([[G0]] E0 m) (fone _)).
  symmetry; apply equiv_deno with (1:=EqObs_G0_G1_prefix_I1).
  intros m1 m2 [H1 [ [H0 H2] [H3 H4] ] ]; unfold  post2, EP, andP, fone.
  rewrite H2, H3, H4.
  case (NoDup_dec eq_nat_dec (m2 L3)); [ | tauto].
  match goal with
   |- context [eqb_list _ ?l _] =>
      generalize (eqb_list_spec _ nat_eqb_spec l l);
      destruct (eqb_list nat_eqb l l); intuition
  end.
  split; intuition.
  apply is_lossless_correct with (refl2_info iE0E0); vm_compute; trivial.
 Qed.

 Definition post3 k := EP k (id_A in_dom L1).

 Lemma G1_prefix_post3 : forall k (m:Mem.t k),
  range (@post3 k) ([[G1_prefix]] E1 m).
 Proof.
  intros; apply mu_range.
  transitivity (mu ([[G0]] E0 m) (fone _)).
  symmetry; apply (equiv_deno EqObs_G0_G1_prefix_I1').
  intros m1 m2 [_ H2]; unfold  post3, EP, fone.
  rewrite H2; trivial.
  split; intuition.
  apply is_lossless_correct with (refl1_info iE0E0); vm_compute; trivial.
 Qed.

 Lemma G1_prefix_post:  forall k (m:Mem.t k),
  range (@S k [&&] @post2 k [&&] @post3 k) ([[G1_prefix]] E1 m).
 Proof.
  intros k m.
  apply mu_range_and.
  apply is_lossless_correct with (refl2_info iE0E1); vm_compute; trivial.
  apply G1_prefix_post1.
  apply mu_range_and.
  apply is_lossless_correct with (refl2_info iE0E1); vm_compute; trivial.
  apply G1_prefix_post2.
  apply G1_prefix_post3.
 Qed.


 (** Here begins the proof of the exact probability of [GoodToss] and
    its independence from [Success] in [G1] *)

 (** Optimum value for probability [p] *)
 Definition p k : U := [1/]1+(qEX_poly k).

 Fixpoint A k l j : Mem.t k -o> U :=
  match l with
   | nil => fun m => if nth j (m T) false then 1 else 0
   | i'::l => Fmult (A l j) (fun m => if nth i' (m T) false then 0 else 1)
  end.

 Fixpoint Af k (m:Mem.t k) l j :=
  match l with
   | nil =>
     if leb (Datatypes.S j) (length (m T)) then
      if nth j (m T) false then 1 else 0
     else p k
   | i'::l => Af m l j *
     if leb (Datatypes.S i') (length (m T)) then
      if nth i' (m T) false then 0 else 1
     else [1-] (p k)
  end.

 Lemma Permutation_A : forall l1 l2,
  Permutation l1 l2 ->
  forall k (m:Mem.t k) j, A l1 j m == A l2 j m.
 Proof.
  intros; induction H; intros.
  trivial.
  simpl; unfold Fmult; rewrite IHPermutation; trivial.
  simpl; unfold Fmult; repeat rewrite <- Umult_assoc; auto.
  rewrite IHPermutation1; trivial.
 Qed.

 Lemma Permutation_Af : forall l1 l2,
  Permutation l1 l2 ->
  forall k (m:Mem.t k) j, Af m l1 j == Af m l2 j.
 Proof.
  intros; induction H.
  trivial.
  simpl; rewrite IHPermutation; trivial.
  simpl; repeat rewrite <- Umult_assoc; auto.
  rewrite IHPermutation1; trivial.
 Qed.

 Lemma Af_0 : forall k (m:Mem.t k),
  m T = nil ->
  forall l j, Af m l j == p k * ([1-] p k) ^ length l.
 Proof.
  clear.
  induction l; intros; simpl.
  rewrite H; simpl; Usimpl; trivial.
  rewrite IHl, H; simpl.
  rewrite <- Umult_assoc; auto.
 Qed.

 Open Scope nat_scope.

 Opaque leb.

 Lemma Pr_eq : forall E k (m:Mem.t k) l j,
  ~In j l ->
  j < qH1_poly k ->
  NoDup l ->
  (forall a, In a l -> a < qH1_poly k) ->
  (mu ([[tail CoinTosses]] E m) (A l j) == Af m l j)%U.
 Proof.
  clear; intros E k m l j Hj Hjlt Hl Hlt.
  apply Sorted_lt_NoDup in Hl.
  destruct Hl as [l' [H1 H2] ].
  transitivity (mu ([[tail CoinTosses]] E m) (A l' j)).
  apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
  apply (Permutation_A H2).
  rewrite (Permutation_Af H2).
  assert (forall a, In a l' -> a < qH1_poly k).
  intros; apply Hlt.
  apply Permutation_sym in H2.
  apply Permutation_in with l'; trivial.
  assert (~In j l').
  intros Hj'; elim Hj.
  apply Permutation_sym in H2.
  apply Permutation_in with l'; trivial.
  clear l Hlt Hj H2; rename l' into l, H into Hlt, H1 into Hl.
  remember (qH1_poly k - length (m T)) as n.
  generalize n l m Hl Hlt H0 Heqn; clear n l m Hl H0 Hlt Heqn.
  induction n; unfold tail, CoinTosses; intros.

  (* |T| >= Q *)
  rewrite deno_while_elim, deno_cond_elim.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite leb_correct_conv; [ | omega].
  rewrite deno_nil_elim.
  induction l.
  simpl.
  rewrite leb_correct; [ | omega]; trivial.
  simpl; unfold Fmult.
  rewrite IHl.
  Usimpl.
  rewrite leb_correct; [ trivial | ].
  assert (a < qH1_poly k) by intuition; omega.
  inversion Hl; trivial.
  intuition.
  intuition.

  (* |T| <= qH1 *)
  rewrite deno_while_elim, deno_cond_elim.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite leb_correct; [ | omega].
  rewrite deno_app_elim, deno_cons_elim, Mlet_simpl.
  rewrite deno_sample_p, deno_assign_elim, deno_assign_elim.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op; mem_upd_simpl.
  rewrite IHn;
   [ | trivial | trivial | trivial | mem_upd_simpl; rewrite app_length; simpl; omega ].
  rewrite IHn;
   [ | trivial | trivial | trivial | mem_upd_simpl; rewrite app_length; simpl; omega ].
  clear IHn Hlt; induction Hl; simpl.
  simpl; mem_upd_simpl; repeat rewrite app_length; simpl.
  case_eq (leb (Datatypes.S j) (length (m T))); intro.
  apply leb_complete in H.
  rewrite leb_correct; [ | omega].
  rewrite app_nth1, app_nth1; [ | omega | omega].
  case (nth j (m T) false); repeat Usimpl; trivial.

  apply leb_complete_conv in H.
  case (eq_nat_dec j (length (m T))); intro.
  rewrite leb_correct; [ | omega].
  subst; rewrite nth_app, nth_app; repeat Usimpl; trivial.

  rewrite leb_correct_conv; [ | omega].
  rewrite <- Udistr_plus_right; auto.

  simpl; mem_upd_simpl; repeat rewrite app_length; simpl.
  case_eq (leb (Datatypes.S a) (length (m T))); intro.
  apply leb_complete in H1.
  rewrite leb_correct; [ | omega].
  rewrite app_nth1, app_nth1; [ | omega | omega].
  case (nth a (m T) false); repeat Usimpl; trivial.
  apply IHHl; intuition.

  apply leb_complete_conv in H1.
  case (eq_nat_dec a (length (m T))); intro.
  rewrite leb_correct; [ | omega].
  subst; rewrite nth_app, nth_app; repeat Usimpl.
  clear IHHl; induction Hl; simpl.

  mem_upd_simpl; rewrite app_length; simpl.
  case_eq (leb (Datatypes.S j) (length (m T))); intro.
  apply leb_complete in H2.
  rewrite leb_correct; [ | omega].
  rewrite app_nth1; [ | omega].
  case (nth j (m T) false); repeat Usimpl; trivial.

  apply leb_complete_conv in H2.
  case (eq_nat_dec j (length (m T))); intro.
  rewrite leb_correct; [ | omega].
  subst; rewrite nth_app; repeat Usimpl; trivial.
  elim H0; intuition.
  rewrite leb_correct_conv; [ | omega]; trivial.

  mem_upd_simpl; rewrite app_length; simpl.
  inversion_clear H.
  rewrite leb_correct_conv; [ | omega].
  rewrite leb_correct_conv; [ | omega].
  rewrite Umult_assoc.
  Usimpl.
  apply IHHl.
  destruct l; constructor.
  transitivity a.
  trivial.
  inversion H2; trivial.
  firstorder.

  rewrite leb_correct_conv; [ | omega].
  rewrite Umult_assoc, Umult_assoc, <- Udistr_plus_right, IHHl; auto.
  intuition.
 Qed.

 Close Scope nat_scope.

 Lemma Pr_GoodToss : forall k (m:Mem.t k),
  (@S k [&&] @post2 k [&&] @post3 k) m ->
  p k * ([1-] p k) ^ qEX_poly k == Pr E1 CoinTosses m (@GoodToss k).
 Proof.
  intros k m'; unfold Pr, CoinTosses.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  simpl E.eval_expr; set (m:=m'{!T <-- nil!}).

  unfold S, post2, post3, andP, EP.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op; bprop; 
  intros [ [H2 [H0 H5] ] [ [H1 [H4 [H7 H9] ] ]  H6 ] ].

  apply nat_eqb_true in H5.
  apply leb_complete in H0.
  generalize (eqb_list_spec nat_eqb nat_eqb_spec
   (map (@snd nat nat) (m' J1))
   (rev (seq 0 (length (m' L1)))) ).
  rewrite H4; clear H4; intro H4.

  assert (H10:E.eval_expr (id_A in_dom J1) m).
  simpl; unfold O.eval_op; simpl.
  destruct H6 as [x [Hx Heq] ].
  generalize (H9 x Hx).
  unfold m; mem_upd_simpl.
  apply nat_eqb_true in Heq; rewrite Heq; trivial.

  assert (H11:(E.eval_expr (J1[{id_A}]) m < qH1_poly k)%nat).
  eapply lt_le_trans with (2:=H0).
  apply in_dom_In in H10.
  apply (in_map (@snd nat nat)) in H10.
  generalize H10.
  unfold m; mem_upd_simpl.
  rewrite H4, <- In_rev.
  simpl; unfold O.eval_op; simpl; mem_upd_simpl.
  intro Hin; apply In_seq_le in Hin; omega.

  assert (H12:forall n, In n (m' L3) ->
   (E.eval_expr (J1[{n}]) m' < qH1_poly k)%nat).
  intros x Hx.
  assert (E.eval_expr (x in_dom J1) m').
  simpl; unfold O.eval_op; simpl.
  generalize (H7 _ Hx); mem_upd_simpl.
  eapply lt_le_trans with (2:=H0).
  apply in_dom_In in H.
  apply (in_map (@snd nat nat)) in H.
  generalize H; rewrite H4, <- In_rev.
  simpl; unfold O.eval_op; simpl; mem_upd_simpl.
  intro Hin; apply In_seq_le in Hin; omega.

  transitivity (Af m
   (map (fun z:nat => E.eval_expr (J1[{z}]) m) (m L3))
   (E.eval_expr (J1[{id_A}]) m)).
  rewrite Af_0, map_length.
  unfold m; mem_upd_simpl.
  rewrite H5; trivial.
  unfold m; mem_upd_simpl.

  rewrite (@Modify_deno_elim E1 {{T,t}});
   [ | apply modify_correct with (refl1_info (empty_info E1 E1)) Vset.empty;
    vm_compute; trivial ].
  rewrite <- Pr_eq; trivial.
  apply mu_stable_eq; refine (ford_eq_intro _); intro m1.
  unfold GoodToss, EP, charfun, restr, andP, andb, fone.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  mem_upd_simpl.
  clear; induction (m L3); simpl.
  case (nth (O.assoc (nat_eqb (m id_A)) 0%nat (m J1)) (m1 T) false); trivial.
  mem_upd_simpl; unfold Fmult; rewrite IHi.
  case (nth (O.assoc (nat_eqb (m id_A)) 0%nat (m J1)) (m1 T) false); trivial.
  case (nth (O.assoc (nat_eqb a) 0%nat (m J1)) (m1 T) false); trivial.

  rewrite in_map_iff; intros [x [Heq Hin] ].
  case (eq_nat_dec (m id_A) x); intro Hx.

  (* id_A = x *)
  subst; elim H2.
  exists (m id_A); split.
  generalize Hin; unfold m; mem_upd_simpl.
  unfold m; mem_upd_simpl; apply nat_eqb_refl.

  (* id_A <> x *)
  generalize H7.
  unfold m in Hin; rewrite Mem.get_upd_diff in Hin; [ | discriminate].
  intro H8; generalize (H8 x Hin); clear Hin H8.
  mem_upd_simpl.
  change (E.eval_expr (x in_dom J1) m' -> False); intro.
  apply in_dom_In in H.
  apply in_dom_In in H10.
  rewrite <- Heq in H10.
  elim Hx.
  eapply NoDup_snd with _ (m' J1) _.
  rewrite H4; apply NoDup_rev; apply NoDup_seq.
  generalize H10; simpl; unfold O.eval_op; simpl.
  unfold m; mem_upd_simpl.
  intro H3; eexact H3.
  trivial.

  apply NoDup_map_inj.
  unfold m; mem_upd_simpl.
  intros x y Hx Hy H.
  assert (E.eval_expr (x in_dom J1) m').
  simpl; unfold O.eval_op; simpl.
  generalize (H7 _ Hx); mem_upd_simpl.
  assert (E.eval_expr (y in_dom J1) m').
  simpl; unfold O.eval_op; simpl.
  generalize (H7 _ Hy); mem_upd_simpl.

  eapply NoDup_snd with _ (m' J1) _.
  rewrite H4; apply NoDup_rev; apply NoDup_seq.
  apply in_dom_In in H3; eexact H3.
  generalize H.
  simpl; unfold O.eval_op; simpl; mem_upd_simpl.
  intro Heq; rewrite Heq.
  apply in_dom_In in H8; eexact H8.

  unfold m; mem_upd_simpl.
  destruct (NoDup_dec eq_nat_dec (m' L3)); [ trivial | discriminate].

  intros; apply in_map_iff in H.
  destruct H as [x [Heq Hin] ].
  unfold m in Hin; rewrite Mem.get_upd_diff in Hin; [ | discriminate].
  generalize (H12 x Hin); rewrite <- Heq.
  simpl; unfold O.eval_op; simpl; unfold m; mem_upd_simpl.
 Qed.

 Lemma S2_indpt : forall k (m:Mem.t k),
  Pr E1 CoinTosses m (@S2 k) ==
  charfun (@Success k) m * Pr E1 CoinTosses m (@GoodToss k).
 Proof.
  intros; unfold Pr.
  rewrite (@Modify_deno_elim E1 {{t, T}});
   [ | apply modify_correct with (refl2_info iE0E1) Vset.empty;
       vm_compute; trivial ].
  symmetry.
  rewrite (@Modify_deno_elim E1 {{t, T}});
   [ | apply modify_correct with (refl2_info iE0E1) Vset.empty;
       vm_compute; trivial ].
  unfold S2, Success, charfun, restr, EP, andP, andb, fone.
  case_eq (@E.eval_expr _ T.Bool (d =?= d_A) m).
  intros H; Usimpl.
  apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
  rewrite (@depend_only_fv_expr T.Bool (d =?= d_A) _ (m{! {{t,T}} <<- m'!}) m).
  rewrite H; trivial.
  apply req_mem_update_disjoint; trivial.
 
  transitivity (mu ([[CoinTosses]] E1 m) (fzero _)).
  rewrite mu_zero; trivial.
  apply mu_stable_eq; refine (ford_eq_intro _); intro m'.

  rewrite (@depend_only_fv_expr T.Bool (d =?= d_A) _ (m{! {{t,T}} <<- m'!}) m).
  rewrite H; trivial.
  apply req_mem_update_disjoint; trivial.
 Qed.

 Lemma Pr_G1_GoodToss : forall k (m:Mem.t k),
  Pr E1 G1 m (@GoodToss k) == p k * ([1-] p k)^qEX_poly k.
 Proof.
  intros; unfold Pr, G1.
  rewrite deno_app_elim.
  transitivity (mu ([[G1_prefix]] E1 m) (fcte _ (p k * ([1-] p k)^qEX_poly k))).
  apply (range_eq (G1_prefix_post m)).
  intros; symmetry; apply Pr_GoodToss; trivial.

  symmetry; rewrite mu_cte, <- Umult_one_right at 1.
  apply Umult_eq_compat_right.
  symmetry.
  apply (is_lossless_correct (refl2_info iE0E1)); vm_compute; trivial.
 Qed.

 Lemma Pr_G1_S2 : forall k (m:Mem.t k),
  Pr E1 G1 m (@S2 k) == Pr E1 G1 m (@Success k) * p k * ([1-] p k)^qEX_poly k.
 Proof.
  intros; unfold G1, Pr.
  rewrite <- Umult_assoc, deno_app_elim, deno_app_elim.
  transitivity (mu ([[G1_prefix]] E1 m)
   (fun m => charfun (@Success k) m * Pr E1 CoinTosses m (@GoodToss k))).
  apply mu_stable_eq; refine (ford_eq_intro _); apply S2_indpt.
  rewrite <- mu_stable_mult_right.
  apply (range_eq (G1_prefix_post m)); intros m' Hm'.
  apply Umult_eq_compat.
  rewrite (@Modify_deno_elim E1 {{t,T}}).
  unfold Success, charfun, restr, EP, andP, andb, fone.
  transitivity (mu ([[CoinTosses]] E1 m')
   (fcte _ (if E.eval_expr (d =?= d_A) m' then 1 else 0))).
  rewrite mu_cte, (CoinTosses_lossless E1 m'), Umult_one_right; trivial.
  apply mu_stable_eq; refine (ford_eq_intro _); intro m''.
  rewrite (@depend_only_fv_expr _ _ _ (m'{! {{t, T}} <<- m''!}) m');
   [ | apply req_mem_update_disjoint ]; trivial.
  apply modify_correct with (refl2_info iE0E1) Vset.empty; vm_compute; trivial.
  symmetry; apply Pr_GoodToss; trivial.
 Qed.


 (** * G1 --> G2 *)

 (*
   CHANGES IN THE GAME:
   1) Use Coron's technique to simulate [H1]. Use invariant
   I2 and lemma [G1_padding] to prove that the simulation
   is perfect.

   RESULTS REGARDING PROBABILITY OF EVENTS:
   1) Probabilities of [Success /\ GoodToss] and [GoodToss]
    are preserved (games are observationally equivalent)
 *)

 Definition G2 :=
  [
   T <- Nil _;
   while Elen T <! qH1 do [ t <$- {0,1}_p; T <- T |++| (t |::| Nil _) ];
   L1 <- Nil _; L2 <- Nil _; L3 <- Nil _; J1 <- Nil _; V <- Nil _;
   P <$- G1o;
   a <$- [1..q-1];
   Ppub <- a |.| P;
   b <$- [1..q-1];
   r1 <c- A1 with {};
   id_A <- Esnd r1;
   m0 <- Efst (Efst r1); m1 <- Esnd (Efst r1);
   d <$- {0,1};
   If d then [ m_d <- m0 ] else [ m_d <- m1 ];
   Q_A <c- H1 with {id_A};
   g <- e(Q_A,Ppub);
   c <$- [1..q-1];
   h2 <c- H2 with { g |^| c };
   y <- (c |.| P | h2 |x| m_d);
   d_A <c- A2 with {y}
  ].

 Definition H1_2 :=
  [
   If !(id_H in_dom L1) _then
   [
    v <$- [1..q-1];
    V <- (id_H | v) |::| V;
    J1 <- (id_H | Elen L1) |::| J1;
    If Enth {Elen L1, T} then
     [ L1 <- (id_H | (b *! v) |.| P) |::| L1 ]
    else
     [ L1 <- (id_H | v |.| P) |::| L1 ]
   ]
  ].

 Definition E2 := make_env H1_2 H2_0 Ex_0.


 Definition I2 := EP2 (0%nat << b !<! q) /-\ EP2 (!(log P =?= 0%nat)).

 Lemma dep_I2 : depend_only_rel I2 Vset.empty {{b,P}}.
 Proof.
  change Vset.empty with (Vset.union Vset.empty Vset.empty) at 1.
  change {{b,P}} with (Vset.union {{b}} {{P}}).
  apply depend_only_andR; apply depend_only_EP2.
 Qed.

 Lemma dec_I2 : decMR I2.
 Proof.
  unfold I2; auto.
 Qed.

 Definition iE1E2_empty : eq_inv_info I2 E1 E2 :=
   (@empty_inv_info I2 _ _ dep_I2 (eq_refl _) dec_I2 E1 E2).


 Lemma H1_E1E2_I2 : EqObsInv I2
  {{b, id_H, L1, P, J1, T}}
  E1 H1_1
  E2 H1_2
  {{b, id_H, L1, P, J1, T}}.
 Proof.
  cp_test (id_H in_dom L1); rewrite proj1_MR.

  (* case [id_H in_dom L1] *)
  nil_nil_tac; intros k m1 m2 [_ [? _] ]; assumption.

  (* case [~(id_H in_dom L1)] *)
  apply equiv_trans with
    (req_mem_rel {{b, id_H, L1, P, J1, T}} I2)
    (kreq_mem {{b, id_H, L1, P, J1, T}})
    (req_mem_rel {{b, id_H, L1, P, J1, T}} I2)
    E1
    [ 
      J1 <- (id_H | Elen L1) |::| J1; 
      b' <- 1%nat;
      P1 <$- G1o; 
      If Enth {Elen L1, T}
      then [ v <- (b ^-1) *! ((log P1) *! ((log P) ^-1)) mod_q]  
      else [ v <- (b' ^-1) *! ((log P1) *! ((log P) ^-1)) mod_q]; 
      L1 <- (id_H | P1) |::| L1
    ].
    apply (decMR_req_mem_rel _ dec_I2).
    intros k m1 m2 [H ?]; split; [ trivial | ].
    refine (@dep_I2 _ _ _ _ _ (req_mem_refl _ _) (req_mem_sym _) H0);
      apply req_mem_weaken with (2:=H); apply eq_refl.
    intros k m1 m2 m3 H [? ?]; split; [ apply req_mem_trans with m2; auto | trivial].
    deadcode; [ apply (decMR_req_mem_rel _ dec_I2) | swap; eqobs_in ].

  apply equiv_trans with
    (req_mem_rel {{b, id_H, L1, P, J1, T}} I2)
    (kreq_mem {{b, id_H, L1, P, J1, T}})
    (req_mem_rel {{b, id_H, L1, P, J1, T}} I2)
    E1
    [
      J1 <- (id_H | Elen L1) |::| J1;
      b' <- 1%nat;
      v <$- [1..q-1];
      If Enth {Elen L1, T}
      then [P1 <- (b *! v) |.| P]
      else [P1 <- (b' *! v) |.| P ];
      L1 <- (id_H | P1) |::| L1
    ].
    apply (decMR_req_mem_rel _ dec_I2).
    intros k m1 m2 [H ?]; split; [ trivial | ].
    refine (@dep_I2 _ _ _ _ _ (req_mem_refl _ _) (req_mem_sym _) H0);
      apply req_mem_weaken with (2:=H); apply eq_refl.
    intros k m1 m2 m3 H [? ?]; split; [ apply req_mem_trans with m2; auto | trivial].
    2:(ep iE1E2_empty; cp_test (Enth {Elen L1, T});
      deadcode iE1E2_empty; swap iE1E2_empty;
      eqobs_in iE1E2_empty; intros k m1 m2 (_,(?,_)); trivial).

    eqobs_hd_n (@empty_inv_info I2 _ _ dep_I2 (eq_refl _) dec_I2 E1 E1) 1%nat. 
    eqobs_tl.
    apply equiv_weaken_kreq_mem with trueR.
    apply equiv_union_Modify with {{v,P1,b'}} {{P1,v,b'}}; [ | apply dec_I2 | ].
      split; apply modify_correct with (refl1_info iE1E2_empty) Vset.empty; apply eq_refl.
    simpl; unfold req_mem_rel; rewrite andR_trueR_r.
    match goal with 
      |- equiv (kreq_mem ?X /-\ _) _ _ _ _ _ => 
        apply equiv_cons with (req_mem_rel (Vset.add b' X) (I2 /-\ (EP2 (0%nat << b' !<! q)))); simpl
    end.
    eqobsrel_tail; expr_simpl; intros k m1 m2 (H1,H2); split.
    refine (@dep_I2 _ _ _ _ _ (req_mem_refl _ _) (req_mem_upd_notin_r _ 
      (req_mem_refl _ _) _) H2); discriminate.
    rewrite leb_correct, leb_correct; trivial; apply (p_bound (q_prime k)).
    cp_test (Enth {Elen L1, T}); rewrite proj1_MR.
      (* coin = true *)
      rewrite <-(@implMR_kreq_mem_subset (Vset.union {{P, b}} {{P1, v}}) 
        {{P1}}); [ | apply eq_refl ].
      deadcode; [ auto using dec_I2 | ]. 
      eapply equiv_strengthen; [ | apply G1_padding; discriminate ].    
      unfold I2, EP1, EP2; intros k m1 m2 (H1,((H2,H3),_)); repeat split.
        apply req_mem_weaken with (2:=H1); apply eq_refl.
        assumption.
        unfold is_true in *; rewrite <- H3;
          refine (@depend_only_fv_expr_subset T.Bool _ _ _ _ _ _ H1); apply eq_refl.
      (* coin = false *)
      rewrite <-(@implMR_kreq_mem_subset (Vset.union {{P, b'}} {{P1, v}}) 
        {{P1}}); [ | apply eq_refl ].
      deadcode; [ auto using dec_I2 | ]. 
      eapply equiv_strengthen; [ | apply G1_padding; discriminate ].    
      unfold I2, EP1, EP2; intros k m1 m2 (H1,((_,H3),H2)); repeat split.
        apply req_mem_weaken with (2:=H1); apply eq_refl.
        assumption.
        unfold is_true in *; rewrite <- H3;
          refine (@depend_only_fv_expr_subset T.Bool _ _ _ _ _ _ H1); apply eq_refl.
  Qed.



  

 Definition iE1E2 :=
  let iH1 := add_info H1 Vset.empty Vset.empty iE1E2_empty H1_E1E2_I2 in
  let iH2 := add_refl_info H2 iH1 in
  let iEx := add_refl_info_O Ex {{id_ex, b, L1, P, a, L3, J1, d_ex}} Vset.empty Vset.empty iH2  in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Lemma EqObs_G1_G2: EqObs
  I
  E1 G1
  E2 G2
  {{d, d_A, id_A, L1, L2, L3, J1, T}}.
 Proof.
  swap iE1E2; eqobs_tl iE1E2.
  match goal with 
  |- equiv (kreq_mem ?I') _ ?c1 _ ?c2 _ =>
     rewrite <- (firstn_skipn 2 c1), <- (firstn_skipn 2 c2);
     apply equiv_app with (kreq_mem (Vset.add T I')); simpl
  end.
  eqobs_in.
  unfold I2; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
  red; intros; unfold is_true; rewrite andb_true_iff; split.
    apply In_seq_le in H2; split; apply leb_correct; omega.
    unfold G1_support in H0; rewrite in_map_iff in H0; destruct H0 as 
      [n [ H1n H2n] ]; clear -H1n H2n; apply In_seq_le in H2n; rewrite <-G1_order in H2n.
    rewrite <-H1n, G1.log_pow.
    replace (G1.log (G1.g k)) with 1%nat; [ |
      rewrite (G1.log_spec (G1.g k)), G1.log_pow, G1_order, G1.log_g, mult_1_l, 
        mod_small; trivial; [
          split; [ auto | apply (p_bound (q_prime k)) ] |
          rewrite G1_order; apply (p_bound (q_prime k)) ] ].
    rewrite mult_1_r, mod_small; [ | split ; [  apply le_0_n | omega ] ].
    generalize (nat_eqb_spec n 0); case_eq (nat_eqb n 0); intros;
      [ subst; elimtype False; omega | trivial ].
 Qed.
 
 Lemma Pr_G1_G2_S2 : forall k (m:Mem.t k),
  Pr E1 G1  m (@S2 k) == Pr E2 G2 m (@S2 k).
 Proof.
  intros.
  apply equiv_deno with (1:=EqObs_G1_G2); [ | trivial].
  intros m1 m2 H; unfold S2, Success, GoodToss.
  rewrite_req_mem_l H.
 Qed.

 Lemma Pr_G1_G2_GT : forall k (m:Mem.t k),
  Pr E1 G1  m (@GoodToss k) == Pr E2 G2 m (@GoodToss k).
 Proof.
  intros.
  apply equiv_deno with (1:=EqObs_G1_G2); [ | trivial].
  intros m1 m2 H; unfold GoodToss.
  rewrite_req_mem_l H.
 Qed.


 (** * G2 --> G3 *)

 (*
    CHANGES IN THE GAME:
    1) Change the bitstring used to mask the plaintext during
    encryption (now we use [H2(g^v')] instead of [H2(g^c)]).
    Used invariant I3 and lemma [pow_uniform_G1_G2] to prove
    observational equivalence.

    RESULTS REGARDING PROBABILITY OF EVENTS:
    1) Probabilities of [Success /\ GoodToss] and [GoodToss]
    are preserved (due to the obs. equiv. of games).
 *)

 Definition G3 :=
  [
   T <- Nil _;
   while Elen T <! qH1 do [ t <$- {0,1}_p; T <- T |++| (t |::| Nil _) ];
   L1 <- Nil _; L2 <- Nil _; L3 <- Nil _; J1 <- Nil _; V <- Nil _;
   P <$- G1o;
   a <$- [1..q-1];
   Ppub <- a |.| P;
   b <$- [1..q-1];
   r1 <c- A1 with {};
   id_A <- Esnd r1;
   m0 <- Efst (Efst r1); m1 <- Esnd (Efst r1);
   d <$- {0,1};
   If d then [ m_d <- m0 ] else [ m_d <- m1 ];
   Q_A <c- H1 with {id_A};
   c <$- [1..q-1];
   v' <- (V[{id_A}]^-1 *! c) mod_q;
   g <- e(Q_A,Ppub);
   h2 <c- H2 with { g |^| v'};
   y <- (v' |.| P | h2 |x| m_d);
   d_A <c- A2 with {y}
  ].

 Definition E3 := E2.

(*** ****)

 Definition I3 :=
   EP1 (E.Eforall z (0%nat << V[{Efst z}] !<! q) L1).

 Lemma dep_I3 : depend_only_rel I3 {{V, L1}} Vset.empty.
 Proof.
  apply depend_only_EP1.
 Qed.

 Lemma dec_I3 : decMR I3.
 Proof.
  apply decMR_EP1; auto.
 Qed.

 Definition iE2E3_I3_empty : eq_inv_info I3 E3 E3.
  refine (@empty_inv_info I3 _ _ dep_I3 _ dec_I3 _ _).
  vm_compute; trivial.
 Defined.

 Lemma H1_E2E3_I3 : EqObsInv I3
  {{T, J1, b, id_H, L1, P, V}}
  E2 H1_2
  E3 H1_2
  {{T, J1, b, id_H, L1, P, V}}.
 Proof.
  unfold H1_2.
  cp_test (id_H in_dom L1).
  (* case [id_H in_dom L1] *)
  nil_nil_tac; intros k m1 m2 [_ [? _] ]; assumption.
  (* case [~(id_H in_dom L1)] *)
  unfold I3; eqobsrel_tail; unfold EP1, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H1 [H2 [H3 _] ] ].
  repeat split; intros. 

  destruct (In_seq_le _ _ _ H)as [Hv1 Hv2]; clear H.
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.  
  rewrite leb_correct, leb_correct; [ simpl| omega | trivial ].
  autorewrite with Ris_true in *; intros uv Huv.
  case_eq (nat_eqb (fst uv) (m1 id_H)); intro Heq.
    elim H3; exists uv; split; [ | rewrite nat_eqb_sym ]; trivial.
    generalize (H2 _ Huv); mem_upd_simpl; omega.

  destruct (In_seq_le _ _ _ H)as [Hv1 Hv2]; clear H.
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.  
  rewrite leb_correct, leb_correct; [ simpl| omega | trivial ].
  autorewrite with Ris_true in *; intros uv Huv.
  case_eq (nat_eqb (fst uv) (m1 id_H)); intro Heq.
    elim H3; exists uv; split; [ | rewrite nat_eqb_sym ]; trivial.
    generalize (H2 _ Huv); mem_upd_simpl; omega.
 Qed.


 Definition iE2E3_I3 :=
  let iH1 := add_info H1 Vset.empty Vset.empty iE2E3_I3_empty H1_E2E3_I3 in
  let iH2 := add_refl_info H2 iH1 in
  let iEx := add_refl_info Ex iH2 in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.


 Definition iE2E3 :=
  let iH1 := add_refl_info_O H1 {{P, b, T, V, J1, L1, id_H}} Vset.empty Vset.empty (empty_info E3 E3) in
  let iH2 := add_refl_info_O H2 {{L2, hv}} Vset.empty Vset.empty iH1 in
  let iEx := add_refl_info_O Ex {{L3, a, P, L1, V, b, J1, T, d_ex}} Vset.empty Vset.empty iH2 in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.


 Open Scope nat_scope.

 Lemma EqObs_G2_G3 : EqObs
  I
  E2 G2
  E3 G3
  {{J1, T, L1, L2, L3, id_A, d, d_A}}.
 Proof.
  eqobs_hd_n (empty_info E2 E3) 2%nat.

  (* Annotation before call to A1 *)
  match goal with
  |- EqObs ?I' _ ?c _ ?c' _ =>
     rewrite <- (firstn_skipn 9 c);
     rewrite <- (firstn_skipn 9 c');
     apply equiv_app with
      (req_mem_rel (Vset.union {{L1, L2, L3, V, J1, P, a, Ppub, b}} I') I3);
      simpl
  end.
  unfold I3; eqobsrel_tail; simpl; unfold O.eval_op; simpl; split.

  (* Annotation after call to H1 *)
  eqobs_hd_n iE2E3_I3 6%nat.
  inline iE2E3_I3 H1; [apply (decMR_req_mem_rel _ dec_I3) | ].
  ep iE2E3_I3; deadcode iE2E3_I3.
  match goal with
   |- equiv (req_mem_rel ?I' I3) _ _ _ _ _ =>
    apply equiv_cons with (req_mem_rel I' (I3 /-\ EP1 (id_A in_dom L1)))
  end.
  cp_test (id_A in_dom L1).
  (* case [id_A in_dom L1] *)
  nil_nil_tac;  intros k m1 m2 [_ [? [? _] ] ]; split; assumption.

  (* case [~(id_A in_dom L1)] *)
  unfold I3; eqobsrel_tail; unfold EP1, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H1 [H2 [H3 _] ] ] v Hv; split; intros.

  destruct (In_seq_le _ _ _ Hv) as [Hv1 Hv2]; clear H.
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.  
  rewrite leb_correct, leb_correct; [ simpl | omega | trivial ].
  autorewrite with Ris_true in *; split; [ | trivial ].
  intros id Hid.
  case_eq (nat_eqb (fst id) (m1 id_A)); intro Heq.
    elim H3; exists id; split; [ | rewrite nat_eqb_sym ]; trivial.
    generalize (H2 _ Hid); mem_upd_simpl; omega.

  rewrite nat_eqb_refl; simpl.
  destruct (In_seq_le _ _ _ Hv)as [Hvl Hvu]; clear Hv.
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  rewrite leb_correct, leb_correct; [ simpl | omega | trivial ].
  autorewrite with Ris_true in *; split; [ | trivial ].
  intros id Hid.
  case_eq (nat_eqb (fst id) (m1 id_A)); intro Heq.
    elim H3; exists id; split; [ | rewrite nat_eqb_sym ]; trivial.
    generalize (H2 _ Hid); mem_upd_simpl; omega.

  (* Application of [pow_uniform_G1_G2] to finish the proof *)
  match goal with
  |- equiv ?P'  _ _ _ _ (kreq_mem ?O') =>
     apply equiv_trans with
      (E2:=E2)
      (c2:=[ c' <$- [1..q-1]; c <- (((V [{id_A}]) ^-1) *! c') mod_q;
        h2 <c- H2 with {e  (L1 [{id_A}], Ppub) |^| c};
        d_A <c- A2 with {(c |.| P | h2 |x| m_d)} ])
      (P1:=P')
      (Q1:=kreq_mem O')
      (Q2:=kreq_mem O')
  end.
  apply (decMR_req_mem_rel _ (decMR_and dec_I3 (decMR_EP1 _))).
  intros k m1 m2 [H1 [H2 H3] ]; repeat split; assumption.
  intros k m1 m2 m3 H1 H2; apply req_mem_trans with m2; assumption.

  eqobs_tl iE2E3.
  apply equiv_weaken_kreq_mem with trueR.
  eapply LS2.equiv_union_Modify with {{c}} {{c,c'}}; [ | | ].
  split; apply modify_correct with (refl1_info iE2E3) Vset.empty; vm_compute; trivial.
  apply (decMR_and dec_I3 (decMR_EP1 _)).
  simpl; unfold req_mem_rel at 2; rewrite andR_trueR_r.
  apply equiv_strengthen with (req_mem_rel (fv_expr (V [{id_A}])) (EP2 (0 << V [{id_A}] !<! q))).
    unfold I3, EP1, EP2; intros k m1 m2 [H1 [H2 H3] ]; split.
      apply req_mem_weaken with (2:=H1); vm_compute; trivial.
      rewrite (@depend_only_fv_expr T.Bool (0 << V [{id_A}] !<! q) _  m2 m1);
        [ | apply req_mem_weaken with (2:=(req_mem_sym H1)); unfold Vset.subset; trivial].
      simpl in *; unfold O.eval_op in *; simpl in *;   autorewrite with Ris_true in *;
        unfold is_true; rewrite <-andb_true_iff.
      destruct H3 as [v [H1v H2v] ]; apply nat_eqb_true in H2v; rewrite H2v.
      generalize (H2 v H1v); mem_upd_simpl.
  apply equiv_trans with
    (E2:=E2)
    (c2:= [c <$- [1..q-1]; c' <- (V [{id_A}]) *! c mod_q])
    (P1:=kreq_mem Vset.empty)
    (Q1:=kreq_mem {{c}})
    (Q2:=kreq_mem {{V,id_A,c,c'}}).
    auto.
    unfold trueR; intros k m1 m2 _; auto with set.
    intros; apply req_mem_trans with y; [ trivial | 
      apply req_mem_weaken with (2:=H0); unfold Vset.subset; trivial ].
    deadcode; eqobs_in.
    apply Zq_padding; discriminate.

  ep iE2E3_I3; deadcode iE2E3_I3.
  alloc_l iE2E3_I3 c' c; ep iE2E3_I3.
  deadcode iE2E3_I3;  eqobs_in iE2E3_I3.
  intros k m1 m2 [_ [? _] ]; trivial.
 Qed.

  
 Lemma Pr_G2_G3_S2 : forall k (m:Mem.t k),
  Pr E2 G2 m (@S2 k) == Pr E3 G3 m (@S2 k).
 Proof.
  intros.
  apply equiv_deno with (1:=EqObs_G2_G3); [|auto].
  intros m1 m2 H; unfold S2, Success, GoodToss, andP, andb, charfun, restr, EP.
  repeat (rewrite depend_only_fv_expr_subset with (2:=H);
   [ | vm_compute]; trivial).
 Qed.

 Lemma Pr_G2_G3_GT : forall k (m:Mem.t k),
  Pr E2 G2  m (@GoodToss k) == Pr E3 G3 m (@GoodToss k).
 Proof.
  intros.
  apply equiv_deno with (1:=EqObs_G2_G3); [|auto].
  intros m1 m2 H; unfold GoodToss, charfun, restr, EP, andP, andb, fone.
  repeat (rewrite depend_only_fv_expr_subset with (2:=H);
   [ | vm_compute]; trivial).
 Qed.

 Lemma G3_lossless : lossless E3 G3.
 Proof.
  change (lossless E3 (CoinTosses ++ (skipn 2 G3))).
  apply lossless_app.
  apply CoinTosses_lossless.
  apply is_lossless_correct with (refl2_info iE2E3_I3); vm_compute; trivial.
 Qed.


 (** G3 --> G4 *)

 (*
    CHANGES IN THE GAME:
    1) Insert the challenge [e(P,P)^abc] into the ciphertext 
    (games are indistinguishable if [GoodToss] holds)
    
    RESULTS REGARDING PROBABILITY OF EVENTS:
    1) Probabilities of [Success /\ GoodToss] and
    [GoodToss] are preserved (fundamental lemma).
 *)

 Definition G4 :=
  [
   T <- Nil _;
   while Elen T <! qH1 do [ t <$- {0,1}_p; T <- T |++| (t |::| Nil _) ];
   L1 <- Nil _; L2 <- Nil _; L3 <- Nil _; J1 <- Nil _; V <- Nil _;
   P <$- G1o;
   a <$- [1..q-1];
   Ppub <- a |.| P;
   b <$- [1..q-1];
   r1 <c- A1 with {};
   id_A <- Esnd r1;
   m0 <- Efst (Efst r1); m1 <- Esnd (Efst r1);
   d <$- {0,1};
   If d then [ m_d <- m0 ] else [ m_d <- m1 ];
   Q_A <c- H1 with {id_A};
   c <$- [1..q-1];
   v' <- (V[{id_A}]^-1 *! c) mod_q;
   h2 <c- H2 with { e(P,P) |^| (a *! b *! c) };
   y <- (v' |.| P | h2 |x| m_d);
   d_A <c- A2 with {y}
  ].

 Definition E4 := E3.


 Definition X_queried k := EP k (e(P,P) |^| (a *! b *! c) in_dom L2).

 Definition O := {{a, b, c, P, L1, L2, L3, T, J1, d, d_A, id_A}}.

 (*
   To prove that the probabilities of events
   [GoodToss /\ X_queried] are the same in (G3,E3) and
   (G4,E4)  we will proceed as follows:
   1) Pr (E4,G4) S4 == Pr (E4,G4') S4
   (Obs equivalence)
   2) Pr (E4,G4') S4 == Pr (E4,G4') (S4 && !bad)
   (poscondition S4 ==> !bad)
   3) Pr (E4,G4') (S4 && !bad)  == Pr (E4,G3'') (S4 && !bad)
   (upto_bad reasoning).
   4) Pr (E4,G3'') (S4 && !bad) == Pr (E4,G3') S4
   (poscondition S4 ==> !bad).
 *)

 Definition G4' :=
  [
   bad <- false;
   T <- Nil _;
   while Elen T <! qH1 do [ t <$- {0,1}_p; T <- T |++| (t |::| Nil _) ];
   L1 <- Nil _; L2 <- Nil _; L3 <- Nil _; J1 <- Nil _; V <- Nil _;
   P <$- G1o;
   a <$- [1..q-1];
   Ppub <- a |.| P;
   b <$- [1..q-1];
   r1 <c- A1 with {};
   id_A <- Esnd r1;
   m0 <- Efst (Efst r1); m1 <- Esnd (Efst r1);
   d <$- {0,1};
   If d then [ m_d <- m0 ] else [ m_d <- m1 ];
   Q_A <c- H1 with {id_A};
   c <$- [1..q-1];
   v' <- (V[{id_A}]^-1 *! c) mod_q;   
   If (Enth {J1 [{id_A}], T}) then
    [
     h2 <c- H2 with { e(P,P) |^| (a *! b *! c) }
    ]
   else
    [
     bad <- true;
     h2 <c- H2 with { e(P,P) |^| (a *! b *! c) }
    ];
   y <- (v' |.| P | h2 |x| m_d);
   d_A <c- A2 with {y}
  ].

 Definition iE4E4 := iE2E3.

 Lemma EqObs_G4_G4': EqObs I E4 G4 E4 G4' O.
 Proof.
  deadcode iE4E4; eqobs_in iE4E4.
 Qed.

 Definition I4 := EP1 (id_A in_dom L1) /-\ EP1((Enth {J1[{id_A}], T}) ==> !bad).

 Lemma dep_I4 : depend_only_rel I4 {{L1, bad, T, J1, id_A}} Vset.empty.
 Proof.
  change {{L1, bad, T, J1, id_A}} with
   (Vset.union {{L1, id_A}} {{bad, T, J1, id_A}}).
  change Vset.empty with (Vset.union Vset.empty Vset.empty).
  apply depend_only_andR; apply depend_only_EP1.
 Qed.

 Lemma dec_I4 : decMR I4.
 Proof.
  unfold I4; auto.
 Qed.

 Definition iE4E4_I4_empty : eq_inv_info I4 E4 E4.
  refine (@empty_inv_info I4 _ _ dep_I4 _ dec_I4 _ _).
  vm_compute; trivial.
 Defined.

 Lemma H1_E4E4_I4 : EqObsInv I4
  {{T, J1, b, id_H, L1, P, V}}
  E4 H1_2
  E4 H1_2
  {{T, J1, b, id_H, L1, P, V}}.
 Proof.
  cp_test (id_H in_dom L1).
  (* case [id_H in_dom L1] *)
  nil_nil_tac.
  intros k m1 m2 [_ [? _] ]; assumption.
  (* case [~(id_H in_dom L1)] *)
  unfold I4; eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H1 [ [H2 H3] [H4 _] ] ] v Hv; repeat split.
  apply orb_true_intro; right; assumption.
  unfold O.assoc; simpl.
  case_eq (nat_eqb (m1 id_A) (m1 id_H)).
  simpl; intro H'; apply nat_eqb_true in H'.
  unfold notR in H4.
  autorewrite with Ris_true in H2, H4; rewrite <-H' in H4.
  tauto.
  intros _; assumption.
  apply orb_true_intro; right; assumption.
  unfold O.assoc; simpl.
  case_eq (nat_eqb (m1 id_A) (m1 id_H)).
  simpl; intro H'; apply nat_eqb_true in H'.
  unfold notR in H4.
  autorewrite with Ris_true in H2, H4; rewrite <-H' in H4.
  tauto.
  intros _; assumption.
 Qed.

 Definition iE4E4_I4 :=
  let iH1 := add_info H1 Vset.empty Vset.empty iE4E4_I4_empty H1_E4E4_I4 in
  let iH2 := add_refl_info H2 iH1 in
  let iEx := add_refl_info Ex iH2 in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Lemma EqObs_G4'_G4': EqObsRel 
  I trueR
  E4 G4'
  E4 G4'
  (Vset.add bad O) I4.
 Proof.
  eqobs_tl_n iE4E4_I4 3%nat.
  apply equiv_trans_eq_mem_l with
   (E1':= E4)
   (c1':= (skipn 1 (firstn 21 G4')) ++ [bad <- false] ++ (firstn 1 (skipn 21 G4')))
   (P1:=trueR);
    simpl;
     [ swap iE4E4; rewrite proj1_MR; apply equiv_eq_mem | |
      unfold trueR; intros _ _ _ _; trivial ].
  swap iE4E4; simpl.
  eqobs_hd_n iE4E4 17%nat.
  match goal with
  |- equiv (kreq_mem ?I') _ _ _ _ _ =>
     apply equiv_cons with (req_mem_rel (Vset.add Q_A I') (EP1 (id_A in_dom L1)))
  end.
  inline iE4E4_I4 H1.
  ep; deadcode.
  cp_test (id_A in_dom L1).
  eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl.
  intros k' m1 m2 [_ [? _] ]; assumption.
  eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl.
  intros k' m1 m2 [H1 [H2 _] ] v Hv;
   split; intros _; bprop; left; apply nat_eqb_refl.
  cp_test (Enth {J1 [{id_A}], T}).
  eqobs_tl_n iE4E4_I4 1%nat.
  unfold I4; eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl.
  intros k' m1 m2 [_ [H2 _ ] ] _ _; split;
   [assumption | rewrite impb_true_r; trivial].
  deadcode iE4E4_I4.
  eqobs_tl iE4E4_I4.
  unfold I4; eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl.
  intros k' m1 m2 [_ [H2 [H3 _] ] ] _ _.
  unfold notR in H3; apply not_true_is_false in H3.
  split; [ | rewrite H3; auto].
  assumption.
 Qed.


 Definition G3' :=
  [
   bad <- false;
   T <- Nil _;
   while Elen T <! qH1 do [ t <$- {0,1}_p; T <- T |++| (t |::| Nil _) ];
   L1 <- Nil _; L2 <- Nil _; L3 <- Nil _; J1 <- Nil _; V <- Nil _;
   P <$- G1o;
   a <$- [1..q-1];
   Ppub <- a |.| P;
   b <$- [1..q-1];
   r1 <c- A1 with {};
   id_A <- Esnd r1;
   m0 <- Efst (Efst r1); m1 <- Esnd (Efst r1);
   d <$- {0,1};
   If d then [ m_d <- m0 ] else [ m_d <- m1 ];
   Q_A <c- H1 with {id_A};
   c <$- [1..q-1];
   v' <- (V[{id_A}]^-1 *! c) mod_q;
   If (Enth {J1 [{id_A}], T}) then
    [
     h2 <c- H2 with { e(P,P) |^| (a *! b *! c) }
    ]
   else
    [
     bad <- true;
     g <- e(Q_A, Ppub);
     h2 <c- H2 with {g |^| v'}
    ];
   y <- (v'|.| P | h2 |x| m_d);
   d_A <c- A2 with {y}
  ].

 Definition I3' :=
  EP2 (Ppub =?= a |.| P) /-\
  EP2 (E.Eforall z ( ((L1[{Efst z}] =?=
   (Enth{J1[{Efst z}], T}) ? ((b *! (V[{Efst z}])) |.| P) ?: (V[{Efst z}]) |.| P)) &&
   (0 << V[{Efst z}] !<! q) ) L1).

 Lemma dep_I3' : depend_only_rel I3' Vset.empty {{a, Ppub, V, b, P, T, J1, L1}}.
 Proof.
  change {{a, Ppub, V, b, P, T, J1, L1}} with
   (Vset.union {{a, P, Ppub}} {{V, b, P, T, J1, L1}}).
  change Vset.empty with (Vset.union Vset.empty Vset.empty). 
  apply depend_only_andR; apply depend_only_EP2.
 Qed.

 Lemma dec_I3' : decMR I3'.
 Proof.
  apply decMR_and; auto.
 Qed.

 Definition iE4E4_I3'_empty : eq_inv_info I3' E4 E4.
  refine (@empty_inv_info I3' _ _ dep_I3' _ dec_I3' _ _).
  vm_compute; trivial.
 Defined.

 Lemma H1_E4E4_I3' : EqObsInv I3'
  {{T, J1, b, id_H, L1, P, V}}
  E4 H1_2
  E4 H1_2
  {{T, J1, b, id_H, L1, P, V}}.
 Proof.
  cp_test (id_H in_dom L1).
  (* case [id_H in_dom L1] *)
  nil_nil_tac.
  intros k m1 m2 [_ [? _] ]; assumption.

  (* case [~(id_H in_dom L1)] *)
  unfold I3'; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H1 [ [H2 H3] [_ H4] ] ].
  repeat split; try assumption.
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  destruct H0 as [_ H0]; rewrite H0, G1.eqb_refl; simpl.
  destruct (In_seq_le _ _ _ H) as [Hv1 Hv2]; clear H.
  assert (H' : exists z:nat, v = Datatypes.S z) by
   (inversion Hv1; [eauto | exists m; trivial]).
  destruct H' as [z Hz].
  rewrite leb_correct; trivial; simpl.
  rewrite leb_correct; [ | omega].
  simpl; autorewrite with Ris_true in H3 |- *.

  intros x Hx; generalize (H3 x Hx); clear H3.
  mem_upd_simpl.
  intro; unfold notR in H4.
  case_eq (nat_eqb (fst x) (m2 id_H)); intro Heq.
  autorewrite with Ris_true in H4; elim H4.
  exists x; split; [ |rewrite nat_eqb_sym]; trivial.
  trivial.
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  destruct H0 as [_ H0]; rewrite not_is_true_false in H0.
  rewrite H0, G1.eqb_refl.
  destruct (In_seq_le _ _ _ H)as [Hv1 Hv2]; clear H.
  assert (H' : exists z:nat, v = Datatypes.S z) by
   (inversion Hv1; [eauto | exists m; trivial]).
  destruct H' as [z Hz].
  rewrite leb_correct; trivial.
  rewrite leb_correct; [ | omega].
  simpl; autorewrite with Ris_true in H3 |- *.
  intros x Hx; generalize (H3 x Hx); clear H3.
  mem_upd_simpl.
  intro; unfold notR in H4.
  case_eq (nat_eqb (fst x) (m2 id_H)); intro Heq.
  autorewrite with Ris_true in H4; elim H4.
  exists x; split; [ |rewrite nat_eqb_sym]; trivial.
  trivial.
 Qed.

 Definition iE4E4_I3' :=
  let iH1 := add_info H1 Vset.empty Vset.empty iE4E4_I3'_empty H1_E4E4_I3' in
  let iH2 := add_refl_info H2 iH1 in
  let iEx := add_refl_info Ex iH2 in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Lemma EqObs_G3'_G3: EqObsRel
  I trueR
  E4 G3'
  E4 G3
  O (EP1((Enth {J1[{id_A}], T}) ==> !bad)).
 Proof.
  unfold G3', G3.
  (* Push assignment [bad <- false] down in the left program *)
  apply equiv_trans_eq_mem_l with
   (E1':= E4)
   (c1':= (skipn 1 (firstn 20 G3')) ++ [bad <- false] ++ (skipn 20 G3'))
   (P1:=trueR); simpl;
    [ swap iE4E4; rewrite proj1_MR; apply equiv_eq_mem | |
     unfold trueR; intros _ _ _ _; trivial ].

  (* Annotate I3' before call to A1 *)
  match goal with
   |- equiv (req_mem_rel ?I' _) _ ?c _ ?c' _ =>
    rewrite <-(firstn_skipn 11 c), <-(firstn_skipn 11 c');
     apply equiv_app with (req_mem_rel
      (Vset.add T (Vset.add L1 (Vset.add L2 (Vset.add L3
       (Vset.add J1 (Vset.add V (Vset.add P
        (Vset.add a (Vset.add Ppub (Vset.add b I')))))))))) I3'); simpl
  end.
  eqobs_hd_n iE4E4 2%nat.
  unfold I3'; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  intros k _ _ _ v1 _ v2 _; split; [apply G1.eqb_refl | trivial ].

  (* I3' holds before computing the [H1(id_A)] *)
  eqobs_hd_n iE4E4_I3' 6%nat.

  (* Added annotation regarding the form of [H1(id_A)] *)
  match goal with
   |- EqObsRel ?I' _ _ _ _ _ _ _ =>
    apply equiv_cons with (req_mem_rel (Vset.add Q_A I')
     ( (EP1 (id_A in_dom L1)) /-\ (EP2 (Ppub =?= a |.| P)) /-\
      (EP2 (Q_A =?=  (Enth{J1[{id_A}], T}) ?
       ((b *! (V[{id_A}])) |.| P) ?: ((V[{id_A}]) |.| P))) /-\
      (EP2 (0 << V[{id_A}] !<! q))))
  end.
  inline iE4E4_I3' H1; [ apply (decMR_req_mem_rel _ dec_I3') | ].
  ep; deadcode;  [ apply (decMR_req_mem_rel _ dec_I3') | ].
  cp_test (id_A in_dom L1).
  (* case *)
  unfold I3'; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  intros k' m1 m2 [_ [ [H0 H1] [H2 H3] ]  ]; repeat split.
  assumption.
  assumption.
  autorewrite with Ris_true in *.
  elim H3; intros x [Hx1 Hx2]; clear H2 H3.
  generalize (H1 x Hx1); clear H1.
  mem_upd_simpl.
  rewrite <-(nat_eqb_true Hx2); bprop; tauto.
  autorewrite with Ris_true in *.
  elim H3; intros x [Hx1 Hx2]; clear H2 H3.
  generalize (H1 x Hx1); clear H1.
  mem_upd_simpl.
  rewrite <-(nat_eqb_true Hx2); bprop; tauto.
  (* case *)
  unfold I3'; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  intros k' m1 m2 [_ [ [H0 H1] [H2 H3] ]  ] v Hv; repeat split.
  bprop; left; apply nat_eqb_refl.
  assumption.
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  destruct H as [_ H4]; rewrite H4, G1.eqb_refl; trivial.
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  destruct (In_seq_le _ _ _ Hv) as [Hv1 Hv2]; clear Hv.
  assert (H' : exists z:nat, v = Datatypes.S z) by
   (inversion Hv1; [eauto | exists m; trivial]).
  destruct H' as [z Hz].
  rewrite leb_correct; trivial.
  rewrite leb_correct; [ | omega].
  trivial.
  bprop; left; apply nat_eqb_refl.
  assumption.
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  destruct H as [_ H4]; apply not_true_is_false in H4.
  rewrite H4, G1.eqb_refl; trivial.
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  destruct (In_seq_le _ _ _ Hv) as [Hv1 Hv2]; clear Hv.
  assert (H' : exists z:nat, v = Datatypes.S z) by
   (inversion Hv1; [eauto | exists m; trivial]).
  destruct H' as [z Hz].
  rewrite leb_correct; trivial.
  rewrite leb_correct; [ | omega].
  trivial.
 
  (* Strengthen the postcondition to eliminate the last two instructions *)
  apply equiv_weaken_req_mem_rel_implMR with I4.
  intros k m1 m2 [_ ?]; assumption.
  eqobs_tl iE4E4_I4.

  (* Case analysis *)
  cp_test_l (Enth {J1 [{id_A}], T}).
  (* case *)
  match goal with
   |- equiv (req_mem_rel ?I' ?P' /-\ _) _ ?c1 _ ?c2 _ =>
    rewrite <-(firstn_skipn 3 c1), <-(firstn_skipn 3 c2);
     apply equiv_app with (req_mem_rel
      (Vset.add c (Vset.add v' I')) (I4 /-\
       (EP2 (g |^| v' =?= e(P,P) |^| (a *! b *! c) )))); simpl
  end.
  unfold I4; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H1 [ [H2 [H3 [H4 H5] ] ] H6 ] ] v Hv; repeat split.
  assumption.
  rewrite impb_true_r; trivial.
  set (X :=  O.assoc (nat_eqb (m2 id_A)) 0 (m2 V)) in *.
  rewrite (H1 _ id_A),  (H1 _ J1),  (H1 _ T) in H6; trivial; rewrite H6 in H4.
  rewrite (proj1  (G1.eqb_true _ _) H3),  (proj1  (G1.eqb_true _ _) H4).
  rewrite bilinear, G2.pow_pow.
  match goal with |- is_true (G2.eqb (G2.pow _ ?X1) (G2.pow _ ?X2)) => 
    rewrite (G2.pow_mod _ X1), (G2.pow_mod _ X2); replace (X1 mod (G2.order k)) 
      with (X2 mod (G2.order k)); [ apply G2.eqb_refl | ]
  end.
  replace (m2 b * X * m2 a * ((inv_mod (Par.q k) X * v) mod (Par.q k))) with 
    (m2 a * m2 b * (X * ((inv_mod (Par.q k) X * v) mod (Par.q k)))) by ring.
  repeat rewrite (mult_mod (m2 a * m2 b)); 
    apply (f_equal (fun m => nmod m (G2.order k))); apply f_equal.
  rewrite G2_order.
  rewrite (mult_mod X), mod_mod, (mult_mod _ v), <-(mod_mod X), 
    <-(mult_mod _ (_ * _)), mult_assoc, (mult_mod), <-(mult_mod X), 
    mod_mod, inv_mod_prime, mult_1_l, mod_mod; trivial.
      apply (q_prime k).
      rewrite is_true_andb in H5; destruct H5 as [H51 H52];
      apply leb_complete in H51; apply leb_complete in H52; omega.


  ep_eq_r (g |^| v')  (e(P,P) |^| (a *! b *! c)).
  intros k m1 m2 [_ [_ ?] ]; rewrite expr_eval_eq; assumption.
  deadcode iE4E4_I4.
  eqobs_in iE4E4_I4.
  intros k m1 m2 [_ [? _] ]; assumption.
  (* case *)
  ep; deadcode iE4E4_I4.
  eqobs_tl iE4E4_I4.
  unfold I4; eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [H1 _] H2] ] v Hv; split.
  assumption.
  unfold notR in H2; apply not_true_is_false in H2.
  rewrite H2; trivial.
 Qed.


 Definition iE4E4_uptobad :=
  let iH1 := add_upto_info (empty_upto_info bad E4 E4) H1 in
  let iH2 := add_upto_info iH1 H2 in
  let iEx := add_upto_info iH2 Ex in
  let iA1 := add_adv_upto_info iEx (EqAD _ _ _ _ _ _) (EqOP _ _ _ _ _ _) (A1_wf_E _ _ _) in
  let iA2 := add_adv_upto_info iA1 (EqAD _ _ _ _ _ _) (EqOP _ _ _ _ _ _) (A2_wf_E _ _ _) in iA2.

 Lemma Pr_G3_G4 : forall k (m:Mem.t k) (TT:Mem.t k -o> boolO),
  (forall m1 m2, kreq_mem O m1 m2 -> charfun TT m1 == charfun TT m2) ->
  (forall m1 m2, req_mem_rel (Vset.add bad O) I4 k m1 m2 ->
   charfun TT m1 == charfun (TT [&&] negP (EP k bad)) m2) ->
  (forall m1 m2,
   req_mem_rel O (EP1 (Enth {J1 [{id_A}], T} ==> (!bad))) k m1 m2 ->
   charfun (TT [&&] negP (EP k bad)) m1 == charfun TT m2) ->
  Pr E4 G3 m TT == Pr E4 G4 m TT.
 Proof.
  intros k m TT H1 H2 H3; symmetry.
  transitivity (Pr E4 G4' m TT).
  apply (equiv_deno EqObs_G4_G4'); trivial.
  transitivity (Pr E4 G4' m (TT [&&] negP (EP k bad))).
  apply (equiv_deno EqObs_G4'_G4'); [ trivial | ].
  split; unfold trueR; trivial.
  transitivity (Pr E4 G3' m (TT [&&] negP (EP k bad))).
  unfold G4', G3', Pr.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  symmetry; rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  apply upto_bad_and_neg with iE4E4_uptobad; vm_compute; trivial.
  apply (equiv_deno EqObs_G3'_G3); [ trivial | ].
  unfold trueR; split; trivial.
 Qed.

 Lemma Pr_G3_G4_GT : forall k (m:Mem.t k),
  Pr E3 G3 m (@GoodToss k) == Pr E4 G4 m (@GoodToss k).
 Proof.
  intros.
  apply Pr_G3_G4.
  intros m1 m2 H.
  unfold GoodToss; rewrite_req_mem_l H.
  intros m1 m2 [H [_ H'] ]; generalize H'.
  unfold I4, GoodToss.
  bool_tauto_l H.
  intros m1 m2 [H H']; generalize H'.
  unfold GoodToss.
  bool_tauto_r H.
 Qed.

 Lemma Pr_G3_G4_S2 : forall k (m:Mem.t k),
  Pr E3 G3 m (@S2 k) == Pr E4 G4 m (@S2 k).
 Proof.
  intros.
  apply Pr_G3_G4.
  intros m1 m2 H.
  unfold S2, Success, GoodToss.
  rewrite_req_mem_l H.
  intros m1 m2 [H [_ H'] ]; generalize H'.
  unfold I4, S2, Success, GoodToss.
  bool_tauto_l H.
  intros m1 m2 [H H']; generalize H'.
  unfold S2, Success, GoodToss.
  bool_tauto_r H.
 Qed.

 (* TODO: skip intermediate proof step G4' <-> G4' <-> G4 *)


 (** G4 --> G5 *)

 (*
    CHANGES IN THE GAME:
    1) New simulation of the extraction oracle (this simulation
    is perfect if [GoodToss] holds)

    RESULTS REGARDING PROBABILITY OF EVENT:
    1) Probabilities of [GoodToss] and [Success /\ GoodToss]
    are preserved (upto-bad reasonings).
 *)

 Definition Ex_5 :=
  [
   Q_ex <c- H1 with {id_ex};
   d_ex <- a |.| (V[{id_ex}] |.| P);
   If id_ex not_in L3 _then [ L3 <- id_ex |::| L3 ]
  ].

 Definition G5 := G4.

 Definition E5 := make_env H1_2 H2_0 Ex_5.

 (*
   Now we will prove that [Pr (E4,G4) S2 == Pr (E5,G4) S2].
   This will follow from equations
   1) Pr (E4,G4) S2 == Pr (E4'',G4'') (S2 && !bad)
   (postcondition S2 ==> !bad)
   2) Pr (E4'',G4'') (S2 && !bad) == Pr (E5',G4'') (S2 && !bad)
   (upto_bad reasoning).
   3) Pr (E5',G4'') (S2 && !bad) == Pr (E5,G4) S2
   (postcondition S2 ==> !bad)
   where G4'' = (bad <- false)::G4
   We will follow the same reasoning to prove that
   [ Pr (E4,G4) GoodToss == Pr (E3,G3) GoodToss ].
 *)

 Definition Ex_4'' :=
  [
   Q_ex <c- H1 with {id_ex};
   If Enth {J1[{id_ex}], T} then
   [
    bad <- true;
    d_ex <- a |.| ((b *! (V[{id_ex}])) |.| P)
   ]
   else
   [
    d_ex <- a |.| (V[{id_ex}] |.| P)
   ];
   If id_ex not_in L3 _then [ L3 <- id_ex |::| L3 ]
  ].

 Definition E4'' := make_env H1_2 H2_0 Ex_4''.


 Definition I4'' :=
  EP2 (E.Eforall z' (z' in_dom L1) L3) /-\
  EP2 ((E.Eforall z' (!(Enth {J1[{z'}], T})) L3) ==> !bad) /-\
  EP2 (E.Eforall z ((Enth {J1 [{Efst z}], T}) ?
   ((b *! (V [{Efst z}]) *! a) |.| P =?= a |.| (L1 [{Efst z}])) ?:
   (((V [{Efst z}]) *! a) |.| P =?= a |.| (L1 [{Efst z}]))) L1).

 Lemma dep_I4'' : depend_only_rel I4'' 
  Vset.empty {{bad, L3, a, V, b, P, T, J1, L1}}.
 Proof.
  change {{bad, L3, a, V, b, P, T, J1, L1}} with
   (Vset.union {{L1, L3}} 
    (Vset.union {{bad, T, J1, L3}} {{a, V, b, P, T, J1, L1}})).
 change Vset.empty with 
  (Vset.union Vset.empty (Vset.union Vset.empty Vset.empty)).
  repeat apply depend_only_andR; apply depend_only_EP2.
 Qed.

 Lemma dec_I4'' : decMR I4''.
 Proof.
  unfold I4''; auto.
 Qed.

 Definition iE4E4''_I4''_empty : eq_inv_info I4'' E4 E4''.
  refine (@empty_inv_info I4'' _ _ dep_I4'' _ dec_I4'' _ _).
  vm_compute; trivial.
 Defined.

 Lemma H1_E4E4''_I4'' : EqObsInv I4''
  {{id_H, V, L1, P, T, J1, b}}
  E4   H1_2
  E4'' H1_2
  {{id_H, V, L1, P, T, J1, b}}.
 Proof.
  unfold H1_2.
  cp_test (id_H in_dom L1).
  (* case [id_H in_dom L1] *)
  nil_nil_tac; intros k m1 m2 [_ [? _] ]; assumption.
  (* case [~(id_H in_dom L1)] *)
  cp_test (Enth {Elen L1, T}).
  (* case  [T[|L1|] = true]  *)
  unfold I4''; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [H1 [H2 H3] ] [_ [_ H4] ] ] ] v Hv; repeat split.
  bprop; intros x Hx; bprop; right.
  autorewrite with Ris_true in H1.
  generalize (H1 _ Hx); bprop.
  mem_upd_simpl.
  trivial.

  bprop; intro H'.
  autorewrite with Ris_true in H2; apply H2.
  intros x Hx; generalize (H' _ Hx); clear Hx.
  mem_upd_simpl.
  unfold O.assoc; simpl.
  case (nat_eqb x (m2 id_H)).
  simpl; rewrite H4; simpl; intros ?; discriminate.
  trivial.

  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  rewrite H4, G1.pow_pow, G1.eqb_refl.
  simpl; bprop; intros x Hx.
  case (nat_eqb (fst x) (m2 id_H)).
  simpl; rewrite H4, G1.pow_pow, G1.eqb_refl; trivial.
  autorewrite with Ris_true in H3.
  generalize (H3 _ Hx).
  mem_upd_simpl.
  trivial.

  (* case [T[|L1|] = false ] *)
  unfold I4''; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [H1 [H2 H3] ] [ [_ H4] [_ H5] ] ] ] v Hv; repeat split.
  bprop; intros x Hx; bprop; right.
  autorewrite with Ris_true in H1.
  generalize (H1 _ Hx); bprop.
  mem_upd_simpl.
  trivial.

  bprop; intro H'.
  autorewrite with Ris_true in H2; apply H2.
  intros x Hx; generalize (H' _ Hx).
  mem_upd_simpl.
  unfold O.assoc at 1; simpl.
  case_eq (nat_eqb x (m2 id_H)); intro Heq.
  absurd (E.eval_expr (id_H in_dom L1) m2).
  assumption.
  autorewrite with Ris_true in H1.
  generalize (H1 _ Hx).
  simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  rewrite (nat_eqb_true Heq); trivial.
  trivial.

  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  unfold notR in H5; apply not_true_is_false in H5.
  rewrite H5, G1.pow_pow, G1.eqb_refl.
  simpl; bprop; intros x Hx.
  case (nat_eqb (fst x) (m2 id_H)).
  simpl; rewrite H5, G1.pow_pow, G1.eqb_refl; trivial.
  autorewrite with Ris_true in H3.
  generalize (H3 _ Hx).
  mem_upd_simpl.
 Qed.

 Lemma EX_E4E4''_I4'' : EqObsInv I4''
  {{id_ex, V, L1, P, T, b, a, J1, L3}}
  E4   Ex_0
  E4'' Ex_4''
  {{d_ex, V, id_ex, L1, P, T, b, a, J1, L3}}.
 Proof.
  (* Annotation after call to H1 *)
  match goal with
  |- EqObsInv _ ?I' _ ?c1 _ _ ?O' => unfold EqObsInv;
     apply equiv_cons with (req_mem_rel (Vset.add Q_ex I')
        (I4'' /-\
        (EP2 (id_ex in_dom L1)) /-\
        (EP2 ((Enth {J1 [{id_ex}], T}) ?
          ((b *! (V [{id_ex}]) *! a) |.| P =?= a |.| Q_ex) ?:
          (((V [{id_ex}]) *! a) |.| P =?= a |.| Q_ex)) )))
  end.
  set (iH1:=add_info H1 Vset.empty Vset.empty iE4E4''_I4''_empty H1_E4E4''_I4'').
  inline iH1 H1; [apply (decMR_req_mem_rel _ dec_I4'') |].
  ep; deadcode iE4E4''_I4''_empty.

  cp_test (id_ex in_dom L1).
  (* case [id_ex in_dom L1] *)
  eqobsrel_tail; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H1 [ [H4 [H5 H6] ] [_ H3] ] ]; unfold EP2 in H4, H5, H6.
  split; [ | repeat split].

  unfold I4'', EP2; repeat split;
   (rewrite (@depend_only_fv_expr T.Bool _  _  _ m2);
    [ assumption |
      apply req_mem_upd_notin_l; [apply req_mem_refl | discriminate] ]).

  assumption.

  generalize H6.
  unfold EP2; simpl; unfold O.eval_op; simpl; bprop.
  intro H; generalize (H _ (in_dom_In H3)).
  mem_upd_simpl.
  simpl; trivial.

  (* case [~(id_ex in_dom L1)] *)
  cp_test (Enth {Elen L1, T}).

  (* case  [T[|L1|] = true]  *)
  unfold I4''; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [H1 [H2 H3] ] [_ [_ H4] ] ] ] v Hv; repeat split.
  bprop; intros x Hx; bprop; right.
  autorewrite with Ris_true in H1.
  generalize (H1 _ Hx); bprop.
  mem_upd_simpl.
  trivial.

  bprop; intro H'.
  autorewrite with Ris_true in H2; apply H2.
  intros x Hx; generalize (H' _ Hx); clear Hx.
  mem_upd_simpl.
  unfold O.assoc; simpl.
  case (nat_eqb x (m2 id_ex)).
  simpl; rewrite H4; simpl; intros ?; discriminate.
  trivial.

  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  rewrite H4, G1.pow_pow, G1.eqb_refl.
  simpl; bprop; intros x Hx.
  case (nat_eqb (fst x) (m2 id_ex)).
  simpl; rewrite H4, G1.pow_pow, G1.eqb_refl; trivial.
  autorewrite with Ris_true in H3.
  generalize (H3 _ Hx).
  mem_upd_simpl.
  trivial.

  rewrite nat_eqb_refl; simpl; trivial.

  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  rewrite H4, G1.pow_pow, G1.eqb_refl; trivial.

  (* case [T[|L1|] = false ] *)
  unfold I4''; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [H1 [H2 H3] ] [ [_ H4] [_ H5] ] ] ] v Hv; repeat split.
  bprop; intros x Hx; bprop; right.
  autorewrite with Ris_true in H1.
  generalize (H1 _ Hx); bprop.
  mem_upd_simpl.
  trivial.

  bprop; intro H'.
  autorewrite with Ris_true in H2; apply H2.
  intros x Hx; generalize (H' _ Hx).
  mem_upd_simpl.
  unfold O.assoc at 1; simpl.
  case_eq (nat_eqb x (m2 id_ex)); intro Heq.
  absurd (E.eval_expr (id_ex in_dom L1) m2).
  assumption.
  autorewrite with Ris_true in H1.
  generalize (H1 _ Hx).
  simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  rewrite (nat_eqb_true Heq); trivial.
  trivial.

  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  unfold notR in H5; apply not_true_is_false in H5.
  rewrite H5, G1.pow_pow, G1.eqb_refl.
  simpl; bprop; intros x Hx.
  case (nat_eqb (fst x) (m2 id_ex)).
  simpl; rewrite H5, G1.pow_pow, G1.eqb_refl; trivial.
  autorewrite with Ris_true in H3.
  generalize (H3 _ Hx).
  mem_upd_simpl.
  trivial.

  rewrite nat_eqb_refl; simpl; trivial.

  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  unfold notR in H5; apply not_true_is_false in H5.
  rewrite H5, G1.pow_pow, G1.eqb_refl; trivial.

  (* Final step *)
  apply equiv_trans_eq_mem_l with
   (E1':=E4)
   (c1':=[If id_ex not_in L3 _then [ L3 <- id_ex |::| L3 ]; d_ex <- a |.| Q_ex ])
   (P1:=trueR);
   [ swap; rewrite proj1_MR; apply equiv_eq_mem | |
    unfold trueR; intros _ _ _ _; trivial ].
  apply equiv_trans_eq_mem_r with
   (E2':=E4'')
   (c2':=[
    If id_ex not_in L3 _then [ L3 <- id_ex |::| L3 ];
    If Enth {J1 [{id_ex}], T} then
     [ bad <- true; d_ex <- a |.| ((b *! (V [{id_ex}])) |.| P)]
    else
     [ d_ex <- a |.| ((V [{id_ex}]) |.| P)] ])
   (P2:=trueR);
   [ swap; rewrite proj1_MR; apply equiv_eq_mem | |
    unfold trueR; intros _ _ _ _; trivial ].
  cp_test_r (Enth {J1 [{id_ex}], T}).
  (* case [ T[ J1[id_ex] ] = true ] *)
  match goal with
   |- equiv ((req_mem_rel ?I' ?P1) /-\ ?P2) _ ?c _ ?c' _ =>
    rewrite <-(firstn_skipn 1 c), <-(firstn_skipn 2 c');
     apply equiv_app with (req_mem_rel I' (P1 /-\ P2)); simpl
  end.
  unfold I4''; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [ [H1 [_ H2] ] [H3 H4] ] H5] ]; repeat split.
  rewrite H3.
  simpl; bprop; intros x Hx.
  autorewrite with Ris_true in H1; generalize (H1 _ Hx).
  mem_upd_simpl.
  trivial.
  rewrite H5; unfold impb; simpl; trivial.
  bprop; intros x Hx.
  autorewrite with Ris_true in H2; generalize (H2 _ Hx).
  mem_upd_simpl.
  trivial.
  assumption.
  assumption.

  bprop; intros x Hx.
  autorewrite with Ris_true in H1; generalize (H1 _ Hx).
  mem_upd_simpl; trivial.
  match goal with
   |- is_true (impb ?x _) => replace x with false; [ trivial | ]
  end.
  symmetry; rewrite <-not_true_iff_false; intro H'.
  destruct H as [_ H6]; apply eq_true_negb_classical in H6.
  generalize H6 H'; clear H6 H';
   match goal with
    |- ?f = true -> ?g = true -> _ =>
     change (f = true) with (is_true f);
      change (g = true) with (is_true g);
       intros H' H6 end;
   autorewrite with Ris_true in H6, H'.
  destruct H' as [z [Hz Hz2] ]; rewrite <-(nat_eqb_true Hz2) in Hz; clear Hz2.
  generalize (H6 _ Hz); unfold is_true in H5; rewrite H5; intro; discriminate.
  bprop; intros x Hx.
  autorewrite with Ris_true in H2; generalize (H2 _ Hx).
  mem_upd_simpl; trivial.
  assumption.
  assumption.
  assumption.

  union_mod; [repeat apply decMR_and; auto | ].
  eapply equiv_strengthen; [ | apply equiv_assign].
  intros k m1 m2 [H1 [ [ [H2 [H3 H4] ] [_ H5] ] H6] ]; split; unfold EP2 in *.
  match goal with
   |- kreq_mem _ (_ {!_ <-- ?v1!}) (_ {!_ <-- ?v2!}) => replace v1 with v2
  end.
  change (@cons VarP.Edec.t (@Var.mkV _ d_ex) nil) with (Vset.add d_ex Vset.empty).
  apply req_mem_update; trivial.
  rewrite (@depend_only_fv_expr _ (a |.| Q_ex) _  _ m2);
   [ | apply req_mem_weaken with (2:=H1); unfold Vset.subset; trivial].
  simpl in *; unfold O.eval_op in *; simpl in *.
  rewrite H6 in H5; simpl in H5; apply G1.eqb_true in H5; assumption.
  unfold I4'', EP2; repeat split;
   (rewrite (@depend_only_fv_expr T.Bool _  _  _ m2);
    [ assumption |
     apply req_mem_upd_notin_l; [apply req_mem_refl | discriminate] ]).

  (* case [ T[ J1[id_ex] ] = false ] *)
  match goal with
   |- equiv ((req_mem_rel ?I' ?P1) /-\ ?P2) _ ?c _ ?c' _ =>
    rewrite <-(firstn_skipn 1 c), <-(firstn_skipn 1 c');
     apply equiv_app with (req_mem_rel I' (P1 /-\ P2)); simpl
  end.
  unfold I4''; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [ [H1 [H2 H3] ] [H4 H5] ] H6] ]; repeat split.

  rewrite H4.
  simpl; bprop; intros x Hx.
  autorewrite with Ris_true in H1; generalize (H1 _ Hx).
  mem_upd_simpl.
  trivial.
  unfold notR in H6; apply not_true_is_false in H6.
  rewrite H6; simpl; trivial.
  bprop; intro H7.
  autorewrite with Ris_true in H2; apply H2.
  intros x Hx; generalize (H7 _ Hx).
  mem_upd_simpl.
  bprop; intros x Hx.
  autorewrite with Ris_true in H3; generalize (H3 _ Hx).
  mem_upd_simpl.
  assumption.
  assumption.
  intuition.

  bprop; intros x Hx.
  autorewrite with Ris_true in H1; generalize (H1 _ Hx).
  mem_upd_simpl.
  bprop; intro H'.
  autorewrite with Ris_true in H2; apply H2.
  intros x Hx; generalize (H' _ Hx).
  mem_upd_simpl.
  bprop; intros x Hx.
  autorewrite with Ris_true in H3; generalize (H3 _ Hx).
  mem_upd_simpl.
  assumption.
  assumption.
  assumption.

  union_mod; [repeat apply decMR_and; auto | ].
  eapply equiv_strengthen; [ | apply equiv_assign].
  intros k m1 m2 [H1 [ [ [H2 [H3 H4] ] [_ H5] ] H6] ]; split; unfold EP2 in *.
  match goal with
   |- kreq_mem _ (_ {!_ <-- ?v1!}) (_ {!_ <-- ?v2!}) => replace v1 with v2
  end.
  change (@cons VarP.Edec.t (@Var.mkV _ d_ex) nil) with (Vset.add d_ex Vset.empty).
  apply req_mem_update; trivial.
  rewrite (@depend_only_fv_expr _ (a |.| Q_ex) _  _ m2);
   [ | apply req_mem_weaken with (2:=H1); unfold Vset.subset; trivial].
  simpl in *; unfold O.eval_op in *; simpl in *.
  unfold notR in H6; apply not_true_is_false in H6.
  rewrite H6 in H5; apply G1.eqb_true in H5; assumption.
  unfold I4'', EP2; repeat split;
   (rewrite (@depend_only_fv_expr T.Bool _  _  _ m2);
    [ assumption |
     apply req_mem_upd_notin_l; [apply req_mem_refl | discriminate] ]).
 Qed.

 Definition iE4E4''_I4'' :=
  let iH1 := add_info H1 Vset.empty Vset.empty  iE4E4''_I4''_empty H1_E4E4''_I4'' in
  let iH2 := add_refl_info H2 iH1 in
  let iEx := add_info Ex Vset.empty  Vset.empty  iH2 EX_E4E4''_I4'' in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Lemma EqObs_G4E4_G4''E4'': EqObsRel
  I trueR
  E4   G4
  E4'' ((bad <- false)::G4)
  O (EP2 ((E.Eforall z' (!(Enth {J1[{z'}], T})) L3) ==> !bad)).
 Proof.
  apply equiv_weaken_req_mem_rel_implMR with I4'';
   [ intros k m1 m2 [ _ [? _] ]; assumption | ].
  eqobs_tl  iE4E4''_I4''.
  match goal with 
   |- equiv _ _ ?c _ _ _ =>
    apply equiv_trans_eq_mem_r with
     (E2':=E4'')
     (c2':=CoinTosses ++ [bad <- false] ++ skipn 2 c)
     (P2:=trueR)
  end;
  simpl; [ swap; rewrite proj1_MR; apply equiv_eq_mem | |
   unfold trueR; intros _ _ _ _; trivial ].
  eqobs_hd_n 2%nat.
  unfold I4''; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
  intros; unfold impb; simpl; repeat split; trivial.
 Qed.


 Definition Ex_5' :=
  [
   Q_ex <c- H1 with {id_ex};
   If Enth {J1[{id_ex}], T} then
    [
     bad <- true;
     d_ex <- a |.| (V[{id_ex}] |.| P)
    ]
   else
    [
     d_ex <- a |.| (V[{id_ex}] |.| P)
    ];
    If id_ex not_in L3 _then [ L3 <- id_ex |::| L3 ]
  ].

 Definition E5' := make_env H1_2 H2_0 Ex_5'.

 Definition iE4''E5'_uptobad :=
  let iH1 := add_upto_info (empty_upto_info bad E4'' E5') H1 in
  let iH2 := add_upto_info iH1 H2 in
  let iEx := add_upto_info iH2 Ex in
  let iA1 := add_adv_upto_info iEx (EqAD _ _ _ _ _ _) (EqOP _ _ _ _ _ _) (A1_wf_E _ _ _) in
  let iA2 := add_adv_upto_info iA1 (EqAD _ _ _ _ _ _) (EqOP _ _ _ _ _ _) (A2_wf_E _ _ _) in iA2.


 Definition I5' :=
  EP1 (E.Eforall z' (z' in_dom L1) L3) /-\
  EP1 ((E.Eforall z' (!(Enth {J1[{z'}], T})) L3) ==> !bad).

 Lemma dep_I5' : depend_only_rel I5' {{L1, bad, T, J1, L3}} Vset.empty.
 Proof. 
  change {{L1, bad, T, J1, L3}} with (Vset.union {{L1, L3}} {{bad, T, J1, L3}}).
  change Vset.empty with (Vset.union Vset.empty Vset.empty).
  apply depend_only_andR; apply depend_only_EP1.
 Qed.

 Lemma dec_I5' : decMR I5'.
 Proof.
  unfold I5'; auto.
 Qed.

 Definition iE5'E5_I5'_empty : eq_inv_info I5' E5' E5.
  refine (@empty_inv_info I5' _ _ dep_I5' _ dec_I5' _ _).
  vm_compute; trivial.
 Defined.


 Lemma H1_E5'E5_I5' : EqObsInv I5'
  {{T, J1, b, id_H, L1, P, V}}
  E5' H1_2
  E5  H1_2
  {{T, J1, b, id_H, L1, P, V}}.
 Proof.
  unfold H1_2.
  cp_test (id_H in_dom L1).
    (* case [id_H in_dom L1] *)
  nil_nil_tac; intros k m1 m2 [_ [? _] ]; assumption.
    (* case [~(id_H in_dom L1)] *)
  unfold I5'; eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H0 [ [H1 H2] [H3 _] ] ] v Hv; repeat split.
  bprop; intros x Hx; bprop; right.
  autorewrite with Ris_true in H1.
  generalize (H1 _ Hx); bprop.
  mem_upd_simpl.
  trivial.
  bprop; intro H'.
  autorewrite with Ris_true in H2; apply H2.
  intros x Hx; generalize (H' _ Hx); clear Hx.
  mem_upd_simpl.
  unfold O.assoc; simpl.
  case (nat_eqb x (m1 id_H)).
  simpl; destruct H as [H4 _]; rewrite H4; simpl; intros ?; discriminate.
  trivial.
  bprop; intros x Hx; bprop; right.
  autorewrite with Ris_true in H1.
  generalize (H1 _ Hx); bprop.
  mem_upd_simpl.
  trivial.
  bprop; intro H'.
  autorewrite with Ris_true in H2; apply H2.
  intros x Hx; generalize (H' _ Hx).
  mem_upd_simpl.
  unfold O.assoc at 1; simpl.
  case_eq (nat_eqb x (m1 id_H)); intro Heq.
  absurd (E.eval_expr (id_H in_dom L1) m1).
  assumption.
  autorewrite with Ris_true in H1.
  generalize (H1 _ Hx).
  simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  rewrite (nat_eqb_true Heq); trivial.
  trivial.
 Qed.

 Lemma EX_E5'E5_I5' : EqObsInv I5'
  {{T, J1, b, V, id_ex, L1, P, a, L3}}
  E5' Ex_5'
  E5  Ex_5
  {{T, J1, b, V, id_ex, L1, P, a, L3, d_ex}}.
 Proof.
  unfold Ex_5, Ex_5'.
  (* Annotation after call to H1 *)
  match goal with
  |- EqObsInv  ?P' ?I' _ _ _ _ _ =>
     apply equiv_cons with (req_mem_rel (Vset.add Q_ex I')
       ((EP1 (id_ex in_dom L1)) /-\ P'))
  end.
  set (iH1 := add_info H1 Vset.empty Vset.empty  iE5'E5_I5'_empty H1_E5'E5_I5').
  inline iH1 H1; [ apply (decMR_req_mem_rel _ dec_I5') | ].
  ep; eqobs_hd iE5'E5_I5'_empty.
  cp_test (id_ex in_dom L1).
    (* case [id_H in_dom L1] *)
  unfold I5'; eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [H1 H2] [H3 _] ] ]; repeat split.
  assumption.
  bprop; intros x Hx.
  autorewrite with Ris_true in H1; generalize (H1 _ Hx); bprop.
  mem_upd_simpl; trivial.
  bprop; intro H'.
  autorewrite with Ris_true in H2; apply H2.
  intros x Hx; generalize (H' _ Hx).
  mem_upd_simpl; trivial.
    (* case [~(id_H in_dom L1)] *)
  unfold I5'; eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [H1 H2] [H3 _] ] ] v Hv; repeat split.
  apply orb_true_intro; left; apply nat_eqb_refl.
  bprop; intros x Hx; bprop; right.
  autorewrite with Ris_true in H1; generalize (H1 _ Hx); bprop.
  mem_upd_simpl; trivial.
  bprop; intro H'.
  autorewrite with Ris_true in H2; apply H2.
  intros x Hx; generalize (H' _ Hx); clear Hx.
  mem_upd_simpl.
  unfold O.assoc at 1; simpl.
  case (nat_eqb x (m1 id_ex)).
  simpl; destruct H as [H4 _]; rewrite H4; simpl; intros ?; discriminate.
  trivial.
  apply orb_true_intro; left; apply nat_eqb_refl.
  bprop; intros x Hx; bprop; right.
  autorewrite with Ris_true in H1; generalize (H1 _ Hx); bprop.
  mem_upd_simpl; trivial.
  bprop; intro H'.
  autorewrite with Ris_true in H2; apply H2.
  intros x Hx; generalize (H' _ Hx).
  mem_upd_simpl.
  unfold O.assoc at 1; simpl.
  case_eq (nat_eqb x (m1 id_ex)); intro Heq.
  absurd (E.eval_expr (id_ex in_dom L1) m1).
  assumption.
  autorewrite with Ris_true in H1.
  generalize (H1 _ Hx).
  simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  rewrite (nat_eqb_true Heq); trivial.
  trivial.

  (* Case analysis *)
  cp_test_l  (Enth {J1 [{id_ex}], T}); ep.
  (* case  [ T[J1(id_ex)] = true ] *)
  unfold I5'; eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [H1 [H2 _] ] H3] ]; repeat split.
  rewrite H1.
  simpl; bprop; intros x Hx.
  autorewrite with Ris_true in H2; generalize (H2 _ Hx).
  mem_upd_simpl; trivial.
  rewrite H3; simpl; trivial.
  bprop; intros; rewrite is_true_forallb in H2.
  generalize (H2 _ H0); mem_upd_simpl.
  bprop.
  intro H0.
  assert (In (m1 id_ex) (m1 L3)).
  destruct H as [H _].
  rewrite <- is_true_negb, negb_involutive in H.
  apply is_true_existsb in H.
  destruct H as [x [Hin Heq] ].
  apply nat_eqb_true in Heq; rewrite Heq; trivial.
  generalize (H0 _ H4); rewrite H3; discriminate.

  (* case [ T[J1(id_ex)] = false ] *)
  unfold I5'; eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [H1 [H2 H3] ] H4] ]; repeat split.
  rewrite H1.
  simpl; bprop; intros x Hx.
  autorewrite with Ris_true in H2; generalize (H2 _ Hx).
  mem_upd_simpl.

  unfold notR in H4; rewrite not_is_true_false in H4; rewrite H4; simpl.
  bprop; intro H'.
  autorewrite with Ris_true in H3; apply H3.
  intros x Hx; generalize (H' _ Hx).
  mem_upd_simpl.
  bprop; intros; rewrite is_true_forallb in H2.
  generalize (H2 _ H0); mem_upd_simpl.
  bprop; intros; rewrite is_true_impb, is_true_forallb in H3.
  apply is_true_negb; apply H3.
  intros x Hx; mem_upd_simpl; auto.
 Qed.


 Definition iE5'E5_I5' :=
  let iH1 := add_info H1 Vset.empty Vset.empty iE5'E5_I5'_empty  H1_E5'E5_I5' in
  let iH2 := add_refl_info H2 iH1 in
  let iEx := add_info Ex Vset.empty  Vset.empty iH2 EX_E5'E5_I5' in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Lemma EqObs_G4''E5'_G4E5: EqObsRel
  I trueR
  E5' ((bad <- false) :: G4)
  E5  G5
  O (EP1 ((E.Eforall z' (!(Enth {J1[{z'}], T})) L3) ==> !bad)).
 Proof.
  apply equiv_weaken_req_mem_rel_implMR with I5';
   [ intros k m1 m2 [_ ?]; assumption | ].
  swap iE5'E5_I5'.
  eqobs_tl  iE5'E5_I5'.
  match goal with |- equiv _ _ _ _ ?c _ =>
    apply equiv_trans_eq_mem_l with
      (E1':= E5')
      (c1':=  CoinTosses ++ [bad <- false] ++ skipn 2 c)
      (P1:=trueR)
  end;
  simpl; [ swap; rewrite proj1_MR; apply equiv_eq_mem | |
    unfold trueR; intros _ _ _ _; trivial ].
  eqobs_hd_n 2%nat.
  unfold I5'; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
  intro; unfold impb; simpl; repeat split; trivial.
 Qed.

 Lemma Pr_G4_G5 : forall k (m:Mem.t k) (TT:Mem.t k -o> boolO),
  (forall m1 m2, req_mem_rel O
   (EP2 (E.Eforall z' (!Enth {J1 [{z'}], T}) L3 ==> (!bad))) k m1 m2 ->
   charfun TT m1 == charfun (TT [&&] negP (EP k bad)) m2) ->
  (forall m1 m2, req_mem_rel O
   (EP1 (E.Eforall z' (!Enth {J1 [{z'}], T}) L3 ==> (!bad))) k m1 m2 ->
   charfun (TT [&&] negP (EP k bad)) m1 == charfun TT m2) ->
  Pr E4 G4 m TT == Pr E5 G5 m TT.
 Proof.
  intros.
  transitivity (Pr E4'' ((bad<-false)::G4) m (TT [&&] negP (EP k bad))).
  apply (equiv_deno EqObs_G4E4_G4''E4''); [ | unfold trueR; split]; trivial.
  transitivity (Pr E5' ((bad<-false)::G4) m (TT [&&] negP (EP k bad))).
  unfold G4, Pr.
  setoid_rewrite deno_cons_elim; setoid_rewrite Mlet_simpl;
   setoid_rewrite deno_assign_elim.
  apply upto_bad_and_neg with iE4''E5'_uptobad; trivial.
  apply (equiv_deno EqObs_G4''E5'_G4E5); [ | unfold trueR; split]; trivial.
 Qed.

 Lemma Pr_G4_G5_S2 : forall k (m:Mem.t k),
  Pr E4 G4 m (@S2 k) == Pr E5 G5 m (@S2 k).
 Proof.
  intros.
  apply Pr_G4_G5.
  intros m1 m2 [H H1]; generalize H1.
  unfold S2, Success, GoodToss.
  bool_tauto_l H.
  intros m1 m2 [H H1]; generalize H1.
  unfold S2, Success, GoodToss.
  bool_tauto_r H.
 Qed.

 Lemma Pr_G4_G5_GT : forall k (m:Mem.t k),
  Pr E4 G4 m (@GoodToss k) == Pr E5 G5 m (@GoodToss k).
 Proof.
  intros.
  apply Pr_G4_G5.
  intros m1 m2 [H H1]; generalize H1; unfold GoodToss.
  bool_tauto_l H.
  intros m1 m2 [H H1]; generalize H1; unfold GoodToss.
  bool_tauto_r H.
 Qed.


 (** G5 --> G6 *)

 (*
    CHANGES IN THE GAME:
    1) Eager sampling of the hash value of [e(P,P)^(abc)] in [H2]
    2) Inline the call [H2(e(P,P)^abc)].

    RESULTS REGARDING PROBABILITY OF EVENTS:
    1) Probabilities of [GoodToss] and [Success /\ GoodToss]
    are preserved (games are obs equivalent -but [H2]'s memory
    is not-)
 *)

 Definition G6 :=
  [
   T <- Nil _;
   while Elen T <! qH1 do [ t <$- {0,1}_p; T <- T |++| (t |::| Nil _) ];
   L1 <- Nil _; L2 <- Nil _; L3 <- Nil _; J1 <- Nil _; V <- Nil _;
   P <$- G1o;
   a <$- [1..q-1];
   b <$- [1..q-1];
   c <$- [1..q-1];
   Ppub <- a |.| P;
   X <- e(P,P) |^| (a *! b *! c);
   X_hv <$- {0,1}^k;
   r1 <c- A1 with {};
   id_A <- Esnd r1;
   m0 <- Efst (Efst r1); m1 <- Esnd (Efst r1);
   d <$- {0,1};
   If d then [ m_d <- m0 ] else [ m_d <- m1 ];
   Q_A <c- H1 with {id_A};
   v' <- (V[{id_A}]^-1 *! c) mod_q; 
   y <- (v' |.| P | X_hv |x| m_d);
   d_A <c- A2 with {y}
  ].

 Definition H2_6 :=
  [
   If X =?= z_H then
    [
     hv <- X_hv;
     If !(X in_dom L2) _then [ L2 <- (X | X_hv) |::| L2 ]
    ]
   else H2_0
  ].

 Definition E6 :=  make_env H1_2 H2_6 Ex_5.


 Definition G5'' :=
  [
   T <- Nil _;
   while Elen T <! qH1 do [ t <$- {0,1}_p; T <- T |++| (t |::| Nil _) ];
   L1 <- Nil _; L2 <- Nil _; L3 <- Nil _; J1 <- Nil _; V <- Nil _;
   P <$- G1o;
   a <$- [1..q-1];
   b <$- [1..q-1];
   c <$- [1..q-1];
   Ppub <- a |.| P;
   X <- e(P,P) |^| (a *! b *! c);
   X_hv <$- {0,1}^k;
   r1 <c- A1 with {};
   id_A <- Esnd r1;
   m0 <- Efst (Efst r1); m1 <- Esnd (Efst r1);
   d <$- {0,1};
   If d then [ m_d <- m0 ] else [ m_d <- m1 ];
   Q_A <c- H1 with {id_A};
   v' <- (V[{id_A}]^-1 *! c) mod_q; 
   h2 <c- H2 with {X};
   y <- (v' |.| P | h2 |x| m_d);
   d_A <c- A2 with {y}
  ].

 Definition H2_5'' :=
  [
   If !(z_H in_dom L2) then
    [
     If X =?= z_H then [ hv <- X_hv ] else [ hv <$- {0,1}^k ];
     L2 <- (z_H | hv) |::| L2 
    ]
   else
    [ hv <- L2[{z_H}] ]
  ].

 Definition E5'' := make_env H1_2 H2_5'' Ex_5.

 Definition X_spl:=
  [ If !(X in_dom L2) then [ X_hv <$- {0,1}^k ] else [ X_hv <- L2[{X}] ] ].

 Lemma swap_equiv_H2 :
  equiv Meq
  E5   (proc_body E5 H2 ++ X_spl)
  E5'' (X_spl ++ proc_body E5'' H2)
  Meq.
 Proof.
  union_mod; [ trivial | ].
  apply equiv_strengthen with (kreq_mem {{z_H, L2, X}}).
  intros k m1 m2 Heq; rewrite Heq; apply req_mem_refl.
  apply EqObs_trans with E5   ((L2' <- L2)::(proc_body E5 H2 ++ X_spl));
   [deadcode; eqobs_in | ].
  apply EqObs_trans with E5'' ((L2' <- L2)::(X_spl ++ proc_body E5'' H2));
   [ | deadcode; eqobs_in].
  apply equiv_cons with (req_mem_rel {{L2', z_H, L2, X}} (EP1 (L2 =?= L2'))).
  eqobsrel_tail; unfold implMR; simpl; unfold O.eval_op; simpl; intros.
  change (E.eval_expr (L2 =?= L2) m1); rewrite <- expr_eval_eq; trivial.
  ep_eq L2 L2'.
  unfold EP1; intros k m1 m2 [Heq H1]; rewrite <- (expr_eval_eq m1 L2 L2') in H1.
  split; [trivial | transitivity (E.eval_expr L2 m1)].
  apply depend_only_fv_expr_subset with (2:=req_mem_sym Heq); vm_compute; trivial.
  rewrite H1.
  apply depend_only_fv_expr_subset with (2:=Heq); vm_compute; trivial.

  cp_test (X =?= z_H).

  cp_test (z_H in_dom L2').

  ep_eq_l L2 L2'.
  unfold req_mem_rel, andR; intros; decompose [and] H; apply expr_eval_eq; trivial.
  ep_eq_l (z_H in_dom L2') true.
  unfold andR; intros; decompose [and] H; trivial.
  swap; eqobs_in.

  alloc_l hv X_hv; ep; deadcode; swap; eqobs_in.
  
  (* X <> z_H *)
  cp_test (z_H in_dom L2').

  ep_eq_l L2 L2'.
  unfold req_mem_rel, andR; intros; decompose [and] H; apply expr_eval_eq; trivial.
  swap; eqobs_in.
  ep_eq_l (X =?= z_H) false.
  unfold EP1, andR, notR; intros; decompose [and] H; apply not_is_true_false; trivial.
  swap; eqobs_in.
 Qed.


 Definition XS := {{X_hv, X, L2}}.

 Lemma Modify_X_spl : forall E, Modify E XS X_spl.
 Proof.
  intro E.
  compute_assertion T' t' (modify (refl1_info (empty_info E E)) {{X,L2}} X_spl).
  apply modify_correct with (1:=T').
 Qed.

 Lemma EqObs_X_spl : EqObs XS E5 X_spl E5'' X_spl XS.
 Proof.
  eqobs_in.
 Qed.

 Lemma XS_global : forall x : VarP.Edec.t, Vset.mem x XS -> Var.is_global x.
 Proof.
  intro x; unfold XS.
  rewrite VsetP.add_spec, VsetP.add_spec, VsetP.add_spec.
  intros [H | [ H | [ H | H ] ] ]; inversion H; subst; trivial.
 Qed.

 Lemma swap_equiv_H1 :
  equiv Meq
  E5   (proc_body E5 H1 ++ X_spl)
  E5'' (X_spl ++ proc_body E5'' H1)
  Meq.
 Proof.
  union_mod; [ trivial | ]; swap; eqobs_in.
 Qed.

 Lemma swap_equiv_Ex :
  equiv Meq
  E5   (proc_body E5 Ex ++ X_spl)
  E5'' (X_spl ++ proc_body E5'' Ex)
  Meq.
 Proof.
  set (swi_H1:=add_sw_info _ _ Vset.empty _ _
   (@Modify_X_spl _) (@Modify_X_spl _)
   EqObs_X_spl XS_global (fun _ _ => None) _ _ swap_equiv_H1).
  apply check_swap_c_correct with (pi:=swi_H1) (I:=Vset.empty).
  apply Modify_X_spl.
  apply Modify_X_spl.
  apply EqObs_X_spl.
  vm_compute; trivial.
 Qed.

 Definition swi : forall tg (g_ : Proc.proc tg),
  option (sw_info X_spl XS Vset.empty E5 E5'' _ g_) :=
  let iH1 := add_sw_info _ _ Vset.empty _ _ (Modify_X_spl E5) (Modify_X_spl E5'') 
   EqObs_X_spl XS_global (fun t f => None) _ _ swap_equiv_H1 in
  let iH2 := add_sw_info _ _ Vset.empty _ _ (Modify_X_spl E5) (Modify_X_spl E5'') 
   EqObs_X_spl XS_global iH1 _ _  swap_equiv_H2 in
  let iEx := add_sw_info _ _ Vset.empty _ _ (Modify_X_spl E5) (Modify_X_spl E5'')
   EqObs_X_spl XS_global iH2 _ _  swap_equiv_Ex in
  let iA1 := add_sw_info_Adv _ _ Vset.empty _ _ (Modify_X_spl E5) (Modify_X_spl E5'') 
   EqObs_X_spl XS_global iEx _ A1 PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) in
  let iA2 := add_sw_info_Adv _ _ Vset.empty _ _ (Modify_X_spl E5) (Modify_X_spl E5'') 
   EqObs_X_spl XS_global iA1 _ A2 PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) in iA2.

 Definition iE5E5 :=
  let iH1 := add_refl_info_O H1 {{P, b, T, V, J1, L1, id_H}} Vset.empty Vset.empty (empty_info E5 E5) in
  let iH2 := add_refl_info_O H2 {{L2, hv}} Vset.empty Vset.empty iH1 in
  let iEx := add_refl_info_O Ex {{L3, a, P, L1, V, b, J1, T, d_ex}} Vset.empty Vset.empty iH2  in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Definition iE5''E5'' :=
  let iH1 := add_refl_info_O H1 {{P, b, T, V, J1, L1, id_H}} Vset.empty Vset.empty (empty_info E5'' E5'') in
  let iH2 := add_refl_info_O H2 {{X_hv, L2, hv}} Vset.empty Vset.empty iH1 in
  let iEx := add_refl_info_O Ex {{L3, a, P, L1, V, b, J1, T, d_ex}} Vset.empty Vset.empty iH2  in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.


 Lemma EqObs_G5_G5'' : EqObs I E5 G5 E5'' G5'' O.
 Proof.
  set (G4_t := map (fun i:I.instr => if (I.eqb i (h2 <c- H2 with {X})) then
   (h2 <c- H2 with { e(P,P) |^| (a *! b *! c) }) else i) (skipn 14 G5'')).
  apply EqObs_trans with E5 ((firstn 13 G5'') ++  (G4_t  ++ X_spl));
    [ ep iE5E5; deadcode iE5E5; swap iE5E5; eqobs_in iE5E5 | ].
  apply EqObs_trans with E5'' ((firstn 13 G5'') ++ (X_spl ++ G4_t));
   [ | ep iE5''E5''; swap iE5''E5''; eqobs_in iE5''E5'' ].
  apply equiv_app with 
   (kreq_mem (Vset.union {{T, L1, L2, L3, J1, V, P, a, b, c, Ppub, X}} Gadv)).
  eqobs_in.
  match goal with 
   |- equiv _ _ _ _ ?c _ =>
     apply equiv_trans_eq_mem_l with (E1':=E5'') (c1':=c) (P1:=trueR)
  end.
  rewrite proj1_MR.
  apply check_swap_c_correct with (pi:=swi) (I:=Vset.empty).
  apply Modify_X_spl.
  apply Modify_X_spl.
  apply EqObs_X_spl.
  vm_compute; trivial.
  eqobs_in iE5''E5''.
  red; intros; red; trivial.
 Qed.

 Definition H2_5''' :=
  [
   If X =?= z_H then
    [
     hv <- X_hv
    ]
   else 
    [
     If !(z_H in_dom L2)
     then [ hv <$- {0,1}^k; L2 <- (z_H | hv) |::| L2 ]
     else [ hv <- L2 [{z_H}] ]
    ]
  ].
 
 Definition E5''' := make_env H1_2 H2_5''' Ex_5.
 
 Definition I5'' := 
  EP1 ((X in_dom L2) ==> (L2[{X}] =?= X_hv)) /-\
  eq_assoc_except X L2.

 Lemma dec_I5'' : decMR I5''.
 Proof.
  unfold I5''; auto.
 Qed.

 Lemma dep_I5'' : depend_only_rel I5'' {{X_hv, X, L2}} {{L2}}.
 Proof.
  change {{X_hv, X, L2}} with (Vset.union {{X_hv, L2, X}} {{X, L2}}).
  change {{L2}} with (Vset.union Vset.empty {{L2}}).
  apply depend_only_andR.
  apply depend_only_EP1.
  apply depend_only_eq_assoc_except.
 Qed.

 Definition iE5''E5'''_I5''_empty : eq_inv_info I5'' E5'' E5'''.
  refine (@empty_inv_info _ _ _ dep_I5'' _ dec_I5'' _ _).
  vm_compute; trivial.
 Defined.

 Lemma H2_E5''E5'''_I5'' : EqObsInv I5''
  {{X_hv, X, z_H}}
  E5''  H2_5''
  E5''' H2_5'''
  {{hv, X_hv}}.
 Proof.
  cp_test (X =?= z_H).

  ep_eq z_H X.
  unfold andR; intros; decompose [and] H; split; symmetry;
   apply expr_eval_eq; trivial.
  
  cp_test_l (X in_dom L2).

  (* X in_dom L2 *)
  ep_eq_l (L2[{X}]) X_hv.
  unfold req_mem_rel, I5'', andR; intros; decompose [and] H; clear H.
  apply expr_eval_eq; apply expr_modus_ponens with (e1:=X in_dom L2); trivial.
  eqobs_in iE5''E5'''_I5''_empty.
  unfold implMR, andR; tauto.
 
  (* X not in_dom L2 *)
  unfold I5''; eqobsrel_tail;
   unfold implMR, EP1, EP2, andR, notR; intros; decompose [and] H; clear H;
   simpl; unfold O.eval_op; simpl; split; mem_upd_simpl.
  unfold O.assoc; simpl; rewrite G2.eqb_refl; simpl; rewrite Veqb_refl; trivial.

  intros ? H; destruct (H4 _ H); unfold O.assoc; simpl.
  case_eq (G2.eqb r (m1 X)); intro; simpl.
  elim H; apply G2.eqb_true; trivial.
  tauto.
  

  (* X <> z_H *)
  cp_test (z_H in_dom L2).
 
  unfold req_mem_rel, I5'', andR, notR; intros; decompose [and] H.
  assert (m1 z_H <> m1 X).
  intro Heq; elim H3; unfold EP1; simpl; unfold O.eval_op; simpl.
  rewrite Heq; apply G2.eqb_refl.
  destruct (H4 _ H1).
  simpl; unfold O.eval_op; simpl; rewrite <- (H2 _ z_H); trivial.

  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold req_mem_rel, upd_para, andR; intros.
  decompose [and] H; clear H; split.
  unfold kreq_mem;match goal with
  |- _{! _ <-- ?x1!} =={_} _{! _ <-- ?x2!} => replace x2 with x1
  end.
  apply req_mem_update; apply req_mem_weaken with (2:=H0); vm_compute; trivial.
  unfold notR, EP1 in H2; rewrite <- (expr_eval_eq m1 X z_H) in H2.
  apply sym_not_eq in H2.
  destruct H4 as (W1, W2);  destruct (W2 _ H2).
  assert (E.eval_expr z_H m1 = E.eval_expr z_H m2) by
   (simpl; rewrite (H0 _ z_H); apply  refl_equal).
  generalize H1;rewrite H4 at 2;trivial.
  apply (@dep_I5'' k m1 m2);trivial.
  apply req_mem_upd_disjoint;vm_compute;trivial.
  apply req_mem_upd_disjoint;vm_compute;trivial.

  unfold I5''; eqobsrel_tail;
   unfold implMR, andR; simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros; decompose [and] H; clear H.
  unfold notR, EP1 in H4; generalize H4; simpl; unfold O.eval_op; simpl; intros W.
  apply not_true_is_false in W; rewrite W; split; trivial.

  intros r H; generalize (H5 _ H); simpl; unfold O.eval_op, O.assoc; simpl.
  intros [W1 W2].
  replace (m2 z_H) with (m1 z_H); trivial.
  split; [rewrite W1; trivial | ].
  destruct (G2.eqb r (m1 z_H)); trivial.
  apply H1; trivial.
 Qed.

 Definition iE5''E5''' :=
  let iH1 := add_refl_info_O H1 {{V,J1,T,b,id_H,L1,P}} Vset.empty Vset.empty iE5''E5'''_I5''_empty in
  let iH2 := add_info H2 Vset.empty Vset.empty iH1 H2_E5''E5'''_I5'' in
  let iEx := add_refl_info Ex iH2 in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Definition iE5'''E5''' :=
  let iH1 := add_refl_info_O H1 (Vset.union {{P,b,T,V,J1}} {{L1, id_H}}) Vset.empty Vset.empty (empty_info E5''' E5''') in
  let iH2 := add_refl_info_O H2 {{X_hv, L2, hv}} Vset.empty Vset.empty iH1 in
  let iEx := add_refl_info_O Ex {{L3, a, P, L1, V, b, J1, T, d_ex}} Vset.empty Vset.empty iH2 in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.


 Lemma EqObs_G5''E5''_G6E5''' : EqObs 
  I 
  E5''  G5'' 
  E5''' G6 
  (Vset.remove L2 O).
 Proof.
  unfold G5'', G6; simpl firstn; simpl skipn.
  eqobs_hd_n 2%nat.
  match goal with 
   |- EqObs _ _ ?c1 _ ?c2 _ =>
   rewrite <- (firstn_skipn 12 c1), <- (firstn_skipn 12 c2)
  end.
  apply equiv_app with 
   (req_mem_rel {{g_a,T,L1,L2,L3,V,J1,P,a,b,c,Ppub,X,X_hv}} 
    (EP1 (L2 =?= Nil _))); simpl.

  eqobsrel_tail; unfold EP1; simpl; unfold O.eval_op; simpl; red; intros; trivial.
  
  match goal with 
   |- equiv (req_mem_rel ?I' _)  _ ?c _ _ ?Q' =>
    apply equiv_trans with (P1:=req_mem_rel I' I5'') (Q1:=Q') (Q2:=Q')
     (E2:=E5''') (c2:=c)
  end.
  auto using dec_I5''.
  unfold req_mem_rel, I5'', andR; intros k m1 m2 H; decompose [and] H; repeat split.

  unfold EP1 in H1 |- *; apply expr_eval_eq in H1.
  simpl in H1 |- *; unfold O.eval_op; simpl; rewrite H1; trivial.
 
  apply req_mem_trans.

  eqobs_in iE5''E5'''.
 
  sinline_l iE5'''E5''' H2.
  swap iE5'''E5'''.
  eqobs_tl iE5'''E5'''.
  nil_nil_tac.
 Qed.

 Definition I5''' :=
  EP2 ((X in_dom L2) ==> (L2[{X}] =?= X_hv)) /-\ eq_assoc_except X L2.

 Lemma dec_I5''' : decMR I5'''.
 Proof.
  unfold I5'''; auto.
 Qed.

 Lemma dep_I5''' : depend_only_rel I5'''
  {{X, L2}} {{X_hv, X, L2}}.
 Proof.
  change {{X, L2}} at 1 with (Vset.union Vset.empty {{X, L2}}).
  change {{X_hv, X, L2}} with (Vset.union {{X_hv, L2, X}} {{L2}}).
  apply depend_only_andR.
  apply depend_only_EP2.
  apply depend_only_eq_assoc_except.
 Qed.

 Definition iE5'''E6_I5'''_empty : eq_inv_info I5''' E5''' E6.
  refine (@empty_inv_info _ _ _ dep_I5''' _ dec_I5''' _ _).
  vm_compute; trivial.
 Defined.

 Lemma H2_E5'''E6_I5''' : EqObsInv I5'''
  {{X_hv, X, z_H}}
  E5''' H2_5'''
  E6    H2_6
  {{hv, X_hv}}.
 Proof.
  cp_test (X =?= z_H).
  
  (* case [z_H = X] *)
  ep_eq z_H X.
  intros k m1 m2 [ [? ?] [? ?] ].
  split; symmetry; rewrite expr_eval_eq; trivial.

  cp_test_r (X in_dom L2).

  eqobs_in iE5'''E6_I5'''_empty.
  unfold implMR, andR; tauto.

  swap; eqobs_tl iE5'''E6_I5'''_empty.
  clear. 
  unfold I5'''; eqobsrel_tail; simpl; unfold O.eval_op; simpl;
   unfold implMR, I5'', andR, notR; intros; decompose [and] H; clear H; split.

  unfold O.assoc; simpl; rewrite G2.eqb_refl, Veqb_refl; trivial.
  
  unfold O.assoc; simpl; intros ? H; destruct (H4 _ H).
  rewrite <- (H0 _ X); [ | trivial].
  case_eq (G2.eqb r (m1 X)); intro.
  elim H; apply G2.eqb_true; trivial.
  split; trivial.
  
  (* case [z_H <> X] *)
  cp_test (z_H in_dom L2).

  unfold req_mem_rel, I5''', andR, notR; intros; decompose [and] H.
  assert (m1 z_H <> m1 X).
  intro Heq; elim H3; unfold EP1; simpl; unfold O.eval_op; simpl.
  rewrite Heq; apply G2.eqb_refl.
  destruct (H4 _ H1).
  simpl; unfold O.eval_op; simpl; rewrite <- (H2 _ z_H); trivial.
  
  eapply equiv_strengthen; [ | apply equiv_assign].
  unfold req_mem_rel, upd_para, andR; intros; decompose [and] H; clear H; split.
  unfold kreq_mem;match goal with
  |- _{! _ <-- ?x1!} =={_} _{! _ <-- ?x2!} => replace x2 with x1
  end.
  apply req_mem_update; apply req_mem_weaken with (2:=H0); vm_compute; trivial.
  unfold notR, EP1 in H2; rewrite <- (expr_eval_eq m1 X z_H) in H2.
  apply sym_not_eq in H2.
  destruct H4 as (W1, W2);  destruct (W2 _ H2).
  assert (E.eval_expr z_H m1 = E.eval_expr z_H m2) by
   (simpl; rewrite (H0 _ z_H); trivial).
  generalize H1; rewrite H4 at 2; trivial.
  apply (@dep_I5''' k m1 m2); trivial.
  apply req_mem_upd_disjoint; vm_compute; trivial.
  apply req_mem_upd_disjoint; vm_compute; trivial.

  unfold I5'''; eqobsrel_tail; unfold implMR; simpl; unfold O.eval_op; simpl.
  unfold O.assoc, andR, notR; simpl; intros; decompose [and] H; clear H.
  unfold EP2 in H7; simpl in H7; unfold O.eval_op in H7; simpl in H7.
  apply not_is_true_false in H7; rewrite H7; split.
  trivial.
  intros ? H; destruct (H5 _ H).
  rewrite <- (H1 _ z_H); [ | trivial].
  split; case (G2.eqb r (m1 z_H)); trivial.
 Qed.

 Definition iE5'''E6_I5''' :=
  let iH1 := add_refl_info_O H1 {{V, J1, T, b, id_H, L1, P}} Vset.empty Vset.empty iE5'''E6_I5'''_empty in
  let iH2 := add_info H2 Vset.empty Vset.empty iH1 H2_E5'''E6_I5''' in
  let iEx := add_refl_info Ex iH2 in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Lemma EqObs_G5''_G6 : EqObs
  I
  E5''' G6
  E6    G6
  (Vset.remove L2 O).
 Proof.
  eqobs_tl iE5'''E6_I5'''.
  eqobs_hd_n 2%nat.
  eqobsrel_tail; 
  unfold I5''', EP2, eq_assoc_except; simpl; unfold O.eval_op; simpl.
  repeat split; mem_upd_simpl; try tauto; discriminate.
 Qed.

 Lemma EqObs_G5_G6 : EqObs I E5 G5 E6 G6 (Vset.remove L2 O).
 Proof.
  apply EqObs_trans with E5'' G5''.
  eapply equiv_weaken; [ | apply EqObs_G5_G5''];
   intros k m1 m2; apply req_mem_weaken; vm_compute; trivial.
  apply EqObs_trans with E5''' G6.
  apply EqObs_G5''E5''_G6E5'''.
  apply EqObs_G5''_G6.
 Qed.

 Lemma Pr_G5_G6_S2 : forall k (m:Mem.t k),
  Pr E5 G5 m (@S2 k) == Pr E6 G6 m (@S2 k).
 Proof.
  intros.
  apply (equiv_deno EqObs_G5_G6); [ | trivial].
  intros m1 m2 H; unfold S2, Success, GoodToss, andP, andb, charfun, restr, EP.
  repeat (rewrite depend_only_fv_expr_subset with (2:=H);
   [ | vm_compute]; trivial).
 Qed.

 Lemma Pr_G5_G6_GT : forall k (m:Mem.t k),
  Pr E5 G5 m (@GoodToss k) == Pr E6 G6 m (@GoodToss k).
 Proof.
  intros.
  apply (equiv_deno EqObs_G5_G6); [ | trivial].
  intros m1 m2 H; unfold GoodToss, charfun, restr, EP, andP, andb, fone.
  repeat (rewrite depend_only_fv_expr_subset with (2:=H);
   [ | vm_compute]; trivial).
 Qed.

 Lemma G6_lossless : lossless E6 G6.
 Proof.
  change (lossless E6 (CoinTosses ++ (skipn 2 G6))).
  apply lossless_app.
  apply CoinTosses_lossless.
  apply is_lossless_correct with (refl2_info iE5'''E6_I5'''); vm_compute; trivial.
 Qed.


 (** G6 --> G7 *)

 (*
    CHANGES IN THE GAME:
    1) Replace the ciphertext [y] with a random one (games are
    obs. equiv. if [X_queried] does not hold).
    2) Now [y] becomes independent of [d], and [d]'s sampling can
    be pushed down to end of the game.

    RESULTS REGARDING PROBABILITY OF EVENTS:
    1) Probabilities of [X_queried] is preserved (since probability 
    of [~X_queried] is preserved -fundamental lemma-)
    2) Bound the probability of event [GoodToss /\ X_queried]
    in [G6].
    *)


 Definition G7 :=
  [
   T <- Nil _;
   while Elen T <! qH1 do [ t <$- {0,1}_p; T <- T |++| (t |::| Nil _) ];
   L1 <- Nil _; L2 <- Nil _; L3 <- Nil _; J1 <- Nil _; V <- Nil _;
   P <$- G1o;
   a <$- [1..q-1];
   b <$- [1..q-1];
   c <$- [1..q-1];
   R <$- {0,1}^k;
   Ppub <- a |.| P;
   r1 <c- A1 with {};
   id_A <- Esnd r1;
   m0 <- Efst (Efst r1); m1 <- Esnd (Efst r1);
   Q_A <c- H1 with {id_A};
   v' <- ((V [{id_A}]) ^-1) *! c mod_q;
   y <- ( v' |.| P | R);
   d_A <c- A2 with {y};
   d <$- {0,1}
  ].

 Definition E7 := E5.

 Definition H2_6_bad1 :=
  [
   If e(P,P) |^| (a *! b *! c) =?= z_H then
    [
     bad <- true;
     hv <- X_hv;
     If !(e(P,P) |^| (a *! b *! c) in_dom L2) _then
     [ L2 <- (e(P,P) |^| (a *! b *!c) | hv) |::| L2  ]
    ]
   else H2_0
  ].

 Definition E6_bad1 := make_env H1_2 H2_6_bad1 Ex_5.

 Definition I6_b1 :=
  EP2 (bad ==> ((e(P,P) |^| (a *! b *! c)) in_dom L2)) /-\
  EP1 (X =?= e(P,P) |^| (a *! b *! c)).

 Lemma dec_I6_b1 : decMR I6_b1.
 Proof.
  unfold I6_b1; auto.
 Qed.

 Lemma dep_I6_b1 : depend_only_rel I6_b1 
  {{c, b, a, P, X}} {{L2, c, b, a, P, bad}}.
 Proof.
  change {{c, b, a, P, X}} with (Vset.union Vset.empty {{c, b, a, P, X}}).
  change {{L2, c, b, a, P, bad}} with 
   (Vset.union {{L2, c, b, a, P, bad}} Vset.empty).
  unfold  I6_b1; apply depend_only_andR.
  apply depend_only_EP2.
  apply depend_only_EP1.
 Qed.

 Definition iE6E6_bad1_I6_b1_empty : eq_inv_info I6_b1 E6 E6_bad1.
  refine (@empty_inv_info _ _ _ dep_I6_b1 _ dec_I6_b1 _ _).
  vm_compute; trivial.
 Defined.

 Lemma H2_E6E6_bad1_I6_b1 : EqObsInv I6_b1
  {{L2, X_hv, P,a,b,c, z_H}}
  E6 H2_6
  E6_bad1 H2_6_bad1
  {{L2, hv, X_hv, P,a,b,c}}.
 Proof.
  unfold H2_6, H2_6_bad1.
  ep_eq_l X (e(P,P) |^| (a *! b *! c));
   [ intros k m1 m2 [_ [_ ?] ]; rewrite expr_eval_eq; assumption | ].
  cp_test (e(P,P) |^| (a *! b *! c) =?= z_H).
    (* case [z_H=e(P,P) |^| (a *! b *! c)] *)
  unfold I6_b1; eqobsrel_tail; unfold EP2, EP1 ;simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H0 [ [_ H1] [_ H2] ] ]; split.
  rewrite H2, H1; unfold impb; simpl.
  intros _; split; trivial.
  intros [_ H']; rewrite H1; split; trivial.
  unfold is_true in H2; rewrite G2.eqb_true in H2; rewrite <-H2 in H'.
  apply eq_true_negb_classical in H'; rewrite H'; apply impb_true_r.
    (* case [z_H<>e(P,P) |^| (a *! b *! c)] *)
  unfold I6_b1; eqobsrel_tail; unfold EP2, EP1, notR ;simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [ [H1 H2] _ ] ]; repeat split.
  bprop; intro H'.
  autorewrite with Ris_true in H1.
  right; exact (H1 H').
  exact H2.
  exact H1.
  exact H2.
 Qed.

 Definition iE6E6_bad1_I6_b1 :=
  let iH1 := add_refl_info_O H1 {{V,J1,T,b,id_H,L1,P}} Vset.empty Vset.empty iE6E6_bad1_I6_b1_empty in
  let iH2 := add_info H2 {{bad}} Vset.empty iH1 H2_E6E6_bad1_I6_b1 in
  let iEx := add_refl_info Ex iH2 in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Lemma EqObs_G6E6_G6E6b1_I6_b1: EqObsRel
  I trueR
  E6      G6
  E6_bad1 ((bad <- false)::G6)
  O I6_b1.
 Proof.
  unfold G6.
  eqobs_tl iE6E6_bad1_I6_b1.
  match goal with |- equiv _ _ ?c1 ?e2 (?i::?c1) _ =>
   apply equiv_trans_eq_mem_r with
    (E2':= e2)
    (c2':= c1 ++ [i] )
    (P2:=trueR); simpl
  end;
  [ swap; rewrite proj1_MR; apply equiv_eq_mem | |
   unfold trueR; intros _ _ _ _; trivial ].
  eqobs_hd_n 2%nat.
  unfold I6_b1; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 H; split.
  unfold impb; simpl; trivial.
  apply G2.eqb_refl.
 Qed.


 Definition H2_6_bad2 :=
  [
   If (e(P,P) |^| (a *! b *! c) =?= z_H) then
    [bad <- true] ++ H2_0
   else H2_0
  ].

 Definition E6_bad2 := make_env H1_2 H2_6_bad2 Ex_5.


 (* (((bad<-false)::G6),E6_bad1) and (((bad<-false)::G6), E6_bad2) 
    are identical upto bad *)
 Definition iE6bad :=
  let iH1 := add_upto_info (empty_upto_info bad E6_bad1 E6_bad2) H1 in
  let iH2 := add_upto_info iH1 H2 in
  let iEx := add_upto_info iH2 Ex in
  let iA1 := add_adv_upto_info iEx (EqAD _ _ _ _ _ _) (EqOP _ _ _ _ _ _) (A1_wf_E _ _ _) in
  let iA2 := add_adv_upto_info iA1 (EqAD _ _ _ _ _ _) (EqOP _ _ _ _ _ _) (A2_wf_E _ _ _) in iA2.


 Definition I6_b2 := EP1 (bad ==> ((e(P,P) |^| (a *! b *! c)) in_dom L2)).

 Lemma dec_I6_b2 : decMR I6_b2.
 Proof.
  unfold I6_b2; auto.
 Qed.

 Lemma dep_I6_b2 : depend_only_rel I6_b2 {{L2, c, b, a, P, bad}} Vset.empty.
 Proof.
  unfold  I6_b2; apply depend_only_EP1.
 Qed.

 Definition iE6_bad2_E7_I6_b2_empty : eq_inv_info I6_b2 E6_bad2 E7.
  refine (@empty_inv_info _ _ _ dep_I6_b2 _ dec_I6_b2 _ _).
  vm_compute; trivial.
 Defined.

 Lemma H2_E6_bad2E7_I6_b2 : EqObsInv I6_b2
  {{L2, P, a, b, c, z_H}}
  E6_bad2 H2_6_bad2
  E7 H2_0
  {{L2, hv, P, a, b, c}}.
 Proof.
  unfold H2_6_bad2, H2_0.
  cp_test (e(P,P) |^| (a *! b *! c) =?= z_H).
  (* case [z_H=e(P,P) |^| (a *! b *! c)] *)
  unfold I6_b2; eqobsrel_tail; unfold EP2, EP1 ;simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [_ [H1 _] ] ]; split.
  intros; rewrite H1; simpl; apply impb_true_r; trivial.
  intros [H _]; apply eq_true_negb_classical in H.
  unfold is_true in H1; rewrite G2.eqb_true in H1; rewrite H1.
  rewrite H; apply impb_true_r; trivial.
 
  (* case [z_H<>e(P,P) |^| (a *! b *! c)] *)
  unfold I6_b2; eqobsrel_tail; 
   unfold EP2, EP1, notR ;simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [H1 _] ]; repeat split.
  intros; bprop; intro; autorewrite with Ris_true in H1; tauto.
  tauto.
 Qed.

 Definition iE6_bad2_E7_I6_b2 :=
  let iH1 := add_refl_info_O H1 {{V, J1, T, b, id_H, L1, P}} Vset.empty Vset.empty   iE6_bad2_E7_I6_b2_empty in
  let iH2 := add_info H2 Vset.empty Vset.empty iH1 H2_E6_bad2E7_I6_b2 in
  let iEx := add_refl_info Ex iH2 in
  let iA1 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless (EqAD _ _ _ _ _ _) (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Lemma EqObs_G6E6b2_G6E7_I6_b2 : EqObsRel
  I trueR
  E6_bad2 ((bad<-false)::G6)
  E7      G6
  O I6_b2.
 Proof.
  unfold G6.
  eqobs_tl  iE6_bad2_E7_I6_b2.
  match goal with |- equiv _ ?e1 (?i::?c1) _ ?c1 _ =>
    apply equiv_trans_eq_mem_l with
     (E1':= e1)
     (c1':= c1 ++ [i] )
     (P1:=trueR); simpl
  end;
  [ swap; rewrite proj1_MR; apply equiv_eq_mem | |
      unfold trueR; intros _ _ _ _; trivial ].
  eqobs_hd_n 2%nat.
  unfold I6_b2; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
  intros _ _ _ _ _ _ _ _ _ _ _ _; trivial.
 Qed.

 Lemma EqObs_G6E7_G7E7 : EqObs I E7 G6 E7 G7 O.
 Proof.
  unfold G6, G7.
  eqobs_hd; deadcode iE5E5.
  swap iE5E5; eqobs_tl iE5E5.
  apply EqObs_trans with E7
   [
     Ppub <- a |.| P;
     r1 <c- A1 with {};
     id_A <- Esnd (r1);
     m0 <- Efst (Efst (r1));
     m1 <- Esnd (Efst (r1));
     d <$- {0,1};
     If d then [m_d <- m0] else [m_d <- m1];
     Q_A <c- H1 with {id_A};
     v' <- ((V [{id_A}]) ^-1) *! c mod_q;
     X_hv <$- {0,1}^k;
     R <-  X_hv |x| m_d;
     y <- (v' |.| P | R )
   ];
   [ ep iE5E5; deadcode iE5E5; swap iE5E5; eqobs_in iE5E5 | ].
  apply EqObs_trans with E7
   [
     Ppub <- a |.| P;
     r1 <c- A1 with {};
     id_A <- Esnd (r1);
     m0 <- Efst (Efst (r1));
     m1 <- Esnd (Efst (r1));
     d <$- {0,1};
     If d then [m_d <- m0] else [m_d <- m1];
     Q_A <c- H1 with {id_A};
     v' <- ((V [{id_A}]) ^-1) *! c mod_q;
     R <$- {0,1}^k;
     X_hv <- R |x| m_d;
     y <- (v' |.| P | R)
   ];
   [ | deadcode iE5E5; swap iE5E5; eqobs_in iE5E5 ].

   eqobs_ctxt iE5E5; union_mod.
   apply equiv_sub with (kreq_mem {{m_d}}) (kreq_mem {{X_hv, R, m_d}}).
   intros k m1 m2; apply req_mem_weaken; vm_compute; trivial.
   intros k m1 m2; apply req_mem_weaken; vm_compute; trivial.
   refine (opt_sampling E7 _ _ _); discriminate.
 Qed.


 Lemma Pr_G6_G7 : forall k (m:Mem.t k) (T:Mem.t k -o> boolO),
  (forall m1 m2, req_mem_rel O I6_b1 k m1 m2 ->
   charfun T m1 == charfun (T [&&] negP (EP k bad)) m2) ->
  (forall m1 m2, req_mem_rel O I6_b2 k m1 m2 ->
   charfun (T [&&] negP (EP k bad)) m1 == charfun T m2) ->
  (forall m1 m2, kreq_mem O m1 m2 -> charfun T m1 == charfun T m2) ->
  Pr E6 G6 m T == Pr E7 G7 m T.
 Proof.
  intros.
  transitivity (Pr E6_bad1 ((bad<-false)::G6) m (T [&&] negP (EP k bad))).
  apply (equiv_deno EqObs_G6E6_G6E6b1_I6_b1);
   [ assumption | unfold trueR; split; trivial].
  transitivity (Pr E6_bad2 ((bad<-false)::G6) m (T  [&&] negP (EP k bad))).
  unfold Pr.
  setoid_rewrite deno_cons_elim; setoid_rewrite Mlet_simpl;
   setoid_rewrite deno_assign_elim.
  eapply upto_bad_and_neg with iE6bad; trivial.
  transitivity (Pr E7 G6 m T).
  apply (equiv_deno EqObs_G6E6b2_G6E7_I6_b2);
   [ assumption | unfold trueR; split; trivial].
  apply equiv_deno with (1:= EqObs_G6E7_G7E7);
   [ assumption | trivial].
 Qed.

 Lemma Pr_G6G7_S2_nXQ : forall k (m:Mem.t k),
  Pr E6 G6 m ((@S2 k) [&&] negP (@X_queried k)) ==
  Pr E7 G7 m ((@S2 k) [&&] negP (@X_queried k)).
 Proof.
  intros k m; apply Pr_G6_G7.
  intros m1 m2 [H [H1 _] ]; generalize H1.
  unfold I6_b1, S2, Success, GoodToss, X_queried.
  bool_tauto_l H.
  intros m1 m2 [H H1]; generalize H1.
  unfold I6_b2, S2, Success, GoodToss, X_queried.
  bool_tauto_r H.
  intros m1 m2 H; unfold  S2, Success, GoodToss, X_queried.
  rewrite_req_mem_l H.
 Qed.

 Lemma Pr_G6G7_GT_nXQ : forall k (m:Mem.t k),
  Pr E6 G6 m ((@GoodToss k) [&&] negP (@X_queried k)) ==
  Pr E7 G7 m ((@GoodToss k) [&&] negP (@X_queried k)).
 Proof.
  intros k m; apply Pr_G6_G7.
  intros m1 m2 [H [H1 _] ]; generalize H1.
  unfold I6_b1, GoodToss, X_queried.
  bool_tauto_l H.
  intros m1 m2 [H H1]; generalize H1.
  unfold I6_b2, GoodToss, X_queried.
  bool_tauto_r H.
  intros m1 m2 H; unfold GoodToss, X_queried.
  rewrite_req_mem_l H.
 Qed.

 Lemma G7_lossless : lossless E7 G7.
 Proof.
  change (lossless E7 (CoinTosses ++ (skipn 2 G7))).
  apply lossless_app.
  apply CoinTosses_lossless.
  apply is_lossless_correct with (refl2_info iE5E5); vm_compute; trivial.
 Qed.

 Lemma Pr_G6G7_XQ : forall k (m:Mem.t k),
  Pr E6 G6 m (@X_queried k) == Pr E7 G7 m (@X_queried k).
 Proof.
  intros.
  transitivity (Pr E6 G6 m (negP (negP (@X_queried k))));
   [ apply mu_stable_eq; apply charfun_eq_compat; rewrite negP_involutive; trivial | ].
  transitivity (Pr E7 G7 m (negP (negP (@X_queried k))));
   [ | apply mu_stable_eq; apply charfun_eq_compat; rewrite negP_involutive; trivial ].
  rewrite (@Pr_neg _ E6 G6), (@Pr_neg _ E7 G7);
   [ Usimpl | apply G7_lossless | apply G6_lossless ].
  apply Pr_G6_G7.
  intros m1 m2 [H [H1 _] ]; generalize H1.
  unfold I6_b1, X_queried.
  bool_tauto_l H.
  intros m1 m2 [H H1]; generalize H1.
  unfold I6_b2, X_queried.
  bool_tauto_r H.
  intros m1 m2 H; unfold GoodToss, X_queried.
  rewrite_req_mem_l H.
 Qed.

 Open Scope U_scope.

 Lemma BlindGuess : forall k (m:Mem.t k),
  Pr E7 G7 m ((@S2 k) [&&] negP (@X_queried k)) ==
  [1/2] * Pr  E7 (removelast G7) m ((@GoodToss k) [&&] negP (@X_queried k)).
 Proof.
  intros.
  change G7 at 1 with ((removelast G7) ++ [ d <$- {0,1} ]).
  unfold Pr; rewrite (deno_app_elim _ _ _ m).

  match eval vm_compute in 
   (modify (refl2_info iE5E5) Vset.empty (removelast G7)) with
   | Some ?x => set (M':=x); rewrite (@Modify_deno_elim _ M');
    [ | apply modify_correct with (refl2_info iE5E5) Vset.empty; vm_compute; trivial ]
  end.
  transitivity
  (mu (([[(removelast G7)]]) E7 m)
    (fun m' => mu (([[ [ d <$- {0,1} ] ]]) E7 (m {!M' <<- m'!})) (fun x =>
      (charfun (@Success k) x) *
      (charfun ((@GoodToss k) [&&] negP (@X_queried k))) m'))).
  apply mu_stable_eq; refine (ford_eq_intro _); intro m1.
  repeat rewrite deno_random_elim.
  apply sum_support_stable_eq; intros v Hv.
  unfold S2; repeat rewrite charfun_and_elim.
  rewrite <-Umult_assoc; apply Umult_eq_compat_right.
  unfold charfun, restr, GoodToss, X_queried, EP, andP, negP, fone.
  assert (H : forall t (expr : E.expr t),
   (fv_expr expr) [<=] M' ->
   Vset.mem d (fv_expr expr) = false ->
   E.eval_expr expr  ((m {!M' <<- m1!}) {!d <-- v!}) = E.eval_expr expr  m1).
  intros; apply depend_only_fv_expr.
  apply  req_mem_upd_notin_l; [|rewrite H0; apply diff_false_true].
  apply req_mem_weaken with M';
   [assumption | apply req_mem_update_mem_l].
 
  repeat (rewrite H; [ | unfold Vset.subset; auto | auto]); trivial.
  eapply Oeq_trans with (mu (([[(removelast G7)]]) E7 m) (fun m' => _ )).
  apply mu_stable_eq; refine (ford_eq_intro _); intro m1.
  apply mu_stable_mult_right.
  eapply Oeq_trans with  (mu (([[(removelast G7)]]) E7 m) (fun m' => _ * [1/2])).
  apply mu_stable_eq; refine (ford_eq_intro _); intro m1.
  rewrite Umult_sym; apply Umult_eq_compat_right.
  change [d <$- {0,1}] with ( (@nil I.instr) ++ [d <$- {0,1}]).
  apply Pr_sample_bool.
  discriminate.
  apply lossless_nil.
  rewrite mu_stable_mult_right; apply Umult_sym.
 Qed.

 Open Scope O_scope.


 Lemma Pr_G6_S2_upper : forall k (m:Mem.t k),
   Pr E6 G6 m (@S2 k) <= 
   [1/2] * Pr E6 G6 m (@GoodToss k) + [1/2] * Pr E6 G6 m ((@GoodToss k) [&&] (@X_queried k)).
 Proof.
  intros.
  assert (H0 : EqObs I E7 (removelast G7) E7 G7 (Vset.remove d O)) by
    (deadcode iE5E5; eqobs_in iE5E5).
  rewrite (Pr_split _ _ _  (@X_queried k)),  Pr_G6G7_S2_nXQ, BlindGuess.
  unfold Pr at 2; rewrite (equiv_deno H0 _ (charfun ((@GoodToss k) [&&] negP (@X_queried k))));
       [clear H0 | intros m1 m2 H; unfold GoodToss, X_queried; rewrite_req_mem_l H |  apply req_mem_refl ].
  fold (Pr E7 G7 m ((@GoodToss k) [&&] negP (@X_queried k))); rewrite <-Pr_G6G7_GT_nXQ.
  rewrite (@Uplus_le_compat_left 
     (Pr E6 G6 m ((@S2 k) [&&] (@X_queried k)))
     (([1/2] * (Pr E6 G6  m ((@GoodToss k) [&&] (@X_queried k)))) +
       [1/2] * (Pr E6 G6 m ((@GoodToss k) [&&] (@X_queried k)))) _).
    rewrite Uplus_sym, Uplus_assoc; apply Uplus_le_compat_left.
    rewrite <-Udistr_plus_left, Uplus_sym, <-(Pr_split _ _ _ (@X_queried k) _);
      [ | apply Uinv_le_trans with (Pr E6 G6 m (negP (@X_queried k))) (Pr E6 G6  m (@X_queried k));
          [ rewrite Pr_neg; [ | apply G6_lossless ] | rewrite proj2_BP | rewrite proj2_BP ] ] ; trivial.
  rewrite Umult_sym, <-Udistr_plus_left, Unth_one_plus, Umult_one_right;
       [ | apply Uinv_le_half_left; trivial ].
    unfold S2; rewrite andP_assoc, proj2_BP; trivial.
 Qed.

 Lemma Pr_G6_S2_lower : forall k (m:Mem.t k),
  [1/2] * Pr E6 G6 m (@GoodToss k) - [1/2] * Pr E6 G6 m ((@GoodToss k) [&&] (@X_queried k)) <= 
  Pr E6 G6 m (@S2 k).
 Proof.
  intros.
  transitivity ([1/2] * Pr E6 G6 m ((@GoodToss k) [&&] negP (@X_queried k))).
    rewrite <-Uminus_distr_right; apply Umult_le_compat_right.
    apply Uplus_le_perm_left; rewrite (Pr_split _ _ _  (@X_queried k)); trivial.
  rewrite Pr_G6G7_GT_nXQ.  
  assert (H0 : EqObs I E7 (removelast G7) E7 G7 (Vset.remove d O)) by
    (deadcode iE5E5; eqobs_in iE5E5).
  unfold Pr at 1;  rewrite <-(equiv_deno H0 (charfun ((@GoodToss k) [&&] negP (@X_queried k))) _);
    [clear H0 | intros m1 m2 H; unfold GoodToss, X_queried; rewrite_req_mem_l H | apply req_mem_refl ]. 
  rewrite <-(@BlindGuess _ m), <-Pr_G6G7_S2_nXQ, proj1_BP; trivial.
 Qed.

    
 Lemma Pr_G6_GT_X_queried : forall k (m:Mem.t k),
   2 */ (Uabs_diff (Pr E0 G0 m (@Success k)) [1/2]) *  p k * ([1-] p k) ^ qEX_poly k <=
   Pr E6 G6 m ((@GoodToss k) [&&] (@X_queried k)).
 Proof.
  intros.
  rewrite <-Umult_assoc.
  match goal with |-  2 */ (Uabs_diff ?x [1/2]) * ?y <= ?z => 
    set (X:=x); set (Y:=y); set (Z:=z) end.
  unfold Uabs_diff; apply (Ule_total X [1/2]); trivial; intro H'; rewrite (Uminus_le_zero _ _ H'); 
    [ rewrite Uplus_zero_left | rewrite Uplus_zero_right ]; clear H'.
    (* case [X <= 1/2] *)
    transitivity (2 */ ([1/2] * Z)).
      apply Nmult_le_compat_right; rewrite Uminus_distr_left.
      apply Uplus_le_perm_left.
      apply Uminus_le_perm_left; [apply Umult_le_compat_right | ]; unfold X, Y, Z.
        rewrite <-(Pr_G1_GoodToss m), Pr_G1_G2_GT, Pr_G2_G3_GT, Pr_G3_G4_GT, Pr_G4_G5_GT, Pr_G5_G6_GT.
        rewrite proj1_BP; trivial.
        rewrite Pr_G0_G1_SA, (Umult_assoc (Pr _ _ _ _)), <-Pr_G1_S2, <-(Pr_G1_GoodToss m).
        rewrite Pr_G1_G2_GT, Pr_G2_G3_GT, Pr_G3_G4_GT, Pr_G4_G5_GT, Pr_G5_G6_GT.
        rewrite Pr_G1_G2_S2, Pr_G2_G3_S2, Pr_G3_G4_S2, Pr_G4_G5_S2, Pr_G5_G6_S2.
        apply Pr_G6_S2_lower.
    rewrite Nmult_2, Umult_sym, <-Udistr_plus_left, Unth_one_plus, Umult_one_right; 
      [| rewrite Unth_one at 1]; trivial.
    (* case [1/2 <= X] *) 
    transitivity (2 */ ([1/2] * Z)).
      apply Nmult_le_compat_right; rewrite Uminus_distr_left.
      apply Uplus_le_perm_left; unfold X, Y, Z.
      rewrite Pr_G0_G1_SA, Umult_assoc, <-Pr_G1_S2, <-(Pr_G1_GoodToss m).
      rewrite Pr_G1_G2_GT, Pr_G2_G3_GT, Pr_G3_G4_GT, Pr_G4_G5_GT, Pr_G5_G6_GT.
      rewrite Pr_G1_G2_S2, Pr_G2_G3_S2, Pr_G3_G4_S2, Pr_G4_G5_S2, Pr_G5_G6_S2.
      apply Pr_G6_S2_upper.
    rewrite Nmult_2, Umult_sym, <-Udistr_plus_left, Unth_one_plus, Umult_one_right; 
      [| rewrite Unth_one at 1]; trivial.
 Qed.
 

 (** G7 --> G8 *)

 (* 
    CHANGES IN THE GAME:
    1) REDUCTION: we build an adversary against the BDH
    assumption using the adversary against the IBE scheme.
    2) Variables [d] and [J1] become deadcode and are eliminated.
  
    RESULTS REGARDING PROBABILITY OF EVENTS:
    1) Probability of [X_queried] is preserved
 *)
 
 Definition B_body :=
  [
   T <- Nil _;
   while Elen T <! qH1 do [ t <$- {0,1}_p; T <- T |++| (t |::| Nil _)  ];
   L1 <- Nil _; L2 <- Nil _; L3 <- Nil _; V <- Nil _;
   R <$- {0,1}^k;
   P <- P'; Ppub <- aP';
   (* [P] and [Ppub] must be set 'cause the adversary has (RO) access
      to them (they are part of the public data of the scheme).
      Moreover, they are needed for the simulation of oracles *)
   bP'' <- bP';
   (* we need this variables to be global because it is needed for
      the simulation oracle [H1] *)
   r1 <c- A1 with {};
   id_A <- Esnd r1;
   Q_A <c- H1 with {id_A};
   v' <- V[{id_A}] ^-1;
   y <- ( v' |.| cP' | R);
   d_A <c- A2 with {y};
   i <$- [0.. Elen L2]
  ].


 Definition G8 := BDH a' b' c' P w 8.

 Definition H1_8 :=
  [
   If !(id_H in_dom L1) _then
   [
    v <$- [1..q-1];
    V <- (id_H | v) |::| V;
    If Enth {Elen L1, T}
    then [ L1 <- (id_H | v |.| bP'') |::| L1 ]
    else [ L1 <- (id_H | v |.| P) |::| L1 ]
   ]
  ].

 Definition Ex_8 :=
   [
   Q_ex <c- H1 with {id_ex};
   d_ex <- V[{id_ex}] |.| Ppub;
   If id_ex not_in L3 _then [ L3 <- id_ex |::| L3 ]
  ].

 Definition E8' := make_env H1_8 H2_0 Ex_8.
 Definition E8  := add_decl E8' B B_params (refl_equal _) B_body B_re.

 Definition I8 := EP2 (Ppub =?= a |.| P) /-\ EP2 (bP'' =?= b |.| P).

 Lemma dep_I8 : depend_only_rel I8
  Vset.empty {{a, Ppub, b, P, bP''}}.
 Proof.
  change {{a, Ppub, b, P, bP''}} with (Vset.union {{a,P,Ppub}} {{b,P,bP''}}).
  change Vset.empty with (Vset.union Vset.empty Vset.empty).
  repeat apply depend_only_andR; apply depend_only_EP2.
 Qed.

 Lemma dec_I8 : decMR I8.
 Proof.
  unfold I8; auto.
 Qed.

 Definition iE7E8_I8_empty : eq_inv_info I8 E7 E8.
  refine (@empty_inv_info I8 _ _ dep_I8 _ dec_I8 _ _).
  vm_compute; trivial.
 Defined.


 Lemma H1_E7E8_I8 : EqObsInv I8
  {{id_H, L1, T, V, P, b}}
  E7 H1_2
  E8 H1_8
  {{id_H, L1, T, V, P, b}}.
 Proof.
  ep_eq_r bP'' (b |.| P);
  [ intros k m1 m2 [H1 [_ H2] ]; rewrite expr_eval_eq; assumption | ].
  deadcode iE7E8_I8_empty; eqobs_in iE7E8_I8_empty.
 Qed.

 Lemma EX_E7E8_I8 : EqObsInv I8
  {{id_ex, L1, T, V, P, b, L3, a}}
  E7 Ex_5
  E8 Ex_8
  {{L1, T, V, P, b, L3, a,  d_ex}}.
 Proof.
  set (iH1 := add_info H1 Vset.empty {{J1}} iE7E8_I8_empty H1_E7E8_I8).
  ep_eq_r iH1 Ppub (a |.| P);
  [ intros k m1 m2 [H1 [H2 _] ]; rewrite expr_eval_eq; assumption | ].
  eqobs_ctxt iH1; union_mod iH1.
  eapply equiv_strengthen; [ | apply equiv_assign ].
  intros k m1 m2 [H1 H2]; unfold upd_para.
  match goal with 
   |- req_mem_rel ?X _ _ (Mem.upd _ _ ?v1) (Mem.upd _ _ ?v2) =>
   change X with {{d_ex}}; replace v1 with v2
  end.
  split.
  apply req_mem_update; trivial.
  apply dep_I8 with (3:=H2); [ | apply req_mem_upd_notin_r; [| discriminate ] ]; trivial.
  simpl; unfold O.eval_op; simpl.
  rewrite G1.pow_pow, mult_comm, (H1 _ P), (H1 _ a), (H1 _ id_ex), (H1 _ V); trivial.
 Qed.

 Lemma EqAD_78 : Eq_adv_decl PrOrcl PrPriv E7 E8.
 Proof.
  unfold Eq_adv_decl, E8, E8', E7, E5, make_env, proc_params, proc_body, proc_res; intros.
  generalize 
   (BProc.eqb_spec (BProc.mkP A1) (BProc.mkP f)),
   (BProc.eqb_spec (BProc.mkP A2) (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A1) (BProc.mkP f));
  destruct (BProc.eqb (BProc.mkP A2) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  inversion H1; simpl; auto.
  inversion H2; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto; intro Heq;
   try (apply H; rewrite <- Heq; vm_compute; trivial; fail);
    apply H0; rewrite <- Heq; vm_compute; trivial.
 Qed.

 Lemma EqAD_8'8 : Eq_adv_decl PrOrcl PrPriv E8' E8.
 Proof.
  unfold Eq_adv_decl, E8, E8', make_env, proc_params, proc_body, proc_res; intros.
  generalize (BProc.eqb_spec (BProc.mkP A1) (BProc.mkP f)),
             (BProc.eqb_spec (BProc.mkP A2) (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A1) (BProc.mkP f));
  destruct (BProc.eqb (BProc.mkP A2) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  inversion H1; simpl; auto.
  inversion H2; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto; intro Heq;
   try (apply H; rewrite <- Heq; vm_compute; trivial; fail);
    apply H0; rewrite <- Heq; vm_compute; trivial.
 Qed.

 Lemma EqAD_88 : Eq_adv_decl PrOrcl PrPriv E8 E8.
 Proof.
  unfold Eq_adv_decl, E8, E8', make_env, proc_params, proc_body, proc_res; intros.
  generalize (BProc.eqb_spec (BProc.mkP A1) (BProc.mkP f)),
             (BProc.eqb_spec (BProc.mkP A2) (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A1) (BProc.mkP f));
  destruct (BProc.eqb (BProc.mkP A2) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  inversion H1; simpl; auto.
  inversion H2; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto; intro Heq;
   try (apply H; rewrite <- Heq; vm_compute; trivial; fail);
    apply H0; rewrite <- Heq; vm_compute; trivial.
 Qed.

 Lemma A1_wf_8 : WFAdv PrOrcl PrPriv Gadv Gcomm E8 A1.
 Proof.
  unfold E8.
  intros; apply WFAdv_trans with (5:=A1_wf_E H1_8 H2_0 Ex_8).
  unfold Eq_orcl_params; intros.
  unfold PrOrcl in H.
  rewrite PrSetP.add_spec in H; destruct H.
  inversion H; simpl.
  vm_compute; trivial.
  rewrite PrSetP.add_spec in H; destruct H.
  inversion H; simpl.
  vm_compute; trivial.
  apply PrSet.singleton_complete in H; inversion H; simpl.
  vm_compute; trivial.
  apply EqAD_8'8.
  discriminate.
  discriminate.
 Qed.

 Lemma A2_wf_8 : WFAdv PrOrcl PrPriv Gadv Gcomm E8 A2.
 Proof.
  intros; apply WFAdv_trans with (5:=A2_wf_E H1_8 H2_0 Ex_8).
  unfold Eq_orcl_params; intros.
  unfold PrOrcl in H.
  rewrite PrSetP.add_spec in H; destruct H.
  inversion H; simpl.
  vm_compute; trivial.
  rewrite PrSetP.add_spec in H; destruct H.
  inversion H; simpl.
  vm_compute; trivial.
  apply PrSet.singleton_complete in H; inversion H; simpl.
  vm_compute; trivial.
  apply EqAD_8'8.
  discriminate.
  discriminate.
 Qed.

 Definition iE7E8_I8 :=
  let iH1 := add_info H1 Vset.empty Vset.empty iE7E8_I8_empty H1_E7E8_I8 in
  let iH2 := add_refl_info H2 iH1 in
  let iEx := add_info Ex  Vset.empty Vset.empty iH2  EX_E7E8_I8 in
  let iA1 := add_adv_info_lossless EqAD_78 (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless EqAD_78 (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Definition iE8E8 :=
  let iH1 := add_refl_info_O H1 (Vset.add bP'' (Vset.add P (Vset.add T (Vset.add V {{L1, id_H}})))) Vset.empty Vset.empty (empty_info E8 E8) in
  let iH2 := add_refl_info_O H2 (Vset.add L2 (fv_expr H2_re)) Vset.empty Vset.empty iH1 in
  let iEx := add_refl_info_O Ex (Vset.add L3 (Vset.add Ppub (Vset.add bP'' (Vset.add P (Vset.add L1 (Vset.add V (Vset.add T (fv_expr Ex_re)))))))) Vset.empty Vset.empty iH2  in
  let iA1 := add_adv_info_lossless EqAD_88 A1_wf_8 (@A1_lossless _) (@A1_lossless _) iEx in
  let iA2 := add_adv_info_lossless EqAD_88 A2_wf_8 (@A2_lossless _) (@A2_lossless _) iA1 in
  let iB  := add_refl_info_O B (fv_expr B_re) Vset.empty Vset.empty iA2 in iB.


 Lemma EqObs_G7_G8 : EqObs 
  I
  E7 (G7 ++ [ret <- e(P,P) |^| (a *! b *! c) in_dom L2])
  E8 (G8 ++ [ret <- e(P,P) |^| (a' *! b' *! c') in_dom L2])
  (fv_expr ret).
 Proof.
  apply EqObs_trans with E8
   ((firstn 13 G7) ++ [bP'' <- b |.| P] ++ (skipn 13 G7) ++ [ret <- e(P,P) |^| (a *! b *! c) in_dom L2]).
    unfold G7; simpl.
    eqobs_tl iE7E8_I8.
    eqobs_hd_n 12%nat.
    unfold I8; eqobsrel_tail; unfold EP2; simpl; unfold O.eval_op; simpl.
     intros k m1 m2 H; split; apply G1.eqb_refl.

    unfold G8, BDH; simpl.
    inline_r iE8E8 B.
    alloc_r iE8E8 a' a; alloc_r iE8E8 b' b; alloc_r iE8E8 c' c; ep iE8E8.
    deadcode iE8E8.
    eqobs_tl iE8E8.
    match goal with 
     |- EqObs _ _ ?c1 _ ?c2 _ =>
      rewrite <-(firstn_skipn 15 c1), <-(firstn_skipn 15 c2);
      apply equiv_app with (kreq_mem {{P, a, b, c, Ppub, g_a, L1, V, T, bP'', L2, L3, r1, R}}); simpl
    end; [swap iE8E8; eqobs_in iE8E8 | ].
    match goal with |- equiv ?I' _ _ _ _ ?O' =>
      apply equiv_trans with
        (P1:=I') (Q1:=O') (Q2:=O') (E2:=E8)
        (c2:= [ y <- ((((V [{Esnd (r1)}]) ^-1) *! c) |.| P | R); d_A <c- A2 with {y} ])
    end.
     auto.
     intros k m1 _ _; apply req_mem_refl. 
     apply req_mem_trans.
     ep_eq_l ((((V [{Esnd (r1)}]) ^-1) *! c mod_q) |.| P)
       ((((V [{Esnd (r1)}]) ^-1) *! c) |.| P).
     intros k m1 m2 H; expr_simpl.
     pattern Par.q at 2; rewrite <-G1_order.
     symmetry; apply G1.pow_mod.
     ep iE8E8; deadcode iE8E8; eqobs_in iE8E8.
    match goal with |- equiv ?I' _ _ _ _ ?O' =>
      apply equiv_trans with
        (P1:=I') (Q1:=O') (Q2:=O') (E2:=E8)
        (c2:= [ y <- ((c *! ((V [{Esnd (r1)}]) ^-1)) |.| P | R); d_A <c- A2 with {y} ])
    end;
    [ auto | intros k m1 _ _; apply req_mem_refl | apply req_mem_trans |
       | ep iE8E8; deadcode iE8E8; eqobs_in iE8E8 ].
    eqobs_tl iE8E8.
    eapply equiv_strengthen; [ | apply equiv_assign]; intros k m1 m2 H1; unfold upd_para.
    match goal with |- kreq_mem ?X (_ {!_ <-- ?v1!}) (_ {!_ <-- ?v2!}) =>
      change X with {{y,L3,L2,bP'',T,V,L1,g_a,Ppub,c,b,a,P}}; replace v1 with v2
    end.
    apply req_mem_update; apply req_mem_weaken with (2:=H1); vm_compute; trivial.
    simpl; unfold O.eval_op; simpl.
    rewrite mult_comm, (H1 _ P), (H1 _ c), (H1 _ r1), (H1 _ V), (H1 _ R); trivial.
 Qed.

 Lemma Pr_G7_G8_XQ : forall k (m:Mem.t k),
  Pr E7 G7 m (@X_queried k)  ==
  Pr E8 G8 m (EP k (e(P,P) |^| (a'*!b'*!c') in_dom L2)).
 Proof.
  intros; unfold X_queried; rewrite (Pr_d_eq _ _ _ ret).
  rewrite (EqObs_Pr _ EqObs_G7_G8).
  symmetry; apply Pr_d_eq.
 Qed.


 Definition iE8'E8 :=
  let iH1 := add_refl_info_O H1 (Vset.add bP'' (Vset.add P (Vset.add T (Vset.add V {{L1, id_H}})))) Vset.empty Vset.empty (empty_info E8' E8) in
  let iH2 := add_refl_info_O H2 (Vset.add L2 (fv_expr H2_re)) Vset.empty Vset.empty iH1 in
  let iEx := add_refl_info_O Ex (
    Vset.add L3 (Vset.add Ppub (Vset.add bP'' (Vset.add P (Vset.add L1 (Vset.add V (Vset.add T (fv_expr Ex_re)))))))) Vset.empty Vset.empty iH2 in
  let iA1 := add_adv_info_lossless EqAD_8'8 (A1_wf_E _ _ _) (@A1_lossless _) (@A1_lossless _) iEx in 
  let iA2 := add_adv_info_lossless EqAD_8'8 (A2_wf_E _ _ _) (@A2_lossless _) (@A2_lossless _) iA1 in iA2.

 Lemma Pr_G7_XQ_BQ : forall k (m:Mem.t k),
    Pr E8 G8 m (EP k (e(P,P) |^| (a'*!b'*!c') in_dom L2)) ==
    Pr E8 G8 m (EP k (Elen L2 <! (qH2_poly k)) [&&] EP k (e(P,P) |^| (a' *! b' *! c') in_dom L2)).
 Proof.
  intros.
  set (G8' := [ L2 <- Nil _;
    P <$- G1o; a' <$- [1..q-1]; b' <$- [1..q-1]; c' <$- [1..q-1];
    P' <- P; aP' <- a' |.| P; bP' <- b' |.| P;  cP' <- c' |.| P
      ] ++ (filter (fun i => negb (I.eqb i (L2 <- Nil _))) B_body)).
  assert (H0 : EqObs I E8' G8' E8 G8 {{P,a',b',c',L2}}) by
   (inline_r iE8'E8 B; deadcode iE8'E8; swap iE8'E8; eqobs_in iE8'E8).
  unfold Pr; rewrite <-(equiv_deno H0 (charfun (EP k (e(P,P)|^|(a'*!b'*!c') in_dom L2))) _);
       [ | intros m1 m2 H; rewrite_req_mem_l H |  apply req_mem_refl ].
  eapply Oeq_trans; [ apply mu_range_strenghten with (P:= EP k (Elen L2 <! qH2)) | ].
    change G8' with ( (L2 <- Nil _)::(skipn 1 (firstn 18 G8')) ++  [r1 <c- A1 with{}] ++
      [ id_A <- Esnd (r1); Q_A <c- H1 with {id_A}; v' <- (V [{id_A}]) ^-1;  y <- (v' |.| cP' | R) ] ++
      [ d_A <c- A2 with {y} ] ++ [i <$- [0..Elen L2] ]).
    eapply A_hyp'.    
    apply (modify_correct (refl1_info iE8'E8) _ Vset.empty); compute; reflexivity.
    apply (modify_correct (refl1_info iE8'E8) _ Vset.empty); compute; reflexivity.
    apply (modify_correct (refl1_info iE8'E8) _ Vset.empty); compute; reflexivity.
    apply (modify_correct (refl1_info iE8'E8) _ Vset.empty); compute; reflexivity.
    apply (modify_correct (refl1_info iE8'E8) _ Vset.empty); compute; reflexivity.
    vm_compute; discriminate.
    vm_compute; discriminate.
    vm_compute; discriminate.
    vm_compute; discriminate.
    vm_compute; discriminate.
    apply equiv_deno with (1:=H0); [ | apply req_mem_refl ].
    intros m1 m2 H; unfold charfun, restr, andP, EP.  
    repeat (rewrite depend_only_fv_expr_subset with (2:=H); 
     [ | vm_compute]; trivial).
 Qed.

 
 Lemma Pr_G8 : forall k (m:Mem.t k), 
  ([1/]1+pred(qH2_poly k)) * Pr E8 G8 m 
  (EP k (Elen L2 <! qH2_poly k) [&&] EP k (e(P,P)|^|(a' *! b' *! c') in_dom L2)) <=
  Pr E8 G8 m (EP k (w =?= e(P,P) |^| (a' *! b' *! c'))).
 Proof.
  set (G8' := CoinTosses ++ 
   [
     L1 <- Nil _; L2 <- Nil _; L3 <- Nil _; V <- Nil _; 
     P <$- G1o;
     a' <$- [1..q-1];
     b' <$- [1..q-1];
     c' <$- [1..q-1];
     R <$- {0,1}^k;
     Ppub <- a' |.| P; 
     bP'' <- b' |.| P; 
     r1 <c- A1 with{};
     id_A <- Esnd (r1);
     Q_A <c- H1 with {id_A};
     v' <- (V [{id_A}]) ^-1;
     y <- (v' |.| (c' |.| P) | R);
     d_A <c- A2 with {y} 
   ]).
  intros; unfold G8, BDH, X_queried; simpl.
  transitivity  ([1/]1+pred (qH2_poly k) * 
   Pr E8 G8' m 
   (EP k (Elen L2 <! qH2_poly k) [&&] EP k (e(P,P)|^|(a' *! b' *! c') in_dom L2))).
  Usimpl.
  apply equiv_deno_le with (kreq_mem I) (kreq_mem {{L2, a',b',c',P}}).
  inline iE8E8 B; ep iE8E8; deadcode iE8E8; swap iE8E8; eqobs_in iE8E8.
  intros m1 m2 H; unfold charfun, restr, andP, EP;
   repeat (rewrite depend_only_fv_expr_subset with (2:=H); 
    [ | vm_compute]; trivial).
  apply req_mem_refl.
  rewrite (@Pr_random_dom G8' _ _ (e(P,P)|^|(a' *! b' *! c')) qH2_poly i w L2 E8).
  apply Oeq_le; apply EqObs_Pr with I.
  inline iE8E8 B; ep iE8E8; deadcode iE8E8; swap iE8E8; eqobs_in iE8E8.
  discriminate.
  discriminate.
 Qed.

 Theorem exact_security : forall k (m:Mem.t k),
  [1/]1+pred(qH2_poly k) * (2 */ A_advantage m * p k * ([1-]p k) ^ qEX_poly k) <=  
  BDH_advantage a' b' c' P w 8 E8 m.
 Proof.
  unfold A_advantage, BDH_advantage; intros.
  rewrite <-Pr_G8; Usimpl.
  rewrite <-Pr_G7_XQ_BQ, <-Pr_G7_G8_XQ, <-Pr_G6G7_XQ.
  rewrite Pr_G6_GT_X_queried, proj2_BP; trivial.
 Qed.
 
End ADVERSARY_AND_PROOF.
