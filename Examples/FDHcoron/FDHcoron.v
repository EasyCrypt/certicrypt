(** * FDHcoron.v: Exact security of the FDH -- improved bound *)

Set Implicit Arguments.

Require Import FDHcsem.


(** [f] is a one-way permutation *)
Section ONE_WAYNESS.

 Variables x y : Var.var (T.User group).
 Variable Bname : positive.
 
 Notation B := (Proc.mkP Bname (T.User group :: nil) (T.User group)).

 Definition Gf :=
  [
   y <$- G_k;
   x <c- B with {y}
  ].

 Axiom f_oneway : forall (m:forall k, Mem.t k) E,
  x <> y ->
  Var.is_local x ->
  Var.is_local y ->
  lossless E (proc_body E B) ->
  PPT_proc E B ->
  negligible (fun k => Pr E Gf (m k) (EP k (x =?= finv {y}))).
 
End ONE_WAYNESS.


(** Applying [f] to a uniformly distributed group element results in a uniformly
   distributed group element *)
Section PERMUTATION_FACTS.

 Variables E1 E2 : env.
 Variables x y : Var.var (T.User group).

 Lemma f_rand : 
  EqObs Vset.empty 
  E1 [ y <$- G_k ]
  E2 [ x <$- G_k; y <- f {x} ]
  (Vset.singleton y).
 Proof.
  apply equiv_cons with (fun k (m1 m2:Mem.t k) => ap_finv (m1 y) = m2 x).
  eapply equiv_strengthen;
   [ | apply equiv_random_permut
       with (f:=fun k (m1 m2:Mem.t k) (v:T.interp k (T.User group)) => ap_f v)].
  intros; split.
  apply PermutP_NoDup with (@ap_finv k); intros.
   apply group_support_NoDup; trivial.
   apply group_support_NoDup; trivial.
   apply finv_spec. 
   apply f_spec.
   apply group_support_full.
   apply group_support_full.
   intros; repeat rewrite Mem.get_upd_same; apply f_spec.
  eapply equiv_strengthen; [ | apply equiv_assign_r ].
  unfold upd2; intros k m1 m2 H; simpl; unfold O.eval_op; simpl.
  rewrite <- H, finv_spec; intros ? ? Hin.
  Vset_mem_inversion Hin; subst; rewrite Mem.get_upd_same; trivial.
 Qed.

 Lemma mul_f_rand : forall z,
  x <> z ->
  EqObs Vset.empty 
  E1 [y <$- G_k] 
  E2 [x <$- G_k; y <- z |x| f {x} ] 
  (Vset.singleton y).
 Proof.
  intros z Hneq.
  apply equiv_cons with 
   (fun k (m1 m2:Mem.t k) => 
    ap_finv (CG.mul (m1 y) (CG.inv (m2 z))) = m2 x).
  eapply equiv_strengthen;
   [ | apply equiv_random_permut with
       (f:=fun k (m1 m2:Mem.t k) v => CG.mul (ap_f v) (m2 z))].
  simpl; red; intros; split.
  apply PermutP_NoDup with (fun v => ap_finv (CG.mul v (CG.inv (m2 z)))); intros.
   apply group_support_NoDup; trivial.
   apply group_support_NoDup; trivial.
   rewrite finv_spec, <- CG.mul_assoc, CG.mul_inv_l, CGP.mul_e_r; trivial.
   rewrite <- CG.mul_assoc, CGP.mul_inv_r, CGP.mul_e_r; apply f_spec.  
   apply group_support_full.
   apply group_support_full.
   intros; repeat rewrite Mem.get_upd_same; rewrite Mem.get_upd_diff; trivial.
   rewrite <- CG.mul_assoc, CGP.mul_inv_r, CGP.mul_e_r; apply f_spec.   
   intro H1; inversion H1; elim Hneq.
   apply (T.inj_pair2 H3).
  eapply equiv_strengthen; [ | apply equiv_assign_r ].
  unfold upd2; intros k m1 m2 H; simpl; unfold O.eval_op; simpl.
  rewrite <- H, finv_spec; intros ? ? Hin.
  Vset_mem_inversion Hin; subst; rewrite Mem.get_upd_same.
  rewrite CGP.mul_comm, <- CG.mul_assoc, CG.mul_inv_l, CGP.mul_e_r; trivial.
 Qed.

End PERMUTATION_FACTS.


(* TODO: Move this somewhere else *)
Lemma CG_eqb_refl : forall k (x:CG.t k), CG.eqb x x.
Proof.
 intros k x; generalize (CG.eqb_spec x x).
 case (CG.eqb x x); [ | intro H; elim H]; trivial.
Qed.

Lemma in_dom_In : forall A B 
 (x:E.expr A) (L:Var.var (T.List (T.Pair A B))) k (m:Mem.t k),
 E.eval_expr (x in_dom L) m ->
 In (E.eval_expr x m, E.eval_expr (L[{x}]) m) (m L). 
Proof.
 simpl; unfold O.eval_op; simpl; intros.
 rewrite is_true_existsb in H.
 destruct H as [(x',y) [Hin Heq] ].
 induction (m L) as [ | xy L0 ].
 inversion Hin.
 simpl in *; destruct xy as (x0, y0); destruct Hin.
 injection H; intros; subst; clear H.
 rewrite is_true_Ti_eqb in Heq; subst.
 unfold O.assoc; simpl; rewrite Ti_eqb_refl; auto.
 rewrite is_true_Ti_eqb in Heq; subst.
 unfold O.assoc; simpl.
 case_eq (T.i_eqb k A (E.eval_expr x m) x0); intro H0.
 left; simpl.
 fold (is_true (T.i_eqb k A (E.eval_expr x m) x0)) in H0.
 rewrite is_true_Ti_eqb in H0; subst; trivial.
 auto.
Qed.

Lemma impb_implb : forall b1 b2, impb b1 b2 = implb b1 b2.
Proof.
 intros b1 b2; case b1; case b2; trivial.
Qed.

Open Scope U_scope.

Lemma range_strengthen : forall A (d:Distr A) (P Q:A -o> boolO),
 mu d (fone _) == 1 ->
 range P d -> 
 range Q d ->
 range (P [&&] Q) d.
Proof.
 intros; apply mu_range.
 rewrite <- (mu_range_strenghten _ Q H0).
 transitivity (mu d (fone _)); [ | trivial].
 apply range_mu; trivial. 
Qed.

Lemma charfun_and_elim : forall (A : Type) (P Q : A -o> boolO) (a:A),
 charfun (P[&&]Q) a == charfun P a * charfun Q a.
Proof.
 intros.
 transitivity (Fmult (charfun P) (charfun Q) a).
 apply ford_eq_elim.
 refine (charfun_and _ _).
 trivial.
Qed.

Lemma length_lfalse : forall n, length (lfalse n) = n.
Proof.
 induction n; simpl; intros; trivial.
 rewrite IHn; trivial.
Qed.

Lemma finite_lfalse : forall (x:Var.var T.Bool) k (m:Mem.t k) f N n,
 n <= N ->
 finite_sum (fun a : bool => [1/]1+N * f (m {!x <-- a!})) (lfalse n) == 
 (n */ [1/]1+N) * f (m{!x <-- false!}).
Proof.
 induction n; simpl; intros.
 auto.
 match goal with 
  |- ?X == ?Y => 
   change Y with (((Datatypes.S n) */ [1/]1+N) * f (m{!x <-- false!}))
 end.
 rewrite Nmult_S, Udistr_plus_right.
 apply Uplus_eq_compat; trivial.
 apply IHn; auto with arith.
 apply Uinv_le_perm_right.
 apply Nmult_le_n_Unth; auto with arith.
Qed.

Lemma deno_sample_p : forall (x:Var.var T.Bool) k (m:Mem.t k) E f,
 mu ([[ [x <$-{0,1}_p] ]] E m) f ==
 [1/]1+(peval qS_poly k)      * (f (m{!x <-- true!})) + 
 ([1-] [1/]1+peval qS_poly k) * (f (m{!x <-- false!})). 
Proof.
 intros; rewrite deno_random_elim.
 change 
  (mu (sum_support (T.default k T.Bool) (E.eval_support {0,1}_p m))
   (fun v => f (m {!x <-- v!}))) 
  with 
   (sum_dom (T.default k T.Bool) (E.eval_support {0,1}_p m)
    (fun v => f (m {!x <-- v!}))).
 rewrite sum_dom_finite; simpl; rewrite length_lfalse.
 apply Uplus_eq_compat; trivial.
 rewrite <- Nmult_n_Unth.
 apply finite_lfalse; auto with arith.
Qed.

Import Datatypes.

Lemma nth_cons : forall l b n i,
 leb (S n) i ->
 nth (i - S n) l false = nth (i - n) (b :: l) false.
Proof.
 intros; change (b :: l) with (b :: nil ++ l).
 rewrite (app_nth2 (b::nil) l); [ | apply leb_complete in H; simpl; omega].
 simpl.
 replace (i- S n)%nat with (i - n - 1)%nat by omega.
 trivial.
Qed.
(*****************************************************************************) 



(** ** Notations *)
Open Scope positive_scope.


(** ** Global variables *)

(** *** Global variables shared by the adversary, the oracles and the game *)
Definition Gcomm := Vset.empty.

(** *** Global variables shared (and only visible) by the oracles and the game *)
Notation LH  := (Var.Gvar (T.List (T.Pair Msg (T.User group))) 1).
Notation LS  := (Var.Gvar (T.List Msg) 2).
Notation T   := (Var.Gvar (T.List T.Bool) 3).
Notation I   := (Var.Gvar (T.List (T.Pair Msg T.Nat)) 4). 
Notation S   := (Var.Gvar (T.List (T.Pair Msg (T.User group))) 5). 
Notation Y   := (Var.Gvar (T.User group) 6).
Notation bad := (Var.Gvar T.Bool 7).

(** *** Global variables for the adversary (there are none) *)
Definition Gadv := Vset.empty.


(** ** Local variables *)

(** *** Hash oracle *)
Notation mH    := (Var.Lvar Msg 1). 
Notation rH    := (Var.Lvar (T.User group) 2).
Notation s     := (Var.Lvar (T.User group) 3).

(** *** Signing oracle *)
Notation mS    := (Var.Lvar Msg 4).
Notation rS    := (Var.Lvar (T.User group) 5).
Notation sigma := (Var.Lvar (T.User group) 6).

(** *** Main *)
Notation rA   := (Var.Lvar (T.Pair Msg (T.User group)) 7).
Notation r    := (Var.Lvar (T.User group) 8).
Notation y    := (Var.Lvar (T.User group) 9).
Notation t    := (Var.Lvar T.Bool 10).
Notation x    := (Var.Lvar (T.User group) 11).

(** ** Procedures *)
Notation A    := (Proc.mkP 1 nil (T.Pair Msg (T.User group))).
Notation Hash := (Proc.mkP 2 (Msg :: nil) (T.User group)).
Notation Sign := (Proc.mkP 3 (Msg :: nil) (T.User group)). 
Notation B    := (Proc.mkP 4 (T.User group :: nil) (T.User group)).

Close Scope positive_scope.
Open Scope U_scope.


(** ** Adversary and proof *)
Section ADVERSARY_AND_PROOF.

 (** Hypotheses
   1) The advesary performs at most a polynomial number of queries [qH] and [qS]
      to the [Hash] and [Sign] oracles respectively.

   2) The adversary does not query [Sign] with the message whose signature 
      she forges.

   3) The adversary runs in PPT as long as its oracles do so
 *)

 (** *** Specification of the adversary *)
 Definition A_params : var_decl (Proc.targs A) := dnil _.

 Variable A_body : cmd.

 (** The adversary returns a (message, signature) pair *)
 Variable A_ret : E.expr (T.Pair Msg (T.User group)).

 (** Adversary's own procedures *)
 Variable adv_env : env.

 Definition Hash_params : var_decl (Proc.targs Hash) := dcons _ mH (dnil _).
 Definition Hash_ret : E.expr (T.User group) := LH[{mH}].

 Definition Sign_params : var_decl (Proc.targs Sign) := dcons _ mS (dnil _). 
 Definition Sign_ret : E.expr (T.User group) := sigma.

 (** Environment constructor *)
 Definition makeEnv (Hash_body Sign_body:cmd) :=
  add_decl
  (add_decl
   (add_decl adv_env 
    Hash Hash_params (refl_equal true) Hash_body Hash_ret)
   Sign Sign_params (refl_equal true) Sign_body Sign_ret)
  A A_params (refl_equal true) A_body A_ret.

 (** The set of oracles, [Hash] and [Sign] *)
 Definition PrOrcl := 
  PrSet.add (BProc.mkP Sign) (PrSet.singleton (BProc.mkP Hash)).

 (** Private procedures, not accessible to the adversary *)
 Definition PrPriv := PrSet.singleton (BProc.mkP B).

 (** Initial Game *)

 Definition G1 : cmd :=
  [
   LH <- Nil _;
   LS <- Nil _;
   rA <c- A with {};
   r <c- Hash with {Efst rA}
  ].

 Definition Hash1_body : cmd :=
  [
   If !(mH in_dom LH) _then
    [
      rH <$- G_k; 
      LH <- (mH | rH) |::| LH
    ]
  ].

 Definition Sign1_body :=
  [
   LS <- mS |::| LS;
   rS <c- Hash with {mS};
   sigma <- finv {rS}
  ].

 Definition E1 := makeEnv Hash1_body Sign1_body.

 Close Scope bool_scope.

 Definition S1 k := EP k ((r =?= f{Esnd rA}) && (Efst rA not_in LS)).

 (** The adversary is well-formed in [E1], i.e. it only reads or writes 
    variables it has access to, and only calls oracles and its own procedures. *)
 Hypothesis A_wf : WFAdv PrOrcl PrPriv Gadv Gcomm E1 A.

 (** The adversary makes at most [qH] and [qS] queries to the 
    hash and signing oracles respectively. *)
 Definition S0 k := 
  EP k (Elen LH <=! (qH +! 1))%nat [&&] 
  EP k (Elen LS <=! qS).

 Hypothesis Hyp : forall k (m:Mem.t k), range (@S0 k) ([[G1]] E1 m).

  (** The adversary runs in PPT as long as the hash and signing oracles do so *)
 Hypothesis A_PPT : forall E,
  Eq_adv_decl PrOrcl PrPriv E1 E ->
  (forall O, PrSet.mem O PrOrcl -> PPT_proc E (BProc.p_name O)) ->
  PPT_proc E A.

 (** The adversary is lossless as long as the hash and signing oracles are so *)
 Hypothesis A_lossless : forall E,   
  (forall O, PrSet.mem O PrOrcl -> lossless E (proc_body E (BProc.p_name O))) ->
  lossless E A_body.

 (** The adversary's own procedures are the same in environments constructed 
    with [makeEnv] *)    
 Lemma EqAD : forall H_body1 S_body1 H_body2 S_body2, 
  Eq_adv_decl PrOrcl PrPriv (makeEnv H_body1 S_body1) (makeEnv H_body2 S_body2).
 Proof.
  unfold Eq_adv_decl, makeEnv, proc_params, proc_body, proc_res; intros.
  generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
  case (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto;
   intros Heq; apply H; rewrite <- Heq; vm_compute; trivial.
 Qed.

 (** Oracles have the same declarations in environments constructed with 
    [makeEnv] *)
 Lemma EqOP : forall H_body1 S_body1 H_body2 S_body2, 
  Eq_orcl_params PrOrcl (makeEnv H_body1 S_body1) (makeEnv H_body2 S_body2).
 Proof.
  unfold Eq_orcl_params, makeEnv, PrOrcl; intros.
  rewrite PrSetP.add_spec in H; destruct H.
  inversion H; vm_compute; trivial.
  apply PrSet.singleton_complete in H; inversion H; vm_compute; trivial.
 Qed.

 (** The adversary is well-formed in any environment constructred with [makeEnv].
    This follows from the adversary being well-formed in [E1] *)
 Lemma A_wf_E : forall H_body S_body,
  WFAdv PrOrcl PrPriv Gadv Gcomm (makeEnv H_body S_body) A.
 Proof.
  intros; apply WFAdv_trans with (5:=A_wf).
  apply EqOP.
  apply EqAD.
  vm_compute; discriminate. 
  vm_compute; discriminate.
 Qed.


 (** BEGIN [Pr_S1_S2] *)

 (** The second game *)
 Definition G2 : cmd :=
  [
   T <- Nil _;
   while Elen T <! (qH +! 1%nat) do 
    [ 
     t <$- {0,1}_p; T <- t |::| T 
    ];
   I  <- Nil _;
   LH <- Nil _;
   LS <- Nil _;
   rA <c- A with {};
   r <c- Hash with {Efst rA}
  ].

 Definition Hash2_body : cmd :=
  [
   If !(mH in_dom LH) _then
   [
    rH <$- G_k; 
    I <- (mH | Elen LH) |::| I;
    LH <- (mH | rH) |::| LH
   ]
  ].

 Definition Sign2_body := Sign1_body.
 
 Definition E2 := makeEnv Hash2_body Sign2_body.

 Notation z := (Var.Lvar Msg 100). 

 Definition S2 k := 
  EP k ((r =?= f {Esnd rA}) && (Efst rA not_in LS)) [&&]
  EP k (Enth {I[{Efst rA}], T}) [&&]
  EP k (E.Eforall z (!(Enth {I[{z}], T})) LS).

 Definition iE1E2 :=
  add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _)
  (@A_lossless _)
  (@A_lossless _)
  (add_refl_info Sign
   (add_refl_info_O Hash
    (Vset.add mH (Vset.singleton LH))
    Vset.empty (Vset.singleton I)
    (empty_info E1 E2))).

 Lemma init_T_lossless : forall E,
  lossless E  
  [ T <- Nil _; while Elen T <! (qH +! 1%nat) do [t <$- {0,1}_p; T <- t |::| T] ].
 Proof.
  intro E.
  unfold lossless. 
  apply lossless_cons.
  apply lossless_assign.  
  assert (H:forall n k (m:Mem.t k), n = (peval qH_poly k + 1 - length (m T))%nat ->
   mu ([[ [while Elen T <! (qH +! 1%nat) do [t <$- {0,1}_p; T <- t |::| T] ] ]] E m)
    (fun _ => 1) == 1).
  induction n; intros; rewrite deno_while_elim, deno_cond_elim.
  assert (@E.eval_expr k T.Bool (Elen T <! (qH +! 1%nat)) m = false) 
   by (simpl; unfold O.eval_op; simpl; apply leb_correct_conv; omega).
  rewrite H0; apply lossless_nil.
  assert (@E.eval_expr k T.Bool (Elen T <! (qH +! 1%nat)) m = true) 
   by (simpl; unfold O.eval_op; simpl; apply leb_correct; omega).
  rewrite H0, deno_app_elim, deno_cons_elim, Mlet_simpl, deno_random_elim.
  transitivity
   (mu (sum_support (T.default k T.Bool) 
    (E.eval_support {0,1}_p m)) (fun _ => 1)).
  apply mu_stable_eq; refine (ford_eq_intro _); intro v.
  rewrite deno_assign_elim; apply IHn.
  rewrite Mem.get_upd_same; simpl; unfold O.eval_op; simpl.
  rewrite Mem.get_upd_diff; [ omega | discriminate ].
  apply sum_support_lossless. 
  unfold lossless; intros.
  apply (H _ k m (refl_equal _)).
 Qed.

 Lemma EqObs_G1_G2 : 
  EqObs Gadv 
  E1 G1 
  E2 G2 
  (Vset.add LS (Vset.add r (Vset.singleton rA))).
 Proof.
  unfold G1, G2.  
  deadcode iE1E2; eqobs_tl iE1E2.
  apply EqObs_lossless_Modify with (Vset.empty) (Vset.add t (Vset.singleton T)).
  apply lossless_nil.  
  apply init_T_lossless.
  apply Modify_nil.
  apply modify_correct with (refl2_info (empty_info E1 E2)) Vset.empty; trivial.
  trivial.
  trivial.
 Qed.

 (** The optimum value for probability [p] *)
 Definition p k : U := [1/]1+(peval qS_poly k).

 Definition init_T1 : cmd :=
  [ 
   while Elen T <! (qH +! 1%nat) do [ t <$-{0,1}_p; T <- t |::| T ]
  ].
 
 Definition S1f k (m:Mem.t k) (n i:nat) :=
  if leb n i then charfun (EP k (Enth {(i - n)%nat, T})) m 
   else [1/]1+(peval qS_poly k). 

 Fixpoint S2f k (m:Mem.t k) (n:nat) (l:list nat) {struct l} :=
  match l with
   | nil => 1
   | i::l' => 
    S2f m n l' *
    (if leb n i then charfun (EP k (!Enth {(i - n)%nat, T})) m 
     else [1-] [1/]1+(peval qS_poly k))
  end.

 Fixpoint S2' k (l:list nat) := 
  match l with
   | nil => EP k true
   | i::l' => EP k (!Enth {i, T}) [&&] S2' k l'
  end.

 Definition inv_while_diff n : mem_rel := fun k (m1 m2:Mem.t k) =>
  length (m1 T) = length (m2 T) /\
  (n >= (peval qH_poly k + 1 - (length (m1 T))))%nat /\
  nth (n - (peval qH_poly k + 1 - (length (m1 T))))%nat (m1 T) false = true /\
  forall j, 
   j <> (n - (peval qH_poly k + 1 - (length (m1 T))))%nat ->
   nth j (m1 T) false = nth j (m2 T) false .

 Lemma equiv_inv_w : forall n E, 
  equiv (req_mem_rel Vset.empty (inv_while_diff n))
  E [while Elen T <! (qH +! 1%nat) do [t <$- {0,1}_p; T <- t |::| T] ]
  E [while Elen T <! (qH +! 1%nat) do [t <$- {0,1}_p; T <- t |::| T] ]
  (req_mem_rel Vset.empty (inv_while_diff n /-\ ~- EP1 (Elen T <! (qH +! 1%nat)) )).
 Proof.
  intros; eapply equiv_weaken; [ | apply equiv_while].
  unfold req_mem_rel, andR; intuition.
  intros k m1 m2 [_ [H _] ].
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite H; trivial.
  eqobsrel_tail.
  unfold implMR, EP1, EP2, andR, inv_while_diff.
  simpl; unfold O.eval_op; simpl T.app_op.
  intros k m1 m2 [_ [ [H1 [H2 [H3b H3] ] ] H4] ] v _.
  mem_upd_simpl. 
  intros; repeat split.
  simpl; rewrite H1; trivial.
  simpl; rewrite H1; omega.

  destruct H4 as [H4 _]; apply leb_complete in H4.
  rewrite <- nth_cons; [ | apply leb_correct; simpl; rewrite H1; omega].
  simpl length.
  replace (n - Datatypes.S (peval qH_poly k + 1 - Datatypes.S (length (m1 T))))%nat 
   with (n - (peval qH_poly k + 1 - length (m1 T)))%nat.
  trivial.
  rewrite minus_Sn_m; omega.
  intros; destruct j; [ trivial | ].
  apply H3.
  destruct H4 as [Hle _]; apply leb_complete in Hle.
  clear -H2 H Hle.
  intro; subst; elim H; clear H; simpl length.
  change (Datatypes.S (length (m1 T))) with (1 + length (m1 T))%nat.
  omega.
 Qed.

 Close Scope nat_scope.

 Lemma Pr_nth_T1_l : forall E k n (m:Mem.t k) (i:nat) (l:list nat),
  ~In i l ->  
  (n = peval qH_poly k + 1 - length (m T))%nat ->
  S1f m n i * S2f m n l <= Pr E init_T1 m (EP k (Enth {i, T}) [&&] S2' l).
 Proof.
  clear; intros E k n m i l Hin Hn.
  transitivity
   (mu ([[init_T1]] E m) (Fmult (charfun (EP k (Enth {i, T}))) (charfun (S2' l)))).
  2:apply Oeq_le; unfold init_T1; apply mu_stable_eq; rewrite charfun_and; trivial.

  generalize l n i m Hin Hn; clear l n i m Hin Hn.
  unfold init_T1, Fmult.
  induction l.

  intros n i m _.
  generalize m i; clear m i; induction n; intros.

  unfold S1f, S2f; Usimpl.
  rewrite leb_correct; [ | omega].
  rewrite <- minus_n_O.
  unfold charfun, restr, EP, andP, fone.
  rewrite deno_while_elim, deno_cond_elim.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite leb_correct_conv; [ | omega].
  rewrite deno_nil_elim; auto.

  (* Inductive case for n *)
  unfold S2f, S2'; Usimpl.
  unfold S2f, S2' in IHn.
  assert (Heq:n = (peval qH_poly k + 1 - Datatypes.S (length (m T)))%nat)
   by (generalize Hn; clear; intro; omega).
  generalize (IHn (m{!t <-- true!}{!T <-- true :: m T!}) i).
  generalize (IHn (m{!t <-- false!}{!T <-- false :: m T!}) i).
  clear IHn; unfold S1f.
  mem_upd_simpl.
  simpl length; simpl plus.
  intros H1 H2; generalize (H1 Heq) (H2 Heq); repeat Usimpl; clear H1 H2.

  case_eq (leb (Datatypes.S n) i); intro.
  apply leb_complete in H.
  rewrite leb_correct; [ | omega].
  unfold charfun, restr, EP, andP, fone.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  mem_upd_simpl.
  rewrite <- nth_cons.
  rewrite <- nth_cons.

  case (nth (i - Datatypes.S n) (m T) false); [ | trivial].
  intros IH1 IH2.

  rewrite deno_while_elim, deno_cond_elim.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite leb_correct; [ | omega].
  rewrite deno_app_elim, deno_cons_elim, Mlet_simpl.
  rewrite deno_sample_p, deno_assign_elim, deno_assign_elim.

  generalize IH1 IH2; clear IH1 IH2.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  mem_upd_simpl. 
  set (A :=  
   mu
     (([[ [while Elen T <! (qH +! 1%nat) do [t <$- {0,1}_p; T <- t |::| T] ] ]]) E
        ((m {!t <-- true!}) {!T <-- true :: m T!}))
     (fun a : Mem.t k =>
      (if nth i (a T) false then 1 else 0) * 1)).
  set (B :=  
   mu
     (([[ [while Elen T <! (qH +! 1%nat) do [t <$- {0,1}_p; T <- t |::| T] ] ]]) E
        ((m {!t <-- false!}) {!T <-- false :: m T!}))
     (fun a : Mem.t k =>
      (if nth i (a T) false then 1 else 0) * 1)).
  intros.

  apply (Ule_total A B); [ trivial | | ]; intro Hle.

  rewrite <- Hle.
  rewrite <- Udistr_plus_right, Uinv_opp_right, Umult_one_left; trivial.
  rewrite Uinv_inv; trivial.

  rewrite <- Hle.
  rewrite <- Udistr_plus_right, Uinv_opp_right, Umult_one_left; trivial.
  rewrite Uinv_inv; trivial.

  apply leb_correct; omega.
  apply leb_correct; omega.
  
  apply leb_complete_conv in H.
  inversion H.
  rewrite leb_correct; [ | omega].
  unfold charfun, restr, EP, andP, fone.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite minus_diag.
  mem_upd_simpl.
  simpl (if nth 0 (true :: m T) false then 1 else 0).
  intros _ IH2.

  rewrite deno_while_elim, deno_cond_elim.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite leb_correct; [ | omega].
  rewrite deno_app_elim, deno_cons_elim, Mlet_simpl.
  rewrite deno_sample_p, deno_assign_elim, deno_assign_elim.
  generalize IH2; clear IH2.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  mem_upd_simpl.
  set (A :=  
   mu
     (([[ [while Elen T <! (qH +! 1%nat) do [t <$- {0,1}_p; T <- t |::| T] ] ]]) E
        ((m {!t <-- true!}) {!T <-- true :: m T!}))
     (fun a : Mem.t k =>
      (if nth n (a T) false then 1 else 0) * 1)).
  set (B :=  
   mu
     (([[ [while Elen T <! (qH +! 1%nat) do [t <$- {0,1}_p; T <- t |::| T] ] ]]) E
        ((m {!t <-- false!}) {!T <-- false :: m T!}))
     (fun a : Mem.t k =>
      (if nth n (a T) false then 1 else 0) * 1)).
  intros.
  rewrite <- IH2; Usimpl; trivial.

  clear m0 H0 H.
  rewrite leb_correct_conv; [ | omega].
  intros IH1 IH2.
  rewrite deno_while_elim, deno_cond_elim.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite leb_correct; [ | omega].
  rewrite deno_app_elim, deno_cons_elim, Mlet_simpl.
  rewrite deno_sample_p, deno_assign_elim, deno_assign_elim.
  generalize IH1 IH2; clear IH1 IH2.
  unfold charfun, restr, EP, andP, fone.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  mem_upd_simpl.
  set (A :=  
   mu
     (([[ [while Elen T <! (qH +! 1%nat) do [t <$- {0,1}_p; T <- t |::| T] ] ]]) E
        ((m {!t <-- true!}) {!T <-- true :: m T!}))
     (fun a : Mem.t k =>
      (if nth i (a T) false then 1 else 0) * 1)).
  set (B :=  
   mu
     (([[ [while Elen T <! (qH +! 1%nat) do [t <$- {0,1}_p; T <- t |::| T] ] ]]) E
        ((m {!t <-- false!}) {!T <-- false :: m T!}))
     (fun a : Mem.t k =>
      (if nth i (a T) false then 1 else 0) * 1)).
  intros.
  rewrite <- IH1, <- IH2.
  rewrite <- Udistr_plus_right, Uinv_opp_right.
  Usimpl; trivial.
  rewrite Uinv_inv; trivial.

  (* Inductive case for l *)
  intros.
  simpl S2f.
  rewrite Umult_assoc.
  simpl in Hin.
  assert (Hneq:a <> i) by auto.
  assert (Hnin:~In i l) by auto.
  clear Hin.
  rewrite (IHl n i m Hnin Hn); clear IHl.
  simpl S2'.
  unfold charfun, restr, EP, andP, andb, fone.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.

  generalize m Hneq Hnin Hn; clear.
  induction n; intros.
  rewrite leb_correct; [ | omega].
  rewrite <- minus_n_O.
  rewrite deno_while_elim, deno_cond_elim.
  rewrite deno_while_elim, deno_cond_elim.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite leb_correct_conv; [ | omega].
  repeat rewrite deno_nil_elim.
  rewrite <- Umult_assoc; Usimpl.
  case (nth a (m T) false); simpl; trivial.

  (* Inductive case for n *)
  assert (Heq:n = (peval qH_poly k + 1 - Datatypes.S (length (m T)))%nat)
   by (generalize Hn; clear; intro; omega).

  generalize (IHn (m{!t <-- true!}{!T <-- true :: m T!}) Hneq Hnin).
  generalize (IHn (m{!t <-- false!}{!T <-- false :: m T!}) Hneq Hnin).
  clear IHn.

  mem_upd_simpl.
  simpl length; simpl plus.
  intros H1 H2; generalize (H1 Heq) (H2 Heq); clear H1 H2.

  case_eq (leb (Datatypes.S n) a); intro H.

  (* S n <= a *)
  rewrite leb_correct; [ | apply leb_complete in H; omega].
  rewrite <- (nth_cons (m T) false _ _ H).
  rewrite <- (nth_cons (m T) true _ _  H).
  intros IH1 IH2.
  rewrite deno_while_elim, deno_cond_elim.
  rewrite deno_while_elim, deno_cond_elim.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite leb_correct; [ | omega].
  rewrite deno_app_elim, deno_cons_elim, Mlet_simpl.
  rewrite deno_sample_p, deno_assign_elim, deno_assign_elim.
  rewrite deno_app_elim, (@deno_cons_elim k E (t <$- {0,1}_p)), Mlet_simpl.
  rewrite deno_sample_p, deno_assign_elim, deno_assign_elim. 
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  mem_upd_simpl.
  generalize IH1 IH2; clear IH1 IH2.
  match goal with
  |- _ -> _ -> Ole _ (_ * ?X + _ * ?Y) => set (A := X); set (B := Y)
  end.
  intros IH1 IH2.
  rewrite <- IH1, <- IH2.  
  rewrite Udistr_plus_right, Umult_assoc, Umult_assoc; trivial.
  trivial.
  apply Uinv_mult_simpl; rewrite Uinv_inv; trivial.
  
  (* a < S n *)
  apply leb_complete_conv in H.
  inversion H.

  (* a = n *)
  rewrite leb_correct; [ | omega].
  rewrite minus_diag.
  simpl (if negb (nth 0 (true :: m T) false) then 1 else 0).
  simpl (if negb (nth 0 (false :: m T) false) then 1 else 0).
  repeat Usimpl.
  intros IH1 _.
  rewrite deno_while_elim, deno_cond_elim.
  rewrite deno_while_elim, deno_cond_elim.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite leb_correct; [ | omega].
  rewrite deno_app_elim, deno_cons_elim, Mlet_simpl.
  rewrite deno_sample_p, deno_assign_elim, deno_assign_elim.
  rewrite deno_app_elim, (@deno_cons_elim k E (t <$- {0,1}_p)), Mlet_simpl.
  rewrite deno_sample_p, deno_assign_elim, deno_assign_elim. 
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  mem_upd_simpl.
  generalize IH1; clear IH1.
  match goal with
  |- _ -> Ole ((_ * ?A + _ * ?B) * _) (_ * ?C + _ * ?D) => 
    set (At := A); set (Af := B); set (Bt := C); set (Bf := D)
  end.
  intros IH1.

  transitivity ([1-] [1/]1+peval qS_poly k * Bf); [ | trivial].
  assert (H2:Bf == Af).
   split; [ | trivial].
   apply mu_monotonic; intro m'.
   case (negb (nth n (m' T) false)); [ | Usimpl ]; trivial.
  rewrite H2; repeat Usimpl.

  (**)
  assert (H3:At <= Af).
  rewrite H1 in *.
  unfold Af, At.
  generalize i m Heq Hneq.
  clear a H1 IH1 H2 H Af At Bf Bt Heq Hnin i m Hneq Hn.
  intros.
  eapply equiv_deno_le; [ apply (equiv_inv_w n) | | ].
  intros m1 m2 [_ [H H0] ].
  unfold inv_while_diff in H; decompose [and] H; clear H.
  rewrite H5.
  Usimpl.
  induction l.
  trivial.
  simpl.
  unfold EP, andP, andb.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  generalize 
   (nat_eqb_spec a (n - (peval qH_poly k + 1 - length (m1 T)))%nat).
  case (nat_eqb a (n - (peval qH_poly k + 1 - length (m1 T)))%nat); intro Ha.
  subst; rewrite H2; trivial.
  rewrite (H5 _ Ha).
  case (negb (nth a (m2 T) false)); auto.

  generalize H0 Hneq; clear.
  unfold EP1, notR.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  intro Hgt.
  rewrite not_is_true_false in Hgt.
  apply leb_complete_conv in Hgt.
  intro; omega.

  split; [ unfold kreq_mem; trivial | ].
  unfold inv_while_diff.
  mem_upd_simpl.
  repeat split.
  simpl; omega.
  simpl length; rewrite Heq, minus_diag; trivial.
  intros; destruct j.
  rewrite Heq in H.
  elim H; rewrite minus_diag; trivial.
  trivial.
  (**)

  rewrite H3.
  rewrite Umult_sym, <- Udistr_plus_left, Uinv_opp_right; trivial.
  rewrite Uinv_inv; trivial.
  trivial.

  (* a < n *)
  clear H m0 H0; change (a < n)%nat in H1.
  rewrite leb_correct_conv; [ | omega].
  intros IH1 IH2.
  rewrite deno_while_elim, deno_cond_elim.
  rewrite deno_while_elim, deno_cond_elim.
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  rewrite leb_correct; [ | omega].
  rewrite deno_app_elim, deno_cons_elim, Mlet_simpl.
  rewrite deno_sample_p, deno_assign_elim, deno_assign_elim.
  rewrite deno_app_elim, (@deno_cons_elim k E (t <$- {0,1}_p)), Mlet_simpl.
  rewrite deno_sample_p, deno_assign_elim, deno_assign_elim. 
  simpl E.eval_expr; unfold O.eval_op; simpl T.app_op.
  mem_upd_simpl.
  rewrite <- IH1, <- IH2.
  rewrite Udistr_plus_right, Umult_assoc, Umult_assoc; trivial.
  trivial.
  apply Uinv_mult_simpl; rewrite Uinv_inv; trivial.
 Qed.

 Notation mr := (Var.Lvar (T.Pair Msg (T.User group)) 101).

 Definition I2b : mem_rel :=
  (fun k (m1 m2:Mem.t k) => map (@snd nat nat) (m1 I) = rev (seq 0 (length (m1 LH)))) /-\
  EP1 (E.Eforall z (z in_dom I) LS) /-\
  EP1 (E.Eforall mr ((Efst mr) in_dom I) LH).

 Definition eq_dec_nat (n m:nat) : sumbool (n = m) True :=
  match (eq_nat_dec n m) with
  | left i => left _ i
  | right _ => right _ Logic.I
  end.

 Lemma eq_dec_nat_r : forall n m i, eq_dec_nat n m = right _ i -> n <> m.
 Proof.
  intros n m; simpl; intro i.
  unfold eq_dec_nat; case (eq_nat_dec n m); intros.
  discriminate.
  trivial.
 Qed.

 Lemma dec_I2b : decMR I2b.
 Proof.
  unfold I2b; apply decMR_and; [ | auto].
  unfold decMR; intros.
  match goal with 
  |- sumbool (?X = ?Y) _ => 
     case_eq (eq_dec_list eq_dec_nat X Y); intros Heq H
  end.
  left; trivial.
  right; apply eq_dec_list_r with (2:=H); apply eq_dec_nat_r.
 Qed.

 Lemma dep_I2b : depend_only_rel I2b 
  (Vset.add LH (Vset.add I (Vset.singleton LS))) Vset.empty.
 Proof.
  unfold I2b.
  change (Vset.add LH (Vset.add I (Vset.singleton LS))) with
   (Vset.union (Vset.add LH (Vset.singleton I)) (Vset.add LH (Vset.add I (Vset.singleton LS)))).
  change Vset.empty with (Vset.union Vset.empty Vset.empty).
  apply depend_only_andR.
  unfold depend_only_rel, EP1; intros.
  rewrite <- H, <- H; trivial.  
  unfold depend_only_rel, andR, EP1; intros.
  apply req_mem_sym in H; destruct H1.
  split.
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  trivial.
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  trivial.
 Qed.

 Definition eE2E2 : eq_inv_info I2b E2 E2.
  refine (@empty_inv_info I2b _ _ dep_I2b _ dec_I2b E2 E2).
  vm_compute; trivial.
 Defined.

 Lemma Hash2_Hash2 :
  EqObsInv I2b
  (Vset.add mH (Vset.add LH (Vset.singleton I)))
  E2 Hash2_body
  E2 Hash2_body  
  (Vset.add mH (Vset.add LH (Vset.singleton I))).
 Proof.
  unfold Hash2_body, I2b.
  eqobsrel_tail; 
   unfold req_mem_rel, implMR, andR, EP1; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [Hreq [Heq [H H0] ] ].
  repeat split.

  mem_upd_simpl.   
  simpl map; rewrite Heq.
  simpl length; rewrite seq_S, rev_unit; trivial.

  bprop; intros x Hin.
  autorewrite with Ris_true in H.
  generalize (H x Hin); clear H.
  bprop; intros [z [Hz ?] ].
  rewrite Mem.get_upd_diff in Hz; [ | discriminate].
  rewrite Mem.get_upd_same in H.
  right; exists z; split; auto.

  rewrite nat_eqb_refl; simpl.
  bprop; intros x Hin.
  autorewrite with Ris_true in H0.
  generalize (H0 x Hin); clear H0.
  bprop; intros [z [Hz ?] ].
  rewrite Mem.get_upd_diff in Hz; [ | discriminate].
  rewrite Mem.get_upd_same in H0.
  right; exists z; split; auto.

  trivial.

  bprop; intros x Hin.
  autorewrite with Ris_true in H.
  generalize (H x Hin); clear H.
  bprop; intros [z [Hz ?] ].
  rewrite Mem.get_upd_diff in Hz; [ | discriminate].
  rewrite Mem.get_upd_same in H.
  exists z; split; auto.

  bprop; intros x Hin.
  autorewrite with Ris_true in H0.
  generalize (H0 x Hin); clear H0.
  bprop; intros [z [Hz ?] ].
  rewrite Mem.get_upd_diff in Hz; [ | discriminate].
  rewrite Mem.get_upd_same in H0.
  exists z; split; auto.  
 Qed.

 Definition hE2E2 : eq_inv_info I2b E2 E2 :=
  add_info Hash Vset.empty Vset.empty eE2E2 Hash2_Hash2.

 Lemma Sign2_Sign2 :
  EqObsInv I2b 
  (Vset.add mS (Vset.add LS (Vset.add LH (Vset.singleton I))))
  E2 Sign2_body
  E2 Sign2_body  
  (Vset.add sigma (Vset.add LS (Vset.add LH (Vset.singleton I)))).
 Proof.
  unfold Sign2_body, Sign1_body.
  inline hE2E2 Hash.
  apply decMR_req_mem_rel; apply dec_I2b.

  ep; deadcode hE2E2.
  eqobs_tl hE2E2.

  unfold I2b.
  eqobsrel_tail; 
   unfold req_mem_rel, implMR, andR, EP1; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [Hreq [Heq [H H0] ] ].
  repeat split.

  mem_upd_simpl.   
  simpl map; rewrite Heq; simpl length; rewrite seq_S, rev_unit; trivial.

  rewrite nat_eqb_refl; simpl.
  bprop; intros x Hin.
  autorewrite with Ris_true in H.
  generalize (H x Hin); clear H.
  bprop; intros [z [Hz ?] ].
  rewrite Mem.get_upd_diff in Hz; [ | discriminate].
  rewrite Mem.get_upd_same in H.
  right; exists z; split; auto.

  rewrite nat_eqb_refl; simpl.
  bprop; intros x Hin.
  autorewrite with Ris_true in H0.
  generalize (H0 x Hin); clear H0.
  bprop; intros [z [Hz ?] ].
  rewrite Mem.get_upd_diff in Hz; [ | discriminate].
  rewrite Mem.get_upd_same in H0.
  right; exists z; split; auto.

  mem_upd_simpl.   
  trivial.

  case_eq (existsb (fun p0 => nat_eqb (m1 mS) (fst p0)) (m1 I)); intro Hex. 
  simpl; bprop; intros x Hin.
  autorewrite with Ris_true in H.
  generalize (H x Hin); clear H.
  mem_upd_simpl.   
  trivial.  
  destruct H1 as [H1 _].
  rewrite <- is_true_negb in H1.
  rewrite negb_involutive in H1.
  autorewrite with Ris_true in H0, H1.
  destruct H1 as [x [Hin H2] ].
  generalize (H0 x Hin).
  mem_upd_simpl.   
  apply nat_eqb_true in H2.
  rewrite <- H2, Hex; trivial.

  bprop; intros x Hin.
  autorewrite with Ris_true in H0.
  generalize (H0 x Hin); clear H0.
  bprop; intros [z [Hz ?] ].
  rewrite Mem.get_upd_diff in Hz; [ | discriminate].
  rewrite Mem.get_upd_same in H0.
  exists z; split; auto.
 Qed.

 Definition sE2E2 : eq_inv_info I2b E2 E2 :=
  add_info Sign Vset.empty Vset.empty hE2E2 Sign2_Sign2.

 Definition iE2E2' :=
  add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _)
  (@A_lossless _)
  (@A_lossless _) 
  sE2E2.


 Definition G2b : cmd :=
  [
   I  <- Nil _;
   LH <- Nil _;
   LS <- Nil _;
   rA <c- A with {};
   r <c- Hash with {Efst rA}
  ] ++
  ((T <- Nil _) :: init_T1).

 Lemma Pr_G2b : forall k (m:Mem.t k),
  Pr E2 ((T <- Nil _) :: init_T1) m (@S2 k) ==
  charfun (@S1 k) m * 
  Pr E2 ((T <- Nil _) :: init_T1) m (EP k (Enth {I [{Efst rA}], T}) [&&]
                                     EP k (E.Eforall z (!Enth {I [{z}], T}) LS)).
 Proof.
  intros; unfold Pr.
  rewrite (@Modify_deno_elim E2 (Vset.add t (Vset.singleton T)));
   [ | apply modify_correct with (refl2_info iE1E2) Vset.empty; 
       vm_compute; trivial ].
  symmetry.
  rewrite (@Modify_deno_elim E2 (Vset.add t (Vset.singleton T)));
   [ | apply modify_correct with (refl2_info iE1E2) Vset.empty; 
       vm_compute; trivial ].
  unfold S2, S1, charfun, restr, EP, andP, andb, fone.
  case_eq (@E.eval_expr _ T.Bool ((r =?= f {Esnd rA}) && (Efst rA not_in LS)) m);
   intro H; Usimpl.
  apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
  rewrite (@depend_only_fv_expr T.Bool ((r =?= f {Esnd rA}) && (Efst rA not_in LS)) _
   (m{!Vset.add t (Vset.singleton T) <<- m'!}) m).
  rewrite H; trivial. 
  apply req_mem_update_disjoint; trivial.

  transitivity
   (mu ([[ [T <- Nil _; while Elen T <! (qH +! 1%nat) do 
           [ t <$- {0,1}_p; T <- t |::| T ] ] ]] E2 m) (fzero _)).
  rewrite mu_zero; trivial.
  apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
  rewrite (@depend_only_fv_expr T.Bool ((r =?= f {Esnd rA}) && (Efst rA not_in LS)) _
   (m{!Vset.add t (Vset.singleton T) <<- m'!}) m).
  rewrite H; trivial. 
  apply req_mem_update_disjoint; trivial.
 Qed.

 Lemma Hyp_G2b : forall k (m:Mem.t k), 
  range (@S0 k) 
  ([[
   [
    I  <- Nil _;
    LH <- Nil _;
    LS <- Nil _;
    rA <c- A with {};
    r <c- Hash with {Efst rA}
   ] ]] E2 m).
 Proof.
  intros.
  apply mu_range.
  transitivity (mu ([[G1]] E1 m) (fun m' => if S0 m' then 1 else 0)).
  symmetry.
  apply EqObs_deno with Gadv (Vset.add rA (Vset.add LS (Vset.singleton LH))).
  deadcode iE1E2; eqobs_in iE1E2.

  intros.
  unfold S0, EP, andP.
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  trivial.
  trivial.

  transitivity (mu ([[G1]] E1 m) (fone _)).
  apply range_mu.  
  apply Hyp.  
  apply is_lossless_correct with (refl1_info iE1E2); vm_compute; trivial.  
 Qed.


 Definition S0b k : Mem.t k -o> boolO :=
  (fun (m:Mem.t k) => eqb_list nat_eqb
   (map (@snd nat nat) (m I)) (rev (seq 0 (length (m LH))))) [&&]
  EP k (E.Eforall z (z in_dom I) LS).

 Lemma G2b_post1 : forall k (m:Mem.t k), 
  range (@S0b k) 
  ([[
   [
    I  <- Nil _;
    LH <- Nil _;
    LS <- Nil _;
    rA <c- A with {};
    r <c- Hash with {Efst rA}
   ] ]] E2 m).
 Proof.
  intros k m1; apply mu_range.
  transitivity (mu ([[
   [
    I  <- Nil _;
    LH <- Nil _;
    LS <- Nil _;
    rA <c- A with {};
    r <c- Hash with {Efst rA}
   ] ]] E2 m1) (fone _)).
  apply equiv_deno with (req_mem_rel Gadv trueR) (req_mem_rel Gadv I2b).
  eqobs_tl iE2E2'.
  unfold I2b; eqobsrel_tail; simpl; unfold implMR; intros.
  mem_upd_simpl.  
  auto.
  intros m2 m3 [_ [Heq [Hdom _] ] ].
  unfold EP1 in Hdom; unfold S0, S0b, EP, andP, fone.
  rewrite Hdom, andb_true_r, Heq.
  generalize (eqb_list_spec nat_eqb nat_eqb_spec
   (rev (seq 0 (length (m2 LH))))
   (rev (seq 0 (length (m2 LH)))) ).
  case (eqb_list nat_eqb 
   (rev (seq 0 (length (m2 LH)))) 
   (rev (seq 0 (length (m2 LH)))) ).
  trivial.
  intro H; elim H; trivial.
  unfold req_mem_rel, trueR, andR; auto.
  apply is_lossless_correct with (refl2_info iE1E2); vm_compute; trivial.  
 Qed.

 Lemma G2b_post2 : forall k (m:Mem.t k), 
  range (EP k (Efst rA in_dom I)) 
  ([[
   [
    I  <- Nil _;
    LH <- Nil _;
    LS <- Nil _;
    rA <c- A with {};
    r <c- Hash with {Efst rA}
   ] ]] E2 m).
 Proof.
  intros k m1; apply mu_range.
  transitivity (mu ([[
   [
    I  <- Nil _;
    LH <- Nil _;
    LS <- Nil _;
    rA <c- A with {};
    r <c- Hash with {Efst rA}
   ] ]] E2 m1) (fone _)).
  apply equiv_deno with (req_mem_rel Gadv trueR) (req_mem_rel Gadv (EP1 (Efst rA in_dom I))).

  match goal with 
  |- equiv _ _ (?i1::?i2::?i3::?i4::?c) _ _ _ =>
     change (i1::i2::i3::i4::c) with ([i1;i2;i3;i4] ++ c);
     apply equiv_app with (req_mem_rel (Vset.add rA (Vset.singleton LH)) I2b) 
  end.  
  eqobs_tl iE2E2'.
  unfold I2b; eqobsrel_tail; simpl; unfold implMR; intros.
  mem_upd_simpl.  
  auto.

  inline iE2E2' Hash.
  auto using dec_I2b.

  eqobsrel_tail; simpl; unfold O.eval_op; simpl; unfold implMR. 
  intros ? m2 m3 [Hreq [Heq [Hdom f] ] ].
  repeat split.
  intros [H1 _] v _.
  rewrite nat_eqb_refl; trivial.

  intros [H1 _].  
  rewrite <- is_true_negb, negb_involutive in H1.
  generalize f; clear f; unfold EP1.
  simpl; unfold O.eval_op; simpl.
  intro H.
  autorewrite with Ris_true in H, H1.
  destruct H1 as [x [Hin ?] ].
  generalize (H x Hin).
  mem_upd_simpl.
  apply nat_eqb_true in H0.
  rewrite H0; trivial.

  unfold EP1, EP; intros m2 m3 [_ H].
  rewrite H; trivial.
  unfold req_mem_rel, andR, trueR; auto.
  apply is_lossless_correct with (refl2_info iE1E2); vm_compute; trivial.  
 Qed.

 Lemma G2b_post : forall k (m:Mem.t k), 
  range (@S0 k [&&] @S0b k [&&] EP k (Efst rA in_dom I))
  ([[
   [
    I  <- Nil _;
    LH <- Nil _;
    LS <- Nil _;
    rA <c- A with {};
    r <c- Hash with {Efst rA}
   ] ]] E2 m).
 Proof.
  intros k m1.
  apply range_strengthen.
  apply is_lossless_correct with (refl2_info iE1E2); vm_compute; trivial.    
  apply Hyp_G2b.
  apply range_strengthen.
  apply is_lossless_correct with (refl2_info iE1E2); vm_compute; trivial.    
  apply G2b_post1.
  apply G2b_post2.
 Qed. 

 Lemma Pr_S2 : forall k (m:Mem.t k),
  Pr E2 G2b m (@S1 k) * p k * ([1-] p k)^(peval qS_poly k) <=
  Pr E2 G2b m (@S2 k).
 Proof.
  intros; unfold Pr.
  repeat rewrite <- mu_stable_mult_right.
  unfold G2b; repeat rewrite deno_app_elim.
  apply Ole_eq_right with
   (mu
    ([[ [
         I <- Nil _;
         LH <- Nil _;
         LS <- Nil _;
         rA <c- A with {};
         r <c- Hash with {Efst rA}
        ] ]] E2 m)
    (fun m =>
      charfun (@S1 k) m * 
      Pr E2 ([ 
         T <- Nil _;
         while Elen T <! (qH +! 1%nat) do 
          [ 
           t <$- {0,1}_p; T <- t |::| T 
          ] 
      ]) m 
      (EP k (Enth {I [{Efst rA}], T}) [&&]
       EP k (E.Eforall z (!Enth {I [{z}], T}) LS)))).
  2:apply mu_stable_eq; refine (ford_eq_intro _); intro m'; rewrite <- Pr_G2b; trivial.
  
  apply (range_le (G2b_post m)).
  intros m' Hm'.
  transitivity
   (mu ([[ [T <- Nil _; while Elen T <! (qH +! 1%nat) do
            [ t <$- {0,1}_p; T <- t |::| T ] ] ]] E2 m')
    (fcte _
     ((charfun (@S1 k) m') * p k * ([1-] p k)^peval qS_poly k))).
  rewrite (@Modify_deno_elim E2 (Vset.add t (Vset.singleton T)));
   [ | apply modify_correct with (refl2_info iE1E2) Vset.empty;
       vm_compute; trivial ].
  unfold S1, charfun, restr, EP, andP, andb, fone.
  apply mu_monotonic; refine (ford_le_intro _); intro m''.
  rewrite (@depend_only_fv_expr T.Bool ((r =?= f {Esnd rA}) && (Efst rA not_in LS)) _
   (m'{!Vset.add t (Vset.singleton T) <<- m''!}) m').
  trivial.
  apply req_mem_update_disjoint; trivial.

  rewrite mu_cte.  
  rewrite (init_T_lossless E2 m').
  unfold S1, charfun, restr, EP, fone.
  replace (@E.eval_expr _ T.Bool ((r =?= f{Esnd rA}) && (Efst rA not_in LS)) m')
   with (E.eval_expr (r =?= f{Esnd rA}) m' && E.eval_expr (Efst rA not_in LS) m')%bool by trivial.
  case_eq (E.eval_expr (Efst rA not_in LS) m'); intro H1.  
  Usimpl; rewrite <- Umult_assoc; Usimpl.
  unfold Pr.

  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  clear m; set (m:=m'{!T <-- E.eval_expr (E.Cnil T.Bool) m'!}).
  unfold andP in Hm'.
  rewrite is_true_andb in Hm'.
  unfold S0, S0b, EP, andP in Hm'; destruct Hm'.
  autorewrite with Ris_true in H, H0.
  destruct H as [H3 H4].
  destruct H0 as [ [H5 H6] H2].

  assert (E.eval_expr (I[{Efst (rA)}]) m' < peval qH_poly k + 1)%nat.
  generalize (eqb_list_spec nat_eqb nat_eqb_spec
   (map (@snd nat nat) (m' I))
   (rev (seq 0 (length (m' LH)))) ).
  rewrite H5; clear H5; intro H5.
  apply in_dom_In in H2.
  generalize H2 H3; clear H2 H3.
  simpl; unfold O.eval_op; simpl.
  intros H2 Hle; apply leb_complete in Hle.  
  eapply lt_le_trans with (2:=Hle).
  apply (in_map (@snd nat nat)) in H2.
  rewrite H5, <- In_rev in H2; clear -H2.
  simpl in H2; apply In_seq_le in H2; omega.

  assert (forall n, 
   In n (m' LS) ->
   E.eval_expr (I[{n}]) m' < peval qH_poly k + 1)%nat.
  generalize (eqb_list_spec nat_eqb nat_eqb_spec
   (map (@snd nat nat) (m' I))
   (rev (seq 0 (length (m' LH)))) ).
  rewrite H5; clear H5; intro H5.
  intros n Hin.
  generalize H6; clear H6.
  simpl; unfold O.eval_op; simpl.
  bprop.
  intro H6; generalize (H6 n Hin); clear H6 Hin.
  unfold m; mem_upd_simpl.
  intro Hin.
  change (is_true (E.eval_expr (n in_dom I) m')) in Hin.
  apply in_dom_In in Hin.
  generalize H3 Hin; clear Hin H3.
  simpl; unfold O.eval_op; simpl.  
  intro Hle; apply leb_complete in Hle.  
  intro Hin.
  eapply lt_le_trans with (2:=Hle); clear Hle.
  apply (in_map (@snd nat nat)) in Hin.
  simpl in Hin; rewrite H5, <- In_rev in Hin; clear -Hin.
  apply In_seq_le in Hin; omega.

  assert (length (m' LS) <= peval qS_poly k)%nat.
   apply leb_complete.
   generalize H4; clear H4; unfold m.
   simpl; unfold O.eval_op; trivial.

  transitivity
   (S1f m (peval qH_poly k + 1) (E.eval_expr (I[{Efst rA}]) m) * 
    S2f m (peval qH_poly k + 1) (map (fun z:nat => E.eval_expr (I[{z}]) m ) (m LS))).
  (**)
  unfold S1f.
  rewrite leb_correct_conv.
  unfold p; Usimpl; fold (p k).

  generalize H4; clear H4.
  simpl; unfold O.eval_op; simpl.
  bprop.
  generalize H7; clear H7.
  unfold m; mem_upd_simpl.
  generalize (m' LS) H0; clear.
  induction (peval qS_poly k); intros l Hin Hlen H.
  destruct l; [trivial | elimtype False; simpl in Hlen; omega].

  inversion Hlen; clear Hlen.
  
  rewrite H1; simpl Uexp.
  destruct l; [ discriminate | ].
  simpl in H1.
  injection H1; clear H1; intro.  
  rewrite (IHn l); trivial.
  simpl.
  rewrite leb_correct_conv; [ | auto with arith].
  Usimpl; trivial.

  generalize (Hin i); clear Hin.
  simpl; unfold O.eval_op; auto.
  intros; apply Hin; simpl; auto.
  rewrite H0; trivial.

  simpl Uexp; rewrite (IHn l); trivial.
  apply leb_correct; trivial.

  generalize H.
  simpl; unfold O.eval_op; simpl.
  unfold m; mem_upd_simpl.
  trivial.
  (**)
 
  rewrite (@Modify_deno_elim E2 (Vset.add T (Vset.singleton t)));
   [ | apply modify_correct with (refl2_info iE1E2) Vset.empty;
       vm_compute; trivial ].
  rewrite (@Pr_nth_T1_l E2).
  unfold Pr, init_T1.
  apply mu_monotonic.
  unfold charfun, restr, EP, andP, andb, fone; intro m''.
  simpl; unfold O.eval_op; simpl. 
  unfold m; mem_upd_simpl.
  case (nth (O.assoc (nat_eqb (fst (m' rA))) 0%nat (m' I)) (m'' T) false); 
   [ | trivial].
  induction (m' LS); simpl.
  trivial.
  unfold EP, andP, andb.
  simpl; unfold O.eval_op; simpl. 
  mem_upd_simpl.
  case (negb (nth (O.assoc (nat_eqb a) 0%nat (m' I)) (m'' T) false)); trivial.
  apply IHi.
  intros; apply H0; simpl; auto.
  simpl in H7; omega.
  2:unfold m; rewrite Mem.get_upd_same; simpl; unfold O.eval_op; auto with arith.

  rewrite in_map_iff; intros [x [Heq Hin] ].
  case (eq_nat_dec (fst (m rA)) x); intro Hx.
  
  (* fst rA = x *)
  rewrite <- Hx in Hin.
  change (E.eval_expr (Efst rA not_in LS) m' = true) with
   (is_true (@E.eval_expr _ _ (Efst rA not_in LS) m')) in H1.
  generalize H1; clear -Hin.
  simpl; unfold O.eval_op; simpl.
  bprop; intro H; elim H; clear H.
  exists (fst (m' rA)).
  split.
  unfold m in Hin; repeat (rewrite Mem.get_upd_diff in Hin; [ | discriminate]).
  trivial.
  apply nat_eqb_refl.

  (* fst rA <> x *)
  generalize H6.
  simpl; unfold O.eval_op; simpl.
  bprop.
  unfold m in Hin; repeat (rewrite Mem.get_upd_diff in Hin; [ | discriminate]).
  intro H8; generalize (H8 x Hin); clear Hin H8; mem_upd_simpl.
  change (E.eval_expr (x in_dom I) m' -> False); intro.
  apply in_dom_In in H8.
  generalize H8; clear H8.
  simpl; unfold O.eval_op; simpl; intro H8.

  generalize (eqb_list_spec nat_eqb nat_eqb_spec
   (map (@snd nat nat) (m' I))
   (rev (seq 0 (length (m' LH)))) ).
  rewrite H5; clear H5; intro H5.
  apply in_dom_In in H2.
  clear H1 H4 H6 H0 H7 A_body A_wf A_ret adv_env Hyp A_PPT A_lossless.
  generalize H2 H3 Heq Hx; clear H2 H3 Heq Hx.
  simpl; unfold O.eval_op; simpl.
  unfold m; clear m; mem_upd_simpl.
  set (t:=m' rA); intros HrA Hle Heq Hneq.
  
  destruct t; simpl in *.
  rewrite <- Heq in HrA.
  clear Heq i0.

  generalize 
   (m' I) 
   (@length (nat * (Ut.interp k group)) (m' LH))
   (O.assoc (nat_eqb x) 0%nat (m' I))  
   H8 Hle H5 HrA; clear H8 Hle H HrA H5.
  induction i0; intros.
  
  inversion H8.  

  destruct n; [ discriminate | ].
  rewrite seq_S, rev_unit in H5.
  simpl in H5; injection H5; clear H5; intros; subst.
  destruct a; simpl in H, H8, HrA; destruct H8; destruct HrA.
  
  injection H0; injection H1; clear H0 H1; intros; subst; intuition.

  injection H0; clear H0; intros; subst.
  apply (in_map (@snd nat nat)) in H1.
  rewrite H in H1.
  apply leb_complete in Hle.
  simpl in H1; rewrite <- In_rev in H1.
  apply In_seq_le in H1; omega.

  injection H1; clear H1; intros; subst.
  apply (in_map (@snd nat nat)) in H0.
  rewrite H in H0.
  apply leb_complete in Hle.
  simpl in H0; rewrite <- In_rev in H0.
  unfold O.eval_op in H; simpl in H.
  apply In_seq_le in H0; omega.
  
  apply (IHi0 i2 n0); trivial.
  apply leb_complete in Hle.
  simpl in Hle.
  apply leb_correct.
  omega.  

  rewrite andb_false_r; repeat Usimpl; trivial.
 Qed.

 Definition iE2E2 :=
  add_adv_info_false (EqAD _ _ _ _) (A_wf_E _ _)
  (add_refl_info Sign
   (add_refl_info_O Hash
    (Vset.add mH (Vset.add LS (Vset.add I (Vset.singleton LH))))
    Vset.empty Vset.empty
    (empty_info E2 E2))).

 Lemma EqObs_G2_G2b :
  EqObs Gadv
  E2 G2
  E2 G2b
  (Vset.add r (Vset.add LS (Vset.add I (Vset.add T (Vset.singleton rA))))).
 Proof.
  unfold G2, G2b, init_T1; intros.
  simpl.
  swap iE2E2.
  eqobs_hd iE2E2.
  eqobs_in iE2E2.
 Qed.

 Lemma Pr_G2_G2b : forall k (m:Mem.t k),
  Pr E2 G2 m (@S1 k) == Pr E2 G2b m (@S1 k).
 Proof.
  intros.
  apply equiv_deno with (1:=EqObs_G2_G2b); [ | trivial].
  intros; unfold charfun, restr, S1, EP.
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  trivial.
 Qed.

 Lemma Pr_G2_G2b' : forall k (m:Mem.t k),
  Pr E2 G2 m (@S2 k) == Pr E2 G2b m (@S2 k).
 Proof.
  intros.
  apply equiv_deno with (1:=EqObs_G2_G2b); [ | trivial].
  intros; unfold charfun, restr, S2, EP, andP.
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  trivial.
 Qed.
 
 Theorem Pr_S1_S2 : forall k (m:Mem.t k), 
  Pr E1 G1 m (@S1 k) * p k * ([1-] p k)^(peval qS_poly k) <= 
  Pr E2 G2 m (@S2 k). 
 Proof.
  intros.
  transitivity (Pr E2 G2 m (@S1 k) * p k * ([1-] p k)^(peval qS_poly k)).
  repeat Usimpl.
  apply equiv_deno_le with (1:=EqObs_G1_G2); [ | trivial].
  intros; unfold charfun, restr, S1, EP.
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  trivial.
  rewrite Pr_G2_G2b, Pr_G2_G2b'.
  apply Pr_S2.
 Qed.
 (** END [Pr_S1_S2] *)


 (** BEGIN [Pr_S2_S3] *)

 (** The third game *)
 Definition G3 : cmd :=
  [
   T <- Nil _;
   while Elen T <! (qH +! 1%nat) do 
    [ 
     t <$- {0,1}_p; T <- t |::| T 
    ];
   Y <$- G_k;
   I  <- Nil _;
   LH <- Nil _;
   LS <- Nil _;
   rA <c- A with {};
   r <c- Hash with {Efst rA}
  ].

 Definition Hash3_body : cmd :=
  [
   If !(mH in_dom LH) _then
   [
    s <$- G_k; 
    If Enth {Elen LH, T} then
     [
      rH <- Y |x| f {s}
     ]
    else 
     [
      rH <- f {s}
     ];
    I <- (mH | Elen LH) |::| I;
    LH <- (mH | rH) |::| LH
   ]
  ].

 Definition Sign3_body := Sign2_body.
 
 Definition E3 := makeEnv Hash3_body Sign3_body.

 Definition S3 := S2.  

 Lemma Hash2_Hash3 :
  EqObsInv trueR 
  (Vset.add mH (Vset.add LH (Vset.add I (Vset.singleton T))))
  E2 Hash2_body
  E3 Hash3_body  
  (Vset.add mH (Vset.add LH (Vset.singleton I))).
 Proof.
  unfold Hash2_body, Hash3_body.
  cp_test (mH in_dom LH).
  eqobs_in.
  deadcode; eqobs_tl.
  cp_test_r (Enth {Elen LH, T}).
  apply equiv_strengthen with
   (kreq_mem (Vset.add mH (Vset.add LH (Vset.add I (Vset.singleton T)))));
   [ unfold andR; intuition | ].
  union_mod.
  eapply equiv_strengthen; [ | apply mul_f_rand; discriminate].
  unfold kreq_mem; trivial.

  apply equiv_strengthen with
   (kreq_mem (Vset.add mH (Vset.add LH (Vset.add I (Vset.singleton T)))));
   [ unfold andR; intuition | ].
  union_mod.
  eapply equiv_strengthen; [ | apply f_rand].
  unfold kreq_mem; trivial.
 Qed. 

 Definition iE2E3 :=
  add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _)
  (@A_lossless _)
  (@A_lossless _)
  (add_refl_info Sign
   (add_info Hash 
    Vset.empty (Vset.singleton S)
    (empty_info E2 E3)
    Hash2_Hash3)).

 Lemma EqObs_G2_G3 : 
  EqObs Gadv 
  E2 G2 
  E3 G3 
  (Vset.add r (Vset.add LS (Vset.add I (Vset.add T (Vset.singleton rA))))).
 Proof.
  unfold G2, G3.
  eqobs_hd; eqobs_tl iE2E3.
  deadcode; eqobs_in.
 Qed. 
   
 Theorem Pr_S2_S3 : forall k (m:Mem.t k), 
  Pr E2 G2 m (@S2 k) == Pr E3 G3 m (@S3 k).
 Proof.
  intros; unfold G2, G3, Pr.
  apply EqObs_deno with (1:=EqObs_G2_G3); [ | trivial].
  intros m1 m2 H; unfold S3, S2, charfun, restr, EP, andP.
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  trivial.
 Qed. 
 (** END [Pr_S2_S3] *)


 (** BEGIN [Pr_S3_S4] *)

 (** The fourth game *)
 Definition G4 : cmd :=
  [
   bad <- false;
   T <- Nil _;
   while Elen T <! (qH +! 1%nat) do 
    [ 
     t <$- {0,1}_p; T <- t |::| T 
    ];
   Y <$- G_k;
   S <- Nil _;
   I  <- Nil _;
   LH <- Nil _;
   LS <- Nil _;
   rA <c- A with {};
   r <c- Hash with {Efst rA};
   x <- Esnd rA |x| (S[{Efst rA}]^-1)
  ].

 Definition Hash4_body :=
  [
   If !(mH in_dom LH) _then
   [
    s <$- G_k; 
    If Enth {Elen LH, T} then
     [
      rH <- Y |x| f {s}
     ]
    else 
     [
      rH <- f {s}
     ];
    I <- (mH | Elen LH) |::| I;
    LH <- (mH | rH) |::| LH;
    S <- (mH | s) |::| S
   ]
  ].

 Definition Sign4_body := 
  [
   LS <- mS |::| LS;
   rS <c- Hash with {mS};
   If Enth {I[{mS}], T} then
    [
     bad <- true;
     sigma <- finv {rS}
    ]
   else
    [
     sigma <- S[{mS}]
    ]
  ].
 
 Definition E4 := makeEnv Hash4_body Sign4_body.

 Definition S4 k := 
  EP k (x =?= finv {Y}) [&&]
  EP k (Enth {I [{Efst (rA)}], T}) [&&]
  EP k (E.Eforall z (!Enth {I [{z}], T}) LS).

 Definition I4 : mem_rel :=
  EP2 (E.Eforall mr
  ( (Esnd mr =?= 
    ((Enth {I[{Efst mr}], T}) ?
      (Y |x| f {S[{Efst mr}]}) ?: (f {S[{Efst mr}]})))) LH).

 Lemma dec_I4 : decMR I4.
 Proof.
  unfold I4; auto.
 Qed.

 Lemma dep_I4 : depend_only_rel I4 
  Vset.empty 
  (fv_expr
   (E.Eforall mr
    ( (Esnd mr =?= 
      ((Enth {I[{Efst mr}], T}) ?
       (Y |x| f {S[{Efst mr}]}) ?: (f {S[{Efst mr}]})))) LH)).
 Proof.
  unfold I4; auto.
 Qed.

 Definition eE3E4 : eq_inv_info I4 E3 E4.
  refine (@empty_inv_info I4 _ _ dep_I4 _ dec_I4 E3 E4).
  vm_compute; trivial.
 Defined.

 Lemma Hash3_Hash4 :
  EqObsInv I4 
   (Vset.add Y (Vset.add mH (Vset.add LH (Vset.add I (Vset.singleton T)))))
  E3 Hash3_body
  E4 Hash4_body  
  (Vset.add mH (Vset.add LH (Vset.singleton I))).
 Proof.
  unfold Hash3_body, Hash4_body.
  cp_test (mH in_dom LH).
  rewrite proj1_MR; eqobs_in eE3E4.

  unfold I4; eqobsrel_tail; 
   unfold req_mem_rel, implMR, andR, EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H1 H2] v _.
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  split; intros.

  decompose [and] H; clear H.
  rewrite H3.
  rewrite UTi_eqb_refl.
  decompose [and] H2; clear H2 H5.
  simpl; autorewrite with Ris_true in H |- *.
  intros x Hx; generalize (H x Hx); clear H.
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ |discriminate]).
  intro; unfold notR in H6.
  case_eq (nat_eqb (fst x) (m2 mH)); intro Heq.
  autorewrite with Ris_true in H6; elim H6.
  exists x; split.
  trivial.
  rewrite nat_eqb_sym; trivial.
  trivial.

  decompose [and] H; clear H.
  rewrite not_is_true_false in H3.
  rewrite H3.
  rewrite UTi_eqb_refl.
  decompose [and] H2; clear H2 H5.
  simpl; autorewrite with Ris_true in H |- *.
  intros x Hx; generalize (H x Hx); clear H.
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ |discriminate]).
  intro; unfold notR in H6.
  case_eq (nat_eqb (fst x) (m2 mH)); intro Heq.
  autorewrite with Ris_true in H6; elim H6.
  exists x; split.
  trivial.
  rewrite nat_eqb_sym; trivial.
  trivial.
 Qed. 

 Definition hE3E4 : eq_inv_info I4 E3 E4 :=
  add_info Hash Vset.empty Vset.empty eE3E4 Hash3_Hash4.
 
 Lemma Sign3_Sign4 :
  EqObsInv I4 
  (Vset.add mS
   (Vset.add LS (Vset.add Y (Vset.add LH (Vset.add I (Vset.singleton T))))))
  E3 Sign3_body
  E4 Sign4_body  
  (Vset.add sigma (Vset.add LS (Vset.add LH (Vset.singleton I)))).
 Proof.
  unfold Sign4_body, Sign3_body, Sign2_body, Sign1_body.
  inline hE3E4 Hash.
  unfold I4; auto.
  ep; deadcode hE3E4; eqobs_hd hE3E4.
  apply equiv_cons with 
   (req_mem_rel 
    (Vset.add LS (Vset.add T 
     (Vset.add mS (Vset.add LH (Vset.singleton I)))))
    (I4 /-\ EP2 (mS in_dom LH))).
  cp_test (mS in_dom LH).

  eapply equiv_strengthen; [ | apply equiv_nil].  
  unfold EP2, andR; intros k m1 m2 [ [Hreq HI] [_ H] ].
  repeat split; trivial.
  apply req_mem_weaken with (2:=Hreq); unfold Vset.subset; trivial.

  unfold I4; eqobsrel_tail; 
   unfold req_mem_rel, implMR, andR, EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H1 H2] v _. 
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  split; intros.

  decompose [and] H; clear H.
  rewrite H3.
  rewrite UTi_eqb_refl.
  decompose [and] H2; clear H2 H5.
  simpl; autorewrite with Ris_true in H |- *.
  split; [ | trivial].
  intros x Hx; generalize (H x Hx); clear H.
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ |discriminate]).
  intro; unfold notR in H6.
  case_eq (nat_eqb (fst x) (m2 mS)); intro Heq.
  autorewrite with Ris_true in H6; elim H6.
  exists x; split.
  trivial.
  rewrite nat_eqb_sym; trivial.
  trivial.

  decompose [and] H; clear H.
  rewrite not_is_true_false in H3.
  rewrite H3.
  rewrite UTi_eqb_refl.
  decompose [and] H2; clear H2 H5.
  simpl; autorewrite with Ris_true in H |- *.
  split; [ | trivial].
  intros x Hx; generalize (H x Hx); clear H.
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ |discriminate]).
  intro; unfold notR in H6.
  case_eq (nat_eqb (fst x) (m2 mS)); intro Heq.
  autorewrite with Ris_true in H6; elim H6.
  exists x; split.
  trivial.
  rewrite nat_eqb_sym; trivial.
  trivial.

  cp_test (Enth {I[{mS}], T}).
  eqobs_in hE3E4; unfold implMR, andR; intros; intuition.

  eapply equiv_strengthen; [ | eapply equiv_assign].
  unfold I4, req_mem_rel, andR, upd_para.
  intros k m1 m2 [ [ H1 [H2 H3] ] [_ H4] ].
  simpl; unfold O.eval_op; simpl.
  split.

  intros t x Hx.
  apply in_dom_In in H3.
  unfold notR, EP2 in H2, H3 , H4; simpl in H2, H3, H4;
   unfold O.eval_op in H2, H3, H4; simpl in H2, H3, H4.
  autorewrite with Ris_true in H2, H4.
  assert (H5:Vset.mem x 
   (Vset.add sigma (Vset.add LS (Vset.add LH (Vset.singleton I))))).
  exact Hx.
  Vset_mem_inversion H5; subst.

  repeat rewrite Mem.get_upd_same.
  generalize (H2 _ H3). 
  rewrite Mem.get_upd_same; repeat rewrite Mem.get_upd_diff; try discriminate.
  rewrite not_is_true_false in H4.
  simpl; rewrite H4.
  rewrite (H1 _ LH), (H1 _ mS); trivial.
  clear; intro Heq.
  rewrite is_true_UTi_eqb in Heq.
  rewrite Heq, f_spec; trivial.
  
  repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  rewrite (H1 _ LS); trivial.
  repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  rewrite (H1 _ LH); trivial.
  repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  rewrite (H1 _ I); trivial.

  assert (forall v,
   kreq_mem (fv_expr 
    (E.Eforall mr
     (Esnd (mr) =?=
      Enth {I [{Efst (mr)}], T} ? Y |x| f {S [{Efst (mr)}]}
       ?: f {S [{Efst (mr)}]}) LH))
   (m2 {! sigma <-- v!}) m2).
   intro; unfold fv_expr; simpl.
   apply req_mem_sym; apply req_mem_upd_disjoint; trivial.
   
   unfold EP2.
   rewrite depend_only_fv_expr_subset with (2:=H _); 
    [ | unfold Vset.subset; trivial].
   trivial.
 Qed. 

 Definition sE3E4 : eq_inv_info I4 E3 E4 :=
  add_info Sign Vset.empty Vset.empty hE3E4 Sign3_Sign4.

 Definition iE3E4 :=
  add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _)
  (@A_lossless _)
  (@A_lossless _) 
  sE3E4.
   
 Theorem Pr_S3_S4 : forall k (m:Mem.t k), 
  Pr E3 G3 m (@S3 k) <= Pr E4 G4 m (@S4 k).
 Proof.
  intros; unfold G3, G4. 
  apply equiv_deno_le with (kreq_mem Gadv) 
   (req_mem_rel 
    (Vset.add r (Vset.add Y (Vset.add LH (Vset.add LS 
     (Vset.add I (Vset.add T (Vset.singleton rA)))))) )
    (I4 /-\ 
     EP2 (r =?= LH[{Efst rA}]) /-\ 
     EP2 (Efst rA in_dom LH) /-\ 
     (EP2 (x =?= Esnd rA |x| (S[{Efst rA}]^-1))))).

  match goal with 
  |- equiv _ _ (?i1::?i2::?c1) _ (?b::?i1::?i2::?c2) _ =>
     change (b::i1::i2::c2) with ([b;i1;i2] ++ c2);
     change (i1::i2::c1) with ([i1;i2] ++ c1);
     apply equiv_app with (kreq_mem (Vset.singleton T)) 
  end.
  deadcode; eqobs_in.

  match goal with 
  |- equiv _ _ (?i1::?i3::?i4::?i5::?i6::?c1) _ 
               (?i1::?i2::?i3::?i4::?i5::?i6::?c2) _ =>
     change (i1::i3::i4::i5::i6::c1) with ([i1;i3;i4;i5;i6] ++ c1);
     change (i1::i2::i3::i4::i5::i6::c2) with ([i1;i2;i3;i4;i5;i6] ++ c2);
     apply equiv_app with 
      (req_mem_rel
       (Vset.add Y (Vset.add LH 
        (Vset.add LS (Vset.add I (Vset.add T (Vset.singleton rA))))))
       I4)
  end.
  eqobs_tl iE3E4.
  unfold I4; eqobsrel_tail; simpl; unfold implMR; trivial.

  inline iE3E4 Hash.
  unfold I4; auto.
  ep; deadcode iE3E4.
  eqobs_hd iE3E4.
  cp_test (Efst rA in_dom LH).

  unfold I4; eqobsrel_tail; 
   unfold implMR, andR, EP2; simpl; unfold O.eval_op; simpl.
  intros ? m1 m2 [Hreq [H [_ H0] ] ].
  repeat split; trivial.
  autorewrite with Ris_true in H |- *.
  intros x Hin; generalize (H x Hin).
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  trivial.
  apply UTi_eqb_refl.
  apply UTi_eqb_refl.

  unfold I4; eqobsrel_tail; 
   unfold req_mem_rel, implMR, andR, EP2; simpl; unfold O.eval_op; simpl.
  intros ? m1 m2 [H1 H2] v _.
  unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
  repeat split; intros.
  decompose [and] H2; clear H2.
  destruct H as [_ H]; rewrite H; simpl.
  rewrite UTi_eqb_refl.
  simpl; autorewrite with Ris_true in H0 |- *.
  intros x Hx; generalize (H0 x Hx); clear H0.
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ |discriminate]).
  clear H; intro H; unfold notR in H5.
  case_eq (nat_eqb (fst x) (fst (m2 rA))); intro Heq.
  autorewrite with Ris_true in H5; elim H5.
  exists x; split.
  trivial.
  rewrite nat_eqb_sym; trivial.
  trivial.

  apply UTi_eqb_refl.
  apply UTi_eqb_refl.

  decompose [and] H; clear H.
  rewrite not_is_true_false in H3.
  rewrite H3; simpl.
  rewrite UTi_eqb_refl.
  decompose [and] H2; clear H2 H5.
  simpl; autorewrite with Ris_true in H |- *.
  intros x Hx; generalize (H x Hx); clear H.
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ |discriminate]).
  intro H; unfold notR in H6.
  case_eq (nat_eqb (fst x) (fst (m2 rA))); intro Heq.
  autorewrite with Ris_true in H6; elim H6.
  exists x; split.
  trivial.
  rewrite nat_eqb_sym; trivial.
  trivial.
  
  apply UTi_eqb_refl.
  apply UTi_eqb_refl.

  intros m1 m2 [Hreq [H [H0 [H1 Hx] ] ] ].
  unfold charfun, restr, S4, S3, S2, EP, andP, andb, fone.
  unfold EP2 in H0, H1.

  rewrite depend_only_fv_expr_subset with (2:=Hreq); 
   [ | unfold Vset.subset; trivial].
  rewrite depend_only_fv_expr_subset with (2:=Hreq); 
   [ | unfold Vset.subset; trivial].
  rewrite depend_only_fv_expr_subset with (2:=Hreq); 
   [ | unfold Vset.subset; trivial].
  trivial.
  clear Hreq.

  case_eq (@E.eval_expr _ T.Bool (Enth {I [{Efst (rA)}], T}) m2); intro HT.
  case (E.eval_expr (E.Eforall z (!Enth {I [{z}], T}) LS) m2).

  assert (@E.eval_expr _ T.Bool (r =?= f {Esnd rA}) m2 = 
          @E.eval_expr _ T.Bool (x =?= finv {Y}) m2).

  apply in_dom_In in H1.
  generalize H H0 H1 Hx HT; clear H0 H1 Hx HT; unfold I4, EP2.
  simpl; unfold O.eval_op; simpl; intros.
  rewrite is_true_UTi_eqb in H1.
  rewrite H1; clear H1.
  rewrite is_true_UTi_eqb in Hx.
  rewrite Hx; clear Hx.

  autorewrite with Ris_true in H0, H2.
  generalize (H0 _ H2); clear H0 H2.
  rewrite Mem.get_upd_same; repeat rewrite Mem.get_upd_diff; try discriminate.
  simpl; intro H2.
  rewrite HT in H2; clear HT.
  rewrite is_true_UTi_eqb in H2.
  rewrite H2; clear H2.

  set (Y := m2 Y).
  set (madv := fst (m2 rA)).
  set (sadv := snd (m2 rA)).
  set (s := O.assoc (nat_eqb madv) (Ut.default k group) (m2 S)).  

  case_eq (@Ut.i_eqb k group (CG.mul Y (ap_f s)) (ap_f sadv)).
  intro.  
  change (is_true (@Ut.i_eqb k group (CG.mul Y (ap_f s)) (ap_f sadv))) in H0.
  rewrite is_true_UTi_eqb in H0.

  rewrite <- (finv_spec Y) in H0.
  rewrite <- f_homo in H0.
  apply f_inj in H0.
  rewrite <- H0, <- CG.mul_assoc, CGP.mul_inv_r, CGP.mul_e_r, UTi_eqb_refl.
  trivial.

  case_eq (@Ut.i_eqb k group (CG.mul sadv (CG.inv s)) (ap_finv Y)); [ |trivial].
  intros H0 H1.
  change (is_true (@Ut.i_eqb k group (CG.mul sadv (CG.inv s)) (ap_finv Y))) in H0.
  rewrite is_true_UTi_eqb in H0. 
  rewrite <- (finv_spec Y) in H1.
  rewrite <- H0, <- f_homo, <- CG.mul_assoc, 
   CG.mul_inv_l, CGP.mul_e_r, UTi_eqb_refl in H1.
  discriminate.
  
  replace (@E.eval_expr _ T.Bool ((r =?= f{Esnd rA}) && (Efst rA not_in LS)) m2)
   with (@E.eval_expr _ T.Bool (r =?= f{Esnd rA}) m2 && E.eval_expr (Efst rA not_in LS) m2)%bool by trivial.
  rewrite H2.

  case (@E.eval_expr k T.Bool (Efst rA not_in LS) m2);
  case (@E.eval_expr _ T.Bool (x =?= finv {Y}) m2);
  trivial.

  case (@E.eval_expr k T.Bool ((r =?= f{Esnd rA}) && (Efst rA not_in LS)) m2);
  case (@E.eval_expr _ T.Bool (x =?= finv {Y}) m2);
  trivial.

  case (@E.eval_expr k T.Bool ((r =?= f{Esnd rA}) && (Efst rA not_in LS)) m2);
  case (@E.eval_expr _ T.Bool (x =?= finv {Y}) m2);
  trivial.

  trivial.
 Qed. 
 (** END [Pr_S3_S4] *)


 (** BEGIN [Pr_S4_S5] *)

 (** The fifth game *)
 Definition G5 : cmd := G4.

 Definition Hash5_body : cmd := Hash4_body.

 Definition Sign5_body := 
  [
   LS <- mS |::| LS;
   rS <c- Hash with {mS};
   If Enth {I[{mS}], T} then
    [
     bad <- true;
     sigma <- S[{mS}]
    ]
   else
    [
     sigma <- S[{mS}]
    ]
  ].
 
 Definition E5 := makeEnv Hash5_body Sign5_body.

 Definition S5 := S4.

 (** We first prove that [ Pr_G4 [S4] = Pr_G4 [S4 /\ ~bad] ] *)
 Definition I4b : mem_rel :=
  EP1 ((E.Eforall z (!(Enth {I[{z}], T})) LS) ==> !bad) /-\
  EP1 (E.Eforall z (z in_dom LH) LS).

 Lemma dec_I4b : decMR I4b.
 Proof.
  unfold I4b; auto.
 Qed.

 Lemma dep_I4b : depend_only_rel I4b 
  (Vset.add I (Vset.add T (Vset.add LS (Vset.add bad (Vset.singleton LH)))))
  Vset.empty.
 Proof.
  unfold depend_only_rel, I4b, andR, EP1; intros.
  apply req_mem_sym in H.
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  trivial.
 Qed.

 Definition eE4E4 : eq_inv_info I4b E4 E4.
  refine (@empty_inv_info I4b _ _ dep_I4b _ dec_I4b E4 E4).
  vm_compute; trivial.
 Defined.

 Lemma Hash4_Hash4 :
  EqObsInv I4b
  (Vset.add S 
   (Vset.add Y (Vset.add mH (Vset.add LH (Vset.add I (Vset.singleton T))))))
  E4 Hash4_body
  E4 Hash4_body  
  (Vset.add mH (Vset.add LH (Vset.add S (Vset.singleton I)))).
 Proof.
  clear; unfold Hash4_body.
  cp_test (mH in_dom LH).
  rewrite proj1_MR; eqobs_in eE4E4.

  unfold I4b; eqobsrel_tail;
   unfold EP1, req_mem_rel, implMR, andR, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H1 H2] v _.
  decompose [and] H2; clear H2 H5.
  autorewrite with Ris_true in H3, H4.
  split; intros [H2 _]; bprop; split.

  intro H0; apply H3.
  intros x Hin.
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  generalize (H0 x Hin); clear H0.
  unfold O.assoc; simpl.
  case_eq (nat_eqb x (m1 mH)); intro Heq; [ | trivial].
  rewrite <- (nat_eqb_true Heq) in H.
  elim H.
  generalize (H4 x Hin).
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  trivial.

  intros x Hin.
  generalize (H4 x Hin).
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  intro Heq; rewrite Heq; rewrite orb_true_r; trivial.

  intro H0; apply H3.
  intros x Hin.
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  generalize (H0 x Hin); clear H0.
  unfold O.assoc; simpl.
  case_eq (nat_eqb x (m1 mH)); intro Heq; [ | trivial].
  rewrite <- (nat_eqb_true Heq) in H.
  elim H.
  generalize (H4 x Hin).
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  trivial.

  intros x Hin.
  generalize (H4 x Hin).
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  intro Heq; rewrite Heq; rewrite orb_true_r; trivial.
 Qed.

 Definition hE4E4 : eq_inv_info I4b E4 E4 :=
  add_info Hash Vset.empty Vset.empty eE4E4 Hash4_Hash4.

 Lemma Sign4_Sign4 :
  EqObsInv I4b 
  (Vset.add mS (Vset.add S 
   (Vset.add LS (Vset.add Y (Vset.add LH (Vset.add I (Vset.singleton T)))))))
  E4 Sign4_body
  E4 Sign4_body  
  (Vset.add sigma (Vset.add S (Vset.add LS (Vset.add LH (Vset.singleton I))))).
 Proof.
  clear; unfold Sign4_body, I4b.
  inline hE4E4 Hash.
  eqobsrel_tail;
   unfold EP1, req_mem_rel, implMR, andR, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [H1 H2].
  decompose [and] H2; clear H2.
  rewrite nat_eqb_refl; simpl.
  repeat split; intros.

  destruct H5 as [H5 _].
  rewrite H5; simpl; trivial.

  bprop; intros x Hin.
  apply orb_true_intro; right.
  autorewrite with Ris_true in H0.
  generalize (H0 x Hin).
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  trivial.

  destruct H4 as [H4 _].
  destruct H5 as [H5 _].
  bprop; intros.
  autorewrite with Ris_true in H.
  apply H; clear H.
  intros x Hin.
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  bprop.
  generalize H5.
  unfold O.assoc; simpl.
  rewrite nat_eqb_refl; simpl.
  rewrite H4; intro; trivialb.

  bprop; intros x Hin.
  apply orb_true_intro; right.
  autorewrite with Ris_true in H0.
  generalize (H0 x Hin).
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  trivial.

  destruct H5 as [H5 _].
  rewrite H5; simpl; trivial.

  bprop; intros x Hin.
  apply orb_true_intro; right.
  autorewrite with Ris_true in H0.
  generalize (H0 x Hin).
  rewrite Mem.get_upd_same; repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  trivial.

  destruct H2 as [H2 _].
  destruct H4 as [H4 _].
  destruct H5 as [H5 _].
  bprop; intros.
  autorewrite with Ris_true in H.
  apply H; clear H.
  intros x Hin.
  case_eq (nat_eqb x (m1 mS)); intros.
  autorewrite with Ris_true in H0.  
  generalize (H0 x Hin).
  mem_upd_simpl.
  rewrite (nat_eqb_true H); intro Hex; rewrite Hex in H2; discriminate.

  mem_upd_simpl.
  rewrite not_is_true_false in H5.
  rewrite H5 in H6; simpl in H6.
  destruct H6 as [_ H6].
  autorewrite with Ris_true in H6.
  generalize (H6 x Hin).
  unfold O.assoc; simpl.
  rewrite H; trivial.

  bprop; intros x Hin.
  apply orb_true_intro; right.
  autorewrite with Ris_true in H0.
  generalize (H0 x Hin).
  mem_upd_simpl.
  trivial.

  destruct H3 as [H3 _].
  rewrite H3; simpl; trivial.

  destruct H2 as [H2 _].
  rewrite not_is_true_false in H2.
  rewrite <- is_true_negb_false in H2.
  rewrite negb_involutive in H2.
  rewrite H2.
  simpl; bprop; intros x Hin.
  autorewrite with Ris_true in H0.
  generalize (H0 x Hin).
  mem_upd_simpl.
  trivial.

  destruct H3 as [H3 _].
  rewrite not_is_true_false in H3.
  rewrite H3; simpl.
  bprop; intro.
  autorewrite with Ris_true in H.
  apply H.
  intros x Hin.
  generalize (H4 x Hin).
  mem_upd_simpl.
  trivial.

  destruct H2 as [H2 _].
  rewrite not_is_true_false in H2.
  rewrite <- is_true_negb_false in H2.
  rewrite negb_involutive in H2.
  rewrite H2.
  simpl; bprop; intros x Hin.
  autorewrite with Ris_true in H0.
  generalize (H0 x Hin).
  mem_upd_simpl.
 Qed. 

 Definition sE4E4 : eq_inv_info I4b E4 E4 :=
  add_info Sign Vset.empty Vset.empty hE4E4 Sign4_Sign4.

 Definition iE4E4 :=
  add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _)
  (@A_lossless _)
  (@A_lossless _) 
  sE4E4.

 Lemma G4_lossless : lossless E4 G4.
 Proof.
  apply lossless_cons.
  apply lossless_assign.
  change
   (lossless E4 
    (((T <- Nil _) :: init_T1) ++ 
     [
      Y <$- G_k;
      S <- Nil _;
      I  <- Nil _;
      LH <- Nil _;
      LS <- Nil _;
      rA <c- A with {};
      r <c- Hash with {Efst rA};
      x <- Esnd rA |x| (S[{Efst rA}]^-1)
     ])).
  apply lossless_app.
  apply init_T_lossless.
  apply is_lossless_correct with (refl1_info iE4E4); vm_compute; trivial.  
 Qed. 

 Definition iE4E4' :=
  add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _)
  (@A_lossless _)
  (@A_lossless _) 
  (add_refl_info Sign
   (add_refl_info Hash 
    (empty_info E4 E4))).

 Lemma G4_post : forall k (m1:Mem.t k), 
  range ((EP k (E.Eforall z (!(Enth {I[{z}], T})) LS)) [=>] (negP (EP k bad))) ([[G4]] E4 m1).
 Proof.
  intros k m1; apply mu_range.
  transitivity (mu ([[G4]] E4 m1) (fone _)); [ | apply G4_lossless].
  apply equiv_deno with (req_mem_rel Gadv trueR) (req_mem_rel Gadv I4b).
  eqobs_tl iE4E4.

  apply equiv_trans with
   (kreq_mem Gadv)
   (kreq_mem
    (Vset.add bad (Vset.add LS 
     (Vset.add S (Vset.add LH (Vset.add I (Vset.add Y (Vset.singleton T))))))))
   (req_mem_rel
    (Vset.add LS (Vset.add S 
     (Vset.add LH (Vset.add I (Vset.add Y (Vset.singleton T)))))) I4b)
   E4
   [
     T <- E.Cnil T.Bool;
     while (Elen T) <! (qH +! 1%nat) do [t <$- {0,1}_p; T <- t |::| T];
     bad <- false;
     Y <$- G_k;
     S <- E.Cnil (T.Pair Msg (T.User group));
     I <- E.Cnil (T.Pair Msg Msg);
     LH <- E.Cnil (T.Pair Msg (T.User group));
     LS <- E.Cnil Msg
     ].
  auto.
  unfold refl_supMR2, trueR; auto.
  unfold req_mem_rel, andR; intros ? ? ? ? ? [? ?].
  split.
  apply req_mem_trans with y.
  apply req_mem_weaken with (2:=H); unfold Vset.subset; trivial.
  apply req_mem_weaken with (2:=H0); unfold Vset.subset; trivial.

  generalize H1; unfold I4b, EP1, andR; trivial.
  
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  trivial.
  swap_tac iE4E4'; eqobs_in iE4E4'.

  swap_tac iE4E4; simpl.
  match goal with 
  |- equiv _ _ (?i1::?i2::?c) _ _ _ =>
     change (i1::i2::c) with ([i1;i2] ++ c);
     apply equiv_app with (kreq_mem (Vset.singleton T)); [eqobs_in | ]
  end.
  unfold I4b; eqobsrel_tail; simpl; unfold implMR; auto.  
  unfold req_mem_rel, kreq_mem, I4b, EP1, EP, negP, implP, fone, andR.
  intros ? ? [Hreq [H _] ].  
  generalize H; clear H; simpl; unfold O.eval_op; simpl.
  rewrite impb_implb; intro H; rewrite H; trivial.
  unfold req_mem_rel, trueR, andR; auto.
 Qed.

 Theorem Pr_S4_S4 : forall k (m:Mem.t k), 
  Pr E4 G4 m (@S4 k) == Pr E4 G4 m (@S4 k [&&] negP (EP k bad)).
 Proof.
  intros; unfold Pr.
  apply (range_eq (G4_post m)); intro m'.
  unfold S4, S3, S2, charfun, restr, EP, implP, andP, andb, implb, fone.  
  case (@E.eval_expr _ T.Bool (E.Eforall z (!Enth {I [{z}], T}) LS) m');
  case (negP (@E.eval_expr _ T.Bool bad) m');
  case (@E.eval_expr k T.Bool (x =?= finv {Y})); 
  case (@E.eval_expr _ T.Bool (Enth {I [{Efst (rA)}], T}) m');
   trivial; intro; discriminate. 
 Qed.


 (** Now, we prove that [ Pr_G4 [S4] <= Pr_G5 [S5] ] *)
 Definition upto_info45 : upto_info bad E4 E5 :=
  add_adv_upto_info
  (add_upto_info
   (add_upto_info 
    (empty_upto_info bad E4 E5) Hash) Sign)
  (EqAD _ _ _ _)
  (EqOP _ _ _ _)   
  (A_wf_E Hash4_body Sign4_body). 

 (* REMARK: this holds because [bad] is a failure event and [G4] and [G5] are 
    syntactically equal up to the raise of this event *)
 Lemma G4_G5_uptobad : forall k (m:Mem.t k),
  Pr E4 G4 m (@S4 k [&&] negP (EP k bad)) == 
  Pr E5 G5 m (@S5 k [&&] negP (EP k bad)).
 Proof.
  intros; unfold G5, G4, Pr.  
  setoid_rewrite deno_cons_elim.
  setoid_rewrite Mlet_simpl.
  setoid_rewrite deno_assign_elim.
  apply upto_bad_and_neg with upto_info45; trivial.
 Qed.

 Close Scope nat_scope.

 Lemma Pr_S4_S5 : forall k (m:Mem.t k), 
  Pr E4 G4 m (@S4 k) <= Pr E5 G5 m (@S5 k).
 Proof.
  intros.
  setoid_rewrite Pr_S4_S4.
  rewrite G4_G5_uptobad.
  unfold Pr; apply mu_le_compat; [trivial | ].
  refine (ford_le_intro _); intro m'.
  unfold charfun, restr, EP, andP.
  case (S5 m'); case (E.eval_expr bad m'); trivial.
 Qed. 
 (** END [Pr_S4_S5] *)


 (** BEGIN [Pr_S5_S6] *)

 (** Definition of the inverter [B] *)
 Notation y' := (Var.Lvar (T.User group) 20).
 Notation x' := (Var.Lvar (T.User group) 21).

 Definition B_params : var_decl (Proc.targs B) := dcons _ y' (dnil _).

 Definition B_body := 
  [ 
    T <- E.Cnil T.Bool;
    while Elen T <! (qH +! 1%nat) do [t <$- {0,1}_p; T <- t |::| T];
    Y <- y';
    I <- Nil _;
    S <- Nil _;
    LH <- Nil _;
    rA <c- A with{}; 
    r <c- Hash with {Efst rA};
    x' <- Esnd rA |x| (S[{Efst rA}]^-1)
  ].

 Definition B_ret : E.expr (T.User group) := x'.

 (** The sixth game *)
 Definition G6 : cmd := Gf x y 4%positive.

 Definition E6 : env := add_decl E5 B B_params (refl_equal true) B_body B_ret.

 Definition S6 k := EP k (x =?= finv {Y}).

 Lemma EqAD_56 : Eq_adv_decl PrOrcl PrPriv E5 E6.
 Proof.
  unfold Eq_adv_decl, E6, E5, makeEnv, proc_params, proc_body, proc_res; intros.
  generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto;
   intro Heq;
   try (apply H; rewrite <- Heq; vm_compute; trivial; fail);
   apply H0; rewrite <- Heq; vm_compute; trivial.
 Qed.

 Lemma A_wf_6 : WFAdv PrOrcl PrPriv Gadv Gcomm E6 A. 
 Proof.
  unfold E6, E5.
  intros; apply WFAdv_trans with (5:=A_wf_E Hash5_body Sign5_body).
  unfold Eq_orcl_params; intros.
  unfold PrOrcl in H.
  rewrite PrSetP.add_spec in H; destruct H.
  inversion H; simpl.
  vm_compute; trivial.
  apply PrSet.singleton_complete in H; inversion H; simpl.
  vm_compute; trivial.
  apply EqAD_56.
  vm_compute; discriminate.
  vm_compute; discriminate.
 Qed.

 Definition iE5E6 :=
  add_adv_info_lossless EqAD_56 (A_wf_E _ _)
  (@A_lossless _)
  (@A_lossless _)
  (add_refl_info Sign
   (add_refl_info_O Hash
    (Vset.add mH (Vset.add S (Vset.add I (Vset.singleton LH))))
    Vset.empty Vset.empty
    (empty_info E5 E6))).

 Lemma EqAD_6 : Eq_adv_decl PrOrcl PrPriv E6 E6.
 Proof.  
  unfold Eq_adv_decl; auto.
 Qed.

 Definition iE6E6 :=
  add_adv_info_false EqAD_6 A_wf_6
  (add_refl_info_rm Sign 
    (Vset.add LS (Vset.singleton bad)) (Vset.add LS (Vset.singleton bad))
   (add_refl_info_O Hash
    (Vset.add mH (Vset.add I (Vset.add S (Vset.singleton LH))))
    (Vset.singleton bad) (Vset.singleton bad)
    (empty_info E6 E6))).

 Lemma EqObs_G5_G6 : 
  EqObs Gadv
  E6 G5
  E6 G6
  (Vset.add Y (Vset.singleton x)).
 Proof.
  unfold G6, Gf, G5, G4.
  sinline_r iE6E6 B.
  eqobs_tl iE6E6.
  swap_tac iE6E6.
  alloc_r y Y.
  ep; deadcode; eqobs_in.
 Qed. 
 
 Theorem Pr_S5_S6 : forall k (m:Mem.t k), 
  Pr E5 G5 m (@S5 k) <= Pr E6 G6 m (@S6 k).
 Proof.
  intros k m.
  apply Ole_eq_left with (Pr E6 G5 m (@S5 k)).
  apply EqObs_deno with Gadv
   (Vset.add x (Vset.add rA 
    (Vset.add S (Vset.add Y (Vset.add I (Vset.add T (Vset.singleton LS))))))). 
  eqobs_in iE5E6.
  intros; unfold charfun, restr, S5, S4, EP, andP.
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  trivial.
  trivial.

  unfold S5, S6, S4.
  apply equiv_deno_le with (1:=EqObs_G5_G6).
  intros; unfold charfun, restr, S6, S5, S4, EP, andP, andb, fone.

  rewrite depend_only_fv_expr_subset with (2:=H); 
   [ | unfold Vset.subset; trivial].
  case (@E.eval_expr _ T.Bool (x =?= finv {Y}) m2); trivial.
  trivial.
 Qed.

 Lemma final : forall k (m:Mem.t k), 
  Pr E1 G1 m (@S1 k) * p k * ([1-] p k)^(peval qS_poly k) <= Pr E6 G6 m (@S6 k).
 Proof.
  intros k m.
  rewrite Pr_S1_S2.
  rewrite Pr_S2_S3.
  rewrite Pr_S3_S4.
  rewrite Pr_S4_S5.
  rewrite Pr_S5_S6.
  trivial.
 Qed.
   
End ADVERSARY_AND_PROOF.
