(** * FDH.v: Exact security of the Full Domain Hash signature scheme *)

Set Implicit Arguments.

Require Import FDHsem.


(** [f] is a one-way permutation *)
Section ONE_WAYNESS.

 Variables x y : Var.var (T.User Bitstring).
 Variable Bname : positive.

 Notation B := (Proc.mkP Bname (T.User Bitstring :: nil) (T.User Bitstring)).
 
 Definition G_f :=
  [
   y <$- {0,1}^k;
   x <c- B with {y}
  ].

 Axiom f_oneway : forall (m:forall k, Mem.t k) E,
  x <> y ->
  Var.is_local x ->
  Var.is_local y ->
  lossless E (proc_body E B) ->
  PPT_proc E B ->
  negligible (fun k => Pr E G_f (m k) (EP k (x =?= apply_finv y))).
 
End ONE_WAYNESS.


(** Applying [f] to a uniformly distributed bitstring results in a uniformly
   distributed bitstring *)
Section RANDOM.

 Variables E1 E2 : env.
 Variables x y : Var.var (T.User Bitstring).

 Lemma apply_f_rand : forall P, 
  equiv P 
  E1 [y <$- {0,1}^k]
  E2 [x <$- {0,1}^k; y <- apply_f x]
  (req_mem_rel (Vset.singleton y) trueR).
 Proof.
  intros P.
  apply equiv_cons with (fun k (m1 m2:Mem.t k) => ap_finv (m1 y) = m2 x).
  eapply equiv_strengthen;
   [ | apply equiv_random_permut
    with (f:=fun k (m1 m2:Mem.t k) (v:T.interp k (T.User Bitstring)) => ap_f v)].
  simpl; red; intros; split.
  unfold permut_support; rewrite (PermutP_map (@eq _) (@ap_f k)).
  exact (f_perm k).
  intros; repeat rewrite Mem.get_upd_same; trivial.
  symmetry; apply f_spec.
  eapply equiv_strengthen; [ | apply equiv_assign_r].
  unfold req_mem_rel, kreq_mem, andR, trueR; intros.
  split; [ | trivial].
  intros t z Hz.
  Vset_mem_inversion Hz.
  rewrite <- Heq, Mem.get_upd_same; trivial.
  compute; rewrite <- H, <- finv_spec; trivial.
 Qed.

End RANDOM.


(** ** Notations *)
Open Scope positive_scope.


(** ** Global variables *)

(** *** Global variables shared by the adversary, the oracles and the game *)
Definition Gcomm := Vset.empty.

(** *** Global variables shared (and only visible) by the oracles and the game *)
Notation r   := (Var.Gvar (T.User Bitstring) 20).
Notation i   := (Var.Gvar T.Nat 21).
Notation j   := (Var.Gvar T.Nat 22).
Notation L   := (Var.Gvar (T.List (T.Pair Msg (T.User Bitstring))) 23).
Notation M  := (Var.Gvar (T.List (T.Pair T.Nat Msg)) 24).  
Notation P   := (Var.Gvar (T.List (T.Pair Msg (T.User Bitstring))) 25).
Notation S   := (Var.Gvar (T.List Msg) 26).
Notation bad := (Var.Gvar T.Bool 27).

(** *** Global variables for the adversary (there are none) *)
Definition Gadv := Vset.empty.


(** ** Local variables *)

(** *** Hash oracle *)
Notation mH   := (Var.Lvar Msg 41). 
Notation rH   := (Var.Lvar (T.User Bitstring) 42).
Notation s    := (Var.Lvar (T.User Bitstring) 43).

(** *** Signing oracle *)
Notation retS := (Var.Lvar (T.User Bitstring) 50). 
Notation mS   := (Var.Lvar Msg 51).
Notation rS   := (Var.Lvar (T.User Bitstring) 52).

(** *** Main *)
Notation retA := (Var.Lvar (T.Pair Msg (T.User Bitstring)) 60).
Notation madv := (Var.Lvar Msg 61).
Notation xadv := (Var.Lvar (T.User Bitstring) 62).
Notation h    := (Var.Lvar (T.User Bitstring) 63).
Notation y    := (Var.Lvar (T.User Bitstring) 64).


(** ** Procedures *)
Notation A    := (Proc.mkP 1 nil (T.Pair Msg (T.User Bitstring))).
Notation Hash := (Proc.mkP 2 (Msg :: nil) (T.User Bitstring)).
Notation Sign := (Proc.mkP 3 (Msg :: nil) (T.User Bitstring)). 
Notation B    := (Proc.mkP 4 (T.User Bitstring :: nil) (T.User Bitstring)).

Close Scope positive_scope.

Open Scope nat_scope.


(** Initial Game *)

Definition G1 : cmd :=
 [
  S <- Nil _;
  L <- Nil _;
  retA <c- A with {};
  madv <- Efst retA;
  xadv <- Esnd retA;
  h <c- Hash with {madv}
 ].

Definition Hash1_body : cmd :=
 [
  If !(mH in_dom L) _then 
  [
   rH <$- {0,1}^k; 
   L <- (mH | rH) |::| L
  ]
 ].

Definition Sign1_body :=
 [
  S <- mS |::| S;
  rS <c- Hash with {mS};
  retS <- apply_finv rS
 ].


(** ** Adversary and proof *)
Section ADVERSARY_AND_PROOF.

 (** Hypotheses
   1) The advesary performs at most a polynomial number of queries [q] to 
      the [Hash] and [Sign] oracles.

   3) The adversary runs in PPT as long as its oracles do so
 *)

 (** *** Specification of the adversary *)
 Definition A_params : var_decl (Proc.targs A) := dnil _.

 Variable A_body : cmd.

 (** The adversary returns a (message, signature) pair *)
 Variable A_ret : E.expr (T.Pair Msg (T.User Bitstring)).

 (** Adversary's own procedures *)
 Variable adv_env : env.
 
 Definition Hash_params : var_decl (Proc.targs Hash) := dcons _ mH (dnil _).
 Definition Hash_ret : E.expr (T.User Bitstring) := L[{mH}].

 Definition Sign_params : var_decl (Proc.targs Sign) := dcons _ mS (dnil _). 
 Definition Sign_ret : E.expr (T.User Bitstring) := retS.

 (** Environment constructor *)
 Definition makeEnv (Hash_body Sign_body:cmd) :=
  add_decl
  (add_decl
   (add_decl adv_env 
    Hash Hash_params (refl_equal true) Hash_body Hash_ret)
   Sign Sign_params (refl_equal true) Sign_body Sign_ret)
  A A_params (refl_equal true) A_body A_ret.

 (** The inital environment *)
 Definition E1 := makeEnv Hash1_body Sign1_body.

 (** The set of oracles, [Hash] and [Sign] *)
 Definition PrOrcl := 
  PrSet.add (BProc.mkP Sign) (PrSet.singleton (BProc.mkP Hash)).

 (** Private procedures, not accessible to the adversary *)
 Definition PrPriv := PrSet.singleton (BProc.mkP B).

 (** The adversary is well-formed in [E1], i.e. it only reads or writes 
    variables it has access to, and only calls oracles and its own procedures. *)
 Hypothesis A_wf : WFAdv PrOrcl PrPriv Gadv Gcomm E1 A.

 (** The adversary makes at most [q] queries to the [Hash] and [Sign] oracles. *)
 Hypothesis bound_queries : forall k (m:Mem.t k),
  range (fun m' => EP k (E.Eop (O.Olength _) {L} <=! (q +! 1)) m') ([[G1]] E1 m).

 (** The adversary runs in PPT as long as the hash and signing oracles do so *)
 Hypothesis A_PPT : forall E,
  Eq_adv_decl PrOrcl PrPriv E1 E ->
  (forall O, PrSet.mem O PrOrcl -> PPT_proc E (BProc.p_name O)) ->
  PPT_proc E A.

 (** The adversary is lossless as long as the hash and signing oracles are so *)
 Hypothesis A_lossless : forall E,   
  (forall O, PrSet.mem O PrOrcl -> 
   lossless E (proc_body E (BProc.p_name O))) -> 
  lossless E A_body.

 (** The adversary's procedures are the same in environments constructed 
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
  unfold E1; apply EqOP.
  unfold E1; apply EqAD.
  vm_compute; intro; discriminate.
  vm_compute; intro; discriminate.
 Qed. 


 (** BEGIN [Pr_G1_G2] *)

 (** The second game *)
 Definition G2 : cmd :=
  [
   j <$- [0..q];
   i <- 0;
   M <- Nil _;
   S <- Nil _;
   L <- Nil _;
   retA <c- A with {};
   madv <- Efst retA;
   xadv <- Esnd retA;
   h <c- Hash with {madv}
  ].
 
 Definition Hash2_body :=
  [
   If !(mH in_dom L) _then 
   [
    rH <$- {0,1}^k;
    L <- (mH | rH) |::| L;
    M <- (i | mH) |::| M;
    i <- i +! 1
   ]
  ].

 Definition Sign2_body := Sign1_body.

 Definition E2 := makeEnv Hash2_body Sign2_body.

 Notation p := (Var.Lvar (T.Pair Msg (T.User Bitstring)) 100). 
 Notation p' := (Var.Lvar (T.Pair T.Nat Msg) 101). 

 Definition I12 := 
  EP2 (E.Eop (O.Olength _) {L} =?= E.Eop (O.Olength _) {M}) /-\
  EP2 (i =?= E.Eop (O.Olength _) {L}) /-\
  EP2 (E.Eforall p' (Efst p' +! 1 <=! i) M) /-\
  EP2 (E.Eforall p (E.Eexists p' (M[{Efst p'}] =?= Efst p) M) L).

 Lemma dec_I12 : decMR I12.
 Proof.
  unfold I12; auto.
 Qed.

 Lemma dep_I12 : depend_only_rel I12
  Vset.empty
  (Vset.add i (Vset.add M (Vset.singleton L))).
 Proof.
  unfold depend_only_rel, I12, andR, EP2; intros.
  rewrite <- depend_only_fv_expr_subset with (2:=H0); unfold Vset.subset; trivial.
  rewrite <- depend_only_fv_expr_subset with (2:=H0); unfold Vset.subset; trivial.
  rewrite <- depend_only_fv_expr_subset with (2:=H0); unfold Vset.subset; trivial.
  rewrite <- depend_only_fv_expr_subset with (2:=H0); unfold Vset.subset; trivial.
 Qed.

 Definition eE1E2 : eq_inv_info I12 E1 E2.
  refine (@empty_inv_info I12 _ _ dep_I12 _ dec_I12 E1 E2).
  vm_compute; trivial.
 Defined.

 Lemma Hash1_Hash2 : 
  EqObsInv I12 (Vset.add mH (Vset.singleton L))
  E1 Hash1_body 
  E2 Hash2_body
  (Vset.add mH (Vset.singleton L)).
 Proof.
  clear; unfold I12, Hash2_body.
  cp_test (mH in_dom L).

  (* [mH in_dom L] *)
  eapply equiv_weaken; [ | apply equiv_nil].
  unfold andR; tauto.

  (* [!(mH in_dom L)] *) 
  eqobsrel_tail; unfold EP2, implMR, andR; 
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2; bprop; intros [Hreq [ [ H [H0 [H1 H2] ] ] [_ H3] ] ] v Hv.

  repeat rewrite nat_eqb_refl; simpl.
  rewrite leb_correct; [ | trivial].
  bprop; repeat split.

  trivial.
  rewrite (nat_eqb_true H0), plus_comm; apply nat_eqb_refl.
 
  intros (ii,m') Hin; simpl.
  generalize (H1 _ Hin).
  rewrite Mem.get_upd_same, Mem.get_upd_diff; [ | discriminate].
  simpl; intro Hle; apply leb_complete in Hle.
  apply leb_correct; set (x:=m2 i) in *; omega.

  intros (m,h) H4.
  generalize (H2 _ H4); bprop.
  intros [(ii, mm) [Hin Heq] ]; right.
  exists (ii, mm).
  generalize Heq Hin; clear Heq Hin.
  mem_upd_simpl.
  intros; split; [ trivial | simpl].
  case_eq (nat_eqb ii (m2 i)); intro H5; [simpl | exact Heq].
  generalize (H1 _ Hin).
  mem_upd_simpl.
  intro Hle; apply leb_complete in Hle.
  rewrite (nat_eqb_true H5) in Hle; simpl in Hle.
  exfalso; omega.
 Qed.

 Definition hE1E2 :=
  add_info Hash Vset.empty Vset.empty eE1E2 Hash1_Hash2.

 Lemma Sign1_Sign2 : 
  EqObsInv I12 (Vset.add mS (Vset.add L (Vset.singleton S)))
  E1 Sign1_body 
  E2 Sign2_body
  (Vset.add retS (Vset.add L (Vset.singleton S))).
 Proof.
  eqobs_in hE1E2.
 Qed.

 Definition iE1E2 :=
  add_adv_info_lossless 
  (EqAD _ _ _ _) 
  (A_wf_E _ _)
  (@A_lossless _)
  (@A_lossless _)
  (add_info Sign Vset.empty Vset.empty hE1E2 Sign1_Sign2).

 (** Input variables *)
 Definition I := Gadv.

 (** Output variables *)
 Definition O := 
  Vset.add S (Vset.add L (Vset.add h (Vset.add madv (Vset.singleton xadv)))).

 Lemma EqObs_G1_G2 : equiv (req_mem_rel I trueR) E1 G1 E2 G2 (req_mem_rel O I12).
 Proof.
  eqobs_tl iE1E2.  
  deadcode iE1E2.
  unfold I12; eqobsrel_tail; unfold implMR, req_mem_rel, andR, EP2;
   simpl; unfold O.eval_op; simpl; auto.
 Qed.

 Close Scope bool_scope.

 Theorem Pr_G1_G2 : forall k (m:Mem.t k), 
  Pr E1 G1 m (EP k ((h =?= apply_f xadv) && (madv not_in S))) == 
  Pr E2 G2 m (EP k ((h =?= apply_f xadv) && (madv not_in S))).
 Proof.
  intros; unfold G1, G2, Pr.
  apply equiv_deno with (1:=EqObs_G1_G2).
  intros m1 m2 [H H1]; unfold charfun, restr, EP.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
  unfold req_mem_rel, trueR, andR; auto.
 Qed.


 (* Input and output set of variables for the hash oracle from now on *)
 Definition I_H :=
  Vset.add mH (Vset.add j (Vset.add M (Vset.add i (Vset.singleton L)))).

 Definition O_H :=
  Vset.add mH (Vset.add M (Vset.add i (Vset.singleton L))).

 Definition iE2E2 :=
  add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _)
  (@A_lossless _)
  (@A_lossless _)
  (add_refl_info Sign
   (add_refl_info_O Hash
    O_H Vset.empty Vset.empty
    (empty_info E2 E2))).

 Lemma G2_bound_queries : forall k (m:Mem.t k),
  range (fun m => EP k (E.Eop (O.Olength _) {M} <=! (q +! 1)) m) ([[tail G2]] E2 m).
 Proof.
  intros; apply mu_range.
  match goal with 
  |- fmonot _ ?f == _  => set (F:=f) 
  end.
  assert (H:forall m1 m2, m1 =={Vset.singleton M} m2 -> F m1 == F m2).
  intros; unfold F, EP.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.

  transitivity (mu ([[G2]] E2 m) F).
  apply EqObs_deno with I (Vset.add M O).
  deadcode iE2E2; eqobs_in iE2E2.  
  intros m1 m2 Hreq; apply H.
  apply req_mem_weaken with (2:=Hreq); unfold Vset.subset; trivial.
  trivial.

  transitivity (mu ([[G1]] E1 m) 
   (charfun (E.eval_expr (E.Eop (O.Olength _) {L} <=! (q +! 1))))).
  symmetry.
  apply equiv_deno with (1:=EqObs_G1_G2); [ | trivial].  

  intros m1 m2; unfold req_mem_rel, I12, andR, EP2, F, EP, charfun, restr.
  intros [Hreq [Heq _] ].
  rewrite depend_only_fv_expr_subset with (2:=Hreq).
  simpl in Heq |- *; unfold O.eval_op in Heq |- *; simpl in Heq |- *.
  apply nat_eqb_true in Heq; rewrite Heq; trivial.
  unfold Vset.subset; trivial.
  unfold req_mem_rel, andR, trueR; auto.

  transitivity (mu ([[G1]] E1 m) (fone _)).
  apply (range_mu _ (bound_queries m)).
  refine (is_lossless_correct (refl1_info iE1E2) _ _ _); vm_compute; trivial.  
 Qed.

 Close Scope bool_scope.

 Lemma madv_is_hashed : forall k (m:Mem.t k),
  range (fun m' => exists i,
    i <= peval q_poly k /\ E.eval_expr ((madv =?= M[{i}]) && (i in_dom M)) m')%nat
  ([[tail G2]] E2 m).
 Proof.
  red; intros.
  rewrite <- (range_eq (G2_bound_queries m)
   (restr (fun m' => EP k (E.Eop (O.Olength _) {M} <=! (q +! 1)) m') f)).

  refine (mu_range    
   (EP k (E.Eexists p' ((madv =?= M[{Efst p'}]) && 
    (Efst p' +! 1 <=! E.Eop (O.Olength _) {M})) M))
   _ _ _ _).
  transitivity (mu ([[tail G2]] E1 m) (fone _));
   [ | refine (is_lossless_correct (refl1_info iE1E2) _ _ _); trivial].

  symmetry.
  apply equiv_deno with 
   (req_mem_rel Gadv trueR) 
   (req_mem_rel Gadv 
    (@EP2 (E.Eexists p' ((madv =?= M[{Efst p'}]) && 
                         (Efst p' +! 1 <=! E.Eop (O.Olength _) {M})) M))).
  change (tail G2) with
   ((rev (tail (rev (tail G2)))) ++ [ h <c- Hash with {madv} ]).
  apply equiv_app with (req_mem_rel (Vset.add L (Vset.singleton madv)) I12).
  eqobs_tl iE1E2.   
  unfold I12; eqobsrel_tail; simpl; unfold implMR; trivial.
  auto.
  inline iE1E2 Hash.  
  unfold req_mem_rel; apply decMR_and; [trivial | apply dec_I12].
  ep iE1E2.
  cp_test (madv in_dom L).
  
  (* [madv in_dom L] *)
  unfold I12; eqobsrel_tail; 
   unfold EP2, implMR; simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl;
   unfold andR, notR; intros k0 m1 m2; bprop.
  intros [Hreq [ [Hlen [Hlt1 [Hlt Hinv] ] ] ] ].
  intros [_ [(ms, r) [Hin Heq] ] ].
  generalize (Hinv (ms, r) Hin); bprop.
  rewrite Mem.get_upd_diff; [ | discriminate].
  intros [(ii,m') [H1 H2] ].  
  exists (ii, m'); split; [trivial | ].
  rewrite (nat_eqb_true Heq); simpl.
     
  rewrite Mem.get_upd_same in H2.
  repeat (rewrite Mem.get_upd_diff in H2; [ | discriminate]).
  rewrite Mem.get_upd_same in H2; simpl in H2.
  rewrite nat_eqb_sym; rewrite H2; simpl.
  rewrite <- (nat_eqb_true Hlen).
  generalize (Hlt _ H1).
  rewrite Mem.get_upd_same, Mem.get_upd_diff; [ | discriminate].
  simpl; intro Hle.
  apply leb_complete in Hle.
  apply leb_correct.
  rewrite (nat_eqb_true Hlt1) in  Hle; omega.

  unfold I12; eqobsrel_tail; 
   unfold EP2, implMR; simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl;
   unfold andR, notR; intros k0 m1 m2.
  repeat rewrite nat_eqb_refl; simpl.
  intros [Hreq [ [Heq [Heq' _] _] ] ]. 
  intros v Hv.
  bprop; left; apply leb_correct.
  rewrite (nat_eqb_true Heq'), (nat_eqb_true Heq).
  rewrite plus_comm; trivial.
  
  unfold EP, EP2; intros m1 m2 [_ H1]; rewrite H1; trivial.  
  unfold req_mem_rel, andR, trueR; auto.

  intro; unfold restr.
  case_eq (EP k (E.Eop (O.Olength _) {M} <=! (q +! 1)) x);
  intros; [ | trivial].
  apply H.
  generalize H0 H1; unfold EP; simpl; unfold O.eval_op; simpl; bprop.
  intros Hle [(ii,m') [Hin Heq] ].
  apply andb_prop in Heq.
  rewrite Mem.get_upd_same in Heq.
  repeat (rewrite Mem.get_upd_diff in Heq; [ | discriminate]).
  simpl in Heq; destruct Heq.
  exists ii; split; [ | trivial].
  apply leb_complete in H3; apply leb_complete in Hle; omega.
  bprop; split; [trivial | ].
  exists (ii, m'); split; [ trivial |].
  apply nat_eqb_refl.
  unfold EP, restr; intros.
  rewrite H0; trivial.
 Qed.

 Definition S3 k := 
  EP k ((h =?= apply_f xadv) && (madv not_in S)) [&&] EP k ((madv =?= M[{j}]) && (j in_dom M)).

 Close Scope nat_scope.

 (* REMARK: if we prove first that [M] is injective, then we can prove 
    the equality *)
 Lemma Pr_G2_le : forall k (m:Mem.t k),
  [1/]1+peval q_poly k * Pr E2 G2 m (EP k ((h =?= apply_f xadv) && (madv not_in S))) <=
  Pr E2 G2 m (@S3 k).
 Proof.
  intros k m; unfold G2.
  
  (* Replace [j] with value after initialization in the second event *)
  transitivity 
   (mu (sum_support (T.default k Msg) (E.eval_support [0..q] m))
     (fun v =>
      mu ([[tail G2]] E2 m)
        (fun m' =>
         charfun (EP k ((h =?= apply_f xadv) && (madv not_in S))) m' * 
         charfun (EP k ((madv =?= M [{v}]) && (v in_dom M))) m'))).
  
  (* Remove [j] initialization from first program *)
  rewrite sum_support_comm.
  unfold Pr.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  transitivity
   ([1/]1+peval q_poly k * 
    mu (sum_support (T.default k Msg) (E.eval_support [0..q] m))
     (fun v =>
      mu ([[tail G2]] E2 m)
       (fun m' => charfun (EP k ((h =?= apply_f xadv) && (madv not_in S))) m'))).
  Usimpl.
  apply mu_le_compat; [trivial | ].
  apply ford_le_intro; intro v.
  apply Oeq_le.
  apply EqObs_deno with Vset.empty (Vset.add M O).
  eqobs_in_tac iE2E2.
  intros m1 m2 Heq; unfold charfun, restr, EP.
  rewrite depend_only_fv_expr_subset with (2:=Heq); unfold Vset.subset; trivial.
  trivial.

  rewrite sum_support_comm.
  setoid_rewrite <- (mu_stable_mult _ ([1/]1+peval q_poly k)).
  unfold fmult.
  apply (range_le (madv_is_hashed m)).
  unfold EP; intros m' Hmadv.
  simpl in Hmadv; unfold O.eval_op in Hmadv; simpl in Hmadv.
  destruct Hmadv as [i [Hle Heq] ].
  apply andb_prop in Heq; destruct Heq as [Heq Hex].

  (* Restate [sum_support] as a finite sum *)
  rewrite sum_support_const; [ | discriminate ].
  unfold O.eval_op, T.app_op, O.interp_op, T.i_eqb, charfun, restr, EP, fone.

  unfold sum_support, mu; rewrite (sum_dom_finite 0%nat). 
  simpl pred; rewrite seq_length; simpl pred.
  
  transitivity
   ([1/]1+peval q_poly k *
    ((if EP k (((h =?= apply_f xadv) && (madv not_in S))) m' then 1 else 0) *
     (if EP k ((madv =?= M[{i}]) && (i in_dom M)) m' then 1 else 0))).
  unfold andP, EP; simpl; unfold O.eval_op; simpl.
  rewrite (nat_eqb_true Heq).
  rewrite Hex; unfold andb.
  rewrite nat_eqb_refl; Usimpl; trivial.

  apply (finite_sum_In
   (fun i:nat => [1/]1+peval q_poly k *
    ((if EP k ((h =?= apply_f xadv) && (madv not_in S)) m' then 1 else 0) *
     if EP k ((madv =?= M [{i}]) && (i in_dom M)) m' then 1 else 0))).
  unfold E.eval_support; apply le_In_seq.
  simpl; unfold O.eval_op; simpl; omega.
  
  (* Remove [j] initialization from second program *)
  unfold Pr.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  apply mu_le_compat; [trivial | ].
  refine (ford_le_intro _); intro v.
  apply Oeq_le.

  unfold G2, tail.
  symmetry.  
  compute_assertion Heq X (modify (refl1_info iE2E2) Vset.empty (tail G2)).
  rewrite (Modify_deno_elim (modify_correct (refl1_info iE2E2) _ _ Heq)); clear Heq.
  match eval red in X with
  | Some ?x => clear X; set (X:=x)
  end.
  apply EqObs_deno with Vset.empty (Vset.add M O).
  eqobs_in_tac iE2E2.
  intros m1 m2 H; unfold charfun, restr, EP, fone.
  set (m1' := m {!j <-- v!} {!X <<- m1!}).
  assert (Heq:m1' =={Vset.add M O} m2).
  apply req_mem_trans with m1; trivial.
  apply req_mem_weaken with X.
  unfold Vset.subset; trivial.
  unfold m1'; apply req_mem_update_mem_l.

  unfold S3, EP, andP.
  rewrite depend_only_fv_expr_subset with (2:=Heq); unfold Vset.subset; trivial.
  case (@E.eval_expr _ T.Bool ((h =?= apply_f xadv) && (madv not_in S)) m2);
  simpl; unfold O.eval_op; simpl.
  rewrite (Heq _ madv); trivial.
  rewrite (Heq _ M); trivial.
  unfold m1'; mem_upd_simpl.
  unfold m1'; rewrite update_mem_notin; [ | intro; discriminate].
  rewrite Mem.get_upd_same; trivial.
  unfold Vset.subset; trivial.
  Usimpl; trivial.
  Usimpl; trivial.
  trivial.
 Qed.

 Open Scope nat_scope.
 (** END [Pr_G1_G2] *)


 (** BEGIN [Pr_G2_G3] *)

 (** The third game *)
 Definition G3 : cmd :=
  [  
   j <$- [0..q];
   i <- 0;
   r <$- {0,1}^k;
   M <- Nil _;
   S <- Nil _;
   L <- Nil _;
   retA <c- A with {};
   madv <- Efst retA;
   xadv <- Esnd retA;
   h <c- Hash with {madv}
  ].

 Definition Hash3_body :=
  [
   If !(mH in_dom L) _then 
   [
    If (i =?= j) then 
     [
      rH <- r
     ]
    else [
     rH <$- {0,1}^k
    ];
    L <- (mH | rH) |::| L;
    M <- (i | mH) |::| M;
    i <- i +! 1
   ]
  ].

 Definition Sign3_body := Sign2_body.

 Definition E3 := makeEnv Hash3_body Sign3_body.

 (** * Lazy sampling *)

 Definition Hash2'_body :=
  [
   If (i <=! j) then (r <$- {0,1}^k) :: Hash3_body else Hash2_body
  ].

 Definition Hash3'_body :=
  [
   If (i <=! j) then Hash3_body else Hash2_body
  ].
  
 Definition E2' := makeEnv Hash2'_body Sign3_body.
 Definition E3' := makeEnv Hash3'_body Sign3_body.
 
 Lemma Hash2_Hash2' :
  EqObsInv trueR I_H
  E2  Hash2_body
  E2' Hash2'_body
  O_H.
 Proof.
  unfold Hash2_body, Hash2'_body, Hash3_body.
  cp_test (i <=! j); [ | eqobs_in].
  cp_test (mH in_dom L).
  deadcode; eqobs_in.
  cp_test (i =?= j).
  alloc_r r rH; ep; deadcode; eqobs_in.
  deadcode; eqobs_in.
 Qed.

 Lemma Hash3'_Hash3 :
  EqObsInv trueR 
  (Vset.add r I_H)
  E3' Hash3'_body
  E3  Hash3_body
  (Vset.add r O_H).
 Proof.
  unfold Hash3'_body, Hash3_body, Hash2_body.
  cp_test (i <=! j).
  eqobs_in.
  cp_test (mH in_dom L).
  eqobs_in.
  cp_test (i =?= j).
  apply equiv_False.
  unfold kreq_mem, andR, notR, EP1, EP2; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [ [ [_ [Hnle _] ] ] [Heq _] ];  elim Hnle.
  unfold is_true; apply leb_correct; rewrite (nat_eqb_true Heq); trivial.
  swap; eqobs_in.
 Qed.

 Definition mkCi Hash_body Hash'_body Sign_body Sign'_body C1 C2 nR nW :=
  let E  := makeEnv Hash_body Sign_body in
  let E' := makeEnv Hash'_body Sign'_body in
  let i0 := empty_context_info E E' C1 C2 nR nW in
  let iH := add_context_info E E' C1 C2 nR nW i0 _ Hash in
  let iS := add_context_info E E' C1 C2 nR nW iH _ Sign in
   add_adv_context_info E E' C1 C2 nR nW iS 
   PrOrcl PrPriv Gadv Gcomm (EqAD _ _ _ _) _ A (A_wf_E _ _).

 Definition iE2E2' :=
  add_adv_info_false (EqAD _ _ _ _) (A_wf_E _ _)
  (add_refl_info Sign
   (add_info Hash 
    Vset.empty (Vset.singleton r)
    (empty_info E2 E2')
    Hash2_Hash2')).

 Definition iE3'E3 :=
  add_adv_info_false (EqAD _ _ _ _) (A_wf_E _ _)
  (add_refl_info Sign
   (add_info Hash 
    Vset.empty Vset.empty
    (empty_info E3' E3)
    Hash3'_Hash3)).

 Definition iE3'E3' :=
  add_adv_info_false (EqAD _ _ _ _) (A_wf_E _ _)
  (add_refl_info Sign
   (add_refl_info_O Hash
    O_H Vset.empty Vset.empty
    (empty_info E3' E3'))).

 Lemma EqObs_G2_G3 : 
  EqObs Gadv 
  E2 G2 
  E3 G3 
  (Vset.add M (Vset.add j O)).
 Proof.
  apply EqObs_trans with E2 G3.
  unfold G2, G3, O.
  deadcode iE2E2; eqobs_in iE2E2.

  unfold G3.
  match goal with
  |- EqObs _ _ (?i1::?i2::?ir::?c) _ _ _ =>
     apply EqObs_trans with E2' ((i1::i2::nil) ++ (c ++ [If i <=! j _then [ir] ]))
  end.
  deadcode iE2E2'; eqobs_in iE2E2'.

  apply EqObs_trans with E3' G3; [ | eqobs_in iE3'E3 ].
  unfold G3.
  match goal with 
  |- EqObs _ _ _ _ (?i1::?i2::?i3::?c) _ =>
     change (i1::i2::i3::c) with ([i1; i2] ++ (i3::c));
     set (C:=c); set (ir:=i3)
  end.
  apply equiv_app with   
   (req_mem_rel (Vset.add i (Vset.add j Gadv)) (EP1 (i <=! j))).
  eqobsrel_tail; unfold implMR; simpl; unfold O.eval_op; split; trivial.

  apply equiv_trans_eq_mem_l with (P1:=EP1 (i <=! j)) (c1':=ir::C) (E1':=E3');
  [ | eqobs_in iE3'E3' | intros k m1 m2 [_ H2]; exact H2].
  
  apply (@equiv_context_true E2' E3' Hash3_body Hash2_body _ r ({0,1}^k) (i <=! j)).
  vm_compute; trivial.
  apply dcontext_correct with 
   (ci:=mkCi Hash2'_body Hash3'_body Sign2_body Sign2_body
    (If (i <=! j) then ((r <$- {0,1}^k) :: Hash3_body) else Hash2_body)
    (If (i <=! j) then Hash3_body else Hash2_body)
    (Vset.singleton r)
    (Vset.add r (Vset.union (fv_expr ((i <=! j))) (fv_distr {0,1}^k)))).  
  vm_compute; trivial.

  unfold Hash2_body.
  union_mod.
  apply proj1_MR.
  eqobsrel_tail; unfold implMR, andR, notR, EP1; 
   simpl; unfold O.eval_op; simpl.
  unfold Meq; intros k m1 m2 [Heq Hle]; subst; split; intros; trivial.
  destruct H.
  intro H2; elim Hle.
  unfold is_true; apply leb_correct.
  unfold is_true in H2; apply leb_complete in H2.
  apply le_trans with (2:=H2); auto with arith.

  unfold Hash3_body.  
  union_mod.
  apply proj1_MR.
  cp_test (mH in_dom L).  
  cp_test (i <=! j).
  deadcode; eqobs_in.
  eqobs_in.
  cp_test (i =?= j).
  ep; ep_eq_l (j +! 1%nat <=! j) false.
  unfold Meq; intros k m1 m2 H.
  simpl; unfold O.eval_op; simpl.
  apply leb_correct_conv; omega.
  eqobs_in.

  swap; eqobs_tl. 
  equiv_trans E2' 
   [
    M <- (i | mH) |::| M; 
    i <- i +! 1%nat; 
    r <$- {0,1}^k; 
    If i <=! j _then [r <$- {0,1}^k] 
   ].
  swap; eqobs_in.
  equiv_trans E2' 
   [
    M <- (i | mH) |::| M; 
    i <- i +! 1%nat; 
    r <$- {0,1}^k
   ]; [ | swap; eqobs_in].
  apply equiv_cons with (req_mem_rel O_H (~- EP1 (i =?= j) /-\ EP1 (i <=! j))).
  eqobsrel_tail; unfold implMR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  unfold Meq; intros k m1 m2 [_ [Hle [_ [H _] ] ] ]; split; trivial.
  apply equiv_cons with (req_mem_rel O_H (EP1 (i <=! j))).
  eqobsrel_tail; unfold implMR, EP1, EP2, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [Hneq Hle] ].  
  unfold is_true; apply leb_correct.
  unfold is_true in Hle; apply leb_complete in Hle; trivial.
  generalize (nat_eqb_spec (m1 i) (m1 j)).
  destruct (nat_eqb (m1 i) (m1 j)).
  elim Hneq; trivial.
  set (x:=m1 i) in *; set (y:=m1 j) in *; omega.

  ep_eq_l (i <=! j) true.
  intros k m1 m2 [_ H]; exact H.
  deadcode; eqobs_in.
 Qed.

 Close Scope nat_scope.

 Theorem Pr_G2_G3 : forall k (m:Mem.t k), 
  [1/]1+peval q_poly k * Pr E2 G2 m (EP k ((h =?= apply_f xadv) && (madv not_in S))) <= 
  Pr E3 G3 m (@S3 k).
 Proof.
  intros.
  rewrite Pr_G2_le.
  apply equiv_deno_le with (1:=EqObs_G2_G3); [ | trivial].
  intros m1 m2 H; unfold charfun, S3, restr, EP, andP.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
 Qed.

 Open Scope nat_scope.
 (** END [Pr_G2_G3] *)


 (** BEGIN [Pr_G3_G4] *)

 (** The fourth game *)
 Definition G4 : cmd := 
  [
   bad <- false;
   j <$- [0..q];
   i <- 0%nat;
   r <$- {0,1}^k;
   y <- r;
   M <- Nil _;
   S <- Nil _;
   L <- Nil _;
   P <- Nil _;
   retA <c- A with {};
   madv <- Efst retA;
   xadv <- Esnd retA;
   h <c- Hash with {madv}
  ].

 Definition Hash4_body :=
  [
   If !(mH in_dom L) _then [
    If (i =?= j) then [
     s <- bottom;
     rH <- r
    ]
    else [
     s <$- {0,1}^k;
     rH <- apply_f s
    ];
    P <- (mH | s) |::| P;
    L <- (mH | rH) |::| L;
    M <- (i | mH) |::| M;
    i <- i +! 1%nat
   ]
  ].

 Definition Sign4_body := Sign3_body.

 Definition E4 := makeEnv Hash4_body Sign4_body.


 Lemma Hash3_Hash4 : 
  EqObsInv trueR
  (Vset.add r I_H) 
  E3 Hash3_body 
  E4 Hash4_body 
  (Vset.add r O_H).
 Proof.
  unfold Hash3_body, Hash4_body.
  cp_test (!(mH in_dom L)).
  eqobs_tl.
  cp_test (i =?= j); deadcode.
  eqobs_in.
  apply equiv_strengthen with (kreq_mem (Vset.add r I_H)).
  unfold andR; intros; tauto.
  union_mod.
  unfold_eqobs.
  rewrite <- (req_mem_rel_trueR (Vset.singleton rH)).
  apply apply_f_rand.
  eqobs_in.
 Qed.

 Definition iE3E4 :=
  add_adv_info_false (EqAD _ _ _ _) (A_wf_E _ _)
  (add_refl_info Sign
   (add_info Hash 
    Vset.empty (Vset.add P (Vset.singleton s))
    (empty_info E3 E4)
    Hash3_Hash4)).

 Lemma EqObs_G3_G4 : EqObs I E3 G3 E4 G4 (Vset.add j (Vset.add M O)).
 Proof.
  deadcode iE3E4.
  eqobs_in iE3E4.
 Qed.

 Theorem Pr_G3_G4 : forall k (m:Mem.t k), 
  Pr E3 G3 m (@S3 k) == Pr E4 G4 m (@S3 k).
 Proof.
  intros; unfold Pr.
  apply EqObs_deno with (1:=EqObs_G3_G4).  
  intros m1 m2 H; unfold S3, charfun, restr, EP, andP.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
  trivial.
 Qed.
 (** END [Pr_G3_G4] *)


 (** BEGIN [Pr_G4_G4'] *)
 Definition Sign4'_body :=  
 [
  S <- mS |::| S;
  rS <c- Hash with {mS};
  If (j +! 1%nat <=! i) && (mS =?= M[{j}]) then 
   [
    bad <- true;
    retS <- apply_finv rS
   ]
  else 
   [
    retS <- apply_finv rS       
   ]
 ]. 

 Definition E4' := makeEnv Hash4_body Sign4'_body.

 (* Input and output set of variables for the sign oracle from now on *)
 Definition I_S := 
  Vset.add M (Vset.add i (Vset.add mS (Vset.add S (Vset.singleton L)))).

 Definition O_S := 
  Vset.add M (Vset.add i (Vset.add mS (Vset.add retS (Vset.add S (Vset.singleton L))))).

 Definition iE4E4' :=
  add_adv_info_false (EqAD _ _ _ _) (A_wf_E _ _)
  (add_refl_info_O Sign
   O_S Vset.empty Vset.empty
   (add_refl_info_O Hash
    O_H Vset.empty Vset.empty
    (empty_info E4 E4'))).

 Lemma EqObs_G4_G4' : EqObs I E4 G4 E4' G4 (Vset.add j (Vset.add M O)).
 Proof.
  eqobs_in iE4E4'.  
 Qed.

 Theorem Pr_G4_G4' : forall k (m:Mem.t k), 
  Pr E4 G4 m (@S3 k) == Pr E4' G4 m (@S3 k).
 Proof.
  intros; unfold Pr.
  apply EqObs_deno with (1:=EqObs_G4_G4').
  intros m1 m2 H; unfold S3, charfun, restr, EP, andP.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
  trivial.
 Qed.
 (** END [Pr_G4_G4'] *)


 (** BEGIN [Pr_G4_G5] *)
 Definition G5 := G4. 

 Definition Hash5_body := Hash4_body.

 Definition Sign5'_body :=
  [
   S <- mS |::| S;
   rS <c- Hash with {mS};
   If (j +! 1%nat <=! i) && (mS =?= M[{j}]) then 
    [
     bad <- true;
     retS <- P[{mS}]
    ]
   else 
    [
     retS <- apply_finv rS
    ]
  ].

 Definition E5' := makeEnv Hash5_body Sign5'_body.

 Definition upto_info4'5' : upto_info bad E4' E5' :=
  add_adv_upto_info
  (add_upto_info
   (add_upto_info 
    (empty_upto_info bad E4' E5') Hash) Sign)
  (EqAD _ _ _ _)
  (EqOP _ _ _ _)   
  (A_wf_E Hash4_body Sign4'_body). 

 (* REMARK: this holds because [bad] is a failure event and [G4'] and [G5'] are 
    syntactically equal up to the raise of this event *)
 Lemma Pr_G4'_G5' : forall k (m:Mem.t k),
  Pr E4' G4 m (@S3 k [&&] negP (EP k bad)) ==
  Pr E5' G4 m (@S3 k [&&] negP (EP k bad)).
 Proof.
  intros; unfold G4, Pr.  
  setoid_rewrite deno_cons_elim.
  setoid_rewrite Mlet_simpl.
  setoid_rewrite deno_assign_elim.
  apply upto_bad_and_neg with upto_info4'5'; vm_compute; trivial.
 Qed.


 Notation m' := (Var.Lvar Msg 102). 

 Definition inv4 := 
  EP1 ((i <=! j) ==> !bad) /-\
  EP1 ((M[{j}] not_in S) ==> !bad).

 Lemma Hash4'_Hash4'  :
  EqObsInv inv4
  (Vset.add r I_H)
  E4' Hash4_body 
  E4' Hash4_body
  (Vset.add r O_H).
 Proof.
  clear; unfold Hash4_body.
  cp_test (mH in_dom L).

  (* [mH in_dom L] *)
  eqobsrel_tail; unfold inv4, EP1, implMR, andR; 
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2; bprop; intros.
  decompose [and] H; auto.

  (* [!(mH in_dom L)] *)
  cp_test (i =?= j).
  
  unfold inv4; eqobsrel_tail; unfold EP1, implMR, notR, andR; 
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2.
  rewrite nat_eqb_refl; simpl; bprop.
  intros [Hreq H]; decompose [and] H.
  clear H A_body A_ret adv_env.
  split; intros.
  apply H2; apply leb_complete in H; exfalso; omega.
  apply H2; apply nat_eqb_true in H0; rewrite H0; apply leb_correct; trivial.

  unfold inv4; eqobsrel_tail; unfold EP1, implMR, notR, andR; 
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2; bprop; intros; bprop.
  decompose [and] H.
  clear H H8 A_body A_ret adv_env.
  split; intros.

  apply H2; apply leb_correct; apply leb_complete in H.
  apply le_trans with (2:=H); auto with arith.

  apply H5.
  case_eq (nat_eqb (m1 i) (m1 j)); intro Heq.
  rewrite Heq in H3; elim H3; trivial.
  rewrite nat_eqb_sym in Heq.
  rewrite Heq in H; trivial.
 Qed.

 Lemma dec_inv4 : decMR inv4.
 Proof.
  unfold inv4; auto.
 Qed.

 Lemma dep_inv4 : depend_only_rel inv4
  (Vset.add bad (Vset.add i (Vset.add j (Vset.add M (Vset.add L (Vset.singleton S))))))
  Vset.empty.
 Proof.
  unfold depend_only_rel, inv4, andR, EP1; intros.
  apply req_mem_sym in H.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
 Qed.

 Definition eE4'E4' : eq_inv_info inv4 E4' E4'.
  refine (@empty_inv_info _ _ _ dep_inv4 _ dec_inv4 _ _).
  vm_compute; trivial.
 Defined.
  
 Definition hE4'E4' :=
  add_info Hash Vset.empty Vset.empty eE4'E4' Hash4'_Hash4'.

 Lemma Sign4'_Sign4' : 
  EqObsInv inv4
  (Vset.add r (Vset.add j I_S))
  E4' Sign4'_body
  E4' Sign4'_body
  (Vset.add r (Vset.add j O_S)).
 Proof.
  clear; unfold Sign4'_body.  
  inline hE4'E4' Hash.
  unfold req_mem_rel; auto using dec_inv4.
  ep hE4'E4'.
  cp_test (mS in_dom L).  

  (* [mS in_dom L] *)  
  cp_test (mS =?= M[{j}]).

  (* [mS =?= M[{j}]] *)  
  unfold inv4; eqobsrel_tail; unfold req_mem_rel, kreq_mem, EP1, implMR, notR, andR; 
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2; rewrite nat_eqb_refl; simpl; bprop.
  intro H; decompose [and] H.
  clear H H7 A_body A_ret adv_env.
  split.
  
  intros [Hle _]; split.
  intro H; apply leb_complete in H; apply leb_complete in Hle.
  exfalso; omega.  
  trivial.

  intros [Hle _]; split; [ trivial | intro; discriminate ].
  
  (* [!(mS =?= M[{j}])] *)    
  unfold inv4; eqobsrel_tail; unfold EP1, implMR, notR, andR; 
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2; bprop.
  intro H; decompose [and] H.
  clear H H7 A_body A_ret adv_env.
  repeat split; auto.

  (* [!(mS in_dom L)] *)
  cp_test (i =?= j).
  
  unfold inv4; eqobsrel_tail; unfold req_mem_rel, kreq_mem, EP1, implMR, notR, andR. 
  simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2; repeat (rewrite nat_eqb_refl; simpl); bprop.
  intros [Hreq H]; decompose [and] H.
  clear H H6 A_body A_ret adv_env. 
  repeat split; intros.
  apply leb_complete in H4; exfalso; omega.
  trivial.
  apply H2.
  apply nat_eqb_true in H0; rewrite H0; apply leb_correct; trivial.
  discriminate.

  (* [!(i =?= j)] *)
  unfold inv4; eqobsrel_tail; unfold EP1, implMR, notR, andR; 
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2; bprop; intros; bprop.
  decompose [and] H.
  clear H H8 A_body A_ret adv_env.
  repeat split; intros.
  
  destruct H as [ [Hle Heq] _].
  apply leb_complete in Hle; apply leb_complete in H6; exfalso; omega.

  destruct H as [ [Hle Heq] _].
  elim H6; left; rewrite nat_eqb_sym; trivial.

  apply H2; apply leb_correct; apply leb_complete in H6.
  apply le_trans with (2:=H6); auto with arith.
  
  destruct H as [H _].
  apply H5.
  case_eq (nat_eqb (m1 i) (m1 j)); intro Heq.
  rewrite Heq in H3; elim H3; trivial.
  rewrite nat_eqb_sym in Heq.
  rewrite Heq in H, H6; trivial.
  intros [x [Hin Hx] ].
  elim H6; right; exists x; split; trivial.
 Qed.

 Definition iE4'E4'inv :=
  add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _)
   (@A_lossless _)
   (@A_lossless _)
   (add_info Sign Vset.empty Vset.empty hE4'E4' Sign4'_Sign4').
 
 (** G4' satisfies the postcondition [M[{j}] not_in S [=>] ! bad] *)
 Lemma G4'_post : forall k (m:Mem.t k), 
  range (implP (EP k (M[{j}] not_in S)) (negP (EP k bad))) ([[G4]] E4' m).
 Proof.
  intros k m; apply mu_range.
  transitivity (mu ([[G4]] E4' m) (fone _));
   [ | refine (is_lossless_correct (refl1_info iE4'E4'inv) _ _ _); trivial].
  apply equiv_deno with 
   (req_mem_rel Gadv trueR) 
   (req_mem_rel Gadv inv4).

  eqobs_tl iE4'E4'inv.
  unfold inv4; eqobsrel_tail; unfold implMR; simpl; auto.
  unfold req_mem_rel, kreq_mem, inv4, EP1, EP, negP, implP, fone, andR.
  intros m1 m2 [Hreq [_ H] ].  
  generalize H.  
  simpl; unfold O.eval_op; simpl.
  case (existsb (nat_eqb (O.assoc (nat_eqb (m1 j)) 0%nat (m1 M))) (m1 S)).
  trivial.
  unfold impb; simpl; intro Heq; rewrite Heq; trivial.

  unfold req_mem_rel, trueR, andR; auto. 
 Qed.

 Definition iE4'E4' :=
  add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _)
  (@A_lossless _)
  (@A_lossless _)
  (add_refl_info_O Sign
   O_S Vset.empty Vset.empty
   (add_refl_info_O Hash
    O_H Vset.empty Vset.empty
    (empty_info E4' E4'))).

 Close Scope nat_scope.

 Theorem Pr_G4_G5 : forall k (m:Mem.t k), 
  Pr E4' G4 m (@S3 k) <= Pr E5' G5 m (@S3 k).
 Proof.
  intros; clear.
  apply Ole_eq_left with (Pr E4' G4 m (@S3 k [&&] negP (EP k bad))).
  symmetry.

  (* Remove [!bad] using the fact that  [S3 [=>] !bad] *)

  (* Eliminate [!bad] because [M[{j}] not_in S [=>] !bad] is a postcondition *)
  unfold Pr; apply (range_eq (G4'_post m)); intro m'.
  unfold S3, S3, charfun, restr, EP, implP, andP, negP, negb, andb, implb, fone.
  assert (H:@E.eval_expr _ T.Bool ((h =?= apply_f xadv) && (madv not_in S)) m' = 
           (@E.eval_expr _ T.Bool (h =?= apply_f xadv) m' && @E.eval_expr _ T.Bool (madv not_in S) m')%bool) by trivial.
  rewrite H; clear H.
  case_eq (@E.eval_expr _ T.Bool ((madv =?= M[{j}]) && (j in_dom M)) m'); intro Heq.  
  assert (H:@E.eval_expr _ T.Bool (M [{j}] not_in S) m' = 
            @E.eval_expr _ T.Bool (madv not_in S) m').
  simpl in Heq |- *; unfold O.eval_op in Heq |- *; simpl in Heq |- *.
  apply andb_prop in Heq; destruct Heq as [Heq H].
  rewrite (nat_eqb_true Heq); trivial.
  rewrite H; clear H.

  case (@E.eval_expr _ T.Bool (M[{j}] not_in S) m');
  case (@E.eval_expr _ T.Bool (h =?= apply_f xadv) m'); 
  case (@E.eval_expr _ T.Bool (madv not_in S) m');
  case (@E.eval_expr _ T.Bool bad m'); trivial;
  intro; try discriminate.

  case (@E.eval_expr _ T.Bool (M[{j}] not_in S) m');
  case (@E.eval_expr _ T.Bool (h =?= apply_f xadv) m'); 
  case (@E.eval_expr _ T.Bool (madv not_in S) m');
  case (@E.eval_expr _ T.Bool bad m'); trivial;
  intro; try discriminate.

  (* Apply G4'_G5'_uptobad to conclude *)
  rewrite Pr_G4'_G5'.
  unfold Pr; apply mu_le_compat; [trivial | ].
  refine (ford_le_intro _); intro m'.
  unfold charfun, restr, EP, andP.
  case (S3 m'); case (E.eval_expr bad m'); trivial.
 Qed.

 Open Scope nat_scope.
 (** END [Pr_G4_G5] *)


 (** BEGIN [Pr_G5'_G5] *)

 Definition Sign5_body :=
  [
   S <- mS |::| S;
   rS <c- Hash with {mS};
   retS <- P[{mS}]
  ].
 
 Definition E5 := makeEnv Hash5_body Sign5_body.

 Close Scope bool_scope.

 Definition inv5' : mem_rel :=
  EP1 ((j in_dom M) ==> !(i <=! j)) /-\
  EP1 (
   E.Eforall p 
   ((Efst p in_range M) && 
    ( ((!(j in_dom M)) || (!(Efst p =?= M [{j}]))) ==>
      (P[{Efst p}] =?= apply_finv (L[{Efst p}])) )) L).

 Lemma EqObs_H_inv_E5'E5 : 
  EqObsInv inv5' 
  (Vset.add r (Vset.add mH (Vset.add i (Vset.add j (Vset.add P (Vset.add L 
   (Vset.singleton M)))))))
  E5' Hash4_body 
  E5  Hash4_body
  (Vset.add mH (Vset.add i (Vset.add P (Vset.add L (Vset.singleton M))))).
 Proof.
  clear; unfold Hash4_body.
  cp_test (mH in_dom L).

  (* [mH in_dom L] *)
  eapply equiv_weaken; [ | apply equiv_nil].
  unfold req_mem_rel, kreq_mem, andR; intros.
  intuition.
  apply req_mem_weaken with (2:=H); unfold Vset.subset; trivial.

  (* [!(mH in_dom L)] *)
  cp_test (i =?= j).

  (* [i =?= j] *)
  unfold inv5'; eqobsrel_tail; unfold EP1, andR, notR, implMR; 
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2.
  repeat rewrite nat_eqb_refl; simpl.
  bprop; intro H; decompose [and] H.
  clear H H6 H7; repeat split.

  intros _ Hle; unfold is_true in Hle; apply leb_complete in Hle; omega.  

  intros (m, r) Hin; simpl.
  bprop; repeat split.
  generalize (H4 (m,r) Hin); clear H4.
  rewrite Mem.get_upd_same, Mem.get_upd_diff; [simpl | discriminate].
  bprop.
  intros [ [(m',r') [? ?] ] ?]; right; exists (m',r'); auto.

  intro H; rewrite not_is_true_false in H; rewrite H.
  generalize (H4 (m,r) Hin); clear H4.
  rewrite Mem.get_upd_same.
  repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  bprop.
  intros [ [(m',r') [? ?] ] ?].
  apply H6; clear H6.
  left; intro.
  elim H1; trivial.
  unfold is_true; apply leb_correct.
  rewrite (nat_eqb_true H2); trivial.
  
  (* [!(i =?= j)] *)
  unfold inv5'; eqobsrel_tail; unfold EP1, andR, implMR, notR; 
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2.
  rewrite nat_eqb_sym, nat_eqb_refl; simpl; intros H v Hv; decompose [and] H.
  rewrite not_is_true_false in H2; rewrite H2; simpl.
  clear H H6 H7; bprop.
  autorewrite with Ris_true in H1, H3, H4.
  bprop; repeat split.
  intros H Hle.
  elim (H1 H).
  unfold is_true in Hle; apply leb_complete in Hle.
  unfold is_true; apply leb_correct.
  apply le_trans with (2:=Hle); auto with arith.

  intros; simpl; intros.
  rewrite <- f_spec; rewrite UTi_eqb_refl; trivial.

  intros (m, r) Hin; simpl; bprop.
  split.
  generalize (H4 (m,r) Hin); clear H4.
  bprop.
  rewrite Mem.get_upd_same, Mem.get_upd_diff; [simpl | discriminate].
  intros [ [(l,r') [? ?] ] ?].
  right; exists (l,r'); auto.

  intros.
  case_eq (nat_eqb m (m1 mH)); intro.
  simpl; intros; rewrite <- f_spec; rewrite UTi_eqb_refl; trivial.
  generalize (H4 (m,r) Hin); clear H4.
  bprop.
  mem_upd_simpl.
  intros; tauto.
 Qed.

 Lemma dep_inv5' : depend_only_rel inv5'
  (Vset.add j (Vset.add M (Vset.add i (Vset.add P (Vset.singleton L)))))
  Vset.empty.
 Proof.
  unfold depend_only_rel, inv5', EP1, andR; intros.
  apply req_mem_sym in H.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
 Qed.

 Lemma dec_inv5' : decMR inv5'.
 Proof.
  unfold inv5'; auto.
 Qed.

 Definition eE5'E5 : eq_inv_info inv5' E5' E5.
  refine (@empty_inv_info inv5' _ _ dep_inv5' _ dec_inv5' E5' E5).
  vm_compute; trivial.
 Defined.

 Definition iE5'E5_H :=
  add_info Hash Vset.empty Vset.empty eE5'E5 EqObs_H_inv_E5'E5.

 Lemma EqObs_S_E5'E5 : 
  EqObsInv inv5'
  (Vset.add P (Vset.add r (Vset.add j I_S)))
  E5' Sign5'_body
  E5  Sign5_body
  (Vset.add P (Vset.add r (Vset.add j O_S))).
 Proof.
  clear; unfold Sign5'_body, Sign5_body.
  inline iE5'E5_H Hash.
  unfold inv5'; auto.
  deadcode iE5'E5_H.
  ep iE5'E5_H.
  eqobs_hd iE5'E5_H.
  cp_test (mS in_dom L).

  (* [mS in_dom L] *)
  deadcode iE5'E5_H.
  cp_test (mS =?= M[{j}]).

  ep_eq_l (M[{j}]) mS.
  unfold req_mem_rel, EP1, andR, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [ _ [Hn _] ].  
  symmetry; apply (nat_eqb_true Hn).
  ep_eq_r (M[{j}]) mS.
  unfold req_mem_rel, EP1, andR, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [ [ [Hreq _] _] [Hn _] ].  
  rewrite <- (Hreq _ mS); trivial.
  rewrite <- (Hreq _ M); trivial.
  rewrite <- (Hreq _ j); trivial.
  symmetry; apply (nat_eqb_true Hn).

  cp_test ((j +! 1%nat) <=! i).

  eqobs_in iE5'E5_H.
  rewrite <- andR_comm, andR_assoc; apply proj1_MR.

  ep_eq_l (apply_finv (L[{mS}])) (P[{mS}]).    
  unfold req_mem_rel, inv5', EP1, andR, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [ [ [ [_ [H1 H2] ] [Hn _] ] [Heq _] ] [Hnle _] ].

  unfold is_true in Hn.
  rewrite existsb_exists in Hn.
  autorewrite with Ris_true in H1, H2.
  destruct Hn as [x [Hin Hx] ].
  generalize (H2 x Hin); clear H2.
  bprop.
  intros [H3 H4].
  symmetry.
  match goal with
  |- ?A = ?B => generalize (UT.i_eqb_spec A B)
  end.  
  rewrite Mem.get_upd_same in H4.
  repeat (rewrite Mem.get_upd_diff in H4; [ | discriminate]).
  rewrite (nat_eqb_true Hx).
  case_eq (existsb (fun p : nat * nat => nat_eqb (m1 j) (fst p)) (m1 M)); intro Hex.
  rewrite existsb_exists in Hex.
  assert (Hn:=H1 Hex).
  rewrite not_is_true_false in Hn, Hnle.
  apply leb_complete_conv in Hn.
  apply leb_complete_conv in Hnle.
  exfalso; omega.

  rewrite H4; trivial.
  left; intro.
  rewrite <- is_true_existsb, Hex in H; discriminate.

  eqobs_in iE5'E5_H; rewrite <- andR_comm, andR_assoc; apply proj1_MR.
  ep_eq_l (apply_finv (L[{mS}])) (P[{mS}]).
  unfold req_mem_rel, inv5', EP1, andR, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [ [ [_ [_ H] ] [Hin _] ] [Hneq _] ].
  autorewrite with Ris_true in H.

  case_eq (existsb (fun p => nat_eqb (m1 mS) (fst p)) (m1 L)).
  rewrite existsb_exists; clear Hin; intros [p [Hin Heq] ].
  apply (@nat_eqb_true (m1 mS) (fst p)) in Heq; rewrite Heq in *; clear Heq.
  generalize (H p Hin).
  repeat rewrite Mem.get_upd_same.
  repeat (rewrite Mem.get_upd_diff; [ | discriminate]); unfold O.eval_op; simpl.
  bprop.
  clear H; intros [_ H].
  symmetry.
  match goal with
  |- ?A = ?B => generalize (UT.i_eqb_spec A B); rewrite H; auto
  end.  
  intro Hex; rewrite Hex in Hin; discriminate.

  eqobs_in iE5'E5_H; rewrite <- andR_comm, andR_assoc; apply proj1_MR.

  (* [!(mS in_dom L)] *)
  cp_test (i =?= j); deadcode iE5'E5_H.

  (* [i =?= j] *)
  ep.
  match goal with
  |- equiv _ _ (?i1::?i2::?i3::?i4::?c1) _ (?j1::?j2::?j3::?j4::?c2) _ =>
     change (i1::i2::i3::i4::c1) with ([i1; i2; i3; i4] ++ c1); 
     change (j1::j2::j3::j4::c2) with ([j1; j2; j3; j4] ++ c2)
  end.
  apply equiv_app with      
   (req_mem_rel (Vset.add P (Vset.add mH (Vset.add r (Vset.add j I_S))))
    (inv5' /-\ EP1 (mS =?= M[{j}]))).
  unfold inv5'; eqobsrel_tail; unfold EP1, andR, implMR, kreq_mem;
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2 [Hreq [H0 [ [H1 _] [H2 _] ] ] ].
  repeat rewrite nat_eqb_refl; simpl.
  autorewrite with Ris_true in H0.
  bprop; repeat split.
  intros _ Hle; unfold is_true in Hle; apply leb_complete in Hle; omega.  
  intros (m, r) Hin; simpl.
  bprop; repeat split.
  destruct H0 as [_ H0]; generalize (H0 (m,r) Hin); clear H0.
  rewrite Mem.get_upd_same, Mem.get_upd_diff; [simpl | discriminate].
  bprop.
  intros [ [(m',r') [? ?] ] ?]; right; exists (m',r'); auto.

  intro H; rewrite not_is_true_false in H; rewrite H.
  destruct H0 as [Hn H0].
  generalize (H0 (m,r) Hin); clear H0.
  rewrite Mem.get_upd_same.
  repeat (rewrite Mem.get_upd_diff; [ | discriminate]).
  bprop.
  intros [ [(m',r') [? ?] ] ?].
  apply H4; clear H4.
  left; intro.
  elim Hn; trivial.
  unfold is_true; apply leb_correct.
  rewrite (nat_eqb_true H2); trivial.

  ep_eq_l (M[{j}]) mS.
  unfold req_mem_rel, andR, EP1; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [_ [_ H] ].
  rewrite (nat_eqb_true H); trivial.
  eqobs_in iE5'E5_H.
  unfold implMR, andR; intros; tauto.

  (* [!(i =?= j)] *)
  match goal with
  |- equiv _ _ (?i1::?i2::?i3::?i4::?i5::?c1) _ (?j1::?j2::?j3::?j4::?j5::?c2) _ =>
     change (i1::i2::i3::i4::i5::c1) with ([i1; i2; i3; i4; i5] ++ c1); 
     change (j1::j2::j3::j4::j5::c2) with ([j1; j2; j3; j4; j5] ++ c2)
  end.
  apply equiv_app with      
   (req_mem_rel (Vset.add P (Vset.add mH (Vset.add r (Vset.add j I_S))))
    (inv5' /-\ 
     EP1 (((!(j in_dom M)) || (!(mS =?= M[{j}]))) ==> (P[{mS}] =?= apply_finv (L[{mS}]))))).
  unfold inv5'; eqobsrel_tail; unfold EP1, andR, implMR, notR, kreq_mem;
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2 [Hreq [H0 [ [H1 _] [H2 _] ] ] ] v Hin.
  repeat rewrite nat_eqb_refl; simpl.
  autorewrite with Ris_true in H0, H1, H2.
  bprop; repeat split.
  intro H; destruct H.
  rewrite nat_eqb_sym in H; tauto.
  destruct H0.
  intro Hle.
  elim (H0 H).
  unfold is_true in Hle; apply leb_complete in Hle.
  unfold is_true; apply leb_correct.
  apply le_trans with (2:=Hle); auto with arith.

  rewrite not_is_true_false, nat_eqb_sym in H2; rewrite H2.
  intros; simpl; rewrite <- f_spec; rewrite UTi_eqb_refl; trivial.
  
  intros (m, r) Hmr; simpl; bprop.
  split.
  destruct H0 as [_ H0].
  generalize (H0 (m,r) Hmr); clear H0.
  bprop.
  mem_upd_simpl.
  intros [ [(l,r') [? ?] ] ?].
  right; exists (l,r'); auto.
  
  intros; case_eq (nat_eqb m (m1 mS)); intro.
  simpl; intros; rewrite <- f_spec; rewrite UTi_eqb_refl; trivial.

  destruct H0 as [_ H0].
  generalize (H0 (m,r) Hmr); clear H0.
  bprop.
  mem_upd_simpl.
  intros [ [(l,r') [? ?] ] ?].
  apply H5; clear H5.
  destruct H; auto.  
  rewrite not_is_true_false, nat_eqb_sym in H2; rewrite H2 in H.
  auto.

  intros; simpl; rewrite <- f_spec; rewrite UTi_eqb_refl; trivial.
  cp_test (mS =?= M[{j}]).

  ep_eq_l (M[{j}]) mS.
  unfold req_mem_rel, EP1, andR, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [ _ [Hn _] ].  
  symmetry; apply (nat_eqb_true Hn).
  ep_eq_r (M[{j}]) mS.
  unfold req_mem_rel, EP1, andR, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [ [Hreq _] [Hn _] ].  
  rewrite <- (Hreq _ mS); trivial.
  rewrite <- (Hreq _ M); trivial.
  rewrite <- (Hreq _ j); trivial.
  symmetry; apply (nat_eqb_true Hn).

  cp_test ((j +! 1%nat) <=! i).

  eqobs_in iE5'E5_H.  
  rewrite andR_comm, andR_assoc, andR_assoc; apply proj1_MR.

  ep_eq_l (apply_finv (L[{mS}])) (P[{mS}]).
  unfold req_mem_rel, EP1, andR, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [ [ [_ [Hinv H] ] [Heq _] ] [Hn _] ].  
  rewrite Heq in H; simpl in H.
  autorewrite with Ris_true in H.  
  symmetry.
  match goal with
  |- ?A = ?B => generalize (UT.i_eqb_spec A B); rewrite H; trivial
  end.
  clear H; left; intro H.
  
  destruct Hinv as [Hdom _]; unfold EP1 in Hdom.
  simpl in Hdom; unfold O.eval_op in Hdom; simpl in Hdom.
  autorewrite with Ris_true in Hdom.  
  assert (Hnle:=Hdom H).
  rewrite not_is_true_false in Hn, Hnle.
  apply leb_complete_conv in Hn.
  apply leb_complete_conv in Hnle; omega.
  eqobs_in iE5'E5_H.
  rewrite <- andR_comm, andR_assoc, andR_assoc; apply proj1_MR. 

  ep_eq_l (apply_finv (L[{mS}])) (P[{mS}]).
  unfold req_mem_rel, EP1, andR, notR; simpl; unfold O.eval_op; simpl.
  intros k m1 m2 [ [_ [_ H] ] [Hn _] ].  
  rewrite not_is_true_false in Hn.
  rewrite Hn in H; simpl in H.
  autorewrite with Ris_true in H.  
  symmetry.
  match goal with
  |- ?A = ?B => generalize (UT.i_eqb_spec A B); rewrite H; auto
  end.
  eqobs_in iE5'E5_H.
  rewrite <- andR_comm, andR_assoc, andR_assoc; apply proj1_MR. 
 Qed.

 Definition iE5'E5 :=
  add_adv_info_false (EqAD _ _ _ _) (A_wf_E _ _)
   (add_info Sign 
    Vset.empty
    Vset.empty
    iE5'E5_H
    EqObs_S_E5'E5).

 Lemma Pr_G5'_G5 : forall k (m:Mem.t k), 
  Pr E5' G5 m (@S3 k) == Pr E5 G5 m (@S3 k).
 Proof.
  intros; unfold Pr.
  apply EqObs_deno with I (Vset.add j (Vset.add M O)).
  eqobs_tl iE5'E5.
  unfold inv5'; eqobsrel_tail; simpl; unfold implMR; auto.  
  intros; unfold S3, charfun, restr, EP, andP.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
  trivial.
 Qed.
 (* END [Pr_G5'_G5] *)


 (* END [Pr_G5_G5] *)
 
 (* [G5] verifies the postcondition [M[{j}] =?= madv ==> h =?= y] *)
 Definition inv5 :=
  EP1 ((j in_dom M) ==> (M[{j}] in_dom L)) /-\
  EP1 ((j in_dom M) ==> (L[{ M[{j}] }] =?= r)).

 Lemma EqObs_H_inv_E5E5 : 
  EqObsInv inv5
  (Vset.add r (Vset.add P I_H)) 
  E5 Hash5_body 
  E5 Hash5_body
  (Vset.add r (Vset.add j (Vset.add P O_H))).
 Proof.
  clear; unfold Hash5_body, Hash4_body.
  
  cp_test (mH in_dom L).

  (* [mH in_dom L] *)
  eapply equiv_weaken; [ | apply equiv_nil].
  unfold req_mem_rel, kreq_mem, inv5, andR; intros.  
  unfold I_H, O_H in *; intuition.
  apply req_mem_weaken with (2:=H).
  unfold Vset.subset; trivial.

  (* [!(mH in_dom L)] *)
  cp_test (i =?= j).

  (* [i =?= j] *)
  unfold inv5;  eqobsrel_tail; unfold EP1, implMR, notR, andR; 
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2; rewrite nat_eqb_refl; simpl; rewrite nat_eqb_refl; simpl.  
  bprop.
  intros H; decompose [and] H.
  clear H H6 H7; repeat split.
  
  intro; apply Veqb_refl.

  (* [!(i =?= j)] *)
  unfold inv5;  eqobsrel_tail; unfold EP1, implMR, notR, andR; 
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k m1 m2; bprop.
  intros H v Hv; decompose [and] H.
  rewrite not_is_true_false, nat_eqb_sym in H2; rewrite H2; simpl.
  clear H H6 H7; bprop; repeat split.
  
  auto.

  intros.
  case_eq (nat_eqb
   match find (fun p => nat_eqb (m1 j) (fst p)) (m1 M)
   with
   | Some e => snd e
   | None => 0
   end (m1 mH)); intro Hj.
  rewrite (nat_eqb_true Hj) in H4.
  elim H3; clear H3.
  destruct (H1 H).
  rewrite (nat_eqb_true Hj) in H3.
  exists x; trivial.
  auto.
 Qed.

 Lemma dec_inv5 : decMR inv5.
 Proof.
  unfold inv5; auto.
 Qed.

 Lemma dep_inv5 : depend_only_rel inv5
  (Vset.add i (Vset.add j (Vset.add M (Vset.add L (Vset.singleton r)))))
  Vset.empty.
 Proof.
  unfold depend_only_rel, inv5, andR, EP1; intros.
  apply req_mem_sym in H.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
 Qed.

 Definition eE5E5 : eq_inv_info inv5 E5 E5.
  refine (@empty_inv_info inv5 _ _ dep_inv5 _ dec_inv5 E5 E5).
  vm_compute; trivial.
 Defined.
  
 Definition iE5E5_H :=
  add_info Hash Vset.empty Vset.empty eE5E5 EqObs_H_inv_E5E5.

 Lemma EqObs_S_E5E5 : EqObsInv inv5
  (Vset.add r (Vset.add j (Vset.add P I_S)))
  E5 Sign5_body
  E5 Sign5_body  
  (Vset.add r (Vset.add j (Vset.add P O_S))).
 Proof.
  clear; unfold Sign5_body.
  eqobs_in iE5E5_H.
 Qed.  
  
 Definition iE5E5inv :=
  add_adv_info_lossless (EqAD _ _ _ _) (A_wf_E _ _)
   (@A_lossless _)
   (@A_lossless _)
   (add_info Sign 
    Vset.empty
    Vset.empty
    iE5E5_H
    EqObs_S_E5E5).

 Lemma G5_post : forall k (m:Mem.t k),
  range (EP k ((j in_dom M) && (madv =?= M[{j}])) [=>] EP k (h =?= r)) ([[G5]] E5 m).
 Proof.
  intros k m; apply mu_range.
  transitivity (mu ([[G5]] E5 m) (fone _));
   [ | refine (is_lossless_correct (refl1_info iE5E5inv) _ _ _); trivial].

  apply equiv_deno with 
   (req_mem_rel Gadv trueR) 
   (req_mem_rel Gadv (@EP1 (((j in_dom M) && (madv =?= M[{j}])) ==> (h =?= r)))).

  change G5 with ((rev (tail (rev G5))) ++ [ h <c- Hash with {madv} ]).
  apply equiv_app with
   (req_mem_rel 
    (Vset.add madv (Vset.add i (Vset.add r (Vset.add j (Vset.add M (Vset.add L Gadv))))))
    inv5).

  eqobs_tl iE5E5inv.
  unfold inv5; eqobsrel_tail; unfold implMR; simpl; unfold O.eval_op; simpl.
  repeat split; auto.

  inline iE5E5inv Hash.
  unfold req_mem_rel; apply decMR_and; [trivial | apply dec_inv5].

  ep iE5E5inv.
  cp_test (madv in_dom L).
  
  (* [madv in_dom L] *)
  unfold inv5; eqobsrel_tail; unfold EP1, implMR, andR;
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros; bprop.
  autorewrite with Ris_true in H.
  decompose [and] H; clear H H5.

  case_eq (nat_eqb (m1 madv) 
   match
    find (fun p => nat_eqb (m1 j) (fst p)) (m1 M)
   with
   | Some e => snd e
   | None => 0
   end); intro Heq.
  intros [Hle _].
  rewrite <- (nat_eqb_true Heq) in H4.
  auto.

  intros [_ ?]; discriminate.
  
  (* [!(madv in_dom L)] *)
  unfold inv5; eqobsrel_tail; unfold EP1, implMR, notR, andR;
   simpl; unfold O.eval_op; simpl; unfold O.assoc; simpl.
  intros k0 m1 m2; bprop.  
  rewrite nat_eqb_refl; simpl.
  intro H; decompose [and] H; clear H H0 H5.

  repeat split; intros.
  apply Veqb_refl.

  destruct H as [Hn _].
  rewrite not_is_true_false in Hn.
  rewrite nat_eqb_sym in Hn; rewrite Hn.
  bprop; intros [Hle Hmadv].
  rewrite <- (nat_eqb_true Hmadv) in H1, H4.  
  elim H2; clear H2.
  apply H1.
  destruct Hle.
  discriminate.
  trivial.

  unfold req_mem_rel, andR, fone, EP, EP1.
  intros m1 m2; simpl; unfold O.eval_op; simpl.
  intros [_ H].
  unfold implP, implb; unfold impb in H.
  destruct (existsb (fun p => nat_eqb (m1 j) (fst p)) (m1 M));
  simpl; simpl in H; trivial.
  destruct (nat_eqb (m1 madv)
   (O.assoc (nat_eqb (m1 j)) 0%nat (m1 M))); trivial.
  simpl in H; simpl.
  rewrite H; trivial.

  unfold req_mem_rel, trueR, andR; auto.
 Qed.

 Close Scope nat_scope.

 Lemma G5_post' : forall k (m:Mem.t k),
  range (EP k (y =?= r)) ([[G5]] E5 m).
 Proof.
  intros; apply mu_range. 
  transitivity (mu ([[G5 ++ [y <- r] ]] E5 m) 
   (fun m => if EP k (y =?= r) m then 1 else 0)).

  apply equiv_deno with 
   (req_mem_rel Gadv trueR) (req_mem_rel (Vset.add r (Vset.add y O)) trueR).

  unfold G5, G4.
  swap iE5E5inv.
  deadcode iE5E5inv.
  eqobs_tl iE5E5inv.
  unfold inv5; eqobsrel_tail; unfold implMR; simpl; unfold O.eval_op; simpl.
  repeat split; auto.

  intros m1 m2 [H _].
  unfold EP.
  rewrite depend_only_fv_expr_subset with (2:=H); unfold Vset.subset; trivial.
  
  unfold req_mem_rel, trueR, andR; auto.
  
  transitivity (mu ([[G5 ++ [y <- r] ]] E5 m) (fone _));
   [ | refine (is_lossless_correct (refl1_info iE5E5inv) _ _ _); trivial].

  apply equiv_deno with 
   (req_mem_rel Gadv trueR) 
   (req_mem_rel Gadv (@EP1 (y =?= r))).

  apply equiv_app with  
   (req_mem_rel (Vset.add y (Vset.singleton r)) trueR).
  eqobs_tl iE5E5inv.
  unfold inv5; eqobsrel_tail; unfold implMR; simpl; unfold O.eval_op; simpl.
  repeat split; auto.

  eqobsrel_tail; unfold implMR; simpl; unfold O.eval_op; simpl.
  intros; apply Veqb_refl.
  unfold EP1, EP; intros m1 m2 [_ H].
  rewrite H; trivial.

  unfold req_mem_rel, andR, trueR; auto.
 Qed.  

 (** [ Pr[S_5] <= Pr[xadv =?= apply_finv y] *)
 Theorem Pr_G5_G5 : forall k (m:Mem.t k),
  Pr E5 G5 m (@S3 k) <= Pr E5 G5 m (EP k (xadv =?= apply_finv y)).
 Proof.
  intros; unfold S3, Pr.
  apply Ole_eq_right with
   (mu ([[G5]] E5 m) (charfun (EP k (xadv =?= apply_finv r)))).
  
  apply (range_le (G5_post m)); intro m'.
  unfold charfun, restr, EP, implP, andP, andb, implb, fone.
  assert (H:@E.eval_expr _ T.Bool ((h =?= apply_f xadv) && (madv not_in S)) m' = 
           (@E.eval_expr _ T.Bool (h =?= apply_f xadv) m' && @E.eval_expr _ T.Bool (madv not_in S) m')%bool) by trivial.
  rewrite H; clear H.
  case_eq (@E.eval_expr _ T.Bool (((j in_dom M) && (madv =?= M[{j}]))) m');
  intros He Heq.
  assert (H:@E.eval_expr _ T.Bool (h =?= apply_f xadv) m' = 
            @E.eval_expr _ T.Bool (xadv =?= apply_finv r) m').
  simpl in Heq |- *; unfold O.eval_op in Heq |- *; simpl in Heq |- *.
  generalize (UT.i_eqb_spec (t:=Bitstring) (m' h) (m' r)).  
  rewrite Heq; clear Heq; intro Heq; rewrite Heq; clear Heq.
  unfold UT.i_eqb.
  symmetry; rewrite <- f_inj_Veqb.
  rewrite <- finv_spec.
  apply Veqb_sym.
  rewrite H.
  case (@E.eval_expr _ T.Bool (madv not_in S) m');
  case (@E.eval_expr _ T.Bool (xadv =?= apply_finv r) m');
  case (@E.eval_expr _ T.Bool (h =?= apply_f xadv) m'); trivial.

  case (@E.eval_expr _ T.Bool (madv not_in S) m');
  case (@E.eval_expr _ T.Bool (xadv =?= apply_finv r) m');
  case (@E.eval_expr _ T.Bool (h =?= apply_f xadv) m'); trivial.
  generalize He.
  simpl; unfold O.eval_op; simpl.
  rewrite andb_comm.
  clear Heq; intro Heq; rewrite Heq; trivial.
  
  apply (range_eq (G5_post' m)); intro m'.
  unfold EP, charfun, restr, fone; simpl; unfold O.eval_op; simpl.
  intro Heq; rewrite <- (Veqb_true _ _ Heq); trivial.
 Qed.
 (* END [Pr_G5_G5] *)


 (** BEGIN [Pr_G5_Gf] *)

 (** Definition of the inverter [B] *)
 Notation Barg := (Var.Lvar (T.User Bitstring) 70).

 Definition B_params : var_decl (Proc.targs B) := dcons _ Barg (dnil _).

 Definition B_body := 
  [
   r <- Barg;
   j <$- [0..q];
   i <- 0%nat;
   L <- Nil _;
   P <- Nil _;
   retA <c- A with {}
  ].   

 Definition B_ret : E.expr (T.User Bitstring) := Esnd retA.

 Definition Gf : cmd :=
  [ 
   y <$- {0,1}^k;
   xadv <c- B with {y}
  ].

 Definition Ef := add_decl E5 B B_params (refl_equal true) B_body B_ret.

 Lemma EqAD_5f : Eq_adv_decl PrOrcl PrPriv E5 Ef.
 Proof.
  unfold Eq_adv_decl, Ef, E5, makeEnv, proc_params, proc_body, proc_res; intros.
  generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto; intro Heq;
   try (apply H; rewrite <- Heq; vm_compute; trivial; fail);
   apply H0; rewrite <- Heq; vm_compute; trivial.
 Qed.

 Lemma A_wf_f : WFAdv PrOrcl PrPriv Gadv Gcomm Ef A. 
 Proof.
  unfold Ef, E5.
  intros; apply WFAdv_trans with (5:=A_wf_E Hash4_body Sign5_body).
  unfold Eq_orcl_params; intros.
  unfold PrOrcl in H.
  rewrite PrSetP.add_spec in H; destruct H.
  inversion H; simpl.
  vm_compute; trivial.
  apply PrSet.singleton_complete in H; inversion H; simpl.
  vm_compute; trivial.
  apply EqAD_5f.
  vm_compute; discriminate.
  vm_compute; discriminate.
 Qed.

 Definition iE5Ef :=
  add_adv_info_lossless EqAD_5f (A_wf_E _ _)
  (@A_lossless _)
  (@A_lossless _)
  (add_refl_info_O Sign
   (Vset.add P (Vset.remove M (Vset.remove S O_S))) Vset.empty Vset.empty
   (add_refl_info_O Hash
    (Vset.add P (Vset.remove M O_H)) Vset.empty Vset.empty
    (empty_info E5 Ef))).

 Notation b := (Var.Lvar T.Bool 163).

 Theorem Pr_G5_Gf : forall k (m:Mem.t k), 
  Pr E5 G5 m (EP k (xadv =?= apply_finv y)) == 
  Pr Ef Gf m (EP k (xadv =?= apply_finv y)).
 Proof.
  intros k m.
  apply EqObs_Pr with I.
  alloc_l r y.
  sinline_r iE5Ef B.
  eqobs_tl iE5Ef.
  swap; deadcode; eqobs_in.
 Qed.  
 (* END [Pr_G5_Gf] *)


 (** * FDH exact security *)
 Theorem FDH_exact_security : forall k (m:Mem.t k), 
  [1/]1+peval q_poly k * Pr E1 G1 m (EP k ((h =?= apply_f xadv) && (madv not_in S))) <= 
  Pr Ef Gf m (EP k (xadv =?= apply_finv y)).
 Proof.
  intros.
  rewrite Pr_G1_G2.
  rewrite Pr_G2_G3.
  rewrite Pr_G3_G4.
  rewrite Pr_G4_G4'.
  rewrite Pr_G4_G5.
  rewrite <- Pr_G5_Gf.
  rewrite Pr_G5'_G5.
  apply Pr_G5_G5.
 Qed.

 Lemma EqAD_1f : Eq_adv_decl PrOrcl PrPriv E1 Ef.
 Proof.
  unfold Eq_adv_decl, Ef, E5, E1, makeEnv, proc_params, proc_body, proc_res; intros.
  generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
  destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
  inversion H1; simpl; auto.
  repeat rewrite add_decl_other_mk; try tauto; intro Heq;
   try (apply H; rewrite <- Heq; vm_compute; trivial; fail);
   apply H0; rewrite <- Heq; vm_compute; trivial.
 Qed.

 Definition pi : PPT_info Ef :=
  PPT_add_adv_infob EqAD_1f A_PPT
  (PPT_add_info (PPT_add_info (PPT_empty_info Ef) Hash) Sign).

 (** * FDH existential unforgeability *)
 Theorem FDH_existential_unforgeability : forall (m:forall k, Mem.t k),
  negligible (fun k => Pr E1 G1 (m k) (EP k ((h =?= apply_f xadv) && (madv not_in S)))).
 Proof.
  intro m.
  destruct (polynomial_bounded q_poly) as [c Hc].
  apply negligible_mult_poly with (1 + c)%nat.
  apply negligible_le with 
   (fun k => [1/]1+peval q_poly k * Pr E1 G1 (m k) (EP k ((h =?= apply_f xadv) && (madv not_in S)))).
  exists 2%nat; intros n Hle; rewrite Umult_sym.
  apply Umult_le_compat; [ | trivial ].
  transitivity ([1/]1+n ^ (1 + c))%nat.
  apply Unth_le_pow; auto with arith.
  apply Unth_anti_mon.
  apply le_trans with (n ^ c)%nat.
  apply Hc; trivial.
  rewrite <- (mult_1_l (pow n c)).
  simpl pow; apply mult_le_compat; auto with arith.
  apply negligible_le_stable with 
   (fun k => Pr Ef Gf (m k) (EP k (xadv =?= apply_finv y))).
  intro k; apply FDH_exact_security.
  apply f_oneway; try discriminate; trivial.
  apply is_lossless_correct with (refl2_info iE5Ef); vm_compute; trivial.
  PPT_proc_tac pi.
 Qed.

End ADVERSARY_AND_PROOF.
