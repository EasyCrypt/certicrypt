(** * SHVZK_of_HVZK.v : Special Honest-Verifier ZK protocol from
 a Honest-Verifier ZK protocol *)

Require Import Sigma.
Require Import SigmaSem.

Set Implicit Arguments.


Module SHVZK_of_HVZK 
 (S : SIGMA' N1 Sem BP
  with Definition xT := T.User xT1 
  with Definition wT := T.User wT1
  with Definition rT := T.User rT1
  with Definition stateT := T.User stateT1
  with Definition cT := T.User Bitstring
  with Definition sT := T.User sT1
  with Definition V1_body := [ (Var.Lvar (T.User Bitstring) N1._c') <$- {0,1}^k ]
  with Definition V1_re := E.Evar (Var.Lvar (T.User Bitstring) N1._c')) 
 : SIGMA N Sem BP.

 (* Redefine notations for readability of proofs *)
 Notation "S:x"      := (Var.Lvar (T.User xT1) 100).
 Notation "S:w"      := (Var.Lvar (T.User wT1) 101).
 Notation "S:r"      := (Var.Lvar (T.User rT1) 102).
 Notation "S:state"  := (Var.Lvar (T.User stateT1) 103).
 Notation "S:c"      := (Var.Lvar (T.User Bitstring) 104).
 Notation "S:s"      := (Var.Lvar (T.User sT1) 105).
 Notation "S:b"      := (Var.Lvar T.Bool 106).
 Notation "S:rstate" := (Var.Lvar (T.Pair (T.User rT1) (T.User stateT1)) 107).
 Notation "S:rs"     := (Var.Lvar (T.Pair (T.User rT1) (T.User sT1)) 108).

 Notation "S:P1" := (Proc.mkP 100 
  (T.User xT1 :: T.User wT1 :: nil) 
  (T.Pair (T.User rT1) (T.User stateT1))).

 Notation "S:P2" := (Proc.mkP 101 
  (T.User xT1 :: T.User wT1 :: T.User stateT1 :: T.User Bitstring :: nil) 
  (T.User sT1)).
 
 Notation "S:V1" := (Proc.mkP 102 
  (T.User xT1 :: T.User rT1 :: nil) 
  (T.User Bitstring)).
 
 Notation "S:V2" := (Proc.mkP 103 
  (T.User xT1 :: T.User rT1 :: T.User Bitstring :: T.User sT1 :: nil) 
  T.Bool).
 
 Notation "S:S" := (Proc.mkP 104
  (T.User xT1 :: T.User Bitstring :: nil) 
  (T.Pair (T.User rT1) (T.User sT1))).
 
 Notation "S:KE" := (Proc.mkP 105
  (T.User xT1 :: T.User rT1 :: T.User Bitstring :: T.User Bitstring :: T.User sT1 :: T.User sT1 :: nil) 
  (T.User wT1)).

 Import N.

 Notation _xT     := (T.User xT1).
 Notation _wT     := (T.User wT1).
 Notation _rT     := (T.Pair (T.User rT1) (T.User Bitstring)).
 Notation _stateT := (T.Pair (T.User stateT1) (T.User Bitstring)).
 Notation _cT     := (T.User Bitstring).
 Notation _sT     := (T.User sT1).

 Definition xT     := _xT.
 Definition wT     := _wT.
 Definition rT     := _rT.
 Definition stateT := _stateT.
 Definition cT     := _cT.
 Definition sT     := _sT.

 (** Knowledge relation *)
 Definition R := S.R.
 Definition R' := S.R'.
 Definition R_dec := S.R_dec.
 Definition R'_dec := S.R'_dec.

 (** Variables *)
 Notation x      := (Var.Lvar _xT 1).
 Notation w      := (Var.Lvar _wT 2).
 Notation r      := (Var.Lvar _rT 3). 
 Notation state  := (Var.Lvar _stateT 4). 
 Notation c      := (Var.Lvar _cT 5). 
 Notation s      := (Var.Lvar _sT 6).
 Notation b      := (Var.Lvar T.Bool 7).
 Notation rstate := (Var.Lvar (T.Pair _rT _stateT) 8).
 Notation rs     := (Var.Lvar (T.Pair _rT _sT) 9).
 Notation x'     := (Var.Lvar _xT 10).
 Notation w'     := (Var.Lvar _wT 11).
 Notation r'     := (Var.Lvar _rT 12). 
 Notation state' := (Var.Lvar _stateT 13). 
 Notation c'     := (Var.Lvar _cT 14). 
 Notation s'     := (Var.Lvar _sT 15).
 Notation c''    := (Var.Lvar _cT 16). 
 Notation s''    := (Var.Lvar _sT 17).
 Notation c1     := (Var.Lvar _cT 18). 
 Notation s1     := (Var.Lvar _sT 19).
 Notation c2     := (Var.Lvar _cT 20). 
 Notation s2     := (Var.Lvar _sT 21).

 (** Procedures *)
 Notation P1 := (Proc.mkP 1 (_xT :: _wT :: nil) (T.Pair _rT _stateT)).
 Notation P2 := (Proc.mkP 2 (_xT :: _wT :: _stateT :: _cT :: nil) _sT).
 Notation V1 := (Proc.mkP 3 (_xT :: _rT :: nil) _cT).
 Notation V2 := (Proc.mkP 4 (_xT :: _rT :: _cT :: _sT :: nil) T.Bool).
 Notation S  := (Proc.mkP 5 (_xT :: _cT :: nil) (T.Pair _rT _sT)).
 Notation KE := (Proc.mkP 6 (_xT :: _rT :: _cT :: _cT :: _sT :: _sT :: nil) _wT).
 

 Definition P1_args : var_decl (Proc.targs P1) := 
  dcons _ x' (dcons _ w' (dnil _)).

 Definition P1_body : cmd := 
  [ 
   S.rstate <c- S.P1 with {x', w'};
   S.r <- Efst S.rstate;
   S.state <- Esnd S.rstate;
   c'' <$- {0,1}^k 
  ].
 
 Definition P1_re := ((S.r | c'') | (S.state | c'')).


 Definition P2_args : var_decl (Proc.targs P2) := 
  dcons _ x' (dcons _ w' (dcons _ state' (dcons _ c' (dnil _)))).

 Definition P2_body : cmd := 
  [ 
   c'' <- Esnd state' (+) c';
   S.s <c- S.P2 with {x', w', Efst state', c''}
  ].

 Definition P2_re  : E.expr sT := S.s.

  
 Definition V1_args : var_decl (Proc.targs V1) := 
  dcons _ x' (dcons _ r' (dnil _)).
 
 Definition V1_body : cmd := [ c' <c- S.V1 with {x', Efst r'} ].
 
 Definition V1_re  : E.expr cT := (c' (+) Esnd r').


 Definition V2_args : var_decl (Proc.targs V2) := 
  dcons _ x' (dcons _ r' (dcons _ c' (dcons _ s' (dnil _)))).
 
 Definition V2_body : cmd := 
  [ S.b <c- S.V2 with {x', Efst r', Esnd r' (+) c', s'} ].
 
 Definition V2_re : E.expr T.Bool := S.b.


 Definition S_args : var_decl (Proc.targs S) :=
  dcons _ x' (dcons _ c' (dnil _)).

 Definition S_body : cmd :=
  [
   S.rcs <c- S.S with {x'};
   S.r <- Efst S.rcs;
   S.c <- Efst (Esnd S.rcs);
   S.s <- Esnd (Esnd S.rcs)
  ].

 Definition S_re : E.expr (T.Pair rT sT) := ((S.r | S.c (+) c') | S.s).

 Definition KE_args : var_decl (Proc.targs KE) := 
  dcons _ x' (dcons _ r' (dcons _ c' (dcons _ c'' (dcons _ s' 
   (dcons _ s'' (dnil _)))))). 

 Definition KE_body : cmd :=
  [ S.w <c- S.KE with {x', Efst r', Esnd r' (+) c', Esnd r' (+) c'', s', s''} ].

 Definition KE_re  : E.expr wT := S.w.

 Section ENV.

  Let add_S_P1 E := add_decl E S.P1 S.P1_args (refl_equal _) S.P1_body S.P1_re.
  Let add_S_P2 E := add_decl E S.P2 S.P2_args (refl_equal _) S.P2_body S.P2_re.
  Let add_S_V1 E := add_decl E S.V1 S.V1_args (refl_equal _) S.V1_body S.V1_re.
  Let add_S_V2 E := add_decl E S.V2 S.V2_args (refl_equal _) S.V2_body S.V2_re.
  Let add_S_S  E := add_decl E S.S S.S_args (refl_equal _) S.S_body S.S_re.
  Let add_S_KE E := add_decl E S.KE S.KE_args (refl_equal _) S.KE_body S.KE_re.
  
  Definition _E : env :=
   add_S_KE (add_S_S (add_S_P1 (add_S_P2 (add_S_V1 (add_S_V2 S.E))))).

  Let add_P1 E := add_decl E P1 P1_args (refl_equal _) P1_body P1_re.
  Let add_P2 E := add_decl E P2 P2_args (refl_equal _) P2_body P2_re.
  Let add_V1 E := add_decl E V1 V1_args (refl_equal _) V1_body V1_re.
  Let add_V2 E := add_decl E V2 V2_args (refl_equal _) V2_body V2_re.
  Let add_S  E :=  add_decl E S S_args (refl_equal _) S_body S_re.
  Let add_KE E := add_decl E KE KE_args (refl_equal _) KE_body KE_re.
  
  Definition E := add_KE (add_S (add_P1 (add_P2 (add_V1 (add_V2 _E))))).

 End ENV.

 Definition iEE := 
  add_refl_info P1 
  (add_refl_info P2
  (add_refl_info V1
  (add_refl_info V2
  (add_refl_info S
  (add_refl_info KE 
  (add_basic_info E E S.P1 S.P1_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E E S.P2 S.P2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E E S.V1 S.V1_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S.V2 S.V2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E E S.S S.S_i   (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E E S.KE S.KE_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (empty_info E E)))))))))))).

 Definition iESE := 
  add_basic_info E S.E S.P1 S.P1_i  (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S.E S.P2 S.P2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S.E S.V1 S.V1_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E S.E S.V2 S.V2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S.E S.S S.S_i   (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S.E S.KE S.KE_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (empty_info E S.E)))))).

 Definition iSEE := 
  add_basic_info S.E E S.P1 S.P1_i  (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info S.E E S.P2 S.P2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info S.E E S.V1 S.V1_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S.E E S.V2 S.V2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info S.E E S.S  S.S_i  (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info S.E E S.KE S.KE_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (empty_info S.E E)))))). 

 Definition iSESE := 
  add_basic_info S.E S.E S.P1 S.P1_i  (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info S.E S.E S.P2 S.P2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info S.E S.E S.V1 S.V1_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info S.E S.E S.V2 S.V2_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S.E S.E S.S S.S_i   (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S.E S.E S.KE S.KE_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (empty_info S.E S.E)))))). 

 Parameter P1_i : info P1_args P1_body P1_re.
 Parameter P2_i : info P2_args P2_body P2_re.
 Parameter V1_i : info V1_args V1_body V1_re.
 Parameter V2_i : info V2_args V2_body V2_re.
 Parameter S_i  : info S_args S_body S_re.
 Parameter KE_i : info KE_args KE_body KE_re.

 Definition protocol := 
  [
   rstate <c- P1 with {x, w};
   r <- Efst rstate; state <- Esnd rstate;
   c <c- V1 with {x, r};
   s <c- P2 with {x, w, state, c};
   b <c- V2 with {x, r, c, s}
  ].

 Definition protocol' := 
  [
   rstate <c- P1 with {x, w};
   r <- Efst rstate; state <- Esnd rstate;
   s <c- P2 with {x, w, state, c};
   b <c- V2 with {x, r, c, s}
  ]. 
 
 Definition simulation :=
  [
   rs <c- S with {x,c};
   r <- Efst rs;
   s <- Esnd rs
  ].

 Definition R1 : mem_rel := fun k m1 _ => R (m1 x) (m1 w).

 Lemma decMR_R1 : decMR R1.
 Proof.
  intros ? ? ?; apply S.R_dec.
 Qed.

 Hint Resolve decMR_R1.  

 Lemma decMR_SR1 : decMR S.R1.
 Proof.
  intros ? ? ?; apply S.R_dec.
 Qed.

 Hint Resolve decMR_SR1.
 
 Lemma completeness : forall k (m:Mem.t k), 
  R (m x) (m w) -> Pr E protocol m (EP k b) == 1%U.
 Proof.
  unfold protocol; intros. 
  rewrite (Pr_d_eq _ _ _ S.b).
  
  transitivity (Pr E ([ S.x <- x; S.w <- w ] ++ S.protocol) m (EP k S.b)).
  apply EqObs_Pr with (I:={{x, w}}).
  inline iEE V1.
  inline_l iEE V2.
  inline_l iEE P1. 
  sinline_l iEE P2.
  alloc_l iEE b S.b.
  alloc_l iEE s S.s.
  alloc_l iEE c' S.c.
  ep iEE; deadcode iEE. 
  eqobs_in iEE.

  transitivity (Pr E
   S.protocol (m {! S.x <-- (m x) !} {! S.w <-- (m w) !}) (EP k S.b)).
  unfold Pr at 1.
  rewrite deno_app_elim.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  rewrite deno_nil_elim.
  unfold E.eval_expr, O.eval_op; rewrite Mem.get_upd_diff; trivial. 
  discriminate.

  transitivity (Pr S.E S.protocol ((m {!S.x <-- m x!}) {!S.w <-- m w!})
   (EP k S.b)). 
  apply EqObs_Pr with {{S.x, S.w}}. 
  eqobs_in iESE.

  apply S.completeness.
  mem_upd_simpl.
 Qed.

 Lemma SHVZK : equiv 
  (req_mem_rel {{x, w, c}} R1)
  E protocol'
  E simulation
  (kreq_mem {{r, c, s}}).
 Proof.
  unfold protocol', simulation.
  apply equiv_trans_trans with E
  ([S.x <- x; S.w <- w] ++ 
   S.protocol ++ 
   [ r <- ( S.r | S.c (+) c) ; s <- S.s ]); auto.
  intros x m1 m2 [H H0]; split; trivial.
  inline_l iEE P1.
  inline_l iEE V1.
  inline_l iEE P2.
  inline_l iEE V2.
  inline_r iEE S.
  inline iEE S.V1.
  alloc_l iEE s S.s.
  alloc_l iEE b S.b.
  alloc_l iEE c' S.c.
  ep iEE; deadcode iEE.
  ep iEE; deadcode iEE. 
  apply equiv_strengthen with (kreq_mem {{x, w, c}}).
  intros k m1 m2 [H1 H2]; auto.
  eqobs_hd iEE; eqobs_tl iEE.  
  
  apply equiv_trans_trans with E
  [  
   c'' <$- {0,1}^k;
   S.c <-  c'' (+) c;
   S.s <c- S.P2 with {Var.Lvar _xT 1, w, Esnd (S.rstate), S.c};
   r <- (Efst (S.rstate) | S.c (+) c) 
  ]; auto.

  ep iEE; deadcode iEE. 
  swap iEE. 
  eqobs_in iEE.

  swap iEE.
  eqobs_tl iEE; union_mod.
   
  apply equiv_trans_trans with E [S.c <$- {0,1}^k; c'' <- S.c (+) c]; auto.

  eapply equiv_strengthen; 
   [ |  eapply equiv_weaken; [ | apply optimistic_sampling] ].

  simpl; intros; eapply req_mem_weaken; [ | apply H].
  vm_compute; trivial.
  simpl; intros; eapply req_mem_weaken; [ | apply H].
  vm_compute; trivial.
  vm_compute; trivial.
  vm_compute; trivial.
  discriminate.
 
  deadcode; eqobs_in.
  
  apply equiv_trans_trans with E 
   ([S.x <- x; S.w <- w] ++ S.simulation ++  [ r <- ( S.r | S.c (+) c) ; s <- S.s ]); auto. 
  intros x m1 m2 [H H0]; split; trivial.

  apply equiv_app with (req_mem_rel {{S.x, S.w, c}} S.R1).
 
  unfold R1, S.R1; eqobsrel_tail.
  unfold implMR, andR; intros k m1 m2 [H1 H2]; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
 
  apply equiv_app with (kreq_mem {{S.r, S.c, S.s, c}}).

  apply equiv_trans_trans with S.E S.protocol; auto. 
  intros x m1 m2 [H H0]; split; trivial.
  eqobs_in iESE.

  apply equiv_trans_trans with S.E S.simulation; auto.
  intros x m1 m2 [H H0]; split; trivial.
  apply equiv_strengthen with
   ((req_mem_rel {{S.x, S.w}} S.R1) /-\ kreq_mem {{c}}).
  intros k m1 m2 [H1 H2].
  repeat split. 
  eapply req_mem_weaken; [ | apply H1].
  vm_compute; trivial.
  trivial.
  eapply req_mem_weaken; [ | apply H1]. 
  vm_compute; trivial. 

  apply equiv_weaken with (req_mem_rel {{S.r, S.c, S.s}} (kreq_mem {{c}})).
  intros k m1 m2 [H1 H2].

  repeat split. 
  eapply req_mem_weaken; [ | eapply req_mem_union; [apply H1 | apply H2] ].
  vm_compute; trivial.

  compute_assertion Heq1 X1 (modify (refl1_info iSEE) Vset.empty S.protocol).
  compute_assertion Heq2 X2 (modify (refl1_info iSEE) Vset.empty S.simulation).
  apply modify_correct in Heq1.
  apply modify_correct in Heq2.

  match goal with 
   [ H1 := Some ?V1 , H2 := Some ?V2   |- _] => pose (M1:=V1); pose (M2:=V2) 
  end.
  
  eapply equiv_inv_Modify with {{c}} {{c}} M1 M2.
  apply depend_only_kreq_mem.

  apply Heq1.
  apply Heq2.
  vm_compute; trivial.
  vm_compute; trivial.
  vm_compute; trivial.

  apply equiv_strengthen with (req_mem_rel {{S.x, S.w}} S.R1).
  intros k m1 m2 [H1 H2]; auto.
  split; auto.

  apply equiv_weaken with (kreq_mem {{S.r, S.c, S.s}}).
  intros k m1 m2 H; split; auto.
  unfold trueR; trivial.
  
  apply S.HVZK.

  eqobs_in iSEE.

  eqobs_in.

  inline_r iEE S.
  ep iEE; deadcode iEE; eqobs_in iEE.
 Qed.


 Section SOUNDNESS.

  Close Scope positive_scope.
  Close Scope nat_scope. 
 
  Variable k : nat.
  Variable m : Mem.t k.

  Hypothesis H_neq : m c1 <> m c2. 
  Hypothesis accepting_1 : Pr E [b <c- V2 with {x, r, c1, s1} ] m (EP k b) == 1.
  Hypothesis accepting_2 : Pr E [b <c- V2 with {x, r, c2, s2} ] m (EP k b) == 1.
  
  Let m' := 
   m{!S.x <-- (m x)!}{!S.r <-- fst (m r)!}
    {!S.c1 <--  Bvector.BVxor k (snd (m r)) (m c1)!}
    {!S.c2 <--  Bvector.BVxor k (snd (m r)) (m c2)!}
    {!S.s1 <-- (m s1)!}{!S.s2 <-- (m s2)!}.

  Lemma S_accepting_1 : Pr S.E 
   [S.b <c- S.V2 with {S.x, S.r, S.c1, S.s1} ] m' (EP k S.b) == 1.
  Proof.
   transitivity
    (Pr E 
     [
      S.x <- x;
      S.r <- Efst r;
      S.c1 <- Esnd r (+) c1;
      S.s1 <- s1;
      S.b <c- S.V2 with {S.x, S.r, S.c1, S.s1}
     ] m (EP k S.b)).
   unfold Pr at 2.
   repeat (
    rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
    simpl E.eval_expr; unfold O.eval_op; simpl T.app_op; mem_upd_simpl).
   apply EqObs_Pr2 with {{S.x, S.r, S.c1, S.s1}} {{S.b}}.
   eqobs_in iSEE.
   vm_compute; trivial.
   unfold m'; intros t x H; Vset_mem_inversion H; subst; mem_upd_simpl; trivial.

   split; [trivial | ].
   transitivity (Pr E
    [
     S.x <- x;
     S.r <- Efst r;
     S.c1 <- Esnd r (+) c1;
     S.s1 <- s1;
     S.b <c- S.V2 with {S.x, S.r, S.c1, S.s1}
    ] m (EP k S.b)).
   rewrite (Pr_d_eq _ _ _ b), <- accepting_1.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c1, s1}}.
   sinline_l iEE V2.
   alloc_l iEE b S.b. eqobs_in iEE.

   apply Oeq_le; apply EqObs_Pr with {{x, r, c1, s1}}.
   deadcode iEE; eqobs_in iEE.
  Qed.

  Lemma S_accepting_2 : Pr S.E 
   [S.b <c- S.V2 with {S.x, S.r, S.c2, S.s2} ] m' (EP k S.b) == 1.
  Proof.
   transitivity
    (Pr E 
     [
      S.x <- x;
      S.r <- Efst r;
      S.c2 <- Esnd r (+) c2;
      S.s2 <- s2;
      S.b <c- S.V2 with {S.x, S.r, S.c2, S.s2}
     ] m (EP k S.b)).
   unfold Pr at 2.
   repeat (
    rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
    simpl E.eval_expr; unfold O.eval_op; simpl T.app_op; mem_upd_simpl).
   apply EqObs_Pr2 with {{S.x, S.r, S.c2, S.s2}} {{S.b}}.
   eqobs_in iSEE.
   vm_compute; trivial.
   unfold m'; intros t x H; Vset_mem_inversion H; subst; mem_upd_simpl; trivial.

   split; [trivial | ].
   transitivity (Pr E
    [
     S.x <- x;
     S.r <- Efst r;
     S.c2 <- Esnd r (+) c2;
     S.s2 <- s2;
     S.b <c- S.V2 with {S.x, S.r, S.c2, S.s2}
    ] m (EP k S.b)).
   rewrite (Pr_d_eq _ _ _ b), <- accepting_2.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c2, s2}}.
   sinline_l iEE V2.
   alloc_l iEE b S.b. deadcode iEE. eqobs_in iEE.

   apply Oeq_le; apply EqObs_Pr with {{x, r, c2, s2}}.
   deadcode iEE; eqobs_in iEE.
  Qed.

  Lemma KE_correct : Pr E [w <c- KE with {x, r, c1, c2, s1, s2} ] m
   (fun m => if R'_dec (m x) (m w) then true else false) == 1.
  Proof.
   assert (H1:Pr E 
    [ S.w <c- S.KE with {S.x, S.r, S.c1, S.c2, S.s1, S.s2} ] m'
    (fun m0 => if S.R'_dec k (m0 S.x) (m0 S.w) then true else false) == 1).   
   rewrite <- S.KE_correct.    
   transitivity
    (Pr E [ S.w <c- S.KE with {S.x, S.r, S.c1, S.c2, S.s1, S.s2} ] m'
    (fun m0 => if S.R'_dec k (m0 S.x) (m0 S.w) then true else false)).
   apply EqObs_deno with {{S.x, S.r, S.c1, S.c2, S.s1, S.s2}} {{S.x, S.w}}.
   deadcode iEE; eqobs_in iEE.
   intros; unfold charfun, restr; rewrite (H _ S.x), (H _ S.w); trivial.
   trivial.

   apply EqObs_deno with {{S.x, S.r, S.c1, S.c2, S.s1, S.s2}} {{S.x, S.w}}.   
   eqobs_in iESE.
   intros; unfold charfun, restr; rewrite (H _ S.x), (H _ S.w); trivial.
   trivial.

   unfold m'; mem_upd_simpl.
   unfold m'; mem_upd_simpl.
   intro H; destruct H_neq.
   rewrite <- (Bitstrings.BVxor_bij (snd (m r)) (m c1)).
   rewrite <- (Bitstrings.BVxor_bij (snd (m r)) (m c2)).
   rewrite (Bitstrings.BVxor_comm (m c1)).
   rewrite (Bitstrings.BVxor_comm (m c2)).
   rewrite H; trivial.

   apply S_accepting_1.
   apply S_accepting_2.

   rewrite <- H1.
   transitivity (Pr E
    [
     S.w <c- S.KE with {S.x, S.r, S.c1, S.c2, S.s1, S.s2};
     S.x <- x
    ] m' (fun m0 => if S.R'_dec k (m0 S.x) (m0 S.w) then true else false)).

   transitivity (Pr E
     ([
      S.x <- x; 
      S.r <- Efst r; 
      S.c1 <- Esnd r (+) c1;
      S.c2 <- Esnd r (+) c2;
      S.s1 <- s1;
      S.s2 <- s2;
      S.w <c- S.KE with {S.x, S.r, S.c1, S.c2, S.s1, S.s2};
      w <- S.w
     ])
     m
     (fun m0 => if R'_dec (m0 x) (m0 w) then true else false)).
   apply EqObs_deno with {{x, r, c1, c2, s1, s2}} {{x, w}}.
   sinline_l iEE KE.  
   alloc_l iEE w S.w. 
   eqobs_in iEE.
   intros; unfold charfun, restr; rewrite (H _ x), (H _ w); trivial.
   trivial.
 
   unfold Pr at 1.
   repeat (
    rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
    simpl E.eval_expr; unfold O.eval_op; simpl T.app_op; mem_upd_simpl).

   apply equiv_deno with 
    (kreq_mem {{x, S.x, S.r, S.c1, S.c2, S.s1, S.s2}})
    (req_mem_rel {{x}} (fun k m1 m2 => m2 S.x = m1 x /\ m2 S.w = m1 w)).

   eqobs_hd iEE;  eqobsrel_tail.
   unfold implMR, andR; intros; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   simpl; rewrite (H _ x), <- (H _ S.w); auto.

   intros m1 m2 [Hreq [Heq1 Heq2] ].
   intros; unfold charfun, restr, fone.
   rewrite Heq1, Heq2, (Hreq _ x); trivial.
   unfold m'. trivial.

   apply equiv_deno with
    (req_mem_rel {{S.x, S.r, S.c1, S.c2, S.s1, S.s2}} (EP1 (x =?= S.x)))
    (kreq_mem {{S.x, S.w}}).
   ep_eq_l iEE x S.x.
   unfold EP1; simpl; unfold O.eval_op; simpl.
   intros ? ? ? [Hreq H ].
   match goal with
    | H:is_true (if U_eq_dec ?x ?y then true else false) |- _ =>
      destruct (U_eq_dec x y); trivialb
   end.
   eqobs_in iEE.
   
   intros; unfold charfun, restr.
   rewrite (H _ S.x), (H _ S.w); trivial.
   repeat split. unfold m'.
   unfold EP1; simpl; unfold O.eval_op; simpl.
   unfold m'; mem_upd_simpl.
   match goal with
   |- is_true (if U_eq_dec ?x ?y then true else false) =>
    destruct (U_eq_dec x y); trivial
   end.
   elim n; trivial.
  Qed.
  
 End SOUNDNESS.
 
End SHVZK_of_HVZK.
