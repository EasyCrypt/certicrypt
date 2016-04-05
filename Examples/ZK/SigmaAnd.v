(** * SigmaAnd.v : AND composition of Sigma protocols *)

Require Import Sigma.
Require Import SigmaSem.

Set Implicit Arguments.


Module AND
 (S1 : SIGMA N1 Sem BP
  with Definition xT := T.User xT1 
  with Definition wT := T.User wT1
  with Definition rT := T.User rT1
  with Definition stateT := T.User stateT1
  with Definition cT := T.User Bitstring
  with Definition sT := T.User sT1
  with Definition V1_body := [ (Var.Lvar (T.User Bitstring) N1._c') <$- {0,1}^k ]
  with Definition V1_re := E.Evar (Var.Lvar (T.User Bitstring) N1._c'))
 (S2 : SIGMA N2 Sem BP
  with Definition xT := T.User xT2
   with Definition wT := T.User wT2
  with Definition rT := T.User rT2
  with Definition stateT := T.User stateT2
  with Definition cT := T.User Bitstring
  with Definition sT := T.User sT2
  with Definition V1_body := [ (Var.Lvar (T.User Bitstring) N2._c') <$- {0,1}^k ]
  with Definition V1_re := E.Evar (Var.Lvar (T.User Bitstring) N2._c')) 
 : SIGMA N Sem BP.

 (* Redefine notations for readability of proofs *)
 Notation "S1:x"      := (Var.Lvar (T.User xT1) 100).
 Notation "S1:w"      := (Var.Lvar (T.User wT1) 101).
 Notation "S1:r"      := (Var.Lvar (T.User rT1) 102).
 Notation "S1:state"  := (Var.Lvar (T.User stateT1) 103).
 Notation "S1:c"      := (Var.Lvar (T.User Bitstring) 104).
 Notation "S1:s"      := (Var.Lvar (T.User sT1) 105).
 Notation "S1:b"      := (Var.Lvar T.Bool 106).
 Notation "S1:rstate" := (Var.Lvar (T.Pair (T.User rT1) (T.User stateT1)) 107).
 Notation "S1:rs"     := (Var.Lvar (T.Pair (T.User rT1) (T.User sT1)) 108).

 Notation "S1:P1" := (Proc.mkP 100 
  (T.User xT1 :: T.User wT1 :: nil) 
  (T.Pair (T.User rT1) (T.User stateT1))).

 Notation "S1:P2" := (Proc.mkP 101 
  (T.User xT1 :: T.User wT1 :: T.User stateT1 :: T.User Bitstring :: nil) 
  (T.User sT1)).

 Notation "S1:V1" := (Proc.mkP 102 
  (T.User xT1 :: T.User rT1 :: nil) 
  (T.User Bitstring)).

 Notation "S1:V2" := (Proc.mkP 103 
  (T.User xT1 :: T.User rT1 :: T.User Bitstring :: T.User sT1 :: nil) 
  T.Bool).
 Notation "S1:S" := (Proc.mkP 104 
  (T.User xT1 :: T.User Bitstring :: nil) 
  (T.Pair (T.User rT1) (T.User sT1))).

 Notation "S1:KE" := (Proc.mkP 105 
  (T.User xT1 :: T.User rT1 :: T.User Bitstring :: T.User Bitstring :: T.User sT1 :: T.User sT1 :: nil) 
  (T.User wT1)).

 Notation "S2:x"      := (Var.Lvar (T.User xT2) 200).
 Notation "S2:w"      := (Var.Lvar (T.User wT2) 201).
 Notation "S2:r"      := (Var.Lvar (T.User rT2) 202).
 Notation "S2:state"  := (Var.Lvar (T.User stateT2) 203).
 Notation "S2:c"      := (Var.Lvar (T.User Bitstring) 204).
 Notation "S2:s"      := (Var.Lvar (T.User sT2) 205).
 Notation "S2:b"      := (Var.Lvar T.Bool 206).
 Notation "S2:rstate" := (Var.Lvar (T.Pair (T.User rT2) (T.User stateT2)) 207).
 Notation "S2:rs"     := (Var.Lvar (T.Pair (T.User rT2) (T.User sT2)) 208).

 Notation "S2:P1" := (Proc.mkP 200 
  (T.User xT2 :: T.User wT2 :: nil) 
  (T.Pair (T.User rT2) (T.User stateT2))).
 
 Notation "S2:P2" := (Proc.mkP 201 
  (T.User xT2 :: T.User wT2 :: T.User stateT2 :: T.User Bitstring :: nil) 
  (T.User sT2)).

 Notation "S2:V1" := (Proc.mkP 202
  (T.User xT2 :: T.User rT2 :: nil) 
  (T.User Bitstring)).

 Notation "S2:V2" := (Proc.mkP 203 
  (T.User xT2 :: T.User rT2 :: T.User Bitstring :: T.User sT2 :: nil) 
  T.Bool).

 Notation "S2:S" := (Proc.mkP 204 
  (T.User xT2 :: T.User Bitstring :: nil) 
  (T.Pair (T.User rT2) (T.User sT2))).

 Notation "S2:KE" := (Proc.mkP 205 
  (T.User xT2 :: T.User rT2 :: T.User Bitstring :: T.User Bitstring :: T.User sT2 :: T.User sT2 :: nil) 
  (T.User wT2)).

 Import N. 

 Notation _xT     := (T.Pair (T.User xT1) (T.User xT2)).
 Notation _wT     := (T.Pair (T.User wT1) (T.User wT2)).
 Notation _rT     := (T.Pair (T.User rT1) (T.User rT2)).
 Notation _stateT := (T.Pair (T.User stateT1) (T.User stateT2)).
 Notation _cT     := (T.User Bitstring).
 Notation _sT     := (T.Pair (T.User sT1) (T.User sT2)).

 Definition xT     := _xT.
 Definition wT     := _wT.
 Definition rT     := _rT.
 Definition stateT := _stateT.
 Definition cT     := _cT.
 Definition sT     := _sT.

 (** Knowledge relation *)
 Definition R : forall k, T.interp k xT -> T.interp k wT -> Prop :=
  fun k x w => S1.R k (fst x) (fst w) /\ S2.R k (snd x) (snd w).

 Definition R' : forall k, T.interp k xT -> T.interp k wT -> Prop :=
  fun k x w => S1.R' k (fst x) (fst w) /\ S2.R' k (snd x) (snd w).

 Lemma R_dec : forall k x y, sumbool (@R k x y) (~@R k x y).
 Proof.
  intros; unfold R.
  case (S1.R_dec k (fst x) (fst y)); [ | intuition].
  case (S2.R_dec k (snd x) (snd y)); intuition.
 Qed.

 Lemma R'_dec : forall k x y, sumbool (@R' k x y) (~@R' k x y).
 Proof.
  intros; unfold R'.
  case (S1.R'_dec k (fst x) (fst y)); [ | intuition].
  case (S2.R'_dec k (snd x) (snd y)); intuition.
 Qed.
  
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
 Notation KE := (Proc.mkP 6 (xT :: rT :: cT :: cT :: sT :: sT :: nil) wT).


 Definition P1_args : var_decl (Proc.targs P1) := 
  dcons _ x' (dcons _ w' (dnil _)).

 Definition P1_body : cmd :=
  [ 
   S1.x <- Efst x';
   S2.x <- Esnd x';
   S1.w <- Efst w';
   S2.w <- Esnd w';
   S1.rstate <c- S1.P1 with {S1.x, S1.w};
   S1.r <- Efst S1.rstate;
   S1.state <- Esnd S1.rstate;
   S2.rstate <c- S2.P1 with {S2.x, S2.w};
   S2.r <- Efst S2.rstate;
   S2.state <- Esnd S2.rstate
  ].

 Definition P1_re   := ((S1.r | S2.r) | (S1.state | S2.state)).


 Definition P2_args : var_decl (Proc.targs P2) := 
  dcons _ x' (dcons _ w' (dcons _ state' (dcons _ c' (dnil _)))).
 
 Definition P2_body :=
  [ 
   S1.s <c- S1.P2 with {Efst x', Efst w', Efst state', c'};
   S2.s <c- S2.P2 with {Esnd x', Esnd w', Esnd state', c'}
  ].
 
 Definition P2_re   := ((S1.s | S2.s)).


 Definition V1_args : var_decl (Proc.targs V1) := 
  dcons _ x' (dcons _ r' (dnil _)).
 
 Definition V1_body := [ c' <$- {0,1}^k ].

 Definition V1_re : E.expr cT := c'.


 Definition V2_args : var_decl (Proc.targs V2) := 
  dcons _ x' (dcons _ r' (dcons _ c' (dcons _ s' (dnil _)))).

 Definition V2_body :=
  [ 
   S1.b <c- S1.V2 with {Efst x', Efst r', c', Efst s'};
   S2.b <c- S2.V2 with {Esnd x', Esnd r', c', Esnd s'}
  ].
 
 Definition V2_re   := S1.b && S2.b.


 Definition S_args : var_decl (Proc.targs S) :=
  dcons _ x' (dcons _ c' (dnil _)).

 Definition S_body  :=
  [
   S1.rs <c- S1.S with {Efst x', c'};
   S2.rs <c- S2.S with {Esnd x', c'}
  ].
 
 Definition S_re := ( (Efst S1.rs | Efst S2.rs) |  (Esnd S1.rs | Esnd S2.rs) ).


 Definition KE_args : var_decl (Proc.targs KE) := 
  dcons _ x' (dcons _ r' (dcons _ c' (dcons _ c'' (dcons _ s' (dcons _ s''
   (dnil _)))))). 

 Definition KE_body := 
   [ 
    S1.w <c- S1.KE with { Efst x', Efst r', c', c'', Efst s', Efst s''};
    S2.w <c- S2.KE with { Esnd x', Esnd r', c', c'', Esnd s', Esnd s''}
   ].
 
 Definition KE_re   := (S1.w | S2.w).


 Section ENV.

  Let add_S2_P1 E := add_decl E S2.P1 S2.P1_args (refl_equal _) S2.P1_body S2.P1_re.
  Let add_S2_P2 E := add_decl E S2.P2 S2.P2_args (refl_equal _) S2.P2_body S2.P2_re.
  Let add_S2_V1 E := add_decl E S2.V1 S2.V1_args (refl_equal _) S2.V1_body S2.V1_re.
  Let add_S2_V2 E := add_decl E S2.V2 S2.V2_args (refl_equal _) S2.V2_body S2.V2_re.
  Let add_S2_S E  := add_decl E S2.S S2.S_args (refl_equal _) S2.S_body S2.S_re.
  Let add_S2_KE E := add_decl E S2.KE S2.KE_args (refl_equal _) S2.KE_body S2.KE_re.
  
  Definition _E := 
   add_S2_KE (add_S2_S (add_S2_P1 (add_S2_P2 (add_S2_V1 (add_S2_V2 S1.E))))).
  
  Let add_P1 E := add_decl E P1 P1_args (refl_equal _) P1_body P1_re.
  Let add_P2 E := add_decl E P2 P2_args (refl_equal _) P2_body P2_re.
  Let add_V1 E := add_decl E V1 V1_args (refl_equal _) V1_body V1_re.
  Let add_V2 E := add_decl E V2 V2_args (refl_equal _) V2_body V2_re.
  Let add_S  E := add_decl E S S_args (refl_equal _) S_body S_re.
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
  (add_basic_info E E S1.P1 S1.P1_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S1.P2 S1.P2_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S1.V1 S1.V1_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S1.V2 S1.V2_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S1.S S1.S_i   (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S1.KE S1.KE_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S2.P1 S2.P1_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S2.P2 S2.P2_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S2.V1 S2.V1_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S2.V2 S2.V2_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S2.S S2.S_i   (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S2.KE S2.KE_i (refl_equal _) (refl_equal _) (refl_equal _)
  (empty_info E E)))))))))))))))))).

 Definition iEE1 :=
  add_basic_info E S1.E S1.P1 S1.P1_i  (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E S1.E S1.P2 S1.P2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S1.E S1.V1 S1.V1_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S1.E S1.V2 S1.V2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S1.E S1.S S1.S_i   (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S1.E S1.KE S1.KE_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (empty_info E S1.E)))))).

 Definition iE1E :=
  add_basic_info S1.E E S1.P1 S1.P1_i  (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info S1.E E S1.P2 S1.P2_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S1.E E S1.V1 S1.V1_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S1.E E S1.V2 S1.V2_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S1.E E S1.S S1.S_i   (refl_equal _) (refl_equal _) (refl_equal _)
  (empty_info S1.E E))))).

 Definition iEE2 :=
  add_basic_info E S2.E S2.P1 S2.P1_i  (refl_equal _) (refl_equal _) (refl_equal _)  
  (add_basic_info E S2.E S2.P2 S2.P2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S2.E S2.V1 S2.V1_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S2.E S2.V2 S2.V2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S2.E S2.S S2.S_i   (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S2.E S2.KE S2.KE_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (empty_info E S2.E)))))).

 Definition iE2E :=
  add_basic_info S2.E E S2.P1 S2.P1_i  (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S2.E E S2.P2 S2.P2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info S2.E E S2.V1 S2.V1_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info S2.E E S2.V2 S2.V2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info S2.E E S2.S S2.S_i   (refl_equal _) (refl_equal _) (refl_equal _) 
  (empty_info S2.E E))))).

 Parameter P1_i : info P1_args P1_body P1_re.
 Parameter P2_i : info P2_args P2_body P2_re.
 Parameter V1_i : info V1_args V1_body V1_re.
 Parameter V2_i : info V2_args V2_body V2_re.
 Parameter S_i  : info S_args S_body S_re.
 Parameter KE_i : info KE_args KE_body KE_re.

 Definition protocol := 
  [
   rstate <c- P1 with {x, w};
   r <- Efst rstate;
   state <- Esnd rstate;
   c <c- V1 with {x, r};
   s <c- P2 with {x, w, state, c};
   b <c- V2 with {x, r, c, s}
  ].

 Definition protocol' := 
  [
   rstate <c- P1 with {x, w};
   r <- Efst rstate;
   state <- Esnd rstate;
   s <c- P2 with {x, w, state, c};
   b <c- V2 with {x, r, c, s}
  ].

 Definition simulation :=
  [
   rs <c- S with {x, c};
   r <- Efst rs;
   s <- Esnd rs
  ].

 Definition R1 : mem_rel := fun k m1 _ => R (m1 x) (m1 w).

 Lemma R1_dec : decMR R1.
 Proof.
  intros ? ? ?; apply R_dec.
 Qed.

 Hint Resolve R1_dec.

 Lemma Pr_accept_split : forall k E c (m:Mem.t k),
  Pr E c m (EP k S1.b) == 1%U ->
  Pr E c m (EP k S2.b) == 1%U ->
  Pr E (c ++ [b <- E.Eop O.Oand {S1.b, S2.b} ]) m (EP k b) == 1%U.
 Proof.
  intros k E' c m PrS1 PrS2.
  rewrite <- Pr_d_eq.
  unfold EP; simpl.
  apply Pr_and; trivial.
 Qed.

 Lemma completeness : forall k (m:Mem.t k), 
  R (m x) (m w) -> Pr E protocol m (EP k b) == 1%U.
 Proof.
  intros k m R_rstate.
  transitivity (Pr E 
   ([  
    rstate <c- P1 with {x, w};
     r <- Efst (rstate);
     state <- Esnd (rstate);
     c <c- V1 with {x, r};
     s <c- P2 with {x, w, state, c};
     S1.b <c- S1.V2 with {Efst x, Efst r, c, Efst s};
     S2.b <c- S2.V2 with {Esnd x, Esnd r, c, Esnd s}
    ] ++ 
    [ b <- E.Eop O.Oand {S1.b, S2.b} ])  m (EP k b)).
  apply EqObs_Pr with (I:={{x, w}}).
  sinline_l iEE V2; eqobs_in iEE.

  apply Pr_accept_split.

  transitivity (Pr E 
   ([ S1.x <- Efst x; S1.w <- Efst w ] ++ S1.protocol) m (EP k S1.b)).
  apply EqObs_Pr with (I:={{x,w}}).
  inline_l iEE P1.
  inline_l iEE V1.
  inline_l iEE P2.
  inline_l iEE V2.
  inline_r iEE S1.V1.
  alloc_l iEE c S1.c; ep iEE; deadcode iEE.
  eqobs_in iEE.

  transitivity (Pr S1.E 
   ([ S1.x <- Efst x; S1.w <- Efst w ] ++ S1.protocol) m (EP k S1.b)).

  apply EqObs_Pr with (I:={{x,w}}).
  eqobs_in iEE1.

  unfold Pr; rewrite deno_app_elim.
  repeat rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  rewrite deno_nil_elim.
  apply S1.completeness.
  simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  firstorder.

  transitivity (Pr E 
   ([ S2.x <- Esnd x; S2.w <- Esnd w ] ++ S2.protocol) m (EP k S2.b)).
  apply EqObs_Pr with (I:={{x,w}}).
  inline_l iEE P1.
  inline_l iEE V1.
  inline_l iEE P2.
  inline_l iEE V2.
  inline_r iEE S2.V1.
  alloc_l iEE c S2.c; ep iEE; deadcode iEE.
  eqobs_in iEE.

  transitivity (Pr S2.E 
   ([ S2.x <- Esnd x; S2.w <- Esnd w ] ++ S2.protocol) m (EP k S2.b)).

  apply EqObs_Pr with (I:={{x,w}}).
  eqobs_in iEE2.

  unfold Pr; rewrite deno_app_elim.
  repeat rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  rewrite deno_nil_elim.
  apply S2.completeness.
  simpl; unfold O.eval_op; simpl.
  mem_upd_simpl; firstorder.
 Qed.

 Lemma SHVZK : 
  equiv (req_mem_rel {{x, w, c}} R1)
  E protocol'
  E simulation
  (kreq_mem {{r, c, s}}).
 Proof.
  unfold protocol', simulation.  

  apply equiv_trans_trans with E
   ([
     S1.x <- Efst x; S1.w <- Efst w; S1.c <- c;
     S2.x <- Esnd x; S2.w <- Esnd w; S2.c <- c
    ] ++
    S1.protocol' ++ 
    S2.protocol' ++ 
    [ 
     r <- (S1.r | S2.r); 
     s <- (S1.s | S2.s) 
    ]); [ auto | | auto | |].
  intros k m1 m2; intros [H1 H2]; split; auto.
 
  rewrite req_mem_rel_req_mem; simpl.
  inline_l iEE P1.
  inline_l iEE P2.
  sinline_l iEE V2.
  swap iEE; eqobs_in iEE.

  apply equiv_trans_trans with E
   ([ 
     S1.x <- Efst x; S1.w <- Efst w; S1.c <- c;
     S2.x <- Esnd x; S2.w <- Esnd w; S2.c <- c
    ] ++
    S1.simulation ++ 
    S2.simulation ++ 
    [ 
     r <- (S1.r | S2.r); 
     s <- (S1.s | S2.s) 
    ]); [ auto | | auto | | sinline_r iEE S; eqobs_in iEE].
  intros k m1 m2; intros [H1 H2]; split; auto.

  apply equiv_app with 
   (req_mem_rel {{c, S1.x, S1.c, S1.w, S2.x, S2.c, S2.w}} (S1.R1 /-\ S2.R1)).
  
  unfold andR; eqobsrel_tail.
  simpl; unfold implMR; simpl; unfold O.eval_op; simpl.
  unfold R1, R, S1.R1, S2.R1; intros k m1 m2 [Hreq HR1].
  mem_upd_simpl; trivial.

  apply equiv_app with (req_mem_rel {{c, S1.r, S1.s, S2.x, S2.c, S2.w}} S2.R1).
    
  compute_assertion Heq1 X1 (modify (refl1_info iEE) Vset.empty S1.protocol').
  compute_assertion Heq2 X2 (modify (refl1_info iEE) Vset.empty S1.simulation).
  apply modify_correct in Heq1.
  apply modify_correct in Heq2.
  eapply equiv_union_Modify.
  split; [eexact Heq1 | eexact Heq2].
  apply decMR_and; intros k m1 m2; [apply S1.R_dec | apply S2.R_dec].

  unfold req_mem_rel.
  rewrite <- andR_assoc.
  eapply equiv_inv_Modify with (X1:={{S2.x, S2.w}}) (X2:=Vset.empty).
  unfold S2.R1; intros k m1 m2 m1' m2' Hreq _ HR.
  rewrite <- (Hreq _ S2.x), <- (Hreq _ S2.w); trivial.
  eexact Heq1.
  eexact Heq2.
  vm_compute; trivial.
  vm_compute; trivial.
  vm_compute; trivial.

  apply equiv_trans_trans with S1.E S1.protocol'; auto.
  apply decMR_req_mem_rel; intros k m1 m2; apply S1.R_dec.
  intros k m1 m2 [Hreq HR]; split; trivial.
  apply transMR_req_mem_rel with Vset.empty Vset.empty; vm_compute; trivial.
  eqobs_in iEE1.

  apply equiv_trans_trans with S1.E S1.simulation; auto.
  apply decMR_req_mem_rel; intros k m1 m2; apply S1.R_dec.
  intros k m1 m2 [Hreq HR]; split; trivial.
  apply transMR_req_mem_rel with Vset.empty Vset.empty; vm_compute; trivial.

  clear.
  simpl; rewrite req_mem_rel_trueR.
  apply equiv_sub with (3:=S1.SHVZK).
  intros; apply req_mem_rel_weaken with (3:=H); vm_compute; trivial.
  intros; apply req_mem_weaken with (2:=H); vm_compute; trivial.

  eqobs_in iE1E.

  
  (** Idem for [R2] *)  
  apply equiv_app with (req_mem_rel {{c, S1.r, S1.s, S2.r, S2.s}} trueR).

  compute_assertion Heq1 X1 (modify (refl1_info iEE) Vset.empty S2.protocol').
  compute_assertion Heq2 X2 (modify (refl1_info iEE) Vset.empty S2.simulation).
  apply modify_correct in Heq1.
  apply modify_correct in Heq2.
  eapply equiv_union_Modify.
  split; [eexact Heq1 | eexact Heq2].
  intros k m1 m2; apply S2.R_dec.

  apply equiv_trans_trans with S2.E S2.protocol'; auto.
  apply decMR_req_mem_rel; intros k m1 m2; apply S2.R_dec.
  intros k m1 m2 [Hreq HR]; split; trivial.
  apply transMR_req_mem_rel with Vset.empty Vset.empty; vm_compute; trivial.
  eqobs_in iEE2.

  apply equiv_trans_trans with S2.E S2.simulation; auto.
  apply decMR_req_mem_rel; intros k m1 m2; apply S2.R_dec.
  intros k m1 m2 [Hreq HR]; split; trivial.
  apply transMR_req_mem_rel with Vset.empty Vset.empty; vm_compute; trivial.

  simpl.
  simpl; rewrite req_mem_rel_trueR.
  apply equiv_sub with (3:=S2.SHVZK).
  intros; apply req_mem_rel_weaken with (3:=H); vm_compute; trivial.
  intros; apply req_mem_weaken with (2:=H); vm_compute; trivial.

  eqobs_in iE2E.
  eqobs_in iEE.
 Qed.

 Section SOUNDNESS.

  Close Scope positive_scope.
  Close Scope nat_scope. 
 
  Variable k : nat.
  Variable m : Mem.t k.

  Hypothesis H_neq : m c1 <> m c2. 
  Hypothesis accepting_1 : Pr E [b <c- V2 with {x, r, c1, s1} ] m (EP k b) == 1.
  Hypothesis accepting_2 : Pr E [b <c- V2 with {x, r, c2, s2} ] m (EP k b) == 1.
  
  Definition R1' k (m:Mem.t k) : boolO := 
   if S1.R'_dec k (m S1.x) (m S1.w) then true else false.

  Definition R2' k (m:Mem.t k) : boolO := 
   if S2.R'_dec k (m S2.x) (m S2.w) then true else false.

  Let m' := 
   m{!S1.x <-- fst (m x)!}{!S1.r <-- fst (m r)!}{!S1.c1 <-- m c1!}
    {!S1.c2 <-- m c2!}{!S1.s1 <-- fst (m s1)!}{!S1.s2 <-- fst (m s2)!}    
    {!S2.x <-- snd (m x)!}{!S2.r <-- snd (m r)!}{!S2.c1 <-- m c1!}
    {!S2.c2 <-- m c2!}{!S2.s1 <-- snd (m s1)!}{!S2.s2 <-- snd (m s2)!}.

  Lemma S1_accepting_1 : Pr S1.E 
   [S1.b <c- S1.V2 with {S1.x, S1.r, S1.c1, S1.s1} ] m' (EP k S1.b) == 1.
  Proof.
   transitivity
    (Pr E 
     [
      S1.x <- Efst x;
      S1.r <- Efst r;
      S1.c1 <- c1;
      S1.s1 <- Efst s1;
      S1.b <c- S1.V2 with {S1.x, S1.r, S1.c1, S1.s1}
     ] m (EP k S1.b)).
   unfold Pr at 2.
   repeat (
    rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
    simpl E.eval_expr; unfold O.eval_op; simpl T.app_op;
    mem_upd_simpl).
   apply EqObs_Pr2 with {{S1.x, S1.r, S1.c1, S1.s1}} {{S1.b}}.
   eqobs_in iE1E.
   vm_compute; trivial.
   unfold m'; intros t x H; Vset_mem_inversion H; subst; mem_upd_simpl; trivial.

   split; [trivial | ].
   transitivity (Pr E
    [
     S1.x <- Efst x;
     S1.r <- Efst r;
     S1.c1 <- c1;
     S1.s1 <- Efst s1;
     S2.x <- Esnd x;
     S2.r <- Esnd r;
     S2.c1 <- c1;
     S2.s1 <- Esnd s1;
     S1.b <c- S1.V2 with {S1.x, S1.r, S1.c1, S1.s1};
     S2.b <c- S2.V2 with {S2.x, S2.r, S2.c1, S2.s1}
    ] m (EP k (S1.b && S2.b))).
   rewrite (Pr_d_eq _ _ _ b), <- accepting_1.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c1, s1}}.
   sinline_l iEE V2; eqobs_in iEE.

   assert (H:EP k (S1.b && S2.b) <= EP k S1.b).
    unfold EP, charfun, restr; simpl; intro m0; case (m0 S1.b); trivial.
   rewrite H.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c1, s1}}.
   deadcode iEE; eqobs_in iEE.
  Qed.

  Lemma S1_accepting_2 : Pr S1.E 
   [S1.b <c- S1.V2 with {S1.x, S1.r, S1.c2, S1.s2} ] m' (EP k S1.b) == 1.
  Proof.
   transitivity
    (Pr E 
     [
      S1.x <- Efst x;
      S1.r <- Efst r;
      S1.c2 <- c2;
      S1.s2 <- Efst s2;
      S1.b <c- S1.V2 with {S1.x, S1.r, S1.c2, S1.s2}
     ] m (EP k S1.b)).
   unfold Pr at 2.
   repeat (
    rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
    simpl E.eval_expr; unfold O.eval_op; simpl T.app_op;
    mem_upd_simpl).
   apply EqObs_Pr2 with {{S1.x, S1.r, S1.c2, S1.s2}} {{S1.b}}.
   eqobs_in iE1E.
   vm_compute; trivial.
   unfold m'; intros t x H; Vset_mem_inversion H; subst; mem_upd_simpl; trivial.

   split; [trivial | ].
   transitivity (Pr E
    [
     S1.x <- Efst x;
     S1.r <- Efst r;
     S1.c2 <- c2;
     S1.s2 <- Efst s2;
     S2.x <- Esnd x;
     S2.r <- Esnd r;
     S2.c2 <- c2;
     S2.s2 <- Esnd s2;
     S1.b <c- S1.V2 with {S1.x, S1.r, S1.c2, S1.s2};
     S2.b <c- S2.V2 with {S2.x, S2.r, S2.c2, S2.s2}
    ] m (EP k (S1.b && S2.b))).
   rewrite (Pr_d_eq _ _ _ b), <- accepting_2.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c2, s2}}.
   sinline_l iEE V2; eqobs_in iEE.

   assert (H:EP k (S1.b && S2.b) <= EP k S1.b).
    unfold EP, charfun, restr; simpl; intro m0; case (m0 S1.b); trivial.
   rewrite H.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c2, s2}}.
   deadcode iEE; eqobs_in iEE.
  Qed.

  Lemma S2_accepting_1 : Pr S2.E 
   [S2.b <c- S2.V2 with {S2.x, S2.r, S2.c1, S2.s1} ] m' (EP k S2.b) == 1.
  Proof.
   transitivity
    (Pr E 
     [
      S2.x <- Esnd x;
      S2.r <- Esnd r;
      S2.c1 <- c1;
      S2.s1 <- Esnd s1;
      S2.b <c- S2.V2 with {S2.x, S2.r, S2.c1, S2.s1}
     ] m (EP k S2.b)).
   unfold Pr at 2.
   repeat (
    rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
    simpl E.eval_expr; unfold O.eval_op; simpl T.app_op;
    mem_upd_simpl).
   apply EqObs_Pr2 with {{S2.x, S2.r, S2.c1, S2.s1}} {{S2.b}}.
   eqobs_in iE2E.
   vm_compute; trivial.
   unfold m'; intros t x H; Vset_mem_inversion H; subst; mem_upd_simpl. 

   split; [trivial | ].
   transitivity (Pr E
    [
     S1.x <- Efst x;
     S1.r <- Efst r;
     S1.c1 <- c1;
     S1.s1 <- Efst s1;
     S2.x <- Esnd x;
     S2.r <- Esnd r;
     S2.c1 <- c1;
     S2.s1 <- Esnd s1;
     S1.b <c- S1.V2 with {S1.x, S1.r, S1.c1, S1.s1};
     S2.b <c- S2.V2 with {S2.x, S2.r, S2.c1, S2.s1}
    ] m (EP k (S1.b && S2.b))).
   rewrite (Pr_d_eq _ _ _ b), <- accepting_1.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c1, s1}}.
   sinline_l iEE V2; eqobs_in iEE.

   assert (H:EP k (S1.b && S2.b) <= EP k S2.b).
    unfold EP, charfun, restr; simpl; unfold O.eval_op; simpl.
    intro m0; case (m0 S2.b); [ | rewrite andb_false_r]; trivial.
   rewrite H.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c1, s1}}.
   deadcode iEE; eqobs_in iEE.
  Qed.

  Lemma S2_accepting_2 : Pr S2.E 
   [S2.b <c- S2.V2 with {S2.x, S2.r, S2.c2, S2.s2} ] m' (EP k S2.b) == 1.
  Proof.
   transitivity
    (Pr E 
     [
      S2.x <- Esnd x;
      S2.r <- Esnd r;
      S2.c2 <- c2;
      S2.s2 <- Esnd s2;
      S2.b <c- S2.V2 with {S2.x, S2.r, S2.c2, S2.s2}
     ] m (EP k S2.b)).
   unfold Pr at 2.
   repeat (
    rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
    simpl E.eval_expr; unfold O.eval_op; simpl T.app_op;
    mem_upd_simpl).
   apply EqObs_Pr2 with {{S2.x, S2.r, S2.c2, S2.s2}} {{S2.b}}.
   eqobs_in iE2E.
   vm_compute; trivial.
   unfold m'; intros t x H; Vset_mem_inversion H; subst; mem_upd_simpl; trivial.

   split; [trivial | ].
   transitivity (Pr E
    [
     S1.x <- Efst x;
     S1.r <- Efst r;
     S1.c2 <- c2;
     S1.s2 <- Efst s2;
     S2.x <- Esnd x;
     S2.r <- Esnd r;
     S2.c2 <- c2;
     S2.s2 <- Esnd s2;
     S1.b <c- S1.V2 with {S1.x, S1.r, S1.c2, S1.s2};
     S2.b <c- S2.V2 with {S2.x, S2.r, S2.c2, S2.s2}
    ] m (EP k (S1.b && S2.b))).
   rewrite (Pr_d_eq _ _ _ b), <- accepting_2.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c2, s2}}.
   sinline_l iEE V2; eqobs_in iEE.

   assert (H:EP k (S1.b && S2.b) <= EP k S2.b).
    unfold EP, charfun, restr; simpl; unfold O.eval_op; simpl.
    intro m0; case (m0 S2.b); [ | rewrite andb_false_r]; trivial.
   rewrite H.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c2, s2}}.
   deadcode iEE; eqobs_in iEE.
  Qed.

  Lemma KE_correct : Pr E [w <c- KE with {x, r, c1, c2, s1, s2} ] m
   (fun m => if R'_dec (m x) (m w) then true else false) == 1.
  Proof.
   assert (H1:Pr E 
    [ 
     S1.w <c- S1.KE with {S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2};
     S2.w <c- S2.KE with {S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2} 
    ] m'
    (fun m0 => if S1.R'_dec k (m0 S1.x) (m0 S1.w) then true else false) == 1).   
   rewrite <- S1.KE_correct.    
   transitivity
    (Pr E 
     [ S1.w <c- S1.KE with {S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2} ] m'
    (fun m0 => if S1.R'_dec k (m0 S1.x) (m0 S1.w) then true else false)).
   apply EqObs_deno with {{S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2}} {{S1.x, S1.w}}.
   deadcode iEE; eqobs_in iEE.
   intros; unfold charfun, restr; rewrite (H _ S1.x), (H _ S1.w); trivial.
   trivial.
   apply EqObs_deno with {{S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2}} {{S1.x, S1.w}}.   eqobs_in iEE1.
   intros; unfold charfun, restr; rewrite (H _ S1.x), (H _ S1.w); trivial.
   trivial.

   unfold m'; mem_upd_simpl.
   apply S1_accepting_1.
   apply S1_accepting_2.

   assert (H2:Pr E 
    [ 
     S1.w <c- S1.KE with {S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2};
     S2.w <c- S2.KE with {S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2} 
    ] m'
    (fun m0 => if S2.R'_dec k (m0 S2.x) (m0 S2.w) then true else false) == 1).   
   rewrite <- S2.KE_correct.    
   transitivity
    (Pr E 
     [ S2.w <c- S2.KE with {S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2} ] m'
    (fun m0 => if S2.R'_dec k (m0 S2.x) (m0 S2.w) then true else false)).
   apply EqObs_deno with {{S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2}} {{S2.x, S2.w}}.
   deadcode iEE; eqobs_in iEE.
   intros; unfold charfun, restr; rewrite (H _ S2.x), (H _ S2.w); trivial.
   trivial.
   apply EqObs_deno with {{S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2}} {{S2.x, S2.w}}.
   eqobs_in iEE2.
   intros; unfold charfun, restr; rewrite (H _ S2.x), (H _ S2.w); trivial.
   trivial.

   unfold m'; mem_upd_simpl.
   apply S2_accepting_1.
   apply S2_accepting_2.

   rewrite <- (Pr_and _ _ _ _ _ H1 H2).
   transitivity (Pr E
    [
     S1.w <c- S1.KE with {S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2};
     S2.w <c- S2.KE with {S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2};
     S1.x <- Efst x;
     S2.x <- Esnd x
    ] m' (@R1' k [&&] @R2' k)).

   transitivity (Pr E
     ([
      S1.x <- Efst x; 
      S1.r <- Efst r; 
      S1.c1 <- c1;
      S1.c2 <- c2;
      S1.s1 <- Efst s1;
      S1.s2 <- Efst s2;
      S2.x <- Esnd x; 
      S2.r <- Esnd r; 
      S2.c1 <- c1;
      S2.c2 <- c2;
      S2.s1 <- Esnd s1;
      S2.s2 <- Esnd s2;
      S1.w <c- S1.KE with {S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2};
      S2.w <c- S2.KE with {S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2};
      w <- (S1.w | S2.w)
     ])
     m
     (fun m0 => if R'_dec (m0 x) (m0 w) then true else false)).
   apply EqObs_deno with {{x, r, c1, c2, s1, s2}} {{x, w}}.
   sinline_l iEE KE; eqobs_in iEE.
   intros; unfold charfun, restr; rewrite (H _ x), (H _ w); trivial.
   trivial.
 
   unfold Pr at 1.
   repeat (
    rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
    simpl E.eval_expr; unfold O.eval_op; simpl T.app_op;
    mem_upd_simpl).

   apply equiv_deno with
    (kreq_mem {{x, S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2, 
                   S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2}})
    (req_mem_rel {{x}}
     (fun k m1 m2 => (m2 S1.x) = fst (m1 x) /\ (m2 S1.w) = fst (m1 w) /\
                     (m2 S2.x) = snd (m1 x) /\ (m2 S2.w) = snd (m1 w))).
   eqobs_hd iEE.
   eqobsrel_tail.
   unfold implMR, andR; intros; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   simpl; rewrite <- (H _ x), <- (H _ S1.w), <- (H _ S2.w); auto.
   
   intros m1 m2 [Hreq [Heq1 [Heq2 [Heq3 Heq4] ] ] ].
   intros; unfold charfun, restr, fone, andP, R1', R2'.
   rewrite Heq1, Heq2, Heq3, Heq4, (Hreq _ x); trivial.
   case (R'_dec (m2 x) (m1 w)); unfold R',R;
   case (S1.R'_dec k (fst (m2 x)) (fst (m1 w))); intro HR1';
   case (S2.R'_dec k (snd (m2 x)) (snd (m1 w))); intro HR2'; trivial; try tauto.
   trivial.

   apply equiv_deno with
    (req_mem_rel {{S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2, 
                   S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2}}
     (EP1 (Efst x =?= S1.x) /-\ EP1 (Esnd x =?= S2.x)))
   (kreq_mem {{S1.x, S1.w, S2.x, S2.w}}).
   ep_eq_l iEE (Efst x) S1.x.
   unfold EP1; simpl; unfold O.eval_op; simpl.
   intros ? ? ? [Hreq [H _] ].
   match goal with
    | H:is_true (if U_eq_dec ?x ?y then true else false) |- _ =>
      destruct (U_eq_dec x y); trivialb
   end.
   ep_eq_l iEE (Esnd x) S2.x.
   unfold EP1; simpl; unfold O.eval_op; simpl.
   intros ? ? ? [Hreq [_ H] ].
   match goal with
    | H:is_true (if U_eq_dec ?x ?y then true else false) |- _ =>
      destruct (U_eq_dec x y); trivialb
   end.
   eqobs_in iEE.
   
   intros; unfold charfun, restr, andP, R1', R2'.
   rewrite (H _ S1.x), (H _ S2.x), (H _ S1.w), (H _ S2.w); trivial.
   repeat split.
   unfold EP1; simpl; unfold O.eval_op; simpl.
   unfold m'; mem_upd_simpl.
   match goal with
   |- is_true (if U_eq_dec ?x ?y then true else false) =>
    destruct (U_eq_dec x y); trivial
   end.
   elim n; trivial.
   unfold EP1; simpl; unfold O.eval_op; simpl.
   unfold m'; mem_upd_simpl.
   match goal with
   |- is_true (if U_eq_dec ?x ?y then true else false) =>
    destruct (U_eq_dec x y); trivial
   end.
   elim n; trivial.
  Qed.
  
 End SOUNDNESS.
 
End AND.
