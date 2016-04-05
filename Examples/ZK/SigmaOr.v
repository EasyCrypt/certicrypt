(** * SigmaOr.v : OR composition of Sigma protocols *)

Require Import SigmaSem.
Require Import Sigma.

Set Implicit Arguments.

Local Close Scope bool_scope.

Module OR 
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
 Notation _wT     := (T.Sum (T.User wT1) (T.User wT2)). 
 Notation _rT     := (T.Pair (T.User rT1) (T.User rT2)).
 Notation _stateT := (T.Pair (T.Sum (T.User stateT1) (T.User stateT2)) 
  (T.Pair (T.User Bitstring) (T.Sum (T.User sT1) (T.User sT2)))).
 Notation _cT     := (T.User Bitstring).
 Notation _sT     := (T.Pair (T.Pair (T.User Bitstring) (T.User sT1)) 
  (T.Pair (T.User Bitstring) (T.User sT2))).

 Definition xT     := _xT.
 Definition wT     := _wT.
 Definition rT     := _rT.
 Definition stateT := _stateT.
 Definition cT     := _cT.
 Definition sT     := _sT.

 (** Knowledge relation *)
 Definition R : forall k, T.interp k xT -> T.interp k wT -> Prop :=
  fun k x w => 
   match w with
    | inl w1 => S1.R k (fst x) w1 /\ exists w2, S2.R k (snd x) w2
    | inr w2 => S2.R k (snd x) w2 /\ exists w1, S1.R k (fst x) w1
   end.

 Definition R' : forall k, T.interp k xT -> T.interp k wT -> Prop :=
  fun k x w => 
   match w with
    | inl w1 => S1.R' k (fst x) w1
    | inr w2 => S2.R' k (snd x) w2
   end.

 Lemma R_dec : forall k (x:T.interp k xT) (w:T.interp k wT), 
  sumbool (R x w) (~R x w).
 Admitted.

 Lemma R'_dec : forall k (x:T.interp k xT) (w:T.interp k wT), 
  sumbool (R' x w) (~R' x w).
 Proof.
  intros k (x1,x2) [w1 | w2]; unfold R'; simpl.
  case (S1.R'_dec k x1 w1); tauto.
  case (S2.R'_dec k x2 w2); tauto.
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
    If Isl w' then
     [
      S1.rstate <c- S1.P1 with {Efst x', Projl w'};
      S1.r <- Efst S1.rstate;
      S1.state <- Esnd S1.rstate;
      S2.c <$- {0,1}^k;
      S2.rs <c- S2.S with {Esnd x', S2.c};
      S2.r <- Efst S2.rs;
      state <- (Inl S1.state | (S2.c | Inr (Esnd S2.rs)))
     ]
    else
     [
      S2.rstate <c- S2.P1 with {Esnd x', Projr w'};
      S2.r <- Efst S2.rstate;
      S2.state <- Esnd S2.rstate;
      S1.c <$- {0,1}^k;
      S1.rs <c- S1.S with {Efst x', S1.c};
      S1.r <- Efst S1.rs;
      state <- (Inr S2.state | (S1.c | Inl (Esnd S1.rs)))
     ]
  ].

 Definition P1_re := ((S1.r | S2.r) | state).

  
 Definition P2_args : var_decl (Proc.targs P2) := 
  dcons _ x' (dcons _ w' (dcons _ state' (dcons _ c' (dnil _)))).

 Definition P2_body :=
  [ 
   If Isl w' then  
    [ 
     S2.c <- Efst (Esnd state');
     S1.c <- S2.c (+) c';
     S1.s <c- S1.P2 with {Efst x', Projl w', Projl (Efst state'), S1.c};
     S2.s <- Projr (Esnd (Esnd state')) 
    ]
   else
    [ 
     S1.c <- Efst (Esnd state');
     S2.c <- S1.c (+) c';
     S2.s <c- S2.P2 with {Esnd x', Projr w', Projr (Efst state'), S2.c};
     S1.s <- Projl (Esnd (Esnd state')) 
    ]
  ].

 Definition P2_re   := ((S1.c | S1.s) | (S2.c | S2.s)). 

 
 Definition V1_args : var_decl (Proc.targs V1) := 
  dcons _ x' (dcons _ r' (dnil _)).
 
 Definition V1_body := [ c' <$- {0,1}^k ].

 Definition V1_re : E.expr cT := c'.


 Definition V2_args : var_decl (Proc.targs V2) := 
  dcons _ x' (dcons _ r' (dcons _ c' (dcons _ s' (dnil _)))).
 
 Definition V2_body :=
  [
   S1.b <c- S1.V2 with {Efst x', Efst r', Efst (Efst s'), Esnd (Efst s')};
   S2.b <c- S2.V2 with {Esnd x', Esnd r', Efst (Esnd s'), Esnd (Esnd s')}
  ].

 Definition V2_re   := 
  (c' =?= Efst (Efst s') (+) Efst (Esnd s')) && S1.b && S2.b.


 Definition S_args : var_decl (Proc.targs S) :=
  dcons _ x' (dcons _ c' (dnil _)).

 Definition S_body  :=
  [
   S2.c <$- {0,1}^k;
   S1.c <- S2.c (+) c';
   S1.rs <c- S1.S with {Efst x', S1.c};
   S2.rs <c- S2.S with {Esnd x', S2.c}
  ].

 Definition S_re := 
  ( (Efst S1.rs | Efst S2.rs ) | 
    ( (S1.c | Esnd S1.rs) | (S2.c | Esnd S2.rs) ) ).


 Definition KE_args : var_decl (Proc.targs KE) := 
  dcons _ x' (dcons _ r' (dcons _ c' (dcons _ c'' (dcons _ s' (dcons _ s''
   (dnil _)))))). 

 Definition KE_body := 
  [ 
   If ! (Efst (Efst s') =?= Efst (Efst s'')) then
    [ 
     S1.w <c- S1.KE with { Efst x', Efst r', Efst (Efst s'), Efst (Efst s''), Esnd (Efst s'), Esnd (Efst s'')};
     w' <- Inl S1.w
    ] else
    [ 
     S2.w <c- S2.KE with { Esnd x', Esnd r', Efst (Esnd s'), Efst (Esnd s''), Esnd (Esnd s'), Esnd (Esnd s'')};
     w' <- Inr S2.w
    ]     
   ].
 
 Definition KE_re   : E.expr wT := w'.

 Section ENV.

  Let add_S2_P1 E := add_decl E S2.P1 S2.P1_args (refl_equal _) S2.P1_body S2.P1_re.
  Let add_S2_P2 E := add_decl E S2.P2 S2.P2_args (refl_equal _) S2.P2_body S2.P2_re.
  Let add_S2_V1 E := add_decl E S2.V1 S2.V1_args (refl_equal _) S2.V1_body S2.V1_re.
  Let add_S2_V2 E := add_decl E S2.V2 S2.V2_args (refl_equal _) S2.V2_body S2.V2_re.
  Let add_S2_S E  := add_decl E S2.S S2.S_args   (refl_equal _) S2.S_body S2.S_re.
  Let add_S2_KE E := add_decl E S2.KE S2.KE_args (refl_equal _) S2.KE_body S2.KE_re.
  
  Definition _E := 
   add_S2_KE (add_S2_S (add_S2_P1 (add_S2_P2 (add_S2_V1 (add_S2_V2 S1.E))))).
  
  Let add_P1 E := add_decl E P1 P1_args (refl_equal _) P1_body P1_re.
  Let add_P2 E := add_decl E P2 P2_args (refl_equal _) P2_body P2_re.
  Let add_V1 E := add_decl E V1 V1_args (refl_equal _) V1_body V1_re.
  Let add_V2 E := add_decl E V2 V2_args (refl_equal _) V2_body V2_re.
  Let add_S E  := add_decl E S S_args   (refl_equal _) S_body S_re.
  Let add_KE E := add_decl E KE KE_args (refl_equal _) KE_body KE_re.

  Definition E := add_KE (add_S (add_P1 (add_P2 (add_V1 (add_V2 _E))))).

 End ENV.

 Definition iEE :=
  add_refl_info_O P1 (fv_expr P1_re) Vset.empty Vset.empty 
  (add_refl_info P2
  (add_refl_info V1
  (add_refl_info_O V2 (fv_expr V2_re) Vset.empty Vset.empty
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
  (add_basic_info S1.E E S1.KE S1.KE_i (refl_equal _) (refl_equal _) (refl_equal _)
  (empty_info S1.E E)))))).

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
  (add_basic_info S2.E E S2.KE S2.KE_i (refl_equal _) (refl_equal _) (refl_equal _)
  (empty_info S2.E E)))))).

 Definition iE1E1 :=
  add_basic_info S1.E S1.E S1.P1 S1.P1_i  (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S1.E S1.E S1.P2 S1.P2_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S1.E S1.E S1.V1 S1.V1_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S1.E S1.E S1.V2 S1.V2_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S1.E S1.E S1.S S1.S_i   (refl_equal _) (refl_equal _) (refl_equal _)
  (empty_info S1.E S1.E))))).

 Definition iE2E2 :=
  add_basic_info S2.E S2.E S2.P1 S2.P1_i  (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S2.E S2.E S2.P2 S2.P2_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S2.E S2.E S2.V1 S2.V1_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S2.E S2.E S2.V2 S2.V2_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info S2.E S2.E S2.S S2.S_i   (refl_equal _) (refl_equal _) (refl_equal _)
  (empty_info S2.E S2.E))))).  

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

 Lemma decMR_R : decMR R1.
 Proof.
  intros ? ? ?; apply R_dec.
 Qed.

 Definition _R1 : mem_rel := fun k m1 _ => 
  match m1 w with
  | inl w1 => S1.R k (fst (m1 x)) w1
  | _ => False
  end.

 Lemma decMR_R1 : decMR _R1.
 Proof.
  intros k m1 m2; unfold _R1.
  case (m1 w).
  intro; apply S1.R_dec.
  right; intro; trivial.
 Qed.

 Definition _R2 : mem_rel := fun k m1 _ => 
  match m1 w with
  | inr w2 => S2.R k (snd (m1 x)) w2
  | _ => False
  end.

 Lemma decMR_R2 : decMR _R2.
 Proof.
  intros k m1 m2; unfold _R2.
  case (m1 w).
  right; intro; trivial.
  intro; apply S2.R_dec.
 Qed.

 Hint Resolve decMR_R1 decMR_R2.

 Lemma Pr_accept_split : forall k E c (m:Mem.t k),
  Pr E c m (EP k S1.b) == 1%U ->
  Pr E c m (EP k S2.b) == 1%U ->
  Pr E (c ++ [b <- S1.b && S2.b]) m (EP k b) == 1%U.
 Proof.
  intros k E' c m PrS1 PrS2.
  rewrite <- Pr_d_eq.
  unfold EP; simpl.
  apply Pr_and; trivial.
 Qed.

 Lemma S1_R1_dec : decMR S1.R1.
 Proof.
  intros x m1 m2; apply S1.R_dec.
 Qed.
 
 Hint Resolve S1_R1_dec.

 Lemma S1_HVZK :
  equiv (req_mem_rel {{S1.x, S1.w}} S1.R1)
  S1.E (rev (tail (rev S1.protocol)))
  S1.E ((S1.c <$- {0,1}^k) :: S1.simulation)
  (kreq_mem {{S1.x, S1.r, S1.c, S1.s}}).
 Proof.
  apply equiv_trans_trans with S1.E ((S1.c <$- {0,1}^k) :: S1.protocol').
  auto.
  intros x m1 m2 [H H0]; split; trivial.
  auto.
  sinline_l iE1E1 S1.V1; swap iE1E1; eqobs_in iE1E1.
  apply equiv_cons with (req_mem_rel {{S1.x, S1.w, S1.c}} S1.R1).
  eqobsrel_tail; unfold implMR; simpl.
  intros k m1 m2 [H H0] v Hin; unfold S1.R1.
  mem_upd_simpl.
  rewrite <- req_mem_rel_trueR.
  compute_assertion Heq1 res1 (modify (refl1_info iE1E) {{c}} S1.protocol').
  compute_assertion Heq2 res2 (modify (refl1_info iE1E) {{c}} S1.simulation).
  apply modify_correct in Heq1; apply modify_correct in Heq2.
  eapply equiv_union_Modify.
  split; [eexact Heq1 | eexact Heq2].
  auto.
  simpl.
  rewrite req_mem_rel_trueR.
  apply equiv_weaken with (2:=S1.SHVZK).
  intros; apply req_mem_weaken with (2:=H); vm_compute; trivial. 
 Qed.

 Lemma S2_R1_dec : decMR S2.R1.
 Proof.
  intros x m1 m2; apply S2.R_dec.
 Qed.
 
 Hint Resolve S2_R1_dec.

 Lemma S2_HVZK :
  equiv (req_mem_rel {{S2.x, S2.w}} S2.R1)
  S2.E (rev (tail (rev S2.protocol)))
  S2.E ((S2.c <$- {0,1}^k) :: S2.simulation)
  (kreq_mem {{S2.x, S2.r, S2.c, S2.s}}).
 Proof.
  apply equiv_trans_trans with S2.E ((S2.c <$- {0,1}^k) :: S2.protocol').
  auto.
  intros x m1 m2 [H H0]; split; trivial.
  auto.
  sinline_l iE2E2 S2.V1; swap iE2E2; eqobs_in iE2E2.
  apply equiv_cons with
   (req_mem_rel {{S2.x, S2.w, S2.c}} S2.R1).
  eqobsrel_tail; unfold implMR; simpl.
  intros k m1 m2 [H H0] v Hin; unfold S2.R1.
  mem_upd_simpl.
 
  rewrite <- req_mem_rel_trueR.
  compute_assertion Heq1 res1 (modify (refl1_info iE2E) {{c}} S2.protocol').
  compute_assertion Heq2 res2 (modify (refl1_info iE2E) {{c}} S2.simulation).
  apply modify_correct in Heq1; apply modify_correct in Heq2.
  eapply equiv_union_Modify.
  split; [eexact Heq1 | eexact Heq2].
  auto.
  simpl.
  rewrite req_mem_rel_trueR.
  apply equiv_weaken with (2:=S2.SHVZK).
  intros; apply req_mem_weaken with (2:=H); vm_compute; trivial. 
 Qed.


 Lemma completeness : forall k (m:Mem.t k), 
  R (m x) (m w) -> Pr E protocol m (EP k b) == 1%U.
 Proof.
  intros k m; unfold R.
  case_eq (m w); [intros w1 Hw [HR HD] | intros w2 Hw [HR HD] ].

  transitivity (Pr E 
   ([
     S1.x <- Efst x;
     S2.x <- Esnd x;
     S1.w <- Projl w;
     S2.c <$- {0,1}^k
    ] ++ 
    S1.protocol ++    
    S2.simulation ++
    [    
     S2.b <c- S2.V2 with {Esnd x, Efst S2.rs, S2.c, Esnd S2.rs}
    ] ++
    [
     b <- S1.b && S2.b
    ]) m (EP k b)).
  
  apply equiv_deno with 
   (P:=req_mem_rel {{x, w}} _R1)
   (Q:=req_mem_rel {{b}} trueR).   
  unfold protocol; simpl.
  inline_l iEE P1.
  inline_l iEE V1.
  inline_l iEE P2.
  sinline_l iEE V2.
  ep_eq iEE (Isl w) true.
   intros ? m1 m2 [Hreq HR1]; unfold _R1 in HR1.
   simpl; unfold O.eval_op; simpl.
   rewrite <- (Hreq _ w); trivial.
   destruct (m1 w); auto.
  sinline_r iEE S1.V1.
  
  rewrite req_mem_rel_req_mem; fold_eqobs_tac.
  apply EqObs_trans with 
   E  
   [
    S1.rstate <c- S1.P1 with {Efst x, Projl w};
    S2.c <$- {0,1}^k;
    S2.rs <c- S2.S with {Esnd x, S2.c};
    c <$- {0,1}^k;
    S1.c <- c (+) S2.c;
    S1.s <c- S1.P2 with {Efst x, Projl w, Esnd S1.rstate, S2.c (+) c};
    S1.b <c- S1.V2 with {Efst x, Efst S1.rstate, S2.c (+) c, S1.s};
    S2.b <c- S2.V2 with {Esnd x, Efst S2.rs, S2.c, Esnd S2.rs};
    b <- S1.b && S2.b
   ].
  ep iEE; deadcode iEE.
  eqobs_in iEE.

  apply EqObs_trans with E  
   [
    S1.rstate <c- S1.P1 with {Efst x, Projl w};
    S2.c <$- {0,1}^k;
    S2.rs <c- S2.S with {Esnd x, S2.c};
    S1.c <$- {0,1}^k;
    c <- S1.c (+) S2.c;
    S1.s <c- S1.P2 with {Efst x, Projl w, Esnd S1.rstate, S2.c (+) c};
    S1.b <c- S1.V2 with {Efst x, Efst S1.rstate, S2.c (+) c, S1.s};
    S2.b <c- S2.V2 with {Esnd x, Efst S2.rs, S2.c, Esnd S2.rs};
    b <- S1.b && S2.b
   ].
  eqobs_ctxt iEE.
  union_mod iEE; eapply equiv_sub; [ | | apply optimistic_sampling ].
   simpl; intros; apply req_mem_weaken with (2:=H); vm_compute; trivial.
   simpl; intros; apply req_mem_weaken with (2:=H); vm_compute; trivial.
   trivial.
   trivial.
   discriminate.

  ep iEE; deadcode iEE.
  swap iEE; eqobs_in iEE.

  intros m1 m2 [Hm _]; unfold charfun, restr, EP; simpl; rewrite (Hm _ b); trivial.
  split; [ | unfold _R1; rewrite Hw]; trivial.  
  
  repeat rewrite <- app_ass; apply Pr_accept_split.

  (* The first protocol is complete *)
  transitivity (Pr E 
   ([S1.x <- Efst (x); S1.w <- Projl w] ++ S1.protocol) m (EP k S1.b)).
  apply EqObs_deno with {{x, w}} {{S1.b}}.
  deadcode iEE; eqobs_in iEE.
  intros; unfold charfun, EP, restr; simpl; rewrite (H _ S1.b); trivial.
  trivial.

  simpl; unfold Pr.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  rewrite <- S1.completeness.
  apply EqObs_deno with {{S1.x, S1.w}} {{S1.b}}.
  eqobs_in iEE1.
  intros; unfold charfun, EP, restr; simpl; rewrite (H _ S1.b); trivial.
  apply req_mem_refl.
  simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  rewrite Hw; trivial.

  (* The simulation of the second protocol is accepting *)
  destruct HD as [w2 HR2].
  transitivity (Pr E 
   ([
    S2.x <- Esnd x; 
    S2.c <$- {0,1}^k
   ] ++
   S2.simulation ++ 
   [ S2.b <c- S2.V2 with {S2.x, S2.r, S2.c, S2.s} ]) (m{!S2.w <-- w2!})
   (EP k S2.b)).
  apply EqObs_deno with {{x}} {{S2.b}}.
  ep iEE; deadcode iEE; eqobs_in iEE.
  intros m1 m2 Hm; unfold charfun, restr, EP; simpl; rewrite (Hm _ S2.b); trivial.
  apply req_mem_upd_disjoint; trivial.

  transitivity (Pr S2.E 
   ([S2.x <- Esnd x; S2.c <$- {0,1}^k] ++ 
    S2.simulation ++
    [S2.b <c- S2.V2 with {S2.x, S2.r, S2.c, S2.s} ])
   (m{!S2.w <-- w2!})
   (EP k S2.b)).
  apply EqObs_Pr with {{x}}; eqobs_in iEE2.

  transitivity (Pr S2.E 
   ([S2.x <- Esnd x] ++ S2.protocol)
   (m{!S2.w <-- w2!})
   (EP k S2.b)).
  symmetry.

  unfold Pr; simpl app.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.  
  apply equiv_deno with 
   (req_mem_rel {{S2.x, S2.w}} S2.R1)
   (req_mem_rel {{S2.b}} trueR).
  eqobs_tl iE2E2; apply S2_HVZK.

  intros m1 m2 [H _]; unfold charfun, restr, EP; simpl; rewrite (H _ S2.b); trivial.

  split; [ auto | ].
  unfold S2.R1; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  trivial.

  unfold Pr; simpl app.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  apply S2.completeness.
  simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  trivial.


  (** Idem for [R2] *)
  transitivity (Pr E 
   ([
     S1.x <- Efst x;
     S2.x <- Esnd x;
     S2.w <- Projr w;
     S1.c <$- {0,1}^k
    ] ++ 
    S1.simulation ++
    S2.protocol ++ 
    [    
     S1.b <c- S1.V2 with {Efst x, Efst S1.rs, S1.c, Esnd S1.rs}
    ] ++
    [
     b <- S1.b && S2.b
    ]) m (EP k b)).
  
  apply equiv_deno with 
   (P:=req_mem_rel {{x, w}} _R2)
   (Q:=req_mem_rel {{b}} trueR).   
  unfold protocol; simpl.
  inline_l iEE P1.
  inline_l iEE V1.
  inline_l iEE P2.
  sinline_l iEE V2.
  ep_eq iEE (Isl w) false.
   intros ? m1 m2 [Hreq HR2]; unfold _R2 in HR2.
   simpl; unfold O.eval_op; simpl.
   rewrite <- (Hreq _ w); trivial.
   destruct (m1 w); auto; elim HR2.
  sinline_r iEE S2.V1.
  
  rewrite req_mem_rel_req_mem; fold_eqobs_tac.
  apply EqObs_trans with 
   E  
   [
    S2.rstate <c- S2.P1 with {Esnd x, Projr w};
    S1.c <$- {0,1}^k;
    S1.rs <c- S1.S with {Efst x, S1.c};
    c <$- {0,1}^k;
    S2.c <- c (+) S1.c;
    S2.s <c- S2.P2 with {Esnd x, Projr w, Esnd S2.rstate, S1.c (+) c};
    S1.b <c- S1.V2 with {Efst x, Efst S1.rs, S1.c, Esnd S1.rs};
    S2.b <c- S2.V2 with {Esnd x, Efst S2.rstate, S1.c (+) c, S2.s};
    b <- S1.b && S2.b
   ].
  ep iEE; deadcode iEE; eqobs_in iEE.

  apply EqObs_trans with E  
   [
    S2.rstate <c- S2.P1 with {Esnd x, Projr w};
    S1.c <$- {0,1}^k;
    S1.rs <c- S1.S with {Efst x, S1.c};
    S2.c <$- {0,1}^k;
    c <- S2.c (+) S1.c;
    S2.s <c- S2.P2 with {Esnd x, Projr w, Esnd S2.rstate, S1.c (+) c};
    S1.b <c- S1.V2 with {Efst x, Efst S1.rs, S1.c, Esnd S1.rs};
    S2.b <c- S2.V2 with {Esnd x, Efst S2.rstate, S1.c (+) c, S2.s};
    b <- S1.b && S2.b
   ].
  eqobs_ctxt iEE.
  union_mod iEE; eapply equiv_sub; [ | | apply optimistic_sampling ].
   simpl; intros; apply req_mem_weaken with (2:=H); vm_compute; trivial.
   simpl; intros; apply req_mem_weaken with (2:=H); vm_compute; trivial.
   trivial.
   trivial.
   discriminate.

  ep iEE; deadcode iEE.
  swap iEE; eqobs_in iEE.

  intros m1 m2 [Hm _]; unfold charfun, restr, EP; simpl; rewrite (Hm _ b); trivial.
  split; [ | unfold _R2; rewrite Hw]; trivial.  
  
  repeat rewrite <- app_ass; apply Pr_accept_split.

  (* The simulation of the first protocol is accepting *)
  destruct HD as [w1 HR1].
  transitivity (Pr E 
   ([
    S1.x <- Efst x; 
    S1.c <$- {0,1}^k
   ] ++
   S1.simulation ++ 
   [ S1.b <c- S1.V2 with {S1.x, S1.r, S1.c, S1.s} ]) (m{!S1.w <-- w1!})
   (EP k S1.b)).
  apply EqObs_deno with {{x}} {{S1.b}}.
  ep iEE; deadcode iEE; eqobs_in iEE.
  intros m1 m2 Hm; unfold charfun, restr, EP; simpl; rewrite (Hm _ S1.b); trivial.
  apply req_mem_upd_disjoint; trivial.

  transitivity (Pr S1.E 
   ([S1.x <- Efst x; S1.c <$- {0,1}^k] ++ 
    S1.simulation ++
    [S1.b <c- S1.V2 with {S1.x, S1.r, S1.c, S1.s} ])
   (m{!S1.w <-- w1!})
   (EP k S1.b)).
  apply EqObs_Pr with {{x}}; eqobs_in iEE1.

  transitivity (Pr S1.E 
   ([S1.x <- Efst x] ++ S1.protocol)
   (m{!S1.w <-- w1!})
   (EP k S1.b)).
  symmetry.

  unfold Pr; simpl app.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.  
  apply equiv_deno with 
   (req_mem_rel {{S1.x, S1.w}} S1.R1)
   (req_mem_rel {{S1.b}} trueR).
  eqobs_tl iE1E1; apply S1_HVZK.

  intros m1 m2 [H _]; unfold charfun, restr, EP; simpl; rewrite (H _ S1.b); trivial.

  split; [ auto | ].
  unfold S1.R1; simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  trivial.

  unfold Pr; simpl app.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  apply S1.completeness.
  simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  trivial.

  (* The second protocol is complete *)
  transitivity (Pr E 
   ([S2.x <- Esnd x; S2.w <- Projr w] ++ S2.protocol) m (EP k S2.b)).
  apply EqObs_deno with {{x, w}} {{S2.b}}.
  deadcode iEE; eqobs_in iEE.
  intros; unfold charfun, EP, restr; simpl; rewrite (H _ S2.b); trivial.
  trivial.

  simpl; unfold Pr.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  rewrite <- S2.completeness.
  apply EqObs_deno with {{S2.x, S2.w}} {{S2.b}}.
  eqobs_in iEE2.
  intros; unfold charfun, EP, restr; simpl; rewrite (H _ S2.b); trivial.
  apply req_mem_refl.
  simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  rewrite Hw; trivial.
 Qed.

 Lemma SHVZK : 
  equiv (req_mem_rel {{x, w, c}} R1)
  E protocol'
  E simulation
  (kreq_mem {{r, c, s}}).
 Proof.
  apply equiv_case1 with _R1.
  auto.

  rewrite req_mem_rel_req_mem.
  apply equiv_trans_trans with E
   (([
     S1.x <- Efst x; S1.w <- Projl w;
     S2.x <- Esnd x; S2.c <$- {0,1}^k; S1.c <- S2.c (+) c
    ] ++ 
    S1.protocol') ++
    S2.simulation ++
    [
     r <- (S1.r | Efst S2.rs);
     s <- ((S1.c | S1.s) | (S2.c | Esnd S2.rs))
    ]
   ); [ auto | firstorder | auto | |].

  inline_l iEE P1.
  inline_l iEE P2.
  sinline_l iEE V2.
  ep_eq iEE (Isl w) true.
   unfold _R1; intros ? ? ? [Hreq HR1].   
   simpl; unfold O.eval_op; simpl; rewrite <- (Hreq _ w); trivial.
   destruct (m1 w); auto.
  rewrite proj1_MR.
  ep iEE; deadcode iEE.
  swap iEE; eqobs_in iEE.

  apply equiv_trans_trans with E
  (([
     S1.x <- Efst x; 
     S1.w <- Projl w;
     S2.x <- Esnd x;
     S2.c <$- {0,1}^k;
     S1.c <- S2.c (+) c
    ] ++
    S1.simulation) ++
    S2.simulation ++
    [
     r <- (S1.r | Efst S2.rs);  
     s <- ((S1.c | S1.s) | (S2.c | Esnd S2.rs))
    ]); [ auto | firstorder | auto | | ].
  
  apply equiv_app with (req_mem_rel {{c, S1.c, S2.c, S2.x, S1.r, S1.s}} trueR).

  apply equiv_app with (req_mem_rel {{c, S1.c, S2.c, S2.x, S1.x, S1.w}} S1.R1).
  eqobsrel_tail.
  unfold implMR; simpl; unfold O.eval_op; simpl.
  unfold _R1, S1.R1; intros k m1 m2 [Hreq HR1] v.
  mem_upd_simpl.
  destruct (m1 w); autob.

  apply equiv_trans_trans with S1.E S1.protocol'.
  apply decMR_req_mem_rel; intros ? ? ?; apply S1.R_dec.
  firstorder.
  apply transMR_req_mem_rel with Vset.empty Vset.empty; auto with set.
  eqobs_in iEE1.

  apply equiv_trans_trans with S1.E S1.simulation.
  apply decMR_req_mem_rel; intros ? ? ?; apply S1.R_dec.
  firstorder.
  apply transMR_req_mem_rel with Vset.empty Vset.empty; auto with set.

  compute_assertion Heq1 res1 (modify (refl1_info iE1E) Vset.empty S1.protocol').
  compute_assertion Heq2 res2 (modify (refl1_info iE1E) Vset.empty S1.simulation).
  apply modify_correct in Heq1; apply modify_correct in Heq2.
  eapply equiv_union_Modify.
  split; [eexact Heq1 | eexact Heq2].
  intros ? ? ?; apply S1.R_dec.
  rewrite req_mem_rel_trueR.

  apply equiv_sub with (3:=S1.SHVZK).
  intros; apply req_mem_rel_weaken with (3:=H); vm_compute; trivial. 
  intros; apply req_mem_weaken with (2:=H); vm_compute; trivial. 

  eqobs_in iE1E.

  eqobs_in iEE.

  rewrite proj1_MR.
  sinline_r iEE S; swap iEE; eqobs_in iEE.

  (** Idem for [R2] *)
  apply equiv_strengthen with (req_mem_rel {{x, w, c}} _R2).
  unfold R1, R, _R1, _R2, notR; intros k m1 m2 [ [Hreq HR] HnR1].
  split; [ trivial | destruct (m1 w); destruct HR; auto].

  apply equiv_trans_trans with E
   (([
     S1.x <- Efst x; S2.w <- Projr w;
     S2.x <- Esnd x; S1.c <$- {0,1}^k; S2.c <- S1.c (+) c
    ] ++ 
    S2.protocol') ++
    S1.simulation ++   
    [
     r <- (Efst S1.rs | S2.r);
     s <- ((S1.c | Esnd S1.rs) | (S2.c | S2.s))
    ]
   ); [ auto | firstorder | auto | |].

  inline_l iEE P1.
  inline_l iEE P2.
  sinline_l iEE V2.
  ep_eq iEE (Isl w) false.
   unfold _R2; intros ? ? ? [Hreq HR2].
   simpl; unfold O.eval_op; simpl.
   rewrite <- (Hreq _ w); trivial.
   destruct (m1 w); autob.
  rewrite req_mem_rel_req_mem.
  ep iEE; deadcode iEE.
  swap iEE; eqobs_in iEE.
  
  apply equiv_trans_trans with E
  (([
     S1.x <- Efst x; 
     S2.w <- Projr w;
     S2.x <- Esnd x;
     S1.c <$- {0,1}^k;
     S2.c <- S1.c (+) c
    ] ++
    S2.simulation) ++
    S1.simulation ++
    [
     r <- (Efst S1.rs | S2.r);
     s <- ((S1.c | Esnd S1.rs) | (S2.c | S2.s))
    ]); [ auto | firstorder | auto | | ].

  apply equiv_app with (req_mem_rel {{c, S1.c, S2.c, S1.x, S2.r, S2.s}} trueR).

  apply equiv_app with (req_mem_rel {{c, S1.c, S2.c, S1.x, S2.x, S2.w}} S2.R1).
  eqobsrel_tail.
  unfold implMR; simpl; unfold O.eval_op; simpl.
  unfold _R2, S2.R1; intros k m1 m2 [Hreq HR1] v.
  mem_upd_simpl.
  destruct (m1 w); trivialb.

  apply equiv_trans_trans with S2.E S2.protocol'.
  apply decMR_req_mem_rel; intros ? ? ?; apply S2.R_dec.
  firstorder.
  apply transMR_req_mem_rel with Vset.empty Vset.empty; auto with set.
  eqobs_in iEE2.

  apply equiv_trans_trans with S2.E S2.simulation.
  apply decMR_req_mem_rel; intros ? ? ?; apply S2.R_dec.
  firstorder.
  apply transMR_req_mem_rel with Vset.empty Vset.empty; auto with set.

  compute_assertion Heq1 res1 (modify (refl1_info iE2E) Vset.empty S2.protocol').
  compute_assertion Heq2 res2 (modify (refl1_info iE2E) Vset.empty S2.simulation).
  apply modify_correct in Heq1; apply modify_correct in Heq2.
  eapply equiv_union_Modify.
  split; [eexact Heq1 | eexact Heq2].
  intros ? ? ?; apply S2.R_dec.
  rewrite req_mem_rel_trueR.
  apply equiv_sub with (3:=S2.SHVZK).
  intros; apply req_mem_rel_weaken with (3:=H); vm_compute; trivial. 
  intros; apply req_mem_weaken with (2:=H); vm_compute; trivial. 
  eqobs_in iE2E.

  eqobs_in iEE.

  rewrite req_mem_rel_req_mem.
  apply equiv_trans_trans with E
   ([
     S1.x <- Efst x; 
     S2.w <- Projr w;
     S2.x <- Esnd x;
     S2.c <$- {0,1}^k;
     S1.c <- S2.c (+) c
    ] ++
    S2.simulation ++
    S1.simulation ++
    [
     r <- (Efst S1.rs | S2.r);
     s <- ((S1.c | Esnd S1.rs) | (S2.c | S2.s))
    ]); [ auto | firstorder | auto | | ].

  eqobs_ctxt iEE.
  union_mod iEE; eapply equiv_sub; [ | | apply optimistic_sampling ].
   simpl; intros; apply req_mem_weaken with (2:=H); vm_compute; trivial.
   intros; apply req_mem_weaken with (2:=H); vm_compute; trivial.
   trivial.
   trivial.
   discriminate.
   
  sinline_r iEE S; swap iEE; eqobs_in iEE.
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
   m{!S1.x <-- fst (m x)!}{!S1.r <-- fst (m r)!}
    {!S1.c1 <-- fst (fst (m s1))!}{!S1.s1 <-- snd (fst (m s1))!}
    {!S1.c2 <-- fst (fst (m s2))!}{!S1.s2 <-- snd (fst (m s2))!}
    {!S2.x <-- snd (m x)!}{!S2.r <-- snd (m r)!}
    {!S2.c1 <-- fst (snd (m s1))!}{!S2.s1 <-- snd (snd (m s1))!}
    {!S2.c2 <-- fst (snd (m s2))!}{!S2.s2 <-- snd (snd (m s2))!}.

  Lemma S1_accepting_1 : Pr S1.E 
   [S1.b <c- S1.V2 with {S1.x, S1.r, S1.c1, S1.s1} ] m' (EP k S1.b) == 1.
  Proof.
   transitivity
    (Pr E 
     [
      S1.x <- Efst x;
      S1.r <- Efst r;
      S1.c1 <- Efst (Efst s1);
      S1.s1 <- Esnd (Efst s1);
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
   unfold m'; intros t x H; Vset_mem_inversion H; subst; mem_upd_simpl.

   split; [trivial | ].
   transitivity (Pr E
    [
     S1.x <- Efst x;
     S1.r <- Efst r;
     S1.c1 <- Efst (Efst s1);
     S1.s1 <- Esnd (Efst s1);
     S2.x <- Esnd x;
     S2.r <- Esnd r;
     S2.c1 <- Efst (Esnd s1);
     S2.s1 <- Esnd (Esnd s1);
     S1.b <c- S1.V2 with {S1.x, S1.r, S1.c1, S1.s1};
     S2.b <c- S2.V2 with {S2.x, S2.r, S2.c1, S2.s1}
    ] m (EP k ((c1 =?= Efst (Efst s1) (+) Efst (Esnd s1)) && S1.b && S2.b))).
   rewrite (Pr_d_eq _ _ _ b), <- accepting_1.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c1, s1}}.
   sinline_l iEE V2; eqobs_in iEE. 

   assert (H:EP k ((c1 =?= Efst (Efst s1) (+) Efst (Esnd s1)) && S1.b && S2.b) <= EP k S1.b).
    unfold EP, charfun, restr; intro m0; simpl; unfold O.eval_op; simpl.
    case (m0 S1.b); [ | rewrite andb_false_r]; trivial.
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
      S1.c2 <- Efst (Efst s2);
      S1.s2 <- Esnd (Efst s2);
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
   unfold m'; intros t x H; Vset_mem_inversion H; subst; mem_upd_simpl.

   split; [trivial | ].
   transitivity (Pr E
    [
     S1.x <- Efst x;
     S1.r <- Efst r;
     S1.c2 <- Efst (Efst s2);
     S1.s2 <- Esnd (Efst s2);
     S2.x <- Esnd x;
     S2.r <- Esnd r;
     S2.c2 <- Efst (Esnd s2);
     S2.s2 <- Esnd (Esnd s2);
     S1.b <c- S1.V2 with {S1.x, S1.r, S1.c2, S1.s2};
     S2.b <c- S2.V2 with {S2.x, S2.r, S2.c2, S2.s2}
    ] m (EP k ((c2 =?= Efst (Efst s2) (+) Efst (Esnd s2)) && S1.b && S2.b))).
   rewrite (Pr_d_eq _ _ _ b), <- accepting_2.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c2, s2}}.
   sinline_l iEE V2; eqobs_in iEE. 

   assert (H:EP k ((c2 =?= Efst (Efst s2) (+) Efst (Esnd s2)) && S1.b && S2.b) <= EP k S1.b).
    unfold EP, charfun, restr; intro m0; simpl; unfold O.eval_op; simpl.
    case (m0 S1.b); [ | rewrite andb_false_r]; trivial.
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
      S2.c1 <- Efst (Esnd s1);
      S2.s1 <- Esnd (Esnd s1);
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
     S1.c1 <- Efst (Efst s1);
     S1.s1 <- Esnd (Efst s1);
     S2.x <- Esnd x;
     S2.r <- Esnd r;
     S2.c1 <- Efst (Esnd s1);
     S2.s1 <- Esnd (Esnd s1);
     S1.b <c- S1.V2 with {S1.x, S1.r, S1.c1, S1.s1};
     S2.b <c- S2.V2 with {S2.x, S2.r, S2.c1, S2.s1}
    ] m (EP k ((c1 =?= Efst (Efst s1) (+) Efst (Esnd s1)) && S1.b && S2.b))).
   rewrite (Pr_d_eq _ _ _ b), <- accepting_1.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c1, s1}}.
   sinline_l iEE V2; eqobs_in iEE. 

   assert (H:EP k ((c1 =?= Efst (Efst s1) (+) Efst (Esnd s1)) && S1.b && S2.b) <= EP k S2.b).
    unfold EP, charfun, restr; intro m0; simpl; unfold O.eval_op; simpl.
    case (m0 S2.b); [ | rewrite andb_false_r]; trivial.
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
      S2.c2 <- Efst (Esnd s2);
      S2.s2 <- Esnd (Esnd s2);
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
   unfold m'; intros t x H; Vset_mem_inversion H; subst; mem_upd_simpl.

   split; [trivial | ].
   transitivity (Pr E
    [
     S1.x <- Efst x;
     S1.r <- Efst r;
     S1.c2 <- Efst (Efst s2);
     S1.s2 <- Esnd (Efst s2);
     S2.x <- Esnd x;
     S2.r <- Esnd r;
     S2.c2 <- Efst (Esnd s2);
     S2.s2 <- Esnd (Esnd s2);
     S1.b <c- S1.V2 with {S1.x, S1.r, S1.c2, S1.s2};
     S2.b <c- S2.V2 with {S2.x, S2.r, S2.c2, S2.s2}
    ] m (EP k ((c2 =?= Efst (Efst s2) (+) Efst (Esnd s2)) && S1.b && S2.b))).
   rewrite (Pr_d_eq _ _ _ b), <- accepting_2.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c2, s2}}.
   sinline_l iEE V2; eqobs_in iEE. 

   assert (H:EP k ((c2 =?= Efst (Efst s2) (+) Efst (Esnd s2)) && S1.b && S2.b) <= EP k S2.b).
    unfold EP, charfun, restr; intro m0; simpl; unfold O.eval_op; simpl.
    case (m0 S2.b); [ | rewrite andb_false_r]; trivial.
   rewrite H.
   apply Oeq_le.
   apply EqObs_Pr with {{x, r, c2, s2}}.
   deadcode iEE; eqobs_in iEE.
  Qed.

  Lemma challenge_neq :
   fst (fst (m s1)) <> fst (fst (m s2)) \/
   (fst (fst (m s1)) = fst (fst (m s2)) /\
    fst (snd (m s1)) <> fst (snd (m s2))).
  Proof.
   set (c1'  := fst (fst (m s1))).
   set (c1'' := fst (fst (m s2))).
   set (c2'  := fst (snd (m s1))).
   set (c2'' := fst (snd (m s2))).

   assert (m c1 = Bvector.BVxor _ c1' c2').

   assert (1 <= Pr E nil m (EP k (c1 =?= Efst (Efst s1) (+) Efst (Esnd s1)))).
   apply Ole_eq_right with (Pr E 
    [
     S1.b <c- S1.V2 with {Efst x, Efst r, Efst (Efst s1), Esnd (Efst s1)};
     S2.b <c- S2.V2 with {Esnd x, Esnd r, Efst (Esnd s1), Esnd (Esnd s1)}
    ] m (EP k (c1 =?= Efst (Efst s1) (+) Efst (Esnd s1)))).
   rewrite (Pr_d_eq _ _ _ b).
   rewrite <- accepting_1.   

   apply Ole_eq_left with (Pr E
    ([
     S1.b <c- S1.V2 with {Efst x, Efst r, Efst (Efst s1), Esnd (Efst s1)};
     S2.b <c- S2.V2 with {Esnd x, Esnd r, Efst (Esnd s1), Esnd (Esnd s1)}
    ] ++
    [
     b <- (c1 =?= Efst (Efst s1) (+) Efst (Esnd s1)) && S1.b && S2.b
    ]) m (EP k b)).
   apply EqObs_Pr with {{x, r, c1, s1}}.
   sinline_l iEE V2; eqobs_in iEE.
   
   rewrite <- Pr_d_eq, <- Pr_d_eq.
   apply mu_le_compat; [ trivial | ].
   unfold charfun, restr, EP; simpl; unfold O.eval_op; simpl; intro.
   match goal with
   |- _ <= (if ?X then _ else _) => case X; trivial 
   end.
   
   apply EqObs_Pr with {{x, r, c1, s1}}.
   deadcode iEE; eqobs_in iEE.

   unfold Pr in H; rewrite deno_nil_elim in H.
   unfold charfun, restr, EP in H; simpl in H; unfold O.eval_op in H; simpl in H.
   apply (Bitstrings.Veqb_true (m c1)); unfold c1', c2'; simpl.
   match goal with
   |- ?X = true => destruct X; auto
   end.
   rewrite H in H_neq; clear H.


   assert (m c2 = Bvector.BVxor _ c1'' c2'').

   assert (1 <= Pr E nil m (EP k (c2 =?= Efst (Efst s2) (+) Efst (Esnd s2)))).
   apply Ole_eq_right with (Pr E 
    [
     S1.b <c- S1.V2 with {Efst x, Efst r, Efst (Efst s2), Esnd (Efst s2)};
     S2.b <c- S2.V2 with {Esnd x, Esnd r, Efst (Esnd s2), Esnd (Esnd s2)}
    ] m (EP k (c2 =?= Efst (Efst s2) (+) Efst (Esnd s2)))).
   rewrite (Pr_d_eq _ _ _ b).
   rewrite <- accepting_2.   

   apply Ole_eq_left with (Pr E
    ([
     S1.b <c- S1.V2 with {Efst x, Efst r, Efst (Efst s2), Esnd (Efst s2)};
     S2.b <c- S2.V2 with {Esnd x, Esnd r, Efst (Esnd s2), Esnd (Esnd s2)}
    ] ++
    [
     b <- (c2 =?= Efst (Efst s2) (+) Efst (Esnd s2)) && S1.b && S2.b
    ]) m (EP k b)).
   apply EqObs_Pr with {{x, r, c2, s2}}.
   sinline_l iEE V2; eqobs_in iEE.
   
   rewrite <- Pr_d_eq, <- Pr_d_eq.
   apply mu_le_compat; [ trivial | ].
   unfold charfun, restr, EP; simpl; unfold O.eval_op; simpl; intro.
   match goal with
   |- _ <= (if ?X then _ else _) => case X; trivial 
   end.
   
   apply EqObs_Pr with {{x, r, c2, s2}}.
   deadcode iEE; eqobs_in iEE.

   unfold Pr in H; rewrite deno_nil_elim in H.
   unfold charfun, restr, EP in H; simpl in H; unfold O.eval_op in H; simpl in H.
   apply (Bitstrings.Veqb_true (m c2)); unfold c1'', c2''; simpl.
   match goal with
   |- ?X = true => destruct X; auto
   end.
   rewrite H in H_neq; clear H.

   generalize (Bitstrings.Veqb_spec c1' c1'').
   case (Bitstrings.Veqb c1' c1''); [right | left; trivial].
   split; [ trivial | ].
   intro H0; rewrite H, H0 in H_neq.  
   elim H_neq; trivial.  
  Qed.

  Definition O1 k : Mem.t k -o> boolO := fun m =>
   if S1.R'_dec _ (m S1.x) (m S1.w) then true else false.

  Definition O2 k : Mem.t k -o> boolO := fun m =>
   if S2.R'_dec _ (m S2.x) (m S2.w) then true else false.
   
  Lemma KE_correct : Pr E [w <c- KE with {x, r, c1, c2, s1, s2} ] m
   (fun m => if R'_dec (m x) (m w) then true else false) == 1.
  Proof.
   clear -m'.
   destruct challenge_neq as [H_neq1 | [Heq2 Hneq2] ].

   transitivity (Pr E 
    [ 
     S1.x <- Efst x;
     S1.r <- Efst r;
     S1.c1 <- Efst (Efst s1);
     S1.s1 <- Esnd (Efst s1);
     S1.c2 <- Efst (Efst s2);
     S1.s2 <- Esnd (Efst s2);
     S2.x <- Esnd x;
     S2.r <- Esnd r;
     S2.c1 <- Efst (Esnd s1);
     S2.s1 <- Esnd (Esnd s1);
     S2.c2 <- Efst (Esnd s2);
     S2.s2 <- Esnd (Esnd s2);     
     S1.w <c- S1.KE with {S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2};
     w <- Inl S1.w;
     x <- (S1.x | S2.x)
    ] m
    (fun m => if R'_dec (m x) (m w) then true else false)).
   apply equiv_deno with 
    (req_mem_rel {{x, r, s1, s2}} (EP1 (!(Efst (Efst s1) =?= (Efst (Efst s2))))))
    (kreq_mem {{x, w}}).
   sinline_l iEE KE.
   cp_test_l (Efst (Efst s1) =?= Efst (Efst s2)).   
   eapply equiv_strengthen; [ | apply equiv_falseR].
   unfold EP1; simpl; unfold O.eval_op; simpl.
   intros k0 m1 m2 [ [Hreq Hneq] Heq].   
   unfold negb in Hneq; rewrite Heq in Hneq; discriminate.   
   rewrite req_mem_rel_req_mem, proj1_MR.   
   ep iEE; deadcode iEE; eqobs_hd iEE. 
   ep_eq_r x (Efst x | Esnd x).
   simpl; unfold O.eval_op; simpl; intros; case (m2 x); trivial.
   eqobs_in.  
   intros m1 m2 H; unfold charfun, restr, fone.
   rewrite (H _ x), (H _ w); trivial.
   unfold EP1; simpl; unfold O.eval_op; simpl.
   split; [ trivial | ].
   apply <- is_true_negb; intro Hneq.
   elim H_neq1; apply Bitstrings.Veqb_true; trivial.

   transitivity (Pr E
    [ S1.w <c- S1.KE with {S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2} ] m' 
    (fun m => if R'_dec (m S1.x, m S2.x) (inl _ (m S1.w)) then true else false)).

   unfold Pr at 1.
   repeat (
    rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
    simpl E.eval_expr; unfold O.eval_op; simpl T.app_op; mem_upd_simpl).
   rewrite deno_cons_elim, Mlet_simpl.
   apply mu_stable_eq.
   refine (ford_eq_intro _); intro m0.
   rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim, deno_assign_elim.
   unfold charfun, restr, fone, andP, andb.
   simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.

   transitivity (Pr S1.E
    [ S1.w <c- S1.KE with {S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2} ] m' 
    (@O1 k)).
   apply EqObs_deno with {{S2.x, S1.x, S1.r, S1.c1, S1.c2, S1.s1, S1.s2}}
    {{S1.x, S1.w, S2.x}}.
    eqobs_in iEE1.
   intros; unfold charfun, restr, fone, O1, andP, andb.
   rewrite (H _ S1.x), (H _ S1.w), (H _ S2.x); trivial.
   destruct (R'_dec (m2 S1.x, m2 S2.x) (inl _ (m2 S1.w)));
   destruct (S1.R'_dec k (m2 S1.x) (m2 S1.w));
   trivial; firstorder.
   trivial.

   apply S1.KE_correct.
   unfold m'; mem_upd_simpl.
   apply S1_accepting_1.
   apply S1_accepting_2.
        
   (* idem *)
   transitivity (Pr E 
    [ 
     S1.x <- Efst x;
     S1.r <- Efst r;
     S1.c1 <- Efst (Efst s1);
     S1.s1 <- Esnd (Efst s1);
     S1.c2 <- Efst (Efst s2);
     S1.s2 <- Esnd (Efst s2);
     S2.x <- Esnd x;
     S2.r <- Esnd r;
     S2.c1 <- Efst (Esnd s1);
     S2.s1 <- Esnd (Esnd s1);
     S2.c2 <- Efst (Esnd s2);
     S2.s2 <- Esnd (Esnd s2);     
     S2.w <c- S2.KE with {S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2};
     w <- Inr S2.w;
     x <- (S1.x | S2.x)
    ] m
    (fun m => if R'_dec (m x) (m w) then true else false)).
   apply equiv_deno with 
    (req_mem_rel {{x, r, s1, s2}} (EP1 (Efst (Efst s1) =?= (Efst (Efst s2)))))
    (kreq_mem {{x, w}}).
   sinline_l iEE KE.
   cp_test_l (!(Efst (Efst s1) =?= Efst (Efst s2))).
   eapply equiv_strengthen; [ | apply equiv_falseR].
   unfold notR, EP1; simpl; unfold O.eval_op; simpl.
   intros k0 m1 m2 [ [Hreq Heq] Hneq].
   unfold negb in Hneq; rewrite Heq in Hneq; discriminate.   
   rewrite req_mem_rel_req_mem, proj1_MR.   
   ep iEE; deadcode iEE; eqobs_hd iEE. 
   ep_eq_r x (Efst x | Esnd x).
   simpl; unfold O.eval_op; simpl; intros; case (m2 x); trivial.
   eqobs_in.  
   intros m1 m2 H; unfold charfun, restr, fone.
   rewrite (H _ x), (H _ w); trivial.
   unfold EP1; simpl; unfold O.eval_op; simpl.
   split; [ trivial | ].
   simpl in Heq2; rewrite Heq2; apply Bitstrings.Veqb_refl.

   transitivity (Pr E
    [ S2.w <c- S2.KE with {S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2} ] m' 
    (fun m => if R'_dec (m S1.x, m S2.x) (inr _ (m S2.w)) then true else false)).

   unfold Pr at 1.
   repeat (
    rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
    simpl E.eval_expr; unfold O.eval_op; simpl T.app_op; mem_upd_simpl).
   rewrite deno_cons_elim, Mlet_simpl.
   apply mu_stable_eq.
   refine (ford_eq_intro _); intro m0.
   rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim, deno_assign_elim.
   unfold charfun, restr, fone, andP, andb.
   simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.

   transitivity (Pr S2.E
    [ S2.w <c- S2.KE with {S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2} ] m' 
    (@O2 k)).
   apply EqObs_deno with {{S1.x, S2.x, S2.r, S2.c1, S2.c2, S2.s1, S2.s2}}
    {{S2.x, S2.w, S1.x}}.
   eqobs_in iEE2.
   intros; unfold charfun, restr, fone, O2.
   rewrite (H _ S2.x), (H _ S2.w), (H _ S1.x); trivial.
   destruct (R'_dec (m2 S1.x, m2 S2.x) (inr _ (m2 S2.w)));
   destruct (S2.R'_dec k (m2 S2.x) (m2 S2.w)); firstorder.
   trivial.

   apply S2.KE_correct.
   unfold m'; mem_upd_simpl.
   apply S2_accepting_1.
   apply S2_accepting_2.
  Qed.

 End SOUNDNESS.

End OR.
