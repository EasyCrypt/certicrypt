(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * HVZK_of_SHVZK.v : Special Honest-Verifier ZK protocols are
 Honest-Verifier ZK protocols *)

Require Import Sigma.
Require Import SigmaSem.

Set Implicit Arguments.


Module HVZK_of_SHVZK 
 (S : SIGMA N1 Sem BP
  with Definition xT := T.User xT1 
  with Definition wT := T.User wT1
  with Definition rT := T.User rT1
  with Definition stateT := T.User stateT1
  with Definition cT := T.User Bitstring
  with Definition sT := T.User sT1
  with Definition V1_body := [ (Var.Lvar (T.User Bitstring) N1._c') <$- {0,1}^k ]
  with Definition V1_re := E.Evar (Var.Lvar (T.User Bitstring) N1._c')) 
 : SIGMA' N Sem BP.

 (* Redefine notations for readability of proofs *)
 Notation "S:x"      := (Var.Lvar (T.User xT1) 100).
 Notation "S:w"      := (Var.Lvar (T.User wT1) 101).
 Notation "S:r"      := (Var.Lvar (T.User rT1) 102).
 Notation "S:state"  := (Var.Lvar (T.User stateT1) 103).
 Notation "S:c"      := (Var.Lvar (T.User Bitstring) 104).
 Notation "S:s"      := (Var.Lvar (T.User sT1) 105).
 Notation "S:b" := (Var.Lvar T.Bool 106).
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
 Notation _rT     := (T.User rT1).
 Notation _stateT := (T.User stateT1).
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
 Notation rcs    := (Var.Lvar (T.Pair _rT (T.Pair _cT _sT)) 9).
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
 Notation S  := (Proc.mkP 5 (_xT :: nil) (T.Pair _rT (T.Pair cT _sT))).
 Notation KE := (Proc.mkP 6 (_xT :: _rT :: _cT :: _cT :: _sT :: _sT :: nil) _wT).


 Definition P1_args : var_decl (Proc.targs P1) := 
  dcons _ x' (dcons _ w' (dnil _)).

 Definition P1_body : cmd :=
  [ 
   S.x <- x';
   S.w <- w';
   S.rstate <c- S.P1 with {S.x, S.w};
   S.r <- Efst S.rstate;
   S.state <- Esnd S.rstate
  ].

 Definition P1_re   := (S.r | S.state).


 Definition P2_args : var_decl (Proc.targs P2) := 
  dcons _ x' (dcons _ w' (dcons _ state' (dcons _ c' (dnil _)))).
 
 Definition P2_body :=
  [ 
   S.s <c- S.P2 with {x', w', state', c'}
  ].
 
 Definition P2_re : E.expr sT  := S.s.


 Definition V1_args : var_decl (Proc.targs V1) := 
  dcons _ x' (dcons _ r' (dnil _)).
 
 Definition V1_body := [ c' <$- {0,1}^k ].

 Definition V1_re : E.expr cT := c'.


 Definition V2_args : var_decl (Proc.targs V2) := 
  dcons _ x' (dcons _ r' (dcons _ c' (dcons _ s' (dnil _)))).

 Definition V2_body :=
  [ 
   S.b <c- S.V2 with {x', r', c', s'}
  ].
 
 Definition V2_re  : E.expr T.Bool := S.b.


 Definition S_args : var_decl (Proc.targs S) :=
  dcons _ x' (dnil _).

 Definition S_body  :=
  [
   S.c  <$- {0,1}^k;
   S.rs <c- S.S with {x', S.c}
  ].
 
 Definition S_re : E.expr (T.Pair rT (T.Pair cT sT)) := 
  (Efst S.rs | (S.c | Esnd S.rs)).


 Definition KE_args : var_decl (Proc.targs KE) := 
  dcons _ x' (dcons _ r' (dcons _ c' (dcons _ c'' (dcons _ s' (dcons _ s''
   (dnil _)))))). 

 Definition KE_body := [ S.w <c- S.KE with { x', r', c', c'', s', s''} ].
 
 Definition KE_re  : E.expr wT  := S.w.

 Section ENV.
  
  Definition _E : env := S.E.
  
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
  (add_basic_info E E S.P1 S.P1_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E E S.P2 S.P2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E E S.V1 S.V1_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E E S.V2 S.V2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E E S.S  S.S_i  (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E E S.KE S.KE_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (empty_info E E)))))))))))).

 Definition iESE := 
  add_basic_info E S.E S.P1 S.P1_i  (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S.E S.P2 S.P2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S.E S.V1 S.V1_i (refl_equal _) (refl_equal _) (refl_equal _)
  (add_basic_info E S.E S.V2 S.V2_i (refl_equal _) (refl_equal _) (refl_equal _) 
  (add_basic_info E S.E S.S  S.S_i  (refl_equal _) (refl_equal _) (refl_equal _) 
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

 Definition simulation :=
  [
   rcs <c- S with {x};
   r <- Efst rcs;
   c <- Efst (Esnd rcs);
   s <- Esnd (Esnd rcs)
  ].

 Definition R1 : mem_rel := fun k m1 _ => R (m1 x) (m1 w).

 Lemma R1_dec : decMR R1.
 Proof.
  intros ? ? ?; apply R_dec.
 Qed.

 Hint Resolve R1_dec.
 
 Lemma SR1_dec : decMR S.R1.
 Proof.
  intros ? ? ?; apply R_dec.
 Qed.

 Hint Resolve SR1_dec.

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
     S.b <c- S.V2 with {x, r, c, s}
    ] ++ [ b <- S.b ]) m (EP k b)).
  apply EqObs_Pr with (I:={{x, w}}).
  sinline_l iEE V2.
  alloc_l b S.b. 
  eqobs_in iEE.

  rewrite <- Pr_d_eq. 
  transitivity (Pr E ([ S.x <- x; S.w <- w ] ++ S.protocol) m (EP k S.b)).
  apply EqObs_Pr with (I:={{x, w}}).
  inline_l iEE P1.
  inline_l iEE V1.
  inline_l iEE P2.
  inline_l iEE V2.
  inline_r iEE S.V1.
  alloc_l iEE c S.c; alloc_l iEE s S.s; ep iEE; deadcode iEE.
  eqobs_in iEE.

  transitivity (Pr S.E ([ S.x <- x; S.w <- w ] ++ S.protocol) m (EP k S.b)).

  apply EqObs_Pr with (I:={{x, w}}).
  eqobs_in iESE.

  unfold Pr; rewrite deno_app_elim.
  repeat rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
  rewrite deno_nil_elim.
  apply S.completeness.
  simpl; unfold O.eval_op; simpl; mem_upd_simpl.
 Qed.

 Lemma HVZK : equiv 
  (req_mem_rel {{x, w}} R1)
  E protocol
  E simulation
  (kreq_mem {{r, c, s}}).
 Proof.
  apply equiv_trans_trans with E 
   ([S.x <- x ; S.w <- w; S.c <$- {0,1}^k]  ++ S.protocol' ++ [r <- S.r; s <- S.s; c <- S.c ]); auto.
  intros x m1 m2 [H H0]; split; trivial.

  inline iEE P1.
  inline iEE P2.
  inline iEE V1. 
  sinline iEE V2.
  alloc_l iEE c S.c.
  alloc_l iEE s S.s.
  ep iEE; deadcode iEE.
  swap iEE; eqobs_in iEE.

  apply equiv_trans_trans with E 
   ([S.x <- x ; S.w <- w; S.c <$- {0,1}^k]  ++ S.simulation ++ [r <- S.r; s <- S.s; c <- S.c]); auto. 
  intros x m1 m2 [H H0]; split; trivial.

  apply equiv_app with (req_mem_rel {{S.x, S.w, S.c}} S.R1).
  eqobsrel_tail; unfold implMR; simpl. 
  intros k m1 m2 [H H0] v Hin.   
  unfold S.R1; mem_upd_simpl.

  apply equiv_app with (kreq_mem {{S.r, S.c, S.s}}).
  apply equiv_trans_trans with S.E (S.protocol'); auto.
  
  intros x m1 m2 [H H0]; split; trivial.
  eqobs_in iESE.
 
  apply equiv_trans_trans with S.E (S.simulation); auto.

  intros x m1 m2 [H H0]; split; trivial.

  apply S.SHVZK.

  eqobs_in iSEE.
  eqobs_in iEE.
  
  sinline_r iEE S. 
  swap iEE; eqobs_in iEE.
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
   m{!S.x <-- m x!}{!S.r <-- m r!}{!S.c1 <-- m c1!}
    {!S.c2 <-- m c2!}{!S.s1 <-- m s1!}{!S.s2 <-- m s2!}.

  Lemma S_accepting_1 : Pr S.E 
   [ S.b <c- S.V2 with {S.x, S.r, S.c1, S.s1} ] m' (EP k S.b) == 1.
  Proof.
   transitivity
    (Pr E 
     [
      S.x <- x;
      S.r <- r;
      S.c1 <- c1;
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
   unfold m'; intros t x H; Vset_mem_inversion H; subst; mem_upd_simpl.

   split; [trivial | ].
   transitivity (Pr E
    [
     S.x <- x;
     S.r <- r;
     S.c1 <- c1;
     S.s1 <- s1;
     S.b <c- S.V2 with {S.x, S.r, S.c1, S.s1}
    ] m (EP k S.b)).
   rewrite (Pr_d_eq _ _ _ b), <- accepting_1.
   apply Oeq_le; apply EqObs_Pr with {{x, r, c1, s1}}.
   sinline_l iEE V2.
   alloc_l iEE b S.b; eqobs_in iEE.

   apply Oeq_le; apply EqObs_Pr with {{x, r, c1, s1}}.
   deadcode iEE; eqobs_in iEE.
  Qed.

  Lemma S_accepting_2 : Pr S.E 
   [ S.b <c- S.V2 with {S.x, S.r, S.c2, S.s2} ] m' (EP k S.b) == 1.
  Proof.
   transitivity
    (Pr E 
     [
      S.x <- x;
      S.r <- r;
      S.c2 <- c2;
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
   unfold m'; intros t x H; Vset_mem_inversion H; subst; mem_upd_simpl.

   split; [trivial | ].
   transitivity (Pr E
    [
     S.x <- x;
     S.r <- r;
     S.c2 <- c2;
     S.s2 <- s2;
     S.b <c- S.V2 with {S.x, S.r, S.c2, S.s2}
    ] m (EP k S.b)).
   rewrite (Pr_d_eq _ _ _ b), <- accepting_2.
   apply Oeq_le; apply EqObs_Pr with {{x, r, c2, s2}}.
   sinline_l iEE V2.
   alloc_l iEE b S.b; deadcode iEE; eqobs_in iEE.

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
      S.r <- r; 
      S.c1 <- c1;
      S.c2 <- c2;
      S.s1 <- s1;
      S.s2 <- s2;
      S.w <c- S.KE with {S.x, S.r, S.c1, S.c2, S.s1, S.s2};
      w <- S.w
     ])
     m
     (fun m0 => if R'_dec (m0 x) (m0 w) then true else false)).
   apply EqObs_deno with {{x, r, c1, c2, s1, s2}} {{x, w}}.
   sinline_l iEE KE; alloc_l iEE w S.w; eqobs_in iEE.
   intros; unfold charfun, restr; rewrite (H _ x), (H _ w); trivial.
   trivial.
 
   unfold Pr at 1.
   repeat (
    rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim;
    simpl E.eval_expr; unfold O.eval_op; simpl T.app_op; mem_upd_simpl).
   apply equiv_deno with 
    (kreq_mem {{x, S.x, S.r, S.c1, S.c2, S.s1, S.s2}})
    (req_mem_rel {{x}} (fun k m1 m2 => m2 S.x = m1 x /\ m2 S.w = m1 w)).

   eqobs_hd iEE; eqobsrel_tail.
   unfold implMR, andR; intros; simpl; unfold O.eval_op; simpl.
   mem_upd_simpl.
   simpl; rewrite (H _ x), <- (H _ S.w); auto.

   intros m1 m2 [Hreq [Heq1 Heq2] ].
   intros; unfold charfun, restr, fone.
   rewrite Heq1, Heq2, (Hreq _ x); trivial.
   trivial.

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
   repeat split.
   unfold EP1; simpl; unfold O.eval_op; simpl.
   unfold m'; mem_upd_simpl.
   match goal with
   |- is_true (if U_eq_dec ?x ?y then true else false) =>
    destruct (U_eq_dec x y); trivial
   end.
   elim n; trivial.
  Qed.
  
 End SOUNDNESS. 

End HVZK_of_SHVZK.
