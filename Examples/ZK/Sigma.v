(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** * Sigma.v : Module type for Sigma protocols *)

Require Import SemTheory.


(** * Variable and procedure names used to specify a Sigma-protocol *)
Module Type SIGMA_NAMES.

 Parameters _x _w _r _state _c _s _b _rstate _rs : positive.
 Parameters _x' _w' _r' _state' _c' _s' _c'' _s'' _c1 _s1 _c2 _s2 : positive.
 Parameters _P1 _P2 _V1 _V2 _S _KE : positive.

End SIGMA_NAMES.


(** * Module type for Sigma protocols *)
Module Type SIGMA (N:SIGMA_NAMES) (Sem:SEM) (SemT:SEM_THEORY Sem).

 Import N Sem SemT.

 Parameters xT wT rT stateT cT sT : T.type.

 (** Knowledge relation *)
 Parameter R  : forall k, T.interp k xT -> T.interp k wT -> Prop. 
 Parameter R' : forall k, T.interp k xT -> T.interp k wT -> Prop. 

 Parameter R_dec : forall k (x:T.interp k xT) (w:T.interp k wT), 
  sumbool (R k x w) (~R k x w).

 Parameter R'_dec : forall k (x:T.interp k xT) (w:T.interp k wT), 
  sumbool (R' k x w) (~R' k x w).

 (** Variables *)
 Notation x      := (Var.Lvar xT _x).
 Notation w      := (Var.Lvar wT _w).
 Notation r      := (Var.Lvar rT _r). 
 Notation state  := (Var.Lvar stateT _state). 
 Notation c      := (Var.Lvar cT _c). 
 Notation s      := (Var.Lvar sT _s).
 Notation rstate := (Var.Lvar (T.Pair rT stateT) _rstate).
 Notation rs     := (Var.Lvar (T.Pair rT sT) _rs).
 Notation b      := (Var.Lvar T.Bool _b).
 Notation x'     := (Var.Lvar xT _x').
 Notation w'     := (Var.Lvar wT _w').
 Notation r'     := (Var.Lvar rT _r'). 
 Notation state' := (Var.Lvar stateT _state'). 
 Notation c'     := (Var.Lvar cT _c'). 
 Notation s'     := (Var.Lvar sT _s').
 Notation c''    := (Var.Lvar cT _c''). 
 Notation s''    := (Var.Lvar sT _s'').
 Notation c1     := (Var.Lvar cT _c1). 
 Notation s1     := (Var.Lvar sT _s1).
 Notation c2     := (Var.Lvar cT _c2). 
 Notation s2     := (Var.Lvar sT _s2).

 (** Procedures *) 
 Notation P1 := (Proc.mkP _P1 (xT :: wT :: nil) (T.Pair rT stateT)).
 Notation P2 := (Proc.mkP _P2 (xT :: wT :: stateT :: cT :: nil) sT).
 Notation V1 := (Proc.mkP _V1 (xT :: rT :: nil) cT).
 Notation V2 := (Proc.mkP _V2 (xT :: rT :: cT :: sT :: nil) T.Bool).
 Notation S  := (Proc.mkP _S (xT :: cT :: nil) (T.Pair rT sT)).
 Notation KE := (Proc.mkP _KE (xT :: rT :: cT :: cT :: sT :: sT :: nil) wT).

 Definition P1_args : var_decl (Proc.targs P1) := 
  dcons _ x' (dcons _ w' (dnil _)). 
 Parameter P1_body : cmd.
 Parameter P1_re   : E.expr (T.Pair rT stateT).

 Definition P2_args : var_decl (Proc.targs P2) := 
  dcons _ x' (dcons _ w' (dcons _ state' (dcons _ c' (dnil _)))).
 Parameter P2_body : cmd.
 Parameter P2_re   : E.expr sT.

 Definition V1_args : var_decl (Proc.targs V1) := 
  dcons _ x' (dcons _ r' (dnil _)).
 Parameter V1_body : cmd.
 Parameter V1_re   : E.expr cT.

 Definition V2_args : var_decl (Proc.targs V2) := 
  dcons _ x' (dcons _ r' (dcons _ c' (dcons _ s' (dnil _)))).
 Parameter V2_body : cmd.
 Parameter V2_re   : E.expr T.Bool.

 Definition S_args : var_decl (Proc.targs S) := 
  dcons _ x' (dcons _ c' (dnil _)).
 Parameter S_body : cmd.
 Parameter S_re   : E.expr (T.Pair rT sT).

 Definition KE_args : var_decl (Proc.targs KE) := 
  dcons _ x' (dcons _ r' (dcons _ c' (dcons _ c'' (dcons _ s' (dcons _ s'' 
   (dnil _)))))). 
 Parameter KE_body : cmd.
 Parameter KE_re   : E.expr wT.
  
 Parameter _E : env.

 Section ENV.

  Let add_P1 E := add_decl E P1 P1_args (refl_equal _) P1_body P1_re.
  Let add_P2 E := add_decl E P2 P2_args (refl_equal _) P2_body P2_re.
  Let add_V1 E := add_decl E V1 V1_args (refl_equal _) V1_body V1_re.
  Let add_V2 E := add_decl E V2 V2_args (refl_equal _) V2_body V2_re.
  Let add_S  E := add_decl E S S_args   (refl_equal _) S_body S_re.
  Let add_KE E := add_decl E KE KE_args (refl_equal _) KE_body KE_re.
  
  Definition E := add_KE (add_S (add_P1 (add_P2 (add_V1 (add_V2 _E))))).

 End ENV.

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

 (** Protocol for a fixed challenge [c] *)
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

 Definition R1 : mem_rel := fun k (m1:Mem.t k) _ => R k (m1 x) (m1 w).
 
 Parameter completeness : forall k (m:Mem.t k),
  R k (m x) (m w) -> Pr E protocol m (EP k b) == 1.

 (** Having [w] on the input relation is not necessary, but simplifies 
    proofs. Having [c] on the output relation is not necessary either, 
    but makes the statement closer to the form it's found in the 
    literature *)
 Parameter SHVZK : equiv 
  (req_mem_rel {{x, w, c}} R1)
  E protocol'
  E simulation
  (kreq_mem {{r, c, s}}).
 
 Parameter KE_correct : forall k (m:Mem.t k),
  m c1 <> m c2 ->
  Pr E [b <c- V2 with {x, r, c1, s1} ] m (EP k b) == 1 ->
  Pr E [b <c- V2 with {x, r, c2, s2} ] m (EP k b) == 1 ->
  Pr E [w <c- KE with {x, r, c1, c2, s1, s2} ] m
   (fun m => if R'_dec k (m x) (m w) then true else false) == 1. 

End SIGMA. 


(** * Alternative module type for Sigma protocols, satisfying just HVZK *)
Module Type SIGMA' (N:SIGMA_NAMES) (Sem:SEM) (SemT:SEM_THEORY Sem).

 Import N Sem SemT.

 Parameters xT wT rT stateT cT sT : T.type.

 (** Knowledge relation *)
 Parameter R  : forall k, T.interp k xT -> T.interp k wT -> Prop. 
 Parameter R' : forall k, T.interp k xT -> T.interp k wT -> Prop. 

 Parameter R_dec : forall k (x:T.interp k xT) (w:T.interp k wT), 
  sumbool (R k x w) (~R k x w).

 Parameter R'_dec : forall k (x:T.interp k xT) (w:T.interp k wT), 
  sumbool (R' k x w) (~R' k x w).
 
 (** Variables *)
 Notation x      := (Var.Lvar xT _x).
 Notation w      := (Var.Lvar wT _w).
 Notation r      := (Var.Lvar rT _r). 
 Notation state  := (Var.Lvar stateT _state). 
 Notation c      := (Var.Lvar cT _c). 
 Notation s      := (Var.Lvar sT _s).
 Notation rstate := (Var.Lvar (T.Pair rT stateT) _rstate).
 Notation rcs    := (Var.Lvar (T.Pair rT (T.Pair cT sT)) _rs).
 Notation b      := (Var.Lvar T.Bool _b).
 Notation x'     := (Var.Lvar xT _x').
 Notation w'     := (Var.Lvar wT _w').
 Notation r'     := (Var.Lvar rT _r'). 
 Notation state' := (Var.Lvar stateT _state'). 
 Notation c'     := (Var.Lvar cT _c'). 
 Notation s'     := (Var.Lvar sT _s').
 Notation c''    := (Var.Lvar cT _c''). 
 Notation s''    := (Var.Lvar sT _s'').
 Notation c1     := (Var.Lvar cT _c1). 
 Notation s1     := (Var.Lvar sT _s1).
 Notation c2     := (Var.Lvar cT _c2). 
 Notation s2     := (Var.Lvar sT _s2).
 
 (** Procedures *)
 Notation P1 := (Proc.mkP _P1 (xT :: wT :: nil) (T.Pair rT stateT)).
 Notation P2 := (Proc.mkP _P2 (xT :: wT :: stateT :: cT :: nil) sT).
 Notation V1 := (Proc.mkP _V1 (xT :: rT :: nil) cT).
 Notation V2 := (Proc.mkP _V2 (xT :: rT :: cT :: sT :: nil) T.Bool).
 Notation S  := (Proc.mkP _S (xT :: nil) (T.Pair rT (T.Pair cT sT))).
 Notation KE := (Proc.mkP _KE (xT :: rT :: cT :: cT :: sT :: sT :: nil) wT).

 Definition P1_args : var_decl (Proc.targs P1) := 
  dcons _ x' (dcons _ w' (dnil _)). 
 Parameter P1_body : cmd.
 Parameter P1_re   : E.expr (T.Pair rT stateT).

 Definition P2_args : var_decl (Proc.targs P2) := 
  dcons _ x' (dcons _ w' (dcons _ state' (dcons _ c' (dnil _)))).
 Parameter P2_body : cmd.
 Parameter P2_re   : E.expr sT.

 Definition V1_args : var_decl (Proc.targs V1) := 
  dcons _ x' (dcons _ r' (dnil _)).
 Parameter V1_body : cmd.
 Parameter V1_re   : E.expr cT.

 Definition V2_args : var_decl (Proc.targs V2) := 
  dcons _ x' (dcons _ r' (dcons _ c' (dcons _ s' (dnil _)))).
 Parameter V2_body : cmd.
 Parameter V2_re   : E.expr T.Bool.

 Definition S_args : var_decl (Proc.targs S) := dcons _ x' (dnil _).
 Parameter S_body : cmd.
 Parameter S_re   : E.expr (T.Pair rT (T.Pair cT sT)).

 Definition KE_args : var_decl (Proc.targs KE) := 
  dcons _ x' (dcons _ r' (dcons _ c' (dcons _ c'' (dcons _ s' (dcons _ s'' 
   (dnil _)))))). 
 Parameter KE_body : cmd.
 Parameter KE_re   : E.expr wT.
  
 Parameter _E : env.

 Section ENV.

  Let add_P1 E := add_decl E P1 P1_args (refl_equal _) P1_body P1_re.
  Let add_P2 E := add_decl E P2 P2_args (refl_equal _) P2_body P2_re.
  Let add_V1 E := add_decl E V1 V1_args (refl_equal _) V1_body V1_re.
  Let add_V2 E := add_decl E V2 V2_args (refl_equal _) V2_body V2_re.
  Let add_S  E := add_decl E S S_args   (refl_equal _) S_body S_re.
  Let add_KE E := add_decl E KE KE_args (refl_equal _) KE_body KE_re.

  Definition E := add_KE (add_S (add_P1 (add_P2 (add_V1 (add_V2 _E))))).

 End ENV.

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

 Definition R1 : mem_rel := fun k (m1:Mem.t k) _ => R k (m1 x) (m1 w).
 
 Parameter completeness : forall k (m:Mem.t k),
  R k (m x) (m w) -> Pr E protocol m (EP k b) == 1.

 (** Having [w] on the input relation is not necessary, but simplifies 
    proofs. Having [c] on the output relation is not necessary either, 
    but makes the statement closer to the form it's found in the 
    literature *)
 Parameter HVZK : equiv 
  (req_mem_rel {{x, w}} R1)
  E protocol
  E simulation
  (kreq_mem {{r, c, s}}).

 Parameter KE_correct : forall k (m:Mem.t k),
  m c1 <> m c2 ->
  Pr E [b <c- V2 with {x, r, c1, s1} ] m (EP k b) == 1 ->
  Pr E [b <c- V2 with {x, r, c2, s2} ] m (EP k b) == 1 ->
  Pr E [w <c- KE with {x, r, c1, c2, s1, s2} ] m
   (fun m => if R'_dec k (m x) (m w) then true else false) == 1. 

End SIGMA'. 



(** Definition of a functor that automatically generates names for the
 variables and procedures of a Sigma protocol *)

Module Type POSITIVE.

 (** Offset *)
 Parameter p : positive.

End POSITIVE.

Module Make_Names (X:POSITIVE) <: SIGMA_NAMES.

 Definition _x      := X.p.
 Definition _w      := Psucc _x.
 Definition _r      := Psucc _w.
 Definition _state  := Psucc _r.
 Definition _c      := Psucc _state.
 Definition _s      := Psucc _c.
 Definition _b      := Psucc _s.
 Definition _rstate := Psucc _b.
 Definition _rs     := Psucc _rstate.
 Definition _x'     := Psucc _rs.
 Definition _w'     := Psucc _x'.
 Definition _r'     := Psucc _w'.
 Definition _state' := Psucc _r'.
 Definition _c'     := Psucc _state'.
 Definition _s'     := Psucc _c'.
 Definition _c''    := Psucc _s'.
 Definition _s''    := Psucc _c''.
 Definition _c1     := Psucc _s''.
 Definition _s1     := Psucc _c1.
 Definition _c2     := Psucc _s1.
 Definition _s2     := Psucc _c2.

 Definition _P1 := X.p.
 Definition _P2 := Psucc _P1.
 Definition _V1 := Psucc _P2.
 Definition _V2 := Psucc _V1.
 Definition _S  := Psucc _V2.
 Definition _KE := Psucc _S.

End Make_Names.


(** Make some modules for variable names *)
Open Scope positive_scope.

Module X.
 Definition p := 1.
End X.

Module X1.
 Definition p := 100.
End X1.

Module X2.
 Definition p := 200.
End X2.

Module N  := Make_Names X.
Module N1 := Make_Names X1.
Module N2 := Make_Names X2.
