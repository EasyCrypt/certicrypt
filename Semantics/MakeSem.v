(** * MakeSem.v : Abstract language semantics, and a functor to derive the 
 language semantics from the semantics of operators, instructions, etc *)


Set Implicit Arguments.

Require Export SemInstr.


Module Type SEM.
  
 Declare Module UT : UTYPE.

 Declare Module T : TYPE UT.

 Declare Module Var : VAR UT T.

 Declare Module Proc : PROC UT T.

 Declare Module Uop : UOP UT T.

 Declare Module O : OP UT T Uop.

 Declare Module US : USUPPORT UT T.

 Declare Module Mem : MEM UT T Var.

 Declare Module E : EXPR UT T Var Uop O US Mem.

 Declare Module I : INSTR UT T Var Proc Uop O US Mem E.

 Declare Module SemI : SEM_INSTR UT T Var Proc Uop O US Mem E I.

 Export SemI.

 (* Notations *)

 (* list of expressions *)
 Notation "{ x , .. , y }" := 
  (@dcons T.type E.expr _ _ x .. 
   (@dcons T.type E.expr _ _ y (@dnil T.type E.expr)) ..). 

 (* boolean expressions *)
 Notation "'!' x"   := (E.Eop O.Onot { x }) (at level 60).
 Notation "x && y"  := (E.Eop O.Oand {x,  y}).
 Notation "x || y"  := (E.Eop O.Oor {x, y}).
 Notation "x ==> y" := (E.Eop O.Oimp {x, y}).
 Notation "b '?' x '?:' y" := (E.Eop (O.Oif _) {b, x, y}) (at level 60).

 (* pair expressions *)
 Notation "'Efst' p" := (E.Eop (O.Ofst _ _) { p }) (at level 0).
 Notation "'Esnd' p" := (E.Eop (O.Osnd _ _) { p }) (at level 0).
 Notation "'(' x '|' y ')'" := (E.Eop (O.Opair _ _) {x,  y} ).

 (* sum expressions *)
 Notation "'Inl' x" := (E.Eop (O.Oinl _ _) { x }) (at level 60).
 Notation "'Inr' x" := (E.Eop (O.Oinr _ _) { x }) (at level 60).
 Notation "'Isl' x" := (E.Eop (O.Oisl _ _) { x }) (at level 60).
 Notation "'Projl' x" := (E.Eop (O.Oprojl _ _) { x }) (at level 60).
 Notation "'Projr' x" := (E.Eop (O.Oprojr _ _) { x }) (at level 60).

 (* option expressions *)
 Notation "'none' t" := (E.Ecte (E.Cnone t)) (at level 0).
 Notation "'some' x" := (E.Eop (O.Osome _) { x }) (at level 60).
 Notation "'IsSome' x" := (E.Eop (O.Oissome _) { x }) (at level 60).
 Notation "'Proj' x" := (E.Eop (O.Oprojo _) { x }) (at level 60).

 (* list expressions *)
 Notation "'Nil' t" := (E.Ecte (E.Cnil t)) (at level 0).
 Notation "x '|::|' y" := 
  (E.Eop (O.Ocons _) {x, y}) (at level 60, right associativity).
 Notation "x |++| l" := 
  (E.Eop (O.Oappend _) {x,l}) (at level 60, right associativity).
 Notation Enth := (E.Eop (O.Onth _)).
 Notation "'Elen' p" := (E.Eop (O.Olength _) {p}) (at level 40).
 Notation "'Zlen' p" := (E.Eop (O.OZlength _) {p}) (at level 40).
 Notation "x 'is_in' y" := (E.Eop (O.Omem _) {x, y}) (at level 60).
 Notation "x 'not_in' y" := (! E.Eop (O.Omem _) {x, y}) (at level 60).

 (* association lists *)
 Notation "x 'in_dom' y" := (E.Eop (O.Oin_dom _ _) {x, y}) (at level 60).
 Notation "x 'in_range' y" := (E.Eop (O.Oin_range _ _) {x, y}) (at level 60).
 Notation "y '[{' x '}]'" := (E.Eop (O.Oimg _ _) {x, y}) (at level 59).
 Notation "l '.[{' x '<<-' v '}]'" := 
   (E.Eop (O.Oupd _ _) {x,v,l}) (at level 50). 


 (* nat expressions *)
 Notation "x '+!' y"  := (E.Eop O.Oadd {x, y}) (at level 50, left associativity).
 Notation "x '*!' y"  := (E.Eop O.Omul {x, y}) (at level 40, left associativity).
 Notation "x '-!' y"  := (E.Eop O.Osub {x, y}) (at level 50, left associativity).
 Notation "x '<=!' y" := (E.Eop O.Ole {x, y}) (at level 50).
 Notation "x '<!' y"  := (E.Eop O.Olt {x, y}) (at level 50).

 (* Z expressions *)
 Notation "x '+Z' y"   := (E.Eop O.OZadd {x, y}) (at level 50, left associativity).
 Notation "x '*Z' y"   := (E.Eop O.OZmul {x, y}) (at level 40, left associativity).
 Notation "x '-Z' y"   := (E.Eop O.OZsub {x, y}) (at level 50, left associativity).
 Notation "x '<=Z' y"  := (E.Eop O.OZle {x, y}) (at level 50).
 Notation "x '<Z' y"   := (E.Eop O.OZlt {x, y}) (at level 50).
 Notation "x '>=Z' y"  := (E.Eop O.OZge {x, y}) (at level 50).
 Notation "x '>Z' y"   := (E.Eop O.OZgt {x, y}) (at level 50).
 Notation "'oppZ' x"   := (E.Eop O.OZopp {x}) (at level 40).
 Notation "x '/Z' y"   := (E.Eop O.OZdiv {x, y}) (at level 50).
 Notation "x 'modZ' y" := (E.Eop O.OZmod {x, y}) (at level 50).
 Notation "x 'powZ' y" := (E.Eop O.OZpow {x, y}) (at level 50).

 (* equality *)
 Notation "x '=?=' y" := (E.Eop (O.Oeq_ _) {x, y}) (at level 70, no associativity).

 (* support *)
 Notation "'{0,1}'" := E.Dbool.
 Notation "'[0..' e ']'" := (E.Dnat e)%nat.
 Notation "'[' e1 ',,' e2 ']'" := (E.DZ e1 e2)%nat.
 
End SEM.


Module Make (UT_:UTYPE) (T_:TYPE UT_) (Uop_:UOP UT_ T_) (US_:USUPPORT UT_ T_) <: SEM.

 Module UT := UT_.

 Module T := T_.

 Module Var := MakeVar UT_ T_.

 Module Proc := MakeProc UT_ T_.

 Module Uop := Uop_.

 Module O := MakeOp UT_ T_ Uop.

 Module US := US_.

 Module Mem:= MakeMem UT_ T_ Var.

 Module E := MakeExpr UT_ T_ Var Uop O US Mem.

 Module I := MakeInstr UT_ T_ Var Proc Uop O US Mem E.

 Module SemI := SemInstr.Make UT T_ Var Proc Uop O US Mem E I.

 Export SemI.

 (* list of expressions *)
 Notation "{ x , .. , y }" := 
  (@dcons T.type E.expr _ _ x .. 
   (@dcons T.type E.expr _ _ y (@dnil T.type E.expr)) ..). 

 (* boolean expressions *)
 Notation "'!' x"   := (E.Eop O.Onot { x }) (at level 60).
 Notation "x && y"  := (E.Eop O.Oand {x,  y}).
 Notation "x || y"  := (E.Eop O.Oor {x, y}).
 Notation "x ==> y" := (E.Eop O.Oimp {x, y}).
 Notation "b '?' x '?:' y" := (E.Eop (O.Oif _) {b, x, y}) (at level 60).

 (* pair expressions *)
 Notation "'Efst' p" := (E.Eop (O.Ofst _ _) { p }) (at level 0).
 Notation "'Esnd' p" := (E.Eop (O.Osnd _ _) { p }) (at level 0).
 Notation "'(' x '|' y ')'" := (E.Eop (O.Opair _ _) {x,  y} ).

 (* sum expressions *)
 Notation "'Inl' x" := (E.Eop (O.Oinl _ _) { x }) (at level 60).
 Notation "'Inr' x" := (E.Eop (O.Oinr _ _) { x }) (at level 60).
 Notation "'Isl' x" := (E.Eop (O.Oisl _ _) { x }) (at level 60).
 Notation "'Projl' x" := (E.Eop (O.Oprojl _ _) { x }) (at level 60).
 Notation "'Projr' x" := (E.Eop (O.Oprojr _ _) { x }) (at level 60).

 (* option expressions *)
 Notation "'none' t" := (E.Ecte (E.Cnone t)) (at level 0).
 Notation "'some' x" := (E.Eop (O.Osome _) { x }) (at level 60).
 Notation "'IsSome' x" := (E.Eop (O.Oissome _) { x }) (at level 60).
 Notation "'Proj' x" := (E.Eop (O.Oprojo _) { x }) (at level 60).

 (* list expressions *)
 Notation "'Nil' t" := (E.Ecte (E.Cnil t)) (at level 0).
 Notation "x '|::|' y" := 
  (E.Eop (O.Ocons _) {x, y}) (at level 60, right associativity).
 Notation "x |++| l" := 
  (E.Eop (O.Oappend _) {x,l}) (at level 60, right associativity).
 Notation Enth := (E.Eop (O.Onth _)).
 Notation "'Elen' p" := (E.Eop (O.Olength _) {p}) (at level 40).
 Notation "'Zlen' p" := (E.Eop (O.OZlength _) {p}) (at level 40).
 Notation "x 'is_in' y" := (E.Eop (O.Omem _) {x, y}) (at level 60).
 Notation "x 'not_in' y" := (! E.Eop (O.Omem _) {x, y}) (at level 60).

 (* association lists *)
 Notation "x 'in_dom' y" := (E.Eop (O.Oin_dom _ _) {x, y}) (at level 60).
 Notation "x 'in_range' y" := (E.Eop (O.Oin_range _ _) {x, y}) (at level 60).
 Notation "y '[{' x '}]'" := (E.Eop (O.Oimg _ _) {x, y}) (at level 59).
 Notation "l '.[{' x '<<-' v '}]'" := 
   (E.Eop (O.Oupd _ _) {x,v,l}) (at level 50).

 (* nat expressions *)
 Notation "x '+!' y"  := (E.Eop O.Oadd {x, y}) (at level 50, left associativity).
 Notation "x '*!' y"  := (E.Eop O.Omul {x, y}) (at level 40, left associativity).
 Notation "x '-!' y"  := (E.Eop O.Osub {x, y}) (at level 50, left associativity).
 Notation "x '<=!' y" := (E.Eop O.Ole {x, y}) (at level 50).
 Notation "x '<!' y"  := (E.Eop O.Olt {x, y}) (at level 50).

 (* Z expressions *)
 Notation "x '+Z' y"   := (E.Eop O.OZadd {x, y}) (at level 50, left associativity).
 Notation "x '*Z' y"   := (E.Eop O.OZmul {x, y}) (at level 40, left associativity).
 Notation "x '-Z' y"   := (E.Eop O.OZsub {x, y}) (at level 50, left associativity).
 Notation "x '<=Z' y"  := (E.Eop O.OZle {x, y}) (at level 50).
 Notation "x '<Z' y"   := (E.Eop O.OZlt {x, y}) (at level 50).
 Notation "x '>=Z' y"  := (E.Eop O.OZge {x, y}) (at level 50).
 Notation "x '>Z' y"   := (E.Eop O.OZgt {x, y}) (at level 50).
 Notation "'oppZ' x"   := (E.Eop O.OZopp {x}) (at level 40).
 Notation "x '/Z' y"   := (E.Eop O.OZdiv {x, y}) (at level 50).
 Notation "x 'modZ' y" := (E.Eop O.OZmod {x, y}) (at level 50).
 Notation "x 'powZ' y" := (E.Eop O.OZpow {x, y}) (at level 50).

 (* equality *)
 Notation "x '=?=' y" := (E.Eop (O.Oeq_ _) {x, y}) (at level 70, no associativity).

 (* support *)
 Notation "'{0,1}'" := E.Dbool.
 Notation "'[0..' e ']'" := (E.Dnat e)%nat.
 Notation "'[' e1 ',,' e2 ']'" := (E.DZ e1 e2)%nat.

End Make.
