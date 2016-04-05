(** * Memory.v : Abstract memory module *)


Set Implicit Arguments.

Require Import Relations.
Require Export Variables.


Module Type MEM (UT:UTYPE) (T:TYPE UT) (Var:VAR UT T).

 Parameter t : nat -> Type.
 
 Parameter get : forall k, t k -> forall v:Var.t, T.interp k (Var.btype v).
 Parameter upd : forall k, t k -> forall v:Var.t, T.interp k (Var.btype v) -> t k.

 Coercion get : t >-> Funclass.

 Notation Local "m '[' x '<--' v ']'" := (upd m x v) (at level 60).

 Parameter get_upd_same : forall k (m:t k) tx (x:Var.var tx) v, 
  m[x <-- v] x = v.

 Parameter get_upd_diff : forall k (m:t k) tx (x:Var.var tx) ty (y:Var.var ty) v,
  Var.mkV x <> y -> m[x <-- v] y = m y.

 Parameter global : forall k, t k -> t k.

 Parameter return_mem : forall k, t k -> t k -> t k.

 Parameter global_spec : forall k (m:t k) tx (x:Var.var tx), 
  Var.is_global x -> m x = global m x.

 Parameter global_local : forall k m tx (x:Var.var tx),
  Var.is_local x -> global m x = T.default k tx.

 Parameter return_mem_local : forall k (m mf:t k) tx (x:Var.var tx),
  Var.is_local x -> return_mem m mf x = m x.

 Parameter return_mem_global : forall k (m mf:t k) tx (x:Var.var tx), 
  Var.is_global x -> return_mem m mf x = mf x.

 Definition eq k (m1 m2:t k) := forall x, m1 x = m2 x.
 
 Parameter eq_leibniz : forall k (m1 m2:t k), eq m1 m2 -> m1 = m2.
 
 Parameter eqb : forall k, t k -> t k -> bool.
 
 Parameter eqb_spec : forall k (m1 m2:t k), if eqb m1 m2 then m1 = m2 else m1 <> m2.
 
End MEM.

Declare Module MakeMem : MEM.
