(** * Utheory.v: Specification of $U$, interval $[0,1]$ *)

Require Export Misc.
Require Export Ccpo.
Set Implicit Arguments.
Open Local Scope O_scope.

(** ** Basic operators of $U$ *)
(** - Constants : $0$ and $1$
    - Constructor : [Unth] $n (\equiv \frac{1}{n+1})$
    - Operations : $x+y~(\equiv min (x+y,1))$, $x*y$, [inv] $x~(\equiv 1 -x)$
    - Relations : $x\leq y$, $x==y$
*)
Module Type Universe.
Parameter U : cpo.
Bind Scope U_scope with U.
Delimit Scope U_scope with U.


Parameter U1 : U. 
Parameters Uplus Umult Udiv: U -> U -> U.
Parameter Uinv : U -> U.
Parameter Unth : nat -> U.
(*
Definition Uplus x y := UPlus x y.
Definition Umult x y := UMult x y.
*)

Infix "+" := Uplus : U_scope.
Infix "*"  := Umult  : U_scope.
Infix "/"  := Udiv  : U_scope.
Notation "[1-]  x" := (Uinv x)  (at level 35, right associativity) : U_scope.
Notation "1" := U1 : U_scope.
Notation "[1/]1+ n" := (Unth n) (at level 35, right associativity) : U_scope.
Open Local Scope U_scope.

(** ** Basic Properties *)

Parameter Udiff_0_1 : ~0 == 1.
Parameter Unit : forall x:U, x <= 1. 

Parameter Uplus_sym : forall x y:U, x + y == y + x.
Parameter Uplus_assoc : forall x y z:U, x + (y + z) == x + y + z.
Parameter Uplus_zero_left : forall x:U, 0 + x == x.

Parameter Umult_sym : forall x y:U, x * y == y * x.
Parameter Umult_assoc : forall x y z:U, x * (y * z) == x * y * z.
Parameter Umult_one_left : forall x:U, 1 * x == x.

Parameter Uinv_one : [1-] 1 == 0. 
Parameter Uinv_opp_left : forall x, [1-] x + x == 1.

Parameter Umult_div : forall x y, ~0 == y -> x <= y -> y * (x/y) == x.
Parameter Udiv_le_one : forall x y,  ~0 == y -> y <= x -> (x/y) == 1.
Parameter Udiv_by_zero : forall x y,  0 == y -> (x/y) == 0.

(** - Property  : $1 - (x+y) + x=1-y$ holds when $x+y$ does not overflow *)
Parameter Uinv_plus_left : forall x y, y <= [1-] x -> [1-] (x + y) + x == [1-] y.

(** - Property  : $(x + y) \times z  = x \times z + y \times z$ 
    holds when $x+y$ does not overflow *)
Parameter Udistr_plus_right : forall x y z, x <= [1-] y -> (x + y) * z == x * z + y * z.

(** - Property  : $1 - (x \times y) = (1 - x)\times y + (1-y)$ *)
Parameter Udistr_inv_right : forall x y:U,  [1-] (x * y) == ([1-] x) * y + [1-] y.

(** - Totality of the order *)
Parameter Ule_class : forall x y : U, class (x <= y).

Parameter Ule_total : forall x y : U, orc (x<=y) (y<=x).
Implicit Arguments Ule_total [].

(** - The relation $x\leq y$ is compatible with operators *)

Parameter Uplus_le_compat_right : forall x y z:U, y <= z -> x + y <= x + z.

Parameter Umult_le_compat_right : forall x y z:U, y <= z -> x * y <= x * z.

Parameter Uinv_le_compat : forall x y:U, x <= y -> [1-] y <= [1-] x.

(** - Properties of simplification in case there is no overflow *)
Parameter Uplus_le_simpl_right : forall x y z, z <= [1-] x -> x + z <= y + z -> x <= y.

Parameter Umult_le_simpl_left : forall x y z: U, ~0 == z -> z * x <= z * y -> x <= y .

(** -  Property [Unth] $\frac{1}{n+1} == 1 - n \times \frac{1}{n+1}$ *)
Parameter Unth_prop : forall n, [1/]1+n == [1-](comp Uplus 0 (fun k => [1/]1+n) n).

(** - Archimedian property *)
Parameter archimedian : forall x, ~0 == x -> exc (fun n => [1/]1+n <= x).

(** - Stability properties of lubs with respect to [+] and [*] *)

Parameter Uplus_right_continuous : forall k, continuous (mk_fmono (Uplus_le_compat_right k)).
Parameter Umult_right_continuous : forall k, continuous (mk_fmono (Umult_le_compat_right k)).

End Universe.
