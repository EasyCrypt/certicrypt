(** * Uprop.v : Properties of operators on [[0,1]] *)
Set Implicit Arguments.
Require Export Utheory.
Require Export Arith.
Require Export Omega.

Module Univ_prop (Univ:Universe).
Import Univ.

Hint Resolve Unit Udiff_0_1 Unth_prop.
Hint Resolve Uplus_sym Uplus_assoc Umult_sym Umult_assoc.
Hint Resolve Uinv_one  Uinv_opp_left  Uinv_plus_left Umult_div Udiv_le_one Udiv_by_zero.
Hint Resolve Uplus_zero_left Umult_one_left Udistr_plus_right Udistr_inv_right.
Hint Resolve Uplus_le_compat_right Umult_le_compat_right Uinv_le_compat.
Hint Resolve lub_le le_lub Uplus_right_continuous Umult_right_continuous.
(* lub_eq_mult lub_eq_plus_cte_left.*)
Hint Resolve Ule_total Ule_class.

Open Local Scope U_scope.

(** ** Direct consequences of axioms  *)

Lemma Ueq_class : forall x y:U, class (x==y).
red; intros.
apply Ole_antisym;
apply Ule_class; intuition.
Save.

Lemma Ueq_double_neg : forall x y : U, ~ ~x == y -> x == y.
exact Ueq_class.
Save.
Hint Resolve Ueq_class.
Hint Immediate Ueq_double_neg.

Lemma Ule_orc : forall x y : U, orc (x<=y) ( ~ x<=y).
auto.
Save.
Implicit Arguments Ule_orc [].

Lemma Ueq_orc : forall x y:U, orc (x==y) ( ~ x==y).
auto.
Save.
Implicit Arguments Ueq_orc [].

Lemma Upos : forall x:U, 0 <= x.
auto.
Save.

Lemma Ule_0_1 : 0 <= 1.
auto.
Save.

Hint Resolve Upos Ule_0_1.

(** - Inverse order on U *)

Definition UI : ord := Iord U.


(** ** Properties of == derived from properties of $\le$ *)

Lemma Uplus_le_compat_left : forall x y z:U, x <= y -> x + z <= y + z.
intros; rewrite (Uplus_sym x z); rewrite (Uplus_sym y z); auto.
Save.
Hint Resolve Uplus_le_compat_left.

Lemma Uplus_eq_compat_left : forall x y z:U, x == y -> x + z == y + z.
intros; apply Ole_antisym; auto.
Save.

Hint Resolve Uplus_eq_compat_left.

Lemma Uplus_eq_compat_right : forall x y z:U, x == y -> (z + x) == (z + y).
intros; apply Oeq_trans with (x + z); auto.
apply Oeq_trans with (y + z); auto.
Save.

Add Morphism Uplus with signature
  (Ole (o:=U)) ++>  (Ole (o:=U))  ++> (Ole (o:=U))
as Uplus_le_compat_morph.
intros; apply Ole_trans with (x+y0); auto.
Save.

Lemma Uplus_le_compat : forall x y z t, x <= y -> z <= t -> x +z <= y + t.
intros; apply Ole_trans with (x+t); auto.
Save.
Hint Immediate Uplus_le_compat.

Definition UPlus := le_compat2_mon Uplus_le_compat.

Definition UPlus_simpl : forall x y, UPlus x y = x+y.
trivial.
Save.

Lemma Uplus_continuous2 : continuous2 UPlus.
apply continuous2_sym.
simpl; auto.
intro k; apply continuous_eq_compat with (2:=Uplus_right_continuous k).
apply fmon_eq_intro; intro m; auto.
Save.

Hint Resolve Uplus_continuous2.

Lemma Umult_le_compat_left : forall x y z:U, x <= y -> x * z <= y * z.
intros; rewrite (Umult_sym x z); rewrite (Umult_sym y z); auto.
Save.
Hint Resolve Umult_le_compat_left.

Add Morphism Umult
with signature (Ole (o:=U)) ++> (Ole (o:=U)) ++> (Ole (o:=U)) as Umult_le_compat_morph.
intros x1 x2 H1 x3 x4 H2; apply Ole_trans with (x1 * x4); auto.
Save.
Hint Immediate Umult_le_compat_morph.

Lemma Umult_le_compat : forall x y z t, x <= y -> z <= t -> x * z <= y * t.
intros; apply Ole_trans with (x*t); auto.
Save.
Hint Immediate Umult_le_compat.

Definition UMult := le_compat2_mon Umult_le_compat.

Lemma Umult_eq_compat_left : forall x y z:U, x == y -> (x * z) == (y * z).
intros;  apply Ole_antisym; auto.
Save.
Hint Resolve Umult_eq_compat_left.

Lemma Umult_eq_compat_right :  forall x y z:U, x == y -> (z * x) == (z * y).
intros; apply Oeq_trans with (x * z); auto.
apply Oeq_trans with (y * z); auto.
Save.

Hint Resolve Uplus_eq_compat_right Umult_eq_compat_right.

Definition UMult_simpl : forall x y, UMult x y = x*y.
trivial.
Save.

Lemma Umult_continuous2 : continuous2 UMult.
apply continuous2_sym.
simpl; auto.
intro k; apply continuous_eq_compat with (2:=Umult_right_continuous k).
apply fmon_eq_intro; intro m; auto.
Save.
Hint Resolve Umult_continuous2.

(** ** [U] is a setoid *)

Add Morphism Uplus with signature Oeq (O:=U) ==> Oeq (O:=U) ==> Oeq (O:=U)
as Uplus_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; apply Oeq_trans with (x1+x4); auto.
Qed.

Add Morphism Umult with signature Oeq (O:=U) ==> Oeq  (O:=U) ==> Oeq  (O:=U)
as Umult_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; apply Oeq_trans with (x1 * x4); auto.
Qed.

Hint Immediate Umult_eq_compat Uplus_eq_compat.

Add Morphism Uinv with signature Oeq (O:=U) ==> Oeq (O:=U) as Uinv_eq_compat.
intros; apply Ole_antisym; auto.
Qed.

Definition UInv : UI -m> U.
exists (fun (x:UI) => [1-]x); red; intros; auto.
Defined.

Definition UInv_simpl : forall x, UInv x = [1-]x.
trivial.
Save.


Lemma Ule_eq_compat :
forall x1 x2 : U, x1 == x2 -> forall x3 x4 : U, x3 == x4 -> x1 <= x3 -> x2 <= x4.
intros x1 x2 eq1 x3 x4 eq2; elim (Ole_eq_compat_iff eq1 eq2); auto.
Save.



(** ** Definition and properties of $x<y$ *)
Definition Ult (r1 r2:U) : Prop := ~ (r2 <= r1).

Infix "<" := Ult : U_scope.

Hint Unfold Ult.

Add Morphism Ult with signature Oeq (O:=U) ==> Oeq (O:=U) ==> iff as Ult_eq_compat_iff.
unfold Ult, not; intros x1 x2 eq1 x3 x4 eq2.
generalize (Ole_eq_compat_iff eq2 eq1); intuition.
Save.

Lemma Ult_eq_compat :
forall x1 x2 : U, x1 == x2 -> forall x3 x4 : U, x3 == x4 -> x1 < x3 -> x2 < x4.
intros x1 x2 eq1 x3 x4 eq2; elim (Ult_eq_compat_iff eq1 eq2); auto.
Save.

Lemma Ult_class : forall x y, class (x<y).
unfold Ult; auto.
Save.
Hint Resolve Ult_class.

(* begin hide *)
(** Tactic for left normal form with respect to associativity *)
Ltac norm_assoc_left :=
     match goal with
      | |- context [(Uplus ?X1 (Uplus ?X2 ?X3))]
        => (setoid_rewrite (Uplus_assoc X1 X2 X3))
     end.

Ltac norm_assoc_right :=
     match goal with
      | |- context [(Uplus (Uplus ?X1 ?X2) ?X3)]
        => (setoid_rewrite <- (Uplus_assoc X1 X2 X3))
     end.
(* end hide *)

(** *** Properties of $x \leq y$ *)

Lemma Ule_zero_eq :  forall x:U, x <= 0 -> x == 0.
intros; apply Ole_antisym; auto.
Save.

Lemma Uge_one_eq : forall x:U, 1 <= x -> x == 1.
intros; apply Ole_antisym; auto.
Save.

Hint Immediate Ule_zero_eq Uge_one_eq.

(** *** Properties of $x < y$ *)

Lemma Ult_neq : forall x y:U, x < y -> ~x == y.
unfold Ult; red; auto.
Save.

Lemma Ult_neq_rev : forall x y:U, x < y -> ~y == x.
unfold Ult; red; auto.
Save.

Lemma Ult_trans : forall x y z, x<y -> y<z -> x <z.
repeat red; intros.
apply (Ule_total y z); intros; auto.
apply H; apply Ole_trans with z; auto.
Save.

Lemma Ult_le : forall x y:U, x < y -> x <= y.
unfold Ult; intros; apply Ule_class; repeat red; intros.
assert (x < x).
apply Ult_trans with y; auto.
apply H1; auto.
Save.

Lemma Ule_diff_lt : forall x y : U,  x <= y -> ~x==y -> x < y.
red; intuition.
Save.

Hint Immediate Ult_neq Ult_neq_rev Ult_le.
Hint Resolve Ule_diff_lt.

Lemma Ult_neq_zero : forall x, ~0 == x -> 0 < x.
auto.
Save.

Hint Resolve Ule_total Ult_neq_zero.

(** ** Properties of $+$ and $\times$  *)

Lemma Udistr_plus_left :  forall x y z, y <= [1-] z -> x * (y + z) == x * y + x * z.
intros.
rewrite (Umult_sym x (y+z)).
rewrite (Umult_sym x y).
rewrite (Umult_sym x z);auto.
Save.


Lemma Udistr_inv_left :  forall x y, [1-](x * y) == (x * ([1-] y)) + [1-] x.
intros.
setoid_rewrite (Umult_sym x y).
setoid_rewrite (Udistr_inv_right y x); auto.
Save.

Hint Resolve Uinv_eq_compat Udistr_plus_left Udistr_inv_left.

Lemma Uplus_perm2 : forall x y z:U, x + (y + z) == y + (x + z).
intros; setoid_rewrite (Uplus_assoc x y z).
setoid_rewrite (Uplus_sym x y); auto.
Save.

Lemma Umult_perm2 : forall x y z:U, x * (y * z) == y * (x * z).
intros; setoid_rewrite (Umult_assoc x y z).
setoid_rewrite (Umult_sym x y); auto.
Save.

Lemma Uplus_perm3 : forall x y z : U, (x + (y + z)) == z + (x + y).
intros; setoid_rewrite (Uplus_assoc x y z); auto.
Save.

Lemma Umult_perm3 : forall x y z : U, (x * (y * z)) == z * (x * y).
intros; setoid_rewrite (Umult_assoc x y z); auto.
Save.

Hint Resolve Uplus_perm2 Umult_perm2 Uplus_perm3 Umult_perm3.

Lemma Uplus_zero_right : forall x:U, x + 0 == x.
intros; setoid_rewrite (Uplus_sym x 0); auto.
Save.
Hint Resolve Uplus_zero_right.

(* ** Properties of [1-] *)

Lemma Uinv_zero : [1-] 0 == 1.
apply Oeq_trans with (([1-] (0 + 0))+0); auto.
apply Oeq_trans with ([1-] (0 + 0)); auto.
setoid_rewrite (Uplus_zero_right 0); auto.
Save.
Hint Resolve Uinv_zero.


Lemma Uinv_opp_right : forall x, x + [1-] x == 1.
intros; apply Oeq_trans with ([1-] x + x); auto.
Save.
Hint Resolve Uinv_opp_right.

Lemma Uinv_inv : forall x : U, [1-] [1-] x == x.
intros; apply Oeq_trans with ([1-] (x + [1-] x) + x); auto.
apply Oeq_sym; auto.
setoid_rewrite (Uinv_opp_right x); setoid_rewrite Uinv_one; auto.
Save.
Hint Resolve Uinv_inv.


Lemma Uinv_simpl :  forall x y : U, [1-] x == [1-] y -> x == y.
intros; setoid_rewrite <- (Uinv_inv x);
 setoid_rewrite <- (Uinv_inv y); auto.
Save.

Hint Immediate Uinv_simpl.

Lemma Umult_decomp : forall x y, x == x * y + x * [1-]y.
intros; apply Oeq_trans with (x * (y + [1-]y)); auto.
apply Oeq_trans with (x * 1); auto.
rewrite Umult_sym; auto.
Save.
Hint Resolve Umult_decomp.

(** ** More properties on [+] and [*]  and [Uinv] *)
(*
Lemma Umult_le_compat_right :  forall x y z: U,  x <= y -> (z * x) <= (z * y).
intros; setoid_rewrite (Umult_sym z x); setoid_rewrite (Umult_sym z y).
apply Umult_le_compat_left; trivial.
Save.

Hint Resolve Umult_le_compat_right.
*)


Lemma Umult_one_right : forall x:U, x * 1 == x.
intros; setoid_rewrite (Umult_sym x 1); auto.
Save.
Hint Resolve Umult_one_right.

Lemma Umult_one_right_eq : forall x y:U, y == 1 -> x * y == x.
intros; rewrite H; auto.
Save.
Hint Resolve Umult_one_right_eq.

Lemma Umult_one_left_eq : forall x y:U, x == 1 -> x * y == y.
intros; rewrite H; auto.
Save.
Hint Resolve Umult_one_left_eq.

Lemma Udistr_plus_left_le :  forall x y z : U, x * (y + z) <= x * y + x * z.
intros; apply (Ule_total y ([1-]z)); intros; auto.
apply Ole_trans with (x *  ([1-]z+z)).
rewrite Uinv_opp_left; auto.
rewrite Udistr_plus_left; auto.
Save.

Lemma Uplus_eq_simpl_right :
forall x y z:U, z <= [1-] x -> z <= [1-] y -> (x + z) == (y + z) -> x == y.
intros; apply Ole_antisym.
apply Uplus_le_simpl_right with z; auto.
apply Uplus_le_simpl_right with z; auto.
Save.

Lemma Ule_plus_right : forall x y, x <= x + y.
intros; apply Ule_eq_compat with (x + 0) (x + y); auto.
Save.

Lemma Ule_plus_left : forall x y, y <= x + y.
intros; apply Ule_eq_compat with (0 + y) (x + y); auto.
Save.
Hint Resolve Ule_plus_right Ule_plus_left.

Lemma Ule_mult_right : forall x y, x * y <= x .
intros; apply Ule_eq_compat with (x * y) (x * 1); auto.
Save.

Lemma Ule_mult_left : forall x y, x * y <= y.
intros; apply Ule_eq_compat with (x * y) (1 * y); auto.
Save.
Hint Resolve Ule_mult_right Ule_mult_left.

Lemma Uinv_le_perm_right : forall x y:U, x <= [1-] y -> y <= [1-] x.
intros; apply Ole_trans with ([1-] ([1-] y)); auto.
Save.
Hint Immediate Uinv_le_perm_right.

Lemma Uinv_le_perm_left :  forall x y:U, [1-] x <= y -> [1-] y <= x.
intros; apply Ole_trans with ([1-] ([1-] x)); auto.
Save.
Hint Immediate Uinv_le_perm_left.

Lemma Uinv_le_simpl :  forall x y:U, [1-] x <= [1-] y -> y <= x.
intros; apply Ole_trans with ([1-] ([1-] x)); auto.
Save.
Hint Immediate Uinv_le_simpl.

Lemma Uinv_double_le_simpl_right : forall x y, x<=y -> x <= [1-][1-]y.
intros; apply Uinv_le_perm_right; auto.
Save.
Hint Resolve Uinv_double_le_simpl_right.

Lemma Uinv_double_le_simpl_left : forall x y, x<=y -> [1-][1-]x <= y.
intros; apply Uinv_le_perm_left; auto.
Save.
Hint Resolve Uinv_double_le_simpl_left.

Lemma Uinv_eq_perm_left :  forall x y:U, x == [1-] y -> [1-] x == y.
intros; apply Oeq_trans with ([1-] ([1-] y)); auto.
Save.
Hint Immediate Uinv_eq_perm_left.

Lemma Uinv_eq_perm_right :  forall x y:U, [1-] x == y ->  x == [1-] y.
intros; apply Oeq_trans with ([1-] ([1-] x)); auto.
Save.

Hint Immediate Uinv_eq_perm_right.

Lemma Uinv_eq_simpl :  forall x y:U, [1-] x == [1-] y -> x == y.
intros; apply Oeq_trans with ([1-] ([1-] x)); auto.
Save.
Hint Immediate Uinv_eq_simpl.

Lemma Uinv_double_eq_simpl_right : forall x y, x==y -> x == [1-][1-]y.
intros; apply Uinv_eq_perm_right; auto.
Save.
Hint Resolve Uinv_double_eq_simpl_right.

Lemma Uinv_double_eq_simpl_left : forall x y, x==y -> [1-][1-]x == y.
intros; apply Uinv_eq_perm_left; auto.
Save.
Hint Resolve Uinv_double_eq_simpl_left.

Lemma Uinv_plus_right : forall x y, y <= [1-] x -> [1-] (x + y) + y == [1-] x.
intros; setoid_rewrite (Uplus_sym x y); auto.
Save.
Hint Resolve Uinv_plus_right.

Lemma Uplus_eq_simpl_left :
forall x y z:U, x <= [1-] y -> x <= [1-] z -> (x + y) == (x + z) -> y == z.
intros x y z H1 H2; setoid_rewrite (Uplus_sym x y); setoid_rewrite (Uplus_sym x z); auto.
intros; apply Uplus_eq_simpl_right with x; auto.
Save.

Lemma Uplus_eq_zero_left : forall x y:U, x <= [1-] y -> (x + y) == y -> x == 0.
intros; apply Uplus_eq_simpl_right with y; auto.
setoid_rewrite H0; auto.
Save.

Lemma Uinv_le_trans : forall x y z t, x <= [1-] y -> z<=x -> t<=y -> z<= [1-] t.
intros; apply Ole_trans with x; auto.
apply Ole_trans with ([1-] y); auto.
Save.


Lemma Uinv_plus_left_le : forall x y, [1-]y <= [1-](x+y) +x.
intros; apply (Ule_total y ([1-]x)); auto; intros.
rewrite Uinv_plus_left; auto.
apply Ole_trans with x; auto.
Save.

Lemma Uinv_plus_right_le : forall x y, [1-]x <= [1-](x+y) +y.
intros; apply (Ule_total y ([1-]x)); auto; intros.
rewrite Uinv_plus_right; auto.
apply Ole_trans with y; auto.
Save.

Hint Resolve Uinv_plus_left_le Uinv_plus_right_le.

(** ** Disequality *)

Lemma neq_sym : forall x y:U, ~x==y -> ~y==x.
red; intros; apply H; auto.
Save.
Hint Immediate neq_sym.

Lemma Uinv_neq_compat : forall x y, ~x == y -> ~ [1-] x == [1-] y.
red; intros; apply H; auto.
Save.

Lemma Uinv_neq_simpl : forall x y, ~ [1-] x == [1-] y-> ~x == y.
red; intros; apply H; auto.
Save.

Hint Resolve Uinv_neq_compat.
Hint Immediate Uinv_neq_simpl.

Lemma Uinv_neq_left : forall x y, ~x == [1-] y -> ~ [1-] x == y.
red; intros; apply H; auto.
Save.

Lemma Uinv_neq_right : forall x y, ~ [1-] x == y -> ~x == [1-] y.
red; intros; apply H; auto.
Save.

(** *** Properties of [<]  *)

Lemma Ult_antirefl : forall x:U, ~x < x.
unfold Ult; intuition.
Save.

Lemma Ult_0_1 : (0 < 1).
red; intuition.
Save.

Lemma Ule_lt_trans : forall x y z:U, x <= y -> y < z -> x < z.
unfold Ult; intuition.
apply H0; apply Ole_trans with x; trivial.
Save.

Lemma Ult_le_trans : forall x y z:U, x < y -> y <= z -> x < z.
unfold Ult; intuition.
apply H; apply Ole_trans with z; trivial.
Save.

Hint Resolve Ult_0_1 Ult_antirefl.

Lemma Ule_neq_zero : forall (x y:U), ~0 == x -> x <= y -> ~ 0 == y.
red; intros.
apply H.
apply Ole_antisym; auto; rewrite H1; trivial.
Save.

Lemma Uplus_neq_zero_left : forall x y, ~0 == x -> ~0 == x+y.
intros; apply Ult_neq.
apply Ult_le_trans with x; auto.
Save.

Lemma Uplus_neq_zero_right : forall x y, ~0 == y -> ~0 == x+y.
intros; apply Ult_neq.
apply Ult_le_trans with y; auto.
Save.

Lemma not_Ult_le : forall x y, ~x < y -> y <= x.
intros; apply Ule_class; auto.
Save.

Lemma Ule_not_lt : forall x y, x <= y -> ~y < x.
repeat red; intros.
apply H0; auto.
Save.

Hint Immediate not_Ult_le Ule_not_lt.

Theorem Uplus_le_simpl_left : forall x y z : U, z <= [1-] x -> z + x <= z + y -> x <= y.
intros.
apply Uplus_le_simpl_right with z; auto.
apply Ole_trans with (z + x); auto.
apply Ole_trans with (z + y); auto.
Save.


Lemma Uplus_lt_compat_left : forall x y z:U, z <= [1-] y -> x < y -> (x + z) < (y + z).
unfold Ult; intuition.
apply H0; apply Uplus_le_simpl_right with z; trivial.
Save.


Lemma Uplus_lt_compat_right : forall x y z:U, z <= [1-] y -> x < y -> (z + x) < (z + y).
intros; setoid_rewrite (Uplus_sym z x).
intros; setoid_rewrite (Uplus_sym z y).
apply Uplus_lt_compat_left; auto.
Save.

Hint Resolve Uplus_lt_compat_right Uplus_lt_compat_left.

Lemma Uplus_lt_compat :
forall x y z t:U, z <= [1-] x -> t <= [1-] y -> x < y -> z < t -> (x + z) < (y + t).
intros; apply Ult_trans with (y + z); auto.
apply Uplus_lt_compat_left; auto.
apply Ole_trans with t; auto.
Save.

Hint Immediate Uplus_lt_compat.

Lemma Uplus_lt_simpl_left : forall x y z:U, z <= [1-] y -> (z + x) < (z + y) -> x < y.
unfold lt; repeat red; intros.
apply H0; auto.
Save.

Lemma Uplus_lt_simpl_right : forall x y z:U, z <= [1-] y -> (x + z) < (y + z) -> x < y.
unfold lt; repeat red; intros.
apply H0; auto.
Save.

Lemma Uplus_one_le : forall x y, x + y == 1 -> [1-] y <= x.
intros; apply Ule_class; red; intros.
assert (x < [1-] y); auto.
assert (x + y < [1-] y + y); auto.
assert (x + y < 1); auto.
setoid_rewrite <- (Uinv_opp_left y); auto.
Save.
Hint Immediate Uplus_one_le.

Theorem Uplus_eq_zero : forall x, x <= [1-] x -> (x + x) == x -> x == 0.
intros x H1 H2; apply Uplus_eq_simpl_left with x; auto.
setoid_rewrite H2; auto.
Save.

Lemma Umult_zero_left : forall x, 0 * x == 0.
intros; apply Uinv_simpl.
setoid_rewrite (Udistr_inv_right 0 x); auto.
setoid_rewrite Uinv_zero.
setoid_rewrite (Umult_one_left x); auto.
Save.
Hint Resolve Umult_zero_left.

Lemma Umult_zero_right : forall x, (x * 0) == 0.
intros; setoid_rewrite (Umult_sym x 0); auto.
Save.
Hint Resolve Uplus_eq_zero Umult_zero_right.

Lemma Umult_zero_left_eq : forall x y, x == 0 -> x * y == 0.
intros; rewrite H; auto.
Save.

Lemma Umult_zero_right_eq : forall x y, y == 0 -> x * y == 0.
intros; rewrite H; auto.
Save.

Lemma Umult_zero_eq : forall x y z, x == 0 -> x * y == x * z.
intros; rewrite H.
rewrite Umult_zero_left; auto.
Save.

(** *** Compatibility of operations with respect to order. *)

Lemma Umult_le_simpl_right : forall x y z, ~0 == z -> (x * z) <= (y * z) -> x <= y.
intros; apply Umult_le_simpl_left with z; auto.
setoid_rewrite (Umult_sym z x);
setoid_rewrite (Umult_sym z y);trivial.
Save.
Hint Resolve Umult_le_simpl_right.

Lemma Umult_simpl_right : forall x y z, ~0 == z -> (x * z) == (y * z) -> x == y.
intros; apply Ole_antisym; auto.
apply Umult_le_simpl_right with z; auto.
apply Umult_le_simpl_right with z; auto.
Save.

Lemma Umult_simpl_left : forall x y z, ~0 == x -> (x * y) == (x * z) -> y == z.
intros; apply Ole_antisym; auto.
apply Umult_le_simpl_left with x; auto.
apply Umult_le_simpl_left with x; auto.
Save.

Lemma Umult_lt_compat_left : forall x y z, ~0 == z-> x < y -> (x * z) < (y * z).
unfold Ult,not;intros.
apply H0; apply Umult_le_simpl_right with z; auto.
Save.

Lemma Umult_lt_compat_right : forall x y z, ~0 == z -> x < y -> (z * x) < (z * y).
unfold Ult,not;intros.
apply H0; apply Umult_le_simpl_left with z; auto.
Save.


Lemma Umult_lt_simpl_right : forall x y z, ~0 == z -> (x * z) < (y * z) -> x < y.
unfold Ult,not;intros.
apply H0; auto.
Save.

Lemma Umult_lt_simpl_left : forall x y z, ~0 == z -> (z * x) < (z * y) -> x < y.
unfold Ult,not;intros.
apply H0; auto.
Save.

Hint Resolve Umult_lt_compat_left Umult_lt_compat_right.

Lemma Umult_zero_simpl_right : forall x y, 0 == x*y -> ~0 == x -> 0 == y.
intros.
apply Umult_simpl_left with x; auto.
rewrite (Umult_zero_right x); trivial.
Save.

Lemma Umult_zero_simpl_left : forall x y, 0 == x*y -> ~0 == y -> 0 == x.
intros.
apply Umult_simpl_right with y; auto.
rewrite (Umult_zero_left y); trivial.
Save.


Lemma Umult_neq_zero : forall x y, ~0 == x -> ~0 == y -> ~0 == x*y.
red; intros.
apply H0; apply Umult_zero_simpl_right with x; trivial.
Save.
Hint Resolve Umult_neq_zero.

Lemma Umult_lt_zero : forall x y, 0 < x -> 0 < y -> 0 < x*y.
auto.
Save.
Hint Resolve Umult_lt_zero.

Lemma Umult_lt_compat : forall x y z t, x < y -> z < t -> x * z < y * t.
intros.
assert (0<y); auto.
apply Ule_lt_trans with x; auto.
assert (0<t); auto.
apply Ule_lt_trans with z; auto.
apply (Ueq_orc 0 z); auto; intros.
rewrite <- H3.
rewrite Umult_zero_right; auto.
apply Ult_trans with (y * z); auto.
Save.


(** *** More Properties *)

Lemma Uplus_one : forall x y, [1-] x <= y -> x + y == 1.
intros; apply Ole_antisym; auto.
apply Ole_trans with (x + [1-] x); auto.
Save.
Hint Resolve Uplus_one.

Lemma Uplus_one_right : forall x, x + 1 == 1.
auto.
Save.

Lemma Uplus_one_left : forall x:U, 1 + x == 1.
auto.
Save.
Hint Resolve Uplus_one_right Uplus_one_left.

Lemma Uinv_mult_simpl : forall x y z t, x <= [1-] y -> (x * z) <= [1-] (y * t).
intros; apply Ole_trans with x; auto.
intros; apply Ole_trans with ([1-] y); auto.
Save.
Hint Resolve Uinv_mult_simpl.

Lemma Umult_inv_plus :   forall x y, x * [1-] y + y == x + y * [1-] x.
intros; apply Oeq_trans with (x * [1-] y + y * ([1-] x + x)).
setoid_rewrite (Uinv_opp_left x); auto.
assert (H:[1-] x <= [1-] x); auto.
rewrite (Udistr_plus_left y ([1-]x) x H).
apply Oeq_trans with (x * [1-] y + y * x + y * [1-] x).
norm_assoc_right; auto.
rewrite (Umult_sym y x).
assert (H1:[1-] y <= [1-] y); auto.
rewrite <- (Udistr_plus_left x ([1-]y) y H1).
setoid_rewrite (Uinv_opp_left y); auto.
Save.
Hint Resolve Umult_inv_plus.

Lemma Umult_inv_plus_le : forall x y z, y <= z -> x * [1-] y + y <= x * [1-] z + z.
intros.
setoid_rewrite (Umult_inv_plus x y);
setoid_rewrite (Umult_inv_plus x z); auto.
Save.
Hint Resolve Umult_inv_plus_le.

Lemma Uplus_lt_Uinv :   forall x y, x+y < 1 -> x <= [1-] y.
intros; apply (Ule_total x ([1-]y)); intro; auto.
case H.
rewrite Uplus_one; auto.
Save.

Lemma Uinv_lt_perm_left: forall x y : U, [1-] x < y -> [1-] y < x.
unfold Ult; intuition.
Save.

Lemma Uinv_lt_perm_right: forall x y : U, x < [1-] y -> y < [1-] x.
unfold Ult; intuition.
Save.

Hint Immediate Uinv_lt_perm_left Uinv_lt_perm_right.

Lemma Uinv_lt_one : forall x, 0 < x -> [1-]x < 1.
intros; assert ([1-]1 < x); auto.
rewrite Uinv_one; auto.
Save.

Lemma Uinv_lt_zero : forall x, x < 1 -> 0 < [1-]x.
intros; assert (x < [1-]0); auto.
rewrite Uinv_zero; auto.
Save.

Hint Resolve Uinv_lt_one Uinv_lt_zero.

Lemma orc_inv_plus_one : forall x y, orc (x<=[1-]y) (x+y==1).
intros; apply (Ule_total x ([1-]y)); intro; auto.
apply class_orc; trivial.
Save.

Lemma Umult_lt_right : forall p q, p <1 -> 0 < q -> p * q < q.
intros.
apply Ult_le_trans with (1 * q); auto.
Save.

Lemma Umult_lt_left : forall p q, 0 < p -> q < 1 -> p * q < p.
intros.
apply Ult_le_trans with (p * 1); auto.
Save.

Hint Resolve Umult_lt_right Umult_lt_left.

(** ** Definition of $x^n$ *)
Fixpoint Uexp (x:U) (n:nat) {struct n} : U :=
   match n with 0 => 1 | (S p) => x * Uexp x p end.

Infix "^" := Uexp : U_scope.

Lemma Uexp_1 : forall x, x^1==x.
simpl; auto.
Save.

Lemma Uexp_0 : forall x, x^0==1.
simpl; auto.
Save.

Lemma Uexp_zero : forall n, (0<n)%nat -> 0^n==0.
destruct n; simpl; intro; auto.
casetype False; omega.
Save.

Lemma Uexp_one : forall n, 1^n==1.
induction n; simpl; auto.
Save.

Lemma Uexp_le_compat_right :
      forall x n m, (n<=m)%nat -> x^m <= x^n.
induction 1; simpl; auto.
apply Ole_trans with (x^m); auto.
Save.

Lemma Uexp_le_compat_left :  forall x y n,  x<=y -> x^n <= y^n.
induction n; simpl; intros; auto.
apply Ole_trans with (x * (y^n)); auto.
Save.
Hint Resolve Uexp_le_compat_left Uexp_le_compat_right.

Lemma Uexp_le_compat : forall x y (n m:natO), x<=y -> n<=m -> x^m <= y^n.
intros; apply Ole_trans with (x^n); auto.
Save.

Definition UExp : UI-m>natO-m>UI.
apply le_compat2_mon with (f:=Uexp:UI->natO->UI); simpl; intros; auto.
apply Uexp_le_compat; trivial.
Defined.

Add Morphism Uexp with signature Oeq (O:=U) ==> eq (A:=nat) ==> Oeq (O:=U) as Uexp_eq_compat.
intros; apply Ole_antisym; auto.
Save.

Lemma Uexp_inv_S : forall x n, ([1-]x^(S n))==x*([1-]x^n)+[1-]x.
simpl; auto.
Save.

Lemma Uexp_lt_compat : forall p q n, (O<n)%nat->(p<q)->(p^n<q^n).
induction n; simpl; intros; auto.
casetype False; omega.
destruct n; auto.
apply Umult_lt_compat; auto with arith.
Save.

Hint Resolve Uexp_lt_compat.

Lemma Uexp_lt_zero : forall p n, (0<p)->(0<p^n).
destruct n; intros; auto.
rewrite <- (Uexp_zero (n:=S n)); auto with arith.
Save.
Hint Resolve Uexp_lt_zero.

Lemma Uexp_lt_one : forall p n, (0<n)%nat->(p<1)->(p^n<1).
intros; rewrite <- (Uexp_one n); auto with arith.
Save.
Hint Resolve Uexp_lt_one.

Lemma Uexp_lt_antimon: forall p n m, (n<m)%nat-> 0<p -> p < 1 -> p^m < p^n.
induction 1; simpl; intros; auto with arith.
apply Ult_trans with (p*p^n); auto with arith.
Save.
Hint Resolve Uexp_lt_antimon.

(** *** Properties of division *)

Lemma Udiv_mult : forall x y, ~0==y -> x <= y -> (x/y)*y == x.
intros; rewrite Umult_sym; auto.
Save.
Hint Resolve Udiv_mult.

Lemma Umult_div_le : forall x y, y * (x / y) <= x.
intros; apply (Ueq_orc 0 y); auto; intros.
apply Ole_trans with (0 * (x/y)); auto.
rewrite Umult_zero_left; auto.
intros; apply (Ule_total x y); auto; intros.
rewrite Udiv_le_one; auto.
rewrite Umult_one_right; auto.
Save.
Hint Resolve Umult_div_le.

Lemma Udiv_mult_le : forall x y, (x/y)*y <= x.
intros; rewrite Umult_sym; auto.
Save.
Hint Resolve Udiv_mult_le.

Lemma Udiv_le_compat_left :  forall x y z, x <= y -> x/z <= y/z.
intros; apply (Ueq_orc 0 z); auto; intros.
rewrite (Udiv_by_zero x); auto.
intros; apply (Ule_total y z); auto; intros.
apply Umult_le_simpl_right with z; auto.
rewrite (Udiv_mult x); auto.
rewrite (Udiv_mult y); auto.
apply Ole_trans with y; auto.
rewrite (Udiv_le_one y); auto.
Save.
Hint Resolve Udiv_le_compat_left.

Lemma Udiv_eq_compat_left : forall x y z, x == y -> x/z == y/z.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve Udiv_eq_compat_left.


Lemma Umult_div_le_left : forall x y z, ~0==y -> x*y<=z -> x <= z/y.
intros; apply (Ule_total y z); auto; intros.
rewrite (Udiv_le_one z); auto.
apply Umult_le_simpl_right with y; auto.
apply Ole_trans with z; auto.
rewrite (Udiv_mult z H); auto.
Save.

Lemma Udiv_le_compat_right : forall x y z, ~0==y -> y <= z ->  x/z <= x/y.
intros; assert ( ~ 0 == z).
apply Ule_neq_zero with y; auto.
apply (Ule_total z x); auto; intros.
rewrite Udiv_le_one; auto.
rewrite Udiv_le_one; auto.
apply Ole_trans with z; trivial.
apply Umult_div_le_left; auto.
apply Ole_trans with (x/z * z); auto.
Save.
Hint Resolve Udiv_le_compat_right.

Lemma Udiv_eq_compat_right : forall x y z, y == z -> x/z == x/y.
intros; apply (Ueq_orc 0 y); auto; intros.
assert (0==z).
rewrite <- H; auto.
repeat rewrite Udiv_by_zero; auto.
assert ( ~ 0 == z).
apply Ule_neq_zero with y; auto.
apply Ole_antisym; auto.
Save.
Hint Resolve Udiv_eq_compat_right.

Add Morphism Udiv with signature Oeq (O:=U) ==> Oeq (O:=U) ==> Oeq (O:=U) as Udiv_eq_compat.
intros.
apply Oeq_trans with (x/y0); auto.
Save.

Add Morphism Udiv with signature Ole (o:=U) ++> Oeq (O:=U) ==> Ole (o:=U) as Udiv_le_compat.
intros.
apply Ole_trans with (x/y0); auto.
Save.

Lemma Umult_div_eq : forall x y z, ~0==y -> x*y==z -> x == z/y.
intros; apply Umult_simpl_right with y; auto.
assert (z<=y).
apply Ole_trans with (x*y); auto.
apply Oeq_trans with z; auto.
apply Oeq_sym; auto.
Save.

Lemma Umult_div_le_right : forall x y z,  x <= y*z -> x/z <= y.
intros; apply (Ueq_orc 0 z); auto; intros.
rewrite Udiv_by_zero; auto.
apply Umult_le_simpl_right with z; auto.
assert (x<=z).
apply Ole_trans with (y*z); auto.
rewrite (Udiv_mult x H0); auto.
Save.

Lemma Udiv_le : forall x y, ~0==y -> x <= x/y.
intros; apply Umult_div_le_left; auto.
Save.

Lemma Udiv_zero : forall x, 0/x==0.
intros; apply (Ueq_orc 0 x); auto; intros.
apply Oeq_sym; apply Umult_div_eq; auto.
Save.
Hint Resolve Udiv_zero.

Lemma Udiv_zero_eq : forall x y, 0==x -> x/y==0.
intros; rewrite <- H; auto.
Save.
Hint Resolve Udiv_zero_eq.

Lemma Udiv_one : forall x, ~0==x -> x/1==x.
intros; apply Oeq_sym; apply Umult_div_eq; auto.
Save.
Hint Resolve Udiv_one.

Lemma Udiv_refl : forall x, ~0==x -> x/x==1.
auto.
Save.
Hint Resolve Udiv_refl.

Lemma Umult_div_assoc : forall x y z, y <= z->  (x*y) / z == x * (y/z).
intros; apply (Ueq_orc 0 z); auto; intros.
repeat rewrite Udiv_by_zero; auto.
apply Oeq_sym; apply Umult_div_eq; auto.
apply Oeq_trans with (x * (y / z * z)); auto.
Save.

Lemma Udiv_mult_assoc : forall x y z, x <= y*z ->  x/(y*z) == (x/y)/z.
intros; apply (Ueq_orc 0 z); auto; intros.
rewrite (Udiv_by_zero (x/y)); auto.
rewrite Udiv_by_zero; auto; rewrite <- H0; auto.
intros; apply (Ueq_orc 0 y); auto; intros.
rewrite (Udiv_by_zero x); auto.
rewrite <-H1; auto.
rewrite (Udiv_by_zero x); auto.
rewrite <-H1; auto.
apply Oeq_sym; apply Umult_div_eq; auto.
rewrite (Umult_sym y z).
apply Oeq_trans with (x / y / z * z * y); auto.
assert (x/y <= z).
apply Umult_div_le_right; auto.
apply Ole_trans with (y*z); auto.
rewrite (Udiv_mult (x/y) H0); auto.
assert (x<=y); auto.
apply Ole_trans with (y*z); auto.
Save.

Lemma Udiv_inv : forall x y, ~0==y -> [1-](x/y) <= ([1-]x)/y.
intros; apply (Ule_total x y); auto; intros.
apply Umult_div_le_left; auto.
apply Ole_trans with ([1-] (x/y * y)); auto.
rewrite Udiv_le_one; auto.
Save.

Lemma Uplus_div_inv : forall x y z, x+y <= z -> x<=[1-]y -> x/z <= [1-](y/z).
intros; apply (Ueq_orc 0 z); auto; intros.
repeat (rewrite Udiv_by_zero; auto).
apply Umult_div_le_right; auto.
apply Uplus_le_simpl_right with ([1-]z).
apply Uinv_le_compat; apply Ole_trans with (x+y); auto.
rewrite <- Udistr_inv_right.
rewrite Udiv_mult; auto.
apply Ole_trans with (x+[1-](x+y)); auto.
rewrite Uplus_sym; rewrite Uinv_plus_left; auto.
apply Ole_trans with (x+y); auto.
Save.
Hint Resolve Uplus_div_inv.

Lemma Udiv_plus_le : forall x y z,  x/z + y/z <= (x+y)/z.
intros; apply (Ueq_orc 0 z); auto; intros.
repeat (rewrite Udiv_by_zero; auto).
intros; apply Umult_div_le_left; auto.
rewrite Umult_sym; rewrite Udistr_plus_left_le.
apply Uplus_le_compat; rewrite Umult_sym; auto.
Save.
Hint Resolve Udiv_plus_le.

Lemma Udiv_plus : forall x y z, (x+y)/z == x/z + y/z.
intros; apply Ole_antisym; auto.
apply (Ueq_orc 0 z); auto; intros.
repeat (rewrite Udiv_by_zero; auto).
apply (Ule_total x z); auto; intros.
apply (Ule_total y z); auto; intros.
apply (Ule_total (x/z) ([1-](y/z))); auto; intros.
apply Umult_div_le_right; auto.
rewrite Udistr_plus_right; auto.
apply Uplus_le_compat; rewrite Udiv_mult; auto.
rewrite (Uplus_one (x/z) (y/z)); auto.
rewrite (Udiv_le_one y H); auto.
apply Ole_trans with 1; auto.
rewrite (Udiv_le_one x H); auto.
apply Ole_trans with 1; auto.
Save.
Hint Resolve Udiv_plus.

Lemma UDiv (k:U) : U-m>U.
intros; exists (fun x => x/k); red; intros; auto.
Defined.

Lemma UDiv_simpl : forall (k:U) x, UDiv k x = x/k.
trivial.
Save.

(** ** Definition and properties of $x \& y$
   A conjonction operation which coincides with min and mult
   on 0 and 1, see Morgan & McIver *)

Definition Uesp (x y:U) := [1-] ([1-] x + [1-] y).

Infix "&" := Uesp  (left associativity, at level 40) : U_scope.

Lemma Uinv_plus_esp : forall x y, [1-] (x + y) == [1-] x & [1-] y.
unfold Uesp; intros.
setoid_rewrite (Uinv_inv x); setoid_rewrite (Uinv_inv y); auto.
Save.
Hint Resolve Uinv_plus_esp.

Lemma Uinv_esp_plus : forall x y, [1-] (x & y) == [1-] x + [1-] y.
unfold Uesp; intros.
setoid_rewrite (Uinv_inv ([1-] x + [1-] y)); trivial.
Save.
Hint Resolve Uinv_esp_plus.


Lemma Uesp_sym : forall x y : U, x & y == y & x.
intros; unfold Uesp; auto.
Save.

Lemma Uesp_one_right : forall x : U, x & 1 == x.
intro; unfold Uesp.
setoid_rewrite Uinv_one.
setoid_rewrite (Uplus_zero_right ([1-] x)); auto.
Save.

Lemma Uesp_one_left : forall x : U, 1 & x  == x.
intros; rewrite Uesp_sym; apply Uesp_one_right.
Save.

Lemma Uesp_zero : forall x y, x <= [1-] y -> x & y == 0.
intros; unfold Uesp.
setoid_rewrite <- Uinv_one; auto.
Save.

Hint Resolve Uesp_sym Uesp_one_right Uesp_one_left Uesp_zero.

Lemma Uesp_zero_right : forall x : U, x & 0 == 0.
auto.
Save.

Lemma Uesp_zero_left : forall x : U, 0 & x == 0.
auto.
Save.

Hint Resolve Uesp_zero_right Uesp_zero_left.

Add Morphism Uesp with signature Oeq (O:=U) ==> Oeq (O:=U) ==> Oeq (O:=U) as Uesp_eq_compat.
unfold Uesp; intros.
apply Uinv_eq_compat.
rewrite H; rewrite H0; auto.
Save.

Lemma Uesp_le_compat : forall x y z t, x<=y -> z <=t -> x&z <= y&t.
unfold Uesp; intros.
apply Uinv_le_compat.
apply Uplus_le_compat; auto.
Save.

Hint Immediate Uesp_le_compat Uesp_eq_compat.

Lemma Uesp_zero_one_mult_left : forall x y, orc (x == 0) (x == 1) -> x & y == x * y.
intros; apply H; intros; auto.
rewrite H0; rewrite Uesp_zero_left; auto.
rewrite H0; rewrite Uesp_one_left; auto.
Save.

Lemma Uesp_zero_one_mult_right : forall x y, orc (y == 0) (y == 1) -> x & y == x * y.
intros; apply H; intros; auto.
rewrite H0; rewrite Uesp_zero_right; auto.
rewrite H0; rewrite Uesp_one_right; auto.
Save.

Hint Immediate Uesp_zero_one_mult_left Uesp_zero_one_mult_right.

Definition UEsp : U -m> U -m> U := le_compat2_mon Uesp_le_compat.

Lemma Uesp_le_left : forall x y, x & y <= x.
unfold Uesp; intros.
apply Uinv_le_perm_left; auto.
Save.

Lemma Uesp_le_right : forall x y, x & y <= y.
unfold Uesp; intros.
apply Uinv_le_perm_left; auto.
Save.

Hint Resolve Uesp_le_left Uesp_le_right.

Lemma Uesp_plus_inv : forall x y, [1-] y <= x -> x == x & y + [1-] y.
unfold Uesp; intros.
rewrite Uinv_plus_right; auto.
Save.
Hint Resolve Uesp_plus_inv.

Lemma Uesp_le_plus_inv : forall x y, x <= x & y + [1-] y.
intros; apply (Ule_total ([1-]y) x); intros; auto.
rewrite Uesp_zero; auto.
rewrite Uplus_zero_left; auto.
Save.
Hint Resolve Uesp_le_plus_inv.

Lemma Uplus_inv_le_esp : forall x y z, x <= y + ([1-] z) -> x & z <= y.
intros; unfold Uesp.
apply Uinv_le_perm_left.
apply Ole_trans with ([1-](y+[1-]z) + [1-]z); auto.
Save.
Hint Immediate Uplus_inv_le_esp.

(** ** Definition and properties of $x - y$ *)

Definition Uminus (x y:U) := [1-] ([1-] x + y).

Infix "-" := Uminus : U_scope.

Lemma Uminus_le_compat_left : forall x y z, x <= y -> x - z <= y - z.
unfold Uminus; auto.
Save.

Lemma Uminus_le_compat_right :  forall x y z, y <= z -> x - z <= x - y.
unfold Uminus; auto.
Save.

Hint Resolve Uminus_le_compat_left Uminus_le_compat_right.

Lemma Uminus_le_compat : forall x y z t, x <= y ->  t <= z -> x - z <= y - t.
intros; apply Ole_trans with (x-t); auto.
Save.

Hint Immediate Uminus_le_compat.

Add Morphism Uminus with signature Oeq (O:=U) ==> Oeq (O:=U) ==> Oeq (O:=U) as Uminus_eq_compat.
intros x1 x2 eq1 x3 x4 eq2; apply Ole_antisym;
apply Ole_trans with (x1-x4); auto.
Save.
Hint Immediate Uminus_eq_compat.

Add Morphism Uminus with signature Ole (o:=U) ++> Ole (o:=U) --> Ole (o:=U) as Uminus_le_compat_morph.
intros x1 x2 eq1 x3 x4 eq2; apply Uminus_le_compat; auto.
Save.


Lemma Uminus_zero_right : forall x, x - 0 == x.
unfold Uminus; intros.
setoid_rewrite (Uplus_zero_right ([1-] x)); auto.
Save.

Lemma Uminus_one_left : forall x, 1 - x == [1-] x.
unfold Uminus; intros.
setoid_rewrite Uinv_one; auto.
Save.

Lemma Uminus_le_zero : forall x y, x <= y -> x - y == 0.
unfold Uminus; intros.
setoid_rewrite <- Uinv_one.
apply Uinv_eq_compat.
apply Ole_antisym; auto.
apply Ole_trans with ([1-] y + y); auto.
Save.

Hint Resolve Uminus_zero_right Uminus_one_left Uminus_le_zero.

Lemma Uminus_eq : forall x, x-x == 0.
auto.
Save.
Hint Resolve Uminus_eq.

Lemma Uminus_le_left : forall x y, x - y <= x.
unfold Uminus; auto.
Save.

Hint Resolve Uminus_le_left.


Lemma Uminus_le_inv : forall x y, x - y <= [1-]y.
intros.
unfold Uminus.
apply Uinv_le_compat; auto.
Save.
Hint Resolve Uminus_le_inv.

Lemma Uminus_plus_simpl : forall x y, y <= x -> (x - y) + y == x.
unfold Uminus; intros.
rewrite (Uinv_plus_right ([1-]x) y); auto.
Save.

Lemma Uminus_plus_zero : forall x y, x <= y -> (x - y) + y == y.
intros; rewrite (Uminus_le_zero x y); auto.
Save.

Hint Resolve Uminus_plus_simpl Uminus_plus_zero.

Lemma Uminus_plus_le : forall x y, x <= (x - y) + y.
intros; apply (Ule_total x y); intros; auto.
apply Ole_trans with y ; auto.
rewrite (Uminus_plus_simpl x y H); trivial.
Save.

Hint Resolve Uminus_plus_le.

Lemma Uesp_minus_distr_left : forall x y z, (x & y) - z  == (x - z) & y.
unfold Uesp, Uminus; intros.
apply Uinv_eq_compat.
setoid_rewrite (Uinv_inv ([1-] x + [1-] y)).
setoid_rewrite (Uinv_inv (([1-] x) + z)).
repeat norm_assoc_right; auto.
Save.

Lemma Uesp_minus_distr_right : forall x y z, (x & y) - z  == x & (y - z).
intros; rewrite (Uesp_sym x y).
setoid_rewrite (Uesp_sym x (y - z));
apply Uesp_minus_distr_left.
Save.

Hint Resolve Uesp_minus_distr_left Uesp_minus_distr_right.

Lemma Uesp_minus_distr : forall x y z t, (x & y) - (z + t) == (x - z) & (y - t).
unfold Uesp, Uminus; intros.
apply Uinv_eq_compat.
setoid_rewrite (Uinv_inv ([1-] x + [1-] y)).
setoid_rewrite (Uinv_inv ([1-] x + z)).
setoid_rewrite (Uinv_inv ([1-] y + t)).
repeat norm_assoc_right; auto.
Save.
Hint Resolve Uesp_minus_distr.

Lemma Uminus_esp_simpl_left : forall x y, [1-]x <= y -> x - (x & y) == [1-]y.
unfold Uesp,Uminus; intros.
apply Uinv_eq_compat.
rewrite (Uplus_sym ([1-]x)).
rewrite Uinv_plus_left; auto.
Save.

Lemma Uplus_esp_simpl : forall x y, (x - (x & y))+y == x+y.
intros; apply (Ule_total ([1-]x) y); auto; intros.
rewrite Uminus_esp_simpl_left; auto.
rewrite (@Uplus_one x y); auto.
rewrite (@Uesp_zero x y); auto.
Save.
Hint Resolve Uminus_esp_simpl_left Uplus_esp_simpl.

Lemma Uminus_esp_le_inv  : forall x y, x - (x & y) <= [1-]y.
intros; apply (Ule_total ([1-]x) y); auto; intros.
rewrite (@Uesp_zero x y); auto.
rewrite Uminus_zero_right; auto.
Save.

Hint Resolve Uminus_esp_le_inv.

Lemma Uplus_esp_inv_simpl : forall x y, x <= [1-]y -> (x + y) & [1-]y == x.
unfold Uesp; intros.
apply Uinv_eq_perm_left.
rewrite Uinv_inv; auto.
Save.
Hint Resolve Uplus_esp_inv_simpl.

Lemma Uplus_inv_esp_simpl : forall x y, x <= y -> (x + [1-]y) & y == x.
intros.
apply Oeq_trans with ((x + [1-] y) & [1-][1-]y); auto.
rewrite Uinv_inv; auto.
Save.
Hint Resolve Uplus_inv_esp_simpl.

Lemma Umult_inv_minus : forall x y, x * [1-]y == x - (x * y).
unfold Uminus; intros.
apply Uplus_eq_simpl_right with (x * y).
rewrite Udistr_inv_left.
rewrite Uinv_inv; auto.
rewrite Uinv_inv; auto.
rewrite <- Udistr_plus_left; auto.
rewrite Uinv_opp_left.
rewrite Umult_one_right.
rewrite Uinv_plus_right; auto.
Save.
Hint Resolve Umult_inv_minus.

(** ** Definition and properties of max *)

Definition max (x y : U) : U := (x - y) + y.

Lemma max_eq_right : forall x y : U, y <= x -> max x y == x.
unfold max; auto.
Save.

Lemma max_eq_left : forall x y : U, x <= y -> max x y == y.
unfold max; auto.
Save.

Hint Resolve max_eq_right max_eq_left.

Lemma max_eq_case : forall x y : U, orc (max x y == x) (max x y == y).
intros; apply (Ule_total x y); auto.
Save.

Add Morphism max with signature Oeq (O:=U) ==> Oeq (O:=U) ==> Oeq (O:=U) as max_eq_compat.
unfold max; intros.
apply Uplus_eq_compat; auto.
Save.

Lemma max_le_right : forall x y : U, x <= max x y.
intros; apply (Ule_total x y); intros; auto.
rewrite max_eq_left; auto.
rewrite max_eq_right; auto.
Save.

Lemma max_le_left : forall x y : U, y <= max x y.
intros; apply (Ule_total x y); intros; auto.
rewrite max_eq_left; auto.
rewrite max_eq_right; auto.
Save.

Hint Resolve max_le_right max_le_left.

Lemma max_le : forall x y z : U, x <= z -> y <= z -> max x y <= z.
intros; apply (Ule_total x y); intros; auto.
rewrite max_eq_left; auto.
rewrite max_eq_right; auto.
Save.

Lemma max_le_compat : forall x y z t: U, x <= y -> z <= t -> max x z <= max y t.
intros; apply max_le; auto.
apply Ole_trans with y; auto.
apply Ole_trans with t; auto.
Save.

Definition Max : U-m>U-m>U := le_compat2_mon max_le_compat.

Lemma max_eq_mult : forall k x y, max (k*x) (k*y) == k * max x y.
intros; apply Ole_antisym.
apply max_le; auto.
apply (max_eq_case (x:=x) (y:= y)); auto; intro H; rewrite H; auto.
Save.

Lemma max_eq_plus_cte_right : forall x y k, max (x+k) (y+k) == (max x y) + k.
intros; apply Ole_antisym.
apply max_le; auto.
apply (max_eq_case (x:=x) (y:= y)); auto; intro H; rewrite H; auto.
Save.

Hint Resolve max_eq_mult max_eq_plus_cte_right.

(** ** Definition and properties of min *)

Definition min (x y : U) : U := [1-] ((y - x) + [1-]y).

Lemma min_eq_right : forall x y : U, x <= y -> min x y == x.
unfold min, Uminus; intros.
apply Uinv_eq_perm_left; auto.
Save.

Lemma min_eq_left : forall x y : U, y <= x -> min x y== y.
unfold min; intros.
rewrite Uminus_le_zero; auto.
Save.

Hint Resolve min_eq_right min_eq_left.

Lemma min_eq_case : forall x y : U, orc (min x y == x) (min x y == y).
intros; apply (Ule_total x y); auto.
Save.

Add Morphism min with signature Oeq (O:=U) ==>  Oeq (O:=U) ==> Oeq (O:=U) as min_eq_compat.
unfold min; intros.
apply Uinv_eq_compat; auto.
apply Uplus_eq_compat; auto.
Save.

Lemma min_le_right : forall x y : U, min x y <=x.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_left; auto.
Save.

Lemma min_le_left : forall x y : U, min x y <= y.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto.
Save.

Hint Resolve min_le_right min_le_left.

Lemma min_le : forall x y z : U, z <= x -> z <= y -> z <= min x y.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto.
rewrite min_eq_left; auto.
Save.

Lemma Uinv_min_max : forall x y, [1-](min x y)==max ([1-]x) ([1-]y).
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto; rewrite max_eq_right; auto.
rewrite min_eq_left; auto; rewrite max_eq_left; auto.
Save.

Lemma Uinv_max_min : forall x y, [1-](max x y)==min ([1-]x) ([1-]y).
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_left; auto; rewrite max_eq_left; auto.
rewrite min_eq_right; auto; rewrite max_eq_right; auto.
Save.

Lemma min_mult : forall x y k,
    min (k * x) (k * y) == k * (min x y).
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto; rewrite min_eq_right; auto.
rewrite min_eq_left; auto; rewrite min_eq_left; auto.
Save.
Hint Resolve min_mult.

Lemma min_plus : forall x1 x2 y1 y2,
    (min x1 x2)  + (min y1 y2) <= min (x1+y1) (x2+y2).
intros; apply min_le; auto.
Save.
Hint Resolve min_plus.

Lemma min_plus_cte : forall x y k, min (x + k) (y + k) == (min x y) + k.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto; rewrite min_eq_right; auto.
rewrite min_eq_left; auto; rewrite min_eq_left; auto.
Save.
Hint Resolve min_plus_cte.

Lemma min_le_compat : forall x1 y1 x2 y2,
      x1<=y1 -> x2 <=y2 -> min x1 x2 <= min y1 y2.
intros; apply min_le.
apply Ole_trans with x1; auto.
apply Ole_trans with x2; auto.
Save.

Definition Min : U-m>U-m>U := le_compat2_mon min_le_compat.

Lemma min_sym : forall x y, min x y == min y x.
intros; apply (Ule_total x y); intros; auto.
rewrite min_eq_right; auto.
rewrite min_eq_left; auto.
rewrite min_eq_left; auto.
rewrite min_eq_right; auto.
Save.
Hint Resolve min_sym.


Lemma incr_decomp_aux : forall f g : fmon natO  U,
     forall n1 n2, (forall m, ~ ((n1<=m)%nat /\ f n1 <= g m))
           -> (forall m, ~((n2<=m)%nat /\ g n2<= f m)) -> (n1<=n2)%nat -> False.
intros; assert (absurd:~ g n2 < g n2); auto.
assert ( ~ (f n1 <= g n2)).
apply not_and_elim_left with (1:= H n2); auto.
assert ( ~ (g n2 <= f n2)); auto.
apply not_and_elim_left with (1:= H0 n2); auto.
apply absurd; apply Ult_le_trans with (f n1); auto.
apply Ole_trans with (f n2); auto.
Save.

Lemma incr_decomp : forall f g: fmon natO U,
     orc (forall n, exc (fun m => (n<=m)%nat /\ f n <= g m))
           (forall n, exc (fun m => (n<=m)%nat /\ g n <= f m)).
intros f g; apply orc_intro; intros.
apply H; clear H; intros.
apply exc_intro_class; intros.
apply H0; clear H0; intros.
apply exc_intro_class; intros.
case (dec_le n n0); intro.
apply (incr_decomp_aux f g) with (n1:=n) (n2:=n0); auto.
apply (incr_decomp_aux g f) with (n1:=n0) (n2:=n); auto; omega.
Save.



(** ** Other properties *)
Lemma Uplus_minus_simpl_right : forall x y, y <= [1-] x -> (x + y) - y == x.
unfold Uminus; intros.
rewrite (Uinv_plus_right x y); auto.
Save.
Hint Resolve Uplus_minus_simpl_right.

Lemma Uplus_minus_simpl_left : forall x y, y <= [1-] x -> (x + y) - x == y.
intros; setoid_rewrite (Uplus_sym x y); auto.
Save.

Lemma Uminus_assoc_left : forall x y z, (x - y) - z == x - (y + z).
unfold Uminus; intros.
apply Uinv_eq_compat.
setoid_rewrite (Uinv_inv ([1-] x + y)); auto.
Save.

Hint Resolve Uminus_assoc_left.

Lemma Uminus_perm : forall x y z, (x - y) - z == (x - z) - y.
intros; rewrite Uminus_assoc_left.
rewrite (Uplus_sym y z); auto.
Save.
Hint Resolve Uminus_perm.

Lemma Uminus_le_perm_left : forall x y z, y <= x -> x - y <= z -> x <= z + y.
intros; rewrite <- (Uminus_plus_simpl x y); auto.
Save.

Lemma Uplus_le_perm_left : forall x y z, x <= y + z  -> x - y <= z.
intros; apply (Ule_total y x); intros; auto.
apply Uplus_le_simpl_left with y.
unfold Uminus; setoid_rewrite (Uinv_inv ([1-] x + y)); auto.
setoid_rewrite (Uplus_sym y (x-y)); rewrite (Uminus_plus_simpl x y); auto.
apply Ole_trans with (0:U); auto.
Save.
(*
Lemma Uplus_le_perm_left : forall x y z, y <= x -> x <= y + z  -> x - y <= z.
intros; apply Uplus_le_simpl_left with y.
unfold Uminus; setoid_rewrite (Uinv_inv ([1-] x + y)); auto.
setoid_rewrite (Uplus_sym y (x-y)); rewrite (Uminus_plus_simpl x y); auto.
Save.
*)

Lemma Uminus_eq_perm_left : forall x y z, y <= x -> x - y == z -> x == z + y.
intros; rewrite <- (Uminus_plus_simpl x y); auto.
Save.

Lemma Uplus_eq_perm_left : forall x y z, y <= [1-] z -> x == y + z  -> x - y == z.
intros; setoid_rewrite H0; auto.
setoid_rewrite (Uplus_sym y z); auto.
Save.

Hint Resolve Uminus_le_perm_left Uminus_eq_perm_left.
Hint Resolve Uplus_le_perm_left Uplus_eq_perm_left.

Lemma Uminus_le_perm_right : forall x y z, z <= y -> x <= y - z -> x + z <= y.
intros; rewrite <- (Uminus_plus_simpl y z); auto.
Save.

Lemma Uplus_le_perm_right : forall x y z, z <= [1-] x -> x + z <= y  -> x <= y - z.
intros; apply Uplus_le_simpl_right with z; auto.
Save.
Hint Resolve Uminus_le_perm_right Uplus_le_perm_right.

Lemma Uminus_le_perm : forall x y z, z <= y -> x <= [1-] z -> x <= y - z -> z <= y - x.
intros; apply Uplus_le_perm_right; auto.
setoid_rewrite (Uplus_sym z x); auto.
Save.
Hint Resolve Uminus_le_perm.

Lemma Uminus_eq_perm_right : forall x y z, z <= y -> x == y - z -> x + z == y.
intros; apply Oeq_trans with (y - z + z); auto.
Save.
Hint Resolve Uminus_eq_perm_right.

Lemma Uminus_plus_perm : forall x y z, y <= x -> z <= [1-]x -> x - y + z == x + z - y.
intros; apply Uminus_eq_perm_right.
apply Ole_trans with (y + z - y); auto.
rewrite Uplus_minus_simpl_left; auto.
apply Ole_trans with ([1-]x); auto.
rewrite Uminus_perm.
rewrite Uplus_minus_simpl_right; auto.
Save.

Lemma Uplus_minus_perm_le : forall x y z, x + z - y <= x - y + z.
intros; apply (Ule_total y x); auto; intro.
apply (Ule_total z ([1-]x)); auto; intro.
rewrite Uminus_plus_perm; auto.
rewrite (Uplus_one x z); auto.
apply Ole_trans with (x - y + [1-]x); auto.
unfold Uminus at 2.
rewrite Uinv_plus_left; auto.
Save.
Hint Resolve Uplus_minus_perm_le.

Lemma Uminus_zero_le : forall x y, x - y == 0 -> x <= y.
intros x y; unfold Uminus; intros.
setoid_rewrite <- (Uinv_inv x).
apply Uplus_one_le.
setoid_rewrite <- Uinv_zero; auto.
setoid_rewrite <- H; auto.
Save.

Lemma Uminus_lt_non_zero : forall x y, x < y -> ~0 == y - x.
red; intros.
apply H; auto.
apply Uminus_zero_le; auto.
Save.
Hint Immediate Uminus_zero_le Uminus_lt_non_zero.

Lemma Ult_le_nth_minus : forall x y, x < y -> exc (fun n => x <= y - [1/]1+n).
intros; apply (archimedian (x:=(y - x))); intros; auto.
apply exc_intro with x0.
apply Uminus_le_perm; auto.
apply Ole_trans with (y - x); auto.
Save.

Lemma Ult_le_nth_plus : forall x y, x < y -> exc (fun n : nat => x + [1/]1+n <= y).
intros.
assert (not (0==y-x)); auto.
assert (H1:exc (fun n => [1/]1+n <= y - x)).
apply archimedian; auto.
apply H1;auto;  intros n H2.
apply exc_intro with n.
apply Ole_trans with (x + (y - x)); auto.
Save.

Lemma Uminus_distr_left : forall x y z, (x - y) * z == (x * z) - (y * z).
intros; apply (Ule_total x y); intros; auto.
(* first case x <= y, left and right hand side equal 0 *)
rewrite (Uminus_le_zero x y); trivial.
rewrite (Umult_zero_left z).
assert (x * z <= y * z); auto.
rewrite (Uminus_le_zero _ _ H0); auto.
(* second case y <= x, use simplification *)
unfold Uminus; intros; auto.
apply Uplus_eq_simpl_right with (y * z); auto.
assert ([1-] ([1-] x + y) <= [1-] y); auto.
rewrite <- (Udistr_plus_right _ _ z H0); auto.
assert (y <= [1-] ([1-] x)); auto.
rewrite (Uinv_plus_right _ _ H1).
rewrite (Uinv_inv x); auto.
Save.

Hint Resolve Uminus_distr_left.

Lemma Uminus_distr_right : forall x y z,  x * (y - z) == (x * y) - (x * z).
intros; setoid_rewrite (Umult_sym x y).
setoid_rewrite (Umult_sym x z).
setoid_rewrite (Umult_sym x (y - z)); auto.
Save.

Hint Resolve Uminus_distr_right.


Lemma Uminus_assoc_right :  forall x y z, y <= x -> z <= y -> x - (y - z) == (x - y) + z.
intros.
apply Uplus_eq_perm_left; auto.
unfold Uminus at 1; apply Uinv_le_compat.
apply Ole_trans with (1 - y + z); auto.
apply Oeq_trans with ((y - z) + z + (x - y)).
rewrite (Uminus_plus_simpl _ _ H0).
rewrite (Uplus_sym y (x - y)); auto.
norm_assoc_right; auto.
Save.

Lemma Uplus_minus_assoc_right : forall x y z, y <= [1-]x -> z <= y -> x + (y - z) == (x + y) - z.
intros; unfold Uminus.
apply Oeq_trans with ([1-] (x + ([1-] (x + y) + z)) + x).
rewrite Uplus_assoc.
rewrite (Uplus_sym x ([1-] (x + y))).
rewrite Uinv_plus_left; auto.
rewrite Uinv_plus_left; auto.
apply Ole_trans with ([1-] (x + y) + y); auto.
Save.

Lemma Udiv_minus : forall x y z, ~0 == z -> x <= z -> (x - y) / z == x/z - y/z.
intros; apply (Ule_total x y); auto; intros.
apply Oeq_trans with (0/z); auto.
rewrite Uminus_le_zero; auto.
assert (y <= z).
apply Ole_trans with x; auto.
apply Oeq_sym; apply Umult_div_eq; auto.
rewrite Uminus_distr_left.
rewrite Udiv_mult; auto.
rewrite Udiv_mult; auto.
Save.

(** ** Definition and properties of generalized sums *)

Definition sigma : (nat -> U) -> natO -m> U.
intros alpha; exists (comp Uplus 0 alpha); red; intros; auto.
induction H; simpl; auto.
apply Ole_trans with (comp Uplus 0 alpha m); auto.
Defined.

Lemma sigma_0 : forall (f : nat -> U), sigma f O == 0.
trivial.
Save.

Lemma sigma_S : forall (f :nat -> U) (n:nat), sigma f (S n) = (f n) + (sigma f n).
trivial.
Save.

Lemma sigma_1 : forall (f : nat -> U), sigma f (S 0) == f O.
intros; rewrite sigma_S; auto.
Save.


Lemma sigma_incr : forall (f : nat -> U) (n m:nat), (n <= m)%nat -> sigma f n <= sigma f m.
intros f n m H; apply (fmonotonic (sigma f)); trivial.
Save.

Hint Resolve sigma_incr.

Lemma sigma_eq_compat : forall (f g: nat -> U) (n:nat),
 (forall k, (k < n)%nat -> f k == g k) -> sigma f n == sigma g n.
induction n; auto.
intros; repeat rewrite sigma_S.
apply Oeq_trans with (g n + sigma f n); auto with arith.
Save.

Lemma sigma_le_compat : forall (f g: nat -> U) (n:nat),
 (forall k, (k < n)%nat -> f k <= g k) -> sigma f n <= sigma g n.
induction n; auto.
intros; repeat rewrite sigma_S.
apply Ole_trans with (g n + sigma f n); auto with arith.
Save.

Lemma sigma_S_lift : forall (f :nat -> U) (n:nat),
          sigma f (S n) == (f O) + (sigma (fun k => f (S k)) n).
intros f n; generalize f; induction n; intros; auto.
rewrite sigma_S.
rewrite IHn.
rewrite sigma_S.
rewrite Uplus_assoc.
rewrite (Uplus_sym (f0 (S n)) (f0 O)); auto.
Save.

Lemma sigma_plus_lift : forall (f :nat -> U) (n m:nat),
          sigma f (n+m)%nat == sigma f n + sigma (fun k => f (n+k)%nat) m.
intros f n m; generalize f; clear f; induction n; intros.
simpl plus.
rewrite sigma_0.
rewrite Uplus_zero_left.
apply sigma_eq_compat; auto.
rewrite sigma_S_lift.
simpl plus.
rewrite sigma_S_lift.
rewrite IHn; auto.
Save.

Lemma sigma_zero : forall f n, (forall k, (k<n)%nat -> f k ==0)-> sigma f n ==0.
induction n; intros; auto.
rewrite sigma_S.
rewrite (H n); auto.
rewrite IHn; auto.
Save.

Lemma sigma_not_zero : forall f n k, (k<n)%nat -> 0 < f k -> 0 < sigma f n.
induction n; intros; auto.
casetype False; omega.
rewrite sigma_S.
assert (k < n \/ k = n)%nat.
omega.
case H1; intros; subst; auto.
apply Ult_le_trans with (sigma f n); auto.
apply (IHn k); auto.
apply Ult_le_trans with (f n); auto.
Save.

Lemma sigma_zero_elim : forall f n, (sigma f n)==0->forall k, (k<n)%nat -> f k ==0.
intros; apply Ueq_class; red; intros.
assert (0 < sigma f n); auto.
apply sigma_not_zero with k; auto.
Save.

Hint Resolve sigma_eq_compat sigma_le_compat sigma_zero.

Lemma sigma_le : forall f n k, (k<n)%nat -> f k <= sigma f n.
induction n; intros.
casetype False; omega.
rewrite sigma_S.
assert (k < n \/ k = n)%nat.
omega.
case H0; intros; subst; auto.
apply Ole_trans with (sigma f n); auto.
Save.

Lemma sigma_minus_decr : forall f n, (forall k, f (S k) <= f k) ->
         sigma (fun k => f k - f (S k)) n == f O - f n.
intros f n fmon;induction n.
rewrite sigma_0; auto.
rewrite sigma_S; rewrite IHn.
rewrite Uplus_sym.
rewrite Uplus_minus_assoc_right; auto.
rewrite Uminus_plus_simpl; auto.
elim n; intros; auto.
apply Ole_trans with (f n0); auto.
Save.

Lemma sigma_minus_incr : forall f n, (forall k, f k <= f (S k)) ->
         sigma (fun k => f (S k) - f k) n == f n - f O.
intros f n fmon;induction n.
rewrite sigma_0; auto.
rewrite sigma_S; rewrite IHn.
rewrite Uplus_minus_assoc_right; auto.
rewrite Uminus_plus_simpl; auto.
elim n; intros; auto.
apply Ole_trans with (f n0); auto.
Save.
(** ** Definition and properties of generalized products *)

Definition prod (alpha : nat -> U) (n:nat) := comp Umult 1 alpha n.

Lemma prod_0 : forall (f : nat -> U), prod f 0 = 1.
trivial.
Save.

Lemma prod_S : forall (f :nat -> U) (n:nat), prod f (S n) = (f n) * (prod f n).
trivial.
Save.

Lemma prod_1 : forall (f : nat -> U), prod f (S 0) == f O.
intros; rewrite prod_S; auto.
Save.

Lemma prod_S_lift : forall (f :nat -> U) (n:nat),
          prod f (S n) == (f O) * (prod (fun k => f (S k)) n).
intros f n; generalize f; induction n; simpl; intros; auto.
rewrite prod_S.
rewrite IHn.
rewrite prod_S.
rewrite Umult_assoc.
rewrite (Umult_sym (f0 (S n)) (f0 O)); auto.
Save.

Lemma prod_decr : forall (f : nat -> U) (n m:nat), (n <= m)%nat -> prod f m <= prod f n.
intros f n m H; induction H; auto.
intros; rewrite prod_S.
apply Ole_trans with (2:=IHle); auto.
Save.

Hint Resolve prod_decr.

Lemma prod_eq_compat : forall (f g: nat -> U) (n:nat),
 (forall k, (k < n)%nat -> f k == g k) -> (prod f n) == (prod g n).
induction n; auto.
intros; repeat rewrite prod_S.
apply Oeq_trans with (g n * prod f n); auto with arith.
Save.

Lemma prod_le_compat : forall (f g: nat -> U) (n:nat),
 (forall k, (k < n)%nat -> f k <= g k) -> prod f n <= prod g n.
induction n; auto.
intros; repeat rewrite prod_S.
apply Ole_trans with (g n * prod f n); auto with arith.
Save.

Lemma prod_zero : forall f n k, (k<n)%nat -> f k ==0 -> prod f n==0.
induction n; simpl; intros; auto.
absurd ((k < 0)%nat); auto with arith.
rewrite prod_S.
assert (k < n \/ k = n)%nat.
omega.
case H1; intros; subst; auto.
rewrite (IHn k); auto.
rewrite H0; auto.
Save.

Lemma prod_not_zero : forall f n, (forall k, (k<n)%nat -> 0 < f k )-> 0 < prod f n.
induction n; simpl; intros; auto.
rewrite prod_S; auto with arith.
Save.

Lemma prod_zero_elim : forall f n, prod f n==0 -> exc (fun k => (k<n)%nat /\ f k ==0).
intros; apply class_exc; red; intros.
assert (forall k, (k<n)%nat -> 0 < f k); intros.
red; intro.
apply H0.
apply exc_intro with k; auto.
absurd (0 < prod f n); auto.
apply prod_not_zero; auto.
Save.

Hint Resolve prod_eq_compat prod_le_compat prod_not_zero.

Lemma prod_le : forall f n k, (k<n)%nat -> prod f n <= f k.
induction n; simpl; intros.
casetype False; omega.
rewrite prod_S.
assert (k < n \/ k = n)%nat.
omega.
case H0; intros; subst; auto.
apply Ole_trans with (prod f n); auto.
Save.

Lemma prod_minus : forall f n, prod f n - prod f (S n) == ([1-]f n)  * prod f n.
intros f n; rewrite prod_S.
apply Oeq_trans with (1 * prod f n - f n * prod f n).
rewrite Umult_one_left; auto.
rewrite <- Uminus_distr_left; auto.
Save.


Definition Prod : (nat->U) -> natO-m>UI.
intro f; exists (prod f); red; intros; auto.
Defined.

Lemma Prod_simpl : forall f n, Prod f n = prod f n.
trivial.
Save.
Hint Resolve Prod_simpl.

(** ** Properties of [Unth] *)
Lemma Unth_zero : [1/]1+0 == 1.
setoid_rewrite (Unth_prop 0); auto.
Save.

Notation "[1/2]" := (Unth 1).

Lemma Unth_one : [1/2] == [1-] [1/2].
apply Oeq_trans with (1:=Unth_prop 1); simpl; auto.
Save.

Hint Resolve Unth_zero Unth_one.

Lemma Unth_one_plus : [1/2] + [1/2] == 1.
apply Oeq_trans with  ([1/2] + [1-][1/2]); auto.
Save.
Hint Resolve Unth_one_plus.

Lemma Unth_not_null : forall n, ~ (0 == [1/]1+n).
red; intros.
apply Udiff_0_1.
apply Oeq_trans with ([1/]1+n); auto.
apply Oeq_trans with ([1-] (sigma (fun k => [1/]1+n) n)).
apply (Unth_prop n).
apply Oeq_trans with ([1-] (sigma (fun k => 0) n)).
apply Uinv_eq_compat.
apply sigma_eq_compat; auto.
apply Oeq_trans with ([1-] 0); auto.
Save.
Hint Resolve Unth_not_null.

Lemma Unth_lt_zero : forall n, 0 < [1/]1+n.
auto.
Save.
Hint Resolve Unth_lt_zero.

Lemma Unth_inv_lt_one : forall n, [1-][1/]1+n<1.
intro; rewrite <- Uinv_zero; auto.
Save.
Hint Resolve Unth_inv_lt_one.

Lemma Unth_not_one : forall n, ~ (1 == [1-][1/]1+n).
auto.
Save.
Hint Resolve Unth_not_one.

Lemma Unth_prop_sigma : forall n, [1/]1+n == [1-] (sigma (fun k => [1/]1+n) n).
exact Unth_prop.
Save.
Hint Resolve Unth_prop_sigma.

Lemma Unth_sigma_n : forall n : nat, ~ (1 == sigma (fun k => [1/]1+n) n).
intros; apply Uinv_neq_simpl.
setoid_rewrite Uinv_one.
setoid_rewrite <- (Unth_prop_sigma n); auto.
Save.

Lemma Unth_sigma_Sn : forall n : nat, 1 == sigma (fun k => [1/]1+n) (S n).
intros; rewrite sigma_S.
apply Oeq_trans with
([1-] (sigma (fun k => [1/]1+n) n) + (sigma (fun k => [1/]1+n) n));auto.
Save.

Hint Resolve Unth_sigma_n Unth_sigma_Sn.


Lemma Unth_decr : forall n, [1/]1+(S n) < [1/]1+n.
repeat red; intros.
apply (Unth_sigma_n (S n)).
apply Ole_antisym; auto.
apply Ole_trans with (sigma (fun _ : nat => [1/]1+n) (S n)); auto.
Save.
Hint Resolve Unth_decr.

Lemma Unth_anti_mon :
forall n m, (n <= m)%nat -> [1/]1+m <= [1/]1+n.
induction 1; auto.
apply Ole_trans with ([1/]1+m); auto.
Save.
Hint Resolve Unth_anti_mon.

Lemma Unth_le_half : forall n, [1/]1+(S n) <= [1/2].
auto with arith.
Save.
Hint Resolve Unth_le_half.

(** *** Mean of two numbers : $\frac{1}{2}x+\frac{1}{2}y$*)
Definition mean (x y:U) := [1/2] * x + [1/2] * y.

Lemma mean_eq : forall x:U, mean x x ==x.
unfold mean; intros.
assert (H : ([1/2] <= [1-] ([1/2]))); auto.
rewrite <- (Udistr_plus_right _ _ x H); auto.
Save.

Lemma mean_sym : forall x y,  mean x y == mean y x.
unfold mean; auto.
Save.
Hint Resolve mean_sym.

Lemma mean_le_compat_right : forall x y z, y <= z -> mean x y <= mean x z.
unfold mean; intros.
apply Uplus_le_compat_right; auto.
Save.

Lemma mean_le_compat_left : forall x y z, x <= y -> mean x z <= mean y z.
unfold mean; intros.
apply Uplus_le_compat_left; auto.
Save.

Hint Resolve mean_eq mean_le_compat_left mean_le_compat_right.

Add Morphism mean with signature (Ole (o:=U)) ++> (Ole (o:=U)) ++> (Ole (o:=U)) as
    mean_le_compat.
intros; apply Ole_trans with (mean y x0); auto.
Save.

Add Morphism mean with signature (Oeq (O:=U)) ==> (Oeq (O:=U)) ==> (Oeq (O:=U)) as
    mean_eq_compat.
split; apply mean_le_compat; auto.
Save.

Lemma mean_lt_compat_right : forall x y z, y < z -> mean x y < mean x z.
unfold mean; intros.
apply Uplus_lt_compat_right; auto.
Save.

Lemma mean_lt_compat_left : forall x y z, x < y -> mean x z < mean y z.
unfold mean; intros.
apply Uplus_lt_compat_left; auto.
Save.

Hint Resolve mean_eq mean_le_compat_left mean_le_compat_right.
Hint Resolve mean_lt_compat_left mean_lt_compat_right.

Lemma mean_le_up : forall x y, x <= y -> mean x y <= y.
intros; apply Ole_trans with (mean y y); auto.
Save.

Lemma mean_le_down : forall x y, x <= y -> x <= mean x y.
intros; apply Ole_trans with (mean x x); auto.
Save.

Lemma mean_lt_up : forall x y, x < y -> mean x y < y.
intros; apply Ult_le_trans with (mean y y); auto.
Save.

Lemma mean_lt_down : forall x y, x < y -> x < mean x y.
intros; apply Ule_lt_trans with (mean x x); auto.
Save.

Hint Resolve mean_le_up mean_le_down mean_lt_up mean_lt_down.

Lemma mean_inv : forall x, mean x ([1-]x) == [1/2].
unfold mean; intros.
rewrite <- Udistr_plus_left; auto.
Save.


Lemma Uinv_mean : forall x y, [1-](mean x y) == mean ([1-]x) ([1-]y).
unfold mean; intros.
repeat rewrite Umult_inv_minus.
apply Oeq_trans with ([1/2]+[1/2] - ([1/2] * x + [1/2]*y)).
rewrite Unth_one_plus; auto.
rewrite <- Uminus_assoc_left.
rewrite <- Uminus_plus_perm; auto.
rewrite <- Uplus_minus_assoc_right; trivial.
apply Uinv_le_perm_right.
rewrite <- Unth_one; auto.
Save.

(** *** Diff function  *)

Definition diff (x y:U) := (x - y) + (y - x).

Lemma diff_eq : forall x, diff x x == 0.
unfold diff; intros; rewrite Uminus_eq; auto.
Save.

Lemma diff_sym : forall x y, diff x y == diff y x.
unfold diff; intros; auto.
Save.


(** *** Properties of $\frac{1}{2}$ *)

Lemma le_half_inv : forall x, x <= [1/2] -> x <= [1-] x.
intros; apply Ole_trans with ([1/2]); auto.
setoid_rewrite Unth_one; auto.
Save.

Hint Immediate le_half_inv.

Lemma ge_half_inv : forall x, [1/2] <= x  -> [1-] x <= x.
intros; apply Ole_trans with ([1/2]); auto.
setoid_rewrite Unth_one; auto.
Save.

Hint Immediate ge_half_inv.

Lemma Uinv_le_half_left : forall x, x <= [1/2] -> [1/2] <= [1-] x.
intros; setoid_rewrite Unth_one; auto.
Save.

Lemma Uinv_le_half_right : forall x, [1/2] <= x -> [1-] x <= [1/2].
intros; setoid_rewrite Unth_one; auto.
Save.

Hint Resolve Uinv_le_half_left Uinv_le_half_right.

Lemma half_twice : forall x,  (x <= [1/2]) -> ([1/2]) * (x + x) == x.
intros; assert (H1 : x <= [1-] x); auto.
rewrite (Udistr_plus_left ([1/2]) _ _ H1).
exact (mean_eq x).
Save.

Lemma half_twice_le : forall x, ([1/2]) * (x + x) <= x.
intros; apply (Ule_total x ([1/2])); intros; auto.
rewrite (half_twice _ H); trivial.
assert (x+x==1); auto.
rewrite H0.
rewrite (Umult_one_right ([1/2])); auto.
Save.

Lemma Uinv_half : forall x, ([1/2]) * ([1-] x)  + ([1/2]) == [1-] (([1/2]) * x).
intros; setoid_rewrite (Udistr_inv_left ([1/2]) x).
setoid_rewrite Unth_one; auto.
Save.

Lemma half_esp :
forall x, ([1/2] <= x) -> ([1/2]) * (x & x) + [1/2] == x.
intros; unfold Uesp.
setoid_rewrite (Uinv_half ([1-] x + [1-] x)).
assert (H1:[1-] x <= [1/2]).
setoid_rewrite Unth_one; auto.
rewrite (half_twice _ H1); auto.
Save.

Lemma half_esp_le : forall x, x <= ([1/2]) * (x & x) + [1/2].
intros; apply (Ule_total ([1/2]) x); intros; auto.
setoid_rewrite (half_esp _ H); trivial.
assert (x & x == 0); auto.
setoid_rewrite H0.
setoid_rewrite (Umult_zero_right ([1/2])).
setoid_rewrite (Uplus_zero_left ([1/2])); auto.
Save.
Hint Resolve half_esp_le.


Lemma half_le : forall x y, y <= [1-] y -> x <= y + y -> ([1/2]) * x <= y.
intros.
apply not_Ult_le; red; intros.
assert (y + y < x); auto.
apply Ult_le_trans with  (mean x x); auto.
unfold mean; apply Uplus_lt_compat; auto.
Save.

Lemma half_Unth: forall n, ([1/2])*([1/]1+n) <= [1/]1+(S n).
intros; apply half_le; auto.
rewrite (Unth_prop_sigma n).
apply Ole_trans with ([1-] (sigma (fun _ : nat => [1/]1+(S n)) n)).
apply Uinv_le_compat.
apply sigma_le_compat; auto.
apply Ole_trans with
([1-] (sigma (fun _ : nat => [1/]1+(S n)) (S n)) + [1/]1+(S n)); auto.
Save.
Hint Resolve half_le half_Unth.

Lemma half_exp : forall n, [1/2]^n == [1/2]^(S n) + [1/2]^(S n).
intros; simpl; apply Oeq_sym; exact (mean_eq ([1/2]^n)).
Save.



(** ** Density *)
Lemma Ule_lt_lim : forall x y,  (forall t, t < x -> t <= y) -> x <= y.
intros; apply Ule_class; red; intros.
pose (z:= mean y x).
assert (y < z); unfold z; auto.
apply H1; apply H; unfold z; auto.
Save.

Lemma Ule_nth_lim : forall x y, (forall p, x <= y + [1/]1+p) -> x <= y.
intros; apply Ule_lt_lim; intros.
apply (Ult_le_nth_minus H0); auto; intros n H1.
apply Ole_trans with (x - [1/]1+n); auto.
apply Ole_trans with (y + [1/]1+n - [1/]1+n); auto.
Save.

(** ** Properties of least upper bounds *)

Lemma lub_un : (lub (fmon_cte natO 1)) == 1.
apply lub_cte.
Save.
Hint Resolve lub_un.

Lemma UPlusk_eq : forall k, UPlus k == mk_fmono (Uplus_le_compat_right k).
intros k; apply fmon_eq_intro; simpl; intros; auto.
Save.

Lemma UMultk_eq : forall k, UMult k == mk_fmono (Umult_le_compat_right k).
intros k; apply fmon_eq_intro; simpl; intros; auto.
Save.

Lemma UPlus_continuous_right : forall k, continuous (UPlus k).
intros; rewrite UPlusk_eq; auto.
Save.
Hint Resolve UPlus_continuous_right.

Lemma UPlus_continuous_left : continuous (UPlus : U -m> U -M-> U).
apply continuous_sym; auto; simpl; auto.
Save.
Hint Resolve UPlus_continuous_left.

Lemma UMult_continuous_right : forall k, continuous (UMult k).
intros; rewrite UMultk_eq; auto.
Save.
Hint Resolve UMult_continuous_right.

Lemma UMult_continuous_left : continuous (UMult : U -m> U -M-> U).
apply continuous_sym; auto; simpl; auto.
Save.
Hint Resolve UMult_continuous_left.

Lemma lub_eq_plus_cte_left : forall (f:natO -m> U) (k:U), lub ((UPlus k) @ f) == k + lub f.
intros; apply Oeq_sym; apply lub_comp_eq with (f:=UPlus k) (h:=f); red; intros; auto.
Save.
Hint Resolve lub_eq_plus_cte_left.

Lemma lub_eq_mult : forall (k:U) (f:natO -m> U), lub ((UMult k) @ f) ==  k * lub f.
intros; apply Oeq_sym; apply lub_comp_eq with (f:=UMult k) (h:=f); trivial.
Save.
Hint Resolve lub_eq_mult.

Lemma lub_eq_plus_cte_right : forall (f : natO -m> U) (k:U),
           lub ((UPlus <_> k) @ f) == lub f + k.
intros; apply Oeq_trans with (k + lub f); auto.
apply Oeq_trans with (lub (UPlus k @ f)); auto.
apply lub_eq_compat; simpl; intros.
apply fmon_eq_intro; simpl; intros.
rewrite (Uplus_sym (f n) k); auto.
Save.
Hint Resolve lub_eq_plus_cte_right.

Lemma min_lub_le : forall f g : natO-m>U,
         lub ((Min @2 f) g) <= min (lub f) (lub g).
intros; apply min_le.
apply lub_le.
intro; apply Ole_trans with (f n); simpl; auto.
apply lub_le.
intro; apply Ole_trans with (g n); simpl; auto.
Save.

Lemma min_lub_le_incr_aux : forall f g : natO -m> U,
         (forall n, exc (fun m => (n<=m)%nat /\ f n <= g m))
         -> min (lub f) (lub g) <= lub ((Min @2 f) g).
intros; apply Ole_trans with (lub f); auto.
apply lub_le; intros.
apply (H n); auto; intros m (H1,H2).
apply Ole_trans with (min (f m) (g m)); auto.
apply min_le; auto.
apply le_lub with (f:=(Min @2 f) g) (n:=m); simpl; auto.
Save.

Lemma min_lub_le_incr : forall f g : natO -m> U,
         min (lub f) (lub g) <= lub ((Min @2 f) g).
intros f g; apply (incr_decomp f g); auto; intros.
apply (min_lub_le_incr_aux f g); auto.
rewrite min_sym.
apply Ole_trans with (lub ((Min @2 g) f)); auto.
apply (min_lub_le_incr_aux g f); auto.
Save.

Lemma lub_eq_esp_right :
  forall (f : natO -m> U) (k : U), lub ((UEsp <_> k) @ f) == lub f & k.
intros; apply Ole_antisym.
apply lub_le; auto.
apply Uplus_inv_le_esp.
rewrite <- lub_eq_plus_cte_right.
apply lub_le_compat; simpl; auto.
Save.
Hint Resolve lub_eq_esp_right.


Lemma Udiv_continuous : forall (k:U), continuous (UDiv k).
red; intros.
rewrite UDiv_simpl.
apply (Ueq_orc 0 k); auto; intros.
rewrite Udiv_by_zero; auto.
apply (excluded_middle (A:=forall n, h n <= k)); auto; intros.
apply Umult_div_le_right; auto.
rewrite Umult_sym.
apply Ole_trans with (lub (UMult k @ (UDiv k @ h))); auto.
apply lub_le_compat; intro n; simpl; auto.
rewrite Umult_div; auto.
assert (exc (fun n => k<=h n)).
apply exc_intro_class; intros; apply H0; intros; auto.
apply Ult_le; auto.
apply H1; auto; intros.
apply Ole_trans with (h x / k).
rewrite (Udiv_le_one (h x) H); auto.
apply le_lub with (f:=UDiv k @ h) (n:=x).
Save.
Hint Resolve Udiv_continuous.

(** ** Greatest lower bounds *)


Definition glb (f:natO-m>UI) := [1-]lub (UInv @ f).

Lemma glb_le:   forall (f : natO -m> UI) (n : nat), glb f <= (f n).
unfold glb; intros; apply Uinv_le_perm_left.
apply le_lub with (f:=UInv @ f) (n:=n); auto.
Save.

Lemma le_glb: forall (f : natO -m> UI) (x:U), (forall n : nat, x <= f n)-> x <= glb f.
unfold glb; intros; apply Uinv_le_perm_right.
apply lub_le with (f:=UInv @ f); auto.
Save.
Hint Resolve glb_le le_glb.

Definition Uopp : cpo.
   exists UI 1 glb; auto.
Defined.

(** Equality in Uopp and U are equivlent *)

Lemma Ueq_opp : forall x y:Uopp, x==y -> (x:U)==y.
unfold Oeq; intuition.
Save.

Lemma Uopp_eq : forall x y:Uopp,  (x:U)==y -> x==y.
unfold Oeq; intuition.
Save.
Hint Immediate Ueq_opp Uopp_eq.

Lemma Uopp_mon_seq : forall f:natO-m>Uopp,
   forall n m:nat, (n <= m)%nat -> (f m:U) <= f n.
intros f n m H; exact (fmonotonic f H).
Save.
Hint Resolve Uopp_mon_seq.


(** Infinite product $\Pi_{i=0}^{\infty} f\,i$ *)
Definition prod_inf (f : nat -> U) : U := glb (Prod f).

(** Properties of glb *)

Lemma glb_le_compat:
  forall f g :  natO -m> UI, (f :natO-o>U) <= g -> glb f <= glb g.
intros f g; exact (lub_le_compat (D:=Uopp) (f:=g) (g:=f)).
Save.
Hint Resolve glb_le_compat.

Lemma glb_eq_compat:
  forall f g : natO -m> UI, f == g -> glb f == glb g.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve glb_eq_compat.

Lemma glb_cte: forall c : U, glb (fmon_cte natO (c:Uopp)) == c.
intros; apply Oeq_sym; exact (lub_cte (D:=Uopp) c).
Save.
Hint Resolve glb_cte.

Lemma glb_eq_plus_cte_right:
  forall (f : natO -m> UI) (k : U), glb (Imon (UPlus <_> k) @ f) == glb f + k.
unfold glb; intros.
apply Oeq_trans with ([1-] lub (UEsp <_> ([1-]k) @ (UInv @ f))); auto.
apply Uinv_eq_compat; apply lub_eq_compat; apply fmon_eq_intro; simpl; auto.
apply Oeq_trans with ([1-] (lub (UInv @ f) & [1-] k)).
apply Uinv_eq_compat; apply (lub_eq_esp_right (UInv @ f) ([1-]k)).
rewrite Uinv_esp_plus; auto.
Save.
Hint Resolve glb_eq_plus_cte_right.

Lemma glb_eq_plus_cte_left:
  forall (f : natO -m> UI) (k : U), glb (Imon (UPlus k) @ f) == k + glb f.
intros; apply Oeq_trans with (glb f + k); auto.
apply Oeq_trans with (glb (Imon (UPlus <_> k) @ f)); auto.
apply glb_eq_compat; apply fmon_eq_intro; simpl; auto.
Save.
Hint Resolve glb_eq_plus_cte_left.

Lemma glb_eq_mult:
  forall (k : U) (f : natO -m> UI), glb (Imon (UMult k) @ f) == k * glb f.
unfold glb; intros; auto.
apply Oeq_trans with ([1-] lub (UPlus <_> ([1-]k) @ (UMult k @ (UInv @ f)))).
apply Uinv_eq_compat; apply lub_eq_compat; apply fmon_eq_intro; simpl; auto.
rewrite lub_eq_plus_cte_right.
rewrite (lub_eq_mult k).
apply Uinv_eq_perm_left; auto.
rewrite Udistr_inv_left; auto.
Save.

Lemma Imon2_plus_continuous
       : continuous2 (D1:=Uopp) (D2:=Uopp) (D3:=Uopp) (Imon2 UPlus).
apply continuous_continuous2; red; intros.
change (glb (Imon (UPlus k) @ h) <= k + glb h).
rewrite glb_eq_plus_cte_left; trivial.
intro y.
change (glb (Imon (UPlus <_> y) @ h) <= glb h + y).
rewrite glb_eq_plus_cte_right; trivial.
Save.

Hint Resolve  Imon2_plus_continuous.

Lemma Uinv_continuous : continuous (D1:=Uopp) UInv.
red; intros.
rewrite UInv_simpl; simpl lub at 1.
unfold glb.
rewrite Uinv_inv; auto.
Save.

Definition UInvopp : U -m> Uopp.
exists (Uinv : U -> Uopp).
red; simpl; intros; auto.
Defined.

Lemma UInvopp_simpl : forall x, UInvopp x = [1-]x.
trivial.
Save.

Lemma Uinvopp_continuous : continuous UInvopp.
red; intros.
rewrite UInvopp_simpl; simpl lub at 2.
unfold glb; auto.
Save.

Hint Resolve Uinv_continuous Uinvopp_continuous.

Definition UMinus : U -m> Uopp -m> U :=
    fcomp2 U Uopp Uopp U UInv (Imon2 UPlus @ UInvopp).

Lemma UMinus_simpl : forall x y, UMinus x y = x - y.
trivial.
Save.

Lemma Uminus_continuous2 : continuous2 UMinus.
unfold UMinus.
apply continuous2_comp2; auto.
apply continuous2_comp with (D1:=U) (D2:=Uopp) (D3:=Uopp)(D4:=Uopp); auto.
Save.
Hint Resolve Uminus_continuous2.
(*
min_lub_le_incr:
  forall f g : nat -> U,
  incr f ->
  incr g -> min (lub f) (lub g) <= lub (fun n : nat => min (f n) (g n))
min_lub_le_incr_aux:
  forall f g : nat -> U,
  incr f ->
  (forall n : nat, exc (fun m : nat => (n <= m)%nat /\ f n <= g m)) ->
  min (lub f) (lub g) <= lub (fun n : nat => min (f n) (g n))
min_lub_le:
  forall f g : nat -> U,
  lub (fun n : nat => min (f n) (g n)) <= min (lub f) (lub g)
*)

Lemma glb_le_esp :  forall f g :natO-m>UI, (glb f) & (glb g) <= glb ((Imon2 UEsp @2 f) g).
intros; apply le_glb; auto.
Save.
Hint Resolve glb_le_esp.

Lemma Uesp_min : forall a1 a2 b1 b2, min a1 b1 & min a2 b2 <= min (a1 & a2) (b1 & b2).
intros; apply min_le.
apply Uesp_le_compat; auto.
apply Uesp_le_compat; auto.
Save.

(** Defining lubs of arbitrary sequences *)

Fixpoint seq_max (f:nat->U) (n:nat) : U := match n with
             O => f O | S p => max (seq_max f p) (f (S p)) end.

Lemma seq_max_incr : forall f n, seq_max f n <= seq_max f (S n).
induction n; simpl; intros; auto.
Save.

Lemma seq_max_le : forall f n, f n <= seq_max f n.
induction n; simpl; intros; auto.
Save.
Hint Resolve seq_max_le.

Definition sMax (f:nat->U) : natO -m> U := fnatO_intro (seq_max_incr f).

Lemma sMax_mult : forall k (f:nat->U),  sMax (fun n => k * f n) == UMult k @ sMax f.
intros; apply fmon_eq_intro; simpl; intros.
induction n; simpl; intros; auto.
rewrite IHn; auto.
Save.

Lemma sMax_plus_cte_right : forall k (f:nat->U),  sMax (fun n => f n + k) == UPlus <_> k @ sMax f.
intros; apply fmon_eq_intro; simpl; intros.
induction n; simpl; intros; auto.
rewrite IHn; auto.
Save.

Definition Ulub  (f:nat-o>U)  := lub (sMax f).

Lemma le_Ulub : forall f n, f n <= Ulub f.
unfold Ulub; intros; apply Ole_trans with (seq_max f n); auto.
apply le_lub with (f:=sMax f) (n:=n).
Save.

Lemma Ulub_le : forall f x, (forall n, f n <= x) -> Ulub f <= x.
unfold Ulub; intros; apply lub_le.
induction n; simpl; intros; auto.
apply max_le; auto.
Save.

Hint Resolve le_Ulub Ulub_le.

Lemma Ulub_le_compat : forall f g : nat-o>U, f <=g -> Ulub f <= Ulub g.
intros; apply Ulub_le; intros; auto.
apply Ole_trans with (g n); auto.
Save.
Hint Resolve Ulub_le_compat.

Add Morphism Ulub with signature Oeq (O:=nat-o>U) ==> Oeq (O:=U) as Ulub_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve Ulub_eq_compat.

Lemma Ulub_eq_mult : forall k (f:nat->U), Ulub (fun n => k * f n)== k * Ulub f.
intros; unfold Ulub.
rewrite sMax_mult; auto.
Save.

Lemma Ulub_eq_plus_cte_right : forall (f:nat->U) k, Ulub (fun n => f n + k)== Ulub f + k.
intros; unfold Ulub.
rewrite sMax_plus_cte_right; auto.
Save.

Hint Resolve Ulub_eq_mult Ulub_eq_plus_cte_right.

Lemma Ulub_eq_esp_right :
  forall (f : nat -> U) (k : U), Ulub (fun n => f n & k) == Ulub f & k.
intros; apply Ole_antisym.
apply Ulub_le; auto.
apply Uplus_inv_le_esp.
apply Ole_trans with (Ulub (fun n => (f n & k) + ([1-]k))); auto.
Save.
Hint Resolve lub_eq_esp_right.

Lemma Ulub_le_plus : forall f g, Ulub (fun n => f n + g n) <= Ulub f + Ulub g.
intros; apply Ulub_le; auto.
Save.
Hint Resolve Ulub_le_plus.

Definition Uglb (f:nat-o>U) :U := [1-]Ulub (fun n => [1-](f n)).

Lemma Uglb_le:   forall (f : nat -> U) (n : nat), Uglb f <= f n.
unfold Uglb; intros; apply Uinv_le_perm_left.
apply le_Ulub with (f:=fun n => [1-]f n) (n:=n); auto.
Save.

Lemma le_Uglb: forall (f : nat -> U) (x:U), (forall n : nat, x <= f n)-> x <= Uglb f.
unfold Uglb; intros; apply Uinv_le_perm_right.
apply Ulub_le with (f:=fun n => [1-]f n); auto.
Save.
Hint Resolve Uglb_le le_Uglb.

Lemma Uglb_le_compat : forall f g : nat-o>U, f <=g -> Uglb f <= Uglb g.
intros; apply le_Uglb; intros; auto.
apply Ole_trans with (f n); auto.
Save.
Hint Resolve Uglb_le_compat.

Add Morphism Uglb with signature Oeq (O:=nat-o>U) ==> Oeq (O:=U) as Uglb_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve Uglb_eq_compat.

Lemma Uglb_eq_plus_cte_right:
  forall (f : nat -> U) (k : U), Uglb (fun n => f n + k) == Uglb f + k.
unfold Uglb; intros.
apply Oeq_trans with ([1-] Ulub (fun n => ([1-]f n) & [1-]k)); auto.
apply Oeq_trans with ([1-] (Ulub (fun n => [1-]f n) & [1-] k)).
apply Uinv_eq_compat; apply (Ulub_eq_esp_right (fun n => [1-]f n) ([1-]k)).
apply Oeq_trans with ([1-]Ulub (fun n => [1-]f n) + [1-][1-]k); auto.
Save.
Hint Resolve Uglb_eq_plus_cte_right.

Lemma Uglb_eq_mult:
  forall (k : U) (f : nat -> U), Uglb (fun n => k * f n) == k * Uglb f.
unfold Uglb; intros; auto.
apply Oeq_trans with ([1-] Ulub (fun n => (k * [1-]f n) + [1-]k)).
apply Uinv_eq_compat; apply Ulub_eq_compat; apply ford_eq_intro; simpl; auto.
apply Oeq_trans with ([1-](Ulub (fun n => k * [1-]f n) + [1-]k)); auto.
apply Oeq_trans with ([1-](k * Ulub (fun n => [1-]f n) + [1-]k)); auto.
apply Uinv_eq_perm_left; auto.
apply Oeq_trans with (k* [1-][1-](Ulub (fun n => [1-]f n)) + [1-]k); auto.
Save.
Hint Resolve Uglb_eq_mult Uglb_eq_plus_cte_right.

Lemma Uglb_le_plus : forall f g, Uglb f + Uglb g <= Uglb (fun n => f n + g n).
intros; apply le_Uglb; auto.
Save.
Hint Resolve Uglb_le_plus.

Lemma Ulub_lub : forall f:natO-m>U, Ulub f == lub f.
intros; unfold Ulub; apply lub_eq_compat; apply fmon_eq_intro; simpl; intros; auto.
induction n; simpl; intros; auto.
rewrite IHn; apply Ole_antisym; auto.
Save.
Hint Resolve Ulub_lub.

Lemma Uglb_glb : forall f:natO-m>UI, Uglb f == glb f.
intros; unfold Uglb,glb.
apply Uinv_eq_compat; apply (Ulub_lub (UInv @ f)).
Save.
Hint Resolve Uglb_glb.

Lemma lub_le_plus : forall (f g : natO-m>U), lub ((UPlus @2 f) g) <= lub f + lub g.
intros; apply lub_le; auto.
Save.
Hint Resolve lub_le_plus.


Lemma glb_le_plus : forall (f g:natO-m>UI) , glb f + glb g <= glb ((Imon2 UPlus @2 f) g).
intros; apply le_glb; auto.
Save.
Hint Resolve glb_le_plus.

(*
Lemma glb_le_plus : forall f g, glb f + glb g <= glb (fun n => f n + g n).
apply le_glb; auto.
Save.
Hint Resolve glb_le_plus.
*)

Lemma lub_eq_plus : forall f g : natO-m>U, lub ((UPlus @2 f) g) == lub f + lub g.
intros; apply Oeq_sym.
apply lub_comp2_eq with (D1:=U) (D2:=U) (D3:=U) (F:=UPlus) (f:=f) (g:=g); auto.
Save.
Hint Resolve lub_eq_plus.

Lemma glb_mon : forall f : natO-m>U, Uglb f == f O.
intros; apply Ole_antisym; auto.
apply le_Uglb; auto with arith.
Save.

Lemma lub_inv : forall (f g : natO-m>U), (forall n, f n <= [1-] g n) -> lub f <= [1-] (lub g).
intros; apply Uinv_le_perm_right.
apply lub_le; intros.
apply Uinv_le_perm_right.
rewrite (lub_lift_left f n).
apply lub_le; simpl; intros.
apply Ole_trans with ([1-] (g (n+n0)%nat)); auto with arith.
Save.


Lemma glb_lift_left : forall (f:natO-m>UI) n,  glb f == glb (mseq_lift_left f n).
intros; apply Ueq_opp.
exact (lub_lift_left (D:=Uopp) f n).
Save.
Hint Resolve glb_lift_left.

Lemma Ulub_mon : forall f : natO-m>UI, Ulub f == f O.
intros; apply Ole_antisym; auto.
apply Ulub_le; intros; auto with arith.
Save.

Lemma lub_glb_le : forall (f:natO-m>U) (g:natO-m>UI), (forall n, f n <= g n) -> lub f <= glb g.
intros; apply lub_le; intros.
rewrite (glb_lift_left g n); auto.
apply le_glb; simpl; intros.
apply Ole_trans with (f (n+n0))%nat; auto with arith.
Save.

Lemma lub_lub_inv_le : forall f g :natO-m>U, (forall n, f n <= [1-]g n) -> lub f <= [1-] lub g.
intros; apply Ole_trans with (glb (UInvopp @ g)).
apply lub_glb_le; auto.
unfold glb; apply Uinv_le_compat.
apply lub_le_compat; auto.
Save.

Lemma Uplus_opp_continuous_right :
     forall k, continuous  (D1:=Uopp) (D2:=Uopp) (Imon (UPlus k)).
red; intros.
change (glb (Imon (UPlus k) @ h) <= k + glb h).
rewrite glb_eq_plus_cte_left; trivial.
Save.

Lemma Uplus_opp_continuous_left :
     continuous  (D1:=Uopp) (D2:=Uopp-M->Uopp) (Imon2 UPlus).
red; intros.
intro k; simpl.
change (glb (Imon (UPlus <_> k) @ h) <= glb h +k).
rewrite glb_eq_plus_cte_right; trivial.
Save.

Hint Resolve Uplus_opp_continuous_right Uplus_opp_continuous_left.

Lemma glb_eq_plus : forall (f g : natO-m>UI), glb ((Imon2 UPlus @2 f)  g) == glb f + glb g.
intros; apply Ueq_opp; apply Oeq_sym.
apply (lub_comp2_eq (D1:=Uopp) (D2:=Uopp) (D3:=Uopp) (F:=Imon2 UPlus)) with (f:=f) (g:=g); intros.
apply continuous_eq_compat with (Imon (UPlus k)); auto.
apply continuous_eq_compat with (Imon2 UPlus); auto.
Save.
Hint Resolve glb_eq_plus.

Definition Sigma : (natO-O->U)-m>natO-M->U.
exists (fun (f:natO-O->U) => sigma f); red; intros.
intro n; apply sigma_le_compat; auto.
Defined.

Lemma Sigma_simpl : forall f, Sigma f = sigma f.
trivial.
Save.

Lemma sigma_continuous1 : continuous Sigma.
red; intros; intro n.
induction n; auto.
change (tord natO) in n.
apply Ole_trans with (sigma (lub h) (S n)); auto.
rewrite sigma_S.
apply Ole_trans with (lub h n + lub (Sigma @ h) n); auto.
simpl lub.
repeat (rewrite lub_fun_eq).
apply Ole_trans with (lub ((UPlus @2 (h <o> n)) ((Sigma @ h) <_> n))); auto.
Save.


Lemma sigma_lub1 : forall (f : natO -m> (natO -O-> U)) n, sigma (lub f) n == lub ((Sigma <_> n) @ f).
intros; assert (Sigma (lub f) == lub (Sigma @ f)).
apply lub_comp_eq with (f:= Sigma); apply sigma_continuous1.
apply Oeq_trans with (lub (Sigma @ f) n); auto.
Save.

(* A more general type to deal with arbitrary representation of
   spaces of measurable functions
(** ** Type of spaces equiped with measurable functions *)
Record MFS : Type := mk_MF
   {MFA:Type; MF:>Type; fapp: MF -> MFA -> U;
     fplus : MF -> MF -> MF;
     fmult : U -> MF -> MF;
     finv : MF -> MF;
     fzero : MF;
     flub : (nat -> MF) -> MF;
     fplus_eq : forall (f g : MF) (x : MFA),
                             fapp (fplus f g) x == fapp f x + fapp g x;
     fmult_eq : forall (k:U) (f : MF) (x : MFA),
                             fapp (fmult k f) x == k * fapp f x;
     fzero_eq : forall (x : MFA), fapp fzero x == 0;
     finv_eq : forall (f : MF) (x : MFA), fapp (finv f) x == [1-]fapp f x;
     flub_eq : forall (f:nat -> MF) (x:MFA),
                            fapp (flub f) x == lub (fun n => fapp (f n) x)
}.
*)

(* Definition MF (A:Type) := A -> U. *)

Definition MF (A:Type) : cpo := A -O-> U.
Definition MF_opp (A:Type) : cpo := A -O-> Uopp.

Definition fplus (A:Type) (f g : MF A) : MF A :=
               fun x => f x + g x.

Definition fmult (A:Type) (k:U) (f : MF A) : MF A :=
               fun x => k *  f x.

Definition finv (A:Type) (f : MF A) : MF A :=
               fun x => [1-]  f x.

Definition fzero (A:Type) : MF A :=
               fun x => 0.

Definition fdiv  (A:Type) (k:U) (f : MF A) : MF A :=
               fun x => (f x) / k.

Definition flub (A:Type) (f : natO -m> MF A) : MF A := lub f.

Lemma  fplus_eq : forall (A:Type)(f g : MF A) (x : A),
                             fplus f g x = f x + g x.
trivial.
Save.

Lemma  fmult_eq : forall (A:Type)(k:U) (f : MF A) (x : A),
                             fmult k f x = k * f x.
trivial.
Save.

Lemma  fdiv_eq : forall (A:Type)(k:U) (f : MF A) (x : A),
                             fdiv k f x = f x / k.
trivial.
Save.

Implicit Arguments fzero [].

Lemma fzero_eq : forall (A:Type)(x : A), fzero A x = 0.
trivial.
Save.

Lemma finv_eq : forall (A:Type)(f : MF A) (x : A), finv f x = [1-]f x.
trivial.
Save.

Lemma flub_eq : forall (A:Type)(f:natO -m> MF A) (x:A),
                           (flub f) x = lub (f <o> x).
trivial.
Save.


Hint Resolve fplus_eq fmult_eq fzero_eq finv_eq flub_eq.


Definition fone (A:Type) : MF A := fun x => 1.
Implicit Arguments fone [].

Lemma fone_eq : forall (A:Type) (x:A), fone A x = 1.
trivial.
Save.

Definition fcte (A:Type) (k:U): MF A := fun x => k.
Implicit Arguments fcte [].

Lemma fcte_eq : forall (A:Type) (k:U) (x:A), fcte A k x = k.
trivial.
Save.

Definition fminus (A:Type) (f g :MF A) : MF A := fun x => f x - g x.

Lemma fminus_eq : forall (A:Type) (f g: MF A) (x:A), fminus f g x = f x - g x.
trivial.
Save.


Definition fesp (A:Type) (f g :MF A) : MF A := fun x => f x & g x.

Lemma fesp_eq : forall (A:Type) (f g: MF A) (x:A), fesp f g x = f x & g x.
trivial.
Save.

Definition fconj (A:Type)(f g:MF A) : MF A := fun x => f x * g x.

Lemma fconj_eq : forall (A:Type) (f g: MF A) (x:A), fconj f g x = f x * g x.
trivial.
Save.

Definition fglb (A:Type) (f : natO -m> MF_opp A) : MF A := fun x => glb (f <o> x).

Lemma fglb_eq : forall ( A:Type) (f : natO -m> MF_opp A)(x:A), fglb f x = glb (f <o> x).
trivial.
Save.

(** *** Elementary properties *)

Lemma fle_fplus_left : forall (A:Type) (f g : MF A), f <= fplus f g.
intros m f g x; rewrite fplus_eq; auto.
Save.

Lemma fle_fplus_right : forall (A:Type) (f g : MF A), g <= fplus f g.
intros m f g x; rewrite fplus_eq; auto.
Save.

Lemma fle_fmult : forall (A:Type) (k:U)(f : MF A), fmult k f <= f.
intros m k f x; rewrite fmult_eq; auto.
Save.

Lemma fle_zero : forall (A:Type) (f : MF A), fzero A <= f.
intros m f x; rewrite fzero_eq; auto.
Save.

Lemma fle_one : forall (A:Type) (f : MF A), f <= fone A.
intros m f x; rewrite fone_eq; auto.
Save.

Lemma feq_finv_finv : forall (A:Type) (f : MF A), finv (finv f) == f.
intros m f; simpl; apply ford_eq_intro; intro x; rewrite finv_eq; simpl; auto.
Save.

Lemma fle_fesp_left : forall (A:Type) (f g : MF A), fesp f g <= f.
intros m f g x; rewrite fesp_eq; auto.
Save.

Lemma fle_fesp_right : forall (A:Type) (f g : MF A), fesp f g <= g.
intros m f g x; rewrite fesp_eq; auto.
Save.

Lemma fle_fconj_left : forall (A:Type) (f g : MF A), fconj f g <= f.
intros m f g x; rewrite fconj_eq; auto.
Save.

Lemma fle_fconj_right : forall (A:Type) (f g : MF A), fconj f g <= g.
intros m f g x; rewrite fconj_eq; auto.
Save.

Lemma fconj_decomp : forall A (f g : MF A), 
             f == fplus (fconj f g) (fconj f (finv g)).
intros; simpl; apply ford_eq_intro; intros; apply Umult_decomp.
Save.
Hint Resolve fconj_decomp.

(** *** Defining morphisms *)

Lemma fplus_eq_compat : forall A  (f1 f2 g1 g2:MF A),
          f1==f2 -> g1==g2 -> fplus f1 g1 == fplus f2 g2.
intros; simpl; apply ford_eq_intro; intro x.
repeat (rewrite fplus_eq); firstorder.
Save.

Add Parametric Morphism (A:Type) : (fplus (A:=A))
  with signature Oeq (O:=MF A) ==> Oeq (O:=MF A) ==> Oeq (O:=MF A)
as fplus_feq_compat_morph.
intros; exact (fplus_eq_compat H H0); auto.
Save.

Lemma fplus_le_compat : forall A  (f1 f2 g1 g2:MF A),
          f1<=f2 -> g1<=g2 -> fplus f1 g1 <= fplus f2 g2.
intros; intro x.
repeat rewrite fplus_eq;firstorder.
Save.

Add Parametric Morphism (A:Type) : (fplus (A:=A))
with signature Ole (o:=MF A) ++> Ole (o:=MF A) ++> Ole (o:=MF A) as fplus_fle_compat_morph.
intros.
exact (fplus_le_compat H H0); auto.
Save.

Lemma finv_eq_compat : forall A (f g:MF A), f==g -> finv f == finv g.
intros; simpl; apply ford_eq_intro; intro x.
repeat (rewrite finv_eq); firstorder.
Save.

Add Parametric Morphism (A:Type) : (finv (A:=A))
with signature Oeq (O:=MF A) ==> Oeq (O:=MF A) as finv_feq_compat_morph.
intros; exact (finv_eq_compat H).
Save.

Lemma finv_le_compat : forall A (f g:MF A), f <= g -> finv g <= finv f.
intros; intro x.
repeat (rewrite finv_eq); firstorder.
Save.

Add Parametric Morphism (A:Type) : (finv (A:=A))
  with signature Ole (o:=MF A) --> Ole (o:=MF A) as finv_fle_compat_morph.
intros; exact (finv_le_compat H).
Save.


Lemma fmult_eq_compat : forall A  k1 k2 (f1 f2:MF A),
          k1==k2 -> f1==f2 -> fmult k1 f1 == fmult k2 f2.
intros; simpl; apply ford_eq_intro; intro x.
repeat (rewrite fmult_eq); firstorder.
Save.

Add Parametric Morphism (A:Type) : (fmult (A:=A))
with signature Oeq (O:=U) ==> Oeq (O:=MF A) ==> Oeq (O:=MF A)
as fmult_feq_compat_morph.
intros; exact (fmult_eq_compat H H0); auto.
Save.

Lemma fmult_le_compat : forall A  k1 k2 (f1 f2:MF A),
          k1 <= k2 -> f1<=f2 -> fmult k1 f1 <= fmult k2 f2.
intros; intro x.
repeat rewrite fmult_eq;firstorder.
Save.

Add Parametric Morphism (A:Type) : (fmult (A:=A))
with signature Ole (o:=U) ++> Ole (o:=MF A) ++> Ole (o:=MF A) as fmult_fle_compat_morph.
intros.
exact (fmult_le_compat x y H H0); auto.
Save.


Lemma fminus_eq_compat : forall A  (f1 f2 g1 g2:MF A),
          f1==f2 -> g1==g2 -> fminus f1 g1 == fminus f2 g2.
intros; simpl; apply ford_eq_intro; intro x.
repeat (rewrite fminus_eq); firstorder.
Save.

Add Parametric Morphism (A:Type) : (fminus (A:=A))
with signature Oeq (O:=MF A) ==> Oeq (O:=MF A) ==> Oeq (O:=MF A)
as fminus_feq_compat_morph.
intros; exact (fminus_eq_compat H H0); auto.
Save.

Lemma fminus_le_compat : forall A  (f1 f2 g1 g2:MF A),
          f1<=f2 -> g2<=g1 -> fminus f1 g1 <= fminus f2 g2.
intros; intro x.
repeat rewrite fminus_eq;firstorder.
Save.

Add Parametric Morphism (A:Type) : (fminus (A:=A))
with signature Ole (o:=MF A) ++> Ole (o:=MF A) --> Ole (o:=MF A) as fminus_fle_compat_morph.
intros; exact (fminus_le_compat H H0); auto.
Save.

Lemma fesp_eq_compat : forall A  (f1 f2 g1 g2:MF A),
          f1==f2 -> g1==g2 -> fesp f1 g1 == fesp f2 g2.
intros; simpl; apply ford_eq_intro; intro x.
repeat (rewrite fesp_eq); firstorder.
Save.

Add Parametric Morphism (A:Type) : (fesp (A:=A))
with signature Oeq (O:=MF A) ==> Oeq (O:=MF A) ==> Oeq (O:=MF A) as fesp_feq_compat_morph.
intros; exact (fesp_eq_compat H H0); auto.
Save.

Lemma fesp_le_compat : forall A  (f1 f2 g1 g2:MF A),
          f1<=f2 -> g1<=g2 -> fesp f1 g1 <= fesp f2 g2.
intros; intro x.
repeat rewrite fesp_eq;firstorder.
Save.

Add Parametric Morphism (A:Type) : (fesp (A:=A))
with signature Ole (o:=MF A) ++> Ole (o:=MF A) ++> Ole (o:=MF A) as fesp_fle_compat_morph.
intros; exact (fesp_le_compat H H0); auto.
Save.

Lemma fconj_eq_compat : forall A  (f1 f2 g1 g2:MF A), 
          f1==f2 -> g1==g2 -> fconj f1 g1 == fconj f2 g2.
intros; simpl; apply ford_eq_intro; intro x.
repeat (rewrite fconj_eq); firstorder.
Save.

Add Parametric Morphism (A:Type) : (fconj (A:=A))
  with signature Oeq (O:=MF A) ==> Oeq (O:=MF A) ==> Oeq (O:=MF A) 
as fconj_feq_compat_morph.
intros; exact (fconj_eq_compat H H0); auto.
Save.

Lemma fconj_le_compat : forall A  (f1 f2 g1 g2:MF A), 
          f1<=f2 -> g1<=g2 -> fconj f1 g1 <= fconj f2 g2.
intros; intro x.
repeat rewrite fconj_eq;firstorder.
Save.

Add Parametric Morphism (A:Type) : (fconj (A:=A))
with signature Ole (o:=MF A) ++> Ole (o:=MF A) ++> Ole (o:=MF A) 
as fconj_fle_compat_morph.
intros.
exact (fconj_le_compat H H0); auto.
Save.

Hint Immediate fplus_le_compat fplus_eq_compat fesp_le_compat fesp_eq_compat
fmult_le_compat fmult_eq_compat fminus_le_compat fminus_eq_compat 
fconj_eq_compat.

Hint Resolve fle_fplus_left  fle_fplus_right fle_zero  fle_one feq_finv_finv finv_le_compat
fle_fmult fle_fesp_left fle_fesp_right fle_fconj_left fle_fconj_right.

Hint Resolve finv_eq_compat.

Definition Fconj A : MF A -m> MF A -M-> MF A
               := le_compat2_mon (fconj_le_compat (A:=A)).

Lemma Fconj_simpl : forall A f g, Fconj A  f g = fconj f g.
trivial.
Save.

Lemma fconj_sym : forall A (f g : MF A), fconj f g == fconj g f.
intros; simpl; apply ford_eq_intro; intro x; unfold fconj; auto.
Save.

Lemma fconj_continuous2 : forall A, continuous2 (Fconj A).
intros; apply continuous2_sym.
intros; repeat rewrite Fconj_simpl.
apply fconj_sym.
red; intros.
rewrite Fconj_simpl.
intro x.
unfold fconj.
unfold MF; repeat rewrite fcpo_lub_simpl.
rewrite (Umult_right_continuous (k x) (h <o> x)).
apply lub_le_compat; simpl; auto.
Save.

Definition Fmult A : U -m> MF A -M-> MF A
               := le_compat2_mon (fmult_le_compat (A:=A)).

Lemma Fmult_simpl : forall A k f, Fmult A  k f = fmult k f.
trivial.
Save.

Lemma fmult_continuous2 : forall A, continuous2 (Fmult A).
red; intros.
rewrite Fmult_simpl.
intro x; unfold fmult.
unfold MF; repeat rewrite fcpo_lub_simpl.
rewrite (Umult_continuous2 f (g <o> x)).
apply lub_le_compat; intro y; simpl; auto.
Save.

(** ** Fixpoints of functions of type $A\ra\U$ *)
Section FixDef.
Variable A :Type.

Variable F : MF A -m> MF A.

Definition mufix : MF A := fixp F.

Definition G : MF_opp A -m> MF_opp A := Imon F.

Definition nufix : MF A := fixp G.

Lemma mufix_inv : forall f : MF A, F f <= f -> mufix  <= f.
unfold mufix; intros; apply fixp_inv; auto.
Save.
Hint Resolve mufix_inv.

Lemma nufix_inv : forall f :MF A, f  <= F f -> f <= nufix.
unfold nufix; intros.
change (fixp (D:=MF_opp A) G <= f); apply fixp_inv with (D:=MF_opp A); auto.
Save.
Hint Resolve nufix_inv.

Lemma mufix_le : mufix  <= F mufix.
unfold mufix; auto.
Save.
Hint Resolve mufix_le.

Lemma nufix_sup : F nufix <= nufix.
unfold nufix.
change (fixp (D:=MF_opp A) G <= G (fixp (D:=MF_opp A) G)); auto.
Save.
Hint Resolve nufix_sup.

(*
Definition Fcontlub := forall (fn : nat -> A -> U), increase fn ->
           fle (F (lub fn)) (lub (fun n => F (fn n))).
Definition Fcontglb := forall (fn : nat -> A -> U), decrease fn ->
           fle (fglb (fun n => F (fn n))) (F (fglb fn)).

Lemma Fcontlub_fle : Fcontlub -> forall (fn : nat -> A -> U), increase fn ->
           fle (F (flub fn)) (flub (fun n => F (fn n))).
auto.
Save.

Lemma Fcontglb_fle : Fcontglb -> forall (fn : nat -> A -> U), decrease fn ->
           fle (fglb (fun n => F (fn n))) (F (fglb fn)).
auto.
Save.


Hypothesis muFcont : forall (fn : nat -> A -> U), increase fn ->
           fle (F (flub fn)) (flub (fun n => F (fn n))).

Hypothesis nuFcont : forall (fn : nat -> A -> U), decrease fn ->
           fle (fglb (fun n => F (fn n))) (F (fglb fn)).

Implicit Arguments muFcont [].
Implicit Arguments nuFcont [].

Lemma incr_muiter : increase muiter.
red; intros; induction n; red; simpl; intros; auto.
Save.

Lemma decr_nuiter : decrease nuiter.
red; intros; induction n; red; simpl; intros; auto.
Save.

Hint Resolve incr_muiter decr_nuiter.
*)

Lemma mufix_eq : continuous F -> mufix  == F mufix.
intros; unfold mufix; auto.
Save.
Hint Resolve mufix_eq.

Lemma nufix_eq : continuous G -> nufix  == F nufix.
intros; unfold nufix.
assert (fixp G == G (fixp G)); auto.
Save.
Hint Resolve nufix_eq.

End FixDef.
Hint Resolve mufix_le mufix_eq nufix_sup nufix_eq.

Definition Fcte (A:Type) (f:MF A) : MF A -m> MF A := fmon_cte (MF A) (O2:=MF A) f.

Lemma mufix_cte : forall (A:Type) (f:MF A), mufix (Fcte f) == f.
intros A f; exact (fixp_cte (D:=MF A) f).
Save.

Lemma nufix_cte : forall (A:Type) (f:MF A), nufix (Fcte f) == f.
intros A f; apply Oeq_sym; exact (fixp_cte (D:=MF_opp A) f).
Save.

Hint Resolve mufix_cte nufix_cte.

(** ** Properties of barycenter of two points *)
Section Barycenter.
Variables a b : U.
Hypothesis sum_le_one : a <= [1-] b.

Lemma Uinv_bary :
   forall x y : U, [1-] (a * x + b * y) == a * [1-] x + b * [1-] y + [1-] (a + b).
intros.
apply Uplus_eq_simpl_left with (a * x); auto.
apply Uinv_le_perm_right.
setoid_rewrite (Udistr_inv_left a x).
repeat norm_assoc_right.
apply Uplus_le_compat_right.
apply Ole_trans with (b + [1-] (a + b)); auto.
apply Ole_trans with ([1-] (a + b) + b); auto.
apply Oeq_trans with ([1-] (b * y)).
apply Oeq_trans with
   ([1-] (a * x + b * y) + a * x); auto.
setoid_rewrite (Udistr_inv_left b y); auto.
apply Oeq_trans with
 ((a * x + a * [1-] x) + b * [1-] y + [1-] (a + b)).
assert (x <= ([1-] ([1-] x))); auto.
rewrite <- (Udistr_plus_left a _ _ H); auto.
rewrite (Uinv_opp_right x).
rewrite (Umult_one_right a).
apply Oeq_trans with (b * [1-] y + ([1-] (a + b) + a)).
assert (b <= [1-] a); auto.
rewrite (Uinv_plus_left _ _ H0); auto.
rewrite (Uplus_sym a (b * [1-] y)); auto.
apply Oeq_trans with
(b * [1-] y + (a + [1-] (a + b))); auto.
apply Oeq_trans with
(((a * x + a * [1-] x) + (b * [1-] y + [1-] (a + b)))); auto.
apply Oeq_trans with
(((a * x + (a * [1-] x + (b * [1-] y + [1-] (a + b)))))); auto.
Save.

Lemma Uinv_bary_le :
   forall x y : U,   a * [1-] x + b * [1-] y <= [1-] (a * x + b * y).
intros; rewrite Uinv_bary; auto.
Save.

End Barycenter.
Hint Resolve Uinv_bary_le.

Lemma Uinv_half_bary :
   forall x y : U, [1-] ([1/2] * x + [1/2] * y) == [1/2] * [1-] x + [1/2] * [1-] y.
intros; rewrite Uinv_bary; auto.
rewrite Unth_one_plus; rewrite Uinv_one; auto.
Save.
Hint Resolve Uinv_half_bary.

(** ** Properties of generalized sums [sigma] *)
Lemma sigma_plus : forall (f g : nat -> U) (n:nat),
   sigma (fun k => (f k) + (g k)) n == sigma f n + sigma g n.
intros; induction n; simpl; auto.
repeat rewrite sigma_S; setoid_rewrite IHn.
repeat norm_assoc_right; apply Uplus_eq_compat_right.
setoid_rewrite (Uplus_sym (g n) ((sigma f n) + (sigma g n))).
repeat norm_assoc_right; apply Uplus_eq_compat_right; auto.
Save.


Definition retract (f : nat -> U) (n : nat) := forall k, (k < n)%nat -> f k <= [1-] (sigma f k).

Lemma retract0 : forall (f : nat -> U), retract f 0.
red; intros; absurd (k < O)%nat; auto with arith.
Save.

Lemma retract_pred : forall (f : nat -> U) (n : nat), retract f (S n) -> retract f n.
unfold retract; auto with arith.
Save.

Lemma retractS: forall (f : nat -> U) (n : nat), retract f (S n) -> f n <= [1-] (sigma f n).
unfold retract; auto with arith.
Save.

Hint Immediate retract_pred retractS.

Lemma retractS_inv :
     forall (f : nat -> U) (n : nat), retract f (S n) -> sigma f n <= [1-] f n.
intros; apply Uinv_le_perm_right; auto.
Save.
Hint Immediate retractS_inv.

Lemma retractS_intro: forall (f : nat -> U) (n : nat),
   retract f n -> f n <= [1-] (sigma f n) -> retract f (S n).
unfold retract; intros.
assert ((k<n)%nat \/ k=n); try omega; intuition; subst; auto.
Save.

Hint Resolve retract0 retractS_intro.

Lemma retract_lt : forall (f : nat -> U) (n : nat),  sigma f n < 1 -> retract f n.
induction n; auto.
rewrite sigma_S.
intros;assert ((sigma f n)<1).
apply Ule_lt_trans with (f n + sigma f n); auto.
assert (f n <= [1-](sigma f n)); auto.
apply Uplus_lt_Uinv; auto.
Save.

Lemma retract_unif :
    forall (f : nat -> U) (n : nat),
             (forall k, (k<=n)%nat -> f k <= [1/]1+n) -> retract f (S n).
red; intros.
apply Ole_trans with ([1/]1+n); auto with arith.
apply Uinv_le_perm_right.
apply Ole_trans with (sigma (fun k => [1/]1+n) n); auto.
apply Ole_trans with (sigma f n); auto with arith.
apply Uinv_le_perm_right; auto.
Save.

Hint Resolve retract_unif.

Lemma sigma_mult :
  forall (f : nat -> U) n c, retract f n -> sigma (fun k => c * (f k)) n == c * (sigma f n).
intros; induction n; simpl; auto.
repeat rewrite sigma_S.
assert (H1: retract f n); auto.
rewrite (IHn H1).
rewrite (Udistr_plus_left c _ _ (retractS H)); auto.
Save.
Hint Resolve sigma_mult.

Lemma sigma_prod_maj :  forall (f g : nat -> U) n,
   sigma (fun k => (f k) * (g k)) n <= sigma f n.
auto.
Save.

Hint Resolve sigma_prod_maj.

Lemma sigma_prod_le :  forall (f g : nat -> U) (c:U), (forall k, (f k) <= c)
   -> forall n, retract g n -> sigma (fun k => (f k) * (g k)) n <= c * (sigma g n).
induction n; simpl; intros; auto.
repeat rewrite sigma_S.
apply Ole_trans with ((f n) * (g n) + (c * sigma g n)); auto.
apply Ole_trans with ( c * (g n) + (c * sigma g n)); auto.
setoid_rewrite (Udistr_plus_left c _ _ (retractS H0)); auto.
Save.

Lemma sigma_prod_ge :  forall (f g : nat -> U) (c:U), (forall k, c <= (f k))
   -> forall n, (retract g n) -> c * (sigma g n) <= (sigma (fun k => (f k) * (g k)) n).
induction n; simpl; intros; auto.
repeat rewrite sigma_S.
rewrite (Udistr_plus_left c _ _ (retractS H0)); auto.
apply Ole_trans with (c * (g n) + sigma (fun k : nat => f k * g k) n); auto.
Save.

Hint Resolve sigma_prod_maj sigma_prod_le  sigma_prod_ge.

Lemma sigma_inv : forall (f g : nat -> U) (n:nat), (retract f n) ->
  [1-] (sigma (fun k => f k * g k) n) == (sigma (fun k => f k * [1-] (g k)) n) + [1-] (sigma f n).
intros; induction n; repeat rewrite sigma_S; auto.
apply Uplus_eq_simpl_right with ((f n) * (g n)).
rewrite
 (Uinv_inv (f n * g n + sigma (fun k : nat => f k * g k) n));auto.
apply Uinv_le_perm_right.
rewrite (Udistr_inv_left (f n) (g n)).
repeat norm_assoc_right; apply Uplus_le_compat_right.
apply Ole_trans with
  (sigma f n + [1-] (f n + sigma f n)); auto.
assert (sigma f n <= [1-] (f n)).
apply Uinv_le_perm_right; auto.
rewrite <- (Uinv_plus_right _ _ H0); auto.

assert (sigma (fun k : nat => f k * g k) n <= [1-] (f n * g n)).
apply Ole_trans with (sigma f n); auto.
apply Ole_trans with ([1-] (f n)); auto.
rewrite (Uinv_plus_left _ _ H0).
apply Oeq_trans with (1:=IHn (retract_pred H)).
rewrite (Uplus_sym (f n * [1-] (g n))
                          (sigma (fun k : nat => f k * [1-] (g k)) n)).
repeat norm_assoc_right; apply Uplus_eq_compat_right.
rewrite (Uplus_sym  ([1-] (f n + sigma f n)) (f n * g n)).
repeat norm_assoc_left.
assert ([1-] (g n) <= [1-] (g n)); auto.

rewrite <- (Udistr_plus_left (f n) _ _ H1).
rewrite (Uinv_opp_left (g n)).
rewrite (Umult_one_right (f n)); auto.
rewrite (Uplus_sym (f n) ([1-] (f n + sigma f n))).
apply Oeq_sym; apply Uinv_plus_left; auto.
Save.


(** ** Product by an integer *)

(** *** Definition of [Nmult n x] written [n */ x] *)
Fixpoint Nmult (n: nat) (x : U) {struct n} : U :=
   match n with O => 0 | (S O) => x | S p => x + (Nmult p x) end.

(** *** Condition for [n */ x] to be exact : $n = 0$ or $x\leq \frac{1}{n}$ *)
Definition Nmult_def (n: nat) (x : U) :=
   match n with O => True | S p => x <= [1/]1+p end.

Lemma Nmult_def_O : forall x, Nmult_def O x.
simpl; auto.
Save.
Hint Resolve Nmult_def_O.

Lemma Nmult_def_1 : forall x, Nmult_def (S O) x.
simpl; intro; rewrite Unth_zero; auto.
Save.
Hint Resolve Nmult_def_1.

Lemma Nmult_def_intro : forall n x , x <= [1/]1+n -> Nmult_def (S n) x.
destruct n; simpl; auto.
Save.
Hint Resolve Nmult_def_intro.

Lemma Nmult_def_Unth: forall n , Nmult_def (S n) ([1/]1+n).
auto.
Save.
Hint Resolve Nmult_def_Unth.

Lemma Nmult_def_pred : forall n x, Nmult_def (S n) x -> Nmult_def n x.
intros n x; case n; simpl; intros; auto.
apply Ole_trans with ([1/]1+(S n0)); auto.
Save.

Hint Immediate Nmult_def_pred.

Lemma Nmult_defS : forall n x, Nmult_def (S n) x -> x <= [1/]1+n.
destruct n; simpl; intros; auto.
Save.
Hint Immediate Nmult_defS.

Lemma Nmult_def_class : forall n p, class (Nmult_def n p).
unfold class; destruct n; intuition.
Save.
Hint Resolve Nmult_def_class.

Infix "*/" := Nmult (at level 60) : U_scope.

Add Morphism Nmult_def with signature eq (A:=nat) ==> Oeq (O:=U) ==> iff
as Nmult_def_eq_compat.
unfold Nmult_def; destruct y; intuition.
apply Ole_trans with x; auto.
apply Ole_trans with y0; auto.
Save.

Lemma Nmult_def_zero : forall n, Nmult_def n 0.
destruct n; auto.
Save.
Hint Resolve Nmult_def_zero.

(** *** Properties of [n */ x] *)

Lemma Nmult_0 : forall (x:U), O*/x = 0.
trivial.
Save.

Lemma Nmult_1 : forall (x:U), (S O)*/x = x.
trivial.
Save.

Lemma Nmult_zero : forall n, n */ 0 == 0.
induction n; simpl; auto.
destruct n; auto.
Save.

Lemma Nmult_SS : forall (n:nat) (x:U), S (S n) */x = x + (S n */ x).
destruct n; simpl; auto.
Save.

Lemma Nmult_2 : forall (x:U), 2*/x = x + x.
trivial.
Save.

Lemma Nmult_S : forall (n:nat) (x:U), S n */ x == x + (n*/x).
destruct n; simpl; auto.
Save.

Hint Resolve Nmult_1 Nmult_SS Nmult_2 Nmult_S.

Add Morphism Nmult with signature eq (A:=nat) ==> Oeq (O:=U) ==> Oeq (O:=U)
as Nmult_eq_compat_left.
intros n x1 x2 eq1; induction n; simpl; auto; intros.
destruct n; repeat rewrite Nmult_SS; trivial.
apply Uplus_eq_compat; auto.
Save.
Hint Resolve Nmult_eq_compat_left.


Lemma Nmult_eq_compat_right : forall (n m:nat) (x:U), (n = m)%nat -> n */ x == m */ x.
intros; subst n; trivial.
Save.
Hint Resolve Nmult_eq_compat_right.

Lemma Nmult_le_compat_right :  forall n x y, x <= y -> n */ x <= n */ y.
intros; induction n; auto.
rewrite (Nmult_S n x); rewrite (Nmult_S n y);auto.
Save.

Lemma Nmult_le_compat_left : forall n m x, (n <= m)%nat -> n */ x <= m */ x.
induction 1; trivial.
rewrite (Nmult_S m x); auto.
apply Ole_trans with (m */ x); auto.
Save.

Hint Resolve Nmult_eq_compat_right Nmult_le_compat_right Nmult_le_compat_left.

Lemma Nmult_le_compat : forall (n m:natO) x y, n <= m -> x<=y -> n */ x <= m */ y.
intros; apply Ole_trans with (n */y); auto.
Save.


Definition NMult : natO-m>U-m>U := le_compat2_mon Nmult_le_compat.


Lemma Nmult_sigma : forall (n:nat) (x:U), n */ x == sigma (fun k => x) n.
intros n x; induction n; simpl; auto.
destruct n; auto.
Save.

Hint Resolve Nmult_eq_compat_right Nmult_le_compat_right
Nmult_le_compat_left Nmult_sigma.

Lemma Nmult_Unth_prop : forall n:nat, [1/]1+n == [1-] (n*/ ([1/]1+n)).
intro.
rewrite (Nmult_sigma n ([1/]1+n)).
exact (Unth_prop n).
Save.
Hint Resolve Nmult_Unth_prop.

Lemma Nmult_n_Unth: forall n:nat, n */ [1/]1+n == [1-] ([1/]1+n).
intro; apply Uinv_eq_perm_right; auto.
Save.

Lemma Nmult_Sn_Unth: forall n:nat, S n */ [1/]1+n == 1.
intro; rewrite (Nmult_S n ([1/]1+n)).
rewrite (Nmult_n_Unth n); auto.
Save.

Hint Resolve Nmult_n_Unth Nmult_Sn_Unth.

Lemma Nmult_ge_Sn_Unth: forall n k, (S n <= k)%nat -> k */ [1/]1+n == 1.
induction 1; auto.
rewrite (Nmult_S m ([1/]1+n)); rewrite IHle; auto.
Save.

Lemma Nmult_le_n_Unth: forall n k, (k <= n)%nat -> k */ [1/]1+n <= [1-] ([1/]1+n).
intros; apply Ole_trans with (n */ [1/]1+n); auto.
Save.

Hint Resolve Nmult_ge_Sn_Unth Nmult_le_n_Unth.


Lemma Nmult_Umult_assoc_left : forall n x y, Nmult_def n x -> n*/(x*y) == (n*/x)*y.
intros n x y; induction n; auto; intros.
destruct n; auto.
repeat rewrite Nmult_SS.
assert(Nmult_def (S n) x); auto.
setoid_rewrite (IHn H0).
assert (x <= [1-] ((S n) */ x)).
apply Uinv_le_perm_right.
apply Ole_trans with ([1-] ([1/]1+(S n))); auto.
apply Ole_trans with ((S n) */ ([1/]1+(S n))); auto.
apply Oeq_sym; auto.
Save.

Hint Resolve Nmult_Umult_assoc_left.

Lemma Nmult_Umult_assoc_right : forall n x y, Nmult_def n y -> n*/(x*y) == x*(n*/y).
intros; rewrite (Umult_sym x y); rewrite (Nmult_Umult_assoc_left n y x H); auto.
Save.

Hint Resolve Nmult_Umult_assoc_right.

Lemma plus_Nmult_distr : forall n m x, (n + m) */ x== (n */ x) + (m */ x).
intros n m x; induction n; auto; intros.
rewrite plus_Sn_m.
rewrite (Nmult_S (n + m) x).
setoid_rewrite IHn.
rewrite (Nmult_S n x); auto.
Save.

Lemma Nmult_Uplus_distr : forall n x y, n */ (x + y) == (n */ x) + (n */ y).
intros n x y; induction n.
simpl; auto.
rewrite (Nmult_S n (x+y)).
rewrite IHn.
norm_assoc_right.
rewrite (Uplus_perm2 y (n */ x) (n */ y)).
rewrite <- (Nmult_S n y).
norm_assoc_left.
apply Uplus_eq_compat; auto.
Save.

Lemma Nmult_mult_assoc : forall n m x, (n * m) */ x == n */ (m */ x).
intros n m x; induction n; intros; auto.
simpl mult.
rewrite (plus_Nmult_distr m (n * m) x).
rewrite IHn; auto.
Save.

Lemma Nmult_Unth_simpl_left : forall n x, (S n) */ ([1/]1+n * x) == x.
intros.
rewrite (Nmult_Umult_assoc_left (S n) ([1/]1+n) x (Nmult_def_Unth n)).
rewrite (Nmult_Sn_Unth n); auto.
Save.

Lemma Nmult_Unth_simpl_right : forall n x, (S n) */ (x * [1/]1+n) == x.
intros.
rewrite (Nmult_Umult_assoc_right (S n) x ([1/]1+n) (Nmult_def_Unth n)).
rewrite (Nmult_Sn_Unth n); auto.
Save.

Hint Resolve Nmult_Umult_assoc_right plus_Nmult_distr Nmult_Uplus_distr
Nmult_mult_assoc Nmult_Unth_simpl_left Nmult_Unth_simpl_right.

Lemma Uinv_Nmult : forall k n, [1-] (k */ [1/]1+n) == ((S n) - k)  */ [1/]1+n.
intros k n; case (le_lt_dec (S n) k); intro.
rewrite (Nmult_ge_Sn_Unth l).
replace (S n - k)%nat with O; auto.
omega.
induction k; intros.
rewrite Nmult_0; rewrite Uinv_zero.
replace (S n - O)%nat with (S n); auto with arith.
rewrite (Nmult_S k ([1/]1+n)).
apply Uplus_eq_simpl_right with ([1/]1+n); auto.
apply Uinv_le_perm_right.
apply Nmult_le_n_Unth.
omega.
apply Oeq_trans with (((S n - S k) + (S O)) */ [1/]1+n).
replace ((S n - S k) + (S O))%nat with (S n - k)%nat.
apply Oeq_trans with ([1-] (k */ [1/]1+n)); auto with arith.
apply Uinv_plus_left.
apply Nmult_le_n_Unth; omega.
omega.
rewrite (plus_Nmult_distr (S n - S k) (S O) ([1/]1+n)); auto.
Save.

Lemma Nmult_neq_zero : forall n x, ~0==x -> ~0==S n */ x.
intros; rewrite (Nmult_S n x); auto.
apply Uplus_neq_zero_left; trivial.
Save.
Hint Resolve Nmult_neq_zero.


Lemma Nmult_le_simpl :  forall (n:nat) (x y:U),
   Nmult_def (S n) x -> Nmult_def (S n) y -> (S n */ x) <= (S n */ y) -> x <= y.
intros; apply Umult_le_simpl_left with (S n */ [1/]1+n).
auto.
assert (Nmult_def (S n) ([1/]1+n)); auto.
rewrite <- (Nmult_Umult_assoc_left (S n) ([1/]1+n) x H2).
rewrite <- (Nmult_Umult_assoc_left (S n) ([1/]1+n) y H2).
rewrite (Nmult_Umult_assoc_right (S n) ([1/]1+n) y H0).
rewrite (Nmult_Umult_assoc_right (S n) ([1/]1+n) x H).
apply Ole_trans with ([1/]1+n * (S n */ x)); auto.
Save.

Lemma Nmult_Unth_le : forall (n1 n2 m1 m2:nat),
   (n2 * S n1<= m2 * S m1)%nat -> n2 */ [1/]1+m1 <= m2 */ [1/]1+n1.
intros.
apply Ole_trans with ((n2 * S n1) */ ([1/]1+m1 * [1/]1+n1)).
rewrite (Nmult_mult_assoc n2 (S n1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_le_compat_right.
rewrite (Nmult_Unth_simpl_right n1 ([1/]1+m1)); auto.
apply Ole_trans with ((m2 * S m1) */ [1/]1+m1 * [1/]1+n1); auto.
rewrite (Nmult_mult_assoc m2 (S m1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_le_compat_right.
rewrite (Nmult_Unth_simpl_left m1 ([1/]1+n1)); auto.
Save.

Lemma Nmult_Unth_eq :
   forall (n1 n2 m1 m2:nat),
   (n2 * S n1= m2 * S m1)%nat -> n2 */ [1/]1+m1 == m2 */ [1/]1+n1.
intros.
apply Oeq_trans with ((n2 * S n1) */ ([1/]1+m1 * [1/]1+n1)).
rewrite (Nmult_mult_assoc n2 (S n1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_eq_compat_left; auto.
(* rewrite (Nmult_Unth_simpl_right n1 ([1/]1+m1)); auto.*)
rewrite H.
rewrite (Nmult_mult_assoc m2 (S m1) ([1/]1+m1 * [1/]1+n1)).
apply Nmult_eq_compat_left; auto.
(* rewrite (Nmult_Unth_simpl_left m1 ([1/]1+n1)); auto. *)
Save.

Hint Resolve Nmult_Unth_le Nmult_Unth_eq.

Lemma Nmult_def_lt : forall n x, n */ x <1 -> Nmult_def n x.
red; destruct n; intros; auto.
apply (Ule_total x ([1/]1+n)); intros; auto.
case H.
apply Ole_trans with (S n */ [1/]1+n); auto.
Save.

Hint Immediate Nmult_def_lt.

(*
Lemma Unth_half : forall n, [1/2] * [1/]1+n == [1/]1+(2*n+1).
intros.

Lemma Unth_mult : forall n m, [1/]1+n * [1/]1+m == [1/]1+(n+m+n*m).
intros.

Lemma half_nth : forall p, [1/]1+(2 * p + 1) + [1/]1+(2 * p + 1) == [1/]1+p.
*)

(*
(** ** Trivial space of measurable function on A : A -> U *)

Definition MFT : Type -> MFS.
intro A; exists A (A->U) (fun (f:A->U) (x:A) => f x)
            (fun (f g:A->U) (x:A) => f x + g x)
            (fun (k:U) (f:A->U) (x:A) => k * f x)
            (fun (f:A->U) (x:A) => [1-] f x) (fun (x:A) => (0:U))
            (fun (f : nat -> A -> U) (x:A) => lub (fun n => f n x)); auto.
Defined.
*)

(** ** Conversion from booleans to U *)

Definition B2U :MF bool := fun (b:bool) => if b then 1 else 0.

Definition NB2U :MF bool := fun (b:bool) => if b then 0 else 1.

Lemma B2Uinv : NB2U == finv B2U.
simpl; apply ford_eq_intro.
unfold NB2U,finv,B2U; intro b; case b; auto.
Save.

Lemma NB2Uinv : B2U == finv NB2U.
simpl; apply ford_eq_intro.
unfold NB2U,finv,B2U; intro b; case b; auto.
Save.

Hint Resolve B2Uinv NB2Uinv.

(** ** Particular sequences *)
  (**  $pmin (p)(n) = p - \frac{1}{2^n}$ *)

Definition pmin (p:U) (n:nat) :=  p - ([1/2]^n).

Add Morphism pmin with signature Oeq (O:=U) ==> eq (A:=nat) ==> Oeq (O:=U)
as pmin_eq_compat.
unfold pmin; auto.
Save.

(** *** Properties of [pmin] *)
Lemma pmin_esp_S : forall p n, pmin (p & p) n == pmin p (S n) & pmin p (S n).
unfold pmin at 1; intros.
rewrite (half_exp n).
rewrite (Uesp_minus_distr p p ([1/2]^(S n)) ([1/2]^(S n))); auto.
Save.

Lemma pmin_esp_le : forall p n,  pmin p (S n) <= [1/2] * (pmin (p & p) n) + [1/2].
intros; setoid_rewrite (pmin_esp_S p n); auto.
Save.

Lemma pmin_plus_eq :  forall p n, p <= [1/2] -> pmin p (S n) == [1/2] * (pmin (p + p) n).
intros; unfold pmin at 2.
setoid_rewrite (Uminus_distr_right [1/2] (p + p) ([1/2]^n)).
setoid_rewrite (half_twice _ H); auto.
Save.

Lemma pmin_0 : forall p:U, pmin p O == 0.
unfold pmin; simpl; auto.
Save.

Lemma pmin_le : forall (p:U) (n:nat), p - ([1/]1+n) <= pmin p n.
unfold pmin; intros.
apply Uminus_le_compat_right.
induction n; simpl; intros; auto.
apply Ole_trans with ([1/2] * ([1/]1+n)); auto.
Save.

Hint Resolve pmin_0 pmin_le.

Lemma pmin_le_compat : forall p (n m : natO), n <= m -> pmin p n <= pmin p m.
unfold pmin; intros.
apply Uminus_le_compat_right; auto.
Save.

Definition Pmin (p:U) :natO-m>U := mk_fmono (pmin_le_compat p).

Lemma le_p_lim_pmin : forall p, p <= lub (Pmin p).
intro; apply Ule_lt_lim; intros.
assert (exc (fun n : nat => t <= p - [1/]1+n)).
apply Ult_le_nth_minus; trivial.
apply H0; auto; intros n H1.
apply Ole_trans with (p - [1/]1+n); auto.
apply Ole_trans with (pmin p n); auto.
apply le_lub with (f:=Pmin p) (n:=n).
Save.

Lemma le_lim_pmin_p : forall p, lub (Pmin p) <= p.
intro; apply lub_le; simpl; unfold pmin; auto.
Save.
Hint Resolve le_p_lim_pmin le_lim_pmin_p.

Lemma eq_lim_pmin_p : forall p, lub (Pmin p) == p.
intros; apply Ole_antisym; auto.
Save.

Hint Resolve eq_lim_pmin_p.

(** Particular case where p = 1 *)

Definition U1min := Pmin 1.

Lemma eq_lim_U1min : lub U1min == 1.
unfold U1min; auto.
Save.

Lemma U1min_S : forall n, U1min (S n) == [1/2]*(U1min n) + [1/2].
intros; unfold U1min at 2,pmin.
rewrite (Uminus_distr_right [1/2] 1 ([1/2]^n)).
rewrite Umult_one_right.
rewrite Uminus_plus_perm; auto.
rewrite Unth_one_plus; auto.
Save.

Lemma U1min_0 : U1min O == 0.
unfold U1min; simpl; auto.
Save.

Hint Resolve eq_lim_U1min U1min_S U1min_0.

Lemma glb_half_exp : glb (UExp [1/2]) == 0.
unfold glb; apply Uinv_eq_perm_left.
apply Oeq_trans with (lub U1min).
apply lub_eq_compat; apply fmon_eq_intro; simpl; unfold U1min,pmin; simpl; auto.
rewrite eq_lim_U1min; auto.
Save.
Hint Resolve glb_half_exp.

Lemma Ule_lt_half_exp : forall x y, (forall p, x <= y + [1/2]^p) -> x <= y.
intros; apply Ole_trans with (glb (UExp [1/2]) + y).
apply Ole_trans with (glb (Imon (UPlus <_> y) @ (UExp [1/2]))).
apply le_glb; intro p; apply Ole_trans with (y + [1/2] ^ p); auto.
rewrite glb_eq_plus_cte_right; auto.
rewrite glb_half_exp; auto.
Save.

Lemma half_exp_le_half : forall p, [1/2]^(S p) <= [1/2].
simpl; auto.
Save.
Hint Resolve half_exp_le_half.

Lemma twice_half_exp : forall p, [1/2]^(S p) + [1/2]^(S p) ==  [1/2]^p.
simpl; intros.
rewrite <- Udistr_plus_right; auto.
Save.
Hint Resolve twice_half_exp.

(** *** Dyadic numbers *)
Fixpoint exp2 (n:nat) : nat :=
   match n with O => (1%nat) | S p => (2 * (exp2 p))%nat end.

Lemma exp2_pos : forall n, (O < exp2 n)%nat.
induction n; simpl; auto with arith.
Save.
Hint Resolve exp2_pos.

Lemma S_pred_exp2 : forall n, S (pred (exp2 n))=exp2 n.
intro; rewrite S_pred with (exp2 n) O; trivial.
Save.
Hint Resolve S_pred_exp2.

Notation "k  /2^ p" := (k */ ([1/2])^p) (at level 35, no associativity).

Lemma Unth_eq : forall n p, n*/ p == [1-]p -> p == [1/]1+n.
intros; apply Ole_antisym; apply (Ule_total p ([1/]1+n)); intros; auto.
apply Uinv_le_simpl.
apply Ole_trans with (n*/[1/]1+n); auto.
apply Ole_trans with (n*/p); auto.
apply Uinv_le_simpl.
apply Ole_trans with (n*/p); auto.
apply Ole_trans with (n*/[1/]1+n); auto.
Save.

Lemma Unth_half : forall n, (O<n)%nat -> [1/]1+(pred (n+n)) == [1/2] * [1/]1+pred n.
intros; apply Oeq_sym; apply Unth_eq.
destruct n; intros.
absurd (0<0)%nat; auto with arith.
simpl.
replace (n + S n)%nat with (2 * n + 1)%nat; auto with zarith.
rewrite plus_Nmult_distr.
rewrite Nmult_1.
rewrite Nmult_mult_assoc.
rewrite Nmult_Umult_assoc_right; auto.
rewrite Nmult_Umult_assoc_left; auto.
rewrite Nmult_Sn_Unth.
rewrite Umult_one_left.
rewrite Nmult_n_Unth.
rewrite Udistr_inv_right; auto.
Save.

Lemma Unth_exp2 : forall p, [1/2]^p == [1/]1+pred (exp2 p).
induction p; simpl; auto.
rewrite <- plus_n_O.
rewrite Unth_half; auto.
Save.

Hint Resolve Unth_exp2.

Lemma Nmult_exp2 : forall p, (exp2 p)/2^p == 1.
intros; rewrite Unth_exp2.
replace (exp2 p) with (S (pred (exp2 p))); auto.
Save.
Hint Resolve Nmult_exp2.

(** ** Tactic for simplification of goals *)

Ltac Usimpl :=  match goal with
    |- context [(Uplus 0 ?x)]     => setoid_rewrite (Uplus_zero_left x)
 |  |- context [(Uplus ?x 0)]     => setoid_rewrite (Uplus_zero_right x)
 |  |- context [(Uplus 1 ?x)]     => setoid_rewrite (Uplus_one_left x)
 |  |- context [(Uplus ?x 1)]     => setoid_rewrite (Uplus_one_right x)
 |  |- context [(Umult 0 ?x)]     => setoid_rewrite (Umult_zero_left x)
 |  |- context [(Umult ?x 0)]     => setoid_rewrite (Umult_zero_right x)
 |  |- context [(Umult 1 ?x)]     => setoid_rewrite (Umult_one_left x)
 |  |- context [(Umult ?x 1)]     => setoid_rewrite (Umult_one_right x)
 |  |- context [(Uesp 0 ?x)]     => setoid_rewrite (Uesp_zero_left x)
 |  |- context [(Uesp ?x 0)]     => setoid_rewrite (Uesp_zero_right x)
 |  |- context [(Uesp 1 ?x)]     => setoid_rewrite (Uesp_one_left x)
 |  |- context [(Uesp ?x 1)]     => setoid_rewrite (Uesp_one_right x)
 |  |- context [(Uminus 0 ?x)]    => rewrite (Uminus_le_zero 0 x);
                                        [idtac | apply (Upos x)]
 |  |- context [(Uminus ?x 0)]    => setoid_rewrite (Uminus_zero_right x)
 |  |- context [(Uminus ?x 1)]    => setoid_rewrite (Uminus_le_zero x 1);
                                        [idtac | apply (Unit x)]
 |  |- context [([1-] ([1-] ?x))] => setoid_rewrite (Uinv_inv x)
 |  |- context [([1-] 1)] => setoid_rewrite Uinv_one
 |  |- context [([1-] 0)] => setoid_rewrite Uinv_zero
 |  |- context [([1/]1+O)]        => setoid_rewrite Unth_zero
 |  |- context [?x^O] => setoid_rewrite (Uexp_0 x)
 |  |- context [?x^(S O)] => setoid_rewrite (Uexp_1 x)
 |  |- context [0^(?n)] => setoid_rewrite Uexp_zero; [idtac|omega]
 |  |- context [U1^(?n)] => setoid_rewrite Uexp_one
 |  |- context [(Nmult 0 ?x)]     => setoid_rewrite (Nmult_0 x)
 |  |- context [(Nmult 1 ?x)]     => setoid_rewrite (Nmult_1 x)
 |  |- context [(Nmult ?n 0)]     => setoid_rewrite (Nmult_zero n)
 |  |- context [(sigma ?f O)]     => setoid_rewrite (sigma_0 f)
 |  |- context [(sigma ?f (S O))]     => setoid_rewrite (sigma_1 f)
 |  |- (Ole (Uplus ?x ?y) (Uplus ?x ?z)) => apply Uplus_le_compat_right
 |  |- (Ole (Uplus ?x ?z) (Uplus ?y ?z)) => apply Uplus_le_compat_left
 |  |- (Ole (Uplus ?x ?z) (Uplus ?z ?y)) => setoid_rewrite (Uplus_sym z y);
					      apply Uplus_le_compat_left
 |  |- (Ole (Uplus ?x ?y) (Uplus ?z ?x)) => setoid_rewrite (Uplus_sym x y);
                                              apply Uplus_le_compat_left
 |  |- (Ole (Uinv ?y) (Uinv ?x)) => apply Uinv_le_compat
 |  |- (Ole (Uminus ?x ?y) (Uplus ?x ?z)) => apply Uminus_le_compat_right
 |  |- (Ole (Uminus ?x ?z) (Uplus ?y ?z)) => apply Uminus_le_compat_left
 |  |- (Oeq (Uinv ?x) (Uinv ?y)) => apply Uinv_eq_compat
 |  |- (Oeq (Uplus ?x ?y) (Uplus ?x ?z)) => apply Uplus_eq_compat_right
 |  |- (Oeq (Uplus ?x ?z) (Uplus ?y ?z)) => apply Uplus_eq_compat_left
 |  |- (Oeq (Uplus ?x ?z) (Uplus ?z ?y)) => setoid_rewrite (Uplus_sym z y);
                                             apply Uplus_eq_compat_left
 |  |- (Oeq (Uplus ?x ?y) (Uplus ?z ?x)) => setoid_rewrite (Uplus_sym x y);
					     apply Uplus_eq_compat_left
 |  |- (Oeq (Uminus ?x ?y) (Uplus ?x ?z)) => apply Uminus_eq_compat;[apply Oeq_refl|idtac]
 |  |- (Oeq (Uminus ?x ?z) (Uplus ?y ?z)) => apply Uminus_eq_compat;[idtac|apply Oeq_refl]
 |  |- (Ole (Umult ?x ?y) (Umult ?x ?z)) => apply Umult_le_compat_right
 |  |- (Ole (Umult ?x ?z) (Umult ?y ?z)) => apply Umult_le_compat_left
 |  |- (Ole (Umult ?x ?z) (Umult ?z ?y)) => setoid_rewrite (Umult_sym z y);
                                             apply Umult_le_compat_left
 |  |- (Ole (Umult ?x ?y) (Umult ?z ?x)) => setoid_rewrite (Umult_sym x y);
                                             apply Umult_le_compat_left
 |  |- (Oeq (Umult ?x ?y) (Umult ?x ?z)) => apply Umult_eq_compat_right
 |  |- (Oeq (Umult ?x ?z) (Umult ?y ?z)) =>  apply Umult_eq_compat_left
 |  |- (Oeq (Umult ?x ?z) (Umult ?z ?y)) => setoid_rewrite (Umult_sym z y);
                                             apply Umult_eq_compat_left
 |  |- (Oeq (Umult ?x ?y) (Umult ?z ?x)) => setoid_rewrite (Umult_sym x y);
                                             apply Umult_eq_compat_left
end.

(** Equality is not true, even for monotonic sequences fot instance n/m *)

Lemma Ulub_Uglb_exch_le : forall f : nat -> nat -> U,
     Ulub (fun n => Uglb (fun m => f n m)) <= Uglb (fun m => Ulub (fun n => f n m)).
intros; apply le_Uglb; intro m.
apply Ulub_le_compat; intro n.
apply Uglb_le with (f:=fun m0 : nat => f n m0) (n:=m).
Save.

(** ** Intervals *)

(** *** Definition *)
Record IU : Type := mk_IU {low:U; up:U; proper:low <= up}.

Hint Resolve proper.

(** the all set : [[0,1]] *)
Definition full := mk_IU 0 1 (Upos 1).
(** singleton : [[x]] *)
Definition singl (x:U) := mk_IU x x (Ole_refl x).
(** down segment : [[0,x]] *)
Definition inf (x:U) := mk_IU 0 x (Upos x).
(** up segment : [[x,1]] *)
Definition sup (x:U) := mk_IU x 1 (Unit x).

(** *** Relations *)
Definition Iin (x:U) (I:IU) := low I <= x /\ x <= up I.

Definition Iincl I J := low J <= low I /\ up I <= up J.

Definition Ieq I J := low I == low J /\ up I == up J.
Hint Unfold Iin Iincl Ieq.

(** *** Properties *)
Lemma Iin_low : forall I, Iin (low I) I.
auto.
Save.

Lemma Iin_up : forall I, Iin (up I) I.
auto.
Save.

Hint Resolve Iin_low Iin_up.

Lemma Iin_singl_elim : forall x y, Iin x (singl y) -> x == y.
unfold Iin; intuition (simpl; auto).
Save.


Lemma Iin_inf_elim : forall x y, Iin x (inf y) -> x <= y.
unfold Iin; intuition (simpl; auto).
Save.

Lemma Iin_sup_elim : forall x y, Iin x (sup y) -> y <= x.
unfold Iin; intuition (simpl; auto).
Save.

Lemma Iin_singl_intro : forall x y, x == y -> Iin x (singl y).
auto.
Save.

Lemma Iin_inf_intro : forall x y, x <= y -> Iin x (inf y).
auto.
Save.

Lemma Iin_sup_intro : forall x y, y <= x -> Iin x (sup y).
auto.
Save.

Hint Immediate Iin_inf_elim Iin_sup_elim Iin_singl_elim.
Hint Resolve Iin_inf_intro Iin_sup_intro Iin_singl_intro.

Lemma Iin_class : forall I x, class (Iin x I).
unfold class, Iin; split.
apply Ule_class; intuition.
apply Ule_class; intuition.
Save.

Lemma Iincl_class : forall I J, class (Iincl I J).
unfold class, Iincl; split.
apply Ule_class; intuition.
apply Ule_class; intuition.
Save.

Lemma Ieq_class : forall I J, class (Ieq I J).
unfold class, Ieq; split.
apply Ueq_class; intuition.
apply Ueq_class; intuition.
Save.
Hint Resolve Iin_class Iincl_class Ieq_class.

Lemma Iincl_in : forall I J, Iincl I J -> forall x, Iin x I -> Iin x J.
unfold Iin,Iincl; intuition.
apply Ole_trans with (low I); auto.
apply Ole_trans with (up I); auto.
Save.

Lemma Iincl_low : forall I J, Iincl I J -> low J <= low I.
unfold Iincl; intuition.
Save.

Lemma Iincl_up : forall I J, Iincl I J -> up I <= up J.
unfold Iincl; intuition.
Save.

Hint Immediate Iincl_low Iincl_up.

Lemma Iincl_refl : forall I, Iincl I I.
unfold Iincl; intuition.
Save.
Hint Resolve Iincl_refl.

Lemma Iincl_trans : forall I J K, Iincl I J -> Iincl J K -> Iincl I K.
unfold Iincl; intuition.
apply Ole_trans with (low J); auto.
apply Ole_trans with (up J); auto.
Save.

Definition IUord : ord.
exists IU (fun I J => Iincl J I); intros; auto.
apply Iincl_trans with y; auto.
Defined.

Lemma low_le_compat : forall I J:IUord, I<=J -> low I <= low J.
simpl; auto.
Save.

Lemma up_le_compat : forall I J : IUord, I<=J -> up J <= up I.
simpl; auto.
Save.

Definition Low : IUord-m>U := mk_fmono low_le_compat.

Definition Up : IUord-m>UI := mk_fmono (fmonot:=up:IUord->UI) up_le_compat.

Lemma Ieq_incl : forall I J, Ieq I J -> Iincl I J.
unfold Ieq,Iincl; intuition.
Save.

Lemma Ieq_incl_sym : forall I J, Ieq I J -> Iincl J I.
unfold Ieq,Iincl; intuition.
Save.
Hint Immediate Ieq_incl Ieq_incl_sym.

Lemma lincl_eq_compat : forall I J K L,
     Ieq I J -> Iincl J K -> Ieq K L -> Iincl I L.
intros; apply Iincl_trans with J; auto.
intros; apply Iincl_trans with K; auto.
Save.

Lemma lincl_eq_trans : forall I J K,
     Iincl I J -> Ieq J K -> Iincl I K.
intros; apply lincl_eq_compat with I J; auto.
Save.

Lemma Ieq_incl_trans : forall I J K,
     Ieq I J -> Iincl J K -> Iincl I K.
intros; apply lincl_eq_compat with J K; auto.
Save.

Lemma Iincl_antisym : forall I J, Iincl I J -> Iincl J I -> Ieq I J.
unfold Iincl; intuition.
Save.
Hint Immediate Iincl_antisym.

Lemma Ieq_refl : forall I, Ieq I I.
unfold Ieq; auto.
Save.
Hint Resolve Ieq_refl.

Lemma Ieq_sym : forall I J, Ieq I J -> Ieq J I.
unfold Ieq; intuition.
Save.
Hint Immediate Ieq_sym.

Lemma Ieq_trans : forall I J K, Ieq I J -> Ieq J K -> Ieq I K.
unfold Ieq; intuition.
apply Oeq_trans with (low J); auto.
apply Oeq_trans with (up J); auto.
Save.

Lemma Isingl_eq : forall x y, Iincl (singl x) (singl y) -> x==y.
unfold Iincl, singl; intuition.
Save.
Hint Immediate Isingl_eq.

Lemma Iincl_full : forall I, Iincl I full.
unfold Iincl, full; intuition.
Save.
Hint Resolve Iincl_full.

(** *** Operations on intervals *)

Definition Iplus I J := mk_IU (low I + low J) (up I + up J)
                                           (Uplus_le_compat _ _ _ _ (proper I) (proper J)).

Lemma low_Iplus : forall I J, low (Iplus I J)=low I + low J.
trivial.
Save.

Lemma up_Iplus : forall I J, up (Iplus I J)=up I + up J.
trivial.
Save.

Lemma Iplus_in : forall I J x y, Iin x I -> Iin y J -> Iin (x+y) (Iplus I J).
unfold Iin,Iplus; intuition (simpl; auto).
Save.

Lemma lplus_in_elim :
forall I J z, low I <= [1-]up J -> Iin z (Iplus I J)
                -> exc (fun x => Iin x I /\
                                                   exc (fun y => Iin y J /\ z==x+y)).
intros I J z H (H1,H2); simpl in H1,H2; intros.
assert (low I <= z).
apply Ole_trans with (low I + low J); auto.
apply (Ule_total (z-low I)  (up J)); intros.
apply class_exc.
(* case [z-low I <= up j] *)
apply exc_intro with (low I); split; auto.
apply exc_intro with (z-low I); split; auto.
assert (low I <= [1-]low J).
apply Ole_trans with ([1-]up J); auto.
split; auto.
apply Uplus_le_perm_right; auto.
rewrite Uplus_sym; auto.
(* case [up j <= z-low I] *)
assert (up J <= z); auto.
apply Ole_trans with (z - low I); auto.
apply exc_intro with (z-up J); split; auto.
split; auto.
apply Uplus_le_perm_left; auto.
rewrite Uplus_sym; auto.
apply exc_intro with (up J); auto.
Save.

Definition Imult I J := mk_IU (low I * low J) (up I * up J)
                                            (Umult_le_compat  _  _  _ _ (proper I) (proper J)).

Lemma low_Imult : forall I J, low (Imult I J) = low I * low J.
trivial.
Save.

Lemma up_Imult : forall I J, up (Imult I J) = up I * up J.
trivial.
Save.


Definition Imultk p I := mk_IU (p * low I) (p * up I) (Umult_le_compat_right p _ _ (proper I)).

Lemma low_Imultk : forall p I, low (Imultk p I) = p * low I.
trivial.
Save.

Lemma up_Imultk : forall p I, up (Imultk p I) = p * up I.
trivial.
Save.

Lemma Imult_in : forall I J x y, Iin x I -> Iin y J -> Iin (x*y) (Imult I J).
unfold Iin; intuition (simpl; auto).
Save.

Lemma Imultk_in : forall p I x , Iin x I -> Iin (p*x) (Imultk p I).
unfold Iin; intuition (simpl; auto).
Save.

(** *** Limits *)

Definition Ilim : forall I:natO-m>IUord, IU.
intros; exists (lub (Low@I)) (glb (Up@I)).
unfold glb; apply lub_inv; auto.
Defined.

Lemma low_lim : forall (I:natO-m>IUord), low (Ilim I) = lub (Low @ I).
trivial.
Save.

Lemma up_lim : forall (I:natO-m>IUord),   up (Ilim I) = glb (Up @ I).
trivial.
Save.

Lemma lim_Iincl :  forall (I:natO-m>IUord) n, Iincl (Ilim I) (I n).
unfold Ilim,Iincl; simpl; split.
apply le_lub with (f:=Low @ I) (n:=n).
apply glb_le with (f:=Up @ I) (n:=n).
Save.
Hint Resolve lim_Iincl.

Lemma Iincl_lim :  forall J (I:natO-m>IUord), (forall n, Iincl J (I n)) -> Iincl J (Ilim I).
unfold Ilim,Iincl; simpl; split.
apply lub_le with (f:=Low @ I); intro.
case (H n); auto.
apply le_glb with (f:=Up @ I); intro.
case (H n); auto.
Save.

Lemma IIim_incl_stable : forall (I J:natO-m>IUord), (forall n, Iincl (I n) (J n)) -> Iincl (Ilim I) (Ilim J).
intros; apply Iincl_lim.
intros; apply Iincl_trans with (I n); auto.
Save.
Hint Resolve IIim_incl_stable.

Definition IUcpo : cpo.
exists IUord full Ilim; intros; auto.
simpl; apply Iincl_lim; auto.
Defined.

(*
(** *** Fixpoints *)
Section Ifixpoint.
Variable A : Type.
Variable F : (A -> IU) -> A -> IU.
Hypothesis Fmon : forall I J, (forall x, Iincl (I x) (J x)) -> forall x, Iincl (F I x) (F J x).

Fixpoint Iiter (n:nat) : A -> IU :=
     match n with O => fun x => full | S m => F (Iiter  m) end.

Lemma Iiter_decr : forall x n, Iincl (Iiter (S n) x) (Iiter n x).
intros x n; generalize x; induction n; simpl; auto.
Save.
Hint Resolve Iiter_decr.

Definition Ifix (x:A) := Ilim (fun n => Iiter n x) (Iiter_decr x).

Lemma Iincl_fix : forall (x:A), Iincl (F Ifix x) (Ifix x).
unfold Ifix at 2; intros.
apply Iincl_lim.
destruct n; simpl; auto.
apply Fmon.
unfold Ifix; intros.
apply (lim_Iincl (fun n0 : nat => Iiter n0 x0)).
Save.

Lemma Iincl_inv : forall f, (forall x, Iincl (f x) (F f x)) -> forall x, Iincl (f x) (Ifix x).
unfold Ifix; intros; apply Iincl_lim.
intro n; generalize x; induction n; simpl; intros; auto.
apply Iincl_trans with (F f x0); auto.
Save.

End Ifixpoint.
*)

(** ** Limits inf and sup *)

Definition fsup (f:nat->U) (n:nat) := Ulub (fun k => f (n+k)%nat).

Definition finf (f:nat->U) (n:nat) := Uglb (fun k => f (n+k)%nat).

Lemma fsup_mon : forall (f:nat->U) n, fsup f (S n) <= fsup f n.
unfold fsup; intros.
apply Ulub_le; intros.
replace (S n+n0)%nat with (n+S n0)%nat; try omega.
apply le_Ulub with (f:=fun k : nat => f (n+k)%nat).
Save.
Hint Resolve fsup_mon.

Lemma finf_mon : forall (f:nat->U) n, finf f n <= finf f (S n).
unfold finf; intros.
apply le_Uglb; intros.
replace (S n+n0)%nat with (n+S n0)%nat; try omega.
apply Uglb_le with (f:=fun k : nat => f (n+k)%nat).
Save.

Hint Resolve finf_mon.

Definition Fsup (f:nat->U) : natO-m>UI := fnatO_intro (f:=fsup f:natO->UI) (fsup_mon f).
Definition Finf (f:nat->U) : natO-m>U := fnatO_intro (f:=finf f:natO->U) (finf_mon f).

Lemma fn_fsup : forall f n, f n <= fsup f n.
unfold fsup; intros.
pattern n at 1; replace n with (n+O)%nat; auto with arith.
apply le_Ulub with (f:=fun k : nat => f (n+k)%nat) (n:=O).
Save.
Hint Resolve fn_fsup.

Lemma finf_fn : forall f n, finf f n <= f n.
unfold finf; intros.
pattern n at 2; replace n with (n+O)%nat; auto with arith.
apply Uglb_le with (f:=fun k : nat => f (n+k)%nat) (n:=O).
Save.
Hint Resolve finf_fn.

Definition limsup f := glb (Fsup f).
Definition liminf f := lub (Finf f).

Lemma le_liminf_sup : forall f, liminf f <= limsup f.
unfold liminf,limsup; simpl; intro.
rewrite <- Uglb_glb.
apply Ole_trans with (Ulub (Finf f)); auto.
unfold Finf,Fsup,finf,fsup.
apply Ole_trans with
    (Uglb (fun m : nat => Ulub (fun n : nat => f (n+m)%nat))).
apply Ulub_Uglb_exch_le with (f:=fun n m => f (n+m)%nat).
apply Uglb_le_compat; simpl; intro.
apply Ulub_le_compat; simpl; intro.
replace ((x0+x)%nat) with ((x+x0)%nat); auto with arith.
Save.

Hint Resolve le_liminf_sup.

Definition has_lim f := limsup f <= liminf f.

Lemma eq_liminf_sup : forall f, has_lim f-> liminf f == limsup f.
intro; unfold has_lim; apply Ole_antisym; auto.
Save.


Definition cauchy f := forall (p:nat), exc (fun M:nat => forall n m,
          (M <= n)%nat -> (M <= m)%nat -> f n <= f m + [1/2]^p).


Definition is_limit f (l:U) := forall (p:nat), exc (fun M:nat => forall n,
          (M <= n)%nat -> f n <= l + [1/2]^p /\ l <= f n + [1/2]^p).

Lemma cauchy_lim : forall f, cauchy f -> is_limit f (limsup f).
unfold cauchy,is_limit; intros.
apply (H p); clear H; auto; intros M H; apply exc_intro with M; intros n H1; unfold limsup; split.
apply Ole_trans with (glb ((Imon (UPlus <_> [1/2]^p)) @ (mseq_lift_left (Fsup f) M))).
apply le_glb; simpl; intro k.
apply Ole_trans with (f (M + k)%nat + [1/2]^p); auto with arith.
rewrite glb_eq_plus_cte_right; Usimpl.
rewrite <- glb_lift_left; auto.
apply Ole_trans with (Fsup f M); auto; simpl.
unfold fsup; apply Ulub_le; intro k; auto with arith.
Save.


Lemma has_limit_cauchy : forall f l, is_limit f l -> cauchy f.
unfold cauchy,is_limit; intros.
apply (H (S p)); clear H; auto; intros M H; apply exc_intro with M; intros n m H1; unfold limsup.
case (H n); auto with arith; intros.
case (H m); auto with arith; intros.
apply Ole_trans with (l + [1/2]^(S p)); auto.
apply Ole_trans with (f m + [1/2]^(S p) + [1/2]^(S p)); auto.
norm_assoc_right; Usimpl; auto.
Save.

Lemma limit_le_unique : forall f l1 l2, is_limit f l1 -> is_limit f l2 -> l1 <= l2.
intros f l1 l2 liml1 liml2; apply Ule_lt_half_exp; intro p2.
intros; apply Ule_lt_half_exp; intro p1.
apply (liml1 p1); auto; intros M1 H1.
apply (liml2 p2); auto; intros M2 H2.
case (H1 (M1+M2)%nat); auto with arith; intros.
case (H2 (M1+M2))%nat; auto with arith; intros.
apply Ole_trans with (f (M1 + M2)%nat + [1/2]^p1); auto.
Save.


Lemma limit_unique : forall f l1 l2, is_limit f l1 -> is_limit f l2 -> l1 == l2.
intros; apply Ole_antisym; apply (limit_le_unique (f:=f)); auto.
Save.
Hint Resolve limit_unique.

Lemma has_limit_compute : forall f l, is_limit f l -> is_limit f (limsup f).
intros; apply cauchy_lim; auto.
apply has_limit_cauchy with l; trivial.
Save.


Lemma limsup_eq_mult : forall k (f : nat -> U),
        limsup (fun n => k * f n) == k * limsup f.
unfold limsup; intros.
apply Oeq_trans with (glb (Imon (UMult k) @ (Fsup f))); auto.
apply glb_eq_compat; apply fmon_eq_intro; simpl; unfold fsup; intros; auto.
rewrite glb_eq_mult; trivial.
Save.

Lemma liminf_eq_mult : forall k (f : nat -> U),
        liminf (fun n => k * f n) == k * liminf f.
unfold liminf; intros.
apply Oeq_trans with (lub ((UMult k) @ (Finf f))); auto.
apply lub_eq_compat; apply fmon_eq_intro; simpl; unfold finf; intros; auto.
Save.

Lemma limsup_eq_plus_cte_right : forall k (f : nat -> U),
                 limsup (fun n => (f n) + k) == limsup f + k.
unfold limsup; intros.
apply Oeq_trans with (glb (Imon (UPlus <_> k) @ (Fsup f))); auto.
apply glb_eq_compat; apply fmon_eq_intro; simpl; unfold fsup; intros; auto.
Save.

Lemma liminf_eq_plus_cte_right : forall k (f : nat -> U),
                 liminf (fun n => (f n) + k) == liminf f + k.
unfold liminf; intros.
apply Oeq_trans with (lub (UPlus <_> k @ (Finf f))); auto.
apply lub_eq_compat; apply fmon_eq_intro; simpl; unfold finf; intros; auto.
Save.

Lemma limsup_le_plus : forall (f g: nat -> U),
                 limsup (fun x => f x + g x) <= limsup f + limsup g.
intros; unfold limsup,fplus.
apply Ole_trans with (glb ((Imon2 UPlus @2 (Fsup f)) (Fsup g))).
apply glb_le_compat; simpl; intro.
unfold fsup; auto.
rewrite glb_eq_plus; auto.
Save.

Lemma liminf_le_plus : forall (f g: nat -> U),
                 liminf f + liminf g <= liminf (fun x => f x + g x).
intros; unfold liminf,fplus.
apply Ole_trans with (lub ((UPlus @2 (Finf f)) (Finf g))); auto.
apply lub_le_compat; simpl; unfold finf; auto.
Save.

Hint Resolve liminf_le_plus limsup_le_plus.

Lemma limsup_le_compat : forall f g : nat -o> U, f <= g -> limsup f <= limsup g.
unfold limsup; intros.
apply glb_le_compat; simpl; intros; unfold fsup; apply Ulub_le_compat; auto.
Save.

Lemma liminf_le_compat : forall f g : nat -o> U, f <= g -> liminf f <= liminf g.
unfold liminf; intros.
apply lub_le_compat; simpl; intros; unfold finf; apply Uglb_le_compat; auto.
Save.

Hint Resolve limsup_le_compat liminf_le_compat.

Lemma limsup_eq_compat : forall f g : nat -o> U, f == g -> limsup f == limsup g.
intros; apply Ole_antisym; auto.
Save.

Lemma liminf_eq_compat : forall f g : nat -o> U, f == g -> liminf f == liminf g.
intros; apply Ole_antisym; auto.
Save.

Hint Resolve liminf_eq_compat limsup_eq_compat.

Lemma limsup_inv :  forall f : nat -> U, limsup (fun x => [1-]f x) == [1-] liminf f.
unfold limsup, liminf; intros.
unfold glb; Usimpl.
apply lub_eq_compat; apply fmon_eq_intro; intro n; simpl; unfold finf,fsup,Uglb; simpl; Usimpl.
apply Ulub_eq_compat; apply ford_eq_intro; intro m; auto.
Save.

Lemma liminf_inv :  forall f : nat -> U, liminf (fun x => [1-]f x) == [1-] limsup f.
unfold limsup, liminf; intros.
unfold glb; Usimpl.
apply lub_eq_compat; apply fmon_eq_intro; intro n; simpl; unfold finf,fsup,Uglb; Usimpl.
apply Ulub_eq_compat; apply ford_eq_intro; intro m; auto.
Save.

Hint Resolve limsup_inv liminf_inv.

(** ** limits *)
Lemma liminf_incr : forall f:natO-m>U, liminf f == lub f.
unfold liminf;intros.
apply lub_eq_compat; apply fmon_eq_intro; simpl; intro.
unfold finf.
rewrite (glb_mon (mseq_lift_left f n)); simpl.
replace (n+0)%nat with n; auto with arith.
Save.

Lemma limsup_incr : forall f:natO-m>U, limsup f == lub f.
unfold limsup; intros.
apply Oeq_trans with (glb (fmon_cte natO (O2:=UI) (lub f))); auto.
apply glb_eq_compat; apply fmon_eq_intro; simpl; intro.
unfold fsup.
apply (Oeq_trans (O:=UI)) with (lub (mseq_lift_left f n)).
apply (Oeq_trans (O:=UI)) with (Ulub (mseq_lift_left f n)); auto.
apply Oeq_sym; auto.
Save.


Lemma has_limit_incr : forall f:natO-m>U, has_lim f.
red; intros.
rewrite liminf_incr; auto; rewrite limsup_incr; auto.
Save.

Lemma liminf_decr : forall f:natO-m>UI, liminf f == glb f.
unfold liminf; intros.
apply Oeq_trans with (lub (fmon_cte natO (glb f))); auto.
apply lub_eq_compat; apply fmon_eq_intro; simpl; unfold finf; intros.
apply Oeq_trans with (glb (mseq_lift_left f n)).
apply Oeq_trans with (Uglb (mseq_lift_left f n)); auto.
apply Oeq_sym; auto.
Save.


Lemma limsup_decr : forall f:natO-m>UI, limsup f == glb f.
unfold limsup;intros.
apply glb_eq_compat; apply fmon_eq_intro; simpl; unfold fsup; intro.
apply (Oeq_trans (O:=UI)) with (Ulub (mseq_lift_left f n)); auto.
apply (Oeq_trans (O:=UI)) with (mseq_lift_left f n O); auto.
apply Uopp_eq; apply (Ulub_mon (mseq_lift_left f n)).
simpl; replace (n+0)%nat with n; auto with arith.
Save.

Lemma has_limit_decr : forall f:natO-m>UI, has_lim f.
red; intros.
rewrite liminf_decr; auto; rewrite limsup_decr; auto.
Save.

Lemma has_limit_sum : forall f g: nat->U, has_lim f -> has_lim g -> has_lim (fun x => f x + g x).
unfold has_lim; intros.
apply Ole_trans with (limsup f + limsup g); auto.
apply  Ole_trans with (liminf f + liminf g); auto.
Save.

Lemma has_limit_inv : forall f : nat -> U, has_lim f -> has_lim (fun x => [1-]f x).
unfold has_lim; intros.
apply Ole_trans with  ([1-]liminf f); auto.
apply Ole_trans with  ([1-]limsup f); auto.
Save.

Lemma has_limit_cte : forall c, has_lim (fun n => c).
intros; apply (has_limit_incr (fmon_cte natO (c:U))); red; auto.
Save.


(** ** Definition and properties of series : infinite sums *)

Definition serie (f : nat -> U) : U := lub (sigma f).

Lemma serie_le_compat : forall (f g: nat -> U),
 (forall k,  f k <= g k) -> serie f  <= serie g.
unfold serie; intros; apply lub_le_compat; auto.
Save.

Lemma serie_eq_compat : forall (f g: nat -> U),
 (forall k, f k == g k) -> serie f == serie g.
unfold serie; intros; apply lub_eq_compat; auto.
Save.

Lemma serie_sigma_lift : forall (f :nat -> U) (n:nat),
          serie f == sigma f n + serie (fun k => f (n + k)%nat).
intros f n; unfold serie; apply Oeq_trans with
   (lub (mseq_lift_left (sigma f) n)); auto.
apply Oeq_trans with
  (lub (UPlus (sigma f n) @  sigma (fun k => f (n+k)%nat))).
apply lub_eq_compat; apply fmon_eq_intro; intros.
rewrite mseq_lift_left_simpl.
rewrite fmon_comp_simpl.
apply (sigma_plus_lift f n n0).
symmetry.
apply (lub_comp_eq (f:=UPlus (sigma f n)) (sigma (fun k : nat => f (n + k)%nat))  ).
apply (continuous2_app Uplus_continuous2).
Save.

Lemma serie_S_lift : forall (f :nat -> U),
          serie f == f O + serie (fun k => f (S k)).
intro; rewrite (serie_sigma_lift f (S O)); simpl.
apply Uplus_eq_compat; auto.
Save.

Lemma serie_zero : forall f, (forall k, f k ==0)-> serie f ==0.
unfold serie; intros.
rewrite <- (lub_cte (D:=U) 0).
apply lub_eq_compat; auto.
Save.

Lemma serie_not_zero : forall f k, 0 < f k ->  0 < serie f.
intros; apply Ult_le_trans with (sigma f (S k)).
apply (sigma_not_zero f) with (k:=k); auto.
unfold serie; apply le_lub; auto.
Save.

Lemma serie_zero_elim : forall f, serie f ==0->forall k, f k ==0.
intros; apply Ueq_class; red; intros.
assert (0 < serie f); auto.
apply serie_not_zero with k; auto.
Save.

Hint Resolve serie_eq_compat serie_le_compat serie_zero.

Lemma serie_le : forall f k, f k <= serie f.
intros; apply Ole_trans with (sigma f (S k)); auto.
unfold serie; apply le_lub; auto.
Save.

Lemma serie_minus_incr : forall f :natO-m> U,
     serie (fun k => f (S k) - f k) == lub f - f O.
intros; apply Oeq_trans with (lub (UMinus <_> f O @ f)).
unfold serie; apply lub_eq_compat.
apply fmon_eq_intro; intro n; rewrite fmon_comp_simpl; rewrite fmon_app_simpl.
rewrite UMinus_simpl.
apply (sigma_minus_incr f); auto.
apply Oeq_sym.
apply (lub_comp_eq (f:=UMinus <_> f O) f).
red; intro; rewrite fmon_app_simpl.
apply (continuous2_left (F:=UMinus) h (f O)); auto.
Save.

Lemma serie_minus_decr : forall f : natO -m> Uopp,
         serie (fun k => f k - f (S k)) == f O - glb f.
intros; apply Oeq_trans with (lub (UMinus (f O) @ f)).
unfold serie; apply lub_eq_compat.
apply fmon_eq_intro; intro n; rewrite fmon_comp_simpl.
rewrite UMinus_simpl.
apply (sigma_minus_decr f); auto.
apply Oeq_sym.
apply (lub_comp_eq (f:=UMinus (f O)) f).
apply (continuous2_app (F:=UMinus)); auto.
Save.

Lemma serie_plus : forall (f g : nat -> U),
   serie (fun k => (f k) + (g k))  == serie f + serie g.
intros; unfold serie.
apply Oeq_trans with
  (lub ((UPlus @2 sigma f) (sigma g))); auto.
apply lub_eq_compat; apply fmon_eq_intro; intro n.
exact (sigma_plus f g n).
Save.


Definition wretract (f : nat -> U) := forall k, f k <= [1-] (sigma f k).

Lemma retract_wretract : forall f, (forall n, retract f n) -> wretract f.
red; intros; auto.
Save.

Lemma wretract_retract : forall f, wretract f -> forall n, retract f n.
red; intros; auto.
Save.

Hint Resolve wretract_retract.

Lemma wretract_lt : forall (f : nat -> U), (forall (n : nat),  sigma f n < 1) -> wretract f.
intros; apply retract_wretract; intros.
apply retract_lt; trivial.
Save.

Lemma retract_zero_wretract :
       forall f n, retract f n -> (forall k, (n <= k)%nat -> f k == 0) -> wretract f.
red; intros.
assert (k < n \/ n <= k)%nat; intuition.
omega.
rewrite H0; auto.
Save.

Lemma wretract_le : forall f g : nat-o>U, f <= g -> wretract g -> wretract f.
red; intros.
apply Ole_trans with (g k); auto.
apply Ole_trans with ([1-]sigma g k); auto.
Save.

Lemma serie_mult :
  forall (f : nat -> U) c, wretract f -> serie (fun k => c * f k) == c * serie f.
unfold serie; intros.
apply Oeq_trans with (lub (UMult c @ sigma f)); auto.
apply lub_eq_compat; apply fmon_eq_intro; intro n.
apply (sigma_mult (f:=f) c (n:=n)); auto.
Save.
Hint Resolve serie_mult.

Lemma serie_prod_maj :  forall (f g : nat -> U),
   serie (fun k => f k * g k) <= serie f.
auto.
Save.

Hint Resolve serie_prod_maj.

Lemma serie_prod_le :  forall (f g : nat -> U) (c:U), (forall k, f k <= c)
   -> wretract g -> serie (fun k => f k * g k) <= c * serie g.
intros; apply Ole_trans with (serie (fun k => c * g k)); auto.
Save.

Lemma serie_prod_ge :  forall (f g : nat -> U) (c:U), (forall k, c <= (f k))
   -> wretract g -> c * serie g <= serie (fun k => f k * g k).
intros; apply Ole_trans with (serie (fun k => c * g k)); auto.
rewrite serie_mult; auto.
Save.

Hint Resolve serie_prod_le  serie_prod_ge.

(*
Lemma serie_inv : forall (f g : nat -> U), wretract f ->
  [1-] (serie (fun k => f k * g k)) == serie (fun k => f k * [1-] (g k)) + [1-] (serie f).
unfold serie; intros.
apply Oeq_trans with
  (glb (UInvopp @ sigma (fun k : nat => f k * g k))).
unfold glb; Usimpl.
apply lub_eq_compat; apply fmon_eq_intro; intro n.
repeat rewrite fmon_comp_simpl; rewrite UInv_simpl.
rewrite (UInvopp_simpl (sigma (fun k : nat => f k * g k) n)); auto.
apply Ole_trans with (glb (UPlus2 @2
*)

Lemma serie_inv_le : forall (f g : nat -> U), wretract f ->
  serie (fun k => f k * [1-] (g k)) <= [1-] (serie (fun k => f k * g k)).
unfold serie; intros.
apply lub_lub_inv_le; intros.
rewrite sigma_inv; auto.
Save.

Definition Serie : (nat -O-> U) -m> U.
exists serie.
red; intros; apply serie_le_compat; auto.
Defined.

Lemma Serie_simpl : forall f, Serie f = serie f.
trivial.
Save.

Lemma serie_continuous : continuous Serie.
red; intros; rewrite Serie_simpl; unfold serie.
apply Ole_trans with (lub (lub (Sigma @ h))).
apply lub_le_compat; intro n; auto.
apply sigma_continuous1.
rewrite <- (lub_exch_eq (Sigma @ h)).
apply lub_le_compat; intro n; auto.
Save.

End Univ_prop.
