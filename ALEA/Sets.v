Set Implicit Arguments.
Set Strict Implicit.
Require Export Setoid.
Require Omega.

(** * Sets.v: Definition of sets as predicates over a type A *)

Section sets.
Variable A : Type.
Variable decA : forall x y :A, {x=y}+{x<>y}. 

Definition set := A->Prop.
Definition full : set := fun (x:A) => True.
Definition empty : set := fun (x:A) => False.
Definition add (a:A) (P:set) : set := fun (x:A) => x=a \/ (P x).
Definition singl (a:A) :set := fun (x:A) => x=a.
Definition union (P Q:set) :set := fun (x:A) => (P x) \/ (Q x).
Definition compl (P:set) :set := fun (x:A) => ~P x.
Definition inter (P Q:set) :set := fun (x:A) => (P x) /\ (Q x).
Definition rem (a:A) (P:set) :set := fun (x:A) => x<>a /\ (P x).

(** ** Equivalence *)
Definition equiv (P Q:set) := forall (x:A), P x <-> Q x.

Implicit Arguments full [].
Implicit Arguments empty [].

Lemma equiv_refl : forall P:set, equiv P P.
unfold equiv; intuition.
Save.

Lemma equiv_sym : forall P Q:set, equiv P Q -> equiv Q P.
unfold equiv; firstorder.
Save.

Lemma equiv_trans : forall P Q R:set, 
   equiv P Q -> equiv Q R -> equiv P R.
unfold equiv; firstorder.
Save.

Hint Resolve equiv_refl.
Hint Immediate equiv_sym.

(** ** Setoid structure *)
Lemma set_setoid : Setoid_Theory set equiv.
split; red; auto.
exact equiv_trans.
Qed.

Add Setoid set equiv set_setoid as Set_setoid.

Add Morphism add : equiv_add.
unfold equiv,add; firstorder.
Save.

Add Morphism rem : equiv_rem.
unfold equiv,rem; firstorder.
Save.
Hint Resolve equiv_add equiv_rem.

Add Morphism union : equiv_union.
unfold equiv,union; firstorder.
Save.
Hint Immediate equiv_union.

Lemma equiv_union_left : 
  forall P1 Q P2,
   equiv P1 P2 -> equiv (union P1 Q) (union P2 Q).
auto.
Save.

Lemma equiv_union_right : 
  forall P Q1 Q2 ,
   equiv Q1 Q2 -> equiv (union P Q1) (union P Q2).
auto.
Save.

Hint Resolve equiv_union_left equiv_union_right.

Add Morphism inter : equiv_inter.
unfold equiv,inter; firstorder.
Save.
Hint Immediate equiv_inter.

Add Morphism compl : equiv_compl.
unfold equiv,compl; firstorder.
Save.
Hint Resolve equiv_compl.

Lemma equiv_add_empty : forall (a:A) (P:set), ~equiv (add a P) empty.
red; unfold equiv,empty,add; intros a P eqH; assert (H:=eqH a);  intuition.
Save.

(** ** Finite sets given as an enumeration of elements *)

Inductive finite (P: set) : Type := 
   fin_eq_empty : equiv P empty -> finite P
 | fin_eq_add : forall (x:A)(Q:set),
             ~ Q x-> finite Q -> equiv P (add x Q) -> finite P.
Hint Constructors finite.

Lemma fin_empty : (finite empty).
auto.
Defined.

Lemma fin_add : forall (x:A)(P:set),
             ~ P x -> finite P -> finite (add x P).
eauto.
Defined.

Lemma fin_equiv: forall (P Q : set), (equiv P Q)->(finite P)->(finite Q).
induction 2.
apply fin_eq_empty.
apply equiv_trans with P; auto.
apply fin_eq_add with x Q0; auto.
apply equiv_trans with P; auto.
Defined.

Hint Resolve fin_empty fin_add.

(** *** Emptyness is decidable for finite sets *)
Definition isempty (P:set) := equiv P empty.
Definition notempty (P:set) := not (equiv P empty).

Lemma isempty_dec : forall P, finite P -> {isempty P}+{notempty P}.
unfold isempty,notempty; destruct 1; auto.
right; red; intros.
apply (@equiv_add_empty x Q); auto.
apply equiv_trans with P; auto.
Save.

(** *** Size of a finite set *)
Fixpoint size (P:set) (f:finite P) {struct f}: nat :=
   match f with fin_eq_empty _ => 0%nat
              | fin_eq_add _ Q _ f' _ => S (size f')
   end.

Lemma size_equiv : forall P Q  (f:finite P) (e:equiv P Q),
    (size (fin_equiv e f)) = (size f).
induction f; simpl; intros; auto.
Save.

(** ** Inclusion *)
Definition incl (P Q:set) := forall x, P x -> Q x.

Lemma incl_refl : forall (P:set), incl P P.
unfold incl; intuition.
Save.

Lemma incl_trans : forall (P Q R:set), 
incl P Q -> incl Q R -> incl P R.
unfold incl; intuition.
Save.

Lemma equiv_incl : forall (P Q : set),  equiv P Q -> incl P Q.
unfold equiv, incl; firstorder.
Save.

Lemma equiv_incl_sym : forall (P Q : set), equiv P Q -> incl Q P.
unfold equiv, incl; firstorder.
Save.

Lemma equiv_incl_intro : 
forall (P Q : set), incl P Q -> incl Q P -> equiv P Q.
unfold equiv, incl; firstorder.
Save.

Hint Resolve incl_refl incl_trans equiv_incl_intro. 
Hint Immediate equiv_incl equiv_incl_sym. 

(** ** Properties of operations on sets *)

Lemma incl_empty : forall P, incl empty P.
unfold incl,empty; intuition.
Save.


Lemma incl_empty_false : forall P a, incl P empty -> ~ P a.
unfold incl; firstorder.
Save.

Lemma incl_add_empty : forall (a:A) (P:set), ~ incl (add a P) empty.
red; unfold incl,empty,add; intros a P eqH; assert (H:=eqH a);  intuition.
Save.

Lemma equiv_empty_false : forall P a, equiv P empty -> P a -> False.
unfold equiv; firstorder.
Save.

Hint Immediate incl_empty_false equiv_empty_false incl_add_empty.

Lemma incl_rem_stable :   forall a P Q, incl P Q -> incl (rem a P) (rem a Q).
unfold incl,rem;intuition.
Save.

Lemma incl_add_stable :   forall a P Q, incl P Q -> incl (add a P) (add a Q).
unfold incl,add;intuition.
Save.

Lemma incl_rem_add_iff : 
  forall a P Q, incl (rem a P) Q <-> incl P (add a Q).
unfold rem, add, incl; intuition.
case (decA x a); auto.
case (H x); intuition.
Save.

Lemma incl_rem_add: 
  forall (a:A) (P Q:set), 
     (P a) -> incl Q (rem a P) -> incl (add a Q) P.
unfold rem, add, incl; intros; auto.
case H1; intro; subst; auto.
case (H0 x); auto.
Save.

Lemma incl_add_rem : 
  forall (a:A) (P Q:set), 
     ~ Q a -> incl (add a Q) P -> incl Q (rem a P) .
unfold rem, add, incl; intros; auto.
case (decA x a); intros; auto.
subst; case H; auto.
Save.

Hint Immediate incl_rem_add incl_add_rem.

Lemma equiv_rem_add : 
 forall (a:A) (P Q:set), 
     (P a) -> equiv Q (rem a P)  -> equiv (add a Q) P.
intros; assert (incl Q (rem a P)); auto.
assert (incl (rem a P) Q); auto.
case (incl_rem_add_iff a P Q); auto.
Save.

Lemma equiv_add_rem : 
 forall (a:A) (P Q:set), 
     ~ Q a -> equiv (add a Q) P -> equiv Q (rem a P).
intros; assert (incl (add a Q) P); auto.
assert (incl P (add a Q)); auto.
case (incl_rem_add_iff a P Q); auto.
Save.

Hint Immediate equiv_rem_add equiv_add_rem.

Lemma add_rem_eq_equiv : 
  forall x (P:set), equiv (add x (rem x P)) (add x P).
unfold equiv, add, rem; intuition.
case (decA x0 x); intuition.
Save.

Lemma add_rem_diff_equiv : 
  forall x y (P:set), 
  x<>y -> equiv (add x (rem y P)) (rem y (add x P)).
unfold equiv, add, rem; intuition.
subst; auto.
Save.

Lemma add_equiv_in : 
  forall x (P:set), P x -> equiv (add x P) P.
unfold equiv, add; intuition.
subst;auto.
Save.

Hint Resolve add_rem_eq_equiv add_rem_diff_equiv add_equiv_in.


Lemma add_rem_equiv_in : 
  forall x (P:set), P x -> equiv (add x (rem x P)) P.
intros; apply equiv_trans with (add x P); auto.
Save.

Hint Resolve add_rem_equiv_in.

Lemma rem_add_eq_equiv : 
  forall x (P:set), equiv (rem x (add x P)) (rem x P).
unfold equiv, add, rem; intuition.
Save.

Lemma rem_add_diff_equiv : 
  forall x y (P:set), 
  x<>y -> equiv (rem x (add y P)) (add y (rem x P)).
intros; apply equiv_sym; auto.
Save.

Lemma rem_equiv_notin : 
  forall x (P:set), ~P x -> equiv (rem x P) P.
unfold equiv, rem; intuition.
subst;auto.
Save.

Hint Resolve rem_add_eq_equiv rem_add_diff_equiv rem_equiv_notin.

Lemma rem_add_equiv_notin : 
  forall x (P:set), ~P x -> equiv (rem x (add x P)) P.
intros; apply equiv_trans with (rem x P); auto.
Save.

Hint Resolve rem_add_equiv_notin.


Lemma rem_not_in : forall x (P:set), ~ rem x P x.
unfold rem; intuition.
Save.

Lemma add_in : forall x (P:set), add x P x.
unfold add; intuition.
Save.

Lemma add_in_eq : forall x y P, x=y -> add x P y.
unfold add; intuition.
Save.

Lemma add_intro : forall x (P:set) y, P y -> add x P y.
unfold add; intuition.
Save.

Lemma add_incl : forall x (P:set), incl P (add x P).
unfold incl,add; intuition.
Save.

Lemma add_incl_intro : forall x (P Q:set), (Q x) -> (incl P Q) -> (incl (add x P) Q).
unfold incl,add; intuition; subst; intuition.
Save.

Lemma rem_incl : forall x (P:set), incl (rem x P) P.
unfold incl, rem; intuition.
Save.

Hint Resolve rem_not_in add_in rem_incl add_incl.

Lemma union_sym : forall P Q : set,
      equiv (union P Q) (union Q P).
unfold equiv, union; intuition.
Save.

Lemma union_empty_left : forall P : set,
      equiv P (union P empty).
unfold equiv, union, empty; intuition.
Save.

Lemma union_empty_right : forall P : set,
      equiv P (union empty P).
unfold equiv, union, empty; intuition.
Save.

Lemma union_add_left : forall (a:A) (P Q: set),
      equiv (add a (union P Q)) (union P (add a Q)).
unfold equiv, union, add; intuition.
Save.

Lemma union_add_right : forall (a:A) (P Q: set),
      equiv (add a (union P Q)) (union (add a P) Q).
unfold equiv, union, add; intuition.
Save.

Hint Resolve union_sym union_empty_left union_empty_right
union_add_left union_add_right.

Lemma union_incl_left : forall P Q, incl P (union P Q).
unfold incl,union; intuition.
Save.

Lemma union_incl_right : forall P Q, incl Q (union P Q).
unfold incl,union; intuition.
Save.

Lemma union_incl_intro : forall P Q R, incl P R -> incl Q R -> incl (union P Q) R.
unfold incl,union; intuition.
Save.

Hint Resolve union_incl_left union_incl_right union_incl_intro.

Lemma incl_union_stable : forall P1 P2 Q1 Q2,
	incl P1 P2 -> incl Q1 Q2 -> incl (union P1 Q1) (union P2 Q2).
intros; apply union_incl_intro; unfold incl,union; intuition.
Save.
Hint Immediate incl_union_stable.

Lemma inter_sym : forall P Q : set,
      equiv (inter P Q) (inter Q P).
unfold equiv, inter; intuition.
Save.

Lemma inter_empty_left : forall P : set,
      equiv empty (inter P empty).
unfold equiv, inter, empty; intuition.
Save.

Lemma inter_empty_right : forall P : set,
      equiv empty (inter empty P).
unfold equiv, inter, empty; intuition.
Save.

Lemma inter_add_left_in : forall (a:A) (P Q: set),
      (P a) -> equiv (add a (inter P Q)) (inter P (add a Q)).
unfold equiv, inter, add; split; intuition.
subst; auto.
Save.

Lemma inter_add_left_out : forall (a:A) (P Q: set),
      ~ P a -> equiv (inter P Q) (inter P (add a Q)).
unfold equiv, inter, add; split; intuition.
subst; case H; auto.
Save.

Lemma inter_add_right_in : forall (a:A) (P Q: set),
      Q a -> equiv (add a (inter P Q)) (inter (add a P) Q).
unfold equiv, inter, add; split; intuition.
subst; auto.
Save.

Lemma inter_add_right_out : forall (a:A) (P Q: set),
      ~ Q a -> equiv (inter P Q) (inter (add a P) Q).
unfold equiv, inter, add; split; intuition.
subst; case H; auto.
Save.

Hint Resolve inter_sym inter_empty_left inter_empty_right
inter_add_left_in inter_add_left_out inter_add_right_in inter_add_right_out.

(** ** Generalized union *)
Definition gunion (I:Type)(F:I->set) : set := fun z => exists i, F i z.

Lemma gunion_intro : forall I (F:I->set) i, incl (F i) (gunion F). 
red; intros; exists i; auto.
Save.

Lemma gunion_elim : forall I (F:I->set) (P:set), (forall i, incl (F i) P) -> incl (gunion F) P.
red; intros I F P H x (i,Hi).
apply (H i x); auto.
Save.

Lemma gunion_monotonic : forall I (F G : I -> set), 
      (forall i, incl (F i) (G i))-> incl (gunion F) (gunion G).
intros I F G H x (i,Hi).
exists i; apply (H i x); trivial.
Save.


(** ** Removing an element from a finite set *)

Lemma finite_rem :  forall (P:set) (a:A),
   finite P -> finite (rem a P).
induction 1; intuition.
apply fin_eq_empty.
unfold rem,empty,equiv; intuition.
apply (equiv_empty_false x e); auto.
case (decA x a); intros.
apply fin_equiv with Q; subst; auto.
apply equiv_add_rem; auto.
apply fin_eq_add with x (rem a Q); auto.
subst; unfold rem; intuition.
apply equiv_trans with (rem a (add x Q)); auto.
Defined.

Lemma size_finite_rem: 
   forall (P:set) (a:A) (f:finite P), 
    (P a) -> size f = S (size (finite_rem a f)).
induction f;  intros.
case (equiv_empty_false a e H).
simpl; case (decA x a); simpl; intros.
case e0; unfold eq_rect_r;simpl; auto.
rewrite size_equiv; auto.
rewrite IHf; auto.
case (e a); unfold add; intuition.
case n0; auto.
Save.

(* bug lie a intuition
Lemma size_finite_rem: 
   forall (P:set) (a:A) (f:finite P), 
    (P a) -> size f = S (size (finite_rem a f)).
induction f;  intuition.
case (equiv_empty_false a e H).
simpl; case (decA x a); simpl; intros.
case e0; unfold eq_rect_r;simpl; auto.
rewrite size_equiv; auto.
rewrite IHf; auto.
case (e a); unfold add; intuition.
case f0; auto.
Save.
*)
Require Import Arith.

Lemma size_incl : 
  forall (P:set)(f:finite P) (Q:set)(g:finite Q), 
  (incl P Q)-> size f <= size g.
induction f; simpl; intros; auto with arith.
apply le_trans with (S (size (finite_rem x g))).
apply le_n_S.
apply IHf with (g:= finite_rem x g); auto.
apply incl_trans with (rem x P); auto.
apply incl_add_rem; auto.
apply incl_rem_stable; auto.
rewrite <- size_finite_rem; auto.
case (e x); intuition.
Save.

Lemma size_unique : 
  forall (P:set)(f:finite P) (Q:set)(g:finite Q), 
  (equiv P Q)-> size f = size g.
intros; apply le_antisym; apply size_incl; auto.
Save.

(** ** Decidable sets *)
Definition dec (P:set) := forall x, {P x}+{~ P x}.

Lemma finite_incl : forall P:set,
   finite P -> forall Q:set, dec Q -> incl Q P -> finite Q.
intros P FP; elim FP; intros; auto.
apply fin_eq_empty.
unfold empty,equiv in *|-*; intuition.
case (e x); auto.
case (X0 x); intros.
apply fin_eq_add with (x:=x) (Q:=(rem x Q0)); auto.
apply X.
unfold dec,rem.
intro y; case (decA x y); intro.
case (X0 y); subst; intuition.
case (X0 y); intuition.
case (incl_rem_add_iff x Q0 Q); intuition.
apply H1; apply incl_trans with P0; auto.
apply equiv_sym; auto.
apply X; auto.
red; intros.
case (e x0); intuition.
case H1; intuition; subst; auto.
case n0; auto.
Save.

Lemma finite_dec : forall P:set, finite P -> dec P.
red; intros P FP; elim FP; intros.
right; intro; apply (equiv_empty_false x e); auto.
case (e x0); unfold add; intuition.
case (X x0); intuition.
case (decA x0 x); intuition.
Save.

Lemma fin_add_in : forall (a:A) (P:set), finite P -> finite (add a P).
intros a P FP; case (finite_dec FP a); intro.
apply fin_equiv with P; auto.
apply equiv_sym; auto.
apply fin_add; auto.
Defined.

Lemma finite_union : 
     forall P Q, finite P -> finite Q -> finite (union P Q).
intros P Q FP FQ; elim FP; intros.
apply fin_equiv with Q; auto.
apply equiv_trans with (union empty Q); auto.
apply fin_equiv with (add x (union Q0 Q)); auto.
apply equiv_trans with (union (add x Q0) Q); auto. 
apply fin_add_in; auto.
Defined.
 
Lemma finite_full_dec : forall P:set, finite full -> dec P -> finite P.
intros; apply finite_incl with full; auto.
unfold full,incl; auto.
Save.

Require Import Lt.

(** *** Filter operation *)

Lemma finite_inter : forall P Q, dec P -> finite Q -> finite (inter P Q).
intros P Q decP FQ.
induction FQ.
constructor 1.
apply equiv_trans with (inter P empty); auto.
case (decP x); intro.
constructor 2 with x (inter P Q); auto.
unfold inter; intuition.
rewrite e.
unfold add,inter; red; intuition.
subst; auto.
apply fin_equiv with (inter P Q); auto.
rewrite e.
unfold add,inter; red; intuition.
subst; intuition.
Defined.

Lemma size_inter_empty : forall P Q (decP:dec P) (e:equiv Q empty), 
   size (finite_inter decP (fin_eq_empty e))=O.
trivial.
Save.

Lemma size_inter_add_in : 
     forall P Q R (decP:dec P)(x:A)(nq:~Q x)(FQ:finite Q)(e:equiv R (add x Q)),
      P x ->size (finite_inter decP (fin_eq_add nq FQ e))=S (size (finite_inter decP FQ)).
intros; simpl.
case (decP x); intro; trivial; contradiction.
Save.

Lemma size_inter_add_notin : 
     forall P Q R (decP:dec P)(x:A)(nq:~Q x)(FQ:finite Q)(e:equiv R (add x Q)),
   ~ P x -> size (finite_inter decP (fin_eq_add nq FQ e))=size (finite_inter decP FQ).
intros; simpl.
case (decP x); intro; try contradiction.
rewrite size_equiv; trivial.
Save.

Lemma size_inter_incl : forall P Q (decP:dec P)(FP:finite P)(FQ:finite Q), 
    (incl P Q) -> size (finite_inter decP FQ)=size FP.
intros; apply size_unique.
unfold inter; intro.
generalize (H x); intuition.
Save.

(** *** Selecting elements in a finite set *)

Fixpoint nth_finite (P:set) (k:nat) (PF : finite P) {struct PF}: (k < size PF) -> A := 
  match PF as F return (k < size F) -> A with 
       fin_eq_empty H => (fun (e : k<0) => match lt_n_O k e with end)
     | fin_eq_add x Q nqx fq eqq => 
           match k as k0 return k0<S (size fq)->A with 
                O => fun e => x
         | (S k1) => fun (e:S k1<S (size fq)) => nth_finite fq (lt_S_n k1 (size fq) e)
           end
  end.


(** A set with size > 1 contains at least 2 different elements **)

Lemma select_non_empty : forall (P:set), finite P -> notempty P -> sigT P.
destruct 1; intros.
case H; auto.
exists x; case (e x); intuition.
Defined.

Lemma select_diff : forall (P:set) (FP:finite P),
     (1 < size FP)%nat -> sigT (fun x => sigT (fun y => P x /\ P y /\ x<>y)).
destruct FP; simpl; intros.
absurd (1<0); omega.
exists x; destruct FP; simpl in H.
absurd (1<1); omega.
exists x0; intuition.
case (e x); auto.
case (e0 x0); case (e x0); unfold add; intuition.
subst; case (e0 x0); intuition.
Save.

End sets.

Hint Resolve equiv_refl.
Hint Resolve equiv_add equiv_rem.
Hint Immediate equiv_sym finite_dec finite_full_dec equiv_incl equiv_incl_sym equiv_incl_intro.

Hint Resolve incl_refl.
Hint Immediate incl_union_stable.
Hint Resolve union_incl_left union_incl_right union_incl_intro incl_empty rem_incl
incl_rem_stable incl_add_stable.

Hint Constructors finite.
Hint Resolve add_in add_in_eq add_intro add_incl add_incl_intro union_sym union_empty_left union_empty_right
union_add_left union_add_right finite_union equiv_union_left 
equiv_union_right.
Implicit Arguments full [].
Implicit Arguments empty [].

Add Parametric Relation (A:Type) : (set A) (equiv (A:=A))
      reflexivity proved by (equiv_refl (A:=A))
      symmetry proved by (equiv_sym (A:=A))
      transitivity proved by (equiv_trans (A:=A))
as equiv_rel.

Add Parametric Relation (A:Type) : (set A) (incl (A:=A))
      reflexivity proved by (incl_refl (A:=A))
      transitivity proved by (incl_trans (A:=A))
as incl_rel.
