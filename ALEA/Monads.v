(** * Monads.v: Monads for randomized constructions *)

Set Implicit Arguments.
Require Export Uprop.

Module Monad (Univ:Universe).
Module UP := (Univ_prop Univ).
(* begin hide *)
Import Univ.
Import UP.
Open Local Scope U_scope.
Open Local Scope O_scope.
(* end hide *)

(** ** Definition of monadic operators as the cpo of monotonic oerators *)
Definition M (A:Type) := (A -O-> U)  -M-> U.

Definition unit : forall (A:Type), A -> M A.
intros A x; exists (fun (f:A-o>U) => f x).
red; auto.
Defined.

Definition star : forall (A B:Type), M A -> (A -> M B) -> M B.
intros A B a F; exists (fun f => a (fun x => F x f)).
red; auto.
Defined.

Lemma star_simpl : forall (A B:Type) (a:M A) (F:A -> M B)(f:MF B),
        star a F f =  a (fun x => F x f).
trivial.
Save.

(** ** Properties of monadic operators *)
Lemma law1 : forall (A B:Type) (x:A) (F:A -> M B) (f:MF B), star (unit x) F f == F x f.
trivial.
Qed.

Lemma law2 :
 forall (A:Type) (a:M A) (f:MF A), star a (fun x:A => unit x) f == a (fun x:A => f x).
trivial.
Qed.

Lemma law3 :
 forall (A B C:Type) (a:M A) (F:A -> M B) (G:B -> M C)
   (f:MF C), star (star a F) G f == star a (fun x:A => star (F x) G) f.
trivial.
Qed.

(** ** Properties of distributions *)
(** *** Expected properties of measures *)

Definition stable_inv (A:Type) (m:M A) : Prop := forall f :MF A, m (finv f) <= [1-] (m f).


Definition fplusok (A:Type) (f g : MF A) :=  f <= finv g.
Hint Unfold fplusok.

Lemma fplusok_sym : forall (A:Type) (f g : MF A) , fplusok f g -> fplusok g f.
unfold fplusok, finv; intros;  intro; auto.
Save.
Hint Immediate fplusok_sym.

Lemma fplusok_inv : forall (A:Type) (f : MF A) , fplusok f (finv f).
intros; apply fplusok_sym; unfold fplusok; auto.
Save.
Hint Resolve fplusok_inv.

Lemma fplusok_le_compat : forall (A:Type)(f1 f2 g1 g2:MF A), 
      fplusok f2 g2 -> f1 <= f2 -> g1 <= g2 -> fplusok f1 g1.
unfold fplusok; intros.
apply Ole_trans with f2; trivial.
apply Ole_trans with (finv g2); trivial.
apply finv_le_compat; auto.
Save.

Lemma fconj_fplusok : forall (A:Type)(f g h:MF A), fplusok g h -> 
          fplusok (fconj f g) (fconj f h).
intros; apply fplusok_le_compat with g h; auto.
Save.
Hint Resolve fconj_fplusok.


Definition stable_plus (A:Type) (m:M A) : Prop :=
  forall f g:MF A, fplusok f g -> m (fplus f g) == (m f) + (m g).

Definition le_plus (A:Type) (m:M A) : Prop :=
  forall f g:MF A,  fplusok f g -> (m f) + (m g) <= m (fplus f g).

Definition le_esp (A:Type) (m:M A) : Prop :=
  forall f g: MF A,  (m f) & (m g) <= m (fesp f g).

Definition le_plus_cte (A:Type) (m:M A) : Prop :=
  forall (f : MF A) (k:U),  m (fplus f (fcte A k))  <= m f + k.

Definition stable_mult (A:Type) (m:M A) : Prop :=
  forall (k:U) (f:MF A), m (fmult k f) == k * (m f).

(** *** Stability for equality *)

Lemma stable_minus_distr : forall (A:Type) (m:M A),
     stable_plus m -> stable_inv m ->
     forall (f g : MF A), g <= f -> m (fminus f g) == m f - m g.
intros A m splus sinv; intros.
assert (m g <= m f); auto.
assert (fminus f g <= finv g).
intros; intro x; unfold fminus,Uminus,fplus, finv; auto.
rewrite (fmon_stable m (x:=f) (y:=fplus (fminus f g) g)).
rewrite (splus (fminus f g)  g); auto.
rewrite Uplus_minus_simpl_right; auto.
apply Uinv_le_perm_right.
apply Ole_trans with (m (finv g)); auto.
simpl; apply ford_eq_intro; intro x; unfold fplus,fminus; auto.
Save.

Hint Resolve stable_minus_distr.

Lemma inv_minus_distr : forall (A:Type) (m:M A),
     stable_plus m -> stable_inv m ->
     forall (f : MF A), m (finv f) == m (fone A) - m f.
intros A m splus sinv; intros.
apply Oeq_trans with (m (fminus (fone A) f)); auto.
apply (fmon_stable m).
simpl; apply ford_eq_intro; intro x; unfold fminus,finv,fone,fplus; intros; auto.
Save.
Hint Resolve inv_minus_distr.

Lemma le_minus_distr : forall (A : Type)(m:M A),
    forall  (f g:A -> U), m (fminus f g) <= m f.
intros A m; intros.
apply (fmonotonic m); intro x; rewrite fminus_eq; auto.
Save.
Hint Resolve le_minus_distr.

Lemma le_plus_distr : forall (A : Type)(m:M A),
    stable_plus m -> stable_inv m -> forall (f g:MF A), m (fplus f g) <= m f + m g.
intros A m splus sinv; intros.
apply Ole_trans with (m (fplus (fminus f (fesp f g)) g)).
apply (fmonotonic m); intro x; unfold fminus,fesp,fplus,finv; intros; auto.
rewrite (splus (fminus f (fesp f g)) g).
Usimpl; auto.
red; intro x; unfold fminus,fesp,finv; auto.
Save.
Hint Resolve le_plus_distr.

Lemma le_esp_distr : forall (A : Type) (m:M A),
     stable_plus m -> stable_inv m -> le_esp m.
intros A m splus sinv; unfold le_esp,fesp,Uesp; intros.
apply Ole_trans with (m (finv (fplus (finv f) (finv g)))).
2:auto.
rewrite inv_minus_distr; trivial.
apply Ole_trans with
  (m (fone A) -  (m (finv f) + m (finv g))).
2:auto.
apply Ole_trans with (m f - [1-] m g) ; repeat Usimpl.
auto.
rewrite inv_minus_distr; trivial.
apply Ole_trans with (m f - m (finv g)) ; repeat Usimpl.
apply Uminus_le_compat_right; trivial.
rewrite <- Uminus_assoc_left.
rewrite Uminus_assoc_right; repeat Usimpl; auto.
Save.


Lemma unit_stable_eq : forall (A:Type) (x:A), stable (unit x).
auto.
Qed.

Lemma star_stable_eq : forall (A B:Type) (m:M A) (F:A -> M B), stable (star m F).
auto.
Qed.

(** *** Stability for inversion *)
Lemma unit_stable_inv : forall (A:Type) (x:A), stable_inv (unit x).
red in |- *; intros.
unfold unit in |- *.
auto.
Qed.

Lemma star_stable_inv : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_inv m -> (forall a:A, stable_inv (F a)) -> stable_inv (star m F).
unfold stable_inv in |- *; intros.
unfold star in |- *; simpl.
apply Ole_trans with (m (finv (fun x:A => F x f))); trivial.
apply (fmonotonic m); intro x.
apply (H0 x f).
Save.

(** *** Stability for addition *)
Lemma unit_stable_plus : forall (A:Type) (x:A), stable_plus (unit x).
red in |- *; intros.
unfold unit in |- *; auto.
Qed.

Lemma star_stable_plus : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_plus m ->
   (forall a:A, forall f g, fplusok f g -> (F a f) <= Uinv (F a g))
   -> (forall a:A, stable_plus (F a)) -> stable_plus (star m F).
unfold stable_plus in |- *; intros.
unfold star in |- *; simpl.
apply Oeq_trans with (m (fplus (fun x:A => F x f) (fun x:A => F x g))); trivial.
apply (fmon_stable m).
simpl; apply ford_eq_intro; intros x; apply (H1 x f g H2).
apply H.
red; intro x; unfold finv; intros; auto.
Qed.

Lemma unit_le_plus : forall (A:Type) (x:A), le_plus (unit x).
red in |- *; intros.
unfold unit in |- *.
auto.
Qed.

Lemma star_le_plus : forall (A B:Type) (m:M A) (F:A -> M B),
   le_plus m ->
   (forall a:A, forall f g, fplusok f g -> (F a f) <= Uinv (F a g))
   -> (forall a:A, le_plus (F a)) -> le_plus  (star m F).
unfold le_plus in |- *; intros.
unfold star in |- *; simpl.
apply Ole_trans with (m (fplus (fun x:A => F x f) (fun x:A => F x g))); trivial.
apply H.
red;intro x; unfold finv; intros; auto.
apply (fmonotonic m).
simpl; unfold fplus at 1; auto.
Qed.

(** *** Stability for product *)
Lemma unit_stable_mult : forall (A:Type) (x:A), stable_mult (unit x).
red in |- *; intros.
unfold unit in |- *; auto.
Qed.

Lemma star_stable_mult : forall (A B:Type) (m:M A) (F:A -> M B),
   stable_mult m -> (forall a:A, stable_mult (F a)) -> stable_mult (star m F).
unfold stable_mult in |- *; intros.
unfold star in |- *; simpl.
apply Oeq_trans with (m (fmult k (fun x:A => F x f))); trivial.
apply (fmon_stable m).
simpl; apply ford_eq_intro; intro.
unfold fmult at 2 in |- *; trivial.
Qed.

(** *** Continuity *)

Lemma unit_continuous : forall (A:Type) (x:A), continuous  (unit x).
red; unfold unit; intros; auto.
Save.

Lemma star_continuous : forall (A B : Type) (m : M A)(F: A -> M B),
    continuous m -> (forall x, continuous (F x)) -> continuous (star m F).
red; intros; simpl.
apply Ole_trans with (m (fun x => lub (F x @ h))).
apply (fmonotonic m); intro x.
apply (H0 x h); auto.
apply Ole_trans with (m (lub (c:=A-O->U) (ford_shift F @ h))); auto.
apply Ole_trans with (1:=H (ford_shift F @ h)); auto.
Save.


End Monad.
