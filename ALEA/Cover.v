(** * Cover.v: Characteristic functions *)
Require Export Prog.
Set Implicit Arguments.
Require Export Sets.
Require Export Arith.
Module CoverFun (Univ:Universe).

Module RP := (Rules Univ).
(* begin hide *)
Import Univ RP PP MP UP.
Open Local Scope U_scope.
Open Local Scope O_scope.
(* end hide *)

(** Properties of zero_one functions *)

Definition zero_one (A:Type)(f:MF A) := forall x, orc (f x == 0) (f x == 1).
Hint Unfold zero_one.

Lemma zero_one_not_one :
forall (A:Type)(f:MF A) x, zero_one f -> ~ 1 <= f x -> f x == 0.
intros; apply (H x); intros; auto.
absurd (1 <= f x); auto.
Save.

Lemma zero_one_not_zero :
forall (A:Type)(f:MF A) x, zero_one f -> ~ f x <= 0 -> f x == 1.
intros; apply (H x); intros; auto.
absurd (0 <= f x); auto.
Save.

Hint Resolve zero_one_not_one zero_one_not_zero.

Definition fesp_zero_one : forall (A:Type)(f g:MF A),
      zero_one f -> zero_one g ->  zero_one (fesp f g).
red; unfold fesp; intros; apply (H x); intros.
auto.
apply orc_left.
rewrite H1; auto.
apply (H0 x); intros.
auto.
apply orc_left.
rewrite H2; auto.
apply orc_right.
rewrite H1; rewrite H2; auto.
Save.

Lemma fesp_conj_zero_one : forall (A:Type)(f g:MF A),
      zero_one f -> fesp f g == fconj f g.
unfold fesp,fconj; intros; simpl; apply ford_eq_intro; intro x;
apply Uesp_zero_one_mult_left; auto.
Save.

Lemma fconj_zero_one : forall (A:Type)(f g:MF A),
      zero_one f -> zero_one g ->  zero_one (fconj f g).
red; unfold fconj; intros; apply (H x); intros.
auto.
apply orc_left.
rewrite H1; auto.
apply (H0 x); intros.
auto.
apply orc_left.
rewrite H2; auto.
apply orc_right.
rewrite H1; rewrite H2; auto.
Save.

Lemma fplus_zero_one : forall (A:Type)(f g:MF A),
      zero_one f -> zero_one g ->  zero_one (fplus f g).
red; unfold fplus; intros; apply (H x); intros.
auto.
apply (H0 x); intros.
auto.
apply orc_left.
rewrite H1; rewrite H2; auto.
apply orc_right.
rewrite H2; auto.
apply orc_right.
rewrite H1; auto.
Save.

Lemma finv_zero_one : forall (A:Type)(f :MF A),
      zero_one f -> zero_one (finv f).
red; unfold finv; intros; apply (H x); intros.
auto.
apply orc_right.
rewrite H0; auto.
apply orc_left.
rewrite H0; auto.
Save.

Lemma fesp_zero_one_mult_left : forall (A:Type)(f:MF A)(p:U),
      zero_one f -> forall x, f x & p == f x * p.
intros; apply Uesp_zero_one_mult_left; auto.
Save.

Lemma fesp_zero_one_mult_right : forall (A:Type)(p:U)(f:MF A),
     zero_one f -> forall x, p & f x == p * f x.
intros; apply Uesp_zero_one_mult_right; auto.
Save.
Hint Resolve fesp_zero_one_mult_left fesp_zero_one_mult_right.

(** ** Covering functions *)

Definition cover (A:Type)(P:set A)(f:MF A) :=
      forall x, (P x -> 1 <= f x)  /\ (~ P x -> f x <= 0).

Lemma cover_eq_one : forall (A:Type)(P:set A)(f:MF A) (z:A),
       cover P f -> P z -> f z == 1.
unfold cover; intros.
case (H z); intuition.
Save.

Lemma cover_eq_zero : forall (A:Type)(P:set A)(f:MF A) (z:A),
       cover P f -> ~ P z -> f z == 0.
unfold cover;intros.
case (H z); intuition.
Save.

Lemma cover_orc_0_1 : forall (A:Type)(P:set A)(f:MF A),
   cover P f -> forall x, orc (f x == 0) (f x == 1).
intros; apply (excluded_middle (A:=P x)); intros; auto.
apply orc_right; apply cover_eq_one with (P:=P) (f:=f); auto.
apply orc_left; apply cover_eq_zero with (P:=P) (f:=f); auto.
Save.

Lemma cover_zero_one : forall (A:Type)(P:set A)(f:MF A),
   cover P f -> zero_one f.
red; intros; apply cover_orc_0_1 with A P; trivial.
Save.

Lemma zero_one_cover : forall (A:Type)(f:MF A),
   zero_one f -> cover (fun x => 1 <= f x) f.
unfold zero_one,cover; intros; split; intros; auto.
apply (H x); intros; auto.
absurd (1 <= f x); auto.
Save.

Lemma cover_esp_mult_left : forall (A:Type)(P:set A)(f:MF A)(p:U),
      cover P f -> forall x, f x & p == f x * p.
intros; apply Uesp_zero_one_mult_left.
apply (cover_orc_0_1 H x).
Save.

Lemma cover_esp_mult_right : forall (A:Type)(P:set A)(p:U)(f:MF A),
     cover P f -> forall x, p & f x == p * f x.
intros; apply Uesp_zero_one_mult_right.
exact (cover_orc_0_1 H x).
Save.
Hint Immediate cover_esp_mult_left cover_esp_mult_right.

Lemma cover_elim : forall (A:Type)(P:set A)(f:MF A),
cover P f -> forall x, orc (~P x /\ f x == 0) (P x /\ f x == 1).
intros; apply (excluded_middle (A:=P x)); intros; auto.
apply orc_right; split; auto; apply cover_eq_one with (P:=P) (f:=f); auto.
apply orc_left; split; auto; apply cover_eq_zero with (P:=P) (f:=f); auto.
Save.


Lemma cover_eq_one_elim_class : forall (A:Type)(P Q:set A)(f:MF A),
       cover P f -> forall z, f z == 1 -> class (Q z) -> incl P Q -> Q z.
intros; apply (excluded_middle (A:=P z)); intros; auto.
case Udiff_0_1.
rewrite <- H0.
apply Oeq_sym; apply (cover_eq_zero (P:=P) (f:=f)); auto.
Save.

Lemma cover_eq_one_elim : forall (A:Type)(P:set A)(f:MF A),
       cover P f -> forall z, f z == 1 -> ~ ~ P z.
intros.
apply (cover_eq_one_elim_class (Q:=fun z => ~ ~ P z) H); auto.
red; auto.
Save.

Lemma cover_eq_zero_elim : forall (A:Type)(P:set A)(f:MF A) (z:A),
       cover P f -> f z == 0 -> ~ P z.
intros; apply (excluded_middle (A:=P z)); intros; auto.
case Udiff_0_1.
rewrite <- H0.
apply (cover_eq_one (P:=P) (f:=f)); auto.
Save.

Lemma cover_unit : forall (A:Type)(P:set A)(f:MF A)(a:A),
             cover P f -> P a -> 1 <= mu (Munit a) f.
simpl; unfold unit,cover; firstorder.
Save.


Lemma cover_let : forall (A B:Type)(m1: distr A)(m2: A->distr B) (P:set A)(cP:MF A)(f:MF B)(p:U),
     cover P cP -> 1 <= mu m1 cP -> (forall x:A, P x -> p <= mu (m2 x) f) -> p <= mu (Mlet m1 m2) f.
intros A B m1 m2.
simpl; unfold star; intuition.
apply Ole_trans with (mu m1 (fun x => p * (cP x))).
rewrite (mu_stable_mult m1 p cP).
apply Ole_trans with (p * 1); auto.
apply (mu_monotonic m1).
intro x.
apply (cover_elim (P:=P) (f:=cP) H x); auto; intros (Hp,cPeq).
rewrite cPeq; repeat Usimpl; auto.
rewrite cPeq; repeat Usimpl; auto.
Save.

Lemma cover_incl_fle : forall (A:Type)(P Q:set A)(f g:MF A),
      cover P f -> cover Q g -> incl P Q ->  f <= g.
intros; intro x.
apply (cover_elim H x); auto; intros (Hp,Hfeq).
rewrite Hfeq; auto.
rewrite (cover_eq_one x H0); auto.
Save.

Lemma cover_incl_eq: forall (A:Type)(P:set A)(f g:MF A),
      cover P f -> cover P g ->  f == g.
intros; apply Ole_antisym.
apply (cover_incl_fle H H0); auto.
apply (cover_incl_fle H0 H); auto.
Save.

Lemma cover_equiv_stable : forall (A:Type)(P Q:set A)(EQ : equiv P Q)(f:MF A),
      cover P f -> cover Q f.
unfold cover; firstorder.
Save.

Lemma cover_eq_stable : forall (A:Type)(P:set A)(f g:MF A),
      cover P f -> f == g -> cover P g.
unfold cover; intros.
case (H x); case (ford_eq_elim H0 x); split; intros; apply Ole_trans with (f x); auto.
Save.

Lemma cover_equiv_eq_stable : forall (A:Type)(P Q:set A)(f g:MF A),
      cover P f -> equiv P Q -> f == g -> cover Q g.
intros; assert (cover P g).
apply cover_eq_stable with f; auto.
apply cover_equiv_stable with P; auto.
Save.

Add Parametric Morphism (A:Type) : (cover (A:=A))
with signature equiv (A:=A) ==> Oeq (O:=MF A) ==> iff as cover_equiv_compat.
intuition.
apply cover_equiv_eq_stable with x x0; auto.
apply cover_equiv_eq_stable with y y0; auto.
Save.

Lemma cover_union : forall (A:Type)(P Q:set A)(f g : MF A),
     cover P f -> cover Q g -> cover (union P Q) (fplus f g).
unfold cover; intros.
case (H x); case (H0 x); unfold union,fplus; split; intros.
case H5; intro.
apply Ole_trans with (f x); auto.
apply Ole_trans with (g x); auto.
assert (~P x); try tauto.
assert (~Q x); try tauto.
apply Ole_trans with (0+0); auto.
apply Uplus_le_compat; auto.
Save.

Lemma cover_inter_esp : forall (A:Type)(P Q:set A)(f g : MF A),
      cover P f -> cover Q g -> cover (inter P Q) (fesp f g).
unfold cover; intros.
case (H x); case (H0 x); unfold inter,fesp; split; intros.
case H5; intros.
apply Ole_trans with (1&1); auto.
apply Uesp_le_compat; auto.
assert (orc (~ P x) (~ Q x)); auto.
apply orc_intro; tauto.
apply H6; auto; intro.
apply Ole_trans with (f x); auto.
apply Ole_trans with (g x); auto.
Save.

Lemma cover_inter_mult : forall (A:Type)(P Q:set A)(f g : MF A),
      cover P f -> cover Q g -> cover (inter P Q) (fun x => f x * g x).
unfold cover; intros.
case (H x); case (H0 x); unfold inter; split; intros.
case H5; intros.
apply Ole_trans with (1*1); auto.
apply Umult_le_compat; auto.
assert (orc (~ P x) (~ Q x)); auto.
apply orc_intro; tauto.
apply H6; auto; intro.
apply Ole_trans with (f x); auto.
apply Ole_trans with (g x); auto.
Save.

Lemma cover_compl : forall (A:Type)(P:set A)(f:MF A),
      cover P f -> cover (compl P) (finv f).
unfold cover; intros.
case (H x); unfold compl,finv; split; intros.
apply Ole_trans with ([1-]0); auto.
apply Ole_trans with ([1-]1); auto.
apply Uinv_le_compat.
apply class_double_neg with (P x); auto.
Save.

Lemma cover_empty : forall (A:Type), cover (empty A) (fzero A).
red; unfold fzero; intuition.
case H.
Save.

(** * Caracteristic functions *)

Definition carac  (A:Type)(P:set A)(Pdec : dec P) : MF A
      := fun z => if Pdec z then 1 else 0.

Lemma carac_incl: forall (A:Type)(P Q:A -> Prop)(Pdec: dec P)(Qdec: dec Q),
                                incl P Q -> carac Pdec <= carac Qdec.
intros; intro x; unfold carac.
case (Pdec x); case (Qdec x); intuition.
absurd (Q x); intuition.
Save.

Lemma carac_monotonic : forall (A B:Type)(P:A -> Prop)(Q:B->Prop)(Pdec: dec P)(Qdec: dec Q) x y,
                                (P  x -> Q y) -> carac Pdec x <= carac Qdec y.
intros; unfold carac; case (Pdec x); intros; auto.
case (Qdec y); intros; auto.
absurd (Q y); auto.
Save.
Hint Resolve carac_monotonic.

Lemma carac_eq_compat : forall (A B:Type)(P:A -> Prop)(Q:B->Prop)(Pdec: dec P)(Qdec: dec Q) x y,
                                (P  x <-> Q y) -> carac Pdec x == carac Qdec y.
intros; apply Ole_antisym; intuition.
Save.
Hint Resolve carac_eq_compat.

Lemma carac_one : forall (A:Type)(P:A -> Prop)(Pdec:dec P)(z:A),
       P z -> carac Pdec z == 1.
unfold carac; intros; case (Pdec z); intuition.
Save.

Lemma carac_zero : forall (A:Type)(P:A -> Prop)(Pdec:dec P)(z:A),
       ~ P z -> carac Pdec z == 0.
unfold carac; intros; case (Pdec z); intuition.
Save.

Lemma cover_dec : forall (A:Type)(P:set A)(Pdec : dec P), cover P (carac Pdec).
red; unfold carac; intros.
case (Pdec x); intuition.
Save.

Lemma cover_mult_fun : forall (A:Type)(P:set A)(cP : MF A)(f g:A->U),
  (forall x, P x -> f x == g x) -> cover P cP -> forall x, cP x * f x == cP x * g x.
intros.
apply (cover_elim H0 x); auto; intuition.
rewrite H3; repeat Usimpl; auto.
Save.

Lemma cover_esp_fun : forall (A:Type)(P:set A)(cP : MF A)(f g:A->U),
  (forall x, P x -> f x == g x) -> cover P cP -> forall x, cP x & f x == cP x & g x.
intros.
apply (cover_elim H0 x); auto; intuition.
rewrite H3; repeat Usimpl; auto.
rewrite H3; repeat Usimpl; auto.
Save.


Lemma cover_esp_fun_le : forall (A:Type)(P:set A)(cP : MF A)(f g:A->U),
  (forall x, P x -> f x <= g x) -> cover P cP -> forall x, cP x & f x <= cP x & g x.
intros.
apply (cover_elim H0 x); auto; intuition.
rewrite H3; repeat Usimpl; auto.
rewrite H3; repeat Usimpl; auto.
Save.
Hint Resolve cover_esp_fun_le.

Lemma cover_ok : forall (A:Type)(P Q:set A)(f g : MF A),
        (forall x, P x -> ~ Q x) -> cover P f -> cover Q g -> fplusok f g.
red; red; intros.
intro x; unfold finv.
apply (cover_elim H0 x); auto; intuition.
rewrite H4; auto.
apply (cover_elim H1 x); auto; intuition.
rewrite H6; auto.
case (H x H3 H5).
Save.
Hint Resolve cover_ok.

(** * Conditional probabilities *)

Definition mcond A (m:M A) (f:MF A) : M A.
intros; exists (fun g => (m (fconj f g)) / m f).
red; intros g h legh.
apply Udiv_le_compat_left.
apply (fmonotonic m); unfold fconj; intros; auto.
Defined.

Lemma mcond_simpl : forall A (m:M A) (f g: MF A),
      mcond m f g = m (fconj f g) / m f.
trivial.
Save.

Lemma mcond_stable_plus : forall A (m:distr A) (f: MF A), stable_plus (mcond (mu m) f).
red; intros.
repeat rewrite mcond_simpl.
simpl; rewrite <- Udiv_plus.
apply Udiv_eq_compat_left.
assert (fplusok (fconj f f0) (fconj f g)).
auto.
rewrite <- (mu_stable_plus m H0).
apply (mu_stable_eq m).
simpl; apply ford_eq_intro; intro x; unfold fconj,fplus; auto.
apply Udistr_plus_left; auto.
apply (H x).
Save.

Lemma mcond_stable_inv : forall A (m:distr A) (f: MF A), stable_inv (mcond (mu m) f).
red; intros.
repeat rewrite mcond_simpl.
apply (Ueq_orc 0 (mu m f)); intro.
auto.
rewrite (Udiv_by_zero (mu m (fconj f (finv f0))) (y:=mu m f)); auto.
apply Ole_trans with (mu m (fminus f (fconj f f0)) / mu m f).
apply Udiv_le_compat_left.
apply (mu_monotonic m).
intro x; unfold fconj,finv,fminus; auto.
rewrite stable_minus_distr; trivial.
rewrite Udiv_minus; trivial.
Save.

Lemma mcond_stable_mult : forall A (m:distr A) (f: MF A), stable_mult (mcond (mu m) f).
red; intros.
repeat rewrite mcond_simpl.
rewrite <- Umult_div_assoc.
apply Udiv_eq_compat_left.
apply Oeq_trans with (mu m (fmult k (fconj f f0))).
apply (mu_stable_eq m).
simpl; apply ford_eq_intro; unfold fconj, fmult; intro; auto.
apply (mu_stable_mult m).
apply (mu_monotonic m); auto.
apply fle_fconj_left.
Save.

Lemma mcond_continuous : forall A (m:distr A) (f: MF A), continuous (mcond (mu m) f).
red; intros.
repeat rewrite mcond_simpl.
apply (Ueq_orc 0 (mu m f)); intro; auto.
rewrite (Udiv_by_zero (mu m (fconj f (lub (c:=A -O-> U) h))) (y:=mu m f)); auto.
apply Umult_div_le_right.
apply Ole_trans with (mu m (lub (c:=A -O-> U) ((Fconj A f)@h))).
apply mu_monotonic.
apply (continuous2_app (F:=Fconj A) (fconj_continuous2 (A:=A))  f h).
rewrite (mu_continuous m).
rewrite <- (lub_comp_le (UMult <_> (mu m f)) (mcond (mu m) f @ h) ).
apply (lub_le_compat (D:=U)).
intro x; simpl.
rewrite Udiv_mult; auto.
apply (mu_monotonic m); auto.
apply fle_fconj_left.
Save.


Definition Mcond A (m:distr A) (f:MF A) : distr A :=
   Build_distr (mcond_stable_inv m f) (mcond_stable_plus m f)
               (mcond_stable_mult m f) (mcond_continuous m f).

(** ** Assuming m is a distribution under assumption P and cP is 0 or 1, builds
     a distribution which is m if cP is 1 and 0 otherwise *)

Definition Mrestr A (cp:U) (m:M A) : M A := UMult cp @ m.

Lemma Mrestr_simpl : forall A cp (m:M A) f, Mrestr cp m f = cp * (m f).
trivial.
Save.

Lemma Mrestr0 : forall A cP (m:M A), cP <= 0 -> forall f, Mrestr cP m f == 0.
intros.
apply Ule_zero_eq; apply Ole_trans with cP;auto.
Save.

Lemma Mrestr1 : forall A cP (m:M A), 1 <= cP -> forall f, Mrestr cP m f == m f.
intros.
assert (H1:cP==1); auto.
rewrite Mrestr_simpl; rewrite H1; auto.
Save.

Definition distr_restr : forall  A (P:Prop) (cp:U) (m:M A),
     ((P  -> 1 <= cp) /\ (~ P -> cp <= 0)) -> (P -> stable_inv m) ->
     (P -> stable_plus m) -> (P -> stable_mult m) -> (P -> continuous m)
     -> distr A.
intros A P cp m HP minv mplus mmult mcont.
exists (Mrestr cp m); case HP; intros P1 P0; red; intros; apply (excluded_middle (A:=P)); auto; intros.
repeat rewrite Mrestr1; auto.
apply minv; trivial.
repeat rewrite Mrestr0; auto.
repeat rewrite Mrestr1; auto.
apply mplus; trivial.
repeat rewrite Mrestr0; auto.
repeat rewrite Mrestr1; auto.
apply mmult; trivial.
repeat rewrite Mrestr0; auto.
repeat rewrite Mrestr1; auto.
rewrite (mcont H h); trivial.
apply lub_le_compat; intro n.
repeat rewrite fmon_comp_simpl.
repeat rewrite Mrestr1; auto.
repeat rewrite Mrestr0; auto.
Defined.

Lemma distr_restr_simpl : forall  A (P:Prop) (cp:U) (m:M A)
     (Hp: (P  -> 1 <= cp) /\ (~ P -> cp <= 0)) (Hinv:P -> stable_inv m)
     (Hplus:P -> stable_plus m)(Hmult:P -> stable_mult m)(Hcont:P -> continuous m) f,
     mu (distr_restr cp Hp Hinv Hplus Hmult Hcont) f = cp * m f.
trivial.
Save.


(** ** Modular reasoning on programs *)

Lemma range_cover : forall A (P:A -> Prop) d cP, range P d -> cover P cP ->
   forall f, mu d f == mu d (fun x => cP x * f x).
intros; apply range_eq with (P:=P); auto; intros.
rewrite (cover_eq_one a H0); auto.
Save.

Lemma mu_cut : forall (A:Type)(m:distr A)(P:set A)(cP f g:MF A),
  cover P cP -> (forall x, P x -> f x == g x) -> 1<=mu m cP -> mu m f == mu m g.
intros; apply Oeq_trans with (mu m (fesp cP f)).
apply (mu_esp_one m cP f); auto.
intros; apply Oeq_trans with (mu m (fesp cP g)).
apply mu_stable_eq.
simpl; apply ford_eq_intro; intro x; unfold fesp;
   apply (cover_esp_fun (P:=P) (cP:=cP)); auto.
apply Oeq_sym; apply (mu_esp_one m cP g); auto.
Save.

(** ** Conditional probabilities *)

(** ** Uniform measure on finite sets *)

Section SigmaFinite.
Variable A:Type.
Variable decA : forall x y:A, {x=y}+{~x=y}.

Section RandomFinite.

(** *** Distribution for [random_fin P] over $\{k:nat | k \leq n\}$
The distribution associated to [random_fin P] is
       $f \mapsto \Sigma_{a\in P} \frac{f(a)}{n+1}$
       with $n+1$ the size of $P$
       we cannot factorize $\frac{1}{n+1}$ because of possible overflow *)

Fixpoint sigma_fin (f:A->U)(P:A->Prop)(FP:finite P){struct FP}:U :=
match FP with
  | (fin_eq_empty eq) => 0
  | (fin_eq_add x Q nQx FQ eq) => (f x) + sigma_fin f FQ
end.

Definition retract_fin (P:A->Prop) (f:A->U) :=
     forall Q (FQ: finite Q), incl Q P -> forall x, ~(Q x) -> (P x) -> f x <= [1-](sigma_fin f FQ).

Lemma retract_fin_inv :
     forall (P:A->Prop) (f:A->U),
              retract_fin P f -> forall Q (FQ: finite Q), incl Q P -> forall x, ~(Q x) -> (P x) -> sigma_fin f FQ <=[1-]f x.
intros; apply Uinv_le_perm_right; auto.
Save.

Hint Immediate retract_fin_inv.

Lemma retract_fin_incl : forall P Q f, retract_fin P f -> incl Q P -> retract_fin Q f.
unfold retract_fin; intros.
apply (H Q0 FQ); auto.
apply incl_trans with Q; auto.
Save.

Lemma sigma_fin_monotonic : forall (f g : A -> U)(P:A->Prop)(FP:finite P),
       (forall x, P x -> (f x)<=(g x))-> sigma_fin f FP <= sigma_fin g FP.
induction FP; simpl; intros; auto.
apply Ole_trans with (f x + sigma_fin g FP); repeat Usimpl.
apply IHFP.
intros; case (e x0); unfold add in *; intuition.
apply H; case (e x); unfold add in *; intuition.
Save.

Lemma sigma_fin_eq_compat :
forall (f g : A -> U)(P:A->Prop)(FP:finite P),
       (forall x, P x -> (f x)==(g x))-> sigma_fin f FP == sigma_fin g FP.
intros; apply Ole_antisym; apply sigma_fin_monotonic; auto.
intros; rewrite (H x); auto.
Save.


Lemma retract_fin_le : forall (P:A->Prop) (f g:A->U),
        (forall x, P x -> f x <= g x) -> retract_fin P g -> retract_fin P f.
unfold retract_fin; intros.
apply Ole_trans with (g x); auto.
apply Ole_trans with ([1-] sigma_fin g FQ); auto.
apply Uinv_le_compat.
apply sigma_fin_monotonic; auto.
Save.

Lemma sigma_fin_mult : forall (f : A -> U) c (P:A->Prop)(FP:finite P),
       retract_fin P f -> sigma_fin (fun k  => c * f k) FP == c * sigma_fin f FP.
induction FP; simpl; intros.
repeat Usimpl; auto.
assert (incl Q P).
apply incl_trans with (add x Q); auto.
rewrite Udistr_plus_left; auto.
(* apply H; auto.*)
(*case (e x); intuition.*)
rewrite IHFP; auto.
apply retract_fin_incl with P; auto.
apply H; auto.
case (e x); intuition.
Save.

Lemma sigma_fin_plus : forall (f g: A -> U) (P:A->Prop)(FP:finite P),
       sigma_fin (fun k  => f k + g k) FP == sigma_fin f FP + sigma_fin g FP.
induction FP; simpl; intros.
repeat Usimpl; auto.
rewrite IHFP.
repeat norm_assoc_left; repeat Usimpl.
repeat norm_assoc_right; repeat Usimpl; auto.
Save.

Lemma sigma_fin_prod_maj :
forall (f g : A -> U)(P:A->Prop)(FP:finite P),
       sigma_fin (fun k  => f k * g k) FP <= sigma_fin f FP.
induction FP; simpl; auto.
Save.

Lemma sigma_fin_prod_le :
forall (f g : A -> U) (c:U) , (forall k, f k <= c) -> forall (P:A->Prop)(FP:finite P),
   retract_fin P g -> sigma_fin (fun k  => f k * g k) FP <= c * sigma_fin g FP.
induction FP; simpl; intros.
repeat Usimpl; auto.
assert (incl Q P).
apply incl_trans with (add x Q); auto.
assert (retract_fin Q g).
apply retract_fin_incl with P; auto.
apply Ole_trans with ((f x) * (g x) + (c * sigma_fin g FP)); auto.
apply Ole_trans with ( c * (g x) + (c * sigma_fin g FP)); auto.
rewrite Udistr_plus_left; auto.
case (e x); intuition.
Save.

Lemma sigma_fin_prod_ge :
forall (f g : A -> U) (c:U) , (forall k, c <= f k) -> forall (P:A->Prop)(FP:finite P),
   retract_fin P g -> c * sigma_fin g FP <= sigma_fin (fun k  => f k * g k) FP.
induction FP; simpl; intros.
repeat Usimpl; auto.
assert (incl Q P).
apply incl_trans with (add x Q); auto.
assert (retract_fin Q g).
apply retract_fin_incl with P; auto.
apply Ole_trans with ((f x) * (g x) + (c * sigma_fin g FP)); auto.
apply Ole_trans with ( c * (g x) + (c * sigma_fin g FP)); auto.
case (e x); intuition.
Save.
Hint Resolve sigma_fin_prod_maj sigma_fin_prod_ge sigma_fin_prod_le.

Lemma sigma_fin_inv : forall (f g : A -> U)(P:A->Prop)(FP:finite P),
       retract_fin P f ->
       [1-] sigma_fin (fun k  => f k * g k) FP ==
       sigma_fin (fun k => f k * [1-] g k) FP + [1-] sigma_fin f FP.
induction FP; simpl.
repeat Usimpl; auto.
intro.
assert (incl Q P).
apply incl_trans with (add x Q); auto.
assert (retract_fin Q f).
apply retract_fin_incl with P; auto.
assert (px:P x).
case (e x); intuition.

apply Uplus_eq_simpl_right with ((f x) * (g x)).
repeat Usimpl; auto.

apply Uinv_le_perm_right.
rewrite (Udistr_inv_left (f x) (g x)).
repeat norm_assoc_right; apply Uplus_le_compat_right.
apply Ole_trans with
  (sigma_fin f FP + [1-] (f x + sigma_fin f FP)); repeat Usimpl.
apply (sigma_fin_prod_maj f (fun k => [1-](g k)) FP).

assert (sigma_fin f FP <= [1-] (f x)).
apply Uinv_le_perm_right; auto.
rewrite <- (Uinv_plus_right _ _ H2); auto.

assert (sigma_fin (fun k => f k * g k) FP <= [1-] (f x * g x)).
apply Ole_trans with (sigma_fin f FP); auto.

apply Ole_trans with ([1-] (f x)); auto.
apply Uinv_le_perm_right; auto.
rewrite (Uinv_plus_left _ _ H2).
apply Oeq_trans with (1:=IHFP H1).
rewrite (Uplus_sym (f x * [1-] (g x))
                          (sigma_fin (fun k  => f k * [1-] (g k)) FP)).
repeat norm_assoc_right;apply Uplus_eq_compat_right.
setoid_rewrite (Uplus_sym  ([1-] (f x + sigma_fin f FP)) (f x * g x)).
repeat norm_assoc_left.
assert ([1-] (g x) <= [1-] (g x)); auto.

rewrite <- (Udistr_plus_left (f x) _ _ H3).
rewrite (Uinv_opp_left (g x)).
rewrite (Umult_one_right (f x)); auto.
rewrite (Uplus_sym (f x) ([1-] (f x + sigma_fin f FP))).
apply Oeq_sym; apply Uinv_plus_left; auto.
apply Uinv_le_perm_right; auto.
Save.

Lemma sigma_fin_equiv : forall f P Q  (FP:finite P) (e:equiv P Q),
    (sigma_fin f (fin_equiv e FP)) = (sigma_fin f FP).
induction FP; simpl; intros; auto.
Save.

Lemma sigma_fin_rem : forall f P (FP:finite P) a,
             P a -> sigma_fin f FP == f a + sigma_fin f (finite_rem decA a FP).
induction FP;  intuition.
case (equiv_empty_false a e);auto.
simpl; case (decA x a); simpl; intros.
case e0; unfold eq_rect_r;simpl; auto.
rewrite sigma_fin_equiv; auto.
rewrite (IHFP a); auto.
case (e a); unfold add; intuition.
case f0; auto.
Save.

Lemma sigma_fin_incl : forall f P (FP:finite P) Q (FQ:finite Q),
              (incl P Q) -> sigma_fin f FP <= sigma_fin f FQ.
induction FP; simpl; intros; auto.
destruct FQ; simpl; intros.
case incl_add_empty with (a:=x) (P:=Q).
apply incl_trans with Q0; auto.
apply incl_trans with P; auto.
case (decA x x0); intro.
(* case x=x0*)
subst; Usimpl; auto.
apply IHFP.
apply incl_trans with (rem x0 P); auto.
apply incl_add_rem; auto.
apply incl_trans with (rem x0 Q0); auto.
rewrite incl_rem_add_iff; auto.
(* Case x<>x0 *)
rewrite (sigma_fin_rem f FQ x).
(*
assert (P x).
red in e; rewrite e; auto.
assert (Q0 x);auto.
assert (Q1 x);auto.
case (e0 x); intuition.
case H4; intuition.*)
repeat norm_assoc_left.
rewrite (Uplus_sym (f x0) (f x)).
repeat norm_assoc_right.
Usimpl.
assert (H3:~(rem x Q1 x0)).
unfold rem; intuition.
assert (incl Q (add x0 (rem x Q1))).
red; intros; case (e0 x1); clear e0; intuition.
case (e x1); clear e; intuition.
generalize (H x1); clear H; intuition.
unfold add,rem in *; intuition.
subst; intuition.
case (decA x1 x0); intuition; subst; intuition.
case (decA x1 x); intuition; subst; intuition.
exact (IHFP (add x0 (rem x Q1)) (fin_eq_add H3 (finite_rem decA x FQ) (equiv_refl (add x0 (rem x Q1)))) H0).
assert (P x).
red in e; rewrite e; auto.
assert (Q0 x);auto.
assert (Q1 x);auto.
case (e0 x); intuition.
case H4; intuition.
Save.

Lemma sigma_fin_unique : forall f P Q (FP:finite P) (FQ:finite Q), (equiv P Q) -> sigma_fin f FP == sigma_fin f FQ.
intros; apply Ole_antisym.
apply sigma_fin_incl; auto.
apply sigma_fin_incl; auto.
Save.

Lemma sigma_fin_cte : forall c P (FP:finite P),
       sigma_fin (fun _ => c) FP == (size FP) */ c.
induction FP; auto.
simpl sigma_fin; simpl size; rewrite IHFP; auto.
Save.

(*
Lemma sigma_fin_continuous : forall P (FP:finite P),
             continuous (fun f : fcpo A U => sigma_fin f FP).
red; intros.
induction FP; auto.
simpl sigma_fin.
apply Ole_trans with
(lub (fun n0 : nat => h n0 x) + lub (fun n : nat => sigma_fin (h n) FP)); auto.
red in H; rewrite lub_eq_plus; auto.
intro y; apply H.
intro y; apply sigma_fin_monotonic; intros; apply H.
Save.


(** *** Definition and Properties of [random_fin] *)

Variable P : A->Prop.
Variable FP : finite P.
Let s:= (size FP - 1)%nat.
Lemma pred_size_le : (size FP <=S s)%nat.
unfold s; omega.
Save.
Hint Resolve pred_size_le.


Lemma pred_size_eq : notempty P -> size FP =S s.
destruct FP; intros; simpl.
unfold notempty in *; contradiction.
unfold s; simpl; omega.
Save.

Definition random_fin :M A := fun (f:A->U) => sigma_fin (fun k => Unth s *  f k) FP.

Lemma fnth_retract_fin:
       forall n, (size FP<=S n)%nat -> (retract_fin P (fun _ => [1/]1+n)).
red; intros.
rewrite sigma_fin_cte.
apply Ole_trans with ([1-] (n */ [1/]1+n)); auto.
apply Uinv_le_compat.
apply Nmult_le_compat_left.
apply le_trans with (size (finite_rem decA x FP)); auto.
apply size_incl; auto.
unfold incl, rem; intuition.
subst; intuition.
apply le_S_n.
apply le_trans with (size FP); auto.
rewrite (size_finite_rem decA x FP); auto.
Save.

Lemma random_fin_stable_inv : stable_inv random_fin.
unfold random_fin, stable_inv, finv; intros; auto.
rewrite (@sigma_fin_inv (fun k => [1/]1+s) f P FP); auto.
apply fnth_retract_fin; trivial.
Save.

Lemma random_fin_stable_plus : stable_plus random_fin.
unfold random_fin, stable_plus, fplus; intros; auto.
unfold fplusok, fle, finv in H.
apply Oeq_trans with
 (sigma_fin (fun k => ([1/]1+s * f k) + ([1/]1+s  * g k)) FP).
apply sigma_fin_eq_compat; intros; auto.
apply sigma_fin_plus with (f:=fun k => Unth s * f k)
                      (g:=fun k => Unth s * g k); auto.
Save.

Lemma random_fin_stable_mult : stable_mult random_fin.
unfold random_fin, stable_mult, fmult; intros; auto.
apply Oeq_trans with  (sigma_fin (fun l => k * ([1/]1+s * f l)) FP).
apply sigma_fin_eq_compat; intros; auto.
apply sigma_fin_mult with (f:=fun k  => Unth s * f k).
apply retract_fin_le with (fun (k:A) => [1/]1+s); auto.
apply fnth_retract_fin; auto.
Save.

Lemma random_fin_monotonic : monotonic random_fin.
unfold monotonic, random_fin; intros.
red in H.
apply sigma_fin_monotonic; auto.
Save.

Lemma random_fin_continuous : continuous random_fin.
unfold random_fin, continuous; intros.
apply Ole_trans with
   (sigma_fin (lub (c:=fcpo A U) (fun n => fmult ([1/]1+s) (h n))) FP).
apply sigma_fin_monotonic; intros.
simpl; rewrite <- lub_eq_mult; auto.
apply sigma_fin_continuous with (h:=fun n : nat => fmult ([1/]1+s) (h n)); auto.
intros y z; unfold fmult.
Usimpl; apply H.
Save.


Definition Random_fin : (distr A).
exists random_fin.
apply random_fin_stable_inv; trivial.
apply random_fin_stable_plus.
apply random_fin_stable_mult; trivial.
apply random_fin_monotonic.
apply random_fin_continuous.
Defined.

Lemma random_fin_total : notempty P -> mu Random_fin (fone A) == 1.
intros; simpl; unfold random_fin.
unfold fone.
apply Oeq_trans with  (sigma_fin (fun k =>  [1/]1+s) FP).
apply sigma_fin_eq_compat.
intros; repeat Usimpl; auto.
rewrite sigma_fin_cte.
rewrite pred_size_eq; auto.
Save.
End RandomFinite.

Lemma random_fin_cover :
    forall P Q (FP:finite P) (decQ:dec Q),
         mu (Random_fin FP) (cover decQ) == size (finite_inter decQ FP) */ [1/]1+(size FP-1)%nat.
intros; simpl mu.
unfold random_fin.
pattern P at 1 3 4 5, FP at 2 3.
elim FP; intros; auto.
simpl sigma_fin.
unfold cover at 1.
rewrite H.
case (decQ x); intro.
rewrite size_inter_add_in; auto.
rewrite Nmult_S; auto.
repeat Usimpl; rewrite size_inter_add_notin; auto.
Save.

Lemma random_fin_P : forall P (FP:finite P) (decP:dec P),
         notempty P -> mu (Random_fin FP) (cover decP) ==1.
intros; rewrite random_fin_cover.
rewrite (size_inter_incl decA decP FP FP); auto.
pattern (size FP) at 1; rewrite pred_size_eq; auto.
Save.
*)
End RandomFinite.

End SigmaFinite.

(** ** Properties of the Random distribution *)
Definition le_dec (n:nat) : dec (fun x => (x <= n)%nat).
red; intros; case (le_lt_dec x n); intuition.
Defined.

Definition lt_dec (n:nat) : dec (fun x => (x < n)%nat).
red; intros; case (le_lt_dec n x); intuition.
Defined.

Definition gt_dec : forall x, dec (lt x).
intros x y; case (le_lt_dec y x); auto with arith.
Defined.

Definition ge_dec : forall x, dec (le x).
intros x y; case (le_lt_dec x y); auto with arith.
Defined.

Definition carac_le n := carac (le_dec n).
Definition carac_lt n := carac (lt_dec n).
Definition carac_gt n := carac (gt_dec n).
Definition carac_ge n := carac (ge_dec n).

Definition is_le (n:nat) : cover (fun x => (x <=n)%nat) (carac_le n) := cover_dec (le_dec n).
Definition is_lt (n:nat) : cover (fun x => (x < n)%nat) (carac_lt n) := cover_dec (lt_dec n).
Definition is_gt (n:nat) : cover (fun x => (n < x)%nat) (carac_gt n):= cover_dec (gt_dec n).
Definition is_ge (n:nat) : cover (fun x => (n <= x)%nat) (carac_ge n) := cover_dec (ge_dec n).

(** count the number of elements between 0 and n-1 which satisfy P *)
Fixpoint nb_elts (P:nat -> Prop)(Pdec : dec P)(n:nat) {struct n} : nat :=
match n with
   0 => 0%nat
  | S n => if Pdec n then (S (nb_elts Pdec n)) else (nb_elts Pdec n)
end.

Lemma nb_elts_true : forall  (P:nat -> Prop)(Pdec : dec P)(n:nat),
        (forall k, (k < n)%nat -> P k) -> nb_elts Pdec n =n.
induction n; simpl; intros; auto.
case (Pdec n); intros; auto with arith.
absurd (P n); auto with arith.
Save.
Hint Resolve nb_elts_true.

(** - the probability for a random number between 0 and n to satisfy P is equal
     to the number of elements below n which satisfy P divided by n+1 *)

Lemma Random_carac : forall (P:nat -> Prop)(Pdec : dec P)(n:nat),
    mu (Random n) (carac Pdec) == (nb_elts Pdec (S n)) */ [1/]1+n.
simpl mu.
unfold random,fnth; intros.
elim (S n); simpl; intros;auto.
rewrite H; unfold carac;case (Pdec n0); Usimpl; auto.
Qed.

Lemma nb_elts_lt_le : forall k n, (k <= n)%nat -> nb_elts (lt_dec k) n = k.
intros k n H; induction H; intros; auto with arith.
simpl.
case (lt_dec k m); intros; auto with arith.
absurd ((m<k)%nat); auto with arith.
Save.

Lemma nb_elts_lt_ge : forall k n, (n <= k)%nat -> nb_elts (lt_dec k) n = n.
intros; auto with zarith.
Save.
Hint Resolve nb_elts_lt_ge nb_elts_lt_le.

Lemma Random_lt : forall n k, mu (Random n) (carac_lt k) == k */ [1/]1+n.
unfold carac_lt; intros; rewrite Random_carac.
case (le_ge_dec k (S n)); intros.
rewrite nb_elts_lt_le; auto.
rewrite nb_elts_lt_ge; auto.
apply Ole_antisym; auto.
apply Ole_trans with 1; auto.
Save.

Hint Resolve Random_lt.

Lemma Random_le : forall n k, mu (Random n) (carac_le k) == (S k) */ [1/]1+n.
intros; apply Oeq_trans with (mu (Random n) (carac_lt (S k))); auto.
apply (mu_stable_eq (Random n)); auto.
unfold carac_le,carac_lt.
simpl; apply ford_eq_intro; intro x.
apply carac_eq_compat; intuition.
Save.

Hint Resolve Random_le.

End CoverFun.
