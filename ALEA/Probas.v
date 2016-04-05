(** * Probas.v: The monad for distributions *)

Require Export Monads.
Set Implicit Arguments.
Module Proba (Univ:Universe).
Module MP := (Monad Univ).
(* begin hide *)
Import Univ.
Import MP.
Import MP.UP.
Open Local Scope U_scope.
Open Local Scope O_scope.

(* end hide *)
(** ** Definition of distribution
Distributions are monotonic measure functions such that
    - $\mu (1-f) \leq 1-\mu(f)$
    - $f \leq 1 -g \Ra \mu(f+g)=\mu(f)+\mu(g)$
    - $\mu(k\times f) = k \times \mu(f)$
    - $\mu(lub f_n) <= lub \mu(f_n)$
*)

Record distr (A:Type) : Type := 
  {mu : M A;
   mu_stable_inv : stable_inv mu; 
   mu_stable_plus : stable_plus mu;
   mu_stable_mult : stable_mult mu;
   mu_continuous : continuous mu}.

Hint Resolve mu_stable_plus mu_stable_inv mu_stable_mult mu_continuous.

(** ** Properties of measures *)

Lemma mu_monotonic : forall (A : Type)(m: distr A), monotonic (mu m).
intros; apply fmonotonic; auto.
Save.
Hint Resolve mu_monotonic.
Implicit Arguments mu_monotonic [A].

Lemma mu_stable_eq : forall (A : Type)(m: distr A), stable (mu m).
intros; apply fmon_stable; auto.
Save.
Hint Resolve mu_stable_eq.
Implicit Arguments mu_stable_eq [A].

Lemma mu_zero : forall (A : Type)(m: distr A), mu m (fzero A) == 0.
intros.
apply Oeq_trans with (mu m (fmult 0 (fzero A))); auto.
apply mu_stable_eq; unfold fmult; simpl; auto.
apply Oeq_trans with (0 * (mu m (fzero A))); auto.
apply mu_stable_mult; auto.
Save.
Hint Resolve mu_zero.

Lemma mu_one_inv : forall (A : Type)(m:distr A),
   mu m (fone A) == 1 -> forall f, mu m (finv f) == [1-] (mu m f).
intros; apply Ole_antisym.
apply (mu_stable_inv m f).
apply Uplus_le_simpl_left with (mu m f); auto.
setoid_rewrite (Uinv_opp_right (mu m f)).
apply Ole_trans with (mu m (fun x => (f x) + [1-] (f x))).
setoid_rewrite <- H; apply (mu_monotonic m); auto.
assert (H1 : fplusok f (finv f)).
red; unfold finv; intro x; auto.
setoid_rewrite <- (mu_stable_plus m H1); auto.
Save.
Hint Resolve mu_one_inv.

Lemma mu_fplusok : forall (A : Type)(m:distr A) f g, fplusok f g -> 
            mu m f <= [1-] mu m g.
intros; apply Ole_trans with (mu m (finv g)); auto.
apply (mu_stable_inv m g).
Save.
Hint Resolve mu_fplusok.

Lemma mu_le_minus : forall (A : Type)(m:distr A) (f g:MF A),
     mu m (fminus f g) <= mu m f.
intros; apply mu_monotonic; unfold fminus; auto.
Save.
Hint Resolve mu_le_minus.

Lemma mu_le_plus : forall (A : Type)(m:distr A) (f g:MF A),
     mu m (fplus f g) <= mu m f + mu m g.
intros; apply Ole_trans with (mu m (fplus (fminus f (fesp f g)) g)).
apply mu_monotonic.
unfold fplus,fminus,fesp; intros; auto. 
rewrite (mu_stable_plus m (f:=fminus f (fesp f g)) (g:=g)).
Usimpl; auto.
red; unfold fminus,fesp,finv; intro x; auto.
Save.
Hint Resolve mu_le_plus.

Lemma mu_cte : forall (A : Type)(m:(distr A)) (c:U),
   mu m (fcte A c) == c * mu m (fone A).
intros.
apply Oeq_trans with (mu m (fun x => c * 1)).
apply (mu_stable_eq m); simpl; auto.
unfold fone; rewrite <- (mu_stable_mult m c (fun x => 1)); auto.
Save.
Hint Resolve mu_cte.

Lemma mu_cte_le :   forall (A : Type)(m:distr A) (c:U), mu m (fcte A c) <= c.
intros; apply Ole_trans with (c * mu m (fone A)); auto.
Save.


Lemma mu_cte_eq : forall (A : Type)(m:distr A) (c:U),
   mu m (fone A) == 1 -> mu m (fcte A c) == c.
intros; apply Oeq_trans with (c * mu m (fone A)); auto.
Save.

Hint Resolve mu_cte_le mu_cte_eq.


Lemma mu_stable_mult_right : forall (A : Type)(m:distr A) (c:U) (f : MF A),
   mu m (fun x => (f x) * c) == (mu m f) * c.
intros; apply Oeq_trans with 
   (mu m (fun x => c * (f x))).
apply mu_stable_eq; simpl; auto.
apply Oeq_trans with (c * mu m f); auto.
exact (mu_stable_mult m c f).
Save.

Lemma mu_stable_minus : forall (A:Type) (m:distr A)(f g : MF A),
 g <= f -> mu m (fun x => f x - g x) == mu m f - mu m g.
intros; change (mu m (fminus f g) == mu m f - mu m g).
apply (stable_minus_distr (m:=mu m)); auto.
Save.

Lemma mu_inv_minus : 
forall (A:Type) (m:distr A)(f: MF A), mu m (finv f) == mu m (fone A) - mu m f.
intros; apply Oeq_trans with (mu m (fun x => fone A x - f x)).
apply (mu_stable_eq m); repeat red; unfold finv,fone; intros; auto.
apply mu_stable_minus; auto.
Save.


Lemma mu_stable_le_minus : forall (A:Type) (m:distr A)(f g : MF A),
 mu m f - mu m g <= mu m (fun x => f x - g x).
intros; apply Uplus_le_perm_left.
apply Ole_trans with (mu m (fun x => g x + (f x - g x))).
apply mu_monotonic; auto.
apply (mu_le_plus m g (fun x => f x - g x)).
Save.

Lemma mu_inv_minus_inv : forall (A:Type) (m:distr A)(f: MF A), 
     mu m (finv f) + [1-](mu m (fone A)) == [1-](mu m f).
intros; apply Uminus_eq_perm_right.
apply Uinv_le_compat.
apply (mu_monotonic m); unfold fone; auto.
unfold Uminus.
rewrite mu_inv_minus; repeat Usimpl.
unfold Uminus.
apply Uinv_eq_compat; auto.
Save.

Lemma mu_le_esp_inv : forall (A:Type) (m:distr A)(f g : MF A),
 ([1-]mu m (finv f)) & mu m g <= mu m (fesp f g).
intros; rewrite Uesp_sym.
apply Uplus_inv_le_esp; Usimpl.
apply Ole_trans with (mu m (fplus (fesp f g) (finv f))); auto.
apply (mu_monotonic m); unfold fplus, fesp,finv; simpl; intros.
rewrite Uesp_sym; auto.
Save.
Hint Resolve mu_le_esp_inv.

Lemma mu_stable_inv_inv : forall (A:Type) (m:distr A)(f : MF A),
             mu m f <= [1-] mu m (finv f).
intros; apply Ole_trans with (mu m (finv (finv f))).
apply (mu_monotonic m); auto.
intro x; unfold finv; auto.
apply (mu_stable_inv m); auto.
Save.
Hint Resolve  mu_stable_inv_inv.

Lemma mu_stable_div : forall (A:Type) (m:distr A)(k:U)(f : MF A),
          ~0==k -> f <= fcte A k -> mu m (fdiv k f) == mu m f / k.
intros; apply Umult_div_eq; auto.
rewrite Umult_sym.
rewrite <- (mu_stable_mult m k).
apply mu_stable_eq; simpl; apply ford_eq_intro; intro x.
unfold fmult,fdiv; apply Umult_div; auto.
apply (H0 x).
Save.

Lemma mu_stable_div_le : forall (A:Type) (m:distr A)(k:U)(f : MF A),
          ~0==k -> mu m (fdiv k f) <= mu m f / k.
intros; apply Umult_div_le_left; auto.
rewrite Umult_sym.
rewrite <- (mu_stable_mult m k).
apply mu_monotonic; intro x.
unfold fmult,fdiv; apply Umult_div_le; auto.
Save.

Lemma mu_le_esp : forall (A:Type) (m:distr A)(f g : MF A),
 mu m f & mu m g <= mu m (fesp f g).
intros; apply Ole_trans with (([1-]mu m (finv f)) & mu m g); auto.
Save.
Hint Resolve mu_le_esp.

Lemma mu_esp_one : forall (A:Type)(m:distr A)(f g:MF A),
   1<=mu m f -> mu m g == mu m (fesp f g).
intros; apply Ole_antisym.
apply Ole_trans with (mu m f & mu m g).
apply Ole_trans with (1 & mu m g); auto.
apply mu_le_esp with (f:=f) (g:=g).
apply mu_monotonic; unfold fesp;  intro x; auto.
Save.

Lemma mu_esp_zero : forall (A:Type)(m:distr A)(f g:MF A),
   mu m (finv f) <= 0 -> mu m g == mu m (fesp f g).
intros; apply Ole_antisym.
apply Ole_trans with (([1-](mu m (finv f))) & mu m g); auto.
apply Ole_trans with (1 & mu m g); auto.
apply Uesp_le_compat; auto.
apply Ole_trans with ([1-]0); auto.
apply mu_monotonic; unfold fesp;  intro x; auto.
Save.

Definition Distr (A:Type) : ord.
intro A; exists (distr A) (fun (f g : distr A) => mu f <= mu g); auto.
intros; apply Ole_trans with (mu y); auto.
Defined.

Lemma eq_distr_intro : 
        forall A (m1 m2:Distr A), (forall f, mu m1 f == mu m2 f) -> m1==m2.
intros; split; auto.
Save.

Lemma eq_distr_elim :  forall A (m1 m2:Distr A), m1==m2 -> forall f, mu m1 f == mu m2 f.
auto.
Save.
Hint Resolve eq_distr_intro eq_distr_elim.

Add Parametric Morphism (A : Type) : (mu (A:=A))
   with signature (Oeq (O:=Distr A)) ==> (Oeq (O:=A-o>U)) ==> (Oeq (O:=U))
as mu_eq_morphism.
intros; apply Oeq_trans with (mu x y0); auto.
apply mu_stable_eq; auto.
Save.

Add Parametric Morphism (A : Type) : (mu (A:=A))
   with signature (Ole (o:=Distr A)) ==> (Ole (o:=A-o>U)) ==> (Ole (o:=U))
as mu_le_morphism.
intros; apply Ole_trans with (mu x y0); auto.
Save.

(** ** Monadic operators for distributions *)
Definition Munit : forall A:Type, A -> Distr A.
intros A x.
exists (unit x).
apply unit_stable_inv.
apply unit_stable_plus.
apply unit_stable_mult.
apply unit_continuous.
Defined.

Definition Mlet : forall A B:Type, Distr A -> (A -> Distr B) -> Distr B.
intros A B mA mB.
exists (star (mu mA) (fun x => (mu (mB x)))).
apply star_stable_inv; auto.
apply star_stable_plus; auto.
apply star_stable_mult; auto.
apply star_continuous; auto.
Defined.

Lemma Mlet_simpl : forall (A B:Type) (m:Distr A) (M:A -> Distr B) (f:B->U),
     mu (Mlet m M) f = mu m (fun x => (mu (M x) f)).
trivial.
Save.


(** ** Operations on distributions *)


Lemma Munit_compat : forall A (x y : A), x=y -> Munit x == Munit y.
intros; subst; auto.
Save.

Lemma Mlet_le_compat : forall (A B : Type) (m1 m2:Distr A) (M1 M2 : A-o> Distr B), 
  m1 <= m2 -> M1<=M2 -> Mlet m1 M1 <= Mlet m2 M2.
unfold Mlet,star; simpl; intros A B m1 m2 M1 M2 Hm HM f.
apply Ole_trans with (mu m2 (fun x : A => mu (M1 x) f)); auto.
Save.
Hint Resolve Mlet_le_compat.

Definition MLet (A B : Type) : Distr A -m> (A-o>Distr B) -m> Distr B
               := le_compat2_mon (Mlet_le_compat (A:=A) (B:=B)).

Lemma MLet_simpl : forall (A B:Type) (m:Distr A) (M:A -> Distr B)(f:B->U),
     mu (MLet A B m M) f =mu m (fun x => mu (M x) f).
trivial.
Save.

Lemma Mlet_eq_compat : forall (A B : Type) (m1 m2:Distr A) (M1 M2 : A-o> Distr B), 
  m1 == m2 -> M1==M2 -> Mlet m1 M1 == Mlet m2 M2.
intros; apply Ole_antisym; auto.
Save.

Lemma Munit_eq : forall (A:Type) (q:A->U) x, mu (Munit x) q == q x.
trivial.
Save.

Lemma mu_le_compat : forall (A:Type) (m1 m2:Distr A),
  m1 <= m2 -> forall f g : A -o>U,  f <= g -> mu m1 f <= mu m2 g.
intros; apply Ole_trans with (mu m2 f); auto.
Save.

(** ** Properties of monadic operators *)
Lemma Mlet_unit : forall (A B:Type) (x:A) (m:A -> Distr B), Mlet (Munit x) m == m x.
auto.
Save.

Lemma Mext : forall (A:Type) (m:Distr A), Mlet m (fun x => Munit x) == m.
intros; apply eq_distr_intro; simpl; intros.
apply (mu_stable_eq m); simpl; apply ford_eq_intro; auto.
Save.

Lemma Mcomp : forall (A B C:Type) (m1: Distr A) (m2:A -> Distr B) (m3:B -> Distr C),
     Mlet (Mlet m1 m2) m3 == Mlet m1 (fun x:A => Mlet (m2 x) m3).
intros; apply eq_distr_intro; intros; simpl; trivial.
Save.

Lemma let_indep : forall (A B:Type) (m1:Distr A) (m2: Distr B) (f:MF B), 
       mu m1 (fun _ => mu m2 f) == mu m1 (fone A) * (mu m2 f).
intros; rewrite (mu_cte m1 (mu m2 f)); auto.
Save.


(** ** A specific distribution *)
Definition distr_null : forall A : Type, Distr A.
intro A; exists (fmon_cte (A -o> U) (0:U)); try red; auto.
Defined.

Lemma le_distr_null : forall (A:Type) (m : Distr A), distr_null A <= m.
red; intros.
unfold distr_null; simpl; auto.
Save.
Hint Resolve le_distr_null.

(** ** Scaling a distribution *)

Definition Mmult A (k:MF A) (m:M A) : M A.
intros;  exists (fun f => m (fun x => k x * f x)).
red; intros.
apply fmonotonic; intro z; auto.
Defined.

Lemma Mmult_stable_inv : forall A (k:MF A) (d:distr A), stable_inv (Mmult k (mu d)).
red; intros; simpl.
apply Ole_trans with (mu d (finv f)); auto.
apply Ole_trans with ([1-]mu d f); auto.
Save.

Lemma Mmult_stable_plus : forall A (k:MF A) (d:distr A), stable_plus (Mmult k (mu d)).
red; intros; simpl.
apply Oeq_trans with (mu d (fun x => k x * f x + k x * g x)).
apply (mu_stable_eq d).
simpl; apply ford_eq_intro; intro x; unfold fplus.
apply Udistr_plus_left; apply (H x).
apply (mu_stable_plus d (f:=fun x=> k x * f x) (g:=fun x => k x * g x)).
intro x; apply Ole_trans with (f x); auto.
apply Ole_trans with (finv g x); auto.
unfold finv; repeat Usimpl; auto.
Save.

Lemma Mmult_stable_mult : forall A (k:MF A) (d:distr A), stable_mult (Mmult k (mu d)).
red; intros; simpl.
apply Oeq_trans with (mu d  (fmult k0 (fun x : A => k x * f x))).
apply (mu_stable_eq d).
simpl; apply ford_eq_intro; intro x; unfold fmult; auto.
apply (mu_stable_mult d).
Save.

Lemma Mmult_continuous : forall A (k:MF A) (d:distr A), continuous (Mmult k (mu d)).
red; intros; simpl.
apply Ole_trans with (mu d (fun (x:A) => lub (UMult (k x) @ (h <o> x)))).
apply (mu_monotonic d); intros x; auto.
rewrite (mu_continuous d (ford_shift (fun x => UMult (k x) @ h <o> x))).
apply lub_le_compat; intro n; simpl; auto.
Save.

Definition distr_mult A (k:MF A) (d:distr A) : distr A.
intros; exists (Mmult k (mu d)).
apply Mmult_stable_inv.
apply Mmult_stable_plus.
apply Mmult_stable_mult.
apply Mmult_continuous.
Defined.

Definition Mdiv A (k:U) (m:M A) : M A := UDiv k @ m.

Lemma Mdiv_simpl : forall A k (m:M A) f, Mdiv k m f = m f / k.
trivial.
Save.

Lemma Mdiv_stable_inv : forall A (k:U) (d:distr A)(dk : mu d (fone A) <= k),
                stable_inv (Mdiv k (mu d)).
red; intros; repeat rewrite Mdiv_simpl.
apply (Ueq_orc 0 k); auto; intros.
repeat (rewrite Udiv_by_zero;auto).
assert (forall f, mu d f <= k).
intros; apply Ole_trans with (mu d (fone A)); auto.
apply Ole_trans with ((mu d (fone A) - mu d f) / k); auto.
Save.

Lemma Mdiv_stable_plus : forall A (k:U)(d:distr A), stable_plus (Mdiv k (mu d)).
red; intros; repeat rewrite Mdiv_simpl.
apply Oeq_trans with ((mu d f + mu d g)/k); auto.
apply Udiv_eq_compat_left; auto.
apply (mu_stable_plus d); trivial. 
Save.

Lemma Mdiv_stable_mult : forall A (k:U)(d:distr A)(dk : mu d (fone A) <= k), 
                          stable_mult (Mdiv k (mu d)).
red; intros; repeat rewrite Mdiv_simpl.
apply (Ueq_orc 0 k); auto; intros.
repeat (rewrite Udiv_by_zero;auto).
assert (forall f, mu d f <= k).
intros; apply Ole_trans with (mu d (fone A)); auto.
apply Oeq_trans with ((k0 * mu d f) / k); auto.
apply Udiv_eq_compat_left; auto.
apply (mu_stable_mult d); trivial.
apply Umult_div_assoc; auto. 
Save.

Lemma Mdiv_continuous : forall A (k:U)(d:distr A), continuous (Mdiv k (mu d)).
red; intros; repeat rewrite Mdiv_simpl.
apply Ole_trans with (lub (mu d @ h) / k); auto.
exact (Udiv_continuous k (mu d @ h)).
Save.

Definition distr_div A (k:U) (d:distr A) (dk : mu d (fone A) <= k)
              : distr A.
intros.
exists (Mdiv k (mu d)).
apply Mdiv_stable_inv; auto.
apply Mdiv_stable_plus.
apply Mdiv_stable_mult; auto.
apply Mdiv_continuous.
Defined.


(** ** Least upper bound of increasing sequences of distributions *)
Section Lubs.
Variable A : Type.

Definition Mu : Distr A -m> M A.
exists (mu (A:=A)); auto.
Defined.

Variable muf : natO -m> Distr A.

Definition mu_lub: Distr A.
exists (lub (Mu @ muf)).

red; intros; simpl; apply lub_inv; intros; simpl.
apply (mu_stable_inv (muf n)).

red; intros; simpl.
apply Oeq_trans with (lub ((UPlus @2 ((Mu @ muf) <_> f)) ((Mu @ muf) <_> g))); auto.
apply lub_eq_compat; auto.
simpl; apply fmon_eq_intro; intro; exact (mu_stable_plus (muf n) H); auto.

red; intros; simpl.
apply Oeq_trans with (lub (UMult k @ ((Mu @ muf) <_> f))); auto.
apply lub_eq_compat; auto.
simpl; apply fmon_eq_intro; intro; exact (mu_stable_mult (muf n) k f); auto.

unfold M; apply cont_lub; intros.
apply (mu_continuous (muf n)).
Defined.

Lemma mu_lub_le : forall n:nat, muf n <= mu_lub.
simpl; intros.
apply le_lub with (f:=(Mu @ muf) <_> x) (n:=n).
Save.

Lemma mu_lub_sup : forall m: distr A, (forall n:nat, muf n <= m) -> mu_lub <= m.
simpl; intros.
apply lub_le; simpl; intros; auto.
Save.

End Lubs.
Hint Resolve mu_lub_le mu_lub_sup.

(** *** Distributions seen as a Ccpo *)

Definition cDistr : forall (A:Type), cpo.
intros; exists (Distr A) (distr_null A) (mu_lub (A:=A)); auto.
Defined.

(** ** Fixpoints *)

Definition Mfix (A B:Type) (F: (A -O-> cDistr B) -m> A -O-> cDistr B) : A-O->cDistr B := fixp F.
Definition MFix (A B:Type) : ((A -O-> cDistr B) -m> A -O-> cDistr B) -m> A -O->cDistr B 
           := Fixp (A -O-> cDistr B).

Lemma Mfix_le : forall  (A B:Type) (F: (A -O-> cDistr B) -m> A -O-> cDistr B) (x :A),
            Mfix F x <= F (Mfix F) x.
intros; unfold Mfix; apply (fixp_le F x).
Save.

Lemma Mfix_eq : forall  (A B:Type) (F: (A -O-> cDistr B) -m> A -O-> cDistr B), 
continuous F -> forall (x :A),  Mfix F x == F (Mfix F) x.
intros; unfold Mfix; apply ford_eq_elim with (n:=x).
apply (fixp_eq H).
Save.

Hint Resolve Mfix_le Mfix_eq.

Lemma Mfix_le_compat : forall (A B:Type) (F G : (A-O->cDistr B)-m>A-O->cDistr B),
        F <= G -> Mfix F <= Mfix G.
intros; unfold Mfix; auto.
Save.

Definition Miter  (A B:Type) := Ccpo.iter (D:=A -O-> cDistr B).

Lemma Mfix_le_iter : forall  (A B:Type) (F:(A -O-> cDistr B)-m> A -O-> cDistr B) (n:nat),
     Miter F n <= Mfix F.
unfold Miter,Mfix,fixp; auto.
Save.

(** ** Continuity *)

Section Continuity.

Variables A B:Type.

Lemma Mlet_continuous_right 
    : forall a:Distr A, continuous (D1:=A-O->cDistr B) (D2:=cDistr B) (MLet A B a).
red; intros; intro f.
rewrite (MLet_simpl (A:=A) (B:=B)).
apply Ole_trans with (mu a (fun x:A => lub ((Mu B @ (h <o> x)) <_> f))); auto.
apply Ole_trans with (mu a (lub (c:=A-O->U) (ford_shift (fun x:A => ((Mu B @ (h <o> x)) <_> f))))); auto.
apply Ole_trans with (1 := mu_continuous a (ford_shift (fun x : A => (Mu B @ (h <o> x)) <_> f))); auto.
Save.

Lemma Mlet_continuous_left 
    : continuous (D1:=cDistr A) (D2:=(A-O->cDistr B) -M-> cDistr B) (MLet A B).
red; intros; intro F; intro f.
rewrite (MLet_simpl (A:=A) (B:=B)).
simpl; auto.
Save.

Hint Resolve Mlet_continuous_right Mlet_continuous_left.

Lemma Mlet_continuous2 : continuous2 (D1:=cDistr A) (D2:= A-O->cDistr B) (D3:=cDistr B) (MLet A B).
intros; apply continuous_continuous2; auto.
Save.
Hint Resolve Mlet_continuous2.


Lemma Mlet_lub_le : forall (mun:natO-m>cDistr A) (Mn : natO-m>(A-O->cDistr B)),
            Mlet (lub mun) (lub Mn) <= lub (c:=cDistr B) ((MLet A B @2 mun) Mn).
intros; apply Mlet_continuous2 with (f:=mun) (g:=Mn).
Save.

Lemma Mfix_continuous : 
     forall (Fn : natO -m> (A -O-> cDistr B) -M-> A -O-> cDistr B),
     (forall n, continuous (Fn n)) -> 
     Mfix (lub Fn) <= lub (MFix A B @ Fn).
unfold Mfix, MFix; intros; apply fixp_continuous; auto.
Save.

End Continuity.


(** ** Distribution for [flip]
The distribution associated to [flip ()] is 
       $f \mapsto \frac{1}{2}f(true)+\frac{1}{2}f(false)$ *)

Definition flip : M bool.
exists (fun (f : bool -> U) => [1/2] * (f true) + [1/2] * (f false)).
red; intros; simpl.
apply Ole_trans with ([1/2]* y true +[1/2]* x false ); auto.
Defined.

Lemma flip_stable_inv : stable_inv flip.
unfold flip, stable_inv, finv; auto.
Save.

Lemma flip_stable_plus : stable_plus flip.
unfold flip, stable_plus, fplus; intros; simpl.
rewrite (Udistr_plus_left [1/2] _ _ (H true)).
rewrite (Udistr_plus_left [1/2] _ _ (H false)).
repeat norm_assoc_right.
apply Uplus_eq_compat_right.
repeat norm_assoc_left; apply Uplus_eq_compat_left; auto.
Save.

Lemma flip_stable_mult : stable_mult flip.
unfold flip, stable_mult, fmult; intros; simpl.
assert (H:([1/2]* f true) <= ([1-] ([1/2]* f false))); auto.
rewrite (Udistr_plus_left k _ _ H); auto.
Save.

Lemma flip_continuous : continuous flip.
unfold continuous; intros; simpl.
do 2 rewrite <- lub_eq_mult.
rewrite <- lub_eq_plus; auto.
Save.

Definition ctrue : MF bool := fun (b:bool) => if b then 1 else 0.
Definition cfalse : MF bool := fun (b:bool) => if b then 0 else 1.

Lemma flip_ctrue : flip ctrue == [1/2].
unfold flip, ctrue; simpl; auto.
setoid_rewrite (Umult_one_right [1/2]).
setoid_rewrite (Umult_zero_right [1/2]); auto.
Save.

Lemma flip_cfalse : flip cfalse == [1/2].
unfold flip, cfalse; simpl; auto.
setoid_rewrite (Umult_one_right [1/2]).
setoid_rewrite (Umult_zero_right [1/2]); auto.
Save.

Hint Resolve flip_ctrue flip_cfalse.

Definition Flip  : Distr bool.
exists flip.
apply flip_stable_inv.
apply flip_stable_plus.
apply flip_stable_mult.
apply flip_continuous.
Defined.


(** ** Uniform distribution beween 0 and n *)
Require Arith.

(** *** Definition of [fnth]
        [fnth n k] is defined as $\frac{1}{n+1}$ *)

Definition fnth (n:nat) : nat -> U := fun k => [1/]1+n.           

(** *** Basic properties of [fnth] *)


Lemma Unth_eq : forall n, Unth n == [1-] (sigma (fnth n) n).
intro; exact (Unth_prop n).
Save.
Hint Resolve Unth_eq.

Lemma sigma_fnth_one : forall n, sigma (fnth n) (S n) == 1.
intros; rewrite sigma_S.
unfold fnth at 1.
rewrite (Unth_eq n); auto.
Save.
Hint Resolve sigma_fnth_one.

Lemma Unth_inv_eq : forall n, [1-] ([1/]1+n) == sigma (fnth n) n.
intro; setoid_rewrite (Unth_eq n); auto.
Save.

Lemma sigma_fnth_sup : forall n m, (m > n) -> sigma (fnth n) m == sigma (fnth n) (S n).
intros.
assert ((S n) <= m)%nat; auto with arith.
elim H0; intros; auto.
rewrite sigma_S; auto.
setoid_rewrite H2.
assert (m0 > n); auto with arith.
setoid_rewrite (sigma_fnth_one n); auto.
Save.


Lemma sigma_fnth_le : forall n m, (sigma (fnth n) m) <= (sigma (fnth n) (S n)).
intros; setoid_rewrite (sigma_fnth_one n); auto.
Save.

Hint Resolve sigma_fnth_le.

(** [fnth] is a retract *)
Lemma fnth_retract : forall n:nat,(retract (fnth n) (S n)).
red; intros.
unfold fnth at 1.
apply Ole_trans with ([1-] (sigma (fnth n) n)); auto with arith.
Save.

Implicit Arguments fnth_retract [].

(** ** Distributions and general summations *)

Definition sigma_fun A (f:nat -> MF A) (n:nat) : MF A := fun x => sigma (fun k => f k x) n.
Definition serie_fun A (f:nat -> MF A) : MF A := fun x => serie (fun k => f k x).

Definition Sigma_fun A (f:nat -> MF A) : natO -m> MF A := 
    ford_shift (fun x => Sigma (fun k => f k x)).

Lemma Sigma_fun_simpl : forall A (f:nat -> MF A) (n:nat),
    Sigma_fun f n = sigma_fun f n.
trivial.
Save.

Lemma serie_fun_lub_sigma_fun : forall A (f:nat -> MF A), 
     serie_fun f == lub (c:=MF A) (Sigma_fun f).
intros; unfold serie_fun.
simpl; apply ford_eq_intro; intro x.
unfold serie; apply lub_eq_compat.
simpl; apply fmon_eq_intro; intro n; trivial.
Save.
Hint Resolve serie_fun_lub_sigma_fun.

Lemma sigma_fun_0 : forall A (f:nat->MF A), sigma_fun f 0 == fzero A.
simpl; unfold fzero; auto.
Save.

Lemma sigma_fun_S : forall A (f:nat->MF A) (n:nat), 
      sigma_fun f (S n) == fplus (f n) (sigma_fun f n).
simpl; unfold fplus; auto.
Save.


Lemma mu_sigma_le : forall A (d:distr A) (f:nat -> MF A) (n:nat), 
      mu d (sigma_fun f n) <= sigma (fun k => mu d (f k)) n.
induction n; intros.
rewrite sigma_0; apply Ole_trans with (mu d (fzero A)); auto.
rewrite sigma_S; apply Ole_trans with (mu d (fplus (f n) (sigma_fun f n))).
auto.
apply Ole_trans with (mu d (f n) + mu d (sigma_fun f n)); auto.
Save.

Lemma retract_fplusok : forall A (f:nat -> MF A) (n:nat), 
     (forall x, retract (fun k => f k x) n) -> 
     forall k, (k < n)%nat -> fplusok (f k) (sigma_fun f k).
red; intros; intro x.
apply (H x k); auto.
Save.


Lemma mu_sigma_eq : forall A (d:distr A) (f:nat -> MF A) (n:nat), 
     (forall x, retract (fun k => f k x) n) -> 
      mu d (sigma_fun f n) == sigma (fun k => mu d (f k)) n.
induction n; intros.
rewrite sigma_0; apply Oeq_trans with (mu d (fzero A)); auto.
rewrite sigma_S; apply Oeq_trans with (mu d (fplus (f n) (sigma_fun f n))).
auto.
apply Oeq_trans with (mu d (f n) + mu d (sigma_fun f n)); auto.
apply (mu_stable_plus d).
apply retract_fplusok with (S n); auto.
Save.


Lemma mu_serie_le : forall A (d:distr A) (f:nat -> MF A), 
      mu d (serie_fun f) <= serie (fun k => mu d (f k)).
intros; apply Ole_trans with (mu d (lub (Sigma_fun f))).
apply mu_monotonic; rewrite (serie_fun_lub_sigma_fun f); trivial.
apply Ole_trans with (lub (mu d @ (Sigma_fun f))).
apply (mu_continuous d).
unfold serie; apply lub_le_compat; intro n.
rewrite fmon_comp_simpl.
exact (mu_sigma_le d f n).
Save.

Lemma mu_serie_eq : forall A (d:distr A) (f:nat -> MF A), 
     (forall x, wretract (fun k => f k x)) -> 
      mu d (serie_fun f) == serie (fun k => mu d (f k)).
intros; apply Oeq_trans with (mu d (lub (Sigma_fun f))).
apply mu_stable_eq; apply (serie_fun_lub_sigma_fun f); trivial.
apply Oeq_trans with (lub (mu d @ (Sigma_fun f))).
apply (lub_comp_eq (f:=mu d)).
apply (mu_continuous d).
unfold serie; apply lub_eq_compat; apply fmon_eq_intro; intro n.
rewrite fmon_comp_simpl.
apply (mu_sigma_eq d f (n:=n)).
red; intros.
apply (H x k).
Save.

Lemma wretract_fplusok : forall A (f:nat -> MF A), 
     (forall x, wretract (fun k => f k x)) -> 
     forall k, fplusok (f k) (sigma_fun f k).
red; intros; intro x.
apply (H x k); auto.
Save.


(** ** Discrete distributions *)

Definition discrete : forall A (c : nat -> U) (p : nat -> A), M A.
intros; exists (fun f : A->U => serie (fun k => c k * f (p k))).
red; intros; auto.
Defined.

Lemma discrete_simpl : forall A (c : nat -> U) (p : nat -> A) f, 
     discrete c p f = serie (fun k => c k * f (p k)).
trivial.
Save.

Lemma discrete_stable_inv : forall A (c : nat -> U) (p : nat -> A), 
    wretract c -> stable_inv (discrete c p).
red; intros.
repeat rewrite discrete_simpl.
unfold finv; apply serie_inv_le; auto.
Save.

Lemma discrete_stable_plus : forall A (c : nat -> U) (p : nat -> A), 
    stable_plus (discrete c p).
red; intros.
repeat rewrite discrete_simpl.
apply Oeq_trans with (serie (fun k : nat => c k * f (p k) + c k * g (p k))).
apply serie_eq_compat.
intros; unfold fplus.
apply Udistr_plus_left.
apply (H (p k)).
apply serie_plus; auto.
Save.

Lemma discrete_stable_mult : forall A (c : nat -> U) (p : nat -> A), 
    wretract c -> stable_mult (discrete c p).
red; intros.
repeat rewrite discrete_simpl; unfold fmult.
apply Oeq_trans with (serie (fun k0 : nat => k * (c k0 * f (p k0)))); auto. 
apply serie_mult.
apply wretract_le with c; auto.
Save.

Lemma discrete_continuous : forall A (c : nat -> U) (p : nat -> A), 
    continuous (discrete c p).
red; intros.
rewrite discrete_simpl.
apply Ole_trans with 
(serie (lub (c:=nat-O->U) (ford_shift (fun k => (UMult (c k) @ (h <o> (p k))))))).
apply serie_le_compat; intro k.
repeat rewrite fcpo_lub_simpl.
apply (UMult_continuous_right (c k) (h <o> p k)).
rewrite (serie_continuous (ford_shift (fun k : nat => UMult (c k) @ h <o> p k))).
apply lub_le_compat; intro n; simpl; auto.
Save.

Record discr (A:Type) : Type := 
     {coeff : nat -> U; coeff_retr : wretract coeff; points : nat -> A}.
Hint Resolve coeff_retr.

Definition Discrete : forall A,  discr A -> Distr A.
intros A d ; exists (discrete (coeff d) (points d)).
apply discrete_stable_inv; trivial.
apply discrete_stable_plus.
apply discrete_stable_mult; trivial.
apply discrete_continuous.
Defined.

Lemma Discrete_simpl : forall A (d:discr A), 
     mu (Discrete d) = discrete (coeff d) (points d).
trivial.
Save.

Definition is_discrete (A:Type) (m: Distr A) := 
      exists d : discr A, m == Discrete d.

(** *** Distribution for [random n]
The distribution associated to [random n] is 
       $f \mapsto \Sigma_{i=0}^n \frac{f(i)}{n+1}$
       we cannot factorize $\frac{1}{n+1}$ because of possible overflow *)

Definition random (n:nat):M nat.
intro n; exists (fun (f:nat->U) => sigma (fun k => Unth n *  f k) (S n)).
red; intros; auto.
Defined.

Lemma random_simpl : forall n (f : nat->U), 
           random n f = sigma (fun k => Unth n *  f k) (S n).
trivial.
Save.

(** *** Properties of [random] *)

Lemma random_stable_inv : forall n, stable_inv (random n).
unfold random, stable_inv, finv; intros; simpl.
rewrite (sigma_inv f (fnth_retract n)); auto.
Save.

Lemma random_stable_plus : forall n, stable_plus (random n).
unfold stable_plus, fplus; intros.
repeat (rewrite random_simpl).
unfold fplusok, finv in H.
apply Oeq_trans with 
 (sigma (fun k : nat => ([1/]1+n * f k) + ([1/]1+n  * g k)) (S n)).
apply sigma_eq_compat; intros.
assert (f k <= [1-] (g k)); auto.
apply sigma_plus with (f:=fun k : nat => Unth n * f k)
                      (g:=fun k : nat => Unth n * g k); auto.
Save.

Lemma random_stable_mult : forall n, stable_mult (random n).
unfold stable_mult, fmult; intros; repeat (rewrite random_simpl).
apply Oeq_trans with 
 (sigma (fun l : nat => k * ([1/]1+n * f l)) (S n)).
apply sigma_eq_compat; intros; auto.
apply sigma_mult with (f:=fun k : nat => Unth n * f k).
red; intros.
apply Ole_trans with ([1/]1+n); auto.
apply Ole_trans with ([1-] (sigma (fun k1 => Unth n) k0)); auto.
apply (fnth_retract n k0); auto.
Save.


Lemma random_continuous : forall n, continuous (random n).
unfold continuous; intros; rewrite random_simpl.
apply Ole_trans with 
    (sigma (fun k : nat => lub (c:=U) (UMult ([1/]1+n) @ (h <o> k))) (S n)).
apply sigma_le_compat; intros; simpl.
rewrite (lub_eq_mult ([1/]1+n) (h <o> k)); auto.
apply Ole_trans with 
(sigma (lub (c:=nat-O->U) (ford_shift (fun k : nat => (UMult ([1/]1+n) @ (h <o> k))))) (S n)); auto.
rewrite sigma_lub1; auto.
Save.

Definition Random (n:nat) : Distr nat.
intro n; exists (random n).
apply random_stable_inv.
apply random_stable_plus.
apply random_stable_mult.
apply random_continuous.
Defined.

Lemma Random_simpl : forall (n:nat), mu (Random n) = random n.  
trivial.
Save.

Lemma Random_total : forall n : nat,  mu (Random n) (fone nat) == 1.
intros; simpl mu;unfold fone; rewrite random_simpl.
apply Oeq_trans with  (sigma (fnth n) (S n)).
apply sigma_eq_compat.
intros; repeat Usimpl; auto.
auto.
Save.
Hint Resolve Random_total.

Lemma Random_inv : forall f n, mu (Random n) (finv f) == [1-] (mu (Random n) f).
intros; apply mu_one_inv; auto.
Save.
Hint Resolve Random_inv.
End Proba.
