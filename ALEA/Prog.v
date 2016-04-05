(** * Prog.v: Composition of distributions *)

Require Export Probas.
Set Implicit Arguments.

Module Rules (Univ:Universe).
Module PP := (Proba Univ).
(* begin hide *)
Import Univ PP MP UP.
Open Local Scope U_scope.
Open Local Scope O_scope.
(* end hide *)

(** ** Conditional *)

Definition Mif (A:Type) (b:Distr bool) (m1 m2: Distr A)
    := Mlet b (fun x:bool => if x then m1 else m2).

Lemma Mif_mon : forall (A:Type) (b1 b2:Distr bool) (m1 m2 n1 n2: Distr A),
    b1 <= b2 -> m1 <= m2 -> n1 <= n2 -> Mif b1 m1 n1 <= Mif b2 m2 n2.
intros; unfold Mif.
apply Mlet_le_compat ; auto.
intro x; destruct x; auto.
Save.

Definition MIf : forall (A:Type), Distr bool -m> Distr A -m> Distr A -m> Distr A.
intro A; exists (fun b => le_compat2_mon (fun m1 m2 n1 n2 (H1:m1 <= m2) (H2:n1<=n2) =>
                                                                    Mif_mon (A:=A) (Ole_refl b) H1 H2)).
red; simpl; intros; auto.
Defined.

(** ** Probabilistic choice *)

(** *** The distribution associated to [pchoice p] is $f \mapsto p m1 f + 1-p m2 $ *)

Definition pchoice : forall A, U -> M A -> M A -> M A.
intros A p m1 m2;
     exists (fun (f : A -> U) => p * m1 f + [1-]p * m2 f).
red; intros; simpl.
apply Uplus_le_compat; auto.
Defined.

Lemma pchoice_simpl : forall A p (m1 m2:M A) f,
      pchoice p m1 m2 f = p * m1 f + [1-]p * m2 f.
trivial.
Save.

Definition Mchoice (A:Type) (p:U) (m1 m2: Distr A) : Distr A.
intros A p m1 m2; exists (pchoice p (mu m1) (mu m2)).
(* stable_inv *)
red; intros; repeat (rewrite pchoice_simpl).
apply Ole_trans with
 (p * [1-]mu m1 f + [1-] p * [1-]mu m2 f).
2:auto.
apply Uplus_le_compat; repeat Usimpl; auto.
(* stable_plus *)
red; intros; repeat (rewrite pchoice_simpl).
rewrite (mu_stable_plus m1 H); rewrite (mu_stable_plus m2 H).
rewrite Udistr_plus_left.
2:auto.
rewrite Udistr_plus_left.
2:auto.
repeat norm_assoc_left; repeat Usimpl.
repeat norm_assoc_right; repeat Usimpl; auto.
(* stable_mult *)
red; intros; repeat (rewrite pchoice_simpl).
rewrite (mu_stable_mult m1 k f); rewrite (mu_stable_mult m2 k f).
rewrite Udistr_plus_left; auto.
(* continuous *)
red; intros; rewrite pchoice_simpl.
apply Ole_trans with
    (p * lub (mu m1 @ h) + [1-] p * lub (mu m2 @ h)).
apply Uplus_le_compat; repeat Usimpl; auto.
repeat rewrite <- lub_eq_mult.
rewrite <- lub_eq_plus; auto.
Defined.

Lemma Mchoice_simpl : forall A p (m1 m2:Distr A) f,
      mu (Mchoice p m1 m2) f = p * mu m1 f + [1-]p * mu m2 f.
trivial.
Save.

Lemma Mchoice_mon : forall (A:Type) (p:U) (m1 m2 n1 n2: Distr A),
        m1<=m2 -> n1<=n2 -> Mchoice p m1 n1 <= Mchoice p m2 n2.
simpl; intros.
apply Uplus_le_compat; repeat Usimpl; auto.
Save.


Add Parametric Morphism (A:Type) :  (Mchoice (A:=A))
  with signature Oeq (O:=U) ==> Oeq (O:=Distr A) ==> Oeq (O:=Distr A) ==> Oeq (O:=Distr A)
as Mchoice_eq_compat.
intros; apply eq_distr_intro; simpl; intros.
rewrite H; apply Uplus_eq_compat; repeat Usimpl; auto.
Save.
Hint Immediate  Mchoice_eq_compat.

Definition MChoice A (p:U) : Distr A -m> Distr A -m> Distr A :=
               le_compat2_mon (Mchoice_mon (A:=A) p).

Lemma MChoice_simpl : forall A (p:U) (m1 m2 : Distr A),
MChoice A p m1 m2 = Mchoice p m1 m2.
trivial.
Save.

Lemma Mchoice_sym_le : forall (A:Type) (p:U) (m1 m2: Distr A),
            Mchoice p m1 m2 <= Mchoice ([1-]p) m2 m1.
simpl; intros.
rewrite Uplus_sym; repeat Usimpl; auto.
Save.
Hint Resolve Mchoice_sym_le.

Lemma Mchoice_sym : forall (A:Type) (p:U) (m1 m2: Distr A),
            Mchoice p m1 m2 == Mchoice ([1-]p) m2 m1.
intros; apply Ole_antisym; auto.
apply Ole_trans with (Mchoice ([1-][1-]p) m1 m2); auto.
Save.

Lemma Mchoice_continuous_right
    : forall (A:Type) (p:U) (m: Distr A), continuous (D1:=cDistr A) (D2:=cDistr A) (MChoice A p m).
red; intros; intro f.
rewrite (MChoice_simpl p m).
rewrite (Mchoice_simpl p m).
simpl mu at 2.
rewrite lub_fun_eq.
rewrite <- (lub_eq_mult ([1-]p) ((Mu A @ h) <_> f)).
rewrite <- lub_eq_plus_cte_left; auto.
Save.
Hint Resolve Mchoice_continuous_right.

Lemma Mchoice_continuous_left : forall (A:Type) (p:U),
    continuous (D1:=cDistr A) (D2:=cDistr A -M-> cDistr A) (MChoice A p).
red; intros; intro m.
rewrite (MChoice_simpl (A:=A) p).
rewrite Mchoice_sym.
apply Ole_trans with (lub (c:=cDistr A) ((MChoice A ([1-] p) m)@h)).
apply (Mchoice_continuous_right ([1-]p) m h).
rewrite fmon_lub_simpl.
apply lub_le_compat; intros; intro f; simpl; auto.
Save.

(*
Lemma Mchoice_continuous_left
    : forall (A:Type) (p:U) (m: Distr A), continuous (D1:=cDistr A) (D2:=cDistr A) (MChoice A p <_> m).
red; intros.
rewrite fmon_app_simpl.
rewrite (MChoice_simpl (A:=A) p).
rewrite Mchoice_sym.
apply Ole_trans with (lub (c:=cDistr A) ((MChoice A ([1-] p) m)@h)).
apply (Mchoice_continuous_right ([1-]p) m h).
apply lub_le_compat; intros; intro f; simpl; auto.
Save.
*)

Lemma Mchoice_continuous :
forall (A:Type) (p:U), continuous2 (D1:=cDistr A) (D2:=cDistr A) (D3:=cDistr A) (MChoice A p).
intros; apply continuous_continuous2; intros.
apply (Mchoice_continuous_right (A:=A) p).
apply (Mchoice_continuous_left (A:=A) p).
Save.

(** ** Image distribution *)

Definition im_distr (A B : Type) (f:A->B) (m:Distr A) : Distr B :=
    Mlet m (fun a => Munit (f a)).

Lemma im_distr_simpl : forall A B (f:A->B) (m:Distr A)(h:B->U),
     mu (im_distr f m)  h == mu m (fun a => h (f a)).
trivial.
Save.

Add Parametric Morphism (A B : Type) : (im_distr (A:=A) (B:=B)) with signature
       (feq (A:=A) (B:=B)) ==> (Oeq (O:=Distr A)) ==> (Oeq (O:=Distr B))
as im_distr_eq_compat.
intros; apply eq_distr_intro; intro h; simpl.
apply (mu_eq_morphism (A:=A)); trivial.
apply ford_eq_intro; intro n; rewrite (H n); auto.
Save.

Lemma im_distr_comp : forall A B C (f:A->B) (g:B->C) (m:Distr A),
            im_distr g (im_distr f m) == im_distr (fun a => g (f a)) m.
intros; apply eq_distr_intro; simpl; auto.
Save.

Lemma im_distr_id : forall A (f:A->A) (m:Distr A), (forall x, f x = x) ->
            im_distr f m == m.
intros; apply eq_distr_intro; simpl; intros.
apply (mu_stable_eq m); simpl; apply ford_eq_intro; intro x; rewrite H; auto.
Save.

(** ** Product distribution *)

Definition prod_distr (A B : Type)(d1:Distr A)(d2:Distr B) : Distr (A*B) :=
                Mlet d1 (fun x => Mlet d2 (fun y => Munit (x,y))).

Add Parametric Morphism (A B : Type) : (prod_distr (A:=A) (B:=B))
with signature (Ole (o:=Distr A)) ++> (Ole (o:=Distr B)) ++> (Ole (o:=Distr (A*B)))
as prod_distr_le_compat.
intros; unfold prod_distr; auto.
Save.
Hint Resolve prod_distr_le_compat.

Add Parametric Morphism (A B : Type) : (prod_distr (A:=A) (B:=B))
with signature (Oeq (O:=Distr A)) ==> (Oeq (O:=Distr B)) ==> (Oeq (O:=Distr (A*B)))
as prod_distr_eq_compat.
intros; apply Ole_antisym; auto.
Save.
Hint Immediate prod_distr_eq_compat.

Definition Prod_distr (A B :Type): Distr A -m> Distr B -m> Distr (A*B).
intros A B; apply le_compat2_mon with (prod_distr (A:=A) (B:=B)); auto.
Defined.

Lemma Prod_distr_simpl : forall (A B:Type)(d1: Distr A) (d2:Distr B),
     Prod_distr A B d1 d2 = prod_distr d1 d2.
trivial.
Save.

Lemma prod_distr_rect : forall  (A B : Type) (d1: Distr A) (d2:Distr B) (f:A->U)(g:B->U),
         mu (prod_distr d1 d2) (fun xy => f (fst xy) * g (snd xy)) == mu d1 f * mu d2 g.
intros; unfold prod_distr; simpl.
apply Oeq_trans with (mu d1 (fun x : A => mu d2 g * f x)).
apply (mu_stable_eq d1).
simpl; apply ford_eq_intro; intro x.
rewrite (mu_stable_mult d2 (f x) g); auto.
rewrite (mu_stable_mult d1 (mu d2 g) f); auto.
Save.

Lemma prod_distr_fst : forall  (A B : Type) (d1: Distr A) (d2:Distr B) (f:A->U),
             mu (prod_distr d1 d2) (fun xy => f (fst xy)) == mu d2 (fone B) * mu d1 f.
intros; rewrite Umult_sym; rewrite <- prod_distr_rect.
apply (mu_stable_eq (prod_distr d1 d2)).
simpl; apply ford_eq_intro; unfold UP.fone; auto.
Save.

Lemma prod_distr_snd : forall  (A B : Type) (d1: Distr A) (d2:Distr B) (g:B->U),
             mu (prod_distr d1 d2) (fun xy => g (snd xy)) == mu d1 (fone A) * mu d2 g.
intros; rewrite <- prod_distr_rect.
apply (mu_stable_eq (prod_distr d1 d2)).
simpl; apply ford_eq_intro; unfold UP.fone; auto.
Save.

Lemma prod_distr_fst_eq : forall  (A B : Type) (d1: Distr A) (d2:Distr B),
mu d2 (fone B) == 1 -> im_distr (fst (A:=A) (B:=B)) (prod_distr d1 d2) == d1.
intros; apply eq_distr_intro; intro g.
rewrite im_distr_simpl.
rewrite prod_distr_fst; auto.
Save.

Lemma prod_distr_snd_eq : forall  (A B : Type) (d1: Distr A) (d2:Distr B),
mu d1 (fone A) == 1 -> im_distr (snd (A:=A) (B:=B)) (prod_distr d1 d2) == d2.
intros; apply eq_distr_intro; intro g.
rewrite im_distr_simpl.
rewrite prod_distr_snd; auto.
Save.

Definition swap A B (x:A*B) : B * A := (snd x,fst x).

Definition arg_swap A B (f : MF (A*B)) : MF (B*A) := fun z => f (swap z).

Definition Arg_swap A B : MF (A*B) -m> MF (B*A).
 intros; exists (arg_swap (A:=A) (B:=B)).
red; unfold arg_swap,swap; auto.
Defined.

Lemma Arg_swap_simpl : forall A B f, Arg_swap A B f = arg_swap f.
trivial.
Save.

Definition prod_distr_com A B (d1: Distr A) (d2:Distr B) (f : MF (A * B)) :=
      mu (prod_distr d1 d2) f == mu (prod_distr d2 d1) (arg_swap f).

Lemma prod_distr_com_eq_compat : forall A B (d1: Distr A) (d2:Distr B) (f g: MF (A * B)),
  f == g -> prod_distr_com d1 d2 f -> prod_distr_com d1 d2 g.
unfold prod_distr_com; intros; apply Oeq_trans with (mu (prod_distr d1 d2) f).
apply mu_stable_eq; auto.
apply Oeq_trans with (mu (prod_distr d2 d1) (arg_swap f)); auto.
apply mu_stable_eq; unfold arg_swap,swap; simpl; apply ford_eq_intro; intro z.
apply (ford_eq_elim H (snd z,fst z)).
Save.

Lemma prod_distr_com_rect : forall (A B : Type) (d1: Distr A) (d2:Distr B) (f:A->U)(g:B->U),
         prod_distr_com d1 d2 (fun xy => f (fst xy) * g (snd xy)).
red; intros.
rewrite prod_distr_rect.
apply Oeq_trans with (mu (prod_distr d2 d1) (fun yx => g (fst yx) * f (snd yx))).
rewrite prod_distr_rect; auto.
apply mu_stable_eq; simpl; apply ford_eq_intro; intro yx; unfold arg_swap; simpl; auto.
Save.

Lemma prod_distr_com_cte : forall (A B : Type) (d1: Distr A) (d2:Distr B) (c:U),
         prod_distr_com d1 d2 (fcte (A*B) c).
intros; apply prod_distr_com_eq_compat with (fun z => fcte A c (fst z) * fone B (snd z)).
simpl; auto.
apply prod_distr_com_rect.
Save.

Lemma prod_distr_com_one : forall (A B : Type) (d1: Distr A) (d2:Distr B),
         prod_distr_com d1 d2 (fone (A*B)).
intros; exact (prod_distr_com_cte d1 d2 1).
Save.

Lemma prod_distr_com_plus : forall (A B : Type) (d1: Distr A) (d2:Distr B) (f g:MF (A*B)),
         fplusok f g ->
         prod_distr_com d1 d2 f -> prod_distr_com d1 d2 g ->
         prod_distr_com d1 d2 (fplus f g).
unfold prod_distr_com; intros.
rewrite (mu_stable_plus (prod_distr d1 d2) (f:=f) (g:=g) H).
rewrite H0; rewrite H1.
rewrite <- (mu_stable_plus (prod_distr d2 d1) (f:=arg_swap f) (g:=arg_swap g)); auto.
red; unfold arg_swap,swap,finv; simpl; intro z; apply (H (snd z,fst z)).
Save.

Lemma prod_distr_com_mult : forall (A B : Type) (d1: Distr A) (d2:Distr B) (k:U)(f:MF (A*B)),
         prod_distr_com d1 d2 f -> prod_distr_com d1 d2 (fmult k f).
unfold prod_distr_com; intros.
rewrite (mu_stable_mult (prod_distr d1 d2) k f).
rewrite H.
rewrite <- (mu_stable_mult (prod_distr d2 d1) k (arg_swap f)); auto.
Save.

Lemma prod_distr_com_inv : forall (A B : Type) (d1: Distr A) (d2:Distr B) (f:MF (A*B)),
         prod_distr_com d1 d2 f -> prod_distr_com d1 d2 (finv f).
unfold prod_distr_com; intros.
rewrite (mu_inv_minus (prod_distr d1 d2) f).
rewrite H.
assert (H1:=prod_distr_com_one d1 d2); red in H1.
rewrite H1.
rewrite <- (mu_inv_minus (prod_distr d2 d1) (arg_swap f)); auto.
Save.

Lemma prod_distr_com_lub : forall (A B : Type) (d1: Distr A) (d2:Distr B) (f:natO-m>MF (A*B)),
         (forall n, prod_distr_com d1 d2 (f n)) -> prod_distr_com d1 d2 (lub f).
unfold prod_distr_com; intros.
rewrite (lub_comp_eq f (mu_continuous (prod_distr d1 d2))).
apply Oeq_trans with (lub (mu (prod_distr d2 d1) @ (Arg_swap A B @ f))).
apply lub_eq_compat; apply fmon_eq_intro; intro n.
repeat rewrite fmon_comp_simpl.
rewrite H; auto.
rewrite <- lub_comp_eq; auto.
Save.

Lemma prod_distr_com_refl : forall A B (d1:distr A) (d2:distr B) (f:MF (A*B)),
     prod_distr_com d1 d2 f -> prod_distr_com d2 d1 (arg_swap f).
red; intros.
apply Oeq_sym; apply Oeq_trans with (mu (prod_distr d1 d2) f); auto.
Save.


Lemma discrete_commute : forall A B (d1:distr A) (d2:distr B) (f:MF (A*B)),
    is_discrete d1 -> prod_distr_com d1 d2 f.
red; intros A B d1 d2 f ((cf,cfr,pt),H); simpl.
unfold arg_swap; unfold swap; simpl.
apply Oeq_trans with
  (mu d2 (fun x : B => discrete cf pt (fun x0 : A => f (x0, x)))).
unfold discrete; simpl.
rewrite (mu_serie_eq d2 (fun k x => cf k * f (pt k, x))).
apply Oeq_trans with (discrete cf pt (fun x : A => mu d2 (fun x0 : B => f (x, x0)))); auto.
rewrite discrete_simpl; apply serie_eq_compat; intro k.
apply Oeq_sym; apply (mu_stable_mult d2 (cf k) (fun x0 : B => f (pt k, x0))).
intros; apply wretract_le with cf; auto.
apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intro x.
apply Oeq_trans with (mu (Discrete (Build_discr cfr pt)) (fun x0 : A => f (x0, x))); auto.
apply Oeq_sym; auto.
Save.

Definition fst_distr A B (m : Distr (A*B)) : Distr A := im_distr (fst (B:=B)) m.
Definition snd_distr A B (m : Distr (A*B)) : Distr B := im_distr (snd (B:=B)) m.


(** ** Range of a distribution *)

Definition range A (P:A->Prop) (d: Distr A) :=
   forall f, (forall x, P x -> 0 == f x) -> 0 == mu d f.

Lemma range_le : forall A (P:A->Prop)  (d:Distr A), range P d ->
       forall f g, (forall a, P a -> f a <= g a) -> mu d f <= mu d g.
   intros; assert (mu d f - mu d g <= 0).
   apply Ole_trans with (mu d (fun x => f x - g x)).
   apply mu_stable_le_minus.
   apply Oeq_le; apply Oeq_sym; apply H; intros.
   rewrite Uminus_le_zero; auto.
   apply Uminus_zero_le; apply Ule_zero_eq; exact H1.
  Save.

Lemma range_eq : forall A (P:A->Prop)  (d:Distr A), range P d ->
       forall f g, (forall a, P a -> f a == g a) -> mu d f == mu d g.
     red; intros; apply Ole_antisym; apply (range_le (P:=P)); intros; auto.
     apply Oeq_le; apply Oeq_sym; auto.
Save.


(** * Prog.v: Axiomatic semantics *)
(** ** Definition of correctness judgements
 $\ok{p}{e}{q}$ is defined as $p \leq \mu(e)(q)$
 $\up{p}{e}{q}$ is defined as $ \mu(e)(q) \leq p$ *)

Definition ok (A:Type) (p:U) (e:Distr A) (q:A->U) := p <= mu e q.

Definition okfun (A B:Type)(p:A->U)(e:A->Distr B)(q:A->B->U)
  := forall x:A, ok (p x) (e x) (q x).

Definition okup (A:Type) (p:U) (e:Distr A) (q:A->U) := mu e q <= p.

Definition upfun (A B:Type)(p:A->U)(e:A->Distr B)(q:A->B->U)
  := forall x:A, okup (p x) (e x) (q x).

(** ** Stability properties *)
Lemma ok_le_compat : forall (A:Type) (p p':U) (e:Distr A) (q q':A-o>U),
    p' <= p -> q <= q' -> ok p e q -> ok p' e q'.
unfold ok; intros.
apply Ole_trans with p; auto.
apply Ole_trans with (mu e q); auto.
Save.

Lemma ok_eq_compat : forall (A:Type) (p p':U) (e e':Distr A) (q q':A-o>U),
    p' == p ->  q == q' -> e == e' -> ok p e q -> ok p' e' q'.
unfold ok; intros.
apply Ole_trans with p; auto.
apply Ole_trans with (mu e q); auto.
apply Ole_trans with (mu e' q); auto.
Save.

Lemma okfun_le_compat :
forall (A B:Type) (p p':A -o> U) (e:A -o> Distr B) (q q':A-o>B-o>U),
    p' <= p -> q <= q' -> okfun p e q -> okfun p' e q'.
unfold okfun; intros.
apply ok_le_compat with (p x) (q x); auto.
Save.

Lemma ok_mult : forall (A:Type)(k p:U)(e:Distr A)(f : A -o> U),
                           ok p e f -> ok (k*p) e (fmult k f).
unfold ok; intros A k p e f oka.
rewrite (mu_stable_mult e k f).
apply Umult_le_compat_right; trivial.
Save.

Lemma ok_inv :   forall (A:Type)(p:U)(e:Distr A)(f : A -> U),
             ok p e f -> mu e (finv f) <= [1-]p.
unfold ok; intros A p e f oka.
apply Ole_trans with ([1-](mu e f)); auto.
Save.

Lemma okup_le_compat : forall (A:Type) (p p':U) (e:Distr A) (q q':A-o>U),
    p <= p' -> q' <= q -> okup p e q -> okup p' e q'.
unfold okup; intros.
apply Ole_trans with p; auto.
apply Ole_trans with (mu e q); auto.
Save.

Lemma okup_eq_compat : forall (A:Type) (p p':U) (e e':Distr A) (q q':A-o>U),
    p == p' ->  q == q' -> e == e' -> okup p e q -> okup p' e' q'.
unfold okup; intros.
apply Ole_trans with p; auto.
apply Ole_trans with (mu e q); auto.
apply Ole_trans with (mu e' q); auto.
Save.

Lemma upfun_le_compat : forall (A B:Type) (p p':A -o> U) (e:A -o> Distr B)
    (q q':A-o>B-o>U),
    p <= p' -> q'<=q -> upfun p e q -> upfun p' e q'.
unfold upfun; intros.
apply okup_le_compat with (p x) (q x); auto.
Save.

Lemma okup_mult : forall (A:Type)(k p:U)(e:Distr A)(f : A -o> U), okup p e f -> okup (k*p) e (fmult k f).
unfold okup; intros A k p e f oka.
rewrite (mu_stable_mult e k f).
apply Umult_le_compat_right; trivial.
Save.


(** ** Basic rules *)
(** *** Rules for application
 $\bfrac{\ok{r}{a}{p}~~~\forall x, \ok{p(x)}{f(x)}{q}}{\ok{r}{f(a)}{q}}$
 $\bfrac{\up{r}{a}{p}~~~\forall x, \up{p(x)}{f(x)}{q}}{\up{r}{f(a)}{q}}$*)

Lemma apply_rule : forall (A B:Type)(a:(Distr A))(f:A->Distr B)(r:U)(p:A->U)(q:B->U),
    ok r a p -> okfun p f (fun x => q) -> ok r (Mlet a f) q.
unfold ok,okfun,Mlet; simpl; intros.
apply Ole_trans with (mu a p); auto.
Save.

Lemma okup_apply_rule : forall (A B:Type)(a:Distr A)(f:A->Distr B)(r:U)(p:A->U)(q:B->U),
    okup r a p -> upfun p f (fun x => q) -> okup r (Mlet a f) q.
unfold okup,upfun,Mlet; simpl; intros.
apply Ole_trans with (mu a p); auto.
Save.

(** *** Rules for abstraction *)
Lemma lambda_rule : forall (A B:Type)(f:A->Distr B)(p:A->U)(q:A -> B->U),
   (forall x:A, ok (p x) (f x) (q x)) -> okfun p f q.
trivial.
Save.

Lemma okup_lambda_rule : forall (A B:Type)(f:A->Distr B)(p:A->U)(q:A -> B->U),
   (forall x:A, okup (p x) (f x) (q x)) -> upfun p f q.
trivial.
Save.

(** *** Rule for conditional
  $ \bfrac{\ok{p_1}{e_1}{q}~~~\ok{p_2}{e_2}{q}}
           {\ok{p_1\times \mu(b)(1_{true}) + p_2\times \mu(b)(1_{false})}
               {if~b~then~e_1~else~e_2}{q}}$

 $ \bfrac{\up{p_1}{e_1}{q}~~~\up{p_2}{e_2}{q}}
           {\up{p_1\times \mu(b)(1_{true}) + p_2\times \mu(b)(1_{false})}
               {if~b~then~e_1~else~e_2}{q}}$
*)

Lemma combiok : forall (A:Type) p q (f1 f2 : A -> U), p <= [1-]q -> fplusok (fmult p f1) (fmult q f2).
unfold fplusok, fmult, finv; intros; intro x.
apply Ole_trans with p; auto.
apply Ole_trans with ([1-]q); auto.
Save.
Hint Resolve combiok.

Lemma fmult_fplusok : forall (A:Type) p q (f1 f2 : A -> U), fplusok f1 f2 -> fplusok (fmult p f1) (fmult q f2).
unfold fplusok, fmult, finv; intros; intro x.
apply Ole_trans with (f1 x); auto.
apply Ole_trans with ([1-]f2 x); auto.
Save.
Hint Resolve fmult_fplusok.

Lemma ifok : forall f1 f2, fplusok (fmult f1 ctrue) (fmult f2 cfalse).
intros; apply fmult_fplusok; unfold fplusok,ctrue,cfalse,finv; intro x; case x; auto.
Save.
Hint Resolve ifok.

Lemma Mif_eq : forall (A:Type)(b:(Distr bool))(f1 f2:Distr A)(q:MF A),
	mu (Mif b f1 f2) q == (mu f1 q) * (mu b ctrue) + (mu f2 q) * (mu b cfalse).
intros.
apply Oeq_trans with (mu b (fplus (fmult (mu f1 q) ctrue) (fmult (mu f2 q) cfalse))).
intros; unfold Mif,Mlet,star; simpl.
apply (mu_stable_eq b); simpl; apply ford_eq_intro; intro x.
unfold fplus,fmult;destruct x; simpl.
rewrite (Umult_one_right (mu f1 q));
rewrite (Umult_zero_right (mu f2 q));
auto.
rewrite (Umult_zero_right (mu f1 q));
rewrite (Umult_one_right (mu f2 q));
auto.
rewrite (mu_stable_plus b (f:=(fmult (mu f1 q) ctrue))
                                (g:=(fmult (mu f2 q) cfalse))
                (ifok (mu f1 q) (mu f2 q))).
rewrite (mu_stable_mult b (mu f1 q) ctrue).
rewrite (mu_stable_mult b (mu f2 q) cfalse); trivial.
Save.

Lemma ifrule :
  forall (A:Type)(b:(Distr bool))(f1 f2:Distr A)(p1 p2:U)(q:A->U),
       ok p1 f1 q -> ok p2 f2 q
       -> ok (p1 * (mu b ctrue) + p2 * (mu b cfalse)) (Mif b f1 f2) q.
unfold ok; intros.
rewrite (Mif_eq b f1 f2 q).
apply Uplus_le_compat.
apply Umult_le_compat_left; auto.
apply Umult_le_compat_left; auto.
Save.

Lemma okup_ifrule :
  forall (A:Type)(b:(Distr bool))(f1 f2:Distr A)(p1 p2:U)(q:A->U),
       okup p1 f1 q -> okup p2 f2 q
       -> okup (p1 * (mu b ctrue) + p2 * (mu b cfalse)) (Mif b f1 f2) q.
unfold okup; intros.
rewrite (Mif_eq b f1 f2 q).
apply Uplus_le_compat.
apply Umult_le_compat_left; auto.
apply Umult_le_compat_left; auto.
Save.


(** *** Rule for fixpoints
with $\phi(x)=F(\phi)(x)$, $p_i$ an increasing sequence of functions starting from $0$

$\bfrac{\forall f~i, (\forall x, \ok{p_i(x)}{f}{q}) \Ra \forall x, \ok{p_{i+1}(x)}{F(f)(x)}{q}}%
     {\forall x, \ok{\bigcup_i p_i~x}{\phi(x)}{q}}$
*)
Section Fixrule.
Variables A B : Type.

Variable F : (A -o> Distr B) -m> A -o> Distr B.


Section Ruleseq.
Variable q : A -> B -> U.

Lemma fixrule_Ulub : forall (p : A -> natO -> U),
   (forall x:A, p x O == 0)->
   (forall (i:nat) (f:A->Distr B),
      (okfun (fun x => p x i) f q) -> okfun (fun x => p x (S i))  (fun x => F f x) q)
   -> okfun (fun x => Ulub (p x)) (Mfix F) q.
red; intros p p0 Hrec.
assert (forall n:nat,
        (okfun (fun x => (p x n)) (fun x => Miter F n x) q)).
induction n; simpl; auto.
red; red; intros; auto.
red; intros.
apply Ulub_le; auto.
intro n; apply Ole_trans with (mu (Miter F n x) (q x)).
apply (H n).
apply Mfix_le_iter; auto.
Save.

Lemma fixrule : forall (p : A -> natO -m> U),
   (forall x:A, p x O == 0)->
   (forall (i:nat) (f:A->Distr B),
      (okfun (fun x => p x i) f q) -> okfun (fun x => p x (S i))  (fun x => F f x) q)
   -> okfun (fun x => lub (p x)) (Mfix F) q.
red; red; intros.
rewrite <- Ulub_lub.
apply (fixrule_Ulub p H H0 x).
Save.


Lemma fixrule_up_Ulub : forall (p : A -> natO -> U),
   (forall (i:nat) (f:A->Distr B),
      (upfun (fun x => p x i) f q) -> upfun (fun x => p x (S i))  (fun x => F f x) q)
   -> upfun (fun x => Ulub (p x)) (Mfix F) q.
red; red; intros.
unfold Mfix; simpl.
apply Ole_trans with (Ulub ((Mu B @ (Miter F <o> x)) <_> q x)); auto.
apply Ulub_le_compat.
intro n; generalize x; induction n; simpl; intros; auto.
apply (H n (Miter F n) IHn x0).
Save.

Lemma fixrule_up_lub : forall (p : A -> natO -m> U),
   (forall (i:nat) (f:A->Distr B),
      (upfun (fun x => p x i) f q) -> upfun (fun x => p x (S i))  (fun x => F f x) q)
   -> upfun (fun x => lub (p x)) (Mfix F) q.
red; red; intros.
rewrite <- Ulub_lub.
apply (fixrule_up_Ulub p H x).
Save.

Lemma okup_fixrule_glb :
   forall p : A -> natO -m> UI,
   (forall (i:nat) (f:A->Distr B),
       (upfun (fun x => p x i) f q) -> upfun (fun x => p x (S i))  (fun x => F f x) q)
   -> upfun (fun x => glb (p x)) (Mfix F) q.
red; intros p Hrec x.
assert (forall n:nat,
        (upfun (fun x => (p x n))
        (fun x => (Miter F n x)) q)).
induction n; simpl; auto.
red; red; intros; auto.
red; intros.
unfold Mfix, fixp; simpl.
apply lub_glb_le; auto.
intro n; exact (H n x).
Save.
End Ruleseq.

Lemma okup_fixrule_inv : forall  (p : A -> U) (q : A -> B -> U),
   (forall (f:A->Distr B), upfun p f q -> upfun p  (fun x => F f x) q)
           -> upfun p (Mfix F) q.
unfold upfun, okup; intros.
unfold Mfix; simpl.
apply lub_le.
intro n; generalize x; induction n; simpl; auto.
Save.


(*
Section Ruleinv.

Variable p : A -> U.
Variable q : A -> B -> U.
Lemma fixruleinv :
   (forall (f:A-> Distr B), (okfun p f q) -> okfun p (fun x => F f x) q)
   -> okfun (fun x => (p x & (mu (Mfix F F_mon x) (f_one B)))) (Mfix F F_mon) q.
red; intros.
assert (forall n:nat,
        (okfun (fun x => (p x & (mu (iter F n x) (f_one B))))
        (fun x => iter F n x) q)).
induction n; simpl; auto.
repeat red; intros; auto.
repeat red; intros.
repeat red in IHn.
apply lub_le; auto.
intro n; apply Ole_trans with (mu (iter F n x) q).
apply (H0 n).
apply Mfix_le_iter; auto.
Save.
End Ruleinv.
*)

(** *** Rules using commutation properties *)

Section TransformFix.


Section Fix_muF.
Variable q : A -> B -> U.
Variable muF : MF A -m> MF A.

Definition admissible (P:(A -O-> cDistr B) -> Prop) := P 0 /\ forall f, P f -> P (F f).

Lemma admissible_true : admissible (fun f => True).
red; auto.
Save.

Lemma admissible_le_fix :
  continuous (D1:=A-O-> cDistr B) (D2:=A-O->cDistr B) F -> admissible (fun f => f <= Mfix F).
split; intros.
auto.
apply Ole_trans with (F (Mfix F)).
auto.
intro x; rewrite Mfix_eq; auto.
Save.

Lemma muF_stable : stable muF.
auto.
Save.

Definition mu_muF_commute_le  :=
  forall f x,  f <= Mfix F ->  mu (F f x) (q x) <= muF (fun y => mu (f y) (q y)) x.
Hint Unfold mu_muF_commute_le.

Section F_muF_results.
Hypothesis F_muF_le : mu_muF_commute_le.

Lemma mu_mufix_le : forall x, mu (Mfix F x) (q x) <= mufix muF x.
intros; unfold mufix,Mfix,mu_lub; simpl.
apply lub_le_compat; intros.
intro n; generalize x; induction n; simpl; intros; auto.
apply Ole_trans with (muF (fun y => mu (Miter F n y) (q y)) x0).
apply F_muF_le.
unfold Mfix,fixp; intros.
apply le_lub.
apply (fmonotonic muF); auto.
Save.
Hint Resolve mu_mufix_le.

Lemma muF_le : forall f, muF f <= f
      ->  forall x, mu (Mfix F x) (q x) <= f x.
intros; apply Ole_trans with (mufix muF x); auto.
apply mufix_inv; auto.
Save.

Hypothesis muF_F_le :
    forall f x, f <= Mfix F ->  muF (fun y => mu (f y) (q y)) x <= mu (F f x) (q x).

Lemma mufix_mu_le : forall x, mufix muF x <= mu (Mfix F x) (q x).
intros; unfold mufix,Mfix; simpl.
apply lub_le_compat; intros.
intro n; generalize x; induction n; simpl; intros; auto.
apply Ole_trans with (muF (fun y => mu (Miter F n y) (q y)) x0).
apply (fmonotonic muF); auto.
apply muF_F_le.
intro y; unfold Mfix,fixp; simpl; intros f.
apply le_lub with (c:=U) (f:=(Mu B @ (Ccpo.iter (D:=A -O-> cDistr B) F <o> y)) <_> f) (n:=n).
Save.

End F_muF_results.
Hint Resolve mu_mufix_le mufix_mu_le.

Lemma mufix_mu :
   (forall f x, f <= Mfix F -> mu (F f x) (q x) == muF (fun y => mu (f y) (q y)) x)
   -> forall x, mufix muF x == mu (Mfix F x) (q x).
intros; apply Ole_antisym; auto.
apply mufix_mu_le; intros; auto.
rewrite (H f x0); auto.
Save.
Hint Resolve mufix_mu.
End Fix_muF.

Section Fix_Term.

Definition pterm : MF A := fun (x:A) => mu (Mfix F x) (fone B).
Variable muFone : MF A -m> MF A.


Hypothesis F_muF_eq_one :
  forall f x, f <= Mfix F -> mu (F f x) (fone B) == muFone (fun y => mu (f y) (fone B)) x.

Hypothesis muF_cont :  continuous muFone.

Lemma muF_pterm :  pterm == muFone pterm.
simpl; apply ford_eq_intro; intro x; unfold pterm.
rewrite <- (mufix_mu (fun (x:A) => fone B) muFone F_muF_eq_one x).
apply Oeq_trans with (muFone (mufix muFone) x); auto.
apply (ford_eq_elim (A:=A)).
apply (mufix_eq (F:=muFone)); auto.
apply (ford_eq_elim (A:=A)).
red; apply muF_stable; auto.
simpl; apply ford_eq_intro; intro; auto.
apply (mufix_mu (fun (x:A) => fone B) muFone F_muF_eq_one n).
Save.
Hint Resolve muF_pterm.
End Fix_Term.

Section Fix_muF_Term.

Variable q : A -> B -> U.
Definition qinv x y := [1-]q x y.

Variable muFqinv : MF A -m> MF A.

Hypothesis F_muF_le_inv : mu_muF_commute_le qinv muFqinv.

Lemma muF_le_term : forall f, muFqinv (finv f) <= finv f ->
    forall x, f x & pterm x <= mu (Mfix F x) (q x).
intros; apply Ole_trans with (mu (Mfix F x) (fesp (q x) (fone B))).
apply Ole_trans with ([1-] mu (Mfix F x) (qinv x) & pterm x).
apply Uesp_le_compat; auto.
apply Uinv_le_perm_right.
apply muF_le with (muF:=muFqinv) (q:=qinv) (f:=finv f) (x:=x); auto.
unfold pterm; replace (qinv x) with (finv (q x)); auto.
apply mu_monotonic; intro; unfold fesp,fone; repeat Usimpl; auto.
Save.

Lemma muF_le_term_minus :
forall f, f <= pterm -> muFqinv (fminus pterm f) <= fminus pterm f ->
    forall x, f x <= mu (Mfix F x) (q x).
intros; apply Ole_trans with ((f x + [1-]pterm x) & pterm x).
red in H; rewrite Uplus_inv_esp_simpl; auto.
apply muF_le_term with (f:=fun y => f y + [1-]pterm y); auto.
apply Ole_trans with (muFqinv (fminus pterm f)).
apply (fmonotonic muFqinv); unfold fminus, finv; intro y.
apply Uinv_le_perm_left; auto.
apply Ole_trans with (fminus pterm f); auto.
unfold fminus, Uminus, finv; intro y; auto.
Save.

Variable muFq : MF A -m> MF A.

Hypothesis F_muF_le : mu_muF_commute_le q muFq.

Lemma muF_eq : forall f, muFq f <= f -> muFqinv (finv f) <= finv f ->
    forall x, pterm x == 1 -> mu (Mfix F x) (q x) == f x.
intros; apply Ole_antisym.
apply muF_le with (muF:=muFq); auto.
apply Ole_trans with (f x & pterm x).
rewrite H1; auto.
apply muF_le_term; auto.
Save.

End Fix_muF_Term.
End TransformFix.


Section LoopRule.
Variable q : A -> B -> U.
Variable stop : A -> Distr bool.
Variable step : A -> Distr A.
Variable a : U.

Definition Loop  : MF A -m> MF A.
exists (fun f (x:A) => mu (stop x) (fun b => if b then a else mu (step x) f)).
red; simpl; intros.
apply (mu_monotonic (stop x0)); intro b; case b; auto.
Defined.

Lemma Loop_eq :
    forall f x, Loop f x = mu (stop x) (fun b => if b then a else mu (step x) f).
trivial.
Save.

Definition loop := mufix Loop.

Lemma Mfixvar :
  (forall (f:A->Distr B),
      okfun (fun x => Loop (fun y => mu (f y) (q y)) x)  (fun x => F f x) q)
 -> okfun loop (Mfix F) q.
intros; unfold loop,mufix,fixp.
apply okfun_le_compat with (fun x => Ulub (fun n => Ccpo.iter Loop n x)) q; auto.
apply fixrule_Ulub with (p:=fun x n => Ccpo.iter Loop n x); simpl; intros;auto.
unfold okfun,ok in *|-*.
intro x; apply Ole_trans with (2:=H f x).
rewrite Loop_eq; apply (mu_monotonic (stop x)); intros.
intro b; case b; auto.
Save.

Definition up_loop : MF A := nufix Loop.

Lemma Mfixvar_up :
  (forall (f:A->Distr B),
      upfun (fun x => Loop (fun y => mu (f y) (q y)) x)  (fun x => F f x) q)
 -> upfun up_loop (Mfix F) q.
intros; unfold up_loop,nufix; simpl.
apply okup_fixrule_glb with (p:=fun x => (Ccpo.iter  (G Loop))  <o>  x); simpl; intros;intro; auto.
unfold upfun,okup in *|-*.
red; apply Ole_trans with (1:=H f x).
rewrite Loop_eq.
apply (mu_monotonic (stop x)); intro x0.
case x0; auto.
Save.

End LoopRule.

End Fixrule.

(** ** Rules for intervals *)
(** Distributions operates on intervals *)

Definition Imu : forall A:Type, Distr A-> (A->IU) -> IU.
intros A m F; exists (mu m (fun x => low (F x))) (mu m (fun x => up (F x))).
apply mu_monotonic; auto.
Defined.

Lemma low_Imu : forall (A:Type) (e:Distr A) (F: A -> IU),
             low (Imu e F) = mu e (fun x => low (F x)).
trivial.
Save.

Lemma up_Imu : forall (A:Type) (e:Distr A) (F: A -> IU),
             up (Imu e F) = mu e (fun x => up (F x)).
trivial.
Save.

Lemma Imu_monotonic : forall (A:Type) (e:Distr A) (F G : A -> IU),
            (forall x, Iincl (F x) (G x)) -> Iincl (Imu e F) (Imu e G).
unfold Iincl,Imu; simpl; intuition.
apply (mu_monotonic e); intro x; case (H x); auto.
apply (mu_monotonic e); intro x; case (H x); auto.
Save.

Lemma Imu_stable_eq : forall (A:Type) (e:Distr A) (F G : A -> IU),
            (forall x, Ieq (F x) (G x)) -> Ieq (Imu e F) (Imu e G).
unfold Ieq,Imu; simpl; intuition.
apply (mu_stable_eq e); simpl; apply ford_eq_intro; intro x; case (H x); auto.
apply (mu_stable_eq e); simpl; apply ford_eq_intro; intro x; case (H x); auto.
Save.
Hint Resolve Imu_monotonic Imu_stable_eq.

Lemma Imu_singl : forall (A:Type) (e:Distr A) (f:A->U),
           Ieq (Imu e (fun x => singl (f x))) (singl (mu e f)).
unfold Ieq,Imu,singl; simpl; intuition.
apply (mu_stable_eq e); simpl; apply ford_eq_intro; intro x; auto.
apply (mu_stable_eq e); simpl; apply ford_eq_intro; intro x; auto.
Save.

Lemma Imu_inf : forall (A:Type) (e:Distr A) (f:A->U),
           Ieq (Imu e (fun x => inf (f x))) (inf (mu e f)).
unfold Ieq,Imu,inf; simpl; intuition.
exact (mu_zero e).
apply (mu_stable_eq e); simpl; apply ford_eq_intro; intro x; auto.
Save.

Lemma Imu_sup : forall (A:Type) (e:Distr A) (f:A->U),
           Iincl (Imu e (fun x => sup (f x))) (sup (mu e f)).
unfold Iincl,Imu,inf; simpl; intuition.
Save.

Lemma Iin_mu_Imu :
   forall (A:Type) (e:Distr A) (F:A->IU) (f:A->U),
           (forall x, Iin (f x) (F x)) -> Iin (mu e f) (Imu e F).
unfold Iin,Imu; simpl; split.
apply (mu_monotonic e); intro x; case (H x); auto.
apply (mu_monotonic e); intro x; case (H x); auto.
Save.
Hint Resolve Iin_mu_Imu.

Definition Iok (A:Type) (I:IU) (e:Distr A) (F:A->IU) := Iincl (Imu e F) I.
Definition Iokfun (A B:Type)(I:A->IU) (e:A->Distr B) (F:A->B->IU)
               := forall x, Iok (I x) (e x) (F x).

Lemma Iin_mu_Iok :
   forall (A:Type) (I:IU) (e:Distr A) (F:A->IU) (f:A->U),
           (forall x, Iin (f x) (F x)) -> Iok I e F -> Iin (mu e f) I.
intros; apply Iincl_in with (Imu e F); auto.
Save.


(** *** Stability *)
Lemma Iok_le_compat : forall (A:Type) (I J:IU) (e:Distr A) (F G:A->IU),
   Iincl I J -> (forall x, Iincl (G x) (F x)) -> Iok I e F -> Iok J e G.
unfold Iok; intros; apply Iincl_trans with I; auto.
apply Iincl_trans with (Imu e F); auto.
Save.

Lemma Iokfun_le_compat : forall (A B:Type) (I J:A->IU) (e:A->Distr B) (F G:A->B->IU),
   (forall x, Iincl (I x) (J x)) -> (forall x y, Iincl (G x y) (F x y)) -> Iokfun I e F -> Iokfun J e G.
unfold Iokfun; intros; apply Iok_le_compat with (I x) (F x); auto.
Save.

(** *** Rule for values *)

Lemma Iunit_eq : forall (A: Type) (a:A) (F:A->IU), Ieq (Imu (Munit a) F) (F a).
intros; unfold Ieq,Imu,Munit; simpl; auto.
Save.


(** *** Rule for application *)

Lemma Ilet_eq : forall (A B : Type) (a:Distr A) (f:A->Distr B)(I:IU)(G:B->IU),
   Ieq (Imu (Mlet a f) G) (Imu a (fun x => Imu (f x) G)).
unfold Ieq,Imu,Mlet,Iincl; simpl; intuition.
Save.
Hint Resolve Ilet_eq.

Lemma Iapply_rule : forall (A B : Type) (a:Distr A) (f:A->Distr B)(I:IU)(F:A->IU)(G:B->IU),
    Iok I a F -> Iokfun F f (fun x => G) -> Iok I (Mlet a f) G.
unfold Iokfun,Iok;intros.
apply Ieq_incl_trans with (Imu a (fun x => Imu (f x) G0)); auto.
apply Iincl_trans with (Imu a F); auto.
Save.

(** *** Rule for abstraction *)
Lemma Ilambda_rule : forall (A B:Type)(f:A->Distr B)(F:A->IU)(G:A -> B->IU),
   (forall x:A, Iok (F x) (f x) (G x)) -> Iokfun F f G.
trivial.
Save.


(** *** Rule for conditional *)

Lemma Imu_Mif_eq : forall (A:Type)(b:Distr bool)(f1 f2:Distr A)(F:A->IU),
 Ieq (Imu (Mif b f1 f2) F) (Iplus (Imultk (mu b ctrue) (Imu f1 F)) (Imultk (mu b cfalse) (Imu f2 F))).
red; intros.
rewrite low_Imu; rewrite up_Imu.
repeat rewrite Mif_eq.
repeat rewrite low_Iplus; repeat rewrite low_Imultk.
repeat rewrite up_Iplus; repeat rewrite up_Imultk.
repeat rewrite low_Imu; repeat rewrite up_Imu; auto.
Save.

Lemma Iifrule :
  forall (A:Type)(b:(Distr bool))(f1 f2:Distr A)(I1 I2:IU)(F:A->IU),
       Iok I1 f1 F -> Iok I2 f2 F
       -> Iok (Iplus (Imultk (mu b ctrue) I1) (Imultk (mu b cfalse) I2)) (Mif b f1 f2) F.
unfold Iok; intros.
apply Ieq_incl_trans with (1:=Imu_Mif_eq b f1 f2 F).
split.
repeat rewrite low_Iplus; repeat rewrite low_Imultk.
apply Uplus_le_compat; auto.
repeat rewrite up_Iplus; repeat rewrite up_Imultk.
apply Uplus_le_compat; auto.
Save.

(** *** Rule for fixpoints
with $\phi(x)=F(\phi)(x)$, $p_i$ an decreasing sequence of intervals functions ($p_{i+1}(x)\subseteq p_i(x)$) such that $p_0(x)$ contains $0$ for all $x$.

$\bfrac{\forall f~i, (\forall x, \iok{p_i(x)}{f}{q~x}) \Ra \forall x, \iok{p_{i+1}(x)}{F(f)(x)}{q~x}}%
     {\forall x, \iok{\bigcap_i p_i~x}{\phi(x)}{q~x}}$
*)
Section IFixrule.
Variables A B : Type.

Variable F : (A -o> Distr B) -m> A -o> Distr B.

Section IRuleseq.
Variable Q : A -> B -> IU.

Variable I : A -> natO -m> IUord.

Lemma Ifixrule :
   (forall x:A, Iin 0 (I x O)) ->
   (forall (i:nat) (f:A->Distr B),
      (Iokfun (fun x => I x i) f Q) -> Iokfun (fun x => I x (S i))  (fun x => F f x) Q)
   -> Iokfun (fun x => Ilim (I x)) (Mfix F) Q.
red; intros p0 Hrec.
assert (forall n:nat,
        (Iokfun (fun x => (I x n)) (fun x => Miter F n x) Q)).
induction n; simpl; auto.
split.
rewrite low_lim; rewrite low_Imu.
apply lub_le; auto.
intro n; apply Ole_trans with (low (Imu (Miter F n x) (Q x))).
case (H n x); auto.
rewrite low_Imu; apply Mfix_le_iter; auto.
rewrite up_lim; rewrite up_Imu.
unfold Mfix,mu_lub; simpl.
apply lub_glb_le; intros.
case (H n x); auto.
Save.
End IRuleseq.

Section ITransformFix.

Section IFix_muF.
Variable Q : A -> B -> IU.
Variable ImuF : (A -o> IUord) -m> A -o> IUord.

Lemma ImuF_stable : forall I J, I==J -> ImuF I == ImuF J.
intros; apply fmon_stable with (f:=ImuF); auto.
Save.

Section IF_muF_results.
Hypothesis Iincl_F_ImuF :
    forall f x, f <= Mfix F ->
                      Iincl (Imu (F f x) (Q x)) (ImuF (fun y => Imu (f y) (Q y)) x).

Lemma Iincl_fix_ifix : forall x, Iincl (Imu (Mfix F x) (Q x)) (fixp (D:=A-O->IUcpo) ImuF x).
assert (forall n x, Iincl (Imu (Miter F n x) (Q x)) (Ccpo.iter (D:=A-O->IUcpo) ImuF n x)).
induction n; simpl; intros; auto.
apply Iincl_trans with (ImuF (fun y => Imu (Miter F n y) (Q y)) x).
apply Iincl_F_ImuF.
intro y; unfold Mfix, fixp.
intro f; simpl.
apply le_lub with (f:=(Mu B @ (Ccpo.iter (D:=A -O-> cDistr B) F <o> y)) <_> f) (n:=n); auto.
apply (fmonotonic ImuF); auto.
intros; unfold Iincl, Imu,Mfix,fixp; simpl; split.
apply lub_le_compat; intros.
intro n; case (H n x); intros.
apply Ole_trans with (low (Imu (Miter F n x) (Q x))); auto.
apply lub_glb_le; intros; auto.
case (H n x); intros.
apply Ole_trans with (up (Imu (Miter F n x) (Q x))); auto.
Save.
Hint Resolve Iincl_fix_ifix.

(*
Hypothesis Iincl_ImuF_F :
    forall f x, (forall y, le_Distr (f y) (Mfix F F_mon y)) ->
                      Iincl (ImuF (fun y => Imu (f y) (Q y)) x) (Imu (F f x) (Q x)).

Lemma Iincl_ifix_fix : forall x, Iincl (Ifix ImuF ImuF_mon x) (Imu (Mfix F F_mon x) (Q x)) .
assert (forall n x, Iincl (Iiter ImuF n x) (Imu (iter F n x) (Q x))).
induction n; simpl; intros; auto.
apply Iincl_trans with (ImuF (fun y => Imu (iter F n y) (Q y)) x).
apply IF_muF_incl.
repeat red; intros; unfold Mfix, mu_lub,mu_lub_;simpl.
apply le_lub with (f:=fun n => mu (iter F n y) f); auto.
apply ImuF_mon; auto.
intros; unfold Iincl, Ifix,Imu,Mfix,mu_lub; simpl.
unfold mu_lub_; split.
apply lub_le_compat; intros.
case (H n x); intros.
apply Ole_trans with (low (Imu (iter F n x) (Q x))); auto.
apply lub_glb_le; intros; auto.
apply (@muf_mon_succ A B F F_mon n x).
case (Iiter_decr ImuF ImuF_mon x n); auto.
case (H n x); intros.
apply Ole_trans with (up (Imu (iter F n x) (Q x))); auto.
Save.
Hint Resolve Iincl_fix_mu.

Lemma Iincl_ImuF : forall f, (forall x, Iincl (f x) (ImuF f x)) -> forall x, Iincl (Imu (Mfix F F_mon x) (Q x)) (f x).
intros; apply Iincl_trans with (Ifix ImuF ImuF_mon x); auto.
apply Iincl_inv; auto.
Save.

Hypothesis muF_F_le :
    forall f x, (forall y, le_Distr (f y) (Mfix F F_mon y)) ->
                        muF (fun y => mu (f y) (q y)) x <= mu (F f x) (q x).

Lemma mufix_mu_le : forall x, mufix muF x <= mu (Mfix F F_mon x) (q x).
intros; unfold mufix,Mfix,mu_lub; simpl.
unfold mu_lub_.
apply lub_le_compat; intros.
generalize x; induction n; simpl; intros; auto.
apply Ole_trans with (muF (fun y => mu (iter F n y) (q y)) x0).
apply muF_mon; auto.
apply muF_F_le.
repeat red; intros; unfold Mfix, mu_lub,mu_lub_;simpl.
apply le_lub with (f:=fun n => mu (iter F n y) f); auto.
Save.

End F_muF_results.
Hint Resolve mu_mufix_le mufix_mu_le.

Lemma mufix_mu :
   (forall f x, (forall y, le_Distr (f y) (Mfix F F_mon y))
          -> mu (F f x) (q x) == muF (fun y => mu (f y) (q y)) x)
   -> forall x, mufix muF x == mu (Mfix F F_mon x) (q x).
intros; apply Ole_antisym; auto.
apply mufix_mu_le; intros; auto.
rewrite (H f x0); auto.
Save.
Hint Resolve mufix_mu.
End Fix_muF.

Section Fix_Term.

Definition pterm (x:A) := mu (Mfix F F_mon x) (f_one B).
Variable muF : (A -> U) -> A -> U.

Hypothesis muF_mon : Fmonotonic muF.

Hypothesis F_muF_eq_one :
    forall f x, (forall y, le_Distr (f y) (Mfix F F_mon y))
    -> mu (F f x) (f_one B) == muF (fun y => mu (f y) (f_one B)) x.

Hypothesis muF_cont :  Fcontlub muF.

Lemma muF_pterm :  feq pterm (muF pterm).
red; intros; unfold pterm.
rewrite <- (mufix_mu (fun (x:A) => f_one B) muF_mon F_muF_eq_one x).
rewrite mufix_eq; auto.
apply muF_stable; auto.
red; intros; auto.
apply (mufix_mu (fun (x:A) => f_one B) muF_mon F_muF_eq_one x0).
Save.
Hint Resolve muF_pterm.
End Fix_Term.

Section Fix_muF_Term.

Variable muF : (A -> B -> U) -> (A -> U) -> A -> U.

Hypothesis muF_mon : forall q, Fmonotonic (muF q).

Variable q : A -> B -> U.
Definition qinv x y := [1-]q x y.

Hypothesis F_muF_le_inv :
    forall f x, (forall y, le_Distr (f y) (Mfix F F_mon y))
    -> mu (F f x) (qinv x) <= muF qinv (fun y => mu (f y) (qinv y)) x.

Lemma muF_le_term : forall f, fle (muF qinv (finv f)) (finv f) ->
    forall x, f x & pterm x <= mu (Mfix F F_mon x) (q x).
intros; apply Ole_trans with (mu (Mfix F F_mon x) (fesp (q x) (f_one B))).
apply Ole_trans with ([1-] mu (Mfix F F_mon x) (qinv x) & pterm x).
apply Uesp_le_compat; auto.
apply Uinv_le_perm_right.
apply muF_le with (muF:=muF qinv) (q:=qinv) (f:=finv f) (x:=x); auto.
unfold pterm; replace (qinv x) with (finv (q x)); auto.
apply mu_monotonic; intro; unfold fesp,f_one; repeat Usimpl; auto.
Save.

Hypothesis F_muF_le :
    forall f x, (forall y, le_Distr (f y) (Mfix F F_mon y))
    -> mu (F f x) (q x) <= muF q (fun y => mu (f y) (q y)) x.

Lemma muF_eq : forall f, fle (muF q f) f -> fle (muF qinv (finv f)) (finv f)->
    forall x, pterm x == 1 -> mu (Mfix F F_mon x) (q x) == f x.
intros; apply Ole_antisym.
apply muF_le with (muF:=muF q); auto.
apply Ole_trans with (f x & pterm x).
rewrite H1; auto.
apply muF_le_term; auto.
Save.

End Fix_muF_Term.

*)
End IF_muF_results.

End IFix_muF.
End ITransformFix.
End IFixrule.



(** ** Rules for [Flip] *)

Lemma Flip_ctrue : mu Flip ctrue == [1/2].
unfold Flip; auto.
Save.

Lemma Flip_cfalse : mu Flip cfalse == [1/2].
unfold Flip; auto.
Save.

Lemma ok_Flip :   forall q : bool -> U, ok ([1/2] * q true + [1/2] * q false) Flip q.
red; unfold Flip, flip; simpl; auto.
Save.

Lemma okup_Flip :   forall q : bool -> U, okup ([1/2] * q true + [1/2] * q false) Flip q.
red; unfold Flip, flip; simpl; auto.
Save.

Hint Resolve ok_Flip okup_Flip Flip_ctrue Flip_cfalse.

Lemma Flip_eq : forall q : bool -> U, mu Flip q == [1/2] * q true + [1/2] * q false.
intros; apply Ole_antisym; auto.
Save.
Hint Resolve Flip_eq.

Lemma IFlip_eq : forall Q : bool -> IU, Ieq (Imu Flip Q) (Iplus (Imultk [1/2] (Q true)) (Imultk [1/2] (Q false))).
red; unfold Flip, flip; simpl; auto.
Save.
Hint Resolve IFlip_eq.

(** ** Rules for total (well-founded) fixpoints *)

Section Wellfounded.
Variables A B : Type.
Variable R : A -> A -> Prop.
Hypothesis Rwf : well_founded R.
Variable F : forall x, (forall y, R y x -> Distr B) -> Distr B.

Definition WfFix : A -> Distr B := Fix Rwf (fun _ => Distr B) F.

Hypothesis Fext : forall x f g, (forall y (p:R y x), f y p == g y p) -> F f == F g.

Lemma Acc_iter_distr :
   forall x, forall r s : Acc R x, Acc_iter (fun _=> Distr B) F r == Acc_iter  (fun _=> Distr B) F s.
intros x r; elim r using Acc_inv_dep; simpl; intros.
case s; simpl; intros.
apply Fext; auto.
Save.

Lemma WfFix_eq : forall x, WfFix x == F (fun (y:A) (p:R y x) => WfFix y).
intro x; unfold WfFix,Fix.
case (Rwf x); simpl; intros.
apply Fext; intros.
apply Acc_iter_distr.
Save.

Variable P : Distr B -> Prop.
Hypothesis Pext : forall m1 m2, m1 == m2 -> P m1 -> P m2.

Lemma WfFix_ind :
     (forall x f, (forall y (p:R y x), P (f y p)) -> P (F f))
  -> forall x, P (WfFix x).
intros; pattern x; apply well_founded_ind with (R:=R); trivial; intros.
apply Pext with (m1:=  F (fun (y:A) (p:R y x0) => WfFix y)).
apply Oeq_sym; apply WfFix_eq.
apply H; auto.
Save.

End Wellfounded.

End Rules.
