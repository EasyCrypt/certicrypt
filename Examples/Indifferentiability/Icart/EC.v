Require Import Field_tac.
Require Import EGroup.
Require Import FGroup.
Require Import UList.
Require Import Arith.
Require Import ZAux.
Require Import Znumtheory.
Require Export Operators.
Require Import Arith.Euclid.
Require Import Padding.
Require Import SMain.


Require Import ssreflect eqtype 
 ssrbool ssrfun fingroup Ssreflect.choice fintype ssrnat seq finalg ssralg.   

Require Import abelian Ssreflect.cyclic bigop gproduct finset div.

Open Scope nat_scope.

Set Implicit Arguments.

Module Type FIELD <: FINITE_TYPE.

  Parameter t : nat -> Type.

  Parameter default : forall k, t k.

  Parameter eqb : forall k, t k -> t k -> bool.

  Parameter eqb_spec : forall k (x y:t k), 
   if eqb x y then x = y else x <> y.

  Parameter eqb_refl : forall k (x:t k), eqb x x.
 
  Parameter elems : forall k, list (t k).

  Parameter elems_poly : polynomial.

  Parameter elems_full : forall k (x:t k), In x (elems k).

  Parameter elems_NoDup : forall k, NoDup (elems k).

  Parameter elems_size_nat : forall k,
    le (size_nat (List.length (elems k))) (peval elems_poly k).

  Parameter elems_notnil : forall k, elems k <> List.nil.

  Parameters kO kI : forall k, t k.

  Parameters kplus kmul ksub kdiv: forall k, t k -> t k -> t k.

  Parameters kopp kinv : forall k, t k-> t k.

  Parameter is_zero : forall k, t k -> bool.

  Parameter K_field : forall k, 
   field_theory (kO k) (kI k) (@kplus k) (@kmul k) (@ksub k) 
   (@kopp k) (@kdiv k) (@kinv k) (@eq (t k)).

  Parameter kinv_kO : forall k,
    kinv (@kO k) = (@kO k).

  Parameter diff_2_0 : forall k, kplus (kI k) (kI k) <> (kO k).
  Parameter diff_3_0 : forall k, kplus (kplus (kI k) (kI k)) (kI k) <> (kO k).

  Parameter diff_mul_0: forall k (x1 x2:t k), 
   x1 <> (kO k) -> x2 <> kO k -> kmul x1 x2 <> kO k.
  
  Definition order k := length (elems k).

  Definition orderZ k := Z_of_nat (length (elems k)).

  Fixpoint kpow (k:nat) x (n:nat) : t k :=
   match n with
    | O => kI k
    | S n' => kmul x (kpow k x n')
   end.

  Parameter one_not_zero : forall k, (kI k) <> (kO k).

  Parameter two_not_zero : forall k, kplus (kI k) (kI k) <> (kO k).

  Parameter is_zero_correct : forall k n , is_zero n = true <-> n = (kO k).

  Parameter fermat : forall k x, kpow x (order k - 1)  = kI k.

  Parameter order_mod1 order_mod2 : nat -> Z.

  Parameter order_mod : forall k, 
   ((orderZ k) mod (order_mod1 k) = (order_mod2 k))%Z.

End FIELD.

Module Type CURVE_PROPERTIES (A : FIELD).

  Import A.

  Parameter A B : forall k, A.t k.

  Parameter NonSingular : forall k, kplus  (kmul (kmul (kmul (kmul (kplus (kI k) (kI k)) (kplus (kI k) (kI k))) (A k)) (A k)) (A k))
  (kmul (kmul (kmul (kmul (kplus (kplus (kI k) (kI k)) (kI k)) (kplus (kplus (kI k) (kI k)) (kI k)))
    (kplus (kplus (kI k) (kI k)) (kI k))) (B k)) (B k)) <> (kO k).

End CURVE_PROPERTIES.

 Lemma NoDup_ulist : forall A (l : list A),
   NoDup l <-> ulist l.
 Proof.
  induction l; split; intros; constructor; inversion H; auto; tauto.
 Qed.

Module EC_BASE  (A : FIELD) (CP : CURVE_PROPERTIES A).

 Import A CP.

 Lemma Eth : forall k, ell_theory (kO k) (kI k) (@kplus k) (@kmul k) (@ksub k) (@kopp k) (@kinv k) (@kdiv k) (A k) (B k) (@is_zero k).
 Proof.
  intros; constructor.
  apply K_field.
  apply NonSingular.
  apply one_not_zero.
  apply two_not_zero.
  apply is_zero_correct.
 Qed.
 
 Definition t (k : nat) : Type := elt (kI k) (@kplus k) (@kmul k) (A k) (B k).

 Definition eqb k (x y : t k) : bool :=
  match ceqb (Eth k) x y with 
   | left _ => true
   | right _ => false
  end.

 Lemma eqb_spec : forall k (x y:t k), if eqb x y then x = y else x <> y.
 Proof.
  intros k x y; unfold eqb.
  case (ceqb (Eth k) x y); intro; trivial.
 Qed.

 Definition e (k : nat) := inf_elt (kI k) (@kplus k) (@kmul k) (A k) (B k).

 Definition inv (k : nat) (x : t k) : t k := opp (Eth k) x.

 Definition mul (k : nat) (x y : t k) : t k := add (Eth k) x y.

 Lemma mul_comm : forall k (x y: t k), mul x y = mul y x.
 Proof.
  intros k x y; unfold mul.
  rewrite add_comm; trivial.
 Qed.

 Lemma mul_assoc : forall k (x y z:t k), mul x (mul y z) = mul (mul x y) z.
 Proof.
  intros k x y z ; unfold mul.
  rewrite add_assoc; trivial.
 Qed.

 Lemma inv_spec : forall k (x:t k), mul x (inv x) = e k.
 Proof.
  intros k x; unfold mul, inv, e; simpl.
  apply add_opp.
 Qed.

 Lemma mul_e_r : forall k (x:t k), mul x (e k) = x.
 Proof.
  intros k x; unfold mul, e; simpl.
  apply add_0_r.
 Qed.
 
 (** Complexity specification *)
 Parameter cost_mul : forall k (x y:t k), nat.

 Parameter cost_inv : forall k (x:t k), nat.

 Parameter cost_mul_poly : polynomial.

 Parameter cost_mul_poly_spec : forall k (x y:t k),
   le (@cost_mul k x y) (peval cost_mul_poly k).

End EC_BASE.
   
Module EC   (A : FIELD) (CP : CURVE_PROPERTIES A) <: CFG.

  Import A CP.

  Module ECB := EC_BASE A CP.
  Import ECB.

 Lemma ULK : forall k, ulist (A.elems k).
 Proof. intros; apply NoDup_ulist; apply A.elems_NoDup. Qed.

 Lemma CLK : forall k (x : A.t k), In x (A.elems k).
 Proof. intros; apply A.elems_full. Qed.
 
 Definition efgroup k := EFGroup (@Eth k) (ULK k) (@CLK k).

 Section K.

   Variable k : nat.

 (* A is an EqType *) 
 Add Field Kfield : (@A.K_field k) (abstract).

 Lemma eqbA : Equality.axiom (@A.eqb k).
 Proof.
  move => a b.
  have H := A.eqb_spec a b.
  apply: (iffP idP); move => H1.
    by rewrite H1 /= in H.
  move: H; rewrite H1.
  by case (A.eqb b b).
 Qed.

 Canonical Structure A_eqMixin := Eval hnf in EqMixin eqbA.
 Canonical Structure A_eqType :=
   Eval hnf in EqType (@A.t k) A_eqMixin.

 (* A is ChoiceType and CountType *)
 Definition pickle (a : A.t k) : nat :=
   find (fun x => A.eqb x a) (A.elems k).

 Definition unpickle (n:nat) : option (A.t k) :=
   if n < (length (A.elems k))
   then Some (seq.nth (A.kO k) (A.elems k) n)
     else None.

 Lemma A_has_In : forall x,
   has (fun x0 : A.t k => @A.eqb k x0 x) (A.elems k) = true.
 Proof.
  move=> x.
  move: (A.elems_full x).
  elim: (A.elems k); rewrite /= //.
  move=> a l IH; case.
  move ->.
  by apply /orP; left; apply /eqP.
  move => H.
  by apply /orP; right; apply: IH.
 Qed.

 Lemma pickleK : pcancel pickle unpickle.
 Proof.
  move=> x.
  rewrite /unpickle /pickle.
  case H : (find (fun a => A.eqb a x) (A.elems k) < length (A.elems k)).
  f_equal.
  apply: eqP.
  apply: (@nth_find _ (A.kO k) (fun x0 : A.t k => @A.eqb k x0 x) (A.elems k)).
  rewrite has_find.
  have <- : (length (A.elems k) = size (A.elems k)).
  elim: (A.elems k) => //=.
  by move => y l ->.
  apply: H.
  move: H.
  have ->  : (length (A.elems k) = size (A.elems k)).
  elim: (A.elems k) => //=.
  by move => _ l ->.
  by rewrite -has_find A_has_In.
 Qed.

Definition ACountMixin := PcanCountMixin pickleK.
Definition AChoiceMixin := PcanChoiceMixin pickleK.

Canonical Structure AChoiceType := 
  Eval hnf in ChoiceType _ AChoiceMixin.
Canonical Structure ACountType := 
  Eval hnf in CountType _ ACountMixin.

(* A is a FinType *)
Lemma In_count : forall (t : eqType) (x : t) l,
  ~In x l -> count (pred1 x) l= 0.
Proof.
 move => t x l; elim: l => //=.
 move => a l IH H.
 apply Decidable.not_or in H.
 case: H; move => H1 H2.
 case: (boolP (a == x)); move => Hb.
 by elim H1; apply /eqP.
 rewrite IH //=.
 Qed.
 
Lemma NoDup_count : forall (t : eqType) (x : t) l,
  In x l ->
  NoDup l ->
  count (pred1 x) l = 1.
Proof.
 move => t x l.
 elim: l => //=.
 move => a l IH; case => Ha.
 rewrite Ha.
 rewrite eqxx // => H.
 inversion H; subst.
 rewrite In_count //=.
 move => H; inversion H; subst.
 rewrite IH //=.
 case: (boolP (a == x)); move => Hb //=. 
 by move /eqP : Hb H2 => ->.
Qed.

 Lemma A_enumP : Finite.axiom (A.elems k). 
 Proof.
  unfold Finite.axiom; intros.
  apply NoDup_count.
  apply: A.elems_full.
  apply: A.elems_NoDup.
 Qed.

Definition AfinMixin := Eval hnf in FinMixin A_enumP.
Canonical Structure AfinType := Eval hnf in FinType _ AfinMixin.

(* A is a Field *)
 Definition AZmodMixin : GRing.Zmodule.mixin_of (A.t k).
 refine (@ZmodMixin (A.t k) (A.kO k) (@A.kopp k) (@A.kplus k) _ _ _ _ ); move => *; field.
 Defined.

 Canonical Structure AZmodType := Eval hnf in ZmodType (A.t k) AZmodMixin.
 Canonical Structure AfinZmodType := Eval hnf in [finZmodType of (A.t k)].

 Lemma Acomm : commutative (@A.kmul k).
 Proof. move => *; field. Qed.

 Lemma Aass : associative (@A.kmul k).
 Proof. move => *; field. Qed.

 Lemma Aleft_id :  left_id (@A.kI k) (@A.kmul k).
 Proof. move => *; field. Qed.

 Lemma Aleft_dist :  left_distributive (@A.kmul k) (@A.kplus k).
 Proof. move => *; field. Qed.

 Lemma Aone_diff_zero : ~~ (A.kI k == 0%R).
 Proof. by apply /eqP => H; apply: (@A.one_not_zero k). Qed.

 Definition AringMixin := ComRingMixin Aass Acomm Aleft_id  Aleft_dist Aone_diff_zero.

 Canonical Structure AringType := Eval hnf in RingType (A.t k) AringMixin.
 Canonical Structure AfinRingType := Eval hnf in [finRingType of (A.t k)].

 Lemma AmulC : commutative (GRing.Ring.mul (GRing.Ring.class AringType)).
 Proof. move => * /=; field. Qed.
 
 Canonical Structure AcomRingType := Eval hnf in ComRingType (@A.t k) AmulC.
 Canonical Structure AfinComRingType := Eval hnf in [finComRingType of (A.t k)].

 Lemma AmulVz : forall x, ~~ A.eqb x (A.kO k) -> A.kmul (A.kinv x) x = A.kI k.
 Proof. by move=> x H; field; move=> W; move /eqP: H. Qed.
 
 Lemma Ainv_out : forall x, ~~ ~~ A.eqb x (A.kO k) -> A.kinv x = x.
 Proof. 
   move => x H; rewrite negb_involutive in H.
   move /eqP : H ->; apply A.kinv_kO.
  Qed.

Lemma Aintro_unit : forall x y, A.kmul y x = A.kI k -> ~~ A.eqb x (A.kO k).
Proof.
  move=> x y H.
  apply /eqP => W.
  rewrite W in H.
  move: H.
  have -> : ( A.kmul y (A.kO k) = A.kO k) by field.
  move => H.
  by apply: (@one_not_zero k).
Qed.

 Definition AunitRingMixin :=
  ComUnitRingMixin AmulVz Aintro_unit Ainv_out.

 Canonical Structure AunitRingType :=
   Eval hnf in UnitRingType (A.t k) AunitRingMixin.
 Canonical Structure AfinUnitRingType := Eval hnf in [finUnitRingType of (A.t k)].
 Canonical Structure AcomUnitRingType := Eval hnf in [comUnitRingType of (A.t k)].
 Canonical Structure AfinComUnitRingType :=
   Eval hnf in [finComUnitRingType of (A.t k)].

 Lemma AfieldMixin : GRing.Field.mixin_of [the unitRingType of (A.t k)].
 Proof. by move=> x nzx; rewrite /GRing.unit /=. Qed.

 Definition AidomainMixin := FieldIdomainMixin AfieldMixin.
 
 Canonical Structure AidomainType :=
   Eval hnf in IdomainType (A.t k)  AidomainMixin.
 Canonical Structure AfinIdomainType := Eval hnf in [finIdomainType of (A.t k)].
 Canonical Structure AfieldType := Eval hnf in FieldType (A.t k) AfieldMixin.
 Canonical Structure AfinFieldType := Eval hnf in [finFieldType of (A.t k)].
 Canonical Structure AdecFieldType :=
   Eval hnf in [decFieldType of (A.t k) for AfinFieldType].

 (* G is a EqType *)

 Lemma eqbP : Equality.axiom (@eqb k).
 Proof.
  move => a b.
  have H := eqb_spec a b.
  apply: (iffP idP); move => H1.
    by rewrite H1 /= in H.
  move: H; rewrite H1.
  by case (eqb b b).
 Qed.

 Canonical Structure G_eqMixin := Eval hnf in EqMixin eqbP.
 Canonical Structure G_eqType := 
   Eval hnf in EqType (@t k) G_eqMixin.

(*
   G is a ChoiceType : 
   Bijection between A*A and elt to proof ChoiceType for elt
   A * A => A * A + proof => option (A * A + proof) => elt
*)

 (* A * A *)
 Definition prodA : choiceType := prod_choiceType ACountType AChoiceType.

 (* A * A => A * A + proof *)
 Definition in_curve : pred prodA :=
   fun pair => A.eqb
     (pow (A.kI k) (@A.kmul k) pair.2 2)
     (A.kplus (A.kplus (pow (@A.kI k) (@A.kmul k) pair.1 3) (A.kmul (CP.A k) pair.1)) (CP.B k)).

 Definition prodA_sig_choiceMixin :=
   [choiceMixin of {x | in_curve x} by <:].
 Canonical Structure prodA_sig_choiceType :=
   Eval hnf in ChoiceType {x | in_curve x} prodA_sig_choiceMixin.
 
 (* A * A + proof => option (A * A + proof) *)
 Definition opt_prod_A : choiceType := option_choiceType prodA_sig_choiceType.

 (* option (A * A + proof) => elt *)
 Definition f_inj (x : t k) : opt_prod_A.
 case; first by exact: None.
 move => x y H.
 refine (Some (exist _ (x, y) _)).
 by rewrite /in_curve //=; apply /eqP.
 Defined.

 Definition f'_inj (x : opt_prod_A) : t k.
 case; last by (exact: inf_elt).
 case; case => x y; rewrite /in_curve => /eqP H.
 by refine (@curve_elt _ _ _ _ _ _ x y _).
 Defined.
 
 Lemma K_f_inf : cancel f_inj f'_inj.
 Proof. case => //= x y H; apply: (curve_elt_irr (Eth k)) => //. Qed.

 Definition GChoiceMixin := CanChoiceMixin K_f_inf.
 Canonical Structure GChoiceType :=
   Eval hnf in ChoiceType _ GChoiceMixin.

 (* G is a CountType *) 
 Definition elems : list (t k) :=
   FELLK (Eth k) (A.elems k) (@A.elems_full k).

 Definition Gpickle (a : t k) : nat :=
   find (fun x => x == a) elems.

 Definition Gunpickle (n:nat) : option (@t k) :=
   if n < (length elems)
   then Some (@nth (@t k) (@e k)  elems n)
     else None.

 Lemma G_has_In : forall x,
   has (fun x0 : t k => x0 == x) elems = true.
 Proof.
  move=> x.
  move: (@FELLK_in _ _ _ _ _ _ _ _ _ _ _ _ (@Eth k) (A.elems k) (@A.elems_full k) x).
  rewrite /elems.
  elim: (FELLK (Eth k) (A.elems k) (@A.elems_full k)); rewrite //=.
  move=> a l IH; case.
  by move ->; apply /orP; left; apply /eqP.
  by move => H; apply /orP; right; apply: IH.
 Qed.

 Lemma GpickleK : pcancel (@Gpickle) (@Gunpickle).
 Proof. 
  move=> x; rewrite /Gunpickle /Gpickle.
  case_eq ((seq.find (fun a => a == x)  elems) < (length elems) ); intros.
  f_equal.
  apply /eqP.
  apply: (@nth_find _ (e k) (fun x0 : t k => @eqb k x0 x) elems).
  rewrite has_find.
  have <- : (length elems = size  elems).
  elim: elems => //=.
  by move => y l ->.
  apply: H.
  move: H.
  have -> : (length elems = size elems).
  elim: elems => //=.
  by move => _ l ->.
  by rewrite -has_find G_has_In.
 Qed.

 Definition GCountMixin := PcanCountMixin GpickleK.
 Canonical Structure GCountType := Eval hnf in CountType _ GCountMixin.
 
 (* G is a FinType *)
 Lemma GenumP : Finite.axiom elems.
 Proof.
  rewrite /Finite.axiom; move=> x.
  apply NoDup_count.
  apply: FELLK_in.
  apply NoDup_ulist.
  apply: FELLK_ulist.
  apply NoDup_ulist.
  apply: A.elems_NoDup.
 Qed.
 
 Definition GfinMixin := Eval hnf in FinMixin GenumP.
 Canonical Structure GfinType := Eval hnf in FinType _ GfinMixin.

 (* G is a FinGroup *)
 Definition GroupMixin : FinGroup.mixin_of (@t k).
  refine (@FinGroup.BaseMixin (@t k) (@mul k) (@e k) (@inv k) _ _ _ _).
  apply: mul_assoc.
  move=> x; rewrite mul_comm; apply: mul_e_r.
  apply: opp_opp.
  move=> x y /=; rewrite mul_comm; apply: opp_add.
 Defined.

 Lemma left_inv : left_inverse (e k) (@inv k) (@mul k).
 Proof. move=> x; rewrite mul_comm; apply: inv_spec. Qed.
 
 Canonical Structure T := 
   Eval hnf in BaseFinGroupType _ GroupMixin.
 
  Lemma mulg_comm : forall (x y:T), mulg x y = mulg y x.
  Proof.
   move=> x y.
   rewrite /mulg /=.
   apply mul_comm.
  Qed.

  (* Definition elems : forall k, list (T k). *)
  Lemma elems_full : forall t, In t elems.
  Proof.
   move=> t.
   apply: (@FELLK_in _ _ _ _ _ _ _ _ _ _ _ _ (@Eth k) (A.elems k) (@A.elems_full k) t).
  Qed.

  Lemma elems_NoDup : NoDup elems.
  Proof.
    rewrite NoDup_ulist.
    apply FELLK_ulist.
    rewrite -NoDup_ulist.
    apply A.elems_NoDup.
  Qed.

  End K.

  End EC.
    
    
