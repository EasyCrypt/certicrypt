(** * Dlist.v: Dependent lists *)


Set Implicit Arguments.

Require Export List.
Require Export EqdepFacts.
Require Export Eqdep_dec.
Require Export SetInterface. 


Section DLIST.

 Variables (A:Type) (P:A -> Type).

 Hypothesis A_dec : forall a1 a2:A, {a1 = a2} + {a1 <> a2}.

 Inductive dlist : (list A) -> Type :=
  | dnil : dlist nil
  | dcons : forall a l, P a -> dlist l -> dlist (a::l).

 Derive Dependent Inversion dlist_inv with (forall l, dlist l) Sort Type.

 Lemma dlist_nil : forall (dl:dlist nil),
  eq_dep (list A) dlist nil dl nil dnil.
 Proof.
  intros.
  apply (dlist_inv (fun l dl => eq_dep (list A) dlist l dl nil dnil) (l:=nil)); intros.
  trivial.
  discriminate.
 Qed.

 Lemma dlist_cons : forall a l (dl:dlist (a::l)), exists x, exists dl', 
  eq_dep (list A) dlist (a::l) dl (a::l) (dcons x dl').
 Proof.
  intros.
  apply (dlist_inv (fun l0 dl => exists x, exists dl',
   eq_dep (list A) dlist l0 dl (a::l) (dcons x dl')) (l:=a::l)); intros.
  discriminate.
  injection H; intros; subst; clear H.
  exists p; exists d; trivial.
 Qed.


 Section DIN.

  Variables (a:A) (x:P a).

  Fixpoint DIn (l:list A) (dl:dlist l) {struct dl}: Prop :=
   match dl with 
   | dnil => False
   | dcons a' l y dl => eq_dep A P a x a' y \/ DIn dl
   end.

 End DIN.


 Variable (f:forall a, P a -> bool).

 Fixpoint dforallb (l:list A) (dl:dlist l) : bool := 
  match dl with 
  | dnil => true
  | dcons a l pa dl => if f pa then dforallb dl else false
  end.

 Lemma dforallb_forall: forall (l : list A) (dl:dlist l),
  dforallb dl = true <-> (forall a (x:P a), DIn x dl -> f x = true).
 Proof.
  induction dl; simpl; split; intros; trivial.
  elim H0.
  case_eq (f p); intros Heq; rewrite Heq in H; [| discriminate].
  destruct H0.
  inversion H0; subst.
  rewrite (eq_dep_eq_dec A_dec H0); trivial.
  destruct IHdl; auto.
  rewrite H.
  destruct IHdl; auto.
  left; constructor.
 Qed.

End DLIST.


Section DMAP.

 Variables (A:Type) (P1 P2:A -> Type) (f:forall a, P1 a -> P2 a).

 Fixpoint dmap (l:list A) (dl: dlist P1 l) {struct dl} : dlist P2 l :=  
  match dl as t0 in (dlist _ l0) return (dlist P2 l0) with
  | dnil => dnil P2
  | dcons a l pa dl  => dcons a (f pa) (dmap dl)
  end.

End DMAP.


Section DFORALL2.

 Variables A B:Type.
 Variables (PA:A -> Type) (PB:B -> Type) (f:forall a b, PA a -> PB b -> bool).

 Fixpoint dforall2
  (la:list A) (dla : dlist PA la) 
  (lb:list B) (dlb : dlist PB lb) {struct dla} : bool :=
  match dla, dlb with
  | dnil, dnil => true
  | dcons a la pa dla, dcons b lb pb dlb =>
     if f pa pb then dforall2 dla dlb
     else false
  | _, _ => false
  end.

End DFORALL2.


Section DFOLD_RIGHT.

 Variables (A B:Type) (P : B -> Type) (f : forall b, P b -> A -> A) (a0:A).

 Fixpoint dfold_right (l:list B) (dlb : dlist P l) {struct dlb} : A :=
  match dlb with
  | dnil => a0
  | dcons b l pb dlb => f pb (dfold_right dlb)
  end.

End DFOLD_RIGHT.


Section DFOLD_LEFT.

 Variables A B:Type. 
 Variables (P:B -> Type) (f:forall b, A -> P b -> A).

 Fixpoint dfold_left (l:list B) (dlb : dlist P l) (a0:A) {struct dlb} : A :=
  match dlb with
  | dnil => a0
  | dcons b l pb dlb => dfold_left dlb (f a0 pb)
  end.

End DFOLD_LEFT.


Module MakeDep (EB:EQBOOL_LEIBNIZ).

 Module Dec.

  Definition U := EB.t. 

  Lemma eq_dec : forall (t1 t2:EB.t), {t1 = t2} + {t1 <> t2}.
  Proof.
   intros t1 t2; generalize (EB.eqb_spec t1 t2); destruct (EB.eqb t1 t2); auto.
  Qed.

 End Dec.
 
 Module Dep := DecidableEqDepSet Dec.

 Module LDec.

  Definition U := list EB.t.

  Lemma eq_dec : forall (l1 l2:list EB.t), {l1 = l2} + {l1 <> l2}.
  Proof.
   induction l1; destruct l2; auto.
   right; intro; discriminate.
   right; intro; discriminate.
   destruct (Dec.eq_dec a t).
   subst; destruct (IHl1 l2); subst; auto.
   right; intro H; apply n; inversion H; trivial.
   right; intros H; apply n; inversion H; trivial.
  Qed.

 End LDec.

 Module LDep := DecidableEqDepSet Dec.

End MakeDep.
