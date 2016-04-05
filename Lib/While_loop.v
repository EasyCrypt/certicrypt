(** * While_loop.v : Fixpoint iteration *)

Set Implicit Arguments.

Require Import ZArith.
  
Section WHILE.

 Variable A B : Type.

 Inductive iter_res : Type :=
  | Result : B -> iter_res
  | Continue : A -> iter_res.

 Variable f : A -> iter_res.

 Definition app_iter_res f r :=
  match r with
  | Result _ => r
  | Continue a => f a 
  end.

 Fixpoint while (p:positive) (a:A) {struct p} : iter_res :=
  match p with
  | xH => f a
  | xO p => app_iter_res (while p) (while p a)
  | xI p => app_iter_res f (app_iter_res (while p) (while p a))
  end.

 Variables P1 : A -> Prop.
 Variables P2 : iter_res -> Prop.

 Hypothesis P1_f_P2 : forall a, P1 a -> P2 (f a).
 Hypothesis P2_P1 : forall a, P2 (Continue a) -> P1 a.

 Lemma while_P : forall p a, P1 a -> P2 (while p a).
 Proof.
  induction p; simpl; intros; auto.
  assert (W:= IHp a H).
  destruct (while p a); simpl; auto.
  assert (W0:= IHp a0 (P2_P1 W)). 
  destruct (while p a0); simpl; auto.
  assert (W:= IHp a).
  destruct (while p a); simpl; auto.
 Qed.

End WHILE.
