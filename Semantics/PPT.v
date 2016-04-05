(** * PPT.v: Theory of probabilistic polynomial time programs *)

Set Implicit Arguments.

Require Import BaseProp.

Open Scope nat_scope.


(** User-defined operators and distributions *)
Module Type UPPT (Sem:SEM) (ST:SEM_THEORY Sem).
 
 Export Sem.
 Export ST.
 
 Implicit Arguments T.size [k t].

 (** PPT expression *)
 Definition PPT_expr (t:T.type) (e:E.expr t) 
  (F:polynomial -> polynomial) 
  (G:polynomial -> polynomial) : Prop := 
  forall k (m:Mem.t k) p,
   (forall t (x:Var.var t), 
    Vset.mem x (fv_expr e) -> T.size (m x) <= peval p k)  ->
   let (v,n) := E.ceval_expr e m in
    T.size v <= peval (F p) k /\
    n <= peval (G p) k.

 (** PPT support *)
 Definition PPT_support t (s:E.support t)
  (F:polynomial -> polynomial) 
  (G:polynomial -> polynomial) : Prop :=
  forall k (m:Mem.t k) p,
   (forall t (x:Var.var t), 
    Vset.mem x (fv_distr s) -> T.size (m x) <= peval p k)  ->
   let (l,n) := E.ceval_support s m in
    (forall v, In v l -> T.size v <= peval (F p) k) /\
    n <= peval (G p) k.

 Parameter utsize : UT.t -> nat.

 Parameter utsize_default_poly : nat -> polynomial.

 Parameter utsize_default_poly_spec : forall r ut,
  utsize ut <= r -> 
  forall k, UT.size (UT.default k ut) <= peval (utsize_default_poly r) k.

 Parameter uop_poly : Uop.t -> bool.

 Parameter uop_poly_spec : forall o (la:dlist E.expr (O.targs (O.Ouser o))),
   uop_poly o ->
   (forall t (e:E.expr t), @DIn _ E.expr _ e _ la -> 
    exists F, exists G, PPT_expr e F G) ->
   exists F, exists G, PPT_expr (E.Eop (O.Ouser o) la) F G.

 Parameter usupport_poly : forall t, US.usupport t -> bool.

 Parameter usupport_poly_spec : forall t (us:US.usupport t),
  usupport_poly us ->
  exists F, exists G, PPT_support (E.Duser us) F G.

End UPPT.


(** Decision procedure for PPT programs and expressions *)
Module Make_PPT (Sem:SEM) (ST:SEM_THEORY Sem) (U:UPPT Sem ST).

 Import U.

 Module VarP := MkEqBool_Leibniz_Theory Var.
 Module VsetP := MkSet_Theory Vset.

 Implicit Arguments T.size [k t]. 

 Fixpoint tsize (t:T.type) : nat :=
  match t with 
  | T.User ut => utsize ut
  | T.Pair t1 t2 => tsize t1 + tsize t2 + 1
  | T.Sum t1 t2 => tsize t1 + tsize t2 + 1
  | _ => 0
  end.

 (** PPT expression *)
 Definition PPT_expr (t:T.type) (e:E.expr t) 
  (F:polynomial -> polynomial) 
  (G:polynomial -> polynomial) : Prop :=
  forall k (m:Mem.t k) p,
   (forall t (x:Var.var t), 
    Vset.mem x (fv_expr e) -> T.size (m x) <= peval p k)  ->
   let (v,n) := E.ceval_expr e m in
    T.size v <= peval (F p) k /\
    n <= peval (G p) k.

 (** PPT support *)
 Definition PPT_support t (s:E.support t)
  (F:polynomial -> polynomial) 
  (G:polynomial -> polynomial) : Prop :=
  forall k (m:Mem.t k) p,
   (forall t (x:Var.var t), 
    Vset.mem x (fv_distr s) -> T.size (m x) <= peval p k)  ->
   let (l,n) := E.ceval_support s m in
    (forall v, In v l -> T.size v <= peval (F p) k) /\
    n <= peval (G p) k.


 (** Expressions *)
 
 Lemma PPT_bool : forall b:bool, 
  PPT_expr b (fun _ => pcst 1) (fun _ => pcst 1).
 Proof.
  unfold PPT_expr; intros; simpl.
  rewrite pcst_spec; auto.
 Qed.
 
 Lemma PPT_nat : forall n:nat, 
  PPT_expr n (fun _ => size_nat n) (fun _ => size_nat n).
 Proof.
  unfold PPT_expr; intros; simpl.
  rewrite pcst_spec; auto.
 Qed.

 Lemma PPT_Z : forall n:Z, 
  PPT_expr n (fun _ => size_Z n) (fun _ => size_Z n).
 Proof.
  unfold PPT_expr; intros; simpl.
  rewrite pcst_spec; auto.
 Qed.

 Lemma PPT_enil : forall t, 
  PPT_expr (Nil t)  (fun _ => pcst 1) (fun _ => pcst 1).
 Proof.
  unfold PPT_expr; intros; simpl.
  rewrite pcst_spec; auto.
 Qed.

 Lemma PPT_var : forall t (x:Var.var t),
  PPT_expr x (fun p => p) (fun _ => pcst 1).
 Proof.
  unfold PPT_expr; intros; simpl.
  split; [ | rewrite pcst_spec; trivial].
  apply H; simpl. 
  unfold fv_expr; simpl.
  apply Vset.add_correct; trivial.
 Qed.

 Lemma PPT_eq : forall t (e1:E.expr t) (e2:E.expr t) F1 G1 F2 G2,
  PPT_expr e1 F1 G1 -> PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop (O.Oeq_ t) {e1, e2})
   (fun p => pcst 1)
   (fun p => pplus (pplus (F1 p) (F2 p)) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros t e1 e2 F1 G1 F2 G2 He1 He2 k m p Hm.
  split; simpl.
  rewrite pcst_spec; trivial.
  rewrite pplus_spec.
  generalize (He1 k m p) (He2 k m p); clear He1 He2.
  case_eq (E.ceval_expr e1 m); simpl.
  case_eq (E.ceval_expr e2 m); simpl.
  intros i n Heqi i0 n0 Heqi0 Hi Hi0.
  destruct Hi.
  intros; apply Hm; simpl.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].  
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  destruct Hi0.
  intros; apply Hm; simpl.
  apply Vset.subset_correct with (fv_expr e2); [ | trivial].  
  unfold fv_expr at 2; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec.
  apply VsetP.subset_union_l.
  apply plus_le_compat.
  rewrite E.ceval_expr_spec, Heqi0; trivial.
  rewrite E.ceval_expr_spec, Heqi; trivial.
  simpl; rewrite pplus_spec.
  apply plus_le_compat; trivial.
  rewrite plus_0_r, pplus_spec.
  apply plus_le_compat; trivial.
 Qed.

 Lemma List_size_length : forall k t (l:T.interp k (T.List t)),
   length l <= T.size (k:=k) (t:=T.List t) l.
 Proof.
  induction l; simpl; auto.
  apply le_n_S; apply le_trans with (1:= IHl); apply le_plus_r.
 Qed.

 Lemma cexistsb_count : forall A (f:A -> bool * nat) p l,
   (forall a, In a l -> snd (f a) <= p) ->
   forall n, snd (cexistsb f l n) <= length l * p + n.
 Proof.
  induction l; simpl; intros; trivial.
  case_eq (f a); intros.
  assert (n0 <= p).
   assert (W:= H a); rewrite H0 in W; simpl in W; apply W; auto.
  destruct b; simpl.
  rewrite plus_comm; apply plus_le_compat; trivial.
  apply le_trans with (1:= H1).
  apply le_plus_l.
  assert (forall a0 : A, In a0 l -> snd (f a0) <= p) by (intros; apply H; auto).
  apply le_trans with (1:= IHl H2 (n + n0)).
  rewrite (plus_comm p), <- plus_assoc, (plus_comm p).
  apply plus_le_compat;[trivial | apply plus_le_compat; trivial].
 Qed.

 Lemma cforallb_count : forall A (f:A -> bool * nat) p l,
   (forall a, In a l -> snd (f a) <= p) ->
   forall n, snd (cforallb f l n) <= length l * p + n.
 Proof.
  induction l; simpl; intros; trivial.
  case_eq (f a); intros.
  assert (n0 <= p).
   assert (W:= H a); rewrite H0 in W; simpl in W; apply W; auto.
  destruct b; simpl.
  assert (forall a0 : A, In a0 l -> snd (f a0) <= p) by (intros; apply H; auto).
  apply le_trans with (1:= IHl H2 (n + n0)).
  rewrite (plus_comm p), <- plus_assoc, (plus_comm p).
  apply plus_le_compat;[trivial | apply plus_le_compat; trivial].
  rewrite plus_comm; apply plus_le_compat; trivial.
  apply le_trans with (1:= H1).
  apply le_plus_l.
 Qed.

 Lemma cfind_default_count : forall A (f:A -> bool * nat) p l def,
   (forall a, In a l -> snd (f a) <= p) ->
   forall n, snd (cfind_default f l n def) <= length l * p + n.
 Proof.
  induction l; simpl; intros; trivial.
  unfold cfind_default in *; simpl.
  case_eq (f a); intros.
  assert (n0 <= p).
   assert (W:= H a); rewrite H0 in W; simpl in W; apply W; auto.
  destruct b; simpl.
  rewrite plus_comm; apply plus_le_compat; trivial.
  apply le_trans with (1:= H1).
  apply le_plus_l.
  assert (forall a0 : A, In a0 l -> snd (f a0) <= p) by (intros; apply H; auto).
  apply le_trans with (1:= IHl def H2 (n + n0)).
  rewrite (plus_comm p), <- plus_assoc, (plus_comm p).
  apply plus_le_compat;[trivial | apply plus_le_compat; trivial].
 Qed.

 Lemma List_size_le : forall k t (l:T.interp k (T.List t)),
    forall a: T.interp k t, In a l -> T.size (k:=k) (t:=t) a <= T.size (k:=k) (t:=T.List t) l.
 Proof.
  induction l; simpl; intros a0 Hin; destruct Hin; apply le_S.
  rewrite H; apply le_plus_l.
  apply le_trans with (1:= IHl _ H); apply le_plus_r.
 Qed.

 Lemma PPT_length : forall t e F G,
  PPT_expr e F G ->
  PPT_expr (E.Eop (O.Olength t) {e}) 
  (fun p => pplus 1 (F p)) (fun p => pplus (F p) (G p)).
 Proof.
  unfold PPT_expr; intros t e F G0 He k m p H.
  generalize (He k m p H); clear H He.
  simpl; rewrite E.ceval_expr_spec.
  case (E.ceval_expr e m); intros l n [Hl Hn].
  assert (W:length l <= peval (F p) k).
   apply le_trans with (2:= Hl); refine (List_size_length l).
  simpl fst; split.
  rewrite pplus_spec, pcst_spec.
  apply le_trans with (S (length l)).
  case (length l).  
  trivial.
  intro n0; apply le_trans with (S n0); auto with arith.
  apply size_nat_le; auto with arith.
  simpl; apply le_n_S; trivial.
  simpl; rewrite plus_0_r, pplus_spec; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_Zlength : forall t e F G,
  PPT_expr e F G ->
  PPT_expr (E.Eop (O.OZlength t) {e}) 
  (fun p => pplus 1 (F p)) (fun p => pplus (F p) (G p)).
 Proof.
  unfold PPT_expr; intros t e F G0 He k m p H.
  generalize (He k m p H); clear H He.
  simpl; rewrite E.ceval_expr_spec.
  case (E.ceval_expr e m); intros l n [Hl Hn].
  assert (W:length l <= peval (F p) k).
   apply le_trans with (2:= Hl); refine (List_size_length l).
  simpl fst; split.
  rewrite pplus_spec, pcst_spec.
  apply le_trans with (S (length l)).
  case (length l).  
  trivial.
  intro n0; apply le_trans with (S n0); auto with arith.
  unfold size_Z; rewrite Zabs_nat_Z_of_nat.
  apply size_nat_le; auto with arith.
  simpl; apply le_n_S; trivial.
  simpl; rewrite plus_0_r, pplus_spec; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_head : forall t e F G,
  PPT_expr e F G ->
  PPT_expr (E.Eop (O.Ohd t) {e}) 
   (fun p => pplus (T.default_poly t) (F p)) (fun p => pplus 1 (G p)).
 Proof.
  unfold PPT_expr; intros t e F G0 He k m p H.
  generalize (He k m p H); clear H He.
  simpl; rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e m) as [l]; simpl; intros; split.
  destruct l as [ | a l].
  eapply le_trans; [ | apply pplus_le_l].
  simpl; apply T.default_poly_spec.
  destruct H as [H _]; simpl in H |- *.
  eapply le_trans; [ | apply pplus_le_r].
  apply le_trans with (2:=H); auto with arith.
  destruct H.
  rewrite plus_0_r, pplus_spec, pcst_spec; apply le_n_S; trivial.
 Qed.

 Lemma PPT_tail : forall t e F G,
  PPT_expr e F G ->
  PPT_expr (E.Eop (O.Otl t) {e}) F (fun p => pplus 1 (G p)).
 Proof.
  unfold PPT_expr; intros t e F G0 He k m p H.
  generalize (He k m p H); clear H He.
  simpl; rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e m); simpl; intros [H1 H2]; split.
  destruct i; simpl in H1 |- *.
  trivial.
  eapply le_trans; [ |apply H1].
  auto with arith.
  rewrite plus_0_r, pplus_spec, pcst_spec; apply le_n_S; trivial.
 Qed.

 Lemma PPT_fst : forall t1 t2 e F G,
  PPT_expr e F G ->
  PPT_expr (E.Eop (O.Ofst t1 t2) {e}) F (fun p => pplus 1 (G p)).
 Proof.
  unfold PPT_expr; intros t1 t2 e F G0 He k m p H.
  generalize (He k m p H); clear H He.
  simpl; rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e m); simpl; intros [H1 H2]; split.
  eapply le_trans; [ |apply H1]; auto with arith.
  rewrite plus_0_r, pplus_spec, pcst_spec; apply le_n_S; trivial.
 Qed.

 Lemma PPT_snd : forall t1 t2 e F G,
  PPT_expr e F G ->
  PPT_expr (E.Eop (O.Osnd t1 t2) {e}) F (fun p => pplus 1 (G p)).
 Proof.
  unfold PPT_expr; intros t1 t2 e F G0 He k m p H.
  generalize (He k m p H); clear H He.
  simpl; rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e m); simpl; intros [H1 H2]; split.
  eapply le_trans; [ |apply H1]; auto with arith.
  rewrite plus_0_r, pplus_spec, pcst_spec; apply le_n_S; trivial.
 Qed.

 Lemma PPT_Ocons : forall t e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop (O.Ocons t) {e1, e2})
  (fun p => pplus 1 (pplus (F1 p) (F2 p))) (fun p => pplus 1 (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros t e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m); destruct (E.ceval_expr e2 m);
   simpl; intros H1 H2.
  destruct H1.
  intros t0 x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e2); [ | trivial].
  unfold fv_expr at 2; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec.
  apply VsetP.subset_union_l.
  destruct H2.
  intros t0 x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  split.
  rewrite pplus_spec, pplus_spec, pcst_spec.
  apply le_n_S; apply plus_le_compat; tauto.
  rewrite plus_0_r, pplus_spec, pplus_spec, pcst_spec.
  apply le_n_S; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_Oappend : forall t e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop (O.Oappend t) {e1, e2})
  (fun p => pplus (F1 p) (F2 p)) (fun p => pplus (F1 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros t e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m); destruct (E.ceval_expr e2 m);
   simpl; intros H1 H2.
  destruct H1.
  intros t0 x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e2); [ | trivial].
  unfold fv_expr at 2; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec.
  apply VsetP.subset_union_l.
  destruct H2.
  intros t0 x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  split.
  rewrite pplus_spec.
  apply le_trans with (fold_right
       (fun (v : T.interp k t) (n : nat) => S (T.size (k:=k) (t:=t) v + n)) 1
       i + peval (F2 p) k).
  generalize i; clear H2 i.
  induction i; simpl; intros.
   apply le_trans with (1:= H0); apply le_S; trivial.
   apply le_n_S.
   rewrite <- plus_assoc; apply plus_le_compat; trivial.
  apply plus_le_compat; trivial.
  repeat rewrite pplus_spec; repeat apply plus_le_compat; trivial.
  apply le_trans with (1:= List_size_length i); trivial.
  rewrite plus_0_r; trivial.
 Qed.

 Lemma PPT_pair : forall t1 t2 e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop (O.Opair t1 t2) {e1, e2}) 
  (fun p => pplus 1 (pplus (F1 p) (F2 p))) (fun p => pplus 1 (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros t1 t2 e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m); destruct (E.ceval_expr e2 m); 
   simpl; intros H1 H2.
  destruct H1.
  intros t0 x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e2); [ | trivial].
  unfold fv_expr at 2; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec.
  apply VsetP.subset_union_l.
  destruct H2.
  intros t0 x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  split.
  rewrite pplus_spec, pplus_spec, pcst_spec.
  apply le_n_S; apply plus_le_compat; tauto.
  rewrite plus_0_r, pplus_spec, pplus_spec, pcst_spec.
  apply le_n_S; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_in_dom : forall t1 t2 e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop (O.Oin_dom t1 t2) {e1, e2})
  (fun p => pcst 1) (fun p => pplus (pplus (pmult (F2 p) (pplus (F1 p) (F2 p))) (pcst 1)) (pplus (G2 p) (G1 p))).
 Proof.
  unfold PPT_expr; intros t1 t2 e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [x nx].
  case (E.ceval_expr e2 m); intros l n Hl Hn.
  destruct Hn.
  intros; apply H; unfold fv_expr; simpl.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  apply fv_expr_rec_subset.
  destruct Hl.
  intros; apply H; unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  unfold O.ceval_op; simpl; fold (T.interp k t2).
  case_eq (cexistsb
      (fun v1 : T.interp k t1 * T.interp k t2 =>
       (T.i_eqb k t1 x (fst v1), O.eq_cost k t1 x (fst v1))) l 1); intros.
  split;[rewrite pcst_spec; trivial | ].
  match type of H4 with cexistsb ?F l _ = _ => set (f := F) in H4 end.
  assert (forall a : T.interp k t1 * T.interp k t2,
     In a l -> snd (f a) <= peval (pplus (F1 p) (F2 p)) k).
   unfold f; intros; simpl; unfold O.eq_cost.
   rewrite pplus_spec; apply plus_le_compat; trivial.
   assert (W:= List_size_le l a H5); simpl in W.
   apply le_trans with (2:= H2); apply le_trans with (2:= W).
   apply le_S; apply le_plus_l.
  assert (W:= @cexistsb_count _ f (peval (pplus (F1 p) (F2 p)) k) l H5 1).
  rewrite pplus_spec; apply plus_le_compat.
  rewrite H4 in W; simpl in W.
  apply le_trans with (1:= W).
  repeat (rewrite pplus_spec || rewrite pmult_spec).
  apply plus_le_compat;[apply mult_le_compat; trivial | rewrite pcst_spec; trivial].
  apply le_trans with (2:= H2); refine (List_size_length l).
  rewrite plus_0_r, plus_comm, pplus_spec.
  apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_img : forall t1 t2 e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop (O.Oimg t1 t2) {e1, e2})
  (fun p => pplus (F2 p) (T.default_poly t2)) 
  (fun p => pplus (pplus (pmult (F2 p) (pplus (F1 p) (F2 p))) (pcst 1)) (pplus (G2 p) (G1 p))).
 Proof.
  unfold PPT_expr; intros t1 t2 e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [x nx].
  case (E.ceval_expr e2 m); intros l n Hl Hn.
  destruct Hn.
  intros; apply H; unfold fv_expr; simpl.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  apply fv_expr_rec_subset.
  destruct Hl.
  intros; apply H; unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  unfold O.ceval_op; simpl; fold (T.interp k t2).
  case_eq (cfind_default
              (fun v1 : T.interp k t1 * T.interp k t2 =>
               (T.i_eqb k t1 x (fst v1), O.eq_cost k t1 x (fst v1))) l 1
              (T.default k t1, T.default k t2)); intros.
  split.
  assert (W:= @find_cfind_default _ 
             (fun v1 : T.interp k t1 * T.interp k t2 => T.i_eqb k t1 x (fst v1))
             (fun v1 : T.interp k t1 * T.interp k t2 =>
                (T.i_eqb k t1 x (fst v1), O.eq_cost k t1 x (fst v1)))
             (T.default k t1, T.default k t2)
             (fun x => refl_equal _)
             l 1).
  rewrite H4 in W; simpl in W; rewrite <- W.
  unfold find_default; rewrite pplus_spec.
  case_eq (find (fun v1 : T.interp k t1 * T.interp k t2 => T.i_eqb k t1 x (fst v1)) l); intros.
  destruct (find_In _ _ H5).
  apply le_trans with (peval (F2 p) k);[ | apply le_plus_l].
  apply le_trans with (T.size (k:=k) (t:= T.Pair t1 t2) p1).
  destruct p1; simpl; apply le_S; apply le_plus_r.
  apply le_trans with (2:= H2); apply List_size_le; trivial.
  apply le_trans with (peval (T.default_poly t2) k).
  simpl; apply T.default_poly_spec.
  apply le_plus_r.
  rewrite pplus_spec; apply plus_le_compat.
  match type of H4 with cfind_default ?F l _ _ = _ => set (f := F) in H4 end.
  assert (forall a : T.interp k t1 * T.interp k t2,
     In a l -> snd (f a) <= peval (pplus (F1 p) (F2 p)) k).
   unfold f; intros; simpl; unfold O.eq_cost.
   rewrite pplus_spec; apply plus_le_compat; trivial.
   assert (W:= List_size_le l a H5); simpl in W.
   apply le_trans with (2:= H2); apply le_trans with (2:= W).
   apply le_S; apply le_plus_l.
  assert (W:= @cfind_default_count _ f (peval (pplus (F1 p) (F2 p)) k) l (T.default k t1, T.default k t2) H5 1).
  rewrite H4 in W; simpl in W.
  rewrite pplus_spec, pcst_spec.
  apply le_trans with (1:= W); apply plus_le_compat;[ | trivial].
  repeat (rewrite pplus_spec || rewrite pmult_spec).
  apply mult_le_compat;[ | trivial].
  apply le_trans with (2:= H2); refine (List_size_length l).
  rewrite plus_0_r, plus_comm, pplus_spec.
  apply plus_le_compat; trivial.
 Qed.

  Lemma PPT_in_range : forall t1 t2 e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop (O.Oin_range t1 t2) {e1, e2})
  (fun p => pcst 1) (fun p => pplus (pplus (pmult (F2 p) (pplus (F1 p) (F2 p))) (pcst 1)) (pplus (G2 p) (G1 p))).
 Proof.
  unfold PPT_expr; intros t1 t2 e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [x nx].
  case (E.ceval_expr e2 m); intros l n Hl Hn.
  destruct Hn.
  intros; apply H; unfold fv_expr; simpl.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  apply fv_expr_rec_subset.
  destruct Hl.
  intros; apply H; unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  unfold O.ceval_op; simpl; fold (T.interp k t1).
  case_eq (cexistsb
      (fun v1 : T.interp k t1 * T.interp k t2 =>
       (T.i_eqb k t2 x (snd v1), O.eq_cost k t2 x (snd v1))) l 1); intros.
  split;[rewrite pcst_spec; trivial | ].
  match type of H4 with cexistsb ?F l _ = _ => set (f := F) in H4 end.
  assert (forall a : T.interp k t1 * T.interp k t2,
     In a l -> snd (f a) <= peval (pplus (F1 p) (F2 p)) k).
   unfold f; intros; simpl; unfold O.eq_cost.
   rewrite pplus_spec; apply plus_le_compat; trivial.
   assert (W:= List_size_le l a H5); simpl in W.
   apply le_trans with (2:= H2); apply le_trans with (2:= W).
   apply le_S; apply le_plus_r.
  assert (W:= @cexistsb_count _ f (peval (pplus (F1 p) (F2 p)) k) l H5 1).
  rewrite pplus_spec; apply plus_le_compat.
  rewrite H4 in W; simpl in W.
  apply le_trans with (1:= W).
  repeat (rewrite pplus_spec || rewrite pmult_spec).
  apply plus_le_compat;[apply mult_le_compat; trivial | rewrite pcst_spec; trivial].
  apply le_trans with (2:= H2); refine (List_size_length l).
  rewrite plus_0_r, plus_comm, pplus_spec.
  apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_mem : forall t1 e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop (O.Omem t1) {e1, e2})
  (fun p => pcst 1) (fun p => pplus (pplus (pmult (F2 p) (pplus (F1 p) (F2 p))) (pcst 1)) (pplus (G2 p) (G1 p))).
 Proof.
  unfold PPT_expr; intros t1 e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [x nx].
  case (E.ceval_expr e2 m); intros l n Hl Hn.
  destruct Hn.
  intros; apply H; unfold fv_expr; simpl.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  apply fv_expr_rec_subset.
  destruct Hl.
  intros; apply H; unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  unfold O.ceval_op; simpl; fold (T.interp k t1).
  case_eq (cexistsb
      (fun v1 : T.interp k t1 =>
       (T.i_eqb k t1 x v1, O.eq_cost k t1 x v1)) l 1); intros.
  split;[rewrite pcst_spec; trivial | ].
  match type of H4 with cexistsb ?F l _ = _ => set (f := F) in H4 end.
  assert (forall a : T.interp k t1 ,
     In a l -> snd (f a) <= peval (pplus (F1 p) (F2 p)) k).
   unfold f; intros; simpl; unfold O.eq_cost.
   rewrite pplus_spec; apply plus_le_compat; trivial.
   assert (W:= List_size_le l a H5); simpl in W.
   apply le_trans with (2:= H2); apply le_trans with (2:= W); trivial.
  assert (W:= @cexistsb_count _ f (peval (pplus (F1 p) (F2 p)) k) l H5 1).
  rewrite pplus_spec; apply plus_le_compat.
  rewrite H4 in W; simpl in W.
  apply le_trans with (1:= W).
  repeat (rewrite pplus_spec || rewrite pmult_spec).
  apply plus_le_compat;[apply mult_le_compat; trivial | rewrite pcst_spec; trivial].
  apply le_trans with (2:= H2); refine (List_size_length l).
  rewrite plus_0_r, plus_comm, pplus_spec.
  apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_nth : forall t1 e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop (O.Onth t1) {e1, e2})
    (fun p => pplus (F2 p)(T.default_poly t1))
    (fun p => pplus (F2 p) (pplus (G2 p) (G1 p))).
 Proof.
  unfold PPT_expr; intros t1 e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [x nx].
  case (E.ceval_expr e2 m); intros l n Hl Hn.
  destruct Hn.
  intros; apply H; unfold fv_expr; simpl.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  apply fv_expr_rec_subset.
  destruct Hl.
  intros; apply H; unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  simpl; split; rewrite pplus_spec.
  destruct (nth_in_or_default x l (T.default k t1)).
  apply le_trans with (1:= List_size_le l  (nth x l (T.default k t1)) i).
  apply le_trans with (1:= H2); apply le_plus_l.
  apply le_trans with (peval (T.default_poly t1) k).
  unfold T.interp; rewrite e; apply T.default_poly_spec.
  apply le_plus_r.
  apply plus_le_compat.
  apply le_trans with (1 := List_size_length l); trivial.
  rewrite plus_0_r, pplus_spec, plus_comm; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_le : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 -> 
  PPT_expr e2 F2 G2 -> 
  PPT_expr (E.Eop O.Ole {e1, e2}) 
   (fun _ => 1) 
   (fun p => pplus (F1 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); clear He1.
  generalize (He2 k m p); clear He2.
  simpl; rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [n Hn].
  destruct (E.ceval_expr e2 m) as [n2 Hn2]; simpl; split.
  rewrite pcst_spec; trivial.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  repeat rewrite pplus_spec; apply plus_le_compat; trivial.
  rewrite plus_0_r; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_Zle : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 -> 
  PPT_expr e2 F2 G2 -> 
  PPT_expr (E.Eop O.OZle {e1, e2}) 
   (fun _ => 1) 
   (fun p => pplus (F1 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); clear He1.
  generalize (He2 k m p); clear He2.
  simpl; rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [n Hn].
  destruct (E.ceval_expr e2 m) as [n2 Hn2]; simpl; split.
  rewrite pcst_spec; trivial.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  repeat rewrite pplus_spec; apply plus_le_compat; trivial.
  rewrite plus_0_r; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_lt : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 -> 
  PPT_expr e2 F2 G2 -> 
  PPT_expr (E.Eop O.Olt {e1, e2}) 
   (fun _ => 1)
   (fun p => pplus (F2 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); clear He1.
  generalize (He2 k m p); clear He2.
  simpl; rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [v1 n1].
  destruct (E.ceval_expr e2 m) as [v2 n2].
  simpl; split.
  rewrite pcst_spec; trivial.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  repeat rewrite pplus_spec; apply plus_le_compat; trivial.
  rewrite plus_0_r; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_Zlt : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 -> 
  PPT_expr e2 F2 G2 -> 
  PPT_expr (E.Eop O.OZlt {e1, e2}) 
   (fun _ => 1)
   (fun p => pplus (F2 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); clear He1.
  generalize (He2 k m p); clear He2.
  simpl; rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [v1 n1].
  destruct (E.ceval_expr e2 m) as [v2 n2].
  simpl; split.
  rewrite pcst_spec; trivial.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  repeat rewrite pplus_spec; apply plus_le_compat; trivial.
  rewrite plus_0_r; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_Zgt : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 -> 
  PPT_expr e2 F2 G2 -> 
  PPT_expr (E.Eop O.OZgt {e1, e2}) 
   (fun _ => 1)
   (fun p => pplus (F2 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); clear He1.
  generalize (He2 k m p); clear He2.
  simpl; rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [v1 n1].
  destruct (E.ceval_expr e2 m) as [v2 n2].
  simpl; split.
  rewrite pcst_spec; trivial.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  repeat rewrite pplus_spec; apply plus_le_compat; trivial.
  rewrite plus_0_r; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_Zge : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 -> 
  PPT_expr e2 F2 G2 -> 
  PPT_expr (E.Eop O.OZge {e1, e2}) 
   (fun _ => 1)
   (fun p => pplus (F2 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); clear He1.
  generalize (He2 k m p); clear He2.
  simpl; rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [v1 n1].
  destruct (E.ceval_expr e2 m) as [v2 n2].
  simpl; split.
  rewrite pcst_spec; trivial.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  repeat rewrite pplus_spec; apply plus_le_compat; trivial.
  rewrite plus_0_r; apply plus_le_compat; trivial.
 Qed.
   
 Lemma PPT_Zopp : forall e F G,
  PPT_expr e F G -> 
  PPT_expr (E.Eop O.OZopp {e}) 
   (fun p => F p)
   (fun p => pplus (F p) (G p)).
 Proof.
  unfold PPT_expr; intros e F G He k m p H.
  generalize (He k m p); clear He.
  simpl; rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e m) as [v n].
  simpl; split.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  apply Hx.
  unfold size_Z, Zabs_nat in *.
  destruct v; simpl in *; trivial.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  apply Hx.
  rewrite pplus_spec; apply plus_le_compat; trivial.
  omega.
 Qed.

 Lemma PPT_Zdiv : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 -> 
  PPT_expr e2 F2 G2 -> 
  PPT_expr (E.Eop O.OZdiv {e1, e2}) 
   (fun p => pplus (F1 p) (pcst 1))
   (fun p => pplus (F1 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); clear He1.
  generalize (He2 k m p); clear He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [v1 n1].
  destruct (E.ceval_expr e2 m) as [v2 n2].
  simpl; split.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  unfold size_Z in *.

  assert (forall p1 p2,  
    size_nat (Zabs_nat (Zpos p1)) <= (F1 p) k ->
    size_nat (Zabs_nat (Zpos p1 / Zpos p2)) <= (F1 p) k).
  intros.
  apply le_trans with (2 := H4).
  apply size_nat_monotonic.
  apply Zabs_nat_le.
  split.
  apply Z_div_pos; auto with zarith.
  apply Zdiv_le_upper_bound; auto with zarith.
  apply Zgt_lt.
  apply Zgt_pos_0.
  apply Zle_trans with ((Zpos p1) * 1)%Z.
  auto with zarith.
  apply Zmult_le_compat; auto with zarith.
  generalize (Zgt_pos_0 p2); omega.

  rewrite pplus_spec, pcst_spec.
  destruct v1; destruct v2; auto; simpl; try omega.
  
  apply le_trans with ((F1 p) k); auto with zarith.

  rewrite <- (Zopp_involutive (Zneg p1)).
  rewrite Zopp_neg.
  destruct (Z_eq_dec (Zmod (Zpos p0) (Zpos p1)) 0%Z).
  rewrite Z_div_zero_opp_r; trivial.
  cutrewrite (Zabs_nat (- (Zpos p0 / Zpos p1)) = Zabs_nat (Zpos p0 / Zpos p1)).
  apply le_trans with ((F1 p) k); auto with zarith.
  destruct (Zpos p0 / Zpos p1)%Z; simpl; auto.
  rewrite Z_div_nz_opp_r; trivial.
  cutrewrite (Zabs_nat (- (Zpos p0 / Zpos p1) - 1) = Zabs_nat (Zpos p0 / Zpos p1 + 1)).
  rewrite Zabs_nat_Zplus; simpl; auto with arith.
  apply le_trans with (1 := size_nat_plus _ _); simpl.
  apply plus_le_compat; auto.
  apply Z_div_pos; auto with zarith.
  omega.
  assert (forall x, Zabs_nat x = Zabs_nat (- x)).
  intros x; destruct x; auto.
  rewrite H5.
  f_equal; ring.

  rewrite <- (Zopp_involutive (Zneg p0)).
  rewrite Zopp_neg.
  destruct (Z_eq_dec (Zmod (Zpos p0) (Zpos p1)) 0%Z).
  rewrite Z_div_zero_opp_full; trivial.
  cutrewrite (Zabs_nat (- (Zpos p0 / Zpos p1)) = Zabs_nat (Zpos p0 / Zpos p1)).
  apply le_trans with ((F1 p) k); auto with zarith.
  destruct (Zpos p0 / Zpos p1)%Z; simpl; auto.
  rewrite Z_div_nz_opp_full; trivial.
  cutrewrite (Zabs_nat (- (Zpos p0 / Zpos p1) - 1) = Zabs_nat (Zpos p0 / Zpos p1 + 1)).
  rewrite Zabs_nat_Zplus; simpl; auto with arith.
  apply le_trans with (1 := size_nat_plus _ _); simpl.
  apply plus_le_compat; auto.
  apply Z_div_pos; auto with zarith.
  omega.
  assert (forall x, Zabs_nat x = Zabs_nat (- x)).
  intros x; destruct x; auto.
  rewrite H5.
  f_equal; ring.

  rewrite <- (Zopp_involutive (Zneg p0)), <- (Zopp_involutive (Zneg p1)).
  repeat rewrite Zopp_neg.
  rewrite Zdiv_opp_opp.
  apply le_trans with ((F1 p) k); auto with zarith.
  repeat rewrite pplus_spec.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  omega.
Qed.

 Lemma PPT_Zmod : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 -> 
  PPT_expr e2 F2 G2 -> 
  PPT_expr (E.Eop O.OZmod {e1, e2}) 
   (fun p => F2 p)
   (fun p => pplus (F2 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); clear He1.
  generalize (He2 k m p); clear He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [v1 n1].
  destruct (E.ceval_expr e2 m) as [v2 n2].
  simpl; intros.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  split.
  apply le_trans with (2 := H0).
  destruct v2; simpl.
  rewrite Zmod_0_r; auto.
  unfold size_Z.
  apply size_nat_monotonic.
  apply Zabs_nat_le.
  generalize (Z_mod_lt v1 (Zpos p0)); intros.
  destruct H4.
  apply Zgt_pos_0.
  omega.
  rewrite <- (Zopp_involutive (Zneg p0)).
  rewrite Zopp_neg.
  destruct (Z_eq_dec (Zmod v1 (Zpos p0)) 0%Z).
  rewrite Z_mod_zero_opp_r; trivial.
  unfold size_Z; simpl; auto.
  apply size_nat_positive.
  rewrite Z_mod_nz_opp_r; trivial.
  unfold size_Z.
  apply size_nat_monotonic.
  assert (forall x, Zabs_nat x = Zabs_nat (- x)).
  intros x; destruct x; auto.
  rewrite H4.
  cutrewrite (- (v1 mod Zpos p0 - Zpos p0) = Zpos p0 - (v1 mod Zpos p0))%Z;[ | ring].
  rewrite Zabs_nat_Zminus.
  rewrite <- H4.
  omega.
  generalize (Z_mod_lt v1 (Zpos p0)); intros.
  destruct H5.
  apply Zgt_pos_0.
  omega.
  repeat rewrite pplus_spec.
  omega.
 Qed.

 Lemma PPT_not : forall e F G,
  PPT_expr e F G -> 
  PPT_expr (E.Eop O.Onot {e})
   (fun _ => 1)
   (fun p => pplus 1 (G p)).
 Proof.
  unfold PPT_expr; intros e F G0 He k m p H.
  generalize (He k m p); clear He.
  simpl; destruct (E.ceval_expr e m) as [n Hn]; split.
  rewrite pcst_spec; trivial.  
  destruct (H0 H).
  rewrite pplus_spec, plus_0_r, pcst_spec; apply le_n_S; trivial.
 Qed.

 Lemma PPT_and : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 -> 
  PPT_expr e2 F2 G2 -> 
  PPT_expr (E.Eop O.Oand {e1, e2})
   (fun _ => 1)
   (fun p => pplus 1 (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); clear He1.
  generalize (He2 k m p); clear He2.
  simpl; destruct (E.ceval_expr e1 m) as [n Hn].
  destruct (E.ceval_expr e2 m) as [n2 Hn2]; simpl; split.
  rewrite pcst_spec; trivial.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  rewrite pplus_spec, pplus_spec, pcst_spec; apply le_n_S.
  rewrite plus_0_r; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_or : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 -> 
  PPT_expr e2 F2 G2 -> 
  PPT_expr (E.Eop O.Oor {e1, e2})
   (fun _ => 1)
   (fun p => pplus 1 (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); clear He1.
  generalize (He2 k m p); clear He2.
  simpl; destruct (E.ceval_expr e1 m) as [n Hn].
  destruct (E.ceval_expr e2 m) as [n2 Hn2]; simpl; split.
  rewrite pcst_spec; trivial.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  rewrite pplus_spec, pplus_spec, pcst_spec; apply le_n_S.
  rewrite plus_0_r; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_imp : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 -> 
  PPT_expr e2 F2 G2 -> 
  PPT_expr (E.Eop O.Oimp {e1, e2})
   (fun _ => 1)
   (fun p => pplus 1 (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); clear He1.
  generalize (He2 k m p); clear He2.
  simpl; destruct (E.ceval_expr e1 m) as [n Hn].
  destruct (E.ceval_expr e2 m) as [n2 Hn2]; simpl; split.
  rewrite pcst_spec; trivial.
  destruct H0.
  intros t x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset.
  rewrite pplus_spec, pplus_spec, pcst_spec; apply le_n_S.
  rewrite plus_0_r; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_if : forall t e1 (e2 e3:E.expr t) F1 G1 F2 G2 F3 G3,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr e3 F3 G3 ->
  PPT_expr (E.Eop (O.Oif t) {e1, e2, e3})
   (fun p => pplus (F2 p) (F3 p))
   (fun p => pplus (S 0) (pplus (G1 p) (pplus (G2 p) (G3 p)))).
 Proof.
  unfold PPT_expr; intros t e1 e2 e3 F1 G1 F2 G2 F3 G3 He1 He2 He3 k m p H.
  generalize (He1 k m p); clear He1.
  generalize (He2 k m p); clear He2.
  generalize (He3 k m p); clear He3.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e1 m) as [v1 n1].
  destruct (E.ceval_expr e2 m) as [v2 n2].
  destruct (E.ceval_expr e3 m) as [v3 n3].
  simpl; intros.
  destruct H0.
  intros t0 x Hx; apply H.
  unfold fv_expr; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  fold (fv_expr_extend e3 (fv_expr_extend e2 (fv_expr_rec Vset.empty e1))).
  rewrite union_fv_expr_spec; auto with set.
  destruct H1.
  intros t0 x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e2); [ | trivial].
  unfold fv_expr; simpl.  
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  fold (fv_expr_extend e3 (fv_expr_extend e2 (fv_expr_rec Vset.empty e1))).
  rewrite union_fv_expr_spec; rewrite union_fv_expr_spec; auto with set.
  destruct H2.
  intros t0 x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.  
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  fold (fv_expr_extend e3 (fv_expr_extend e2 (fv_expr_rec Vset.empty e1))).
  rewrite union_fv_expr_spec; rewrite union_fv_expr_spec; auto with set.
  split.
  case v1.
  eapply le_trans; [ |  apply pplus_le_l]; trivial.
  eapply le_trans; [ |  apply pplus_le_r]; trivial.
  rewrite pplus_spec, pplus_spec, pplus_spec, pcst_spec.
  apply le_n_S.
  rewrite plus_0_r; apply plus_le_compat; trivial.
  apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_add : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop O.Oadd {e1, e2})
  (fun p => pplus (F1 p) (F2 p))
  (fun p => pplus (F1 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e2 m). 
  destruct (E.ceval_expr e1 m).
  intros H2 H1.
  destruct H1 as [HF1 HG1].
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset. 
  destruct H2 as [HF2 HG2].
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e2); [ | trivial].
  unfold fv_expr at 2; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec.
  apply VsetP.subset_union_l.
  simpl; split.
  rewrite pplus_spec.
  eapply le_trans; [apply size_nat_plus | ].
  apply plus_le_compat; trivial.
  rewrite pplus_spec; apply plus_le_compat.
  trivial.
  rewrite plus_0_r, pplus_spec; apply plus_le_compat; trivial.
 Qed.

 Lemma ineq_triang_Zabs_nat : forall a b,
  Zabs_nat (a + b) <= Zabs_nat a + Zabs_nat b.
 Proof.
  intros.
  induction a; simpl; induction b; simpl; auto with zarith.
  rewrite nat_of_P_plus_morphism; trivial.

  generalize (lt_eq_lt_dec (nat_of_P p) (nat_of_P p0)); intro Helim; elim Helim;
     [ intro Helim'; elim Helim';clear Helim' | ]; intro H; clear Helim.
  rewrite (nat_of_P_lt_Lt_compare_complement_morphism p p0 H); simpl.
  rewrite nat_of_P_minus_morphism.
  apply le_trans with (nat_of_P p0).
  apply le_minus.
  apply le_plus_r.
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  change (nat_of_P p < nat_of_P p0); trivial.
 
  assert (Heq := nat_of_P_inj p p0 H);subst.
  rewrite Pcompare_refl; simpl; trivial.
  rewrite <- nat_of_P_plus_morphism; trivial.
  apply lt_le_weak.
  apply lt_O_nat_of_P.

  rewrite (nat_of_P_gt_Gt_compare_complement_morphism p p0 H); simpl.
  rewrite nat_of_P_minus_morphism.
  apply le_trans with (nat_of_P p).
  apply le_minus.
  apply le_plus_l.
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  change (nat_of_P p0 < nat_of_P p); trivial.

   generalize (lt_eq_lt_dec (nat_of_P p) (nat_of_P p0)); intro Helim; elim Helim;
     [ intro Helim'; elim Helim';clear Helim' | ]; intro H; clear Helim.
    rewrite (nat_of_P_lt_Lt_compare_complement_morphism p p0 H); simpl.
  rewrite nat_of_P_minus_morphism.
  apply le_trans with (nat_of_P p0).
  apply le_minus.
  apply le_plus_r.
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  change (nat_of_P p < nat_of_P p0); trivial.

  assert (Heq := nat_of_P_inj p p0 H);subst.
  rewrite Pcompare_refl; simpl; trivial.
  rewrite <- nat_of_P_plus_morphism; trivial.
  apply lt_le_weak.
  apply lt_O_nat_of_P.

  rewrite (nat_of_P_gt_Gt_compare_complement_morphism p p0 H); simpl.
  rewrite nat_of_P_minus_morphism.
  apply le_trans with (nat_of_P p).
  apply le_minus.
  apply le_plus_l.
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  change (nat_of_P p0 < nat_of_P p); trivial.
  
  rewrite nat_of_P_plus_morphism; trivial.
 Qed.

 Lemma ineq_triang_Zabs_nat_minus : forall a b,
  Zabs_nat (a - b) <= Zabs_nat a + Zabs_nat b.
 Proof.
  intros.
  induction a; simpl; induction b; simpl; auto with zarith.

  generalize (lt_eq_lt_dec (nat_of_P p) (nat_of_P p0)); intro Helim; elim Helim;
     [ intro Helim'; elim Helim';clear Helim' | ]; intro H; clear Helim.
  rewrite (nat_of_P_lt_Lt_compare_complement_morphism p p0 H); simpl.
  rewrite nat_of_P_minus_morphism.
  apply le_trans with (nat_of_P p0).
  apply le_minus.
  apply le_plus_r.
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  change (nat_of_P p < nat_of_P p0); trivial.
 
  assert (Heq := nat_of_P_inj p p0 H);subst.
  rewrite Pcompare_refl; simpl; trivial.
  rewrite <- nat_of_P_plus_morphism; trivial.
  apply lt_le_weak.
  apply lt_O_nat_of_P.

  rewrite (nat_of_P_gt_Gt_compare_complement_morphism p p0 H); simpl.
  rewrite nat_of_P_minus_morphism.
  apply le_trans with (nat_of_P p).
  apply le_minus.
  apply le_plus_l.
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  change (nat_of_P p0 < nat_of_P p); trivial.

  rewrite nat_of_P_plus_morphism; trivial.
  rewrite nat_of_P_plus_morphism; trivial.

   generalize (lt_eq_lt_dec (nat_of_P p) (nat_of_P p0)); intro Helim; elim Helim;
     [ intro Helim'; elim Helim';clear Helim' | ]; intro H; clear Helim.
    rewrite (nat_of_P_lt_Lt_compare_complement_morphism p p0 H); simpl.
  rewrite nat_of_P_minus_morphism.
  apply le_trans with (nat_of_P p0).
  apply le_minus.
  apply le_plus_r.
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  change (nat_of_P p < nat_of_P p0); trivial.

  assert (Heq := nat_of_P_inj p p0 H);subst.
  rewrite Pcompare_refl; simpl; trivial.
  rewrite <- nat_of_P_plus_morphism; trivial.
  apply lt_le_weak.
  apply lt_O_nat_of_P.

  rewrite (nat_of_P_gt_Gt_compare_complement_morphism p p0 H); simpl.
  rewrite nat_of_P_minus_morphism.
  apply le_trans with (nat_of_P p).
  apply le_minus.
  apply le_plus_l.
  apply nat_of_P_gt_Gt_compare_complement_morphism.
  change (nat_of_P p0 < nat_of_P p); trivial.
 Qed.

 Lemma PPT_Zadd : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop O.OZadd {e1, e2})
  (fun p => pplus (F1 p) (F2 p))
  (fun p => pplus (F1 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e2 m). 
  destruct (E.ceval_expr e1 m).
  intros H2 H1.
  destruct H1 as [HF1 HG1].
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset. 
  destruct H2 as [HF2 HG2].
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e2); [ | trivial].
  unfold fv_expr at 2; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec.
  apply VsetP.subset_union_l.
  simpl; split.
  rewrite pplus_spec.
  unfold size_Z in * |- *.
  
  apply le_trans with (size_nat ((Zabs_nat i0) + (Zabs_nat i))).
  apply size_nat_monotonic.
  apply ineq_triang_Zabs_nat.
  apply le_trans with (size_nat (Zabs_nat i0) + size_nat (Zabs_nat i)).
  apply size_nat_plus.
  apply plus_le_compat; trivial.
  rewrite plus_0_r, pplus_spec; apply plus_le_compat; trivial.
  rewrite pplus_spec; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_sub : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop O.Osub {e1, e2})
  (fun p => F1 p)
  (fun p => pplus (F2 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e2 m) as [v1 n1].  
  destruct (E.ceval_expr e1 m) as [v2 n2].
  intros H2 H1.
  destruct H1 as [HF1 HG1].
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset. 
  destruct H2 as [HF2 HG2].
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e2); [ | trivial].
  unfold fv_expr at 2; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec.
  apply VsetP.subset_union_l.
  simpl; split.

  apply le_trans with (size_nat v2).
  apply size_nat_monotonic; omega.
  trivial.
  rewrite pplus_spec, pplus_spec.  
  apply plus_le_compat; trivial.
  rewrite plus_0_r.
  apply plus_le_compat; trivial.
 Qed. 

 Lemma PPT_Zsub : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop O.OZsub {e1, e2})
  (fun p => pplus (F1 p) (F2 p))
  (fun p => pplus (F2 p) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e2 m) as [v1 n1].  
  destruct (E.ceval_expr e1 m) as [v2 n2].
  intros H2 H1.
  destruct H1 as [HF1 HG1].
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset. 
  destruct H2 as [HF2 HG2].
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e2); [ | trivial].
  unfold fv_expr at 2; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec.
  apply VsetP.subset_union_l.
  simpl; split.

  unfold size_Z in * |- *.
  apply le_trans with (size_nat (Zabs_nat v1 + Zabs_nat v2)).
  apply size_nat_monotonic.
  rewrite plus_comm.
  apply  ineq_triang_Zabs_nat_minus.
  rewrite pplus_spec.
  apply le_trans with (size_nat (Zabs_nat v1) + size_nat (Zabs_nat v2)).
  apply size_nat_plus.
  rewrite plus_comm.
  apply plus_le_compat; trivial.  

  rewrite pplus_spec, pplus_spec.  
  apply plus_le_compat; trivial.
  rewrite plus_0_r.
  apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_mul : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop O.Omul {e1, e2})
   (fun p => pplus (F1 p) (F2 p))
   (fun p => pplus (pmult (F1 p) (F2 p)) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e2 m). 
  destruct (E.ceval_expr e1 m).
  intros H2 H1.
  destruct H1 as [HF1 HG1].
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset. 
  destruct H2 as [HF2 HG2].
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e2); [ | trivial].
  unfold fv_expr at 2; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec.
  apply VsetP.subset_union_l.
  simpl; split.

  rewrite pplus_spec.
  eapply le_trans; [apply size_nat_mult | ].
  apply plus_le_compat; trivial.

  rewrite pplus_spec, pmult_spec; apply plus_le_compat.
  apply mult_le_compat; trivial.
  rewrite plus_0_r, pplus_spec; apply plus_le_compat; trivial.
 Qed.

 Lemma PPT_Zmul : forall e1 e2 F1 G1 F2 G2,
  PPT_expr e1 F1 G1 ->
  PPT_expr e2 F2 G2 ->
  PPT_expr (E.Eop O.OZmul {e1, e2})
   (fun p => pplus (F1 p) (F2 p))
   (fun p => pplus (pmult (F1 p) (F2 p)) (pplus (G1 p) (G2 p))).
 Proof.
  unfold PPT_expr; intros e1 e2 F1 G1 F2 G2 He1 He2 k m p H.
  generalize (He1 k m p); generalize (He2 k m p); clear He1 He2.
  simpl; repeat rewrite E.ceval_expr_spec.
  destruct (E.ceval_expr e2 m). 
  destruct (E.ceval_expr e1 m).
  intros H2 H1.
  destruct H1 as [HF1 HG1].
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e1); [ | trivial].
  unfold fv_expr; simpl.
  apply fv_expr_rec_subset. 
  destruct H2 as [HF2 HG2].
  intros t x Hx; apply H.
  apply Vset.subset_correct with (fv_expr e2); [ | trivial].
  unfold fv_expr at 2; simpl.
  fold (fv_expr_extend e2 (fv_expr_rec Vset.empty e1)).
  rewrite union_fv_expr_spec.
  apply VsetP.subset_union_l.
  simpl; split.

  unfold size_Z in * |- *.
  rewrite pplus_spec.
  rewrite Zabs_nat_mult.
  apply le_trans with ((size_nat (Zabs_nat i0) + size_nat ( Zabs_nat i))).
  apply size_nat_mult.
  apply plus_le_compat; trivial.  

  rewrite pplus_spec, pmult_spec; apply plus_le_compat.
  apply mult_le_compat; trivial.
  rewrite plus_0_r, pplus_spec; apply plus_le_compat; trivial.
 Qed.


 (** Supports *)

 Lemma PPT_Dbool : PPT_support E.Dbool (fun p => pplus p 1) (fun p => 1).
 Proof.  
  intros k m p Hm.
  simpl; split.
  intros b Hb.
  apply le_trans with (peval 1 k).
  rewrite pcst_spec; trivial.
  apply pplus_le_r.
  rewrite pcst_spec; trivial.
 Qed.

 Lemma PPT_Dnat : forall e Fe Ge,
  PPT_expr e Fe Ge ->
  PPT_support (E.Dnat e) Fe Ge.
 Proof.
  intros e Fe Ge He k m p Hm; simpl.
  generalize (He k m p Hm); clear He Hm.
  case (E.ceval_expr e m); intros v n [H1 H2]; split.
  intros v0 Hin.
  apply le_trans with (size_nat v); [clear H1 | trivial].
  apply size_nat_monotonic.
  induction v.
  simpl in Hin; case Hin; intro H; [subst; trivial | elim H].
  replace (S v) with (v + 1) in Hin by (rewrite plus_comm; trivial).
  rewrite seq_append in Hin.
  simpl in Hin; case Hin; intro H; clear Hin. 
  rewrite <- H; apply le_O_n.
  case (in_app_or _ _ _ H); clear H; intro Hin.
  apply le_trans with v; [ | apply le_S; trivial].
  apply IHv; right; trivial.
  simpl in Hin; case Hin; intro H; [subst; trivial | elim H].
  trivial.
 Qed.

 Lemma In_seqZ_le :
   forall (n : nat) (m i : Z), In i (seqZ m n) -> (m <= i < Z_of_nat n + m)%Z.
 Proof.
   induction n; intros.
   elim H.
   simpl seqZ in H.
   simpl In in H.
   destruct H; subst.
   split.
   omega.
   apply Zle_lt_trans with (Z_of_nat 0%nat + i)%Z.
   omega.
   apply Zplus_lt_compat_r.
   apply inj_lt.
   omega.
   apply IHn in H.
   destruct H.
   split.
   omega.
   rewrite inj_S.
   omega.
 Qed.

 Lemma PPT_DZ : forall e1 e2 F1 F2 G1 G2,
   PPT_expr e1 F1 G1 ->
   PPT_expr e2 F2 G2 ->
   PPT_support (E.DZ e1 e2)
   (fun p => pplus 1 (pplus (F1 p) (F2 p)))
   (fun p => pplus (G1 p) (G2 p)).
 Proof.
  intros e1 e2 F1 F2 G1 G2 H1 H2 k m p Hm; simpl.
  generalize (H1 k m p); clear H1.
  generalize (H2 k m p); clear H2.
  destruct (E.ceval_expr e1 m).
  destruct (E.ceval_expr e2 m).
  intros.
  simpl in Hm.
  rewrite pplus_spec, pplus_spec, pcst_spec, pplus_spec.
  destruct H; [ intros; apply Hm; auto with set | ].
  destruct H0;[ intros; apply Hm; auto with set | ].
  split; simpl in *; intros.
  unfold Z_support in H3.
  case_eq (Zle_bool i i0); intros; rewrite H4 in H3.
  apply Zle_bool_imp_le in H4.
  apply In_seqZ_le in H3.
  rewrite inj_Zabs_nat in H3.
  rewrite Zabs_eq in H3;[ | omega].
  apply le_trans with (size_Z i + size_Z i0).
  unfold size_Z.
  destruct (Z_lt_le_dec 0 v).
  apply le_trans with ( size_nat (Zabs_nat i0)).
  apply size_nat_monotonic.
  apply Zabs_nat_le.
  omega.
  omega.
  apply le_trans with ( size_nat (Zabs_nat i)).
  apply size_nat_monotonic.  
  assert (forall x, Zabs_nat x = Zabs_nat (- x)).
  intros x; destruct x; auto.
  rewrite (H5 v), (H5 i).
  apply Zabs_nat_le.
  omega.
  omega.
  omega.
  destruct H3; subst.
  unfold size_Z; simpl.
  omega.
  elim H3.
  omega.
Qed.

 Lemma PPT_prod : forall t1 t2 (s1 : E.support t1) (s2 : E.support t2) F1 F2 G1 G2,
   PPT_support s1 F1 G1 ->
   PPT_support s2 F2 G2 ->
   PPT_support (E.Dprod s1 s2) 
   (fun p => pplus 1 (pplus (F1 p) (F2 p))) 
   (fun p => pmult (G1 p) (G2 p)).
 Proof.
  intros t1 t2 s1 s2 F1 F2 G1 G2 H1 H2 k m p Hm; simpl.
  generalize (H1 k m p); clear H1.
  generalize (H2 k m p); clear H2.
  destruct (E.ceval_support s1 m).
  destruct (E.ceval_support s2 m).
  intros.
  simpl in Hm.
  rewrite pplus_spec, pmult_spec, pcst_spec, pplus_spec.
  destruct H; [ intros; apply Hm; auto with set | ].
  destruct H0;[ intros; apply Hm; auto with set | ].
  split;[ destruct v as [v1 v2]; simpl in *; intro | ].
  apply le_n_S.
  apply in_prod_iff in H3.
  apply plus_le_compat.
  apply H0; tauto.
  apply H; tauto.
  apply mult_le_compat; trivial.
 Qed.


 (** PPT commands *)

 Section PPT.

  Variable E : env.
  Variable r : nat.
 
  (** Bounded state *)
  Definition bound k (p q:polynomial) (mn:Mem.t k * nat) : Prop :=
   let (m,n) := mn in  
    (forall t, tsize t <= r -> forall x:Var.var t, T.size (m x) <= peval p k) /\ 
    n <= peval q k.

  Implicit Arguments bound [k].

  (** Polynomial sequence of distributions.
    If the probability of reaching a certain final state [(m,c)] is
    positive, then (asymptotically):
     - the size of the values in [m] is bounded by a polynomial, and
     - the final cost [c] is bounded by a polynomial
  *)
  Definition PPT (c:cmd)
   (F:polynomial -> polynomial) 
   (G:polynomial -> polynomial) : Prop :=
   forall k (d:Distr (Mem.t k * nat)) p q,
    range (bound p q) d ->
    range (bound (F p) (pplus q (G p))) (Mlet d ([[[c]]] E)).

  Lemma PPT_unit : forall c F G, 
   PPT c F G ->
   forall k (mn:Mem.t k * nat) p q,
    bound p q mn ->
    range (bound (F p) (pplus q (G p))) ([[[c]]] E mn).
  Proof.
   intros c F G0 Hc k mn p q Hmn.
   generalize (Hc k (Munit mn) p q).  
   unfold range; simpl; intros; auto.
  Qed.

  Lemma PPT_assign : forall t (x:Var.var t) (e:E.expr t) F G,
   PPT_expr e F G ->
   (forall t (x:Var.var t), Vset.mem x (fv_expr e) -> tsize t <= r) ->
   PPT [x <- e] (fun p => pplus (F p) p) G.
  Proof.
   unfold PPT, PPT_expr; intros t x e F G0 He Hr k d p q Hd f Hf.
   rewrite Mlet_simpl.
   rewrite <- (Hd (fun mn => mu ([[[ [x <- e] ]]] E mn) f)); [trivial | ].
   intros (m,n) [Hm1 Hm2]; rewrite cdeno_assign_elim; simpl.
   generalize (He k m p); clear He.
   case (E.ceval_expr e m); intros v n0 He.
   destruct He as [W1 W2]; trivial.
   intros t0 y Hy; apply Hm1.
   apply Hr with y; trivial.
   apply Hf; split.

   (* mem *)
   intros t0 Ht0 y; simpl.
   generalize (Var.veqb_spec_dep x y).
   case (Var.veqb x y); intro W.
   inversion W; subst; simpl; clear H1 H2.
   rewrite Mem.get_upd_same.
   apply le_trans with (peval (F p) k).
   trivial.
   apply pplus_le_l.
   rewrite Mem.get_upd_diff.
   apply le_trans with (peval p k).
   apply (Hm1 t0); auto.
   apply pplus_le_r.
   intro Heq; elim W; inversion Heq; trivial.

   (* cost *)
   apply le_trans with (peval q k + n0).
   auto with arith.
   rewrite pplus_spec; auto with arith.
  Qed.

  Lemma PPT_random : forall t (x:Var.var t) (s:E.support t) F G,
   PPT_support s F G ->
   (forall t (x:Var.var t), Vset.mem x (fv_distr s) -> tsize t <= r) ->
   PPT [x <$- s] (fun p => pplus (F p) p) G.
  Proof.
   unfold PPT; intros t x s Fs Gs Hs Hr k d p q Hd f Hf.
   rewrite Mlet_simpl.
   rewrite <- (Hd (fun mn => mu ([[[ [x <$- s] ]]] E mn) f)); [trivial | ].
   intros (m,n) [Hm1 Hm2]; rewrite cdeno_random_elim.
   simpl fst; simpl snd.
   generalize (Hs k m p); clear Hs.
   case (E.ceval_support s m); intros l n0 H.
   destruct H as [Hl Hn0].
   intros t0 y Hy; apply Hm1.
   apply Hr with y; trivial.

   symmetry; refine (sum_dom_zero _ _ _ _ Hl _).
   intros v Hv; symmetry.
   apply Hf; split.
   intros t0 Ht0 x0.
   generalize (Var.veqb_spec_dep x x0).   
   case (Var.veqb x x0); intro W.
   inversion W; subst; simpl; clear H1 H2.
   rewrite Mem.get_upd_same.
   eapply le_trans; [ | apply pplus_le_l]; trivial.
   rewrite Mem.get_upd_diff.
   eapply le_trans; [ | apply pplus_le_r]; trivial.
   apply Hm1; trivial.
   intro Heq; elim W.
   injection Heq; intros; subst.
   rewrite (T.inj_pair2 H); trivial.

   rewrite pplus_spec; apply plus_le_compat; trivial.
  Qed. 

  Lemma PPT_nil : PPT nil (fun p => p) (fun _ => 0).
  Proof.
   unfold PPT; intros k d p q Hd f Hf.
   rewrite Mlet_simpl.
   apply Oeq_trans with (mu d f).
   apply Hd.
   intros (m,n) Hmn; apply Hf.
   unfold bound; rewrite pplus_spec, pcst_spec; destruct Hmn; auto with arith.
   apply mu_stable_eq.  
   refine (ford_eq_intro _); intro.
   rewrite cdeno_nil_elim; trivial.
  Qed.

  Lemma PPT_cons : forall i c Fi Fc Gi Gc,
   PPT [i] Fi Gi ->
   PPT c Fc Gc ->
   PPT (i::c) (fun p => Fc (Fi p)) (fun p => pplus (Gi p) (Gc (Fi p))).
  Proof.
   unfold PPT; intros.
   apply range_stable_eq with 
    (Mlet (Mlet d ([[[ [i] ]]] E)) ([[[c]]] E)).
   intros; rewrite Mcomp.
   apply Mlet_eq_compat; trivial.
   apply ford_eq_intro; intro.
   apply eq_distr_intro; intro.
   rewrite cdeno_cons_elim; trivial.
   unfold bound in H0 |- *; intros.
   rewrite <- pplus_assoc.
   apply (H0 k (Mlet d ([[[ [i] ]]] E))).
   intro; unfold bound in H; apply H; trivial.
  Qed.

  Lemma PPT_cond : forall e c1 c2 Fe Ge Fc1 Fc2 Gc1 Gc2,
   PPT_expr e Fe Ge ->
   (forall t (x:Var.var t), Vset.mem x (fv_expr e) -> tsize t <= r) ->
   PPT c1 Fc1 Gc1 ->
   PPT c2 Fc2 Gc2 ->
   PPT [If e then c1 else c2]
    (fun p => pplus (Fe p) (pplus (Fc1 p) (Fc2 p)))
    (fun p => pplus (Ge p) (pplus (Gc1 p) (Gc2 p))).
  Proof.
   unfold PPT, PPT_expr.
   intros e c1 c2 Fe Ge Fc1 Fc2 Gc1 Gc2 He Hr Hc1 Hc2 k d p q Hd f Hf.
   apply Ole_antisym; [trivial | ].

   apply Ole_trans with (mu d
    (fplus
     (fun mn => mu ([[[c1]]] E (fst mn, snd mn + snd (E.ceval_expr e (fst mn)))) f)
     (fun mn => mu ([[[c2]]] E (fst mn, snd mn + snd (E.ceval_expr e (fst mn)))) f))).
   rewrite Mlet_simpl; refine (mu_le_compat _ _).
   trivial.
   apply ford_le_intro; intro m.
   unfold fplus; rewrite cdeno_cond_elim.
   case (E.ceval_expr e (fst m)); intro b; case b; trivial.  

   rewrite (mu_le_plus d).
   apply Ole_trans with (0 + 0)%U; [apply Uplus_le_compat | auto]. 

   apply Ole_trans with (
    mu 
    (Mlet 
     (Mlet d (fun mn => Munit (fst mn, snd mn + snd (E.ceval_expr e (fst mn)))))
     ([[[c1]]] E)) f); [trivial | ].
   apply Oeq_le; symmetry.
   refine (Hc1 k _ p (pplus q (Ge p)) _ _ _).
   refine (range_Mlet _ _ _ (P:=bound p q)).
   exact Hd.
   intros (m,n) [H1 H2] g Hg; simpl.
   apply Hg; split.
   exact H1.
   rewrite pplus_spec.
   apply plus_le_compat.
   exact H2.
   generalize (He k m p).
   case (E.ceval_expr e m); simpl; intros i n0 H.
   destruct H; [ | trivial].
   intros t x Hx; apply H1.
   apply Hr with x; trivial.

   intros (m,n) [H1 H2].
   apply Hf; split.
   intros; apply le_trans with (peval (Fc1 p) k); [auto |].
   eapply le_trans; [ | apply pplus_le_r ]; apply pplus_le_l.
   eapply le_trans; [apply H2 | ].
   repeat rewrite pplus_spec.
   rewrite plus_assoc; auto with arith.

   apply Ole_trans with (
    mu 
    (Mlet 
     (Mlet d (fun mn => Munit (fst mn, snd mn + snd (E.ceval_expr e (fst mn)))))
     ([[[c2]]] E)) f); [trivial | ].
   apply Oeq_le; symmetry.
   refine (Hc2 k _ p (pplus q (Ge p)) _ _ _).
   refine (range_Mlet _ _ _ (P:=bound p q)).
   exact Hd.
   intros (m,n) [H1 H2] g Hg; simpl.
   apply Hg; split.
   exact H1.
   rewrite pplus_spec.
   apply plus_le_compat.
   exact H2.
   generalize (He k m p).
   case (E.ceval_expr e m); simpl; intros i n0 H. 
   destruct H; [ | trivial].
   intros t x Hx; apply H1.
   apply Hr with x; trivial.

   intros (m,n) [H1 H2].
   apply Hf; split.
   intros; apply le_trans with (peval (Fc2 p) k); [auto |].
   eapply le_trans; [ | apply pplus_le_r ]; apply pplus_le_r.
   eapply le_trans; [apply H2 | ].
   repeat rewrite pplus_spec.
   rewrite plus_assoc; auto with arith.
  Qed.

  Lemma PPT_call : forall t (x:Var.var t) (f:Proc.proc t) (la:E.args (Proc.targs f)) 
   Fa Ga Fb Gb Fr Gr,
   (forall k (m:Mem.t k) p,
    (forall t (x:Var.var t), tsize t <= r -> T.size (m x) <= peval p k) ->
    bound (Fa p) (Ga p) (cinit_mem E f la m)) ->

   PPT (proc_body E f) Fb Gb ->

   (forall t (x:Var.var t), Vset.mem x (fv_expr (proc_res E f)) -> tsize t <= r) ->
   PPT_expr (proc_res E f) Fr Gr ->

   PPT [x <c- f with la]
    (fun p => pplus p (pplus (Fb (Fa p)) (Fr (Fb (Fa p)))))
    (fun p => pplus (Ga p) (pplus (Gb (Fa p)) (Gr (Fb (Fa p))))).
  Proof.
   unfold PPT; intros t x f la Fa Ga Fb Gb Fr Gr Ha Hb Ht Hr k d p q Hd.

   apply range_stable_eq with
    (Mlet d 
     (fun mn => 
      Mlet (Mlet (Munit (cinit_mem E f la (fst mn)))
       (fun mn' =>
        ([[[ proc_body E f ]]] E (fst mn', snd mn + snd mn'))))
      (fun mn'' => 
       Munit (fst (creturn_mem E x f (fst mn) (fst mn'')),
        snd (creturn_mem E x f (fst mn) (fst mn'')) + snd mn'')))).
   apply eq_distr_intro; intro g.
   repeat rewrite Mlet_simpl.
   apply mu_stable_eq.
   refine (ford_eq_intro _); intros (m,n).
   rewrite cdeno_call_elim; trivial.

   refine (range_Mlet _ _ _ (P:=bound p q)).
   trivial.
   intros (m,n) Hmn.
   refine (range_Mlet _ _ _ 
    (P:=bound (Fb (Fa p)) (pplus q (pplus (Ga p) (Gb (Fa p))))) ).

   intros g Hg; simpl.
   refine (Hb k 
    (Munit (fst (cinit_mem E f la m),
            n + snd (cinit_mem E f la m))) (Fa p) (pplus q (Ga p))
   _ _ _).
   intros ga Hga; simpl; apply Hga.
   destruct Hmn as [Hmn1 Hmn2].
   generalize (Ha k m p); simpl.
   destruct (cinit_mem E f la m) as (m',n'); intro H.
   destruct H; intros.
   apply (Hmn1 t0); auto.
   split; simpl.
   trivial.
   rewrite pplus_spec; apply plus_le_compat; trivial.
   intros (m',n') [H1 H2].
   apply Hg.
   split.
   auto.
   rewrite <- pplus_assoc; trivial.

   intros (m',n') [H1 H2] gr Hgr.
   simpl; apply Hgr.
   rewrite creturn_mem_spec_l, creturn_mem_spec_r.
   split.

   intros t0 Ht0 x0.
   generalize (Var.veqb_spec_dep x x0).   
   case (Var.veqb x x0); intro W.
   inversion W; subst; simpl; clear H3 H4.
   rewrite return_mem_dest.
   generalize (Hr k m' ((Fb (Fa p)))). 
   rewrite E.ceval_expr_spec.
   case (E.ceval_expr (proc_res E f) m'); intros v n0 H.
   destruct H; simpl fst.
   intros t1 y Hy.
   apply H1; apply Ht with y; trivial.
   eapply le_trans; [ |apply pplus_le_r].
   eapply le_trans; [ |apply pplus_le_r]; trivial.

   destruct Hmn as [Hmn1 Hmn2].
   assert (W1:Var.mkV x <> x0).
   intro Heq; elim W.
   injection Heq; intros; subst.
   rewrite (T.inj_pair2 H); trivial.
   case_eq (Var.vis_local x0); rewrite (Var.vis_local_local); intro Hl.
   rewrite return_mem_local with (1:=W1) (2:=Hl). 
   eapply le_trans; [ | apply pplus_le_l]; auto.

   assert (~Var.is_local x0) by trivialb.
   rewrite <- Var.global_local in H.
   rewrite return_mem_global with (1:=W1) (2:=H).
   eapply le_trans; [ | apply pplus_le_r].
   eapply le_trans; [ | apply pplus_le_l]; auto.

   rewrite <- pplus_assoc, <- pplus_assoc, pplus_spec.
   rewrite plus_comm.
   apply plus_le_compat.
   rewrite pplus_assoc; trivial.

   generalize (Hr k m' ((Fb (Fa p)))).     
   case (E.ceval_expr (proc_res E f) m'); intros v n0 H.
   destruct H; [ | trivial].
   intros t0 y Hy.
   apply H1; apply Ht with y; trivial.
  Qed.

  Definition PPT_cmd c := exists F, exists G, PPT c F G.

  Definition PPT_proc' (t:T.type) (f:Proc.proc t) : Prop :=
   (forall t (x:Var.var t), Vset.mem x (fv_expr (proc_res E f)) -> tsize t <= r) /\
   PPT_cmd (proc_body E f) /\
   exists F, exists G, PPT_expr (proc_res E f) F G.
    
  Record PPT_info' :=
   mkPPT_info {
    ppt_info :> forall t (f:Proc.proc t), bool;
    ppt_spec : forall t (f:Proc.proc t), ppt_info f -> PPT_proc' f
   }.

  Open Scope bool_scope.

  Fixpoint expr_poly t (e:E.expr t) {struct e} : bool :=
   match e with
   | E.Ecte _ _ => true
   | E.Evar _ _ => true
   | E.Eop op la =>
     match op, la with
     | O.Olength _, dcons _ _ e dnil => expr_poly e
     | O.OZlength _, dcons _ _ e dnil => expr_poly e 
     | O.Ohd _, dcons _ _ e dnil => expr_poly e
     | O.Otl _, dcons _ _ e dnil => expr_poly e
     | O.Ocons _, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.Oappend _, dcons _ _ e1 (dcons _ _ e2 dnil) =>
       expr_poly e1 && expr_poly e2
     | O.Omem _, dcons _ _ e1 (dcons _ _ e2 dnil) =>
       expr_poly e1 && expr_poly e2
     | O.Oin_dom _ _, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.Oin_range _ _, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2 
     | O.Oimg _ _, dcons _ _ e1 (dcons _ _ e2 dnil) =>
       expr_poly e1 && expr_poly e2
     | O.Onth _, dcons _ _ e1 (dcons _ _ e2 dnil) =>
       expr_poly e1 && expr_poly e2
     | O.Opair _ _, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.Ofst _ _, dcons _ _ e dnil => expr_poly e     
     | O.Osnd _ _, dcons _ _ e dnil => expr_poly e
     | O.Oinl _ _, dcons _ _ e dnil => expr_poly e
     | O.Oinr _ _, dcons _ _ e dnil => expr_poly e
     | O.Oisl _ _, dcons _ _ e dnil => expr_poly e
     | O.Oprojl _ _, dcons _ _ e dnil => expr_poly e
     | O.Oprojr _ _, dcons _ _ e dnil => expr_poly e
     | O.Osome _ , dcons _ _ e dnil => expr_poly e
     | O.Oissome _, dcons _ _ e dnil => expr_poly e
     | O.Oprojo _, dcons _ _ e dnil => expr_poly e
     | O.Oeq_ _, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.Oadd, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.Osub, dcons _ _ e1 (dcons _ _ e2 dnil) =>
       expr_poly e1 && expr_poly e2
     | O.Omul, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.Ole, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.Olt, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2     
     | O.OZadd, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.OZsub, dcons _ _ e1 (dcons _ _ e2 dnil) =>
       expr_poly e1 && expr_poly e2
     | O.OZmul, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.OZle, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.OZlt, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.OZge, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.OZgt, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.OZopp, dcons _ _ e dnil => 
       expr_poly e
     | O.OZdiv, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.OZmod, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.Onot, dcons _ _ e1 dnil => expr_poly e1
     | O.Oand, dcons _ _ e1 (dcons _ _ e2 dnil) =>
       expr_poly e1 && expr_poly e2
     | O.Oor, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.Oimp, dcons _ _ e1 (dcons _ _ e2 dnil) => 
       expr_poly e1 && expr_poly e2
     | O.Oif _ , dcons _ _ e1 (dcons _ _ e2 (dcons _ _ e3 dnil)) => 
       expr_poly e1 && expr_poly e2 && expr_poly e3
     | O.Ouser o, _ => uop_poly o && dforallb expr_poly la
     | _, _ => false
     end
   | E.Eexists t x e1 e2 => expr_poly e1 && expr_poly e2
   | E.Eforall t x e1 e2 => expr_poly e1 && expr_poly e2
   | E.Efind t x e1 e2 => expr_poly e1 && expr_poly e2
   end.

  Lemma expr_poly_spec : forall t (e:E.expr t),
   expr_poly e ->
   exists F, exists G, PPT_expr e F G.
  Proof.
   induction e using E.expr_ind2 with
    (Pl := fun l la => forall t (e:E.expr t), 
      DIn t e la -> expr_poly e -> exists F, exists G, PPT_expr e F G).

   (* Ecst *)
   intro He.
   destruct c; simpl.

    (* Bool *)
    exists (fun _ => pcst 1).
    exists (fun _ => pcst 1).
    apply PPT_bool.

    (* Nat *)
    exists (fun _ => pcst (size_nat n)).
    exists (fun _ => pcst (size_nat n)).
    apply PPT_nat.

    (* Z *)
    exists (fun _ => pcst (size_Z z)).
    exists (fun _ => pcst (size_Z z)).
    apply PPT_Z.

    (* Enil *)
    exists (fun _ => pcst 1).
    exists (fun _ => pcst 1).   
    apply PPT_enil.
 
    (* Enone *)
    exists (fun _ => pcst 1).
    exists (fun _ => pcst 1).   
    unfold PPT_expr; intros; simpl.
    rewrite pcst_spec; auto.

   (* Evar *)
   intro He.
   exists (fun p => p).
   exists (fun _ => pcst 1).   
   apply PPT_var.

   (* Eop *)
   intro Hla.
   rename args into la.
   destruct op; try discriminate.
 
    (* O.Olength *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p : polynomial => pplus 1 (Fe p)).
    exists (fun p : polynomial => pplus (Fe p) (Ge p)).
    apply PPT_length; trivial.

    (* O.OZlength *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p : polynomial => pplus 1 (Fe p)).
    exists (fun p : polynomial => pplus (Fe p) (Ge p)).
    apply PPT_Zlength; trivial.

    (* Ohd *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p => pplus (T.default_poly t) (Fe p)).
    exists (fun p => pplus (pcst 1) (Ge p)).
    apply PPT_head; trivial.

    (* Otl *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p => Fe p).
    exists (fun p => pplus (pcst 1) (Ge p)).
    apply PPT_tail; trivial.

    (* Ocons *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p : polynomial => pplus 1 (pplus (Fe1 p) (Fe2 p))).
    exists (fun p : polynomial => pplus 1 (pplus (Ge1 p) (Ge2 p))).
    apply PPT_Ocons; trivial.

    (* Oappend *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pplus (Fe1 p) (Fe2 p)).
    exists (fun p => pplus (Fe1 p) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_Oappend; trivial.

    (* Omem *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun _ : polynomial => 1).
    exists (fun p : polynomial =>
     pplus (pplus (pmult (Fe2 p) (pplus (Fe1 p) (Fe2 p))) 1)
     (pplus (Ge2 p) (Ge1 p))).
    apply PPT_mem; trivial.

    (* Oin_dom *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pcst 1).
    exists (fun p => pplus (pplus (pmult (Fe2 p) (pplus (Fe1 p) (Fe2 p))) 1)
            (pplus (Ge2 p) (Ge1 p))).
    apply PPT_in_dom; trivial.

    (* Oin_range *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pcst 1).
    exists (fun p => pplus (pplus (pmult (Fe2 p) (pplus (Fe1 p) (Fe2 p))) 1)
            (pplus (Ge2 p) (Ge1 p))).
    apply PPT_in_range; trivial.

    (* Oimg *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pplus (Fe2 p) (T.default_poly t0)).
    exists (fun p => pplus (pplus (pmult (Fe2 p) (pplus (Fe1 p) (Fe2 p))) 1)
            (pplus (Ge2 p) (Ge1 p))).
    apply PPT_img; trivial.

    (* Onth *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pplus (Fe2 p) (T.default_poly t)).
    exists (fun p => pplus (Fe2 p) (pplus (Ge2 p) (Ge1 p))).
    apply PPT_nth with Fe1; trivial.

    (* Opair *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pplus 1 (pplus (Fe1 p) (Fe2 p))).
    exists (fun p => pplus (pcst 1) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_pair; trivial.

    (* Ofst *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p => Fe p).
    exists (fun p => pplus (pcst 1) (Ge p)).
    apply PPT_fst; trivial.

    (* Osnd *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p => Fe p).
    exists (fun p => pplus (pcst 1) (Ge p)).
    apply PPT_snd; trivial.

    (* Oinl *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p => pplus 1 (Fe p)).
    exists (fun p => pplus 1 (Ge p)).
    intros k m p H2.
    generalize (He k m p H2); clear He H2.
    simpl.
    rewrite E.ceval_expr_spec.
    case (E.ceval_expr x m); simpl.
    intros i n [? ?]; split.
    rewrite pplus_spec, pcst_spec; apply le_n_S; trivial. 
    rewrite pplus_spec, pcst_spec; apply le_n_S; rewrite plus_0_r; trivial.
  
    (* Oinr *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p => pplus 1 (Fe p)).
    exists (fun p => pplus 1 (Ge p)).
    intros k m p H2.
    generalize (He k m p H2); clear He H2.
    simpl.
    rewrite E.ceval_expr_spec.
    case (E.ceval_expr x m); simpl.
    intros i n [? ?]; split.
    rewrite pplus_spec, pcst_spec; apply le_n_S; trivial. 
    rewrite pplus_spec, pcst_spec; apply le_n_S; rewrite plus_0_r; trivial.

    (* Oisl *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p => 1).
    exists (fun p => pplus 1 (Ge p)).
    intros k m p H2.
    generalize (He k m p H2); clear He H2.
    simpl.  
    case (E.ceval_expr x m); simpl.
    intros [i1 | i2] n [? ?]; split.
    rewrite pcst_spec; trivial.
    rewrite pplus_spec, pcst_spec; apply le_n_S; rewrite plus_0_r; trivial.
    rewrite pcst_spec; trivial.
    rewrite pplus_spec, pcst_spec; apply le_n_S; rewrite plus_0_r; trivial.
 
    (* Oprojl *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p => pplus (T.default_poly t) (Fe p)).
    exists (fun p => pplus 1 (Ge p)).
    intros k m p H2.
    generalize (He k m p H2); clear He H2.
    simpl.  
    rewrite E.ceval_expr_spec.
    case (E.ceval_expr x m); simpl.
    intros [i1 | i2] n [? ?]; split.
    rewrite pplus_spec; apply le_trans with (Fe p k); auto with arith.   
    rewrite pplus_spec, pcst_spec; apply le_n_S; rewrite plus_0_r; trivial.
    rewrite pplus_spec; apply le_trans with (1:=T.default_poly_spec k t); auto with arith.
    rewrite pplus_spec, pcst_spec; apply le_n_S; rewrite plus_0_r; trivial.

    (* Oprojr *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p => pplus (T.default_poly t0) (Fe p)).
    exists (fun p => pplus 1 (Ge p)).
    intros k m p H2.
    generalize (He k m p H2); clear He H2.
    simpl.  
    rewrite E.ceval_expr_spec.
    case (E.ceval_expr x m); simpl.
    intros [i1 | i2] n [? ?]; split.
    rewrite pplus_spec; apply le_trans with (1:=T.default_poly_spec k t0); auto with arith.
    rewrite pplus_spec, pcst_spec; apply le_n_S; rewrite plus_0_r; trivial.  
    rewrite pplus_spec; apply le_trans with (Fe p k); auto with arith.   
    rewrite pplus_spec, pcst_spec; apply le_n_S; rewrite plus_0_r; trivial.

    (* Osome *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p => pplus 1 (Fe p)).
    exists (fun p => pplus 1 (Ge p)).
    intros k m p H2.
    generalize (He k m p H2); clear He H2.
    simpl.  
    rewrite E.ceval_expr_spec.
    case (E.ceval_expr x m); simpl.
    intros i n [? ?]; split.
    rewrite pplus_spec, pcst_spec; apply le_n_S; trivial.
    rewrite pplus_spec, pcst_spec; apply le_n_S; rewrite plus_0_r; trivial.  

    (* Oissome *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p => 1).
    exists (fun p => pplus 1 (Ge p)).
    intros k m p H2.
    generalize (He k m p H2); clear He H2.
    simpl.  
    case (E.ceval_expr x m); simpl.
    intros i n [? ?]; split.
    rewrite pcst_spec; trivial.
    rewrite pplus_spec, pcst_spec; apply le_n_S; rewrite plus_0_r; trivial.

    (* Oprojo *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe [Ge He] ].
    left; trivial.
    trivial.
    exists (fun p => pplus (T.default_poly t) (Fe p)).
    exists (fun p => pplus 1 (Ge p)).
    intros k m p H2.
    generalize (He k m p H2); clear He H2.
    simpl.  
    rewrite E.ceval_expr_spec.
    case (E.ceval_expr x m); simpl.
    intros [i | ] n [? ?]; split.
    rewrite pplus_spec; apply le_trans with (Fe p k); auto with arith.   
    rewrite pplus_spec, pcst_spec; apply le_n_S; rewrite plus_0_r; trivial.
    rewrite pplus_spec; apply le_trans with (1:=T.default_poly_spec k t); auto with arith.
    rewrite pplus_spec, pcst_spec; apply le_n_S; rewrite plus_0_r; trivial.
      
    (* Oeq_ *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pcst 1).
    exists (fun p => pplus (pplus (Fe1 p) (Fe2 p)) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_eq; eauto.
  
    (* Oadd *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pplus (Fe1 p) (Fe2 p)).
    exists (fun p => pplus (Fe1 p) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_add; trivial.

    (* Osub *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => Fe1 p).
    exists (fun p => pplus (Fe2 p) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_sub; trivial.

    (* Omul *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pplus (Fe1 p) (Fe2 p)).
    exists (fun p => pplus (pmult (Fe1 p) (Fe2 p)) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_mul; trivial.

    (* Ole *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun _ => pcst 1).
    exists (fun p => pplus (Fe1 p) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_le with Fe2; trivial.
  
    (* Olt *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun _ => pcst 1).
    exists (fun p => pplus (Fe2 p) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_lt with Fe1; trivial.

    (* OZadd *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pplus (Fe1 p) (Fe2 p)).
    exists (fun p => pplus (Fe1 p) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_Zadd; trivial.

    (* OZsub *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pplus (Fe1 p) (Fe2 p)).
    exists (fun p => pplus (Fe2 p) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_Zsub; trivial.

    (* OZmul *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pplus (Fe1 p) (Fe2 p)).
    exists (fun p => pplus (pmult (Fe1 p) (Fe2 p)) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_Zmul; trivial.


    (* OZle *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun _ => pcst 1).
    exists (fun p => pplus (Fe1 p) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_Zle with Fe2; trivial.
  
    (* OZlt *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun _ => pcst 1).
    exists (fun p => pplus (Fe2 p) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_Zlt with Fe1; trivial.

    (* OZge *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun _ => pcst 1).
    exists (fun p => pplus (Fe2 p) (pplus (Ge1 p) (Ge2 p))).
    eapply PPT_Zge with Fe1; trivial.
  
    (* OZgt *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun _ => pcst 1).
    exists (fun p => pplus (Fe2 p) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_Zgt with Fe1; trivial.

    (* OZopp *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    simpl in Hla; trivial.
    exists (fun p => Fe1 p).
    exists (fun p => pplus (Fe1 p) (Ge1 p)).
    apply PPT_Zopp; trivial.

    (* OZdiv *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => pplus (Fe1 p) 1).
    exists (fun p => pplus (Fe1 p) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_Zdiv with Fe2; trivial.

    (* OZmod *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun p => Fe2 p).
    exists (fun p => pplus (Fe2 p) (pplus (Ge1 p) (Ge2 p))).
    apply PPT_Zmod with Fe1; trivial.

    (* Onot *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    simpl in Hla; trivial.
    exists (fun _ => pcst 1).
    exists (fun p => pplus 1 (Ge1 p)).
    apply PPT_not with Fe1; trivial.

    (* Oand *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun _ => pcst 1).
    exists (fun p => pplus 1 (pplus (Ge1 p) (Ge2 p))).
    apply PPT_and with Fe1 Fe2; trivial.

    (* Oor *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun _ => pcst 1).
    exists (fun p => pplus 1 (pplus (Ge1 p) (Ge2 p))).
    apply PPT_or with Fe1 Fe2; trivial.

    (* Oimp *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    exists (fun _ => pcst 1).
    exists (fun p => pplus 1 (pplus (Ge1 p) (Ge2 p))).
    apply PPT_imp with Fe1 Fe2; trivial.

    (* Oif *)
    T.dlist_inversion la.
    rewrite Heq in IHe, Hla |- *.
    simpl in Hla; unfold is_true in Hla.
    apply andb_prop in Hla; destruct Hla.
    apply andb_prop in H; destruct H.
    destruct (IHe _ x) as [Fe1 [Ge1 He1] ].
    left; trivial.
    trivial.
    destruct (IHe _ x0) as [Fe2 [Ge2 He2] ].
    right; left; trivial.
    trivial.
    destruct (IHe _ x1) as [Fe3 [Ge3 He3] ].
    right; right; left; trivial.
    trivial.
    exists (fun p => pplus (Fe2 p) (Fe3 p)).
    exists (fun p => pplus 1 (pplus (Ge1 p) (pplus (Ge2 p) (Ge3 p)))).
    apply PPT_if with Fe1; trivial.

    (* Ouser *)
    simpl in Hla; apply andb_prop in Hla; destruct Hla.
    apply uop_poly_spec; trivial.
    intros; apply IHe.
    trivial.
    rewrite dforallb_forall in H0.
    apply H0; trivial. 
    intros t1 t2; case_eq (T.eq_dec t1 t2); intros.
    left; trivial.
    apply T.eq_dec_r in H2; right; trivial.

    (* Eexists *)
    simpl; intros.
    rewrite is_true_andb in H; destruct H.
    exists (fun _ => pcst 1).
    destruct (IHe1 H) as (F1, (G1, H1)).
    destruct (IHe2 H0) as (F2, (G2, H2)).
    unfold PPT_expr in H1, H2.
    exists (fun p => pplus (pmult (F2 p) (G1 (pplus p (F2 p)))) (G2 p)).
    red.
    intros k m p Hfv; simpl.
    case_eq (E.ceval_expr e2 m).
    intros l2 n2; case_eq (cexistsb (fun v0 : T.interp k t => E.ceval_expr e1 (m {!v <-- v0!})) l2 n2).
    intros b n1 Heq1 Heq2; split.
    rewrite pcst_spec; trivial.
    match type of Heq1 with cexistsb ?F l2 n2 = _ => set (f := F) in Heq1 end.
    assert (W:= H2 k m p); rewrite Heq2 in W; destruct W.
    intros; apply Hfv; unfold fv_expr; simpl; fold (fv_expr e2); auto with set.   
    assert (forall a : T.interp k t,
     In a l2 -> snd (f a) <= peval (G1 (pplus p (F2 p))) k).
       intros; unfold f.  
       assert (W:= H1 k (m {!v <-- a!}) (pplus p (F2 p))).
       case_eq (E.ceval_expr e1 (m {!v <-- a!})); intros.
       rewrite H6 in W; destruct W;[ | trivial].
       intros; rewrite pplus_spec.
       destruct (Var.eq_dec v x).
       inversion e; simpl; rewrite Mem.get_upd_same.
       apply le_trans with (peval (F2 p) k);[ | apply le_plus_r].
       apply le_trans with (2:= H3).
       apply List_size_le; trivial.
       rewrite Mem.get_upd_diff;[ | trivial].
       assert (Vset.mem x (fv_expr (E.Eexists v e1 e2))).
         unfold fv_expr; simpl; fold (fv_expr e2); auto with set.
       apply le_trans with (1:= Hfv _ _ H8); apply le_plus_l.
    assert (W:= @cexistsb_count _ f (peval (G1 (pplus p (F2 p))) k) l2 H5 n2).
    rewrite Heq1 in W; simpl in W.
    apply le_trans with (1:= W).
    rewrite pplus_spec; apply plus_le_compat;[ | trivial].  
    rewrite pmult_spec; apply mult_le_compat_r.
    apply le_trans with (2:= H3).
    exact (@List_size_length k t l2).

    (* Eforall *)
    simpl; intros.
    rewrite is_true_andb in H; destruct H.
    exists (fun _ => pcst 1).
    destruct (IHe1 H) as (F1, (G1, H1)).
    destruct (IHe2 H0) as (F2, (G2, H2)).
    unfold PPT_expr in H1, H2.
    exists (fun p => pplus (pmult (F2 p) (G1 (pplus p (F2 p)))) (G2 p)).
    red.
    intros k m p Hfv; simpl.
    case_eq (E.ceval_expr e2 m).
    intros l2 n2; case_eq (cforallb (fun v0 : T.interp k t => E.ceval_expr e1 (m {!v <-- v0!})) l2 n2).
    intros b n1 Heq1 Heq2; split.
    rewrite pcst_spec; trivial.
    match type of Heq1 with cforallb ?F l2 n2 = _ => set (f := F) in Heq1 end.
    assert (W:= H2 k m p); rewrite Heq2 in W; destruct W.
    intros; apply Hfv; unfold fv_expr; simpl; fold (fv_expr e2); auto with set.   
    assert (forall a : T.interp k t,
     In a l2 -> snd (f a) <= peval (G1 (pplus p (F2 p))) k).
       intros; unfold f.  
       assert (W:= H1 k (m {!v <-- a!}) (pplus p (F2 p))).
       case_eq (E.ceval_expr e1 (m {!v <-- a!})); intros.
       rewrite H6 in W; destruct W;[ | trivial].
       intros; rewrite pplus_spec.
       destruct (Var.eq_dec v x).
       inversion e; simpl; rewrite Mem.get_upd_same.
       apply le_trans with (peval (F2 p) k);[ | apply le_plus_r].
       apply le_trans with (2:= H3).
       apply List_size_le; trivial.
       rewrite Mem.get_upd_diff;[ | trivial].
       assert (Vset.mem x (fv_expr (E.Eexists v e1 e2))).
         unfold fv_expr; simpl; fold (fv_expr e2); auto with set.
       apply le_trans with (1:= Hfv _ _ H8); apply le_plus_l.
    assert (W:= @cforallb_count _ f (peval (G1 (pplus p (F2 p))) k) l2 H5 n2).
    rewrite Heq1 in W; simpl in W.
    apply le_trans with (1:= W).
    rewrite pplus_spec; apply plus_le_compat;[ | trivial].  
    rewrite pmult_spec; apply mult_le_compat_r.
    apply le_trans with (2:= H3).
    exact (@List_size_length k t l2).

    (* Efind *)
    simpl; intros.
    rewrite is_true_andb in H; destruct H.
    destruct (IHe1 H) as (F1, (G1, H1)).
    destruct (IHe2 H0) as (F2, (G2, H2)).
    unfold PPT_expr in H1, H2.
    exists (fun p => pplus (F2 p) (T.default_poly t)).
    exists (fun p => pplus (pmult (F2 p) (G1 (pplus p (F2 p)))) (G2 p)).
    red.
    intros k m p Hfv; simpl.
    case_eq (E.ceval_expr e2 m).
    intros l2 n2; case_eq (cfind_default (fun v0 : T.interp k t => E.ceval_expr e1 (m {!v <-- v0!}))
      l2 n2 (T.default k t)).
    intros r1 n1 Heq1 Heq2.
    assert (HH:= H2 k m p).
    rewrite Heq2 in HH; destruct HH as (HH1, HH2).
    intros; apply Hfv; unfold fv_expr; simpl; fold (fv_expr e2); auto with set.  
    split.
    assert (X : forall x : T.interp k t,
     (fun v0 : T.interp k t => E.eval_expr e1 (m {!v <-- v0!})) x =
     fst ((fun v0 : T.interp k t => E.ceval_expr e1 (m {!v <-- v0!})) x)).
     intros; apply E.ceval_expr_spec.
    assert (W:= @find_cfind_default _
             (fun v0 : T.interp k t => E.eval_expr e1 (m {!v <-- v0!}))
             (fun v0 : T.interp k t => E.ceval_expr e1 (m {!v <-- v0!}))
             (T.default k t) X l2 n2). 
    rewrite Heq1 in W; simpl in W; rewrite <- W.
    unfold find_default; rewrite pplus_spec.
    case_eq (find (fun v0 : T.interp k t => E.eval_expr e1 (m {!v <-- v0!})) l2); intros.
    destruct (find_In _ _ H3).
    apply le_trans with (peval (F2 p) k);[ | apply le_plus_l].
    apply le_trans with (2:= HH1).
    apply List_size_le; trivial.
    apply le_trans with (peval (T.default_poly t) k).
    apply T.default_poly_spec.
    apply le_plus_r.
    match type of Heq1 with cfind_default ?F _ _ _ = _ => set (f := F) in Heq1 end.
    assert (forall a : T.interp k t,
     In a l2 -> snd (f a) <= peval (G1 (pplus p (F2 p))) k).
       intros; unfold f.  
       assert (W:= H1 k (m {!v <-- a!}) (pplus p (F2 p))).
       case_eq (E.ceval_expr e1 (m {!v <-- a!})); intros.
       rewrite H4 in W; destruct W;[ | trivial].
       intros; rewrite pplus_spec.
       destruct (Var.eq_dec v x).
       inversion e; simpl; rewrite Mem.get_upd_same.
       apply le_trans with (peval (F2 p) k);[ | apply le_plus_r].
       apply le_trans with (2:= HH1).
       apply List_size_le; trivial.
       rewrite Mem.get_upd_diff;[ | trivial].
       assert (Vset.mem x (fv_expr (E.Efind v e1 e2))).
         unfold fv_expr; simpl; fold (fv_expr e2); auto with set.
       apply le_trans with (1:= Hfv _ _ H6); apply le_plus_l.
    assert (W:= @cfind_default_count _ f _ l2 (T.default k t) H3 n2).
    rewrite Heq1 in W; apply le_trans with (1:= W).
    rewrite pplus_spec; apply plus_le_compat; trivial.
    rewrite pmult_spec; apply mult_le_compat; trivial.
    apply le_trans with (2:= HH1).
    apply (List_size_length l2).
  
   (* Nil *)
   intros t e Hin; elim Hin.

   (* Cons *)
   intros t0 e0 Hin He0.
   simpl in Hin; case Hin; intro H.
   inversion H; clear H2 H3; subst.
   rewrite (T.eq_dep_eq H) in He0 |- *; apply IHe; trivial.
   auto.
  Qed.

  Fixpoint support_poly t (s:E.support t) : bool :=
   match s with 
   | E.Dbool => true
   | E.Dnat e => expr_poly e
   | E.DZ e1 e2 => expr_poly e1 && expr_poly e2
   | E.Duser _ us => usupport_poly us
   | E.Dprod _ _ s1 s2 => support_poly s1 && support_poly s2
   end.

  Lemma support_poly_spec : forall t (s:E.support t),
   support_poly s ->
   exists F, exists G, PPT_support s F G.
  Proof.
   intros t s.
   induction s.

   (* Dbool *)
   intros _.
   exists (fun p => pplus p 1). 
   exists (fun _ => pcst 1).
   apply PPT_Dbool.

   (* Dnat *)
   intros Hs; simpl in Hs.
   destruct (expr_poly_spec _ Hs) as [Fe [Ge He] ].
   exists Fe.
   exists Ge.
   apply PPT_Dnat; trivial.

   (* DZ *)
   intros Hs; simpl in Hs.   
   apply andb_true_iff in Hs.
   destruct Hs.
   destruct (expr_poly_spec _ H) as [F1 [G1 H1] ].
   destruct (expr_poly_spec _ H0) as [F2 [G2 H2] ].
   exists (fun p : polynomial => pplus 1 (pplus (F1 p) (F2 p))).
   exists (fun p : polynomial => pplus (G1 p) (G2 p)).
   apply PPT_DZ; trivial.

   (* Duser *)
   intro; apply usupport_poly_spec; trivial.
 
   (* Dprod *)
   intro H; simpl in H; apply andb_prop in H.
   destruct IHs1 as [F1 [ G1 H1 ] ]; [ tauto | ].
   destruct IHs2 as [F2 [ G2 H2 ] ]; [ tauto | ].
   exists (fun p : polynomial => pplus 1 (pplus (F1 p) (F2 p))).
   exists (fun p : polynomial => pmult (G1 p) (G2 p)).
   apply PPT_prod; trivial.
  Qed.


  Section CMD_POLY.
   
   Variable proc_poly : PPT_info'.

   Definition args_poly l (le:dlist E.expr l) := dforallb (expr_poly) le.

   Lemma args_poly_aux : forall l (la:dlist E.expr l),
    args_poly la  ->
    (forall t (e:E.expr t), DIn t e la -> forall t0 (x:Var.var t0), Vset.mem x (fv_expr e) -> tsize t0 <= r) ->
    exists F,
    forall t (e:E.expr t),
     DIn t e la ->
      forall k (m:Mem.t k) p,
       (forall t (x:Var.var t), tsize t <= r -> T.size (m x) <= peval p k) ->
       T.size (E.eval_expr e m) <= peval (F p) k.
   Proof.
    intros l la.
    induction l as [e1 [la' Heq] | ]; intros Hla Hr.
    
    rewrite (T.l_eq_dep_eq (dlist_nil la)).
    exists (fun p => p); intros t1 e He; elim He.

    destruct (dlist_cons la) as [e1 [la' Heq] ].
    rewrite (T.l_eq_dep_eq Heq) in Hla, Hr |- *; clear la Heq.
    simpl in Hla.
    case_eq (expr_poly e1).
    intros W; rewrite W in Hla.
    destruct (expr_poly_spec _ W) as [Fe [Ge He] ].
    destruct (IHl la' Hla) as [F Ha]; clear IHl.
    intros t e0 He0 t0 x Hx.
    refine (Hr _ _ _ _ _ Hx); simpl; auto.
    
    exists (fun p => pplus (Fe p) (F p)).
    intros t0 e0 He0 k m p Hm.
    simpl in He0; case He0; intro Heq.
    inversion Heq; intros; subst.
    rewrite (T.inj_pair2 H2) in *; clear H1 H2 Heq.
    generalize (He k m p).
    rewrite E.ceval_expr_spec; case (E.ceval_expr e1 m).    
    intros i n H.
    destruct H as [Hv Hn].
    intros t x Hx; apply Hm.
    refine (Hr _ _ _ _ _ Hx); simpl; auto.

    eapply le_trans; [ | apply pplus_le_l]; trivial.

    eapply le_trans; [ | apply pplus_le_r].
    apply (Ha t0 e0 Heq); trivial.

    intro H; rewrite H in Hla; discriminate.
   Qed.

   Fixpoint tsize_default_poly r : polynomial :=
    pplus (utsize_default_poly r)
    match r with
     | O => 1
     | S r' => pplus 1 (pplus (tsize_default_poly r') (tsize_default_poly r'))
    end.
  
   Lemma tsize_default_poly_le : forall r n, 
    1 <= peval (tsize_default_poly r) n.
   Proof.
    induction r0; simpl; intros.
    rewrite pplus_spec, pcst_spec; omega.
    rewrite pplus_spec, pplus_spec, pcst_spec; omega.
   Qed.

   Lemma tsize_default_poly_spec : forall t,
    tsize t <= r -> 
    forall k, T.size (T.default k t) <= peval (tsize_default_poly r) k.
   Proof.
   intro t; generalize t r; clear t.
    induction t; simpl; intros.

    destruct r0; simpl.
    eapply le_trans; [ | apply pplus_le_l].
    apply utsize_default_poly_spec; trivial.
    eapply le_trans; [ | apply pplus_le_l].
    apply utsize_default_poly_spec; trivial.

    apply tsize_default_poly_le.   
    apply tsize_default_poly_le.
    apply tsize_default_poly_le.
    apply tsize_default_poly_le.
    apply tsize_default_poly_le.

    destruct r0; [omega | ].
    simpl.
    repeat rewrite pplus_spec.
    eapply le_trans; [ | apply le_plus_r].
    rewrite pcst_spec; apply le_n_S; apply plus_le_compat.
    apply IHt1; omega.
    apply IHt2; omega.

    destruct r0; [omega | ].
    simpl.
    repeat rewrite pplus_spec.
    eapply le_trans; [ | apply le_plus_r].
    rewrite pcst_spec; apply le_n_S.
    eapply le_trans; [ | apply le_plus_r].
    apply IHt1; omega.

    apply tsize_default_poly_le.
   Qed.
       
   Lemma args_poly_spec : forall t (f:Proc.proc t) (la:E.args (Proc.targs f)),
    args_poly la ->
    (forall t (e:E.expr t), DIn t e la -> forall t0 (x:Var.var t0), Vset.mem x (fv_expr e) -> tsize t0 <= r) ->
    exists F, exists G,
     forall k (m:Mem.t k) p,
      (forall t (x:Var.var t), tsize t <= r -> T.size (m x) <= peval p k) ->      
      bound (pplus (tsize_default_poly r) (pplus p (F p))) (G p) (cinit_mem E f la m).
   Proof.   
    intros t f la.
    destruct f; simpl in la.
    set (f:=Proc.mkP pname targs tres). 
    induction targs.
    
    intros _ Hr.
    rewrite (T.l_eq_dep_eq (dlist_nil la)).
    exists (fun _ => 0).
    exists (fun _ => 0).
    intros k m p Hm.
    unfold bound; rewrite (surjective_pairing (cinit_mem E f (dnil _) m)).
    rewrite cinit_mem_spec_l, cinit_mem_spec_r; split; [ | apply le_O_n].
    simpl.
    intros t Ht x.
    generalize (lookup_init_mem E f (dnil _) m x).
    generalize (get_arg_Some2 x (proc_params E f) (dnil _)).
    simpl (Proc.targs f); case (get_arg x (lt1:=nil) (proc_params E f) (dnil E.expr)).
    intros e V W; rewrite W; clear W.
    elim (V e); trivial.

    intros _ W; rewrite W.
    destruct x; intros.
    rewrite <- Mem.global_spec; trivial.
    eapply le_trans; [ | apply pplus_le_r]; 
    eapply le_trans; [ | apply pplus_le_l].
    apply (Hm t); auto.

    rewrite Mem.global_local; trivial.
    eapply le_trans; [ | apply pplus_le_l].
    apply tsize_default_poly_spec; trivial.
 
    destruct (dlist_cons la) as [e [la' Hla'] ]; intros Hla Hr.
    destruct (args_poly_aux la Hla Hr) as [F Haux]; generalize Hla; clear Hla.
    rewrite (T.l_eq_dep_eq Hla') in Haux, Hr |- *; clear Hla'; simpl.
    case_eq (expr_poly e); intro H1; try (intro; discriminate).
    case_eq (args_poly la'); intro H2; try (intro; discriminate); intros _.
    destruct (expr_poly_spec _ H1) as [Fe [Ge He] ].
    destruct (IHtargs la' H2) as [Fa [Ga Ha] ].
    intros t e0 He0 t0 x Hx.
    apply Hr with (2:=Hx); simpl; auto.
 
    exists F.
    exists (fun p => pplus (Ge p) (Ga p)).
    intros k m p Hm.
    unfold bound; rewrite (surjective_pairing (cinit_mem E f (dcons _ e la') m)).
    rewrite cinit_mem_spec_l, cinit_mem_spec_r; split.
    
    intros t Hx x.
    generalize (lookup_init_mem E f (dcons _ e la') m x).
    generalize (get_arg_Some2 x (proc_params E f) (dcons _ e la')).
    simpl (Proc.targs f).
    case (get_arg x (lt1:=a::targs) (proc_params E f) (dcons _ e la')).
    intros e0 V W; rewrite W; clear W.
    eapply le_trans; [ | apply pplus_le_r].
    eapply le_trans; [ | apply pplus_le_r]; auto.
  
    intros _ W; rewrite W.
    destruct x; intros.
    rewrite <- Mem.global_spec; trivial.
    eapply le_trans; [ | apply pplus_le_r].
    eapply le_trans; [ | apply pplus_le_l]; auto.

    rewrite Mem.global_local; trivial.
    eapply le_trans; [ | apply pplus_le_l].
    apply tsize_default_poly_spec; trivial.

    simpl.
    rewrite pplus_spec, plus_comm.
    apply plus_le_compat.
    generalize (He k m p); case (E.ceval_expr e m).
    intros ? ? H; destruct H.
    intros t x Hx; apply Hm.
    apply Hr with (2:=Hx); simpl; auto.
    trivial.
    generalize (Ha k m p).
    unfold bound; rewrite (surjective_pairing (cinit_mem E (Proc.mkP pname targs tres) la' m)).   
    rewrite cinit_mem_spec_r; tauto.
   Qed.
 
   Open Scope bool_scope.

   Fixpoint instr_poly (i:I.instr) {struct i} : bool :=
    match i with
    | I.Instr (I.Assign _ x e) => 
      expr_poly e && 
      Vset.forallb 
       (fun x => match x with Var.mkV t _ => Compare_dec.leb (tsize t) r end) 
       (fv_expr e)
    | I.Instr (I.Random _ x s) => 
      support_poly s && 
      Vset.forallb 
       (fun x => match x with Var.mkV t _ => Compare_dec.leb (tsize t) r end) 
       (fv_distr s)
    | I.Cond e c1 c2 => 
      expr_poly e && 
      Vset.forallb 
       (fun x => match x with Var.mkV t _ => Compare_dec.leb (tsize t) r end) 
       (fv_expr e) &&
      forallb instr_poly c1 && 
      forallb instr_poly c2
    | I.Call t x f la => 
      args_poly la && 
      dforallb (fun t (e:E.expr t) => 
       Vset.forallb
        (fun x => match x with Var.mkV t _ => Compare_dec.leb (tsize t) r end) 
        (fv_expr e)) la &&
       proc_poly _ f
    | _ => false
    end.

   Definition cmd_poly := forallb instr_poly.

   Lemma cmd_poly_spec : forall c, 
    cmd_poly c = true ->
    exists F, exists G, PPT c F G.
   Proof.
    induction c using I.cmd_ind with
     (Pi:=fun i => instr_poly i = true -> exists Fi, exists Gi, PPT [i] Fi Gi).

     (* baseInstr *)
     destruct i.

      (* Assign *)
      intros Hi; simpl in Hi.
      apply andb_prop in Hi; destruct Hi as [Hi Hr].
      destruct (expr_poly_spec _ Hi) as [ Fe [Ge He] ].
      exists (fun p => pplus (Fe p) p); exists Ge.
      apply PPT_assign; trivial.
      intros t0 x Hx.
      apply leb_complete.
      apply fold_is_true.
      refine (Vset.forallb_correct _ Hr Hx).
      intros y z H.
      unfold Vset.E.eq in H; rewrite H; trivial.

      (* Random *)
      intro Hi; simpl in Hi.
      apply andb_prop in Hi; destruct Hi as [Hi Hr].
      destruct (support_poly_spec _ Hi) as [ Fs [Gs Hs] ].
      exists (fun p => pplus (Fs p) p); exists Gs.
      apply PPT_random; trivial.
      intros t0 x Hx.
      apply leb_complete.
      apply fold_is_true.
      refine (Vset.forallb_correct _ Hr Hx).
      intros y z H.
      unfold Vset.E.eq in H; rewrite H; trivial.

      (* Cond *)
      intro Hi; simpl in Hi.
      apply andb_prop in Hi; destruct Hi as [Hi H2].
      apply andb_prop in Hi; destruct Hi as [Hi H1].
      apply andb_prop in Hi; destruct Hi as [H0 Hr].
      destruct (expr_poly_spec _ H0) as [ Fe [Ge He] ].
      destruct (IHc1 H1) as [ Fc1 [Gc1 Hc1] ].
      destruct (IHc2 H2) as [ Fc2 [Gc2 Hc2] ].
      exists (fun p => pplus (Fe p) (pplus (Fc1 p) (Fc2 p))).
      exists (fun p => pplus (Ge p) (pplus (Gc1 p) (Gc2 p))).
      apply PPT_cond; trivial.
      intros t0 x Hx.
      apply leb_complete.
      apply fold_is_true.
      refine (Vset.forallb_correct _ Hr Hx).
      intros y z H.
      unfold Vset.E.eq in H; rewrite H; trivial.

      (* While *)
      intros; discriminate.

      (* Call *)
      intro Hi; simpl in Hi.
      apply andb_prop in Hi; destruct Hi as [Hi H0].
      apply andb_prop in Hi; destruct Hi as [H1 H2].

      destruct (ppt_spec _ _ H0) as [H3 [ [Fb [Gb Hb] ]  [Fr [Gr Hr] ] ] ]. 
      destruct (args_poly_spec _ _ H1) as [ Fa [Ga Ha] ].
      intros t0 e He0 t1 y Hy.
      apply leb_complete.
      apply fold_is_true.
      assert (Hdec:forall t1 t2:T.type, sumbool (t1 = t2) (t1 <> t2)).
      intros t2 t3; generalize (T.eqb_spec t2 t3); case (T.eqb t2 t3); auto.
      rewrite (dforallb_forall Hdec
       (fun t (e:E.expr t) =>
          Vset.forallb
            (fun x =>
             match x with
             | Var.mkV t _ => Compare_dec.leb (tsize t) r
             end) (fv_expr e)) ) in H2.
      refine (Vset.forallb_correct _ (H2 t0 e He0) Hy).
      intros w z H.
      unfold Vset.E.eq in H; rewrite H; trivial.
      exists (fun p => pplus p (pplus (Fb (pplus (tsize_default_poly r) (pplus p (Fa p)))) 
        (Fr (Fb (pplus (tsize_default_poly r) (pplus p (Fa p))))))).
      exists (fun p => pplus (Ga p) (pplus (Gb (pplus (tsize_default_poly r) (pplus p (Fa p)))) 
        (Gr (Fb (pplus (tsize_default_poly r) (pplus p (Fa p))))))).
      apply PPT_call; trivial.

     intro.
     exists (fun p => p).
     exists (fun _ => 0).
     apply PPT_nil; trivial.

     intro H; simpl in H.
     apply andb_prop in H; destruct H as [H0 H1].
     destruct (IHc H0) as [ Fi [Gi Hi] ].
     destruct (IHc0 H1) as [ Fc [Gc Hc] ].
     exists (fun p => Fc (Fi p)).
     exists (fun p => pplus (Gi p) (Gc (Fi p))).
     apply PPT_cons; trivial.
    Qed.

  End CMD_POLY.

  Definition res_poly (t:T.type) (p:Proc.proc t) : bool :=
   Vset.forallb 
    (fun x => match x with Var.mkV t _ => Compare_dec.leb (tsize t) r end)
    (fv_expr (proc_res E p)).

   Lemma res_poly_spec : forall t (p:Proc.proc t), 
    res_poly p ->
    forall t (x:Var.var t),
     Vset.mem x (fv_expr (proc_res E p)) -> tsize t <= r.
   Proof.
    intros ? ? H ? ? H0.
    apply leb_complete; apply fold_is_true.
    refine (Vset.forallb_correct _ H H0).
    intros ? ? Heq; unfold Vset.E.eq in Heq; rewrite Heq; trivial.
   Qed.

 End PPT.

 Definition tsize_limit := 10.

 Definition PPT_proc E := PPT_proc' E tsize_limit. 

 Definition PPT_info E := PPT_info' E tsize_limit.

 Definition PPT_empty_info E : PPT_info E := 
  mkPPT_info (fun t (f:Proc.proc t) => false) 
   (fun _ f => false_true_elim (PPT_proc E f)).

 Definition PPT_add_info E (pi:PPT_info E) t (p:Proc.proc t) : PPT_info E.
  intros E pi t p.
  case_eq (res_poly E tsize_limit p); intro Hres; [ | exact pi].
  case_eq (cmd_poly pi (proc_body E p)); intro Hp; [ | exact pi].
  case_eq (expr_poly (proc_res E p)); intro He; [ | exact pi].
  refine (
   mkPPT_info 
   (fun t (f:Proc.proc t) => if Proc.eqb f p then true else pi t f)
   _).
  intros t0 f.
  generalize (Proc.eqb_spec_dep f p).
  case (Proc.eqb f p); intros H H0.
  inversion H; subst.
  rewrite (T.inj_pair2 H4).
  split; [ | split].
  refine (res_poly_spec Hres).
  refine (cmd_poly_spec pi (proc_body E p) Hp).
  refine (expr_poly_spec _ He).
  apply (ppt_spec pi); trivial. 
 Defined.

 Definition PPT_add_adv_info : forall E t (A:Proc.proc t),
  PPT_info E -> 
  PPT_proc E A ->
  PPT_info E.  
  intros E' t A pi HA.
  refine (mkPPT_info (fun _ f => if Proc.eqb f A then true else pi _ f) _).
  intros t0 f.
  generalize (Proc.eqb_spec_dep f A).
  case (Proc.eqb f A); intros H H0.
  inversion H; subst.
  rewrite (T.inj_pair2 H4).
  apply HA.
  apply ppt_spec with pi; trivial.
 Defined.

 Ltac PPT_tac pi :=
  match goal with
   |- PPT_cmd _ _ ?c =>
   let Heq := fresh "Heq" in
   let res := fresh "res" in
    compute_assertion Heq res (cmd_poly pi c);
    refine (cmd_poly_spec pi c Heq)
  end.

 Ltac PPT_proc_tac pi :=
  match goal with
   |- PPT_proc ?E ?p =>
   let Heq := fresh "Heq" in
   let res := fresh "res" in
    split; 
     [ refine (res_poly_spec _); trivial |
       split; 
       [ compute_assertion Heq res (cmd_poly pi (proc_body E p)); 
         refine (cmd_poly_spec pi (proc_body E p) Heq) |
         refine (expr_poly_spec (proc_res E p) _); trivial ] ]
  end.

End Make_PPT.
