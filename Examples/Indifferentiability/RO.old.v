Set Implicit Arguments.

Require Export Semantics.
Require Export RelationClasses.
Require Import EncodingAux.


(** TODO: Move to CCMisc.v, replacing existing lemmas *)
Lemma PermutP_weaken : forall A B (R1 R2:A -> B -> Prop) la lb,
 (forall a b, In a la -> In b lb -> R1 a b -> R2 a b) -> 
 PermutP R1 la lb ->
 PermutP R2 la lb.
Proof.
 induction la; intros.
 inversion H0; constructor.
 induction lb; inversion H0; subst.
 elim (app_cons_not_nil l1' l2' x' (eq_sym H3)).
 apply permP_swap.
 apply H; auto using in_eq.
 rewrite <-H3; apply in_or_app; right; apply in_eq.
 apply IHla. 
 intros; apply H; auto using in_cons, in_eq.
 rewrite <-H3; destruct (in_app_or _ _ _  H2); auto using in_or_app, in_cons.
 trivial.
Qed.

Lemma PermutP_refl' : forall A (R:A -> A -> Prop) l,
 (forall x, In x l -> R x x) ->
 PermutP R l l.
Proof.
 induction l; intros.
 constructor.
 apply PermutP_cons.
 apply H; apply in_eq.
 apply IHl; intros x Hx; exact (H x (in_cons  a _ _  Hx)). 
Qed.


Module RO (A:A_TYPE) (G:CYCLIC_GROUP_WITH_ORDER) (ET:ENCODING_TYPE A G).

 Module Sem := SEM A G ET.

 Import Sem.


 Lemma A_eqb_refl : forall k (x:A.t k), A.eqb x x.
  intros.
  generalize (A.eqb_spec x x).
  case (A.eqb x x); intuition.
 Qed.

 Lemma G_eqb_refl : forall k (x:G.t k), G.eqb x x.
 Proof.
  intros.
  generalize (G.eqb_spec x x).
  case (G.eqb x x); intuition.
 Qed.

 Lemma Geqb_true: forall k (x y:G.t k), G.eqb x y -> x = y. 
 Proof.
  intros.
  generalize (G.eqb_spec x y).
  rewrite H; trivial.
 Qed.

 (** TODO: move to GenOpt.v, where [expr_eval_eq] is *)
 Lemma eval_lt : forall k (m:Mem.t k)  (e1 e2:E.expr T.Nat),
  E.eval_expr e1 m < E.eval_expr e2 m <-> E.eval_expr (e1 <! e2) m.
 Proof.
  intros; split; intros.
  change (is_true (leb (E.eval_expr e1 m + 1) (E.eval_expr e2 m))).
  apply leb_correct; omega.
  change (is_true (leb (E.eval_expr e1 m + 1) (E.eval_expr e2 m))) in H.
  apply leb_complete in H; omega.
 Qed.

 Lemma eval_le : forall k (m:Mem.t k) (e1 e2:E.expr T.Nat),
  (E.eval_expr e1 m <= E.eval_expr e2 m)%nat <-> E.eval_expr (e1 <=! e2) m.
 Proof.
  intros; simpl; unfold O.eval_op; simpl; split; intro.
  apply leb_correct; omega.
  apply leb_complete in H; omega.
 Qed.

 Lemma eval_negb : forall (e:E.expr T.Bool) k (m:Mem.t k),
  negb (E.eval_expr e m) = E.eval_expr (!e) m. 
 Proof.
  trivial.
 Qed.

 Lemma eval_andb: forall (e1 e2:E.expr T.Bool) k (m:Mem.t k),
  andb (E.eval_expr e1 m) (E.eval_expr e2 m) = E.eval_expr (e1 && e2) m.
 Proof.
  trivial.
 Qed.
 (***************************************************)


 (** TODO: Move to Adversary.v *)
 Lemma slossless_app : forall E c1 c2,
  slossless_c E c1 ->
  slossless_c E c2 ->
  slossless_c E (c1 ++ c2).
 Proof.
  induction c1; intros.
  simpl; trivial.
  inversion_clear H.
  rewrite <-app_comm_cons.
  apply slossless_cons; auto.
 Qed.


 (** TODO: Move to SemInstr.v *)
 Lemma deno_if_nil_elim : forall (b:E.expr T.Bool) E k (m:Mem.t k) f,
  mu ([[ [If b _then nil] ]] E m) f == f m.
 Proof.
  intros; rewrite deno_cond_elim.
  case (E.eval_expr b m); rewrite deno_nil_elim; trivial.
 Qed.
 
 Lemma while_false_elim : forall (e:E.expr T.Bool) c E k (m:Mem.t k) f,
  E.eval_expr e m = false ->
  mu ([[ [while e do c] ]] E m) f == f m.
 Proof.
  intros; rewrite deno_while_elim, deno_cond_elim, H.
  apply deno_nil_elim.
 Qed.

 Lemma unroll_while_false_elim: forall (e:E.expr T.Bool) c E k (m:Mem.t k) n f,
  E.eval_expr e m = false ->
  mu ([[unroll_while e c n]] E m) f == f m.
 Proof.
  intros; case n; unfold unroll_while.
  apply deno_if_nil_elim.
  intro n'; fold (unroll_while e c n').
  rewrite deno_cond_elim, H, deno_nil_elim; trivial.
 Qed.
 

 Section BOUNDED_LOOP.

  Variable c : cmd.
  Variable E : env.
  Variable b : E.expr T.Bool.
  Variable variant : E.expr T.Nat.

  Hypothesis Hvar: forall k (m:Mem.t k), 
   E.eval_expr b m -> 
   range (EP k (variant <! (E.eval_expr variant m))) ([[c]] E m).

  Lemma lossless_bounded_while:
   lossless E c ->
   lossless E [while b do c].
  Proof.
   intros Hloss k.
   assert (forall (n:nat) (m:Mem.t k), 
    E.eval_expr variant m = n -> (mu ([[ [while b do c] ]] E m)) (fone _) == 1%U).
   induction n using lt_wf_ind; intros.
   rewrite deno_while_elim, deno_cond_elim.
   case_eq (E.eval_expr b m); intros Heq; [ | rewrite deno_nil_elim; trivial].
   rewrite deno_app_elim, <- (Hloss k m).
   apply range_eq with (1:=Hvar m Heq).
   intros m' Hlt; apply (H (E.eval_expr variant m')); trivial.
   rewrite <- H0; unfold EP in Hlt; simpl in Hlt; unfold O.eval_op in Hlt.
   apply leb_complete in Hlt; omega.
   intros m; apply (H (E.eval_expr variant m) m (eq_refl _)).
  Qed.

  Lemma deno_bounded_while_elim: forall k n (m:Mem.t k) f,
   (forall m':Mem.t k, E.eval_expr variant m' = 0 -> E.eval_expr b m' = false) ->
   E.eval_expr variant m <= n ->
   mu ([[ [while b do c] ]] E m) f == mu ([[ unroll_while b c n ]] E m) f.
  Proof.
   induction n using lt_wf_ind; induction n.
   (* base case *)
   intros m f Hb Hm.
   rewrite (while_false_elim _ _ _ _ _ (Hb _ (eq_sym (le_n_0_eq _ Hm)))).
   rewrite (unroll_while_false_elim _ _ _ _ _ _ (Hb _ (eq_sym (le_n_0_eq _ Hm)))).
   trivial.
   (* inductive case *)
   intros m f Hb Hn'.
   unfold unroll_while; fold (unroll_while b c n).
   rewrite deno_while_elim.
   repeat rewrite deno_cond_elim; case_eq (E.eval_expr b m); intro Heq.
   repeat rewrite deno_app_elim.
   apply range_eq with (1:=Hvar _ Heq).
   intros m' Hm'; apply H; auto.
   generalize Hn' Hm'; clear Hn' Hm'; unfold EP; rewrite <- eval_lt.
   change (E.eval_expr (E.eval_expr variant m) m') with (E.eval_expr variant m).
   omega.
   trivial.
  Qed.

 End BOUNDED_LOOP.
 (******************************)


 (** TODO: see if this generalization can replace the existing rule for 
    random assignments in BaseProp.v *)
 Definition permut_support t1 t2
  (f:forall k, Mem.t k -> Mem.t k -> T.interp k t2 -> T.interp k t1) 
  (d1:E.support t1) (d2:E.support t2) : mem_rel :=
  fun k (m1 m2:Mem.t k) =>
   PermutP (fun v1 v2 => v1 = f k m1 m2 v2) 
   (E.eval_support d1 m1) (E.eval_support d2 m2).

 Lemma sum_dom_permut : forall (B1 B2 : Type) (def1:B1) (def2:B2) 
  (dom1:list B1) (dom2:list B2) (f1:B1->U) (f2:B2->U),
  PermutP (fun x1 x2 => f1 x1 == f2 x2) dom1 dom2 ->
  sum_dom def1 dom1 f1 == sum_dom def2 dom2 f2.
 Proof.
  intros; repeat rewrite sum_dom_finite.
  apply finite_sum_Perm.
  rewrite (PermutP_length H).
  eapply PermutP_weaken  with (2:=H).
  intros a b _ _ Heq; rewrite Heq; trivial.
 Qed.
 
 Lemma equiv_random_permut : forall (Q:mem_rel) E1 E2 t1 t2 
  (x1:Var.var t1) (x2:Var.var t2)
  (f:forall k, Mem.t k -> Mem.t k -> T.interp k t2 -> T.interp k t1) 
  (d1:E.support t1) (d2:E.support t2),
  equiv 
  ((permut_support f d1 d2) /-\ 
   (fun k m1 m2 => forall v, 
    In v (E.eval_support d2 m2) -> 
    Q k (m1{!x1 <-- f k m1 m2 v!}) (m2{!x2 <-- v!})))
  E1 [x1 <$- d1] 
  E2 [x2 <$- d2] 
  Q.
 Proof.
  unfold equiv; intros.
  exists (fun m1 m2 =>
   Mlet ([[ [x2 <$- d2] ]] E2 m2)  (fun m => 
    Munit (m1{! x1 <-- f k m1 m2 (m x2) !}, m))).
  intros m1 m2 [H H0]; constructor; intros.
  rewrite Mlet_simpl, deno_random_elim, deno_random_elim.
  change (fun x0:T.interp k t2 =>
   mu (Munit (m1 {!x1 <-- f k m1 m2 ((m2{!x2 <-- x0!}) x2)!}, m2{!x2 <-- x0!}))
   (fun x => f0 (fst x))) 
   with
    (fun x0 => f0 (m1{!x1 <-- f k m1 m2 (m2{!x2 <-- x0!} x2)!})).
  symmetry.
  refine (@sum_dom_permut (T.interp k t1) (T.interp k t2)
   (T.default k t1) (T.default k t2)
   (E.eval_support d1 m1) (E.eval_support d2 m2) 
   (fun x0 => f0 (m1{!x1 <-- x0!}))
   (fun x0 => f0 (m1{!x1 <-- f k m1 m2 (m2{!x2 <-- x0!} x2)!})) _).
  red in H.
  generalize (E.eval_support d1 m1) (E.eval_support d2 m2) H; clear H H0.
  induction 1; constructor; subst; trivial.
  rewrite Mem.get_upd_same; trivial.
  rewrite Mlet_simpl, deno_random_elim, deno_random_elim; trivial.
  rewrite deno_random.
  unfold range; intros.
  repeat rewrite Mlet_simpl.
  change (0 == sum_dom (T.default k t2) (E.eval_support d2 m2)
   (fun x => f0 (m1{!x1 <-- f k m1 m2 (m2{!x2 <-- x!} x2)!}, m2{!x2 <-- x!}))).
  rewrite sum_dom_finite.
  generalize (E.eval_support d2 m2) 
   ([1/]1+pred (length (E.eval_support d2 m2))) H0.
  induction l; simpl; intros; trivial.
  rewrite <- IHl; auto.
  rewrite <- H1; auto.
  red; simpl; mem_upd_simpl; auto.
 Qed.

 
 (** TODO: Move to BaseDef.v *)
 Lemma finite_sum_notIn2 : forall (A:Type) (f:A -> U) l,
  (forall x, In x l -> f x == 0) ->
  finite_sum f l == 0.
 Proof.
  induction l; simpl; intros; [trivial | ].
  rewrite H; firstorder.
 Qed.

 Lemma finite_sum_In2 : forall (A:Type) (f:A -> U) l (v : U),
  (forall x, In x l -> f x == v) ->
  finite_sum f l == (length l) */ v.
 Proof.
  induction l; simpl; trivial; intros.
  rewrite IHl; auto.
  rewrite H; auto.
  destruct (length l); auto.
 Qed.

 Lemma finite_sum_le : forall (A:Type) (f1 f2:A -o> U) l,
  (forall x, In x l -> (f1 x <= f2 x)%tord) ->
  (finite_sum f1 l <= finite_sum f2 l)%tord.
 Proof.
  induction l; simpl; trivial; intros.
  apply Uplus_le_compat; auto.
 Qed.
 
 Lemma finite_sum_eq : forall (A:Type) (f1 f2 : A-o>U) l,
  (forall x, In x l -> f1 x == f2 x) ->
  finite_sum f1 l == finite_sum f2 l.
 Proof.
  induction l; simpl; trivial; intros.
  apply Uplus_eq_compat; auto.
 Qed.
 
 Lemma finite_sum_mult : forall A f v (l:list A),
  finite_sum (fun a => f a */ v) l == 
  fold_right (fun a r => f a + r) 0%nat l */ v.
 Proof.
  induction l; simpl; intros; auto.
  rewrite IHl.
  rewrite <- plus_Nmult_distr; auto.
 Qed.


 (** TODO: suggest to add to ALEA *)
 Lemma fplus_fzero_r: forall (A:Type) (f:A -o> U), fplus f (fzero _) == f.
 Proof. 
  intros; unfold fplus.  
  refine (ford_eq_intro _); auto.
 Qed.

 Lemma fplus_fzero_l: forall (A:Type) (f:A -o> U), fplus (fzero _) f == f.
 Proof. 
  intros; unfold fplus.  
  refine (ford_eq_intro _); auto.
 Qed.

 (** TODO: Move to BaseProp.v *)
 Lemma req_mem_PER: forall (X:Vset.t) (k: nat), @PER (Mem.t k) (@req_mem k X).
 Proof.
  intros X k; constructor.
  intros m1 m2; apply req_mem_sym.
  intros m1 m2 m3; apply req_mem_trans.
 Qed.

 Lemma req_mem_update' : forall k (X:Vset.t) (m m':Mem.t k) 
  (t:T.type) (d:Var.var t) (v1 v2:T.interp k (Var.btype d)),
  v1 = v2 ->
  m =={ X}m' -> 
  m {!d <-- v1!} =={Vset.add d X}m' {!d <-- v2!}.
 Proof.
  intros; subst; apply req_mem_update; trivial.
 Qed.


 Ltac slossless_tac := 
  repeat apply slossless_cons; 
    (apply slossless_assign; apply lossless_assign) ||
     (apply slossless_random; apply lossless_random) || 
      (apply slossless_nil; apply lossless_nil) || 
       (apply slossless_cond; slossless_tac) ||
        (apply slossless_while; [ | slossless_tac ]) ||
         apply slossless_call_adv || idtac.

 Ltac elim_assign := 
  rewrite (@deno_cons_elim _ _ (_ <- _)), Mlet_simpl, deno_assign_elim.
 
 Ltac elim_cond b m := let H := fresh "Hguard" in
  repeat (rewrite (@deno_cons_elim _ _ (If _ then _ else _)), 
   Mlet_simpl, (@deno_cond_elim _ _ b _ _ m));
  case_eq (@E.eval_expr _ T.Bool b m); intro H.

 Ltac expr_simpl := 
  unfold EP1, EP2, notR, andR, orR, impR, E.eval_expr; simpl; 
   unfold O.eval_op; simpl; mem_upd_simpl.


 (** TODO: Move to BaseDef.v *)
 Lemma range_strengthen : forall A (d:Distr A) (P Q:A -o> boolO),
  mu d (fone _) == 1%U ->
  range P d -> 
  range Q d ->
  range (P [&&] Q) d.
 Proof.
  intros; apply mu_range.
  rewrite <- (mu_range_strenghten _ Q H0).
  transitivity (mu d (fone _)); [ | trivial].
  apply range_mu; trivial. 
 Qed.

 Lemma equiv_strengthen_range: forall E c P (Q:mem_rel) 
  (R:forall k, Mem.t k -o> boolO),
  decMR Q ->
  lossless E c ->
  (forall k (m:Mem.t k), range (@R k) ([[c]] E m))  ->
  equiv P E c E c Q ->
  equiv P E c E c (Q /-\ (fun k (m1 _:Mem.t k) => R _ m1)).
 Proof.
  unfold equiv; intros.
  destruct (H1 k) as [d Hd]; clear H1.
  exists d; intros; constructor.
  apply (l_fst (Hd m1 m2 H1)).
  apply (l_snd (Hd m1 m2 H1)).
  apply range_weaken with 
   (P1:=fun v => 
    ((fun xy => if @X k (fst xy) (snd xy) then true else false) [&&] 
     (fun xy => R k (fst xy))) v = true).
  unfold prodP, andP; intros; rewrite andb_true_iff in H2; destruct H2.
  split. 
  destruct (X k (fst x) (snd x)); [trivial | discriminate].
  trivial.
  apply range_strengthen.
  transitivity (mu (d m1 m2) (fun xy => fone _ (fst xy)));
   [trivial | rewrite (l_fst (Hd m1 m2 H1)); apply H].
  apply range_weaken with (2:=l_range (Hd m1 m2 H1)).
  intros (m1',m2'); unfold prodP, fst, snd.
  destruct (X k m1' m2'); [trivial | intro; tauto].
  apply mu_range.
  rewrite (l_fst (Hd m1 m2 H1) (fun m => if R k m then 1%U else D0)).
  rewrite (range_mu _ (H0 _ m1) ).
  apply H.
 Qed.

 Lemma equiv_inv_Modify : forall (inv:mem_rel) (X1 X2 M1 M2:Vset.t) 
  (P:mem_rel) (E1:env) (c1:cmd) (E2:env) (c2:cmd) (Q:mem_rel) ,
  depend_only_rel inv X1 X2 ->
  Modify E1 M1 c1 ->
  Modify E2 M2 c2 ->
  (forall k (m1 m2 m1' m2':Mem.t k),
   P k m1 m2 -> Q k m1' m2' -> Q k (m1{!M1 <<- m1'!}) (m2{!M2 <<- m2'!})) ->  
  Vset.disjoint X1 M1 -> 
  Vset.disjoint X2 M2 -> 
  equiv P E1 c1 E2 c2 (Q /-\ trueR) ->
  equiv (P /-\ inv) E1 c1 E2 c2 (Q /-\ inv).
 Proof. 
  intros; intros k.
  destruct (H5 k) as [d Hd].
  exists (fun m1 m2 => 
   Mlet (d m1 m2) (fun mm => Munit (m1{! M1 <<- fst mm !}, m2{! M2 <<- snd mm!}))).
  intros.
  destruct H6 as [Hreq Hinv].
  destruct (Hd m1 m2 Hreq); clear Hd.
  constructor; intros.

  rewrite (Modify_deno_elim H0).
  apply (l_fst (fun m' => f (m1{!M1 <<- m'!}))). 

  rewrite (Modify_deno_elim H1).
  apply (l_snd (fun m' => f (m2{!M2 <<- m'!}))). 

  apply (range_Mlet _ l_range).
  unfold prodP, andR; intros (m1',m2') (H6,_) f Hf'.
  simpl; unfold fst, snd in *.
  apply Hf'; simpl; split; auto.
    
  apply H with (3:=Hinv).
  apply req_mem_sym; apply req_mem_update_disjoint; trivial.
  apply req_mem_sym; apply req_mem_update_disjoint; trivial.
 Qed.
 (****************************)
 

 Lemma rtriple_refl_zero: forall (E:env) c k, 
  @rtriple k E E c c (fzero _).
 Proof.
  intros E c k m f; apply Oeq_le; apply Uabs_diff_zero.
  apply equiv_deno with Meq Meq.
  apply equiv_eq_mem.
  intros m1 m2 Hm; rewrite Hm; trivial.
  trivial.
 Qed.

 Lemma prg_SD_seq_Meq: forall (P Q:mem_rel) E1 E2 (c1 c2 c1' c2':cmd) 
  (ep ep':nat -o> U),
  prg_SD P   E1 c1  E2 c2 Meq ep ->
  prg_SD Meq E1 c1' E2 c2' Q ep' ->
  prg_SD P   E1 (c1++c1') E2 (c2++c2') Q (fplus ep ep').
 Proof.
  unfold prg_SD, fplus; intros.
  repeat rewrite deno_app_elim.
  rewrite (@Uabs_diff_triangle_ineq _ _ 
   (mu ([[c1]] E1 m1) (fun m' => mu ([[c2']] E2 m') g))).
  rewrite (Uplus_sym (ep k)); apply Uplus_le_compat.
  rewrite Uabs_diff_mu_compat, <-(mu_cte_le ([[c1]] E1 m1) (ep' k)).
  apply equiv_deno_le with Meq Meq; trivial.
  apply equiv_eq_mem.
  unfold fabs_diff, fcte; intros; apply H0; trivial.
  apply H; trivial.
  intros; apply equiv_deno with Meq Meq; trivial.
  apply equiv_eq_mem.
  intros; rewrite H4; trivial.
 Qed.

 Lemma prg_SD_Meq_pre_weaken: forall (P Q:mem_rel) E1 E2 (c1 c2:cmd)
  (ep:nat -o> U),
  prg_SD Meq E1 c1 E2 c2 Q ep ->
  equiv  Meq E1 c1 E1 c1 Q ->
  equiv  P   E2 c2 E2 c2 Q ->
  symMR Q ->
  prg_SD P   E1 c1 E2 c2 Q ep.
 Proof.
  unfold prg_SD; intros.
  match goal with 
   |- (Uabs_diff ?x ?y <= _)%tord =>
    rewrite (@Uabs_diff_triangle_ineq x y (mu ([[c1]] E1 m1) g)),
     (@Uabs_diff_triangle_ineq (mu ([[c1]] E1 m1) g) y (mu ([[c2]] E2 m1) f))
  end.
  match goal with 
   |- ( (?x + (?y + ?z))%U <= _)%tord  => 
    assert ((x==0%U)%tord); [ | assert ((z==0%U)%tord) ] 
  end. 
  rewrite Uabs_diff_zero; apply equiv_deno with Meq Q; trivial.
  rewrite Uabs_diff_zero; apply equiv_deno with P Q; trivial.
  rewrite H5, H6; repeat Usimpl; apply H; trivial.
  auto.
  intros m1' m2' H'; symmetry; apply (H3 _ _ (proj2 H2 _ _ _ H')).
 Qed.


 (** Rule to move a piece of code outside of a loop *)
 Section WHILE_HOIST.
 
  Variable E1 E2 : env.
  Variables c1 c2 c1' c2' : cmd.
  Variables b1 b2 : E.expr T.Bool.
  Variables I P Q : mem_rel.

  Hypothesis H_guards: forall k (m1 m2:Mem.t k),
   (I /-\ P) _ m1 m2 ->
   E.eval_expr b1 m1 = E.eval_expr b2 m2.
  
  Hypothesis H_c1_c2: equiv 
   (I /-\ EP1 b1 /-\ EP2 b2) 
   E1 c1 
   E2 c2
   (I /-\ P).
  
  Hypothesis H_c1'_c2': equiv 
   (I /-\ P /-\ ~- EP1 b1 /-\ ~- EP2 b2) 
   E1 c1' 
   E2 c2'
   (I /-\ Q /-\ ~- EP1 b1 /-\ ~- EP2 b2).

  Lemma loop_hoist: equiv 
   (I /-\ EP1 b1 /-\ EP2 b2) 
   E1 ([ while b1 do c1 ] ++ c1')
   E2 ([ while b2 do c2 ] ++ c2') 
   (I /-\ Q /-\ ~-EP1 b1 /-\ ~-EP2 b2).
  Proof.
   apply equiv_trans_eq_mem_r with trueR E2  
    ( [If b2 _then (c2 ++ [while b2 do c2])] ++ c2'); 
    [ rewrite proj1_MR; apply equiv_eq_sem; intros; apply eq_distr_intro;
     intro f; repeat rewrite deno_app_elim; apply eq_distr_elim;
      apply eq_distr_intro;  apply deno_while_elim | | 
       unfold trueR; intros k m1 _ _; trivial ].
   apply equiv_trans_eq_mem_l with trueR E1  
    ( [If b1 _then (c1 ++ [while b1 do c1])] ++ c1'); 
    [ rewrite proj1_MR; apply equiv_eq_sem; intros; apply eq_distr_intro;
     intro f; repeat rewrite deno_app_elim; apply eq_distr_elim;
      apply eq_distr_intro;  apply deno_while_elim | | 
       unfold trueR; intros k m1 _ _; trivial ].
   apply equiv_app with (Q:= (I /-\ P) /-\ ~- EP1 b1 /-\ ~- EP2 b2)
    (c1:= [If b1 _then c1 ++ [while b1 do c1] ] ) (c2:=c1') 
    (c3:= [If b2 _then c2 ++ [while b2 do c2] ]) (c4:=c2').
   apply equiv_cond.
   apply equiv_app with (I /-\ P).
   rewrite proj1_MR; assumption.
   apply equiv_while.
   assumption.
   apply equiv_strengthen with (2:=H_c1_c2).
   intros k m1 m2 ( (H1,_),H2); split; assumption.
   apply equiv_False; unfold notR; intros k m1 m2 ((_,(?,_)),(?,_)); tauto.
   intros k m1 m2  (_,(H1,H2)); rewrite H1, H2; trivial.
   rewrite andR_assoc; assumption.
  Qed.

 End WHILE_HOIST.


 Definition distr_cond (A: Type) (d:Distr A) (P:A -o> boolO) : Distr A.
  intros A' d P.
  apply (distr_div (mu d (charfun P)) (drestr d P)).
  rewrite mu_drestr; trivial.
 Defined.
 
 Lemma distr_cond_simpl: forall (A: Type) (d:Distr A) (P: A -o> boolO) f,
  mu (distr_cond d P) f == (mu d (restr P f)) / (mu d (charfun P)).
 Proof.
  intros; unfold distr_cond, distr_div.
  rewrite (Mdiv_simpl ((mu d) (charfun P)) (mu (drestr d P))).
  apply Udiv_eq_compat_left.
  apply mu_drestr.
 Qed.


 (**********************  Sampling Facts  *********************)

 Section PERMUTATION_FACTS.

  Open Scope nat_scope.

  Definition minus_mod (x m k:nat) :=
   match le_lt_dec m x with
    | left _ => x - m
    | _ => k - m + x
   end.

  Definition minus_mod_inv (k n y:nat) :=
   match le_lt_dec y n with
    | left _ => n - y
    | _ => k + n - y
   end.

  Lemma minus_mod_bound : forall (m n k:nat),
   m < k ->
   minus_mod m n k < k.
  Proof.
   intros m n k Hm.
   unfold minus_mod.
   case (le_lt_dec n m); intro H; omega.
  Qed.

  Lemma minus_mod_inv_bound : forall (m n k:nat),
   m < k ->
   minus_mod_inv k m n < k.
  Proof.
   intros m n k Hm.
   unfold minus_mod_inv.
   case (le_lt_dec n m); intro H; omega.
  Qed.

  Lemma pow_minus_mod : forall k (a:G.t k) m n,
   n <= G.o k ->
   G.pow a (minus_mod m n (G.o k)) = G.mul (G.pow a m) (G.inv (G.pow a n)).
  Proof.
   intros.
   unfold minus_mod.
   case (le_lt_dec n m); intro H'.
   (* case [n <= m] *)
   apply G_Prop.mul_cancel_l with (G.pow a n).
   rewrite G_Prop.mul_pow_plus, <-(le_plus_minus _ _ H').
   rewrite (G.mul_comm (G.pow a m) _), G.mul_assoc, G.inv_spec.
   rewrite G.mul_comm, G.mul_0_r; trivial.

   (* case [m < n] *)
   apply G_Prop.mul_cancel_r with (G.pow a n).
   rewrite <-G.mul_assoc, (G.mul_comm (G.inv _) _), G.inv_spec, G.mul_0_r.
   rewrite G_Prop.mul_pow_plus. 
   rewrite (G_Prop.pow_periodic a m 1), mult_1_l.
   replace (G.o k - n + m + n)  with (m + G.o k); trivial.
   rewrite (plus_comm _ n), plus_assoc, <-le_plus_minus;
    [ apply plus_comm | assumption ].
  Qed.


  Lemma sampling_fact1: forall (E:env) (x s:Var.var (T.User G)) (z:Var.var T.Nat),
   Var.mkV x <> Var.mkV s -> 
   EqObs 
   (Vset.singleton s)
   E [z <$- Zn; x <- s |-| z |*| gen]
   E [x <$- G; z <- log (s|-|x)]
   (Vset.add x (Vset.add z (Vset.singleton s))).
  Proof.
   intros.
   apply EqObs_sym.
   apply equiv_cons with (fun k (m1 m2:Mem.t k) => 
    E.eval_expr (s |-| z |*| gen) m2 = m1 x /\
    E.eval_expr (log (s |-| x)) m1 = m2 z /\ 
    m1 s = m2 s).
   eapply equiv_strengthen; [ | apply equiv_random_permut with 
    (f:=fun k (m1 m2:Mem.t k) (v:T.interp k T.Nat ) => 
     G.mul (m2 s) (G.inv (G.pow (G.g k) v))) ].
   intros; split.
   (* Permutation *)
   unfold permut_support; simpl E.eval_support; unfold Zn_support, G_support.
   apply PermutP_sym; apply PermutP_map.
   rewrite (G.log_spec (m2 s)); generalize (G.log (m2 s)), (G.log_lt (m2 s)).
   intros n Hn.
   apply PermutP_sym. 
   apply PermutP_weaken with (fun b a => b = minus_mod n a (G.o k)).
   intros; subst.
   apply In_seq_le in H2; rewrite plus_0_r in H2; destruct H2 as [_ H2].
   apply (pow_minus_mod _ _ (lt_le_weak _ _ H2)).

   apply PermutP_NoDup with (f_inv:=minus_mod_inv (G.o k) n).
   apply NoDup_seq.
   apply NoDup_seq.
   intros; unfold minus_mod, minus_mod_inv; apply In_seq_le in H1.
   destruct (le_lt_dec x0 n).
   destruct (le_lt_dec (n - x0) n); omega.
   destruct (le_lt_dec (G.o k + n - x0) n); omega.
   intros; unfold minus_mod, minus_mod_inv; apply In_seq_le in H1.
   destruct (le_lt_dec x0 n).
   destruct (le_lt_dec (n-x0) n); omega.
   destruct (le_lt_dec (G.o k - x0 + n) n); omega.
   intros.
   apply In_seq_le in H1; rewrite plus_0_r in H1; destruct H1 as [_ H1].
   apply le_In_seq; split; [ apply le_0_n | rewrite plus_0_r ].
   apply (minus_mod_bound _ Hn).
   intros.
   apply In_seq_le in H1; rewrite plus_0_r in H1; destruct H1 as [_ H1].
   apply le_In_seq; split; [ apply le_0_n | rewrite plus_0_r ].
   apply (minus_mod_inv_bound _ Hn).
  
   (* Postcondition *)
   intros v Hv; repeat split; expr_simpl.
   rewrite Mem.get_upd_diff; [ | trivial].
   rewrite G_Prop.inv_mul, G_Prop.inv_inv, 
    <-(G.mul_comm (G.inv (m2 s))), G.mul_assoc, (H0 _ s), 
    G.inv_spec, G.mul_comm, G.mul_0_r, G_Prop.log_pow; trivial.
   apply In_seq_le in Hv; rewrite plus_0_r in Hv; destruct Hv; trivial.
   apply Vset.singleton_correct; trivial.
   repeat rewrite Mem.get_upd_diff; [ | discriminate | trivial ].
   refine (H0 (T.User G) s _); apply Vset.singleton_correct; trivial.

   eapply equiv_strengthen ; [ | apply equiv_assign ].
   unfold upd_para; intros k m1 m2 [H1 [H2 H3] ] t v Hv.
   Vset_mem_inversion Hv; subst; mem_upd_simpl.
   symmetry; trivial.
   rewrite Mem.get_upd_diff; trivial.
  Qed.

  Lemma sampling_fact2: forall (E:env) (x s :Var.var (T.User G)) (z:Var.var T.Nat),
   Var.mkV x <> Var.mkV s -> 
   EqObs 
   (Vset.singleton s)
   E [z <$- Zn; x <- s |+| z |*| gen]
   E [x <$- G; z <- log (x |-| s)]
   (Vset.add x (Vset.add z (Vset.singleton s))).
  Proof.
   intros.
   apply EqObs_sym.
   apply equiv_cons with (fun k (m1 m2:Mem.t k) => 
    E.eval_expr (s |+| z |*| gen) m2 = m1 x /\
    E.eval_expr (log (x |-| s)) m1 = m2 z /\ 
    m1 s = m2 s).
   eapply equiv_strengthen; [ | apply equiv_random_permut with 
    (f:=fun k (m1 m2:Mem.t k) (v:T.interp k T.Nat ) => 
     G.mul (m2 s) (G.pow (G.g k) v)) ].
   intros; split.
       (* Permutation *)
   unfold permut_support; simpl E.eval_support; unfold Zn_support, G_support.
   apply PermutP_sym; apply PermutP_map.
   rewrite (G.log_spec (m2 s)); generalize (G.log (m2 s)), (G.log_lt (m2 s)); intros n Hn.
   apply PermutP_weaken with (fun a b => a = minus_mod b n (G.o k)).
   intros; subst.
   apply In_seq_le in H2; rewrite plus_0_r in H2; destruct H2 as [_ H2].
   rewrite (pow_minus_mod _ _ (lt_le_weak _ _ Hn)).
   rewrite (G.mul_comm  (G.pow (G.g k) b)), G.mul_assoc, G.inv_spec,
    G.mul_comm, G.mul_0_r; trivial.

   apply PermutP_NoDup with (f_inv := fun b =>
    if le_lt_dec ((G.o k) - n) b then b - ((G.o k) - n) else b + n).
   apply NoDup_seq.
   apply NoDup_seq.
   intros; unfold minus_mod, minus_mod_inv; apply In_seq_le in H1.
   destruct (le_lt_dec (G.o k - n) x0).
   destruct (le_lt_dec n (x0 - (G.o k - n))). 
   elimtype False; omega.
   omega.
   destruct (le_lt_dec n (x0 + n)); omega.
   intros; unfold minus_mod, minus_mod_inv; apply In_seq_le in H1.
   destruct (le_lt_dec n x0).
   destruct (le_lt_dec (G.o k - n) (x0 - n)); omega.
   destruct (le_lt_dec (G.o k - n) (G.o k - n + x0)); omega.
   intros.
   apply In_seq_le in H1; rewrite plus_0_r in H1; destruct H1 as [_ H1].
   apply le_In_seq; split; [ apply le_0_n | rewrite plus_0_r ].
   apply (minus_mod_bound _ H1).
   intros.
   apply In_seq_le in H1; rewrite plus_0_r in H1; destruct H1 as [_ H1].
   apply le_In_seq; split; [ apply le_0_n | rewrite plus_0_r ].
   destruct (le_lt_dec (G.o k - n) x0); omega.
       (* Poscondition *)
   intros v Hv; repeat split; expr_simpl.
   rewrite Mem.get_upd_diff; [ | trivial].
   rewrite (G.mul_comm (m2 s)), <-G.mul_assoc, (H0 _ s), 
    G.inv_spec, G.mul_0_r, G_Prop.log_pow; trivial.
   apply In_seq_le in Hv; rewrite plus_0_r in Hv; destruct Hv; trivial.
   apply Vset.singleton_correct; trivial.
   repeat rewrite Mem.get_upd_diff; [ | discriminate | trivial ].
   refine (H0 (T.User G) s _); apply Vset.singleton_correct; trivial.

   eapply equiv_strengthen ; [ | apply equiv_assign ].
   unfold upd_para; intros k m1 m2 [H1 [H2 H3] ] t v Hv.
   Vset_mem_inversion Hv; subst; mem_upd_simpl.
   symmetry; trivial.
   rewrite Mem.get_upd_diff; trivial.
  Qed.
 
 End PERMUTATION_FACTS.

 Close Scope nat_scope.


 (* ********  Variable and procedure declarations  ********** *)  

 Notation sIf     := (Var.Lvar (T.User G) 1).
 Notation n       := (Var.Lvar (T.Nat) 2).
 Notation len     := (Var.Lvar (T.Nat) 3).
 Notation l       := (Var.Lvar (T.List (T.User A)) 4).
 Notation r_v2    := (Var.Lvar (T.User G) 5).
 Notation ret_v2  := (Var.Lvar (T.Option (T.User A)) 6).
 Notation n'      := (Var.Lvar T.Nat 7).
 Notation ns      := (Var.Lvar (T.Pair T.Nat (T.User A)) 8).
 Notation n_v2    := (Var.Lvar T.Nat 9).
 Notation s       := (Var.Lvar (T.User A) 10).
 Notation a       := (Var.Lvar (T.Option (T.User A)) 11).
 Notation x       := (Var.Lvar (T.User G) 12).
 Notation a'      := (Var.Lvar (T.User A) 13).
 Notation r''     := (Var.Lvar (T.User G) 14).
 Notation ret'    := (Var.Lvar (T.Option (T.Pair (T.User A) (T.Nat))) 15).
 Notation i       := (Var.Lvar T.Nat 16).
 Notation z       := (Var.Lvar T.Nat 17).
 Notation r       := (Var.Lvar (T.User G) 18).
 Notation ret''   := (Var.Lvar (T.Option (T.Pair (T.User A) (T.Nat))) 19).
 Notation m'      := (Var.Lvar Msg 20). 
 Notation L       := (Var.Gvar (T.List (T.Pair Msg (T.Pair 
  (T.Option (T.Pair (T.User A) T.Nat)) (T.User G)))) 21).
 Notation b       := (Var.Lvar T.Bool 22).
 Notation b'      := (Var.Lvar T.Bool 23).
 Notation bad     := (Var.Gvar T.Bool 24).
 Notation Ll      := (Var.Gvar 
   (T.List (T.Pair Msg (T.Option (T.Pair (T.User Sem.A) Msg)))) 25).
 Notation Lr      := (Var.Gvar (T.List (T.Pair Msg (T.User G))) 26).
 Notation ml      := (Var.Lvar Msg 27).
 Notation mr      := (Var.Lvar Msg 28).
 Notation retlr   := (Var.Lvar 
  (T.Pair (T.Option (T.Pair (T.User A) T.Nat)) (T.User G)) 29).
 Notation retl := (Var.Lvar (T.Option (T.Pair (T.User A) T.Nat)) 30).
 Notation retl':= (Var.Lvar (T.Option (T.Pair (T.User A) T.Nat)) 31).
 Notation retr := (Var.Lvar (T.User G) 32).
 

 Notation Invf_v1 := (Proc.mkP 1 (T.User G :: nil) (T.Pair T.Nat (T.User A))).
 Notation Invf_v2 := (Proc.mkP 2 (T.User G :: nil) (T.Option (T.User A))).
 Notation InvF    := (Proc.mkP 3 (T.User G :: nil) 
  (T.Option (T.Pair (T.User A) T.Nat))).
 Notation H       := (Proc.mkP 4 (Msg:: nil) 
  (T.Pair (T.Option (T.Pair (T.User A) T.Nat)) (T.User G))).
 Notation Hl      := (Proc.mkP 5 (Msg:: nil) (T.Option (T.Pair (T.User A) T.Nat))).
 Notation Hr      := (Proc.mkP 6 (Msg:: nil) (T.User G)).
 Notation A'      := (Proc.mkP 7 nil T.Bool).
 Notation A       := (Proc.mkP 8 nil T.Bool).

 Section THEOREM1.

 Variable E0 : env.
 
 (* ******************************  CLAIM 1  ****************************** *)
 (* Let [f:A -> G] be the Icart's function ([A] is the field --of size      *)
 (* [length (A.elems k)]-- and  [G] the elliptic curve --of order [G.o k]-- *)
 (* for some parameters [a] [b]. Then [f] is an (alpha,epsilon)-weak        *)
 (* encoding v2 with [alpha = 4|G|/|A|] and [epsilon = 0]                   *)
 (* *********************************************************************** *)
 
 (*  TODO: which parameters? *)
 Definition alpha k := (G.o k * ET.size, (length (A.elems k)))%nat .
 Definition epsilon := fzero nat.
 Definition one_over_alpha k := (snd (alpha k)) */ [1/]1+ pred (fst (alpha k)).


 Definition Invf_v1_params : var_decl (Proc.targs Invf_v1) := dcons _ sIf (dnil _).
 
 Definition Invf_v1_body :=
  [ 
   l <- finv_ sIf;
   len <- Elen l;
   n <$- [0..(len -! 1)]
  ].

 Definition Invf_v1_ret := (len | Enth {n, l} ).

 Definition Invf_v2_params : var_decl (Proc.targs Invf_v2) := 
  dcons _ r_v2 (dnil _).

 Definition Invf_v2_body :=
  [ 
   n' <$- [0..B-!1];
   ns <c- Invf_v1 with {r_v2};
   n_v2 <- Efst ns;
   s <- Esnd ns;
   If n' <! (B -! n_v2) then
    [ ret_v2 <- none _ ]
   else 
    [ ret_v2 <- some s ]
  ].
 
 Definition Invf_v2_ret := ret_v2.
    
 (* Environment containing info for [Invf_v1] and [Invf_v2] *)
 Definition E' := 
  let E_initial := E0 in
  let E_Invf_v1 := add_decl E_initial Invf_v1 Invf_v1_params (eq_refl true) Invf_v1_body Invf_v1_ret in
  let E_Invf_v2 := add_decl E_Invf_v1 Invf_v2 Invf_v2_params (eq_refl true) Invf_v2_body Invf_v2_ret in
   E_Invf_v2.

 (* Info for [Invf_v1] and [Invf_v2] *)
 Definition i_E'E' :=
  let i_empty   :=  empty_info E' E' in
  let i_Invf_v1 :=  add_refl_info_rm Invf_v1 Vset.empty Vset.empty i_empty in
  let i_Invf_v2 :=  add_refl_info_rm Invf_v2 Vset.empty Vset.empty i_Invf_v1 in
   i_Invf_v2.

 Definition pi' : PPT_info E' := 
  PPT_add_info (PPT_add_info (PPT_empty_info E') Invf_v1) Invf_v2.
  
 (* [Invf_v2] is PPT *)
 Lemma Invf_v2_is_PPT : PPT_proc E' Invf_v2.
 Proof.
  PPT_proc_tac pi'.
 Qed.

 Definition Invf_v2_in_rnd := [ r_v2 <$- G ] ++ Invf_v2_body.
    
 (* When given a random input, [Invf_v2] either fails or return 
    a preimage of its input. *)
 Lemma Invf_v2_is_partial_inverter: forall k (m:Mem.t k),
   range (EP k ((IsSome a) ==> (x =?= f_ (Proj a)))) 
   ([[ [x <$-G; a <c- Invf_v2 with {x} ] ]] E' m).
 Proof.
  intros.
  apply mu_range.
  assert (Hloss :  lossless E' [x <$-G; a <c- Invf_v2 with {x} ] ) by
    (apply is_lossless_correct with (refl2_info i_E'E'); apply eq_refl).
  rewrite <- (@Hloss _ m).
  apply equiv_deno with (kreq_mem Vset.empty) (req_mem_rel Vset.empty
    ((EP1 ((IsSome a) ==> (x =?= f_ (Proj a)))) /-\ (EP2 ((IsSome a) ==> (x =?= f_ (Proj a)))))). 
  sinline i_E'E' Invf_v2.
  sinline i_E'E' Invf_v1.

  ep; deadcode.
  eqobsrel_tail; simpl; unfold O.eval_op; simpl.
  red; intros.

  split.
  intros; auto.
  intros [H3 _].
  generalize (ET.finv_spec v (nth v1 (ET.finv_def v) (A.default k0))); intros.
  destruct H4.
  rewrite H4.
  rewrite G_eqb_refl; auto.
  
  destruct (ET.finv_def v).
  simpl in *.
  destruct H2; auto.
  subst.
  elim H3.
  destruct H1.
  subst.
  generalize (ET.size_not_0).
  destruct ET.size; intros.
  elimtype False; omega.
  auto.
  apply In_seq_le in H1.
  apply leb_correct.
  omega.  
  destruct H2.
  subst; simpl; auto.
  apply nth_In.
  apply In_seq_le in H2.
  omega.

  intros m1 m2 Hm.
  generalize Hm; unfold EP1, EP2, EP; simpl; unfold O.eval_op; simpl.
  red; intros; unfold req_mem_rel, andR in Hm0.
  destruct Hm0 as [ H1 [ H2 H3 ] ].
  rewrite H2; trivial; auto.
  auto.
 Qed.

 (* [Invf_v2] succeeds to invert a random element with probability 
    at least [1/alpha] *)
 Lemma Invf_v2_success_probability : forall k (m:Mem.t k),
  Pr E' [ x <$-G; a <c- Invf_v2 with {x} ] m (EP k (IsSome a)) ==
  one_over_alpha k.
 Proof.
  intros; symmetry.
  (* trans inlining/deadcode/ep *)
  transitivity (mu ([[ 
   [
     x <$-G;
     n' <$- [0..B -! 1];
     If (n') <! (B -! Elen (finv_ x))
     then [a <- none _]
     else 
      [ 
       n_v2 <$- [0..Elen (finv_ x) -! 1]; 
       a <- some Enth {n_v2, finv_ x } 
      ]
   ] ]] E' m) (charfun (EP k (IsSome a)))).
   
  (* simpl deno *)
  rewrite deno_cons_elim, Mlet_simpl.

  transitivity 
   (mu ([[ [x <$- G] ]] E' m) 
    (fun m => length (ET.finv_def (m x)) */ [1/]1+pred ET.size )).

  rewrite deno_random_elim, (sum_dom_finite (G.g k) (G_support k)).

  unfold G_support.
  rewrite map_length, seq_length.

  transitivity (finite_sum (fun a => 
   (length (ET.finv_def a)) */ [1/]1+pred(G.o k * ET.size)) (G_support k)).
  rewrite finite_sum_mult.
  unfold one_over_alpha, alpha; simpl.
  apply Nmult_eq_compat_right.
  apply fold_right_incl_eq with (f:=@ET.f_def k).
  apply ET.finv_NoDup.
  intros; apply ET.finv_spec.
  apply A.elems_NoDup.
  apply G_support_NoDup.
  trivial.
  apply A.elems_full.
  apply G_support_full.

  apply finite_sum_eq; intros.
  mem_upd_simpl.
  rewrite <- Nmult_Umult_assoc_right.

  destruct (G.o k).
  elim H.
  generalize ET.size_not_0.
  destruct ET.size; intros.
  exfalso; omega.
  repeat rewrite <- pred_Sn.
  rewrite Unth_prod; trivial.

  unfold Nmult_def.
  generalize (ET.size_spec x).
  destruct (ET.finv_def x); simpl; intros; auto.
  apply Unth_anti_mon; simpl.
  omega.

  apply mu_stable_eq.
  refine (ford_eq_intro _); intro m'.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  simpl RO.Sem.T.default.
  simpl E.eval_support.
  unfold O.eval_op.
  simpl RO.Sem.T.app_op.
  assert (0%nat :: seq 1 (ET.size - 1) = seq 0 ET.size).
  generalize ET.size_not_0; intros.
  destruct ET.size.
  elimtype False; omega.
  simpl.
  rewrite <- minus_n_O; trivial.
  rewrite H; clear H.

  transitivity (mu (sum_support 0%nat (seq 0 ET.size)) (fun x' => 
   if leb (x' + 1) (ET.size - length (ET.finv_def (m' x))) then 0%U else 1%U)).
  Opaque sum_dom.
  simpl; unfold O.eval_op; simpl.
  rewrite (sum_dom_finite 0%nat (seq 0%nat ET.size)).
  generalize (ET.size_spec (m' x)); intros.

  assert (ET.size = (ET.size - (length (ET.finv_def (m' x))) +
   (length (ET.finv_def (m' x))))%nat) by omega.

  rewrite H0 at 2.
  rewrite seq_append, finite_sum_app.
  match goal with [ |- _ == (?a + ?b)%U ] => assert (a == 0) end.
  apply finite_sum_notIn2.
  intros.
  apply In_seq_le in H1.
  rewrite leb_correct.
  Usimpl; trivial.
  omega.

  rewrite H1; clear H1; Usimpl.
  rewrite finite_sum_In2.
  rewrite seq_length.
  auto.
  intros.
  apply In_seq_le in H1.
  rewrite leb_correct_conv;[ | omega ].
  rewrite seq_length; auto.

 apply mu_stable_eq.
 refine (ford_eq_intro _); intro ms.
 rewrite deno_cond_elim.
 simpl E.eval_expr; unfold O.eval_op; simpl RO.Sem.T.app_op.
 mem_upd_simpl.
 case_eq (leb (ms + 1) (ET.size - length (ET.finv_def (m' x)))); intros; auto.
 rewrite deno_assign_elim; simpl.
 unfold charfun, restr, EP; simpl.
 unfold O.eval_op; simpl.
 mem_upd_simpl.
 rewrite deno_cons_elim.
 rewrite Mlet_simpl.
 rewrite deno_random_elim.
 simpl RO.Sem.T.default.
 simpl E.eval_support.
 unfold O.eval_op.
 simpl RO.Sem.T.app_op.

 transitivity ((mu (sum_support 0%nat
 (0%nat :: seq 1 (length (ET.finv_def ((m' {!n' <-- ms!}) x)) - 1))))
 (fun v => 1%U)).
 rewrite BaseDef.sum_support_lossless; auto.
 intro; discriminate.
 apply mu_stable_eq.
 refine (ford_eq_intro _); intro.
 rewrite deno_assign_elim.
 unfold charfun, restr, EP.
 simpl E.eval_expr; unfold O.eval_op; simpl RO.Sem.T.app_op.
 mem_upd_simpl.
 
 apply equiv_deno with (kreq_mem Vset.empty)  (kreq_mem {{ a }} ); auto.
 sinline i_E'E' Invf_v2.
 sinline i_E'E' Invf_v1.
 eqobs_hd.
 cp_test ((n') <! (B -! Elen (finv_ x))).
 deadcode.
 eqobs_in i_E'E'.
 alloc_l n_v2 n; ep; deadcode; eqobs_in i_E'E'.
 intros; unfold charfun, restr, EP.
 simpl; unfold O.eval_op; simpl.
 rewrite (H _ a); auto.
Qed.

Lemma finite_sum_full2:
  forall (A : Type) (v : A) (f : A -> U),
    forall l,
    (forall x : A, x <> v -> In x l -> f x == 0) ->
    In v l -> NoDup l -> finite_sum f l == f v.
Proof.
 induction l; simpl; intros; auto.
 elim H0.
 destruct H0; subst.
 rewrite finite_sum_notIn2; auto.
 intros; apply H; auto.
 inversion H1; subst.
 intro Heq; elim H4; subst; auto.
 rewrite H, IHl; auto.
 inversion H1; auto.
 inversion H1; subst.
 intro Heq; elim H4; subst; auto.
Qed.
  
 (* Given a random input, [Invf_v2]'s output distribution conditioned
    on non-failure is at distance [epsilon=0] from being random *) 
 Lemma Invf_v2_distance_from_random: forall k  (f g: Mem.t k -o> U),
  (forall m1 m2 : Mem.t k, kreq_mem {{a'}} m1 m2 -> f m1 == g m2) ->
  forall m1 m2,
  Uabs_diff 
  (mu (distr_cond ([[ [ x <$- G; a <c- Invf_v2 with {x}; a' <- Proj a ] ]] E' m1) (EP k (IsSome a))) f)
  (mu ([[ [ a' <$- A] ]] E' m2) g) <= epsilon k.
 Proof.
  Opaque deno.
  intros;unfold distr_cond;simpl.
  
  assert (mu (([[ [x <$-G; a <c- Invf_v2 with {x}; a' <- Proj a] ]]) E' m1)  (charfun (EP k (IsSome a))) == 
             one_over_alpha k).
  transitivity (mu (([[ [x <$-G; a <c- Invf_v2 with {x} ] ]]) E' m1)  (charfun (EP k (IsSome a)))).
  apply EqObs_deno with Vset.empty {{ a }}.
  deadcode i_E'E'.
  eqobs_in i_E'E'.
  intros.
  unfold charfun, restr, EP; simpl.
  unfold O.eval_op; simpl.
  rewrite (H0 _ a); auto.
  auto.
  apply Invf_v2_success_probability.

  assert (((mu (([[ [x <$-G; a <c- Invf_v2 with {x}; a' <- Proj a] ]]) E' m1))
     (fun x : Mem.t k =>
      (mu (if EP k (IsSome a) x then Munit x else distr0 (Mem.t k))) f)) == 
      (finite_sum (fun s' => f (m1{!a' <-- s'!}) * [1/]1+pred (ET.size * G.o k)) (A.elems k))).
  transitivity ((mu (([[ [
    x <$-G;
    n' <$- [0..B -! 1];
    n_v2 <$- [0..Elen (finv_ x) -! 1];
    If (n') <! (B -! Elen (finv_ x))
    then [a <- none _]
    else [a <- some Enth {n_v2, finv_ x } ]; a' <- Proj a ] ]]) E' m1)) 
  (fun x : Mem.t k => (mu (if EP k (IsSome a) x then Munit x else distr0 (Mem.t k))) g)).
  apply equiv_deno with (kreq_mem Vset.empty)  (kreq_mem {{ a, a' }} ); auto.
  sinline i_E'E' Invf_v2.
  sinline i_E'E' Invf_v1.
  alloc_l n n_v2; ep; deadcode.
  eqobs_hd.
  cp_test ((n') <! (B -! Elen (finv_ x))).
  deadcode.
  eqobs_in i_E'E'.
  alloc_r ret_v2 a; ep; deadcode; eqobs_in i_E'E'.
  intros; unfold charfun, restr, EP.
  simpl; unfold O.eval_op; simpl.
  rewrite (H1 _ a); auto.
  case (m3 a); simpl; intros; auto.
  apply H. 
  unfold kreq_mem in *.
  eapply req_mem_weaken; eauto; auto with set.
  
  transitivity ( mu ([[ [x <$- G;n' <$- [0..B -! 1]; n <$- [0..Elen (finv_ x) -! 1] ] ]] E' m1)
    (fun m' => 
      charfun (EP k (!(n' <! (B -! Elen finv_ x)))) m' * f (m1{!a' <-- E.eval_expr (Enth {n,finv_ x}) m'!}))).
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  apply mu_stable_eq;refine (ford_eq_intro _);intros r.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  apply mu_stable_eq;refine (ford_eq_intro _);intros n.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
  apply mu_stable_eq;refine (ford_eq_intro _);intros n'.
  rewrite deno_nil_elim.
  rewrite deno_cons_elim, Mlet_simpl.
  rewrite deno_cond_elim.
  unfold charfun, restr, EP.
  simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  case_eq (leb (n + 1) (ET.size - length (ET.finv_def r))); intros; simpl; try Usimpl.
  rewrite (deno_assign_elim E' a _ (((m1 {!x <-- r!}) {!RO.n' <-- n!}) {!n_v2 <-- n'!})).
  rewrite (deno_assign_elim E' a' _
    ((((m1 {!x <-- r!}) {!RO.n' <-- n!}) {!n_v2 <-- n'!}) {!a <-- E.eval_expr (E.Cnone (T.User Sem.A))
      (((m1 {!x <-- r!}) {!RO.n' <-- n!}) {!n_v2 <-- n'!})!})).
  mem_upd_simpl.
  rewrite (deno_assign_elim E' a _ (((m1 {!x <-- r!}) {!RO.n' <-- n!}) {!n_v2 <-- n'!})).
  rewrite (deno_assign_elim E' a' _  ((((m1 {!x <-- r!}) {!RO.n' <-- n!}) {!n_v2 <-- n'!}) {!a <--
    E.eval_expr (some Enth {n_v2, finv_ x}) (((m1 {!x <-- r!}) {!RO.n' <-- n!}) {!n_v2 <-- n'!})!})).
  mem_upd_simpl.
  unfold charfun, restr, EP, fone.
  simpl; unfold O.eval_op; simpl.
  mem_upd_simpl.
  Usimpl.
  symmetry.
  apply H.
  unfold kreq_mem in *.
  apply req_mem_update;apply req_mem_empty.

  set (F m' := (fun s' => 
    (charfun (EP k (n' <! B)) m') * (
    (charfun (EP k (!(n' <! (B -! Elen finv_ x)))) m'* f (m1{!a' <-- s'!}) * 
      charfun (T.i_eqb k (T.User Sem.A) s') (E.eval_expr (Enth {n,finv_ x}) m'))))).
  transitivity ( mu ([[ [x <$- G;n' <$- [0..B -! 1]; n <$- [0..Elen (finv_ x) -! 1] ] ]] E' m1)
      (fun m' => finite_sum (F m') (A.elems k))).
  rewrite (mu_range_restr (EP k (n' <! B))).
  apply mu_stable_eq;refine (ford_eq_intro _);intros m'.
  rewrite (@finite_sum_full _ (E.eval_expr (Enth {n, finv_ x}) m') (F m'));unfold F.
  unfold charfun at 4; unfold restr, fone.
  rewrite Ti_eqb_refl;auto.
  unfold charfun, restr.
  case (EP k (n' <! B) m'); Usimpl; auto.

  intros x Hdiff.
  unfold charfun at 3;unfold restr, fone.
  generalize (T.i_eqb_spec k (T.User Sem.A) x (E.eval_expr (Enth {n, finv_ RO.x}) m')).
  destruct (T.i_eqb k (T.User Sem.A) x (E.eval_expr (Enth {n, finv_ RO.x}) m'));intros.
  elim (Hdiff H1). auto.
  repeat Usimpl; auto.
  apply (@A.elems_full k). apply (@A.elems_NoDup k).
  rewrite deno_cons.
  apply range_Mlet with (fun _ => True).
  apply range_True.
  intros m' _.
  rewrite deno_cons.
  apply range_Mlet with (fun x : Mem.t k => EP k (n' <! B) x = true).
  unfold range; intros.
  rewrite deno_random_elim.
  simpl.
  rewrite (sum_dom_finite 0%nat).
  simpl; unfold O.eval_op; simpl.
  rewrite <- H1.
  rewrite finite_sum_notIn2.
  Usimpl; auto.
  intros.
  rewrite <- H1.
  Usimpl; auto.
  unfold EP; simpl; unfold O.eval_op; simpl.
  apply leb_correct.
  mem_upd_simpl; simpl.
  apply In_seq_le in H2; omega.
  unfold EP; simpl; unfold O.eval_op; simpl.
  apply leb_correct.
  mem_upd_simpl; simpl.
  apply ET.size_not_0.
  intros.
  unfold range; intros.
  rewrite deno_random_elim.
  transitivity ((mu
    (sum_support (RO.Sem.T.default k Msg)
      (E.eval_support [0..Elen (finv_ RO.x) -! 1] x))) (fcte _ 0)).
  rewrite mu_cte.
  Usimpl; auto.
  apply mu_stable_eq;refine (ford_eq_intro _);intros m''.
  apply H2.
  revert H1.
  unfold EP; simpl; unfold O.eval_op; simpl.  
  mem_upd_simpl.
  
  transitivity 
    (finite_sum (fun s' => mu
      (([[ [x <$-G; n' <$- [0..B -! 1]; n <$- [0..Elen (finv_ x) -! 1] ] ]]) E' m1)
      (fun m' => F m' s')) (A.elems k)).
  rewrite <- (@sigma_finite_sum _ (A.default k)).
  rewrite <- mu_sigma_eq.
  apply mu_stable_eq;refine (ford_eq_intro _);intros m'.
  unfold sigma_fun.
  rewrite sigma_finite_sum.
  trivial.
  intros m.
  unfold retract.
  intros.
  unfold F.
  Opaque T.i_eqb sigma.
  unfold charfun, restr, fone, EP; simpl; unfold O.eval_op; simpl.
  generalize (T.i_eqb_spec k (T.User Sem.A) (nth k0 (A.elems k) (A.default k))
    (nth (m n) (ET.finv_def (m x)) (A.default k))).  
  case(T.i_eqb k (T.User Sem.A) (nth k0 (A.elems k) (A.default k))
    (nth (m n) (ET.finv_def (m x)) (A.default k))); intros.
  Usimpl.
  case_eq (leb (m n' + 1) ET.size); intros; Usimpl; auto.
  match goal with |- _ <= [1-] (?x ?x') => 
    assert (forall k, (k <= k0)%nat -> x k == 0)
  end.
  induction k1; intros.
  rewrite sigma_0; trivial.
  rewrite sigma_S, IHk1;[ Usimpl | omega ].
  generalize (T.i_eqb_spec k (T.User Sem.A) (nth k1 (A.elems k) (A.default k))
    (nth (m n) (ET.finv_def (m x)) (A.default k))).  
  case(T.i_eqb k (T.User Sem.A) (nth k1 (A.elems k) (A.default k))
    (nth (m n) (ET.finv_def (m x)) (A.default k))); intros.
  case_eq (length (ET.finv_def (m x))); intros.
  rewrite <- minus_n_O.
  rewrite H3.
  simpl; repeat Usimpl; auto.
  
  assert (k1 = k0).
     rewrite <- H2 in H5.
     revert H5 H1 H4.
     clear.
     revert k0 k1.
     generalize (@A.elems_NoDup k).
     induction 1; intros; simpl in *.
     elimtype False; omega.
     destruct k1; destruct k0; trivial.
     elim H.
     subst; apply nth_In.
     omega.
     elim H.
     subst; apply nth_In.
     omega.
     rewrite (IHNoDup k0 k1); auto; omega.
     repeat Usimpl; trivial.
     elimtype False; omega.
     
  Usimpl; trivial.
  rewrite H4; auto; Usimpl; auto.
  repeat Usimpl; trivial.
 
  apply finite_sum_eq;intros s' Hin.
  unfold F.

  transitivity
    (f (m1 {!a' <-- s'!}) *
      (mu
        (([[[x <$-G; n' <$- [0..B -! 1]; n <$- [0..Elen (finv_ x) -! 1] ] ]]) E'
          m1))
      (fun m' : Mem.t k =>
        charfun (EP k (n' <! B)) m' * (
        charfun (EP k (!n' <! (B -! Elen (finv_ x)))) m' *
        charfun (T.i_eqb k (T.User Sem.A) s')
        (E.eval_expr (Enth {n, finv_ x}) m')))).
    rewrite Umult_sym, <- mu_stable_mult_right.
    apply mu_stable_eq; refine (ford_eq_intro _); intro m'.

    repeat rewrite <- Umult_assoc.
    apply Umult_eq_compat; trivial.
    repeat rewrite Umult_assoc.
    rewrite Umult_sym, Umult_assoc; apply Umult_eq_compat; trivial.
    
    apply Umult_eq_compat; trivial.
      
    transitivity 
        (mu
          (sum_support (RO.Sem.T.default k (T.User G))
            (E.eval_support (E.Duser (UG T.User Msg T.Bool)) m1))
     (fun vx => 
       charfun (fun w => negb (nat_eqb 0%nat w)) (length (ET.finv_def vx)) *
       charfun (T.i_eqb k (T.User Sem.G) (ET.f_def s')) vx * [1/]1+pred (length (ET.finv_def vx)) *
       ([1-] ((ET.size - length (ET.finv_def vx)) */ [1/]1+pred ET.size)))).

    rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
    apply mu_stable_eq;refine (ford_eq_intro _);intros vx.
    rewrite deno_cons_elim, Mlet_simpl, deno_random_elim.
    unfold charfun, restr, EP, fone; simpl mu.
    simpl E.eval_expr; unfold O.eval_op; simpl RO.Sem.T.app_op.
    rewrite (sum_dom_finite (RO.Sem.T.default k Msg)).
    assert (forall x, 0 < x -> 0%nat :: seq 1 (x - 1) = seq 0 x)%nat.
    destruct x; intros.
    elimtype False; omega.
    simpl.
    rewrite <- minus_n_O; trivial.
    rewrite H1.
    generalize (ET.size_spec vx); intros.

    assert (ET.size = (ET.size - (length (ET.finv_def vx)) +
      (length (ET.finv_def vx)))%nat) by omega.
    rewrite H3 at 1.
    rewrite seq_append, finite_sum_app.

    match goal with [ |- (?a + ?b)%U  == _ ] => assert (a == 0) end.
        apply finite_sum_notIn2.
        intros.
        apply In_seq_le in H4.
        rewrite deno_random_elim.
        simpl mu.
        simpl E.eval_expr; unfold O.eval_op; simpl RO.Sem.T.app_op.
        mem_upd_simpl.
        rewrite (sum_dom_finite 0%nat).
        rewrite finite_sum_notIn2.
        auto.
        intros.
        mem_upd_simpl.
        case_eq (leb (x + 1) (ET.size - length (ET.finv_def vx))); intros; simpl.
        repeat Usimpl; auto.
        apply leb_complete_conv in H6.
        elimtype False; omega.
        rewrite H4; clear H4.
     
        Usimpl.

     transitivity ( finite_sum
       (fun a : RO.Sem.T.interp k Msg =>
         [1/]1+pred (length (seq 0 ET.size)) * [1/]1+pred(length (ET.finv_def vx)) * 
         (charfun (T.i_eqb k (T.User G) (ET.f_def s')) vx))
       (seq (0 + (ET.size - length (ET.finv_def vx))) (length (ET.finv_def vx)))).
     apply finite_sum_eq; intros a Ha.
     rewrite <- Umult_assoc;apply Umult_eq_compat; trivial.
     rewrite deno_random_elim.
     unfold charfun, restr, EP, fone.

     case_eq (T.i_eqb k (T.User G) (ET.f_def s') vx); intros.
     Opaque E.eval_support.
     Opaque T.i_eqb.
     simpl; rewrite (sum_dom_finite (RO.Sem.T.default k Msg)).
     generalize (T.i_eqb_spec k (T.User G) (ET.f_def s') vx).
     rewrite H4; intros.
     apply ET.finv_spec in H5.
     destruct (In_nth_inv s' (A.default k) (ET.finv_def vx) H5) as [n [ H6 H7 ] ].
     rewrite (@finite_sum_full2 _ n).
     mem_upd_simpl; Usimpl.
     rewrite leb_correct; simpl.
     Usimpl.
     rewrite leb_correct_conv; simpl.
     Usimpl.
     rewrite H7.
     rewrite Ti_eqb_refl.
     Transparent E.eval_support.
     simpl; unfold O.eval_op; simpl RO.Sem.T.app_op.
     rewrite seq_length; auto.
     mem_upd_simpl; Usimpl.
     rewrite pred_of_minus; trivial.
     apply In_seq_le in Ha; omega.

     apply In_seq_le in Ha.
     omega.

     Opaque In.
     simpl; unfold O.eval_op; simpl RO.Sem.T.app_op.
     mem_upd_simpl; intros.
     rewrite H1 in H9.
     apply In_seq_le in H9.
     mem_upd_simpl; simpl.
     generalize (T.i_eqb_spec k (T.User Sem.A) s' (nth x (ET.finv_def vx) (A.default k))).
     destruct (T.i_eqb k (T.User Sem.A) s' (nth x (ET.finv_def vx) (A.default k))); intros.
     elim H8.
     destruct H9.
     revert H7 H8 H6 H11.
     rewrite H10.
     clear.
     revert n x.
     generalize (ET.finv_NoDup vx).
     induction 1; intros; simpl in *.
     elimtype False; omega.
     destruct x0; destruct n; trivial.
     elim H.
     subst; apply nth_In.
     omega.
     elim H.
     subst; apply nth_In.
     omega.
     rewrite (IHNoDup x0 n); auto; omega.
     repeat Usimpl; trivial.
     simpl in H6; omega.
     simpl.
     simpl; unfold O.eval_op; simpl RO.Sem.T.app_op.
     rewrite H1.
     mem_upd_simpl; simpl.
     apply le_In_seq; simpl in *; omega.
     mem_upd_simpl; simpl in *; omega.
     simpl; unfold O.eval_op; simpl RO.Sem.T.app_op.
     rewrite H1.
     apply NoDup_seq.
     mem_upd_simpl; simpl.
     simpl in H6; omega.

     simpl.
     rewrite (sum_dom_finite 0%nat).
     Usimpl.
     apply finite_sum_notIn2.
     simpl; unfold O.eval_op; simpl RO.Sem.T.app_op.
     intros.
     mem_upd_simpl; simpl.
     generalize (T.i_eqb_spec k (T.User Sem.A) s' (nth x (ET.finv_def vx) (A.default k))).
     destruct (T.i_eqb k (T.User Sem.A) s' (nth x (ET.finv_def vx) (A.default k))); intros.
     destruct (zerop (length (ET.finv_def vx))).
     rewrite e; simpl.
     replace (leb (a + 1) (ET.size - 0)) with true.
     simpl; repeat Usimpl; auto.
     symmetry.
     apply leb_correct.
     apply In_seq_le in Ha.
     omega.
     
     replace vx with (ET.f_def s') in H4.
     rewrite Ti_eqb_refl in H4.
     discriminate.
     apply ET.finv_spec; subst.
     apply nth_In.
     rewrite H1 in H5.
     apply In_seq_le in H5.
     generalize H5; mem_upd_simpl; simpl in *; intros; omega.
     mem_upd_simpl; simpl.
     repeat Usimpl; auto.

     rewrite finite_sum_In2 with (v :=  (([1/]1+pred (length (seq 0 ET.size)) *
      [1/]1+pred (length (ET.finv_def vx)) *
      charfun (T.i_eqb k (T.User G) (ET.f_def s')) vx))).
     repeat rewrite seq_length.
     destruct (length (ET.finv_def vx)).
     simpl; repeat Usimpl; auto.
     simpl nat_eqb; simpl negb.
     cbv iota.
     Usimpl.
     rewrite Nmult_Umult_assoc_left.
     rewrite Umult_sym.
     rewrite <- Umult_assoc.
     apply Umult_eq_compat.
     trivial.
     rewrite Nmult_Unth_simpl_right.
     rewrite Uinv_Nmult.
     replace (S (pred ET.size) - (ET.size - S n))%nat with (S n )%nat.
     rewrite Umult_sym.
     rewrite <- Nmult_Umult_assoc_left.
     rewrite Nmult_Unth_simpl_right; trivial.
     unfold Nmult_def.
     apply Unth_anti_mon.
     omega.
     omega.
     unfold Nmult_def.
     rewrite Unth_prod.
     apply Unth_anti_mon.
     simpl.
     auto with arith.
     intros.
     auto.
     apply ET.size_not_0.

     simpl.
     rewrite (sum_dom_finite (G.g k)).
     simpl in s'. 
     rewrite (@finite_sum_full _ (ET.f_def s')).
     unfold charfun, restr, fone; rewrite Ti_eqb_refl; Usimpl.
     case_eq (ET.finv_def (ET.f_def s')); intros.
     assert (W := @ET.finv_spec k (ET.f_def s') s').
     rewrite H1 in W.
     destruct W.
     elim H3; trivial.
     simpl.
     repeat Usimpl.
     rewrite Uinv_Nmult.
     replace (S (pred ET.size) - (ET.size - S (length l)))%nat with (S (length l))%nat.
     setoid_replace ( ([1/]1+length l * (S (length l) */ [1/]1+pred ET.size)) ) with ([1/]1+pred (ET.size)).
     
     generalize (@ET.size_group k).
     generalize (@G_support_notnil k).
     unfold G_support.
     rewrite map_length, seq_length.
     destruct (G.o k); simpl; intros.
     elim H2; trivial.
     generalize ET.size_not_0.
     destruct (ET.size); intros.
     elimtype False; omega.
     rewrite <- Unth_prod.
     auto.
     rewrite <- Nmult_Umult_assoc_right.
     rewrite Nmult_Unth_simpl_left; trivial.
     unfold Nmult_def.
     apply Unth_anti_mon.
     change (length l) with (pred (length (t :: l))).
     rewrite <- H1.
     apply le_pred.
     apply ET.size_spec.
     generalize ET.size_not_0.
     assert (S (length l) <= ET.size)%nat.
     change (S (length l)) with (length (t :: l)).
     rewrite <- H1.
     apply ET.size_spec.
     omega.
     
     intros x Hdiff.
     unfold charfun, restr, fone.
     generalize (T.i_eqb_spec k (T.User G) (ET.f_def s') x).
     destruct (T.i_eqb k (T.User G) (ET.f_def s') x).
     intros Heq; elim Hdiff;auto.
     repeat Usimpl;auto.
     apply G_support_full.
     apply G_support_NoDup; trivial.

  assert ((mu (([[ [a' <$-A] ]]) E' m2)) g == 
        finite_sum (fun s' => f (m1{!a' <-- s'!}) * [1/]1+pred(length (A.elems k))) (A.elems k)).
    rewrite deno_random_elim.
    Opaque sum_dom.
    simpl;rewrite (sum_dom_finite (A.default k)).
    apply finite_sum_eq.
    intros;rewrite Umult_sym.
    apply Umult_eq_compat_left.
    symmetry;apply H.
    apply req_mem_update;apply req_mem_empty.
    
  rewrite H0, H1, H2.
  (* TODO: make a lemma for this *)
  assert (finite_sum
      (fun s' : RO.Sem.T.interp k (Var.btype a') =>
        f (m1 {!a' <-- s'!}) * [1/]1+pred (ET.size * G.o k)) (A.elems k) /
    one_over_alpha k == 
      (finite_sum (fun s' : RO.Sem.T.interp k (Var.btype a') =>
        f (m1 {!a' <-- s'!}) * [1/]1+pred (ET.size * G.o k) / one_over_alpha k) (A.elems k))).
     clear.
     induction (A.elems k); simpl; trivial.
     rewrite <- IHl.
     rewrite Udiv_plus; trivial.

  rewrite H3;unfold epsilon.
  match goal with |- ?x <= _ => assert (W:x==0);[ | rewrite W;trivial]  end.
  rewrite Uabs_diff_zero.
  apply finite_sum_eq.
  intros.
  set (N:= (pred (length (A.elems k)))).
  assert (length (A.elems k) = S N).
   unfold N;destruct (A.elems k);[ elim H4 | trivial].
  rewrite mult_comm.
  rewrite Umult_div_assoc.
  apply Umult_eq_compat;trivial.
  unfold one_over_alpha, alpha;simpl.
  symmetry;apply Umult_div_eq.
  rewrite H5;apply Nmult_neq_zero;auto.
  rewrite Umult_sym, <- Nmult_Umult_assoc_left, H5.
  apply Nmult_Unth_simpl_right.
  rewrite H5;simpl;apply Unth_anti_mon.
  unfold N; apply le_pred;apply ET.size_group.
  unfold one_over_alpha, alpha;simpl.
  change ([1/]1+pred (G.o k * ET.size)) with (1 */ ([1/]1+pred (G.o k * ET.size))).
  apply Nmult_le_compat_left;omega.
Qed.

Transparent T.i_eqb sigma E.eval_support In sum_dom.


 (* *********************************************************************** *)
 (* ******************************  CLAIM 2  ****************************** *)
 (* Let [F : A x Zn -> G] be defined as F (a,z) = f a + z x g (where [g] is *)
 (* a generator of [G]). Then [F] is an epsilon-admissible encoding v2 with *)
 (* [epsilon = (1 - 1/alpha)^Tmax                                           *)
 (* *********************************************************************** *)

 Definition InvF_params : var_decl (Proc.targs InvF) := dcons _ r'' (dnil _).

 Definition InvF_res := ret'.

 Definition cond := (i <=! TMax) && !(IsSome a).

 Definition InvF_body :=
  [
   i <- 0%nat;
   a <- none _; 
   z <- 0%nat;
   x <- gen;
   a' <- Adef; 
   while ((i <=! TMax) && !(IsSome a)) do 
    [ 
     i <- i +! 1%nat;
     z <$- Zn;
     x <- r'' |-| z |*| gen;
     a <c- Invf_v2 with {x}
    ];     
    If (IsSome a) _then [ a' <- Proj a ];
    If (IsSome a) then
     [ ret' <- some (a' | z) ]
    else
     [ ret' <- none _ ]
  ].

    
 (* Environment containting info for [Invf_v1], [Invf_v2] and [InvF] *)
 Definition E'' := 
  add_decl E' InvF InvF_params (eq_refl true) InvF_body InvF_res.

 Definition i_E'E'' :=
  let i_empty   := empty_info E' E'' in
  let i_Invf_v1 := add_refl_info_rm Invf_v1 Vset.empty Vset.empty i_empty in
  let i_Invf_v2 := add_refl_info_rm Invf_v2 Vset.empty Vset.empty i_Invf_v1 in
   i_Invf_v2.

 Definition i_E''E'' :=
  let i_empty   :=  empty_info E'' E'' in
  let i_Invf_v1 :=  add_refl_info_rm Invf_v1 Vset.empty Vset.empty i_empty in
  let i_Invf_v2 :=  add_refl_info_rm Invf_v2 Vset.empty Vset.empty i_Invf_v1 in
  let i_InvF    :=  add_refl_info_rm InvF Vset.empty Vset.empty i_Invf_v2 in i_InvF.

 Definition Gi := [ r <$- G; ret'' <c- InvF with {r} ].

 Definition Gf :=
  [
   a' <$- A;
   z <$- Zn;
   ret'' <- some (a' | z)
  ]. 


 (* **************************** 1st STEP **************************** *)
 (* 1) Inline IF                                                       *)
 (******************************************************************** *)

 Definition G1 :=
  ([
   r <$- G;
   i <- 0%nat;
   a <- none _; 
   z <- 0%nat;
   x <- gen;
   a' <- Adef
  ] ++ 
  [
   while cond do 
    [ 
     i <- i +! 1%nat;
     z <$- Zn;
     x <- r |-| z |*| gen;
      a <c- Invf_v2 with {x}
     ]  
  ]) ++ 
  [     
   If (IsSome a) _then [ a' <- Proj a ];
   If (IsSome a) then
    [ ret'' <- some (a' | z) ]
   else
    [ ret'' <- none _ ]
  ].

  Lemma G1_Gi: EqObs Vset.empty E' G1 E'' Gi {{r,ret''}}.
  Proof.
   sinline i_E'E'' InvF.
   eqobs_hd i_E'E''.
   cp_test (IsSome a); deadcode; eqobs_in.
  Qed.


  (* **************************** 2nd STEP **************************** *)
  (* 1) Apply [sampling_fact1] to compute the values assigned           *)
  (* to [z] and [x]                                                     *)
  (******************************************************************** *)

  Definition G2 :=
   ([
    r <$- G;
    i <- 0%nat;
    a <- none _; 
    z <- 0%nat;
    x <- gen;
    a' <- Adef
   ] ++ 
   [
    while cond do 
     [ 
      i <- i +! 1%nat;
      x <$- G;  
      z <- log (r |-| x);
      a <c- Invf_v2 with {x}
     ]  ]) ++ 
   [
    If (IsSome a) _then [ a' <- Proj a ];
    If (IsSome a) then
     [ ret'' <- some (a' | z) ]
   else
    [ ret'' <- none _ ]
  ].

 Lemma G1_G2: EqObs Vset.empty E' G1 E' G2 {{r,ret''}}.
 Proof.
  unfold G1, G2.
  apply equiv_app with (kreq_mem {{i,z,a,r}} /-\ ~- EP1 cond  /-\ ~- EP2 cond).
  apply equiv_app with (kreq_mem {{i,z,a,r}}).
  eqobs_in.
  apply equiv_while.
  intros k m1 m2 Hm.
  apply (depend_only_fv_expr cond).
  apply req_mem_weaken with (2:=Hm); apply eq_refl.
  eqobs_tl i_E'E'.
  rewrite proj1_MR; eqobs_hd_n i_E'E' 1%nat; union_mod.
  eapply equiv_sub; [ | | apply sampling_fact1 ].
  intro k; apply implMR_kreq_mem_subset; apply eq_refl.
  intro k; apply implMR_kreq_mem_subset; apply eq_refl.
  discriminate.
  cp_test (IsSome a); eqobs_in.
 Qed.


 (* **************************** 3rd STEP **************************** *)
 (* 1) Push assignment [ z <- log (r |-| x) ] outside the loop         *) 
 (******************************************************************** *)

 Definition G3 :=
  [
   r <$- G;
   i <- 0%nat;
   a <- none _; 
   z <- 0%nat; 
   x <- gen;
   a' <- Adef
   ] ++ 
  ([
   while cond do 
    [ 
     i <- i +! 1%nat;
     x <$- G;  
     a <c- Invf_v2 with {x}
    ];
    z <- log (r |-| x) 
  ] ++ 
  [
   If (IsSome a) _then [ a' <- Proj a ];
   
   If (IsSome a) then
    [ ret'' <- some (a' | z) ]
   else
    [ ret'' <- none _ ]
  ]).


 Lemma G2_G3: EqObs Vset.empty E' G2 E' G3 {{r,ret''}}.
 Proof.
  unfold G2, G3; rewrite <- app_assoc.
  apply equiv_app with (kreq_mem {{a,i,r}} /-\ (EP1 cond) /-\ (EP2 cond)).
  fold (req_mem_rel {{a, i, r}} (EP1 cond /-\ EP2 cond)).
  eqobsrel_tail; unfold EP1, EP2; simpl; unfold O.eval_op; simpl;
   intros _ _ _ _ _ _; split; trivial.
  apply equiv_app with (kreq_mem {{r,z,a}}).

  eapply equiv_weaken; [ | apply (@loop_hoist _ _ 
   ([ i <- i +! 1%nat; x <$-G; z <- log (r |-| x); a <c- Invf_v2 with {x}  ])  
   ([ i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ] ) (@nil I.instr)  
   ([ z <- log (r |-| x) ]) _ _ _ (req_mem_rel {{x}} (EP1 (z=?=log (r |-| x)))) (kreq_mem {{z}})) ].
  intros k m1 m2 (H1,(H2,_)).
  apply req_mem_weaken with (Vset.union {{a, i, r}} {{z}});
   [ apply eq_refl | apply req_mem_union; trivial ].

  intros k m1 m2 (H1,_); apply depend_only_fv_expr.
  apply req_mem_weaken with (2:=H1); apply eq_refl.

  apply equiv_trans_eq_mem_l with trueR E' 
   [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x}; z <- log (r |-| x) ];
   [ rewrite proj1_MR; swap i_E'E'; apply equiv_eq_mem | | 
    unfold trueR; intros k m1 _ _; trivial ].
  rewrite proj1_MR; eqobs_hd_n i_E'E' 3%nat.
  eapply equiv_strengthen; [ | apply equiv_assign_l ].
  intros k m1 m2 H; split.
  apply req_mem_trans with m1; [ apply req_mem_sym | ].
  apply req_mem_upd_disjoint; apply eq_refl.
  apply req_mem_weaken with (2:=H); apply eq_refl.
  split.
  apply req_mem_trans with m1; [ apply req_mem_sym | ].
  apply req_mem_upd_disjoint; apply eq_refl.
  apply req_mem_weaken with (2:=H); apply eq_refl.
  unfold EP1; simpl; unfold O.eval_op; simpl; mem_upd_simpl; apply nat_eqb_refl.

  eapply equiv_strengthen; [ | apply equiv_assign_r ].
  intros k m1 m2 (H1,((H2,H3),(H4,H5))); unfold EP1, EP2, andR, notR in *; 
   split;[ | split; [ | split ] ].
  apply req_mem_trans with m2; [ assumption | 
   apply req_mem_upd_disjoint; apply eq_refl ].
  intros t v Hv; Vset_mem_inversion Hv; rewrite <-Heq.
  mem_upd_simpl.
  rewrite (@depend_only_fv_expr T.Nat (log (r |-| x)) _ m2 m1); [ |
   apply req_mem_sym; apply req_mem_weaken with (Vset.union {{a, i, r}} {{x}});
    [ apply eq_refl | apply req_mem_union; trivial ] ].
  apply nat_eqb_true; setoid_rewrite <-(@eval_eq k m1 T.Nat z (log (r |-| x))).
  apply H3.
  assumption.
  intro H; elim H5; unfold is_true in *; rewrite <-H.
  apply (@depend_only_fv_expr T.Bool cond).
  apply req_mem_upd_disjoint; apply eq_refl.

  cp_test (IsSome a); eqobs_in.
 Qed.
 

 (* **************************** 4th STEP **************************** *)
 (* 1) Apply [sampling_fact2] to assign a fresh random value to [z]    *)
 (* (and remove variable [r] since it becomes dead code)               *)
 (******************************************************************** *)

 Definition G4 :=
  ([
   i <- 0%nat;
   a <- none _; 
   z <- 0%nat;
   x <- gen;
   a' <- Adef
  ] ++ 
  [
   while cond do 
    [ 
     i <- i +! 1%nat;
     x <$- G;  
     a <c- Invf_v2 with {x}
    ];
    z <$- Zn 
  ]) ++ 
  [
   If (IsSome a) _then [ a' <- Proj a ];
   If (IsSome a) then
    [ ret'' <- some (a' | z) ]
   else
    [ ret'' <- none _ ]
  ].


 Lemma G3_G4: EqObs Vset.empty E' G3 E' G4 {{ret''}}.
 Proof.
  unfold G3, G4.
  apply EqObs_trans with E'
   ([
     i <- 0%nat;
     a <- none _; 
     z <- 0%nat;
     x <- gen;
     a' <- Adef;
     while cond do 
      [ 
       i <- i +! 1%nat;
       x <$- G;  
       a <c- Invf_v2 with {x}
      ];
     r <$- G;
     z <- log (r |-| x) 
   ] ++ 
   [
    If (IsSome a) _then [ a' <- Proj a ];
    If (IsSome a) then
     [ ret'' <- some (a' | z) ]
    else
     [ ret'' <- none _ ]
  ]).
  swap i_E'E'; eqobs_hd_n i_E'E' 7%nat.
  cp_test (IsSome a); eqobs_in.
  apply equiv_app with (kreq_mem {{a,z}}).
  eqobs_hd i_E'E'; union_mod.
  apply equiv_strengthen with (kreq_mem {{x}}).
  intros; eapply req_mem_weaken with (2:=H); apply eq_refl.
  apply EqObs_trans with E' [z <$-Zn; r <- x |+| z |*| gen].
  apply EqObs_sym; apply equiv_weaken with (kreq_mem {{r,z,x}});
   [ intros; eapply req_mem_weaken with (2:=H); apply eq_refl | ].
  apply (@sampling_fact2 E' r x z); discriminate.
  deadcode; eqobs_in.
  cp_test (IsSome a); eqobs_in.
 Qed.


 (* **************************** 5th STEP **************************** *)
 (* 1) Use the fact that [f] is a weak-encoding to replace [Invf]      *)
 (* output with a truely random value when the inverter succeeds at    *)
 (* some iteration                                                     *)
 (* 2) Add the [bad] flag for the next transition                      *)
 (******************************************************************** *)

 Lemma foo : forall k (f g:Mem.t k -o> U),
  (forall m1 m2, kreq_mem {{a'}} m1 m2 -> f m1 == g m2) ->
  forall m1 m2,
   mu (distr_cond
    ([[ [x <$-G; a <c- Invf_v2 with {x}; a' <- Proj a] ]] E' m1)
    (EP k (IsSome a))) f == 
   mu ([[ [a' <$- A] ]] E' m2) g.
 Proof.
  intros.
  apply Uabs_diff_zero.
  split; [ | trivial ].
  apply Invf_v2_distance_from_random; trivial.
 Qed.

 Lemma bar : forall k (f g:Mem.t k -o> U),
  (forall m1 m2, kreq_mem {{a'}} m1 m2 -> f m1 == g m2) ->
  forall m1 m2,
   mu ([[ [x <$-G; a <c- Invf_v2 with {x}; a' <- Proj a] ]] E' m1)
   (restr (EP k (IsSome a)) f) == 
  mu ([[ [a' <$- A] ]] E' m2) g * 
  mu ([[ [x <$-G; a <c- Invf_v2 with {x}; a' <- Proj a] ]] E' m1)
   (charfun (EP k (IsSome a))).
 Proof.
  intros.
  rewrite <- Udiv_mult with
   (y:=mu ([[ [x <$-G; a <c- Invf_v2 with {x}; a' <- Proj a] ]] E' m1)
    (charfun (EP k (IsSome a)))).
  Usimpl.
  rewrite <- (foo f g H m1 m2); simpl.
  match goal with
   |- ?x / _ == ?y / _ => setoid_replace x with y; trivial
  end.
  refine (mu_stable_eq _ _ _ _); refine (ford_eq_intro _); intro m'.
  unfold restr, EP; case (@E.eval_expr k T.Bool (IsSome a)); trivial.

  (* Add as hypothesis *)
  admit.

  apply mu_le_compat; [ trivial | ]; apply ford_le_intro; intro m'.
  unfold charfun, restr, EP; case (E.eval_expr (IsSome a)); trivial.
 Qed.

 Lemma foobar : forall k f g,
  (forall m1 m2, kreq_mem {{a'}} m1 m2 -> f m1 == g m2) ->
  forall m1 m2,
   mu ([[ [x <$-G; a <c- Invf_v2 with {x}; a' <- Proj a] ]] E' m1)
    (restr (EP k (IsSome a)) f) == 
   mu ([[ [x <$-G; a <c- Invf_v2 with {x}; a' <- Proj a] ]] E' m1)
    (fun m' => if m' a then mu ([[ [a' <$- A] ]] E' m2) g else 0).
 Proof.
  intros.
  rewrite (bar _ _ H m1 m2).
  rewrite <- (mu_stable_mult _ (mu ([[ [a' <$- A] ]] E' m2) g)).
  apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
  unfold fmult, charfun, restr, EP; expr_simpl; case (m' a); trivial.
 Qed.  

 Lemma foobarfoo : forall k f g,
  (forall m1 m2, kreq_mem {{a'}} m1 m2 -> f m1 == g m2) ->
  forall m1 m2,
   mu ([[ [x <$-G; a <c- Invf_v2 with {x}; a' <- Proj a] ]] E' m1)
    (restr (EP k (IsSome a)) f) == 
   mu ([[ [x <$-G; a <c- Invf_v2 with {x} ] ]] E' m1)
    (fun m' => if m' a then mu ([[ [a' <$- A] ]] E' m2) g else 0).
 Proof.
  intros.
  rewrite (foobar _ _ H m1 m2).
  apply EqObs_deno with Vset.empty {{a}}.
  deadcode i_E'E'; eqobs_in i_E'E'.
  intros; rewrite (H0 _ a); trivial.
  trivial.
 Qed.
 
 Lemma Invf_v2_output : forall k (f g:Mem.t k -o> U),
  (forall m1 m2, kreq_mem {{a'}} m1 m2 -> f m1 == g m2) -> 
  forall m1 m2,
   mu ([[ [x <$- G; a <c- Invf_v2 with {x}; a' <- Proj a] ]] E' m1) 
    (restr (EP k (IsSome a)) f) ==
   mu ([[ [x <$- G; a <c- Invf_v2 with {x}; a' <$- A] ]] E' m2)
    (restr (EP k (IsSome a)) g) .
 Proof.
  intros.
  rewrite (foobarfoo f g H _ m1).
  change [x <$- G; a <c- Invf_v2 with {x}; a' <$- A] with
   ([x <$-G; a <c- Invf_v2 with {x} ] ++ [a' <$- A]).
  rewrite deno_app_elim.
  apply EqObs_deno with Vset.empty {{a}}; trivial.
  eqobs_in i_E'E'.
  
  intros.
  case_eq (m0 a); intros.
  apply equiv_deno with 
   (req_mem_rel Vset.empty (EP2 (IsSome a)))
   (req_mem_rel {{a'}} (EP2 (IsSome a))). 
  eqobsrel_tail; unfold implMR; expr_simpl; intuition.
  unfold restr, charfun, EP, EP2; expr_simpl; intros.
  destruct H2; rewrite <- (H m4); trivial.
  destruct (m5 a); auto; discriminate.
  split.
  apply req_mem_empty.
  expr_simpl; rewrite <- (H0 _ a), H1; trivial.
  
  rewrite <- (mu_0 ([[ [a' <$- A] ]] E' m3)).
  apply equiv_deno with 
   (req_mem_rel Vset.empty (EP2 (!IsSome a)))
   (req_mem_rel {{a'}} (EP2 (!IsSome a))). 
  eqobsrel_tail; unfold implMR; expr_simpl; intuition.
  unfold restr, charfun, EP, EP2; expr_simpl; intros.
  destruct H2; destruct (m5 a); trivial; discriminate.
  
  split.
  apply req_mem_empty.
  expr_simpl; rewrite <- (H0 _ a); destruct (m0 a); trivial; discriminate.
 Qed.


 Lemma loop_unroll_dist: forall k (n:nat) (f g:Mem.t k -o> U),
  (forall m1 m2:Mem.t k, kreq_mem {{a'}} m1 m2 -> f m1 == g m2) ->
  forall m1 m2:Mem.t k,
   req_mem_rel {{a,i}} (EP1 (!(IsSome a))) _ m1 m2 -> 
   mu ([[ 
    unroll_while cond [ i <- i +! 1%nat; x <$- G; a <c- Invf_v2 with {x} ] (S n) ++
    [ If (IsSome a) _then [ a' <- Proj a ] ] 
   ]] E' m1) (restr (EP k (IsSome a)) f) ==
   mu ([[ 
    unroll_while cond [ i <- i +! 1%nat; x <$- G; a <c- Invf_v2 with {x} ] (S n) ++
    [ If (IsSome a) _then [ a' <$- A ]  ] 
   ]] E' m2) (restr (EP k (IsSome a)) g).
 Proof.
  induction n; intros.
 
  (* base case *)
  unfold unroll_while.
  repeat rewrite deno_app_elim, deno_cond_elim.
  rewrite (@depend_only_fv_expr T.Bool cond _ m2 m1); 
   [ | refine (req_mem_weaken _ (req_mem_sym (proj1 H0))); apply eq_refl ].
  case_eq (E.eval_expr cond m1); intro Hcond; setoid_rewrite Hcond.
 
  (* cond *)
  repeat (rewrite deno_app_elim; elim_assign).
  transitivity (
   mu ([[ [  x <$- G; a <c- Invf_v2 with {x} ] ++ [a' <- Proj a] ]] E'
    (m1 {!i <-- E.eval_expr (i +! 1%nat) m1!})) (restr (EP k (IsSome a)) f)).   
  rewrite deno_app_elim.
  apply mu_stable_eq; refine (ford_eq_intro _); intro m.
  unfold restr, EP; case_eq (@E.eval_expr _ T.Bool (IsSome a) m); intro Hguard.
  rewrite deno_if_nil_elim, deno_cond_elim, Hguard; trivial.
  rewrite deno_assign_elim.
  setoid_rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ 
   (m {!a' <-- E.eval_expr (Proj a) m!}) m);
  [  rewrite Hguard | apply req_mem_sym; apply req_mem_upd_disjoint ]; trivial.
  rewrite deno_if_nil_elim, deno_cond_elim, Hguard, deno_nil_elim, Hguard; trivial.
  transitivity (mu ([[ [x <$- G; a <c- Invf_v2 with {x} ] ++ [a' <$- A] ]] E' 
   (m2 {!i <-- E.eval_expr (i +! 1%nat) m2!})) (restr (EP k (IsSome a)) g)).

  apply (Invf_v2_output _ _ H).

  rewrite deno_app_elim.
  apply mu_stable_eq; refine (ford_eq_intro _); intro m; unfold restr, EP.
  case_eq (@E.eval_expr _ T.Bool (IsSome a) m); intro Hguard.

  rewrite deno_if_nil_elim, deno_cond_elim, Hguard; trivial.

  rewrite deno_if_nil_elim, deno_cond_elim, Hguard, deno_nil_elim.
  rewrite deno_random_elim, Hguard.
  rewrite <- mu_0; apply mu_stable_eq; refine (ford_eq_intro _); intro v.
  rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ (m {!a' <-- v!}) m); 
  [ | apply req_mem_sym; apply req_mem_upd_disjoint ]; trivial.
  rewrite Hguard; trivial.
 
  (* ~cond *)
  repeat rewrite deno_nil_elim, deno_cond_elim.
  rewrite (@depend_only_fv_expr T.Bool  (IsSome a) _ m2 m1); 
   [ | refine (req_mem_weaken _ (req_mem_sym (proj1 H0))); apply eq_refl ].
  case_eq (@E.eval_expr _ T.Bool (IsSome a) m1); intro Hguard.
  
  (* case (IsSome a) *)
  generalize (proj2 H0) Hguard; expr_simpl; case (m1 a); discriminate.

  (* case ~(IsSome a) *)
  repeat rewrite deno_nil_elim.
  unfold restr, EP.
  rewrite (@depend_only_fv_expr T.Bool  (IsSome a) _ m2 m1); 
   [ | refine (req_mem_weaken _ (req_mem_sym (proj1 H0))); apply eq_refl ].
  rewrite Hguard; trivial.

  (* inductive case *)
  unfold unroll_while; fold (unroll_while cond 
   [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ] (S n)).
  repeat rewrite deno_app_elim, deno_cond_elim.
  rewrite (@depend_only_fv_expr T.Bool cond _ m2 m1); 
   [ | refine (req_mem_weaken _ (req_mem_sym (proj1 H0))); apply eq_refl ].
  case_eq (E.eval_expr cond m1); intro Hcond; setoid_rewrite Hcond.
 
  (* cond *)
  repeat (rewrite deno_app_elim; elim_assign).
  rewrite (mu_restr_split ([[ [x <$-G; a <c- Invf_v2 with {x} ] ]] E'
   (m2 {!i<--E.eval_expr (i +! 1%nat) m2!})) (EP k (IsSome a))),
  (mu_restr_split ([[ [x <$-G; a <c- Invf_v2 with {x} ] ]] E'
   (m1 {!i<--E.eval_expr (i +! 1%nat) m1!})) (EP k (IsSome a))).
  apply Uplus_eq_compat.
 
  (* IsSome a *)
  transitivity (mu ([[ [x <$- G; a <c- Invf_v2 with {x} ] ++ [a' <- Proj a] ]] E' 
   (m1 {!i <-- E.eval_expr (i +! 1%nat) m1!})) (restr (EP k (IsSome a)) f)).
  rewrite deno_app_elim.
  apply mu_stable_eq; refine (ford_eq_intro _); intro m.
  unfold restr, EP; case_eq (@E.eval_expr _ T.Bool (IsSome a) m); intro Hguard.
 
  rewrite unroll_while_false_elim; 
   [ | unfold cond; 
    rewrite <- eval_andb, <- eval_negb, Hguard, andb_false_r; trivial ].
  repeat rewrite deno_cond_elim; rewrite Hguard; trivial.
            
  rewrite deno_assign_elim.
  setoid_rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ 
   (m {!a' <-- E.eval_expr (Proj a) m!}) m);
   [ rewrite Hguard | apply req_mem_sym; apply req_mem_upd_disjoint ]; trivial.
  transitivity (mu ([[ [x <$- G; a <c- Invf_v2 with {x} ] ++ [a' <$- A] ]] E' 
   (m2 {!i <-- E.eval_expr (i +! 1%nat) m2!})) (restr (EP k (IsSome a)) g)).
  apply (Invf_v2_output _ _ H).
 
  rewrite deno_app_elim.
  apply mu_stable_eq; refine (ford_eq_intro _); intro m; unfold restr, EP.
  case_eq (@E.eval_expr _ T.Bool (IsSome a) m); intro Hguard.

  rewrite unroll_while_false_elim; [ | unfold cond;
   rewrite <- eval_andb, <- eval_negb, Hguard, andb_false_r; trivial ].
  rewrite deno_cond_elim, Hguard; trivial.

  repeat rewrite deno_random_elim.
  rewrite <- mu_0; apply mu_stable_eq; refine (ford_eq_intro _); intro v.
  rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ (m {!a' <-- v!}) m), Hguard; 
   [ | apply req_mem_sym; apply req_mem_upd_disjoint ]; trivial.
 
  (* ~ IsSome a *)
  apply equiv_deno with (kreq_mem {{a,i}}) (kreq_mem {{a,i}}).
  eqobs_in i_E'E'.
  intros m1' m2' H1m'; unfold restr, EP, negP, negb.
  rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ m2' m1'); 
   [ | refine (req_mem_weaken _ (req_mem_sym H1m')); apply eq_refl ].
  case_eq (@E.eval_expr _ T.Bool (IsSome a) m1'); intro Hguard.
  trivial.
  repeat rewrite <-deno_app_elim; apply (IHn _ _ H).
  split.
  refine (req_mem_weaken _ H1m'); apply eq_refl.
  unfold EP1; rewrite <- eval_negb, Hguard; trivial.
  intros t x Hx; Vset_mem_inversion Hx; subst; mem_upd_simpl.
  apply H0; trivial.
  apply depend_only_fv_expr; refine (req_mem_weaken _ (proj1 H0)); apply eq_refl.
  
  (* ~cond *)
  repeat rewrite deno_nil_elim, deno_cond_elim.
  rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ m2 m1); 
   [ | refine (req_mem_weaken _ (req_mem_sym (proj1 H0))); apply eq_refl ].
  generalize (proj2 H0); unfold EP1, is_true.
  rewrite <- eval_negb, negb_true_iff; intro H0'; rewrite H0'.
  repeat rewrite deno_nil_elim.
  unfold restr, EP.
  rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ m2 m1); 
   [ | refine (req_mem_weaken _ (req_mem_sym (proj1 H0))); apply eq_refl ].
  rewrite H0'; trivial.
 Qed.


 Definition G5 :=
  [
   i <- 0%nat;
   a <- none _; 
   z <- 0%nat;
   x <- gen;
   a' <- Adef;
   bad <- false;
   while cond do 
    [ 
     i <- i +! 1%nat;
     x <$- G;  
     a <c- Invf_v2 with {x}
    ] 
  ] ++ 
  [
    If (IsSome a) then [ a' <$- A ] else [ bad <- true ];
    z <$- Zn;
    If (IsSome a) then
     [ ret'' <- some (a' | z) ]
    else
     [ ret'' <- none _ ]
   ].


 Lemma body_loop_range: forall k (m: Mem.t k),
  E.eval_expr cond m ->
  range (fun m' =>
   EP k ((TMax +! 1%nat -! i) <! E.eval_expr (TMax +! 1%nat -! i) m) m')
  ([[ [ i <- i +! 1%nat; x <$- G; a <c- Invf_v2 with {x} ] ]] E' m).
 Proof.
  intros k m Hm f H_f.
  elim_assign.
  rewrite (@Modify_deno_elim E' {{a,x}} [x <$-G; a <c- Invf_v2 with {x} ]);
   [ | apply modify_correct with (refl1_info i_E'E') Vset.empty; apply eq_refl ].
  match goal with |- _ == fmonot (mu ?d) _ => rewrite <-(mu_zero d) end.
  apply mu_stable_eq; unfold fzero; refine (ford_eq_intro _); intro m'.
  apply H_f.
  generalize Hm; unfold cond, EP; clear Hm.
  expr_simpl; mem_upd_simpl.
  rewrite is_true_andb; intros [Hm _].
  apply leb_correct; apply leb_complete in Hm; omega.
 Qed.

 Lemma loop_lossless: lossless E' 
  [ while cond do [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ] ].
 Proof.
  apply lossless_bounded_while with (TMax +! 1%nat -! i).
  apply body_loop_range.
  apply is_lossless_correct with (refl1_info i_E'E'); apply eq_refl.
 Qed.
 
 Lemma G4_G5: prg_SD 
  (kreq_mem Vset.empty) 
  E' G4 E' G5 
  (kreq_mem {{ret''}}) 
  (fzero _).
 Proof.
  intros k f g Hfg m1 m2 Hm.
  set (G4' := 
   [ i <- 0%nat; a <- none _; z <- 0%nat; x <- gen; a' <- Adef ] ++
   [ while cond do [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ];
    If IsSome a _then [a' <- Proj a] ] ++
   [ z <$-Zn;
    If IsSome a
    then [ret'' <- some (a' | z)]
    else [ret'' <- none _]
   ]).
  set (G5' :=
   [ i <- 0%nat; a <- none _; z <- 0%nat; x <- gen; a' <- Adef ] ++
   [ while cond do [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ];
    If IsSome a _then [a' <$- A] ] ++
   [ z <$-Zn;
    If IsSome a
    then [ret'' <- some (a' | z)]
    else [ret'' <- none _]
   ]).
  unfold fzero; apply Oeq_le; rewrite Uabs_diff_zero.
  transitivity (mu ([[G4']] E' m1) g).
  
  apply equiv_deno with Meq (kreq_mem {{ret''}}).
  swap i_E'E'; eqobs_in i_E'E'.
  apply Hfg.
  unfold Meq; trivial.

  transitivity (mu ([[G5']] E' m2) f); [ | 
   apply equiv_deno with Meq (kreq_mem {{ret''}}); 
    [ deadcode i_E'E'; swap i_E'E'; eqobs_in i_E'E' | apply Hfg | trivial ] ].
  unfold G4', G5'.
  repeat rewrite (deno_app_elim 
   E' [i <- 0%nat; a <- none _; z <- 0%nat; x <- gen; a' <- Adef]).
  apply equiv_deno with (kreq_mem Vset.empty) (req_mem_rel {{i,a,z,x,a'}} 
   (EP1 (!(IsSome a)) /-\ EP1 (i=?=0%nat))); trivial.
  eqobsrel_tail; expr_simpl; intros; split; trivial.
  clear m1 m2 Hm; intros m1 m2 Hm.
  repeat rewrite deno_app_elim.
  rewrite (mu_restr_split 
   ([[ [
    while cond do [ i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ];
     If IsSome a _then [a' <- Proj a]
   ] ]] E' m1) (EP k (IsSome a))), 
  (mu_restr_split ([[ 
   [
    while cond do [ i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ];
     If IsSome a _then [a' <$- A]
   ] ]] E' m2) (EP k (IsSome a))).
  apply Uplus_eq_compat.
  

   (* case [IsSome a] *)
  assert (aux: forall (m:Mem.t k) F,
   mu ([[  [ while cond do  
    [ i <- i +! 1%nat; x <$- G; a <c- Invf_v2 with {x} ] ] ]] E' m) F ==
   mu ([[ unroll_while cond  [ i <- i +! 1%nat; x <$- G; a <c- Invf_v2 with {x} ]
    (E.eval_expr (TMax +! 1%nat -! i) m) ]] E' m) F).
  intros.
  apply deno_bounded_while_elim with (TMax +! 1%nat -! i).
  apply body_loop_range.
  intros m'; unfold cond; expr_simpl; intro H.
  rewrite leb_correct_conv, andb_false_l; [ trivial | omega ].
  trivial.
  rewrite (@deno_app_elim _ E' [ while cond do [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ] ]
   [ If IsSome a _then [a' <- Proj a] ] ), aux,
  (@deno_app_elim _ E'  
   [ while cond do [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ] ] 
   [ If IsSome a _then [a' <$- A] ] ), aux, <-deno_app_elim, <-deno_app_elim.
  replace (E.eval_expr (TMax +! 1%nat -! i) m1) with (S (T_poly k)) by
   (generalize (proj2 (proj2 Hm)); expr_simpl; intro H; rewrite (nat_eqb_true H); omega).
  replace (E.eval_expr (TMax +! 1%nat -! i) m2) with (S (T_poly k)) by
   (generalize (proj2 (proj2 Hm)); expr_simpl; rewrite (proj1 Hm _ i);
    [ intro H; rewrite (nat_eqb_true H); omega | trivial ]).

  transitivity
   (mu
    ([[unroll_while cond [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ]
     (S (T_poly k)) ++ [If IsSome a _then [a' <$- A] ] ]] E' m2)
    (restr (EP k (IsSome a)) 
    (fun mn' => (mu ([[ [ z <$- Zn; ret'' <- some (a' | z) ] ]] E' mn') g)))).  
  Focus 2.
  apply mu_stable_eq; refine (ford_eq_intro _); intros m'.
  unfold restr, EP, charfun, restr.
  case_eq (@E.eval_expr k T.Bool (IsSome a) m'); intros.
  apply equiv_deno with
   (req_mem_rel {{a'}} (EP2 (IsSome a)))
   (kreq_mem {{ret''}}).
  ep_eq_r (IsSome a) true.
  generalize H; expr_simpl; unfold req_mem_rel, andR; intuition.   
  eqobs_in i_E'E'.
  intros.
  transitivity (f m3); [ symmetry | ]; auto.
  split; trivial.
  trivial.
  
  transitivity
   (mu
    ([[unroll_while cond [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ]
     (S (T_poly k)) ++ [If IsSome a _then [a' <- Proj a] ] ]] E' m1)
    (restr (EP k (IsSome a)) 
    (fun mn' => (mu ([[ [ z <$- Zn; ret'' <- some (a' | z) ] ]] E' mn') g)))).  
  apply mu_stable_eq; refine (ford_eq_intro _); intros m'.
  unfold restr, EP, charfun, restr.
  case_eq (@E.eval_expr k T.Bool (IsSome a) m'); intros.
  apply equiv_deno with
   (req_mem_rel {{a'}} (EP1 (IsSome a)))
   (kreq_mem {{ret''}}).
  ep_eq_l (IsSome a) true.
  generalize H; expr_simpl; unfold req_mem_rel, andR; intuition.   
  eqobs_in i_E'E'.
  intros.
  transitivity (f m3); [ symmetry | ]; auto.
  split; trivial.
  trivial.


  apply loop_unroll_dist.
  intros; apply EqObs_deno with {{a'}} {{ret''}}.
  eqobs_in i_E'E'.
  clear - Hfg; intros.
  rewrite <- (Hfg m1); auto.
  trivial.
  destruct Hm as [? [? ?] ].
  split; auto.
  eapply req_mem_weaken with (2:=H); vm_compute; trivial.
  
  apply equiv_deno with (kreq_mem {{i, a, z, x, a'}}) (kreq_mem {{a}}); 
   [ | | exact (proj1 Hm) ].
  apply equiv_app with
   (Q  := kreq_mem {{i, a,  x}})  
   (c1 := [ while cond do [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ] ])
   (c2 := [ If IsSome a _then [a' <- Proj a] ] )
   (c3 := [ while cond do [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ] ])     
   (c4 := [  If IsSome a _then [a' <$-A] ] );
   [ eqobs_in i_E'E' | deadcode; eqobs_in ].
  clear m1 m2 Hm; intros m1 m2 Hm.
  unfold restr, negP, negb, EP.
  rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ m2 m1); [ | exact (req_mem_sym Hm) ]. 
  case_eq (@E.eval_expr _ T.Bool (IsSome a) m1); intro Hguard.
  trivial.
  apply equiv_deno with (req_mem_rel {{a}}  (~-(EP1 (IsSome a)))) (kreq_mem {{ret''}}).
  cp_test (IsSome a).
  apply equiv_False; intros k' m1' m2' ((_,H1),(H2,_)); unfold notR in H1; tauto.
  eqobs_in.
  intros; symmetry; auto.
  split; [ trivial | unfold notR, EP1; rewrite Hguard; discriminate ].
 Qed.
     

 (* **************************** 6th STEP **************************** *)
 (* 1) Assign [a'] a random value if inverter [Invf] fails in all the  *)
 (* iterations                                                         *)
 (******************************************************************** *)

 Definition G6 :=
  [
   i <- 0%nat;
   a <- none _; 
   z <- 0%nat;
   x <- gen;
   a' <- Adef;
   bad <- false;
   while cond do 
    [ 
     i <- i +! 1%nat;
     x <$- G;  
     a <c- Invf_v2 with {x}
    ] 
  ] ++ 
  [
   If (IsSome a) then [ a' <$- A ] else [ bad <- true; a' <$-A; a <- some Adef ];
    z <$- Zn;
    If (IsSome a) then
     [ ret'' <- some (a' | z) ]
   else
     [ ret'' <- none _ ]
  ].


 Lemma loop_failure: forall n k (m:Mem.t k), 
  m bad = false ->
  n = (S (T_poly k) - (m i))%nat ->
  Pr E'
  [
   while cond do [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ];
    If !(IsSome a) _then [bad <- true]
  ] m (EP k bad) <= (1 - one_over_alpha k) ^ n.
 Proof.
  unfold Pr; induction n; intros k m Hbad Hn.
  auto.
  rewrite deno_cons_elim, Mlet_simpl, deno_while_elim, deno_cond_elim.
  case_eq (@E.eval_expr _ T.Bool cond m); intro Hc.
  
  (* case [cond=true] *)
  rewrite deno_app_elim.
  rewrite (mu_restr_split _ (fun m' => EP k (IsSome a) m')).
  match goal with |- ?X' + _ <= _ => assert (X'==0) end.
  rewrite (@Modify_deno_elim E' {{a,x,i}} 
   [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ]); 
  [ | apply modify_correct with (refl1_info i_E'E') Vset.empty; apply eq_refl ].
  match goal with |- fmonot (mu ?d) _ == 0 => rewrite <-(mu_zero d) end.
  apply mu_stable_eq; unfold fzero, restr; refine (ford_eq_intro _); intro m'.
  case_eq (EP k (IsSome a) (m {!{{a, x, i}} <<- m'!})); unfold EP; intro Heq.
  rewrite deno_while_elim, deno_cond_elim.
  replace (@E.eval_expr _ T.Bool cond (m {!{{a, x, i}} <<- m'!})) with false 
   by (unfold cond; rewrite <- eval_andb, <- eval_negb, Heq, andb_false_r; trivial).
  rewrite deno_nil_elim, deno_cond_elim, <- eval_negb, Heq;
   unfold negb, charfun, restr; rewrite deno_nil_elim;simpl;
    mem_upd_simpl; rewrite Hbad; trivial.
  trivial.
  rewrite H; Usimpl.
  transitivity  (mu ([[ [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ] ]]
   E' m) (restr (negP (fun m' => EP k (IsSome a) m')) (fcte _ ((1 - one_over_alpha k) ^ n)))).
       
  (*  *)
  apply range_le with (P:=fun m':Mem.t k =>  n = (S (T_poly k) - m' i)%nat /\ m' bad = false).
  intros f H_f.
  elim_assign.
  rewrite (@Modify_deno_elim E' {{a,x}} [x <$-G; a <c- Invf_v2 with {x} ]); 
   [ | apply modify_correct with (refl1_info i_E'E') Vset.empty; apply eq_refl ].
  match goal with |- _ == fmonot (mu ?d) _ => rewrite <-(mu_zero d) end.
  apply mu_stable_eq; unfold fzero; refine (ford_eq_intro _); intro m'.
  apply H_f; split.
  generalize Hc; unfold cond; clear Hc.
  rewrite <- eval_andb, (is_true_andb (E.eval_expr (i <=! TMax) m) 
   (E.eval_expr (!(IsSome a)) m)).
  rewrite update_mem_notin, Mem.get_upd_same; [ | discriminate ]; 
   change (E.eval_expr (i +! 1%nat) m) with (m i + 1)%nat.
  intros [Hm _]; apply (leb_complete (m i) (T_poly k)) in Hm.
  omega.
  rewrite update_mem_notin; mem_upd_simpl; discriminate. 
  intros m' [Hn' Hbad']; unfold restr, negP, negb.
  case_eq (EP k (IsSome a) m'); unfold EP; intro Heq.
  trivial.
  rewrite <-Mlet_simpl, <-deno_cons_elim; apply IHn; assumption.
  (*  *)
  rewrite mu_restr_cte, (Umult_sym (1-one_over_alpha k) ((1 - one_over_alpha k)^n)); Usimpl.
  rewrite Uminus_one_left, <- (Uinv_eq_compat (Invf_v2_success_probability m)).
  rewrite (@Pr_neg _ E' [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ] m 
   (fun m' : Mem.t k => EP k (IsSome a) m'));
  [ |  apply is_lossless_correct with (refl2_info i_E'E'); apply eq_refl ].
  Usimpl.
  unfold Pr; apply Oeq_le; apply EqObs_deno_same with Vset.empty (fv_expr (IsSome a)).
  set (i_aux:=let i_empty := empty_info E' E' in
   let i_Invf_v1 :=  add_refl_info_rm Invf_v1 Vset.empty Vset.empty i_empty in
    add_refl_info_rm Invf_v2 Vset.empty Vset.empty i_Invf_v1).
  deadcode i_aux; eqobs_in i_aux.
  unfold  negP, charfun, restr, EP, fone; intros m1 m2 Hm.
  rewrite (@depend_only_fv_expr T.Bool (IsSome a) _ _ _ Hm); trivial.
 
  (* case [cond=false] *)
  rewrite deno_nil_elim, deno_cond_elim.
  replace (@E.eval_expr _ T.Bool (!(IsSome a)) m) with false.
  rewrite deno_nil_elim.
  unfold charfun, restr, EP; simpl; rewrite Hbad; trivial.
  generalize Hc; unfold cond; simpl; unfold O.eval_op; simpl.
  replace (leb (m i) (T_poly k)) with true by (symmetry; apply leb_correct; omega).
  auto.
 Qed.


 Definition i_upto_E'E' :=
  let i_empty   := empty_upto_info bad E' E' in
  let i_Invf_v1 := add_upto_info i_empty Invf_v1 in 
  let i_Invf_v2 := add_upto_info i_Invf_v1 Invf_v2 in i_Invf_v2.

 Lemma G5_G6: prg_SD (kreq_mem Vset.empty) E' G5 E' G6 (kreq_mem {{ret''}}) 
  (fun k => (1 - one_over_alpha k)^(S (T_poly k))).
 Proof.
  apply prg_SD_Meq_pre_weaken;
   [ | eqobs_in i_E'E' | eqobs_in i_E'E' | apply symMR_kreq_mem ].

  apply prg_SD_weaken with Meq (kreq_mem {{ret''}})
   (fplus (fun k : nat => (1 - one_over_alpha k) ^ S (T_poly k)) (fzero _));
   [ | | unfold fplus, fzero | ];  auto.
  rewrite <- (firstn_skipn 8 G5), <- (firstn_skipn 8 G6).
  apply prg_SD_seq_Meq; simpl firstn; simpl skipn.
  rewrite <-rtriple_deno.
  intros k m f.
  repeat elim_assign.
  match goal with 
   |- Uabs_diff (fmonot (mu ([[ _ ]] _ ?m'')) _) _ <= _ => 
   set (m':=m''); simpl in m'; unfold O.eval_op in m'; simpl in m' 
  end.
  rewrite (@upto_bad_GSD _ _ _  bad is_true_true i_upto_E'E'); 
   [ | apply eq_refl | ].
  apply Ole_eq_left with  (Pr E' [ while cond do 
   [i <- i +! 1%nat; x <$-G; a <c- Invf_v2 with {x} ];
   If !IsSome a _then  [bad <- true] ] m' (EP k bad)).
  apply EqObs_Pr with {{bad,i,a,a'}}.
  deadcode i_E'E'; eqobs_hd i_E'E'; cp_test (IsSome a); eqobs_in.

  apply loop_failure; unfold m'; mem_upd_simpl.
  apply lossless_cons.
  apply loop_lossless.
  apply is_lossless_correct with (refl2_info i_E'E'); apply eq_refl.

  unfold prg_SD; intros. 
  unfold fzero; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with Meq (kreq_mem {{ret''}}); trivial; eqobs_in.
 Qed.


 (* **************************** 7th STEP **************************** *)
 (* 1) Remove deadcode                                                 *)
 (******************************************************************** *)

 Lemma G6_Gf: EqObs Vset.empty E' G6 E' Gf {{ret''}}.
 Proof.
  unfold G6, Gf.
  apply equiv_app with (c3:=@nil I.instr) (c4:=Gf) (Q:=trueR).
  apply equiv_True.
  rewrite <-(firstn_skipn 6); apply lossless_app; simpl.
  apply is_lossless_correct with (refl2_info i_E'E'); apply eq_refl.
  apply loop_lossless.
  apply lossless_nil.
  cp_test_l (IsSome a).
  cp_test_r (IsSome a); apply equiv_strengthen 
   with (kreq_mem Vset.empty); try (intros; apply req_mem_empty).
  eqobs_in.
  eqobs_in.

  deadcode.
  cp_test_l (IsSome (some Adef)).
  apply equiv_strengthen with (kreq_mem Vset.empty); 
   try (intros; apply req_mem_empty).
  eqobs_in.
  apply equiv_False.
  intros k m1 m2 (_,H); generalize H.
  unfold notR, EP1; simpl; unfold O.eval_op; simpl; auto.
 Qed.


 (* When given a random input, [InvF]'s output is at distance
   [(1-1/alpha)^Tmax] from the uniform distritubion *)
 Lemma Inv_F_distance_from_random: 
  prg_SD (kreq_mem Vset.empty) E'' Gi E' Gf (kreq_mem {{ret''}})  
   (fun k => (1 - one_over_alpha k)^(S (T_poly k))).
 Proof.
  rewrite <-(fplus_fzero_l  (fun k => (1 - one_over_alpha k)^(S (T_poly k)))).
  apply prg_SD_trans_PER with E'' G1; try apply req_mem_PER.
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.

  transitivity (mu ([[G1]] E' m2) g).
  symmetry; apply equiv_deno with (1:=G1_Gi).
  intros; symmetry; apply H;
   apply req_mem_sym; apply req_mem_weaken with (2:=H1); apply eq_refl.
  apply req_mem_empty.

  eapply EqObs_deno with Vset.empty {{ret''}}.
  eqobs_in i_E'E''.
  intros; transitivity (f m3); intuition.
  symmetry; auto.
  auto.
  
  rewrite <-(fplus_fzero_l  (fun k => (1 - one_over_alpha k)^(S (T_poly k)))).
  apply prg_SD_trans_PER with E' G2; try apply req_mem_PER.
    unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.

  transitivity (mu ([[G1]] E' m1) f).
  symmetry; apply EqObs_deno with Vset.empty {{ret''}}.
  eqobs_in i_E'E''.
  intros; transitivity (g m0); intuition.
  symmetry; auto.
  auto.

  apply equiv_deno with (1:=G1_G2).
  intros; apply H; apply req_mem_weaken with (2:=H1); apply eq_refl.
  apply req_mem_empty.
  rewrite <-(fplus_fzero_l  (fun k => (1 - one_over_alpha k)^(S (T_poly k)))).
  apply prg_SD_trans_PER with E' G3; try apply req_mem_PER.
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with (1:=G2_G3).
  intros; apply H; apply req_mem_weaken with (2:=H1); apply eq_refl.
  apply req_mem_empty.
  rewrite <-(fplus_fzero_l  (fun k => (1 - one_over_alpha k)^(S (T_poly k)))).
  apply prg_SD_trans_PER with E' G4; try apply req_mem_PER.
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with (1:=G3_G4); trivial; apply req_mem_empty.
  rewrite <-(fplus_fzero_l  (fun k => (1 - one_over_alpha k)^(S (T_poly k)))).
  apply prg_SD_trans_PER with (3:=G4_G5); try apply req_mem_PER.
  rewrite <-(fplus_fzero_r  (fun k => (1 - one_over_alpha k)^(S (T_poly k)))).
  apply prg_SD_trans_PER with (3:=G5_G6); try apply req_mem_PER.
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with (1:=G6_Gf); trivial; apply req_mem_empty.
 Qed.

 (* REMARK: this condition is equivalent to the one given in the paper *)
 Lemma InvF_is_partial_inverter : forall k (m:Mem.t k),
  range (fun m' => 
   EP k ((IsSome ret'') ==> 
   (r =?= f_ (Efst (Proj ret'')) |+|  (Esnd (Proj ret'')) |*| gen)) m')
  ([[ [ r <$-G; ret'' <c- InvF with {r} ] ]] E'' m).
 Proof.
  intros k m.
  apply mu_range.
  change (Pr E'' Gi m (EP k ((IsSome ret'') ==>
   (r =?= f_ Efst (Proj ret'') |+| Esnd (Proj ret'') |*| gen))) == 1).
  transitivity  (Pr E' G1 m (EP k ((IsSome ret'') ==>
   (r =?= f_ Efst (Proj ret'') |+| Esnd (Proj ret'') |*| gen)))).
  symmetry.
  apply EqObs_Pr2 with (1:=G1_Gi); [ apply eq_refl | auto ].
  transitivity  (Pr E' G2 m (EP k ((IsSome ret'') ==>
   (r =?= f_ Efst (Proj ret'') |+| Esnd (Proj ret'') |*| gen)))).
  apply EqObs_Pr2 with (1:=G1_G2); [ apply eq_refl | auto ].
  transitivity  (Pr E' G3 m (EP k ((IsSome ret'') ==>
   (r =?= f_ Efst (Proj ret'') |+| Esnd (Proj ret'') |*| gen)))).
  apply EqObs_Pr2 with (1:=G2_G3); [ apply eq_refl | auto ].
  assert (lossless E' G3).
  apply lossless_app; [ | apply lossless_app ].
  apply is_lossless_correct with (refl1_info i_E'E''); vm_compute; trivial.
  apply lossless_cons; [ apply loop_lossless | apply lossless_assign ].
  apply is_lossless_correct with (refl1_info i_E'E''); vm_compute; trivial.
  rewrite <-(H _ m).
  apply equiv_deno with (kreq_mem Vset.empty) (req_mem_rel Vset.empty (EP1
   ((IsSome ret'') ==> (r =?= f_ Efst (Proj ret'') |+| Esnd (Proj ret'') |*| gen)))).
  unfold G3.
  apply equiv_app with 
   (req_mem_rel {{i,x,a}} (EP1 ((IsSome a) ==> (x  =?= f_ (Proj a))))).
  eqobsrel_tail; expr_simpl; intros ? _ _ _ _ _; trivial.
  eapply equiv_cons; [ apply equiv_while | ].
  intros k' m1' m2' (H1,_). 
  apply depend_only_fv_expr_subset with (2:=H1); apply eq_refl.
  apply equiv_strengthen_range.
          
  auto.
  apply is_lossless_correct with (refl1_info i_E'E''); vm_compute; trivial.
  intros; apply mu_range.
  transitivity (Pr E' [x <$-G; a <c- Invf_v2 with {x} ] m0 
   (EP k0 ((IsSome a) ==> (x =?= f_ (Proj a))) )); symmetry.
  apply EqObs_Pr with (Vset.empty); deadcode i_E'E'; eqobs_in i_E'E'.
  assert (Hloss: lossless E' [x <$-G; a <c- Invf_v2 with {x} ]) by
   (apply is_lossless_correct with (refl1_info i_E'E'); vm_compute; trivial).
  rewrite <-(Hloss _ m0); symmetry.
  apply range_mu; apply Invf_v2_is_partial_inverter.          
  eqobs_in i_E'E'.
  eqobsrel_tail; unfold implMR; expr_simpl.
  intros k' m1' m2'; case_eq (m1' a). 
  intros v Hv (H1',(H2',(H3',H4'))); split; intros; split; intros; trivial.
  rewrite is_true_impb in H2'.
  rewrite <- G.log_spec, <- (Geqb_true (H2' is_true_true)).
  rewrite G.mul_comm, <-G.mul_assoc, <-(G.mul_comm (m1' x)), 
   G.inv_spec, G.mul_0_r, (G_eqb_refl (m1' r)); trivial.
  destruct H0; apply not_true_is_false in H0; discriminate.
  intros Ha (H1',(H2',(H3',H4'))); split; intros; split; intros; trivial.
  destruct H0; discriminate H0.
  destruct H1; discriminate H1.
  unfold EP1, charfun, restr, EP; intros m1 m2 (_,H'); rewrite H'; trivial.
  trivial.
 Qed.


 (* ******************************  CLAIM 3  ****************************** *)
 (* Let [F : A x Zn -> G] defined as [F (a,z) = f a + z x g] be an epsilon- *)
 (* admissible encoding v2 with [epsilon = (1 - 1/alpha)^Tmax] and let      *)
 (* [H:M -> A x Z] be a random oracle. Then [F o H] is                      *)
 (* [(q, 2q(1-1/alpha)^Tmax)]-indifferentiable from a random oracle into [G]*)  
 (* *********************************************************************** *)

 Definition Hi :=
  [ 
   a' <$- A; 
   z <$- Zn;
   ret'' <- some (a'|z); 
   r <- f_ a' |+| z |*| gen 
  ].
 
 Definition Hf := 
  [ 
   r <$- G; 
   ret'' <c- InvF with {r}; 
   a' <- Efst (Proj ret''); 
   z <- Esnd (Proj ret'') 
  ].


 Lemma body_loop2_range: forall k (m: Mem.t k),
  E.eval_expr cond m ->
  range (fun m' =>
   EP k ((TMax +! 1%nat -! i) <! E.eval_expr (TMax +! 1%nat -! i) m) m')
  ([[ [ 
   i <- i +! 1%nat; 
   z <$-Zn; 
   x <- r'' |-| z |*| gen;
   a <c- Invf_v2 with {x} 
  ] ]] E'' m).
 Proof.
  intros k m Hm f H_f.
  elim_assign.
  rewrite (@Modify_deno_elim E'' {{a,x,z}} 
   [ z <$-Zn; x <- r'' |-| z |*| gen; a <c- Invf_v2 with {x} ]); 
  [ | apply modify_correct with (refl1_info i_E''E'') Vset.empty; apply eq_refl].
  match goal with |- _ == fmonot (mu ?d) _ => rewrite <-(mu_zero d) end.
  apply mu_stable_eq; unfold fzero; refine (ford_eq_intro _); intro m'.
  apply H_f.
  generalize Hm; unfold cond, EP; clear Hm.
  expr_simpl; mem_upd_simpl.
  rewrite is_true_andb; intros [Hm _].
  apply leb_correct; apply leb_complete in Hm; omega.
 Qed.

 Lemma lossless_InvF_body : lossless E'' InvF_body.
 Proof.
  unfold InvF_body.
  match goal with 
   |- lossless _ [?i1;?i2;?i3;?i4;?i5;?i6;?i7;?i8] => 
    change [i1;i2;i3;i4;i5;i6;i7;i8] with 
     ([i1;i2;i3;i4;i5] ++ ([i6] ++ [i7;i8]))
  end.
  apply lossless_app; [ | apply lossless_app ].
  apply is_lossless_correct with (refl1_info (empty_info E'' E'')); 
   vm_compute; trivial.
  
  apply lossless_bounded_while with (TMax +! 1%nat -! i).
  apply body_loop2_range.
  apply is_lossless_correct with (refl2_info i_E''E''); apply eq_refl.
  apply is_lossless_correct with (refl2_info i_E''E''); apply eq_refl.
 Qed.

 Lemma lossless_InvF_in_rnd: lossless E'' [ r <$- G; ret'' <c- InvF with {r} ].
 Proof.
  apply lossless_cons; [ apply lossless_random | ].
  apply lossless_call; change (lossless E'' InvF_body).
  apply lossless_InvF_body.
 Qed.



 (* ******************************  CLAIM 3.1  **************************** *)
 (* Let [F] be an [epsilon]-admissible enconding v2, with inverter [InvF].  *)
 (* Then the probability that [InvF] fails to invert a uniformly chosen     *)
 (* value is upper bounded by [epsilon]                                     *)
 (* *********************************************************************** *)
 
 Lemma Pr_InvF_failure : forall k (m:Mem.t k), 
  Pr E'' [ r <$- G; ret'' <c- InvF with {r} ] m (EP k (!(IsSome ret''))) <= 
  (1 - one_over_alpha k)^(S (T_poly k)).
 Proof.
  intros.
  transitivity 
   (Pr E'' [ r <$- G; ret'' <c- InvF with {r} ] m (negP (EP k (IsSome ret'')))); 
   [ trivial | ].
  rewrite Pr_neg; [rewrite <- Uminus_one_left | apply lossless_InvF_in_rnd].
  assert 
   (H:Pr E' [a' <$- A; z <$- Zn; ret'' <- some (a'|z)] m
    (EP k (IsSome ret'')) == 1).
  assert (Hloss: lossless E' [a' <$-A; z <$-Zn; ret'' <- some (a' | z)]) by
   (apply is_lossless_correct with (refl1_info i_E'E''); vm_compute; trivial).
  rewrite <-(Hloss _ m).
  apply equiv_deno with Meq (req_mem_rel Vset.empty (EP1 (IsSome ret''))).
  eqobsrel_tail; expr_simpl; intros _ _ _ _ _ _ _ _; trivial.
  unfold EP1, charfun, restr, EP; intros  m1 m2 (_,H); rewrite H; trivial.
  trivial.
  rewrite (Uminus_triangle_ineq2 _ _ 
   (Pr E' [ a' <$- A; z <$- Zn; ret'' <- some (a'|z)] m (EP k (IsSome ret''))));
  trivial.
  rewrite H, Uminus_eq, Uplus_zero_right,<-H; rewrite H at 2.
  match goal with 
   |- ?x - ?y <= _ => transitivity (Uabs_diff y x); [ unfold Uabs_diff; auto | ] 
  end.
  apply Inv_F_distance_from_random.
  intros m1 m2 H'; unfold charfun, restr, EP.
  rewrite (@depend_only_fv_expr T.Bool (IsSome ret'') _ m1 m2); [ | apply H' ].
  case_eq (@E.eval_expr _ T.Bool (IsSome ret'') m2); trivial.
  apply req_mem_empty.
  rewrite H; trivial.
 Qed.


 (* ******************************  CLAIM 3.2  **************************** *)
 (* Let [F] be an [epsilon]-admissible enconding v2, with inverter [InvF].  *)
 (* Then, [prg_SD {{ }} Hi Hf {{r,a,a'}} (2*epsilon)].                      *)
 (* This corresponds to [Lemma 2] in Section 3.1 of the paper               *)
 (* *********************************************************************** *)

 (* Augment [Hi] with some dead code *)
 Let H_1 := 
  [ a' <$- A; z <$- Zn; ret'' <- some (a'|z) ] ++
  [
   bad <- false;
   If !(IsSome ret'') then
    [ bad <- true; r <$- G; a' <- Efst (Proj ret''); z <- Esnd (Proj ret'') ]
   else
    [ a' <- Efst (Proj ret''); z <- Esnd (Proj ret'');  r <- f_ a' |+| z |*| gen ]
  ].

 Lemma Hi_H1: EqObs Vset.empty E' Hi E' H_1 {{r,ret'',a',z}}.
 Proof.
  unfold Hi, H_1.
  apply EqObs_trans with E' [ a' <$- A; z <$- Zn; ret'' <- some (a'|z); 
   a' <- Efst (Proj ret''); z <- Esnd (Proj ret''); r <- f_ a' |+| z |*| gen ].
  apply equiv_app with 
   (Q :=req_mem_rel {{ret'',a',z}} (EP2 (a' =?=  Efst (Proj ret'')) /-\ EP2 (z =?= Esnd (Proj ret''))))
   (c1:=[a' <$-A; z <$- Zn; ret'' <- some (a'|z)]) (c2:=[r <- f_ a' |+| z |*| gen]) 
   (c3:=[a' <$-A; z <$- Zn; ret'' <- some (a'|z)]) (c4:=[ a' <- Efst (Proj ret''); z <- Esnd (Proj ret''); r <- f_ a' |+| z |*| gen]); 
   [ deadcode; unfold Hi; eqobsrel_tail; simpl; unfold O.eval_op, implMR; simpl; 
    intros; split; [ apply A_eqb_refl | apply nat_eqb_refl] | ].
  eqobs_tl.
  apply equiv_app with 
   (Q :=req_mem_rel {{ret'',a',z}} (EP2 (z =?= Esnd (Proj ret''))))
   (c1:= @nil I.instr) (c2:=@nil I.instr) 
   (c3:=[a' <- Efst (Proj ret'')]) (c4:=[ z <- Esnd (Proj ret'') ]).
  eapply equiv_strengthen; [ | apply equiv_assign_r ].     
  intros k m1 m2 (H1,(H2,H3)); split.
  intros t x Hx; Vset_mem_inversion Hx; subst; mem_upd_simpl; try (apply H1; trivial).
  rewrite <- (proj2 (expr_eval_eq m2 a' (Efst (Proj ret''))) H2); apply H1; trivial.
  expr_simpl.
  eapply equiv_strengthen; [ | apply equiv_assign_r ].     
  intros k m1 m2 (H1,H2); 
   change (kreq_mem {{ret'',a',z}} m1 (m2 {!z <-- E.eval_expr Esnd (Proj ret'') m2!})).
  intros t x Hx; Vset_mem_inversion Hx; subst;  mem_upd_simpl; try (apply H1; trivial).
  setoid_rewrite <- (proj2 (expr_eval_eq m2 z (Esnd (Proj ret''))) H2); apply H1; trivial.
  deadcode.
  apply equiv_app with 
   (c1:= [ a' <$- A; z <$- Zn; ret'' <- some (a'|z) ]) (c2 := [ a' <- Efst (Proj ret''); z <- Esnd (Proj ret'');  r <- f_ a' |+| z |*| gen ])
   (c3:= [ a' <$- A; z <$- Zn; ret'' <- some (a'|z) ]) (c4 := [ If !(IsSome ret'')
    then [r <$-G; a' <- Efst (Proj ret''); z <- Esnd (Proj ret'')]
    else [ a' <- Efst (Proj ret''); z <- Esnd (Proj ret''); r <- f_ a' |+| z |*| gen ] ])
   (Q :=req_mem_rel {{ret'', a',z}} (EP2 (IsSome ret''))).
  eqobsrel_tail; simpl; unfold O.eval_op, implMR; simpl; intros; split; trivial.
  cp_test (IsSome ret'').
  deadcode; eqobs_in.
  apply equiv_False; unfold notR; intros k m1 m2 [ [_ H]  [_ H'] ]; tauto.    
 Qed.
      

 (* Use the fact that [f] is a weak encoding --lossy transformation-- *)
 Let H_2 := 
  [ r <$- G; ret'' <c- InvF with {r} ] ++
  [
   bad <- false;
   If !(IsSome ret'') then
    [ bad <- true; r <$- G;  a' <- Efst (Proj ret''); z <- Esnd (Proj ret'') ]
   else
    [ a' <- Efst (Proj ret''); z <- Esnd (Proj ret''); r <- f_ a' |+| z |*| gen ]
  ].

 Lemma H1_H2: prg_SD 
  (kreq_mem Vset.empty) 
  E' H_1 
  E'' H_2 
  (kreq_mem {{r,ret'',a',z}})
  (fun k : nat => (1 - one_over_alpha k)^S (T_poly k)).
 Proof.
  unfold H_1, H_2, prg_SD; intros.
  repeat rewrite deno_app_elim.
  rewrite Uabs_diff_sym.
  apply Inv_F_distance_from_random.
  intros m1' m2' Hm'.
  apply equiv_deno with (kreq_mem {{ret''}}) (kreq_mem {{r, ret'', a',z}}).
  deadcode; cp_test (IsSome ret''); eqobs_in.
  intros m1'' m2'' Hm''; symmetry; apply (H _ _ (req_mem_sym Hm'')). 
  trivial.
  apply req_mem_empty.
 Qed.
        

 (* Eliminate the resampling of [r] when the adversary fails 
    --lossy transformation-- *)
 Let H_3 := 
  [ r <$- G; ret'' <c- InvF with {r} ] ++
  [
   bad <- false;
   If !(IsSome ret'') then
    [ bad <- true;  a' <- Efst (Proj ret''); z <- Esnd (Proj ret'') ] 
   else
    [ a' <- Efst (Proj ret''); z <- Esnd (Proj ret''); r <- f_ a' |+| z |*| gen ]
  ].


 Definition i_upto_E''E'' :=
  let i_empty   := empty_upto_info bad E'' E'' in
  let i_Invf_v1 := add_upto_info i_empty Invf_v1 in 
  let i_Invf_v2 := add_upto_info i_Invf_v1 Invf_v2 in i_Invf_v2.

 Lemma H2_H3: forall k,
  @rtriple k E'' E'' H_2 H_3 (fun _ => (1 - one_over_alpha k)^S (T_poly k)).  
 Proof.
  intros k; unfold H_2, H_3.
  apply rtriple_weaken with 
   (fun m => Pr E'' [r <$-G; ret'' <c- InvF with {r} ] m (EP k (!(IsSome ret''))) + (fzero _) m).
  unfold fzero; refine (ford_le_intro _); intro m; Usimpl; apply Pr_InvF_failure.  
  apply rtriple_app.
  apply rtriple_refl_zero.
  intros m f.
  repeat elim_assign; simpl (m {!bad <-- E.eval_expr false m!}).
  rewrite (@upto_bad_GSD _ E'' E'' bad is_true_true i_upto_E''E''); [ | apply eq_refl |
   apply is_lossless_correct with (pi := refl2_info i_E''E''); apply eq_refl ].
  unfold Pr, EP, charfun, restr; rewrite deno_cond_elim.
  rewrite (@depend_only_fv_expr T.Bool (!(IsSome ret'')) _ m (m {!bad <-- false!})); 
   [ | apply req_mem_upd_disjoint; trivial ].
  case_eq (@E.eval_expr _ T.Bool (!(IsSome ret'')) (m {!bad <-- false!})); intro Heq.
  trivial.
  repeat elim_assign; rewrite deno_nil_elim; expr_simpl.
 Qed.

 Lemma H3_Hf: EqObs Vset.empty E'' H_3 E'' Hf {{r,ret'',a',z}}.
 Proof.
  unfold H_3, Hf, app.
  apply equiv_weaken with (kreq_mem {{a',z,r,ret''}}).
  apply (@implMR_kreq_mem_subset {{a',z,r,ret''}} {{r,ret'',a',z}}); apply eq_refl.
  deadcode i_E''E''.
  apply equiv_app with
   (c1:=[r <$-G;ret'' <c- InvF with {r} ]) (c2:=[ If !(IsSome ret'') 
    then [ a' <- Efst (Proj ret''); z <- Esnd (Proj ret'')]
    else [ a' <- Efst (Proj ret''); z <- Esnd (Proj ret''); r <- f_ a' |+| z |*| gen ] ])
   (c3:= [r <$-G; ret'' <c- InvF with {r} ]) (c4:=[  a' <- Efst (Proj ret''); z <- Esnd (Proj ret'') ])
   (Q:= req_mem_rel {{ret'',r}} (EP1  ((IsSome ret'') ==> (r =?= f_ (Efst (Proj ret''))  |+| ( Esnd (Proj ret'')) |*| gen )))).
  apply equiv_strengthen_range.
  auto.
  apply lossless_InvF_in_rnd.
  apply InvF_is_partial_inverter.
  eqobs_in i_E''E''.
  cp_test_l (IsSome ret'').
  (* case [IsSome ret''] *)
  apply equiv_app with
   (c1:= [a' <- Efst (Proj ret''); z <- Esnd (Proj ret'')]) 
   (c2:= [ r <- f_ Efst (Proj ret'') |+| Esnd (Proj ret'') |*| gen ])
   (c3:= [a' <- Efst (Proj ret''); z <- Esnd (Proj ret'')])    
   (c4:= @nil I.instr)
   (Q:= req_mem_rel {{a',z,r, ret''}} (EP1 ((IsSome ret'') ==> 
    (r =?= f_ (Efst (Proj ret''))  |+| ( Esnd (Proj ret'')) |*| gen )) /-\ EP1 (IsSome ret''))).
  eqobsrel_tail; expr_simpl; intros k m1 m2 (H1,(H2,H3)); split; trivial.
  eapply equiv_strengthen; [ | apply equiv_assign_l ].
  intros k m1 m2 (H,(H',H'')).
  intros t x Hx; Vset_mem_inversion Hx; subst; mem_upd_simpl; (try apply H; trivial).
  rewrite <-(proj2 (expr_eval_eq m1 r (f_ Efst (Proj ret'') |+| Esnd (Proj ret'') |*| gen))
   (expr_modus_ponens _ _ _ H' H'')); apply H; trivial.
  (* case [!IsSome a] *)
  unfold req_mem_rel; repeat rewrite proj1_MR; eqobs_in.
 Qed.


 Lemma Hi_Hf :
  prg_SD (kreq_mem Vset.empty) E' Hi E'' Hf (kreq_mem {{r,ret'',a',z}}) 
  (fplus (fun k => (1 - one_over_alpha k)^S (T_poly k)) 
         (fun k => (1 - one_over_alpha k)^S (T_poly k))).
 Proof.
  rewrite <-(fplus_fzero_l (fplus _ _)).
  apply prg_SD_trans_PER with E' H_1; try apply req_mem_PER.
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with (1:=Hi_H1); trivial; apply req_mem_empty.

  apply prg_SD_trans_PER with E'' H_2; try apply req_mem_PER.
  apply H1_H2.
    
  rewrite <-(fplus_fzero_r (fun k : nat => (1 - one_over_alpha k) ^ S (T_poly k))).
  apply prg_SD_trans_PER with E'' H_3; try apply req_mem_PER.

  rewrite <-(fplus_fzero_l (fun k : nat => (1 - one_over_alpha k) ^ S (T_poly k))).
  apply prg_trans_Meq_Meq.
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with (kreq_mem Vset.empty) (kreq_mem {{r, ret'', a', z}}); auto.
  eqobs_in i_E''E''.
  apply rtriple_deno; exact H2_H3.  
  
  unfold prg_SD, fzero; intros; apply Oeq_le; rewrite Uabs_diff_zero.
  apply equiv_deno with (1:=H3_Hf); trivial; apply req_mem_empty.
 Qed.
   

 Theorem Hi_Hf_Meq: forall k, 
  @rtriple k E' E'' Hi Hf (fun _ => 2 */ (1 - one_over_alpha k)^S (T_poly k)).
 Proof.
  intros k m f.
  rewrite (@Modify_deno_elim E' {{r,ret'',z,a'}} Hi); 
   [ | apply modify_correct with (refl1_info i_E'E'') Vset.empty; apply eq_refl ].
  rewrite (@Modify_deno_elim E'' {{z,a',ret'',r}} Hf); 
   [ | apply modify_correct with (refl1_info i_E''E'') Vset.empty; apply eq_refl ].
  apply Hi_Hf.
  intros m1 m2 Hm.
  assert (Meq _ (m {!{{r, ret'',z, a'}} <<- m1!}) (m {!{{z,a',ret'',r}} <<- m2!})).
  assert ({{r, ret'',z, a'}} [=] {{z,a',ret'',r}}) by (apply eq_refl).
  apply Mem.eq_leibniz; red; intros [t v].
  case_eq (Vset.mem v {{r, ret'', z, a'}}); intro Hv.
  rewrite update_mem_in, update_mem_in; [ | rewrite <-H | ]; trivial.
  apply Hm; apply Vset.subset_correct with (2:=Hv); apply eq_refl.
  rewrite update_mem_notin, update_mem_notin; [ | rewrite <-H | ]; trivial.
  rewrite Hv; discriminate.
  rewrite Hv; discriminate.
  rewrite H; trivial.
  trivial.
 Qed.


 (* ******************************  CLAIM 3.3 ****************************** *)
 (* Let [F:A * Z -> G] be an epsilon-admissible enconding v2, with           *)
 (* inverter algorithm [InvF]. Then, an adversary making at most [q] queries *) 
 (* can tell appart [Hi] from [Hf] with probability at most [2q epsilon].    *)
 (****************************************************************************)

 Section ADVERSARY.

  Definition H_params : var_decl (Proc.targs H) := dcons _ m' (dnil _).
  Definition H_res := L[{m'}].

  (* Adversary declaration *)
  Definition A_params : var_decl (Proc.targs A) := dnil _.
  Variable A_res : E.expr T.Bool.
  Variable A_body : cmd.

  (* Resulting enviromnets contain  [InvF], [H], and [A] 
     (since [E''] contains info about [InvF]) *)
  Definition mkEnv H_body := 
   let Ef := add_decl E'' H H_params (eq_refl true) H_body H_res in
    add_decl Ef A A_params (eq_refl true) A_body A_res.

  (* Initial Game *)
  Definition Or_i :=
   [
    If !(m' in_dom L) _then
    [
     If (Elen L <! (qQ1 +! qQ2)) then 
      (Hi ++ [L <- (m' | (ret''|r)) |::| L])
     else
      (bad <- true) :: 
      (Hi ++ [L <- (m' | (ret''|r)) |::| L])
    ]
   ].

  Definition Ei := mkEnv Or_i.

  Definition G := [ L <- Nil _; b <c- A with {} ].

  Definition Ev := b && (Elen L <=! (qQ1 +! qQ2)).


  (* Final Game *)
  (* TODO: elim assignmet to a' in Hf *)
  Definition Or_f :=
   [
    If !(m' in_dom L) _then
    [
     If (Elen L <! (qQ1 +! qQ2)) then 
      (Hf ++ [L <- (m' | (ret''|r)) |::| L])
     else
      (bad <- true) :: 
      (Hf ++ [L <- (m' | (ret''|r)) |::| L])                          
    ]
   ].

  Definition Ef := mkEnv Or_f.


  (* Adversary specification *)
  Definition PrOrcl := PrSet.singleton (BProc.mkP H).
  Definition PrPriv := PrSet.empty.

  Definition Gadv  := Vset.empty.
  Definition Gcomm := Vset.empty.

  Hypothesis A_wf : WFAdv PrOrcl PrPriv Gadv Gcomm Ei A.

  Hypothesis A_slossless : forall Fbody,
   (forall O, PrSet.mem O PrOrcl -> 
    slossless_c (mkEnv Fbody) (proc_body (mkEnv Fbody) (BProc.p_name O))) -> 
   slossless_c (mkEnv Fbody) A_body.

  Lemma EqAD : forall H_body1 H_body2, 
   Eq_adv_decl PrOrcl PrPriv (mkEnv H_body1) (mkEnv H_body2).
  Proof.
   unfold Eq_adv_decl, mkEnv; intros.
   unfold proc_params, proc_body, proc_res.
   generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
   destruct (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros.
   inversion H1; simpl; auto.
   repeat rewrite add_decl_other_mk; try tauto;
    intros Heq; 
     (apply H; rewrite <- Heq; vm_compute; reflexivity)
     || (apply H0; rewrite <- Heq; vm_compute; reflexivity).
  Qed.

  Lemma EqOP : forall H_body1 H_body2, 
   Eq_orcl_params PrOrcl (mkEnv H_body1) (mkEnv H_body2).
  Proof.
   unfold Eq_orcl_params, mkEnv; intros.
   unfold PrOrcl in H.
   apply PrSet.singleton_complete in H; inversion H; simpl.
   vm_compute; trivial.
  Qed.

  Lemma EqOR : forall H_body1 H_body2 t (p:Proc.proc t), 
   PrSet.mem (BProc.mkP p) PrOrcl -> 
   proc_res (mkEnv H_body1) p = proc_res (mkEnv H_body2) p.
  Proof.
   unfold mkEnv; intros.
   unfold PrOrcl in H.
   apply PrSet.singleton_complete in H; inversion H; simpl.
   vm_compute; trivial.
  Qed.

  (** The adversary is well-formed in any environment constructed with [mkEnv].
      This follows from the adversary being well-formed in [Ei] *)
  Lemma A_wf_E : forall H_body,
   WFAdv PrOrcl PrPriv Gadv Gcomm (mkEnv H_body) A.
  Proof.
   intros; apply WFAdv_trans with (5:=A_wf).
   unfold Ei; apply EqOP.
   unfold Ei; apply EqAD.
   vm_compute; intro; discriminate.
   vm_compute; intro; discriminate.
  Qed.


  (** Proof of Main Lemma *)

  Definition Or_i' :=
   [
    If !(m' in_dom L) _then
    [
     If (Elen L <! (qQ1 +! qQ2)) then 
      (Hi ++ [L <- (m' | (ret''|r)) |::| L])
     else
      (bad <- true) :: 
      (Hf ++ [L <- (m' | (ret''|r)) |::| L])                          
    ]
   ].

  Definition Ei' := mkEnv Or_i'.

  Definition  i_InvF_Ei_Ei' :=
   let i_empty   := empty_info Ei Ei' in
   let i_InvF_v1 := add_refl_info_rm Invf_v1 Vset.empty Vset.empty i_empty in
   let i_InvF_v2 := add_refl_info_rm Invf_v2 Vset.empty Vset.empty i_InvF_v1 in
   let i_InvF    := add_refl_info_rm InvF Vset.empty Vset.empty i_InvF_v2 in
    i_InvF.

  (* Transition from Ei to Ei' *)

  Definition I := EP1 (Elen L <=! (qQ1 +! qQ2) ==> !bad).
 
  Lemma dep_I: depend_only_rel I {{bad,L}} Vset.empty.
  Proof.
   apply depend_only_EP1.
  Qed.

  Lemma dec_I: decMR I.
  Proof.
   unfold I; auto.
  Qed.

  Lemma H_I : 
   EqObsInv I 
   {{m',L}}
   Ei Or_i 
   Ei Or_i
   {{m',L}}.
  Proof.
   cp_test (m' in_dom L).
 
   eqobsrel_tail; unfold implMR, andR; intros.
   expr_simpl.
   decompose [and] H; trivial.
   
   cp_test (Elen L <! (qQ1 +! qQ2)).
  
   unfold I; eqobsrel_tail; unfold implMR, andR; expr_simpl; intros.
   decompose [and] H; clear H H5 H7 H8.
   apply leb_complete in H3; destruct H3.
   rewrite is_true_impb in H4; rewrite H4.
   rewrite impb_true_r; trivial.
   apply leb_correct; auto with arith.
   apply is_true_impb; intro Hle.
   rewrite is_true_impb in H4; apply H4.
   apply leb_correct; apply leb_complete in Hle; auto with arith.
 
   unfold I; eqobsrel_tail; unfold implMR, andR; expr_simpl; intros.
   decompose [and] H; clear H H5 H7 H8.
   apply not_is_true_false in H3; apply leb_complete_conv in H3.
   apply is_true_impb; intro Hle.
   destruct (q1_poly k + q2_poly k)%nat; trivial.
   apply leb_complete in Hle.
   match goal with
    | H3 : (_ < ?len + 1)%nat |- _ => assert (n < len)%nat by omega
   end.
   exfalso; destruct H; omega.
  Qed.
 
  Definition i_Ei_Ei_empty: eq_inv_info I Ei Ei.
   refine (@empty_inv_info I _ _ _ _ _ _ _).
   apply dep_I. 
   vm_compute; trivial.
   apply dec_I.
  Defined.

  Definition i_Ei_Ei_I :=
   let i_empty := i_Ei_Ei_empty in
   let i_Or    := add_info H Vset.empty Vset.empty i_empty H_I in 
   let i_Adv   := add_adv_info_false (EqAD _ _ ) (A_wf_E _) i_Or in i_Adv.

  Lemma Pr_G : forall k (m:Mem.t k), 
   Pr Ei G m (EP k Ev) == 
   Pr Ei ((bad <- false) :: G) m (EP k Ev [&&] (negP (EP k bad))).
  Proof.
   intros.
   symmetry; apply equiv_deno with Meq (req_mem_rel {{L,b}} I).
   eqobs_tl i_Ei_Ei_I.
   unfold I; eqobsrel_tail; unfold implMR; expr_simpl.
   
   unfold I; intros m1 m2 [Heq H]; unfold charfun, restr, EP, fone.
   apply req_mem_sym in Heq.
   rewrite (@depend_only_fv_expr T.Bool Ev _ _ _ Heq).
   generalize H; unfold Ev, EP1, negP, andP, negb, andb.
   simpl; unfold O.eval_op; simpl; unfold andb; intros.
   repeat match goal with |- context[if ?b then _ else _] => case_eq b end;
    try discriminate; trivial.
   rewrite is_true_impb in H0; intros.
   rewrite H1 in H0; simpl in H0; discriminate H0; trivial.
   trivial.
  Qed.


  Definition Ile := (EP1 (bad =?= true) /-\ ~- EP1 (Elen L <! (qQ1 +! qQ2))).
 
  Lemma dep_Ile: depend_only_rel Ile 
   (Vset.union {{bad}} {{L}}) (Vset.union Vset.empty Vset.empty).
  Proof.
   apply depend_only_andR.
   apply depend_only_EP1.
   apply depend_only_notR.
   apply depend_only_EP1.
  Qed.

  Lemma dec_Ile: decMR Ile.
  Proof.
   unfold Ile; auto.
  Qed.

  Definition i_Ei'_Ei'_empty : eq_inv_info Ile Ei' Ei'.
   refine (@empty_inv_info Ile _ _ _ _ _ _ _).
   apply dep_Ile. 
   vm_compute; trivial.
   apply dec_Ile.
  Defined.

  Definition i_Ei'_Ei'_InvF :=
   let i_empty   := i_Ei'_Ei'_empty in
   let i_InvF_v1 := add_refl_info_rm Invf_v1 Vset.empty Vset.empty i_empty in
   let i_InvF_v2 := add_refl_info_rm Invf_v2 Vset.empty Vset.empty i_InvF_v1 in
   let i_InvF    := add_refl_info_rm InvF Vset.empty Vset.empty i_InvF_v2 in
    i_InvF.

  Eval vm_compute in (print_info i_Ei'_Ei'_InvF InvF).

  Lemma EqObs_H : 
   EqObsInv I
   {{m',L}}
   Ei' Or_i' 
   Ei' Or_i'
   {{m',L}}.
  Proof.
   cp_test (m' in_dom L).
   unfold I; eqobsrel_tail; unfold implMR; expr_simpl; intuition.
   
   cp_test (Elen L <! (qQ1 +! qQ2)).

   unfold I; eqobsrel_tail; unfold implMR; expr_simpl; intros.
   decompose [and] H; clear H.
   apply is_true_impb; intros _.
   rewrite is_true_impb in H4; apply H4.
   apply leb_complete in H3; apply leb_correct; omega.

   apply equiv_cons with
    (req_mem_rel {{m', L, bad}} 
     (EP1 (bad =?= true) /-\ ~- EP1 (Elen L <! (qQ1 +! qQ2)))).
   eapply equiv_strengthen; [ | apply equiv_assign].
   unfold I, req_mem_rel, upd_para, andR, notR, EP1; 
    simpl E.eval_expr; unfold O.eval_op; simpl T.app_op; intros.
   decompose [and] H; clear H; repeat split.
   intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl; auto.
   mem_upd_simpl.
   apply not_is_true_false; apply leb_correct_conv.
   apply not_is_true_false in H3; apply leb_complete_conv in H3.
   mem_upd_simpl; omega.

   match goal with
   |- equiv _ _ ?c1 _ ?c2 _ => rewrite <- (firstn_skipn 2%nat c1) 
   end.
   apply equiv_app with 
    (req_mem_rel {{m', L, bad, r, ret''}} 
     (EP1 (bad =?= true) /-\ ~- EP1 (Elen L <! (qQ1 +! qQ2))) ).
   simpl.
   apply equiv_strengthen with (req_mem_rel {{m',L,bad}} Ile); trivial.
   apply equiv_weaken with (req_mem_rel {{m',L,bad,r,ret''}} Ile); trivial.
   eqobs_in i_Ei'_Ei'_InvF.

   simpl.
   unfold I; eqobsrel_tail; unfold implMR; expr_simpl.
   intros; decompose [and] H; clear H.
   apply is_true_impb; intros Hle.
   apply not_is_true_false in H3; apply leb_complete_conv in H3.
   destruct (q1_poly k + q2_poly k)%nat.
   discriminate.
   exfalso.
   apply leb_complete in Hle.
   rewrite plus_comm in H3; apply lt_S_n in H3.
   assert (n < n)%nat. 
   apply lt_le_trans with (length (m1 L)); trivial.
   omega.
  Qed.

  Definition i_Ei'_Ei'_I_empty : eq_inv_info I Ei' Ei'.
   refine (@empty_inv_info I _ _ _ _ _ _ _).
   apply dep_I. 
   vm_compute; trivial.
   apply dec_I.
  Defined.

  Definition i_Ei'_Ei' :=
   let i_empty   := i_Ei'_Ei'_I_empty in
   let i_InvF_v1 := add_refl_info_rm Invf_v1 Vset.empty Vset.empty i_empty in
   let i_InvF_v2 := add_refl_info_rm Invf_v2 Vset.empty Vset.empty i_InvF_v1 in
   let i_InvF    := add_refl_info_rm InvF Vset.empty Vset.empty i_InvF_v2 in
   let i_H       := add_info H Vset.empty Vset.empty i_InvF EqObs_H in
   let i_A       := add_adv_info_false (EqAD _ _ ) (A_wf_E _) i_H in i_A.

  Lemma Pr_G' : forall k (m:Mem.t k), 
   Pr Ei' G m (EP k Ev) == 
   Pr Ei' ((bad <- false) :: G) m (EP k Ev [&&] (negP (EP k bad))).
  Proof.
   intros.
   symmetry; apply equiv_deno with Meq (req_mem_rel {{L,b}} I).
   eqobs_tl i_Ei'_Ei'.
   unfold I; eqobsrel_tail; unfold implMR; expr_simpl.
   
   unfold I; intros m1 m2 [Heq H]; unfold charfun, restr, EP, fone.
   apply req_mem_sym in Heq.
   rewrite (@depend_only_fv_expr T.Bool Ev _ _ _ Heq).
   generalize H; unfold Ev, EP1, negP, andP, negb, andb.
   simpl; unfold O.eval_op; simpl; unfold andb; intros.
   repeat match goal with |- context[if ?b then _ else _] => case_eq b end;
    try discriminate; trivial.
   rewrite is_true_impb in H0; intros.
   rewrite H1 in H0; simpl in H0; discriminate H0; trivial.
   trivial.
  Qed.


  Definition  i_Ei_Ei'_upto :=
   let i_empty   := empty_upto_info bad Ei Ei' in
   let i_Invf_v1 := add_upto_info i_empty Invf_v1 in
   let i_Invf_v2 := add_upto_info i_Invf_v1 Invf_v2 in
   let i_InvF    := add_upto_info i_Invf_v2 InvF in
   let i_Or      := add_upto_info i_InvF H in
   let i_Adv     := add_adv_upto_info i_Or (EqAD _ _ ) (EqOP _ _) (A_wf_E _) in 
    i_Adv.

  Lemma Pr_i_i': forall k (m:Mem.t k),
   Pr Ei G m (EP k Ev) == Pr Ei' G m (EP k Ev).
  Proof.
   intros.
   rewrite Pr_G, Pr_G'.
   unfold Pr.
   rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
   rewrite deno_cons_elim, Mlet_simpl, deno_assign_elim.
   apply upto_bad_and_neg with i_Ei_Ei'_upto; vm_compute; trivial.
  Qed.

 
  (* Transition from Ei' to Ef *)
  Section Rtriple.

   Variable k : nat.

   Definition h n := 
    if leb (S n) (q1_poly k + q2_poly k) 
    then 2 */ ((1 - one_over_alpha k)^(S (T_poly k))) else 0.

   Definition Fb c := fun m:Mem.t k => 
    mu ([[c]] Ef m) 
    (fun m' => sum_f (E.eval_expr (Elen L) m) (E.eval_expr (Elen L) m') h).

   Definition  i_Ef_Ef :=
    let i_empty   := empty_info Ef Ef in
    let i_InvF_v1 := add_refl_info_rm Invf_v1 Vset.empty Vset.empty i_empty in
    let i_InvF_v2 := add_refl_info_rm Invf_v2 Vset.empty Vset.empty i_InvF_v1 in
    let i_InvF    := add_refl_info_rm InvF Vset.empty Vset.empty i_InvF_v2 in 
     i_InvF.

   Definition  i_Ef_E'' :=
    let i_empty   := empty_info Ef E'' in
    let i_InvF_v1 := add_refl_info_rm Invf_v1 Vset.empty Vset.empty i_empty in
    let i_InvF_v2 := add_refl_info_rm Invf_v2 Vset.empty Vset.empty i_InvF_v1 in
    let i_InvF    := add_refl_info_rm InvF Vset.empty Vset.empty i_InvF_v2 in 
     i_InvF.

   Definition  i_Ei'_Ef :=
    let i_empty   := empty_info Ei' Ef in
    let i_InvF_v1 := add_refl_info_rm Invf_v1 Vset.empty Vset.empty i_empty in
    let i_InvF_v2 := add_refl_info_rm Invf_v2 Vset.empty Vset.empty i_InvF_v1 in
    let i_InvF    := add_refl_info_rm InvF Vset.empty Vset.empty i_InvF_v2 in 
     i_InvF.

   Lemma Orc_distance: rtriple Ef Ei' Or_f Or_i' (Fb Or_f).
   Proof.
    intros m f; unfold Or_i', Or_f, Fb.
    assert (H: forall E g, Oeq (O:=Mem.t k -o> U) (fun x =>
     mu ([[nil]] E x) (fun x' => mu ([[nil]] E x') g)) g) by 
    (intros; refine (ford_eq_intro _); intro; 
     repeat rewrite deno_nil_elim; trivial).
    elim_cond (!(m' in_dom L)) m.
    
    (* case [~(RO.m in_dom L)] *)
    elim_cond ( Elen L <! (qQ1 +! qQ2)) m; 
    repeat rewrite (mu_stable_eq _ _ _ (H _ _)).

    (* case [|L| < (qQ1 +! qQ2) ] *)
    rewrite (@rtriple_app _ _ _ _ _ _ _ (fzero (Mem.t k)) 
     (fun _ => 2 */ ((1 - one_over_alpha k)^(S (T_poly k))))).
    rewrite mu_zero, deno_app_elim; Usimpl.
    match goal with |- _ <= fmonot (mu _) ?F => 
     apply Ole_trans with (fmonot (mu ([[ nil ]] Ef m)) F) 
    end.
    rewrite deno_nil_elim, deno_assign_elim; expr_simpl; simpl length.
    rewrite sum_f_non_empty, <-(Ule_plus_right (h (length (m L)))); trivial.
    unfold h; rewrite leb_correct; trivial.
    apply (leb_complete (length (m L) + 1) (q1_poly k + q2_poly k)) in Hguard0;
     rewrite plus_comm in Hguard0; trivial.
    apply equiv_deno_le with (kreq_mem {{L}}) (kreq_mem {{L}}).

    deadcode i_Ef_Ef.
    apply EqObs_lossless_Modify with (M1:=Vset.empty) (M2:={{r,ret''}}).
    apply lossless_nil.
    intros k0 m0; rewrite <- (lossless_InvF_in_rnd m0).
    apply EqObs_deno with Vset.empty Vset.empty.
    eqobs_in i_Ef_E''.
    trivial.
    trivial.
    apply Modify_nil.
    apply modify_correct with (pi:=refl1_info i_Ef_E'') (X:={{r,ret''}});
     vm_compute; trivial.
    trivial.
    trivial.
    
    intros m1 m2 Hm; repeat rewrite deno_assign_elim; expr_simpl; simpl length. 
    rewrite (Hm _ L); trivial.
    trivial.
    apply rtriple_eq_deno_r with E' Hi; 
     [ union_mod; auto; eqobs_in | ].
    apply rtriple_eq_deno_l with E'' Hf; 
     [ union_mod  i_Ef_E''; auto; eqobs_in  i_Ef_E'' | ].
    apply rtriple_sym; apply Hi_Hf_Meq.

    apply rtriple_eq_deno_r with Ef [L <- (m' | ( ret'' | r)) |::| L ];
     [ union_mod i_Ei'_Ef; auto; eqobs_in i_Ei'_Ef | ].
    apply rtriple_refl_zero.

    (* case [|L| < (qQ1 +! qQ2) ] *)
    set (c:= ((bad <- true) :: Hf ++ [L <- (m' | (ret'' | r)) |::| L])).
    apply (@rtriple_eq_deno_r _ _ Ef _ _ c _ (Fb c)).  
    union_mod i_Ei'_Ef; auto; eqobs_in i_Ei'_Ef.
    apply rtriple_weaken with (fun _:Mem.t k => 0); 
     [ auto | apply rtriple_refl_zero ].
   
    (* case [~(RO.m in_dom L)] *)
    repeat rewrite deno_nil_elim; rewrite Uabs_diff_compat_eq; trivial.
   Qed.

   Lemma Orc_range: forall (m:Mem.t k),
    range (fun m' => (E.eval_expr (Elen L) m <= E.eval_expr (Elen L) m')%nat)
    ([[Or_f]] Ef m).
   Proof.
    intros m f H_f.
    rewrite <-(mu_zero ([[Or_f]] Ef m)).
    apply equiv_deno with (P:=Meq /-\ EP1 ((length (m L)) =?= Elen L))
     (Q:=req_mem_rel {{L}} (EP1 ((length (m L)) <=! Elen L))).
    unfold Or_f, Hf.
    cp_test (m' in_dom L).
    unfold EP1; eqobsrel_tail; simpl; unfold O.eval_op; simpl.
    intros k' m1 m2 [_ [H _] ]; apply leb_correct; 
     rewrite (nat_eqb_true H); trivial.
    set (c1:= [ r <$-G; ret'' <c- InvF with {r}; a' <- Efst (Proj ret''); z <- Esnd (Proj ret'') ]).
    set (c2:= [  L <- (m' | (ret'' | r)) |::| L ]).
    cp_test (Elen L <! (qQ1 +! qQ2)); rewrite proj1_MR, proj1_MR.
          (* case [ |L| < q ] *)
    apply equiv_app with  (Q:=Meq /-\ EP1 (length (m L) =?= Elen L))
     (c1:=c1) (c2:=c2) (c3:=c1) (c4:=c2).
    apply equiv_inv_Modify with {{L}} Vset.empty {{z,a',ret'',r}} {{z,a',ret'',r}} ; auto.
    apply depend_only_EP1.
    apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl.
    apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl. 
    intros.
    apply Mem.eq_leibniz; red; intros t; destruct t.
    destruct (VsetP.mem_dec v {{z,a', ret'', r}}) as [Hv | Hv].
    rewrite update_mem_in, update_mem_in, H0; trivial.
    rewrite update_mem_notin, update_mem_notin, H; trivial.
    apply equiv_weaken with Meq; [ apply (proj2 (andR_trueR_r Meq)) | ].
    apply equiv_eq_mem.
    eqobsrel_tail; expr_simpl; intros k' m1 m2 (H1,H2).
    rewrite <-(nat_eqb_true H2); apply leb_correct; auto.

    (* case [ |L| < q ] *)
    unfold c2.
    apply equiv_app with  (Q:=Meq /-\ EP1 (length (m L) =?= Elen L))
     (c1:=(bad<-true)::c1) (c2:=c2) (c3:=(bad<-true)::c1) (c4:=c2).
    apply equiv_inv_Modify with {{L}} Vset.empty {{z,a',ret'',r,bad}} {{z,a',ret'',r,bad}}; auto.
    apply depend_only_EP1.
    apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl.
    apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl.
    intros.
    apply Mem.eq_leibniz; red; intros t; destruct t.
    destruct (VsetP.mem_dec v {{z,a', ret'', r, bad}}) as [Hv | Hv].
    rewrite update_mem_in, update_mem_in, H0; trivial.
    rewrite update_mem_notin, update_mem_notin, H; trivial.
    apply equiv_weaken with Meq; [ apply (proj2 (andR_trueR_r Meq)) | ].
    apply equiv_eq_mem.
    eqobsrel_tail; expr_simpl; intros k' m1 m2 (H1,H2).
    rewrite <-(nat_eqb_true H2); apply leb_correct; auto.
    unfold EP1; intros m1 m2 [H1m H2m].
    apply H_f.
    generalize (proj2 (eval_le _ _ _) H2m); simpl; unfold O.eval_op; simpl.
    rewrite (H1m _ L); trivial.
    split; [ trivial | refine (nat_eqb_refl _) ].
   Qed.

   Lemma body_loop3_range: forall k (m: Mem.t k),
    E.eval_expr cond m ->
    range (fun m' =>
     EP k ((TMax +! 1%nat -! i) <! E.eval_expr (TMax +! 1%nat -! i) m) m')
    ([[ [ i <- i +! 1%nat; z <$-Zn; x <- r'' |-| z |*| gen; a <c- Invf_v2 with {x} ] ]] Ef m).
   Proof.
    intros k' m Hm f H_f.
    elim_assign.
    rewrite (@Modify_deno_elim Ef {{a,x,z}} [z <$-Zn; x <- r'' |-| z |*| gen; a <c- Invf_v2 with {x} ]); [ | 
     apply modify_correct with (refl1_info i_Ef_Ef) Vset.empty; apply eq_refl ].
    match goal with |- _ == fmonot (mu ?d) _ => rewrite <-(mu_zero d) end.
    apply mu_stable_eq; unfold fzero; refine (ford_eq_intro _); intro m'.
    apply H_f.
    generalize Hm; unfold cond, EP; clear Hm.
    expr_simpl; mem_upd_simpl.
    rewrite is_true_andb; intros [Hm _].
    apply leb_correct; apply leb_complete in Hm; omega.
   Qed.

   Lemma slossless_Hf: slossless_c Ef Hf.
   Proof.
    slossless_tac. 
    change (slossless_c Ef (InvF_body)); slossless_tac.
    apply lossless_bounded_while with (TMax +! 1%nat -! i).
    apply body_loop3_range.
    apply is_lossless_correct with (refl2_info i_Ef_Ef); apply eq_refl.
    change (slossless_c Ef Invf_v2_body); slossless_tac.
    change (slossless_c Ef Invf_v1_body); slossless_tac.
   Qed.

   Lemma slossless_Or_f: slossless_c Ef Or_f.
   Proof.
    apply slossless_cons; [ | apply slossless_nil; apply lossless_nil ].
    apply slossless_cond; [ | apply slossless_nil; apply lossless_nil ].
    apply slossless_cons; [ | apply slossless_nil; apply lossless_nil ].
    apply slossless_cond.
    apply slossless_app.
    apply slossless_Hf.
    apply slossless_cons; [ | apply slossless_nil; apply lossless_nil ].
    constructor; apply lossless_assign.
    apply slossless_cons; [ | apply slossless_app].
    constructor; apply lossless_assign.
    apply slossless_Hf.
    apply slossless_cons; [ | apply slossless_nil; apply lossless_nil ].
    constructor; apply lossless_assign.
   Qed.

   Lemma Pr_Ei'_Ef : forall (m:Mem.t k),
    Uabs_diff (Pr Ei' G m (EP k Ev)) (Pr Ef G m (EP k Ev)) <=
    (q1_poly k + q2_poly k) */ (2 */  (1 - one_over_alpha k)^(S (T_poly k))).
   Proof.
    intros.
    unfold G, Pr.
    repeat elim_assign.
    rewrite Uabs_diff_sym.
    refine (rtriple_adv_cte (EqOP _ _) (EqOR _ _) (EqAD _ _) (depend_only_fv_expr (Elen L)) 
     _ _ (q1_poly k + q2_poly k) _ _ _ _ _ _ _ _ _ _ (m {!L <-- nil!}) _).
    intros x Hx; rewrite <-(Vset.singleton_complete _ _ Hx); trivial.
    intros ? _; apply Vset.empty_spec.
    apply Orc_distance.
    apply Orc_range.
    apply A_slossless.
    intros; apply PrSet.singleton_complete in H; destruct H; simpl;
     change (proc_body (mkEnv Or_f) H) with Or_f.
    apply slossless_Or_f.
    discriminate.
    discriminate.
    apply A_wf_E; intros x Hx; discriminate Hx.
    intros x Hx; discriminate Hx.
   Qed.
  
  End Rtriple.
  
  Theorem security_bound_single_oracle : forall k (m:Mem.t k),
   Uabs_diff (Pr Ei G m (EP k Ev)) (Pr Ef G m (EP k Ev)) <= 
   2 * (q1_poly k + q2_poly k) */ ((1 - one_over_alpha k)^(S (T_poly k))).
  Proof.
   intros.
   rewrite Pr_i_i', Pr_Ei'_Ef, <-Nmult_mult_assoc, mult_comm; trivial.
  Qed.

 End ADVERSARY.

 End THEOREM1.


 Section DECOUPLING.

  
  (** TODO: Change definition of A.default in the semantics to match this *)
  Axiom f_Adef : forall k, ET.f_def (A.default k) = G.g k.

  (* Declaration of adversary A'{Hl,Hr} *)
  Variable A'_body : cmd.
  Variable A'_res : E.expr T.Bool.
  
  Definition Hl_params : var_decl (Proc.targs H) := dcons _ ml (dnil _).
  Definition Hl_res := retl.

  Definition Hr_params : var_decl (Proc.targs H) := dcons _ mr (dnil _).
  Definition Hr_res := retr.
 
  Definition Hil_body' :=
   [
    If !(ml in_dom Ll) then
     [ 
      a' <$- A; 
      z <$- Zn; 
      Ll <- (ml | some (a' | z)) |::| Ll;
      retl <- some (a' | z)  
     ]
    else
     [
      retl <- Ll[{ml}]
     ]    
   ].
 
  Definition Hir_body' :=
   [
    retl' <c- Hl with {mr};
    retr <- f_ (Efst (Proj retl')) |+| (Esnd (Proj retl')) |*| gen
   ].

  Variable E0:env.

  Notation "c 'Upd' a '<|' b" := (E.Eop (O.Oupd _ _) {a,b,c}) (at level 40).
  Notation "'Etl' p"          := (E.Eop (O.Otl _) {p}) (at level 40).
  Notation "'Ehd' p"          := (E.Eop (O.Ohd _) {p}) (at level 40).

  Notation T_assoc_b := 
                   (T.Pair T.Nat
                      (T.Pair (T.Pair T.Bool (T.Option (T.Pair (T.User Sem.A) T.Nat)))
                         (T.User Sem.G))).
  Notation Lb := (Var.Gvar (T.List T_assoc_b) 1000%positive).

  Notation Hb := (Proc.mkP (xO (xO (xO (xO (xO xH))))) (cons T.Nat (cons T.Bool nil))
                (T.Pair (T.Option (T.Pair (T.User Sem.A) T.Nat))
                   (T.User Sem.G))).

  Definition Hb_params := (dcons Msg m' (dcons T.Bool b (dnil Var.var))).

  Definition Or_f_b := 
   [
     If !(m' in_dom Lb) then [ 
       r <$-G;
       ret'' <c- InvF with {r};
       Lb <- (m' | ( (b | ret'') | r)) |::| Lb 
     ] else [
       If Efst (Efst (Lb [{m'}])) _then [
         Lb <- Lb Upd m' <| (( b | Esnd (Efst (Lb [{m'}]))) | Esnd (Lb[{m'}])) 
       ]
     ]
   ].

  Definition Hb_res := (Esnd (Efst (Lb [{m'}])) | Esnd (Lb[{m'}])).

 (* Definition of adversary A{H} *)
  Definition A_body := [ b' <c- A' with {} ].

  Definition mkEnv' H_body Hb_body Hl_body Hr_body :=
   let EH := add_decl (E'' E0) H H_params (eq_refl true) H_body H_res in
   let EHb := add_decl EH Hb Hb_params (eq_refl true) Hb_body Hb_res in
   let El := add_decl EHb Hl Hl_params (eq_refl true) Hl_body Hl_res in
   let Er := add_decl El Hr Hr_params (eq_refl true) Hr_body Hr_res in
   let EA' := add_decl Er A' (dnil _) (eq_refl true) A'_body A'_res in
   add_decl EA' A (dnil _) (eq_refl true) A_body b'.
 
  Let Ei' := mkEnv' Or_i Or_f_b Hil_body' Hir_body'.
  
  Definition PrOrcl' := 
   PrSet.add (BProc.mkP Hl) (PrSet.singleton (BProc.mkP Hr)).

  Definition PrPriv' :=
    PrSet.add (BProc.mkP Hb) (PrSet.add (BProc.mkP A) (PrSet.add (BProc.mkP H) PrSet.empty)).
 
  Hypothesis A'_wf': WFAdv PrOrcl' PrPriv' Vset.empty Vset.empty Ei' A'.

  Lemma EqAD' : forall H_body1 Hb_body1 Hl_body1 Hr_body1 H_body2 Hb_body2 Hl_body2 Hr_body2, 
   Eq_adv_decl PrOrcl' PrPriv' 
   (mkEnv' H_body1 Hb_body1 Hl_body1 Hr_body1) (mkEnv' H_body2 Hb_body2 Hl_body2 Hr_body2).
  Proof.
   unfold Eq_adv_decl; unfold mkEnv', proc_params, proc_body, proc_res; intros.
   generalize (BProc.eqb_spec (BProc.mkP A) (BProc.mkP f)).
   case (BProc.eqb (BProc.mkP A) (BProc.mkP f)); intros W.
   elim H0. rewrite <- W;trivial.
   rewrite add_decl_other_mk;trivial.
   generalize (BProc.eqb_spec (BProc.mkP A') (BProc.mkP f)).
   case (BProc.eqb (BProc.mkP A') (BProc.mkP f)); intros.
   inversion H1; simpl; auto.
   rewrite add_decl_other_mk;trivial.
   generalize (BProc.eqb_spec (BProc.mkP Hr) (BProc.mkP f)).
   case (BProc.eqb (BProc.mkP Hr) (BProc.mkP f)); intros.
   elim H. rewrite <- H2;trivial.
   rewrite add_decl_other_mk;trivial.
   generalize (BProc.eqb_spec (BProc.mkP Hl) (BProc.mkP f)).
   case (BProc.eqb (BProc.mkP Hl) (BProc.mkP f)); intros.
   elim H. rewrite <- H3;trivial.
   rewrite add_decl_other_mk;trivial.
   generalize (BProc.eqb_spec (BProc.mkP Hb) (BProc.mkP f)).
   case (BProc.eqb (BProc.mkP Hb) (BProc.mkP f)); intros.
   elim H0. rewrite <- H4;trivial.
   generalize (BProc.eqb_spec (BProc.mkP RO.H) (BProc.mkP f)).
   case (BProc.eqb (BProc.mkP RO.H) (BProc.mkP f)); intros.
   elim H0. rewrite <- H5;trivial.
   repeat rewrite add_decl_other_mk;auto.
  Qed.
 
  Lemma EqOp': forall H_body1 Hb_body1 Hl_body1 Hr_body1 H_body2 Hb_body2 Hl_body2 Hr_body2, 
    Eq_orcl_params PrOrcl' 
     (mkEnv' H_body1 Hb_body1 Hl_body1 Hr_body1) (mkEnv' H_body2 Hb_body2 Hl_body2 Hr_body2).
  Proof.
    red;intros.
    unfold PrOrcl' in H.
    rewrite PrSetP.add_spec in H;destruct H.
    inversion H;trivial.
    apply PrSet.singleton_complete in H;inversion H;trivial.
  Qed.
  
  Lemma WF_adv_mkEnv' : forall H_body1 Hb_body1 Hl_body1 Hr_body1,
    WFAdv PrOrcl' PrPriv' Vset.empty Vset.empty (mkEnv' H_body1 Hb_body1 Hl_body1 Hr_body1) A'.
  Proof.
   intros;apply WFAdv_trans with (5:= A'_wf').
   apply EqOp'. apply EqAD'. 
   vm_compute;discriminate.
   vm_compute;discriminate.
  Qed.


  Definition Hl_body :=
   [
    retlr <c- H with {ml};
    retl <- Efst retlr
   ].
 
  Definition Hr_body :=
   [
    retlr <c- H with {mr};
    retr <- Esnd retlr
   ].

  Let Ei :=  mkEnv' Or_i Or_f_b Hl_body Hr_body.
(*
   let EH  := add_decl (E'' E0) H H_params (eq_refl true) Or_i H_res in
   let EHl := add_decl EH Hl Hl_params (eq_refl true) Hl_body Hl_res in
   let EHr := add_decl EHl Hr Hr_params (eq_refl true) Hr_body Hr_res in
   let EA' := add_decl EHr A' (dnil _) (eq_refl true) A'_body A'_res in
    add_decl EA' A (dnil _) (eq_refl true) A_body b'.
*)
  Lemma A'_wf : WFAdv PrOrcl' PrPriv' Vset.empty Vset.empty Ei A'.
  Proof. apply WF_adv_mkEnv'. Qed. 

(* TAKED from OAEP *)
 Definition my_add_refl_info inv E E' (pi:eq_inv_info inv E E')
  t (f:Proc.proc t) :=
  match modify2 pi (proc_body E f) (proc_body E' f) with
  | Some (M1, M2) =>
     let R1 := Vset.diff M1 M2 in
     let R2 := Vset.diff M2 M1 in
     let O := Vset.union (fv_expr (proc_res E f)) 
                         (get_globals (Vset.inter M1 M2)) in
      add_refl_info_O f O R1 R2 pi 
  | None => pi
  end.

Definition my_build_dinv_info_rm (n:positive) inv (E1 E2:env) 
 (piit1:eq_inv_info trueR E1 E1) 
 (piit2:eq_inv_info trueR E2 E2)
 (pii:eq_inv_info inv E1 E2) 
 t (f:Proc.proc t) I O R1 R2 :
 option (dproc_eq_inv_info E1 E2 f) :=
 match build_refl_info_rm n (refl1_info piit1) f R1,
  build_refl_info_rm n (refl1_info piit2) f R2 with
  | Some eqr1, Some eqr2 => 
    let res1 := proc_res E1 f in
    let res2 := proc_res E2 f in
     if E.eqb res1 res2 then 
      let fv := fv_expr res1 in
      let output := get_globals O in
      let input := get_globals I in
      let local := get_locals I in
      if fv [<=?] O then
       if local [<=?] Vset_of_var_decl (proc_params E1 f) then
        if local [<=?] Vset_of_var_decl (proc_params E2 f) then
         Some (Build_dproc_eq_inv_info eqr1 eqr2 input local output)
        else None
       else None
      else None
     else None
  | _, _ => None
 end.

Lemma my_build_sinv_info_rm : forall (n:positive) inv (E1 E2:env) 
 (piit1:eq_inv_info trueR E1 E1) 
 (piit2:eq_inv_info trueR E2 E2)
 (pii:eq_inv_info inv E1 E2)
 t (f:Proc.proc t) I O R1 R2 d,
 EqObsInv inv I E1 (proc_body E1 f) E2 (proc_body E2 f) O ->
 my_build_dinv_info_rm n piit1 piit2 pii f I O R1 R2 = Some d ->
 sproc_eq_inv_info inv d.
Proof.
 intros n0 inv E1' E2' piit1 piit2 pii t f1 I O R1 R2 d HEO.
 unfold my_build_dinv_info_rm.
 case_opt; intros eqr1 _.
 case_opt; intros eqr2 _.
 case_opt; intros Hres.
 case_opt; intros Hfv.
 case_opt; intros Hp1.  
 case_opt; intros Hp2.
 intros Heq; injection Heq; clear Heq; intros; subst. 
 constructor; simpl; trivial.
 apply get_globals_spec.
 apply get_globals_spec.
 exists (get_locals O); split; [apply get_locals_spec | split].
 rewrite VsetP.union_sym; repeat rewrite union_locals_globals; trivial.
 generalize (E.eqb_spec (proc_res E1' f1) (proc_res E2' f1));
  rewrite Hres; intros Heq; rewrite <- Heq.
 rewrite union_locals_globals.
 eapply EqObs_e_strengthen; auto using EqObs_e_fv_expr;
  apply VsetP.subset_trans with (1:= Hfv); auto with set.
Qed.

Definition my_build_inv_info_rm (n:positive) inv (E1 E2:env) 
 (piit1:eq_inv_info trueR E1 E1) 
 (piit2:eq_inv_info trueR E2 E2) 
 (pii:eq_inv_info inv E1 E2) 
 t (f:Proc.proc t) (I O R1 R2:Vset.t) 
 (HEO:EqObsInv inv I E1 (proc_body E1 f) E2 (proc_body E2 f) O) :
 option (proc_eq_inv_info inv E1 E2 f).
 intros n0 inv E1' E2' piit1 piit2 pii t0 f1 I O R1 R2 HEO.
 generalize (fun d => 
  @my_build_sinv_info_rm n0 inv E1' E2' piit1 piit2 pii t0 f1 I O R1 R2 d HEO).
 destruct (my_build_dinv_info_rm n0 piit1 piit2 pii f1 I O R1 R2);
 intros; [ | exact None].
 exact (Some (@Build_proc_eq_inv_info inv E1' E2' t0 f1 d (H _ (refl_equal _)))).
Defined.

Definition my_add_info inv E1 E2 fr (f:Proc.proc fr) R1 R2 
 (piit1:eq_inv_info trueR E1 E1) 
 (piit2:eq_inv_info trueR E2 E2)
 (pii:eq_inv_info inv E1 E2)
 I O 
 (HEO: EqObsInv inv I E1 (proc_body E1 f) E2 (proc_body E2 f) O) :=
 match @my_build_inv_info_rm 
  100%positive inv E1 E2 piit1 piit2 pii fr f I O R1 R2 HEO with
  | Some j => @add_pii_info inv E1 E2 fr f j pii
  | _ => pii
 end.
(* End OAEP *)

 Definition mkEiEi H_body Hb_body Hl_body Hr_body := 
   let E := mkEnv' H_body Hb_body Hl_body Hr_body in
   let ie := empty_info E E in 
   let iv1 := @my_add_refl_info trueR E E ie _ Invf_v1 in
   let iv2 := @my_add_refl_info trueR E E iv1 _ Invf_v2 in
   let ivf := @my_add_refl_info trueR E E iv2 _ InvF in (* warning infer false for lossless *)
   let iH := @my_add_refl_info trueR E E ivf _ H in
   let iHb := @my_add_refl_info trueR E E iH _ Hb in
   let ir := @my_add_refl_info trueR E E iHb _ Hr in
   let il :=  @my_add_refl_info trueR E E ir _ Hl in
   let iA' := @add_adv_info_false trueR E E PrOrcl' PrPriv' Vset.empty Vset.empty
      (EqAD' H_body Hb_body Hl_body Hr_body H_body Hb_body Hl_body Hr_body)
      _ A'
      (WF_adv_mkEnv' H_body Hb_body Hl_body Hr_body) il in
   @my_add_refl_info trueR E E iA' _ A.

  Definition Ei'Ei' := mkEiEi Or_i Or_f_b Hil_body' Hir_body'.

  Lemma EqAD_ii : 
   Eq_adv_decl PrOrcl' PrPriv' Ei Ei.
  Proof. apply EqAD'. Qed.

  Lemma EqAD_ii' : Eq_adv_decl PrOrcl' PrPriv' Ei Ei'.
  Proof. apply EqAD'. Qed.

  Definition Inv k (m1 m2:Mem.t k) :=
   m1 L = map 
   (fun x =>
    match x with
     | (mm, Some (aa, zz)) => 
       (mm, (Some (aa, zz), G.mul (ET.f_def aa) (G.pow (G.g k) zz)))
     | (mm, _) => (mm, (None, G.mul (ET.f_def (A.default k)) (G.pow (G.g k) 0)))  
    end) (m2 Ll).

  Lemma dep_Inv : depend_only_rel Inv {{L}} {{Ll}}.
  Proof.
   unfold Inv; intros k m1 m2 m1' m2' Heq Heq'.   
   rewrite (Heq _ L), (Heq' _ Ll); trivial.
  Qed.

  Lemma dec_Inv: decMR Inv.
  Proof.
   unfold Inv, decMR; intros.
   match goal with
    |- sumbool (?x = ?y) _ =>
     generalize (RO.Sem.T.i_eqb_spec _ _ x y);
     case (RO.Sem.T.i_eqb _ _ x y); auto
   end.
  Qed.

  Definition EiEi'_empty: eq_inv_info Inv Ei Ei'.
   refine (@empty_inv_info Inv _ _ _ _ _ _ _).
   apply dep_Inv. 
   vm_compute; trivial.
   apply dec_Inv.
  Defined.

 (* Definition EiEi := mkEiEi Or_i Or_f_b Hl_body Hr_body. *)

 Definition EiEi :=
   let iempty := empty_info Ei Ei in   
   let iH     := add_refl_info_O H {{m',L}} {{bad}} {{bad}} iempty in
   let iHl    := add_refl_info_rm Hl {{bad}} {{bad}} iH in
   let iHr    := add_refl_info_rm Hr {{bad}} {{bad}} iHl in 
   let iA'    := add_adv_info_false EqAD_ii A'_wf iHr in 
   let iA     := add_refl_info_rm A {{bad}} {{bad}} iA' in iA.

  Lemma EqObs_Hl :
   EqObsInv Inv
   {{ml}}
   Ei  Hl_body
   Ei' Hil_body'
   {{retl}}.
  Proof.
   apply equiv_trans with 
    (kreq_mem {{ml,L}})
    (kreq_mem {{retl,L}})
    (req_mem_rel {{retl}} Inv)
    Ei
    [
     If !(ml in_dom L) then
     [      
      a' <$- A; 
      z <$- Zn;
      r <- f_ a' |+| z |*| gen;
      L <- (ml | (some (a' | z) | r)) |::| L;
      retl <- Efst(L[{ml}])
     ]
    else
     [
      retl <- Efst(L[{ml}])
     ]
   ].
   auto using dec_Inv.   
   unfold refl_supMR2; unfold req_mem_rel, andR; intros; split; auto.
   intros k m1 m2 m3 ? [? ?]; split.
   apply req_mem_trans with m2;
    [apply req_mem_weaken with (2:=H); vm_compute | ]; trivial.
   unfold Inv in H1 |- *.
   simpl; unfold O.eval_op; simpl; rewrite (H _ L); trivial.

   sinline_l EiEi H.  
   cp_test (ml in_dom L); eqobs_in.
  
   ep; deadcode EiEi'_empty.
   cp_test_l (ml in_dom L); cp_test_r (ml in_dom Ll).

   eapply equiv_strengthen; [ | apply equiv_assign].
   unfold Inv, upd_para, req_mem_rel, andR; intros k m1 m2 [ [ [? ?] _] _].
   mem_upd_simpl; split; [ | trivial ].
   simpl E.eval_expr; unfold O.eval_op; simpl O.interp_op; simpl RO.Sem.T.app_op.
   rewrite H0, (H _ ml); clear; trivial.
   intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl.
   induction (m2 Ll); simpl; trivial.
   destruct a as (mm, xx); destruct xx as [ (aa, zz) | ];
   unfold O.assoc; simpl; case (nat_eqb (m2 ml) mm); trivial.
   
   apply equiv_False.
   unfold Inv, req_mem_rel, EP1, EP2, andR, notR; intros k m1 m2 H.
   decompose [and] H; clear H.
   elim H1; generalize H3; expr_simpl.
   intro Hex; apply is_true_existsb in Hex; apply is_true_existsb.
   rewrite H4 in Hex; clear H4.
   destruct Hex as [ (p,(q,r)) [? ?] ].
   exists (p,q); split.
   apply in_map_iff in H.
   destruct H as [ (p',[ (q',r') | ]) [? ?] ]; simpl in H.
   injection H; intros; subst; trivial.
   injection H; intros; subst; trivial.
   rewrite <- (H0 _ ml); trivial.
   
   apply equiv_False.
   unfold Inv, req_mem_rel, EP1, EP2, andR, notR; intros k m1 m2 H.
   decompose [and] H; clear H.
   elim H3; generalize H1; expr_simpl.
   rewrite H4; clear H1 H3 H4.
   rewrite (H0 _ ml); trivial.
   intro Hex.
   apply is_true_existsb in Hex; apply is_true_existsb.
   destruct Hex as [ (p, [ (q',z') | ]) [? ?] ].
   exists (p, (Some (q', z'), 
    G.mul (ET.f_def q') (G.pow (G.g k) z'))); split.
   apply in_map_iff.
   exists (p, Some (q', z')); auto.
   trivial.
   exists (p,( None, G.mul (ET.f_def (A.default k)) (G.pow (G.g k) 0))); split.
   apply in_map_iff.
   exists (p, None); auto.
   trivial.

   match goal with
   |- equiv _ _ ?c1 _ ?c2 _ => 
      rewrite <- (firstn_skipn 2%nat c1); 
      rewrite <- (firstn_skipn 2%nat c2) 
   end.
   apply equiv_app with (req_mem_rel {{ml,a',z}} Inv).
   eqobs_in EiEi'_empty.
   unfold implMR, andR; intuition.
   
   ep_eq_r 
    (f_ Efst (Proj (some (a' | z))) |+| Esnd (Proj (some (a' | z))) |*| gen)
    (f_ a' |+| z |*| gen).
   trivial.
   simpl.
   apply equiv_cons with 
    (req_mem_rel {{z,a',ml}} (Inv /-\ EP1 (Efst(L[{ml}]) =?= some (a' | z)))).
   eapply equiv_strengthen; [ | apply equiv_assign].
   unfold Inv, upd_para, req_mem_rel, andR, EP2; intros k m1 m2 [? ?].
   mem_upd_simpl; split; [ | trivial ].
   simpl E.eval_expr; unfold O.eval_op; simpl O.interp_op; simpl RO.Sem.T.app_op.
   intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl; auto.
   expr_simpl; unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
   rewrite (H _ z), (H _ a'), (H _ ml), H0; trivial.
   rewrite A_eqb_refl, nat_eqb_refl; auto.

   ep_eq_l (Efst(L[{ml}])) (some (a' | z)).
   unfold req_mem_rel, andR, EP1; intros k m1 m2 [? [? ?] ].
   apply expr_eval_eq; trivial.
   eqobs_in EiEi'_empty.
   unfold implMR, andR; intuition.  
  Qed.


  Lemma EqObs_Hr :
   EqObsInv Inv
   {{mr}}
   Ei  Hr_body
   Ei' Hir_body'
   {{retr}}.
  Proof.
   unfold Hr_body, Hir_body'.
   eapply equiv_trans with 
    (kreq_mem {{mr,L}})
    (kreq_mem {{retr,L}})
    (req_mem_rel {{retr}} Inv)
    Ei
    [
     If !(mr in_dom L) then
     [     
      a' <$- A; 
      z <$- Zn;
      r <- f_ a' |+| z |*| gen;
      L <- (mr | (some (a' | z) | r)) |::| L;
      retr <- Esnd(L[{mr}]) (* some (a' | z) *)
     ]
    else
     [
      retr <- Esnd(L[{mr}])
     ]
   ].
   auto using dec_Inv.   
   unfold refl_supMR2; unfold req_mem_rel, andR; intros; split; auto.
   intros k m1 m2 m3 ? [? ?]; split.
   apply req_mem_trans with m2;
    [apply req_mem_weaken with (2:=H); vm_compute | ]; trivial.
   unfold Inv in H1 |- *.
   simpl; unfold O.eval_op; simpl; rewrite (H _ L); trivial.

   sinline_l EiEi H.  
   cp_test (mr in_dom L); eqobs_in.
   
   inline_r EiEi'_empty Hl.
   auto using dec_Inv.
   ep; deadcode EiEi'_empty.
   cp_test_l (mr in_dom L); cp_test_r (mr in_dom Ll).
   deadcode EiEi'_empty.

   eapply equiv_strengthen; [ | apply equiv_assign].
   unfold Inv, upd_para, req_mem_rel, andR; intros k m1 m2 [ [ [? ?] _] _].
   mem_upd_simpl; split; [ | trivial ].
   simpl E.eval_expr; unfold O.eval_op; simpl O.interp_op; simpl RO.Sem.T.app_op.
   rewrite (H _ mr), H0; clear; trivial.
   intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl.
   induction (m2 Ll); simpl; trivial.
   rewrite f_Adef, G.pow_0, G.mul_0_r; trivial.
   destruct a as (mm, xx); destruct xx as [ (aa, zz) | ];
   unfold O.assoc; simpl; case (nat_eqb (m2 mr) mm); trivial.
   
   apply equiv_False.
   unfold Inv, req_mem_rel, EP1, EP2, andR, notR; intros k m1 m2 H.
   decompose [and] H; clear H.
   elim H1; generalize H3; expr_simpl.
   intro Hex; apply is_true_existsb in Hex; apply is_true_existsb.
   rewrite H4 in Hex; clear H4.
   destruct Hex as [ (p,(q,r)) [? ?] ].
   exists (p,q); split.
   apply in_map_iff in H.
   destruct H as [ (p',[ (q',r') | ]) [? ?] ]; simpl in H.
   injection H; intros; subst; trivial.
   injection H; intros; subst; trivial.
   rewrite <- (H0 _ mr); trivial.
   
   apply equiv_False.
   unfold Inv, req_mem_rel, EP1, EP2, andR, notR; intros k m1 m2 H.
   decompose [and] H; clear H.
   elim H3; generalize H1; expr_simpl.
   rewrite H4; clear H1 H3 H4.
   rewrite (H0 _ mr); trivial.
   intro Hex.
   apply is_true_existsb in Hex; apply is_true_existsb.
   destruct Hex as [ (p, [ (q',z') | ]) [? ?] ].
   exists (p, (Some (q', z'), 
    G.mul (ET.f_def q') (G.pow (G.g k) z'))); split.
   apply in_map_iff.
   exists (p, Some (q', z')); auto.
   trivial.
   exists (p,( None, G.mul (ET.f_def (A.default k)) (G.pow (G.g k) 0))); split.
   apply in_map_iff.
   exists (p, None); auto.
   trivial.
  
   match goal with
   |- equiv _ _ ?c1 _ ?c2 _ => 
      rewrite <- (firstn_skipn 2%nat c1); 
      rewrite <- (firstn_skipn 2%nat c2) 
   end.
   apply equiv_app with (req_mem_rel {{mr,a',z}} Inv).
   eqobs_in EiEi'_empty.
   unfold implMR, andR; intuition.
   
   ep_eq_r 
    (f_ Efst (Proj (some (a' | z))) |+| Esnd (Proj (some (a' | z))) |*| gen)
    (f_ a' |+| z |*| gen).
   trivial.
   simpl.
   apply equiv_cons with 
    (req_mem_rel {{z,a',mr}} 
     (Inv /-\ EP1 (Esnd(L[{mr}]) =?= f_ a' |+| z |*| gen))).
   eapply equiv_strengthen; [ | apply equiv_assign].
   unfold Inv, upd_para, req_mem_rel, andR, EP2; intros k m1 m2 [? ?].
   mem_upd_simpl; split; [ | trivial ].
   simpl E.eval_expr; unfold O.eval_op; simpl O.interp_op; simpl RO.Sem.T.app_op.
   intros ? ? Hin; Vset_mem_inversion Hin; subst; mem_upd_simpl; auto.
   expr_simpl; unfold O.assoc; simpl; rewrite nat_eqb_refl; simpl.
   rewrite (H _ z), (H _ a'), (H _ mr), H0; trivial.
   rewrite f_Adef, G.pow_0, G.mul_0_r; auto using G_eqb_refl.
  
   deadcode EiEi'_empty.
   ep_eq_l (Esnd(L[{mr}])) (f_ a' |+| z |*| gen).
   unfold req_mem_rel, andR, EP1; intros k m1 m2 [? [? ?] ].
   apply expr_eval_eq; trivial.
   eqobs_in EiEi'_empty.
   unfold implMR, andR; intuition.  
  Qed.

  Definition EiEi' :=
    let ie := EiEi'_empty in
    let il := my_add_info Hl {{bad}} {{bad}} EiEi Ei'Ei' ie EqObs_Hl in
    let ir := my_add_info Hr {{bad}} {{bad}} EiEi Ei'Ei' il EqObs_Hr in
    add_adv_info_false EqAD_ii' A'_wf ir.

  Definition G' := [ Ll <- Nil _; Lr <- Nil _; b <c- A' with {} ].

  (** TODO: maybe the bound should be on Elen Ll + Elen Lr? *) 
  Definition Ev' := b && (Elen Ll <=! (qQ1 +! qQ2)).

  Lemma decouple_i : forall k (m:Mem.t k),
   Pr Ei G m (EP k Ev) == Pr Ei' G' m (EP k Ev').
  Proof.
   intros.
   transitivity (Pr Ei [ L <- Nil _; b <c- A' with {} ] m (EP k Ev)).
   apply equiv_deno with (kreq_mem Vset.empty) (kreq_mem {{L,b}}).
   sinline_l EiEi A; eqobs_in EiEi.
   unfold charfun, restr, EP; intros.
   rewrite (@depend_only_fv_expr T.Bool Ev k m1 m2 H); trivial.
   trivial.

   apply equiv_deno with (kreq_mem Vset.empty) (req_mem_rel {{b}} Inv); trivial.
   eqobs_tl EiEi'.
   unfold Inv; eqobsrel_tail; unfold implMR; intros; expr_simpl.
   unfold Inv; intros m1 m2 [? ?]; unfold charfun, EP, restr, Ev, Ev'.
   expr_simpl; rewrite (H _ b), H0, map_length; trivial.
  Qed.


  (* This is the 'simulator' *)
  Definition Hfl_body' :=
   [
    If !(ml in_dom Ll) then 
     [
      r <c- Hr with {ml};
      retl <c- InvF with {r};
      Ll <- (ml | retl) |::| Ll
     ]
    else 
     [ retl <- Ll[{ml}] ]
   ].

  Definition Hfr_body' :=
   [
    If !(mr in_dom Lr) then
     [
      retr <$- G;
      Lr <- (mr | retr) |::| Lr
     ]
    else
     [ retr <- Lr[{mr}] ]
   ].

  Definition Ef' := mkEnv' Or_f Or_f_b Hfl_body' Hfr_body'.
  
  Let Ef := mkEnv' Or_f Or_f_b Hl_body Hr_body.
(*
   let EH  := add_decl (E'' E0) H H_params (eq_refl true) Or_f H_res in
   let EHl := add_decl EH Hl Hl_params (eq_refl true) Hl_body Hl_res in
   let EHr := add_decl EHl Hr Hr_params (eq_refl true) Hr_body Hr_res in
   let EA' := add_decl EHr A' (dnil _) (eq_refl true) A'_body A'_res in
    add_decl EA' A (dnil _) (eq_refl true) A_body b'. *)

 
  Notation aux := (Var.Gvar T_assoc_b 1001%positive).
  Notation RET := (Var.Gvar (T.Option (T.Pair (T.User Sem.A) T.Nat)) 1003%positive).

  Definition Hl_body_b := [retlr <c- Hb with {ml, false}; retl <- Efst (retlr)].
  Definition Hr_body_b := [retlr <c- Hb with {ml, true}; retr <- Esnd (retlr)].

  Let Efb := mkEnv' Or_f Or_f_b Hl_body_b Hr_body_b.

  Definition Gb := 
   [ Lb <- Nil _; b <c- A with{} ].

  Definition Or_f_b_sample := 
   [
     If !(m' in_dom Lb) then [ 
       r <$-G;
       ret'' <c- InvF with {r};
       Lb <- (m' | ( (b | ret'') | r)) |::| Lb 
     ] else [ 
       If Efst (Efst (Lb [{m'}])) _then [ 
         r <- Esnd (Lb [{m'}]);
         ret'' <c- InvF with {r};
         Lb <- Lb Upd m' <| (( b | ret'') | r) 
       ] 
     ]
   ].

 Let Efbs := mkEnv' Or_f Or_f_b_sample Hl_body_b Hr_body_b.

  Definition sample_body (LGhd LGtl : Var.var (T.List T_assoc_b)) :=
  [ 
   aux <- Ehd LGtl;
   LGtl <- Etl LGtl;
   If Efst (Efst (Esnd aux)) _then [
    RET <c- InvF with {Esnd (Esnd aux) };
    aux <- (Efst aux | ((true | RET) | Esnd (Esnd aux)))
   ];
   LGhd <- LGhd |++| aux |::| Nil _
  ].

 Definition sample_while (LGhd LGtl : Var.var (T.List T_assoc_b)) :=
  while !(LGtl =?= Nil _) do sample_body LGhd LGtl.

 Definition sample_true (LGhd LGtl :Var.var (T.List T_assoc_b)) (LG : E.expr (T.List T_assoc_b)):= 
  [
   LGhd <- Nil _;
   LGtl <- LG;
   sample_while LGhd LGtl
  ].
 Notation Lb_hd := (Var.Gvar (T.List T_assoc_b) 1004%positive).
 Notation Lb_tl := (Var.Gvar (T.List T_assoc_b) 1005%positive).

 Definition SLGb :=
  sample_true Lb_hd Lb_tl Lb ++
  [ 
   Lb <- Lb_hd; 
   (* This part resets the auxiliary variables *)
   Lb_hd <- Nil _;
   RET <- none _;
   aux <- (0%nat | ((true | RET) | gen))
  ].

 Axiom G_Gb : EqObs Vset.empty Ef G Efb Gb {{b}}.

 (* Ca c'est le truc dure, swap sample de OAEP *)
 Axiom Gb_Gbs : EqObs Vset.empty Efb Gb Efbs Gb {{b}}.

 (* Ca ca doit passer avec la remarque que dans Hr on utilise pas le resultat de l'inversion *)
 Axiom Gbs_Gf' : EqObs Vset.empty Efbs Gb Ef' G' {{b}}.

(* ..... *)



  Lemma A'_wf'_f : WFAdv PrOrcl' PrPriv' Vset.empty Vset.empty Ef' A'.
  Proof. apply WF_adv_mkEnv'. Qed.

  Lemma A'_wf_f : WFAdv PrOrcl' PrPriv' Vset.empty Vset.empty Ef A'.
  Proof. apply WF_adv_mkEnv'. Qed.

  Definition Ef'Ef' := mkEiEi Or_f Or_f_b Hfl_body' Hfr_body'.

  Eval vm_compute in (print_info Ef'Ef' A).
  
  Lemma EqAD_ff : Eq_adv_decl PrOrcl' PrPriv' Ef Ef.
  Proof. apply EqAD'. Qed.

  Lemma EqAD_ff' : Eq_adv_decl PrOrcl' PrPriv' Ef Ef'.
  Proof. apply EqAD'. Qed.


  Definition Inv' :=
   (fun k m1 m2 => m2 Ll = map (fun x => (fst x, fst (snd x))) (m1 L)) /-\
   (fun k m1 m2 => m2 Lr = map (fun x => (fst x, snd (snd x))) (m1 L)).
   
  Lemma dep_Inv' : depend_only_rel Inv' {{L}} {{Ll,Lr}}.
  Proof.
   unfold Inv', andR.
   intros k m1 m2 m1' m2' Heq Heq';
    rewrite (Heq _ L), (Heq' _ Ll), (Heq' _ Lr); trivial.
  Qed.

  Lemma dec_Inv' : decMR Inv'.
  Proof.
   apply decMR_and;
   unfold decMR; intros;
   match goal with
    |- sumbool (?x = ?y) _ =>
     generalize (RO.Sem.T.i_eqb_spec _ _ x y);
     case (RO.Sem.T.i_eqb _ _ x y); auto
   end.
  Qed.

  Definition EfEf'_empty: eq_inv_info Inv' Ef Ef'.
   refine (@empty_inv_info Inv' _ _ _ _ _ _ _).
   apply dep_Inv'. 
   vm_compute; trivial.
   apply dec_Inv'.
  Defined.


  (** REMARK: altogether takes ages to typecheck *)
  Definition EfEf_InvF :=
   let iempty   := empty_info Ef Ef in   
   let iInvf_v1 := add_refl_info_rm Invf_v1 Vset.empty Vset.empty iempty in
   let iInvf_v2 := add_refl_info_rm Invf_v2 Vset.empty Vset.empty iInvf_v1 in
   let iInvF    := add_refl_info_rm InvF Vset.empty Vset.empty iInvf_v2 in
    iInvF.

  Definition EfEf :=
   let iH     := add_refl_info_O H {{m',L}} {{bad}} {{bad}} EfEf_InvF in
   let iHl    := add_refl_info_rm Hl {{bad}} {{bad}} iH in
   let iHr    := add_refl_info_rm Hr {{bad}} {{bad}} iHl in 
   let iA'    := add_adv_info_false EqAD_ff A'_wf_f iHr in 
   let iA     := add_refl_info_rm A {{bad}} {{bad}} iA' in iA.

(*  Definition EfEf2 := mkEiEi Or_f Or_f_b Hl_body Hr_body. *)
  Eval vm_compute in (print_info EfEf A).

  
  Lemma EqObs_Hrf :
   EqObsInv Inv'
   {{mr}}
   Ef  Hr_body
   Ef' Hfr_body'
   {{retr}}.
  Proof. 
   unfold Hr_body, Hfr_body'.
   eapply equiv_trans with 
    (kreq_mem {{mr,L}})
    (kreq_mem {{retr,L}})
    (req_mem_rel {{retr}} Inv')
    Ef
    [
     If !(mr in_dom L) then
     [   
      r <$- G; 
      ret'' <c- InvF with {r};
      L <- (mr | (ret'' | r)) |::| L;
      retr <- Esnd(L[{mr}])
     ]
    else
     [
      retr <- Esnd(L[{mr}])
     ]
   ].
   auto using dec_Inv'.   
   unfold refl_supMR2; unfold req_mem_rel, andR; intros; split; auto.
   intros k m1 m2 m3 ? [? ?]; split.
   apply req_mem_trans with m2;
    [apply req_mem_weaken with (2:=H); vm_compute | ]; trivial.
   unfold Inv', andR in H1 |- *.
   simpl; unfold O.eval_op; simpl; rewrite (H _ L); trivial.

   sinline_l EfEf H.
   cp_test (mr in_dom L); eqobs_in EfEf.
 
   cp_test_l (mr in_dom L); cp_test_r (mr in_dom Lr).
   eapply equiv_strengthen; [ | apply equiv_assign].
   unfold Inv', upd_para, req_mem_rel, andR; intros k m1 m2 H.
   decompose [and] H; clear H.
   mem_upd_simpl; repeat split; trivial.

   intros ? ? Hin.
   Vset_mem_inversion Hin; subst; mem_upd_simpl.
   expr_simpl.
   rewrite H5, (H0 _ mr); unfold O.assoc; clear; trivial.
   induction (m1 L); simpl.
   trivial.
   match goal with
    |- context[nat_eqb ?x ?y] => destruct (nat_eqb x y); trivial
   end.
   
   apply equiv_False.
   unfold Inv', req_mem_rel, EP1, EP2, andR, notR; intros k m1 m2 H.
   decompose [and] H; clear H.
   elim H1; generalize H3; expr_simpl.
   intro Hex; apply is_true_existsb in Hex; apply is_true_existsb.
   rewrite H5.
   destruct Hex as [ (p,(q,r)) [? ?] ].
   exists (p,r); split.
   apply in_map_iff.
   exists (p,(q,r)); auto.
   rewrite <- (H0 _ mr); trivial.
 
   apply equiv_False.
   unfold Inv', req_mem_rel, EP1, EP2, andR, notR; intros k m1 m2 H.
   decompose [and] H; clear H.
   elim H3; generalize H1; expr_simpl.
   intro Hex; apply is_true_existsb in Hex; apply is_true_existsb.
   rewrite H5 in Hex.
   destruct Hex as [ (p,r) [? ?] ].
   apply in_map_iff in H.
   destruct H as [p' [? ?] ].
   exists p'; split.
   trivial.
   injection H; intros; subst.
   rewrite (H0 _ mr); trivial.
   
   apply equiv_strengthen with (req_mem_rel {{mr}} Inv').
   unfold andR; intuition.

   (** I do not think this is provable without modifying the 
      code of the oracles *)
   admit.
  Qed.

  Lemma EqObs_Hlf :
   EqObsInv Inv'
   {{ml}}
   Ef  Hl_body
   Ef' Hfl_body'
   {{retl}}.
  Proof.
   unfold Hl_body, Hfl_body'.
   eapply equiv_trans with 
    (kreq_mem {{ml,L}})
    (kreq_mem {{retl,L}})
    (req_mem_rel {{retl}} Inv')
    Ef
    [
     If !(ml in_dom L) then
     [ 
      r <$- G; 
      ret'' <c- InvF with {r};
      L <- (ml | (ret'' | r)) |::| L;
      retl <- Efst(L[{ml}])
     ]
    else
     [
      retl <- Efst(L[{ml}])
     ]
   ].
   auto using dec_Inv'.   
   unfold refl_supMR2; unfold req_mem_rel, andR; intros; split; auto.
   intros k m1 m2 m3 ? [? ?]; split.
   apply req_mem_trans with m2;
    [apply req_mem_weaken with (2:=H); vm_compute | ]; trivial.
   unfold Inv', andR in H1 |- *.
   simpl; unfold O.eval_op; simpl; rewrite (H _ L); trivial.

   sinline_l EfEf H.
   cp_test (ml in_dom L); eqobs_in EfEf.

   cp_test_l (ml in_dom L); cp_test_r (ml in_dom Ll).
   eapply equiv_strengthen; [ | apply equiv_assign].
   unfold Inv', upd_para, req_mem_rel, andR; intros k m1 m2 H.
   decompose [and] H; clear H.
   mem_upd_simpl; repeat split; trivial.

   intros ? ? Hin.
   Vset_mem_inversion Hin; subst; mem_upd_simpl.
   expr_simpl.
   rewrite H2, (H0 _ ml); unfold O.assoc; clear; trivial.
   induction (m1 L); simpl.
   trivial.
   match goal with
    |- context[nat_eqb ?x ?y] => destruct (nat_eqb x y); trivial
   end.
   
   apply equiv_False.
   unfold Inv', req_mem_rel, EP1, EP2, andR, notR; intros k m1 m2 H.
   decompose [and] H; clear H.
   elim H1; generalize H3; expr_simpl.
   intro Hex; apply is_true_existsb in Hex; apply is_true_existsb.
   rewrite H2.
   destruct Hex as [ (p,(q,r)) [? ?] ].
   exists (p,q); split.
   apply in_map_iff.
   exists (p,(q,r)); auto.
   rewrite <- (H0 _ ml); trivial.
 
   apply equiv_False.
   unfold Inv', req_mem_rel, EP1, EP2, andR, notR; intros k m1 m2 H.
   decompose [and] H; clear H.
   elim H3; generalize H1; expr_simpl.
   intro Hex; apply is_true_existsb in Hex; apply is_true_existsb.
   rewrite H2 in Hex.
   destruct Hex as [ (p,r) [? ?] ].
   apply in_map_iff in H.
   destruct H as [p' [? ?] ].
   exists p'; split.
   trivial.
   injection H; intros; subst.
   rewrite (H0 _ ml); trivial.

   (** I do not think this is provable without modifying the 
      code of the oracles *)
   admit.
  Qed.

  Definition EfEf_lr :=
   let iHr := add_refl_info_rm Hr {{bad}} {{bad}} EfEf in 
   let iHl := add_refl_info_rm Hl {{bad}} {{bad}} iHr in
   let iA' := add_adv_info_false EqAD_ff A'_wf_f iHl in 
   let iA  := add_refl_info_rm A {{bad}} {{bad}} iA' in iA.

  Definition iHrf : eq_inv_info Inv' Ef Ef'.
  destruct (refl1_info EfEf_lr Hr); [ | exact EfEf'_empty].
  destruct (refl2_info Ef'Ef' Hr); [ | exact EfEf'_empty].
  refine (@add_pii_info Inv' Ef Ef' _ Hr _ EfEf'_empty).
  refine (Build_proc_eq_inv_info
  (dpii:=Build_dproc_eq_inv_info 
   p p0
   Vset.empty
   (Vset_of_var_decl (proc_params Ef Hr))
   Vset.empty) _).
  split; simpl; intros; try discriminate.
  apply VsetP.subset_refl.
  apply VsetP.subset_refl.
  exists (fv_expr (proc_res Ef Hr)); repeat split.
  intros.
  simpl in H; unfold Hr_res in H.
  generalize (VarP.Edec.eqb_spec x retr), H.
  case (VarP.Edec.eqb x retr); [ | discriminate].
  intros; subst; trivial.
  apply EqObs_Hrf.
  intros k m1 m2 Heq.
  rewrite depend_only_fv_expr_subset with (2:=Heq); auto with set.
  Defined.

  Definition iHlf : eq_inv_info Inv' Ef Ef'.
  destruct (refl1_info EfEf_lr Hl); [ | exact EfEf'_empty].
  destruct (refl2_info Ef'Ef' Hl); [ | exact EfEf'_empty].
  refine (@add_pii_info Inv' Ef Ef' _ Hl _ iHrf).
  refine (Build_proc_eq_inv_info
  (dpii:=Build_dproc_eq_inv_info 
   p p0
   Vset.empty
   (Vset_of_var_decl (proc_params Ef Hl))
   Vset.empty) _).
  split; simpl; intros; try discriminate.
  apply VsetP.subset_refl.
  apply VsetP.subset_refl.
  exists (fv_expr (proc_res Ef Hl)); repeat split.
  intros.
  simpl in H; unfold Hl_res in H.
  generalize (VarP.Edec.eqb_spec x retl), H.
  case (VarP.Edec.eqb x retl); [ | discriminate].
  intros; subst; trivial.
  apply EqObs_Hlf.
  intros k m1 m2 Heq.
  rewrite depend_only_fv_expr_subset with (2:=Heq); auto with set.
  Defined.

  Definition EfEf' := add_adv_info_false EqAD_ff' A'_wf_f iHlf.

  Eval vm_compute in (print_info EfEf' A').

  Lemma decouple_f : forall k (m:Mem.t k),
   Pr Ef G m (EP k Ev) == Pr Ef' G' m (EP k Ev').
  Proof.
   intros; unfold G, G'.
   transitivity (Pr Ef [ L <- Nil _; b <c- A' with {} ] m (EP k Ev)).
   apply equiv_deno with (kreq_mem Vset.empty) (kreq_mem {{L,b}}).
   sinline_l EfEf A.
   eqobs_in EfEf.
   unfold charfun, restr, EP; intros.
   rewrite (@depend_only_fv_expr T.Bool Ev k m1 m2 H); trivial.
   trivial.

   apply equiv_deno with (kreq_mem Vset.empty) (req_mem_rel {{b}} Inv'); trivial.
   eqobs_tl EfEf'.
   eqobsrel_tail; unfold implMR; intros; expr_simpl.
   unfold Inv', andR; split; expr_simpl. 
   unfold Inv'; intros m1 m2 [? [? ?] ]; unfold charfun, EP, restr, Ev, Ev'.
   expr_simpl.
   rewrite (H _ b), H0, map_length; trivial.
  Qed.


  Theorem security_bound : forall k (m:Mem.t k),
   Uabs_diff (Pr Ei' G' m (EP k Ev')) (Pr Ef' G' m (EP k Ev')) <= 
   2 * (q1_poly k + q2_poly k) */ ((1 - one_over_alpha k)^(S (T_poly k))).
  Proof.
   intros.
   rewrite <-decouple_i, <-decouple_f; clear.
   rewrite <-security_bound_single_oracle with (E0:=E0) (m:=m) (A_res:=b') (A_body:=A_body).
   apply Uabs_diff_morphism.
   
   (* 
     To prove this [security_bound_single_oracle] must be parametrized by 
     an initial environment for the private procedures of the adversary 
   *)
   admit.
   admit.
   admit.
   admit.
  Qed.
 
 End DECOUPLING.

End RO.
