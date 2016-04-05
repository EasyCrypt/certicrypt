(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

Require Import SwitchingSem.
Require Export SD.

Set Implicit Arguments.


(* *********************** SOME AUXILIARY STUFF *********************** *)
(* ******************************************************************** *)

 Lemma mu_stable_plus_range: forall (A:Type) (d:Distr A) R,
   range R d ->
   forall f g,
   (forall a, R a ->  g a <= [1-] f a) ->
   mu d (fplus f g) == mu d f + mu d g.
 Proof.
  intros; split.
    auto.
    transitivity (mu d (fminus (fplus f g) g) + mu d g).
      Usimpl.
      apply range_le with (1:=H).
      intros a Ha; unfold fminus, fplus.
      rewrite Uplus_minus_simpl_right; auto.
      rewrite <-(@mu_stable_plus _ d _ _); unfold fminus, fplus.
        apply range_le with (1:=H).
        intros a _; rewrite Uminus_plus_simpl; auto.
        unfold fplusok, finv; refine (ford_le_intro _); intro a.
        rewrite <-Uminus_one_left.
        apply Uminus_le_compat_left; trivial.
 Qed.

 Lemma Uplus_le_minus: forall a b c,
  a - b <= c -> a <= c + b.
 Proof.
   intros.
   apply (Ule_total a b); [auto|intro H'|intro H'].
     rewrite (Uminus_plus_le a b), (Uminus_le_zero _ _ H'); auto.
     apply (Uminus_le_perm_left _ _ _ H' H).
 Qed.

 Lemma Uabs_diff_le_intro: forall a b c,
    a <= c + b ->
    b <= c + a ->
    Uabs_diff a b <= c.
 Proof.
  intros a b c Ha Hb.
  unfold Uabs_diff.
  apply (Ule_total a b); [auto|intro H''|intro H''].
    rewrite (Uminus_le_zero _ _ H''); Usimpl.
    rewrite Hb; auto.
    rewrite (Uminus_le_zero _ _ H''); Usimpl.
    rewrite Ha; auto.
 Qed.


(*
 Lemma Uabs_diff_le_lub_compat : forall (f g h: natO -m> U),
  (forall n, Uabs_diff (f n) (g n) <= h n) ->
  Uabs_diff (lub f) (lub g) <= lub h. 
 Proof.
  intros.
  apply Uabs_diff_le_intro.
    apply lub_le; intro n.
    transitivity (h n + g n).
      apply Uplus_le_minus; rewrite <-H; apply Ule_plus_right.
      apply Uplus_le_compat; apply le_lub.
    apply lub_le; intro n.
    transitivity (h n + f n).
      apply Uplus_le_minus; rewrite <-H; apply Ule_plus_left.
      apply Uplus_le_compat; apply le_lub.
 Qed.
*)


   (* sums up [ f(Min) + ... +  f(pred Max) ] *)
 Definition sum_f (Min Max:nat) (f:nat -> U) 
   := finite_sum f (seq Min (Max - Min)).

 Lemma sum_f_split: forall (a b c:nat) f,
   (a <= c)%nat ->
   (c <= b)%nat ->
   sum_f a b f == sum_f a c f + sum_f c b f.
 Proof.
  intros a b c f Hab Hcb; unfold sum_f.
  replace (b-a)%nat with  ((c - a) + (b - c))%nat by omega.
  rewrite seq_append, (le_plus_minus_r _ _ Hab).
   apply finite_sum_app.
 Qed.

 Lemma sum_f_empty: forall (a b:nat) f,
   (b <= a)%nat ->
   sum_f a b f == 0.
 Proof.  
  intros; unfold sum_f.
  replace (b-a)%nat with 0%nat by omega; trivial.
 Qed.

 Lemma sum_f_non_empty: forall f a n, 
   (a <= n)%nat -> 
   sum_f a (S n) f == f n + sum_f a n f.
 Proof.
  intros.
  rewrite (@sum_f_split _ _ n); [ Usimpl | auto | auto ].
  unfold sum_f.
  rewrite <-(minus_Sn_m _ _ (le_refl _)), minus_diag.
  simpl; auto.
 Qed.

 Lemma sum_f_monot: forall (min max min' max':nat) f,
   (min' <= min)%nat ->
   (max <= max')%nat ->
   sum_f min max f <= sum_f min' max' f.
 Proof.
  intros mi ma mi' ma' f Hmi Hma.
  destruct (le_lt_dec ma mi) as [H | H].
    rewrite (sum_f_empty _ H); auto.
    rewrite (@sum_f_split mi' ma' ma _); [ | omega | trivial ].
    rewrite (@sum_f_split mi' ma mi _); [ | omega | omega ].
    rewrite <-Uplus_assoc, Uplus_sym, <-Uplus_assoc; auto.
 Qed.

 Lemma sum_f_0_sigma: forall b f, 
   sum_f 0 b f == (sigma f) b.
 Proof.
  intros; unfold sum_f.
  rewrite <-(@sigma_finite_sum _ 0%nat).
  rewrite <-minus_n_O, seq_length.  
  apply sigma_eq_compat.
  intros; rewrite (seq_nth _ _ H); auto.
 Qed.

 Lemma wretract_sum_f: forall f,
   wretract f ->
   forall a b c, sum_f a b f <= [1-] sum_f b c f.
 Proof.
  intros f Hf a b c.
  destruct (le_lt_dec b a) as [H1 | H1 ];
    [ rewrite (sum_f_empty _ H1); auto | ].
  destruct (le_lt_dec c b) as [H2 | H2 ];
    [ rewrite (sum_f_empty _ H2); auto | ].
  apply Uinv_le_perm_right.
  replace c with (b + S (pred (c - b)))%nat by omega.
  generalize (pred (c-b)); clear c H2;
    intro n; generalize n a b H1; clear H1 a b n.
  induction n; intros a b Hab.
    (* case [n = 0] *) 
    rewrite plus_comm, (sum_f_non_empty _ (le_refl b)), 
      (sum_f_empty  _ (le_refl b)); Usimpl.
    rewrite (Hf b); apply Uinv_le_compat.  
    rewrite (sum_f_monot _ (le_0_n _) (le_refl _)).
    apply sum_f_0_sigma.
    (* inductive case *)
    rewrite plus_comm, plus_Sn_m, (sum_f_non_empty _ (le_plus_r _ _)).
    transitivity ([1-] (sum_f a b f + sum_f b (S n + b) f) + sum_f b (S n + b) f).
      Usimpl; rewrite (Hf (S n + b)%nat); Usimpl.
      rewrite <-sum_f_split; [ | apply (lt_le_weak _ _ Hab) | apply le_plus_r ].
      rewrite (sum_f_monot _ (le_0_n _) (le_refl _)).
      apply sum_f_0_sigma.
    apply Uinv_plus_right.
    rewrite plus_comm; apply (IHn _ _ Hab).
 Qed.


(*
   (* sums up [ f(Min) + ... +  f(pred Max) ] *)
   Definition sum_over_nat (Min Max:nat) (f:nat -> U) 
     := (sigma (fun n => f (Max - S n)) (Max - Min))%nat.
*)


(* ******************************************************************** *)
(* ******************************************************************** *)

Section TRIPLE.
  
 Variable k : nat.
 Variable e1 e2 : env.

 Definition triple c1 c2 (g:Mem.t k -> U) := forall (m:Mem.t k) f, 
   Uabs_diff (mu ([[c1]] e1 m) f) (mu ([[c2]] e2 m) f)  <= g m.

 Notation "'[|' c1 ',' c2  '|]' '<~' g" := (triple c1 c2 g) (at level 50).

 Lemma triple_weaken : forall (g g':Mem.t k -o> U) c1 c2,
   g' <= g -> 
   [| c1,c2 |] <~ g' ->
   [| c1,c2 |] <~ g.
 Proof.
  unfold triple; intros.
  rewrite <-(H m); auto.
 Qed.

 Add Morphism triple with signature 
   (@eq cmd) ==> (@eq cmd) ==> (@Ole (ford (Mem.t k) (tcpo U))) ++>
    impl as triple_Ole_Morph.
 Proof.
  unfold impl; intros.
  refine (triple_weaken H H0).   
 Qed.   

 Lemma triple_ass : forall t (x:Var.var t) e,
   [| [x <- e], [x <- e] |] <~ fzero _.
 Proof.   
  unfold triple; intros.
  repeat rewrite deno_assign_elim; auto.
 Qed.

 Lemma triple_rand : forall t (x:Var.var t) s,
   [| [x <$- s], [x <$- s] |] <~ fzero _.
 Proof.
  unfold triple; intros.
  repeat rewrite deno_random_elim; auto.
 Qed.

 Lemma triple_cond : forall (e:E.expr T.Bool) c1 c1' c2 c2' g,
   [| c1,c1' |] <~ g -> 
   [| c2,c2' |] <~ g -> 
   [| [If e then c1 else c2], [If e then c1' else c2'] |] <~ g. 
  Proof.
   unfold triple; intros.
   repeat rewrite deno_cond_elim.
   case (E.eval_expr e m); auto.
 Qed.

 Lemma triple_nil: [| nil, nil |] <~ fzero _.
 Proof.
   unfold triple; intros.
   repeat rewrite deno_nil_elim; auto.
 Qed.

 Lemma triple_app: forall c1 c2 c1' c2' g h,
   [| c1, c2 |] <~ h -> 
   [| c1', c2' |] <~ g -> 
   [| c1++c1',c2++c2' |] <~ fun (m:Mem.t k) => mu ([[c1]] e1 m) g + h m.
 Proof.
  unfold triple; intros.
  repeat rewrite deno_app_elim.
  rewrite (Uabs_diff_triangle_ineq _ _ (mu ([[c1]] e1 m) (fun m' => mu ([[c2']] e2 m') f))).
  apply Uplus_le_compat.
    rewrite Uabs_diff_mu_compat. 
    refine (mu_monotonic _ _ _ _); refine (ford_le_intro _). 
    intro m'; unfold fabs_diff; apply H0.
    apply H.
 Qed.

(* 
 Lemma triple_call : forall t (p:Proc.proc t) (x:Var.var t) arg X g,
   proc_params e1 p = proc_params e2 p ->
   proc_res e1 p = proc_res e2 p ->
   depend_only_f g X ->
   (forall x, Vset.mem x X -> Var.is_global x) -> 
   [| (proc_body e1 p), (proc_body e2 p) |] <~ g -> 
   [| [x <c- p with arg], [x <c- p with arg] |] <~ g.
 Proof.
  unfold triple; intros.
  repeat rewrite deno_call_elim.
  rewrite <-(init_mem_eq2 e1 _ _ arg _ _ H); trivial.
  rewrite (mu_stable_eq ([[proc_body e2 p]] e2 (init_mem e1 p arg m)) _ 
    (fun m' => f (return_mem e1 x p m m'))); [ | refine (ford_eq_intro _); 
      intro m'; rewrite (return_mem_eq _ _ _ _ _ _ H0); trivial ].
  rewrite H3.
  apply Oeq_le; apply H1.
  red; intros; apply init_mem_global; auto.
 Qed.
*)
 
 Section ADVERSARY.

  Variables PrOrcl PrPriv : PrSet.t.
  Variables Gadv Gcomm :Vset.t.

  Definition all_orc_lossless := forall t (p:Proc.proc t), 
   PrSet.mem (BProc.mkP p) PrOrcl -> lossless e1 (proc_body e1 p).


  (* Hypoteses about the invariant *)
  Variable S: Mem.t k -> Mem.t k -> Prop.
  Hypothesis S_compat_glob_var: forall (m1 m2 m1' m2':Mem.t k),
    S m1 m2 ->
    (forall t (x:Var.var t), Var.is_global x -> m1 x = m1' x) ->
    (forall t (x:Var.var t), Var.is_global x -> ~ Vset.mem x Gadv -> m2 x = m2' x) ->
    S m1' m2'.
  Hypothesis S_refl: forall m, S m m. 
  Hypothesis S_trans: forall m1 m2 m3,
    S m1 m2 -> S m2 m3 -> S m1 m3.


  (* Hypotheses about the bounding function *)
  Variable F:cmd -> env -> Mem.t k -o> U.
  Hypothesis F_app_compat: forall (c1 c1' : cmd),
    (all_orc_lossless -> lossless e1 c1) ->
    [|c1, c1 |]<~ F c1 e1 ->
    (forall m, range (fun m' => S m m') ([[ c1 ]] e1 m)) ->
    (all_orc_lossless -> lossless e1 c1')->
    [|c1', c1' |]<~ F c1' e1  ->
    (forall m, range (fun m' => S m m') ([[ c1' ]] e1 m)) ->
    forall m, 
      F c1 e1 m + mu ([[c1]] e1 m) (F c1' e1) <= F (c1 ++ c1') e1 m.
  Hypothesis F_if_compat: forall c1 c2,
    (all_orc_lossless -> lossless e1 c1) ->
    [|c1, c1 |]<~ F c1 e1 ->
    (forall m, range (fun m' => S m m') ([[ c1 ]] e1 m)) ->
    (all_orc_lossless -> lossless e1 c2)->
    [|c2, c2 |]<~ F c2 e1  ->
    (forall m, range (fun m' => S m m') ([[ c2 ]] e1 m)) ->
    forall (b:E.expr T.Bool) (m:Mem.t k), 
    (if E.eval_expr b m then F c1 e1 m else F c2 e1 m) <=
    F [If b then c1 else c2] e1 m.
  Hypothesis F_calls_compat: forall t (x: Var.var t),
    WFWrite Gadv x ->
    forall (f: Proc.proc t) args m,
    F (proc_body e1 f) e1 (init_mem e1 f args m) <= F [x <c- f with args] e1 m.


  (* Hypotheses about the environments *)
  Hypothesis procs_params: forall t (p:Proc.proc t), 
   proc_params e1 p = proc_params e2 p.
  Hypothesis procs_res: forall t (p:Proc.proc t), 
   proc_res e1 p = proc_res e2 p.
  Hypothesis Adv_bodies: forall t (p:Proc.proc t), 
   ~ PrSet.mem (BProc.mkP p) PrOrcl ->
   ~ PrSet.mem (BProc.mkP p) PrPriv ->
   proc_body e1 p = proc_body e2 p.


  (* Hypotheses about the oracles *)  
  Hypothesis Orcl_dist: forall t  (p:Proc.proc t), 
   PrSet.mem (BProc.mkP p) PrOrcl ->
   [| (proc_body e1 p), (proc_body e2 p) |] <~ F (proc_body e1 p) e1.
  Hypothesis Orcl_range: forall t (p:Proc.proc t), 
   PrSet.mem (BProc.mkP p) PrOrcl ->
   forall m, range (fun m' => S m m') ([[proc_body e1 p]] e1 m).


  Lemma triple_adv : forall ca I O,
    WFAdv_c PrOrcl PrPriv Gadv Gcomm e1 I ca O ->
    (forall x, Vset.mem x I -> Var.is_local x) ->
       [| ca,ca |] <~ F ca e1 /\ 
       (forall m, range (fun m' => S m m') ([[ ca ]] e1 m)) /\
       (all_orc_lossless -> lossless e1 ca).
   Proof.
    intros c I O Hwf Hloc.
    generalize (eq_refl c); generalize c at 2 4.
    induction Hwf using WFAdv_c_prop with
     (P0 := fun I i O (H:WFAdv_i PrOrcl PrPriv Gadv Gcomm e1 I i O) => 
      (forall x : VarP.Edec.t, Vset.mem x I -> Var.is_local x) -> forall i', i=i' -> 
        ([| [i],[i'] |] <~ F [i] e1) /\ 
        (forall m, range (fun m' => S m m') ([[ [i] ]] e1 m)) /\
        (all_orc_lossless -> lossless e1 [i])).

    (* nil *)
    intros c' Hc; subst; split; [ |split].
      (* dist *)
      rewrite <-(fle_zero (F _ _)); apply triple_nil.
      (* range *)
      intros m f Hf; rewrite deno_nil_elim.
      apply (Hf _ (S_refl _)).
      (* lossless *)
      intros _; apply lossless_nil.

    (* cons *)
    intros c' Hc; subst.
    change (i::c) with ([i]++c).    
    destruct (IHHwf Hloc _ (eq_refl _)) as [H1 [H2 H3] ].
    destruct (IHHwf0 (fun x Hx => WFAdv_i_local w Hloc x Hx) _ (eq_refl _)) as [H4 [H5 H6] ].
    split; [ | split].
      (* dist *)
      apply triple_weaken with (fun m => mu ([[ [i] ]] e1 m) (F c e1) + F [i] e1 m).  
        refine (ford_le_intro _); intro m; rewrite Uplus_sym; apply F_app_compat; assumption.
      apply triple_app; assumption.
      (* range *)
      intros m1 f Hf; rewrite deno_app_elim.
      apply H2.
      intros m2 Hm2; apply H5.
      intros m3 Hm3; apply (Hf _ (S_trans Hm2 Hm3)).
      (* lossless *)
      intro H7; apply (lossless_app (H3 H7) (H6 H7)).

    (* assignment *)
    intros i' Hi; subst; split; [ |split].
      (* dist *)
      rewrite <-(fle_zero (F _ _)); apply triple_ass.
      (* range *)
      intros m f Hf; rewrite deno_assign_elim.
      apply Hf.
      apply (S_compat_glob_var (S_refl m)).
        auto.
        intros t' x' Hx' H'.
        apply req_mem_upd_disjoint with {{x'}}.  
          apply not_true_is_false; apply (@VsetP.singleton_mem_diff  x' x).
          intro H; rewrite <-H in w; elim H'; exact (w Hx').
          apply (Vset.singleton_correct (VarP.Edec.eq_refl x')). 
      (* lossless *)
      intros _; apply lossless_assign.

    (* random sampling *)
    intros i' Hi; subst; split; [ |split].
      (* dist *)
      rewrite <-(fle_zero (F _ _)); apply triple_rand.
      (* range *)
      intros m f Hf.
      rewrite deno_random_elim.
      match goal with |- _ == fmonot (mu ?d) ?g =>
        rewrite <-(mu_0 d); apply mu_stable_eq; refine (ford_eq_intro _) 
      end.
      intro m'. 
      apply Hf.
      apply (S_compat_glob_var (S_refl m)).
        auto.
        intros t' x' Hx' H'.
        apply req_mem_upd_disjoint with {{x'}}.
          apply not_true_is_false; apply (@VsetP.singleton_mem_diff  x' x).
          intro H; rewrite <-H in w; elim H'; exact (w Hx').
          apply (Vset.singleton_correct (VarP.Edec.eq_refl x')). 
      (* lossless *)
      intros _; apply lossless_random.

    (* conditional *)
    intros i' Hi; subst.
    destruct (IHHwf1 Hloc _ (eq_refl _)) as [H1 [H2 H3] ]; clear IHHwf1.
    destruct (IHHwf2 Hloc _ (eq_refl _)) as [H4 [H5 H6] ]; clear IHHwf2.
    split; [ |split].
      (* dist *)
      unfold triple; intros m f.
      rewrite deno_cond_elim, deno_cond_elim, <-(F_if_compat); trivial.
      case (E.eval_expr e m); auto.
      (* range *)
      intros m f Hf; rewrite deno_cond_elim.
      case (E.eval_expr e m); [ exact (H2 m _ Hf) | exact (H5 m _ Hf) ].
      (* lossless *)
      intro H7; apply (lossless_cond _ (H3 H7) (H6 H7)).

    (* while *)
    admit.

    (* oracle call *)
    intros i' Hi; subst;  split; [ |split].
      (* dist *)
      intros m g.
      repeat rewrite deno_call_elim.
      rewrite <-(init_mem_eq2 e1 e2 f args args m); [ | auto | auto ].
      rewrite (mu_stable_eq ([[proc_body e2 f]] e2 (init_mem e1 f args m)) _ 
        (fun m' => g (return_mem e1 x f m m'))); [ | refine (ford_eq_intro _); 
          intro m'; rewrite (return_mem_eq e1 e2 f x m m'); auto ].  
      rewrite <-(F_calls_compat w0).
      apply Orcl_dist; assumption.
      (* range *)
      intros m g Hg; rewrite deno_call_elim.
      apply (Orcl_range _ i).  
      intros m' Hm'; apply Hg.
      apply (S_compat_glob_var Hm').
        apply init_mem_global.
        intros t' x' H1x' H2x'; symmetry.
        refine (return_mem_global _ _ _ _ _ H1x').
        intro H; rewrite H in w0; elim H2x'; exact (w0 H1x').
      (* lossless *)
      intro H7; apply (lossless_call _ _ _ (H7 _ _ i)).
    (* other adversary call *)
    intros i' Hi; subst.
    assert (H:forall x': VarP.Edec.t,
      Vset.mem x' (Vset_of_var_decl (proc_params e1 f)) -> Var.is_local x').
      intros (t0, x0) Hx0.
        apply Vset_of_var_decl_ind with (P:=fun t (x:Var.var t) => Var.is_local x) (lv:=proc_params e1 f).
          intros; change (Var.vis_local x1); apply proc_params_local with e1 t f; trivial.
          trivial.
    split; [ |split].
      (* dist *)
      intros m g.
      repeat rewrite deno_call_elim.
      rewrite <-(init_mem_eq2 e1 e2 f args args m); [ | auto | auto ].
      rewrite (mu_stable_eq ([[proc_body e2 f]] e2 (init_mem e1 f args m)) _ 
        (fun m' => g (return_mem e1 x f m m'))); [ | refine (ford_eq_intro _); 
          intro m'; rewrite (return_mem_eq e1 e2 f x m m'); auto ].  
      rewrite <-(F_calls_compat w1).
      refine (proj1 (IHHwf H _ (Adv_bodies _ _ _)) _ _); assumption.
      (* range *)
      intros m g Hg; rewrite deno_call_elim.
      apply (proj1 (proj2 (IHHwf H _ (eq_refl _))) _).
      intros m' Hm'; apply Hg.
      apply (S_compat_glob_var Hm').
        apply init_mem_global.
        intros t' x' H1x' H2x'; symmetry.
        refine (return_mem_global _ _ _ _ _ H1x').
        intro H'; rewrite H' in w1; elim H2x'; exact (w1 H1x').
      (* lossless *)
       intro H7; apply lossless_call. 
       apply (proj2 (proj2 (IHHwf H _ (eq_refl _))) H7).
  Qed.


  Lemma triple_adv_Call : forall t (x:Var.var t) (A:Proc.proc t) arg,
     ~ PrSet.mem (BProc.mkP A) PrOrcl ->
     ~ PrSet.mem (BProc.mkP A) PrPriv ->
     WFAdv PrOrcl PrPriv Gadv Gcomm e1 A ->
     (forall x, Vset.mem x (Vset_of_var_decl (proc_params e1 A)) -> Var.is_local x) ->
     [| [x <c- A with arg], [x <c- A with arg]  |] <~ 
     fun m => F (proc_body e1 A) e1 (init_mem e1 A arg m). 
  Proof.
    intros t x A arg H1 H2 [O [HWF H3] ] H4 m f.
    repeat rewrite deno_call_elim.
    rewrite <-(init_mem_eq2 e1 e2 A arg arg m); [ | auto | auto ].
    rewrite (mu_stable_eq ([[proc_body e2 A]] e2 (init_mem e1 A arg m)) _ 
        (fun m' => f (return_mem e1 x A m m'))); [ | refine (ford_eq_intro _); 
          intro m'; rewrite (return_mem_eq e1 e2 A x m m'); auto ].  
    rewrite <-( Adv_bodies _ H1 H2).
    apply (proj1 (triple_adv HWF H4)).
  Qed. 


 End  ADVERSARY.

End TRIPLE.



(* INSTANTIATION OF THE ADVERSARY RULE *)
Section TRIPLE_EXPR.

  Variables PrOrcl PrPriv : PrSet.t.
  Variables Gadv Gcomm :Vset.t.


 (* Hypotheses about the environments *)
  Variables e1 e2: env.
  Hypothesis procs_params: forall t (p:Proc.proc t), 
   proc_params e1 p = proc_params e2 p.
  Hypothesis procs_res: forall t (p:Proc.proc t), 
   proc_res e1 p = proc_res e2 p.
  Hypothesis Adv_bodies: forall t (p:Proc.proc t), 
   ~ PrSet.mem (BProc.mkP p) PrOrcl ->
   ~ PrSet.mem (BProc.mkP p) PrPriv ->
   proc_body e1 p = proc_body e2 p.



  (* Invariant definition and properties *)
  Variable e : E.expr T.Nat.
  Hypothesis fv_e_global: forall x, Vset.mem x (fv_expr e) -> Var.is_global x.
  Hypothesis fv_e_Gadv: forall x, Vset.mem x (fv_expr e) -> ~ Vset.mem x Gadv.
  Let S k (m m':Mem.t k) := (E.eval_expr e m <= E.eval_expr e m')%nat.

  Implicit Arguments S [k].
  Hint Unfold S.

  Lemma S_compat_glob_var: forall k (m1 m2 m1' m2':Mem.t k),
    S m1 m2 ->
    (forall t (x:Var.var t), Var.is_global x -> m1 x = m1' x) ->
    (forall t (x:Var.var t), Var.is_global x -> ~ Vset.mem x Gadv -> m2 x = m2' x) ->
    S m1' m2'.
  Proof.
   unfold S; intros k m1 m2 m1' m2' H1 Hl Hr.
   rewrite <-(@depend_only_fv_expr _ e _ m1 m1'); [ | intros t x Hx; auto ].
   rewrite <-(@depend_only_fv_expr _ e _ m2 m2'); [ | intros t x Hx; auto ].
   assumption.
  Qed.

  Lemma S_refl: forall k (m:Mem.t k), S m m. 
  Proof. auto. Qed.

  Lemma S_trans: forall k (m1 m2 m3:Mem.t k),
    S m1 m2 -> S m2 m3 -> S m1 m3.
  Proof. eauto using le_trans. Qed.



  (* Bounding-function definition and properties *)
  Variable h: nat -> U.
  Hypothesis h_wretract: wretract h. 

  Lemma h_non_overflow: forall a b c,
     sum_f a b h <= [1-] sum_f b c h.
  Proof.
    apply wretract_sum_f; assumption.
  Qed.
   
  Let F k (c:cmd) (E:env) := 
     fun (m:Mem.t k) => mu ([[ c ]] E m)
       (fun m' => sum_f (E.eval_expr e m) (E.eval_expr e m') h).
  Implicit Arguments F [k].

  Lemma F_app: forall (k:nat) (c1 c1' : cmd),
    lossless e1 c1  ->
    (forall m, range (fun m' => @S k m m') ([[ c1 ]] e1 m)) ->
    lossless e1 c1' ->
    (forall m, range (fun m' => @S k m m') ([[ c1' ]] e1 m)) ->
    forall (m:Mem.t k), 
      mu ([[c1]] e1 m) (F c1' e1) + F c1 e1 m == F (c1 ++ c1') e1 m.
  Proof.
   unfold F; intros k c1 c1' H1 H2 H3 H4 m.
   rewrite deno_app_elim.
   transitivity (
      (mu ([[ c1 ]] e1 m) (fun m' => mu ([[c1']] e1 m') (fun m'' =>
        sum_f (E.eval_expr e m') (E.eval_expr e m'') h))) +
      (mu ([[ c1 ]] e1 m) (fun m' => mu ([[c1']] e1 m') (fcte _
        (sum_f (E.eval_expr e m) (E.eval_expr e m') h))))).
      (* left ineq *)
      apply Uplus_eq_compat.
        trivial.
        apply mu_stable_eq; refine (ford_eq_intro _); intros m'.
        rewrite mu_cte, (H3 _ m'); auto.
      (* right ineq *)
      rewrite <-(@mu_stable_plus _ _ _ _).
      apply (range_eq (H2 _)); intros m' Hm'; unfold fplus.
      rewrite <-mu_stable_plus_range; [ | apply (H4 _) |
        intros m'' Hm''; apply h_non_overflow  ].
        apply (range_eq (H4 _)); intros m'' Hm''; unfold fplus, fcte. 
        rewrite Uplus_sym; symmetry; apply sum_f_split; assumption.
      unfold fplusok; refine (ford_le_intro _); intro m''; unfold finv.
      apply mu_fplusok; unfold fplusok, finv, fcte.
      refine (ford_le_intro _); intro m'''.
      apply Uinv_le_perm_right; apply h_non_overflow.
  Qed.

  Lemma F_if: forall c1 c2 (b:E.expr T.Bool) k (m:Mem.t k), 
    (if E.eval_expr b m then F c1 e1 m else F c2 e1 m) ==
    F [If b then c1 else c2] e1 m.
  Proof.
   unfold F; intros.
   rewrite deno_cond_elim; case (E.eval_expr b m); trivial.
  Qed.

  Lemma F_calls: forall t (x: Var.var t),
    WFWrite Gadv x ->
    forall (f: Proc.proc t) args k (m:Mem.t k),
    F (proc_body e1 f) e1 (init_mem e1 f args m) == F [x <c- f with args] e1 m.
  Proof.
    unfold F; intros.
    rewrite deno_call_elim.
    apply mu_stable_eq; refine (ford_eq_intro _); intro m'.
    rewrite (@depend_only_fv_expr _ e _ (init_mem e1 f args m) m).
    rewrite <-(@depend_only_fv_expr _ e _ (return_mem e1 x f m m') m'); trivial.
      intros t' x' Hx'; apply return_mem_global.
        intro H'; rewrite H' in H; elim (fv_e_Gadv _ Hx'); 
          exact (H (fv_e_global _ Hx')).
        exact (fv_e_global _ Hx').
      intros t' x' Hx'; apply (init_mem_global _ _ _ _ _ (fv_e_global _ Hx')).
   Qed.


  Notation "'[|' c1 ',' c2  '|]' '<~' g" := (triple e1 e2 c1 c2 g) (at level 50).

  (* Hypotheses about the oracles *)  
  Hypothesis Orc_lossless: all_orc_lossless e1 PrOrcl.
  Hypothesis Orcl_dist: forall t  (p:Proc.proc t) k, 
   PrSet.mem (BProc.mkP p) PrOrcl ->
   [| (proc_body e1 p), (proc_body e2 p) |] <~ @F k (proc_body e1 p) e1.
  Hypothesis Orcl_range: forall t (p:Proc.proc t) k, 
   PrSet.mem (BProc.mkP p) PrOrcl ->
   forall m, range (fun m' => @S k m m') ([[proc_body e1 p]] e1 m).


  Hint Resolve S_compat_glob_var S_refl S_trans F_app F_if F_calls.

  Lemma triple_adv_call_expr : forall t (x:Var.var t) (A:Proc.proc t) arg k,
    ~ PrSet.mem (BProc.mkP A) PrOrcl ->
    ~ PrSet.mem (BProc.mkP A) PrPriv ->
    WFAdv PrOrcl PrPriv Gadv Gcomm e1 A ->
    (forall x, Vset.mem x (Vset_of_var_decl (proc_params e1 A)) -> Var.is_local x) ->
    [| [x <c- A with arg], [x <c- A with arg]  |] <~ 
    fun m => @F k (proc_body e1 A) e1 (init_mem e1 A arg m). 
   Proof.
    intros.
    apply triple_adv_Call with PrOrcl PrPriv Gadv Gcomm (@S k); trivial.
      apply S_compat_glob_var.
      apply S_trans.
      intros c1 c2 H4 _ H5 H6 _ H7 m; rewrite Uplus_sym;
        apply (F_app  (H4 Orc_lossless) H5 (H6 Orc_lossless) H7).
      intros c1 c2 _ _ _ _ _ _ b m; apply F_if.
      intros; apply Oeq_le; apply F_calls; assumption.
      intros; apply Orcl_dist; assumption.
      intros; apply Orcl_range; assumption.
  Qed.

End TRIPLE_EXPR.
