Require Export eLift.
Require Export SD.
Require Export SD_Others.

Set Implicit Arguments.


(*********************** SOME AUXILIARY STUFF ***********************)
(********************************************************************)

 Definition uncurry (A B C:Type) (f : A -> B -> C) : A * B -> C :=
  fun ab => f (fst ab) (snd ab). 

 Lemma discr_srange: forall (A:Type) (d:Distr A)  
  (Hdiscr: is_Discrete d) (carA: A -> MF A),
  (forall a, cover (fun x => a = x) (carA a)) ->
  srange (fun a => exc (fun k => a = D_points Hdiscr k) /\ ~ mu d (carA a) == 0) d.
 Proof.
  intros.
  split.
    (* range *)
    intros f Hf.
    rewrite (mu_is_Discrete _ H Hdiscr); destruct Hdiscr; simpl in *.
    symmetry; apply serie_zero.
    intro k.
    apply (Ueq_orc (mu d (carA (D_points k))) 0); [ auto | | ]; intro Hk.
      unfold coeff; rewrite Hk; repeat Usimpl; trivial.
      rewrite <-Hf; [ auto | ];
        split; [ apply exc_intro with k | ]; trivial.
    (* drange *)
    intro f.
    rewrite (mu_is_Discrete _ H Hdiscr).
    intros Hf a [H1 H2]; simpl in *.
    generalize (serie_zero_elim _ (Oeq_sym Hf)); clear Hf; intro Hf.
    assert (H': exc (In_class eq (D_points Hdiscr) a)).
      apply H1;[auto | ].
      induction x using Wf_nat.lt_wf_ind; intros.
      apply (cover_elim (cover_not_first_repr _ _ H (D_points Hdiscr)) x);  
        [ auto | | ]; intros [H5 H6].
        apply exc_intro with x. 
        split; [ | red;intros;elim H5;apply exc_intro with k0];auto.
        apply H5;[auto | ].
        intros m (H7, H8);apply (H0 m); [ | rewrite <-H8 ]; auto.
    clear H1; apply H'; [ auto | intros k [Hk Hk']; subst; clear H' ].
    apply (Umult_zero_simpl_right (Oeq_sym (Hf k))).
    apply (cover_elim  (cover_not_first_repr _ _ H (D_points Hdiscr)) k); 
      [ auto | | ]; intros [H4 H5]. 
      unfold coeff; rewrite H5; repeat Usimpl; auto.
      apply H4; [auto | intros k2 [Hk2 Hk2'] ]; generalize (Hk' _ Hk2); tauto.
 Qed.

 Lemma discr_ext: forall (A:Type) (d1 d2: Distr A),
   (forall f, mu d1 f == 0 -> mu d2 f == 0) ->
   is_Discrete d1 ->
   is_Discrete d2.
 Proof.
  intros A d1 d2 Hd [p Hdis1].
  apply mkDiscr with p.
  unfold Discrete in *.
  intros f Hf.
  symmetry; apply Hd. 
  symmetry; apply (Hdis1 _ Hf).
 Qed.


(* Given a distribution on a product, if both projections  *
 * are discrete, then the distribution is discrete.        *)
Section DISCRETE.

 Variables A B: Type.

 Variable carB : B -> MF B.
 Variable carA : A -> MF A.
 
 Hypothesis carB_prop : forall b, cover (fun x => b = x) (carB b).
 Hypothesis carA_prop : forall a, cover (fun x => a = x) (carA a).

 Variable d  : Distr (A * B).
 
 Hypothesis discr_d1: is_Discrete (Mlet d (fun ab => Munit (fst ab))).
 Hypothesis discr_d2: is_Discrete (Mlet d (fun ab => Munit (snd ab))).


 Lemma discr_projs: is_Discrete d.
 Proof.
  destruct discr_d1 as [p1 H1]. 
  destruct discr_d2 as [p2 H2].
  apply mkDiscr with (fun k => (p1 (fst (bij_n_nxn k)), p2 (snd (bij_n_nxn k)))).
  unfold Discrete, range in *; simpl in *.
  intros f Hf.
  rewrite (d_ito_p2_d _ carB_prop discr_d2); simpl.
  apply H2 with (f:= fun b => 
      (mu d) (fun ab : A * B => carB b (snd ab) * f ab) /
      (mu d) (fun ab : A * B => carB b (snd ab))).
  intros b Hb; apply Hb; [ auto | intros kb Hkb ].
  symmetry; apply Udiv_zero_eq.

  transitivity (mu (d_inv d) (fun ba => carB b (fst ba) * f (snd ba, fst ba)));
    [ | simpl; apply (mu_stable_eq d); refine (ford_eq_intro _); intros (a',b'); auto ].
  rewrite (d_ito_p2_d _ carA_prop); [ simpl |
    refine (is_Discrete_eq_compat _  discr_d1); auto ].
  apply H1 with (f:= fun a  => mu d
    (fun ab => carA a (fst ab) * (carB b (snd ab) * f (fst ab, snd ab))) /
    mu d (fun ab => carA a (fst ab))).
  intros a Ha; apply Ha; [ auto | intros ka Hka ].
  symmetry; apply Udiv_zero_eq.

  rewrite <-(mu_zero d); unfold fzero;
  apply mu_stable_eq; refine (ford_eq_intro _).
  intros (a',b'); simpl.
  apply (cover_elim (carB_prop b) b'); [ auto | | ]; intros [H4 H5].
    rewrite H5; repeat Usimpl; trivial.
    rewrite H5, <-H4; Usimpl; clear H4 H5.
    apply (cover_elim (carA_prop a) a'); [ auto | | ]; intros [H4 H5].
      rewrite H5; repeat Usimpl; trivial.
      rewrite H5, <-H4; Usimpl; clear H4 H5.
      apply Hf.
      destruct (bij_surj ka kb) as [k Hk].
      apply exc_intro with k.
      rewrite Hk; simpl; rewrite Hkb, Hka; trivial.
 Qed.

End DISCRETE.



(********************************************************************)
(********************************************************************)


Module Make (SemO:SEM_OPT).

 Module OPT2 := SD_Others.Make SemO.
 Export OPT2.

 Set Implicit Arguments.

 Definition eequiv (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) (ep:nat-o>U) :=
  forall k, exists d,
   forall (m1 m2 : Mem.t k),
   P _ m1 m2 ->
   elift (@Q k) (d m1 m2) ([[c1]] E1 m1)  ([[c2]] E2 m2) (ep k).


 Lemma eequiv_deno: forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) ep,
  eequiv P E1 c1 E2 c2 Q ep -> prg_SD P E1 c1 E2 c2 Q ep.
 Proof.
  unfold eequiv, prg_SD; intros.
  destruct (H k) as [d Hd]; clear H.
  apply elift_dist with (Q k) (d m1 m2); auto.
 Qed.     

 Lemma eequiv_sdeno: forall c1 E1 c2 E2 (P Q: mem_rel) ep,
   decMR P ->
   eequiv P E1 c1 E2 c2 Q ep ->
   forall k (d1 d2 : Distr(Mem.t k)) (del:nat -o> U), 
   (exists d, elift (@P k) d d1 d2 (del k) /\ exists R, srange R d) ->
   forall f g,
   (forall m1 m2 : Mem.t k, Q k m1 m2 -> f m1 == g m2) ->
   Uabs_diff (mu (Mlet d1 ([[c1]] E1)) f) (mu (Mlet d2 ([[c2]] E2)) g) <= (ep k + del k).
 Proof.
  intros.
  destruct H0 as [d [Hd HdR] ].
  destruct (H k) as [d' Hd']; clear H.
  apply elift_dist with (R:=Q k) (d:=Mlet d (fun mm => d' (fst mm) (snd mm))).
    assumption.
    apply elift_Mlet with (P k); try assumption.
      exists (carac (fun mm => X k (fst mm) (snd mm)));
        apply (cover_dec (fun mm => X k (fst mm) (snd mm))).
 Qed.

 Lemma eequiv_sdeno_case: forall  (P P':mem_rel) E1 c1 E2 c2 Q ep1 ep2
   (P_dec: decMR P) (P'_dec: decMR P') k (d1 d2: Distr(Mem.t k)) (del:nat -o> U) d,
   eequiv (P /-\ P') E1 c1 E2 c2 Q ep1 ->
   eequiv (P /-\ ~-P') E1 c1 E2 c2 Q ep2 ->
   (elift (@P k) d d1 d2 (del k) /\ exists R, srange R d) ->
   ep1 k < 1 ->
   ep2 k < 1 ->
   let pt := mu d (charfun (fun mm => if (P'_dec k (fst mm) (snd mm)) then true else false)) in 
   let pf := mu d (charfun (negP (fun mm => if (P'_dec k (fst mm) (snd mm)) then true else false))) in 
   exists d',  
     elift (Q k) d' (Mlet d1 (([[ c1 ]]) E1)) (Mlet d2 (([[ c2 ]]) E2))
     (ep1 k * pt + ep2 k * pf + del k).
 Proof.
  intros.
  destruct H1 as [Hd HdR].
  destruct (H k) as [dt Hdt]; clear H.
  destruct (H0 k) as [df Hdf]; clear H0.
  set (Cond := fun mm => if (P'_dec k (fst mm) (snd mm)) then true else false).
  exists (Mlet d (fun mm => if Cond mm then uncurry dt mm else uncurry df mm)).
  apply elift_MletCase with (R1:=P k); trivial.
    exists (carac (fun mm => P_dec k (fst mm) (snd mm)));
      apply (cover_dec (fun mm => P_dec k (fst mm) (snd mm))).
    intros; apply Hdt; split.
      trivial.
      generalize H0; unfold Cond; simpl; case (P'_dec k x y); [ trivial | discriminate ].
    intros; apply Hdf; split.
      trivial.
      generalize H0; unfold Cond; simpl; case (P'_dec k x y); [ discriminate | trivial ].
 Qed.


 Lemma eequiv_weaken: forall P E1 c1 E2 c2 Q ep P' Q' (ep':nat -o> U),
  implMR P P' ->
  implMR Q' Q ->
  ep' <= ep ->
  eequiv P' E1 c1 E2 c2 Q' ep' ->
  eequiv P  E1 c1 E2 c2 Q  ep.
 Proof.
  unfold eequiv; intros.
  destruct (H2 k) as [d Hd]; clear H2.
  exists d.
  intros m1 m2 Hm. 
  apply elift_weaken with (Q' k) (ep' k); auto.
 Qed.

 Add Morphism eequiv with signature 
   implMR --> (@eq env) ==> (@eq cmd) ==> (@eq env) ==> 
   (@eq cmd) ==> implMR ++> (@Ole (ford nat (tcpo U))) ++>
    impl as eequiv_imp_Morph.
 Proof.
  unfold impl; intros.
  apply eequiv_weaken with (4:=H2); assumption.
 Qed.   


 Add Morphism eequiv with signature 
   iffMR ==> (@eq env) ==> (@eq cmd) ==> (@eq env) ==> 
   (@eq cmd) ==> iffMR ==> (@Oeq (ford nat (tcpo U))) ==> 
   iff as eequiv_iff_Morph.
 Proof.
  unfold iffMR; intros. 
  destruct H; destruct H0.
  split; intros.
    apply eequiv_weaken with (4:=H4); auto.
    apply eequiv_weaken with (4:=H4); auto.
 Qed.


 Lemma eequiv_trueR: forall (P:mem_rel) E1 c1 E2 c2 ep1 ep2,
  (forall k (m1 m2:Mem.t k), P _ m1 m2 ->
    ep1 k <=  mu ([[c1]] E1 m1) (fone _) /\
    ep2 k <=  mu ([[c2]] E2 m2) (fone _)) ->
  (forall k (m1 m2:Mem.t k), P _ m1 m2 ->
  ~ mu ([[c1]] E1 m1) (fone _) == 0 /\
  ~ mu ([[c2]] E2 m2) (fone _) == 0) ->
  eequiv P E1 c1 E2 c2 trueR (fun k => [1-] (ep1 k) + [1-] (ep2 k)).
 Proof.
  unfold eequiv; intros.
  exists (fun m1 m2 => prod_distr ([[c1]] E1 m1) ([[c2]] E2 m2)).
  intros m1 m2 Hm.
  eapply elift_weaken; [ | | apply (@elift_true _ _ ([[c1]] E1 m1) ([[c2]] E2 m2)) ].
    auto.
    apply Uplus_le_compat; Usimpl.
      exact (proj1 (H _ _ _ Hm)).
      exact (proj2 (H _ _ _ Hm)).
    exact (proj1 (H0 _ _ _ Hm)).
    exact (proj2 (H0 _ _ _ Hm)).
 Qed.


 Lemma eequiv_trueR_lossless: forall (P:mem_rel) E1 c1 E2 c2,
   lossless E1 c1 -> 
   lossless E2 c2 -> 
   eequiv P E1 c1 E2 c2 trueR (fzero _).
 Proof.
  intros.
  apply eequiv_weaken with P trueR (fun k => [1-] fone _ k + [1-] fone _ k).
    trivial.
    trivial.
    unfold fzero, fone; refine (ford_le_intro _); intro k; rewrite Uinv_one; auto.
    apply eequiv_trueR.
      intros k m1 m2 Hm; split; [ rewrite (H _ m1) | rewrite (H0 _ m2) ]; trivial.
      intros k m1 m2 Hm; split; [ rewrite (H _ m1) | rewrite (H0 _ m2) ]; auto.
 Qed.


 Lemma eequiv_falseR: forall E1 c1 E2 c2 Q,
  eequiv falseR E1 c1 E2 c2 Q (fzero _).
 Proof.
  unfold eequiv; intros.
  exists (fun _ _ => distr0 _).
  unfold falseR; intros m1 m2 H; tauto.
 Qed.

 Hint Resolve eequiv_falseR.


 Lemma eequiv_transp: forall P E1 c1 E2 c2 Q ep,
   eequiv (transpR P) E2 c2 E1 c1 (transpR Q) ep ->
   eequiv P E1 c1 E2 c2 Q ep.
 Proof.
  unfold eequiv, transpR; intros.
  destruct (H k) as [d Hd]; clear H.
  exists (fun m1 m2 => Mlet (d m2 m1) (fun mm => Munit (snd mm, fst mm))).
  intros.
  apply elift_transp.
  apply elift_stable_eq with (5:=Hd _ _ H); auto.
    rewrite Mcomp, <-(Mext (d m2 m1)) at 1.
    apply Mlet_eq_compat; trivial.
    refine (ford_eq_intro _); intros (m1',m2'); auto.
 Qed.


 Lemma eequiv_sym :  forall P E1 c1 E2 c2 Q ep,
  symMR P ->
  symMR Q ->
  eequiv P E2 c2 E1 c1 Q ep ->
  eequiv P E1 c1 E2 c2 Q ep.
 Proof.
  intros.
  apply eequiv_transp.
  unfold symMR in *; rewrite H, H0; trivial.
 Qed.


 Lemma eequiv_case: forall  (P P':mem_rel) E1 c1 E2 c2 Q ep,
   decMR P' ->
   eequiv (P /-\ P') E1 c1 E2 c2 Q ep ->
   eequiv (P /-\ ~-P') E1 c1 E2 c2 Q ep ->
   eequiv P E1 c1 E2 c2 Q ep. 
 Proof.
  unfold andR, notR, eequiv; intros.
  destruct (H k) as (dt,Hdt); destruct (H0 k) as (df,Hdf); clear H H0.
  exists (fun m1 m2 => if X k m1 m2 then dt m1 m2 else df m1 m2); intros.
  destruct (X k m1 m2); auto.
 Qed.


 Lemma eequiv_nil: forall P E1 E2, 
   eequiv P E1 nil E2 nil P (fzero _).
 Proof.
  unfold eequiv; intros.
  exists (fun m1 m2 => Munit (m1, m2)); intros.
  repeat rewrite deno_nil. 
  apply (elift_Munit _ _ _ H).
 Qed.


 Lemma elift_deno_witness_discr_Mlet: forall (c1 c2:cmd) e1 e2 k (d1 d2: Distr (Mem.t k))
  d R ep,
  is_Discrete d1 ->
  is_Discrete d2 ->
  elift R d (Mlet d1 ([[c1]] e1)) (Mlet d2 ([[c2]] e2)) ep ->
  is_Discrete d.
 Proof.
  intros.
  destruct H as (_, _, Hl, Hr).
  apply discr_projs with (carA:=@mem_eqU k) (carB:=@mem_eqU k).
    apply mem_eqU_spec.
    apply mem_eqU_spec.
    apply discr_ext with (Mlet d1 ([[c1]] e1)).
      intros f Hf; apply (proj2 (Hl f) Hf).
      apply is_Discrete_Mlet; trivial.
        apply sem_discr.
    apply discr_ext with (Mlet d2 ([[c2]] e2)).
      intros f Hf; apply (proj2 (Hr f) Hf).
      apply is_Discrete_Mlet; trivial.
        apply sem_discr.
 Qed.

 Lemma elift_deno_witness_discr: forall (c1 c2:cmd) e1 e2 k (m1 m2:Mem.t k) d R ep,
  elift R d ([[c1]] e1 m1) ([[c2]] e2 m2) ep ->
  is_Discrete d.
 Proof.
  intros.
  apply elift_deno_witness_discr_Mlet with 
    c1 c2 e1 e2 (Munit m1) (Munit m2) R ep.
    apply is_Discrete_Munit.
    apply is_Discrete_Munit.
    apply elift_stable_eq with d (([[ c1 ]]) e1 m1) (([[ c2 ]]) e2 m2) ep; trivial.
      rewrite Mlet_unit; trivial.
      rewrite Mlet_unit; trivial.
 Qed.


 Lemma eequiv_seq: forall P E1 c1 E2 c2 Q' ep Q c1' c2' ep',
   decMR Q' ->
   eequiv P E1 c1  E2 c2 Q' ep ->
   eequiv Q' E1 c1' E2 c2' Q ep' ->
   eequiv P E1 (c1 ++ c1') E2 (c2 ++ c2') Q (fplus ep' ep).
 Proof.
   unfold eequiv; intros.
   destruct (H k) as (d, Hd); destruct (H0 k) as (d', Hd'); clear H H0.
   exists (fun m1 m2 => Mlet (d m1 m2) (fun p => d' (fst p) (snd p))). 
     intros.
     repeat rewrite deno_app.
     apply elift_Mlet with (Q' k); auto.
       exists (carac (fun mm => X k (fst mm) (snd mm))).
         apply (cover_dec (fun mm => X k (fst mm) (snd mm))).
         eexists; apply (discr_srange (elift_deno_witness_discr (Hd _ _ H)) _ 
           (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k))).
 Qed.


 Lemma eequiv_trans_l : forall (P1 P2 Q1 Q2 Q3:mem_rel) E1 c1 E2 c2 E3 c3 ep ep',
  decMR P2 ->
  refl_supMR2 P2 P1 ->
  (forall k x y z, Q1 k x y -> Q2 k y z -> Q3 k x z) -> 
  eequiv P1 E1 c1 E2 c2 Q1 ep-> 
  eequiv P2 E2 c2 E3 c3 Q2 ep'->
  eequiv P2 E1 c1 E3 c3 Q3 (fplus ep ep').
 Proof.
  intros.
  intros k; destruct (H1 k) as (d, Hd); destruct (H2 k) as (d',Hd').
  exists (
   fun m1 m3 =>
    match X k m1 m3 with
    | left _ =>
        dd' (@mem_eqU k) (d m1 m1) (d' m1 m3) ([[c2]] E2 m1)
    | _ => distr0 _
    end).  
  intros m1 m3 HP2.
  destruct (X k m1 m3); simpl.
    (* P m1 m3 *)
    apply elift_trans_discr with (P:=Q1 k) (Q:=Q2 k). 
      apply mem_eqU_spec.
      apply H0.
      apply (Hd _ _ (H _ _ _ p)).
      apply (Hd' _ _ p).
      apply discr_ext with (d1:=[[c2]] E2 m1).
        intros f Hf; apply (proj2 (el_supp_r (Hd _ _ (H _ _ _ p)) f) Hf).
        apply sem_discr.
      apply discr_ext with (d1:=[[c2]] E2 m1).
        intros f Hf; apply (proj2 (el_supp_l (Hd' _ _ p) f) Hf).
        apply sem_discr.
    (* ~P m1 m3 *)
    tauto.
 Qed.


 Lemma eequiv_trans_r : forall (P1 P2 Q1 Q2 Q3:mem_rel) E1 c1 E2 c2 E3 c3 ep ep',
  decMR P1 ->
  refl_supMR2 (transpR P1) (transpR P2) ->
  (forall k x y z, Q1 k x y -> Q2 k y z -> Q3 k x z) -> 
  eequiv P1 E1 c1 E2 c2 Q1 ep -> 
  eequiv P2 E2 c2 E3 c3 Q2 ep' ->
  eequiv P1 E1 c1 E3 c3 Q3 (fplus ep' ep).
 Proof.
  intros; apply eequiv_transp.
  apply eequiv_trans_l with (P1 := transpR P2) (P2:=transpR P1)
   (Q1 := transpR Q2) (Q2 := transpR Q1) (E2 := E2) (c2:= c2).
  auto. 
  trivial.
  unfold transpR; intros; eapply H0; eauto.
  apply eequiv_transp; repeat rewrite transpR_transpR; trivial.
  apply eequiv_transp; repeat rewrite transpR_transpR; trivial.
 Qed.


 Lemma eequiv_trans_trans : forall P Q E1 c1 E2 c2 E3 c3 ep ep',
   decMR P ->
   refl_supMR P ->
   transMR Q ->
   eequiv P E1 c1 E2 c2 Q ep-> 
   eequiv P E2 c2 E3 c3 Q ep'->
   eequiv P E1 c1 E3 c3 Q (fplus ep ep').
 Proof.
  intros; eapply eequiv_trans_l; eauto; trivial.
 Qed.


 Lemma eequiv_cond_l : forall P E1 e c c' E2 c2 Q ep,
  eequiv (P /-\ EP1 e) E1 c E2 c2 Q ep ->
  eequiv (P /-\ ~- EP1 e) E1 c' E2 c2 Q ep ->
  eequiv P E1 [If e then c else c'] E2 c2 Q ep.
 Proof.
  unfold eequiv, andR, notR, EP1, is_true.
  intros P E3 e1 c c' E4 c2 Q ep Ht Hf k.
  destruct (Ht k) as (dt,Hdt); destruct (Hf k) as (df,Hdf); clear Ht Hf.
  exists (fun m1 m2 => if E.eval_expr e1 m1 then dt m1 m2  else df m1 m2). 
  intros.
  repeat rewrite deno_cond.
  case_eq (E.eval_expr e1 m1); intros Heq;
   [ apply Hdt | apply Hdf ]; (split; [ | rewrite Heq]; auto).
 Qed.


 Lemma eequiv_cond_r :  forall P E1 c1 E2 e c c' Q ep,
  eequiv (P /-\ EP2 e) E1 c1 E2 c Q ep ->
  eequiv (P /-\ ~- EP2 e) E1 c1 E2 c' Q ep ->
  eequiv P E1 c1 E2 [If e then c else c'] Q ep.
 Proof.
  unfold eequiv, andR, notR, EP2, is_true.
  intros P E3 c c' e E4 c2 Q ep Ht Hf k.
  destruct (Ht k) as (dt,Hdt); destruct (Hf k) as (df,Hdf); clear Ht Hf.
  exists (fun m1 m2 => if E.eval_expr e m2 then dt m1 m2  else df m1 m2). 
  intros.
  repeat rewrite deno_cond.
  case_eq (E.eval_expr e m2); intros Heq;
   [ apply Hdt | apply Hdf ]; (split; [ | rewrite Heq]; auto).
 Qed.


 Lemma eequiv_cond : forall P Q E1 (e1:E.expr T.Bool) c1 c2 E2 (e2:E.expr T.Bool) c3 c4 ep,
  eequiv (P /-\ (EP1 e1 /-\ EP2 e2)) E1 c1 E2 c3 Q ep ->
  eequiv (P /-\ (~- EP1 e1 /-\ ~- EP2 e2)) E1 c2 E2 c4 Q ep ->
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
  eequiv P E1 [If e1 then c1 else c2] E2 [If e2 then c3 else c4] Q ep.
 Proof.
  intros; apply eequiv_cond_l; apply eequiv_cond_r.
  simplMR; trivial.
  apply eequiv_weaken with falseR Q (fzero _); auto; unfold EP1, EP2.
    intros k m1 m2 ((H2, H3), H4); apply H4; erewrite <-H1; eauto.
  apply eequiv_weaken with falseR Q (fzero _); auto; unfold EP1, EP2.
    intros k m1 m2 ((H2, H3), H4); apply H3; erewrite H1; eauto.
  simplMR; trivial.
 Qed.


Section WHILE.

  Variables c1 c2 : cmd.
  Variables e1 e2 : env.

  Variables I P1 P2: mem_rel.
  Variables b1 b2: E.expr T.Bool.


  Hypothesis I_b: forall k (m1 m2:Mem.t k), 
   I m1 m2 -> E.eval_expr b1 m1 = E.eval_expr b2 m2. 
 
  Hypothesis I_dec: decMR I.

  Hypothesis I_P: forall k (m1 m2:Mem.t k),
    I m1 m2 -> P1 m1 m1 /\ P2 m2 m2.

  Variable ep: nat -o> U.
  Hypothesis Hc:  
    eequiv (I /-\ EP1 b1) e1 c1 e2 c2 I ep.


  Variable q: nat.

  Hypothesis H_while1:
    eequiv 
    (Meq /-\ P1) 
    e1 [while b1 do c1]
    e1 (unroll_while b1 c1 q)
    (Meq /-\ ~-EP2 b1) 
    (fzero _).

  Hypothesis H_while2:
    eequiv 
    (Meq /-\ P2) 
    e2 [while b2 do c2]
    e2 (unroll_while b2 c2 q)
    (Meq /-\ ~-EP2 b2) 
    (fzero _).

  Ltac My_Usimpl :=  (try Usimpl); match goal with
    |- context [(Uabs_diff ?x ?x)] => setoid_rewrite (Uabs_diff_compat_eq x)
  end.

  Lemma deno_unroll_while_0: forall c e b k (m:Mem.t k),
   [[ unroll_while b c 0 ]] e m == Munit m.
  Proof.
   unfold unroll_while; intros.
   rewrite deno_cond.
   case (E.eval_expr b m); apply deno_nil.
  Qed.
  
  Lemma while_rule: 
    eequiv I e1 [while b1 do c1] e2  [while b2 do c2] (I /-\ ~-EP1 b1) 
    (fun k => q */ ep k).
  Proof.
   apply eequiv_weaken with I (I /-\ ~-EP1 b1) (fplus (fzero _) (fplus (fzero _) 
      (fun k => q */ ep k))); trivial.
     unfold fplus, fzero; refine (ford_le_intro _); intro m; auto.
   apply eequiv_trans_l  with (1:=I_dec) (4:=H_while1) (Q2:=I).
     intros k m1 m2 Hm; split; [ trivial | apply (proj1 (I_P Hm)) ].
     intros k m1 m2 m3 [H1 H2] H3; split; rewrite H1; trivial.
   eapply eequiv_trans_r  with (1:=I_dec) (5:=eequiv_transp H_while2) (Q1:=I).
     intros k m1 m2 Hm; split; [ trivial | apply (proj2 (I_P Hm)) ].
     intros k m1 m2 m3 H1 [H2 _]; rewrite H2; trivial.

   clear H_while1 H_while2.
   induction q.
     (* base case *)
     intro k.
     exists (fun m1 m2 => Munit (m1,m2)).
     intros m1 m2 Hm; repeat rewrite deno_unroll_while_0.
     apply (elift_Munit _ _ _ Hm).

     (* inductive case *)
     unfold unroll_while; fold (unroll_while b1 c1 n) (unroll_while b2 c2 n). 
     apply eequiv_cond with (3:=I_b).
       apply eequiv_weaken with (I /-\ EP1 b1) I (fplus (fun k => n */ ep k) ep).
         rewrite <-andR_assoc; apply proj1_MR.
         trivial.
         unfold fplus; refine (ford_le_intro _); intro m; rewrite Uplus_sym; auto.
       apply eequiv_seq with I; trivial.
       apply eequiv_weaken with I I (fzero _).
         apply proj1_MR.
         trivial.
         unfold fzero; refine (ford_le_intro _); intro m; trivial.
       apply eequiv_nil.
 Qed.

 End WHILE.

 Lemma equiv_eequiv: forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel),
   eequiv P E1 c1 E2 c2 Q (fzero _) <-> equiv P E1 c1 E2 c2 Q.
 Proof.
  unfold equiv, eequiv; split; intros.
    (* eequiv ==> equiv *)
    destruct (H k) as [d Hd]; clear H.
    exists d.
      intros m1 m2 H; rewrite <-lift_elift; exact (Hd _ _ H).
    (* equiv ==> eequiv *)
    destruct (H k) as [d Hd]; clear H.
    exists d.
      intros m1 m2 H; rewrite lift_elift; exact (Hd _ _ H).
 Qed.



 (* ONE VARIANT OF EEQUIV *)

 Definition eEqObs I e1 c1 e2 c2 O (ep:nat-o>U) := 
   eequiv (kreq_mem I) e1 c1 e2 c2 (kreq_mem O) ep.


Lemma eEqObs_sym : forall I E1 c1 E2 c2 O ep,
  eEqObs I E1 c1 E2 c2 O ep -> eEqObs I E2 c2 E1 c1 O ep.
 Proof.
  unfold eEqObs; intros; apply eequiv_sym; auto.
 Qed.

 Lemma eEqObs_trans: forall I E1 c1 E2 c2 E3 c3 O ep ep',
   eEqObs I E1 c1 E2 c2 O ep ->
   eEqObs I E2 c2 E3 c3 O ep'->
   eEqObs I E1 c1 E3 c3 O (fplus ep ep').
 Proof.
  unfold eEqObs; intros.
  apply eequiv_trans_trans with E2 c2; auto.
 Qed.
 
(*
 Add Morphism eEqObs 
  with signature Vset.subset ++> (@eq env) ==> (@eq cmd) ==> 
   (@eq env) ==> (@eq cmd) ==> Vset.subset ++> (@Ole (ford nat (tcpo U))) ++> impl 
  as eEqObs_imp_Morph.
 Proof.
  unfold eEqObs, flip, impl; intros.
  eapply eequiv_imp_Morph with (8:=H2); auto.  y0 y1 y2 y3 (kreq_mem y4) 
  rewrite H0, <- H; trivial.
 Qed.
*)

 Lemma eEqObs_Pr2 : forall I E1 c1 E2 c2 O ep,
  eEqObs I E1 c1 E2 c2 O ep ->
  forall e, fv_expr e [<=] O ->
   forall k (m1 m2:Mem.t k), m1 =={I} m2 -> 
   Uabs_diff (Pr E1 c1 m1 (EP k e)) (Pr E2 c2 m2 (EP k e)) <= ep k.
 Proof.
  unfold Pr; intros.
  eapply eequiv_deno with (1:=H); trivial.
    unfold charfun,restr, EP; intros.
    rewrite (@depend_only_fv_expr_subset _ e _ H0 _ _ _ H2); trivial.
 Qed.

 Lemma eEqObs_Pr : forall I E1 c1 E2 c2 e ep,
  eEqObs I E1 c1 E2 c2 (fv_expr e) ep ->
  forall k m, 
   Uabs_diff (Pr E1 c1 m (EP k e)) (Pr E2 c2 m (EP k e)) <= ep k.
 Proof.
  intros; eapply eEqObs_Pr2; eauto with set.
 Qed.

End Make.

(*
 Require Import WhileStuff.

 Section For_loop_rule.
 
  Variables i : E.expr T.Nat.
  
 (* [q] is a constant expression *)
  Variable q: E.expr T.Nat.
  Variable q_interp : nat -> nat.
  Hypothesis Hq_cte : forall k (m:Mem.t k), E.eval_expr q m = q_interp k.

  Variables c1 c2 : cmd.
  Variables e1 e2 : env.

  Variables I: mem_rel.

  (* First argument is the security parameter *)
  Variable h : nat -> nat -o> U.

  Hypothesis Hc: forall n:nat, 
    eequiv 
    (I /-\ EP1 (i=?=n) /-\ EP2 (i=?=n)) 
    e1 c1 e2 c2 
    (I /-\ EP1 (i=?=S n) /-\ EP2 (i=?=S n))
    (fun k => h k n).


  Variable P1 P2: forall k, Mem.t k -> Prop.

  Hypothesis H_P : forall k (m1 m2:Mem.t k), I m1 m2 -> P1 m1 /\ P2 m2.

  Hypothesis Hran1: forall k (m:Mem.t k),
    P1 m -> 
    range (fun m' => E.eval_expr i m' = S (E.eval_expr i m) /\ P1 m') (([[c1]]) e1 m).
  Hypothesis Hran2: forall k (m:Mem.t k),
    P2 m -> 
    range (fun m' => E.eval_expr i m' = S (E.eval_expr i m) /\ P2 m')  (([[c2]]) e2 m).

  Hypothesis I_dec: decMR I.


  Lemma cover_prec: forall (n k:nat),
    cover (prodP ((I /-\ EP1 (i =?= n) /-\ EP2 (i =?= n)) k )) 
     (fun mm => (fun z => if I_dec (fst z) (snd z) then 1 else 0) mm * (
     ((fun z => if nat_eqb (E.eval_expr i (fst z)) n then 1 else 0) mm) * 
     ((fun z => if nat_eqb (E.eval_expr i (snd z)) n then 1 else 0) mm))).
  Proof.
   intros; unfold prodP, andR.
   repeat apply cover_inter_mult.
     apply  (cover_dec (fun mm => @I_dec k (fst mm) (snd mm))).
     unfold cover; unfold EP1; simpl; unfold O.eval_op; simpl.
     intro mm; generalize (nat_eqb_spec (E.eval_expr i (fst mm)) n);
     case (nat_eqb (E.eval_expr i (fst mm)) n); split; intros; trivial.
       generalize is_true_true; tauto.
       discriminate.
     unfold cover; unfold EP2; simpl; unfold O.eval_op; simpl.
     intro mm; generalize (nat_eqb_spec (E.eval_expr i (fst mm)) n);
     case (nat_eqb (E.eval_expr i (snd mm)) n); split; intros; trivial.
       generalize is_true_true; tauto.
       discriminate.
 Qed.


 (* REMARK: wasn't able to weaken the poscondition in [Hc] 
    using [Hran1], [Hran2] and [H_P] *)

  Lemma eequiv_for_loop :  eequiv 
   (I /-\ EP1 (i=?=0%nat) /-\ EP2 (i=?=0%nat)) 
   e1 [ while (i <! q) do c1 ] e2 [ while (i <! q) do c2 ] 
   (I /-\ EP1 (i=?=q) /-\ EP2 (i=?=q))  
   (fun k => sigma (h k) (q_interp k)).
  Proof.
   unfold eequiv; intros.
   cut (exists d: Mem.t k -> Mem.t k -> Distr (Mem.t k * Mem.t k),
     forall m1 m2 : Mem.t k,
     (I /-\ EP1 (i =?= 0%nat) /-\ EP2 (i =?= 0%nat)) k m1 m2 ->
     elift ((I /-\ EP1 (i =?= q_interp k) /-\ EP2 (i =?= q_interp k)) k) 
       (d m1 m2) (([[ [while i <! q_interp k do c1] ]]) e1 m1)
       (([[ [while i <! q_interp k do c2] ]]) e2 m2) ((sigma (h k)) (q_interp k))).
     intros [d Hd].
     exists d; intros m1 m2 Hm.
     eapply elift_weaken with (P:=(I /-\ EP1 (i =?= q_interp k) /-\ EP2 (i =?= q_interp k)) k).
       intros m1' m2' [HI [H1 H2] ]; repeat split; unfold EP1, EP2 in *.
         trivial.
         rewrite <-(Hq_cte m1') in H1; apply H1.
         rewrite <-(Hq_cte m2') in H2; apply H2.
       apply Ole_refl.
     eapply elift_stable_eq with (5:=Hd _ _ Hm); trivial.
     apply eq_distr_intro; intro f.
     apply while_eq_guard_compat_elim. 
     intro m'; change (leb (E.eval_expr i m' + 1) (q_interp k) = 
       leb (E.eval_expr i m' + 1) (E.eval_expr q m')); rewrite Hq_cte; trivial.
     apply eq_distr_intro; intro f.
     apply while_eq_guard_compat_elim. 
     intro m'; change (leb (E.eval_expr i m' + 1) (q_interp k) = 
       leb (E.eval_expr i m' + 1) (E.eval_expr q m')); rewrite Hq_cte; trivial.

   induction (q_interp k).
     (* base case *)
     exists (fun m1 m2 => Munit (m1,m2)).
     intros m1 m2 Hm; constructor.
       (* dist *)
       intros f g.
       repeat rewrite deno_while_elim, deno_cond_elim.
       replace (@E.eval_expr _ T.Bool (i <! 0) m1) with false by 
         (symmetry; apply (leb_correct_conv 0%nat (E.eval_expr i m1 + 1)); omega). 
       replace (@E.eval_expr _ T.Bool (i <! 0) m2) with false by 
         (symmetry; apply (leb_correct_conv 0%nat (E.eval_expr i m2 + 1)); omega). 
       repeat rewrite deno_nil_elim, Munit_eq, Uabs_diff_compat_eq; auto.
       (* range *)
       apply range_Munit; assumption.
       (* supp *)
       intro f.
       rewrite deno_while_elim, deno_cond_elim.
       replace (@E.eval_expr _ T.Bool (i <! 0) m1) with false by 
         (symmetry; apply (leb_correct_conv 0%nat (E.eval_expr i m1 + 1)); omega). 
       rewrite deno_nil_elim, Munit_eq; auto.
       intro g.
       rewrite deno_while_elim, deno_cond_elim.
       replace (@E.eval_expr _ T.Bool (i <! 0) m2) with false by 
         (symmetry; apply (leb_correct_conv 0%nat (E.eval_expr i m2 + 1)); omega). 
       rewrite deno_nil_elim, Munit_eq; auto.
     (* inductive case *)
      assert (H1: forall (m:Mem.t k) f, P1 m -> E.eval_expr i m = 0%nat -> 
        mu ([[ [while i <! S n do c1] ]] e1 m) f == 
        mu ([[ [while i <! n do c1] ]] e1 m) (fun m' => mu ([[c1]] e1 m') f)).
        intros.
         rewrite <-(deno_cons_elim e1 (while i <! n do c1) c1 m f).
         apply (init_for_loop_tail_unroll _ _ P1 m _ Hran1 H H0).  
      assert (H2: forall (m:Mem.t k) f, P2 m -> E.eval_expr i m = 0%nat -> 
        mu ([[ [while i <! S n do c2] ]] e2 m) f == 
        mu ([[ [while i <! n do c2] ]] e2 m) (fun m' => mu ([[c2]] e2 m') f)).
        intros.
         rewrite <-(deno_cons_elim e2 (while i <! n do c2) c2 m f).
         apply (init_for_loop_tail_unroll _ _ P2 m _ Hran2 H H0).
       


     destruct IHn as [d Hd].
     destruct (Hc n k) as [d' Hd']; clear Hc.
     exists (fun m1 m2 => Mlet (d m1 m2) (fun mm => d' (fst mm) (snd mm))).
     intros m1 m2 Hm; constructor.

       (* dist *)
       intros f g.
       set (Hm':=Hm).
       destruct Hm' as [HI [Hil Hir] ]; unfold EP1 in Hil; unfold EP2 in Hir.
       setoid_rewrite (eval_eq m1 i 0%nat) in Hil; apply nat_eqb_true in Hil.
       setoid_rewrite (eval_eq m2 i 0%nat) in Hir; apply nat_eqb_true in Hir.
       rewrite (H1 _ _ (proj1 (H_P HI)) Hil), (H2 _ _ (proj2 (H_P HI)) Hir).
       rewrite (Uabs_diff_triangle_ineq _ 
         (mu ([[ [while i <! n do c1] ]] e1 m1) (fun m => mu ([[c1]] e1 m) f))
         (mu (d m1 m2) (fun x => mu ([[c1]] e1 (fst x)) f))).
       rewrite (Uabs_diff_triangle_ineq _ 
         (mu ([[ [while i <! n do c2] ]] e2 m2) (fun m => mu ([[c2]] e2 m) g))
         (mu (d m1 m2) (fun x => mu ([[c2]] e2 (snd x)) g))).
       match goal with |- (?A + ?B) + (?C + ?D) <= _ =>
         rewrite <-(Uplus_assoc A), (Uplus_sym B), Uplus_assoc, (Uplus_assoc A), <-(Uplus_assoc), (Uplus_sym D)
       end.
       rewrite sigma_S; apply Uplus_le_compat.
         (* left inequality *)
         apply (Ueq_orc (h k n) 1); [apply Ule_class | | ]; intro Hhn.
           (* case [h n = 1] *)
           rewrite Hhn; auto.
           (* case [h n < 1] *)
           repeat rewrite Mlet_simpl.
           rewrite Uabs_diff_mu_compat, Uabs_diff_mu_compat, 
             <-(mu_stable_plus_range (el_range (Hd _ _ Hm))).
           rewrite <-(mu_cte_le (d m1 m2) (h k n)); apply (range_le (el_range (Hd _ _ Hm))).
             intros (m1',m2') Hm'; unfold fplus, fcte, fabs_diff.
             apply (el_dist (Hd' _ _ Hm')).
             intros (m1',m2') Hm'; unfold fabs_diff.
             apply Uplus_lt_Uinv; apply Ule_lt_trans with (h k n); [ | auto ].
             rewrite Uplus_sym; apply (el_dist (Hd' _ _ Hm')).
         (* right inequality *)
         apply (el_dist (Hd _ _ Hm) (fun m => mu ([[c1]] e1 m) f) (fun m => mu ([[c2]] e2 m) g)).

    (* range *)
    apply range_Mlet with (1:=el_range (Hd _ _ Hm)).
    intros (m1',m2') Hm'; apply (el_range (Hd' _ _ Hm')).

    (* supp_l *)
    assert (Hd_srange: exists R, srange R (d m1 m2)) by
       (eexists; apply (discr_srange  (elift_deno_witness_discr (Hd _ _ Hm)) _ 
         (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)))).
    destruct Hd_srange as (R,(Hd_ran,Hd_dran)).
    intro f.
    set (Hm':=Hm); destruct Hm' as [HI [Hil _] ]; unfold EP1 in Hil.
    setoid_rewrite (eval_eq m1 i 0%nat) in Hil; apply nat_eqb_true in Hil.
    rewrite Mlet_simpl, (H1 _ _ (proj1 (H_P HI)) Hil).
    generalize (el_supp_l (Hd _ _ Hm)); intro Hl.
    split; intro H.
      (*  *)
      rewrite <-Hl.
      symmetry; apply Hd_ran.
      intros (m1',m2') Hm'; simpl.
      assert (Hm'_2: (I /-\ EP1 (i =?= n) /-\ EP2 (i =?= n)) _ m1' m2') by
        refine (drange_range (@cover_prec n k) (el_range (Hd _ _ Hm)) Hd_dran _ Hm').
      destruct (Hd' _ _ Hm'_2) as (_, Hran', Hsupp', _); simpl in *.  
      symmetry; rewrite <-Hsupp'.
      symmetry; apply (Hd_dran _ (Oeq_sym H) _ Hm').
      (*  *)
      rewrite <-Hl in H.
      symmetry; apply Hd_ran.
      intros (m1',m2') Hm'; simpl.
      assert (Hm'_2: (I /-\ EP1 (i =?= n) /-\ EP2 (i =?= n)) _ m1' m2') by
        refine (drange_range (@cover_prec n k) (el_range (Hd _ _ Hm)) Hd_dran _ Hm').
      destruct (Hd' _ _ Hm'_2) as (_, Hran', Hsupp', _); simpl in *.  
      symmetry; rewrite Hsupp'.
      symmetry; apply (Hd_dran _ (Oeq_sym H) _ Hm').

    (* supp_r *)  
    assert (Hd_srange: exists R, srange R (d m1 m2)) by
       (eexists; apply (discr_srange  (elift_deno_witness_discr (Hd _ _ Hm)) _ 
         (cover_eq_prod _ _ (@mem_eqU_spec k) (@mem_eqU_spec k)))).
    destruct Hd_srange as (R,(Hd_ran,Hd_dran)).
    intro g.
    set (Hm':=Hm); destruct Hm' as [HI [_ Hir] ]; unfold EP2 in Hir.
    setoid_rewrite (eval_eq m2 i 0%nat) in Hir; apply nat_eqb_true in Hir.
    rewrite Mlet_simpl, (H2 _ _ (proj2 (H_P HI)) Hir).
    generalize (el_supp_r (Hd _ _ Hm)); intro Hr.
    split; intro H.
      (*  *)
      rewrite <-Hr.
      symmetry; apply Hd_ran.
      intros (m1',m2') Hm'; simpl.
      assert (Hm'_2: (I /-\ EP1 (i =?= n) /-\ EP2 (i =?= n)) _ m1' m2') by
        refine (drange_range (@cover_prec n k) (el_range (Hd _ _ Hm)) Hd_dran _ Hm').
      destruct (Hd' _ _ Hm'_2) as (_, Hran', _, Hsupp'); simpl in *.  
      symmetry; rewrite <-Hsupp'.
      symmetry; apply (Hd_dran _ (Oeq_sym H) _ Hm').
      (*  *)
      rewrite <-Hr in H.
      symmetry; apply Hd_ran.
      intros (m1',m2') Hm'; simpl.
      assert (Hm'_2: (I /-\ EP1 (i =?= n) /-\ EP2 (i =?= n)) _ m1' m2') by
        refine (drange_range (@cover_prec n k) (el_range (Hd _ _ Hm)) Hd_dran _ Hm').
      destruct (Hd' _ _ Hm'_2) as (_, Hran', _, Hsupp'); simpl in *.  
      symmetry; rewrite Hsupp'.
      symmetry; apply (Hd_dran _ (Oeq_sym H) _ Hm').
 Qed.

End For_loop_rule.
*)






(*
 Lemma eequiv_random_permut: forall (P:mem_rel) E1 t (x:Var.var t) (D1:E.support t) 
   E2 (D2:E.support t), 
  eequiv P E1 [x <$- D1] E2 [x <$- D2] P (fone _).
 Proof.
  unfold eequiv; intros.
  exists (fun m1 m2 => Munit (m1,m2)).
  intros m1 m2 Hm; constructor.
    (* dist *)
    intros f g.
    rewrite deno_random_elim, Munit_eq; unfold fst.
    admit.
    
    (* range *)
    apply range_Munit; trivial.

    (* l_supp *)
    intro f.
    rewrite deno_random_elim, Munit_eq; unfold fst.
    

  rewrite equiv_eequiv.
  apply equiv_random_permut. 
 Qed.
*)


(*

 Lemma Uplus_le_minus: forall a b c,
  a - b <= c -> a <= c + b.
 Proof.
   intros.
   apply (Ule_total a b); [auto|intro H'|intro H'].
     rewrite (Uminus_plus_le a b), (Uminus_le_zero _ _ H'); auto.
     apply (Uminus_le_perm_left _ _ _ H' H).
 Qed.

 Lemma Uabs_diff_restr: forall (A:Type) (d:Distr A)  f R,
  Uabs_diff (mu d f) (mu d (restr R f)) <= mu d (restr (negP R) f).
 Proof.
  intros.
  rewrite <-(Uplus_zero_right (mu d (restr R f))), 
    (mu_restr_split d R f), Uabs_diff_plus, Uabs_diff_compat_eq, Uplus_zero_left.
  unfold Uabs_diff; rewrite (Uminus_le_zero 0 _ (Upos _)); auto. 
 Qed.


 Lemma eequiv_failure_events: forall (P:mem_rel) E1 c1 E2 c2 (Q:mem_rel) (ep ep1: nat -o> U)
  (bad1 bad2: Var.var T.Bool),
  (forall k (m1 m2:Mem.t k), P _ m1 m2 -> Pr E1 c1 m1 (EP k bad1) + Pr E2 c2 m2 (EP k bad2) <= ep k) ->
   eequiv P E1 c1 E2 c2 ((~-EP1 bad1 \-/ ~-EP2 bad2) |-> Q) ep1 ->
   eequiv P E1 c1 E2 c2 Q (fplus (fplus ep1 ep) ep1).
 Proof.
  unfold eequiv;  intros.
  destruct (H0 k) as [d Hd]; clear H0.
  exists (fun m1 m2 => drestr (d m1 m2) (fun mm => if andb (fst mm bad1) (snd mm bad2) then false else true)).
  intros m1 m2 Hm.
  constructor.
    (* dist *)
    intros.
    rewrite (Uabs_diff_triangle_ineq _ (mu ([[c1]] E1 m1) f) (mu (d m1 m2) (fun x => f (fst x)))).
    rewrite (Uabs_diff_triangle_ineq _ (mu ([[c2]] E2 m2) g) (mu (d m1 m2) (fun x => g (snd x)))).
    match goal with |- (?A + ?B) + (?C + ?D) <= _ =>
      rewrite <-(Uplus_assoc A), (Uplus_sym B), Uplus_assoc, (Uplus_assoc A), <-(Uplus_assoc), (Uplus_sym D)
    end.
    apply Uplus_le_compat.
      rewrite mu_drestr, (Uabs_diff_sym _ (mu _ (fun x => f (fst x)))), Uabs_diff_restr.
      rewrite mu_drestr, (Uabs_diff_sym _ (mu _ (fun x => g (snd x)))), Uabs_diff_restr.
      transitivity ( mu (d m1 m2) (fun x => charfun (EP k bad1) (fst x)) + 
        mu (d m1 m2) (fun x => charfun (EP k bad2) (snd x))).
        apply Uplus_le_compat; unfold charfun, restr, EP, negP;
          (apply mu_le_compat; [ trivial | simpl ]; refine (ford_le_intro _); 
            intro mm; case (fst mm bad1); case (snd mm bad2); simpl; auto).
      unfold fplus; rewrite <-(H _ _ _ Hm).
      apply Uplus_le_minus.
      rewrite <-(el_dist (Hd _ _  Hm) (charfun (EP k bad1)) (charfun (EP k bad2))).
      rewrite <-Uabs_diff_plus; apply Ule_plus_right.
      apply (el_dist (Hd _ _ Hm)).
    (* range *)
    unfold drestr; apply range_Mlet with (1:=el_range (Hd _ _ Hm)).
    unfold prodP, notR, impR, orR, EP1, EP2; intros (m1',m2') Hm'; 
     unfold fst, snd in *; generalize Hm'; simpl.
    case (m1' bad1); case (m2' bad2); intros Hbad; simpl. 
      apply distr0_range; trivial.
      apply range_Munit; apply Hbad; right; discriminate.
      apply range_Munit; apply Hbad; left; discriminate.
      apply range_Munit; apply Hbad; left; discriminate.
 Qed.
*)

  
 

(*
 Lemma eequiv_assign: forall E1 (t1 : T.type) (x1 : Var.var t1) 
   (e1 : E.expr t1) E2 (t2 : T.type) (x2 : Var.var t2) (e2 : E.expr t2)  Q,
    eequiv (upd_para Q x1 e1 x2 e2) E1 [x1 <- e1] E2 [x2 <- e2] Q (fzero _).
 Proof.
  unfold eequiv, upd_para; intros. 
  exists (fun m1 m2 => Munit (m1{!x1<-- E.eval_expr e1 m1!}, m2{!x2<--E.eval_expr e2 m2!})). 
  intros.
  repeat rewrite deno_assign; auto using elift_Munit.
 Qed.


 Lemma eequiv_random_permut: forall (Q:mem_rel) E1 t (x1:Var.var t) (D1:E.support t) 
   E2 (x2: Var.var t) (D2:E.support t) (h:forall k, Mem.t k -> Mem.t k -> T.interp k t -> T.interp k t),
  eequiv 
   ((permut_support h D1 D2) /-\ (fun k m1 m2 => forall v, In v (E.eval_support D2 m2) -> 
     Q k (m1{!x1 <-- h k m1 m2 v!}) (m2{!x2 <-- v!})))
   E1 [x1 <$- D1] E2 [x2 <$- D2] Q (fzero _).
 Proof.
  intros.
  rewrite equiv_eequiv.
  apply equiv_random_permut. 
 Qed.


 Lemma eequiv_while : forall (P:mem_rel) E1 (e1:E.expr T.Bool) c1 E2 (e2:E.expr T.Bool) c2,
  (forall k m1 m2, P k m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
  eequiv (P /-\ EP1 e1 /-\ EP2 e2) E1 c1 E2 c2 P (fzero _) -> 
  eequiv P E1 [while e1 do c1] E2 [while e2 do c2] (P /-\ ~-EP1 e1 /-\ ~-EP2 e2) (fzero _).
 Proof.
  intros.
  rewrite equiv_eequiv.
  apply (equiv_while H).
  rewrite <-equiv_eequiv.
  assumption.
 Qed.
*)


    

