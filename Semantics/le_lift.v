Require Export BaseDef.
Require Import Classical.
Require Import Arith Even Div2.
Require Import RelationClasses.

Set Implicit Arguments.

Lemma even_2n : forall n, even (2*n).
 Proof.
  intro n.
  apply even_mult_l.
  repeat constructor.
 Qed.

 Lemma odd_S2n : forall n, odd (S(2*n)).
 Proof.
  intro n.
  constructor.
  apply even_2n.
 Qed.


(* 
  parity_split f g (2m) = f m
  parity_split f g (2m+1) = g m
*)   
 Definition parity_split := fun (A:Type) (f g : nat -> A) n  =>
   match (even_odd_dec n) with
   | left x => f (div2 n)
   | right x => g (div2 (pred n)) 
   end.


(* Given two discrete disctribution over [A], restate them in terms
   of the same enumearion of [A]'s elements *)
Section SamePoints.

 Variable A : Type.
 Variable AeqU : A -> A -O-> U.
 Hypothesis cover_uR: forall a : A, cover (eq a) (AeqU a).

 Variable d1 d2 : Distr A.
 Hypothesis is_Discr_d1 : is_Discrete d1.
 Hypothesis is_Discr_d2 : is_Discrete d2.

 Let p1 := D_points is_Discr_d1.
 Let p2 := D_points is_Discr_d2.
 Let D1 := D_Discr is_Discr_d1.
 Let D2 := D_Discr is_Discr_d2.

 Let c1 : nat -> U := parity_split (coeff AeqU p1 d1) (fzero _).
 Let c2 : nat -> U := parity_split (fzero _) (coeff AeqU p2 d2).
 Let p  : nat -> A := parity_split p1 p2.

 Lemma disc_eqpoint_l : Discrete (@eq A) p d1.
 Proof.
  apply range_weaken with (2:=D1); fold p1.
  unfold In_classes; intros x Hx.
  unfold p, parity_split.
  unfold exc in *. 
  intros P HP H.
  apply (Hx _ HP).
  intros n Hn.
  generalize (H (2*n)%nat).
  elim (even_odd_dec (2*n)%nat); intro Hn'.
     rewrite div2_double.
     exact (fun n => n Hn).
     elimtype False; refine (not_even_and_odd _ (even_2n _) Hn').
 Qed.

 Lemma disc_eqpoint_r : Discrete (@eq A) p d2.
 Proof.
  apply range_weaken with (2:=D2); fold p2.
  unfold In_classes; intros x Hx.
  unfold p, parity_split.
  unfold exc in *. 
  intros P HP H.
  apply (Hx _ HP).
  intros n Hn.
  generalize (H (S(2*n))).
  elim (even_odd_dec (S(2*n))); intro Hn'.
     elimtype False; refine (not_even_and_odd _ Hn' (odd_S2n _)).
     rewrite <-pred_Sn, div2_double; exact (fun n => n Hn).
 Qed.

 End SamePoints.



(* *********** Some Auxiliary Stuff about distributions *********** *)

 Definition p1 (A B:Type) (d:Distr (A*B)) : (Distr A) := 
   Mlet d (fun ab => Munit (fst ab)). 

 Definition p2 (A B:Type) (d:Distr (A*B)) : (Distr B) := 
   Mlet d (fun ab => Munit (snd ab)). 

 Add Parametric Morphism (A B:Type) : (@p1 A B)
 with signature Oeq (O:=Distr (A*B))  ==> Oeq (O:=Distr A) 
 as p1_eq_compat_morph.
 Proof.
  unfold p1; intros.
  apply Mlet_eq_compat; trivial.
 Qed.

 Add Parametric Morphism (A B:Type) : (@p2 A B)
 with signature Oeq (O:=Distr (A*B))  ==> Oeq (O:=Distr B) 
 as p2_eq_compat_morph.
 Proof.
  unfold p2; intros.
  apply Mlet_eq_compat; trivial.
 Qed.

 Lemma p2_prod_distr: forall (A B:Type) (d1:Distr A) (d2:Distr B),
   p2 (prod_distr d1 d2) == distr_mult (fcte _ (mu d1 (fone _))) d2.
 Proof.
  intros.
  refine (ford_eq_intro _); intro g; unfold fcte.
  simpl.
  rewrite (mu_cte d1 ((mu d2) (fun b:B => g b))),
     (mu_stable_mult d2 (mu d1 (fone A)) g), Umult_sym.
  apply Umult_eq_compat_right.
  apply mu_stable_eq; refine (ford_eq_intro _); trivial.
 Qed.

 Lemma p1_prod_distr: forall (A B:Type) (d1:Distr A) (d2:Distr B),
   p1 (prod_distr d1 d2) == distr_mult (fcte _ (mu d2 (fone _))) d1.
 Proof.
  intros.
  refine (ford_eq_intro _); intro f; unfold fcte.
  simpl.
  rewrite (mu_stable_mult d1 (mu d2 (fone B)) f), Umult_sym.
  transitivity  (mu d1 (fun x : A => (mu d2 (fone _)) * f x)).
  apply (mu_stable_eq d1); refine (ford_eq_intro _); intro a;
    rewrite (mu_cte d2 (f a)); apply Umult_sym.
  rewrite (mu_stable_mult d1 (mu d2 (fone B)) f); apply Umult_sym.
 Qed.

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



 Lemma Uminus_triang_ineq: forall a b c, a - b <=  (a - c) + (c - b).
 Proof.
  intros.
  apply (Ule_total a b); [ auto | | ]; intros Hab.
    rewrite (Uminus_le_zero _ _ Hab); trivial.
  apply (Ule_total a c); [ auto | | ]; intros Hac.
    rewrite (Uminus_le_zero _ _ Hac), Uplus_zero_left.
    apply (Uminus_le_compat_left _ _ _ Hac).
  apply (Ule_total c b); [ auto | | ]; intros Hcb.
    rewrite (Uminus_le_zero _ _ Hcb), Uplus_zero_right.
    apply (Uminus_le_compat_right _ _ _ Hcb).
    rewrite Uplus_sym, <-Uminus_triangle_ineq2; trivial.
 Qed.


 Lemma max_comm: forall x y, max x y ==  max y x.
 Proof.
  intros. 
  apply (Ule_total x y); [ auto | | ]; intro H; unfold max;
    rewrite (Uminus_le_zero _ _ H), Uplus_zero_left; auto.
 Qed.




(*
 Section DMIN.

 Variable A: Type.

 Variable eqbA: A -> A -> bool.
 Hypothesis eqb_spec : forall a1 a2, if  eqbA a1 a2 then a1 = a2 else a1 <> a2.
 Definition carA : A -> A -> U := fun a1 a2 => if eqbA a1 a2 then 1 else 0.

 Definition dmin (d1 d2:Distr A) : Distr A :=
   Mlet d1 (fun a1 => Mlet d2 (fun a2 => if eqbA a1 a2 then
     Mif (Munit (Uleb (mu d1 (carA a1)) (mu d2 (carA a1)))) d1 d2  else distr0 _)).


 Lemma toto1: forall (d1 d2:Distr A) f,
   (forall a, mu d1 (carA a) < mu d2 (carA a) -> f a = 0) ->
   mu d2 f <= mu d1 f.
 Proof.
 Admitted.


 Lemma Uleb_corr_conv: forall x y : U, y < x -> Uleb x y = false.
 Proof.
 Admitted.

 Lemma Uleb_comp_conv: forall x y : U, x <= y -> Uleb x y.
 Proof.
 Admitted.

 Lemma dmin_spec2: forall d1 d2 f,
   mu (dmin d1 d2) f <= mu d1 f. 
 Proof.
   intros; unfold dmin.
   rewrite 2 (mu_restr_split  _ (fun a => Uleb (mu d1 (carA a)) (mu d2 (carA a))) f).
   transitivity ( 
     mu d2 (restr (fun a0 : A => Uleb ((mu d1) (carA a0)) ((mu d2) (carA a0))) f) +
     mu d1 (restr (negP (fun a : A => Uleb ((mu d1) (carA a)) ((mu d2) (carA a)))) f)).
  
   apply Uplus_le_compat.
     match goal with |- _ <= ?X =>  rewrite <-(mu_cte_le d1 X), Mlet_simpl end.
     apply mu_monotonic; refine (ford_le_intro _); intro a; unfold fcte.
     match goal with |- _ <= ?X =>  rewrite <-(mu_cte_le d2 X), Mlet_simpl end.
     apply mu_monotonic; refine (ford_le_intro _); intro a'; unfold fcte.
     case_eq (eqbA a a'); intro Haa'; [ | auto ].
     unfold Mif; rewrite Mlet_simpl, Munit_eq.
     case_eq (Uleb ((mu d1) (carA a)) ((mu d2) (carA a))); intro Heq.
       apply toto1; unfold restr, negP, negb; intros a'' Ha'';  
          rewrite (Uleb_corr_conv Ha''); trivial.
       trivial.
  
     match goal with |- _ <= ?X =>  rewrite <-(mu_cte_le d1 X), Mlet_simpl end.
     apply mu_monotonic; refine (ford_le_intro _); intro a; unfold fcte.
     match goal with |- _ <= ?X =>  rewrite <-(mu_cte_le d2 X), Mlet_simpl end.
     apply mu_monotonic; refine (ford_le_intro _); intro a'; unfold fcte.
     case_eq (eqbA a a'); intro Haa'; [ | auto ].
       unfold Mif; rewrite Mlet_simpl, Munit_eq.
        case_eq (Uleb ((mu d1) (carA a)) ((mu d2) (carA a))); intro Heq.
          trivial.
          apply toto1; unfold restr, negP, negb; intros a'' Ha''.
          rewrite (Uleb_comp_conv _ _ (Ult_le Ha'')); trivial.

  Usimpl.
  apply toto1; unfold restr, negP, negb; intros a Ha.
  rewrite (Uleb_corr_conv Ha).
  
  
  


SearchAbout Uleb.
            rewrite (Uleb_corr_conv Ha''); trivial.

       auto.   









          

SearchAbout Uleb.
          Check (Uleb_complete

   destruct (Uleb_dec ((mu d2) (carA a'')) ((mu d1) (carA a''))).

          SearchAbout sumbool.

          rewrite Uplus





rewrite Ha''.
          

        
          admit.
        


        apply toto2.
     




     rewrite Mlet_simpl; apply mu_monotonic; refine (ford_le_intro _); intro a.
     rewrite Mlet_simpl; match goal with |- _ <= ?X =>  rewrite <-(mu_cte_le d2 X) end.
     apply mu_monotonic; refine (ford_le_intro _); intro a'.
      case_eq (eqbA a a'); intro Haa'.
        unfold Mif, fcte; rewrite Mlet_simpl, Munit_eq.
        case_eq (Uleb ((mu d1) (carA a)) ((mu d2) (carA a))); intro Heq.
        match goal with |- _ <= ?X =>  rewrite <-(mu_cte_le d1 X) end.
        apply mu_monotonic; refine (ford_le_intro _); intro a''.
        unfold restr, fcte.

        unfold restr at 2.
        rewrite Heq.
        rewrite <-(mu_cte_le d1 (f a)).
        
        unfold fcte.

     

      rewrite <-(mu_cte_le d2 (f a)).
     unfold restr.


idtac end.

     rewrite Mlet_simpl:

 
     (@mu_restr_split _ _ (fun a => Uleb (mu d1 (carA a)) (mu d2 (carA a))) f).

SearchAbout restr.

   rewrite Mlet_simpl; apply mu_monotonic; refine (ford_le_intro _); intro a.

     rewrite <-(mu_cte_le d2 (f a)).
     rewrite Mlet_simpl; apply mu_monotonic; refine (ford_le_intro _); intro a'.
       case (eqbA a a').
       simpl.
       unfold fcte.



     rewrite Mlet_simpl.

     

     unfold Mif.
     simpl.
     simpl.

   rewrite Mlet_simpl, <-(mu_cte_le d2 (f a)); apply mu_monotonic; refine (ford_le_intro _); intro a'.
   case_eq (eqbA a a'); intro Heq.   
     unfold Mif, fcte.
     rewrite Mlet_simpl, Munit_eq.
     

 Lemma dmin_simpl1: forall d1 d2 (f:A-o>U),
   mu (dmin d1 d2) f == mu d1 (fun a => mu d2 (fun a' =>
      if eqbA a a' then 1 else 1)).
 Proof.
  unfold dmin; intros.
  rewrite Mlet_simpl; apply mu_stable_eq; refine (ford_eq_intro _); intro a.
  rewrite Mlet_simpl; apply mu_stable_eq; refine (ford_eq_intro _); intro a'.
  case_eq (eqbA a a'); intro Heq.


  unfold Mif. ; rewrite Mlet_unit.
SearchAbout [Mlet Munit].
  Mletunit
  rewrite Mif_simpl

  rewrite Mlet_simpl.
  
  
  






Definition im_distr2 (A B C: Type)(f:A->B->C)
(m:Distr A) (m':Distr B): Distr C :=
   Mlet m  (fun a => Mlet m' (fun b => Munit (f a b))).

Lemma im_distr2_simpl : forall A0 B C (f:A0->B->C)(m:Distr A0) (m':Distr B)(h:C->U),
    mu (im_distr2 f m m')  h ==
mu m (fun a => mu m' (fun b => (h (f a b)))).
intros; simpl.
apply mu_stable_eq with (m:=m).
refine (ford_eq_intro _).
intros.
apply mu_stable_eq with (m:=m').
refine (ford_eq_intro _).
 auto.
Save.


 




Definition dmin (d1 d2:Distr A) : Distr A :=  let aux  := 
(fun a1 a2 => ) in Mif (im_distr2 aux d1 d2) d1 d2.



 


carA a1 a2 * if
   d1 a1 <= d2 a1 then d1 else d2)
   
 *)  



 (* Axiomatization of the [1,+inf) real interval *) 
Module Type REALS_GE_ONE.

 Parameter tREAL:Type.

 (* Order properties *)
 Parameter le_D: tREAL -> tREAL -> Prop.
 Parameter le_D_refl: forall (x:tREAL),
  le_D x x.
 Parameter le_D_trans: forall (x y z:tREAL),
  le_D x y ->
  le_D y z ->
  le_D x z.
 Definition D := mk_ord le_D_refl le_D_trans : ord.


 (* Distinguished element *)
 Parameter D1 : D.

 
 (* Algebraic properties *) 
 Parameter multDU: D -> U -> U.
 Parameter multDD: D -> D -> D.
 Infix "**" := multDU (at level 40).
 Infix "*D*" := multDD (at level 42). 

 Parameter multDU_D1_l: forall (a:U),
   D1 ** a == a.
 Parameter D1bot: forall (x:D),
   D1 <= x.
 Parameter multDD_D1_l: forall (x:D),
   D1 *D* x == x.
 Parameter multDU_0_r: forall (x:D),
   x ** 0 == 0.
 Parameter multDD_multDU_assoc: forall (x y:D) (a:U),
   (x *D* y) ** a == x ** (y ** a).
 Parameter multDD_comm: forall (x y:D),
   x *D* y == y *D* x.
 Parameter Umult_multDU_assoc: forall (x:D) (a b:U),
   (x ** a) * b <= x ** (a * b).
 Parameter multDD_distr_minus_l: forall (x:D) (a b:U),
   x ** a - x ** b <= x ** (a - b).
 Parameter multDD_distr_plus_l: forall (x:D) (a b:U),
   x ** a + x ** b <= x ** (a + b).


 (* Compatibility of operations wrt the order *)
 Parameter multDU_eq_compat: forall (x y:D) (a b:U),
   x == y ->
   a == b -> 
   x ** a == y ** b.
 Parameter multDU_le_compat: forall (x y:D) (a b:U),
   x <= y ->
   a <= b ->
   x ** a <= y ** b.

 (* Derived Properties and Operations *)
 Lemma multDU_le: forall (x:D) (a:U),
   a <= x ** a.
 Proof.
  intros.
  rewrite <-(multDU_D1_l a) at 1.
  apply multDU_le_compat; [ apply D1bot | auto ].
 Qed.

 Fixpoint powD (x:D) (n:nat) {struct n} : D :=
 match n with
  | 0%nat => D1 
  | S n' => x *D* powD x n'
 end.  


 Hint Resolve  multDU_D1_l multDD_D1_l  D1bot multDU_0_r.
 Hint Resolve  multDU_le multDD_multDU_assoc multDU_eq_compat multDU_le_compat. 


 Add Parametric Morphism : multDU 
 with signature Oeq (O:=D) ==> Oeq (O:=U) ==> Oeq (O:=U) 
 as multDU_eq_compat_r_morph.
 Proof. auto. Qed.

 Add Parametric Morphism: multDU
 with signature Ole (o:=D) ++> Ole (o:=U) ++> Ole (o:=U) 
 as multDU_le_compat_r_morph.
 Proof. auto. Qed.


 (* TODO: Fix this *)
 Parameter lt_1_dec: U -> bool.
 Parameter lt_1_dec_spec: forall a, if lt_1_dec a then a < 1 else a == 1. 

 Parameter mu_le_compat_fmultDU: forall (A:Type) (d:Distr A) (x:D) f,
   (forall a, x ** f a < 1) ->
   mu d (fun a => x ** f a) <=  x ** mu d f.

 Lemma multD_mu: forall (A:Type) (d: Distr A) x f ,
   mu d (fun a  => x ** f a) <= x ** (mu d) f.
 Proof.
  intros.
  rewrite (mu_restr_split d (fun a => lt_1_dec (x ** f a))). 
  transitivity (x **  mu d (restr (fun a : A => lt_1_dec (x ** f a)) f) +
    mu d (restr (negP (fun a : A => lt_1_dec (x ** f a))) (fun a : A => x ** f a))).
  apply Uplus_le_compat.
    rewrite <-mu_le_compat_fmultDU.
      apply mu_monotonic; refine (ford_le_intro _); unfold restr; intro a;
        case (lt_1_dec (x ** f a)); trivial.
      unfold restr; intro a.
      generalize (lt_1_dec_spec (x ** f a)); case_eq (lt_1_dec (x ** f a)); 
        intros _  ?; [ trivial | rewrite multDU_0_r; auto ].

    trivial.
(*
  rewrite Uplus_sym.
  apply Uminus_le_perm_right.
    apply multDU_le_compat.
    apply mu_monotonic; refine (ford_le_intro _); unfold restr; 
      intro a; case (lt_1_dec (x ** f a)); trivial.
  
    rewrite  multDD_distr_minus_l, <-mu_neg_restr.
    rewrite <-mu_le_compat_fmultDU
    *)
 Admitted.

End REALS_GE_ONE.


Module APPROX_LIFT (DOM: REALS_GE_ONE).


Export DOM.


(* Expression used to define the [lambda-epsilon Distance] *)
Section LE_DIST_EXPR.

 Definition d_expr (A B:Type) (d1:Distr A) (d2:Distr B) (lam:D) f1 f2 :=
  (mu d1 f1 - lam ** (mu d2 f2)) + (mu d2 f2 - lam ** (mu d1 f1)).


 Lemma d_expr_le: forall (A B:Type) (d1: Distr A) (d2: Distr B) lam ep f g,
  d_expr d1 d2 lam f g <= ep <->  
  mu d2 g - lam ** mu d1 f <= ep /\ mu d1 f - lam ** mu d2 g <= ep.
 Proof.
  unfold d_expr; split; intros.
  (*  ==> *)
  apply (Ule_total (mu d1 f) (mu d2 g)); [ auto | | ]; 
    intro H'; split; rewrite <-H; auto.
  (* <== *)
  apply (Ule_total (mu d1 f) (mu d2 g)); [ auto | | ]; intro H'; destruct H.
    rewrite (Uminus_le_zero (mu d1 f) (lam ** (mu d2 g))), Uplus_zero_left; trivial.
    rewrite H'; auto.
    rewrite (Uminus_le_zero (mu d2 g) (lam ** mu d1 f)), Uplus_zero_right; trivial.
    rewrite H'; auto.
 Qed.


 Lemma d_expr_nul: forall (A:Type) (d: Distr A) (lam:D) f,
   d_expr d d lam f f == 0. 
 Proof.
  unfold d_expr; intros.
  rewrite <-(Uplus_zero_right 0); apply Uplus_eq_compat;
  apply Uminus_le_zero; apply multDU_le.
 Qed.

 Lemma d_expr_sym: forall (A B:Type) (d1: Distr A) (d2: Distr B) (lam:D) f1 f2,
  d_expr d1 d2 lam f1 f2 == d_expr d2 d1 lam f2 f1.
 Proof.
  unfold d_expr; intros; apply Uplus_sym. 
 Qed.

 Lemma d_expr_trans_aux (A B C:Type) (d1: Distr A) (d2: Distr B) (d3: Distr C) (lam lam':D) f1 f2 f3 :
  let ep := d_expr d1 d2 lam f1 f2 in
  let ep' := d_expr d2 d3 lam' f2 f3 in 
  d_expr d1 d3 (lam *D* lam') f1 f3 <= (max (ep + lam ** ep') (ep' + lam' ** ep)).
 Proof.
  unfold d_expr at 3; intros A B C d1 d2 d3 lam lam' f1 f2 f3 ep ep'.
  apply (@Ule_total (mu d1 f1) (mu d3 f3)); 
    [ auto | | ]; intros H.
    (*    *)
    rewrite <-max_le_left.
    rewrite (Uminus_le_zero (mu d1 f1) ((lam *D* lam') ** (mu d3 f3))), Uplus_zero_left; 
      [ | rewrite H, <-multDU_le; trivial ].
    unfold ep, ep', d_expr.
    rewrite Uminus_triang_ineq with (c:= lam' ** (mu d2 f2)).
    apply Uplus_le_compat.
      auto.
      rewrite multDD_comm, multDD_multDU_assoc, multDD_distr_minus_l.
      apply multDU_le_compat; auto.
    (*   *)
    rewrite <-max_le_right.
    rewrite (Uminus_le_zero (mu d3 f3) ((lam *D* lam') ** (mu d1 f1))), Uplus_zero_right; 
      [ | rewrite H, <-multDU_le; trivial ].
    unfold ep, ep', d_expr.
    rewrite Uminus_triang_ineq with (c:= lam ** (mu d2 f2)).
    apply Uplus_le_compat.
      auto.
      rewrite multDD_multDU_assoc, multDD_distr_minus_l.
      apply multDU_le_compat; auto.
 Qed.

 Lemma d_expr_trans (A B C:Type) (d1: Distr A) (d2: Distr B) (d3: Distr C) (lam lam':D) f1 f2 f3 :
  let ep := d_expr d1 d2 lam f1 f2 in
  let ep' := d_expr d2 d3 lam' f2 f3 in 
  d_expr d1 d3 (lam *D* lam') f1 f3 <= lam' ** ep + lam ** ep'.
 Proof.
  intros.
  transitivity (max (ep + lam ** ep') (ep' + lam' ** ep)).
    apply d_expr_trans_aux.
    match goal with |- (max ?A ?B) <= _ =>
      apply (@max_eq_case  A B); [ auto | | ]; intros H; rewrite H
    end.
    apply Uplus_le_compat_left; apply multDU_le.
    rewrite Uplus_sym; apply Uplus_le_compat_right; apply multDU_le.
 Qed.


 Lemma d_expr_lam_weaken: forall (A B:Type)  (d1: Distr A) (d2: Distr B) (lam lam': D) f1 f2,
  lam <= lam' ->
  d_expr d1 d2 lam' f1 f2 <= d_expr d1 d2 lam f1 f2.
 Proof.
  unfold d_expr; intros.
  apply Uplus_le_compat; apply Uminus_le_compat_right;
    apply multDU_le_compat; trivial.
 Qed.


 Lemma d_expr_eq_compat: forall (A B:Type) (d1 d1':Distr A)  (d2 d2':Distr B) (lam lam':D) f1 f1' f2 f2',
   d1' == d1 ->
   d2' == d2 ->
   lam' == lam ->
   f1' == f1  ->
   f2' == f2 ->
   d_expr d1' d2' lam' f1' f2' ==  d_expr d1 d2 lam f1 f2. 
 Proof.
  unfold d_expr; intros A B d1 d1' d2 d2' lam lam' f1 f1' f2 f2' Hd1 Hd2 Hlam Hf1 Hf2.
  rewrite (mu_stable_eq d1' _ _ Hf1), (mu_stable_eq d2' _ _ Hf2),
    (ford_eq_elim Hd1 f1), (ford_eq_elim Hd2 f2), Hlam.
  trivial.
 Qed.


 Lemma d_expr_distr_mult:forall (A:Type) (d:Distr A) x lam f,
  d_expr (distr_mult (fcte A x) d) d lam f f <= [1-] (lam ** x).
 Proof.
  unfold d_expr; intros.
  simpl; unfold fcte.
  rewrite (mu_stable_mult d x f).
  rewrite (Uminus_le_zero (x * (mu d f))  (lam ** (mu d f))), 
    Uplus_zero_left; [ | rewrite Ule_mult_left; apply multDU_le ].
  match goal with |- ?X - _ <= _ => rewrite <-(Umult_one_left X),
    <-Umult_multDU_assoc, <-Uminus_distr_left end.
  rewrite Ule_mult_right; trivial.
 Qed.


 Lemma d_expr_mu_compat : forall (A:Type) (d: Distr A) (lam:D) f1 f2,
   d_expr d d lam f1 f2 <= 
   mu d (fplus (fun a => f1 a - lam ** f2 a) (fun a => f2 a - lam ** f1 a)).
 Proof.
  unfold d_expr; intros.
  rewrite (@mu_stable_plus _ d (fun a => f1 a - lam ** f2 a) (fun a => f2 a - lam ** f1 a)).
  apply Uplus_le_compat; rewrite <-mu_stable_le_minus; 
    apply Uminus_le_compat_right; apply  multD_mu.
    intros x; unfold finv.
    apply (Ule_total (f1 x) (f2 x)); [auto| |]; intro H'.
      rewrite (Uminus_le_zero (f1 x) (lam ** (f2 x))); trivial.
      rewrite H'; apply multDU_le.
      rewrite (Uminus_le_zero (f2 x) (lam ** (f1 x))), Uinv_zero; auto.
      rewrite H'; apply multDU_le.
 Qed.


End LE_DIST_EXPR.



(* [Lmabda-Epsilon]-Distance between two distributions *)
Section LE_DIST.

 Definition le_dist (A:Type) (d1 d2: Distr A) (lam:D) (ep:U) :=
   forall f, d_expr d1 d2 lam f f <= ep.

 Lemma le_dist_nul (A:Type) (d: Distr A) (lam:D):
  le_dist d d lam 0.
 Proof.
  unfold le_dist; intros.
  rewrite  d_expr_nul; trivial.
 Qed.


 Lemma le_dist_sym (A:Type) (d1 d2: Distr A) (lam:D) (ep:U) :
  le_dist d1 d2 lam ep ->
  le_dist d2 d1 lam ep.
 Proof.
  unfold le_dist; intros A d1 d2 lam ep H f.
  rewrite d_expr_sym; auto.
 Qed.
  
 Lemma le_dist_trans (A:Type) (d1 d2 d3: Distr A) (lam lam':D) (ep ep':U) :
  le_dist d1 d2 lam ep ->
  le_dist d2 d3 lam' ep' ->
  le_dist d1 d3 (lam *D* lam') (max (ep + lam ** ep') (ep' + lam' ** ep)).
 Proof.
  unfold le_dist; intros A d1 d2 d3 lam lam' ep ep' H12 H23 f.
  rewrite (d_expr_trans_aux _ d2).
  apply max_le_compat; apply Uplus_le_compat; auto using multDU_le_compat.
 Qed.

 Lemma le_dist_weaken_lam (A:Type) (d1 d2: Distr A) (lam lam':D) (ep:U) :
  lam' <= lam ->
  le_dist d1 d2 lam' ep ->
  le_dist d1 d2 lam ep.
 Proof.
  unfold le_dist; intros.
  rewrite <-(H0 f); apply (d_expr_lam_weaken _ _ _ _ H).
 Qed.

 Lemma le_dist_weaken_ep (A:Type) (d1 d2: Distr A) (lam:D) (ep ep':U) :
  ep' <= ep ->
  le_dist d1 d2 lam ep' ->
  le_dist d1 d2 lam ep.
 Proof.
  unfold le_dist; intros.
  transitivity ep'; auto.
 Qed.

 Lemma le_dist_weaken (A:Type) (d1 d2: Distr A) (lam lam':D) (ep ep':U) :
  ep' <= ep ->
  lam' <= lam ->
  le_dist d1 d2 lam' ep' ->
  le_dist d1 d2 lam ep.
 Proof.
  intros.
  apply le_dist_weaken_ep with ep'; trivial.
  apply le_dist_weaken_lam with lam'; trivial.
 Qed.    

 Lemma le_dist_D1_0 (A:Type) (d1 d2: Distr A):
   le_dist d1 d2 D1 0 -> d1 == d2.
 Proof.
  unfold le_dist, d_expr; intros.
  refine (ford_eq_intro _); intro f.
  rewrite <-Uabs_diff_zero; apply Ule_zero_eq.
  rewrite <-(H f), multDU_D1_l, multDU_D1_l; trivial.
 Qed.

 Lemma le_dist_Mlet : forall (A B:Type) (d1 d2: Distr A) (F:A->Distr B) (lam:D) (ep:U),
   le_dist d1 d2 lam ep ->
   le_dist (Mlet d1 F) (Mlet d2 F) lam ep.
 Proof.
  unfold le_dist, d_expr; intros.
  repeat rewrite Mlet_simpl.
  apply H.
 Qed.


End  LE_DIST.


 Section DMIN.

 Variable A : Type.
 Variable AeqU : A -> A -O-> U.
 Hypothesis cover_uR: forall a : A, cover (eq a) (AeqU a).
 Variable p: nat -> A.

 Variable d1 d2 : Distr A.
 Hypothesis H_d1: Discrete (@eq A) p d1.
 Hypothesis H_d2: Discrete (@eq A) p d2.

 Definition dd:Distr A.
   apply PP.Discrete.
   refine (@Build_discr _ (fun k => min (coeff AeqU p d1 k) (coeff AeqU p d2 k)) _ p).
   apply wretract_le with  (coeff AeqU p d1); [ auto | ].
   
(*   unfold Discrete in H_d1. 

   SearchAbout wretract.
   

   unfold wretract, coeff; intro.
   apply (cover_orc_0_1 (cover_not_first_repr (@eq A) AeqU cover_uR p) k); [ auto | | ]; intro H.
    rewrite H; Usimpl.
  Usimpl.
*)
  admit.
 Defined.

 Lemma d_le_d1: forall f, mu dd f <= mu d1 f.
 Proof.
  intros.
  unfold dd; simpl.
  rewrite (mu_discrete AeqU cover_uR (@eq_Transitive A)(@eq_Symmetric A) H_d1);
      [ | intros x y Heq; rewrite Heq; trivial ].
  auto.
 Qed.


 Variable Uleb: U -> U -> bool.
 
 Let P := fun a => Uleb (mu d1 (AeqU a)) (mu d2 (AeqU a)).

 Lemma d_split: forall f, 
   mu dd f == mu d1 (restr P f) + mu d2 (restr (negP P) f). 
 Proof.
 Admitted.

 Lemma toto: forall f,
   mu d1 (restr P f) <= mu d2 (restr P f).
 Admitted.

 Lemma toto': forall f,
   mu d2 (restr (negP P) f) <= mu d1 (restr (negP P) f).
 Admitted.


Lemma Uplus_minus_perm_assoc : forall a b c d,
 (a + b) - (c + d) <= (a - c) + (b - d).
Proof.
 intros.
 rewrite <-Uminus_assoc_left, Uplus_minus_perm_le.
 apply Uplus_minus_le.
Qed.

 Lemma foo: forall (lam:D) (ep:U),
   le_dist d1 d2 lam ep ->
   le_dist d1 dd lam ep.
 Proof.
  unfold le_dist; intros.
  rewrite d_expr_le; split.
    rewrite d_le_d1.
    admit.
    rewrite d_split.
    transitivity (mu d1 (restr P f) + mu d1 (restr (negP P) f) - lam ** (mu d1 (restr P f) + mu d2 (restr (negP P) f))).
      apply Uminus_le_compat; trivial.
     admit.
    transitivity ((mu d1) (restr P f) + (mu d1) (restr (negP P) f) - (lam ** (mu d1) (restr P f) + lam ** (mu d2) (restr (negP P) f))).
   admit.
    rewrite Uplus_minus_perm_assoc.
   assert (Hz:(mu d1) (restr P f) - lam ** (mu d1) (restr P f) == 0) by admit.
rewrite Hz; Usimpl.
 eapply transitivity; [ | apply H].
 unfold d_expr; apply Ule_plus_right.
Qed.


End DMIN.

 Add Parametric Morphism (A B:Type): (d_expr (A:=A) (B:=B))
 with signature Oeq (O:=Distr A) ==> Oeq (O:=Distr B) ==> 
   Oeq (O:=D) ==> Oeq (O:=MF A) ==>  Oeq (O:=MF B) ==> Oeq (O:=U) as  d_expr_eq_compat_morph.
 Proof.
  intros.
  apply d_expr_eq_compat; assumption.
 Qed.



(* [Lmabda-Epsilon]-Lift of a relation to distributions *)
Section LE_LIFT.

 Record le_lift (A B: Type) (R:A->B->Prop) (d:Distr (A * B))
   (d1:Distr A) (d2:Distr B) (lam:D) (ep:U) := Build_elift
 { 
   le_d: forall f g, max (d_expr (p1 d) d1 lam f f) (d_expr (p2 d) d2 lam g g) <= ep;
   le_r: range (prodP R) d;
   le_p1: forall f, mu (p1 d) f <= mu d1 f;
   le_p2: forall f, mu (p2 d) f <= mu d2 f
 }.



 Lemma le_lift_elim: forall A B (R:A -> B -> Prop) 
  (d1:Distr A) (d2:Distr B) d (lam:D) ep (f:A -o> U) (g:B-o>U),
  (forall a b, R a b -> f a == g b) ->
  le_lift R d d1 d2 lam ep ->
  d_expr d1 d2 lam f g <= ep.
 Proof.
  intros A B R d1 d2 d lam ep f g Hfg (Hdist, Hrange, Hp1, Hp2). 
  rewrite d_expr_le; split.
    rewrite (Uminus_le_compat_right _ (lam ** (mu (p2 d)) g)). 
      rewrite <-(Hdist f g), <-max_le_left; apply Ule_plus_left.
      apply multDU_le_compat; trivial.      
      rewrite <-Hp1; unfold p1, p2; repeat rewrite Mlet_simpl.
      apply range_le with (1:=Hrange); intros; apply (Hfg _ _ H).
    rewrite (Uminus_le_compat_right _ (lam ** (mu (p1 d)) f)). 
      rewrite <-(Hdist f g), <-max_le_right; apply Ule_plus_left.
      apply multDU_le_compat; trivial.      
      rewrite <-Hp2; unfold p1, p2; repeat rewrite Mlet_simpl.
      apply range_le with (1:=Hrange); intros; apply (Hfg _ _ H).
 Qed.


 Lemma le_lift_true: forall (A B: Type) (d1: Distr A) (d2: Distr B) lam,
  le_lift (fun _ _ => True) (prod_distr d1 d2) d1 d2 lam
    ([1-] (lam ** (min (mu d1 (fone _)) (mu d2 (fone _))))).
 Proof.
  intros A B d1 d2 lam.
  constructor.
    (* distance *)
    intros f g; apply max_le.
      rewrite p1_prod_distr, d_expr_distr_mult; auto.
      rewrite p2_prod_distr, d_expr_distr_mult; auto.
    (* range *)
    apply range_True.
    (* projections *)
    intros.
    apply (mu_monotonic d1 (fun x : A => (mu d2) (fun _ : B => f x)) f).
    refine (ford_le_intro _); intro a; apply mu_cte_le.
    intros.
    rewrite (mu_cte_le d1 (mu d2 (fun b => f b))).
    apply mu_monotonic; auto.
 Qed.


 Lemma le_lift_Munit: forall (A:Type) (x y:A) (P:relation A) (lam:D) , 
  P x y -> 
  le_lift P (Munit (x,y)) (Munit x) (Munit y) lam 0.
 Proof.
  intros; constructor.
    (* distance *)
    intros.
       unfold p1, p2; repeat rewrite Mlet_unit, d_expr_nul; auto.
   (* range *)
   apply range_Munit with (1:=H).
   (* projections *)
   intros; trivial.
   intros; trivial.
 Qed.


 Lemma le_lift_Mlet: forall (A1 A2 B1 B2: Type) (R1: A1 -> B1 -> Prop)
  (R2: A2 -> B2 -> Prop) (d: Distr (A1 * B1)) 
  (d1: Distr A1) (d2: Distr B1) (F: A1 * B1 -> Distr (A2 * B2))
  (F1: A1 -> Distr A2) (F2: B1 -> Distr B2) (lam lam': D) (ep ep' :U),
  le_lift R1 d d1 d2 lam ep ->
  (forall (x : A1) (y : B1), R1 x y -> le_lift R2 (F (x, y)) (F1 x) (F2 y) lam' ep') ->
  le_lift R2 (Mlet d F) (Mlet d1 F1) (Mlet d2 F2) (lam *D* lam') (max (ep + lam ** ep') (ep' + lam' ** ep)).
 Proof.
  intros A1 A2 B1 B2 R1 R2 d d1 d2 F F1 F2 lam lam' ep ep' (Hd_dist, Hd_ran, Hp1d, Hp2d) HF.
  constructor.
    (* distance *)
    intros.
    apply (Ueq_orc ep' 1); [apply Ule_class | | ]; intro Hep'.
    (* case [ep'=1] *)
      rewrite  <-(max_le_right (ep + lam ** ep')), <-multDU_le, Hep', 
        <-(Uplus_sym 1), <-(Ule_plus_right 1); apply Unit.
    (* case [ep' < 1] *) 
    apply (Ule_diff_lt (Unit ep')) in Hep'.
    apply max_le; rewrite d_expr_le; split.
      (* 1st *)
      rewrite  <-(max_le_right).
      rewrite (Uminus_triang_ineq _ _ (lam ** (mu (Mlet (p1 d) F1) f))); apply Uplus_le_compat.
        rewrite <-(Hd_dist (fun x : A1 => (mu (F1 x)) f) (fzero _)), 
          <-max_le_right; apply Ule_plus_left.
        rewrite multDD_multDU_assoc, multDD_distr_minus_l; apply multDU_le_compat; trivial.
        unfold p1; repeat rewrite Mlet_simpl; rewrite <-multD_mu, mu_stable_le_minus.
        rewrite <-(mu_cte_le d ep'); unfold fcte.
        apply (range_le Hd_ran); intros (a,b) Hab; simpl. 
        rewrite <-(le_d (HF _ _ Hab) f g), <-max_le_right; apply Ule_plus_left.
      (* 2nd *)
      rewrite  <-(max_le_left).
      rewrite (Uminus_triang_ineq _ _ (lam' ** (mu (Mlet (p1 d) F1) f))); apply Uplus_le_compat.
        unfold p1; repeat rewrite Mlet_simpl; rewrite <-multD_mu, mu_stable_le_minus.
        rewrite <-(mu_cte_le d ep'); unfold fcte.
        apply (range_le Hd_ran); intros (a,b) Hab; simpl. 
        rewrite <-(le_d (HF _ _ Hab) f g), <-max_le_right; apply Ule_plus_right.
        rewrite multDD_comm, multDD_multDU_assoc, multDD_distr_minus_l; apply multDU_le_compat; trivial.
        rewrite <-(Hd_dist (fun x : A1 => (mu (F1 x)) f) (fzero _)), 
          <-max_le_right; apply Ule_plus_right.
      (* 3rd *)
      rewrite <-(max_le_right).
      rewrite (Uminus_triang_ineq _ _ (lam ** (mu (Mlet (p2 d) F2) g))); apply Uplus_le_compat.
        rewrite <-(Hd_dist (fzero _) (fun x  => (mu (F2 x)) g)), <-max_le_left; apply Ule_plus_left.
        rewrite multDD_multDU_assoc, multDD_distr_minus_l; apply multDU_le_compat; trivial.
        unfold p2; repeat rewrite Mlet_simpl; rewrite <-multD_mu, mu_stable_le_minus.
        rewrite <-(mu_cte_le d ep'); unfold fcte.
        apply (range_le Hd_ran); intros (a,b) Hab; simpl. 
        rewrite <-(le_d (HF _ _ Hab) f g), <-max_le_left; apply Ule_plus_left.
      (* 4th *)  
      rewrite  <-(max_le_left).
      rewrite (Uminus_triang_ineq _ _ (lam' ** (mu (Mlet (p2 d) F2) g))); apply Uplus_le_compat.
        unfold p2; repeat rewrite Mlet_simpl; rewrite <-multD_mu, mu_stable_le_minus.
        rewrite <-(mu_cte_le d ep'); unfold fcte.
        apply (range_le Hd_ran); intros (a,b) Hab; simpl. 
        rewrite <-(le_d (HF _ _ Hab) f g), <-max_le_left; apply Ule_plus_right.
        rewrite multDD_comm, multDD_multDU_assoc, multDD_distr_minus_l; apply multDU_le_compat; trivial.
        rewrite <-(Hd_dist (fzero _) (fun x => (mu (F2 x)) g)), 
          <-max_le_left; apply Ule_plus_right.
    (* range *)
    apply range_Mlet with (prodP R1).
    exact Hd_ran. 
    intros (a,b) H'; apply (le_r (HF _ _ H')).    

    (* projections *)
    intros.
    rewrite Mlet_simpl, <-Hp1d; unfold p1; repeat rewrite Mlet_simpl.
    apply range_le with (1:=Hd_ran); intros (a1,b1) Hab; simpl.
    refine (le_p1 (HF a1 b1 Hab) _).
    intros.
    rewrite Mlet_simpl, <-Hp2d; unfold p2; repeat rewrite Mlet_simpl.
    apply range_le with (1:=Hd_ran); intros (a1,b1) Hab; simpl.
    refine (le_p2 (HF a1 b1 Hab) _).
  Qed.


 Lemma le_lift_lift: forall A B (R:A -> B -> Prop) 
  (d1:Distr A) (d2:Distr B) d,
  le_lift R d d1 d2 D1 0 <-> lift R d d1 d2.
 Proof.
  split. 
    intros (Hdist, Hran, Hp1, Hp2).
    constructor.
      intro f.
      rewrite <-Uabs_diff_zero, <-(Ule_zero_eq _ (Ole_trans (max_le_right _ _) (Hdist f (fzero _)))).
      unfold Uabs_diff, d_expr; repeat rewrite multDU_D1_l; apply Oeq_refl.
      intro f.
      rewrite <-Uabs_diff_zero, <-(Ule_zero_eq _ (Ole_trans (max_le_left _ _) (Hdist (fzero _) f))).
      unfold Uabs_diff, d_expr; repeat rewrite multDU_D1_l; apply Oeq_refl.
      trivial.

    intros (Hfst, Hsnd, Hran).
    constructor; [ | auto | auto | auto ].
      intros f g.
      setoid_replace (p1 d) with d1 by refine (ford_eq_intro Hfst).
      setoid_replace (p2 d) with d2 by refine (ford_eq_intro Hsnd).
      rewrite d_expr_nul, d_expr_nul; auto.
 Qed.

 Lemma le_lift_weaken: forall A B d d1 d2 (P P':A -> B -> Prop) (lam lam':D) (ep ep':U), 
  (forall x y, P' x y -> P x y) ->
  lam' <= lam ->
  ep' <= ep ->
  le_lift P' d d1 d2 lam' ep' -> 
  le_lift P  d d1 d2 lam ep.
 Proof.
  intros A B d d1 d2 P P' lam' lam ep' ep HP Hlam Hep (Hdist, Hran).
  constructor.
    (* distance *)
    intros f g.
    rewrite <-Hep, <-(Hdist f g).
    apply max_le_compat; apply (d_expr_lam_weaken _ _ _ _ Hlam).  
    (* range *)
    apply range_weaken with (prodP P'). 
      unfold prodP; auto.
      assumption.
    (* projection *)
    assumption.
    assumption.
 Qed.

 
 Lemma le_lift_eq_compat : forall A B (R:A -> B -> Prop) 
 (d d' : Distr (A*B)) (d1 d1':Distr A) (d2 d2':Distr B) (lam lam':D) (ep ep':U),
  d == d' -> 
  d1 == d1' -> 
  d2 == d2' -> 
  lam == lam' ->
  ep == ep' ->
  le_lift R d d1 d2 lam ep -> le_lift R d' d1' d2' lam' ep'.
 Proof.
  intros A B R d d' d1 d1' d2 d2' lam lam' ep ep' Heq Heq1 Heq2 Heq3 Heq4 (Hdist, Hran, Hp1, Hp2).
  constructor.
    intros.
    unfold p1, p2; rewrite <-(@Mlet_eq_compat _ _  d d' (fun ab => Munit (fst ab)) (fun ab => Munit (fst ab)) Heq (Oeq_refl _)),
     <-(@Mlet_eq_compat _ _  d d' (fun ab => Munit (snd ab)) (fun ab => Munit (snd ab)) Heq (Oeq_refl _)).
    rewrite <-Heq1, <-Heq2, <-Heq3, <-Heq4.
    apply Hdist.
    apply range_stable_eq with (1:=Heq); trivial.
    intro f; rewrite <-(eq_distr_elim Heq1), <-Hp1.
    apply eq_distr_elim; rewrite Heq; trivial.
    intro f; rewrite <-(eq_distr_elim Heq2), <-Hp2.
    apply eq_distr_elim; rewrite Heq; trivial.
 Qed.


 Lemma le_lift_transp : forall (A B:Type) (d: Distr (A*B)) (d1:Distr A) (d2:Distr B) R lam ep, 
   le_lift (fun b a => R a b) (Mlet d (fun ab => Munit (snd ab, fst ab))) d2 d1 lam ep ->
   le_lift R d d1 d2 lam ep. 
 Proof.
  intros A B d d1 d2 R lam ep (Hdist, Hran, Hp1, Hp2); constructor.
    (* distance *)
    intros f g;  apply max_le.
      rewrite <-(Hdist g f), <-max_le_left; auto.
      rewrite <-(Hdist g f), <-max_le_right; auto.
    (* range *)
    intros f Hf.
    rewrite (Hran (fun ba => f (snd ba,fst ba))).
      rewrite Mlet_simpl; simpl.
      apply (mu_stable_eq d); refine (ford_eq_intro _); intros (a,b); trivial.
      auto.
    (* projections *)
    assumption.
    assumption.
 Qed.

 Lemma le_lift_prod: forall (A B:Type) (d:Distr (A * B)) (P: A -> B -> Prop),
   range (prodP P) d ->
   le_lift P d (p1 d) (p2 d) D1 0.
 Proof. 
  intros; constructor; trivial.
  intros; repeat rewrite d_expr_nul; auto.
 Qed.
     
   
End LE_LIFT.

 Add Parametric Morphism A B : (le_lift (A:=A) (B:=B))
 with signature Fimp2 (A:=A) (B:=B) --> 
  Oeq (O:=Distr (A * B)) ==> Oeq (O:=Distr A) ==> 
  Oeq (O:=Distr B) ==> Oeq (O:=D) ==> Oeq (O:=U) ==> inverse impl
 as elift_morph.
 Proof.
  unfold impl, Fimp2; intros R1 R2 H d1 d2 H0 d3 d4 H1 d5 d6 H2 lam1 lam2 H3 ep1 ep2 H4 H5.
  eapply le_lift_weaken  with R2 lam2 ep2; auto.
  apply le_lift_eq_compat with d2 d4 d6 lam2 ep2; auto.
 Qed.


End APPROX_LIFT.

