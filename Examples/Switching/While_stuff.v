Require Import SwitchingSem.

Open Scope nat_scope.
Set Implicit Arguments.

(********************* MOVE THIS SOMEWHERE ELSE *********************)
(********************************************************************)

 Lemma range_Munit: forall (A:Type) (a : A) (P : A -> Prop),
  P a -> range  P (Munit a).
 Proof.
  intros A a P Ha f Hf.
  apply (Hf a Ha).
 Qed.

 Lemma eval_lt : forall k (m:Mem.t k)  (e1 e2: E.expr T.Nat),
   E.eval_expr  e1 m < E.eval_expr e2 m <-> 
   E.eval_expr (e1 <! e2) m.
 Proof.
  intros; split; intros.
    change (is_true (leb ((E.eval_expr e1 m)+1) (E.eval_expr e2 m))).
    apply leb_correct; rewrite plus_comm; apply gt_le_S.
    assumption.
    change (is_true (leb ((E.eval_expr e1 m) + 1) (E.eval_expr e2 m))) in H.
    apply leb_complete in H; rewrite plus_comm in H; apply le_S_gt in H.
    assumption.
 Qed.

 Lemma drestr_range: forall A (d:Distr A) (P:A-o>boolO),  
    range P (drestr d  P).
  Proof.
   unfold range; intros.
   rewrite mu_drestr.
   rewrite (mu_stable_eq d _ (fzero _)).
     rewrite <-mu_zero; trivial.
     unfold restr; refine (ford_eq_intro _); intro a.
     generalize (H a); case (P a); intro Heq.
       rewrite <-Heq; trivial.
       trivial.
 Qed.

(********************************************************************)
(********************************************************************)


 Fixpoint seq_cmd (c:cmd) (n:nat) {struct n} : cmd :=
  match n with
   | O => @nil I.instr
   | S n => c ++ (seq_cmd c n)
  end.

 Lemma seq_cmd_Sn_tail_unfold : forall c E n k (m:Mem.t k) f,
  mu ([[ seq_cmd c (S n) ]] E m) f ==  
  mu ([[ seq_cmd c n ]] E m) (fun m' => mu ([[ c ]] E m') f). 
 Proof.
  induction n; intros.
    rewrite (deno_app_elim E c nil m), deno_nil_elim.
    refine (mu_stable_eq _ _ _ _); refine (ford_eq_intro _). 
    intro m'; apply deno_nil_elim.

    rewrite (deno_app_elim E c (seq_cmd c (S n)) m),
      (deno_app_elim E c (seq_cmd c n) m).
    refine (mu_stable_eq _ _ _ _); refine (ford_eq_intro _). 
    intro m'; apply IHn.
 Qed.

 Opaque deno.
 Opaque E.eval_expr.

 Lemma unroll_false_while_elim : forall (e:E.expr T.Bool) c n E k (m:Mem.t k) f,
  E.eval_expr e m = false ->
  mu ([[unroll_while e c n ]] E m) f == f m.
 Proof.
  intros; case n; simpl.
    
    rewrite (deno_cond_elim _ _ _ _ m).  
    case (@E.eval_expr _ T.Bool e m); rewrite deno_nil_elim; trivial.
    intro.
    rewrite (deno_cond_elim _ _ _ _ m), H, deno_nil_elim; trivial.
 Qed.


 Lemma false_while_elim : forall (e:E.expr T.Bool) c E k (m:Mem.t k) f,
  E.eval_expr e m = false ->
  mu ([[ [while e do c] ]] E m) f == f m.
 Proof.
  intros.
  rewrite deno_while_elim, deno_cond_elim, H.
  apply deno_nil_elim.
 Qed.


 Section for_loop.

  Close Scope U_scope.
  Open Scope nat_scope.

  Variable i : E.expr T.Nat.
  Variable q : nat.
  Variable c : cmd.
  Variable E : env.
  Variable P : forall k, (Mem.t k) -> Prop.
  
  Hypothesis Hran : forall k (m:Mem.t k), 
   P m ->
   range (fun m' => E.eval_expr i m' = S (E.eval_expr i m) /\ P m') ([[c]] E m).


 Lemma seq_cmd_range:  forall n k (m:Mem.t k), 
  P m ->
  range (fun m' => E.eval_expr i m' = E.eval_expr i m + n /\ P m') ([[seq_cmd c n ]] E m). 
 Proof.
  induction n; intros.
    rewrite deno_nil, plus_0_r.
    apply range_Munit; split; trivial.

    rewrite (deno_app E c (seq_cmd c n) m) .
    eapply range_Mlet; [ apply (Hran H) | ].
    intros m' [Hm'1 Hm'2].
    eapply range_weaken; [ | apply (IHn _ _ Hm'2) ].
    intros m'' [Hm''1 Hm''2]; split.
      rewrite Hm''1, Hm'1; apply plus_Snm_nSm.
      assumption.
 Qed.
  (* TODO: use this to simpify following proofs *)


  Lemma unroll_for_loop_aux: forall n j k (m:Mem.t k) f, 
   P m ->
   q - E.eval_expr i m < S n ->
   mu ([[ unroll_while (i <! q) c (j + n)]] E m) f == 
   mu ([[ unroll_while (i <! q) c n ]] E m)  
     (fun m' => mu (if negP (E.eval_expr (i <! q)) m' then Munit m' else (@distr0 _) ) f).
 Proof.
  induction n; intros; unfold negP; intros.
    (* case n=0 *)
    rewrite plus_0_r.
    assert (@E.eval_expr _ T.Bool (i <! q) m = false) by
      (apply (leb_correct_conv q (E.eval_expr i m + 1)%nat); omega).
    destruct j; simpl.
      repeat (rewrite (deno_cond_elim _ _ _ _ m); case (@E.eval_expr _ T.Bool (i <! q) m); 
        rewrite deno_nil_elim); (rewrite H1; trivial).
      repeat rewrite (deno_cond_elim  _ _ _ _ m), H1, deno_nil_elim.
      rewrite H1; trivial.
    (* inductive case *)
    rewrite plus_comm, plus_Sn_m, plus_comm; simpl.
    repeat rewrite (deno_cond_elim  _ _ _ _ m).
    case_eq (@E.eval_expr _ T.Bool (i <! q) m); [ intros _ | intro Heq ].
      (* case [i < q] *)
      repeat rewrite deno_app_elim.
      apply (range_eq (Hran H)); intros m' [Hm'1 Hm'2].
      apply (IHn _ _ _ _ Hm'2); repeat rewrite eval_minus in *; omega.
      (* case [i >= q ] *) 
      rewrite deno_nil_elim, deno_nil_elim, Heq; trivial.
 Qed.


 Lemma unroll_for_loop: forall k (m:Mem.t k) f n,
   P m ->
   q - E.eval_expr i m < S n ->
   mu ([[ [while (i <! q) do c] ]] E m) f ==  mu ([[ unroll_while (i <! q) c n]] E m) 
     (fun m' => mu (if negP (E.eval_expr (i <! q)) m' then Munit m' else (@distr0 _) ) f).
 Proof.
  intros.
  rewrite deno_while_unfold_elim.
  match goal with |- _ == ?F => rewrite <-(lub_cte F) end.
  refine (@lub_eq_lift _ _ _ n _). 
  intros j Hj; simpl.
  rewrite <-(plus_0_l n), (le_plus_minus _ _ Hj), plus_comm.
  repeat rewrite (@unroll_for_loop_aux  n _ _ _ _ H H0). 
  trivial.
 Qed.


 Lemma unroll_for_loop_seq_cmd_aux: forall j n k (m:Mem.t k) f, 
   P m ->
   (j <= q - E.eval_expr i m)%nat ->
   mu ([[ unroll_while (i <! q) c (j + n) ]] E m) f == 
   mu ([[ seq_cmd c j ]] E m)  
    (restr (EP k (i =?= E.eval_expr i m + j))  
      (fun m' => mu ([[ unroll_while (i <! q) c n]] E m') f)). 
 Proof.
  induction j; intros; unfold seq_cmd.
    (* case [j = 0] *)
    rewrite deno_nil_elim, plus_0_r.
    unfold restr, EP; replace 
      (@E.eval_expr _ T.Bool (i =?= E.eval_expr i m) m) with true; trivial.
      symmetry; apply (nat_eqb_refl (E.eval_expr i m)).
    (* inductive case *)
    rewrite plus_Sn_m; simpl; fold (seq_cmd c j).
    repeat rewrite (deno_cond_elim _ _ _ _ m).
    replace (@E.eval_expr _ T.Bool (i <! q) m) with true;
     [|symmetry; apply (leb_correct (E.eval_expr i m + 1) q); omega ].
    repeat rewrite (deno_app_elim _ _ _ m).
    apply (range_eq (Hran H)); intros m' [Hm'1 Hm'2].
    rewrite <-plus_Snm_nSm, <-Hm'1.
    apply (IHj _ _ _ _ Hm'2); omega.
 Qed.



End for_loop.

 
Close Scope U_scope.

 Lemma unroll_for_loop_seq_cmd: forall (i : E.expr T.Nat) c E (P:forall k, Mem.t k -> Prop) (n:nat) k (m:Mem.t k) f,
   (forall k (m:Mem.t k), P _ m ->
    range (fun m' => E.eval_expr i m' = S (E.eval_expr i m) /\ P _ m') ([[c]] E m)) ->
   P _ m ->
   E.eval_expr (i <! n) m = true  ->
   mu ([[ [ while (i <! n) do c ] ]] E m) f == 
   mu ([[ seq_cmd c (n - E.eval_expr i m) ]] E m) 
     (restr (EP k (i =?= n)) f).
 Proof.
  intros.
  rewrite (@unroll_for_loop _ _ _ _ _ H _ _ _ _  H0 (lt_n_Sn _)).    
  rewrite <-(plus_0_r (n - E.eval_expr i m)),
   (unroll_for_loop_seq_cmd_aux _ _ _ H _ _ _ H0 (le_refl _)), plus_0_r.
  refine (mu_stable_eq _ _ _ _).
  unfold restr, EP, negP; refine (ford_eq_intro _); intro m'.
  replace (E.eval_expr i m + (n - E.eval_expr i m))%nat with n;
   [ | apply (leb_complete  (E.eval_expr i m + 1) n) in H1; omega].
  generalize (eval_eq m' i n); simpl;
  case_eq (@E.eval_expr _ T.Bool (i =?= n) m'); intros ? Heq.
    assert (@E.eval_expr _ T.Bool (i <! n) m' = false) by
      (apply (leb_correct_conv (E.eval_expr n m') (E.eval_expr i m' + 1));
      rewrite (nat_eqb_true (eq_sym Heq)), plus_comm; apply lt_n_Sn).
    rewrite (deno_cond_elim _ _ _ _ m');  case (@E.eval_expr _ T.Bool (i <! n) m'); 
      rewrite deno_nil_elim; rewrite H3; trivial.
    trivial.
 Qed.

 Lemma for_loop_tail_unroll: forall (i : E.expr T.Nat) (n:nat) c E (P:forall k, Mem.t k -> Prop) k (m:Mem.t k) f,
   (forall k (m:Mem.t k), P _ m ->
    range (fun m' => E.eval_expr i m' = S (E.eval_expr i m) /\ P _ m') ([[c]] E m)) ->
   P _ m ->
   mu ([[ [ while i <! S n do c ] ]] E m) f  == 
   mu ([[ (while i <! n do c) :: [If i <! S n _then c]   ]] E m) f.
 Proof.
  intros.
  rewrite (deno_cons_elim _ (while i <! n do c)), Mlet_simpl.
  destruct (lt_eq_lt_dec (E.eval_expr i m) n) as [ [H' | H'] | H'].
    (* case [i < n] *)
    repeat rewrite (unroll_for_loop_seq_cmd _ _ _ _ _ H H0); [ |
      rewrite <-(eval_lt m i n); trivial |
      rewrite <-(eval_lt m i (S n)); transitivity n; [ trivial | apply lt_n_Sn ] ].
    rewrite <-(minus_Sn_m _ _ (lt_le_weak _ _ H')), seq_cmd_Sn_tail_unfold.
    apply (range_eq (seq_cmd_range _ _ H _ _ H0)).
    intros m' [Hm'1 Hm'2]; rewrite <-(le_plus_minus _ _  (lt_le_weak _ _ H')) in Hm'1.
    unfold restr, EP; replace (@E.eval_expr _ T.Bool (i =?= n) m') with true;
      [ | symmetry; setoid_rewrite (eval_eq m' i n); rewrite Hm'1; apply nat_eqb_refl ].
    rewrite (deno_cond_elim _ _ _ _ m').
    replace (@E.eval_expr _ T.Bool (i <! S n) m') with true;
     [ | symmetry; rewrite <-(eval_lt m' i (S n)), Hm'1; apply lt_n_Sn ].
    apply (range_eq (H _ _ Hm'2)); intros m'' [Hm''1 Hm''2].
    replace (@E.eval_expr _ T.Bool (i =?= S n) m'') with true; trivial.
      symmetry; setoid_rewrite (eval_eq m'' i (S n)); rewrite Hm''1, Hm'1; apply nat_eqb_refl.
    (* case [i = n] *)
    rewrite (unroll_for_loop_seq_cmd _ _ _ _ _ H H0); 
      [ | rewrite <-(eval_lt m i (S n)), H'; apply lt_n_Sn ].
    rewrite  H', <-(minus_Sn_m _ _ (le_refl _)), minus_diag.
    rewrite false_while_elim; [ |
     apply (leb_correct_conv n (E.eval_expr i m + 1)); rewrite H', plus_comm; apply lt_n_Sn ].
    rewrite deno_cond_elim.
    replace (@E.eval_expr _ T.Bool (i <! S n) m) with true; [ |
      symmetry; apply (leb_correct (E.eval_expr i m + 1) (S n)); rewrite H', plus_comm; apply le_refl ].
    simpl; rewrite (app_nil_r c).
    apply (range_eq (H _ _ H0)).
    intros m' [Hm'1 Hm'2].
    unfold restr, EP; replace (@E.eval_expr _ T.Bool (i =?= S n) m') with true; trivial.
      symmetry; setoid_rewrite (eval_eq m' i (S n)); rewrite Hm'1, H'; apply nat_eqb_refl.
    (* case [i > n] *)
    rewrite (false_while_elim (i <! n));
      [ | apply (leb_correct_conv n (E.eval_expr i m + 1)); omega ].
    rewrite deno_while_elim, deno_cond_elim, deno_cond_elim.
    replace (@E.eval_expr _ T.Bool (i <! S n) m) with false; trivial.
      symmetry; apply (leb_correct_conv (S n) (E.eval_expr i m + 1)); omega.
 Qed.

 Lemma while_range : forall (i: E.expr T.Nat) (n:nat) c E (P:forall k, Mem.t k -> Prop) k (m:Mem.t k),
   (forall k (m:Mem.t k), P _ m ->
    range (fun m' => E.eval_expr i m' = S (E.eval_expr i m) /\ P _ m') ([[c]] E m)) ->
   P _ m ->
   E.eval_expr (i<!n) m = true ->
   range (EP k (i =?= n)) ([[ [ while i <! n do c ] ]] E m).
 Proof.
  intros.
  apply range_stable_eq with (drestr ([[seq_cmd c (n - E.eval_expr i m)]] E m) (EP k (i =?= n))).
    apply eq_distr_intro; intro f;
     rewrite (unroll_for_loop_seq_cmd _ _ _ _ _ H H0 H1), mu_drestr; trivial.
    apply drestr_range.
 Qed.


 (* This is the lemma used to prove the rule for bounded loops.
    TODO: simplify the proof *)
 Lemma init_for_loop_tail_unroll: forall (i : E.expr T.Nat) (n:nat) c E (P:forall k, Mem.t k -> Prop) k (m:Mem.t k) f,
   (forall k (m:Mem.t k), P _ m ->
    range (fun m' => E.eval_expr i m' = S (E.eval_expr i m) /\ P _ m') ([[c]] E m)) ->
   P _ m ->
   E.eval_expr i m = 0%nat ->
   mu ([[ [ while i <! S n do c ] ]] E m) f  == 
   mu ([[ (while i <! n do c)::c ]] E m) f.
 Proof.
  intros.
  rewrite (for_loop_tail_unroll _ _ _ _ _ H H0).
  rewrite deno_cons_elim, Mlet_simpl, (deno_cons_elim _ _ c), Mlet_simpl.
  case_eq (nat_eqb n 0); intro Hn.
    (* case [n=0] *)
    apply nat_eqb_true in Hn.
    assert (Hc1: @E.eval_expr _ T.Bool (i <! n) m = false) by
      (apply (leb_correct_conv n (E.eval_expr i m + 1)); omega).
    repeat rewrite deno_while_elim, (deno_cond_elim _ (i <! n)), Hc1, deno_nil_elim.
    assert (Hc: @E.eval_expr _ T.Bool (i <! S n) m = true) by
      (apply (leb_correct (E.eval_expr i m + 1) (S n)); omega).
    rewrite deno_cond_elim, Hc; trivial.
    (* case [n<>0] *)
    generalize (nat_eqb_spec n 0); rewrite Hn; clear Hn; intro Hn.  
    assert (Hc: E.eval_expr (i <! n) m = true) by
      (apply (leb_correct  (E.eval_expr i m + 1) n); omega).
    refine (range_eq (while_range _ _ _ _ H H0 Hc) _ _ _).
    unfold EP; intros m' Hm'.
    setoid_rewrite (eval_eq m' i n) in Hm'; apply nat_eqb_true in Hm';
      change ( E.eval_expr i m' = n) in Hm'.
    assert (Hc' : @E.eval_expr _ T.Bool (i <! S n) m' = true) by
      (apply (leb_correct  (E.eval_expr i m' + 1) (S n)); omega).
    rewrite deno_cond_elim, Hc'; trivial.
 Qed.

 Lemma while_eq_guard_compat_elim: forall (e1 e2 : E.expr T.Bool) c E k (m:Mem.t k) f,
   (forall (m':Mem.t k), E.eval_expr e1 m' = E.eval_expr e2 m') ->
   mu ([[ [ while e1 do c ] ]] E m) f == mu ([[ [ while e2 do c ] ]] E m) f.
 Proof.
  intros.
  repeat rewrite deno_while_unfold_elim.
  apply lub_eq_compat.
  refine (ford_eq_intro _). 
  intro n; generalize n m H; clear H m n.
  induction n; intros; simpl in *; unfold negP.
    repeat rewrite (deno_cond_elim _ _ _ _ m).
    rewrite <-H; case (@E.eval_expr _ T.Bool e1 m).
      rewrite deno_nil_elim, deno_nil_elim, <-H; trivial.
      rewrite deno_nil_elim, deno_nil_elim, <-H; trivial.

    repeat rewrite (deno_cond_elim _ _ _ _ m).
    rewrite <-H; case (@E.eval_expr _ T.Bool e1 m).
      repeat rewrite deno_app_elim.
      apply mu_stable_eq; refine (ford_eq_intro _); intros m'.
      apply (IHn _ H). 
      rewrite deno_nil_elim, deno_nil_elim, <-H; trivial.
 Qed.


