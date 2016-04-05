(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

Require Export Operators.

Require Import ssreflect eqtype 
 ssrbool ssrfun fingroup Ssreflect.choice fintype ssrnat seq finalg ssralg.   

Require Import abelian Ssreflect.cyclic bigop gproduct finset div.

Open Scope nat_scope.

Set Implicit Arguments.

Fixpoint seq_list_def A (l : list A) : seq A :=
 match l with
  | List.nil => nil
  | List.cons a tl => Cons _ a (seq_list_def tl)
 end.

Fixpoint list_seq_def A (l : seq A) : list A :=
 match l with
  | nil => List.nil
  | Cons a tl => List.cons a (list_seq_def tl)
 end.

Coercion seq_list_def : list >-> seq.
Coercion list_seq_def : seq >-> list.

Lemma nth_ssr_coq : forall A i (l : list A) d,
 List.nth i l d = nth d l i.
Proof.
 move=> A; elim => /=.
 by case=> d /=.
 move=> n IH; case => d //=.
Qed.

Lemma seq_list_seq_def : forall A (l : seq A),
 seq_list_def (list_seq_def l) = l.
Proof.
 move=> A; elim => //.
 by move=> x l H; rewrite -{2} H.
Qed.

Lemma list_seq_seq_def : forall A (l : list A),
 list_seq_def (seq_list_def l) = l.
Proof.
 move=> A; elim => //.
 by move=> x l H; rewrite -{2} H.
Qed.

Fixpoint seq_combine A B  (l : seq A) (l' : seq B) : seq (A*B) :=
 match l,l' with
  | x::tl, y::tl' => (x,y)::(seq_combine tl tl')
  | _, _ => nil
 end.

Lemma seq_combine_length : forall A B (l:seq A)(l':seq B),
 size (seq_combine l l') = MinMax.min (size l) (size l').
Proof. by move=> A B l; elim: l => //= => x l IH; case=> //= y l'; rewrite IH. Qed.

Lemma combine_nth2 : forall (A B : Type) (l : seq A) (l' : seq B) 
 (n : nat) (x : A) (y : B),
 size l = size l' ->
 nth (x,y) (seq_combine l l') n = (nth x l n, nth y l' n).
Proof.
 move=> A B; elim.
 by case => //=; case => /=.
 move=> a l IH; case => //= b l'; case => //= n x y H.
 rewrite IH => //; move: H; apply eq_add_S.
Qed.

Definition seq_mmap2 (A B C:Type) (f:A -> B-> C) (l1:seq A) (l2:seq B) :=
 map (fun ab => f (fst ab) (snd ab)) (seq_combine l1 l2).

Lemma map_nth2 : forall (A B : Type) (f : A -> B) (l : seq A) (d : A) (n : nat),
 nth (f d) (map f l) n = f (nth d l n).
Proof.
 move=> A B f; elim.
 by move=> d n /=; case: n.
 move=> x l IH d n /=.
 by case: n => // n'; apply: IH.
Qed.

Lemma size_length : forall A (l : list A), length l = size l.
Proof. by move=> A l; elim l => //= x l' ->. Qed.


Module Type CFG.

 Parameter T : nat -> baseFinGroupType.
 
 Parameter mulg_comm : forall k (x y:T k), mulg x y = mulg y x.
 
 Parameter left_inv:forall k (x:T k), (x^-1 * x)%g = 1%g.
 
 Parameter elems : forall k, list (T k).
 
 Parameter elems_full : forall k t, In t (elems k).
 
 Parameter elems_NoDup : forall k, NoDup (elems k).

End CFG.


Module Type FINITE_TYPE.

 Parameter t : nat -> Type.

 Parameter default : forall k, t k.

 Parameter elems : forall k, list (t k).

 Parameter elems_poly : polynomial.

 Parameter eqb : forall k, t k -> t k -> bool.
 
 Parameter eqb_spec : forall k (x y:t k), if eqb x y then x = y else x <> y.

 Parameter eqb_refl : forall k (x:t k), eqb x x.

 Parameter elems_notnil : forall k, elems k <> nil.

 Parameter elems_full : forall k (x:t k), In x (elems k).

 Parameter elems_NoDup : forall k, NoDup (elems k).

 Parameter elems_size_nat : forall k,
  (size_nat (length (elems k)) <= elems_poly k)%coq_nat.

End FINITE_TYPE.


Module CFG_TO_FT (FG:CFG) <: FINITE_TYPE.

 Definition t k : Type := FG.T k.

 Section DEF.

  Variable k : nat.

  Definition default : t k := 1%g.

  Definition elems := FG.elems.

  Parameter elems_poly : polynomial.

  Definition eqb (x y:t k) := x == y.
 
  Lemma eqb_spec : forall (x y:t k), if eqb x y then x = y else x <> y.
  Proof.
   by move=> x y;rewrite /eqb;case: eqP.
  Qed.

  Lemma eqb_refl : forall (x:t k), eqb x x.
  Proof.
   rewrite /eqb=> x;rewrite eqxx //.
  Qed.

  Parameter elems_full : forall (x:t k), In x (elems k).

  Lemma elems_notnil : elems k <> List.nil.
  Proof.
   move=> Heq; move:(elems_full default);rewrite Heq //=.
  Qed.

  Definition elems_NoDup := FG.elems_NoDup.

  Parameter elems_size_nat : 
    (size_nat (length (elems k)) <= elems_poly k)%coq_nat.

 End DEF.

End CFG_TO_FT.


Module CFG_TO_LOG (FG:CFG) <: FINITE_TYPE.

 Section DEF.

  Variable k : nat.

  Canonical Structure GFinGroupType := 
   Eval hnf in FinGroupType (FG.left_inv k).
  
  Lemma abelian_G : forall G : {group (FG.T k)}, abelian G.
  Proof.
   move => G; rewrite /abelian; apply /subsetP => x Hx.
   apply /centP => y hy; rewrite /commute; apply: FG.mulg_comm.
  Qed.
  
  Definition G := [set: GFinGroupType]%G.
  
  Import FG.
  
  Definition gen : seq (T k) :=
   let (a, _, _) := abelian_structure (abelian_G G) in a.
  
  Definition invariants :  seq nat := map (fun g => #|<[g]>|)%G gen. 
  
  Definition N := size invariants.
  
  Lemma invariants_lb : forall (n : nat),
   n \in invariants -> 0 < n.
  Proof.
   rewrite /invariants => n /mapP [x H1 ->]; exact: cardG_gt0.
  Qed.
  
  Definition P (l : seq nat) : bool :=
   (size l == N) && 
   all (fun (i : nat) => nth 0 l i < nth 0 invariants i) (List.seq 0 N).
  
  Definition t := {l:seq nat | P l }.
  
  Lemma cyclePmin2 : forall (gT : finGroupType) (g y : gT),
   {i : nat | y \in <[g]>%g -> (i < #[g]%g) /\ (y = (g ^+ i)%g) }.
  Proof.
   move=> gT g y.
   case H : (y \in <[g]>%g).
   case: (cyclePmin H) => n W1 W2.
   by exists n.
   by exists 0.
  Qed.
  
  Definition log1 (g x : T k) : nat :=
   let (n, _) := cyclePmin2 _ g x in n.
  
  Lemma log1_lt : forall (x g : T k),
   x \in <[g]>%g -> log1 g x < #[g]%g.
  Proof.
   rewrite /log1 => x g H.
   case: cyclePmin2 => i H2.
   by apply H2 in H; case: H.
  Qed.
  
  Fixpoint logN_def (x : T k) (l : seq (T k)) : seq nat :=
   match l with
    | nil => nil
    | g :: l' => 
     let x1 := divgr (<[g]>)%g (\big[dprod/1]_(j <- l') <[j]>)%g x in
     let x2 := remgr (<[g]>)%g (\big[dprod/1]_(j <- l') <[j]>)%g x in
      log1 g x1 :: logN_def x2 l'
   end.
  
  Fixpoint powN_def (lg : seq (T k)) (ln : seq nat) : (T k) :=
   match lg, ln with
    | nil, nil => 1%g
    | g :: lg', n :: ln' =>
     ((g ^+ n)%g * (powN_def lg' ln'))%g
    | _, _ => 1%g
   end.
  
  Lemma G_full : forall (x : T k), x \in G.
  Proof. move=> x; apply in_setT. Qed.
  
  Lemma powN_logN_def : forall (x:T k),
   x = powN_def gen (logN_def x gen).
  Proof.
   move=> x.
   rewrite  /gen.
   case: (abelian_structure (abelian_G G )) => lg H1 _.
   have:= (G_full x).
   elim: lg x G H1.
   rewrite big_nil.
   move => x G H1 /=.
   move => H2.
   apply/(@set1gP _ x).
   by rewrite H1.
   move=> g lg H1 x G.
   rewrite big_cons => defG HG.
   case/dprodP: defG => [[_ H _ defH] W4 _ prod] /=.
   rewrite /log1.
   case: (cyclePmin2 GFinGroupType g (divgr <[g]> (\big[dprod/1]_(j <- lg) <[j]>) x))%g => n.
   case H2: (divgr <[g]> (\big[dprod/1]_(j <- lg) <[j]>) x \in <[g]>)%g.
   move=> Hn.
   case: Hn; first by [].
   move => W1 W2.
   rewrite -W2 -(H1 _ H) -?divgr_eq //.
   rewrite -defH.
   apply: mem_remgr.
   by rewrite  W4.
   move=> _.
   move: HG.  rewrite -W4.
   by move /mem_divgr; move /negP : H2.
  Qed.

  Lemma ttP : forall l,
   reflect (size l = N /\ forall i, i < N -> nth 0 l i < nth 0 invariants i)
   (P l).
  Proof.
   move=> l; rewrite /P.
   case H : ((size l == N ) && 
    all (fun (i : nat) => nth 0 l i < nth 0 invariants i) (List.seq 0 N));
   [apply: ReflectT | apply: ReflectF].
   
   move /andP : H => [/eqP H1 /allP H2].
   split => //.
   move=> i /ltP Hi.
   apply H2.
   assert (In i (List.seq 0 N)).
   apply le_In_seq; split; omega.
   move: H; clear.
   move: 0.
   elim: N  => //=.
   move=> n IH i' [<- | H2].
   apply: mem_head.
   rewrite in_cons; apply /orP; right.
   by apply IH.
   
   move /andb_false_iff : H => [H | H] [H1 H2].
   by move /eqP : H.
   move /allP : H; apply => i Hi.
   apply H2.
   assert (In i (List.seq 0 N )).
   move: Hi; clear.
   move: 0.
   elim: N  => //=.
   move=> n IH i'.
   rewrite in_cons.
   move=> /orP [/eqP -> | H2].
   by left.
   by right; apply IH.
   apply In_seq_le in H.
   apply /ltP; omega.
  Qed.

  Definition logN (x : T k) : t.
   move=> x.
   exists (logN_def x gen).
   apply /ttP.
   rewrite /N /invariants size_map /gen.
   case: (abelian_structure (abelian_G G)) => lg H1 _.
   have:= (G_full x).
   move: x; elim: lg G H1 => //=.
   move=> g gen H G.
   rewrite big_cons => defG x Hin.
   case/dprodP: defG => [[_ F _ defF] defG _ prod] /=.
   have:= (H F defF (remgr <[g]>%g (\big[dprod/1%g]_(j <- gen) <[j]>%g) x)); clear H; case.
   rewrite defF.  
   by apply: mem_remgr; rewrite -defF defG.
   move=> [-> W]; split => //; case => /= Hi.
   apply: log1_lt.
   by apply: mem_divgr; rewrite defG.
   move=> n.
   by apply W.
  Defined.

  Definition powN (l : t) : T k :=
   let (l, K) := l in powN_def gen l.

  Definition tid := logN 1.
  
  (* [logN] specification *)

  Lemma powN_logN : forall (x:T k), 
   x = powN (logN x).
  Proof. rewrite /powN /logN => x; apply powN_logN_def. Qed.
 
  (* [powN] specification *)
  Lemma powN_1 : 1%g = powN tid.
  Proof.
   apply powN_logN.
  Qed.
  
  Lemma powN_in_big : forall lg ln (G' : {group GFinGroupType }),
   (\big[dprod/1%g]_(j <- lg) <[j]>%g = G')%g ->
   size ln = size lg ->
   powN_def lg ln \in \big[dprod/1%g]_(j <- lg) <[j]>%g.
  Proof.
   move => lg; elim: lg.
   case => //=; rewrite big_nil.
   by move => G H _; apply /set1gP.
   move=> x lg IH; case => // n ln G /=.
   rewrite big_cons => H1 H2.
   case/dprodP: H1 => [[G1 G2 HG1 defG'] W4 _ prod] /=.
   rewrite defG'.
   rewrite dprodE.
   apply: mem_mulg.
   apply: mem_cycle.
   rewrite -defG'.
   apply: (IH _ G2) => //.
   move: H2;apply eq_add_S.
   apply /subsetP => y Hy; apply /centP => z Hz.
   rewrite /commute.
   apply: FG.mulg_comm.
   by rewrite -defG'.
  Qed.
  
  Lemma powN_inj: forall (z1 z2:t ),
   powN z1 = powN z2 -> 
   proj1_sig z1 = proj1_sig z2.
  Proof.
   move=> [l1 W1] [l2 W2] => /=.
   move /ttP : W1.
   move /ttP : W2.
   move=> [W1 W1'] [W2 W2'].
   have:= (@G_full (powN_def gen l1)).
   have:= (@G_full (powN_def gen l2)).
   move: l1 l2 W1 W2 W1' W2'; rewrite /N /invariants /gen size_map.
   case: (abelian_structure (abelian_G G)) => lg H1 _.   
   elim: lg G H1.
   move=> G HG.
   case => //; case => //.
   move=> g lg IH G; rewrite big_cons => defG.
   case => //.
   move => n1 l1.
   case => //.
   case/dprodP: defG => [[_ F _ defF] defG _ prod] /=.  
   move => n2 l2 /= Hsize1 Hsize2 Hnf1 Hnf2 Hin2 Hin1.

   have dp : ((<[g]> \x F)%g = G).
   rewrite dprodE.
   by rewrite -defF.
   apply /subsetP => y Hy; apply /centP => z Hz.
   rewrite /commute.
   apply: mulg_comm.
   by rewrite -defF.
   move=> Heq.

   have H : ((g ^+ n1)%g = (g^+ n2)%g /\ powN_def lg l1 = powN_def lg l2).
   case: (mem_dprod dp Hin1) => a1.
   case => a2 Ha.
   case Ha => A1 A2 A3 A4.
   case: (mem_dprod dp Hin2) => b1.
   case => b2 Hb.
   case Hb => B1 B2 B3 B4.

   case (A4 (g ^+ n1)%g (powN_def lg l1) ) => //.
   apply: mem_cycle.
   rewrite -defF.
   apply: (powN_in_big l1 F defF).
   by apply eq_add_S.

   case (B4 (g ^+ n2)%g (powN_def lg l2) ) => //.
   apply: mem_cycle.
   rewrite -defF.
   apply: (powN_in_big l2 F defF).
   by apply eq_add_S.

   move=> -> -> -> ->.
   apply: B4 => //; by rewrite -Heq.
   case H => H1 H2.

   f_equal.
   move /eqP : H1 => H1.
   rewrite eq_expg_mod_order in H1.
   move: H1.
   rewrite !modn_small.
   apply /eqP.
   by have:= (Hnf1 0) => /=; apply.
   by have:= (Hnf2 0) => /=; apply.

   apply (IH F) => //.
   
   by apply eq_add_S.
   by apply eq_add_S.
   move=> i Hi; by have:= (Hnf1 (S i)) => /=; apply.
   move=> i Hi; by have:= (Hnf2 (S i)) => /=; apply.
   rewrite -defF.
   apply: (powN_in_big l2 F defF).
   by apply eq_add_S.
   rewrite -defF.
   apply: (powN_in_big l1 F defF).
   by apply eq_add_S.
  Qed.
  
  Lemma eq_P : forall A x (P:A -> bool) (H1:P x) (H2:P x), H1 = H2.
  Proof.
   move=> A x P H1 H2.
   apply eq_proofs_unicity.
   intros a b; case (bool_dec a b); auto.
  Qed.
  
  Lemma eq_exist : forall A (P:A -> bool) x1 x2 (H1:P x1) (H2:P x2),
   x1 = x2 ->
   exist P x1 H1 = exist P x2 H2.
  Proof. 
   move=> A P x1 x2 H1 H2 H; move: H1 H2.
   rewrite H => p1 p2.
   by rewrite (eq_P _ _ p1 p2). 
  Qed.

  Lemma logN_powN: forall (z:t), logN (powN z) = z.
  Proof.
   move=> [l Hl].
   rewrite /powN /logN; apply eq_exist.
   move /ttP : Hl.
   rewrite  /logN /powN /P /N /invariants /gen.
   move: (@abelian_type_gt1 GFinGroupType G) => Hgt.
   case: (abelian_structure (abelian_G G )) => lg defG _ [Hl1 Hl2].
   elim: lg l G Hl1 Hl2 defG.
   by rewrite big_nil => /=; case.
   move=> g lg IH.
   case; first by [].
   move => n l G Hsize Hnf.
   rewrite big_cons => defG /=.
   case/dprodP: defG => [[_ G' _ defG'] W4 _ prod] /=.
   f_equal.
   have Hlog:(n = log1 g (g ^+ n))%g.
   rewrite /log1.
   case: cyclePmin2.
   move=> i W1.
   case: W1.
   apply: mem_cycle.
   move=> W1 W2.
   move /eqP : W2.
   rewrite eq_expg_mod_order.
   rewrite !modn_small; trivial.
   by move /eqP.
   have:= (Hnf 0) => /=.
   by rewrite size_map; apply.
   rewrite{2} Hlog.
   f_equal.
   rewrite defG' divgrMid //.
   by rewrite -defG'.
   apply: mem_cycle.
   rewrite -defG'.
   apply (@powN_in_big _ _ _ defG').
   clear Hnf; move: Hsize => /=.
   rewrite size_map; apply eq_add_S.
   rewrite defG' remgrMid.
   apply: (IH l G').
   clear Hnf; move: Hsize => /=; apply eq_add_S.
   rewrite size_map.
   move=> i Wi /=.
   by have:= (Hnf (S i)) => /=; apply; rewrite size_map.
   by rewrite -defG'.
   by rewrite -defG'.
   apply: mem_cycle.
   rewrite -defG'.
   apply (@powN_in_big _ _ _ defG').
   clear Hnf; move: Hsize => /=.
   rewrite size_map; apply eq_add_S.
  Qed.

  Definition tinv (z:t) := logN ((powN z)^-1).

  Lemma inv_powN : forall (z:t),
   ((powN z)^-1)%g = powN (tinv z).
  Proof.
   move=> z; rewrite /tinv -powN_logN //.
  Qed.

  Definition tplus (z1 z2:t) := logN (powN z1 * powN z2).

  Lemma mul_powN : forall (z1 z2:t),
   ((powN z1) * (powN z2) = powN (tplus z1 z2))%g.
  Proof.
   move=> z1 z2;rewrite /tplus -powN_logN //.
  Qed.

  Definition default := logN (1%g).

  Definition elems := List.map logN (FG.elems k).

  Parameter elems_poly : polynomial.

  Definition eqb (x y : t):= x == y.

  Lemma eqb_spec : forall (x y:t), if eqb x y then x = y else x <> y.
  Proof. by move=> x y;rewrite /eqb;case: eqP. Qed.

  Lemma eqb_refl : forall (x:t), eqb x x.
  Proof. by move=>x; rewrite /eqb eqxx. Qed.

  Lemma elems_full : forall (x:t), In x elems.
  Proof.
   rewrite /elems; move=> x.
   rewrite -(logN_powN x).
   apply in_map.
   apply FG.elems_full.
  Qed.

  Lemma elems_notnil : elems <> nil.
  Proof.
   move=> Heq; move:(elems_full default);rewrite Heq //=.
  Qed.

  Lemma elems_NoDup : NoDup elems.
  Proof.
   rewrite /elems; apply NoDup_map_inj.
   move=> x y _ _ Heq;rewrite (powN_logN x) (powN_logN y) Heq //.
   apply FG.elems_NoDup.
  Qed.

  Parameter elems_size_nat :
   (size_nat (length elems) <= elems_poly k)%coq_nat.

  Lemma logN_tplus : forall  (x y : T k),
   tplus (logN x) (logN y) = logN (x * y)%g.
  Proof.
   move=> x y.
   rewrite -(logN_powN  (tplus _ _)) -mul_powN  -!powN_logN //.
  Qed.

  Lemma tinv_tplus : forall (z1 z2 : t),
   tinv (tplus z1 z2) = tplus (tinv z1) (tinv z2).
  Proof.
   move=>  z1 z2;rewrite -(logN_powN (tinv (tplus z1 z2))).
   rewrite -inv_powN -mul_powN invMg mulg_comm !inv_powN mul_powN logN_powN //.
  Qed.
  
  Lemma tplus_assoc : forall (z1 z2 z3 : t),
   tplus z1 (tplus z2 z3) = tplus (tplus z1 z2) z3.
  Proof.
   move=> z1 z2 z3;rewrite -(logN_powN (tplus _ _)) -!mul_powN mulgA !mul_powN logN_powN //.
  Qed.

  Lemma tplus_tinv_tid : forall (z : t),
   tplus z (tinv z) = tid.
  Proof.
   move=> z; rewrite -(logN_powN (tplus _ _)) -mul_powN -inv_powN mulg_comm left_inv //.
  Qed. 

  Lemma tplus_tid : forall (z : t),
   tplus tid z = z.
  Proof.
   move=> z.
   by rewrite -(logN_powN (tplus _ _)) -mul_powN -powN_1  mul1g logN_powN.
  Qed.

 End DEF.

End CFG_TO_LOG. 


Module Type PADDING_ALGEBRA (A:FINITE_TYPE) (B:FINITE_TYPE).

 (** Operations *)
 Parameter pad     : forall k, A.t k -> B.t k -> B.t k.
 Parameter unpad   : forall k, A.t k -> B.t k -> B.t k.
 Parameter pad_inv : forall k, B.t k -> B.t k -> A.t k.

 (* Needed to prove [SamplingFact1] *) 
 Parameter pad_padinv : forall k p r, 
  In p (A.elems k) -> pad_inv (pad p r) r = p. 

 Parameter P_R_iso_pad : forall k x,
  PermutP (fun p r => r = pad p x) (A.elems k) (B.elems k).

 (* Needed to prove [SamplingFact2] *) 
 Parameter unpad_padinv : forall k p r, 
  In p (A.elems k) -> pad_inv r (unpad p r) = p.
 
 Parameter P_R_iso_unpad : forall k x,
  PermutP (fun p r => r = unpad p x) (A.elems k) (B.elems k).

 (* Needed to prove [I_F] is an inverter for [F] *)
 Parameter padinv_unpad : forall k (r s:B.t k), unpad (pad_inv s r) s = r. 

 (** Complexity specification *) 
 Parameter cost_pad    : forall k, A.t k -> B.t k -> nat.
 Parameter cost_unpad  : forall k, A.t k -> B.t k -> nat.
 Parameter cost_padinv : forall k, B.t k -> B.t k -> nat.

 Parameter cost_pad_poly : polynomial.

 Parameter cost_pad_poly_spec : forall k p r,
  (@cost_pad k p r <= cost_pad_poly k)%coq_nat.

End PADDING_ALGEBRA.

Module Padding (FG:CFG).

 Module A := CFG_TO_LOG FG.
 Module B := CFG_TO_FT FG.

 Definition pad k (p : A.t k) (r : B.t k) : B.t k :=
  (r * (A.powN (A.tinv p)))%g.
   
 Definition unpad k (p : A.t k) (r : B.t k) : B.t k :=
  (r * (A.powN p))%g.

 Definition pad_inv k (r1 r2 : B.t k) := 
  A.tinv (A.logN k (r2^-1 * r1)%g ).

 (* Needed to prove [SamplingFact1] *)
 Lemma pad_padinv : forall k (p : A.t k) r, 
  In p (A.elems k) -> pad_inv k (pad p r) r = p. 
 Proof.
  rewrite /pad_inv /pad => k p r _.
  rewrite mulgA (@mulVg (A.GFinGroupType k)) mul1g A.logN_powN .
  rewrite - (A.logN_powN (A.tinv _)) -!A.inv_powN invgK A.logN_powN //.
 Qed.
 
 Lemma P_R_iso_pad : forall k x,
  PermutP (fun p r => r = pad p x) (A.elems k) (B.elems k).
 Proof.
  move=> k x.
  rewrite /A.elems /B.elems.
  apply PermutP_sym.
  rewrite <- PermutP_map.
  unfold pad.
  apply PermutP_NoDup with (f_inv := fun r => unpad (A.logN k (r^-1)%g) x).
  apply B.elems_NoDup.
  apply B.elems_NoDup.

  rewrite /unpad => y Hy.
  rewrite /A.tinv -!A.powN_logN invMg invgK (FG.mulg_comm k y) mulgA (@mulgV (A.GFinGroupType k)) mul1g //.

  rewrite /unpad => y Hy.
  rewrite -A.powN_logN invMg (FG.mulg_comm _ _ (x^-1)%g).

  rewrite mulgA (@mulgV (A.GFinGroupType k)) mul1g -A.inv_powN invgK -A.powN_logN //.
  
  move=> a _;apply FG.elems_full.  
  move=> a _;apply FG.elems_full.
 Qed.
 
 (* Needed to prove [SamplingFact2] *) 
 Lemma unpad_padinv : forall k (p : A.t k) r, 
  In p (A.elems k) -> pad_inv k r (unpad p r) = p.
 Proof.
  move=> k p r _;rewrite /pad_inv /unpad /A.tinv -A.powN_logN.
  rewrite invMg invgK mulgA (FG.mulg_comm k _ r) (@mulgV (A.GFinGroupType k)) mul1g A.logN_powN //.
 Qed.
 
 Lemma P_R_iso_unpad : forall k x,
  PermutP (fun p r => r = unpad p x) (A.elems k) (B.elems k).
 Proof.
  move=> k x.
  rewrite /A.elems /B.elems.
  apply PermutP_sym.
  rewrite <- PermutP_map.
  unfold unpad.
  apply PermutP_NoDup with (f_inv := fun r => pad (A.logN k (r^-1)%g) (x^-1)%g).
  apply B.elems_NoDup.
  apply B.elems_NoDup.

  rewrite /pad => y Hy.
  rewrite /A.tinv -!A.powN_logN invgK mulgA (@mulgV (A.GFinGroupType k)) mul1g //.

  rewrite /pad => y Hy.
  rewrite /A.tinv -!A.powN_logN invgK mulgA  (FG.mulg_comm _ (x^-1)%g) (@mulgV (A.GFinGroupType k)) mul1g//.

  move=> a _;apply FG.elems_full.  
  move=> a _;apply FG.elems_full.
 Qed.

 (* Needed to prove [I_F] is an inverter for [F] *)
 Lemma padinv_unpad : forall k (r s: B.t k), unpad (pad_inv k s r) s = r. 
 Proof.
  rewrite /unpad /pad_inv /A.tinv=> k r s.
  rewrite -!A.powN_logN invMg mulgA (@mulgV (A.GFinGroupType k)) invgK mul1g//.
 Qed.

 Parameter cost_pad    : forall k, A.t k -> B.t k -> nat.
 Parameter cost_unpad  : forall k, A.t k -> B.t k -> nat.
 Parameter cost_padinv : forall k, B.t k -> B.t k -> nat.

 Parameter cost_pad_poly : polynomial.

 Parameter cost_pad_poly_spec : forall k p r,
  (@cost_pad k p r <= cost_pad_poly k)%coq_nat.
 
End Padding.


Module Type ENCODING (A:FINITE_TYPE) (B:FINITE_TYPE).

 Section SPEC.
 
  Variable k : nat.

  Parameter f_def : A.t k -> B.t k.

  Parameter finv_def : B.t k -> list (A.t k).
   
  Parameter finv_len : nat.

  Parameter cost_f : A.t k -> nat.

  Parameter cost_f_poly : polynomial.

  Parameter cost_f_poly_spec : forall x, (cost_f x <= cost_f_poly k)%coq_nat.

  Parameter cost_finv : B.t k -> nat.

  Parameter cost_finv_poly : polynomial.

  Parameter cost_finv_poly_spec : forall x, (cost_finv x <= cost_finv_poly k)%coq_nat.
  
  Parameter finv_len_poly : polynomial.

  Parameter finv_len_poly_spec : (finv_len <= finv_len_poly k)%coq_nat.

  Parameter finv_len_spec : forall x, (length (finv_def x) <= finv_len)%coq_nat.

  Parameter finv_len_not_0 : (0 < finv_len)%coq_nat.

 End SPEC.

End ENCODING.
