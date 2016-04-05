Set Implicit Arguments.

Require Import ZArith.

  
Section TREE.

 Variables (A:Type) (default : A) (eq_def : A -> bool).
 Hypothesis eq_def_spec : forall a, if eq_def a then a = default else a <> default.

 Inductive tree : Type :=
  | Node : A -> tree -> tree -> tree
  | Empty : tree.

 Definition mkNode a l r :=
   if eq_def a then
     match l, r with
     | Empty, Empty => Empty
     | _, _ => Node a l r
     end
   else Node a l r.
  
 Fixpoint get (t:tree) (k:positive) {struct t} : A :=
  match t with
  | Empty => default
  | Node a tl tr =>
    match k with
    | xH => a
    | xO k => get tl k
    | xI k => get tr k
    end
  end.

    Fixpoint upd (t:tree) (k:positive) (f:A -> A) {struct k} : tree :=
    match k, t with
    | xH, Empty => mkNode (f default) Empty Empty
    | xH, Node a tl tr => mkNode (f a) tl tr
    | xO k, Empty => mkNode default (upd Empty k f) Empty
    | xO k, Node a tl tr => mkNode a (upd tl k f) tr
    | xI k, Empty => mkNode default Empty (upd Empty k f)
    | xI k, Node a tl tr => mkNode a tl (upd tr k f)
    end.

  Lemma get_mkNode : forall k a l r, get (mkNode a l r) k = get (Node a l r) k.
  Proof.
    unfold mkNode; intros.
    generalize (eq_def_spec a); destruct (eq_def a); intros; subst; trivial.
    destruct l; trivial.
    destruct r; trivial.
    destruct k; trivial.
  Qed.

  Lemma get_upd_Empty_diff : forall k1 k2 f, k1 <> k2 -> get (upd Empty k1 f) k2 = default.
  Proof.
   induction k1; destruct k2; intros; simpl; repeat rewrite get_mkNode; simpl; trivial;
   try (apply IHk1; intro; subst; auto; fail).
   elim H; trivial. 
  Qed.

  Lemma get_upd_Empty_same : forall k f, get (upd Empty k f) k = f default.
  Proof.
    induction k; intros; simpl; repeat rewrite get_mkNode; simpl; trivial.
  Qed.

  Hint Resolve get_upd_Empty_diff get_upd_Empty_same.

  Lemma get_upd_same : forall t k f, get (upd t k f) k = f (get t k).
  Proof.
   intros t k; generalize k t; clear k t.
   induction k; destruct t; simpl; intros; repeat rewrite get_mkNode; simpl; auto.
  Qed.

    
  Lemma get_upd_diff : forall t k1 k2 f, k1 <> k2 -> get (upd t k1 f) k2 = get t k2.
  Proof.
    intros t k1; generalize k1 t; clear k1 t.
    induction k1; destruct t; destruct k2; simpl; intros f H; repeat rewrite get_mkNode; simpl; auto;
    (apply IHk1; intro; subst; auto; fail) || 
    (apply get_upd_Empty_diff; intro; subst; auto; fail) ||
    (try (elim H; trivial; fail)).
  Qed.

  Variable (Aeqb : A -> A -> bool).

  Fixpoint is_Empty t : bool :=
   match t with
   | Empty => true
   | Node a tl tr => 
     if Aeqb a default then if is_Empty tl then is_Empty tr else false
     else false
   end.
 
  Hypothesis Aeqb_def : Aeqb default default = true.
  Hypothesis Aeqb_def_comm : forall a, Aeqb a default = Aeqb default a.

  Lemma is_Empty_spec : forall t, is_Empty t = true <-> forall x, Aeqb (get t x) default = true.
  Proof.
    induction t; simpl; trivial.
    case_eq (Aeqb a default); intros.
    destruct (is_Empty t1).
    rewrite IHt2; split; intros.
    destruct IHt1; destruct x; auto.
    apply (H0 (xI x)).
    split; intros; try discriminate.
    rewrite IHt1; intros x; apply (H0 (xO x)).
    split; intros; try discriminate.
    rewrite <- (H0 xH); symmetry; apply H.
    split; auto.
   Qed.

  Fixpoint eqb (x y : tree) {struct x} : bool :=
    match x, y with
    | Empty, _ => is_Empty y
    | _, Empty => is_Empty x
    | Node a1 xl xr, Node a2 yl yr =>
      if Aeqb a1 a2 then
       if eqb xl yl then eqb xr yr else false
      else false
    end.

  Lemma eqb_get : forall x y, 
     eqb x y = true <-> forall k, Aeqb (get x k) (get y k)  = true.
  Proof.
   induction x; intros y.
   destruct y; simpl.
   case_eq (Aeqb a a0); intro; try (intros; discriminate).
   case_eq (eqb x1 y1); intro; try (intros; discriminate).
   split; intros.
   destruct k; auto.
   rewrite IHx2 in H1; auto.
   rewrite IHx1 in H0; auto.
   rewrite IHx2; intros k; apply (H1 (xI k)).
   split; intros; try discriminate.
   assert (eqb x1 y1 = true).
      rewrite IHx1; intros k; apply (H1 (xO k)).
   rewrite <- H0; trivial.
   split; intros; try discriminate.
   rewrite <- H; apply (H0 xH).
   change ( is_Empty (Node a x1 x2) = true <-> forall k, Aeqb (get (Node a x1 x2) k) default = true).
   apply is_Empty_spec.
   change (is_Empty y = true <-> forall k, Aeqb default (get y k) = true).
   rewrite is_Empty_spec.
   split; intros H k; rewrite <- (H k); auto.
  Qed.
     
  Variable Aeq : A -> A -> Prop.

  Hypothesis Aeq_refl : forall x, Aeq x x.
  Hypothesis Aeq_trans : forall x y z, Aeq x y -> Aeq y z -> Aeq x z.
  Hypothesis Aeq_sym : forall x y, Aeq x y -> Aeq y x.
  Hypothesis Aeqb_spec : forall x y, if Aeqb x y then Aeq x y else ~Aeq x y.

  Definition eq (x y:tree) := forall k, Aeq (get x k) (get y k).
  
  Lemma eq_refl : forall x, eq x x.
  Proof. unfold eq; intros; apply Aeq_refl. Qed.

  Lemma eq_sym : forall x y, eq x y -> eq y x.
  Proof. unfold eq; intros; apply Aeq_sym; trivial. Qed.

  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof. unfold eq; intros; eapply Aeq_trans; eauto. Qed.

  Lemma eqb_spec : forall x y, if eqb x y then eq x y else ~eq x y.
  Proof.
   intros x y; generalize (eqb_get x y).
   destruct (eqb x y).
   unfold eq; intros.
   assert (W:=Aeqb_spec (get x k) (get y k)).
   destruct H as (H,_); rewrite H in W; trivial.
   intros; intro; assert (false = true).
     rewrite H; intros k; assert (W:= H0 k).
     assert (W1:=Aeqb_spec (get x k) (get y k)).
     destruct (Aeqb (get x k) (get y k)); trivial.
     elim (W1 W).
   discriminate.
  Qed.

  Fixpoint app_pos (x y:positive) {struct x} : positive :=
    match x with
    | xH => y
    | xO x => app_pos x (xO y)
    | xI x => app_pos x (xI y)
    end.

  Variable f : positive -> A -> bool.

  Fixpoint forallb_i_rec (p:positive) (t:tree) {struct t} : bool :=
    match t with
    | Empty => true
    | Node a l r =>
      if f (app_pos p xH) a then 
       if forallb_i_rec (xO p) l then forallb_i_rec (xI p) r else false
      else false
    end.

  Hypothesis f_def : forall k, f k default = true.

  Lemma forallb_i_rec_spec : 
     forall t p, forallb_i_rec p t = true <-> forall k, f (app_pos p k) (get t k) = true.
  Proof.
   induction t; simpl; intros.
   case_eq ( f (app_pos p 1) a); intros.
    case_eq (forallb_i_rec (xO p) t1); intros.   
    rewrite IHt2.
    split; intros.
    destruct k; auto.
    apply (H1 k).
    destruct (IHt1 (xO p)) as (H3,_); exact (H3 H0 k). 
    exact (H1 (xI k)).
    split; intros; try discriminate.
    rewrite <- H0; rewrite (IHt1 (xO p)).
    intros k; exact (H1 (xO k)).
    split; intros; try discriminate.
    rewrite <- H; exact (H0 xH).
    split; trivial.
   Qed.

   Definition forallb_i := forallb_i_rec xH.
    
   Lemma forallb_i_spec : 
     forall t, forallb_i t = true <-> forall k, f k (get t k) = true.
   Proof.
    unfold forallb_i; intros; rewrite forallb_i_rec_spec; simpl; tauto.
   Qed.

End TREE.

Section Map.

    Variables (A B:Type) (defA:A) (defB:B) (Beq_def : B -> bool) (f : A -> B) .

    Fixpoint map (t:tree A) : tree B:=
      match t with 
      | Empty => Empty _
      | Node o tl tr => mkNode Beq_def (f o) (map tl) (map tr)
      end.
    Hypothesis Beq_def_spec : forall a, if Beq_def a then a = defB else a <> defB.
    Hypothesis f_def : f defA = defB.
    Lemma map_spec : forall t k, get defB (map t) k = f (get defA t k).
    Proof.
     induction t; simpl; intros; trivial; destruct k; repeat rewrite get_mkNode; simpl; auto.
    Qed.

End Map.

Section Filter.

    Variables (A:Type) (defA:A) (eq_def : A -> bool)(f : A -> bool).
    Definition filter_a a := if f a then a else defA.

    Definition filter := map eq_def filter_a.
    Hypothesis Aeq_def_spec : forall a, if eq_def a then a = defA else a <> defA.
    Hypothesis f_def : f defA = true.

    Lemma filter_spec : forall t k, f (get defA (filter t) k) = true.
    Proof.
      unfold filter; intros.
      rewrite (@map_spec A A defA defA eq_def filter_a Aeq_def_spec); unfold filter_a.
      case_eq (f (get defA t k)); trivial.
      rewrite f_def; trivial.
    Qed.

End Filter.

Section Map2.

  Variables (A B C : Type) (dA:A) (dB:B) (dC:C) (Ceq_def:C -> bool) (f : A -> B -> C).
  
  Fixpoint map2 (ta:tree A) (tb:tree B) {struct ta} : tree C :=
    match ta with
    | Empty => map Ceq_def (f dA) tb
    | Node a tal tar =>
      match tb with
      | Empty =>map Ceq_def (fun a => f a dB) ta
      | Node b tbl tbr => mkNode Ceq_def (f a b) (map2 tal tbl) (map2 tar tbr)
      end
     end.

  Hypothesis Aeq_def_spec : forall a, if Ceq_def a then a = dC else a <> dC.

  Hypothesis f_def : dC = f dA dB.

  Lemma map2_spec : forall ta tb k, get dC (map2 ta tb) k = f (get dA ta k) (get dB tb k).
  Proof.
    induction ta; destruct tb; intros; unfold map2; fold map2; repeat rewrite get_mkNode; simpl; auto;
    destruct k; simpl; auto; rewrite get_mkNode; auto; simpl.
    rewrite (@map_spec A C dA dC Ceq_def); auto.
    rewrite (@map_spec A C dA dC Ceq_def); auto.
    rewrite (@map_spec B C dB dC Ceq_def); auto.
    rewrite (@map_spec B C dB dC Ceq_def); auto.
  Qed.

End Map2.

(*
Section OPTION.
  Variable A:Type.
  Variable (Aeqb : A -> A -> bool).
  Variable Aeq : A -> A -> Prop.

  Hypothesis Aeq_refl : forall x, Aeq x x.
  Hypothesis Aeq_trans : forall x y z, Aeq x y -> Aeq y z -> Aeq x z.
  Hypothesis Aeq_sym : forall x y, Aeq x y -> Aeq y x.
  Hypothesis Aeqb_spec : forall x y, if Aeqb x y then Aeq x y else ~Aeq x y.

  Definition oeq (x y:option A) := 
    match x, y with
    | Some a1, Some a2 => Aeq a1 a2
    | None, None => True
    | _, _ => False
    end. 
  
  Lemma oeq_refl : forall x, oeq x x.
  Proof. destruct x; simpl; auto. Qed.

  Lemma oeq_sym : forall x y, oeq x y -> oeq y x.
  Proof. destruct x; destruct y; simpl; auto. Qed.

  Lemma oeq_trans : forall x y z, oeq x y -> oeq y z -> oeq x z.
  Proof.
   destruct x; destruct y; destruct z; simpl; eauto.
   intros H; elim H.
  Qed.

  Definition oeqb (x y:option A) := 
    match x, y with
    | Some a1, Some a2 => Aeqb a1 a2
    | None, None => true
    | _, _ => false
    end. 

  Lemma oeqb_spec : forall x y, if oeqb x y then oeq x y else ~oeq x y.
  Proof.
   destruct x; destruct y; auto; simpl; auto.
   apply Aeqb_spec.
  Qed.

  Variable (M:Type->Type) (K:Type) (get : M A -> K -> option A).

  Definition eq (x y:M A) := forall k, oeq (get x k) (get y k).
  
  Lemma eq_refl : forall x, eq x x.
  Proof. unfold eq; intros; apply oeq_refl. Qed.

  Lemma eq_sym : forall x y, eq x y -> eq y x.
  Proof. unfold eq; intros; apply oeq_sym; trivial. Qed.

  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof. unfold eq; intros; eapply oeq_trans; eauto. Qed.

  Variables (B:Type) (f : A -> option B).

  Definition f_opt o :=
     match o with
     | Some a => f a
     | None => None
     end.

End OPTION.

Module Type MAP.
 
  Parameter key : Type.
  Parameter t : Type -> Type.

  Parameter get : forall A, t A -> key -> option A.
  Parameter upd : forall A, t A -> key -> option A -> t A.
  Parameter get_upd_same : forall A (m:t A) k a, get (upd m k a) k = a.
  Parameter get_upd_diff : forall A (m:t A) k1 k2 a, k1 <> k2 -> get (upd m k1 a) k2 = get m k2.

  Parameter empty : forall A, t A.
  Parameter empty_spec : forall A k, get (empty A) k = None.

  Parameter eqb : forall A, (A->A->bool) -> t A -> t A -> bool.

  Parameter eqb_get : forall A (Aeqb:A->A->bool) (x y:t A), 
     eqb Aeqb x y = true <-> forall k, oeqb Aeqb (get x k) (get y k)  = true.

  Definition eq A (Aeq:A->A->Prop) (x y:t A) := forall k, oeq Aeq (get x k) (get y k).
  
  Parameter eqb_spec : forall A (Aeqb : A -> A -> bool) (Aeq : A -> A -> Prop),
    (forall x y, if Aeqb x y then Aeq x y else ~Aeq x y) ->
    forall (x y:t A), if eqb Aeqb x y then eq Aeq x y else ~eq Aeq x y.

  Parameter forallb_i : forall A, (key -> A -> bool) -> t A -> bool.
    
  Parameter forallb_i_spec : 
     forall A f (m:t A), forallb_i f m = true <-> forall k a, get m k = Some a -> f k a = true.
  
  Parameter map : forall A B, (A -> option B) -> t A -> t B.

  Parameter map_spec : forall A B (f:A->option B) (m:t A) k, get (map f m) k = f_opt f (get m k).

  Parameter map2 : forall A B C, (option A -> option B -> option C) -> t A -> t B -> t C.
  
  Parameter map2_spec : forall A B C (f:option A -> option B -> option C),
        None = f None None ->
        forall ma mb k, get (map2 f ma mb) k = f (get ma k) (get mb k).

End MAP.

Module Pmap <: MAP with Definition key := positive.

  Definition key : Type := positive.

  Section TREE.

   Variable A:Type.

   Inductive tree : Type :=
    | Node : option A -> tree -> tree -> tree
    | Empty : tree.

   Fixpoint get (t:tree) (k:positive) {struct t} : option A :=
    match t with
    | Empty => None
    | Node a tl tr =>
       match k with
      | xH => a
      | xO k => get tl k
      | xI k => get tr k
      end
    end.

  Fixpoint upd (t:tree) (k:positive) (a:option A) {struct k} : tree :=
    match k, t with
    | xH, Empty => Node a Empty Empty
    | xH, Node _ tl tr => Node a tl tr
    | xO k, Empty => Node None (upd Empty k a) Empty
    | xO k, Node o tl tr => Node o (upd tl k a) tr
    | xI k, Empty => Node None Empty (upd Empty k a)
    | xI k, Node o tl tr => Node o tl (upd tr k a)
    end.

  Lemma get_upd_same : forall t k a, get (upd t k a) k = a.
  Proof.
   intros t k; generalize k t; clear k t.
   induction k; destruct t; simpl; auto.
  Qed.

  Lemma get_upd_Empty : forall k1 k2 a, k1 <> k2 -> get (upd Empty k1 a) k2 = None.
  Proof.
   induction k1; destruct k2; intros; simpl; trivial;
   try (apply IHk1; intro; subst; auto; fail).
   elim H; trivial. 
  Qed.
   
  Lemma get_upd_diff : forall t k1 k2 a, k1 <> k2 -> get (upd t k1 a) k2 = get t k2.
  Proof.
    intros t k1; generalize k1 t; clear k1 t.
    induction k1; destruct t; destruct k2; simpl; intros a H; auto;
    (apply IHk1; intro; subst; auto; fail) || 
    (apply get_upd_Empty; intro; subst; auto; fail) ||
    (elim H; trivial).
  Qed.

  Definition mkNode o t1 t2 :=
    match o, t1, t2 with
    | None, Empty, Empty => Empty
    | _, _, _ => Node o t1 t2
    end.

  Lemma mkNode_spec : forall o t1 t2 k, get (mkNode o t1 t2) k = get (Node o t1 t2) k.
  Proof.
   intros; destruct o; trivial; destruct t1; trivial; destruct t2; trivial.
   destruct k; trivial.
  Qed.

  Definition empty := Empty.

  Lemma empty_spec : forall k, get empty k = None.
  Proof. trivial. Qed.

  Variable (Aeqb : A -> A -> bool).

  Fixpoint is_Empty t : bool :=
   match t with
   | Empty => true
   | Node (Some _) _ _ => false
   | Node _ tl tr => if is_Empty tl then is_Empty tr else false
   end.

  Lemma is_Empty_spec : forall t, is_Empty t = true <-> forall x, get t x = None.
  Proof.
    induction t; simpl; trivial.
    destruct o; intros.
    split.
    intros; discriminate.
    intros H; assert (H1:= H xH); discriminate.
    destruct (is_Empty t1).
    rewrite IHt2; split; intros.
    destruct IHt1; destruct x; auto.
    apply (H  (xI x)).
    split; intros; try discriminate.
    rewrite IHt1; intros x; exact (H (xO x)).
    split; trivial.
  Qed.

  Fixpoint eqb (x y : tree) {struct x} : bool :=
    match x, y with
    | Empty, _ => is_Empty y
    | _, Empty => is_Empty x
    | Node a1 xl xr, Node a2 yl yr =>
      if oeqb Aeqb a1 a2 then
       if eqb xl yl then eqb xr yr else false
      else false
    end.

  Lemma eqb_get : forall x y, 
     eqb x y = true <-> forall k, oeqb Aeqb (get x k) (get y k)  = true.
  Proof.
   induction x; intros y.
   destruct y; simpl.
   case_eq (oeqb Aeqb o o0); intro; try (intros; discriminate).
   case_eq (eqb x1 y1); intro; try (intros; discriminate).
   split; intros.
   destruct k; auto.
   rewrite IHx2 in H1; auto.
   rewrite IHx1 in H0; auto.
   rewrite IHx2; intros k; apply (H1 (xI k)).
   split; intros; try discriminate.
   assert (eqb x1 y1 = true).
      rewrite IHx1; intros k; apply (H1 (xO k)).
   rewrite <- H0; trivial.
   split; intros; try discriminate.
   rewrite <- H; apply (H0 xH).
   change (is_Empty (Node o x1 x2) = true <-> forall k, oeqb Aeqb (get (Node o x1 x2) k) None = true).
   rewrite is_Empty_spec; split; intros.
   rewrite H; trivial.
   assert (H1 := H x); destruct (get (Node o x1 x2) x); trivial; discriminate.
   change (eqb Empty y) with (is_Empty y).
   rewrite is_Empty_spec; split; intros.
   rewrite H; trivial.
   assert (H1 := H x); destruct (get y x); trivial; discriminate.
  Qed.
     
  Variable Aeq : A -> A -> Prop.

  Hypothesis Aeqb_spec : forall x y, if Aeqb x y then Aeq x y else ~Aeq x y.

  Definition eq (x y:tree) := forall k, oeq Aeq (get x k) (get y k).
  
  Lemma eqb_spec : forall x y, if eqb x y then eq x y else ~eq x y.
  Proof.
   intros x y; generalize (eqb_get x y).
   destruct (eqb x y).
   unfold eq; intros.
   assert (W:=oeqb_spec Aeqb Aeq Aeqb_spec (get x k) (get y k)).
   destruct H as (H,_); rewrite H in W; trivial.
   intros; intro; assert (false = true).
     rewrite H; intros k; assert (W:= H0 k).
     assert (W1:=oeqb_spec Aeqb Aeq Aeqb_spec (get x k) (get y k)).
     destruct (oeqb Aeqb (get x k) (get y k)); trivial.
     elim (W1 W).
   discriminate.
  Qed.

  Fixpoint app_pos (x y:positive) {struct x} : positive :=
    match x with
    | xH => y
    | xO x => app_pos x (xO y)
    | xI x => app_pos x (xI y)
    end.

  Variable f : positive -> A -> bool.

  Fixpoint forallb_i_rec (p:positive) (t:tree) {struct t} : bool :=
    match t with
    | Empty => true
    | Node o l r =>
      let test := 
        match o with
        | Some a => f (app_pos p xH) a
        | None => true
        end in
      if test then 
       if forallb_i_rec (xO p) l then forallb_i_rec (xI p) r else false
      else false
    end.

  Lemma forallb_i_rec_spec : 
     forall t p, forallb_i_rec p t = true <-> forall k e, get t k = Some e -> f (app_pos p k) e = true.
  Proof.
   induction t; simpl; intros.
   case_eq (match o with
    | Some a => f (app_pos p 1) a
    | None => true
    end); intros.
    case_eq (forallb_i_rec (xO p) t1); intros.   
    rewrite IHt2.
    split; intros.
    destruct k.
    simpl in H1; auto. 
    destruct (IHt1 (xO p)) as (H3,_); exact (H3 H0 _ _ H2). 
    rewrite H2 in H; trivial.    
    exact (H1 (xI k) _ H2).
    split; intros; try discriminate.
    rewrite <- H0; rewrite (IHt1 (xO p)).
    intros k e Heq; exact (H1 (xO k) _ Heq).
    split; intros; try discriminate.
    destruct o; try discriminate.
    rewrite <- H; exact (H0 xH a (refl_equal _)).
    split; trivial; intros; discriminate.
   Qed.

   Definition forallb_i := forallb_i_rec xH.
    
   Lemma forallb_i_spec : 
     forall t, forallb_i t = true <-> forall k e, get t k = Some e -> f k e = true.
   Proof.
    unfold forallb_i; intros; rewrite forallb_i_rec_spec; simpl; tauto.
   Qed.

  End TREE.
  
  Section Map.

    Variables (A B:Type) (f : A -> option B).

    Fixpoint map (t:tree A) : tree B:=
      match t with 
      | Empty => Empty _
      | Node o tl tr => mkNode (f_opt f o) (map tl) (map tr)
      end.

    Lemma map_spec : forall t k, get (map t) k = f_opt f (get t k).
    Proof.
     induction t; simpl; intros; trivial; destruct k; rewrite mkNode_spec; simpl; auto.
    Qed.

  End Map.

  Section Map2.

   Variables (A B C : Type) (f : option A -> option B -> option C).
  
  Fixpoint map2 (ta:tree A) (tb:tree B) {struct ta} : tree C :=
    match ta with
    | Empty => map (fun b => f None (Some b)) tb
    | Node oa tal tar =>
      match tb with
      | Empty =>
         mkNode (f oa None)
                       (map (fun a => f (Some a) None) tal) 
                       (map (fun a => f (Some a) None) tar)
      | Node ob tbl tbr => 
        mkNode (f oa ob) (map2 tal tbl) (map2 tar tbr)
      end
     end.

  Hypothesis f_None : None = f None None.

  Lemma map2_spec : forall ta tb k, get (map2 ta tb) k = f (get ta k) (get tb k).
  Proof.
    induction ta; destruct tb; intros; unfold map2; fold map2; try rewrite mkNode_spec; simpl; auto;
    destruct k; simpl; auto.
    rewrite map_spec; destruct (get ta2 k); simpl; auto.
    rewrite map_spec; destruct (get ta1 k); simpl; auto.
    rewrite mkNode_spec; simpl;
    rewrite map_spec; destruct (get tb2 k); simpl; auto.
    rewrite mkNode_spec; simpl; rewrite map_spec; destruct (get tb1 k); simpl; auto.
    rewrite mkNode_spec; simpl; destruct o; simpl; auto.
  Qed.

  End Map2.

 Definition t := tree.

End Pmap.

*)