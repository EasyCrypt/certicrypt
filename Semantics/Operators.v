(** * Operators.v : Operators used in pWHILE expressions *)

Set Implicit Arguments.

Require Export Types.


(** * User-defined operators *)
Module Type UOP (UT:UTYPE) (T:TYPE UT).
  
 Parameter t : Type.

 Parameter eqb : t -> t -> bool.

 Parameter eqb_spec :  forall x y, if eqb x y then x = y else x <> y.

 Parameter targs : t -> list T.type.

 Parameter tres : t -> T.type.

 Parameter interp_op : forall k op, T.type_op k (targs op) (tres op).

 Parameter cinterp_op : forall k op, T.ctype_op k (targs op) (tres op).

 Definition eval_op k
  (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) :=
  @T.app_op k (targs op) (tres op) (interp_op k op) args.

 Definition ceval_op k 
  (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) * nat :=
  @T.capp_op k (targs op) (tres op) (cinterp_op k op) args.

 Parameter ceval_op_spec : forall k op args,
  @eval_op k op args = fst (@ceval_op k op args).

 Implicit Arguments interp_op [k].  
 Implicit Arguments cinterp_op [k].

End UOP.

Module EmptyUop (UT:UTYPE) (T:TYPE UT) <: UOP UT T.

  Inductive t_ : Type :=.

  Definition t := t_.

  Definition eqb : t -> t -> bool := fun _ _ => true.
  
  Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
  Proof.
   destruct x.
  Qed.

  Definition targs (op : t) : list T.type :=  match op with end.

  Definition tres (op : t) : T.type :=  match op with end.

  Definition interp_op (k : nat) (op : t) : T.type_op k (targs op) (tres op) :=
    match op as op0 return T.type_op k (targs op0) (tres op0) with end.

  Implicit Arguments interp_op [k].

  Definition cinterp_op (k : nat) (op : t) : T.ctype_op k (targs op) (tres op) :=
    match op as op0 return T.ctype_op k (targs op0) (tres op0) with end.

  Implicit Arguments cinterp_op [k].

  Definition eval_op k
    (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) :=
    @T.app_op k (targs op) (tres op) (interp_op op) args.
  
  Definition ceval_op k
    (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) * nat :=
    @T.capp_op k (targs op) (tres op) (cinterp_op op) args.
  
  Lemma ceval_op_spec : forall k op args,
    @eval_op k op args = fst (@ceval_op k op args).
  Proof.
    intros k o args; destruct o.
  Qed.

End EmptyUop.


(** Operators *)
Module Type OP (UT:UTYPE) (T:TYPE UT) (Uop:UOP UT T).

 Inductive op : Type :=
 (* List operations *)
 | Olength : T.type -> op
 | OZlength : T.type -> op
 | Ohd : T.type -> op
 | Otl : T.type -> op
 | Ocons : T.type -> op
 | Oappend : T.type -> op
 | Omem : T.type -> op
 | Oupd : T.type -> T.type -> op
 | Oin_dom : T.type -> T.type -> op
 | Oin_range : T.type -> T.type -> op
 | Osplit : T.type -> T.type -> op
 | Oimg : T.type -> T.type -> op
 | Onth : T.type -> op
 (* Pair operations *)
 | Opair : T.type -> T.type -> op
 | Ofst : T.type -> T.type -> op
 | Osnd : T.type -> T.type -> op
 (* Sum type operations *)
 | Oinl : T.type -> T.type -> op
 | Oinr : T.type -> T.type -> op
 | Oisl : T.type -> T.type -> op
 | Oprojl : T.type -> T.type -> op
 | Oprojr : T.type -> T.type -> op
 (* Option type operators *)
 | Osome : T.type -> op
 | Oissome : T.type -> op
 | Oprojo : T.type -> op
 (* Equality *)
 | Oeq_ : T.type -> op
 (* Arithmetic operations (nat) *)
 | Oadd : op
 | Osub : op
 | Omul : op
 | Ole : op
 | Olt : op 
 (* Arithmetic operations (Z) *)
 | OZadd : op
 | OZsub : op
 | OZmul : op
 | OZle : op
 | OZlt : op
 | OZge : op
 | OZgt : op
 | OZopp : op
 | OZdiv : op
 | OZmod : op
 | OZpow : op
 (* Boolean operations *)
 | Onot : op
 | Oand : op
 | Oor : op 
 | Oimp : op
 | Oif : T.type -> op
 (* User operations *) 
 | Ouser : Uop.t -> op.
  
 Definition t : Type := op.

 Parameter eqb : op -> op -> bool.
 Parameter eqb_spec :  forall x y, if eqb x y then x = y else x <> y.

 (* Argument types for each operator *)
 Definition targs (o : op) : list T.type := 
  match o with
  | Olength t1 => T.List t1 :: nil
  | OZlength t1 => T.List t1 :: nil
  | Ohd t1 => T.List t1 :: nil
  | Otl t1 => T.List t1 :: nil
  | Ocons t1 => t1 :: T.List t1 :: nil
  | Oappend t1 => T.List t1 :: T.List t1 :: nil
  | Omem t1 => t1 :: T.List t1 :: nil
  | Oupd t1 t2 => t1 :: t2 :: T.List (T.Pair t1 t2) :: nil
  | Oin_dom t1 t2 => t1 :: T.List (T.Pair t1 t2) :: nil
  | Oin_range t1 t2 => t2 :: T.List (T.Pair t1 t2) :: nil
  | Oimg t1 t2 => t1 :: T.List (T.Pair t1 t2) :: nil
  | Osplit t1 t2 => t1 :: T.List (T.Pair t1 t2) :: nil
  | Onth t1 => T.Nat :: T.List t1 :: nil
  (* Pair operations *)
  | Opair t1 t2 => t1 :: t2 :: nil
  | Ofst t1 t2 => T.Pair t1 t2 :: nil
  | Osnd t1 t2 => T.Pair t1 t2 :: nil
  (* Sum type operations *)
  | Oinl t1 t2 => t1 :: nil
  | Oinr t1 t2 => t2 :: nil
  | Oisl t1 t2 => T.Sum t1 t2 :: nil
  | Oprojl t1 t2 => T.Sum t1 t2 :: nil
  | Oprojr t1 t2 => T.Sum t1 t2 :: nil
  (* Option type operators *)
  | Osome t => t :: nil
  | Oissome t => T.Option t :: nil
  | Oprojo t => T.Option t :: nil
  (* Equality *)
  | Oeq_ t1 => t1 :: t1 :: nil
  (* Arithmetic operations (nat) *)
  | Oadd => T.Nat :: T.Nat :: nil 
  | Osub => T.Nat :: T.Nat :: nil 
  | Omul => T.Nat :: T.Nat :: nil 
  | Ole => T.Nat :: T.Nat :: nil
  | Olt => T.Nat :: T.Nat :: nil  
  (* Arithmetic operations (Z) *)
  | OZadd => T.Zt :: T.Zt :: nil 
  | OZsub => T.Zt :: T.Zt :: nil 
  | OZmul => T.Zt :: T.Zt :: nil 
  | OZle => T.Zt :: T.Zt :: nil
  | OZlt => T.Zt :: T.Zt :: nil
  | OZge => T.Zt :: T.Zt :: nil
  | OZgt => T.Zt :: T.Zt :: nil
  | OZopp => T.Zt :: nil
  | OZdiv => T.Zt :: T.Zt :: nil
  | OZmod => T.Zt :: T.Zt :: nil
  | OZpow => T.Zt :: T.Zt :: nil
  (* Boolean operations *)
  | Onot => T.Bool :: nil
  | Oand => T.Bool :: T.Bool :: nil
  | Oor => T.Bool :: T.Bool :: nil
  | Oimp => T.Bool :: T.Bool :: nil
  | Oif t => T.Bool :: t :: t :: nil
  (* User operations *) 
  | Ouser uop => Uop.targs uop
  end.

 (* Result types for each operator *)
 Definition tres (o : op) : T.type :=
  match o with
  | Olength t1 => T.Nat
  | OZlength t1 => T.Zt
  | Ohd t1 => t1
  | Otl t1 => T.List t1
  | Ocons t1 => T.List t1
  | Oappend t1 => T.List t1
  | Omem t1 => T.Bool
  | Oupd t1 t2 => T.List (T.Pair t1 t2)
  | Oin_dom t1 t2 => T.Bool
  | Oin_range t1 t2 => T.Bool
  | Oimg t1 t2 => t2
  | Osplit t1 t2 => T.Pair (T.List (T.Pair t1 t2)) (T.Pair t2 (T.List (T.Pair t1 t2)))
  | Onth t1 => t1
  (* Pair operations *)
  | Opair t1 t2 => T.Pair t1 t2 
  | Ofst t1 t2 => t1
  | Osnd t1 t2 => t2
  (* Sum type operations *)
  | Oinl t1 t2 => T.Sum t1 t2
  | Oinr t1 t2 => T.Sum t1 t2
  | Oisl t1 t2 => T.Bool
  | Oprojl t1 t2 => t1
  | Oprojr t1 t2 => t2
  (* Option type operators *)
  | Osome t => T.Option t
  | Oissome t => T.Bool
  | Oprojo t => t
  (* Equality *)
  | Oeq_ t1 => T.Bool
  (* Arithmetic operations (nat) *)
  | Oadd => T.Nat
  | Osub => T.Nat
  | Omul => T.Nat
  | Ole => T.Bool
  | Olt => T.Bool 
  (* Arithmetic operations (Z) *)
  | OZadd => T.Zt
  | OZsub => T.Zt
  | OZmul => T.Zt
  | OZle => T.Bool
  | OZlt => T.Bool
  | OZge => T.Bool
  | OZgt => T.Bool
  | OZopp => T.Zt
  | OZdiv => T.Zt
  | OZmod => T.Zt
  | OZpow => T.Zt
  (* Boolean operations *)
  | Onot => T.Bool
  | Oand => T.Bool
  | Oor => T.Bool
  | Oimp => T.Bool
  | Oif t => t
  (* User operations *) 
  | Ouser uop => Uop.tres uop
  end. 


 Section EVAL.

  Variable k : nat.
  
  Definition assoc (A B:Type) (f:A -> bool) (b:B) (l:list (A*B)) :=
   match List.find (fun p => f (fst p)) l with
   | Some p => snd p
   | None => b
   end.

 Fixpoint upd (A B:Type) (f:A -> A -> bool) (a:A) (b:B) (l:list (A*B)) :=
   match l with
   | nil => (a,b)::nil
   | (a',b')::l =>
     if f a a' then (a',b)::l
     else (a',b')::upd f a b l
   end.

  Fixpoint cupd (A B:Type) (f:A -> A -> bool * nat) (a:A) (b:B) (l:list (A*B))  (n:nat) : list (A*B) * nat :=
   match l with
   | nil => ((a,b)::nil, S n)
   | (a',b')::l =>
     let (t,n0) := f a a' in
     if t then ((a',b)::l, S (n+n0)) 
     else 
       let (l', n1) := cupd f a b l (n+n0) in
       ((a',b')::l', S n1)
   end.

  Fixpoint split_assoc  (A B:Type) (f:A -> bool) (b:B) (l:list (A*B)) : list (A*B) * (B * list (A*B)):=
    match l with
    | nil => (nil, (b, nil))
    | hd::l =>
      if f (fst hd) then (nil, (snd hd, l))
      else 
       let r := split_assoc f b l in
       (hd::fst r, snd r)
   end.

  Fixpoint csplit_assoc  (A B:Type) (f:A -> bool * nat) (b:B) (l:list (A*B)) (n:nat) : (list (A*B) * (B * list (A*B))) * nat :=
    match l with
    | nil => ((nil, (b, nil)), S n)
    | hd::l =>
      let tn0 := f (fst hd) in
      let n0 := snd tn0 in
      if fst tn0 then ((nil, (snd hd, l)), S (n+n0))
      else 
       let rn1 := csplit_assoc f b l (n+n0) in
       ((hd::fst (fst rn1), snd (fst rn1)), S (snd rn1))
   end.

  Definition interp_op (o:op) : T.type_op k (targs o) (tres o) :=
   match o as op0 return T.type_op k (targs op0) (tres op0) with
   | Olength t1 => @List.length (T.interp k t1)
   | OZlength t1 => fun v => Z_of_nat (@List.length (T.interp k t1) v)
   | Ohd t1 => @List.hd (T.interp k t1) (T.default k t1)
   | Otl t1 => @List.tail (T.interp k t1)
   | Ocons t1 => @List.cons (T.interp k t1)
   | Oappend t1 => @List.app (T.interp k t1)
   | Omem t1 =>
     fun v => @List.existsb (T.interp k t1) (T.i_eqb k t1 v)
   | Oupd t1 t2 => 
     @upd (T.interp k t1) (T.interp k t2) (T.i_eqb k t1)
 
   | Oin_dom t1 t2 =>
     fun v => @List.existsb (T.interp k t1 * T.interp k t2)%type
     (fun p => T.i_eqb k t1 v (fst p))
   | Oin_range t1 t2 =>
     fun v => @List.existsb (T.interp k t1 * T.interp k t2)%type
      (fun p => T.i_eqb k t2 v (snd p))
   | Osplit t1 t2 =>
     fun v => @split_assoc (T.interp k t1) (T.interp k t2) (T.i_eqb k t1 v) (T.default k t2)
   | Oimg t1 t2 =>
     fun v => @assoc (T.interp k t1) (T.interp k t2) (T.i_eqb k t1 v) (T.default k t2)
   | Onth t1 => fun n l => @List.nth (T.interp k t1) n l (T.default k t1)
   (* Pair operations *)   
   | Opair t1 t2 => @pair (T.interp k t1) (T.interp k t2)
   | Ofst t1 t2 => @fst (T.interp k t1) (T.interp k t2)
   | Osnd t1 t2 => @snd (T.interp k t1) (T.interp k t2)
   (* Sum type operations *)
   | Oinl t1 t2 => @inl (T.interp k t1) (T.interp k t2)
   | Oinr t1 t2 => @inr (T.interp k t1) (T.interp k t2)
   | Oisl t1 t2 => fun s => if s then true else false
   | Oprojl t1 t2 => fun s => 
     match s with
     | inl x => x
     | _ => T.default k t1
     end 
   | Oprojr t1 t2 => fun s => 
     match s with
     | inr x => x
     | _ => T.default k t2
     end 
   (* Option type operators *)
   | Osome t => @Some (T.interp k t)
   | Oissome t => fun o => if o then true else false
   | Oprojo t => fun o =>
     match o with 
     | Some x => x
     | _ => T.default k t
     end   
   (* Equality *)
   | Oeq_ t1 => T.i_eqb k t1
   (* Arithmetic operations (nat) *)
   | Oadd => plus
   | Osub => minus
   | Omul => mult
   | Ole => Compare_dec.leb
   | Olt => fun n1 n2 => Compare_dec.leb (n1 + 1) n2
   (* Arithmetic operations (Z) *)
   | OZadd => Zplus
   | OZsub => Zminus
   | OZmul => Zmult   
   | OZle =>  Zle_bool
   | OZlt =>  Zlt_bool
   | OZge => Zge_bool
   | OZgt => Zgt_bool
   | OZopp => Zopp
   | OZdiv => Zdiv
   | OZmod => Zmod
   | OZpow => Zpower
   (* Boolean operations *)
   | Onot => negb
   | Oand => andb
   | Oor => orb
   | Oimp => impb
   | Oif t => fun b v1 v2 => if b then v1 else v2
   (* User operations *)
   | Ouser uop => @Uop.interp_op k uop
   end.

   Definition eq_cost k t (x y : T.interp k t) := (T.size k t x + T.size k t y)%nat.

   Definition cinterp_op (o:op) : T.ctype_op k (targs o) (tres o) :=
   match o as op0 return T.ctype_op k (targs op0) (tres op0) with
   | Olength t1 => fun l => let n:=List.length l in (n,n) 
   | OZlength t1 => fun l => let n:=List.length l in (Z_of_nat n,n) 
   | Ohd t1 => fun l => (List.hd (T.default k t1) l, S O)
   | Otl t1 => fun l => (List.tail l, S O)
   | Ocons t1 => fun a l => (List.cons a l, S O)
   | Oappend t1 => fun l1 l2 => (List.app l1 l2, List.length l1)
   | Omem t1 =>
     fun v l => cexistsb (fun v1 => (T.i_eqb k t1 v v1, eq_cost k _ v v1)) l 1%nat
   | Oupd t1 t2 =>
     fun a b l => cupd (fun v1 v2 => (T.i_eqb k t1 v1 v2, eq_cost k _ v1 v2)) a b l 1%nat 
   | Oin_dom t1 t2 =>
     fun v l => cexistsb (fun v1 => (T.i_eqb k t1 v (fst v1), eq_cost k _ v (fst v1))) l 1%nat
   | Oin_range t1 t2 =>
     fun v l => cexistsb (fun v1 => (T.i_eqb k t2 v (snd v1), eq_cost k _ v (snd v1))) l 1%nat
   | Osplit t1 t2 =>
     fun v l => 
        @csplit_assoc (T.interp k t1) (T.interp k t2) (fun v1 => (T.i_eqb k t1 v v1, eq_cost k _ v v1)) (T.default k t2) l 1%nat 
   | Oimg t1 t2 =>
     fun v l => 
     let (r, c) := 
      cfind_default (fun v1 => (T.i_eqb k t1 v (fst v1), eq_cost k _ v (fst v1))) l 1%nat (T.default k t1, T.default k t2) in
     (snd r, c)
   | Onth t1 =>
     fun n l => (@List.nth (T.interp k t1) n l (T.default k t1), List.length l)
   (* Pair operations *)
   | Opair t1 t2 => fun x y => (pair x y, S O)
   | Ofst t1 t2 => fun p => (fst p, S O)
   | Osnd t1 t2 => fun p => (snd p, S O)
   (* Sum type operations *)
   | Oinl t1 t2 => fun x => (inl _ x, S O) 
   | Oinr t1 t2 => fun x => (inr _ x, S O)
   | Oisl t1 t2 => fun s => (if s then true else false, S O)
   | Oprojl t1 t2 => fun s => 
     (match s with
     | inl x => x
     | _ => T.default k t1
     end, S O) 
   | Oprojr t1 t2 => fun s => 
     (match s with
     | inr x => x
     | _ => T.default k t2
     end, S O) 
   (* Option type operators *)
   | Osome t => fun x => (Some x, S O)
   | Oissome t => fun o => (if o then true else false, S O)
   | Oprojo t => fun o =>
     (match o with 
     | Some x => x
     | _ => T.default k t
     end, S O)
   (* Equality *)
   | Oeq_ t1 => fun x y => (T.i_eqb k _ x y, eq_cost k _ x y)%nat  
   (* Arithmetic operations (nat) *)
   | Oadd => fun x y => (plus x y, size_nat x)
   | Osub => fun x y => (minus x y, size_nat y)
   | Omul => fun x y => (mult x y, size_nat x * size_nat y)%nat
   | Ole => fun x y => (Compare_dec.leb x y, size_nat x)
   | Olt => fun x y => (Compare_dec.leb (x+1) y, size_nat y)  
   (* Arithmetic operations (Z) *)
   | OZadd => fun x y => (Zplus x y, size_Z x)
   | OZsub => fun x y => (Zminus x y, size_Z y)
   | OZmul => fun x y => (Zmult x y, size_Z x * size_Z y)%nat
   | OZle => fun x y => (Zle_bool x y, size_Z x)
   | OZlt => fun x y => (Zlt_bool x y, size_Z y)
   | OZge => fun x y => (Zge_bool x y, size_Z y)
   | OZgt => fun x y => (Zgt_bool x y, size_Z y)
   | OZopp => fun x => (Zopp x, size_Z x)
   | OZdiv => fun x y => (Zdiv x y, size_Z x)
   | OZmod => fun x y => (Zmod x y, size_Z y)
   | OZpow => fun x y => (Zpower x y, size_Z x)
   (* Boolean operations *)
   | Onot => fun b => (negb b, S O)
   | Oand => fun b1 b2 => (andb b1 b2, S O)
   | Oor => fun b1 b2 => (orb b1 b2, S O)
   | Oimp => fun b1 b2 => (impb b1 b2, S O)
   | Oif t => fun b v1 v2 => (if b then v1 else v2, S O)
   (* User operations *)
   | Ouser uop => @Uop.cinterp_op k uop
   end.

  Definition eval_op 
   (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) :=
   @T.app_op k (targs op) (tres op) (interp_op op) args.

  Definition ceval_op 
   (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) * nat :=
   @T.capp_op k (targs op) (tres op) (cinterp_op op) args.

 End EVAL.

 Implicit Arguments eval_op [k].
 Implicit Arguments ceval_op [k].

 Parameter ceval_op_spec : forall k op args,
  @eval_op k op args = fst (@ceval_op k op args).

 (* Dependant equality *) 
 Parameter eq_dep_eq : forall (P:op->Type) (p:op) (x y:P p), 
  eq_dep op P p x p y -> x = y.
 
 Parameter UIP_refl : forall (x:op) (p:x = x), p = refl_equal x.
 
 Parameter inj_pair2 : forall (P:op -> Type) (p:op) (x y:P p),
  existT P p x = existT P p y -> x = y.

End OP. 


Module MakeOp (UT:UTYPE) (T:TYPE UT) (Uop : UOP UT T) <: OP UT T Uop.


 Inductive op : Type :=
 (* List operations *)
 | Olength : T.type -> op
 | OZlength : T.type -> op
 | Ohd : T.type -> op
 | Otl : T.type -> op
 | Ocons : T.type -> op
 | Oappend : T.type -> op
 | Omem : T.type -> op
 | Oupd : T.type -> T.type -> op
 | Oin_dom : T.type -> T.type -> op
 | Oin_range : T.type -> T.type -> op
 | Osplit : T.type -> T.type -> op
 | Oimg : T.type -> T.type -> op
 | Onth : T.type -> op
 (* Pair operations *)
 | Opair : T.type -> T.type -> op
 | Ofst : T.type -> T.type -> op
 | Osnd : T.type -> T.type -> op
 (* Sum type operations *)
 | Oinl : T.type -> T.type -> op
 | Oinr : T.type -> T.type -> op
 | Oisl : T.type -> T.type -> op
 | Oprojl : T.type -> T.type -> op
 | Oprojr : T.type -> T.type -> op
 (* Option type operators *)
 | Osome : T.type -> op
 | Oissome : T.type -> op
 | Oprojo : T.type -> op
 (* Equality *)
 | Oeq_ : T.type -> op
 (* Arithmetic operations (nat) *)
 | Oadd : op
 | Osub : op
 | Omul : op
 | Ole : op
 | Olt : op 
 (* Arithmetic operations (Z) *)
 | OZadd : op
 | OZsub : op
 | OZmul : op 
 | OZle : op
 | OZlt : op
 | OZge : op
 | OZgt : op
 | OZopp : op
 | OZdiv : op
 | OZmod : op
 | OZpow : op
 (* Boolean operations *)
 | Onot : op
 | Oand : op
 | Oor : op 
 | Oimp : op
 | Oif : T.type -> op
 (* User operations *) 
 | Ouser : Uop.t -> op.
  
 Definition t : Type := op.
 
 Definition eqb (x y:op) : bool := 
  match x, y with
  | Olength t1, Olength t2 => T.eqb t1 t2
  | OZlength t1, OZlength t2 => T.eqb t1 t2
  | Ohd t1, Ohd t2 => T.eqb t1 t2
  | Otl t1, Otl t2 => T.eqb t1 t2
  | Ocons t1, Ocons t2 => T.eqb t1 t2
  | Oappend t1, Oappend t2 => T.eqb t1 t2
  | Omem t1, Omem t2 => T.eqb t1 t2
  | Oupd t11 t12, Oupd t21 t22 => 
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  | Oin_dom t11 t12, Oin_dom t21 t22 =>
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  | Oin_range t11 t12, Oin_range t21 t22 =>
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  | Osplit t11 t12, Osplit t21 t22 =>
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  | Oimg t11 t12, Oimg t21 t22 =>
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  | Onth t1, Onth t2 => T.eqb t1 t2
  (* Pair operations *)
  | Opair t11 t12, Opair t21 t22 =>
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  | Ofst t11 t12, Ofst t21 t22 =>
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  | Osnd t11 t12, Osnd t21 t22 =>
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  (* Sum type operations *)
  | Oinl t11 t12, Oinl t21 t22 => 
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  | Oinr t11 t12, Oinr t21 t22 => 
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  | Oisl t11 t12, Oisl t21 t22 => 
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  | Oprojl t11 t12, Oprojl t21 t22 => 
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  | Oprojr t11 t12, Oprojr t21 t22 => 
    if T.eqb t11 t21 then T.eqb t12 t22 else false
  (* Option type operators *)
  | Osome t1, Osome t2 => T.eqb t1 t2
  | Oissome t1, Oissome t2 => T.eqb t1 t2
  | Oprojo t1, Oprojo t2 => T.eqb t1 t2
  (* Equality *)
  | Oeq_ t1, Oeq_ t2 => T.eqb t1 t2
  (* Arithmetic operations (nat) *)
  | Oadd, Oadd => true
  | Osub, Osub => true
  | Omul, Omul => true
  | Ole, Ole => true
  | Olt, Olt => true  
  | OZge, OZge => true  
  | OZgt, OZgt => true  
  | OZopp, OZopp => true  
  | OZdiv, OZdiv => true  
  | OZmod, OZmod => true  
  | OZpow, OZpow => true  
 (* Arithmetic operations (Z) *)
  | OZadd, OZadd => true
  | OZsub, OZsub => true
  | OZmul, OZmul => true  
  | OZle, OZle => true
  | OZlt, OZlt => true
  (* Boolean operations *)
  | Onot, Onot => true
  | Oand, Oand => true
  | Oor, Oor => true
  | Oimp, Oimp => true
  | Oif t1, Oif t2 => T.eqb t1 t2
  (* User operations *) 
  | Ouser u1, Ouser u2 => Uop.eqb u1 u2
  | _, _ => false
  end.

 Lemma eqb_spec : forall x y, if eqb x y then x = y else x <> y.
 Proof.
  destruct x; destruct y; simpl; try reflexivity; try (intro; discriminate);
   match goal with
    |- if T.eqb ?t1 ?t2 then _ else _ => 
      generalize (T.eqb_spec t1 t2); case (T.eqb t1 t2); 
       intros H; subst; trivial; intro H1; apply H; injection H1; trivial
    | |- if if T.eqb ?t11 ?t21 then T.eqb ?t12 ?t22 else false then _ else _ =>
      generalize (T.eqb_spec t11 t21); case (T.eqb t11 t21); 
       intros H; subst; 
       [generalize (T.eqb_spec t12 t22); case (T.eqb t12 t22); intros H; subst;
       trivial; intros H1; apply H; injection H1; trivial
      | intros H1; apply H; injection H1; trivial]
    | _ => idtac
   end.
  generalize (Uop.eqb_spec t0 t1); case (Uop.eqb t0 t1); intros H; subst; trivial.
  intro H1; apply H; injection H1; trivial.
 Qed.
  
 (* Argument types for each operator *)
 Definition targs (o : op) : list T.type := 
  match o with
   | Olength t1 => T.List t1 :: nil
   | OZlength t1 => T.List t1 :: nil 
   | Ohd t1 => T.List t1 :: nil
   | Otl t1 => T.List t1 :: nil
   | Ocons t1 => t1 :: T.List t1 :: nil
   | Oappend t1 => T.List t1 :: T.List t1 :: nil
   | Omem t1 => t1 :: T.List t1 :: nil
   | Oupd t1 t2 => t1 :: t2 :: T.List (T.Pair t1 t2) :: nil
   | Oin_dom t1 t2 => t1 :: T.List (T.Pair t1 t2) :: nil
   | Oin_range t1 t2 => t2 :: T.List (T.Pair t1 t2) :: nil
   | Osplit t1 t2 => t1 :: T.List (T.Pair t1 t2) :: nil
   | Oimg t1 t2 => t1 :: T.List (T.Pair t1 t2) :: nil
   | Onth t1 => T.Nat :: T.List t1 :: nil
   (* Pair operations *)
   | Opair t1 t2 => t1 :: t2 :: nil
   | Ofst t1 t2 => T.Pair t1 t2 :: nil
   | Osnd t1 t2 => T.Pair t1 t2 :: nil
   (* Sum type operations *)
   | Oinl t1 t2 => t1 :: nil
   | Oinr t1 t2 => t2 :: nil
   | Oisl t1 t2 => T.Sum t1 t2 :: nil
   | Oprojl t1 t2 => T.Sum t1 t2 :: nil
   | Oprojr t1 t2 => T.Sum t1 t2 :: nil
   (* Option type operators *)
   | Osome t => t :: nil
   | Oissome t => T.Option t :: nil
   | Oprojo t => T.Option t :: nil
   (* Equality *)
   | Oeq_ t1 => t1 :: t1 :: nil
   (* Arithmetic operations (nat) *)
   | Oadd => T.Nat :: T.Nat :: nil 
   | Osub => T.Nat :: T.Nat :: nil 
   | Omul => T.Nat :: T.Nat :: nil 
   | Ole => T.Nat :: T.Nat :: nil 
   | Olt => T.Nat :: T.Nat :: nil    
   (* Arithmetic operations (Z) *)
   | OZadd => T.Zt :: T.Zt :: nil 
   | OZsub => T.Zt :: T.Zt :: nil 
   | OZmul => T.Zt :: T.Zt :: nil   
   | OZle => T.Zt :: T.Zt :: nil 
   | OZlt => T.Zt :: T.Zt :: nil
   | OZge => T.Zt :: T.Zt :: nil
   | OZgt => T.Zt :: T.Zt :: nil
   | OZopp => T.Zt :: nil
   | OZdiv => T.Zt :: T.Zt :: nil
   | OZmod => T.Zt :: T.Zt :: nil
   | OZpow => T.Zt :: T.Zt :: nil
   (* Boolean operations *)
   | Onot => T.Bool :: nil
   | Oand => T.Bool :: T.Bool :: nil
   | Oor => T.Bool :: T.Bool :: nil
   | Oimp => T.Bool :: T.Bool :: nil
   | Oif t => T.Bool :: t :: t :: nil
   (* User operations *) 
   | Ouser uop => Uop.targs uop
  end.

 (* Result types for each operator *)
 Definition tres (o : op) : T.type :=
  match o with
  | Olength t1 => T.Nat
  | OZlength t1 => T.Zt 
  | Ohd t1 => t1
  | Otl t1 => T.List t1
  | Ocons t1 => T.List t1
  | Oappend t1 => T.List t1
  | Omem t1 => T.Bool
  | Oupd t1 t2 => T.List (T.Pair t1 t2)
  | Oin_dom t1 t2 => T.Bool
  | Oin_range t1 t2 => T.Bool
  | Osplit t1 t2 => T.Pair (T.List (T.Pair t1 t2)) (T.Pair t2 (T.List (T.Pair t1 t2)))
  | Oimg t1 t2 => t2
  | Onth t1 => t1
  (* Pair operations *)
  | Opair t1 t2 => T.Pair t1 t2 
  | Ofst t1 t2 => t1
  | Osnd t1 t2 => t2
  (* Sum type operations *)
  | Oinl t1 t2 => T.Sum t1 t2
  | Oinr t1 t2 => T.Sum t1 t2
  | Oisl t1 t2 => T.Bool
  | Oprojl t1 t2 => t1
  | Oprojr t1 t2 => t2
  (* Option type operators *)
  | Osome t => T.Option t
  | Oissome t => T.Bool
  | Oprojo t => t
  (* Equality *)
  | Oeq_ t1 => T.Bool
  (* Arithmetic operations (nat) *)
  | Oadd => T.Nat
  | Osub => T.Nat
  | Omul => T.Nat
  | Ole => T.Bool
  | Olt => T.Bool 
  (* Arithmetic operations (Z) *)
  | OZadd => T.Zt
  | OZsub => T.Zt
  | OZmul => T.Zt
  | OZle => T.Bool
  | OZlt => T.Bool
  | OZge => T.Bool
  | OZgt => T.Bool
  | OZopp => T.Zt
  | OZdiv => T.Zt
  | OZmod => T.Zt
  | OZpow => T.Zt
  (* Boolean operations *)
  | Onot => T.Bool
  | Oand => T.Bool
  | Oor => T.Bool
  | Oimp => T.Bool
  | Oif t => t
  (* User operations *) 
  | Ouser uop => Uop.tres uop
  end. 
 
 Section EVAL.

  Variable k : nat.

  Definition assoc (A B:Type) (f:A -> bool) (b:B) (l:list (A*B)) :=
   match List.find (fun p => f (fst p)) l with
   | Some p => snd p
   | None => b
   end.

  Fixpoint upd (A B:Type) (f:A -> A -> bool) (a:A) (b:B) (l:list (A*B)) :=
   match l with
   | nil => (a,b)::nil
   | (a',b')::l =>
     if f a a' then (a',b)::l
     else (a',b')::upd f a b l
   end.

  Fixpoint cupd (A B:Type) (f:A -> A -> bool * nat) (a:A) (b:B) (l:list (A*B))  (n:nat) : list (A*B) * nat :=
   match l with
   | nil => ((a,b)::nil, S n)
   | (a',b')::l =>
     let (t,n0) := f a a' in
     if t then ((a',b)::l, S (n+n0)) 
     else 
       let (l', n1) := cupd f a b l (n+n0) in
       ((a',b')::l', S n1)
   end.

 Fixpoint split_assoc  (A B:Type) (f:A -> bool) (b:B) (l:list (A*B)) : list (A*B) * (B * list (A*B)):=
    match l with
    | nil => (nil, (b, nil))
    | hd::l =>
      if f (fst hd) then (nil, (snd hd, l))
      else 
       let r := split_assoc f b l in
       (hd::fst r, snd r)
   end.

  Fixpoint csplit_assoc  (A B:Type) (f:A -> bool * nat) (b:B) (l:list (A*B)) (n:nat) : (list (A*B) * (B * list (A*B))) * nat :=
    match l with
    | nil => ((nil, (b, nil)), S n)
    | hd::l =>
      let tn0 := f (fst hd) in
      let n0 := snd tn0 in
      if fst tn0 then ((nil, (snd hd, l)), S (n+n0))
      else 
       let rn1 := csplit_assoc f b l (n+n0) in
       ((hd::fst (fst rn1), snd (fst rn1)), S (snd rn1))
   end.

  Definition interp_op (o:op) : T.type_op k (targs o) (tres o) :=
   match o as op0 return T.type_op k (targs op0) (tres op0) with
   | Olength t1 => @List.length (T.interp k t1)
   | OZlength t1 => fun v => Z_of_nat (@List.length (T.interp k t1) v)
   | Ohd t1 => @List.hd (T.interp k t1) (T.default k t1)
   | Otl t1 => @List.tail (T.interp k t1)
   | Ocons t1 => @List.cons (T.interp k t1)
   | Oappend t1 => @List.app (T.interp k t1)
   | Omem t1 =>
     fun v => @List.existsb (T.interp k t1) (T.i_eqb k t1 v)
   | Oupd t1 t2 => 
     @upd (T.interp k t1) (T.interp k t2) (T.i_eqb k t1)
 
   | Oin_dom t1 t2 =>
     fun v => @List.existsb (T.interp k t1 * T.interp k t2)%type
     (fun p => T.i_eqb k t1 v (fst p))
   | Oin_range t1 t2 =>
     fun v => @List.existsb (T.interp k t1 * T.interp k t2)%type
      (fun p => T.i_eqb k t2 v (snd p))
   | Osplit t1 t2 =>
     fun v => @split_assoc (T.interp k t1) (T.interp k t2) (T.i_eqb k t1 v) (T.default k t2)
   | Oimg t1 t2 =>
     fun v => @assoc (T.interp k t1) (T.interp k t2) (T.i_eqb k t1 v) (T.default k t2)
   | Onth t1 => fun n l => @List.nth (T.interp k t1) n l (T.default k t1)
   (* Pair operations *)   
   | Opair t1 t2 => @pair (T.interp k t1) (T.interp k t2)
   | Ofst t1 t2 => @fst (T.interp k t1) (T.interp k t2)
   | Osnd t1 t2 => @snd (T.interp k t1) (T.interp k t2)
   (* Sum type operations *)
   | Oinl t1 t2 => @inl (T.interp k t1) (T.interp k t2)
   | Oinr t1 t2 => @inr (T.interp k t1) (T.interp k t2)
   | Oisl t1 t2 => fun s => if s then true else false
   | Oprojl t1 t2 => fun s => 
     match s with
     | inl x => x
     | _ => T.default k t1
     end 
   | Oprojr t1 t2 => fun s => 
     match s with
     | inr x => x
     | _ => T.default k t2
     end 
   (* Option type operators *)
   | Osome t => @Some (T.interp k t)
   | Oissome t => fun o => if o then true else false
   | Oprojo t => fun o =>
     match o with 
     | Some x => x
     | _ => T.default k t
     end   
   (* Equality *)
   | Oeq_ t1 => T.i_eqb k t1
   (* Arithmetic operations (nat) *)
   | Oadd => plus
   | Osub => minus
   | Omul => mult
   | Ole => Compare_dec.leb
   | Olt => fun n1 n2 => Compare_dec.leb (n1 + 1) n2
  (* Arithmetic operations (Z) *)
   | OZadd => Zplus
   | OZsub => Zminus
   | OZmul => Zmult   
   | OZle =>  Zle_bool
   | OZlt =>  Zlt_bool
   | OZge => Zge_bool
   | OZgt => Zgt_bool
   | OZopp => Zopp
   | OZdiv => Zdiv
   | OZmod => Zmod
   | OZpow => Zpower
   (* Boolean operations *)
   | Onot => negb
   | Oand => andb
   | Oor => orb
   | Oimp => impb
   | Oif t => fun b v1 v2 => if b then v1 else v2
   (* User operations *)
   | Ouser uop => @Uop.interp_op k uop
   end.

   Definition eq_cost k t (x y : T.interp k t) := (T.size k t x + T.size k t y)%nat.

   Definition cinterp_op (o:op) : T.ctype_op k (targs o) (tres o) :=
   match o as op0 return T.ctype_op k (targs op0) (tres op0) with
   | Olength t1 => fun l => let n:=List.length l in (n,n) 
   | OZlength t1 => fun l => let n:=List.length l in (Z_of_nat n,n)  
   | Ohd t1 => fun l => (List.hd (T.default k t1) l, S O)
   | Otl t1 => fun l => (List.tail l, S O)
   | Ocons t1 => fun a l => (List.cons a l, S O)
   | Oappend t1 => fun l1 l2 => (List.app l1 l2, List.length l1)
   | Omem t1 =>
     fun v l => cexistsb (fun v1 => (T.i_eqb k t1 v v1, eq_cost k _ v v1)) l 1%nat
   | Oupd t1 t2 =>
     fun a b l => cupd (fun v1 v2 => (T.i_eqb k t1 v1 v2, eq_cost k _ v1 v2)) a b l 1%nat 
   | Oin_dom t1 t2 =>
     fun v l => cexistsb (fun v1 => (T.i_eqb k t1 v (fst v1), eq_cost k _ v (fst v1))) l 1%nat
   | Oin_range t1 t2 =>
     fun v l => cexistsb (fun v1 => (T.i_eqb k t2 v (snd v1), eq_cost k _ v (snd v1))) l 1%nat
   | Osplit t1 t2 =>
     fun v l => 
        @csplit_assoc (T.interp k t1) (T.interp k t2) (fun v1 => (T.i_eqb k t1 v v1, eq_cost k _ v v1)) (T.default k t2) l 1%nat 
   | Oimg t1 t2 =>
     fun v l => 
     let (r, c) := 
      cfind_default (fun v1 => (T.i_eqb k t1 v (fst v1), eq_cost k _ v (fst v1))) l 1%nat (T.default k t1, T.default k t2) in
     (snd r, c)
   | Onth t1 =>
     fun n l => (@List.nth (T.interp k t1) n l (T.default k t1), List.length l)
   (* Pair operations *)
   | Opair t1 t2 => fun x y => (pair x y, S O)
   | Ofst t1 t2 => fun p => (fst p, S O)
   | Osnd t1 t2 => fun p => (snd p, S O)
   (* Sum type operations *)
   | Oinl t1 t2 => fun x => (inl _ x, S O) 
   | Oinr t1 t2 => fun x => (inr _ x, S O)
   | Oisl t1 t2 => fun s => (if s then true else false, S O)
   | Oprojl t1 t2 => fun s => 
     (match s with
     | inl x => x
     | _ => T.default k t1
     end, S O) 
   | Oprojr t1 t2 => fun s => 
     (match s with
     | inr x => x
     | _ => T.default k t2
     end, S O) 
   (* Option type operators *)
   | Osome t => fun x => (Some x, S O)
   | Oissome t => fun o => (if o then true else false, S O)
   | Oprojo t => fun o =>
     (match o with 
     | Some x => x
     | _ => T.default k t
     end, S O)
   (* Equality *)
   | Oeq_ t1 => fun x y => (T.i_eqb k _ x y, eq_cost k _ x y)%nat  
   (* Arithmetic operations (nat) *)
   | Oadd => fun x y => (plus x y, size_nat x)
   | Osub => fun x y => (minus x y, size_nat y)
   | Omul => fun x y => (mult x y, size_nat x * size_nat y)%nat
   | Ole => fun x y => (Compare_dec.leb x y, size_nat x)
   | Olt => fun x y => (Compare_dec.leb (x+1) y, size_nat y)  
   (* Arithmetic operations (Z) *)
   | OZadd => fun x y => (Zplus x y, size_Z x)
   | OZsub => fun x y => (Zminus x y, size_Z y)
   | OZmul => fun x y => (Zmult x y, size_Z x * size_Z y)%nat
   | OZle => fun x y => (Zle_bool x y, size_Z x)
   | OZlt => fun x y => (Zlt_bool x y, size_Z y)
   | OZge => fun x y => (Zge_bool x y, size_Z y)
   | OZgt => fun x y => (Zgt_bool x y, size_Z y)
   | OZopp => fun x => (Zopp x, size_Z x)
   | OZdiv => fun x y => (Zdiv x y, size_Z x)
   | OZmod => fun x y => (Zmod x y, size_Z y)
   | OZpow => fun x y => (Zpower x y, size_Z x)
   (* Boolean operations *)
   | Onot => fun b => (negb b, S O)
   | Oand => fun b1 b2 => (andb b1 b2, S O)
   | Oor => fun b1 b2 => (orb b1 b2, S O)
   | Oimp => fun b1 b2 => (impb b1 b2, S O)
   | Oif t => fun b v1 v2 => (if b then v1 else v2, S O)
   (* User operations *)
   | Ouser uop => @Uop.cinterp_op k uop
   end.

  Definition eval_op 
   (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) :=
   @T.app_op k (targs op) (tres op) (interp_op op) args.

  Definition ceval_op 
   (op:t) (args: dlist (T.interp k) (targs op)) : T.interp k (tres op) * nat :=
   @T.capp_op k (targs op) (tres op) (cinterp_op op) args.

 End EVAL.

 Implicit Arguments eval_op [k].
 Implicit Arguments ceval_op [k].

 Lemma ceval_op_spec : forall k op args,
  @eval_op k op args = fst (@ceval_op k op args).
 Proof.
  intros k o args; destruct o; simpl in args;    
   try (T.dlist_inversion args; subst; trivial);
   try (unfold eval_op, ceval_op; simpl); try (apply existsb_cexistsb; trivial; fail).
   generalize 1%nat;induction x1;simpl;trivial.
   intros;destruct a.
   destruct (T.i_eqb k t0 x f);trivial.
   rewrite (IHx1 (n + eq_cost k t0 x f)%nat).
   match goal with |- _ :: fst ?X = _ => destruct X end;trivial.
   fold (T.interp k t1).
   generalize 1%nat;induction x0;simpl;trivial.
   intros.
   destruct (T.i_eqb k t0 x (@fst  (T.interp k t0) (T.interp k t1) a));trivial.
   rewrite (IHx0 (n + eq_cost k t0 x (fst a))%nat);trivial.
   fold (T.interp k t1).
   
   assert (W:= @find_cfind_default (T.interp k t0 * T.interp k t1)
            (fun v1 : T.interp k t0 * T.interp k t1 => T.i_eqb k t0 x (fst v1))
            (fun v1 : T.interp k t0 * T.interp k t1 =>
                 (T.i_eqb k t0 x (fst v1), eq_cost k t0 x (fst v1)))
            (T.default k t0, T.default k t1)
            (fun v => refl_equal _) x0 1).
   unfold assoc, find_default in W |- *.
   destruct (cfind_default
         (fun v1 : T.interp k t0 * T.interp k t1 =>
          (T.i_eqb k t0 x (fst v1), eq_cost k t0 x (fst v1))) x0 1
         (T.default k t0, T.default k t1)).
   destruct (find (fun v1 : T.interp k t0 * T.interp k t1 => T.i_eqb k t0 x (fst v1)) x0).
   rewrite W; trivial.
   simpl in W; rewrite <- W; trivial.
   refine (Uop.ceval_op_spec _).
 Qed.

 (* Dependant equality *)
 Module Odec <: DecidableType.

  Definition U := op.

  Lemma eq_dec : forall (t1 t2:op), {t1 = t2} + {t1 <> t2}.
  Proof.
   intros t1 t2; generalize (eqb_spec t1 t2); destruct (eqb t1 t2); auto.
  Qed.

 End Odec.
 
 Include DecidableEqDepSet Odec.

End MakeOp.
