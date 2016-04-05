(** * SemInstr.v : Semantics of pWHILE programs *)

Require Import List.


Set Implicit Arguments.

Require Export Instructions.
Require Export Relations.
Require Import Wf_nat.


Module Type SEM_INSTR (UT:UTYPE) (T:TYPE UT) (Var:VAR UT T) (Proc:PROC UT T)
 (Uop:UOP UT T) (O:OP UT T Uop) (US:USUPPORT UT T)
 (Mem:MEM UT T Var) (E:EXPR UT T Var Uop O US Mem)
 (I:INSTR UT T Var Proc Uop O US Mem E).

 Notation "m '{!' x '<--' v '!}'" := (Mem.upd m x v) (at level 60).

 Notation "[ x ; .. ; y ]" :=
  (@cons I.instr x .. (@cons I.instr y (@nil I.instr)) ..)
  (format "'[hv' [ '/' x ;  '/' .. ;  '/' y '/' ] ']'").

 Notation "'If' e 'then' c1 'else' c2" := (I.Cond e c1 c2)
  (at level 65,
   format "'[hv' 'If'  e  '/' 'then'  '[hv' c1 ']'  '/' 'else'  '[hv' c2 ']' ']'").

 Notation "'If' e '_then' c" := (I.Cond e c nil) 
  (at level 65, format "'[hv' 'If'  e  '/' '_then'  '[hv' c ']' ']'").

 Notation "'while' e 'do' c" := (I.While e c) (at level 65).

 Notation "d '<c-' f 'with' a" := (I.Call d f a) (at level 61). 

 (* Call with no arguments *)
 Notation "d '<c-' f 'with' '{}'" := (d <c- f with dnil _) (at level 61).

 Notation "x '<-' e" := (I.Instr (I.Assign x e)) (at level 65).
 
 Notation " x '<$-' d " := (I.Instr (I.Random x d)) (at level 65).

 Notation cmd := (list I.instr).

 Definition var_decl := @dlist T.type Var.var.

 Definition eqb_var_decl lt (l1 l2:var_decl lt) :=
  dforall2 Var.veqb l1 l2.

 Parameter eqb_var_decl_spec : forall lt l1 l2,
  if @eqb_var_decl lt l1 l2 then l1 = l2 else l1 <> l2.

 Record decl (rt:T.type) (lt:list T.type) : Type := 
  mk_Decl {
   d_params : var_decl lt;
   d_res : E.expr rt;
   d_body : cmd;
   d_all_local : forall t (x:Var.var t), 
    @DIn _ Var.var t x lt d_params -> Var.vis_local x
  }.

 Definition env := forall tr (f:Proc.proc tr), decl tr (Proc.targs f).
 
 Definition proc_body (E:env) tr (p:Proc.proc tr) := d_body (E tr p).

 Definition proc_res (E:env) tr (p:Proc.proc tr) := d_res (E tr p).

 Definition proc_params (E:env) tr (p:Proc.proc tr) := d_params (E tr p).

 Definition proc_params_local (E:env) tr (p:Proc.proc tr) := 
  d_all_local (E tr p).

 Parameter dforallb_local : forall lt (l:var_decl lt), 
  dforallb Var.vis_local l ->
  forall t (x:Var.var t), @DIn _ Var.var t x lt l -> Var.vis_local x.

 Definition add_decl (E:env) fr (f:Proc.proc fr) 
  (params:var_decl (Proc.targs f))
  (Hl:dforallb Var.vis_local params) 
  (body:cmd) 
  (res: E.expr fr) : env :=
  let d := mk_Decl params res body (dforallb_local params Hl) in
   fun (gr:T.type) =>
    match T.eq_dec fr gr with
    | left Heqr => 
      match Heqr in (_ = y0) return forall (g:Proc.proc y0), decl y0 (Proc.targs g) with
      | refl_equal =>
        fun (g:Proc.proc fr) =>
         match Proc.eq_dec f g with
         | left Heqf =>
           match Heqf in (_ = y0) return decl fr (Proc.targs y0) with
           | refl_equal => d
           end
         | right _ => E fr g
         end
      end
    | right _ => fun g => E gr g
    end.

 Parameter add_decl_same : forall E fr f params Hl body res, 
  proc_params (@add_decl E fr f params Hl body res) f = params /\
  proc_body (@add_decl E fr f params Hl body res) f = body /\
  proc_res (@add_decl E fr f params Hl body res) f = res.

 Parameter add_decl_other : forall E fr f params Hl body res gr g,
  ~eq_dep T.type Proc.proc fr f gr g -> 
  proc_params (@add_decl E fr f params Hl body res) g = proc_params E g /\
  proc_body (@add_decl E fr f params Hl body res) g = proc_body E g /\
  proc_res (@add_decl E fr f params Hl body res) g = proc_res E g.
 
      
 (** ** Semantics of procedure calls *)

 Parameter init_mem : forall k, env -> forall fr (f:Proc.proc fr), 
  E.args (Proc.targs f) -> Mem.t k -> Mem.t k.

 Parameter cinit_mem : forall k, env -> forall fr (f:Proc.proc fr), 
  E.args (Proc.targs f) -> Mem.t k -> Mem.t k * nat.

 Parameter return_mem : forall k, env -> forall t (x:Var.var t), 
  Proc.proc t -> Mem.t k -> Mem.t k -> Mem.t k.

 Parameter creturn_mem : forall k, env -> forall t (x:Var.var t), 
  Proc.proc t -> Mem.t k -> Mem.t k -> Mem.t k * nat.
 
 Parameter return_mem_eq : forall k E1 E2 t (f:Proc.proc t) x (m m':Mem.t k), 
  proc_res E1 f = proc_res E2 f ->
  return_mem E1 x f m m' = return_mem E2 x f m m'.

 (** Specification of [init_mem] *)

 Fixpoint get_arg (t:T.type) (x:Var.var t) (lt1 lt2:list T.type) 
  (lv:var_decl lt1) (la:E.args lt2) {struct lv} : option (E.expr t) :=
  match lv, la with
  | dcons t1 lt1 y lv, dcons t2 lt2 e_y la =>
   match get_arg x lv la with
   | Some r => Some r
   | None =>
     if Var.veqb x y then
      match T.eq_dec t2 t with
      | left Heq =>
        match Heq in (_ = y0) return  option (E.expr y0) with
        | refl_equal => Some (e_y)
        end
      | _ => None
      end
     else None
   end
  | _, _ => None
  end.
 
 Parameter get_arg_Some : forall t (x:Var.var t) lt1 (lv:var_decl lt1) lt2
  (la:E.args lt2) e, 
  get_arg x lv la = Some e -> DIn t x lv.
 
 Parameter get_arg_Some2 : forall t (x:Var.var t) lt1 (lv:var_decl lt1) lt2
  (la:E.args lt2) e, 
  get_arg x lv la = Some e -> DIn t e la.
 
 Parameter lookup_init_mem : forall k E t (f:Proc.proc t) a (m:Mem.t k) tx 
  (x:Var.var tx),
  match get_arg x (proc_params E f) a with
  | Some e => (init_mem E f a m) x = E.eval_expr e m
  | None => (init_mem E f a m) x = Mem.global m x
  end.
 
 Parameter init_mem_global : forall k E t (f:Proc.proc t) a (m:Mem.t k) 
  tx (x:Var.var tx),
  Var.is_global x -> (init_mem E f a m) x = m x.

 Parameter init_mem_local : forall k E t (f:Proc.proc t) 
  (a1 a2:E.args (Proc.targs f)) 
  (m1 m2:Mem.t k),
  E.eval_args  a1 m1 = E.eval_args a2 m2 ->
  forall tx (x:Var.var tx), 
   Var.is_local x ->
   init_mem E f a1 m1 x = init_mem E f a2 m2 x.

 Parameter init_mem_eq : forall k E t (f:Proc.proc t) 
  (a1 a2:E.args (Proc.targs f)) (m:Mem.t k),
  E.eval_args  a1 m = E.eval_args a2 m ->
  init_mem E f a1 m = init_mem E f a2 m.

 Parameter init_mem_eq2 : forall k E1 E2 t (f:Proc.proc t) 
  (a1 a2:E.args (Proc.targs f)) (m:Mem.t k),
  proc_params E1 f = proc_params E2 f ->
  E.eval_args  a1 m = E.eval_args a2 m ->
  init_mem E1 f a1 m = init_mem E2 f a2 m.
 
 Parameter cinit_mem_spec_l : forall k E fr f a m,
  fst (@cinit_mem k E fr f a m) = @init_mem k E fr f a m.
 
 Parameter cinit_mem_spec_r : forall k E fr f a m,
  snd (@cinit_mem k E fr f a m) =
  dfold_right (fun t vn n => n + snd vn)%nat O (E.ceval_args a m).

 (* Specification of [return_mem] *)

 Parameter return_mem_dest : forall k E t (x:Var.var t) f (m mf:Mem.t k),
  return_mem E x f m mf x = E.eval_expr (proc_res E f) mf.
 
 Parameter return_mem_local : forall k E tx (x:Var.var tx) f (m mf:Mem.t k) 
  ty (y:Var.var ty), 
  Var.mkV x <>  y -> Var.is_local y -> 
  (return_mem E x f m mf) y = m y.
 
 Parameter return_mem_global : forall k E tx (x:Var.var tx) f (m mf:Mem.t k) 
  ty (y:Var.var ty),
  Var.mkV x <> y ->
  Var.is_global y -> (return_mem E x f m mf) y = mf y.

 Parameter creturn_mem_spec_l : forall k E t (x:Var.var t) f (m mf:Mem.t k),
  fst (creturn_mem E x f m mf) = return_mem E x f m mf.
 
 Parameter creturn_mem_spec_r : forall k E t (x:Var.var t) f (m mf:Mem.t k),
  snd (creturn_mem E x f m mf) = snd (E.ceval_expr (proc_res E f) mf).

 (** Specification of [sum_support] *)

 Parameter sum_support_lossless : forall k t (d:E.support t) (m:Mem.t k),
  mu (sum_support (T.default k t) (@E.eval_support k t d m)) (fun _ => 1) == 1.
 
 Parameter deno : forall k, cmd -> env -> (Mem.t k) -> Distr (Mem.t k).
 
 Parameter cdeno : forall k, cmd -> env -> (Mem.t k*nat) -> Distr (Mem.t k*nat).
  
 Notation "'[[[' c ']]]'" := (cdeno c) (at level 59, format "[[[  c  ]]]").
 Notation "'[[' c ']]'" := (deno c) (at level 59, format "[[  c  ]]").


 Section DENO_FACTS.   
 
  Variable k : nat.
  Variable E : env.

  Parameter sem_discr : forall c (m:Mem.t k), is_Discrete ([[c]] E m).

  Parameter cdeno_assign_elim : forall t (x:Var.var t) e (mn:Mem.t k * nat) f,
   mu ([[[ [x <- e] ]]] E mn) f == 
   let (v,n) := E.ceval_expr e (fst mn) in
    f (fst mn{!x <-- v!}, snd mn + n)%nat.

  Parameter cdeno_assign : forall t (x:Var.var t) e (mn:Mem.t k * nat),
   [[[ [x <- e] ]]] E mn == 
   let (v,n) := E.ceval_expr e (fst mn) in
    Munit (fst mn{!x <-- v!}, snd mn + n)%nat.
  
  Parameter deno_assign_elim : forall t (x:Var.var t) e (m:Mem.t k) f,
   mu ([[ [x <- e] ]] E m) f == 
   f (m{! x <-- E.eval_expr e m !}).
  
  Parameter deno_assign : forall t (x:Var.var t) e (m:Mem.t k),
   [[ [x <- e] ]] E m == Munit (m{! x <-- E.eval_expr e m !}).
  
  Parameter cdeno_random_elim : forall t (x:Var.var t) s (mn:Mem.t k * nat) f,
   mu ([[[ [x <$- s] ]]] E mn) f ==
   let (s,n) := E.ceval_support s (fst mn) in
    mu (sum_support (T.default k t) s)
    (fun v => f (fst mn {!x <-- v!}, snd mn + n))%nat.
  
  Parameter cdeno_random : forall t (x:Var.var t) s (mn:Mem.t k * nat),
   [[[ [x <$- s] ]]] E mn ==
   let (s,n) := E.ceval_support s (fst mn) in
    Mlet (sum_support (T.default k t) s)      
    (fun v => Munit (fst mn {!x <-- v!}, snd mn + n))%nat.
 
  Parameter deno_random_elim : forall t (x:Var.var t) s (m:Mem.t k) f,
   mu ([[ [x <$- s] ]] E m) f== 
   mu (sum_support (T.default k t) (E.eval_support s m))
   (fun v => f (m{!x <-- v!})).
  
  Parameter deno_random : forall t (x:Var.var t) s (m:Mem.t k),
   [[ [x <$- s] ]] E m == 
   Mlet (sum_support (T.default k t) (E.eval_support s m)) 
   (fun v => Munit (m{!x <-- v!})).
  
  Parameter cdeno_nil_elim : forall (mn:Mem.t k * nat) f,
   mu ([[[nil]]] E mn) f == f mn.
  
  Parameter cdeno_nil : forall (mn:Mem.t k * nat),
   [[[nil]]] E mn == Munit mn.
  
  Parameter deno_nil_elim : forall (m:Mem.t k) f,
   mu ([[nil]] E m) f == f m.
  
  Parameter deno_nil : forall m:Mem.t k, 
   [[nil]] E m == Munit m.
  
  Parameter cdeno_cons_elim : forall i c (mn:Mem.t k * nat) f,
   mu ([[[ i::c ]]] E mn) f == 
   mu (Mlet ([[[ [i] ]]] E mn) ([[[c]]] E)) f.
  
  Parameter cdeno_cons : forall i c (mn:Mem.t k * nat),
   [[[ i::c ]]] E mn == 
   Mlet ([[[ [i] ]]] E mn) ([[[c]]] E).
  
  Parameter cdeno_add_end : forall c (m:Mem.t k) n p f,
   mu ([[[c]]] E (m, n + p)%nat) f == 
   mu ([[[c]]] E (m, n)) (fun mn' => f (fst mn', p + snd mn')%nat).

  Parameter deno_cons_elim : forall i c (m:Mem.t k) f,
   mu ([[i::c]] E m) f == mu (Mlet ([[ [i] ]] E m) ([[c]] E)) f.
  
  Parameter deno_cons : forall i c (m:Mem.t k),
   [[i::c]] E m == Mlet ([[ [i] ]] E m) ([[c]] E).
  
  Parameter cdeno_app_elim : forall c1 c2 (mn:Mem.t k * nat) f,
   mu ([[[c1 ++ c2]]] E mn) f == 
   mu (Mlet ([[[c1]]] E mn) ([[[c2]]] E)) f.
  
  Parameter cdeno_app : forall c1 c2 (mn:Mem.t k * nat),
   [[[c1 ++ c2]]] E mn == Mlet ([[[c1]]] E mn) ([[[c2]]] E).
  
  Parameter deno_app_elim : forall c1 c2 (m:Mem.t k) f, 
   mu ([[c1 ++ c2]] E m) f == 
   mu ([[ c1 ]] E m) (fun m' => mu ([[c2]] E m') f).
  
  Parameter deno_app : forall c1 c2 (m:Mem.t k), 
   [[c1 ++ c2]] E m == Mlet ([[c1]] E m) ([[c2]] E).
 
  Parameter cdeno_cond_t_elim : forall (e:E.expr T.Bool) c1 c2 
   (mn:Mem.t k * nat) f,
   E.eval_expr e (fst mn) = true ->
   mu ([[[ [If e then c1 else c2] ]]] E mn) f ==
   mu ([[[c1]]] E (fst mn, snd mn + snd (E.ceval_expr e (fst mn)))%nat) f.
 
  Parameter cdeno_cond_f_elim : forall (e:E.expr T.Bool) c1 c2 
   (mn:Mem.t k * nat) f,
   E.eval_expr e (fst mn) = false ->
   mu ([[[ [If e then c1 else c2] ]]] E mn) f ==
   mu ([[[c2]]] E (fst mn, snd mn + snd (E.ceval_expr e (fst mn)))%nat) f.
  
  Parameter cdeno_cond_elim : forall e c1 c2 (mn:Mem.t k * nat) f,
   mu ([[[ [If e then c1 else c2] ]]] E mn) f ==
   let (b,n) := E.ceval_expr e (fst mn) in
    mu (if b then [[[c1]]] E (fst mn, snd mn + n)%nat 
     else [[[c2]]] E (fst mn, snd mn + n)%nat) f.
 
  Parameter cdeno_cond : forall e c1 c2 (mn:Mem.t k * nat),
   [[[ [If e then c1 else c2] ]]] E mn ==
   let (b,n) := E.ceval_expr e (fst mn) in
    if b then [[[c1]]] E (fst mn, snd mn + n)%nat
     else [[[c2]]] E (fst mn, snd mn + n)%nat.
 
  Parameter deno_cond_t_elim : forall (e:E.expr T.Bool) c1 c2 (m:Mem.t k) f, 
   E.eval_expr e m = true -> 
   mu ([[ [If e then c1 else c2] ]] E m) f == mu ([[c1]] E m) f.
  
  Parameter deno_cond_f_elim : forall (e:E.expr T.Bool) c1 c2 (m:Mem.t k) f, 
   E.eval_expr e m = false -> 
   mu ([[ [If e then c1 else c2] ]] E m) f == mu ([[c2]] E m) f.
 
  Parameter deno_cond_elim : forall (e:E.expr T.Bool) c1 c2 (m:Mem.t k) f,
   mu ([[ [If e then c1 else c2] ]] E m) f == 
   mu (if E.eval_expr e m then [[c1]] E m else [[c2]] E m) f.
 
  Parameter deno_cond : forall (e:E.expr T.Bool) c1 c2 (m:Mem.t k),
   [[ [ If e then c1 else c2] ]] E m == 
   if E.eval_expr e m then ([[c1]] E m) else ([[c2]] E m).
 
  Parameter cdeno_while_elim : forall e c (mn:Mem.t k * nat) f, 
   mu ([[[ [while e do c] ]]] E mn) f == 
   mu ([[[ [If e _then (c ++ [while e do c])] ]]] E mn) f.
 
  Parameter cdeno_while : forall e c (mn:Mem.t k * nat), 
   [[[ [while e do c] ]]] E mn == 
   [[[ [If e _then (c ++ [while e do c])] ]]] E mn.
 
  Parameter deno_while_elim : forall e c (m:Mem.t k) f, 
   mu ([[ [while e do c] ]] E m) f == 
   mu ([[ [If e _then (c ++ [while e do c])] ]] E m) f.

  Parameter deno_while : forall e c (m:Mem.t k), 
   [[ [while e do c] ]] E m == [[ [If e _then (c ++ [while e do c])] ]] E m.

  Parameter cdeno_call_elim : forall t (x:Var.var t) (p:Proc.proc t) 
   (la:E.args (Proc.targs p)) (mn:Mem.t k*nat) f,
   mu ([[[ [x <c- p with la] ]]] E mn) f ==
   mu (Mlet (Munit (cinit_mem E p la (fst mn)))
    (fun mn' =>
     Mlet ([[[ proc_body E p ]]] E (fst mn', snd mn + snd mn')%nat)
     (fun mn'' =>
      Munit (fst (creturn_mem E x p (fst mn) (fst mn'')),
       snd (creturn_mem E x p (fst mn) (fst mn'')) + snd mn'')%nat))) f.

  Parameter cdeno_call : forall t (x:Var.var t) (p:Proc.proc t) 
   (la:E.args (Proc.targs p)) (mn:Mem.t k*nat),
   [[[ [x <c- p with la] ]]] E mn ==
   Mlet (Munit (cinit_mem E p la (fst mn)))
   (fun mn' =>
    Mlet ([[[ proc_body E p ]]] E (fst mn', snd mn + snd mn')%nat)
    (fun mn'' =>
     Munit (fst (creturn_mem E x p (fst mn) (fst mn'')),
      snd (creturn_mem E x p (fst mn) (fst mn'')) + snd mn'')%nat)).

  Parameter deno_call_elim : forall t (x:Var.var t) p la (m:Mem.t k) f,
   mu ([[ [x <c- p with la] ]] E m) f ==
   mu (([[proc_body E p]]) E (init_mem E p la m)) 
   (fun m' => f (return_mem E x p m m')).

  Parameter deno_call : forall t (x:Var.var t) p la (m:Mem.t k),
   [[ [x <c- p with la] ]] E m ==
   Mlet ([[ proc_body E p ]] E (init_mem E p la m)) 
   (fun m' => Munit (return_mem E x p m m')).

  Parameter deno_prod_comm :  forall (A:Type) (d:Distr A) E c (m:Mem.t k),
   prod_comm ([[c]] E m) d.

  Parameter deno_comm : forall E1 E2 c1 c2 (m1 m2:Mem.t k) f,
   mu ([[c1]] E1 m1) (fun m  => mu ([[c2]] E2 m2) (fun m' => f m m')) ==
   mu ([[c2]] E2 m2) (fun m' => mu ([[c1]] E1 m1) (fun m  => f m m')).

  Fixpoint unroll_while (e:E.expr T.Bool) (c:cmd) (n:nat) {struct n} : cmd :=
   match n with
   | O => [If e _then nil]
   | S n => [If e _then (c ++ unroll_while e c n)]
   end.

  Parameter unroll_sem_mono : forall E e c (m:Mem.t k), 
   monotonic 
   (fun (n:natO) => drestr ([[ unroll_while e c n ]] E m) (negP (E.eval_expr e))).
  
  Definition unroll_while_sem E e c m : natO -m> cDistr (Mem.t k) :=
   mk_fmono (unroll_sem_mono E e c m).
  
  Parameter deno_while_unfold : forall E e c m,
   [[ [while e do c] ]] E m == lub (unroll_while_sem E e c m).

  Parameter deno_while_unfold_elim : forall E e c m f,
   mu ([[ [while e do c] ]] E m) f ==
   lub ((@Mu _ @ (unroll_while_sem E e c m)) <_> f).
    
  Parameter deno_while_restr_elim : forall E e c (m:Mem.t k) f,
   mu ([[ [while e do c] ]] E m) f == 
   mu ([[ [while e do c] ]] E m) (fun m => if E.eval_expr e m then 0 else f m).

  Parameter while_ind0 : forall (P: Mem.t k -> Prop) E (e:E.expr T.Bool) c, 
   (forall m, P m -> E.eval_expr e m = true -> range P ([[ c ]] E m)) ->
   forall m , P m -> 
    range (fun m => P m /\ E.eval_expr e m = false) ([[ [while e do c] ]] E m). 
  
  Parameter while_indR : forall (R : Mem.t k-> Mem.t k-> Prop)
   (d:Mem.t k-> Mem.t k-> Distr (Mem.t k* Mem.t k)) 
   (E1:env) (e1:E.expr T.Bool) (c1:cmd) 
   (E2:env) (e2:E.expr T.Bool) (c2:cmd),
   (forall m1 m2:Mem.t k, R m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2) ->
   (forall m1 m2:Mem.t k,
    R m1 m2 ->
    E.eval_expr e1 m1 = true ->
    lift R (d m1 m2) (([[c1]]) E1 m1) (([[c2]]) E2 m2)) ->
   exists dw : Mem.t k -> Mem.t k-> Distr (Mem.t k * Mem.t k),
    forall m1 m2 : Mem.t k,
     R m1 m2 ->
     lift (fun m3 m4:Mem.t k => R m3 m4 /\ E.eval_expr e1 m3 = false)
     (dw m1 m2) (([[ [while e1 do c1] ]]) E1 m1)
     (([[ [while e2 do c2] ]]) E2 m2).

 End DENO_FACTS.

End SEM_INSTR.


Module Make (UT:UTYPE) (T:TYPE UT) (Var:VAR UT T) (Proc:PROC UT T)
 (Uop:UOP UT T) (O:OP UT T Uop) (US:USUPPORT UT T)
 (Mem:MEM UT T Var)
 (E:EXPR UT T Var Uop O US Mem)
 (I:INSTR UT T Var Proc Uop O US Mem E) <: 
 SEM_INSTR UT T Var Proc Uop O US Mem E I.

 Notation "m '{!' x '<--' v '!}'" := (Mem.upd m x v) (at level 60).

 Notation "[ x ; .. ; y ]" := 
  (@cons I.instr x .. (@cons I.instr y (@nil I.instr)) ..)
  (format "'[hv' [ '/' x ;  '/' .. ;  '/' y '/' ] ']'").

 Notation "'If' e 'then' c1 'else' c2" := (I.Cond e c1 c2)
  (at level 65,
   format "'[hv' 'If'  e  '/' 'then'  '[hv' c1 ']'  '/' 'else'  '[hv' c2 ']' ']'").

 Notation "'If' e '_then' c" := (I.Cond e c nil) 
  (at level 65, format "'[hv' 'If'  e  '/' '_then'  '[hv' c ']' ']'").

 Notation "'while' e 'do' c" := (I.While e c) (at level 65).

 Notation "d '<c-' f 'with' a" := (I.Call d f a) (at level 61).
 (* Call with no arguments *)
 Notation "d '<c-' f 'with' '{}'" := (d <c- f with dnil _) (at level 61).

 Notation "x '<-' e" := (I.Instr (I.Assign x e)) (at level 65).

 Notation " x '<$-' d " := (I.Instr (I.Random x d)) (at level 65).

 Notation cmd := (list I.instr).

 Definition var_decl := @dlist T.type Var.var.

 Definition eqb_var_decl lt (l1 l2:var_decl lt) :=
  dforall2 Var.veqb l1 l2.
 
 Lemma eqb_var_decl_spec : forall lt l1 l2,
  if @eqb_var_decl lt l1 l2 then l1 = l2 else l1 <> l2.
 Proof.
  assert (forall lt1 (l1 : var_decl lt1) lt2 (l2:var_decl lt2),
   if dforall2 Var.veqb l1 l2 then eq_dep (list T.type) (dlist Var.var) lt1 l1 lt2 l2 else 
    ~eq_dep (list T.type) (dlist Var.var) lt1 l1 lt2 l2).
  induction l1; destruct l2; simpl.
  constructor.
  intros Heq; inversion Heq.
  intros Heq; inversion Heq.
  generalize (Var.veqb_spec_dep p v); destruct (Var.veqb p v).
  intros H0; inversion H0; simpl.
  generalize (IHl1 _ l2); destruct (dforall2 Var.veqb l1 l2); intros.
  inversion H1; simpl; constructor.
  intros Heq; apply H1; inversion Heq; simpl; constructor.
  intros H1 H2; apply H1; inversion H2; simpl; constructor.
  intros lt l1 l2; generalize (H _ l1 _ l2); unfold eqb_var_decl;
   destruct (dforall2 Var.veqb l1 l2); intros.
  apply T.l_eq_dep_eq; trivial.
  intros Heq; apply H0; rewrite Heq; constructor.
 Qed.

 Record decl (rt:T.type) (lt:list T.type) : Type := 
  mk_Decl {
   d_params : var_decl lt;
   d_res : E.expr rt;
   d_body : cmd;
   d_all_local : forall t (x:Var.var t), 
    @DIn _ Var.var t x lt d_params -> Var.vis_local x
  }.

 Definition env := forall tr (f:Proc.proc tr), decl tr (Proc.targs f).
 
 Definition proc_body (E:env) tr (p:Proc.proc tr) := d_body (E tr p).

 Definition proc_res (E:env) tr (p:Proc.proc tr) := d_res (E tr p).

 Definition proc_params (E:env) tr (p:Proc.proc tr) := d_params (E tr p).

 Definition proc_params_local (E:env) tr (p:Proc.proc tr) := 
  d_all_local (E tr p).
 
 Lemma dforallb_local : forall lt (l:var_decl lt), 
  dforallb Var.vis_local l ->
  forall t (x:Var.var t), @DIn _ Var.var t x lt l -> Var.vis_local x.
 Proof.
  intros lt l H; unfold is_true.
  rewrite <- dforallb_forall; trivial.
  intros a1 a2; generalize (T.eqb_spec a1 a2); destruct (T.eqb a1 a2); auto.
 Qed.
 
 Definition add_decl (E:env) fr (f:Proc.proc fr) 
  (params:var_decl (Proc.targs f))
  (Hl:dforallb Var.vis_local params) 
  (body:cmd) 
  (res: E.expr fr) : env :=
  let d := mk_Decl params res body (dforallb_local params Hl) in
  fun (gr:T.type) =>
    match T.eq_dec fr gr with
    | left Heqr => 
       match Heqr in (_ = y0) return forall (g:Proc.proc y0), decl y0 (Proc.targs g) with
       | refl_equal =>
         fun (g:Proc.proc fr) =>
          match Proc.eq_dec f g with
          | left Heqf =>
            match Heqf in (_ = y0) return decl fr (Proc.targs y0) with
            | refl_equal => d
            end
          | right _ => E fr g
          end
       end
    | right _ => fun g => E gr g
    end.

 Lemma add_decl_same : forall E fr f params Hl body res, 
  proc_params (@add_decl E fr f params Hl body res) f = params /\
  proc_body (@add_decl E fr f params Hl body res) f = body /\
  proc_res (@add_decl E fr f params Hl body res) f = res.
 Proof.   
  intros; unfold add_decl, proc_params,proc_body, proc_res; simpl. 
  case_eq (T.eq_dec fr fr); intros.
  unfold d_params, d_body, d_res.
  rewrite (T.UIP_refl e).
  case_eq (Proc.eq_dec f f); intros.
  rewrite (Proc.UIP_refl e0); auto.
  elim (Proc.eq_dec_r H0); trivial.
  elim (T.eq_dec_r H); trivial.
 Qed.

 Lemma add_decl_other : forall E fr f params Hl body res gr (g:Proc.proc gr), 
  ~eq_dep T.type Proc.proc fr f gr g -> 
  proc_params (@add_decl E fr f params Hl body res) g = proc_params E g /\
  proc_body (@add_decl E fr f params Hl body res) g = proc_body E g /\
  proc_res (@add_decl E fr f params Hl body res) g = proc_res E g.
 Proof.   
  intros; unfold add_decl, proc_params,proc_body, proc_res; simpl. 
  case_eq (T.eq_dec fr gr); intros; auto.
  clear H0.
  generalize e g H; clear g H; rewrite <- e; intros.
  rewrite (T.UIP_refl e0).
  case_eq (Proc.eq_dec f g); intros; auto.
  elim H; rewrite e1; constructor.
 Qed.
      
 (** ** Semantics of procedure calls *)
 
 Fixpoint init_local_mem (k:nat) (lt1 lt2:list T.type) (lp:var_decl lt1) 
  (lv:dlist (T.interp k) lt2) (m:Mem.t k)  {struct lp} : Mem.t k :=
  match lp, lv with
  | dcons tx tl1 x lp', dcons tv lt2 v lv =>
    let m' := 
     match T.eq_dec tx tv with
     | left Heq =>
       match Heq in (_ = y0) return T.interp k y0 -> Mem.t k with
       | refl_equal => fun v => Mem.upd m x v
       end v
     | right _ => m
     end 
     in init_local_mem lp' lv m'
  | _, _ => m
  end.

 Fixpoint cinit_local_mem (k:nat) (lt1 lt2:list T.type) (lp:var_decl lt1) 
  (lv:dlist (fun t => T.interp k t * nat)%type lt2) (m:Mem.t k) (n:nat)
  {struct lp} : Mem.t k * nat :=
  match lp, lv with
  | dcons tx _ x lp', dcons tv _ vn lv' =>
    let m' := 
     match T.eq_dec tx tv with
     | left Heq =>
       match Heq in (_ = y0) return T.interp k y0 -> Mem.t k with
       | refl_equal => fun v => Mem.upd m x v
       end (fst vn)
     | right _ => m
     end 
     in cinit_local_mem lp' lv' m' (n + snd vn)
  | _, _ => (m, n)
  end.

 Lemma cinit_local_mem_spec : forall k lt2 lt1 lp a (m mi:Mem.t k) n,
  fst (@cinit_local_mem k lt1 lt2 lp (E.ceval_args a mi) m n) =
  @init_local_mem k lt1 lt2 lp (E.eval_args a mi) m.
 Proof.
  intros k; induction lt2; intros lt1 lp a0 m mi n; destruct lp.
  trivial.
  rewrite (T.l_eq_dep_eq (dlist_nil a0)); trivial.
  trivial.
  destruct (dlist_cons a0) as [x1 [y1 H1] ].
  rewrite (T.l_eq_dep_eq H1).
  simpl; rewrite E.ceval_expr_spec; trivial.
 Qed.  

 Definition init_mem k (E:env) fr (f:Proc.proc fr) (a:E.args (Proc.targs f)) 
  (m:Mem.t k) : Mem.t k :=
  let lx := proc_params E f in
  let lv := E.eval_args a m in
  let m' := Mem.global m in
   init_local_mem lx lv m'.

 Definition cinit_mem k (E:env) fr (f:Proc.proc fr) (a:E.args (Proc.targs f)) 
  (m:Mem.t k) : Mem.t k * nat :=
  let lx := proc_params E f in
  let lv := E.ceval_args a m in
  let m' := Mem.global m in
   cinit_local_mem lx lv m' O.

 Lemma cinit_mem_spec_l : forall k E fr f a m,
  fst (@cinit_mem k E fr f a m) = @init_mem k E fr f a m.
 Proof.
  intros; refine (cinit_local_mem_spec _ _ _ _ _).
 Qed.

 Lemma cinit_local_mem_eq : forall k l lp lvn (m1 m2:Mem.t k) n,
  snd (@cinit_local_mem k l l lp lvn m1 n) =
  snd (@cinit_local_mem k l l lp lvn m2 n).
 Proof.
  intros k l lp lvn.
  unfold var_decl in lp.
  induction l; intros.
  rewrite (T.l_eq_dep_eq (dlist_nil lp)).
  rewrite (T.l_eq_dep_eq (dlist_nil lvn)); trivial.
  
  destruct (dlist_cons lp) as [x [lp' Hlp'] ].
  rewrite (T.l_eq_dep_eq Hlp').
  destruct (dlist_cons lvn) as [vn [lvn' Hlvn'] ].
  rewrite (T.l_eq_dep_eq Hlvn').
  simpl.
  case_eq (T.eq_dec a a).
  intros Heq _.
  rewrite (T.UIP_refl Heq); clear Heq.
  apply IHl.

  intros ? W; elim (T.eq_dec_r W); trivial.
 Qed.

 Lemma cinit_local_mem_plus : forall k l lp lvn m n p,
  snd (@cinit_local_mem k l l lp lvn m (n + p))%nat =  
  (snd (@cinit_local_mem k l l lp lvn m n) + p)%nat.
 Proof.
  intros k l lp lvn.
  unfold var_decl in lp.
  induction l; intros.
  rewrite (T.l_eq_dep_eq (dlist_nil lp)).
  rewrite (T.l_eq_dep_eq (dlist_nil lvn)); trivial.  
  destruct (dlist_cons lp) as [x [lp' Hlp'] ].
  rewrite (T.l_eq_dep_eq Hlp').
  destruct (dlist_cons lvn) as [vn [lvn' Hlvn'] ].
  rewrite (T.l_eq_dep_eq Hlvn').
  simpl.
  case_eq (T.eq_dec a a).
  intros Heq _.
  rewrite (T.UIP_refl Heq); clear Heq.
  rewrite plus_comm, plus_assoc, IHl, (plus_comm (snd vn)); trivial.
  intros ? W; elim (T.eq_dec_r W); trivial.
 Qed.

 Lemma cinit_mem_spec_r : forall k E fr f a m,
  snd (@cinit_mem k E fr f a m) =
  dfold_right (fun t vn n => n + snd vn)%nat O (E.ceval_args a m).
 Proof.
  intros k E0 fr f la.
  destruct f; simpl in la.
  unfold cinit_mem.
  generalize O.
  generalize (proc_params E0 (Proc.mkP pname targs tres)); intro lp.
  unfold E.args in la.
  unfold var_decl in lp; simpl in lp.
  induction targs; intros n m.  
  rewrite (T.l_eq_dep_eq (dlist_nil la)).
  rewrite (T.l_eq_dep_eq (dlist_nil lp)); trivial.
  destruct (dlist_cons la) as [e [la' Hla'] ].
  rewrite (T.l_eq_dep_eq Hla').
  destruct (dlist_cons lp) as [x [lp' Hlp'] ].
  rewrite (T.l_eq_dep_eq Hlp').
  simpl.
  case_eq (T.eq_dec a a).
  intros Heq _.
  rewrite (T.UIP_refl Heq); clear Heq.
  rewrite cinit_local_mem_plus.
  rewrite <- (cinit_local_mem_eq lp' (E.ceval_args la' m) (Mem.global m)).
  rewrite IHtargs; trivial.
  intros ? W; elim (T.eq_dec_r W); trivial.
 Qed.


 Definition return_mem k (E:env) tx (x:Var.var tx) (f:Proc.proc tx) 
  (m mf:Mem.t k) : Mem.t k :=
  Mem.upd (Mem.return_mem m mf) x (E.eval_expr (proc_res E f) mf).
 
 Definition creturn_mem k (E:env) tx (x:Var.var tx) (f:Proc.proc tx) 
  (m mf:Mem.t k) : Mem.t k * nat :=
  let vn := E.ceval_expr (proc_res E f) mf in
   (Mem.upd (Mem.return_mem m mf) x (fst vn), snd vn).

 Lemma return_mem_eq : forall k E1 E2 t (f:Proc.proc t) x (m m':Mem.t k),
  proc_res E1 f = proc_res E2 f ->
  return_mem E1 x f m m' = return_mem E2 x f m m'.
 Proof.
  unfold return_mem; intros; rewrite H; trivial.
 Qed.

 Lemma return_mem_dest : forall k E tx (x:Var.var tx) f (m mf:Mem.t k),
  (return_mem E x f m mf) x = E.eval_expr (proc_res E f) mf.
 Proof.
  unfold return_mem; intros.
  apply Mem.get_upd_same.
 Qed.
 
 Lemma return_mem_local : forall k E tx (x:Var.var tx) f (m mf:Mem.t k)
  ty (y:Var.var ty), 
  Var.mkV x <> y -> Var.is_local y -> 
  (return_mem E x f m mf) y = m y.
 Proof.
  unfold return_mem; intros.
  rewrite Mem.get_upd_diff; trivial.
  rewrite Mem.return_mem_local; trivial.
 Qed.
 
 Lemma return_mem_global : forall k E tx (x:Var.var tx) f (m mf:Mem.t k) 
  ty (y:Var.var ty),
  Var.mkV x <> y ->
  Var.is_global y -> (return_mem E x f m mf) y = mf y.
 Proof.
  unfold return_mem; intros.
  rewrite Mem.get_upd_diff; trivial.
  rewrite Mem.return_mem_global; trivial.
 Qed.

 Lemma creturn_mem_spec_l : forall k E t (x:Var.var t) f (m mf:Mem.t k),
  fst (creturn_mem E x f m mf) = return_mem E x f m mf.
 Proof.
  intros; unfold return_mem; rewrite E.ceval_expr_spec; trivial.
 Qed.

 Lemma creturn_mem_spec_r : forall k E t (x:Var.var t) f (m mf:Mem.t k),
  snd (creturn_mem E x f m mf) = snd (E.ceval_expr (proc_res E f) mf).
 Proof.
  trivial.
 Qed.

 Fixpoint get_arg (t:T.type) (x:Var.var t) (lt1 lt2:list T.type) 
  (lv:var_decl lt1) (la:E.args lt2) {struct lv} : option (E.expr t) :=
  match lv, la with
  | dcons t1 lt1 y lv, dcons t2 lt2 e_y la =>
   match get_arg x lv la with
   | Some r => Some r
   | None =>
     if Var.veqb x y then
      match T.eq_dec t2 t with
      | left Heq =>
       match Heq in (_ = y0) return  option (E.expr y0) with
       | refl_equal => Some (e_y)
       end
      | _ => None
      end
     else None
   end
  | _, _ => None
  end.
 
 Lemma get_arg_Some : forall t (x:Var.var t) lt1 (lv:var_decl lt1) lt2 
  (la:E.args lt2) e, 
  get_arg x lv la = Some e -> DIn t x lv.
 Proof.
  induction lv; destruct la; simpl; try (intros; discriminate).
  intros e0; case_eq (get_arg x lv la); [intros r Heq | intros Heq].
  intros; right; eapply IHlv; eauto.
  generalize (Var.veqb_spec_dep x p); destruct (Var.veqb x p); intro Heq'.
  inversion Heq'; subst; simpl.
  left; constructor. 
  intros; discriminate. 
 Qed.

 Lemma get_arg_Some2 : forall t (x:Var.var t) lt1 (lv:var_decl lt1) lt2 
  (la:E.args lt2) e, 
  get_arg x lv la = Some e -> DIn t e la.
 Proof.
  induction lv; simpl; intros.
  discriminate.

  destruct lt2.
  rewrite (T.l_eq_dep_eq (dlist_nil la)) in H; discriminate.
  destruct (dlist_cons la) as [e0 [la' Hla'] ].
  rewrite (T.l_eq_dep_eq Hla') in H |- *.
  case_eq (get_arg x lv la'); [intros r Heq | intros Heq]; rewrite Heq in H.
  injection H; intro; subst; right; auto.

  generalize (Var.veqb_spec_dep x p); destruct (Var.veqb x p); intro Heq'.
  destruct (T.eq_dec t0 t).

  left.
  destruct t; destruct t0; try discriminate.
  injection e1; intros; subst; 
   rewrite (T.UIP_refl e1) in H; injection H; intro; subst; trivial.
  rewrite (T.UIP_refl e1) in H; injection H; intro; subst; trivial.
  rewrite (T.UIP_refl e1) in H; injection H; intro; subst; trivial. 
  rewrite (T.UIP_refl e1) in H; injection H; intro; subst; trivial.
  rewrite (T.UIP_refl e1) in H; injection H; intro; subst; trivial. 
  injection e1; intros; subst;
   rewrite (T.UIP_refl e1) in H; injection H; intro; subst; trivial. 
  injection e1; intros; subst; 
   rewrite (T.UIP_refl e1) in H; injection H; intro; subst; trivial. 
  injection e1; intros; subst;
   rewrite (T.UIP_refl e1) in H; injection H; intro; subst; trivial. 
  injection e1; intros; subst; 
   rewrite (T.UIP_refl e1) in H; injection H; intro; subst; trivial. 
  discriminate.
  discriminate.
 Qed.

 Lemma get_arg_init_local_mem : forall k t (x:Var.var t) lt1 (lv:var_decl lt1) lt2 
  (la:dlist E.expr lt2) (m m' : Mem.t k),
  match get_arg x lv la with
  | Some a =>
    (init_local_mem lv (E.eval_args la m) m') x = E.eval_expr a m
  | None =>
    (init_local_mem lv (E.eval_args la m) m') x = m' x
  end.
 Proof.
  induction lv; simpl; intros; trivial.
  destruct la as [ | a0 l0 e d] ; simpl; trivial.
  generalize (IHlv l0 d).
  case_eq (get_arg x lv d); auto.
  intros Hget Hinit.
  generalize (Var.veqb_spec_dep x p); destruct (Var.veqb x p).
  intros Heq; inversion Heq; subst.
  assert (W:= T.inj_pair2 H2); clear H1 H2; subst.
  simpl. case_eq (T.eq_dec a0 a).
  intros e0; generalize e0 e; clear e; rewrite e0.
  intros e1; rewrite (T.UIP_refl e1).
  intros e _.
  case_eq (T.eq_dec a a); intros.
  rewrite (T.UIP_refl e2).
  rewrite Hinit; apply Mem.get_upd_same.
  elim (T.eq_dec_r H (refl_equal _)).
  intros i Heq'.
  case_eq (T.eq_dec a a0); auto.
  intros.
  rewrite e0 in Heq'; elim (T.eq_dec_r Heq' (refl_equal _)).
  case_eq (T.eq_dec a a0); auto.
  intros e0 _; generalize e0 e; rewrite <- e0.
  intros e1 e2; rewrite (T.UIP_refl e1).
  intros; rewrite Hinit, Mem.get_upd_diff; auto.
  intros Heq; apply H; inversion Heq; constructor.
 Qed.
 
 Lemma lookup_init_mem : forall k E t (f:Proc.proc t) a (m:Mem.t k) 
  tx (x:Var.var tx),
  match get_arg x (proc_params E f) a with
  | Some e => (init_mem E f a m) x = E.eval_expr e m
  | None => (init_mem E f a m) x = Mem.global m x
  end.
 Proof.
  unfold init_mem; intros.
  generalize (get_arg_init_local_mem x (proc_params E f) a m (Mem.global m)).
  destruct (get_arg x (proc_params E f) a); trivial.
 Qed.
 
 Lemma init_mem_global : forall k E t (f:Proc.proc t) a (m:Mem.t k) 
  tx (x:Var.var tx),
  Var.is_global x -> (init_mem E f a m) x = m x.
 Proof.
  intros; unfold init_mem.
  generalize  (get_arg_init_local_mem x (proc_params E f) a m (Mem.global m))
   (get_arg_Some x (proc_params E f) a);
   destruct (get_arg x (proc_params E f) a); intros.
  assert (X:=proc_params_local E f x (H1 _ (refl_equal (Some e)))).
  destruct x; discriminate.
  rewrite H0; symmetry; apply Mem.global_spec; trivial.
 Qed. 

 Lemma init_mem_local : forall k E t (f:Proc.proc t) 
  (a1 a2:E.args (Proc.targs f)) (m1 m2:Mem.t k),
  E.eval_args  a1 m1 = E.eval_args a2 m2 ->
  forall tx (x:Var.var tx), 
   Var.is_local x -> 
   init_mem E f a1 m1 x = init_mem E f a2 m2 x.
 Proof.
  intros; unfold init_mem.
  rewrite H.
  assert (W:forall lt1 (lv:var_decl lt1) lt2 (la:dlist (T.interp k) lt2) 
   (t0 t1 : Mem.t k),
   (forall (tx0 : T.type) (x0 : Var.var tx0),
    Var.is_local x0 -> t0 x0 = t1 x0) ->
   init_local_mem lv la t0 x = init_local_mem lv la t1 x).
  induction lv; simpl; auto.
  destruct la; simpl; auto.
  intros; case_eq (T.eq_dec a a0); auto.
  intros e _; generalize e i; clear i; rewrite <- e.
  intros e0 i; rewrite (T.UIP_refl e0).
  apply IHlv; intros; auto.
  destruct (Var.eq_dec p x0).
  inversion e1; simpl.
  repeat rewrite Mem.get_upd_same; trivial.
  repeat rewrite Mem.get_upd_diff; auto.

  apply W; intros.
  repeat rewrite Mem.global_local; trivial.
 Qed.
 
 Lemma init_mem_eq2 : forall k E1 E2 t (f:Proc.proc t) 
  (a1 a2:E.args (Proc.targs f)) (m:Mem.t k),
  proc_params E1 f = proc_params E2 f ->
  E.eval_args  a1 m = E.eval_args a2 m ->
  init_mem E1 f a1 m = init_mem E2 f a2 m.
 Proof.
  intros; unfold init_mem.
  rewrite H, H0; trivial.
 Qed.

 Lemma init_mem_eq : forall k E t (f:Proc.proc t) 
  (a1 a2:E.args (Proc.targs f)) (m:Mem.t k),
  E.eval_args  a1 m = E.eval_args a2 m ->
  init_mem E f a1 m = init_mem E f a2 m.
 Proof. 
  intros; unfold init_mem.
  rewrite H; trivial.
 Qed.


 (** ** Semantics of basic instructions *)

 Section K.

  Variable k : nat.
  
  Definition base_step i (mn:Mem.t k * nat) : Distr (Mem.t k * nat) :=
   let (m, n) := mn in
    match i with
    | I.Assign t x e => 
      let vn := @E.ceval_expr k t e m in
       Munit (Mem.upd m x (fst vn), n + (snd vn))%nat
    | I.Random t x d =>
      let sn := @E.ceval_support k t d m in
      Mlet (sum_support (T.default k t) (fst sn))
       (fun v => Munit (Mem.upd m x v, (n+snd sn)%nat))
    end.
  
  (** Properties of [base_step] *)

  Ltac ltrivial :=
   intros;
   match goal with 
    | |- context [E.ceval_expr ?E ?M] => destruct (E.ceval_expr E M)    
    | |- context [E.ceval_support ?S ?M] => destruct (E.ceval_support S M)
    | _ => idtac
   end;
   trivial.
  
  Lemma base_step_add_end : forall i m p n f, 
   mu (base_step i (m, p + n)%nat) f = 
   mu (Mlet (base_step i (m, p)) (fun mn' => Munit (fst mn', n + snd mn')%nat)) f.
  Proof.
   destruct i; intros.
   simpl; rewrite plus_assoc, (plus_comm p); trivial.
   rewrite plus_comm.
   simpl; rewrite plus_assoc; trivial.
  Qed.

  Lemma sum_support_lossless : forall t (d:E.support t) (m:Mem.t k),
   mu (sum_support (T.default k t) (@E.eval_support k t d m)) (fun _ => 1) == 1.
  Proof.
   intros.
   refine (sum_support_lossless (T.default k t) _).
   apply E.eval_support_nil.
  Qed.

  Lemma base_step_lossless : forall i m, mu (base_step i m) (fun _ => 1) == 1.
  Proof.
   destruct m as (m,n); destruct i; intros; simpl.   
   trivial.
   rewrite <- E.ceval_support_spec.   
   refine (sum_support_lossless _ _).
  Qed.
  
  Lemma base_step_comm : forall (A:Type) (d:Distr A) b m,
   prod_comm (base_step b m) d.
  Proof.
   destruct b; destruct m; simpl; intros.
   apply prod_comm_Munit.
   apply prod_comm_Mlet; auto using prod_comm_Munit, prod_comm_sum_support.
  Qed.

  Lemma base_step_stable_eq : forall b m f g, 
   f == g ->
   mu (base_step b m) f == mu (base_step b m) g.
  Proof.
   intros; apply (mu_stable_eq (base_step b m) f); trivial.
  Qed.
  
  (** ** Semantic of instructions *)

  Record frame : Type := MkFrame {
   fr_type : T.type;
   fr_desti : Var.var fr_type;
   fr_called : Proc.proc fr_type;
   fr_cont : cmd;
   fr_mem : Mem.t k
  }.

  Record state : Type := MkState {
   st_pc : cmd;
   st_mem : Mem.t k;
   st_stack : list frame
  }.

  Definition final s :=
   match s.(st_pc), s.(st_stack) with
   | nil, nil => true
   | _, _ => false
   end.
  
  Section DENO.
   
   Variable E : env.

   (** First we define one execution step *)
   Definition ceval_test (e:E.expr T.Bool) c1 c2 s n : Distr (state*nat) :=
    let vn := E.ceval_expr e s.(st_mem) in
    Munit ((MkState (if fst vn then c1 else c2)
     s.(st_mem) 
     s.(st_stack)),  
    (n + snd vn)%nat).

   (** One-step executable semantics *)
   Definition step (sn:state*nat) : Distr (state*nat) :=
    let (s,n) := sn in
     match s.(st_pc) with
     | nil => 
      match s.(st_stack) with 
      | nil => Munit sn
      | fr :: l =>
        let mn := creturn_mem E  fr.(fr_desti) fr.(fr_called) fr.(fr_mem) s.(st_mem) in
         Munit (MkState fr.(fr_cont) (fst mn) l, (n+snd mn)%nat)
      end
     | i :: c => 
      match i with
      | I.Instr i => 
       Mlet (base_step i (s.(st_mem), n)) 
        (fun mn => Munit (MkState c (fst mn) s.(st_stack),  snd mn))
      | I.Cond e c1 c2 => ceval_test e (c1++c) (c2++c) s n
      | I.While e c1 => ceval_test e (c1++ i::c) c s n 
      | I.Call t d p a =>
        let mn := cinit_mem E p a s.(st_mem) in
       Munit (MkState 
        (proc_body E p)
        (fst mn)
        (MkFrame d p c s.(st_mem) :: s.(st_stack)), (n+snd mn)%nat) 
      end
     end.
   
   (** Then we define the [n]-unfold of [step] *)
   Fixpoint step_trans (sn:state*nat) (n:nat) {struct n} : Distr (state*nat) :=
    match n with
    | O => Munit sn
    | S n => Mlet (step_trans sn n) step
    end.
   
   Transparent sum_support UP.sigma.
   
   Lemma eval_test_add_end : forall f e c1 c2 s m n,
    mu (ceval_test e c1 c2 s (m + n)%nat) f = 
    mu (ceval_test e c1 c2 s m) (fun s => f (fst s, n + snd s)%nat).
   Proof.
    unfold ceval_test, unit; simpl; intros.
    rewrite plus_assoc, (plus_comm m); trivial.
   Qed.
   
   (** [step] properties *)

   Opaque base_step.

   Lemma step_add_end : forall s m n f, 
    mu (step (s, m + n)%nat) f = 
    mu (Mlet (step (s, m)) (fun s => Munit (fst s, n + snd s)%nat)) f.
   Proof.
    unfold step; intros.
    case_eq (st_pc s); intros.
    case_eq (st_stack s); intros; trivial.
    simpl; rewrite plus_comm; trivial.
    simpl; rewrite plus_assoc, (plus_comm m); trivial.
    destruct i; simpl; unfold star, unit; simpl.
    refine (base_step_add_end _ _ _ _ _).
    rewrite plus_assoc, (plus_comm m); trivial.
    rewrite plus_assoc, (plus_comm m); trivial.
    rewrite plus_assoc, (plus_comm m); trivial.
   Qed.

   Lemma step_lossless : forall s, 
    mu (step s) (fun _ => 1) == 1.
   Proof.
    unfold step; simpl; intros (s,n).
    destruct (st_pc s).
    destruct (st_stack s); trivial.
    destruct i; trivial.
    simpl; unfold star,unit; simpl.
    rewrite base_step_lossless; trivial.
   Qed.

   Lemma step_const_eq : forall s c,
    mu (step s) (fun _ => c) == c.
   Proof.
    intros; change (mu (step s) (UP.fcte _ c) == c).
    rewrite mu_cte; unfold UP.fone; rewrite step_lossless; auto.
   Qed.

   Lemma step_final : forall s,
    final (fst s) = true -> step s = Munit s.
   Proof.
    intros (([ |i c], m, [ |fr l]),n); unfold final; simpl; intro;
     try discriminate; reflexivity.
   Qed.

   Lemma step_stable_eq : forall s f g, 
    f == g ->
    mu (step s) f == mu (step s) g.
   Proof.
    intros; apply (mu_stable_eq (step s) f g); trivial.
   Qed.


   (** [step_trans] properties *)
   
   Lemma step_trans_O : forall s, step_trans s O = Munit s.
   Proof. 
    trivial.
   Qed.

   Lemma step_trans_S : forall s n f,
    mu (step_trans s (S n)) f =
    mu (Mlet (step_trans s n) (fun s' => step_trans s' (S O))) f.
   Proof. 
    trivial.
   Qed.
     
   Lemma step_trans_step : forall n s f,
    mu (step_trans s (S n)) f == 
    mu (Mlet (step s) (fun s' => step_trans s' n )) f.
   Proof.
    induction n; intros; simpl; trivial.
    apply step_stable_eq; trivial.
    simpl; apply ford_eq_intro; trivial.
    refine (IHn _ _).
   Qed.

   Lemma step_trans_stable_eq : forall n s f g, 
    f == g ->
    mu (step_trans s n) f == mu (step_trans s n) g.
   Proof.
    intros; apply (mu_stable_eq (step_trans s n) f g); trivial.
   Qed.

   Lemma step_trans_final: forall s n f , 
    final (fst s) = true -> mu (step_trans s n) f = mu (Munit s) f.
   Proof.
    induction n; simpl; intros; auto.
    rewrite IHn; trivial. 
    simpl; rewrite (step_final s H); trivial.
   Qed.

   Opaque step.

   Lemma step_trans_add_end: forall p s m n f,
    mu (step_trans (s, m + n)%nat p) f == 
    mu (Mlet (step_trans (s, m) p) (fun s => Munit (fst s, snd s + n)%nat)) f.
   Proof.
    induction p; simpl; intros.
    trivial.
    rewrite IHp; simpl.
    apply step_trans_stable_eq.
    simpl; apply ford_eq_intro; intros [s' n'].
    rewrite (@step_add_end s' n').
    simpl; apply step_stable_eq.
    refine (ford_eq_intro _); intro.
    rewrite plus_comm; trivial.
   Qed.

   Transparent step.
   Opaque base_step.

   Lemma step_trans_base : forall i m N n f,
    mu (step_trans ((MkState (I.Instr i :: nil) m nil),N) (S n)) f ==
    mu (Mlet (base_step i (m,N)) 
     (fun mn => Munit (MkState nil (fst mn) nil, snd mn))) f.
   Proof.
    intros; rewrite step_trans_step; simpl.
    apply base_step_stable_eq. 
    simpl; apply ford_eq_intro.
    intro; rewrite step_trans_final; trivial.
   Qed.

   Transparent base_step.

   Lemma step_trans_step_comm : forall s n f,
    mu (Mlet (step_trans s n) step) f ==
    mu (Mlet (step s) (fun s' => step_trans s' n)) f.
   Proof with trivial.
    induction n; intros; simpl.
    apply step_stable_eq ...
    simpl; apply ford_eq_intro...
    simpl in IHn; rewrite IHn...
   Qed.
   
   (* Given a state, appends a stack and a command as a continuation *)
   
   Fixpoint append_frame (fr:frame) (l1:list frame) (c:cmd) (l2:list frame) 
    {struct l1} : list frame :=
    match l1 with
    | nil => 
     (MkFrame 
      fr.(fr_desti)
      fr.(fr_called) 
      (fr.(fr_cont)++c)
      fr.(fr_mem)) :: l2
    | fr' :: l => fr :: (append_frame fr' l c l2)
    end.
   
   Definition append s c l :=
    match s.(st_stack) with
    | nil => MkState (s.(st_pc) ++ c) s.(st_mem) l
    | fr::l' => MkState s.(st_pc) s.(st_mem) (append_frame fr l' c l)
    end.
   
   Lemma append_final : forall s c l, 
    final s = true ->
    append s c l = MkState c s.(st_mem) l.
   Proof.
    intros ([ | i c'], m, [ | fr l']) c l H; try discriminate H; trivial.
   Qed.
   
   Lemma append_not_final : forall s c l, 
    final s = false ->
    final (append s c l) = false.
   Proof.
    intros ([ | i c'], m, [ | fr l']) c l H; try discriminate H; trivial.
    unfold append; simpl.
    clear H; case_eq (append_frame fr l' c l); intros; trivial.
    destruct l'; try discriminate H.
   Qed.

   Lemma step_trans_append_not_final : forall s c l n f, 
    final (fst s) = false ->
    mu (Mlet (step s) (fun s => step_trans (append (fst s) c l, snd s) n)) f ==
    mu (step_trans (append (fst s) c l, snd s) (S n)) f.
   Proof.
    intros; rewrite step_trans_step.
    apply eq_distr_elim. 
    destruct s as (([ | i c'], m, l'),n1).
    destruct l' as [ | fr l'].
    discriminate H.
    unfold append at 2; simpl.
    eapply Oeq_trans;[apply Mlet_unit | ].
    destruct l'; unfold step; simpl; rewrite Mlet_unit; trivial.
    destruct i as [ i | e c1 c2 | e c1 | dest' p args'].
    apply eq_distr_intro; destruct l'; trivial.
    destruct l'; unfold step; simpl.
    unfold ceval_test; simpl.
    destruct (fst (A:=bool) (E.ceval_expr e m)); 
     repeat rewrite Mlet_unit; simpl; trivial.
    unfold append; simpl; rewrite app_ass; trivial.
    unfold append; simpl; rewrite app_ass; trivial.
    unfold ceval_test; simpl.
    destruct (fst (A:=bool) (E.ceval_expr e m)); 
     repeat rewrite Mlet_unit; trivial.
    destruct l'; unfold step; simpl.
    unfold ceval_test; simpl.
    destruct (fst (A:=bool) (E.ceval_expr e m)); 
     repeat rewrite Mlet_unit; trivial.
    unfold append; simpl; rewrite app_ass; trivial.
    unfold append, ceval_test; simpl.
    destruct (fst (A:=bool) (E.ceval_expr e m)); 
     repeat rewrite Mlet_unit; trivial.
    destruct l'; unfold step; simpl; destruct proc_body; auto. 
   Qed.

   Lemma step_trans_append_final : forall s c l n f, 
    final (fst s) = true ->
    mu (Mlet (step s) (fun s => step_trans (append (fst s) c l, snd s) n)) f ==
    mu (step_trans (append (fst s) c l, snd s) n) f.
   Proof.
    intros (([ |i c'], m, [ | fr l']),n1) c l n f H; try discriminate H.
    rewrite step_final; trivial; rewrite Mlet_unit; trivial.
   Qed.

   
   (** Distribution of final memories reacheable in at most [n] steps *)
   
   Definition step_star (s:state*nat) : natO -m> Distr (Mem.t k*nat).
    intros s.
    refine (@mk_fmono _ _ 
      (fun (n:natO) => 
        Mlet (drestr (step_trans s n) (fun sn => final (fst sn)))
          (fun sn => Munit ((fst sn).(st_mem), snd sn))) _).
    unfold monotonic; intros; generalize s; clear s.
    induction H; intros; auto.
    refine (Ole_trans (IHle s) _).
    simpl; intros; apply (mu_monotonic (step_trans s m)); simpl.
    clear H m IHle s. 
    intros (([ | i c], m, fr),n'); simpl; trivial.
    destruct fr as [ | fr l]; simpl; trivial.
   Defined.

   Hint Unfold step_star.
   
  (** [step_star] properties *)
   
   Lemma step_star_stable_eq : forall s n f g, 
    f == g -> 
    mu (step_star s n) f == mu (step_star s n) g.
   Proof.
    intros; apply (mu_stable_eq (step_star s n)); trivial.
   Qed.
   
   Lemma step_star_add_end : forall s m n p f, 
    mu (step_star (s, m + n)%nat p) f == 
    mu (Mlet (step_star (s, m) p) (fun s => Munit (fst s, n + snd s)%nat)) f.
   Proof.
    intros; simpl.
    rewrite step_trans_add_end; simpl.
    apply step_trans_stable_eq; intros.
    refine (ford_eq_intro _); intros (s', n').
    simpl; destruct (final s'); simpl; trivial.
    rewrite plus_comm; trivial.
   Qed.
   
   Lemma step_star_O : forall s f,
    mu (step_star s O) f = 
    if final (fst s) then f ((fst s).(st_mem),snd s) else 0.
   Proof.
    simpl; intros.
    destruct (final (fst s)); trivial.
   Qed.
   
   Lemma step_star_S : forall s n f,
    mu (step_star s (S n)) f == 
    mu (Mlet (step_trans s n) (fun s' => step_star s' (S O))) f.
   Proof. 
    intros; trivial. 
   Qed.
   
   Lemma step_star_step : forall s n f, 
    mu (step_star s (S n)) f == mu (Mlet (step s) (fun s' => step_star s' n)) f.
   Proof. 
    intros; refine (step_trans_step _ _ _). 
   Qed.

   Lemma step_star_final : forall s n f,
    final (fst s) = true -> 
    mu (step_star s n) f == mu (Munit ((fst s).(st_mem),snd s)) f.
   Proof.
    intros s n f H; simpl.
    rewrite (step_trans_final s); trivial.
    simpl; rewrite H; trivial.
   Qed.
   
   Lemma step_star_append_not_final: forall s c l n f, 
    final (fst s) = false ->
    mu (Mlet (step s) (fun s => step_star (append (fst s) c l, snd s) n)) f ==
    mu (step_star (append (fst s) c l, snd s) (S n)) f.
   Proof.
    intros; refine (step_trans_append_not_final _ _ _ _ _ _); trivial.
   Qed.
   
   Lemma step_star_append_final: forall s c l n f, 
    final (fst s) = true ->
    mu (Mlet (step s) (fun s => step_star (append (fst s) c l, snd s) n)) f ==
    mu (step_star (append (fst s) c l, snd s) n) f.
   Proof.
    intros; refine (step_trans_append_final _ _ _ _ _ _); trivial.
   Qed.
   
   Opaque step.
   
   Lemma step_star_append : forall f f' c1 c2 lf1 lf2 n s cost,
    (forall n' cost' M, (n' <= n)%nat ->
     mu (step_star (MkState c1 M lf1, cost') n') f <= 
     mu (step_star (MkState c2 M lf2, cost') n') f') ->
    mu (step_star (append s c1 lf1, cost) n) f <= 
    mu (step_star (append s c2 lf2, cost) n) f'.
   Proof.
    induction n; intros.
    case_eq (final s); intros.
    repeat rewrite append_final; auto with arith.
    repeat rewrite step_star_O; unfold fst.
    repeat rewrite append_not_final; trivial.
    case_eq (final s); intros.
    repeat rewrite append_final; auto with arith.
    change s with (fst (s,cost)). 
    change cost with (snd (s,cost)); unfold snd at 1 3. 
    repeat rewrite <- step_star_append_not_final; trivial.
    simpl; refine (mu_monotonic _ _ _ _); intro.
    refine (IHn _ _ _); auto.
   Qed.
   
   Opaque step_star.
   
   Lemma step_star_append_lub : forall s c lf cost f,
    mu (Lub (cDistr (Mem.t k*nat)) (step_star (append s c lf, cost))) f ==
    mu (Mlet (Lub (cDistr (Mem.t k*nat)) (step_star (s, cost))) 
     (fun mc => Lub (cDistr (Mem.t k*nat)) (step_star (MkState c (fst mc) lf, snd mc)))) f.
   Proof.
    split; simpl.   
    
    apply lub_le_compat; simpl; intro n.
    generalize s c lf cost f; clear s c lf cost f; induction n; intros.
    rewrite (step_star_O (s,cost)) ; simpl.
    case_eq (final s); intros.
    rewrite append_final; trivial.
    exact (le_lub ((Mu (Mem.t k* nat) @ step_star (MkState c (st_mem s) lf, cost)) <_> f) O).
    rewrite step_star_O.
    simpl; rewrite append_not_final; auto.
    case_eq (final s); intros.
    rewrite (step_star_final (s,cost)); trivial.
    rewrite append_final; trivial; simpl.
    exact (le_lub ((Mu (Mem.t k* nat) @ step_star (MkState c (st_mem s) lf, cost)) <_> f) (S n)).

    assert (X := step_star_append_not_final (s,cost) c lf n f H);
     simpl fst in X; simpl snd in X.
    rewrite <- X.
    rewrite step_star_step; simpl.
    apply (mu_monotonic (step (s, cost))); intros (s',n').
    simpl; apply IHn.

    apply lub_le; intros; simpl.
    assert (monotonic (O1:=natO) (O2:=(Mem.t k* nat) -o> U)
     (fun (n0 : natO) (x : Mem.t k* nat) => mu (step_star (MkState c (fst x) lf, snd x) n0) f)).
    unfold monotonic; simpl; intros.
    apply (fmonotonic (step_star (MkState c (fst x0) lf, snd x0))); trivial.
    assert (X:= mu_continuous ((step_star (s, cost) n))
     (mk_fmono H)); simpl in X.
    eapply Ole_trans; [ | eapply Ole_trans; [ apply X | ]].
    apply (mu_monotonic (step_star (s,cost) n)); intro.
    apply lub_le_compat; intro; trivial.
    clear X.
    transitivity 
     (lub (c:=U) (mseq_lift_left (O:=U) ((Mu (Mem.t k* nat) @ step_star (append s c lf, cost)) <_> f) n)).
    apply lub_le_compat; simpl.
    generalize s cost; clear s cost; induction n; intros.
    rewrite step_star_O; simpl.
    case_eq (final s); intro; auto.
    rewrite append_final; trivial.
    case_eq (final s); intro.
    rewrite step_star_final; simpl; trivial.
    rewrite append_final; trivial.
    apply (fmonotonic (step_star (MkState c (st_mem s) lf, cost))); auto with zarith.
    assert (X:= step_star_append_not_final (s,cost) c lf (n+x)%nat f H0).
    simpl in X; rewrite <- X.
    rewrite step_star_step; simpl.
    apply (mu_monotonic (step (s,cost))); intro.
    destruct x0; apply IHn.
    apply Oeq_le.
    symmetry; apply lub_lift_left.
   Qed.

   Transparent step_star step.

   Hint Resolve step_star_O step_star_S.

  (** [step_star] equations *)
   Opaque step_trans.

   Lemma step_star_base : forall i m n cost f,
    mu (step_star (MkState (I.Instr i :: nil) m nil, cost) (S n)) f == 
    mu (base_step i (m,cost)) f.
   Proof.
    intros; simpl.
    rewrite step_trans_base.
    simpl; apply (base_step_stable_eq i (m,cost)).
    simpl; apply ford_eq_intro; intro x; destruct x; trivial.
   Qed.

   Transparent step_trans.

   Lemma step_star_nil : forall p m n f, 
    mu ((step_star (MkState nil m nil, n) p)) f == mu (Munit (m,n)) f.
   Proof.
    intros; refine (step_star_final _ _ _ _); trivial.
   Qed.

   Lemma step_star_cond_t : forall p (b:E.expr T.Bool) c1 c2 m n f,
    E.eval_expr b m = true ->
    mu ((step_star (MkState ((If b then c1 else c2)::nil) m nil, n) (1+p)%nat)) f ==
    mu ((step_star (MkState c1 m nil, (n+snd (E.ceval_expr b m))%nat) p)) f.
   Proof. 
    intros; simpl plus. 
    rewrite step_star_step; unfold step; simpl.
    assert (W:=E.ceval_expr_spec b m); simpl in W; rewrite <- W.
    simpl; rewrite H.
    rewrite <- app_nil_end; auto.
   Qed.

   Lemma step_star_cond_f : forall p (b:E.expr T.Bool) c1 c2 m n f,
    E.eval_expr b m = false ->
    mu (step_star (MkState ((If b then c1 else c2)::nil) m nil, n) (1+p)%nat) f ==
    mu (step_star (MkState c2 m nil, (n+snd (E.ceval_expr b m))%nat) p) f.
   Proof.
    intros; simpl plus; rewrite step_star_step; unfold step; simpl.
    assert (W:=E.ceval_expr_spec b m); simpl in W; rewrite <- W.
    rewrite H.
    rewrite <- app_nil_end; auto.
   Qed.

   Lemma step_star_while : forall p b c m n f, 
    mu (step_star (MkState ((while b do c)::nil) m nil, n) (1+p)%nat) f ==
    mu (step_star (MkState ((If b _then (c++(while b do c)::nil))::nil) m nil, n) (1+p)%nat) f.
   Proof.
    intros; simpl plus at 1; rewrite step_star_step; trivial.
    unfold step, st_pc, st_stack, ceval_test, st_mem. 
    case_eq (fst (E.ceval_expr b m)); intros.
    rewrite step_star_cond_t; trivial.
    rewrite E.ceval_expr_spec; trivial.
    rewrite step_star_cond_f; trivial. 
    rewrite E.ceval_expr_spec; trivial.
   Qed.
 
  End DENO.
   
  (** Denotational semantics for commands *)

  Definition cdeno (c:cmd) (E:env) (m:Mem.t k*nat) : Distr (Mem.t k*nat) :=
   Lub (cDistr (Mem.t k*nat)) (step_star E (MkState c (fst m) nil, snd m)).
 
  Definition deno (c:cmd) (E:env) (m:Mem.t k) : Distr (Mem.t k) :=
   Mlet (cdeno c E (m,0%nat)) (fun mn => Munit (fst mn)).

  Notation "'[[[' c ']]]'" := (cdeno c) (at level 59, format "[[[  c  ]]]").
  Notation "'[[' c ']]'" := (deno c) (at level 59, format "[[  c  ]]").

  Hint Unfold cdeno deno.

  Section DENO_FACTS. 
   
   Variable E : env.

   Lemma step_star_le_cdeno : forall c m p n f,
    mu (step_star E (MkState c m nil, p) n) f <= mu ([[[c]]] E (m,p)) f.
   Proof.
    simpl; intros.
    refine 
     (@le_lub (cDistr (Mem.t k*nat)) (step_star E (MkState c m nil, p)) n f).
   Qed.
   
   Lemma step_star_cdeno_lub : forall d c m p f,
    (forall n, step_star E (MkState c m nil, p) n <= d) ->
    mu ([[[c]]] E (m,p)) f <= mu d f.
   Proof.
    simpl; intros.
    apply lub_le; auto.
   Qed.

   Hint Resolve step_star_le_cdeno step_star_cdeno_lub.
   
   Lemma cdeno_stable_eq : forall c m n f g, 
    f == g -> mu ([[[c]]] E (m,n)) f == mu ([[[c]]] E (m,n)) g.
   Proof.
    intros; apply (mu_stable_eq ([[[c]]] E (m,n))); trivial.
   Qed.

   Lemma deno_stable_eq : forall c m f g, 
    f == g -> mu ([[c]] E m) f == mu ([[c]] E m) g.
   Proof.
    intros; apply (mu_stable_eq ([[c]] E m)); trivial.
   Qed.

   Opaque step_star base_step.

   Lemma cdeno_base_elim : forall i mn f, 
    mu ([[[ [I.Instr i] ]]] E mn) f == mu (base_step i mn) f.
   Proof.
    intros i (m,n) f.
    apply Ole_antisym.
    simpl; apply lub_le; intro p. 
    rewrite <- (step_star_base E i m p n f); simpl.
    apply (fmonotonic (step_star E (MkState [I.Instr i] m nil, n)));
     auto with arith.
    rewrite <- (step_star_base E i m O n).     
    apply (@le_lub (cDistr (Mem.t k * nat)) 
     (step_star E (MkState [I.Instr i] m nil, n)) 1%nat).
   Qed.

   Transparent step_star base_step.

   Lemma cdeno_base : forall i mn,
    [[[ [I.Instr i] ]]] E mn == base_step i mn.
   Proof.
    intros i (m,n); apply eq_distr_intro; intro f.
    apply cdeno_base_elim.
   Qed.

   Lemma deno_base_elim : forall i m f,
    mu ([[ [I.Instr i] ]] E m) f == 
    mu (base_step i (m, 0%nat)) (fun mn => f (fst mn)). 
   Proof.
    intros i m f; rewrite <- cdeno_base_elim; trivial.    
   Qed.

   Lemma deno_base : forall i m,
    [[ [I.Instr i] ]] E m == 
    Mlet (base_step i (m, 0%nat)) (fun mn => Munit (fst mn)). 
   Proof.
    intros i m; apply eq_distr_intro; intro f.
    refine (deno_base_elim _ _ _).
   Qed.

   Lemma cdeno_assign_elim : forall t (x:Var.var t) e mn f,
    mu ([[[ [x <- e] ]]] E mn) f == 
    let (v,n) := E.ceval_expr e (fst mn) in
    f (fst mn{!x <-- v!}, snd mn + n)%nat.
   Proof.
    intros t x e (m,n) f.
    rewrite cdeno_base_elim; simpl.
    case (E.ceval_expr e m); trivial.
   Qed.

   Lemma cdeno_assign : forall t (x:Var.var t) e mn,
    [[[ [x <- e] ]]] E mn == 
    let (v,n) := E.ceval_expr e (fst mn) in
    Munit (fst mn{!x <-- v!}, snd mn + n)%nat.
   Proof.
    intros t x e (m,n); apply eq_distr_intro; intro f.
    rewrite cdeno_base_elim.    
    simpl; case (E.ceval_expr e m); trivial.
   Qed.

   Lemma deno_assign_elim : forall t (x:Var.var t) e m f,
    mu ([[ [x <- e] ]] E m) f == 
    f (m{! x <-- E.eval_expr e m !}).
   Proof.
    intros t x e m f.
    rewrite deno_base_elim, E.ceval_expr_spec; trivial.
   Qed.

   Lemma deno_assign : forall t (x:Var.var t) e m,
    [[ [x <- e] ]] E m == Munit (m{! x <-- E.eval_expr e m !}).
   Proof.
    intros t x e m; apply eq_distr_intro; intro f.
    rewrite deno_assign_elim; trivial.
   Qed.

   Lemma cdeno_random_elim : forall t (x:Var.var t) s mn f,
    mu ([[[ [x <$- s] ]]] E mn) f ==
    let (s,n) := E.ceval_support s (fst mn) in
     mu (sum_support (T.default k t) s)
      (fun v => f (fst mn {!x <-- v!}, snd mn + n))%nat.
   Proof.
    intros t x s (m,n) f.
    rewrite cdeno_base_elim.
    simpl; case (E.ceval_support s m); trivial.
   Qed.

   Lemma cdeno_random : forall t (x:Var.var t) s mn,
    [[[ [x <$- s] ]]] E mn ==
    let (s,n) := E.ceval_support s (fst mn) in
     Mlet (sum_support (T.default k t) s)      
     (fun v => Munit (fst mn {!x <-- v!}, snd mn + n))%nat.
   Proof.
    intros t x s (m,n); apply eq_distr_intro; intro f.
    rewrite cdeno_base_elim.    
    simpl; case (E.ceval_support s m); trivial.
   Qed.

   Lemma deno_random_elim : forall t (x:Var.var t) s m f,
    mu ([[ [x <$- s] ]] E m) f== 
    mu (sum_support (T.default k t) (E.eval_support s m))
     (fun v => f (m{!x <-- v!})).
   Proof.
    intros t x s m f.
    rewrite deno_base_elim, E.ceval_support_spec; trivial.
   Qed.

   Lemma deno_random : forall t (x:Var.var t) s m,
    [[ [x <$- s] ]] E m == 
    Mlet (sum_support (T.default k t) (E.eval_support s m)) 
     (fun v => Munit (m{!x <-- v!})).
   Proof.
    intros t x s m; apply eq_distr_intro; intro f.
    rewrite deno_random_elim; trivial.
   Qed.

   Opaque step_star.
   
   Lemma cdeno_nil_elim : forall mn f,
    mu ([[[nil]]] E mn) f == f mn.
   Proof.
    intros (m,n) f; split.
    simpl; apply lub_le; intros; simpl.
    rewrite step_star_nil; trivial.    
    refine (le_lub ((Mu (Mem.t k * nat) @ 
     step_star E (MkState nil m nil, n)) <_> f) 1%nat).
   Qed.

   Transparent step_star.

   Lemma cdeno_nil : forall mn,
    [[[nil]]] E mn == Munit mn.
   Proof.
    intros (m,n); apply eq_distr_intro; intro f.
    rewrite cdeno_nil_elim; trivial.
   Qed.

   Lemma deno_nil_elim : forall m f,
    mu ([[nil]] E m) f == f m.
   Proof.
    intros m f; unfold deno.
    refine (cdeno_nil_elim _ _).
   Qed.

   Lemma deno_nil : forall m, 
    [[nil]] E m == Munit m.
   Proof.
    intros m; apply eq_distr_intro; intro f.
    refine (deno_nil_elim _ _).
   Qed.

   Lemma cdeno_cons_elim : forall i c mn f,
    mu ([[[ i::c ]]] E mn) f == 
    mu (Mlet ([[[ [i] ]]] E mn) ([[[c]]] E)) f.
   Proof.
    intros i c (m,n) f.
    unfold cdeno; simpl fst.
    change (MkState (i :: c) m nil) with (append (MkState [i] m nil) c nil).
    apply step_star_append_lub.
   Qed. 

   Lemma cdeno_cons : forall i c mn,
    [[[ i::c ]]] E mn == 
    Mlet ([[[ [i] ]]] E mn) ([[[c]]] E).
   Proof.
    intros i c (m,n); apply eq_distr_intro; intro f.
    apply cdeno_cons_elim.
   Qed.

   Opaque step_star. 

   Lemma cdeno_add_end : forall c m n p f,
    mu ([[[c]]] E (m, n + p)%nat) f == 
    mu ([[[c]]] E (m, n)) (fun mn' => f (fst mn', p + snd mn')%nat).
   Proof.
    unfold cdeno; intros.
    simpl; apply lub_eq_compat. 
    refine (@ford_eq_intro _ _ _ _ _).
    simpl; intros.
    refine (step_star_add_end _ _ _ _ _ _).
   Qed.

   Transparent step_star.

   Lemma deno_cons_elim : forall i c m f,
    mu ([[i::c]] E m) f == mu (Mlet ([[ [i] ]] E m) ([[c]] E)) f.
   Proof.
    intros i c m f.
    unfold deno; rewrite Mlet_simpl.
    rewrite cdeno_cons_elim.  
    repeat rewrite Mlet_simpl.
    apply cdeno_stable_eq.
    refine (ford_eq_intro _); intros (m',n').
    rewrite Munit_eq, Mlet_simpl.
    change n' with (O + n')%nat.
    rewrite cdeno_add_end; trivial.
   Qed.

   Lemma deno_cons : forall i c m,
    [[i::c]] E m == Mlet ([[ [i] ]] E m) ([[c]] E).
   Proof.
    intros; apply eq_distr_intro; intro.
    apply deno_cons_elim.
   Qed.

   Lemma cdeno_app_elim : forall c1 c2 mn f,
    mu ([[[c1 ++ c2]]] E mn) f == 
    mu (Mlet ([[[c1]]] E mn) ([[[c2]]] E)) f.
   Proof.
    intros i c (m,n) f; unfold cdeno; simpl fst; simpl snd.
    change (MkState (i++c) m nil) with (append (MkState i m nil) c nil).
     apply step_star_append_lub.
   Qed.

   Lemma cdeno_app : forall c1 c2 mn,
    [[[c1 ++ c2]]] E mn == Mlet ([[[c1]]] E mn) ([[[c2]]] E).
   Proof.
    intros c1 c2 mn; apply eq_distr_intro; intro f.
    apply cdeno_app_elim.
   Qed.
 
   Lemma deno_app_elim : forall c1 c2 mn f, 
    mu ([[c1 ++ c2]] E mn) f == 
    mu ([[ c1 ]] E mn) (fun mn' => mu ([[c2]] E mn') f).
   Proof. 
    intros c1 c2 mn f; unfold deno.
    repeat rewrite Mlet_simpl.
    rewrite cdeno_app_elim, Mlet_simpl.
    apply cdeno_stable_eq.
    refine (@ford_eq_intro _ _ _ _ _); intros (m, n).        
    change n with (O + n)%nat.
    rewrite cdeno_add_end; trivial.
   Qed.

   Lemma deno_app : forall c1 c2 m, 
    [[c1 ++ c2]] E m == Mlet ([[c1]] E m) ([[c2]] E).
   Proof.
    intros c1 c2 m; apply eq_distr_intro; intro f.
    refine (deno_app_elim _ _ _ _).
   Qed.

   Opaque step_star.

   Lemma cdeno_cond_t_elim : forall (e:E.expr T.Bool) c1 c2 mn f,
    E.eval_expr e (fst mn) = true ->
    mu ([[[ [If e then c1 else c2] ]]] E mn) f ==
    mu ([[[c1]]] E (fst mn, snd mn + snd (E.ceval_expr e (fst mn)))%nat) f.
   Proof.
    unfold cdeno; intros e c1 c2 mn f.
    rewrite E.ceval_expr_spec.
    case (E.ceval_expr_spec e (fst mn)); intro Heq.
    transitivity 
     (lub (c:=U) (mseq_lift_left (O:=U) ((Mu (Mem.t k * nat) @
      step_star E (MkState [If e then c1 else c2] (fst mn) nil, snd mn)) <_> f) 1%nat)).
    simpl; apply lub_lift_left.
    simpl; apply lub_eq_compat.
    refine (@ford_eq_intro _ _ _ _ _); intro p.

    intros; simpl.
    change (S p) with (1+p)%nat.
    rewrite step_star_cond_t; trivial.
   Qed.

   Lemma cdeno_cond_f_elim : forall (e:E.expr T.Bool) c1 c2 mn f,
    E.eval_expr e (fst mn) = false ->
    mu ([[[ [If e then c1 else c2] ]]] E mn) f ==
    mu ([[[c2]]] E (fst mn, snd mn + snd (E.ceval_expr e (fst mn)))%nat) f.
   Proof.
    unfold cdeno; intros e c1 c2 mn f.
    rewrite E.ceval_expr_spec.
    case (E.ceval_expr_spec e (fst mn)); intro Heq.
    transitivity 
     (lub (c:=U) (mseq_lift_left (O:=U) ((Mu (Mem.t k * nat) @
      step_star E (MkState [If e then c1 else c2] (fst mn) nil, snd mn)) <_> f) 1%nat)).
    simpl; apply lub_lift_left.
    simpl; apply lub_eq_compat.
    refine (@ford_eq_intro _ _ _ _ _); intro p.

    intros; simpl.
    change (S p) with (1+p)%nat.
    rewrite step_star_cond_f; trivial.
   Qed.

   Lemma cdeno_cond_elim : forall e c1 c2 mn f,
    mu ([[[ [If e then c1 else c2] ]]] E mn) f ==
    let (b,n) := E.ceval_expr e (fst mn) in
     mu (if b then [[[c1]]] E (fst mn, snd mn + n)%nat 
              else [[[c2]]] E (fst mn, snd mn + n)%nat) f.
   Proof.
    intros e c1 c2 mn f; case_eq (E.ceval_expr e (fst mn)).
    intro b; case b; intros.
    rewrite cdeno_cond_t_elim.  
    rewrite H; trivial.
    rewrite E.ceval_expr_spec, H; trivial.
    rewrite cdeno_cond_f_elim.    
    rewrite H; trivial.
    rewrite E.ceval_expr_spec, H; trivial.
   Qed.

   Lemma cdeno_cond : forall e c1 c2 (mn:Mem.t k * nat),
    [[[ [If e then c1 else c2] ]]] E mn ==
    let (b,n) := E.ceval_expr e (fst mn) in
    if b then [[[c1]]] E (fst mn, snd mn + n)%nat
         else [[[c2]]] E (fst mn, snd mn + n)%nat.
   Proof.
    intros e c1 c2 mn; apply eq_distr_intro; intro f.
    rewrite cdeno_cond_elim; case (E.ceval_expr e (fst mn)); trivial.
   Qed.

   Lemma deno_cond_t_elim : forall (e:E.expr T.Bool) c1 c2 m f, 
    E.eval_expr e m = true -> 
    mu ([[ [If e then c1 else c2] ]] E m) f == mu ([[c1]] E m) f.
   Proof. 
    intros; unfold deno.
    rewrite Mlet_simpl.
    rewrite cdeno_cond_t_elim; [ | trivial].
    rewrite Mlet_simpl, cdeno_add_end; trivial.
   Qed.

   Lemma deno_cond_f_elim : forall (e:E.expr T.Bool) c1 c2 m f, 
    E.eval_expr e m = false -> 
    mu ([[ [If e then c1 else c2] ]] E m) f == mu ([[c2]] E m) f.
   Proof. 
    intros; unfold deno.
    rewrite Mlet_simpl.
    rewrite cdeno_cond_f_elim; [ | trivial].
    rewrite Mlet_simpl, cdeno_add_end; trivial.
   Qed.

   Lemma deno_cond_elim : forall (e:E.expr T.Bool) c1 c2 m f,
    mu ([[ [If e then c1 else c2] ]] E m) f == 
    mu (if E.eval_expr e m then [[c1]] E m else [[c2]] E m) f.
   Proof. 
    intros e c1 c2 m f.
    case_eq (E.eval_expr e m); intro H.
    rewrite deno_cond_t_elim; trivial.
    rewrite deno_cond_f_elim; trivial.
   Qed.

   Lemma deno_cond : forall (e:E.expr T.Bool) c1 c2 m,
    [[ [ If e then c1 else c2] ]] E m == 
    if E.eval_expr e m then ([[c1]] E m) else ([[c2]] E m).
   Proof.
    intros e c1 c2 m; apply eq_distr_intro; intro f.
    apply deno_cond_elim.
   Qed.

   Lemma deno_cond_nil_elim : forall (e:E.expr T.Bool) m f,
     mu (([[ [If e _then nil] ]]) E m) f == f m.
   Proof.
     intros.
     rewrite deno_cond_elim.
     case (E.eval_expr e m); rewrite deno_nil_elim; trivial.
   Qed.

   Lemma cdeno_while_elim : forall e c mn f, 
    mu ([[[ [while e do c] ]]] E mn) f == 
    mu ([[[ [If e _then (c ++ [while e do c])] ]]] E mn) f.
   Proof.
    simpl; intros.
    apply lub_eq_compat; intros.
    refine (ford_eq_intro _); intro n.
    destruct n. 
    trivial.
    refine (step_star_while _ _ _ _ _ _ _).
   Qed.

   Lemma cdeno_while : forall e c mn, 
    [[[ [while e do c] ]]] E mn == 
    [[[ [If e _then (c ++ [while e do c])] ]]] E mn.
   Proof.
    intros e c mn; apply eq_distr_intro; intro f.
    apply cdeno_while_elim.
   Qed.

   Lemma deno_while_elim : forall e c m f, 
    mu ([[ [while e do c] ]] E m) f == 
    mu ([[ [If e _then (c ++ [while e do c])] ]] E m) f.
   Proof.
    intros e c m f; unfold deno.
    rewrite Mlet_simpl, cdeno_while_elim; trivial.
   Qed.

   Lemma deno_while : forall e c m, 
    [[ [while e do c] ]] E m == [[ [If e _then (c ++ [while e do c])] ]] E m.
   Proof.
    intros e c m; apply eq_distr_intro; intro f.
    apply deno_while_elim.
   Qed.
   
   Lemma deno_while_false_elim : forall (e:E.expr T.Bool) c m f,
    E.eval_expr e m = false ->
    mu ([[ [while e do c] ]] E m) f == f m.
   Proof.
    intros.
    rewrite deno_while_elim, deno_cond_elim, H.
    apply deno_nil_elim.
   Qed.

   Lemma deno_call_unfold : forall t (d:Var.var t) p a m f,
    mu ([[[ [d <c- p with a] ]]] E m) f == 
    mu (Lub (cDistr (Mem.t k*nat)) 
     (step_star E
      (MkState (proc_body E p) (init_mem E p a (fst m)) (MkFrame d p nil (fst m)::nil), snd m)))
    (fun m' => f (fst m', (snd (cinit_mem E p a (fst m)) + snd m')%nat)).
   Proof.
    unfold cdeno; intros; simpl.
    transitivity (lub (c:=U)
     (mseq_lift_left (O:=U) ((Mu (Mem.t k* nat) @
      step_star E (MkState [d <c- p with a] (fst m) nil, snd m)) <_> f) 1%nat)).
    apply lub_lift_left.
    apply lub_eq_compat.
    refine (@ford_eq_intro _ _ _ _ _); intro n.

    intros; simpl.
    rewrite step_star_step; simpl.    
    rewrite step_star_add_end, cinit_mem_spec_l.
    simpl; apply step_star_stable_eq; trivial.
   Qed.

   Lemma step_star_return_mem : forall n m' m k t (d:Var.var t) p f,
    (0 < n)%nat ->
    mu (step_star E (MkState nil m' (MkFrame d p nil m::nil), k) n) f ==
    f (return_mem E d p m m', (k + snd (creturn_mem E d p m m'))%nat). 
   Proof.
    intros.
    destruct n.
    elim (lt_n_O O); trivial.
    rewrite step_star_step, <- creturn_mem_spec_l.
    refine (step_star_nil _ _ _ _ _).
   Qed.

   Lemma cdeno_call_elim : forall t (x:Var.var t) (p:Proc.proc t) 
    (la:E.args (Proc.targs p)) (mn:Mem.t k*nat) f,
    mu ([[[ [x <c- p with la] ]]] E mn) f ==
    mu (Mlet (Munit (cinit_mem E p la (fst mn)))
     (fun mn' =>
      Mlet ([[[ proc_body E p ]]] E (fst mn', snd mn + snd mn')%nat)
      (fun mn'' =>
       Munit (fst (creturn_mem E x p (fst mn) (fst mn'')),
              snd (creturn_mem E x p (fst mn) (fst mn'')) + snd mn'')%nat))) f.
   Proof.
    intros t x p la (m, n) f.
    rewrite Mlet_simpl, Munit_eq, Mlet_simpl.    
    rewrite cdeno_add_end.
    rewrite deno_call_unfold; unfold cdeno.
    rewrite <- cinit_mem_spec_l.
    simpl fst; simpl snd.
    set (n':=snd (cinit_mem E p la m));
    set (m':=fst (cinit_mem E p la m)); 
    set (c:=proc_body E p).
    replace 
     (MkState c m' (MkFrame x p nil m :: nil)) with
     (append (MkState c m' nil) nil (MkFrame x p nil m :: nil))
     by (unfold append; simpl; rewrite <- app_nil_end; trivial).
    rewrite step_star_append_lub.
    simpl; apply lub_eq_compat.
    apply fmon_eq_intro; intro.

    simpl; apply step_star_stable_eq.
    simpl; apply ford_eq_intro; intro.
    match goal with 
     |- _ == ?X => transitivity (lub (fmon_cte _ X))
    end.
    match goal with
     |- lub ?F == _=> transitivity (lub (mseq_lift_left F 1%nat))
    end.
    apply lub_lift_left.
    apply lub_eq_compat.
    apply fmon_eq_intro; intro.
    simpl; rewrite step_star_return_mem. 
    simpl; unfold return_mem.
    rewrite E.ceval_expr_spec, plus_assoc, plus_comm; trivial.
    apply lt_O_Sn.    
    trivial.
   Qed.

   Lemma cdeno_call : forall t (x:Var.var t) (p:Proc.proc t) 
    (la:E.args (Proc.targs p)) (mn:Mem.t k*nat),
    [[[ [x <c- p with la] ]]] E mn ==
    Mlet (Munit (cinit_mem E p la (fst mn)))
     (fun mn' =>
      Mlet ([[[ proc_body E p ]]] E (fst mn', snd mn + snd mn')%nat)
      (fun mn'' =>
       Munit (fst (creturn_mem E x p (fst mn) (fst mn'')),
              snd (creturn_mem E x p (fst mn) (fst mn'')) + snd mn'')%nat)).
   Proof.
    intros; apply eq_distr_intro; intro.
    apply cdeno_call_elim.
   Qed.

   Lemma deno_call_elim : forall t (x:Var.var t) p la m f,
    mu ([[ [x <c- p with la] ]] E m) f ==
    mu (([[proc_body E p]]) E (init_mem E p la m)) 
     (fun m' => f (return_mem E x p m m')).
   Proof. 
    intros t x p la m f; unfold deno.
    rewrite Mlet_simpl, cdeno_call_elim.
    rewrite <- cinit_mem_spec_l.
    rewrite Mlet_simpl, Munit_eq, Mlet_simpl.
    rewrite cdeno_add_end.
    simpl.
    apply lub_eq_compat.
    apply fmon_eq_intro; intro.
    simpl.
    refine (mu_stable_eq _ _ _ _). 
    refine (ford_eq_intro _); intro.
    unfold return_mem.
    rewrite E.ceval_expr_spec; trivial.
   Qed.

   Lemma deno_call : forall t (x:Var.var t) p la m,
    [[ [x <c- p with la] ]] E m ==
    Mlet ([[ proc_body E p ]] E (init_mem E p la m)) 
    (fun m' => Munit (return_mem E x p m m')).
   Proof.
    intros t x p la m; apply eq_distr_intro; intro f.
    refine (deno_call_elim _ _ _ _ _).
   Qed.
  
  End DENO_FACTS.


  Opaque base_step.

  Lemma step_comm : forall (A:Type) (d:Distr A) E s, 
   prod_comm (step E s) d.
  Proof with (auto using prod_comm_Munit).
   unfold step; intros.
   destruct s as (s,n).
   destruct (st_pc s).
   destruct (st_stack s) ...
   destruct i; unfold ceval_test ...
   apply prod_comm_Mlet; auto using base_step_comm ...
  Qed.

  Lemma step_trans_comm : forall A (d:Distr A) E n s,
   prod_comm (step_trans E s n) d.
  Proof.
   induction n; intros.
   simpl; apply prod_comm_Munit.
   simpl; apply prod_comm_Mlet; auto using prod_comm_Munit, step_comm.
  Qed. 
  
  Lemma step_star_comm : forall A (d:Distr A) E s n,
   prod_comm (step_star E s n) d .
  Proof.
   simpl; intros.
   apply prod_comm_Mlet; auto using prod_comm_Munit.
   apply prod_comm_drestr; apply step_trans_comm.
  Qed.
 
  Lemma cdeno_comm :  forall A (d:Distr A) E c m,
   prod_comm ([[[c]]] E m) d.
  Proof.
   unfold cdeno; intros.
   refine (@prod_comm_lub _ _ (step_star E (MkState c (fst m) nil, snd m)) d _).
   intros; apply step_star_comm.
  Qed.
  
  Lemma deno_prod_comm :  forall A (d:Distr A) E c m, 
   prod_comm ([[c]] E m) d.
  Proof.
   unfold deno; intros.
   apply prod_comm_Mlet; auto using prod_comm_Munit.
   apply cdeno_comm.
  Qed.

  Lemma deno_comm : forall E1 E2 c1 c2 m1 m2 f,
   mu ([[c1]] E1 m1) (fun m  => mu ([[c2]] E2 m2) (fun m' => f m m')) ==
   mu ([[c2]] E2 m2) (fun m' => mu ([[c1]] E1 m1) (fun m  => f m m')).
  Proof.
   intros.
   exact (eq_distr_elim 
    (deno_prod_comm ([[c1]] E1 m1) E2 c2 m2) (fun p => f (fst p) (snd p))).
  Qed.

  Fixpoint unroll_while (e:E.expr T.Bool) (c:cmd) (n:nat) {struct n} : cmd :=
   match n with
   | O => [If e _then nil]
   | S n => [If e _then (c ++ unroll_while e c n)]
   end.

  Lemma deno_unroll_while_false_elim: forall (e:E.expr T.Bool) c E m n f,
    E.eval_expr e m = false ->
    mu (([[unroll_while e c n]]) E m) f == f m.
  Proof.
    intros; case n; unfold unroll_while.
    apply deno_cond_nil_elim.
    intro n'; fold (unroll_while e c n').
    rewrite deno_cond_elim, H, deno_nil_elim; trivial.
  Qed.
 
  Opaque cdeno.   
 
  Lemma unroll_csem_mono : forall E e c m, monotonic (fun (n:natO) => 
   drestr ([[[unroll_while e c n]]] E m) (fun sn => negb (E.eval_expr e (fst sn)))).
  Proof.
   unfold monotonic; intros.
   induction H; intros; trivial.
   eapply Ole_trans; [apply IHle | ].
   clear IHle H; generalize m; clear m; induction m0; simpl; intros m f;
    case_eq (E.eval_expr e (fst m)); intros.
   rewrite cdeno_cond_t_elim; trivial.
   rewrite cdeno_nil_elim; simpl; rewrite H; simpl; trivial.
   repeat rewrite cdeno_cond_f_elim; trivial.
   repeat rewrite cdeno_cond_t_elim; trivial.
   repeat rewrite cdeno_app_elim; simpl.
   apply (mu_monotonic ([[[c]]] E (fst m, snd m + snd (E.ceval_expr e (fst m)))%nat)).
   intros m1.
   simpl in IHm0; apply IHm0.
   repeat rewrite cdeno_cond_f_elim; trivial.
  Qed. 
  
  Transparent cdeno.

  Definition unroll_while_csem E e c m : natO -m> cDistr (Mem.t k * nat) :=
   mk_fmono (unroll_csem_mono E e c m).

  Opaque step_star.

  Lemma cdeno_while_unfold : forall E e c m f,
   mu ([[[ [while e do c] ]]] E m) f == 
   mu (lub (unroll_while_csem E e c m)) f.
  Proof.
   intros; apply Ole_antisym.
   unfold cdeno at 1; simpl. 
   apply lub_le_compat.
   intro n; simpl. 
   match goal with |- _ <= lub (c:= U) ?F => transitivity (F n) end; simpl.
   assert (forall m cost f N, (n <= N)%nat ->
    mu (step_star E (MkState [while e do c] m nil, cost) n) f <=
    mu (step_star E (MkState (unroll_while e c N)  m nil, cost) n)
    (fun x : Mem.t k * nat =>
      mu (if Datatypes.negb (E.eval_expr e (fst x))
      then Munit x
      else distr0 (Mem.t k * nat)) f)); auto with arith.
   clear m f; induction n using lt_wf_ind.
   destruct n; intros.
   rewrite step_star_O; trivial.
   change (S n) with (1+n)%nat; rewrite step_star_while.
   destruct N. inversion H0. 
   simpl unroll_while. 
   case_eq (E.eval_expr e m); intros.
   repeat rewrite step_star_cond_t; trivial.
   apply (@step_star_append 
    E f (fun x : Mem.t k* nat => mu (if negb (E.eval_expr e (fst x)) then Munit x else distr0 (Mem.t k* nat)) f)
    [while e do c] (unroll_while e c N) nil nil n (MkState c m nil) (cost + snd (E.ceval_expr e m))%nat).
   intros; assert (n' < S n)%nat by auto with arith.
   assert (n' <= N)%nat by auto with zarith.
   apply H; auto.
   repeat rewrite step_star_cond_f; trivial.
   repeat rewrite step_star_final; simpl; trivial.
   rewrite H1; trivial.
   match goal with |- _ <= lub (c:=U) ?X => exact (le_lub X n) end. 

   assert (lub (c:=cDistr (Mem.t k* nat)) (unroll_while_csem E e c m) <=
    ([[[ [while e do c] ]]]) E m); trivial.
   apply lub_le.

   Opaque cdeno.

   intros n; generalize n m; clear n m f; induction n; 
    intros m f; simpl; rewrite cdeno_while_elim.
   case_eq (E.eval_expr e (fst m)); intros.
   repeat rewrite cdeno_cond_t_elim; trivial.
   rewrite cdeno_nil_elim; simpl.
   rewrite H; trivial.
   repeat rewrite cdeno_cond_f_elim; trivial.
   repeat rewrite cdeno_nil_elim; unfold unit; simpl.
   rewrite H; trivial.
   case_eq (E.eval_expr e (fst m)); intros.
   repeat rewrite cdeno_cond_t_elim; trivial.
   repeat rewrite cdeno_app_elim; simpl.
   refine (mu_monotonic ([[[c]]] E _) _ _ _); intro. 
   refine (IHn _ _).
   repeat rewrite cdeno_cond_f_elim; trivial.
   repeat rewrite cdeno_nil_elim; simpl.
   rewrite H; trivial.
  Qed.

  Lemma unroll_sem_mono : forall E e c m, monotonic 
   (fun (n:natO) => drestr ([[ unroll_while e c n ]] E m) (negP (E.eval_expr e))).
  Proof.
   unfold monotonic; intros.
   intros f; unfold deno; simpl.
   assert (X:= @unroll_csem_mono E e c (m,0%nat) x y H (fun mn => f (fst mn))).
   simpl in X.
   eapply Ole_trans; [ | eapply Ole_trans;[ apply X | ] ].
   refine (mu_monotonic (([[[unroll_while e c x]]]) E (m, 0%nat)) _ _ _); intro.
   unfold negP; destruct (E.eval_expr e (fst x0)); trivial.
   refine (mu_monotonic (([[[unroll_while e c y]]]) E (m, 0%nat)) _ _ _); intro.
   unfold negP; destruct (E.eval_expr e (fst x0)); trivial.
  Qed.

  Definition unroll_while_sem E e c m : natO -m> cDistr (Mem.t k) :=
   mk_fmono (unroll_sem_mono E e c m).

  Lemma deno_while_unfold : forall E e c m,
   [[ [while e do c] ]] E m == 
   lub (unroll_while_sem E e c m).
  Proof.
   unfold deno; intros; apply eq_distr_intro; intro; simpl.
   rewrite cdeno_while_unfold; simpl.
   apply lub_eq_compat.
   apply fmon_eq_intro; intro n; simpl.
   apply (mu_stable_eq (([[[unroll_while e c n]]]) E (m, 0%nat))); simpl.
   apply ford_eq_intro; intros.
   unfold negP; destruct (E.eval_expr e (fst n0)); trivial.
  Qed.

  Lemma deno_while_unfold_elim : forall E e c m f,
   mu ([[ [while e do c] ]] E m) f ==
   lub ((@Mu _ @ (unroll_while_sem E e c m)) <_> f).
  Proof.
   intros; transitivity (mu (lub (unroll_while_sem E e c m)) f).
   apply (ford_eq_elim (deno_while_unfold E e c m)).
   trivial.
  Qed.
 
  Lemma cwhile_ind : forall (P: Mem.t k * nat -> Prop) E (e:E.expr T.Bool) c, 
   (forall cost m, P (m, cost)%nat -> E.eval_expr e m = true ->
    range (fun mn => P (fst mn, snd mn + snd (E.ceval_expr e (fst mn)))%nat)
    ([[[ c ]]] E (m, cost)%nat)) ->
   forall m cost,
    P (m, cost + snd (E.ceval_expr e m))%nat ->
    range (fun mn => P mn /\ E.eval_expr e (fst mn) = false) ([[[ [while e do c] ]]] E (m,cost)).
  Proof.
   intros.  
   apply range_stable_eq with (lub (unroll_while_csem E e c (m,cost))).
   intros; symmetry. 
   apply eq_distr_intro; intro f; apply cdeno_while_unfold.

   apply lub_range.
   intros n; generalize n m cost H0; clear n m cost H0.
   induction n; unfold range; intros; simpl.
   case_eq (E.eval_expr e m); intros.
   repeat rewrite cdeno_cond_t_elim; trivial. 
   repeat rewrite cdeno_nil_elim; unfold unit, fst, snd.
   rewrite H2; simpl; trivial.

   repeat rewrite cdeno_cond_f_elim; trivial. 
   repeat rewrite cdeno_nil_elim; unfold unit, fst, snd.
   rewrite H2; simpl; auto.
   
   case_eq (E.eval_expr e m); intros.
   repeat rewrite cdeno_cond_t_elim; trivial. 
   repeat rewrite cdeno_app_elim; simpl.
   apply H; trivial.
   
   destruct x; simpl; intros; unfold range in IHn; simpl in IHn.
   apply IHn; trivial.
   repeat rewrite cdeno_cond_f_elim; trivial. 
   repeat rewrite cdeno_nil_elim; unfold unit, fst, snd.
   rewrite H2; simpl; auto.
  Qed.

  Opaque deno.
  
  Lemma while_ind0 :forall (P: Mem.t k-> Prop) E (e:E.expr T.Bool) c, 
   (forall m, P m -> E.eval_expr e m = true -> range P ([[ c ]] E m)) ->
   forall m , P m -> 
    range (fun m => P m /\ E.eval_expr e m = false) ([[ [while e do c] ]] E m). 
  Proof.
   intros.
   apply range_stable_eq with (lub (unroll_while_sem E e c m)).
   symmetry; apply deno_while_unfold.
   apply lub_range.
   intros n; generalize n m H0; clear n m H0.
   induction n; simpl.   
   intros; apply range_stable_eq with 
    (drestr (if E.eval_expr e m then ([[ nil]]) E m else [[ nil ]] E m) (negP (E.eval_expr e))).
   apply eq_distr_intro; simpl.
   intro f; rewrite (eq_distr_elim (deno_cond E e nil nil m)); trivial.
   unfold range; simpl; intros.       
   unfold negP; case_eq (E.eval_expr e m); intros; repeat rewrite (eq_distr_elim (deno_nil E m));
    simpl; rewrite H2; simpl; auto.
   intros; apply range_stable_eq with 
    (drestr (if E.eval_expr e m then ([[ c ++ unroll_while e c n]]) E m else [[ nil ]] E m) 
     (negP (E.eval_expr e))).
   apply eq_distr_intro; simpl.
   intro f; rewrite (eq_distr_elim (deno_cond E e (c ++ unroll_while e c n) nil m)); trivial.
   unfold range; simpl; intros. 
   unfold negP; case_eq (E.eval_expr e m); intros.
   rewrite (eq_distr_elim (deno_app E c (unroll_while e c n) m)); simpl.
   apply H; trivial; intros.
   unfold range in IHn; simpl in IHn; apply IHn; auto.
   rewrite (eq_distr_elim (deno_nil E m)); simpl; rewrite H2; simpl; auto.
  Qed.

  Lemma deno_while_restr_elim : forall E e c m f,
   mu ([[ [while e do c] ]] E m) f == 
   mu ([[ [while e do c] ]] E m) (fun m => if E.eval_expr e m then 0 else f m).
  Proof.
   intros.
   assert (range (fun m => True /\ E.eval_expr e m = false)  
    ([[ [while e do c] ]] E m)).
   apply while_ind0.
   intros; apply range_True.
   trivial.   
   apply range_eq with (1:=H).
   intros m0 [_ He]; case_eq (E.eval_expr e m0).
   intro Heq; rewrite Heq in He; discriminate.    
   trivial.
  Qed.

  Section WHILE_IND.

   Section IND.

    Variable A : Type.
    Variable test : A -> bool.
    Variable c : A -> Distr A.
    
    Fixpoint wi_n (n:nat) (cont : A -> Distr A) {struct n} : A -> cDistr A :=
     match n with
     | O => cont  
     | S n =>
      fun m => if (test m) then Mlet (c m) (wi_n n cont) else (Munit m)
     end.
    
    Definition wi_n' (n:nat) := 
     wi_n n (fun a => if test a then distr0 _ else Munit a).
    
    Lemma wi_n_comm : forall p n cont m,
     wi_n (p + n) cont m ==
     wi_n n (wi_n p cont) m.
    Proof.
     induction n; intros.
     rewrite plus_0_r; simpl; trivial.
     rewrite plus_comm.
     simpl; rewrite plus_comm.
     destruct (test m); trivial.
     apply Mlet_morph; trivial.
     intro; apply IHn.
    Qed.

    Lemma wi_n'_S : forall n a, wi_n' n a <= wi_n' (S n) a.
    Proof.
     unfold wi_n'; intros. 
     change (S n) with (1+n)%nat. 
     rewrite wi_n_comm. 
     generalize a; clear a; induction n; simpl; intros.
     destruct (test a); simpl; auto.
     destruct (test a); simpl; trivial.
     apply (mu_monotonic (c a)); simpl; intros.
     exact (IHn x0 x).
    Qed.

    Definition wi_N (a:A) : natO -m> cDistr A :=
     fnatO_intro (fun n => wi_n'_S n a). 

   End IND.
   
   Variable R : Mem.t k -> Mem.t k -> Prop.
   Variable d : Mem.t k -> Mem.t k -> Distr (Mem.t k * Mem.t k).
   Variable E1 : env.
   Variable e1 : E.expr T.Bool.
   Variable c1 : cmd.
   Variable E2 : env.
   Variable e2 : E.expr T.Bool.
   Variable c2 : cmd.

   Hypothesis He : forall m1 m2, 
    R m1 m2 -> E.eval_expr e1 m1 = E.eval_expr e2 m2.
   
   Hypothesis Hc : forall m1 m2, R m1 m2 -> E.eval_expr e1 m1 = true -> 
    lift R (d m1 m2) ([[c1]] E1 m1)  ([[c2]] E2 m2).
   
   Definition wi_N2 m1 m2 :=
    @wi_N (Mem.t k*Mem.t k) (fun p => E.eval_expr e1 (fst p))
    (fun p => d (fst p) (snd p)) (m1,m2).

   Lemma while_indR_n : forall (n:natO) m1 m2, 
    R m1 m2 -> 
    lift (fun m1 m2 => R m1 m2 /\ E.eval_expr e1 m1 = false) 
    (wi_N2 m1 m2 n) 
    (unroll_while_sem E1 e1 c1 m1 n) 
    (unroll_while_sem E2 e2 c2 m2 n).
   Proof.
    simpl; unfold wi_n'.
    induction n; simpl; intros.
    unfold drestr; eapply lift_stable_eq.
    trivial.
    apply Mlet_eq_compat.
    symmetry; apply deno_cond.
    trivial.
    apply Mlet_eq_compat.
    symmetry; apply deno_cond.
    trivial.
   
    unfold negP; rewrite <- (He H).
    case_eq (E.eval_expr e1 m1); intros.
    repeat rewrite deno_nil, Mlet_unit.
    rewrite <- (He H), H0; simpl.
    apply distr0_lift.
    repeat rewrite deno_nil, Mlet_unit.
    rewrite <- (He H), H0; simpl.
    apply lift_unit; auto.
    case_eq (E.eval_expr e1 m1); intros.
    unfold drestr.
    rewrite deno_cond, deno_cond, <- (He H), H0, deno_app, deno_app, Mcomp, Mcomp.
    apply lift_Mlet with R; auto.
    unfold drestr.
    rewrite deno_cond, deno_cond, <- (He H), H0, deno_nil, deno_nil, Mlet_unit, Mlet_unit.
    unfold negP; rewrite <- (He H), H0.
    simpl; apply lift_unit; auto.
   Qed.

   Lemma while_indR : exists dw:Mem.t k -> Mem.t k -> Distr (Mem.t k * Mem.t k),
    forall m1 m2 , R m1 m2 -> 
     lift (fun m1 m2 => R m1 m2 /\ E.eval_expr e1 m1 = false) 
     (dw m1 m2) ([[ [while e1 do c1] ]] E1 m1) ([[ [while e2 do c2] ]] E2 m2).
   Proof.
    exists (fun m1 m2 => lub (wi_N2 m1 m2)).
    intros.
    eapply lift_stable_eq with 
     (d1:=lub (unroll_while_sem E1 e1 c1 m1))
     (d2:=lub (unroll_while_sem E2 e2 c2 m2)).
    trivial.
    symmetry; apply deno_while_unfold.
    symmetry; apply deno_while_unfold.
    apply lift_lub; intros; apply while_indR_n; trivial.
   Qed.

  End WHILE_IND. 

 End K. 

 Notation "'[[' c ']]'" := (deno c) (at level 59).

 Lemma sem_discr : forall k E c (m:Mem.t k),  is_Discrete ([[c]] E m).
 Proof. 
  unfold deno; intros.
  apply is_Discrete_Mlet.
  unfold cdeno.
  change (is_Discrete
   (lub (c:= cDistr (Mem.t k * nat))
    (step_star E (MkState c (fst (m, 0%nat)) nil, snd (m, 0%nat))))).
  apply is_Discrete_lub.
  intros; unfold step_star; simpl.
  apply is_Discrete_Mlet.
  unfold drestr; apply is_Discrete_Mlet.
  induction n.
  simpl; apply is_Discrete_Munit.
  simpl; apply is_Discrete_Mlet; trivial.
  intros (s, p); simpl.
  destruct (st_pc s).
  destruct (st_stack s); apply is_Discrete_Munit.
  destruct i.
  apply is_Discrete_Mlet; auto using is_Discrete_Munit.
  destruct b; 
   auto using is_Discrete_Munit, is_Discrete_Mlet, is_Discrete_sum_support.
  unfold ceval_test; auto using is_Discrete_Munit, is_Discrete_Mlet.
  unfold ceval_test; auto using is_Discrete_Munit, is_Discrete_Mlet.
  apply is_Discrete_Munit.
  intros a; destruct (final (fst a)).
  apply is_Discrete_Munit.
  apply mkDiscr with (D_points:=fun p => (MkState nil m nil, O)).
  red; red; intros; trivial.
  intros; apply is_Discrete_Munit.
  intros; apply is_Discrete_Munit.
 Qed.

End Make.



 
 
 


 