From HB Require Import structures.

(* SSReflect *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import order eqtype fintype finset seq choice ssrnat.
(* Import Order.LTheory. *)

From Coq Require Import Sets.Ensembles.

From Lagois Require Import lagoisgraph.
(* Open Scope order_scope. *)
(* From Coq Require Import Logic.EqdepFacts. *)
(* Require Import Coq.Arith.Wf_nat. *)

Section graphsem.

Context
  (G : LagoisGraph.type)
  (Var : finType).

Definition Val := nat.

(* Abstract syntax of expressions *)
Inductive Exp : Type :=
  | const : Val -> Exp
  | var : Var -> Exp
  | add : Exp -> Exp -> Exp
  | sub : Exp -> Exp -> Exp
  | not : Exp -> Exp
  | cmp : Exp -> Exp -> Exp.

(* Definition of m(e) *)
Definition Mem := Var -> Val.
Fixpoint ExpSem (m : Mem) (e : Exp) : Val :=
  match e with
  | const n => n
  | var v => m v
  | add e1 e2 => ExpSem m e1 + ExpSem m e2
  | sub e1 e2 => ExpSem m e1 - ExpSem m e2
  | not e' => if 0 < ExpSem m e' then 0 else 1
  | cmp e1 e2 => ExpSem m e1 == ExpSem m e2
  end.
Notation "m <( e )>" := (ExpSem m e) (at level 20).

(* Abstract syntax of statements *)
Inductive Stmt {v : G} : Type :=
  | skip : Stmt
  | assign : Var -> Exp -> Stmt
  | putbuf : L(v) -> Exp -> Stmt
  | getbuf : L(v) -> Var -> Stmt
  | send (v' : G) (f : v @> v') : L(v) -> Stmt
  | receive (v' : G) (g : v' @> v) : L(v') -> Stmt
  | ifelse : Exp -> Stmt -> Stmt -> Stmt
  | while : Exp -> Stmt -> Stmt
  | seque : Stmt -> Stmt -> Stmt.

Definition Buf := seq Val.
Definition BufM (v : G) := L(v) -> Buf.
Definition State v := (@Stmt v * Mem * BufM v)%type.

(* Definition of signals *)
Inductive Sig {v : G} : Type :=
  | ε_sig : Sig
  | putbuf_sig : L(v) -> Val -> Sig
  | getbuf_sig : L(v) -> Val -> Sig
  | send_sig (v' : G) : L(v) -> L(v') -> Val -> Sig
  | receive_sig (v' : G) : L(v') -> L(v) -> Val -> Sig.

(* Small steps semantics of local execution *)
Inductive SemSS {v : G} : @Sig v -> State v -> State v -> Prop :=
  | ex_assign m b x e n :
      ExpSem m e == n ->
      SemSS ε_sig
          (assign x e, m, b)
          (skip, [eta m with x |-> n] : Mem, b)
  | ex_putbuf m b p e n :
      ExpSem m e == n ->
      SemSS (putbuf_sig p n)
          (putbuf p e, m, b)
          (skip, m, [eta b with p |-> b p ++ [:: n]] : BufM v)
  | ex_getbuf m b p x n :
      ohead (b p) == Some (n) ->
      SemSS (getbuf_sig p n)
          (getbuf p x, m, b)
          (skip, [eta m with x |-> n] : Mem, [eta b with p |-> behead (b p)] : BufM v)
  | ex_send m b v' (f : v @> v') p n :
      ohead (b p) == Some (n) ->
      SemSS (send_sig p (f p) n)
          (send f p, m, b)
          (skip, m, [eta b with p |-> behead (b p)] : BufM v)
  | ex_receive m b v' (g : v' @> v) q n :
      SemSS (receive_sig q (g q) n)
          (receive g q, m, b)
          (skip, m, [eta b with (g q) |-> b (g q) ++ [:: n]] : BufM v)
  | ex_ifelse_ff m b e s1 s2 :
      ExpSem m e == 0 ->
      SemSS ε_sig
          (ifelse e s1 s2, m, b)
          (s2, m, b)
  | ex_ifelse_tt m b e s1 s2 :
      0 < ExpSem m e ->
      SemSS ε_sig
          (ifelse e s1 s2, m, b)
          (s1, m, b)
  | ex_while m b e s :
      SemSS ε_sig
          (while e s, m, b)
          (ifelse e (seque s (while e s)) skip, m, b)
  | ex_seque_cont m m' b b' s1 s1' s2 ϕ :
      SemSS ϕ (s1, m, b) (s1', m', b') ->
      SemSS ϕ (seque s1 s2, m, b) (seque s1' s2, m', b')
  | ex_seque_skip m b s :
      SemSS ε_sig (seque skip s, m, b) (s, m, b).

(* Definition of events *)
Inductive Ev : Type :=
  | ε_ev : Ev
  | putbuf_ev (v : G) : L(v) -> Val -> Ev
  | getbuf_ev (v : G) : L(v) -> Val -> Ev
  | exch_ev (v v' : G) : L(v) -> L(v') -> Val -> Ev.

Definition GState := forall (v : G), State v.

Definition update_GState (St : GState) (v : G) (st : State v): GState.
Proof.
  move=> v'.
  case v_eq_v': (v == v').
    move/eqP in v_eq_v'.
    elim: v_eq_v'.
    exact: st.
  exact: (St v').
Defined.

(* Small steps semantics of distributed execution *)
Inductive GSemSS : Ev -> GState -> GState -> Prop :=
  | Ex_sp St v st st':
      St v = st ->
      SemSS ε_sig st st' ->
      GSemSS ε_ev St (update_GState St st')
  | Ex_putbuf St v st st' (p : L(v)) n :
      St v = st ->
      SemSS (putbuf_sig p n) st st' ->
      GSemSS (putbuf_ev p n) St (update_GState St st')
  | Ex_getbuf St v st st' (p : L(v)) n :
      St v = st ->
      SemSS (getbuf_sig p n) st st' ->
      GSemSS (getbuf_ev p n) St (update_GState St st')
  | Ex_exch St v1 v2 st1 st1' st2 st2' (p : L(v1)) (q : L(v2)) n:
      St v1 = st1 ->
      St v2 = st2 ->
      SemSS (send_sig p q n) st1 st1' ->
      SemSS (receive_sig p q n) st2 st2'  ->
      GSemSS (exch_ev p q n) St (update_GState (update_GState St st1') st2').

Inductive trace {v : G} : State v -> State v -> Type :=
  | exs_refl st : trace st st
  | exs_trans st st' st'' φ :
      trace st st' ->
      SemSS φ st' st'' ->
      trace st st''.

(* Definition 17 *)
Inductive Trace : GState -> GState -> Type :=
  | Exs_refl St : Trace St St
  | Exs_trans St St' St'' α :
      Trace St St' ->
      GSemSS α St' St'' ->
      Trace St St''.

Section observations.

Context (v : G) (ℓ : L(v)).

Definition check_ℓ T (x : T) (ℓ' : L(v)) : seq T :=
  if ℓ' < ℓ then [:: x] else [::].

Fixpoint obs st st'' (t : trace st st'') : seq Sig :=
  match t with
  | exs_refl _ => [::]
  | exs_trans _ _ _ φ t' _ => match φ with
                              | ε_sig => obs t'
                              | putbuf_sig ℓ' n
                              | getbuf_sig ℓ' n => check_ℓ φ ℓ' ++ obs t'
                              | send_sig v' ℓ' ℓ'' n => check_ℓ (getbuf_sig ℓ' n) ℓ' ++ obs t'
                              | receive_sig v' ℓ'' ℓ' n => check_ℓ (putbuf_sig ℓ' n) ℓ' ++ obs t'
                              end
  end.

Fixpoint Obs St St'' (t : Trace St St'') : seq Ev :=
  match t with
  | Exs_refl _ => [::]
  | Exs_trans _ _ _ α t' _ => match α with
                              | ε_ev => Obs t'
                              | putbuf_ev v' ℓ' n
                              | getbuf_ev v' ℓ' n =>
                                  match @eqP _ v v' with
                                  | ReflectT v2v' =>
                                      match v2v' with
                                      | erefl => fun ℓ' => check_ℓ α ℓ' ++ Obs t'
                                      end ℓ'
                                  | ReflectF v0v' => Obs t'
                                  end
                              | exch_ev v' v'' ℓ' ℓ'' n =>
                                  match @eqP _ v v' with
                                  | ReflectT v2v' =>
                                      match v2v' with
                                      | erefl => fun ℓ' => check_ℓ (getbuf_ev ℓ' n) ℓ' ++ Obs t'
                                      end ℓ'
                                  | ReflectF v0v' =>
                                      match @eqP _ v v'' with
                                      | ReflectT v2v'' => match v2v'' with
                                                          | erefl => fun ℓ'' => check_ℓ (putbuf_ev ℓ'' n) ℓ'' ++ Obs t'
                                                          end ℓ''
                                      | ReflectF v0v'' => Obs t'
                                      end
                                  end
                              end
  end.

Definition SemTrace (st : State v) (τ : seq Sig) : Prop :=
  exists st' (t : trace st st'), obs t = τ.

(* Definition of State emitting observable sequence *)
Definition GSemTrace (St : GState) (τ : seq Ev) : Prop :=
  exists St' (t : Trace St St'), Obs t = τ.

(* Definition of knowledge *)
Definition k (s : Stmt) (t : seq Sig) : Ensemble (BufM v) :=
  fun b => exists m, SemTrace (s, m, b) t.

Definition K (S : forall v, @Stmt v) (t : seq Ev) : Ensemble (BufM v) :=
  fun b => exists St, GSemTrace St t /\ (St v).2 = b.

(* Definition 19 *)
Definition nonintf (st : State v) : Prop :=
  forall t φ, SemTrace st (φ :: t) ->
  Included _ (k st.1.1 t) (k st.1.1 (φ :: t)).

Definition Nonintf (St : GState) : Prop :=
  forall t α, GSemTrace St (α :: t) ->
  Included _ (K (fun v' => (St v').1.1) t) (K (fun v' => (St v').1.1) (α :: t)).

End observations.

Check Nonintf.

Theorem soundness (St : GState) :
  (forall v ℓ, @nonintf v ℓ (St v)) -> forall v ℓ, @Nonintf v ℓ St.
Proof.
  rewrite /nonintf /Nonintf /SemTrace /GSemTrace /Included /In /k /K=> idk.
  move=> v ℓ τ α [St' [t t2ατ]] b [St0 [[St0' [t0 t02τ]] St0v2_eq_b]].
  rewrite /GSemTrace.
  exists St0; split => [|//].
  elim: α t2ατ.
  - admit. (* This case should be a contradiction as an attacker will never observe an ε event. *)
  - move=> v' q n t2ατ.
  - admit.
  - admit. (* Also a contradiction exchange events are only partially visible to an attacker. *)
Admitted.

End graphsem.
