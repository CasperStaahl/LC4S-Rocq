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

Section abstract_syntax.

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
  | exch (v' : G) (f : v @> v') : L(v) -> Stmt
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
  | exch_sig (v' : G) : L(v) -> L(v') -> Val -> Sig.

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
  | ex_exch m b v' (f : v @> v') p n :
      ohead (b p) == Some (n) ->
      SemSS (exch_sig p (f p) n)
          (exch f p, m, b)
          (skip, m, [eta b with p |-> behead (b p)] : BufM v)
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
      GSemSS ε_ev St (@update_GState St v st')
  | Ex_putbuf St v st st' (p : L(v)) n :
      St v = st ->
      SemSS (putbuf_sig p n) st st' ->
      GSemSS (putbuf_ev p n) St (@update_GState St v st')
  | Ex_getbuf St v st st' (p : L(v)) n :
      St v = st ->
      SemSS (getbuf_sig p n) st st' ->
      GSemSS (getbuf_ev p n) St (@update_GState St v st')
  | Ex_exch St v1 v2 st1 st1' st2 st2' (p : L(v1)) (q : L(v2)) n:
      St v1 = st1 ->
      St v2 = st2 ->
      SemSS (exch_sig p q n) st1 st1' ->
      SemSS (putbuf_sig q n) st2 st2'  ->
      GSemSS (exch_ev p q n) St (@update_GState (@update_GState St v1 st1') v2 st2').

(* Definition 17 *)
Inductive Trace G : GState G -> GState G -> Type :=
  | exs_refl St : Trace St St
  | exs_trans St St' St'' α :
      Trace St St' ->
      GSemSS St' α St'' ->
      Trace St St''.

Definition PMem := (Var -> option Val).

(* Definition 18 *)
HB.mixin Record IsAtk (G : LagoisGraph.type) Σ := {
  σ_init : Σ;
  δ : Σ -> PMem -> Σ;
}.
HB.structure Definition Atk G := {Sts of IsAtk G Sts}.

Section Security.

Variables (G : LagoisGraph.type)
    (A : Atk.type G) (loc : G) (lvl : L(loc)) (λ : Var -> L(loc)).

(* Definition of observable sequences *)
Definition obs (m : Mem) : PMem :=
  fun x => if (λ x <= lvl) then Some (m x) else None.

Fixpoint Obs St St'' (t : @Trace G St St'') : seq PMem :=
  match t with
  | exs_refl St => [:: obs (St loc).2]
  | exs_trans St St' St'' α t' _ =>
      let μs := Obs t' in
        match α with
        | ε_ev => μs
        | ass_ev v x => if (loc == v) && (λ x <= lvl)
                       then obs (St'' loc).2 :: μs
                       else μs
        end
  end.

(* Definition of State emitting observable sequence *)
Definition GSemTrace (St : GState G) (μs : seq PMem) : Prop :=
  exists St' (t : Trace St St'), Obs t = μs.

(* Definition of A(μs) *)
Fixpoint observe (μs : seq PMem) : A :=
  match μs with
  | [::] => σ_init
  | μ :: μs' => δ (observe μs') μ
  end.

(* Definition of knowledge *)
Definition k (S : G -> Stmt) (σ : A) : Ensemble Mem :=
  fun m => exists St μs, GSemTrace St μs
                            /\ (forall v, (St v).1 = S v)
                            /\ (St loc).2 = m
                            /\ observe μs = σ.

Definition k_plus (S : G -> Stmt) (σ : A) : Ensemble Mem :=
  fun m => exists St μs μ, GSemTrace St (μ :: μs)
                            /\ (forall v, (St v).1 = S v)
                            /\ (St loc).2 = m
                            /\ observe μs = σ.

(* Definition of observable initial memory *)
Definition m_equiv (m m' : Mem) : Prop :=
  forall x, λ x <= lvl -> m x = m' x.

Definition m_equiv_class (m : Mem) : Ensemble Mem :=
  fun m' => m_equiv m m'.

(* Definition 19 *)
Definition nonintf (St : GState G) : Prop :=
  forall μs μ, GSemTrace St (μ :: μs) ->
    Included _
      (Intersection _
        (m_equiv_class (St loc).2)
        (k (fun v => (St v).1) (observe μs)))
      (k (fun v => (St v).1) (observe (μ :: μs))).

(* Definition 20 *)
Definition pi_nonintf (St : GState G) : Prop :=
  forall μs μ, GSemTrace St (μ :: μs) ->
    Included _
      (Intersection _
        (m_equiv_class (St loc).2)
        (k_plus (fun v => (St v).1) (observe μs)))
      (k (fun v => (St v).1) (observe (μ :: μs))).

End Security.
