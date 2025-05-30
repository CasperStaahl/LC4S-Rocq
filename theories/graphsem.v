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


Definition Var := nat.
Definition Ch := nat.
Definition Val := nat.

(* Abstract syntax of expressions *)
Inductive Exp : Set :=
  | const : Val -> Exp
  | var : Var -> Exp
  | add : Exp -> Exp -> Exp
  | sub : Exp -> Exp -> Exp
  | not : Exp -> Exp
  | cmp : Exp -> Exp -> Exp.

(* Definition of m(e) *)
Definition Mem := Var -> Val.
Fixpoint ExpSem (m : Mem) (e : Exp)  : Val :=
  match e with
  | const n => n
  | var v => m v
  | add e1 e2 => ExpSem m e1 + ExpSem m e2
  | sub e1 e2 => ExpSem m e1 - ExpSem m e2
  | not e' => if 0 < ExpSem m e' then 0 else 1
  | cmp e1 e2 => ExpSem m e1 == ExpSem m e2
  end.

(* Abstract syntax of statements *)
Inductive Stmt : Set :=
  | skip : Stmt
  | assign : Var -> Exp -> Stmt
  | output : Ch -> Exp -> Stmt
  | input : Var -> Ch -> Stmt
  | ifelse : Exp -> Stmt -> Stmt -> Stmt
  | while : Exp -> Stmt -> Stmt
  | seque : Stmt -> Stmt -> Stmt.

Definition State := (Stmt * Mem)%type.

(* Definition of signals *)
Inductive Sig : Type :=
  | ε_sig : Sig
  | ass_sig : Var -> Sig
  | out_sig : Ch -> Val -> Sig
  | in_sig : Ch -> Var -> Val -> Sig.

(* Small steps semantics of local execution *)
Inductive SemSS : State -> Sig -> State -> Prop :=
  | ex_assign m x e n :
      ExpSem m e = n ->
      SemSS (assign x e, m) (ass_sig x)
          (skip, fun_of_simpl [eta m with x |-> n])
  | ex_out m c e n:
      ExpSem m e = n ->
      SemSS (output c e, m) (out_sig c n) (skip, m)
  | ex_in m c x n :
      SemSS (input c x, m) (in_sig c x n)
          (skip, fun_of_simpl [eta m with x |-> n])
  | ex_ifelse_ff e s1 s2 m :
      ExpSem m e = 0 ->
      SemSS (ifelse e s1 s2, m) ε_sig (s2, m)
  | ex_ifelse_tt e s1 s2 m :
      0 < ExpSem m e ->
      SemSS (ifelse e s1 s2, m) ε_sig (s1, m)
  | ex_while e s m :
      SemSS (while e s, m) ε_sig (ifelse e (seque s (while e s)) skip, m)
  | ex_seque_cont s1 s1' s2 m m' ϕ :
      SemSS (s1, m) ϕ (s1', m') ->
      SemSS (seque s1 s2, m) ϕ (seque s1' s2, m')
  | ex_seque_skip s m :
      SemSS (seque skip s, m) ε_sig (s, m).

(* Definition of events *)
Inductive Ev G : Type :=
  | ε_ev : Ev G
  | ass_ev : G -> Var -> Ev G.
Arguments ε_ev {G}.

Definition GState (G : LagoisGraph.type) := G -> State.

(* Small steps semantics of distributed execution *)
Inductive GSemSS G : GState G -> Ev G -> GState G -> Prop :=
  | ex_sp St v st st':
      St v = st ->
      SemSS st ε_sig st' ->
      GSemSS St ε_ev [eta St with v |-> st']
  | ex_lp St v st st' x :
      St v = st ->
      SemSS st (ass_sig x) st' ->
      GSemSS St (ass_ev v x) [eta St with v |-> st']
  | ex_exch St v_i v_j st_i st'_i st_j st'_j c x n:
      v_i @> v_j ->
      St v_i = st_i ->
      St v_j = st_j ->
      SemSS st_i (out_sig c n) st'_i ->
      SemSS st_j (in_sig c x n) st'_j ->
      GSemSS St (ass_ev v_j x) [eta St with v_i |-> st'_i, v_j |-> st'_j].

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
