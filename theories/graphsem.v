From HB Require Import structures.

(* SSReflect *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import order eqtype fintype finset seq choice ssrnat.
(* Import Order.LTheory. *)

From Lagois Require Import lagoisgraph.
(* Open Scope order_scope. *)
(* From Coq Require Import Logic.EqdepFacts. *)
(* Require Import Coq.Arith.Wf_nat. *)

Definition Var := nat.
Definition Ch := nat.
Definition Val := nat.

Definition Env := Var -> Val.

Inductive Exp : Set :=
  | const : Val -> Exp
  | var : Var -> Exp
  | add : Exp -> Exp -> Exp
  | not : Exp -> Exp.

Fixpoint ExpSem (m : Env) (e : Exp)  : Val :=
  match e with
  | const n => n
  | var v => m v
  | add e1 e2 => ExpSem m e1 + ExpSem m e2
  | not e' => if 0 < ExpSem m e' then 0 else 1
  end.

Inductive Stmt : Type :=
  | skip : Stmt
  | assign : Var -> Exp -> Stmt
  | output : Ch -> Exp -> Stmt
  | input : Var -> Ch -> Stmt
  | ifelse : Exp -> Stmt -> Stmt -> Stmt
  | while : Exp -> Stmt -> Stmt
  | seque : Stmt -> Stmt -> Stmt.

Inductive Event {G : LagoisGraph.type} : Type :=
  | ε_ev : Event
  | update  : G -> Var -> Val -> Event.

Definition State := prod Stmt Env.

Definition GState (G : LagoisGraph.type) := G -> State.

Inductive GSemSS G : GState G -> Event -> GState G -> Prop :=
  | ex_assign (Gst : GState G) v m i e :
      Gst v = (assign i e, m) ->
      GSemSS Gst (update v i (ExpSem m e)) [eta Gst with v |-> (skip, fun_of_simpl [eta m with i |-> (ExpSem m e)])]
  | ex_exch (Gst : GState G) v m v' m' c i' e :
      Gst v = (output c e, m) ->
      Gst v' = (input i' c, m') ->
      GSemSS Gst (update v' i' (ExpSem m e)) [eta Gst with v  |-> (skip, m),
                                                           v' |-> (skip, fun_of_simpl [eta m' with i' |-> (ExpSem m e)])]
  | ex_ifelse_ff (Gst : GState G) v b s1 s2 m :
      Gst v = (ifelse b s1 s2, m) ->
      ExpSem m b = 0 ->
      GSemSS Gst ε_ev [eta Gst with v |-> (s2, m)]
  | ex_ifelse_tt (Gst : GState G) v b s1 s2 m :
      Gst v = (ifelse b s1 s2, m) ->
      ExpSem m b > 0 ->
      GSemSS Gst ε_ev [eta Gst with v |-> (s1, m)]
  | ex_while (Gst : GState G) v b s m :
      Gst v = (while b s, m) ->
      ExpSem m b = 0 ->
      GSemSS Gst ε_ev [eta Gst with v |-> (ifelse b (seque s (while b s)) skip, m)]
  | ex_seque_cont (Gst Gst': GState G) v s1 s1' s2 m m' ev :
      Gst v = (seque s1 s2, m) ->
      GSemSS [eta Gst with v |-> (s1, m)] ev Gst' ->
      Gst' v = (s1', m') ->
      GSemSS Gst ev [eta Gst with v |-> (seque s1' s2, m')]
  | ex_seque_skip (Gst Gst': GState G) v s m :
      Gst v = (seque skip s, m) ->
      GSemSS Gst ε_ev [eta Gst with v |-> (s, m)].

Inductive GSemBS G : GState G -> seq Event -> GState G -> Type :=
  | sem_refl (Gst  : GState G) : GSemBS Gst [::] Gst
  | sem_trans (Gst Gst' Gst'' : GState G) evs ev :
      GSemBS Gst evs Gst' ->
      GSemSS Gst' ev Gst'' ->
      GSemBS Gst (ev :: evs) Gst''.

Record Atk (G : LagoisGraph.type) (loc : G) (lvl : L(loc)) := {
  Sts : Type;
  init : Sts;
  tfun : @Event G -> Sts -> Sts;
}.

Fixpoint observe (G : LagoisGraph.type) (loc : G) (sec : Var -> L(loc)) (lvl : L(loc)) (a : Atk lvl) (Gst Gst' : GState G) evs (trace : GSemBS Gst evs Gst') : Sts a :=
  match trace with
  | sem_refl Gst0  => init a
  | sem_trans _ _ _ _ ev trace' _ =>
      let st := observe sec a trace' in match ev with
                                    | ε_ev => st
                                    | update v i n => if v == loc && sec i <= lvl then
                                    end

  end.
