From HB Require Import structures.

(* SSReflect *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import eqtype ssrnat seq finset.
From Lagois Require Import abssyn.

Inductive Var :=
  | loc of ident
  | exp of ident
  | imp of ident.

Definition eqVar x y :=
  match x, y with
  | loc x', loc y'
  | exp x', exp y'
  | imp x', imp y' => x' == y'
  |      _,      _ => false
  end.

Lemma eqVarP : Equality.axiom eqVar.
Proof.
  rewrite/Equality.axiom => x y.
  case x_eq_y: (eqVar x y); case: x x_eq_y => x;
  case: y => y //= x_eq_y; move/eqP in x_eq_y;
  do 1? (apply: ReflectT; rewrite x_eq_y; by []);
  apply: ReflectF => //=; by rewrite/not in x_eq_y * => [[x_eq_y']].
Qed.

HB.instance Definition _ := hasDecEq.Build Var eqVarP.

Definition Store T := simpl_fun Var T.
Definition Store2 T := prod (Store T) (Store T).

HB.mixin Record isBigStepSemantic (T Term : Type) := {
  bigstep : T -> Term -> T -> Prop;
}.
HB.structure Definition BigStepSemantic T := {Term of isBigStepSemantic T Term}.

Notation "s ==[ t ]==> s'" := (bigstep s t s') (at level 30).

HB.mixin Record IsSubSemantic
    (Val Term : Type) of BigStepSemantic (Store Val) Term := {
  determines : Term -> Var -> seq.seq Var ;

  assigned : Term -> Var -> bool ;
  frame s s' t v : s ==[ t ]==> s' -> ~~ (assigned t v) -> s v = s' v ;

  read : Term -> Var -> bool ;
  readP t w' : reflect (exists w, w' \in determines t w) (read t w') ;

  simple_security t z (μ μ' ν ν' : Store Val):
      assigned t z ->
      μ ==[ t ]==> μ' ->
      ν ==[ t ]==> ν' ->
      (forall w, w \in determines t z -> μ w = ν w) ->
      μ' z = ν' z ;

  xs_not_assigned : forall x t, ~~ (assigned t (exp x)) ;
  ys_not_assigned : forall y t, ~~ (assigned t (imp y)) ;
}.
HB.structure Definition SubSemantic Val :=
  {Term of IsSubSemantic Val Term & BigStepSemantic Val Term}.

Inductive commsem {Val : Type} {Term : SubSemantic.type Val} :
    Store Val -> command Term -> Store Val -> Prop :=
  | Tsem μ ν t :
      μ ==[ t ]==> ν ->
      commsem μ (tsyn t) ν
  | WRsem μ x z :
      commsem μ (wr x z) [eta μ with exp x |-> μ (loc  z)]
  | RDsem μ z y :
      commsem μ (rd z y) [eta μ with loc z |-> μ (imp y)].
HB.instance Definition _ Val (Term : SubSemantic.type Val) :=
  isBigStepSemantic.Build (Store Val) (command Term) commsem.

Inductive phrasesem {Val : Type} {Term Term' : SubSemantic.type Val} :
    Store2 Val -> phrase Term Term' -> Store2 Val -> Prop :=
  | Lcommsem μ μ' ν c :
      μ ==[ c ]==> ν ->
      phrasesem (μ, μ') (csyn c) (ν, μ')
  | Rcommsem μ μ' ν' c' :
      μ' ==[ c' ]==> ν' ->
      phrasesem (μ, μ') (csyn' c') (μ, ν')
  | TRLsem μ μ' y x' :
      phrasesem (μ, μ') (T_RL y x') ([eta μ with imp y |-> μ' (exp x')], μ')
  | TLRsem μ μ' y' x :
      phrasesem (μ, μ') (T_LR y' x) (μ, [eta μ' with imp y' |-> μ (exp x)]).
HB.instance Definition _ Val (Term Term' : SubSemantic.type Val) :=
  isBigStepSemantic.Build (Store2 Val) (phrase Term Term') phrasesem.

Inductive seqsem {Val : Type} {Term Term': SubSemantic.type Val} :
    Store2 Val -> seq Term Term' -> Store2 Val -> Prop :=
  | εsem μ:
      seqsem μ ε μ
  | seqconssem s (p : phrase Term Term') μ μ1 μ2:
      seqsem μ s μ1 ->
      μ1 ==[ p ]==> μ2 ->
      seqsem μ (seqcons s p) μ2.
HB.instance Definition _ Val (Term Term' : SubSemantic.type Val) :=
  isBigStepSemantic.Build (Store2 Val) (seq Term Term') seqsem.
