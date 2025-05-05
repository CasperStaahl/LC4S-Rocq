(* SSReflect *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import seq ssrnat.

Definition ident := nat.

Inductive command (Term : Type) :=
  | tsyn (t : Term)
  | rd (z : ident) (y : ident)
  | wr (x : ident) (z : ident).

Arguments tsyn {_}.
Arguments rd {_}.
Arguments wr {_}.

Inductive phrase (Term Term' : Type) :=
  | csyn (c : command Term)
  | csyn' (c' : command Term')
  | T_RL (y : ident) (x' : ident)
  | T_LR (y' : ident) (x : ident).

Arguments csyn {_ _}.
Arguments csyn' {_ _}.
Arguments T_RL {_ _}.
Arguments T_LR {_ _}.

Inductive seq (Term Term' : Type) :=
  | ε
  | seqcons (s : seq Term Term') (p : phrase  Term Term').

Arguments ε {_ _}.
Arguments seqcons {_ _}.
