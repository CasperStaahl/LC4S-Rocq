From HB Require Import structures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From mathcomp Require Import  ssrbool ssreflect ssrfun order seq eqtype.
Import Order.LTheory.
Require Import lagoisgraph.
Require Import Relations.
Require Import Sets.Ensembles.
Require Import Logic.Eqdep_dec.

Section soundness.

Context (G : LagoisGraph.type) (N S : Type).
Definition 𝒮 := forall (v : G), (L(v) -> N) * S : Type.
Context (R : 𝒮 -> 𝒮 -> Prop).

Inductive connected : seq 𝒮 -> Prop :=
  | connects_empty : connected [::]
  | connects_singleton x : connected [:: x]
  | connects_cons x1 x2 xs :
      R x1 x2 ->
      connected (x2 :: xs) ->
      connected (x1 :: x2 :: xs).

Definition Trace : Type := {Σs : seq 𝒮 | connected Σs}.
Definition Trace2Seq (Σs : Trace) : seq 𝒮 := proj1_sig Σs.
Coercion Trace2Seq : Trace >-> seq.

Definition obs (v : G) (ℓ : L(v)) (Σ : 𝒮) (ℓ' : L(v)) : option N :=
  if ℓ' <= ℓ then Some ((Σ v).1 ℓ') else None.

Inductive Obs (v : G) (ℓ : L(v)) : seq 𝒮  -> seq (L(v) -> option N) -> Prop :=
  | Obs_empty : Obs ℓ [::] [::]
  | Obs_empty' Σ Σs :
      Obs ℓ Σs [::] ->
      Obs ℓ (Σ :: Σs) [:: obs ℓ Σ]
  | Obs_stutter Σ Σs σ σs :
      σ = obs ℓ Σ ->
      Obs ℓ Σs (σ :: σs) ->
      Obs ℓ (Σ :: Σs) (σ :: σs)
  | Obs_cons Σ Σs σ σs :
      σ <> obs ℓ Σ ->
      Obs ℓ Σs (σ :: σs) ->
      Obs ℓ (Σ :: Σs) (obs ℓ Σ :: σ :: σs).

Definition emits (v : G) (ℓ : L(v)) (Σ : 𝒮) (σs : seq (L(v) -> option N)) : Prop :=
  exists (Σs Σs' : Trace), Σs = Σ :: Σs' :> seq 𝒮 /\ Obs ℓ Σs σs.

Definition distr_interface_equiv (v : G) (ℓ : L(v)) (Γ Γ' : forall (v : G), L(v) -> N) : Prop :=
  forall (v' : G) (ℓ' : L(v')), flow ℓ' ℓ -> Γ v' ℓ' = Γ' v' ℓ'.

Definition distr_interface_class (v : G) (ℓ : L(v)) (Γ : (forall (v : G), L(v) -> N)) : Ensemble (forall (v : G), L(v) -> N) :=
  fun Γ' => distr_interface_equiv ℓ Γ Γ'.

Definition 𝕂 (v : G) (ℓ : L(v)) (σs : seq (L(v) -> option N)) : Ensemble (forall (v : G), L(v) -> N) :=
  fun Γ => exists (Σ : 𝒮), (forall v ℓ, (Σ v).1 ℓ = Γ v ℓ) /\ emits ℓ Σ σs.

Definition respects (Σ : 𝒮) : Prop :=
  forall (v : G) (ℓ : L(v)) σs, emits ℓ Σ σs -> Included _ (distr_interface_class ℓ (fun v ℓ => fst (Σ v) ℓ)) (𝕂 ℓ σs).

Definition local_interface_equiv (v : G) (ℓ : L(v)) (ρ ρ' : L(v) -> N) : Prop :=
  forall ℓ', (ℓ' <= ℓ) -> ρ ℓ' = ρ' ℓ'.

Definition local_interface_class (v : G) (ℓ : L(v)) (ρ : L(v) -> N) : Ensemble (L(v) -> N) :=
  fun ρ' => local_interface_equiv ℓ ρ ρ'.

Definition K (v : G) (ℓ : L(v)) (σs : seq (L(v) -> option N)) : Ensemble (L(v) -> N) :=
  fun ρ => exists (Σ : 𝒮), (forall (ℓ' : L(v)), (Σ v).1 ℓ' = ρ ℓ') /\ emits ℓ Σ σs.

Definition noninterference (Σ : 𝒮) : Prop :=
  forall (v : G) (ℓ : L(v)) σs, emits ℓ Σ σs -> Included _ (local_interface_class ℓ (fun ℓ => fst (Σ v) ℓ)) (K ℓ σs).

Definition update (Γ : forall (v : G), L(v) -> N) (v : G) (ρ : L(v) -> N) (v' : G) : L(v') -> N :=
  match @eqP _ v v' with
  | ReflectF _ => Γ v'
  | ReflectT p => match p with
                  | erefl => ρ
                  end
  end.

Check eq_axiomK.

Proposition respects2noninterference Σ :
  respects Σ -> flow_secure_graph G -> noninterference Σ.
Proof.
  rewrite /respects /flow_secure_graph /flow_secure /noninterference /Included /distr_interface_class /distr_interface_equiv /local_interface_class /local_interface_equiv /In /K /𝕂.
  move=> respΣ secG v ℓ σs emitsℓΣσs ρ  ρ_in_equiv.
  (* set Γ := update (fun v => (Σ v).1) ρ. *)
  move/(_ v ℓ σs emitsℓΣσs (update (fun v => (Σ v).1) ρ)) in respΣ.
  have low_flow_eq (v' : G) (ℓ' : L( v')) : flow ℓ' ℓ -> (Σ v').1 ℓ' = (update (fun v => (Σ v).1) ρ) v' ℓ'.
    rewrite /update.
    elim: (@eqP _ v v') => [v2v' | //].
    move: ℓ'.
    refine (match v2v' with erefl => _ end) => ℓ' ℓ'flowℓ.
    move/(_ _ _ _ ℓ'flowℓ) in secG.
    by move/(_ _ secG) in ρ_in_equiv.
  move: (respΣ low_flow_eq) => [Σ' [rest0 rest1]].
  move/(_ v) in rest0.
  have fuck ℓ' : update (fun v : G => (Σ v).1) ρ ℓ' = ρ ℓ'.
    rewrite /update /=.
    elim: (@eqP _ v v) => [v2v | //].
    by move: (eq_axiomK v2v) => ->.
  rewrite /update in rest0.
  exists Σ'.
  split=> [ℓ'|//].
  by rewrite -fuck.
Qed.

