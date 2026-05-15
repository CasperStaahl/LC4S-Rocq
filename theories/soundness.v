From HB Require Import structures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From mathcomp Require Import  ssrbool ssreflect ssrfun order seq eqtype.
Import Order.LTheory.
Require Import lagoisgraph Relations Sets.Ensembles Logic.Eqdep_dec.

Section soundness.

Context (G : LagoisGraph.type) (S : Type) (N : forall (v : G) (ℓ : L(v)), Type).
Definition 𝒮 := forall (v : G), (forall ℓ : L(v), N ℓ) * S : Type.
Context (R : 𝒮 -> 𝒮 -> Prop).

Definition Interface := forall (v : G) (ℓ : L(v)), N ℓ.
Definition LocalInterface v := forall ℓ : L(v), N ℓ.
Definition Observation v := seq (forall (ℓ : L(v)), option (N ℓ)).

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

Definition obs (v : G) (ℓ : L(v)) (Σ : 𝒮) (ℓ' : L(v)) : option (N ℓ') :=
  if ℓ' <= ℓ then Some ((Σ v).1 ℓ') else None.

Inductive Obs (v : G) (ℓ : L(v)) : seq 𝒮  -> Observation v -> Prop :=
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

Definition emits (v : G) (ℓ : L(v)) (Σ : 𝒮) (σs : Observation v) : Prop :=
  exists (Σs Σs' : Trace), Σs = Σ :: Σs' :> seq 𝒮 /\ Obs ℓ Σs σs.

Definition distr_interface_equiv (v : G) (ℓ : L(v)) (Γ Γ' : Interface) : Prop :=
  forall (v' : G) (ℓ' : L(v')), flow ℓ' ℓ -> Γ v' ℓ' = Γ' v' ℓ'.

Definition distr_interface_class (v : G) (ℓ : L(v)) (Γ : Interface) : Ensemble Interface :=
  fun Γ' => distr_interface_equiv ℓ Γ Γ'.

Definition 𝕂 (v : G) (ℓ : L(v)) (σs : Observation v) : Ensemble Interface :=
  fun Γ => exists (Σ : 𝒮), (forall v ℓ, (Σ v).1 ℓ = Γ v ℓ) /\ emits ℓ Σ σs.

(* Definition 29*)
Definition respects (Σ : 𝒮) : Prop :=
  forall (v : G) (ℓ : L(v)) σs, emits ℓ Σ σs -> Included _ (distr_interface_class ℓ (fun v ℓ => fst (Σ v) ℓ)) (𝕂 ℓ σs).

Definition local_interface_equiv (v : G) (ℓ : L(v)) (ρ ρ' : LocalInterface v) : Prop :=
  forall ℓ', (ℓ' <= ℓ) -> ρ ℓ' = ρ' ℓ'.

Definition local_interface_class (v : G) (ℓ : L(v)) (ρ : LocalInterface v) : Ensemble (LocalInterface v) :=
  fun ρ' => local_interface_equiv ℓ ρ ρ'.

Definition K (v : G) (ℓ : L(v)) (σs : Observation v) : Ensemble (LocalInterface v) :=
  fun ρ => exists (Σ : 𝒮), (forall (ℓ' : L(v)), (Σ v).1 ℓ' = ρ ℓ') /\ emits ℓ Σ σs.

(* Definition 30 *)
Definition noninterference (Σ : 𝒮) : Prop :=
  forall (v : G) (ℓ : L(v)) σs, emits ℓ Σ σs -> Included _ (local_interface_class ℓ (fun ℓ => fst (Σ v) ℓ)) (K ℓ σs).

Definition update (Γ : Interface) (v : G) (ρ : LocalInterface v) (v' : G) : LocalInterface v' :=
  match @eqP _ v v' with
  | ReflectF _ => Γ v'
  | ReflectT p => match p with
                  | erefl => ρ
                  end
  end.

(* Theorem 31 *)
Theorem respects2noninterference Σ :
  respects Σ -> flow_secure_graph G -> noninterference Σ.
Proof.
  move=> respΣ secG v ℓ σs emitsℓΣσs ρ  ρ_in_equiv.
  set Γ := update (fun v => (Σ v).1) ρ.
  have Γvℓ'_eq_ρℓ' ℓ' : Γ v ℓ' = ρ ℓ'.
    rewrite /Γ /update.
    elim: (@eqP _ v v) => [v2v | //].
    by rewrite (eq_axiomK v2v).
  have low_flow_eq v' ℓ' : flow ℓ' ℓ -> (Σ v').1 ℓ' = Γ v' ℓ'.
    rewrite /Γ /update.
    elim: (@eqP _ v v') ℓ' => [v2v' | //].
    refine (match v2v' with erefl => _ end) => ℓ' ℓ'flowℓ.
    move/(_ _ _ _ ℓ'flowℓ) in secG.
    by move/(_ _ secG) in ρ_in_equiv.
  move/(_ v ℓ σs emitsℓΣσs Γ) in respΣ.
  move: (respΣ low_flow_eq) => [Σ' [low_eq emitsℓΣ'σs]].
  move/(_ v) in low_eq.
  exists Σ'; split=> [ℓ' | //].
  by rewrite -Γvℓ'_eq_ρℓ'.
Qed.

End soundness.
