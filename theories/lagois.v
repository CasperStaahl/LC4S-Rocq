From HB Require Import structures.

(* SSReflect *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import order eqtype fintype finset.
Import Order.LTheory.

Open Scope order_scope.

(* Definition 10 *)
HB.mixin Record IsLagois d (P : porderType d) d' (Q : porderType d')
    (fg : {omorphism P -> Q} * {omorphism Q -> P}) := {
  lc1 q : q <= fg.2 (fg.1 q) ;
  lc2 p : p <= fg.1 (fg.2 p) ;
  lc3 p : fg.1 (fg.2 (fg.1 p)) = fg.1 p ;
  lc4 q : fg.2 (fg.1 (fg.2 q)) = fg.2 q ;
}.
HB.structure Definition Lagois d P d' Q := {fg of IsLagois d P d' Q fg}.

HB.instance Definition _
    d (P : porderType d)
    d' (Q : porderType d')
    (fg : Lagois.type P Q)
  := IsLagois.Build d' Q d P (fg.2, fg.1) lc2 lc1 lc4 lc3.

Lemma melton_3_3 d (P : finLatticeType d) d' (Q : finLatticeType d')
    (f : { omorphism P -> Q}) (g : { omorphism Q -> P}) :
  (forall p, f (g (f p)) = f p) <-> (forall q, q \in f @: setT <-> f (g q) = q).
Proof.
  split=> [LC3 | LC3'].
  - split=> [q_in_fP | fgq_eq_q].
    + case/imsetP: q_in_fP => p _ q_eq_fp; rewrite q_eq_fp; apply: LC3.
    + apply/imsetP; exists (g q)=>//.
  - move=> p; apply (LC3' (f p)); apply/imsetP; exists p=>//.
Qed.

Lemma PC
    d (P : finTBLatticeType d)
    d' (Q : finTBLatticeType d')
    (fg : Lagois.type P Q) q :
  q \in fg.1 @: setT -> fg.2 q = \join_(p | fg.1 p == q) p.
Proof.
  move=> q_in_fP.
  have fgq_eq_q : fg.1 (fg.2 q) = q
    by move/(iffLR (melton_3_3 fg.1 fg.2)) in q_in_fP; exact /q_in_fP /lc3.
  have gq_in_fqiq : fg.2 q \in fg.1 @^-1: [set q]
    by rewrite in_set fgq_eq_q; exact: set11.
  have fp_eq_q_if_p_in_fiq : forall p, p \in fg.1 @^-1: [set q] -> fg.1 p = q
    by move=> p; rewrite in_set in_set1; apply/eqP.
  have p_in_fi_q_if_p_le_gq : forall p, p \in fg.1 @^-1: [set q] -> p <= fg.2 q
    by move=> p /(fp_eq_q_if_p_in_fiq p) <-; exact: lc1.
  have gq_le : fg.2 q <= \join_(p | fg.1 p == q) p.
    apply: joins_min.
      by apply/eqP; exact fgq_eq_q.
    exact: le_refl.
  have gq_ge : \join_(p | fg.1 p == q) p <= fg.2 q.
    apply/joinsP => p /eqP fp_eq_q.
    apply p_in_fi_q_if_p_le_gq.
    rewrite in_set fp_eq_q.
    exact: set11.
  by apply: le_anti; apply/andP.
Qed.

Lemma melton_3_7
    d (P : finTBLatticeType d)
    d' (Q : finTBLatticeType d')
    (fg : Lagois.type P Q) q :
  q \in fg.1 @: setT -> fg.2 q = \join_(p in fg.1@^-1: [set q]) p.
Proof.
  move=> q_in_fP.
  rewrite (PC q_in_fP).
  apply/le_anti/andP; split.
  - apply/joinsP => p /eqP fp_eq_q.
    apply: joins_min => //.
    by rewrite in_set; apply/set1P.
  - apply/joinsP => p p_in_fnq.
    rewrite in_set in p_in_fnq.
    move/set1P in p_in_fnq.
    apply: joins_min => //.
    by rewrite -p_in_fnq.
Qed.

Lemma melton_3_7_full
    d (P : finTBLatticeType d)
    d' (Q : finTBLatticeType d')
    (fg : Lagois.type P Q) q :
  q \in fg.1 @: setT ->
  fg.2 q \in fg.1@^-1: [set q]
  /\ forall p, p \in fg.1@^-1: [set q] -> p <= fg.2 q.
Proof.
  move=> q_in_fP; split; first last.
    rewrite (melton_3_7 q_in_fP) => p' p'_in_fq .
    exact: (joins_min p'_in_fq).
  move: q_in_fP => /imsetP [p _ q_eq_fp].
  rewrite in_set q_eq_fp lc3; exact: set11.
Qed.

Lemma CC
    d (P : porderType d)
    d' (Q : porderType d')
    (fg : Lagois.type P Q) q q' :
  fg.1 (fg.2 q) = q' -> fg.1 (fg.2 q') = q'.
Proof. by move=> <-; rewrite lc3. Qed.

Lemma melton_3_8
    d (P : finTBLatticeType d)
    d' (Q : finTBLatticeType d')
    (fg : Lagois.type P Q) q :
  fg.1 (fg.2 q) = \meet_(q' in fg.1 @: setT | q <= q') q'.
Proof.
  have fgq_in_qleq': fg.1 (fg.2 q) \in [set q' in fg.1 @: setT | q <= q'].
    rewrite in_set; apply/andP; split; first last.
      exact: lc2.
    by apply/imsetP; exists (fg.2 q).
  have fgq_le_q'_if :
      forall q', q' \in fg.1 @: setT -> q <= q' -> fg.1 (fg.2 q) <= q'.
    move=> q' /imsetP [p] _ -> q_le_q'.
    move /(omorph_le fg.2) /(omorph_le fg.1) in q_le_q'.
    by rewrite lc3 in q_le_q'.
  have fgq_le :
      fg.1 (fg.2 q) <= \meet_(q' in [set fg.1 x | x in [set: P]] | q <= q') q'
    by apply/meetsP => q' /andP [/fgq_le_q'_if q'_in_fiP /q'_in_fiP q_le_q'].
  have fgq_ge :
      \meet_(q' in [set fg.1 x | x in [set: P]] | q <= q') q' <= fg.1 (fg.2 q).
    apply/meets_max => //.
    rewrite setIdE in_setI in fgq_in_qleq'.
    move/andP: fgq_in_qleq' => [fgq_in_fP fgq_over_q].
    rewrite in_set in fgq_over_q.
    apply/andP => //.
  exact/le_anti/andP.
Qed.

Lemma melton_3_9
    d (P : finTBLatticeType d)
    d' (Q : finTBLatticeType d')
    (fg : Lagois.type P Q) q :
  fg.2 q =
    \join_(q'' in fg.1@^-1: [set \meet_(q' in fg.1 @: setT | q <= q') q']) q''.
Proof.
  have: fg.2 q = \join_(p in fg.1@^-1: [set fg.1 (fg.2 q)]) p
    by rewrite -[in LHS]lc4 melton_3_7 => //; apply/imsetP; exists (fg.2 q).
  by rewrite melton_3_8.
Qed.

Definition meetOfInIs d (L : finTBLatticeType d) (A B : {set L}) x :=
  (forall a, a \in A -> x <= a)
  /\ (forall b, b \in B -> (forall a, a \in A -> b <= a) -> b <= x)
  /\ x \in B.
Notation "'meet' 'of' A 'in' B 'is' x" := (meetOfInIs A B x) (at level 30).

Definition joinOfInIs d (L : finTBLatticeType d) (A B : {set L}) x :=
  (forall a, a \in A -> a <= x)
  /\ (forall b, b \in B -> (forall a, a \in A -> a <= b) -> x <= b)
  /\ x \in B.
Notation "'join' 'of' A 'in' B 'is' x" := (joinOfInIs A B x) (at level 30).

Check forall d (P : finTBLatticeType d)
             d' (Q : finTBLatticeType d')
             (fg : Lagois.type P Q)
             (A : {set P}),
  A \subset fg.2 @: setT ->
  (forall p : {b | meet of A in (fg.2 @: setT) is b},
      exists b, meet of A in setT is b /\ b = proj1_sig p)
  /\ (forall p : {b | meet of A in setT is b},
      exists b, meet of A in (fg.2 @: setT) is b /\ b = proj1_sig p).

Lemma melton_3_11
    d (P : finTBLatticeType d)
    d' (Q : finTBLatticeType d')
    (fg : Lagois.type P Q)
    (A : {set P}) :
  A \subset fg.2 @: setT ->
  (forall b, meet of A in (fg.2 @: setT) is b <-> meet of A in setT is b).
Proof.
  move=>  A_subset_gQ b.
  have gfa_eq_a a (a_in_A : a \in A) : fg.2 (fg.1 a) = a
    by move: A_subset_gQ => /subsetP /(_ a a_in_A) /imsetP [q _ ->]; exact: lc4.
  split; first last.
  - move=> [b_le_a [p_le_b _]].
    split => //; split.
      by move=> x' _ x'_le_a; apply: p_le_b => //.
    have gfb_le_gfa a (a_in_A : a \in A) : fg.2 (fg.1 b) <= fg.2 (fg.1 a).
      apply/(omorph_le fg.2)/(omorph_le fg.1); exact: b_le_a.
    have gfb_le_a a (a_in_A : a \in A) : fg.2 (fg.1 b) <= a
      by rewrite -(gfa_eq_a a a_in_A); exact: gfb_le_gfa.
    have b_eq_gfb : b = fg.2 (fg.1 b).
      apply/le_anti/andP; split.
        exact: lc1.
      apply: p_le_b => //.
    apply/imsetP; exists (fg.1 b) => //.
  - move=> [b_le_a [b_greatest b_in_gQ]].
    split => [//|]; split => [dd _ d_lb_A |//=].
    have gfd_le_gfa a (a_in_A : a \in A) :
        dd <= fg.2 (fg.1 dd) <= fg.2 (fg.1 a).
      apply/andP; split.
        exact: lc1.
      exact /(omorph_le fg.2) /(omorph_le fg.1) /d_lb_A.
    have gfd_in_gQ : fg.2 (fg.1 dd) \in fg.2 @: setT by
      apply/imsetP; exists (fg.1 dd) => //.
    have gfd_le_b : fg.2 (fg.1 dd) <= b.
      apply: (b_greatest _ gfd_in_gQ) => a a_in_A.
      rewrite -(gfa_eq_a a a_in_A).
      by move: gfd_le_gfa => /(_ a a_in_A) /andP [_ gfd_eq_gfa].
    exact: le_trans (lc1 dd) gfd_le_b.
Qed.

Lemma melton_3_11_1'
    d (P : finTBLatticeType d)
    d' (Q : finTBLatticeType d')
    (fg : Lagois.type P Q)
    (A : {set P}) :
  A \subset fg.2 @: setT ->
  (forall p : {b | meet of A in (fg.2 @: setT) is b},
      exists b, meet of A in setT is b /\ b = proj1_sig p)
  /\ (forall p : {b | meet of A in setT is b},
      exists b, meet of A in (fg.2 @: setT) is b /\ b = proj1_sig p).
Proof.
  move=> A_subset_gQ; split=> p; exists (proj1_sig p); split=> //;
  apply/(melton_3_11 A_subset_gQ); exact (proj2_sig p).
Qed.

Lemma melton_3_11_2
    d (P : finTBLatticeType d)
    d' (Q : finTBLatticeType d')
    (fg : Lagois.type P Q)
    (A : {set P}) :
  A \subset fg.2 @: setT ->
  (forall a', join of A in setT is a' ->
      join of A in (fg.2 @: setT) is (fg.2 (fg.1 a'))).
Proof.
  move=> A_subset_gQ a' [a'_ub_A [a'_least _]].
  split => [a a_in_A |].
    exact: le_trans (a'_ub_A a a_in_A) (lc1 a').
  split; first last => [| p p_in_gQ p_ub_A].
    by apply/imsetP; exists (fg.1 a') => //; rewrite in_set.
  have p_eq_gfp : fg.2 (fg.1 p) = p
    by move: p_in_gQ => /imsetP [q _ ->]; exact: lc4.
  rewrite -p_eq_gfp; apply /(omorph_le fg.2) /(omorph_le fg.1); exact: a'_least.
Qed.
