From HB Require Import structures.

(* SSReflect *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import order eqtype fintype finset.
Import Order.LTheory.

Open Scope order_scope.

HB.mixin Record IsLagois d (P : porderType d) d' (Q : porderType d')
    (fg : { omorphism P -> Q} * { omorphism Q -> P}) := {
  lc1 q : q <= fg.2 (fg.1 q) ;
  lc2 p : p <= fg.1 (fg.2 p) ;
  lc3 p : fg.1 (fg.2 (fg.1 p)) = fg.1 p ;
  lc4 q : fg.2 (fg.1 (fg.2 q)) = fg.2 q ;
}.
HB.structure Definition Lagois d P d' Q := {fg of IsLagois d P d' Q fg}.

Lemma lexididx d (P : porderType d) (p : P) : p <= idfun (idfun p).
Proof. exact: lexx. Qed.

Lemma eqidididxidx d (P : porderType d) : forall x : P, id (id (id x)) = id x.
Proof. trivial. Qed.

(* HB.instance Definition test d P := *)
(*   @IsLagois.Build d P d P idfun idfun (@lexididx d P) (@lexididx d P) (@eqidididxidx d P) (@eqidididxidx d P). *)

Definition incr {A: porderType (Order.Disp tt tt)} (f : A -> A) := forall a, a <= f a.

Definition quasi {A B} (f : A -> B) (g : B -> A) := g \o f \o g =1 g.

Inductive FLagois (P Q : finTBLatticeType (Order.Disp tt tt)) (f : { omorphism P -> Q}) (g : { omorphism Q -> P}) : Prop :=
  | PFLagois : incr (f \o g) -> incr (g \o f) -> quasi f g -> quasi g f -> FLagois f g.

Notation "P '<~' f '~' g '~>' Q" := (@FLagois P Q f g) (at level 35).

Lemma melton_3_2 P Q f g :
  P<~f~g~>Q -> Q<~g~f~>P.
Proof. move=> [LC1 LC2 LC3 LC4]//. Qed.

Lemma melton_3_3 (P Q : finLatticeType (Order.Disp tt tt)) (f : { omorphism P -> Q}) (g : { omorphism Q -> P}) :
  f \o g \o f =1 f <-> (forall q, q \in f @: setT <-> (f \o g) q = q).
Proof.
  split=> [LC3 | LC3'].
  - split=> [q_in_fP | fgq_eq_q].
    + case/imsetP: q_in_fP => p _ q_eq_fp; rewrite q_eq_fp; apply: LC3.
    + apply/imsetP; exists (g q)=>//.
  - move=> p; apply (LC3' (f p)); apply/imsetP; exists p=>//.
Qed.

Lemma SC1 P Q f g :
  P<~f~g~>Q -> incr (g \o f).
Proof. move=> [_ LC2 _ _]//. Qed.

Lemma SC2 P Q f g :
  P<~f~g~>Q -> incr (f \o g).
Proof. move=> [LC1 _ _ _]//. Qed.

Lemma PC1 P Q f g p :
  P<~f~g~>Q ->
  p \in g @: setT -> f p = \join_(q | g q == p) q.
Proof.
  move=> [LC1 _ LC3 _] p_in_gQ.
  have gfp_eq_p : g (f p) = p
    by rewrite /quasi melton_3_3 in LC3; rewrite LC3 in p_in_gQ.
  have fp_in_gpip : f p \in g @^-1: [set p]
    by rewrite in_set gfp_eq_p; exact: set11.
  have gq_eq_p_if_q_in_gpi_p : forall q, q \in g @^-1: [set p] -> g(q) = p
    by move=> q; rewrite in_set in_set1; apply/eqP.
  have q_le_fp_if_q_in_gpip : forall q, q \in g @^-1: [set p] -> q <= f(p)
    by move=> q /(gq_eq_p_if_q_in_gpi_p q) <-; exact: LC1.
  have fp_le : f p <= \join_(q | g q == p) q.
    apply: joins_min.
      by apply/eqP; exact gfp_eq_p.
    exact: le_refl.
  have fp_ge : \join_(q | g q == p) q <= f p.
    apply/joinsP => q /eqP gq_eq_p.
    apply q_le_fp_if_q_in_gpip.
    rewrite in_set gq_eq_p.
    exact: set11.
  by apply: le_anti; apply/andP.
Qed.

Lemma PC2 P Q f g q :
  P<~f~g~>Q ->
  q \in f @: setT -> g q = \join_(p | f p == q) p.
Proof. move/melton_3_2/PC1. exact. Qed.

Lemma melton_3_7_1 P Q f g q :
  P<~f~g~>Q ->
  q \in f @: setT -> g q = \join_(p in f@^-1: [set q]) p.
Proof.
  move=> LC q_in_fP.
  rewrite (PC2 LC q_in_fP).
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

Lemma melton_3_7_2 P Q f g p :
  P<~f~g~>Q ->
  p \in g @: setT -> f p = \join_(q in g@^-1: [set p]) q.
Proof. move/melton_3_2/melton_3_7_1. exact. Qed.

Lemma melton_3_7_1_full P Q f g q :
  P<~f~g~>Q ->
  q \in f @: setT ->
  g q \in f@^-1: [set q] /\ forall p, p \in f@^-1: [set q] -> p <= g q.
Proof.
  move=> LC q_in_fP; split; first last.
    rewrite (melton_3_7_1 LC q_in_fP) => p' p'_in_fq .
    exact: (joins_min p'_in_fq).
  move: LC => [_ _ _ LC4]; rewrite/quasi/eqfun/= in LC4.
  move: q_in_fP => /imsetP [p _ q_eq_fp].
  rewrite in_set q_eq_fp LC4; exact: set11.
Qed.

Lemma melton_3_7_2_full P Q f g p :
  P<~f~g~>Q ->
  p \in g @: setT ->
  f p \in g@^-1: [set p] /\ forall q, q \in g@^-1: [set p] -> q <= f p.
Proof. move/melton_3_2/melton_3_7_1_full. exact. Qed.

Lemma CC1 P Q f g p p' :
  P<~f~g~>Q ->
  g (f p) = p' -> g (f p') = p'.
Proof. by move=> [_ _ _ LC4] <-; rewrite/quasi/eqfun/= in LC4; rewrite LC4. Qed.

Lemma CC2 P Q f g q q' :
  P<~f~g~>Q ->
  f (g q) = q' -> f (g q') = q'.
Proof. move/melton_3_2/CC1. exact. Qed.

Lemma melton_3_8_1 P Q f g q :
  P<~f~g~>Q ->
  f (g q) = \meet_(q' in f @: setT | q <= q') q'.
Proof.
  move=> [LC1 _ _ LC4]; rewrite/quasi/eqfun/= in LC4.
  have fgq_in_qleq': f (g q) \in [set q' in f @: setT | q <= q']
    by rewrite in_set; apply/andP; split => //; apply/imsetP; exists (g q).
  have fgq_le_q'_if : forall q', q' \in f @: setT -> q <= q' -> f (g q) <= q'.
    move=> q' /imsetP [p] _ -> q_le_q'.
    by move/(omorph_le g)/(omorph_le f) in q_le_q'; rewrite LC4 in q_le_q'.
  have fgq_le : f (g q) <= \meet_(q' in [set f x | x in [set: P]] | q <= q') q'
    by apply/meetsP => q' /andP [/fgq_le_q'_if q'_in_fiP /q'_in_fiP q_le_q'].
  have fgq_ge : \meet_(q' in [set f x | x in [set: P]] | q <= q') q' <= f (g q).
    apply/meets_max => //.
    rewrite setIdE in_setI in fgq_in_qleq'.
    move/andP: fgq_in_qleq' => [fgq_in_fP fgq_over_q].
    rewrite in_set in fgq_over_q.
    apply/andP => //.
  exact/le_anti/andP.
Qed.

Lemma melton_3_8_2 P Q f g p :
  P<~f~g~>Q ->
  g (f p) = \meet_(p' in g @: setT | p <= p') p'.
Proof. move/melton_3_2/melton_3_8_1. exact. Qed.

Lemma melton_3_9_1 P Q f g q :
  P<~f~g~>Q ->
  g q = \join_(q'' in f@^-1: [set \meet_(q' in f @: setT | q <= q') q']) q''.
Proof.
  move=> L; case L => [_ _ /ltac:(rewrite/quasi/eqfun/=) LC3 _].
  have: g q = \join_(p in f@^-1: [set f (g q)]) p
    by rewrite -[in LHS]LC3 (melton_3_7_1 L) => //; apply/imsetP; exists (g q).
  by rewrite melton_3_8_1.
Qed.

Lemma melton_3_9_2 P Q f g p :
  P<~f~g~>Q ->
  f p = \join_(p'' in g@^-1: [set \meet_(p' in g @: setT | p <= p') p']) p''.
Proof. move/melton_3_2/melton_3_9_1. exact. Qed.

Definition meetOfInIs {L : finTBLatticeType (Order.Disp tt tt)} (A B : {set L}) (x : L) : Prop :=
  (forall a, a \in A -> x <= a)
  /\ (forall b, b \in B -> (forall a, a \in A -> b <= a) -> b <= x)
  /\ x \in B.
Notation "'meet' 'of' A 'in' B 'is' x" := (meetOfInIs A B x) (at level 30).

Definition joinOfInIs {L : finTBLatticeType (Order.Disp tt tt)} (A B : {set L}) (x : L) : Prop :=
  (forall a, a \in A -> a <= x)
  /\ (forall b, b \in B -> (forall a, a \in A -> a <= b) -> x <= b)
  /\ x \in B.
Notation "'join' 'of' A 'in' B 'is' x" := (joinOfInIs A B x) (at level 30).

Check forall (P Q : finTBLatticeType (Order.Disp tt tt)) f g (A : {set P}),
  P<~f~g~>Q ->
  A \subset g @: setT ->
  (forall p : {b | meet of A in (g @: setT) is b}, exists b, meet of A in setT is b /\ b = proj1_sig p)
  /\ (forall p : {b | meet of A in setT is b}, exists b, meet of A in (g @: setT) is b /\ b = proj1_sig p).

Lemma melton_3_11_1 {P Q : finTBLatticeType (Order.Disp tt tt)} f g (A : {set P}) :
  P<~f~g~>Q ->
  A \subset g @: setT ->
  (forall b, meet of A in (g @: setT) is b <-> meet of A in setT is b).
Proof.
  move=> [_ LC2 LC3 LC4] A_subset_gQ b.
  rewrite/quasi/eqfun/= in LC3; rewrite/quasi/eqfun/= in LC4.
  have gfa_eq_a a (a_in_A : a \in A) : g (f a) = a
    by move: A_subset_gQ => /subsetP /(_ a a_in_A) /imsetP [q _ ->]; exact: LC3.
  split; first last.
  - move=> [b_le_a [p_le_b _]].
    split => //; split.
      by move=> x' _ x'_le_a; apply: p_le_b => //.
    have gfb_le_gfa a (a_in_A : a \in A) : g (f b) <= g (f a).
      apply/(omorph_le g)/(omorph_le f); exact: b_le_a.
    have gfb_le_a a (a_in_A : a \in A) : g (f b) <= a
      by rewrite -(gfa_eq_a a a_in_A); exact: gfb_le_gfa.
    have b_eq_gfb : b = g (f b)
      by apply/le_anti/andP; split => //; apply: p_le_b => //.
    apply/imsetP; exists (f b) => //.
  - move=> [b_le_a [b_greatest b_in_gQ]].
    split => //; split => // d _ d_lb_A.
    have gfd_le_gfa a (a_in_A : a \in A) : d <= g (f d) <= g (f a)
      by apply/andP; split => //; apply/(omorph_le g)/(omorph_le f); exact: d_lb_A.
    have gfd_in_gQ : g (f d) \in g @: setT by apply/imsetP; exists (f d) => //.
    have gfd_le_b : g (f d) <= b.
      apply: (b_greatest _ gfd_in_gQ) => a a_in_A.
      rewrite -(gfa_eq_a a a_in_A).
      by move: gfd_le_gfa => /(_ a a_in_A) /andP [_ gfd_eq_gfa].
    exact: le_trans (LC2 d) gfd_le_b.
Qed.

Lemma melton_3_11_1' {P Q : finTBLatticeType (Order.Disp tt tt)} f g (A : {set P}) :
  P<~f~g~>Q ->
  A \subset g @: setT ->
  (forall p : {b | meet of A in (g @: setT) is b}, exists b, meet of A in setT is b /\ b = proj1_sig p)
  /\ (forall p : {b | meet of A in setT is b}, exists b, meet of A in (g @: setT) is b /\ b = proj1_sig p).
Proof.
  move=> LC A_subset_gQ; split=> p; exists (proj1_sig p); split=> //;
  apply/(melton_3_11_1 LC A_subset_gQ); exact (proj2_sig p).
Qed.

Lemma melton_3_11_2 {P Q : finTBLatticeType (Order.Disp tt tt)} f g (A : {set P}) :
  P<~f~g~>Q ->
  A \subset g @: setT ->
  (forall a', join of A in setT is a' -> join of A in (g @: setT) is (g (f a'))).
Proof.
  move=> [_ LC2 /ltac:(rewrite/quasi/eqfun/=) LC3 _] A_subset_gQ a' [a'_ub_A [a'_least _]].
  split => [a a_in_A |].
    exact: le_trans (a'_ub_A a a_in_A) (LC2 a').
  split; first last => [| p p_in_gQ p_ub_A].
    by apply/imsetP; exists (f a') => //; rewrite in_set.
  have p_eq_gfp : g (f p) = p
    by move: p_in_gQ => /imsetP [q _ ->]; exact: LC3.
  rewrite -p_eq_gfp; apply/(omorph_le g)/(omorph_le f); exact: a'_least.
Qed.
