From HB Require Import structures.

(* SSReflect *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import order eqtype fintype finset seq choice ssrnat.
Import Order.LTheory.

From Lagois Require Import lagois.
Open Scope order_scope.
From Coq Require Import Logic.EqdepFacts.
Require Import Coq.Arith.Wf_nat.

HB.mixin Record IsLagoisGraph V of Equality V := {
  lattice : V -> {d & finTBLatticeType d} ;
  edge v v' : option (Lagois.type (projT2 (lattice v)) (projT2 (lattice v'))) ;

  edge_irefl v : edge v v = None ;

  edge_sym v v' fg :
    edge v v' = Some fg -> {gf | edge v' v = Some gf /\ fg.1 = gf.2} ;
}.
HB.structure Definition LagoisGraph := {T of IsLagoisGraph T & Equality T}.
Notation "L( v )" := (projT2 (lattice v)).
Notation "v @ f > v'" := (edge v v' = Some f) (at level 70, f at level 60).

Inductive flow (G : LagoisGraph.type) : forall v v' : G, L(v) -> L(v') -> Prop :=
  | flow_le v (p p' : L(v)) :
      p <= p' -> flow p p'
  | flow_lc v v' p f :
      v @f> v' -> flow p (f.1 p)
  | flow_trans v v' v'' (p : L(v)) (q : L(v')) (r : L(v'')) :
      flow p q -> flow q r -> flow p r.

Reserved Notation "v ~> v'" (at level 80).
Reserved Notation "v ~> v' :> G".
Inductive path (G : LagoisGraph.type) : G -> G -> Type :=
  | path_empty v : v~>v
  | path_cons v v' v'' f : v@f>v' -> v'~>v'' -> v~>v''
where "v ~> v'" := (path v v')
and   "v ~> v' :> G" := (@path G v v').
Notation "'ε'" := (path_empty _).

Fixpoint path2fun G v v' (f : v ~> v' :> G) : L(v) -> L(v') :=
  match f with
  | path_empty _ => idfun
  | path_cons _ _ _ f' _ g => path2fun g \o f'.1
  end.
Coercion path2fun : path >-> Funclass.

Fixpoint path2seq_aux G v v' (f : v ~> v' :> G) : seq G :=
  match f with
  | path_empty _ => [::]
  | path_cons _ v' _ _ _ g => v' :: path2seq_aux g
  end.

Definition path2seq G v v' (f : v ~> v' :> G) : seq G :=
  match f with
  | path_empty _ => [::]
  | path_cons v v' _ _ _ g => [:: v, v' & path2seq_aux g]
  end.
Coercion path2seq : path >-> seq.

Definition edge2path G v v' f' (f : v @f'> v') : v ~> v' :> G :=
  path_cons f (path_empty v').
Coercion edge2path : eq >-> path.

Reserved Notation "f \* g" (at level 60, right associativity).
Fixpoint path_concat G v v' v'' (f : v ~> v' :> G) (g : v' ~> v'') : v ~> v'' :=
  match f in @path _ v v' return @path G v' v'' -> @path G v v'' with
  | path_empty _ => fun g => g
  | path_cons _ _ _ f' vf'v' h => fun g => path_cons vf'v' (h \* g)
  end g
where "f \* g" := (path_concat f g).

Reserved Notation "f ^<~".
Fixpoint path_reverse G v v'(f : v ~> v' :> G ) : v' ~> v :=
  match f with
  | path_empty _ => path_empty _
  | path_cons v v'' v' f' vf'v'' g =>
      g^<~ \* (path_cons
          (proj1 (projT2 (edge_sym v v'' f' vf'v''))) (path_empty v))
  end
where "f ^<~" := (path_reverse f).

Section LagoisGraphTheory.
Variable (G : LagoisGraph.type).

Definition flow_secure (v : G) := forall (p p' : L(v)), flow p p' -> p <= p'.

Definition flow_secure_graph := forall v : G, flow_secure v.

Definition loop_secure v (f : v ~> v :> G) := forall (p : L(v)), p <= f p.

Definition loop_secure_vertex v := forall (f : v ~> v :> G), loop_secure f.

Definition loop_secure_graph := forall v : G, loop_secure_vertex v.

Lemma pathcomp2funcomp (v v' v'' : G) (f : v ~> v') (g : v' ~> v'') :
   f \* g =1 g \o f.
Proof.
  move=> p; elim: v v' / f g p => [ // | v v' v0 h' h f g g0 h0 //=].
Qed.

Lemma path_nondecreasing v v' (f : v ~> v' :> G) :
  nondecreasing f.
Proof.
  elim: f => [ _// | {}x {}y z f' e g ndg p p' plep' /=].
  exact/ndg/(omorph_le f'.1).
Qed.

Lemma flow2path (v v' : G) (p : L(v)) (q : L(v')) :
  flow p q -> exists (f : v ~> v' :> G), f p <= q.
Proof.
  elim=> [ {p q}v p p' plep'
         | {p}v {q}v' p f vfv'
         | {p}v {q}v' v'' p q r _ [g IHg] _ [h IHh] ].
  - exists (path_empty v)=>//.
  - exists vfv'=>//.
  - exists (g \* h).
    rewrite pathcomp2funcomp /comp.
    move/(path_nondecreasing h) in IHg.
    exact: le_trans IHg IHh.
Qed.

Lemma path2flow (v v' : G) (p : L(v)) : forall (f : v ~> v' :> G), flow p (f p).
Proof.
  move=> f; elim: v v' / f p => [ v p | v v' v'' f' f h IH p].
    exact/flow_le/lexx.
  apply: flow_trans.
    exact: flow_lc f.
  by move/(_ (f p)) in IH.
Qed.

Lemma vertex_flow_secure_iff_loop_secure (v : G) :
  flow_secure v <-> loop_secure_vertex v .
Proof.
  rewrite/loop_secure_vertex/flow_secure/loop_secure; split.
  - move=> plep'_if_p2p' f p; exact/plep'_if_p2p'/path2flow.
  - move=> H1 p p' p2p'; move: (flow2path p2p') => [h Hh].
    apply: le_trans.
      exact: H1.
      exact: Hh.
Qed.

Lemma flow_secure_graph_is_loop_secure :
  flow_secure_graph <-> loop_secure_graph.
Proof.
  split => [ fcG v | scG v ].
    - move/(_ v) in fcG; exact/vertex_flow_secure_iff_loop_secure.
    - move/(_ v) in scG; exact/vertex_flow_secure_iff_loop_secure.
Qed.

Lemma pathcons2funcomp (v v' v'' : G) f' (f : v @ f' > v') (g : v' ~> v'') :
  path_cons f g =1 g \o f.
Proof. trivial. Qed.

Lemma pathcons2concat (v v' v'' : G) f' (f : v @ f' > v') (g : v' ~> v'') :
  path_cons f g = f \* g.
Proof. trivial. Qed.

Lemma reversepathcons2funcomp
    (v v' v'' : G) f' (f : v @ f' > v') (g : v' ~> v'') :
  (path_cons f g)^<~ =1 f^<~ \o g^<~.
Proof. by move=> p; rewrite pathcomp2funcomp. Qed.

Lemma reverse_path_loop_secure v v' (f : v ~> v') : loop_secure (f \* f^<~).
Proof.
  elim: f => [ _// | {}v {}v' v'' f' f g IHg p].
  have fp_le_ggfp: f p <= (path_reverse g) (g (f p)).
    move/(_ (f p)) in IHg.
    rewrite/loop_secure in IHg.
    by rewrite pathcomp2funcomp /comp in IHg.
  rewrite pathcomp2funcomp /comp.
  rewrite pathcons2funcomp /comp.
  rewrite reversepathcons2funcomp /comp.
  have p_le_prffp : p <= path_reverse f (f p).
    rewrite/=.
    move: (edge_sym v v' f' f) => [fn [_ r]]/=.
    rewrite r.
    exact: lc2.
  move/(path_nondecreasing (path_reverse f)) in fp_le_ggfp.
  exact: (le_trans p_le_prffp fp_le_ggfp).
Qed.

Fixpoint pathlen (v v' : G) (f : v ~> v') : nat :=
  match f with
  | path_empty _ => 0
  | path_cons _ _ _ _ _ g => 1 + pathlen g
  end.

Lemma pathlen_homo (v1 v2 v3 : G) (f : v1 ~> v2) (g : v2 ~> v3) :
  pathlen (f \* g) = pathlen f + pathlen g.
Proof. elim: v1 v2 / f g => // v1 v2 vn h' h f IH g /=; by rewrite IH. Qed.

Definition looplen (f : {v & v ~> v :> G}) := pathlen (projT2 f).

Definition lelooplen (f g : {v : G & v ~> v}) := (looplen f < looplen g).

Lemma fsubg_fleg (f g : {v : G & v ~> v}) :
  lelooplen f g -> (looplen f < looplen g)%coq_nat.
Proof. exact: ltP. Qed.

Lemma subloopwf : well_founded lelooplen.
Proof. apply: (well_founded_lt_compat _ looplen _ fsubg_fleg). Qed.

Lemma pathconcatA (v1 v2 v3 v4 : G) (f : v1~>v2) (g : v2~>v3) (h : v3~>v4) :
  (f \* g) \* h = f \* (g \* h).
Proof. by elim: v1 v2 / f g h => // v1 v2 v3' f' f g IH h j; rewrite /= IH. Qed.

Lemma LagoisGraph_dec (v1 v2 : G) : {v1 = v2} + {v1 <> v2}.
Proof. case v1_eq_v2: (v1 == v2); move/eqP in v1_eq_v2. by left. by right. Qed.

Lemma edgeuniq (v v' : G) f' (f : v @f'> v') : uniq f.
Proof.
  rewrite /=; apply/andP; split=> //.
  have v_neq_v': v <> v'.
    move=> v_eq_v'.
    have vv'irefl: edge v v' = None by rewrite v_eq_v'; exact: edge_irefl.
    by rewrite vv'irefl in f.
  move/eqP in v_neq_v'.
  rewrite Bool.negb_andb.
  by apply/orP; left.
Qed.

Lemma nuniqdecomp v1 v2 (f : v1 ~> v2 :> G) : ~~ uniq f ->
  exists v (fl : v1 ~> v) (g : v ~> v) (fr : v ~> v2),
    0 < pathlen g /\ f = fl \* g \* fr.
Proof.
  rewrite /uniq; elim: v1 v2 / f => //= v1 v2 v3 g' g f IH.
  rewrite Bool.negb_andb => /orP [{IH}vl_in_f | un_f].
    have v1_neq_v2 : v1 <> v2.
      move=> v1_eq_v2.
      have v1v2irefl: edge v1 v2 = None by rewrite v1_eq_v2; exact: edge_irefl.
      by rewrite v1v2irefl in g.
    rewrite Bool.negb_involutive /in_mem /= in vl_in_f.
    move: vl_in_f => /orP [/eqP //| {v1_neq_v2}v1_in_f].
    rewrite pathcons2concat.
    move: (edge2path g) => {g'}g.
    elim: v2 v3 / f v1 g v1_in_f=> [// | v2 v3 v4 f' f g IH v1 h /= v1_in_fg].
    move: v1_in_fg => /orP [/eqP v1_eq_v3 | key].
      elim: v1_eq_v3 h g f' f IH => h g f' f _.
      exists v1; exists ε; exists (h \* f); exists g; split.
        by rewrite pathlen_homo addnC.
      by rewrite pathcons2concat [ε \* _]/= pathconcatA.
    move: (IH v1 (h \* f) key) => [v [fl [g0 [fr [lt0g0 hfg_eq_flg0fr]]]]].
    exists v. exists fl; exists g0; exists fr; split => //.
    by rewrite pathcons2concat -pathconcatA.
  case: v2 v3 / f g' g IH un_f => //= v2 v3 v4 h' h p g' g IH un_f.
  move: (IH un_f) => [v [fl [gp [fr [lt0gp hp_eq_flgpfr]]]]].
  exists v; exists (g \* fl); exists gp; exists fr; split => //=.
  by rewrite hp_eq_flgpfr.
Qed.

Lemma loopdecomp v (f : v ~> v :> G) :
    f = ε
    \/ (exists v' g' (g : v @g'> v') (h : v' ~> v) (_ : uniq h), f = g \* h)
    \/ (
      exists v' v'' fl' (fl : v @fl'> v')
          (gl : v' ~> v'')
          (h : v'' ~> v'')
          (gr : v'' ~> v),
      f = fl \* gl \* h \* gr /\ 0 < pathlen h
    ).
Proof.
  refine (
    match f as f' in vl ~> vr return
      forall (vr_eq_vl : vr = vl) (vl_eq_v : vl = v),
      f = eq_rect vl (fun x => x ~> x) (eq_rect vr _ f' vl vr_eq_vl) v vl_eq_v ->
      f = ε \/
      (exists v' g' (g : v @g'> v') (h : v' ~> v) (_ : uniq h), f = g \* h) \/
      (exists (v' v'' : G) (fl' : Lagois.type L( v) L( v')) (fl : v @ fl' > v')
      (gl : v' ~> v'' :> G) (h : v'' ~> v'' :> G) (gr : v'' ~> v :> G),
      f = fl \* gl \* h \* gr /\ 0 < pathlen h)
    with
    | ε => _
    | path_cons _ _ _ _ _ _ => _
    end erefl erefl erefl
  ).
  - move=> p; left; symmetry.
    rewrite H -[(eq_rect s _ ε s p)](Eqdep_dec.eq_rect_eq_dec); first last.
      exact: LagoisGraph_dec.
    refine (match vl_eq_v with erefl => _ end).
    apply: Eqdep_dec.eq_rect_eq_dec.
      exact: LagoisGraph_dec.
  - case un_p : (uniq p).
      right; left; rewrite {}H; refine (match vl_eq_v with erefl => _ end).
      rewrite -(Eqdep_dec.eq_rect_eq_dec LagoisGraph_dec).
      move: t e p un_p.
      refine (match vr_eq_vl with erefl => _ end) => t e p un_p.
    rewrite -(Eqdep_dec.eq_rect_eq_dec LagoisGraph_dec).
      by exists s0; exists t; exists e; exists p; exists un_p.
    right; right; rewrite {}H; refine (match vl_eq_v with erefl => _ end).
    rewrite -(Eqdep_dec.eq_rect_eq_dec LagoisGraph_dec).
    move: t e p un_p.
    refine (match vr_eq_vl with erefl => _ end) => t e p un_p.
    rewrite -(Eqdep_dec.eq_rect_eq_dec LagoisGraph_dec).
    move/negbT in un_p.
    move: (nuniqdecomp un_p) => [v' [x [g [fr [lt0g p_eq_xgfr]]]]].
    exists s0. exists v'; exists t; exists e; exists x; exists g; exists fr.
    split => //.
    by rewrite p_eq_xgfr.
Qed.

Lemma loopdecomp' v (f : v ~> v :> G) :
  f = ε
  \/ (exists v' g' (g : v @g'> v') (h : v' ~> v) (_ : uniq h), f = g \* h)
  \/ (
    exists v' f1 (g : v' ~> v') f2, f = f1 \* g \* f2
    /\ lelooplen (existT _ v' g) (existT _ v f)
    /\ lelooplen (existT _ v (f1 \* f2)) (existT _ v f)
  ).
Proof.
  case: (loopdecomp f).
    by left.
  case.
    by right; left.
  move=> [v' [v'' [fl' [fl [gl [h [gr [f_eq lt0h]]]]]]]].
  right; right.
  exists v''; exists (fl \* gl); exists h; exists (gr).
  split => //; split.
    rewrite /lelooplen /looplen f_eq /= 2!pathlen_homo addnC
        [pathlen gl + (pathlen h + pathlen gr)]addnC.
    by rewrite ltEnat /= -{1}(addn0 (pathlen h)) -2!addnA ltn_add2l addnC
        [pathlen gl + 1]addnC.
  rewrite /lelooplen /looplen f_eq /= pathlen_homo ltEnat /= ltn_add2l.
  rewrite pathlen_homo ltn_add2l pathlen_homo addnC -{1}(addn0 (pathlen gr)).
  by rewrite ltn_add2l.
Qed.

Fixpoint loop_ind_aux
    (P : forall v : G, v ~> v -> Prop)
    (bc_1 : forall v : G, P v (ε))
    (bc_2 : forall (v v' : G) g' (g : v @ g' > v') (h : v' ~> v), uniq h -> P v (g \* h))
    (ic : forall (v v': G) f1 f2 h, P v' h -> P v (f1 \* f2) -> P v (f1 \* h \* f2))
    v (f : v ~> v) (ACC : Acc lelooplen (existT _ v f)) {struct ACC} : P v f :=
  match loopdecomp' f with
  | or_introl f_eq_ε => eq_rect ε _ (bc_1 v) f (esym f_eq_ε)
  | or_intror rest =>
      match rest with
      | or_introl f_imm =>
          let: ex_intro v' (ex_intro g' (ex_intro g (ex_intro h (ex_intro un_h f_imm)))) := f_imm in
            eq_rect (g \* h) _ (bc_2 v v' g' g h un_h) f (esym f_imm)
      | or_intror f_dup =>
          let: ex_intro v' (ex_intro f1 (ex_intro g (ex_intro f2 (conj f_eq (conj glef f1f1lef))))) := f_dup in
          let Pg := loop_ind_aux bc_1 bc_2 ic (Acc_inv ACC glef) in
          let Pf1f2 := loop_ind_aux bc_1 bc_2 ic (Acc_inv ACC f1f1lef) in
            eq_rect (f1 \* g \* f2) _ (ic v v' f1 f2 g Pg Pf1f2) f (esym f_eq)
      end
  end.

Definition loop_ind
    (P : forall v : G, v ~> v :> G -> Prop)
    (bc_1 : forall v : G, P v (ε))
    (bc_2 : forall (v v' : G) g' (g : v @ g' > v') (h : v' ~> v), uniq h -> P v (g \* h))
    (ic : forall (v v': G) f1 f2 h, P v' h -> P v (f1 \* f2)-> P v (f1 \* h \* f2))
    v (f : v ~> v) : P v f :=
  loop_ind_aux bc_1 bc_2 ic (subloopwf (existT _ v f)).

Definition simply_secure := forall (v v' : G) (f : v ~> v') (g : v' ~> v),
  uniq f -> uniq g -> forall p, p <= (f \* g)(p).

Proposition simply_secure_iff_loop_secure : simply_secure <-> loop_secure_graph.
Proof.
  split; first last => [ Gls v v' f g _ _ p | Gss v f ].
    exact: Gls.
  rewrite /loop_secure; elim/loop_ind: v / f => [ // | v v' f' f g un_g p |].
    have un_f : uniq f := edgeuniq f.
    by move/(_ _ _ _ _ un_f un_g) in Gss.
  move=> v v' f1 f2 h sh sf1f2 p.
  move/(_ p) in sf1f2; rewrite pathcomp2funcomp /= in sf1f2.
  move/(_ (f1 p))/(path_nondecreasing f2) in sh.
  do 2! rewrite pathcomp2funcomp /=.
  exact: le_trans sf1f2 sh.
Qed.

End LagoisGraphTheory.

HB.mixin Record IsLagoisVForest G of LagoisGraph G := {
  vacyclic v v' (f g : v ~> v' :> G) : uniq f -> uniq g -> f =1 g ;
}.
HB.structure Definition LagoisVForest :=
    {T of IsLagoisVForest T & IsLagoisGraph T & Finite T}.

Section LagoisVForestTheory.
Variable (G : LagoisVForest.type).

Theorem VForest_loop_secure : loop_secure_graph G.
Proof.
  move=> v f.
  elim/loop_ind: v / f => [ _// | v v' g' g h un_h p | v v' f1 f2 h sh sf1f2 p].
    move: (edge_sym v v' g' g) => [f' [f f_eq]].
    have un_erev : uniq f by exact: edgeuniq.
    have p_eq_erev : h =1 f by exact: vacyclic.
    rewrite pathcomp2funcomp /= p_eq_erev f_eq.
    exact: lc2.
  move/(_ p) in sf1f2; rewrite pathcomp2funcomp /= in sf1f2.
  move/(_ (f1 p))/(path_nondecreasing f2) in sh.
  do 2! rewrite pathcomp2funcomp /=.
  exact: le_trans sf1f2 sh.
Qed.

End LagoisVForestTheory.

HB.mixin Record IsLagoisForest G of LagoisGraph G := {
  acyclic v v' (f g : v ~> v' :> G) : uniq f -> uniq g -> f = g ;
}.
HB.structure Definition LagoisForest :=
    {T of IsLagoisForest T & LagoisVForest T & IsLagoisGraph T & Finite T}.

Section LagoisForestTheory.
Variable (G : LagoisForest.type).

(* Observe that this lemma can be proven without vacyclic *)
Lemma LagoisForest_vacyclic v v' (f g : v ~> v' :> G) :
  uniq f -> uniq g -> f =1 g.
Proof. by move=> un_f un_g p; rewrite (acyclic _ _ _ _ un_f un_g). Qed.

Lemma uniqloopε v (f : v ~> v :> G) : uniq f -> f = ε.
Proof. move=> uf; rewrite (acyclic _ _ f ε) => //. Qed.

Theorem Forest_loop_secure : loop_secure_graph G.
Proof. exact: VForest_loop_secure. Qed.

End LagoisForestTheory.
