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

(* Definition 11 *)
HB.mixin Record IsLagoisGraph V of Equality V := {
  lattice : V -> {d & porderType d} ;
  edge v v' : bool ;
  label v v' : edge v v' -> Lagois.type (projT2 (lattice v)) (projT2 (lattice v')) ;

  edge_irefl v : edge v v = false ;
  edge_sym v v' : edge v v' -> edge v' v ;
  label_sym v v' p p' : (label v v' p).1 =1 (label v' v p').2;
}.
HB.structure Definition LagoisGraph := {T of IsLagoisGraph T & Equality T}.
Notation "L( v )" := (projT2 (lattice v)).
Notation "v @> v'" := (edge v v' = true) (at level 70).

Definition edge2label (G : LagoisGraph.type) (v v' : G) (f : v @> v') := label v v' f.
Coercion edge2label : eq >-> Lagois.type.

(* Definition 12 *)
Inductive flow (G : LagoisGraph.type) :
    forall v v' : G, L(v) -> L(v') -> Prop :=
  | flow_le v (p p' : L(v)) :
      p <= p' -> flow p p'
  | flow_lc v v' p (f : v @> v') :
      flow p (f.1 p)
  | flow_trans v v' v'' (p : L(v)) (q : L(v')) (r : L(v'')) :
      flow p q -> flow q r -> flow p r.

Reserved Notation "v ~> v'" (at level 80).
Reserved Notation "v ~> v' :> G".
Inductive path (G : LagoisGraph.type) : G -> G -> Type :=
  | path_empty v : v~>v
  | path_cons v v' v'' : v@>v' -> v'~>v'' -> v~>v''
where "v ~> v'" := (path v v')
and   "v ~> v' :> G" := (@path G v v').
Notation "'ε'" := (path_empty _).

Fixpoint path2fun G v v' (f : v ~> v' :> G) : L(v) -> L(v') :=
  match f with
  | path_empty _ => idfun
  | path_cons _ _ _ f g => path2fun g \o f.1
  end.
Coercion path2fun : path >-> Funclass.

Fixpoint path2seq G v v' (f : v ~> v' :> G) : seq G :=
  match f with
  | path_empty v => [:: v]
  | path_cons v _ _ _ g => v :: path2seq g
  end.
Coercion path2seq : path >-> seq.

Definition edge2path G v v' (f : v @> v') : v ~> v' :> G :=
  path_cons f (path_empty v').
Coercion edge2path : eq >-> path.

Reserved Notation "f \* g" (at level 60, right associativity).
Fixpoint path_concat G v v' v'' (f : v ~> v' :> G) (g : v' ~> v'') : v ~> v'' :=
  match f in @path _ v v' return @path G v' v'' -> @path G v v'' with
  | path_empty _ => fun g => g
  | path_cons _ _ _ f' h => fun g => path_cons f' (h \* g)
  end g
where "f \* g" := (path_concat f g).

Reserved Notation "f ^<~".
Fixpoint path_reverse G v v' (f : v ~> v' :> G ) : v' ~> v :=
  match f with
  | path_empty _ => path_empty _
  | path_cons v v'' v' f' g =>
      g^<~ \* (path_cons (edge_sym _ _ f') (path_empty v))
  end
where "f ^<~" := (path_reverse f).

Section LagoisGraphTheory.
Variable (G : LagoisGraph.type).

Lemma edge_uip (v v' : G) (f g : v @>v') : f = g.
Proof.
  case: (edge v v') f g => [f g | //].
  by rewrite (Eqdep_dec.UIP_refl_bool true f)
             (Eqdep_dec.UIP_refl_bool true g).
Qed.


Lemma path_idr (v1 v2 : G) (f : v1 ~> v2) : f = f \* ε.
Proof.
  elim: v1 v2 / f => [//| v1 v2 v3 f g IH].
  by rewrite [in LHS]IH.
Qed.

Lemma path_reverse_assoc (v1 v2 v3 v4 : G) (f : v1 ~> v2) (g : v2 ~> v3) (h : v3 ~> v4) :
  f \* g \* h = (f \* g) \* h.
Proof.
  elim: v1 v2 / f g => [//| v1 v2 v3' f g IH h' /=].
  by rewrite IH.
Qed.

Lemma path_reverse_distrb (v1 v2 v4 : G) (f : v1 ~> v2) (h : v2 ~> v4) :
  (f \* h)^<~ = (h^<~ \* f^<~).
Proof.
  elim: v1 v2 / f h => [v1 f| v1 v2 v3 f g IH h /=].
    exact: path_idr.
  by rewrite IH path_reverse_assoc.
Qed.

Lemma path_reverse_involution (v1 v2 : G) (f : v1 ~> v2) : f^<~^<~ = f.
Proof.
  elim: v1 v2 / f => [//| v1 v2 v3 f g IH].
  by rewrite path_reverse_distrb IH /= (edge_uip (edge_sym v2 v1 (edge_sym v1 v2 f))).
Qed.

(* Definition 13.1 *)
Definition flow_secure (v : G) := forall (p p' : L(v)), flow p p' -> p <= p'.

(* Definition 13.2 *)
Definition flow_secure_graph := forall v : G, flow_secure v.

(* Definition 14.1 *)
Definition loop_secure v (f : v ~> v :> G) := forall (p : L(v)), p <= f p.

(* Definition 14.2 *)
Definition loop_secure_vertex v := forall (f : v ~> v :> G), loop_secure f.

(* Definition 14.3 *)
Definition loop_secure_graph := forall v : G, loop_secure_vertex v.

Lemma pathcomp2funcomp (v v' v'' : G) (f : v ~> v') (g : v' ~> v'') :
   f \* g =1 g \o f.
Proof.
  move=> p; elim: v v' / f g p => [ // | v v' v0 h f g g0 h0 //=].
Qed.

(* Lemma 2 *)
Lemma path_nondecreasing v v' (f : v ~> v' :> G) :
  nondecreasing f.
Proof.
  elim: f => [ _// | {}x {}y z e g ndg p p' plep' /=].
  exact/ndg/(omorph_le e.1).
Qed.

(* Lemma 1 *)
Lemma flow2path (v v' : G) (p : L(v)) (q : L(v')) :
  flow p q -> exists (f : v ~> v' :> G), f p <= q.
Proof.
  elim=> [ {p q}v p p' plep'
         | {p}v {q}v' p f
         | {p}v {q}v' v'' p q r _ [g IHg] _ [h IHh] ].
  - exists (path_empty v)=>//.
  - exists f=>//.
  - exists (g \* h).
    rewrite pathcomp2funcomp /comp.
    move/(path_nondecreasing h) in IHg.
    exact: le_trans IHg IHh.
Qed.

Lemma path2flow (v v' : G) (p : L(v)) : forall (f : v ~> v' :> G), flow p (f p).
Proof.
  move=> f; elim: v v' / f p => [ v p | v v' v'' f h IH p].
    exact/flow_le/lexx.
  apply: flow_trans.
    exact: flow_lc f.
  by move/(_ (f p)) in IH.
Qed.

(* Proposition 2.1 *)
Proposition vertex_flow_secure_iff_loop_secure (v : G) :
  flow_secure v <-> loop_secure_vertex v .
Proof.
  rewrite/loop_secure_vertex/flow_secure/loop_secure; split.
  - move=> plep'_if_p2p' f p; exact/plep'_if_p2p'/path2flow.
  - move=> H1 p p' p2p'; move: (flow2path p2p') => [h Hh].
    apply: le_trans.
      exact: H1.
      exact: Hh.
Qed.

(* Proposition 2.2 *)
Lemma flow_secure_graph_is_loop_secure :
  flow_secure_graph <-> loop_secure_graph.
Proof.
  split => [ fcG v | scG v ].
    - move/(_ v) in fcG; exact/vertex_flow_secure_iff_loop_secure.
    - move/(_ v) in scG; exact/vertex_flow_secure_iff_loop_secure.
Qed.

Lemma pathcons2funcomp (v v' v'' : G) (f : v @> v') (g : v' ~> v'') :
  path_cons f g =1 g \o f.
Proof. trivial. Qed.

Lemma pathcons2concat (v v' v'' : G) (f : v @> v') (g : v' ~> v'') :
  path_cons f g = f \* g.
Proof. trivial. Qed.

Lemma reversepathcons2funcomp
    (v v' v'' : G) (f : v @> v') (g : v' ~> v'') :
  (path_cons f g)^<~ =1 f^<~ \o g^<~.
Proof. by move=> p; rewrite pathcomp2funcomp. Qed.

(* Lemma 3 *)
Lemma reverse_path_loop_secure v v' (f : v ~> v') : loop_secure (f \* f^<~).
Proof.
  elim: f => [ _// | {}v {}v' v'' f g IHg p].
  have fp_le_ggfp: f p <= (path_reverse g) (g (f p)).
    move/(_ (f p)) in IHg.
    rewrite/loop_secure in IHg.
    by rewrite pathcomp2funcomp /comp in IHg.
  rewrite pathcomp2funcomp /comp.
  rewrite pathcons2funcomp /comp.
  rewrite reversepathcons2funcomp /comp.
  have p_le_prffp : p <= path_reverse f (f p).
    rewrite /=.
    move: (label_sym v v' f (edge_sym v v' f)) => idk.
    rewrite idk.
    exact: lc2.
  move/(path_nondecreasing (path_reverse f)) in fp_le_ggfp.
  exact: (le_trans p_le_prffp fp_le_ggfp).
Qed.

Fixpoint pathlen (v v' : G) (f : v ~> v') : nat :=
  match f with
  | path_empty _ => 0
  | path_cons _ _ _ _ g => 1 + pathlen g
  end.

Lemma pathlen_homo (v1 v2 v3 : G) (f : v1 ~> v2) (g : v2 ~> v3) :
  pathlen (f \* g) = pathlen f + pathlen g.
Proof. elim: v1 v2 / f g => // v1 v2 vn h f IH g /=; by rewrite IH. Qed.

Lemma in_path_homo (v v1 v2 v3: G) (f : v1 ~> v2) (g : v2 ~> v3) :
  v \in path2seq (f \* g) = (v \in path2seq f) || (v \in path2seq g).
Proof.
  elim: v1 v2 / f v3 g => [v1 v2 g | v1 v2 v3 f1 f2 IH v4 g] /=.
    case v_eq_v1: (v \in [:: v1]) => [/=|//].
    case: v1 v2 / g v_eq_v1 => [//|v1 v2 v3 g1 g2 IH /=].
    rewrite in_cons; apply/orP; left.
    by rewrite mem_seq1 in IH.
  move/(_ _ g) in IH.
  case: v3 v4 / g f2 IH => [v3 f2|v3 v4 v5 g1 g2 f2 /= IH1]; first last.
    by rewrite in_cons IH1 [in RHS]in_cons Bool.orb_assoc.
  rewrite -path_idr /= => IH1.
  case v_in_v3 : (v \in [:: v3]); first last.
    by rewrite Bool.orb_false_r.
  rewrite Bool.orb_true_r in_cons.
  apply /orP; right.
  rewrite IH1.
  by apply /orP; right.
Qed.

Lemma uniq_fc4p (v1 v2 v3 : G) (f : v1 ~> v2) (g : v2 ~> v3) : uniq (f \* g) -> uniq f && uniq g.
Proof.
  elim: v1 v2 / f g => [//|v1 v12 v2 f1 f2 /= IH g un_f1f2g].
  move/andP : un_f1f2g => [v1_nin_f2g un_f2g].
  move/(_ g un_f2g) /andP : IH => [un_f2 un_g].
  apply /andP; split=> //.
  apply /andP; split=> //.
  rewrite in_path_homo negb_or in v1_nin_f2g.
  by move/andP : v1_nin_f2g => [v1_nin_f2 _].
Qed.

Definition looplen (f : {v & v ~> v :> G}) := pathlen (projT2 f).

Definition lelooplen (f g : {v : G & v ~> v}) := looplen f < looplen g.

Lemma subloopwf : well_founded lelooplen.
Proof. apply: well_founded_lt_compat=> f g; exact ltP. Qed.

Lemma pathconcatA (v1 v2 v3 v4 : G) (f : v1~>v2) (g : v2~>v3) (h : v3~>v4) :
  (f \* g) \* h = f \* (g \* h).
Proof. by elim: v1 v2 / f g h => // v1 v2 v3' f g IH h j; rewrite /= IH. Qed.

Lemma LagoisGraph_dec (v1 v2 : G) : {v1 = v2} + {v1 <> v2}.
Proof. case v1_eq_v2: (v1 == v2); move/eqP in v1_eq_v2. by left. by right. Qed.

Lemma edgeuniq (v v' : G) (f : v @> v') : uniq f.
Proof.
  rewrite /=; apply/andP; split=> //.
  have v_neq_v': v <> v'.
    move=> v_eq_v'.
    have vv'irefl: edge v v' = None by rewrite v_eq_v'; rewrite edge_irefl.
    by rewrite (vv'irefl nat) in f.
  move/eqP in v_neq_v'.
  rewrite Bool.negb_andb.
  by apply/orP; left.
Qed.

Lemma noloopedge (v v' : G) (f : v @> v') : v <> v'.
Proof.
  move=> v_eq_v'.
    have vv'irefl: edge v v' = None by rewrite v_eq_v'; rewrite edge_irefl.
    by rewrite (vv'irefl nat) in f.
Qed.

Lemma concatpA (v1 v2 v3 v4 : G) (f : v1 ~> v2) (g : v2 ~> v3) (h : v3 ~> v4) :
  f \* g \* h = (f \* g) \* h.
Proof.
  by elim: v1 v2 / f v3 v4 g h =>
      [//| v1 v2 v3 f g IH v4 v5 h j /=];
  rewrite IH.
Qed.

Lemma nuniqdecomp v1 v2 (f : v1 ~> v2 :> G) : ~~ uniq f ->
  exists v (fl : v1 ~> v) (g : v ~> v) (fr : v ~> v2),
    0 < pathlen g /\ f = fl \* g \* fr.
Proof.
  elim:  v1 v2 / f => [// | v1 v2 v3 g f IH].
  rewrite /= Bool.negb_andb => /orP [{IH}v1_in_f | f_un]; first last.
    move: IH => /(_ f_un) [v [fl [h [fr [h_ne f_decomp]]]]].
    exists v; exists (g \* fl); exists h; exists fr; split => [//|].
    by rewrite /= f_decomp.
  rewrite Bool.negb_involutive in v1_in_f.
  move gstar_eq_g: (edge2path g) => g_star.
  have g_star_ne: 0 < pathlen g_star by rewrite -gstar_eq_g.
  rewrite pathcons2concat gstar_eq_g => {gstar_eq_g g}.
  elim: v2 v3 / f v1 v1_in_f g_star g_star_ne =>
      [v2 v1 /= v1_in_v2 g_star g_star_ne|].
    rewrite mem_seq1 in v1_in_v2.
    move/eqP in v1_in_v2.
    exists v1; exists ε; elim: v1_in_v2 g_star g_star_ne => g_star g_star_ne.
    by exists g_star; exists ε.
  move=> v2 v3 v4 g f IH v1 /= v1_in_gf g_star g_star_ne.
  move: v1_in_gf => /orP [/eqP v1_eq_v2 | key].
    elim: v1_eq_v2 g g_star g_star_ne => g g_star g_star_ne.
    by exists v1; exists ε; exists g_star; exists (g \* f).
  have gstarg_ne: 0 < pathlen (g_star \* g) by rewrite pathlen_homo /= addnC.
  move: (IH v1 key (g_star \* g) gstarg_ne) =>
      [v' [fl [g0 [fr [g0_ne gstarg_decomp]]]]].
  exists v'; exists fl; exists g0; exists fr; split => //=.
  by rewrite -gstarg_decomp pathcons2concat concatpA.
Qed.

Lemma loopdecomp v (f : v ~> v :> G) :
    f = ε
    \/ (exists v' (g : v @> v') (h : v' ~> v) (_ : uniq h), f = g \* h)
    \/ (
      exists v' v'' (fl : v @> v')
          (gl : v' ~> v'')
          (h : v'' ~> v'')
          (gr : v'' ~> v),
      f = fl \* gl \* h \* gr /\ 0 < pathlen h
    ).
Proof.
  refine (
    match f as f' in vl ~> vr return
      forall (vr_eq_vl : vr = vl) (vl_eq_v : vl = v),
      f = eq_rect vl (fun x => x ~> x) (eq_rect vr _ f' vl vr_eq_vl) v vl_eq_v->
      f = ε \/
      (exists v' (g : v @> v') (h : v' ~> v) (_ : uniq h), f = g \* h) \/
      (exists (v' v'' : G) (fl : v @> v')
      (gl : v' ~> v'' :> G) (h : v'' ~> v'' :> G) (gr : v'' ~> v :> G),
      f = fl \* gl \* h \* gr /\ 0 < pathlen h)
    with
    | ε => _
    | path_cons _ _ _ _ _ => _
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
      move: e p un_p.
      refine (match vr_eq_vl with erefl => _ end) => e p un_p.
    rewrite -(Eqdep_dec.eq_rect_eq_dec LagoisGraph_dec).
      by exists s0; exists e; exists p; exists un_p.
    right; right; rewrite {}H; refine (match vl_eq_v with erefl => _ end).
    rewrite -(Eqdep_dec.eq_rect_eq_dec LagoisGraph_dec).
    move: e p un_p.
    refine (match vr_eq_vl with erefl => _ end) => e p un_p.
    rewrite -(Eqdep_dec.eq_rect_eq_dec LagoisGraph_dec).
    move/negbT in un_p.
    move: (nuniqdecomp un_p) => [v' [x [g [fr [lt0g p_eq_xgfr]]]]].
    exists s0. exists v'; exists e; exists x; exists g; exists fr.
    split => //.
    by rewrite p_eq_xgfr.
Qed.

Lemma loopdecomp' v (f : v ~> v :> G) :
  f = ε
  \/ (exists v' (g : v @> v') (h : v' ~> v) (_ : uniq h), f = g \* h)
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
  move=> [v' [v'' [fl [gl [h [gr [f_eq lt0h]]]]]]].
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
    (bc_2 : forall (v v' : G) (g : v @> v') (h : v' ~> v),
        uniq h -> P v (g \* h))
    (ic : forall (v v': G) f1 f2 h,
        P v' h -> P v (f1 \* f2) -> P v (f1 \* h \* f2))
    v (f : v ~> v) (ACC : Acc lelooplen (existT _ v f)) {struct ACC} : P v f :=
  match loopdecomp' f with
  | or_introl f_eq_ε => eq_rect ε _ (bc_1 v) f (esym f_eq_ε)
  | or_intror rest =>
      match rest with
      | or_introl f_imm =>
          let: ex_intro v' (ex_intro g
              (ex_intro h (ex_intro un_h f_imm))) := f_imm in
            eq_rect (g \* h) _ (bc_2 v v' g h un_h) f (esym f_imm)
      | or_intror f_dup =>
          let: ex_intro v' (ex_intro f1 (ex_intro g (ex_intro f2
              (conj f_eq (conj glef f1f1lef))))) := f_dup in
          let Pg := loop_ind_aux bc_1 bc_2 ic (Acc_inv ACC glef) in
          let Pf1f2 := loop_ind_aux bc_1 bc_2 ic (Acc_inv ACC f1f1lef) in
            eq_rect (f1 \* g \* f2) _ (ic v v' f1 f2 g Pg Pf1f2) f (esym f_eq)
      end
  end.

(* Theorem 2 *)
Definition loop_ind
    (P : forall v : G, v ~> v :> G -> Prop)
    (bc_1 : forall v : G, P v (ε))
    (bc_2 : forall (v v' : G) (g : v @> v') (h : v' ~> v),
        uniq h -> P v (g \* h))
    (ic : forall (v v': G) f1 f2 h,
        P v' h -> P v (f1 \* f2)-> P v (f1 \* h \* f2))
    v (f : v ~> v) : P v f :=
  loop_ind_aux bc_1 bc_2 ic (subloopwf (existT _ v f)).

(* Definition 15 *)
Definition simply_secure := forall (v v' : G) (f : v ~> v') (g : v' ~> v),
  uniq f -> uniq g -> forall p, p <= (f \* g)(p).

(* Proposition 3 *)
Proposition simply_secure_iff_loop_secure :
  simply_secure <-> loop_secure_graph.
Proof.
  split; first last => [ Gls v v' f g _ _ p | Gss v f ].
    exact: Gls.
  rewrite /loop_secure; elim/loop_ind: v / f => [ // | v v' f g un_g p |].
    have un_f : uniq f := edgeuniq f.
    by move/(_ _ _ _ _ un_f un_g) in Gss.
  move=> v v' f1 f2 h sh sf1f2 p.
  move/(_ p) in sf1f2; rewrite pathcomp2funcomp /= in sf1f2.
  move/(_ (f1 p))/(path_nondecreasing f2) in sh.
  do 2! rewrite pathcomp2funcomp /=.
  exact: le_trans sf1f2 sh.
Qed.

End LagoisGraphTheory.

(* Definition 16 *)
HB.mixin Record IsLagoisVForest G of LagoisGraph G := {
  vacyclic v v' (f g : v ~> v' :> G) : uniq f -> uniq g -> f =1 g ;
}.
HB.structure Definition LagoisVForest :=
    {T of IsLagoisVForest T & IsLagoisGraph T & Finite T}.

Section LagoisVForestTheory.
Variable (G : LagoisVForest.type).

(* Theorem 3 *)
Theorem VForest_loop_secure : loop_secure_graph G.
Proof.
  move=> v f.
  elim/loop_ind: v / f => [ _// | v v'  g h un_h p | v v' f1 f2 h sh sf1f2 p].
    move: (edge_sym v v' g) => g'.
    have un_erev : uniq g' by exact: edgeuniq.
    have p_eq_erev : h =1 g' by exact: vacyclic.
    rewrite pathcomp2funcomp /= p_eq_erev.
    move: (label_sym v v' g g') => ->.
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

(* Corollary 1 *)
Lemma LagoisForest_vacyclic v v' (f g : v ~> v' :> G) :
  uniq f -> uniq g -> f =1 g.
(* Observe that this lemma can be proven without vacyclic *)
Proof. by move=> un_f un_g p; rewrite (acyclic _ _ _ _ un_f un_g). Qed.

Lemma uniqloopε v (f : v ~> v :> G) : uniq f -> f = ε.
Proof. move=> uf; rewrite (acyclic _ _ f ε) => //. Qed.

Theorem Forest_loop_secure : loop_secure_graph G.
Proof. exact: VForest_loop_secure. Qed.

End LagoisForestTheory.

Inductive Bridge (G G' : LagoisGraph.type) (v_abut : G) (v'_abut : G') (fg : Lagois.type L(v_abut) L(v'_abut)) : Type :=
  | lbank : G -> Bridge fg
  | rbank : G' -> Bridge fg.
Arguments lbank {G G' v_abut v'_abut fg}.
Arguments rbank {G G' v_abut v'_abut fg}.

Section Bridge.

Context (G G' : LagoisGraph.type) (v_abut : G) (v'_abut : G') (fg : Lagois.type L(v_abut) L(v'_abut)).

Definition Bridge_eq (v1 v2 : Bridge fg) :=
  match v1, v2 with
  | lbank v1, lbank v2
  | rbank v1, rbank v2 => v1 == v2
  | _v1, _v2 => false
  end.

Lemma Bridge_eq_axiom : eq_axiom Bridge_eq.
Proof.
  move=> v1 v2.
  case: v1 => v1.
  - case: v2 => v2; first last.
      exact: ReflectF.
    rewrite /=.
    case v1_eq_v2: (v1 == v2); move /eqP in v1_eq_v2.
      apply: ReflectT.
      by rewrite v1_eq_v2.
    apply: ReflectF.
    injection.
    exact: v1_eq_v2.
  - case: v2 => v2.
      exact: ReflectF.
    rewrite /=.
    case v1_eq_v2: (v1 == v2); move /eqP in v1_eq_v2.
      apply: ReflectT.
      by rewrite v1_eq_v2.
    apply: ReflectF.
    injection.
    exact: v1_eq_v2.
Qed.

Definition Bridge_lattice (v : Bridge fg) :=
  match v with
  | lbank v => lattice v
  | rbank v' => lattice v'
  end.

Definition Bridge_edge (v1 v2 : Bridge fg) :=
  match v1, v2 with
  | lbank v1, lbank v2
  | rbank v1, rbank v2 => edge v1 v2
  | lbank v1, rbank v2 => (v1 == v_abut) && (v2 == v'_abut)
  | rbank v1, lbank v2 => (v1 == v'_abut) && (v2 == v_abut)
  end.

Lemma Bridge_edge_abuts : Bridge_edge (lbank v_abut) (rbank v'_abut).
Proof. by rewrite /= eq_refl eq_refl. Qed.
Notation "o-o" := (Bridge_edge_abuts).

Lemma Bridge_edge_irefl (v : Bridge fg) :
  Bridge_edge v v = false.
Proof. elim: v => v; exact: edge_irefl. Qed.

Lemma Bridge_edge_sym (v1 v2 : Bridge fg) :
  Bridge_edge v1 v2 -> Bridge_edge v2 v1.
Proof.
  elim: v1 => v1.
    elim: v2 => v2 => /=.
      exact: edge_sym.
    by rewrite Bool.andb_comm.
  elim: v2 => v2 => /=.
    by rewrite Bool.andb_comm.
  exact: edge_sym.
Qed.

Definition labut_id (v1 : G) (v2: G') :
  Bridge_edge (lbank v1) (rbank v2) -> v_abut = v1.
Proof. by move=> /andP [/eqP e _]. Defined.

Definition rabut_id (v1 : G) (v2: G') :
  Bridge_edge (lbank v1) (rbank v2) -> v'_abut = v2.
Proof. by move=> /andP [_ /eqP e]. Defined.

Definition labut_id_inv (v1 : G) (v2: G') :
  Bridge_edge (rbank v2) (lbank v1) -> v_abut = v1.
Proof. by move=> /andP [_ /eqP e]. Defined.

Definition rabut_id_inv (v1 : G) (v2: G') :
  Bridge_edge (rbank v2) (lbank v1) -> v'_abut = v2.
Proof. by move=> /andP [/eqP e _]. Defined.

(*Yeah this his horrible...*)
Definition Bridge_label (v1 v2 : Bridge fg) (e : Bridge_edge v1 v2) :
  Lagois.type (projT2 (Bridge_lattice v1)) (projT2 (Bridge_lattice v2)) :=
match v1, v2 return Bridge_edge v1 v2 -> Lagois.type (projT2 (Bridge_lattice v1)) (projT2 (Bridge_lattice v2)) with
| lbank v1, lbank v2 => fun e => e
| rbank v1, rbank v2 => fun e => e
| lbank v1, rbank v2 => fun e => match labut_id e with
                                 | erefl => match rabut_id e with
                                            | erefl => fg
                                            end
                                 end
| rbank v1, lbank v2 => fun e => match labut_id (Bridge_edge_sym e) with
                                 | erefl => match rabut_id (Bridge_edge_sym e) with
                                            | erefl => (fg.2, fg.1)
                                            end
                                 end
end e.

Lemma Bridge_label_sym (v1 v2 : Bridge fg) (e1 : Bridge_edge v1 v2) (e2 : Bridge_edge v2 v1) :
  (Bridge_label e1).1 =1 (Bridge_label e2).2.
Proof.
  elim: v1 e1 e2 => v1 e1 e2.
    elim: v2 e1 e2 => v2 e1 e2 p.
      exact: label_sym.
    have v1_eq_vabut : v_abut = v1 by move: e1 => /andP [/eqP e1 _].
    have v2_eq_v'abut : v'_abut = v2 by move: e1 => /andP [_ /eqP e1].
    elim: v1 / v1_eq_vabut e1 e2 p.
    elim: v2 / v2_eq_v'abut => e1 e2 p.
    rewrite /=.
    have idk : labut_id e1 = erefl by exact: eq_axiomK.
    have idk' : rabut_id e1 = erefl by exact: eq_axiomK.
    have idk'' : labut_id (Bridge_edge_sym e2) = erefl by exact: eq_axiomK.
    have idk''' : rabut_id (Bridge_edge_sym e2) = erefl by exact: eq_axiomK.
    by rewrite idk idk' idk'' idk'''.
  elim: v2 e1 e2 => v2 e1 e2 p.
    have v2_eq_vabut : v_abut = v2 by move: e1 => /andP [_ /eqP e1].
    have v1_eq_v'abut : v'_abut = v1 by move: e1 => /andP [/eqP e1 _].
    elim: v1 / v1_eq_v'abut e1 e2 p.
    elim: v2 / v2_eq_vabut => e1 e2 p.
    rewrite /=.
    have idk  : labut_id (Bridge_edge_sym e1) = erefl by exact: eq_axiomK.
    have idk' : rabut_id (Bridge_edge_sym e1) = erefl by exact: eq_axiomK.
    have idk'' : labut_id e2 = erefl by exact: eq_axiomK.
    have idk''' : rabut_id e2 = erefl by exact: eq_axiomK.
    by rewrite idk idk' idk'' idk'''.
  exact: label_sym.
Qed.

HB.instance Definition _ := hasDecEq.Build (Bridge fg) Bridge_eq_axiom.

HB.instance Definition _ := IsLagoisGraph.Build (Bridge fg) Bridge_edge_irefl Bridge_edge_sym Bridge_label_sym.

Definition inl (v : Bridge fg) := {v0 | lbank v0 = v}.

Definition extl (v : Bridge fg) (v_in_l : inl v) : G :=
  let: exist v0 v_eq := v_in_l in
    match v_eq with
    | erefl => v0
    end.

Definition extl_id (v : Bridge fg) (v_inl : inl v) :
  lbank (extl v_inl) = v.
Proof.
  elim: v_inl => v' v2v'.
  by refine (match v2v' with erefl => _ end) => /=.
Defined.


Definition el2e (v1 v2 : G)  (f : v1 @> v2) :
  lbank v1 @> lbank v2 := f.

Definition e2el (v1 v2 : G)  (f : lbank v1 @> lbank v2) :
  v1 @> v2 := f.

Fixpoint pl2p (v1 v2 : G) (f : v1 ~> v2) : lbank v1 ~> lbank v2 :=
  match f with
  | ε => ε
  | path_cons _ _ _ g h => el2e g \* pl2p h
  end.

Lemma pl2p_id (v1 v2 : G) (f : v1 ~> v2) : pl2p f =1 f.
Proof.
  elim: v1 v2 / f => [//| v1 v2 v3 f1 f2 IH p].
  by rewrite /= IH.
Qed.

Fixpoint bwbridge_nun' (v2 : G) (v1 : G') (f : rbank v1 ~> lbank v2) {struct f}:
  exists (f1 : rbank v1 ~> rbank v'_abut) (f2 : lbank v_abut ~> lbank v2), f1 \* o-o^<~ \* f2 = f.
Proof.
  refine (match f with
    | path_empty v1 => _
    | path_cons v1 v12 v2 f1 f2 => _
    end
  ).
    elim: v1 => _ //.
  elim: v1 f1 => [_ _//| v1 f1 ].
  elim: v2 f2 => v2 f2; elim: v12 f1 f2 => v12 f1 f2; first last.
  - by [].
  - by [].
  - move: (bwbridge_nun' _ _ f2) => [f21 [f22 f21f22_eq]].
    exists (f1 \* f21); exists f22.
    by rewrite pathconcatA f21f22_eq.
  - move: (rabut_id_inv f1) => v'_abut_eq_v1.
    move: (labut_id_inv f1) => v_abut_eq_v12.
    elim: v_abut_eq_v12 f1 f2 => f1 f2.
    elim: v'_abut_eq_v1 f1 => f1.
    exists ε; exists f2.
    Check edge_uip.
    by rewrite /= (edge_uip f1 (edge_sym (lbank v_abut) (rbank v'_abut) o-o)).
Qed.


Lemma bwbridge_nun (v1 v3 : G) (v2 : G') (f : lbank v1 @> rbank v2) (g : rbank v2 ~> lbank v3) :
  ~~ uniq (path_cons f g).
Proof.
  rewrite /= negb_and Bool.negb_involutive.
  apply/orP; left.
  move: (bwbridge_nun' g) => [g1 [g2 {g}<-]].
  rewrite /= in_path_homo.
  apply /orP; right.
  rewrite pathcons2concat in_path_homo.
  apply /orP; left.
  rewrite /in_mem /=.
  apply /orP; left.
  by elim: (labut_id f).
Qed.

Fixpoint unf_inl_inl_aux
  (v1 v2 : G)
  (f : lbank v1 ~> lbank v2)
  : uniq f -> exists (g : v1 ~> v2),
    f = pl2p g.
Proof.
  refine (match f with
          | path_empty v1' => _
          | path_cons v1' v2' v3' g h => _
          end).
    by elim: v1' => [v1' _ | _ //]; exists ε.
  elim: v1' g => [v1' g | _ _ //].
  elim: v3' h => [v3' h | _ _ //].
  elim: v2' g h => v2' g h un_gh.
    rewrite pathcons2concat in un_gh.
    move/uniq_fc4p: un_gh => /andP[un_g un_h].
    move: (unf_inl_inl_aux v2' v3' h un_h) => [h' ->].
    move: (e2el g) => g'.
    exists (g' \* h') => /=.
    by rewrite (edge_uip g (el2e g')).
  move: (bwbridge_nun g h) => cont.
  by rewrite un_gh in cont.
Qed.

Theorem un_inl_inl (v1 v2 : G) (f : lbank v1 ~> lbank v2)
  : uniq f -> exists (g : v1 ~> v2), f =1 g.
Proof.
  move=> un_f; move: (unf_inl_inl_aux un_f) => /= [g ->].
  exists g => p.
  exact: pl2p_id.
Qed.

Theorem un_inr_inr (v1 v2 : G') (f : rbank v1 ~> rbank v2)
  : uniq f -> exists (g : v1 ~> v2), f =1 g.
Proof.
Admitted.

Theorem l2r_bpath_decomp (v1 : G) (v2 : G') (f : lbank v1 ~> rbank v2) :
  uniq f -> exists (g : v1 ~> v_abut) (h : v'_abut ~> v2), f =1 h \o o-o \o g.
Proof.
Admitted.

Theorem r2l_bpath_decomp (v1 : G') (v2 : G) (f : rbank v1 ~>lbank v2) :
  uniq f -> exists (g : v1 ~> v'_abut) (h : v_abut ~> v2), f =1 h \o o-o^<~ \o g.
Proof.
Admitted.

Theorem Bridge_secure : loop_secure_graph G -> loop_secure_graph G' -> loop_secure_graph (Bridge fg).
Proof.
  move=> Gs G's; apply /simply_secure_iff_loop_secure.
  elim=> v1; elim=> v2 f g un_f un_g p; last 1 first; rewrite pathcomp2funcomp /comp.
  - move: (un_inr_inr un_f) (un_inr_inr un_g) => [h /ltac:(rewrite /eqfun) ->] [k /ltac:(rewrite /eqfun) ->].
    apply: le_trans.
      exact: (G's v1 (h \* k)).
    by rewrite pathcomp2funcomp /comp.
  - move: (un_inl_inl un_f) (un_inl_inl un_g) => [h /ltac:(rewrite /eqfun) ->] [k /ltac:(rewrite /eqfun) ->].
    apply: le_trans.
      exact: (Gs v1 (h \* k)).
    by rewrite pathcomp2funcomp /comp.
  - move: (l2r_bpath_decomp un_f) => [f_1 [f_2 ->]].
    move: (r2l_bpath_decomp un_g) => [g_1 [g_2 ->]].
    have idk : Bridge_edge_abuts (f_1 p) <= g_1 (f_2 (Bridge_edge_abuts (f_1 p))).
      move: (G's v'_abut (f_2 \* g_1)) => idk'.
      rewrite /loop_secure in idk'.
      move: (pathcomp2funcomp f_2 g_1) => /ltac:(rewrite /eqfun) idk''.
      move/(_ (Bridge_edge_abuts (f_1 p))) in idk'.
      by rewrite idk'' in idk'.
      have idk' : f_1 p <= o-o^<~ (o-o (f_1 p))
                        <= o-o^<~ (g_1 (f_2 (o-o (f_1 p)))).
      apply /andP; split.
        exact: (reverse_path_loop_secure o-o).
      exact: (path_nondecreasing _).
    have idk'' : p <= g_2 (f_1 p)
                   <= g_2 (o-o^<~ (g_1 (f_2 (o-o (f_1 p))))).
      apply /andP; split.
        by move : (Gs _ (f_1 \* g_2)) => /(_ p) /ltac:(rewrite /loop_secure pathcomp2funcomp /=) ikd.
      apply: (path_nondecreasing _).
      move/andP: idk' => [idk'1 idk'2].
      exact: le_trans idk'1 idk'2.
    move/andP: idk'' => [idk'1 idk'2].
    exact: le_trans idk'1 idk'2.
  - move: (r2l_bpath_decomp un_f) => [f_1 [f_2 ->]].
    move: (l2r_bpath_decomp un_g) => [g_1 [g_2 ->]].
    have idk : o-o^<~ (f_1 p) <= g_1 (f_2 (o-o^<~ (f_1 p))).
      move: (Gs v_abut (f_2 \* g_1)) => idk'.
      rewrite /loop_secure in idk'.
      move: (pathcomp2funcomp f_2 g_1) => /ltac:(rewrite /eqfun) idk''.
      move/(_ (o-o^<~ (f_1 p))) in idk'.
      by rewrite idk'' in idk'.
    have idk' : f_1 p <= o-o (o-o^<~ (f_1 p))
                      <= o-o (g_1 (f_2 (o-o^<~ (f_1 p)))).
      apply /andP; split.
        move: (reverse_path_loop_secure o-o^<~) => kk.
        rewrite /loop_secure in kk.
        move/(_ (f_1 p)) in kk.
        by rewrite path_reverse_involution pathcomp2funcomp /comp in kk.
      exact: (path_nondecreasing _).
    have idk'' : p <= g_2 (f_1 p)
                   <= g_2 ((o-o (g_1 (f_2 (o-o^<~ (f_1 p)))))).
      apply /andP; split.
        by move : (G's _ (f_1 \* g_2)) => /(_ p) /ltac:(rewrite /loop_secure pathcomp2funcomp /=) ikd.
      apply: (path_nondecreasing _).
      move/andP: idk' => [idk'1 idk'2].
      exact: le_trans idk'1 idk'2.
    move/andP: idk'' => [idk'1 idk'2].
    exact: le_trans idk'1 idk'2.
Qed.

End Bridge.
