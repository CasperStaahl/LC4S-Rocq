From HB Require Import structures.

(* SSReflect *)
From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import order eqtype.
From Lagois Require Import abssyn sem lagois.
Import Order.LTheory.

Open Scope order_scope.

Section typrls.

Variable Val : Type.
Variable Term Term' : SubSemantic.type Val.
Variable Q P : finTBLatticeType (Order.Disp tt tt).
Variable f : { omorphism P -> Q}.
Variable g : { omorphism Q -> P}.
Variable HL : P<~f~g~>Q.

Inductive CommSType {A : finTBLatticeType (Order.Disp tt tt)} {Term0 : SubSemantic.type Val} : (Store A) -> command Term0 -> A -> Prop :=
  | Tt (λ : Store A) t l:
      (forall z, assigned t z -> l <= λ z) ->
      (forall z, read t z -> λ z <= l) ->
      CommSType λ (tsyn t) l
  | Trd (λ : Store A) y z :
      λ (imp y) <= λ (loc z) ->
      CommSType λ (rd z y) (λ (loc z))
  | Twr (λ : Store A) x z :
      λ (loc z) <= λ (exp x) ->
      CommSType λ (wr x z) (λ (exp x)).

Inductive PhraseSType : (Store P * Store Q) -> phrase Term Term' -> (P * Q) -> Prop :=
  | LCT (λ : Store P) (λ' : Store Q) c l m':
      CommSType λ c l ->
      PhraseSType (λ, λ') (csyn c) (l, m')
  | RCT (λ : Store P) (λ' : Store Q) c' l m':
      CommSType λ' c' m' ->
      PhraseSType (λ, λ') (csyn' c') (l, m')
  | TTrl (λ : Store P) (λ' : Store Q) x' y :
      g (λ' (exp x')) <= λ (imp y) ->
      PhraseSType (λ, λ') (T_RL y x') (λ (imp y), λ' (exp x'))
  | TTlr (λ : Store P) (λ' : Store Q) x y' :
      f (λ (exp x)) <= λ' (imp y') ->
      PhraseSType (λ, λ') (T_LR y' x) (λ (exp x), λ' (imp y')).

Inductive SeqSType : (Store P * Store Q) -> seq Term Term' -> (P * Q) -> Prop :=
  | Com0 λ t :
      SeqSType λ ε t
  | ComP λ t_1 t p s:
      PhraseSType λ p t_1 ->
      SeqSType λ s t ->
      SeqSType λ (seqcons s p) (t_1.1 `&` t.1, t_1.2 `&` t.2).

Lemma CommsSType_sound {A : finTBLatticeType (Order.Disp tt tt)} {Term0 : SubSemantic.type Val} (λ : Store A) τ τ_0 (μ ν μ' ν' : Store Val) (c : command Term0):
  CommSType λ c τ_0 ->
  μ ==[ c ]==> μ' ->
  ν ==[ c ]==> ν' ->
  (forall w : Var, λ w <= τ -> μ w = ν w) ->
  (forall w : Var, λ w <= τ -> μ' w = ν' w).
Proof.
  move=> λ_gives_c_type_τ' μ_c_μ' ν_c_ν' λw_le_τ_impl_μw_eq_νw w λw_le_τ.
  have λw''_le_λw'_impl_μup_eq_νup : forall w' w'', λ w'' <= λ w' -> [eta μ with w' |-> μ w''] w = [eta ν with w' |-> ν w''] w.
    move=> w' w'' w'_le_w'' /=; case w_eq_expx: (w == w'); first last.
      exact: λw_le_τ_impl_μw_eq_νw λw_le_τ.
    apply: λw_le_τ_impl_μw_eq_νw.
    apply: (le_trans w'_le_w'').
    move/eqP: w_eq_expx => <-.
    exact: λw_le_τ.
  inversion μ_c_μ'; subst; inversion ν_c_ν'; subst; inversion λ_gives_c_type_τ'; subst; first last.
  - exact: λw''_le_λw'_impl_μup_eq_νup.
  - exact: λw''_le_λw'_impl_μup_eq_νup.
  - have w_notassin_t_impl_μ'w_eq_ν'w : ~~(assigned t w) -> μ' w = ν' w.
      move=> w_notassin_t.
      have <-: μ w = μ' w by apply: frame H w_notassin_t.
      have <-: ν w = ν' w by apply: frame H2 w_notassin_t.
      exact: λw_le_τ_impl_μw_eq_νw.
    case: w λw_le_τ w_notassin_t_impl_μ'w_eq_ν'w {λw''_le_λw'_impl_μup_eq_νup} => n λn_le_τ w_notassin_t_impl_μ'w_eq_ν'w; first last.
    + exact: w_notassin_t_impl_μ'w_eq_ν'w (ys_not_assigned n t).
    + exact: w_notassin_t_impl_μ'w_eq_ν'w (xs_not_assigned n t).
    + case n_assin_t: (~~ (assigned t (loc n))).
        exact: w_notassin_t_impl_μ'w_eq_ν'w n_assin_t.
      move/negbFE in n_assin_t.
      apply/(simple_security _ _ _ _ _ _ n_assin_t H H2) => w' w'_det_z'.
      apply: λw_le_τ_impl_μw_eq_νw.
      have readtw : (read t w') by apply/readP; exists (loc n).
      move/(_ w' readtw) in H4.
      move/H1 in n_assin_t.
      move: (le_trans n_assin_t λn_le_τ) => τ0_le_τ.
      exact: le_trans H4 τ0_le_τ.
Qed.

Lemma T_sound (A B : finTBLatticeType (Order.Disp tt tt)) (h : {omorphism A -> B}) (i : {omorphism B -> A}) (λ : Store A) (λ' : Store B) (m' : B) (y x' : ident) (w : Var) (μ ν μ' ν' : Store Val) :
  A <~ h ~ i ~> B ->
  m' = h (i m') ->
  i (λ' (exp x')) <= λ (imp y) ->
  λ w <= i m' ->
  (forall w' : Var, λ' w' <= m' -> μ' w' =  ν' w') ->
  (forall w : Var, λ w <= i m' -> μ w = ν w) ->
  (if w == imp y then μ' (exp x') else μ w) = (if w == imp y then ν' (exp x') else ν w).
Proof.
  move=> LC m'_eq_him' iλ'x'_le_λy λw_le_im' μ'w'_eq_ν'w' μw_eq_νw.
  case w_eq_y: (w == imp y); last first.
    exact: μw_eq_νw λw_le_im'.
  apply: μ'w'_eq_ν'w'.
  have λ'x'_le_hiλ'x' : λ' (exp x') <= h (i (λ' (exp x')))
    by move: LC => [LC1 _ _ _]; exact: LC1.
  have iλ'x'_le_im' : i (λ' (exp x')) <= i m'
    by move/eqP in w_eq_y; rewrite -w_eq_y in iλ'x'_le_λy; apply: le_trans iλ'x'_le_λy λw_le_im'.
  have hiλ'x'_le_m' : h (i (λ' (exp x'))) <= m'.
    by move/(omorph_le h) in iλ'x'_le_im'; rewrite -m'_eq_him' in  iλ'x'_le_im'.
  exact: le_trans λ'x'_le_hiλ'x' hiλ'x'_le_m'.
Qed.

Theorem SeqSType_sound l m' t_0 s λ μ μ_f ν ν_f :
  l = g m' ->
  m' = f l ->
  μ ==[ s ]==> μ_f ->
  ν ==[ s ]==> ν_f ->
  SeqSType λ s t_0 ->
  (forall w : Var, λ.1 w <= l -> μ.1 w = ν.1 w) ->
  (forall w' : Var, λ.2 w' <= m' -> μ.2 w' = ν.2 w') ->
  (forall w : Var, λ.1 w <= l -> μ_f.1 w = ν_f.1 w)
      /\ (forall w' : Var, λ.2 w' <= m' -> μ_f.2 w' = ν_f.2 w').
Proof.
  move=> l_eq_gm' m'_eq_fl μ_s_μf; elim: μ_s_μf ν ν_f t_0 λ.
    move=> {}μ ν ν_f t_0 λ ν_ε_νf; case ε_eq: _ _ / ν_ε_νf => //.
  move=> s_1 p {}μ μ_1 {}μ_f μ_s1_μ1 IH μ1_p_μf ν ν_f t_0 λ ν_s1p_νf λ_gives_s1p_type_t0.
  case E: _ _ / ν_s1p_νf => [|s_1' p' {}ν ν_1 {}ν_f ν_s1_ν1 ν1_p_νf]//.
  move: E => [s1_eq_s1' p_eq_p']; rewrite -{s_1'}s1_eq_s1' in ν_s1_ν1; rewrite -{p'}p_eq_p' in ν1_p_νf.
  case E: _ _ / λ_gives_s1p_type_t0 => [|{}λ t_p t_s p' s_1' λ_gives_p_tp λ_gives_s1_ts]//.
  move: E => [s1_eq_s1' p_eq_p']; rewrite -{s_1'}s1_eq_s1' in λ_gives_s1_ts; rewrite -{p'}p_eq_p' in λ_gives_p_tp.
  move=> μ1w_eq_ν1w μ2w_eq_ν2w.
  move/(_ ν ν_1 t_s λ ν_s1_ν1 λ_gives_s1_ts μ1w_eq_ν1w μ2w_eq_ν2w): IH => {μ1w_eq_ν1w μ2w_eq_ν2w}[μ11w_eq_ν11w μ12w_eq_ν12w].
  case: p μ1_p_μf ν1_p_νf λ_gives_p_tp => [ c | c' | y x' | y' x ] μ1_p_μf ν1_p_νf λ_gives_p_tp.
  - inversion μ1_p_μf; inversion ν1_p_νf; inversion λ_gives_p_tp; subst.
    split => //; exact: CommsSType_sound H9 H1 H5 μ11w_eq_ν11w.
  - inversion μ1_p_μf; inversion ν1_p_νf; inversion λ_gives_p_tp; subst.
    split => //; exact: CommsSType_sound H9 H1 H5 μ12w_eq_ν12w.
  - inversion μ1_p_μf; inversion ν1_p_νf; inversion λ_gives_p_tp; subst => /=.
    split=> [w λ0w_le_l | // ]; exact: T_sound HL m'_eq_fl H11 λ0w_le_l μ12w_eq_ν12w μ11w_eq_ν11w.
  - inversion μ1_p_μf; inversion ν1_p_νf; inversion λ_gives_p_tp. move: l_eq_gm' m'_eq_fl. subst => l_eq_gm' m'_eq_fl /=.
    split=> [ // | w' λ'w_le_m'].
    rewrite m'_eq_fl in l_eq_gm' λ'w_le_m' μ12w_eq_ν12w.
    exact: (T_sound (melton_3_2 HL) l_eq_gm' H11 λ'w_le_m' μ11w_eq_ν11w μ12w_eq_ν12w).
Qed.

End typrls.
