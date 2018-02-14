(* This file contains the definition of standard terms and the
   formalisation of their basic properties (including those stated in
   lemma 9) *)

Require Import general.
Require Import list_facts.
Require Import iterms.
Require Import lterms.
Require Import subterms.
Require Import erasure.
Require Import sred.

Definition Std t :=
  match t with
  | itm _ => True
  | ltup x y l =>
    is_ltup x = false /\ is_ltup y = false /\ forall x, In x l -> is_ltup x = false
  | _ =>
    Sterm t /\ (forall t', Red_clc_s t t' -> Sterm t') /\
    match t with
    | C1 @l z @l _ @l _ => sNF z -> z = T1 \/ z = F1
    | C2 @l _ @l x @l y => ErasedEqv x y
    | S1 l @l x @l y @l z => is_ltup y = true /\ is_ltup z = true /\
                             (forall n, In n l -> n > 0) /\
                             lst_sum l < length (tuple_of_lterm z) /\
                             (length (tuple_of_lterm y) = length l)
    | S2 n @l x @l y @l z => is_ltup y = false /\ is_ltup z = true /\
                             n > 0 /\ n < length (tuple_of_lterm z)
    | _ => True
    end
  end.

Definition Standard t := forall x, Subterm x t -> Std x.

Definition StronglyStandard t := forall x, Red_clc_s t x -> Standard x.

Definition Leadsto t t' := StronglyStandard t /\ (forall x, Red_clc_s t x -> sNF x -> t' = x).

Hint Unfold sNF Std Standard StronglyStandard Leadsto : unfold_hints.

Lemma lem_subterm_standard : forall x, Standard x -> forall y, Subterm y x -> Standard y.
Proof.
  intro x; lterm_induction x; unfold Standard in *; intros; destruct y;
    try solve [ pose_subterm; iauto 1 ].
Qed.

Lemma lem_reduce_subterm_strongly_standard :
  forall x, StronglyStandard x -> forall y, Red_clc_s x y ->
                                            forall z, Subterm z y -> StronglyStandard z.
Proof.
  autounfold with unfold_hints.
  pose lem_subterm_standard.
  intros.
  assert (exists y', Red_clc_s y y' /\ Subterm x0 y').
  pose_red_s; ycrush.
  simp_hyps.
  assert (exists y', Red_clc_s x y' /\ Subterm x0 y').
  pose_red_s; ycrush.
  simp_hyps; eauto.
Qed.

Lemma lem_subterm_strongly_standard :
  forall x, StronglyStandard x -> forall y, Subterm y x -> StronglyStandard y.
Proof.
  pose lem_reduce_subterm_strongly_standard; unfold Red_clc_s in *; pose_rt; ycrush.
Qed.

Lemma lem_standard_not_reduces_to_tuple :
  forall x, Standard x -> is_ltup x = false ->
            forall y, Red_clc_s x y -> is_ltup y = false.
Proof.
  unfold Standard.
  intros.
  yinversion H0.
  assert (Std x) by (pose_subterm; eauto).
  Ltac mytac :=
    match goal with
    | [ H : Red_clc_s ?x ?y |- ?G ] =>
      assert (y = x) by (pose lem_red_s_basic; unfold lterm_basic in *; yelles 1);
      sintuition
    end.
  ydestruct x; simpl in *; simp_hyps; try mytac.
  assert (Sterm y) by auto.
  sterm_tac 1.
Qed.

Lemma lem_strongly_standard_c1_red_s :
  forall x, StronglyStandard x -> forall z y1 y2, Subterm (C1 @l z @l y1 @l y2) x ->
                                                  Red_clc_s z T1 \/ Red_clc_s z F1.
Proof.
  intros.
  generalize (lem_red_s_wn z); yintro.
  assert (StronglyStandard (C1 @l z @l y1 @l y2)).
  pose lem_reduce_subterm_strongly_standard; pose lem_red_s_refl; ycrush.
  assert (Red_clc_s (C1 @l z @l y1 @l y2) (C1 @l x0 @l y1 @l y2)).
  eauto using lem_red_s_refl, lem_red_s_cong_l, lem_red_s_cong_r.
  assert (Std (C1 @l x0 @l y1 @l y2)).
  unfold StronglyStandard, Standard in *; pose_red_s; pose_subterm; ycrush.
  ycrush.
Qed.

Lemma lem_standard_implies_std : forall x, Standard x -> Std x.
Proof.
  unfold Standard in *; pose_subterm; ycrush.
Qed.

Lemma lem_strongly_standard_implies_std : forall x, StronglyStandard x -> Std x.
Proof.
  unfold StronglyStandard in *; pose_subterm; ycrush.
Qed.

Lemma lem_strongly_standard_implies_standard : forall x, StronglyStandard x -> Standard x.
Proof.
  unfold StronglyStandard in *; pose_subterm; ycrush.
Qed.

Lemma lem_s_term_erasure_k :
  forall t q0 q1, Sterm t -> Erasure t (K @i q0 @i q1) ->
                  exists t0 t1, t = K1 @l t0 @l t1 /\ Erasure t0 q0 /\ Erasure t1 q1.
Proof.
  intros.
  yinversion H0; try iauto 1.
  yinversion H4; try solve [ yinversion H; iauto 1 ].
  yinversion H3; try solve [ yinversion H; iauto 3 ].
Qed.

Lemma lem_s_term_erasure_c :
  forall t q0 q1 q2, Sterm t -> Erasure t (C @i q0 @i q1 @i q2) ->
                     exists t0 t1 t2,
                       (t = C1 @l t0 @l t1 @l t2 \/ t = C2 @l t0 @l t1 @l t2) /\
                       Erasure t0 q0 /\ Erasure t1 q1 /\ Erasure t2 q2.
Proof.
  intros.
  yinversion H0; try iauto 1.
  yinversion H4; try solve [ yinversion H; iauto 1 ].
  yinversion H3; try solve [ yinversion H; iauto 2 ].
  yinversion H4; yinversion H; try iauto 3; ycrush.
Qed.

Lemma lem_standard_ltup : forall x y z l, Standard (ltup x y (z :: l)) -> Standard (ltup x y l).
Proof.
  unfold Standard; intros.
  yinversion H0.
  assert (Std (ltup x y (z :: l))).
  pose_subterm; ycrush.
  unfold Std in *; ycrush.
  pose_subterm; ycrush.
  pose_subterm; ycrush.
  assert (In z0 (z :: l)).
  auto with datatypes.
  pose_subterm; ycrush.
Qed.

Lemma lem_strongly_standard_ltup :
  forall x y z l, StronglyStandard (ltup x y (z :: l)) -> StronglyStandard (ltup x y l).
Proof.
  unfold StronglyStandard; intros.
  generalize (lem_red_s_ltup_inv x y l x0 H0); yintro; subst.
  assert (Red_clc_s (ltup x y (z :: l)) (ltup x1 x2 (z :: x3))).
  pose lem_red_s_ltup_closure; pose_lc; pose lem_red_s_refl; ycrush.
  pose lem_standard_ltup; ycrush.
Qed.

Lemma lem_std_ltup : forall x y z l, Std (ltup x y (z :: l)) -> Std (ltup x y l).
Proof.
  pose lem_standard_ltup; unfold Standard in *; pose_subterm; ycrush.
Qed.

Lemma lem_standard_sterm : forall x y, Standard x -> Sterm x -> Red_clc_s x y -> Sterm y.
Proof.
  unfold Standard; intros.
  assert (Std x) by (pose_subterm; ycrush).
  ydestruct x; try yelles 1.
Qed.

Lemma lem_standard_no_nested_tuple :
  forall x, Standard x -> forall y, In y (tuple_of_lterm x) -> is_ltup y = false.
Proof.
  intros.
  assert (is_ltup x = true \/ is_ltup x = false) by ycrush.
  yintuition; simpl in *.
  ydestruct x; yisolve; simpl in *.
  pose lem_standard_implies_std; pose_subterm; ycrush.
  assert (HH: tuple_of_lterm x = x :: nil) by ycrush.
  rewrite HH in *; clear HH.
  simpl in *; ycrush.
Qed.

Lemma lem_standard_basic_app_1 :
  forall a x, Sterm a -> lterm_basic a -> a <> I1 -> Standard x -> Standard (a @l x).
Proof.
  intros.
  unfold Standard; intros.
  yinversion H3.
  unfold Std.
  yintuition.
  pose_sterm; ycrush.
  pose lem_red_s_basic_app_1; pose_sterm; ycrush.
  ydestruct a; simpl in *; yisolve; yinversion H0; ycrush.
  yinversion H6; try yelles 1.
  unfold Std.
  ydestruct a; yisolve.
  pose lem_red_s_basic; ycrush.
  pose lem_red_s_basic; ycrush.
  pose lem_red_s_basic; ycrush.
  pose lem_red_s_basic; ycrush.
  pose lem_red_s_basic; ycrush.
  pose lem_red_s_basic; ycrush.
  pose lem_red_s_basic; ycrush.
  yinversion H0; ycrush.
  yinversion H0; ycrush.
  yinversion H0; ycrush.
  unfold Standard in *; ycrush.
Qed.

Lemma lem_standard_basic_app_2 :
  forall a x y, Sterm a -> lterm_basic a -> a <> I1 -> a <> K1 -> Standard x -> Standard y ->
                Standard (a @l x @l y).
Proof.
  intros.
  unfold Standard; intros.
  yinversion H5.
  unfold Std.
  yintuition.
  pose_sterm; ycrush.
  pose lem_red_s_basic_app_2; pose_sterm; ycrush.
  ydestruct a; simpl in *; yisolve; yinversion H0; ycrush.
  assert (Standard (a @l x)).
  pose lem_standard_basic_app_1; ycrush.
  unfold Standard in *; ycrush.
  unfold Standard in *; ycrush.
Qed.

Lemma lem_iterm_standard : forall x y, is_iterm x = true -> Subterm y x -> Standard y.
Proof.
  unfold Standard; pose lem_subterm_trans; ycrush.
Qed.

Lemma lem_basic_standard : forall x, lterm_basic x -> Standard x.
Proof.
  unfold Standard; intros.
  ydestruct x; yisolve.
  yinversion H0; pose lem_red_s_basic; ycrush.
  yinversion H0; pose lem_red_s_basic; ycrush.
  yinversion H0; pose lem_red_s_basic; ycrush.
  yinversion H0; pose lem_red_s_basic; ycrush.
  yinversion H0; pose lem_red_s_basic; ycrush.
  yinversion H0; pose lem_red_s_basic; ycrush.
  yinversion H0; pose lem_red_s_basic; ycrush.
  yinversion H0; pose lem_red_s_basic; ycrush.
  yinversion H0; pose lem_red_s_basic; ycrush.
  yinversion H; ycrush.
  yinversion H; ycrush.
Qed.

Lemma lem_standard_lterm_of_tuple :
  forall l, Standard (lterm_of_tuple l) -> forall x, In x l -> Standard x.
Proof.
  induction l.
  ycrush.
  ydestruct l; simpl in *.
  ycrush.
  ydestruct l0; simpl in *.
  unfold Standard in *; pose_subterm; ycrush.
  intros.
  assert (Standard (ltup l l0 l1)).
  clear -H.
  assert (Standard l).
  unfold Standard in *; pose_subterm; ycrush.
  assert (forall x, In x (l0 :: l1) -> Standard x).
  unfold Standard in *; pose_subterm; ycrush.
  simpl in *.
  assert (Std (ltup a l (l0 :: l1))).
  unfold Standard in *; pose_subterm; ycrush.
  simpl in *; simp_hyps.
  assert (Std (ltup l l0 l1)) by ycrush.
  unfold Standard; intros.
  yinversion H8.
  trivial.
  ycrush.
  unfold Standard in *; pose_subterm; ycrush.
  unfold Standard in *; pose_subterm; ycrush.
  destruct H0.
  unfold Standard in *; pose_subterm; ycrush.
  auto.
Qed.
