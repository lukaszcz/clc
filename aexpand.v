(* This file contains the formalisation of lemma 18 *)

Require Import general.
Require Import iterms.
Require Import lterms.
Require Import subterms.
Require Import standard.
Require Import erasure.
Require Import red.
Require Import sred.
Require Import ired.
Require Import ared.
Require Import sexpand.

Lemma lem_clc0_expansion_root :
  forall t q q', Sterm t -> Standard t -> Erasure t q ->
                 RootContr_clc0 q' q ->
                 exists t', Red_clc_i_a t' t /\ Erasure t' q'.
Proof.
  Ltac mytac := split; [ apply lem_rcontr_a_implies_red_i_a; ycrush | pose_erasure; ycrush ].
  intros.
  assert (Std t) by auto using lem_standard_implies_std.
  invert_rcontr_clc0.
  yintuition; simp_hyps; subst; simpl in *.

  exists (C1 @l T1 @l t @l (itm x0)); mytac.
  exists (C1 @l F1 @l (itm x) @l t); mytac.
  exists (C2 @l (itm x1) @l t @l t); pose_red_s; mytac.
  exists (I1 @l t); mytac.
  exists (K1 @l t @l (itm x0)); mytac.
  
  yinversion H1; try yelles 1.
  assert (Sterm x2) by iauto 1.
  yinversion H6; try yelles 1.
  assert (Standard y).
  pose lem_subterm_standard; pose_subterm; ycrush.
  assert (Standard y0).
  pose lem_subterm_standard; pose_subterm; ycrush.
  assert (exists t' : lterm, RootContr_S t' (x3 @l y0 @l y) /\ Erasure t' (Si @i x @i x0 @i x1)).
  exists (build_s_redex x3 y0 y).
  pose lem_s_expand; pose lem_s_expand_erasure; ycrush.
  simp_hyps.
  exists x2.
  assert (RootContr_clc_a x2 (x3 @l y0 @l y)).
  racrush.
  mytac.
Qed.

(* lemma 18 *)
Lemma lem_clc0_expansion :
  forall t q q', Standard t -> Erasure t q -> Contr_clc0 q' q ->
                 exists t', Red_clc_i_a t' t /\ Erasure t' q'.
Proof.
  Ltac mytac1 :=
    match goal with
      [ H0 : Erasure _ _, H1 : Contr_clc0 _ _ |- _ ] =>
      yinversion H0; yinversion H1; pose lem_clc0_expansion_root; yelles 1
    end.
  intro t; lterm_induction t; intros; try mytac1.
  
  yinversion H0.
  exists (itm q').
  pose lem_contr_clc0_implies_contr_i_a; unfold Red_clc_i_a; pose_rt; pose_erasure; ycrush.

  assert (HH: Std (t1 @l t2)) by auto using lem_standard_implies_std.
  assert (Sterm (t1 @l t2)) by ycrush.
  yinversion H0.
  yinversion H1; fold Contr_clc0 in *.
  pose lem_clc0_expansion_root; pose_erasure; ycrush.
  assert (Standard t1).
  pose lem_subterm_standard; pose_subterm; ycrush.
  yforwarding.
  exists (x0 @l t2).
  pose_red_i_a; pose_erasure; ycrush.
  assert (Standard t2).
  pose lem_subterm_standard; pose_subterm; ycrush.
  yforwarding.
  exists (t1 @l x).
  pose_red_i_a; pose_erasure; ycrush.

  yinversion H0.
  assert (Standard t1).
  pose lem_subterm_standard; pose_subterm; ycrush.
  assert (Standard t2).
  pose lem_subterm_standard; pose_subterm; ycrush.
  assert (forall t, In t l1 -> Standard t).
  pose lem_subterm_standard; pose_subterm; ycrush.
  yforwarding.
  assert (forall t, In t l1 -> exists t', Red_clc_i_a t' t /\ Erasure t' q') by ycrush.
  assert (exists l', Red_clc_i_a (ltup t1 t2 l') (ltup t1 t2 l1) /\
                     forall t, In t l' -> Erasure t q').
  apply lem_red_ltup_in_2; pose_red_i_a; ycrush.
  simp_hyps.
  exists (ltup x0 x x1).
  pose_red_i_a; pose erasure_ltup; ycrush.

  ycrush.
Qed.
