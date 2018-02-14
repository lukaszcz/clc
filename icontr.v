(* This file contains the formalisation of lemma 10 *)

Require Import general.
Require Import iterms.
Require Import lterms.
Require Import erase_facts.
Require Import subterms.
Require Import standard.
Require Import erasure.
Require Import red.
Require Import sred.
Require Import ired.

Lemma lem_clc0_contraction_root :
  forall t q q', Sterm t -> StronglyStandard t -> Erasure t q ->
                 RootContr_clc0 q q' ->
                 exists t', Red_clc_i_s t t' /\ Erasure t' q'.
Proof.
  Ltac assert_snf :=
      match goal with
      | [ H : sNF ?x -> _ |- _ ] =>
        assert (sNF x) by (generalize lem_basic_is_snf; unfold lterm_basic; ycrush)
      end.
  Ltac myinvert t n :=
    ydestruct t; try iauto 1;
    match goal with
    | [ H : Erasure _ _ |- _ ] =>
      yinversion H; invert_sterm_erasure n; yintuition
    end.
  intros.
  assert (Std t) by auto using lem_strongly_standard_implies_std.
  invert_rcontr_clc0.
  yintuition; simp_hyps; subst; simpl in *.
  
  myinvert t 3.
  ydestruct y0; try iauto 1.
  assert_snf; ycrush.
  pose lem_rcontr_s_implies_red_i_s; ycrush.
  clear -H0.
  pose (lem_strongly_standard_c1_red_s (C1 @l ltup y0_1 y0_2 l @l y @l t2) H0
                                       (ltup y0_1 y0_2 l) y t2).
  pose lem_red_s_preserves_is_ltup.
  assert (Red_clc_s (ltup y0_1 y0_2 l) T1 \/ Red_clc_s (ltup y0_1 y0_2 l) F1).
  pose_subterm; ycrush.
  exfalso; ycrush.
  assert (RootContr_clc_s (C2 @l y0 @l y @l t2) y) by ycrush.
  pose_red_s; pose lem_red_s_implies_red_i_s; ycrush.
  
  myinvert t 3.
  ydestruct y0; try iauto 1.
  assert_snf; ycrush.
  pose lem_rcontr_s_implies_red_i_s; ycrush.
  clear -H0.
  pose (lem_strongly_standard_c1_red_s (C1 @l ltup y0_1 y0_2 l @l y @l t2) H0
                                       (ltup y0_1 y0_2 l) y t2).
  pose lem_red_s_preserves_is_ltup.
  assert (Red_clc_s (ltup y0_1 y0_2 l) T1 \/ Red_clc_s (ltup y0_1 y0_2 l) F1).
  pose_subterm; ycrush.
  exfalso; ycrush.
  assert (RootContr_clc_s (C2 @l y0 @l y @l t2) t2) by ycrush.
  pose_red_s; pose lem_red_s_implies_red_i_s; ycrush.

  myinvert t 3.
  assert (Red_clc_s y0 T1 \/ Red_clc_s y0 F1).
  pose (lem_strongly_standard_c1_red_s (C1 @l y0 @l y @l t2) H0 y0 y t2).
  pose_subterm; ycrush.
  yintuition.
  assert (Red_clc_s (C1 @l y0 @l y @l t2) (C1 @l T1 @l y @l t2)).
  pose_red_s; ycrush.
  assert (RootContr_clc_s (C1 @l T1 @l y @l t2) y) by ycrush.
  assert (Red_clc_s (C1 @l y0 @l y @l t2) y).
  pose_red_s; ycrush.
  pose lem_red_s_implies_red_i_s; pose_red_i_s; ycrush.
  assert (Red_clc_s (C1 @l y0 @l y @l t2) (C1 @l F1 @l y @l t2)).
  pose_red_s; ycrush.
  assert (RootContr_clc_s (C1 @l F1 @l y @l t2) t2) by ycrush.
  assert (Red_clc_s (C1 @l y0 @l y @l t2) t2).
  pose_red_s; ycrush.
  pose lem_red_s_implies_red_i_s; pose_red_i_s; ycrush.
  assert (RootContr_clc_s (C2 @l y0 @l y @l t2) y) by ycrush.
  pose_red_s; pose lem_red_s_implies_red_i_s; ycrush.

  myinvert t 2.
  assert (RootContr_clc_s (I1 @l t2) t2) by ycrush.
  pose_red_s; pose lem_red_s_implies_red_i_s; ycrush.

  myinvert t 2.
  assert (RootContr_clc_s (K1 @l y @l t2) y) by ycrush.
  pose_red_s; pose lem_red_s_implies_red_i_s; ycrush.

  myinvert t 3.
  assert (All_pairs (tuple_of_lterm y) ErasedEqv).
  pose lem_erasure_equal; ycrush.
  assert (All_pairs (tuple_of_lterm t2) ErasedEqv).
  pose lem_erasure_equal; ycrush.
  assert (forall u, In u (tuple_of_lterm t2) -> is_ltup u = false).
  assert (Standard t2).
  unfold StronglyStandard in *; pose lem_subterm_standard; pose_subterm; pose_red_s; ycrush.
  pose lem_standard_no_nested_tuple; ycrush.
  assert (RootContr_clc_s (S1 l @l y0 @l y @l t2)
                          (build_s_result l y0 (tuple_of_lterm y) (tuple_of_lterm t2))) by ycrush.
  assert (Erasure (build_s_result l y0 (tuple_of_lterm y) (tuple_of_lterm t2))
                  (x @i x1 @i (x0 @i x1))).
  assert (is_nonempty l).
  ydestruct l; yisolve; ydestruct y; yisolve; simpl in *; omega.
  assert (is_nonempty (tuple_of_lterm y)) by ycrush.
  pose lem_s_result_erasure; pose lem_erasure_tuple; ycrush.
  pose_red_s; pose lem_red_s_implies_red_i_s; ycrush.

  assert (All_pairs (tuple_of_lterm t2) ErasedEqv).
  pose lem_erasure_equal; ycrush.
  assert (forall u, In u (tuple_of_lterm t2) -> is_ltup u = false).
  assert (Standard t2).
  unfold StronglyStandard in *; pose lem_subterm_standard; pose_subterm; pose_red_s; ycrush.
  pose lem_standard_no_nested_tuple; ycrush.
  assert (RootContr_clc_s (S2 n @l y0 @l y @l t2)
                          (y0 @l (lterm_of_tuple (firstn n (tuple_of_lterm t2))) @l
                             (glue_iterms y (lterm_of_tuple (skipn n (tuple_of_lterm t2)))))) by ycrush.
  assert (Erasure (y0 @l lterm_of_tuple (firstn n (tuple_of_lterm t2)) @l
                      glue_iterms y (lterm_of_tuple (skipn n (tuple_of_lterm t2))))
                  (x @i x1 @i (x0 @i x1))).
  pose lem_s2_result_erasure; pose lem_erasure_tuple; ycrush.
  pose_red_s; pose lem_red_s_implies_red_i_s; ycrush.
Qed.

(* lemma 10 *)
Lemma lem_clc0_contraction :
  forall t q q', StronglyStandard t -> Erasure t q -> Contr_clc0 q q' ->
                 exists t', Red_clc_i_s t t' /\ Erasure t' q'.
Proof.
  Ltac mytac H :=
    yinversion H;
    match goal with [ H1 : StronglyStandard ?x |- _ ] => exists x end;
    unfold Red_clc_i_s; pose_rt; yelles 2.
  intro t; lterm_induction t; intros; try mytac H0.
  yinversion H0.
  exists (itm q').
  pose lem_contr_clc0_implies_contr_i_s; unfold Red_clc_i_s; pose_rt; pose_erasure; ycrush.
  assert (HH: Std (t1 @l t2)) by auto using lem_strongly_standard_implies_std.
  assert (Sterm (t1 @l t2)) by ycrush.
  yinversion H0.
  yinversion H1; fold Contr_clc0 in *.
  pose lem_clc0_contraction_root; pose_erasure; ycrush.
  assert (StronglyStandard t1).
  pose lem_subterm_strongly_standard; pose_subterm; ycrush.
  yforwarding.
  exists (x @l t2).
  pose_red_i_s; pose_erasure; ycrush.
  assert (StronglyStandard t2).
  pose lem_subterm_strongly_standard; pose_subterm; ycrush.
  yforwarding.
  exists (t1 @l x).
  pose_red_i_s; pose_erasure; ycrush.

  yinversion H0.
  assert (StronglyStandard t1).
  pose lem_subterm_strongly_standard; pose_subterm; ycrush.
  assert (StronglyStandard t2).
  pose lem_subterm_strongly_standard; pose_subterm; ycrush.
  assert (forall t, In t l1 -> StronglyStandard t).
  pose lem_subterm_strongly_standard; pose_subterm; ycrush.
  yforwarding.
  assert (forall t, In t l1 -> exists t', Red_clc_i_s t t' /\ Erasure t' q') by ycrush.
  assert (exists l', Red_clc_i_s (ltup t1 t2 l1) (ltup t1 t2 l') /\
                     forall t, In t l' -> Erasure t q').
  apply lem_red_ltup_in; pose_red_i_s; ycrush.
  simp_hyps.
  exists (ltup x0 x x1).
  pose_red_i_s; pose erasure_ltup; ycrush.

  ycrush.
  ycrush.
Qed.
