(* This file contains the formalisation of lemma 19 and corollary 20 *)

Require Import general.
Require Import lterms.
Require Import erase_facts.
Require Import svars.
Require Import subterms.
Require Import standard.
Require Import sred.
Require Import ared.
Require Import sexpand_std.

Lemma lem_a_root_commute :
  forall x y z, RootContr_clc_a x y -> RootContr_clc_s x z -> Standard y ->
                exists u, (RootContr_clc_a z u \/ z = u) /\ Red_clc_s y u.
Proof.
  intros.
  invert_rcontr_clc_a.
  yintuition; yintuition; try yelles 1.
  invert_rcontr_clc_s.
  yintuition; yintuition; yelles 1.
Qed.

Lemma lem_standard_implies_glue_iterms_l :
  forall y, Standard y -> forall z, In z (tuple_of_lterm y) -> R_glue_iterms_l Contr_clc_s z.
Proof.
  unfold R_glue_iterms_l.
  intros.
  assert (HStd_z: Std z).
  unfold Standard in *; pose_subterm; ydestruct y; simpl in *; ycrush.
  assert (HH: is_iterm z = true \/ Sterm z).
  assert (is_ltup z = false).
  assert (Std y).
  apply lem_standard_implies_std; ycrush.
  ydestruct y; simpl in *; yisolve.
  ydestruct z; simpl in *; yisolve.
  destruct HH.
  destruct z, x', y0; pose lem_contr_s_basic; pose_contr_s; ycrush.
  assert (Sterm x').
  unfold Std in *; pose_red_s; ycrush.
  destruct z, x'; pose_contr_s; ycrush.
Qed.

Lemma lem_standard_implies_glue_iterms_r :
  forall y, Standard y -> forall z, In z (tuple_of_lterm y) -> R_glue_iterms_r Contr_clc_s z.
Proof.
  unfold R_glue_iterms_r.
  intros.
  assert (HStd_z: Std z).
  unfold Standard in *; pose_subterm; ydestruct y; simpl in *; ycrush.
  assert (HH: is_iterm z = true \/ Sterm z).
  assert (is_ltup z = false).
  assert (Std y).
  apply lem_standard_implies_std; ycrush.
  ydestruct y; simpl in *; yisolve.
  ydestruct z; simpl in *; yisolve.
  destruct HH.
  destruct z, y', x; pose lem_contr_s_basic; pose_contr_s; ycrush.
  assert (Sterm y').
  unfold Std in *; pose_red_s; ycrush.
  destruct z, y', x; pose_contr_s; ycrush.
Qed.

Lemma lem_standard_red_s_preserves_not_ltup :
  forall x y, Standard x -> Red_clc_s x y -> is_ltup x = false -> is_ltup y = false.
Proof.
  intros.
  assert (Std x).
  unfold Standard in *; pose_subterm; ycrush.
  assert (HH: is_iterm x = true \/ Sterm x).
  ydestruct x; unfold Std in *; yisolve.
  destruct HH.
  assert (is_iterm y = true).
  assert (lterm_basic x).
  ydestruct x; ycrush.
  assert (x = y).
  pose lem_red_s_basic; ycrush.
  ycrush.
  ydestruct y; ycrush.
  assert (Sterm y).
  unfold Std in *; ycrush.
  ydestruct y; ycrush.
Qed.

Lemma lem_standard_contr_s_preserves_no_nested_tuple :
  forall y y', Standard y -> Contr_clc_s y y' ->
               (forall x, In x (tuple_of_lterm y) -> is_ltup x = false) ->
               forall x, In x (tuple_of_lterm y') -> is_ltup x = false.
Proof.
  intros.
  assert (is_ltup y' = true \/ is_ltup y' = false) by ycrush.
  yintuition.
  ydestruct y'; yisolve; simpl in *.
  yinversion H0; fold Contr_clc_s in *; simpl in *.
  ydestruct y; yisolve; simpl in *.
  ydestruct y1; yisolve; simpl in *.
  assert (Red_clc_s (I1 @l y2) y2).
  apply lem_rcontr_s_to_red_s; ycrush.
  assert (is_ltup y2 = false).
  eapply lem_standard_red_s_preserves_not_ltup; ycrush.
  ycrush.
  ydestruct y1_1; yisolve; simpl in *.
  assert (Red_clc_s (K1 @l y1_2 @l y2) y1_2).
  apply lem_rcontr_s_to_red_s; ycrush.
  assert (is_ltup y1_2 = false).
  eapply lem_standard_red_s_preserves_not_ltup; ycrush.
  ycrush.
  ydestruct y1_1_1; yisolve; simpl in *.
  ydestruct y1_1_2; yisolve; simpl in *.
  assert (Red_clc_s (C1 @l T1 @l y1_2 @l y2) y1_2).
  apply lem_rcontr_s_to_red_s; ycrush.
  assert (is_ltup y1_2 = false).
  eapply lem_standard_red_s_preserves_not_ltup; ycrush.
  ycrush.
  assert (Red_clc_s (C1 @l F1 @l y1_2 @l y2) y2).
  apply lem_rcontr_s_to_red_s; ycrush.
  assert (is_ltup y2 = false).
  eapply lem_standard_red_s_preserves_not_ltup; ycrush.
  ycrush.
  simp_hyps.
  destruct H0.
  assert (Red_clc_s (C2 @l y1_1_2 @l y1_2 @l y2) y1_2).
  apply lem_rcontr_s_to_red_s; ycrush.
  assert (is_ltup y1_2 = false).
  eapply lem_standard_red_s_preserves_not_ltup; ycrush.
  ycrush.
  assert (Red_clc_s (C2 @l y1_1_2 @l y1_2 @l y2) y2).
  apply lem_rcontr_s_to_red_s; ycrush.
  assert (is_ltup y2 = false).
  eapply lem_standard_red_s_preserves_not_ltup; ycrush.
  ycrush.
  simp_hyps.
  unfold build_s_result in *.
  assert (exists a b s, split_in_groups l0 (tuple_of_lterm y2) = a :: b :: s).
  ydestruct l0.
  generalize (lem_tuple_len_nonzero y1_2); simpl in *; omega.
  pose lem_split_result; ycrush.
  ycrush.
  destruct H2; subst.
  assert (Standard x0).
  pose lem_subterm_standard; pose_subterm; ycrush.
  eapply lem_standard_red_s_preserves_not_ltup; pose_red_s; ycrush.
  ycrush.
  destruct H2; subst.
  ycrush.
  destruct H0; subst.
  assert (Standard y0).
  pose lem_subterm_standard; pose_subterm; ycrush.
  eapply lem_standard_red_s_preserves_not_ltup; pose_red_s; ycrush.
  ycrush.
  destruct H2; subst.
  ycrush.
  destruct H0; subst.
  ycrush.
  induction l0; simpl in *.
  destruct H0; subst.
  assert (Standard z).
  assert (HH: z :: l' = nil ++ z :: l') by ycrush.
  rewrite HH in *; clear HH.
  pose lem_subterm_standard; pose_subterm; ycrush.
  eapply lem_standard_red_s_preserves_not_ltup; pose_red_s; ycrush.
  ycrush.
  destruct H0; subst.
  ycrush.
  assert (Standard (ltup y'1 y'2 (l0 ++ z :: l'))).
  eapply lem_standard_ltup; ycrush.
  apply IHl0; ycrush.
  assert (HH: tuple_of_lterm y' = y' :: nil).
  ydestruct y'; ycrush.
  rewrite HH in *; clear HH; simpl in *.
  ycrush.
Qed.

Lemma lem_a_commute_0 :
  forall x y z, RootContr_clc_a x y -> Contr_clc_s x z -> Standard y ->
                exists u, (RootContr_clc_a z u \/ z = u) /\ Red_clc_s y u.
Proof.
  intros.
  yinversion H0; fold Contr_clc_s in *; try yelles 1.
  
  pose lem_a_root_commute; ycrush.
  
  invert_rcontr_clc_a; yintuition; yintuition.
  yinversion H; repeat invert_contr_clc_s; [ yelles 2 | yelles 2 | racrush ].
  yinversion H; repeat invert_contr_clc_s; [ yelles 2 | yelles 2 |
                                             ydestruct x; yisolve; yelles 2 ].
  yinversion H; repeat invert_contr_clc_s.
  yelles 2.
  ydestruct x2; yisolve; yelles 2.
  assert (ErasedEqv y' x1) by
      (eauto 8 using lem_red_s_implies_erased_eqv, lem_erased_eqv_trans,
       lem_erased_eqv_sym, lem_contr_s_to_red_s).
  racrush.
  yinversion H3; yinversion H2; yinversion H.
  yinversion H; repeat invert_contr_clc_s; [ yelles 2 | racrush ].
  ydestruct x0; yisolve.
  ydestruct x0_1; yisolve.
  ydestruct x0_1_1; yisolve; simp_hyps.
  repeat invert_contr_clc_s.
  clear -H12; yelles 2.
  assert (is_nonempty l).
  ydestruct l; ycrush.
  assert (Red_clc_s (build_s_result l x0_1_2 (tuple_of_lterm x0_2) (tuple_of_lterm y0))
                      (build_s_result l y' (tuple_of_lterm x0_2) (tuple_of_lterm y0))).
  pose lem_contr_s_s_result_1; pose_red_s; ycrush.
  assert (RootContr_clc_a (S1 l @l y' @l x0_2 @l y0)
                          (build_s_result l y' (tuple_of_lterm x0_2) (tuple_of_lterm y0))).
  racrush.
  ycrush.
  assert (is_nonempty l).
  ydestruct l; ycrush.
  assert (forall z, In z (tuple_of_lterm x0_2) -> R_glue_iterms_l Contr_clc_s z).
  assert (Standard x0_2).
  assert (RootContr_S (S1 l @l x0_1_2 @l x0_2 @l y0)
                      (build_s_result l x0_1_2 (tuple_of_lterm x0_2) (tuple_of_lterm y0))) by ycrush.
  eapply lem_standard_expand_below_S_redex; pose_subterm; ycrush.
  apply lem_standard_implies_glue_iterms_l; ycrush.
  assert (Red_clc_s (build_s_result l x0_1_2 (tuple_of_lterm x0_2) (tuple_of_lterm y0))
                      (build_s_result l x0_1_2 (tuple_of_lterm y') (tuple_of_lterm y0))).
  pose lem_contr_s_s_result_2; pose_red_s; ycrush.
  assert (is_ltup y' = true).
  pose lem_contr_s_preserves_is_ltup; ycrush.
  assert (length (tuple_of_lterm y') = length l).
  rewrite <- lem_contr_s_length with (x := x0_2); ycrush.
  assert (All_pairs (tuple_of_lterm y') ErasedEqv).
  pose lem_contr_s_all_pairs_erased_eqv; ycrush.
  assert (RootContr_clc_a (S1 l @l x0_1_2 @l y' @l y0)
                          (build_s_result l x0_1_2 (tuple_of_lterm y') (tuple_of_lterm y0))).
  racrush.
  ycrush.
  repeat invert_contr_clc_s.
  clear -H10; yelles 2.
  exists (y' @l lterm_of_tuple (firstn n (tuple_of_lterm y0)) @l
             (glue_iterms x0_2 (lterm_of_tuple (skipn n (tuple_of_lterm y0))))).
  racrush.
  exists (x0_1_2 @l lterm_of_tuple (firstn n (tuple_of_lterm y0)) @l
                 (glue_iterms y' (lterm_of_tuple (skipn n (tuple_of_lterm y0))))).
  assert (Standard x0_2).
  apply lem_standard_expand_below_S_redex with
  (r1 := S2 n @l x0_1_2 @l x0_2 @l y0)
    (r2 := x0_1_2 @l lterm_of_tuple (firstn n (tuple_of_lterm y0)) @l
                  (glue_iterms x0_2 (lterm_of_tuple (skipn n (tuple_of_lterm y0)))));
    pose lem_s2_discriminate_y; pose_subterm; ycrush.
  assert (Red_clc_s
            (x0_1_2 @l lterm_of_tuple (firstn n (tuple_of_lterm y0)) @l
                    (glue_iterms x0_2 (lterm_of_tuple (skipn n (tuple_of_lterm y0)))))
            (x0_1_2 @l lterm_of_tuple (firstn n (tuple_of_lterm y0)) @l
                    (glue_iterms y' (lterm_of_tuple (skipn n (tuple_of_lterm y0)))))).
  assert (RootContr_S
            (S2 n @l x0_1_2 @l x0_2 @l y0)
            (x0_1_2 @l lterm_of_tuple (firstn n (tuple_of_lterm y0)) @l
                    (glue_iterms x0_2 (lterm_of_tuple (skipn n (tuple_of_lterm y0)))))).
  ycrush.
  pose lem_standard_implies_glue_iterms_l.
  unfold R_glue_iterms_l in *.
  assert (Contr_clc_s (glue_iterms x0_2 (lterm_of_tuple (skipn n (tuple_of_lterm y0))))
                      (glue_iterms y' (lterm_of_tuple (skipn n (tuple_of_lterm y0))))).
  assert (tuple_of_lterm x0_2 = x0_2 :: nil) by ycrush.
  eapply r; ycrush.
  pose_red_s; ycrush.
  assert (is_ltup y' = false).
  pose lem_standard_not_reduces_to_tuple; pose_red_s; ycrush.
  assert (RootContr_clc_a (S2 n @l x0_1_2 @l y' @l y0)
                          (x0_1_2 @l lterm_of_tuple (firstn n (tuple_of_lterm y0)) @l
                                  (glue_iterms y' (lterm_of_tuple (skipn n (tuple_of_lterm y0)))))).
  racrush.
  ycrush.

  invert_rcontr_clc_a; yintuition; yintuition.
  yinversion H; repeat invert_contr_clc_s; ydestruct x1; yisolve; yelles 2.
  yinversion H; repeat invert_contr_clc_s; racrush.
  yinversion H; repeat invert_contr_clc_s.
  assert (ErasedEqv x y') by
      (eauto 8 using lem_red_s_implies_erased_eqv, lem_erased_eqv_trans,
       lem_erased_eqv_sym, lem_contr_s_to_red_s).
  racrush.
  yinversion H3; racrush.
  yinversion H; repeat invert_contr_clc_s; ydestruct x1; yisolve; yelles 2.
  ydestruct x0; yisolve.
  ydestruct x0_1; yisolve.
  ydestruct x0_1_1; yisolve; simp_hyps.
  assert (is_nonempty l).
  ydestruct l; ycrush.
  assert (Standard y0).
  assert (RootContr_S (S1 l @l x0_1_2 @l x0_2 @l y0)
                      (build_s_result l x0_1_2 (tuple_of_lterm x0_2) (tuple_of_lterm y0))) by ycrush.
  eapply lem_standard_expand_below_S_redex; pose_subterm; ycrush.
  assert (forall z, In z (tuple_of_lterm y0) -> R_glue_iterms_r Contr_clc_s z).
  apply lem_standard_implies_glue_iterms_r; ycrush.
  assert (Red_clc_s (build_s_result l x0_1_2 (tuple_of_lterm x0_2) (tuple_of_lterm y0))
                      (build_s_result l x0_1_2 (tuple_of_lterm x0_2) (tuple_of_lterm y'))).
  pose lem_contr_s_s_result_3; pose_red_s; ycrush.
  assert (is_ltup y' = true).
  pose lem_contr_s_preserves_is_ltup; ycrush.
  assert (lst_sum l < length (tuple_of_lterm y')).
  rewrite <- lem_contr_s_length with (x := y0); ycrush.
  assert (All_pairs (tuple_of_lterm y') ErasedEqv).
  pose lem_contr_s_all_pairs_erased_eqv; ycrush.
  assert (forall x : lterm, In x (tuple_of_lterm y') -> is_ltup x = false).
  pose lem_standard_contr_s_preserves_no_nested_tuple; ycrush.
  assert (RootContr_clc_a (S1 l @l x0_1_2 @l x0_2 @l y')
                          (build_s_result l x0_1_2 (tuple_of_lterm x0_2) (tuple_of_lterm y'))).
  racrush.
  ycrush.
  assert (Standard y0).
  assert (RootContr_S (S2 n @l x0_1_2 @l x0_2 @l y0)
                      (x0_1_2 @l lterm_of_tuple (firstn n (tuple_of_lterm y0)) @l
                              glue_iterms x0_2 (lterm_of_tuple (skipn n (tuple_of_lterm y0))))).
  ycrush.
  eapply lem_standard_expand_below_S_redex; pose_subterm; ycrush.
  assert (forall z, In z (tuple_of_lterm y0) -> R_glue_iterms_r Contr_clc_s z).
  apply lem_standard_implies_glue_iterms_r; ycrush.
  assert (Red_clc_s (x0_1_2 @l lterm_of_tuple (firstn n (tuple_of_lterm y0)) @l
                            (glue_iterms x0_2 (lterm_of_tuple (skipn n (tuple_of_lterm y0)))))
                    (x0_1_2 @l lterm_of_tuple (firstn n (tuple_of_lterm y')) @l
                            (glue_iterms x0_2 (lterm_of_tuple (skipn n (tuple_of_lterm y')))))).
  pose lem_contr_s_s2_result; pose_red_s; ycrush.
  assert (is_ltup y' = true).
  pose lem_contr_s_preserves_is_ltup; ycrush.
  assert (n < length (tuple_of_lterm y')).
  rewrite <- lem_contr_s_length with (x := y0); ycrush.
  assert (All_pairs (tuple_of_lterm y') ErasedEqv).
  pose lem_contr_s_all_pairs_erased_eqv; ycrush.
  assert (forall x : lterm, In x (tuple_of_lterm y') -> is_ltup x = false).
  pose lem_standard_contr_s_preserves_no_nested_tuple; ycrush.
  assert (RootContr_clc_a (S2 n @l x0_1_2 @l x0_2 @l y')
                          (x0_1_2 @l lterm_of_tuple (firstn n (tuple_of_lterm y')) @l
                                  (glue_iterms x0_2 (lterm_of_tuple (skipn n (tuple_of_lterm y')))))).
  racrush.
  ycrush.
Qed.

Lemma lem_a_commute_1 :
  forall x y z, Contr_clc_a x y -> RootContr_clc_s x z -> Standard y ->
                exists u, (Contr_clc_a z u \/ z = u) /\ Red_clc_s y u.
Proof.
  intros.
  yinversion H; fold Contr_clc_a in *; try yelles 1.

  pose lem_a_root_commute; pose_contr_a; ycrush.

  invert_rcontr_clc_s; yintuition; yintuition.
  yinversion H; repeat invert_contr_clc_a.
  racrush.
  racrush.
  yinversion H3; racrush.
  yinversion H3; racrush.
  exists y'; pose_red_s; ycrush.
  yinversion H; repeat invert_contr_clc_a.
  racrush.
  racrush.
  yinversion H3; racrush.
  yinversion H3; racrush.
  exists x1; pose_red_s; ycrush.
  yinversion H; repeat invert_contr_clc_a.
  racrush.
  racrush.
  yinversion H4; racrush.
  exists x; intuition; apply lem_rcontr_s_to_red_s; ycrush.
  assert (ErasedEqv y' x1) by
      (eauto 8 using lem_contr_a_to_erased_eqv, lem_erased_eqv_trans,
       lem_erased_eqv_sym, lem_contr_s_to_red_s).
  exists y'; intuition; apply lem_rcontr_s_to_red_s; ycrush.
  yinversion H; repeat invert_contr_clc_a.
  racrush.
  racrush.
  yinversion H4; racrush.
  exists x1; intuition; apply lem_rcontr_s_to_red_s; ycrush.
  assert (ErasedEqv y' x1) by
      (eauto 8 using lem_contr_a_to_erased_eqv, lem_erased_eqv_trans,
       lem_erased_eqv_sym, lem_contr_s_to_red_s).
  exists x1; intuition; apply lem_rcontr_s_to_red_s; ycrush.
  yinversion H; repeat invert_contr_clc_a.
  yinversion H2; racrush.
  yinversion H; repeat invert_contr_clc_a.
  racrush.
  yinversion H4; racrush.
  exists y'; intuition; apply lem_rcontr_s_to_red_s; ycrush.
  rename x into l.
  yinversion H; repeat invert_contr_clc_a.
  racrush.
  racrush.
  yinversion H11; racrush.
  assert (is_nonempty l).
  ydestruct l; ycrush.
  assert (Contr_clc_a (build_s_result l x1 (tuple_of_lterm x2) (tuple_of_lterm x3))
                      (build_s_result l y' (tuple_of_lterm x2) (tuple_of_lterm x3))).
  pose lem_contr_a_s_result_1; ycrush.
  assert (Red_clc_s (S1 l @l y' @l x2 @l x3)
                    (build_s_result l y' (tuple_of_lterm x2) (tuple_of_lterm x3))).
  apply lem_rcontr_s_to_red_s; ycrush.
  ycrush.
  assert (is_nonempty l).
  ydestruct l; ycrush.
  assert (Contr_clc_a (build_s_result l x1 (tuple_of_lterm x2) (tuple_of_lterm x3))
                      (build_s_result l x1 (tuple_of_lterm y') (tuple_of_lterm x3))).
  pose lem_contr_a_s_result_2; ycrush.
  assert (is_ltup y' = true).
  pose lem_contr_a_preserves_is_ltup; ycrush.
  assert (length (tuple_of_lterm y') = length l).
  rewrite <- lem_contr_a_length with (x := x2); ycrush.
  assert (All_pairs (tuple_of_lterm y') ErasedEqv).
  pose lem_contr_a_all_pairs_erased_eqv; ycrush.
  assert (Red_clc_s (S1 l @l x1 @l y' @l x3)
                    (build_s_result l x1 (tuple_of_lterm y') (tuple_of_lterm x3))).
  apply lem_rcontr_s_to_red_s; ycrush.
  assert (Sterm (build_s_result l x1 (tuple_of_lterm y') (tuple_of_lterm x3))).
  pose lem_standard_sterm; pose_sterm; ycrush.
  ycrush.
  rename x into n.
  yinversion H; repeat invert_contr_clc_a.
  racrush.
  racrush.
  yinversion H9; racrush.
  exists (y' @l lterm_of_tuple (firstn n (tuple_of_lterm x3)) @l
             (glue_iterms x2 (lterm_of_tuple (skipn n (tuple_of_lterm x3))))).
  split; [ pose_contr_a; ycrush | apply lem_rcontr_s_to_red_s; ycrush ].
  exists (x1 @l lterm_of_tuple (firstn n (tuple_of_lterm x3)) @l
             (glue_iterms y' (lterm_of_tuple (skipn n (tuple_of_lterm x3))))).
  assert (Contr_clc_a
            (x1 @l lterm_of_tuple (firstn n (tuple_of_lterm x3)) @l
                (glue_iterms x2 (lterm_of_tuple (skipn n (tuple_of_lterm x3)))))
            (x1 @l lterm_of_tuple (firstn n (tuple_of_lterm x3)) @l
                (glue_iterms y' (lterm_of_tuple (skipn n (tuple_of_lterm x3)))))).
  pose lem_contr_a_glue_l.
  unfold R_glue_iterms_l in *.
  pose_contr_a; ycrush.
  assert (is_ltup y' = false).
  yinversion H10; try yelles 1.
  assert (HH: Sterm y') by racrush.
  yinversion HH; ycrush.
  assert (Red_clc_s (S2 n @l x1 @l y' @l x3)
                    (x1 @l lterm_of_tuple (firstn n (tuple_of_lterm x3)) @l
                        (glue_iterms y' (lterm_of_tuple (skipn n (tuple_of_lterm x3)))))).
  apply lem_rcontr_s_to_red_s; ycrush.
  ycrush.

  invert_rcontr_clc_s; yintuition; yintuition.
  yinversion H; repeat invert_contr_clc_a; exists x; pose_red_s; ycrush.
  yinversion H; repeat invert_contr_clc_a; exists y'; pose_red_s; ycrush.
  yinversion H; repeat invert_contr_clc_a.
  assert (ErasedEqv x y') by
      (eauto 8 using lem_contr_a_to_erased_eqv, lem_erased_eqv_trans,
       lem_erased_eqv_sym, lem_contr_s_to_red_s).
  exists x; intuition; apply lem_rcontr_s_to_red_s; ycrush.
  yinversion H; repeat invert_contr_clc_a.
  assert (ErasedEqv x y') by
      (eauto 8 using lem_contr_a_to_erased_eqv, lem_erased_eqv_trans,
       lem_erased_eqv_sym, lem_contr_s_to_red_s).
  exists y'; intuition; apply lem_rcontr_s_to_red_s; ycrush.
  yinversion H.
  exists y'; pose_red_s; ycrush.
  yinversion H; repeat invert_contr_clc_a; exists x; pose_red_s; ycrush.
  rename x into l.
  yinversion H; repeat invert_contr_clc_a.
  assert (is_nonempty l).
  ydestruct l; ycrush.
  assert (Contr_clc_a (build_s_result l x1 (tuple_of_lterm x2) (tuple_of_lterm x3))
                      (build_s_result l x1 (tuple_of_lterm x2) (tuple_of_lterm y'))).
  pose lem_contr_a_s_result_3; ycrush.
  assert (is_ltup y' = true).
  pose lem_contr_a_preserves_is_ltup; ycrush.
  assert (lst_sum l < length (tuple_of_lterm y')).
  rewrite <- lem_contr_a_length with (x := x3); ycrush.
  assert (All_pairs (tuple_of_lterm y') ErasedEqv).
  pose lem_contr_a_all_pairs_erased_eqv; ycrush.
  assert (forall x : lterm, In x (tuple_of_lterm y') -> is_ltup x = false).
  assert (Standard y').
  pose lem_subterm_standard; pose_subterm; ycrush.
  Reconstr.hobvious (@H14)
	            (@standard.lem_standard_no_nested_tuple)
		    Reconstr.Empty.
  assert (Red_clc_s (S1 l @l x1 @l x2 @l y')
                    (build_s_result l x1 (tuple_of_lterm x2) (tuple_of_lterm y'))).
  apply lem_rcontr_s_to_red_s; ycrush.
  ycrush.
  rename x into n.
  yinversion H; repeat invert_contr_clc_a.
  assert (Contr_clc_a (x1 @l lterm_of_tuple (firstn n (tuple_of_lterm x3)) @l
                          (glue_iterms x2 (lterm_of_tuple (skipn n (tuple_of_lterm x3)))))
                      (x1 @l lterm_of_tuple (firstn n (tuple_of_lterm y')) @l
                          (glue_iterms x2 (lterm_of_tuple (skipn n (tuple_of_lterm y')))))).
  pose lem_contr_a_s2_result; ycrush.
  assert (is_ltup y' = true).
  pose lem_contr_a_preserves_is_ltup; ycrush.
  assert (n < length (tuple_of_lterm y')).
  rewrite <- lem_contr_a_length with (x := x3); ycrush.
  assert (All_pairs (tuple_of_lterm y') ErasedEqv).
  pose lem_contr_a_all_pairs_erased_eqv; ycrush.
  assert (forall x : lterm, In x (tuple_of_lterm y') -> is_ltup x = false).
  assert (Standard y').
  pose lem_subterm_standard; pose_subterm; ycrush.
  Reconstr.hobvious (@H11)
	            (@standard.lem_standard_no_nested_tuple)
		    Reconstr.Empty.
  assert (Red_clc_s (S2 n @l x1 @l x2 @l y')
                    (x1 @l lterm_of_tuple (firstn n (tuple_of_lterm y')) @l
                        (glue_iterms x2 (lterm_of_tuple (skipn n (tuple_of_lterm y')))))).
  apply lem_rcontr_s_to_red_s; ycrush.
  ycrush.
Qed.

(* lemma 19 *)
Lemma lem_a_commute :
  forall x y z, Contr_clc_a x y -> Contr_clc_s x z -> Standard y ->
                exists u, (Contr_clc_a z u \/ z = u) /\ Red_clc_s y u.
Proof.
  assert (forall x z, Contr_clc_s x z ->
                      forall y, Contr_clc_a x y -> Standard y ->
                                exists u, (Contr_clc_a z u \/ z = u) /\ Red_clc_s y u).
  intros x z H.
  induction H; fold Contr_clc_s in *; yintros.
  
  pose lem_a_commute_1; ycrush.
  
  invert_contr_clc_a.
  assert (Contr_clc_s (x @l y) (x' @l y)).
  pose_contr_s; ycrush.
  pose lem_a_commute_0; pose_contr_a; ycrush.
  assert (Standard x'0).
  pose lem_subterm_standard; pose_subterm; ycrush.
  pose_contr_a; pose_red_s; ycrush.
  assert (Standard y').
  pose lem_subterm_standard; pose_subterm; ycrush.
  pose_contr_a; pose_red_s; ycrush.

  invert_contr_clc_a.
  assert (Contr_clc_s (x @l y) (x @l y')).
  pose_contr_s; ycrush.
  pose lem_a_commute_0; pose_contr_a; ycrush.
  assert (Standard x').
  pose lem_subterm_standard; pose_subterm; ycrush.
  pose_contr_a; pose_red_s; ycrush.
  assert (Standard y'0).
  pose lem_subterm_standard; pose_subterm; ycrush.
  pose_contr_a; pose_red_s; ycrush.

  yinversion H0; fold Contr_clc_a in *; yisolve.
  racrush.
  assert (Standard x'0).
  pose lem_subterm_standard; pose_subterm; ycrush.
  pose_contr_a; pose_red_s; ycrush.  
  pose_contr_a; pose_red_s; ycrush.
  pose_contr_a; pose_red_s; ycrush.

  yinversion H0; fold Contr_clc_a in *; yisolve.
  racrush.
  pose_contr_a; pose_red_s; ycrush.
  assert (Standard y'0).
  pose lem_subterm_standard; pose_subterm; ycrush.
  pose_contr_a; pose_red_s; ycrush.  
  pose_contr_a; pose_red_s; ycrush.

  yinversion H0; fold Contr_clc_a in *; yisolve.
  racrush.
  pose_contr_a; pose_red_s; ycrush.
  pose_contr_a; pose_red_s; ycrush.
  assert (Standard z'0).
  pose lem_subterm_standard; pose_subterm; ycrush.
  generalize l0 l'0 H5.
  clear l0 l'0 H1 H5.
  induction l; intros.
  ydestruct l0.
  simpl in *.
  yinversion H5.
  assert (exists u : lterm, (Contr_clc_a z' u \/ z' = u) /\ Red_clc_s z'0 u).
  pose_contr_a; pose_red_s; ycrush.
  assert (exists u : lterm,
             (Contr_clc_a (ltup x y (nil ++ z' :: l')) u \/ ltup x y (nil ++ z' :: l') = u) /\
             Red_clc_s (ltup x y (nil ++ z'0 :: l')) u).
  pose_contr_a; pose_red_s; ycrush.
  ycrush.
  assert (l = z).
  yinversion H5; trivial.
  assert (l' = (l0 ++ z0 :: l'0)).
  yinversion H5; trivial.
  subst; simpl; clear H5.
  assert (Contr_clc_a (ltup x y ((z' :: l0) ++ z0 :: l'0)) (ltup x y ((z' :: l0) ++ z'0 :: l'0))).
  pose_contr_a; ycrush.
  assert (Red_clc_s (ltup x y (nil ++ z :: l0 ++ z'0 :: l'0)) (ltup x y (nil ++ z' :: l0 ++ z'0 :: l'0))).
  clear -H; pose_red_s; ycrush.
  ycrush.
  ydestruct l0; simpl in *.
  assert (a = z0).
  yinversion H5; trivial.
  assert (l'0 = l ++ z :: l').
  yinversion H5; trivial.
  subst; simpl in *.
  assert (Contr_clc_a (ltup x y (nil ++ z0 :: l ++ z' :: l'))
                      (ltup x y (nil ++ z'0 :: l ++ z' :: l'))).
  pose_contr_a; ycrush.
  assert (Red_clc_s (ltup x y ((z'0 :: l) ++ z :: l')) (ltup x y ((z'0 :: l) ++ z' :: l'))).
  pose_red_s; ycrush.
  ycrush.
  yinversion H5.
  yforwarding.
  assert (is_ltup (ltup x y (l1 ++ z'0 :: l'0)) = true) by ycrush.
  assert (is_ltup x0 = true).
  pose lem_red_s_preserves_is_ltup; ycrush.
  ydestruct x0; yisolve.
  yintuition.
  pose lem_contr_a_ltup_extend; pose lem_red_s_ltup_extend; ycrush.
  yinversion H4.
  pose lem_red_s_ltup_extend; ycrush.
  ycrush.
Qed.

(* corollary 20 *)
Lemma lem_a_commute_red :
  forall x y z, Contr_clc_a x y -> Red_clc_s x z -> StronglyStandard y ->
                exists u, (Contr_clc_a z u \/ z = u) /\ Red_clc_s y u.
Proof.
  assert (forall x z, Red_clc_s x z ->
                      forall y, Contr_clc_a x y -> StronglyStandard y ->
                                exists u, (Contr_clc_a z u \/ z = u) /\ Red_clc_s y u).
  intros x z H.
  induction H; fold Red_clc_s in *; yintros.
  pose lem_a_commute; pose_red_s; ycrush.
  ycrush.
  assert (exists u : lterm, (Contr_clc_a y u \/ y = u) /\ Red_clc_s y0 u) by ycrush.
  yintuition.
  assert (exists u : lterm, (Contr_clc_a z u \/ z = u) /\ Red_clc_s x0 u).
  assert (StronglyStandard x0).
  pose lem_reduce_subterm_strongly_standard; pose_subterm; ycrush.
  ycrush.
  pose_red_s; ycrush.
  pose_red_s; ycrush.
  ycrush.
Qed.
