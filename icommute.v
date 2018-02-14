(* This file contains the formalisation of lemma 11 *)

Require Import general.
Require Import iterms.
Require Import lterms.
Require Import erase_facts.
Require Import svars.
Require Import ired.
Require Import sred.

Ltac invert_contr_exp_i_app :=
  simpl in *; subst;
  repeat match goal with
         | [ H : Contr_exp_clc_i _ (_ @l _) |- _ ] =>
           yinversion H; fold Contr_exp_clc_i in *; simp_hyps; try yelles 1
         end.

Lemma lem_contr_exp_i_glue_l : forall x, R_glue_iterms_l Contr_exp_clc_i x.
Proof.
  unfold R_glue_iterms_l.
  intros x x' y H.
  assert (Contr_clc_i x x' \/ Contr_clc_i x' x).
  apply lem_contr_exp_i; auto.
  apply lem_contr_exp_i.
  destruct x; try yelles 1.
  destruct x'; try yelles 1.
  destruct y; simpl; try solve [ pose_ctx_l; unfold Contr_clc_i in *; yelles 1 ].
  yintuition.
  assert (Contr_clc i i0).
  unfold Contr_clc_i; yelles 1.
  assert (Contr_clc (i @i i1) (i0 @i i1)).
  pose_ctx_i; unfold Contr_clc in *; yelles 1.
  pose_ctx_l; unfold Contr_clc_i in *; yelles 1.
  assert (Contr_clc i0 i).
  unfold Contr_clc_i; yelles 1.
  assert (Contr_clc (i0 @i i1) (i @i i1)).
  pose_ctx_i; unfold Contr_clc in *; yelles 1.
  pose_ctx_l; unfold Contr_clc_i in *; yelles 1.
  pose_ctx_l; unfold Contr_clc_i in *; yelles 1.
  pose_ctx_l; unfold Contr_clc_i in *; yelles 1.
Qed.

Lemma lem_contr_exp_i_glue_r : forall x, R_glue_iterms_r Contr_exp_clc_i x.
Proof.
  unfold R_glue_iterms_r.
  intros x y x' H.
  assert (Contr_clc_i x x' \/ Contr_clc_i x' x).
  apply lem_contr_exp_i; auto.
  apply lem_contr_exp_i.
  destruct x; try yelles 1.
  destruct x'; try yelles 1.
  destruct y; simpl; try solve [ pose_ctx_l; unfold Contr_clc_i in *; yelles 1 ].
  yintuition.
  assert (Contr_clc i i0).
  unfold Contr_clc_i; yelles 1.
  assert (Contr_clc (i1 @i i) (i1 @i i0)).
  pose_ctx_i; unfold Contr_clc in *; yelles 1.
  pose_ctx_l; unfold Contr_clc_i in *; yelles 1.
  assert (Contr_clc i0 i).
  unfold Contr_clc_i; yelles 1.
  assert (Contr_clc (i1 @i i0) (i1 @i i)).
  pose_ctx_i; unfold Contr_clc in *; yelles 1.
  pose_ctx_l; unfold Contr_clc_i in *; yelles 1.
  pose_ctx_l; unfold Contr_clc_i in *; yelles 2.
  pose_ctx_l; unfold Contr_clc_i in *; yelles 2.
Qed.

Lemma lem_contr_exp_i_s_result_1 :
  forall ns x x' l1 l2,
    is_nonempty ns ->
    Contr_exp_clc_i x x' ->
    Contr_exp_clc_i (build_s_result ns x l1 l2) (build_s_result ns x' l1 l2).
Proof.
  apply lem_s_result_1; cei_crush.
Qed.

Lemma lem_contr_exp_i_s_result_2 :
  forall ns x y y' l,
    is_ltup y = true ->
    lst_sum ns < length l ->
    length (tuple_of_lterm y) = length ns ->
    Contr_exp_clc_i y y' ->
    Contr_exp_clc_i (build_s_result ns x (tuple_of_lterm y) l)
                    (build_s_result ns x (tuple_of_lterm y') l).
Proof.
  intros.
  assert (forall z, In z (tuple_of_lterm y) -> R_glue_iterms_l Contr_exp_clc_i z).
  pose lem_contr_exp_i_glue_l; ycrush.
  apply lem_s_result_2; cei_crush.
Qed.

Lemma lem_contr_exp_i_s_result_3 :
  forall ns x l y y',
    is_ltup y = true ->
    lst_sum ns < length (tuple_of_lterm y) ->
    length l = length ns ->
    Contr_exp_clc_i y y' ->
    Contr_exp_clc_i (build_s_result ns x l (tuple_of_lterm y))
                    (build_s_result ns x l (tuple_of_lterm y')).
Proof.
  intros.
  assert (forall z, In z (tuple_of_lterm y) -> R_glue_iterms_r Contr_exp_clc_i z).
  pose lem_contr_exp_i_glue_r; ycrush.
  apply lem_s_result_3; cei_crush.
Qed.

Lemma lem_contr_exp_i_s2_result :
  forall n x y z z',
    is_ltup z = true ->
    Contr_exp_clc_i z z' ->
    Contr_exp_clc_i (x @l lterm_of_tuple (firstn n (tuple_of_lterm z)) @l
                       glue_iterms y (lterm_of_tuple (skipn n (tuple_of_lterm z))))
                    (x @l lterm_of_tuple (firstn n (tuple_of_lterm z')) @l
                       glue_iterms y (lterm_of_tuple (skipn n (tuple_of_lterm z')))).
Proof.
  intros.
  assert (forall u, In u (tuple_of_lterm z) -> R_glue_iterms_r Contr_exp_clc_i u).
  pose lem_contr_exp_i_glue_r; ycrush.
  apply lem_s2_result; cei_crush.
Qed.

Lemma lem_contr_exp_i_length_preserved :
  forall x y, is_ltup x = true -> is_ltup y = true ->
              Contr_exp_clc_i x y -> length (tuple_of_lterm x) = length (tuple_of_lterm y).
Proof.
  induction x, y; try yelles 2.
  intros.
  yinversion H1.
  yinversion H2.
  fold Contr_exp_clc_i in *; ycrush.
  fold Contr_exp_clc_i in *; ycrush.
  induction l1; ycrush.
Qed.

Lemma lem_contr_exp_i_preserves_ltup :
  forall x y, Contr_exp_clc_i x y -> is_ltup x = true -> is_ltup y = true.
Proof.
  yelles 1.
Qed.

Lemma lem_contr_exp_i_preserves_not_ltup :
  forall x y, Contr_exp_clc_i x y -> is_ltup x = false -> is_ltup y = false.
Proof.
  yelles 1.
Qed.

Lemma lem_contr_exp_i_preserves_no_nested_tuple :
  forall y y', Contr_exp_clc_i y y' ->
               (forall x, In x (tuple_of_lterm y) -> is_ltup x = false) ->
               forall x, In x (tuple_of_lterm y') -> is_ltup x = false.
Proof.
  intros.
  assert (is_ltup y' = true \/ is_ltup y' = false) by ycrush.
  yintuition.
  ydestruct y'; yisolve; simpl in *.
  yinversion H; fold Contr_exp_clc_i in *; simpl in *.
  ycrush.
  pose lem_contr_exp_i_preserves_not_ltup; ycrush.
  pose lem_contr_exp_i_preserves_not_ltup; ycrush.
  yintuition; try yelles 1.
  induction l0; simpl in *.
  pose lem_contr_exp_i_preserves_not_ltup; ycrush.
  intuition; firstorder.
  assert (HH: tuple_of_lterm y' = y' :: nil) by ycrush.
  rewrite HH in *; clear HH.
  simpl in *; ycrush.
Qed.

Lemma lem_contr_exp_i_preserves_iterm :
  forall x y, Contr_exp_clc_i x y -> is_iterm x = true -> is_iterm y = true.
Proof.
  yelles 1.
Qed.

Lemma lem_contr_exp_i_preserves_sterm :
  forall x y, Contr_exp_clc_i x y -> Sterm x -> Sterm y.
Proof.
  induction x; try (pose_sterm; yelles 1).
  intros y H1 H2.
  yinversion H1; yinversion H2; pose_sterm; yelles 1.
Qed.

Lemma lem_contr_exp_i_postpone : forall x y z, Contr_exp_clc_i x y -> Contr_clc_s y z ->
                                               exists u, Contr_clc_s x u /\
                                                         (Contr_exp_eq_clc_i u z).
Proof.
  assert (forall y x z, Contr_exp_clc_i x y -> Contr_clc_s y z ->
                        exists u, Contr_clc_s x u /\
                                  (Contr_exp_eq_clc_i u z)).
  unfold Contr_exp_eq_clc_i in *.
  intro y; lterm_induction y.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.

  intros x z H0 H.
  yinversion H; fold Contr_clc_s in *.

  assert (exists u : lterm, RootContr_clc_s x u /\ (u = z \/ Contr_exp_clc_i u z)).
  ydestruct y1; try yelles 1.
  invert_contr_exp_i_app.
  ydestruct y1_1; try yelles 1.
  invert_contr_exp_i_app.
  ydestruct y1_1_1; try yelles 1.
  invert_contr_exp_i_app.
  invert_contr_exp_i_app.
  pose lem_contr_exp_i_implies_erased_eqv; pose_erased_eqv; ycrush.
  pose lem_contr_exp_i_implies_erased_eqv; pose_erased_eqv; ycrush.
  invert_contr_exp_i_app.
  assert (is_nonempty l).
  ydestruct l; yisolve; ydestruct y1_2; simpl in *; omega.
  pose lem_contr_exp_i_s_result_1; ycrush.

  assert (is_nonempty l).
  ydestruct l; yisolve; ydestruct y1_2; simpl in *; omega.
  assert (length (tuple_of_lterm y) = length l).
  pose lem_contr_exp_i_length_preserved; pose lem_contr_exp_i_sym;
    pose lem_contr_exp_i_preserves_ltup; ycrush.
  yintuition.
  assert (All_pairs (tuple_of_lterm y) ErasedEqv).
  apply lem_all_pairs_erased_eqv_rev with (R := Contr_exp_clc_i) (y' := y1_2);
    pose lem_contr_exp_i_implies_erased_eqv; cei_crush.
  assert (is_ltup y = true).
  pose lem_contr_exp_i_preserves_ltup; pose lem_contr_exp_i_sym; ycrush.
  pose lem_contr_exp_i_s_result_2; ycrush.

  assert (is_nonempty l).
  ydestruct l; yisolve; ydestruct y1_2; simpl in *; omega.
  assert (lst_sum l < length (tuple_of_lterm y)).
  pose lem_contr_exp_i_length_preserved; pose lem_contr_exp_i_sym;
    pose lem_contr_exp_i_preserves_ltup; ycrush.
  yintuition.
  assert (All_pairs (tuple_of_lterm y) ErasedEqv).
  apply lem_all_pairs_erased_eqv_rev with (R := Contr_exp_clc_i) (y' := y2);
    pose lem_contr_exp_i_implies_erased_eqv; cei_crush.
  assert (is_ltup y = true).
  pose lem_contr_exp_i_preserves_ltup; pose lem_contr_exp_i_sym; ycrush.
  assert (forall x : lterm, In x (tuple_of_lterm y) -> is_ltup x = false).
  pose lem_contr_exp_i_preserves_no_nested_tuple; pose lem_contr_exp_i_sym; ycrush.
  pose lem_contr_exp_i_s_result_3; ycrush.

  invert_contr_exp_i_app.
  exists (y @l lterm_of_tuple (firstn n (tuple_of_lterm y2)) @l
            glue_iterms y1_2 (lterm_of_tuple (skipn n (tuple_of_lterm y2)))).
  cei_crush.
  exists (y1_1_2 @l lterm_of_tuple (firstn n (tuple_of_lterm y2)) @l
                 glue_iterms y (lterm_of_tuple (skipn n (tuple_of_lterm y2)))).
  pose lem_contr_exp_i_glue_l; unfold R_glue_iterms_l in *; cei_crush.
  assert (All_pairs (tuple_of_lterm y) ErasedEqv).
  apply lem_all_pairs_erased_eqv_rev with (R := Contr_exp_clc_i) (y' := y2);
    pose lem_contr_exp_i_implies_erased_eqv; cei_crush.
  assert (is_ltup y = true).
  pose lem_contr_exp_i_preserves_ltup; pose lem_contr_exp_i_sym; ycrush.
  assert (n < length (tuple_of_lterm y)).
  pose lem_contr_exp_i_length_preserved; pose lem_contr_exp_i_sym;
    pose lem_contr_exp_i_preserves_ltup; ycrush.
  assert (forall x : lterm, In x (tuple_of_lterm y) -> is_ltup x = false).
  pose lem_contr_exp_i_preserves_no_nested_tuple; pose lem_contr_exp_i_sym; ycrush.
  pose lem_contr_exp_i_s2_result; ycrush.

  yinversion H0; yisolve; fold Contr_exp_clc_i in *.
  unfold Contr_clc_s in *; cei_crush.
  unfold Contr_clc_s in *; cei_crush.

  yinversion H0; yisolve; fold Contr_exp_clc_i in *.
  unfold Contr_clc_s in *; cei_crush.
  unfold Contr_clc_s in *; cei_crush.
  
  yinversion H0; yisolve; fold Contr_exp_clc_i in *.
  unfold Contr_clc_s in *; cei_crush.
  unfold Contr_clc_s in *; cei_crush.

  (* commutation in tuples *)
  intros x z H0 H.
  yinversion H; yisolve; fold Contr_clc_s in *.
  yinversion H0; yisolve; fold Contr_exp_clc_i in *.
  unfold Contr_clc_s in *; cei_crush.
  unfold Contr_clc_s in *; cei_crush.
  unfold Contr_clc_s in *; cei_crush.
  yinversion H0; yisolve; fold Contr_exp_clc_i in *.
  unfold Contr_clc_s in *; cei_crush.
  unfold Contr_clc_s in *; cei_crush.
  unfold Contr_clc_s in *; cei_crush.
  yinversion H0; yisolve; fold Contr_exp_clc_i in *.
  unfold Contr_clc_s in *; cei_crush.
  unfold Contr_clc_s in *; cei_crush.
  generalize l0 l'0 H4.
  clear l0 l'0 H4.
  induction l; intros.
  ydestruct l0.
  simpl in *.
  assert (z'0 = z0) by ycrush.
  assert (l'0 = l') by ycrush.
  subst.
  assert (exists u : lterm, Contr_clc_s z u /\ (Contr_exp_clc_i u z' \/ u = z')) by ycrush.
  yintuition.
  assert (Contr_exp_clc_i (ltup y1 y2 (nil ++ x :: l')) (ltup y1 y2 (nil ++ z' :: l'))) by cei_crush.
  assert (Contr_clc_s (ltup y1 y2 (nil ++ z :: l')) (ltup y1 y2 (nil ++ x :: l'))).
  unfold Contr_clc_s in *; cei_crush.
  ycrush.
  assert (Contr_clc_s (ltup y1 y2 (nil ++ z :: l')) (ltup y1 y2 (nil ++ z' :: l'))).
  unfold Contr_clc_s in *; cei_crush.
  ycrush.
  simpl in *.
  assert (z0 = l) by ycrush.
  assert (l' = l0 ++ z'0 :: l'0) by ycrush.
  subst.
  clear -H2 H5.
  exists (ltup y1 y2 (z' :: l0 ++ z :: l'0)).
  split.
  assert (Contr_clc_s (ltup y1 y2 (nil ++ l :: (l0 ++ z :: l'0)))
                          (ltup y1 y2 (nil ++ z' :: (l0 ++ z :: l'0)))).
  unfold Contr_clc_s in *; cei_crush.
  auto with datatypes.
  assert (Contr_exp_clc_i (ltup y1 y2 ((z' :: l0) ++ z :: l'0))
                          (ltup y1 y2 ((z' :: l0) ++ z'0 :: l'0))).
  unfold Contr_exp_clc_i in *; cei_crush.
  auto with datatypes.
  ydestruct l0.  
  simpl in *.
  assert (a = z'0) by ycrush.
  assert (l'0 = l ++ z0 :: l') by ycrush.
  subst.
  clear -H2 H5.
  exists (ltup y1 y2 (z :: l ++ z' :: l')).
  split.
  assert (Contr_clc_s (ltup y1 y2 ((z :: l) ++ z0 :: l'))
                      (ltup y1 y2 ((z :: l) ++ z' :: l'))).
  unfold Contr_clc_s in *; cei_crush.
  auto with datatypes.
  left.
  assert (Contr_exp_clc_i (ltup y1 y2 (nil ++ z :: (l ++ z' :: l')))
                          (ltup y1 y2 (nil ++ z'0 :: (l ++ z' :: l')))).
  cei_crush.
  auto with datatypes.
  assert (forall y : lterm,
             In y (l ++ z0 :: l') ->
             forall x z : lterm,
               Contr_exp_clc_i x y ->
               Contr_clc_s y z -> exists u : lterm, Contr_clc_s x u /\
                                                    (Contr_exp_clc_i u z \/ u = z)).
  ycrush.
  assert (l1 ++ z'0 :: l'0 = l ++ z0 :: l') by ycrush.
  generalize (IHl H l1 l'0 H0).
  intro HH.
  assert (l0 = a) by ycrush.
  subst.
  clear -HH.
  yintuition.
  assert (is_ltup x = true) by ycrush.
  ydestruct x; yisolve.
  assert (Contr_clc_s (ltup y1 y2 (a :: l1 ++ z :: l'0)) (ltup x1 x2 (a :: l0))).
  yinversion H; fold Contr_clc_s in *.
  ycrush.
  unfold Contr_clc_s in *; cei_crush.
  unfold Contr_clc_s in *; cei_crush.
  assert (Contr_clc_s (ltup x1 x2 ((a :: l2) ++ z0 :: l'1))
                      (ltup x1 x2 ((a :: l2) ++ z'0 :: l'1))).
  unfold Contr_clc_s in *; cei_crush.
  ycrush.
  assert (Contr_exp_clc_i (ltup x1 x2 (a :: l0)) (ltup y1 y2 (a :: l ++ z' :: l'))).
  yinversion H1; fold Contr_exp_clc_i in *.
  ycrush.
  cei_crush.
  cei_crush.
  assert (Contr_exp_clc_i (ltup y1 y2 ((a :: l2) ++ z0 :: l'1))
                          (ltup y1 y2 ((a :: l2) ++ z'0 :: l'1))).
  cei_crush.
  ycrush.
  ycrush.
  yinversion H; yisolve; fold Contr_clc_s in *.
  unfold Contr_clc_s in *; cei_crush.
  unfold Contr_clc_s in *; cei_crush.
  assert (Contr_clc_s (ltup y1 y2 ((a :: l0) ++ z0 :: l'1))
                      (ltup y1 y2 ((a :: l0) ++ z'0 :: l'1))).
  unfold Contr_clc_s in *; cei_crush.
  ycrush.

  ycrush.
  ycrush.
  ycrush.
Qed.

(* lemma 11 *)
Lemma lem_contr_exp_i_postpone_red : forall x y z, Contr_exp_clc_i x y -> Red_clc_s y z ->
                                                   exists u, Red_clc_s x u /\
                                                             (Contr_exp_eq_clc_i u z).
Proof.
  assert (forall y z, Red_clc_s y z -> forall x, Contr_exp_clc_i x y ->
                                                 exists u, Red_clc_s x u /\
                                                           (Contr_exp_eq_clc_i u z)).
  intros y z H.
  induction H.
  pose lem_contr_exp_i_postpone; pose_red_s; ycrush.
  unfold Contr_exp_eq_clc_i; pose_red_s; ycrush.
  fold Red_clc_s in *; intros.
  yforwarding.
  assert (exists u : lterm, Red_clc_s x1 u /\ Contr_exp_eq_clc_i u z).
  unfold Contr_exp_eq_clc_i in *; ycrush.
  pose_red_s; ycrush.
  ycrush.
Qed.

Lemma lem_contr_exp_i_preserves_snf : forall x y, sNF x -> Contr_exp_clc_i x y -> sNF y.
Proof.
  intros.
  assert ((exists z, Contr_clc_s y z) -> False).
  yintro.
  assert (exists u, Contr_clc_s x u).
  pose lem_contr_exp_i_postpone; ycrush.
  pose lem_subterm_redex; unfold sNF in *; ycrush.
  pose lem_subterm_redex; unfold sNF in *; ycrush.
Qed.
