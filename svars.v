
Require Import general.
Require Import list_facts.
Require Import iterms.
Require Import lterms.
Require Import erase_facts.

Section SVars.

Variable R : lterm -> lterm -> Prop.
Variable R_cong_app_l : forall x x' y, R x x' -> R (x @l y) (x' @l y).
Variable R_cong_app_r : forall x y y', R y y' -> R (x @l y) (x @l y').
Variable R_cong_ltup_0 : forall x x' y l, R x x' -> R (ltup x y l) (ltup x' y l).
Variable R_cong_ltup_1 : forall x y y' l, R y y' -> R (ltup x y l) (ltup x y' l).
Variable R_cong_ltup_2 : forall x y l1 z z' l2, R z z' -> R (ltup x y (l1 ++ z :: l2))
                                                            (ltup x y (l1 ++ z' :: l2)).
Variable R_invert_ltup : forall x y l w, R (ltup x y l) w ->
                                         (exists x', w = ltup x' y l /\ R x x') \/
                                         (exists y', w = ltup x y' l /\ R y y') \/
                                         (exists l1 l2 z z', l = l1 ++ z :: l2 /\
                                                             w = ltup x y (l1 ++ z' :: l2) /\
                                                             R z z').

Lemma lem_s_result_1 :
  forall ns x x' l1 l2,
    is_nonempty ns ->
    R x x' ->
    R (build_s_result ns x l1 l2) (build_s_result ns x' l1 l2).
Proof.
  intros.
  ydestruct ns.
  ycrush.
  unfold build_s_result; simpl.
  ydestruct (split_in_groups ns (skipn n l2)).
  ycrush.
  ycrush.
Qed.

Inductive R_in_list : list lterm -> list lterm -> Prop :=
| cil_base : forall x y l, R x y -> R_in_list (x :: l) (y :: l)
| cil_step : forall x l l', R_in_list l l' -> R_in_list (x :: l) (x :: l').

Lemma lem_list_cil :
  forall l1 z z' l2, R z z' -> R_in_list (l1 ++ z :: l2) (l1 ++ z' :: l2).
Proof.
  induction l1; pose cil_base; pose cil_step; ycrush.
Qed.

Lemma lem_cil_list :
  forall l l', R_in_list l l' ->
               exists l1 z z' l2, l = l1 ++ z :: l2 /\ l' = l1 ++ z' :: l2 /\
                                  R z z'.
Proof.
  induction l, l'; try yelles 1.
  intro H.
  yinversion H.
  exists nil.
  exists a.
  exists l0.
  exists l'.
  ycrush.
  yforwarding.
  exists (l0 :: x).
  exists x0.
  exists x1.
  exists x2.
  ycrush.
Qed.

Ltac pose_cil := pose cil_base; pose cil_step; pose lem_list_cil.

Lemma lem_ltup_to_cil :
  forall x x', is_ltup x = true -> R x x' -> R_in_list (tuple_of_lterm x) (tuple_of_lterm x').
Proof.
  destruct x; destruct x'; try (pose_cil; yforwarding; yelles 2).
  simpl; intros; yforwarding; yintuition; pose_cil; ycrush.
Qed.

Lemma lem_cil_to_ltup :
  forall l l', R_in_list l l' -> R (lterm_of_tuple l) (lterm_of_tuple l').
Proof.
  induction l, l'; try yelles 1.
  intro H.
  yinversion H.
  ycrush.
  destruct l, l'; try yelles 1.
  yinversion H1.
  ycrush.
  pose lem_cil_list; ycrush.
Qed.

Lemma lem_R_preserves_ltup :
  forall x y, R x y -> is_ltup x = true -> is_ltup y = true.
Proof.
  destruct x, y; yelles 1.
Qed.

Definition R_glue_iterms_l x := forall x' y, R x x' -> R (glue_iterms x y) (glue_iterms x' y).
Definition R_glue_iterms_r y := forall x y', R y y' -> R (glue_iterms x y) (glue_iterms x y').

Lemma lem_build_ys_cil :
  forall l1 l1' l2, (forall x, In x l1 -> R_glue_iterms_l x) ->
                    length l1 = length l2 -> R_in_list l1 l1' ->
                    R_in_list (build_ys l1 l2) (build_ys l1' l2).
Proof.
  induction l1, l1'.
  pose_cil; ycrush.
  pose_cil; ycrush.
  pose_cil; ycrush.
  intros.
  yinversion H1.
  simpl in H.
  ydestruct l2.
  ycrush.
  assert (R (a @l lterm_of_tuple l0) (l @l lterm_of_tuple l0)) by ycrush.
  pose_cil; ycrush.
  ydestruct l2.
  ycrush.
  pose_cil; ycrush.
Qed.

Lemma lem_s_result_2 :
  forall ns x y y' l,
    (forall z, In z (tuple_of_lterm y) -> R_glue_iterms_l z) ->
    is_ltup y = true ->
    lst_sum ns < length l ->
    length (tuple_of_lterm y) = length ns ->
    R y y' ->
    R (build_s_result ns x (tuple_of_lterm y) l)
      (build_s_result ns x (tuple_of_lterm y') l).
Proof.
  intros.
  ydestruct ns.
  ycrush.
  unfold build_s_result; simpl.
  ydestruct (split_in_groups ns (skipn n l)).
  ycrush.
  assert (R_in_list (build_ys (tuple_of_lterm y) (l0 :: l1))
                                  (build_ys (tuple_of_lterm y') (l0 :: l1))).
  assert (length (split_in_groups ns (skipn n l)) = length ns + 1).
  pose (lem_skipn_length n l); simpl in *; apply lem_split_length; omega.
  assert (length (tuple_of_lterm y) = length (l0 :: l1)).
  rewrite <- Heql0; simpl in *; omega.
  pose lem_build_ys_cil; pose lem_ltup_to_cil; ycrush.
  pose lem_cil_to_ltup; ycrush.
Qed.

Inductive R_in_list2 : list (list lterm) -> list (list lterm) -> Prop :=
| cil2_base : forall x y l, R_in_list x y -> R_in_list2 (x :: l) (y :: l)
| cil2_step : forall x l l', R_in_list2 l l' -> R_in_list2 (x :: l) (x :: l').

Ltac pose_cil2 := pose cil2_base; pose cil2_step.

Lemma lem_split_in_list2 : forall ns l l', R_in_list l l' ->
                                           R_in_list2 (split_in_groups ns l)
                                                      (split_in_groups ns l').
Proof.
  induction ns.
  pose_cil2; ycrush.
  simpl.
  induction a.
  pose_cil2; ycrush.
  destruct l, l'; try yelles 1.
  simpl; intro H; yinversion H; pose_cil; pose_cil2; ycrush.
Qed.

Lemma lem_R_in_list_in :
  forall l l', R_in_list l l' ->
               forall x, In x l -> In x l' \/
                                   exists y, In y l' /\ R x y.
Proof.
  intros l l' H; induction H; ycrush.
Qed.

Lemma lem_build_ys_cil2 :
  forall l1 l2 l2', (forall x, In x l2 -> forall y, In y x -> R_glue_iterms_r y) ->
    length l1 = length l2 -> R_in_list2 l2 l2' ->
    R_in_list (build_ys l1 l2) (build_ys l1 l2').
Proof.
  induction l1.
  ycrush.
  destruct l2, l2'; try yelles 1.
  simpl.
  intros H H1 H2.
  yinversion H2.
  assert (R (glue_iterms a (lterm_of_tuple l)) (glue_iterms a (lterm_of_tuple l0))).
  yinversion H3.
  ydestruct l2.
  assert (R_glue_iterms_r x).
  apply H with (x0 := x :: nil); ycrush.
  ycrush.
  ydestruct a; ycrush.
  assert (R (lterm_of_tuple (x :: l2)) (lterm_of_tuple (x :: l'))).
  pose lem_cil_to_ltup; pose_cil; ycrush.
  ydestruct l2; yelles 1.
  pose_cil; ycrush.
  pose_cil; ycrush.
Qed.

Lemma lem_s_result_3 :
  forall ns x l y y',
    (forall z, In z (tuple_of_lterm y) -> R_glue_iterms_r z) ->
    is_ltup y = true ->
    lst_sum ns < length (tuple_of_lterm y) ->
    length l = length ns ->
    R y y' ->
    R (build_s_result ns x l (tuple_of_lterm y))
      (build_s_result ns x l (tuple_of_lterm y')).
Proof.
  intros.
  unfold build_s_result; simpl.
  ydestruct ns.
  ycrush.
  generalize (lem_split_result n ns (tuple_of_lterm y)).
  generalize (lem_split_result n ns (tuple_of_lterm y')).
  yintros.
  rewrite H4, H5.
  assert (R_in_list2 (x3 :: x4 :: x5) (x0 :: x1 :: x2)).
  rewrite <- H4, <- H5.
  apply lem_split_in_list2.
  pose lem_ltup_to_cil; pose lem_R_preserves_ltup; ycrush.
  assert (length l = length (x4 :: x5)).
  assert (length (split_in_groups (n :: ns) (tuple_of_lterm y)) = length (n :: ns) + 1).
  eapply lem_split_length; ycrush.
  rewrite H5 in H7; simpl in *.
  omega.
  yinversion H6.
  pose lem_cil_to_ltup; ycrush.
  assert (forall x, In x (x0 :: x4 :: x5) -> forall y, In y x -> R_glue_iterms_r y).
  rewrite <- H5; pose lem_split_preserves_elements; ycrush.
  simpl in *; pose lem_build_ys_cil2; pose lem_cil_to_ltup; ycrush.
Qed.

Lemma lem_all_pairs_erased_eqv_rev :
  forall y y', (forall x x', R x x' -> ErasedEqv x x') -> is_ltup y = true -> R y y' ->
    All_pairs (tuple_of_lterm y') ErasedEqv -> All_pairs (tuple_of_lterm y) ErasedEqv.
Proof.
  unfold All_pairs; intros.
  assert (In y0 (tuple_of_lterm y') \/
       (exists z : lterm, In z (tuple_of_lterm y') /\ R y0 z)).
  pose lem_ltup_to_cil; pose lem_R_in_list_in; ycrush.
  assert (In x (tuple_of_lterm y') \/
       (exists z : lterm, In z (tuple_of_lterm y') /\ R x z)).
  pose lem_ltup_to_cil; pose lem_R_in_list_in; ycrush.
  clear R_cong_app_l R_cong_app_r R_cong_ltup_0 R_cong_ltup_1 R_cong_ltup_2 R_invert_ltup.
  yintuition; pose_erased_eqv; ycrush.
Qed.

Lemma lem_all_pairs_erased_eqv :
  forall y y', (forall x x', R x x' -> ErasedEqv x x') -> is_ltup y = true -> R y y' ->
    All_pairs (tuple_of_lterm y) ErasedEqv -> All_pairs (tuple_of_lterm y') ErasedEqv.
Proof.
  unfold All_pairs; intros.
  ydestruct y; yisolve.
  generalize (R_invert_ltup y1 y2 l y' H1); yintro.
  yintuition; simp_hyps; subst; simpl in *.
  assert (ErasedEqv y1 x0) by auto.
  clear R_cong_app_l R_cong_app_r R_cong_ltup_0 R_cong_ltup_1 R_cong_ltup_2 R_invert_ltup H H1 H5.
  yintuition; solve [ pose lem_erased_eqv_trans; pose lem_erased_eqv_sym; pose lem_erased_eqv_refl;
                      auto; eauto 7 ].
  assert (ErasedEqv y2 x0) by auto.
  clear R_cong_app_l R_cong_app_r R_cong_ltup_0 R_cong_ltup_1 R_cong_ltup_2 R_invert_ltup H H1 H5.
  yintuition; solve [ pose lem_erased_eqv_trans; pose lem_erased_eqv_sym; pose lem_erased_eqv_refl;
                      auto; eauto 8 ].
  assert (ErasedEqv x2 x3) by auto.
  clear R_cong_app_l R_cong_app_r R_cong_ltup_0 R_cong_ltup_1 R_cong_ltup_2 R_invert_ltup H H1 H6.
  assert (forall x, x = x2 \/ In x x0 \/ In x x1 -> In x (x0 ++ x2 :: x1)).
  auto using lem_in_app_2.
  assert (forall x, In x (x0 ++ x3 :: x1) -> x = x3 \/ In x x0 \/ In x x1).
  auto using lem_in_app_1.
  yintuition; try solve [ pose lem_erased_eqv_trans; pose lem_erased_eqv_sym; pose lem_erased_eqv_refl;
                          auto ].
  
  assert (x = x3 \/ In x x0 \/ In x x1) by auto.
  yintuition.
  assert (ErasedEqv x2 y0).
  apply H2; intuition.
  pose_erased_eqv; eauto.
  apply H2; intuition.
  apply H2; intuition.

  assert (y0 = x3 \/ In y0 x0 \/ In y0 x1) by auto.
  yintuition.
  assert (ErasedEqv x x2).
  apply H2; intuition.
  pose_erased_eqv; eauto.
  apply H2; intuition.
  apply H2; intuition.

  assert (x = x3 \/ In x x0 \/ In x x1) by auto.
  yintuition.
  assert (ErasedEqv y0 x2).
  apply H2; intuition.
  pose_erased_eqv; eauto.
  apply H2; intuition.
  apply H2; intuition.

  assert (y0 = x3 \/ In y0 x0 \/ In y0 x1) by auto.
  yintuition.
  assert (ErasedEqv x x2).
  apply H2; intuition.
  pose_erased_eqv; eauto.
  apply H2; intuition.
  apply H2; intuition.

  assert (y0 = x3 \/ In y0 x0 \/ In y0 x1) by auto.
  assert (x = x3 \/ In x x0 \/ In x x1) by auto.
  yintuition.
  assert (ErasedEqv x x2).
  apply H2; intuition.
  pose_erased_eqv; eauto.
  assert (ErasedEqv x x2).
  apply H2; intuition.
  pose_erased_eqv; eauto.
  assert (ErasedEqv y0 x2).
  apply H2; intuition.
  pose_erased_eqv; eauto.
  assert (ErasedEqv y0 x2).
  apply H2; intuition.
  pose_erased_eqv; eauto.
  apply H2; intuition.
  apply H2; intuition.
  apply H2; intuition.
  apply H2; intuition.
Qed.

Lemma lem_first_skip : forall n l l', R_in_list l l' ->
                                      (R_in_list (firstn n l) (firstn n l') /\
                                       skipn n l = skipn n l') \/
                                      (R_in_list (skipn n l) (skipn n l') /\
                                       firstn n l = firstn n l').
Proof.
  induction n.
  ycrush.
  destruct l, l'; yisolve.
  intro H; yinversion H; pose_cil; ycrush.
Qed.

Lemma lem_glue_list : forall l, is_nonempty l ->
                                (forall u, In u l -> R_glue_iterms_r u) ->
                                R_glue_iterms_r (lterm_of_tuple l).
Proof.
  destruct l.
  ycrush.
  unfold R_glue_iterms_r.
  ydestruct l0.
  ycrush.
  simpl; yintros; ydestruct y'; ycrush.
Qed.

Lemma lem_s2_result :
  forall n x y z z',
    (forall u, In u (tuple_of_lterm z) -> R_glue_iterms_r u) ->
    is_ltup z = true ->
    R z z' ->
    R (x @l lterm_of_tuple (firstn n (tuple_of_lterm z)) @l
         glue_iterms y (lterm_of_tuple (skipn n (tuple_of_lterm z))))
      (x @l lterm_of_tuple (firstn n (tuple_of_lterm z')) @l
         glue_iterms y (lterm_of_tuple (skipn n (tuple_of_lterm z')))).
Proof.
  intros.
  assert (is_ltup z' = true).
  pose lem_R_preserves_ltup; yelles 1.
  destruct z, z'; yisolve.
  simpl in *.
  assert (HH: R_in_list (z1 :: z2 :: l) (z'1 :: z'2 :: l0)).
  apply (lem_ltup_to_cil (ltup z1 z2 l) (ltup z'1 z'2 l0)); ycrush.
  generalize (lem_first_skip n (z1 :: z2 :: l) (z'1 :: z'2 :: l0) HH).
  intro HH1; destruct HH1; simp_hyps.
  pose lem_cil_to_ltup; ycrush.
  assert (R_glue_iterms_r (lterm_of_tuple (skipn n (z1 :: z2 :: l)))).
  assert (forall u, In u (skipn n (z1 :: z2 :: l)) -> In u (z1 :: z2 :: l)).
  pose (lem_skipn_preserves_elements n (z1 :: z2 :: l)); ycrush.
  assert (is_nonempty (skipn n (z1 :: z2 :: l))) by ycrush.
  simpl in *; apply lem_glue_list; ycrush.
  pose lem_cil_to_ltup; ycrush.
Qed.

End SVars.
