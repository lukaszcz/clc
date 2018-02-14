Require Import general.
Require Import basic_defs.
Require Import lterms.
Require Import subterms.
Require Import standard.

Lemma lem_subterm_build_s_result_expand_1 :
  forall ns x l1 l2 t, is_nonempty ns -> Subterm t x -> Subterm t (build_s_result ns x l1 l2).
Proof.
  unfold build_s_result.
  destruct ns; yisolve.
  pose lem_split_result; pose_subterm; ycrush.
Qed.

Lemma lem_subterm_build_ys_expand :
  forall l1 l2 u t, length l1 = length l2 -> Subterm t u -> In u l1 ->
                    exists x, Subterm t x /\ In x (build_ys l1 l2).
Proof.
  induction l1.
  ycrush.
  simpl; intros.
  ydestruct l2; yisolve; simpl in *.
  yintuition.
  assert (is_iterm u = true \/ is_iterm u = false) by ycrush.
  yintuition.
  ydestruct u; yisolve.
  assert (is_iterm (lterm_of_tuple l) = true \/ is_iterm (lterm_of_tuple l) = false).
  ydestruct (lterm_of_tuple l); ycrush.
  yintuition.
  ydestruct (lterm_of_tuple l); yisolve.
  exists (itm (i @i i0)); pose_subterm; pose_subterm_i; ycrush.
  exists (itm i @l lterm_of_tuple l); pose_subterm; ycrush.
  exists (u @l lterm_of_tuple l); unfold glue_iterms; pose_subterm; ycrush.
  assert (length l1 = length l2) by omega.
  ycrush.
Qed.

Lemma lem_subterm_build_s_result_expand_2 :
  forall ns x l1 l2 u t, is_nonempty ns -> length l1 = length ns -> lst_sum ns < length l2 ->
                         Subterm t u -> In u l1 ->
                         Subterm t (build_s_result ns x l1 l2).
Proof.
  unfold build_s_result.
  destruct ns; yisolve.
  intros.
  assert (length (split_in_groups (n :: ns) l2) = length l1 + 1).
  assert (length (split_in_groups (n :: ns) l2) = length (n :: ns) + 1).
  pose lem_split_length; ycrush.
  simpl in *; omega.
  assert (exists a b c, split_in_groups (n :: ns) l2 = a :: b :: c).
  pose lem_split_result; ycrush.
  simp_hyps.
  rewrite H5 in *; clear H5.
  assert (length (x1 :: x2) = length l1).
  simpl in *; omega.
  assert (exists z, Subterm t z /\ In z (build_ys l1 (x1 :: x2))).
  pose lem_subterm_build_ys_expand; ycrush.
  simp_hyps.
  assert (Subterm t (lterm_of_tuple (build_ys l1 (x1 :: x2)))).
  pose lem_subterm_lterm_of_tuple; ycrush.
  pose lem_subterm_trans; pose_subterm; ycrush.
Qed.

Lemma lem_build_ys_no_nested_tuple :
  forall l1 l2 u, length l1 = length l2 -> In u l1 ->
                  (forall x, In x (build_ys l1 l2) -> Standard x) ->
                  is_ltup u = false.
Proof.
  induction l1; simpl.
  ycrush.
  destruct l2; simpl.
  ycrush.
  intros.
  yintuition.
  assert (Std (glue_iterms u (lterm_of_tuple l))).
  pose lem_standard_implies_std; ycrush.
  ydestruct u; yisolve; simpl in *; simp_hyps; iauto 2.
  assert (length l1 = length l2) by omega.
  ycrush.
Qed.

Lemma lem_build_s_no_nested_tuple :
  forall ns x l1 l2 u, is_nonempty ns -> length l1 = length ns -> lst_sum ns < length l2 ->
                       In u l1 -> Standard (build_s_result ns x l1 l2) ->
                       is_ltup u = false.
Proof.
  unfold build_s_result.
  destruct ns; yisolve.
  intros.
  assert (length (split_in_groups (n :: ns) l2) = length l1 + 1).
  assert (length (split_in_groups (n :: ns) l2) = length (n :: ns) + 1).
  pose lem_split_length; ycrush.
  simpl in *; omega.
  assert (exists a b c, split_in_groups (n :: ns) l2 = a :: b :: c).
  pose lem_split_result; ycrush.
  simp_hyps.
  rewrite H5 in *; clear H5.
  assert (length (x1 :: x2) = length l1).
  simpl in *; omega.
  assert (forall x, In x (build_ys l1 (x1 :: x2)) -> Standard x).
  pose lem_standard_lterm_of_tuple; pose lem_subterm_standard; pose_subterm; ycrush.
  pose lem_build_ys_no_nested_tuple; ycrush.
Qed.

Lemma lem_subterm_build_ys_expand_2 :
  forall l1 l2 u v t, length l1 = length l2 -> Subterm t u -> In u v -> In v l2 ->
                    exists x, Subterm t x /\ In x (build_ys l1 l2).
Proof.
  induction l1.
  ycrush.
  destruct l2.
  ycrush.
  simpl; intros.
  destruct H2.
  subst; simpl.
  assert (Subterm t (lterm_of_tuple v)).
  eapply lem_subterm_lterm_of_tuple; ycrush.
  assert (is_iterm (lterm_of_tuple v) = true \/ is_iterm (lterm_of_tuple v) = false).
  ydestruct (lterm_of_tuple v); ycrush.
  yintuition.
  assert (is_iterm a = true \/ is_iterm a = false) by ycrush.
  yintuition.
  ydestruct a; yisolve.
  ydestruct (lterm_of_tuple v); yisolve.
  simpl.
  exists (itm (i @i i0)); pose_subterm; pose_subterm_i; ycrush.
  unfold glue_iterms; pose_subterm; pose_subterm_i; ycrush.
  unfold glue_iterms; pose_subterm; pose_subterm_i; ycrush.
  assert (length l1 = length l2) by omega.
  ycrush.
Qed.

Lemma lem_subterm_build_s_result_expand_3 :
  forall ns x l1 l2 u t, is_nonempty ns -> (forall n, In n ns -> n > 0) ->
                         length l1 = length ns -> lst_sum ns < length l2 ->
                         Subterm t u -> In u l2 ->
                         Subterm t (build_s_result ns x l1 l2).
Proof.
  unfold build_s_result.
  destruct ns; yisolve.
  intros.
  assert (length (split_in_groups (n :: ns) l2) = length l1 + 1).
  assert (length (split_in_groups (n :: ns) l2) = length (n :: ns) + 1).
  pose lem_split_length; ycrush.
  simpl in *; omega.
  assert (exists a, In u a /\ In a (split_in_groups (n :: ns) l2)).
  apply lem_split_in_groups_preserves_elements_2; ycrush.
  simp_hyps.
  assert (exists a b c, split_in_groups (n :: ns) l2 = a :: b :: c).
  pose lem_split_result; ycrush.
  simp_hyps.
  rewrite H8 in *; clear H8.
  assert (length (x2 :: x3) = length l1).
  simpl in *; omega.
  simpl in H7.
  destruct H7.
  subst.
  assert (Subterm t (lterm_of_tuple x0)).
  pose lem_subterm_lterm_of_tuple; ycrush.
  pose lem_subterm_trans; pose_subterm; ycrush.
  assert (exists z, Subterm t z /\ In z (build_ys l1 (x2 :: x3))).
  pose lem_subterm_build_ys_expand_2; ycrush.
  simp_hyps.
  assert (Subterm t (lterm_of_tuple (build_ys l1 (x2 :: x3)))).
  pose lem_subterm_lterm_of_tuple; ycrush.
  pose lem_subterm_trans; pose_subterm; ycrush.
Qed.

Lemma lem_standard_expand_below_S_redex :
  forall r1 r2 t, RootContr_S r1 r2 -> Standard r2 -> Subterm t r1 -> t <> r1 ->
                  Standard t.
Proof.
  autounfold; intros.
  invert_rcontr_S.
  yintuition; simp_hyps; subst; simpl in *.

  (* S1 *)
  assert (is_nonempty x).
  ydestruct x; yisolve; simpl in *; generalize (lem_tuple_len_nonzero x1); omega.
  yinversion H1.
  ycrush.
  assert (Standard x0).
  eapply lem_subterm_standard; pose lem_subterm_build_s_result_expand_1; ycrush.  
  assert (Standard x1).
  assert (HH: forall u, In u (tuple_of_lterm x1) -> Standard u).
  intros;
    apply lem_subterm_standard with
    (x := build_s_result x x0 (tuple_of_lterm x1) (tuple_of_lterm x2));
    pose lem_subterm_build_s_result_expand_2; pose_subterm; ycrush.
  assert (HH1: forall u, In u (tuple_of_lterm x1) -> is_ltup u = false).
  pose lem_build_s_no_nested_tuple; ycrush.
  ydestruct x1; yisolve.
  unfold Standard in HH; simpl in *.
  assert (Std (ltup x1_1 x1_2 l)) by ycrush.
  clear -HH HH1 H11.
  unfold Standard; intros x H.
  yinversion H; pose_subterm; ycrush.
  assert (Standard (S1 x @l x0 @l x1)).
  apply lem_standard_basic_app_2; ycrush.
  eapply lem_subterm_standard; ycrush.
  assert (Standard x2).
  assert (HH: forall u, In u (tuple_of_lterm x2) -> Standard u).
  intros;
    apply lem_subterm_standard with
    (x := build_s_result x x0 (tuple_of_lterm x1) (tuple_of_lterm x2));
    pose lem_subterm_build_s_result_expand_3; pose_subterm; ycrush.
  ydestruct x2; yisolve.
  unfold Standard in HH; simpl in *.
  assert (HH1: Std (ltup x2_1 x2_2 l)) by ycrush.
  clear -HH HH1 H6.
  unfold Standard; intros x H.
  yinversion H; pose_subterm; ycrush.
  eapply lem_subterm_standard; ycrush.

  (* S2 *)
  yinversion H1.
  ycrush.
  assert (Standard x0).
  unfold Standard in *; pose_subterm; ycrush.
  assert (Standard x1).
  clear -H0.
  assert (Subterm x1 (glue_iterms x1 (lterm_of_tuple (skipn x (tuple_of_lterm x2))))).
  unfold glue_iterms in *; pose_subterm; pose_subterm_i; ycrush.
  unfold Standard in *; pose lem_subterm_trans; pose_subterm; ycrush.
  assert (Standard (S2 x @l x0 @l x1)).
  apply lem_standard_basic_app_2; ycrush.
  eapply lem_subterm_standard; ycrush.
  assert (Standard x2).
  assert (HH1: forall u, In u (tuple_of_lterm x2) -> In u (firstn x (tuple_of_lterm x2)) \/
                                                In u (skipn x (tuple_of_lterm x2))).
  assert (HH0: firstn x (tuple_of_lterm x2) ++ skipn x (tuple_of_lterm x2) = tuple_of_lterm x2).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Lists.List.firstn_skipn)
		    Reconstr.Empty.
  Reconstr.hsimple (@HH0)
		   (@Coq.Lists.List.in_app_or)
		   Reconstr.Empty.
  assert (forall u, In u (tuple_of_lterm x2) -> Standard u).
  intros; yforwarding.
  destruct H1.
  assert (Subterm u (lterm_of_tuple (firstn x (tuple_of_lterm x2)))).
  pose lem_subterm_lterm_of_tuple; pose_subterm; ycrush.
  unfold Standard in *; pose lem_subterm_trans; pose_subterm; ycrush.
  assert (Subterm u (lterm_of_tuple (skipn x (tuple_of_lterm x2)))).
  pose lem_subterm_lterm_of_tuple; pose_subterm; ycrush.
  assert (Subterm (lterm_of_tuple (skipn x (tuple_of_lterm x2)))
                  (glue_iterms x1 (lterm_of_tuple (skipn x (tuple_of_lterm x2))))).
  unfold glue_iterms in *; pose_subterm; pose_subterm_i; ycrush.
  unfold Standard in *; pose lem_subterm_trans; pose_subterm; ycrush.
  ydestruct x2; yisolve; simpl in *.
  unfold Standard; simpl; intros.
  assert (Std (ltup x2_1 x2_2 l)) by ycrush.
  yinversion H1; yisolve; unfold Standard in *; pose lem_subterm_trans; pose_subterm; ycrush.
  pose lem_subterm_standard; ycrush.
Qed.
