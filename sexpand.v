Require Import general.
Require Import list_facts.
Require Import iterms.
Require Import lterms.
Require Import erasure.
Require Import subterms.
Require Import standard.

Fixpoint split_y_z_list l :=
  match l with
  | x @l y :: t => (x, tuple_of_lterm y) :: split_y_z_list t
  | itm (x @i y) :: t => (itm x, (itm y :: nil)) :: split_y_z_list t
  | _ => nil
  end.

Fixpoint get_ns (l : list (lterm * list lterm)) :=
  match l with
  | nil => nil
  | _ :: nil => nil
  | (_, h) :: t => length h :: get_ns t
  end.

Fixpoint mk_zs (l : list (lterm * list lterm)) :=
  match l with
  | nil => nil
  | (_, h) :: t => h ++ mk_zs t
  end.

Definition build_s_redex t1 t2 t3 :=
  let l3 := split_y_z_list (tuple_of_lterm t3) in
  let l2 := tuple_of_lterm t2 in
  let ys := map fst l3 in
  let ns := length l2 :: get_ns l3 in
  let zs := mk_zs ((itm C, l2) :: l3) in
  match length (tuple_of_lterm t3) with
  | 1 => S2 (length l2) @l t1 @l (lterm_of_tuple ys) @l (lterm_of_tuple zs)
  | S (S _) => S1 ns @l t1 @l (lterm_of_tuple ys) @l (lterm_of_tuple zs)
  | 0 => itm C (* impossible *)
  end.

Lemma lem_split_y_z_preserves_length :
  forall l q1 q2, (forall x, In x l -> is_ltup x = false /\ Erasure x (q1 @i q2)) ->
                  length (split_y_z_list l) = length l.
Proof.
  induction l.
  ycrush.
  intros q1 q2 H.
  assert (is_ltup a = false) by ycrush.
  assert (HH: Erasure a (q1 @i q2)) by ycrush.
  yinversion HH; ycrush.
Qed.

Lemma lem_mk_zs_split_y_z_len :
  forall l q1 q2, (forall x, In x l -> is_ltup x = false /\ Erasure x (q1 @i q2)) ->
                  length (mk_zs (split_y_z_list l)) >= length l.
Proof.
  induction l.
  ycrush.
  intros q1 q2 H.
  assert (is_ltup a = false) by ycrush.
  assert (HH: Erasure a (q1 @i q2)) by ycrush.
  yinversion HH; simpl in *.
  assert (length (mk_zs (split_y_z_list l)) >= length l) by ycrush.
  omega.
  assert (H1: length (tuple_of_lterm y) > 0).
  Reconstr.htrivial Reconstr.Empty
                    (lem_tuple_len_nonzero)
                    Reconstr.Empty.
  assert (H2: length (mk_zs (split_y_z_list l)) >= length l) by ycrush.
  clear -H1 H2.
  generalize (app_length (tuple_of_lterm y) (mk_zs (split_y_z_list l))); omega.
  ycrush.
Qed.

Lemma lem_get_ns_length : forall l, length l > 0 -> length (get_ns l) = length l - 1.
Proof.
  induction l; yisolve.
  intros.
  simpl in *.
  ydestruct a.
  ydestruct l.
  ycrush.
  assert (length (length l1 :: get_ns (p :: l)) = S (length (get_ns (p :: l)))).
  ycrush.
  assert (length (p :: l) > 0).
  simpl; omega.
  yforwarding; omega.
Qed.

Lemma lem_split_y_z_snd_len :
  forall l q1 q2, (forall x, In x l -> is_ltup x = false /\ Erasure x (q1 @i q2)) ->
                  forall x, In x (split_y_z_list l) -> length (snd x) > 0.
Proof.
  induction l.
  ycrush.
  intros q1 q2 H.
  assert (is_ltup a = false) by ycrush.
  assert (HH: Erasure a (q1 @i q2)) by ycrush.
  yinversion HH; simpl in *.
  ycrush.
  pose lem_tuple_len_nonzero; ycrush.
  ycrush.
Qed.

Lemma lem_get_ns_lens : forall l, (forall x, In x l -> length (snd x) > 0) ->
                                  forall n, In n (get_ns l) -> n > 0.
Proof.
  induction l.
  ycrush.
  simpl.
  ydestruct a.
  intros.
  assert (HH: match l with
              | nil => nil
              | _ :: _ => length l1 :: get_ns l
              end = length l1 :: get_ns l).
  ydestruct l; ycrush.
  rewrite HH in *; clear HH.
  yintuition.
  assert (HH: l1 = snd (l0, l1)) by ycrush.
  rewrite HH; clear HH.
  ycrush.
Qed.

Lemma lem_get_ns_sum : forall l, (forall x, In x l -> length (snd x) > 0) ->
                                 length l > 0 -> lst_sum (get_ns l) < length (mk_zs l).
Proof.
  induction l.
  ycrush.
  ydestruct l.
  ydestruct a.
  simpl; intro H.
  assert (HH: l0 ++ nil = l0).
  Reconstr.htrivial Reconstr.Empty
                    (@Coq.Lists.List.app_nil_r)
                    Reconstr.Empty.
  rewrite HH; clear HH.
  assert (HH: l0 = snd (l, l0)) by ycrush.
  rewrite HH; clear HH.
  auto with arith.
  intro H.
  simpl in H.
  unfold get_ns in *; fold get_ns in *.
  unfold mk_zs in *; fold mk_zs in *.
  ydestruct a; ydestruct p.
  ydestruct l.
  simpl.
  rewrite app_length.
  rewrite app_length.
  assert (length (snd (l2, l3)) > 0) by ycrush.
  simpl in *; omega.
  intro.
  unfold lst_sum in *; fold lst_sum in *.
  rewrite app_length.
  assert (length l3 + lst_sum (get_ns (p :: l)) < length (l3 ++ mk_zs (p :: l))).
  apply IHl; ycrush.
  omega.
Qed.

Lemma lem_split_y_z_erasure :
  forall l q1 q2, (forall x, In x l -> is_ltup x = false /\ Erasure x (q1 @i q2)) ->
                  forall x, In x (split_y_z_list l) ->
                            Erasure (fst x) q1 /\ Erasure (lterm_of_tuple (snd x)) q2.
Proof.
  induction l.
  ycrush.
  intros.
  simpl in H.
  assert (is_ltup a = false) by ycrush.
  assert (HH: Erasure a (q1 @i q2)) by ycrush.
  yinversion HH; simpl in *.
  pose_erasure; ycrush.
  pose_erasure; pose lterm_tuple_cancel; ycrush.
  ycrush.
Qed.

Lemma lem_split_y_z_no_nested_tuple :
  forall l, (forall x, In x l -> Standard x) ->
            forall x, In x (split_y_z_list l) ->
                      forall y, In y (snd x) -> is_ltup y = false.
Proof.
  induction l.
  ycrush.
  intros.
  simpl in H.
  ydestruct a; yisolve.
  ydestruct i; yisolve.
  ycrush.
  simpl in H0.
  assert (Standard a2).
  pose lem_subterm_standard; pose_subterm; ycrush.
  pose lem_standard_no_nested_tuple; ycrush.
Qed.

Lemma lem_mk_zs_preserves_elements :
  forall (P : lterm -> Prop) l, (forall x, In x l -> forall y, In y (snd x) -> P y) ->
              forall x, In x (mk_zs l) -> P x.
Proof.
  induction l; intros.
  ycrush.
  simpl in *.
  ydestruct a.
  assert (HH: In x l1 \/ In x (mk_zs l)).
  Reconstr.htrivial (@H0)
                    (@Coq.Lists.List.in_app_iff)
                    Reconstr.Empty.
  destruct HH; ycrush.
Qed.

Lemma lem_build_ys_rev :
  forall l q1 q2, (forall x, In x l -> is_ltup x = false /\ Erasure x (q1 @i q2) /\ Std x) ->
                  build_ys (map fst (split_y_z_list l))
                           (split_in_groups (get_ns (split_y_z_list l))
                                            (mk_zs (split_y_z_list l))) = l.
Proof.
  induction l; intros.
  ycrush.
  assert (is_ltup a = false) by ycrush.
  assert (Std a) by ycrush.
  assert (HH: Erasure a (q1 @i q2)) by ycrush.
  yinversion HH; simpl in *.

  ydestruct l.
  ycrush.
  assert (HH: match split_y_z_list (l :: l0) with
          | nil => nil
          | _ :: _ => 1 :: get_ns (split_y_z_list (l :: l0))
          end = 1 :: get_ns (split_y_z_list (l :: l0))).
  assert (is_ltup l = false) by ycrush.
  assert (HH: Erasure l (q1 @i q2)) by ycrush.
  yinversion HH; simpl in *; ycrush.
  rewrite HH; clear HH.
  unfold split_in_groups; fold split_in_groups.
  unfold firstn; fold firstn.
  unfold lterm_of_tuple; fold lterm_of_tuple.
  unfold skipn; fold skipn.
  rewrite IHl with (q1 := q1) (q2 := q2) by ycrush.
  ycrush.

  ydestruct l.
  simpl.
  assert (HH: tuple_of_lterm y ++ nil = tuple_of_lterm y) by auto with datatypes.
  rewrite HH; clear HH.
  rewrite lterm_tuple_cancel.
  rewrite lem_sterm_glue_iterms by ycrush.
  trivial.
  assert (Sterm (x @l y)) by ycrush.
  clear H1 H0.
  assert (HH: match split_y_z_list (l :: l0) with
          | nil => nil
          | _ :: _ => (length (tuple_of_lterm y)) :: get_ns (split_y_z_list (l :: l0))
          end = (length (tuple_of_lterm y)) :: get_ns (split_y_z_list (l :: l0))).
  assert (is_ltup l = false) by ycrush.
  assert (HH: Erasure l (q1 @i q2)) by ycrush.
  yinversion HH; simpl in *; ycrush.
  rewrite HH; clear HH.
  unfold split_in_groups; fold split_in_groups.
  rewrite lem_firstn_len.
  rewrite lem_skipn_len.
  rewrite lterm_tuple_cancel.
  rewrite lem_sterm_glue_iterms by ycrush.
  rewrite IHl with (q1 := q1) (q2 := q2) by ycrush.
  ycrush.

  ycrush.
Qed.

Lemma lem_s_expand :
  forall t1 t2 t3 x y z, Standard t2 -> Standard t3 -> Erasure t1 x -> Erasure t2 z ->
                         Erasure t3 (y @i z) ->
                         RootContr_S (build_s_redex t1 t2 t3) (t1 @l t2 @l t3).
Proof.
  intros.
  unfold build_s_redex; simpl.

  ydestruct (length (tuple_of_lterm t3)).
  ycrush.
  ydestruct n.

  (* S2 *)
  assert (is_ltup t3 = false).
  ydestruct t3; ycrush.
  assert (HH: tuple_of_lterm t3 = t3 :: nil) by ycrush.
  rewrite HH; clear HH.
  yinversion H3.

  assert (HH: mk_zs (split_y_z_list (itm (y @i z) :: nil)) = itm z :: nil) by ycrush.
  rewrite HH; clear HH.
  assert (HH: (map fst (split_y_z_list (itm (y @i z) :: nil))) = itm y :: nil) by ycrush.
  rewrite HH; clear HH.
  assert (length (tuple_of_lterm t2 ++ itm z :: nil) > 1).
  ydestruct t2; simpl; yisolve; omega.
  cbn.
  rewrite lem_tuple_lterm_cancel_2 by ycrush.
  rewrite (lem_firstn_len (tuple_of_lterm t2) (itm z :: nil)).
  rewrite (lem_skipn_len (tuple_of_lterm t2) (itm z :: nil)).
  rewrite lterm_tuple_cancel.
  assert (forall u, In u (tuple_of_lterm t2 ++ itm z :: nil) -> Erasure u z).
  assert (forall u, In u (tuple_of_lterm t2) -> Erasure u z).
  pose lem_erasure_tuple; ycrush.
  assert (forall u, In u (itm z :: nil) -> Erasure u z).
  pose_erasure; ycrush.
  apply lem_all_append; ycrush.
  assert (All_pairs (tuple_of_lterm t2 ++ itm z :: nil) ErasedEqv).
  pose lem_all_pairs_erasure; ycrush.
  assert (forall x0 : lterm, In x0 (tuple_of_lterm t2 ++ itm z :: nil) -> is_ltup x0 = false).
  intro x0; pose (lem_in_app_1 x0); pose lem_standard_no_nested_tuple; ycrush.
  pose lem_is_ltup_len; pose lem_len_app; pose lem_tuple_len_nonzero.
  ycrush.

  assert (HH: mk_zs (split_y_z_list (x0 @l y0 :: nil)) = tuple_of_lterm y0).
  simpl.
  Reconstr.htrivial Reconstr.Empty
                (@Coq.Lists.List.app_nil_r)
                Reconstr.Empty.
  rewrite HH; clear HH.
  assert (HH: (map fst (split_y_z_list (x0 @l y0 :: nil))) = x0 :: nil) by ycrush.
  rewrite HH; clear HH.
  simpl.
  assert (length (tuple_of_lterm t2 ++ tuple_of_lterm y0) > 1).
  ydestruct t2; simpl; yisolve; ydestruct y0; simpl; yisolve; omega.
  rewrite lem_tuple_lterm_cancel_2 by ycrush.
  rewrite (lem_firstn_len (tuple_of_lterm t2) (tuple_of_lterm y0)).
  rewrite (lem_skipn_len (tuple_of_lterm t2) (tuple_of_lterm y0)).
  rewrite lterm_tuple_cancel.
  rewrite lterm_tuple_cancel.
  assert (Sterm (x0 @l y0)).
  pose lem_standard_implies_std; ycrush.
  rewrite lem_sterm_glue_iterms by ycrush.
  assert (forall u, In u (tuple_of_lterm t2 ++ tuple_of_lterm y0) -> Erasure u z).
  assert (forall u, In u (tuple_of_lterm t2) -> Erasure u z).
  pose lem_erasure_tuple; ycrush.
  assert (forall u, In u (tuple_of_lterm y0) -> Erasure u z).
  pose lem_erasure_tuple; ycrush.
  apply lem_all_append; ycrush.
  assert (All_pairs (tuple_of_lterm t2 ++ tuple_of_lterm y0) ErasedEqv).
  pose lem_all_pairs_erasure; ycrush.
  assert (is_ltup x0 = false).
  assert (Sterm x0) by iauto 1.
  ydestruct x0; ycrush.
  assert (forall x1 : lterm, In x1 (tuple_of_lterm t2 ++ tuple_of_lterm y0) -> is_ltup x1 = false).
  assert (Standard y0).
  pose lem_subterm_standard; pose_subterm; ycrush.
  intros.
  assert (In x1 (tuple_of_lterm t2) \/ In x1 (tuple_of_lterm y0)).
  Reconstr.htrivial (@H12)
                    (@Coq.Lists.List.in_app_iff)
                    Reconstr.Empty.
  pose lem_standard_no_nested_tuple; ycrush.
  pose lem_is_ltup_len; pose lem_len_app; pose (lem_tuple_len_nonzero t2);
    pose (lem_tuple_len_nonzero y0).
  ycrush.

  ycrush.

  (* S1 *)
  assert (is_ltup t3 = true).
  ydestruct t3; ycrush.
  yinversion H3; yisolve.
  assert (HH: tuple_of_lterm (ltup x0 y0 l) = x0 :: y0 :: l) by ycrush.
  rewrite HH in *; clear HH.
  clear Heqn n H4.
  unfold RootContr_S.
  assert (Std (ltup x0 y0 l)).
  pose lem_standard_implies_std; ycrush.
  assert (forall u, In u (x0 :: y0 :: l) -> is_ltup u = false /\ Erasure u (y @i z)) by yintuition.
  assert (HStd: forall u, In u (x0 :: y0 :: l) -> Std u).
  unfold Standard in *; pose_subterm; ycrush.
  assert (length (split_y_z_list (x0 :: y0 :: l)) = length (x0 :: y0 :: l)).
  eapply lem_split_y_z_preserves_length; ycrush.
  assert (length (mk_zs (split_y_z_list (x0 :: y0 :: l))) >= length (x0 :: y0 :: l)).
  pose lem_mk_zs_split_y_z_len; ycrush.
  assert (HH: length (x0 :: y0 :: l) = length l + 2).
  simpl; omega.
  rewrite HH in *; clear HH.
  assert (length (map fst (split_y_z_list (x0 :: y0 :: l))) = length l + 2).
  pose map_length; ycrush.
  assert (length (tuple_of_lterm t2 ++ mk_zs (split_y_z_list (x0 :: y0 :: l))) >=
          length l + 2).
  generalize (app_length (tuple_of_lterm t2) (mk_zs (split_y_z_list (x0 :: y0 :: l)))); omega.
  rewrite lem_tuple_lterm_cancel_2 by omega.
  rewrite lem_tuple_lterm_cancel_2 by omega.
  intuition.

  assert (HH: n = length (tuple_of_lterm t2) \/ In n (get_ns (split_y_z_list (x0 :: y0 :: l)))).
  ycrush.
  destruct HH.
  pose lem_tuple_len_nonzero; ycrush.
  pose lem_split_y_z_snd_len; pose lem_get_ns_lens; ycrush.

  pose lem_tuple_len_nonzero; ycrush.

  clear -H11.
  assert (length (tuple_of_lterm t2 ++ mk_zs (split_y_z_list (x0 :: y0 :: l))) > 1) by omega.
  apply lem_is_ltup_len; pose lem_tuple_len_nonzero; ycrush.

  assert (forall u, In u (x0 :: y0 :: l) -> Standard u).
  clear -H0; pose lem_subterm_standard; pose_subterm; ycrush.
  assert (HH1: forall u, In u (mk_zs (split_y_z_list (x0 :: y0 :: l))) -> is_ltup u = false).
  apply lem_mk_zs_preserves_elements; pose lem_split_y_z_no_nested_tuple; ycrush.
  assert (HH2: forall u, In u (tuple_of_lterm t2) -> is_ltup u = false).
  pose lem_standard_no_nested_tuple; ycrush.
  Reconstr.hobvious (@HH1, @H12, @HH2)
                    (@Coq.Lists.List.in_app_iff)
                    Reconstr.Empty.
  (* auto with datatypes does not work here *)

  rewrite H10.
  assert (HH: length (length (tuple_of_lterm t2) :: get_ns (split_y_z_list (x0 :: y0 :: l))) =
              length (get_ns (split_y_z_list (x0 :: y0 :: l))) + 1).
  simpl; omega.
  rewrite HH; clear HH.
  rewrite lem_get_ns_length by omega.
  rewrite H8.
  omega.

  rewrite app_length.
  unfold lst_sum; fold lst_sum.
  assert (lst_sum (get_ns (split_y_z_list (x0 :: y0 :: l))) <
          length (mk_zs (split_y_z_list (x0 :: y0 :: l)))).
  assert (length (split_y_z_list (x0 :: y0 :: l)) > 0) by omega.
  pose lem_get_ns_sum; pose lem_split_y_z_snd_len; ycrush.
  omega.

  assert (forall u, In u (map fst (split_y_z_list (x0 :: y0 :: l))) -> Erasure u y).
  apply lem_map_preserves_elements.
  pose lem_split_y_z_erasure; simp_hyps; eauto.
  pose lem_all_pairs_erasure; ycrush.

  assert (forall u, In u (mk_zs (split_y_z_list (x0 :: y0 :: l))) -> Erasure u z).
  apply lem_mk_zs_preserves_elements.
  intros x1 HH.
  apply lem_erasure_lterm_of_tuple_inv.
  pose lem_split_y_z_erasure; simp_hyps; eauto.
  assert (forall u, In u (tuple_of_lterm t2) -> Erasure u z).
  clear -H2.
  yinversion H2; pose_erasure; ycrush.
  assert (forall u, In u (tuple_of_lterm t2 ++ mk_zs (split_y_z_list (x0 :: y0 :: l))) ->
                    Erasure u z).
  Reconstr.hobvious (@H12, @H13)
                    (@Coq.Lists.List.in_app_iff)
                    Reconstr.Empty.
  pose lem_all_pairs_erasure; ycrush.

  unfold build_s_result.
  ydestruct (split_in_groups (length (tuple_of_lterm t2) :: get_ns (split_y_z_list (x0 :: y0 :: l)))
                             (tuple_of_lterm t2 ++ mk_zs (split_y_z_list (x0 :: y0 :: l)))).
  pose lem_split_result; ycrush.
  ydestruct l1.
  pose lem_split_result; ycrush.
  assert (HH: l0 = tuple_of_lterm t2).
  pose lem_split_in_groups_skip; ycrush.
  rewrite HH; clear HH.
  rewrite lterm_tuple_cancel.
  assert (HH: l1 :: l2 = split_in_groups (get_ns (split_y_z_list (x0 :: y0 :: l)))
                                         (mk_zs (split_y_z_list (x0 :: y0 :: l)))).
  pose lem_split_in_groups_skip; ycrush.
  rewrite HH; clear HH.
  assert (HH: build_ys (map fst (split_y_z_list (x0 :: y0 :: l)))
                       (split_in_groups (get_ns (split_y_z_list (x0 :: y0 :: l)))
                                        (mk_zs (split_y_z_list (x0 :: y0 :: l)))) = (x0 :: y0 :: l)).
  apply lem_build_ys_rev with (q1 := y) (q2 := z); ycrush.
  rewrite HH; clear HH.
  ycrush.
Qed.

Lemma lem_s_expand_erasure :
  forall t1 t2 t3 x y z, Standard t3 -> Erasure t1 x -> Erasure t2 z -> Erasure t3 (y @i z) ->
                         Erasure (build_s_redex t1 t2 t3) (Si @i x @i y @i z).
Proof.
  intros.

  assert (forall u, In u (tuple_of_lterm t3) -> is_ltup u = false /\ Erasure u (y @i z)).
  yinversion H2.
  ycrush.
  pose_erasure; ycrush.
  simpl.
  assert (Std (ltup x0 y0 l)).
  unfold Standard in *; pose_subterm; ycrush.
  unfold Std in *; ycrush.

  assert (Erasure (lterm_of_tuple (map fst (split_y_z_list (tuple_of_lterm t3)))) y).
  assert (is_nonempty (map fst (split_y_z_list (tuple_of_lterm t3)))).
  assert (length (split_y_z_list (tuple_of_lterm t3)) = length (tuple_of_lterm t3)).
  eapply lem_split_y_z_preserves_length; ycrush.
  assert (length (map fst (split_y_z_list (tuple_of_lterm t3))) = length (tuple_of_lterm t3)).
  pose map_length; ycrush.
  assert (length (map fst (split_y_z_list (tuple_of_lterm t3))) > 0).
  assert (length (tuple_of_lterm t3) > 0).
  Reconstr.htrivial Reconstr.Empty
                    (lem_tuple_len_nonzero)
                    Reconstr.Empty.
  omega.
  ycrush.
  assert (forall u, In u (map fst (split_y_z_list (tuple_of_lterm t3))) -> Erasure u y).
  apply lem_map_preserves_elements.
  pose lem_split_y_z_erasure; simp_hyps; eauto.
  pose lem_erasure_lterm_of_tuple; pose lterm_tuple_cancel; yelles 1.

  assert (Erasure (lterm_of_tuple (tuple_of_lterm t2 ++ mk_zs (split_y_z_list (tuple_of_lterm t3)))) z).
  assert (forall u, In u (mk_zs (split_y_z_list (tuple_of_lterm t3))) -> Erasure u z).
  apply lem_mk_zs_preserves_elements.
  intros x1 HH.
  apply lem_erasure_lterm_of_tuple_inv.
  pose lem_split_y_z_erasure; simp_hyps; eauto.
  assert (forall u, In u (tuple_of_lterm t2) -> Erasure u z).
  clear -H1.
  yinversion H1; pose_erasure; ycrush.
  assert (forall u, In u (tuple_of_lterm t2 ++ mk_zs (split_y_z_list (tuple_of_lterm t3))) ->
                    Erasure u z).
  Reconstr.hobvious (@H5, @H6)
                    (@Coq.Lists.List.in_app_iff)
                    Reconstr.Empty.
  assert (is_nonempty (tuple_of_lterm t2 ++ mk_zs (split_y_z_list (tuple_of_lterm t3)))).
  assert (length (tuple_of_lterm t2 ++ mk_zs (split_y_z_list (tuple_of_lterm t3))) > 0).
  assert (length (tuple_of_lterm t2) > 0).
  pose lem_tuple_len_nonzero; ycrush.
  rewrite app_length; omega.
  ycrush.
  pose lem_erasure_lterm_of_tuple; yelles 1.

  unfold build_s_redex; simpl.
  ydestruct (length (tuple_of_lterm t3)).
  ycrush.
  ydestruct n.
  pose_erasure; yelles 3.
  pose_erasure; yelles 3.
Qed.
