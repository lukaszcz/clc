(* This file contains the formalisation of the properties of (s-)-reduction: lemmas 26 and 7 *)

Require Import general.
Require Import iterms.
Require Import lterms.
Require Import erase_facts.
Require Import sred.
Require Import erasure.
Require Import sn.

Lemma rcontr_clc_s_minus_inversion :
  forall t1 t2, RootContr_clc_s_minus t1 t2 ->
                (exists x y, t1 = C1 @l T1 @l x @l y /\ t2 = x) \/
                (exists x y, t1 = C1 @l F1 @l x @l y /\ t2 = y) \/
                (exists x y z, t1 = C2 @l z @l x @l y /\ t2 = x /\ ErasedEqv x y) \/
                (exists x, t1 = I1 @l x /\ t2 = x) \/
                (exists x y, t1 = K1 @l x @l y /\ t2 = x) \/
                (exists ns x ys zs, t1 = S1 ns @l x @l ys @l zs /\
                                    (forall n, In n ns -> n > 0) /\
                                    is_ltup ys = true /\ is_ltup zs = true /\
                                    let l1 := tuple_of_lterm ys in
                                    let l2 := tuple_of_lterm zs in
                                    (forall x, In x l2 -> is_ltup x = false) /\
                                    length l1 = length ns /\
                                    lst_sum ns < length l2 /\
                                    All_pairs l1 ErasedEqv /\
                                    All_pairs l2 ErasedEqv /\
                                    t2 = build_s_result ns x l1 l2) \/
                (exists n x y zs, t1 = S2 n @l x @l y @l zs /\
                                  is_ltup y = false /\ is_ltup zs = true /\
                                  let l := tuple_of_lterm zs in
                                  (forall x, In x l -> is_ltup x = false) /\
                                  n > 0 /\ n < length l /\
                                  All_pairs l ErasedEqv /\
                                  t2 = x @l (lterm_of_tuple (firstn n l)) @l
                                         (glue_iterms y (lterm_of_tuple (skipn n l)))).
Proof.
  intros; ydestruct t1; simpl in *; yisolve.
Qed.

Ltac invert_rcontr_clc_s_minus :=
  repeat match goal with
         | [ H : (RootContr_clc_s_minus ?x ?y) |- ?G ] =>
           generalize (rcontr_clc_s_minus_inversion x y H); yintro; clear H
         end.

Lemma lem_rcontr_s_minus_to_contr_s_minus :
  forall x y, RootContr_clc_s_minus x y -> Contr_clc_s_minus x y.
Proof.
  pose_s_minus; ycrush.
Qed.

Lemma lem_contr_s_minus_to_contr_s :
  forall t1 t2, Contr_clc_s_minus t1 t2 -> Contr_clc_s t1 t2.
Proof.
  intros.
  induction H.
  invert_rcontr_clc_s_minus.
  rename H0 into H.
  assert (RootContr_clc_s t1 t2).
  repeat (destruct H; ycrush).
  unfold Contr_clc_s; pose_ctx_l; ycrush.
  unfold Contr_clc_s; pose_ctx_l; ycrush.
  unfold Contr_clc_s; pose_ctx_l; ycrush.
Qed.

Lemma lem_red_s_minus_to_red_s :
  forall t1 t2, Red_clc_s_minus t1 t2 -> Red_clc_s t1 t2.
Proof.
  pose lem_contr_s_minus_to_contr_s.
  intros t1 t2 H; induction H; unfold Red_clc_s; pose_rt; ycrush.
Qed.

Lemma lem_contr_s_minus_to_red_s_minus :
  forall t1 t2, Contr_clc_s_minus t1 t2 -> Red_clc_s_minus t1 t2.
Proof.
  intros; unfold Red_clc_s_minus; pose_rt; ycrush.
Qed.

Lemma lem_red_s_minus_refl : forall x, Red_clc_s_minus x x.
Proof.
  unfold Red_clc_s_minus; pose_rt; ycrush.
Qed.

Lemma lem_red_s_minus_trans : forall x y z, Red_clc_s_minus x y -> Red_clc_s_minus y z ->
                                            Red_clc_s_minus x z.
Proof.
  unfold Red_clc_s_minus; pose_rt; ycrush.
Qed.

Definition sNFm x := not (exists y, Contr_clc_s_minus x y).

Lemma lem_red_s_minus_wn : forall x, exists y, Red_clc_s_minus x y /\ sNFm y.
Proof.
  intro.
  assert (Acc (fun x y : lterm => Contr_clc_s y x) x).
  pose lem_contr_clc_s_sn; unfold well_founded in *; eauto.
  induction H.
  assert ((exists y, Contr_clc_s_minus x y) \/ not (exists y, Contr_clc_s_minus x y)).
  apply classic.
  destruct H1.
  pose lem_contr_s_minus_to_contr_s; pose lem_contr_s_minus_to_red_s_minus;
    pose lem_red_s_minus_trans; ycrush.
  assert (sNFm x).
  unfold sNFm in *; ycrush.
  ycrush.
Qed.

Lemma lem_snfm_app : forall x y, sNFm (x @l y) -> sNFm x /\ sNFm y.
Proof.
  unfold sNFm; pose_s_minus; ycrush.
Qed.

Lemma lem_snfm_app_inv : forall x y, sNFm x -> sNFm y ->
                                     ~(exists z, RootContr_clc_s_minus (x @l y) z) ->
                                     sNFm (x @l y).
Proof.
  unfold sNFm, not; yintros; yinversion H2; ycrush.
Qed.

Lemma lem_snfm_not_s_redex : forall x y, sNFm x -> RootContr_clc_s x y -> False.
Proof.
  induction x; try solve [ unfold sNFm; yintuition ].
  ydestruct x1; try solve [ unfold sNFm; yintuition ].
  unfold sNFm; pose_s_minus; ycrush.
  ydestruct x1_1; try solve [ unfold sNFm; yintuition ].
  unfold sNFm; pose_s_minus; ycrush.
  ydestruct x1_1_1; try solve [ unfold sNFm; yintuition ].
  unfold sNFm; pose_s_minus; ycrush.
  intros.
  unfold sNFm in *.
  apply H.
  simpl in *; simp_hyps.
  clear -H2.
  exists x1_2; apply s_minus_base; ycrush.
  unfold sNFm; pose_s_minus; ycrush.
  unfold sNFm; pose_s_minus; ycrush.
Qed.

Inductive Contr_clc_s_in_tuple : lterm -> lterm -> Prop :=
| cituple_base : forall x y, is_ltup x = true -> Contr_clc_s x y -> Contr_clc_s_in_tuple x y
| cituple_app_l : forall x y x', Contr_clc_s_in_tuple x x' -> Contr_clc_s_in_tuple (x @l y) (x' @l y)
| cituple_app_r : forall x y y', Contr_clc_s_in_tuple y y' -> Contr_clc_s_in_tuple (x @l y) (x @l y').

Ltac pose_cituple := pose cituple_base; pose cituple_app_l; pose cituple_app_r.

Lemma lem_snfm_contr_s_in_tuple : forall x y, sNFm x -> Contr_clc_s x y -> Contr_clc_s_in_tuple x y.
Proof.
  intros.
  induction H0; fold Contr_clc_s in *.
  pose lem_snfm_not_s_redex; yelles 1.
  pose lem_snfm_app; pose_cituple; ycrush.
  pose lem_snfm_app; pose_cituple; ycrush.
  pose lem_contr_s_ltup_0; pose_cituple; ycrush.
  pose lem_contr_s_ltup_1; pose_cituple; ycrush.
  pose lem_contr_s_ltup_2; pose_cituple; ycrush.
Qed.

Lemma lem_contr_s_in_tuple_to_contr_s :
  forall x y, Contr_clc_s_in_tuple x y -> Contr_clc_s x y.
Proof.
  intros x y H; induction H; unfold Contr_clc_s; pose_ctx_l; ycrush.
Qed.

Lemma lem_all_pairs_expand :
  forall x2 y, All_pairs (tuple_of_lterm x2) ErasedEqv -> is_ltup y = true ->
               Contr_clc_s y x2 -> All_pairs (tuple_of_lterm y) ErasedEqv.
Proof.
  intros x2 y H5 H H8.
  ydestruct y; yintuition.
  yinversion H8; fold Contr_clc_s in *.
  yelles 1.
  simpl in *; unfold All_pairs in *.
  intros.
  assert (ErasedEqv y1 x') by auto using lem_contr_s_implies_erased_eqv.
  assert (In x' (x' :: y2 :: l)).
  Reconstr.hobvious Reconstr.Empty
		    (@Coq.Lists.List.not_in_cons)
		    Reconstr.Empty.
  assert (In y2 (x' :: y2 :: l)).
  Reconstr.hobvious Reconstr.Empty
		    (@Coq.Lists.List.not_in_cons)
		    Reconstr.Empty.
  assert (forall z, In z l -> In z (x' :: y2 :: l)).
  Reconstr.hobvious Reconstr.Empty
		    (@Coq.Lists.List.not_in_cons)
		    Reconstr.Empty.
  yinversion H.
  yinversion H0.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H7.
  yinversion H0.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H.
  ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H0.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H7.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  ycrush.

  simpl in *; unfold All_pairs in *.
  intros.
  assert (ErasedEqv y2 y') by auto using lem_contr_s_implies_erased_eqv.
  assert (In y' (y1 :: y' :: l)).
  Reconstr.hobvious Reconstr.Empty
		    (@Coq.Lists.List.not_in_cons)
		    Reconstr.Empty.
  assert (In y1 (y1 :: y' :: l)).
  Reconstr.hobvious Reconstr.Empty
		    (@Coq.Lists.List.not_in_cons)
		    Reconstr.Empty.
  assert (forall z, In z l -> In z (y1 :: y' :: l)).
  Reconstr.hobvious Reconstr.Empty
		    (@Coq.Lists.List.not_in_cons)
		    Reconstr.Empty.
  yinversion H.
  yinversion H0.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H7.
  yinversion H0.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H.
  ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H0.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H7.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  ycrush.

  simpl in *; unfold All_pairs in *.
  intros.
  assert (ErasedEqv z z') by auto using lem_contr_s_implies_erased_eqv.
  assert (In y1 (y1 :: y2 :: l0 ++ z' :: l')).
  Reconstr.hobvious Reconstr.Empty
		    (@Coq.Lists.List.not_in_cons)
		    Reconstr.Empty.
  assert (In y2 (y1 :: y2 :: l0 ++ z' :: l')).
  Reconstr.hobvious Reconstr.Empty
		    (@Coq.Lists.List.not_in_cons)
		    Reconstr.Empty.
  assert (forall z, In z l0 \/ In z l' -> In z (y1 :: y2 :: l0 ++ z' :: l')).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Lists.List.in_or_app, @Coq.Lists.List.Add_in, @Coq.Lists.List.not_in_cons, @Coq.Lists.List.in_cons)
		    (@Coq.Lists.List.In, @Coq.Init.Datatypes.app).
  assert (In z' (y1 :: y2 :: l0 ++ z' :: l')).
  assert (In z' (z' :: l')).
  ycrush.
  pose @Coq.Lists.List.in_cons; pose @Coq.Lists.List.in_or_app.
  ycrush.
  yinversion H.
  yinversion H0.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  assert (In y l0 \/ In y (z :: l')).
  Reconstr.htrivial (@H0)
		    (@Coq.Lists.List.NoDup_Add, @Coq.Lists.List.elements_in_partition, @Coq.Lists.List.in_app_or, @Coq.Lists.List.in_inv)
		    (@Coq.Lists.List.In).
  destruct H.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  destruct H; try subst.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H8.
  yinversion H0.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H.
  ycrush.
  assert (In y l0 \/ In y (z :: l')).
  Reconstr.htrivial (@H0)
		    (@Coq.Lists.List.NoDup_Add, @Coq.Lists.List.elements_in_partition, @Coq.Lists.List.in_app_or, @Coq.Lists.List.in_inv)
		    (@Coq.Lists.List.In).
  destruct H.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  destruct H; try subst.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H0.
  assert (In x l0 \/ In x (z :: l')).
  Reconstr.htrivial (@H)
		    (@Coq.Lists.List.NoDup_Add, @Coq.Lists.List.elements_in_partition, @Coq.Lists.List.in_app_or, @Coq.Lists.List.in_inv)
		    (@Coq.Lists.List.In).
  destruct H0.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  destruct H0; try subst.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H8.
  assert (In x l0 \/ In x (z :: l')).
  Reconstr.htrivial (@H)
		    (@Coq.Lists.List.NoDup_Add, @Coq.Lists.List.elements_in_partition, @Coq.Lists.List.in_app_or, @Coq.Lists.List.in_inv)
		    (@Coq.Lists.List.In).
  destruct H0.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  destruct H0; try subst.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  assert (In x l0 \/ In x (z :: l')).
  Reconstr.htrivial (@H)
		    (@Coq.Lists.List.NoDup_Add, @Coq.Lists.List.elements_in_partition, @Coq.Lists.List.in_app_or, @Coq.Lists.List.in_inv)
		    (@Coq.Lists.List.In).
  assert (In y l0 \/ In y (z :: l')).
  Reconstr.htrivial (@H0)
		    (@Coq.Lists.List.NoDup_Add, @Coq.Lists.List.elements_in_partition, @Coq.Lists.List.in_app_or, @Coq.Lists.List.in_inv)
		    (@Coq.Lists.List.In).
  destruct H8; destruct H9.
  clear -H6 H8 H9 H5.
  ycrush.
  destruct H9; try subst.
  assert (In x (y1 :: y2 :: l0 ++ z' :: l')) by ycrush.
  assert (In z' (y1 :: y2 :: l0 ++ z' :: l')) by ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  assert (In x (y1 :: y2 :: l0 ++ z' :: l')) by ycrush.
  assert (In y (y1 :: y2 :: l0 ++ z' :: l')) by ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  yinversion H8.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  assert (In x (y1 :: y2 :: l0 ++ z' :: l')) by ycrush.
  assert (In y (y1 :: y2 :: l0 ++ z' :: l')) by ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  destruct H8; destruct H9; try subst.
  ycrush.
  assert (In y (y1 :: y2 :: l0 ++ z' :: l')) by ycrush.
  assert (In z' (y1 :: y2 :: l0 ++ z' :: l')) by ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  assert (In x (y1 :: y2 :: l0 ++ z' :: l')) by ycrush.
  assert (In z' (y1 :: y2 :: l0 ++ z' :: l')) by ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
  assert (In x (y1 :: y2 :: l0 ++ z' :: l')) by ycrush.
  assert (In y (y1 :: y2 :: l0 ++ z' :: l')) by ycrush.
  pose lem_erased_eqv_sym; pose lem_erased_eqv_trans; ycrush.
Qed.

Lemma lem_tuple_length_expand :
  forall x y, is_ltup x = true -> is_ltup y = true -> Contr_clc_s x y ->
              length (tuple_of_lterm x) = length (tuple_of_lterm y).
Proof.
  intros.
  ydestruct x; ydestruct y; try yelles 1.
  yinversion H1.
  ycrush.
  ycrush.
  ycrush.
  simpl.
  induction l1; ycrush.
Qed.

Lemma lem_expand_s_in_tuple : forall y x z, Contr_clc_s_in_tuple x y -> RootContr_clc_s_minus y z ->
                                            exists z', RootContr_clc_s_minus x z'.
Proof.
  Ltac mytac :=
    match goal with
    | [ H : Contr_clc_s_in_tuple _ _ |- _ ] =>
      yinversion H; try solve [ pose lem_contr_s_preserves_is_ltup; yauto 1 ]
    end.
  intros.
  invert_rcontr_clc_s_minus.
  yintuition; simp_hyps; try subst.
  repeat mytac.
  repeat mytac.
  mytac.
  mytac.
  mytac.
  mytac.
  pose lem_contr_s_in_tuple_to_contr_s; pose lem_contr_s_erased_eqv; pose lem_erased_eqv_sym; ycrush.
  pose lem_contr_s_in_tuple_to_contr_s; pose lem_contr_s_erased_eqv; pose lem_erased_eqv_sym; ycrush.
  repeat mytac.
  yinversion H.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  yinversion H2.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  yinversion H1.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  ycrush.
  ycrush.
  yinversion H.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  yinversion H10.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  yinversion H9.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  yinversion H10.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  ycrush.

  assert (is_ltup y = true).
  ycrush.
  yinversion H9; yintuition.
  assert (All_pairs (tuple_of_lterm y) ErasedEqv).
  pose lem_all_pairs_expand; ycrush.
  pose lem_contr_s_length; ycrush.

  assert (is_ltup y = true).
  ycrush.
  yinversion H10; yintuition.
  assert (All_pairs (tuple_of_lterm y) ErasedEqv).
  pose lem_all_pairs_expand; ycrush.
  pose lem_exp_s_preserves_no_nested_tuple; pose lem_tuple_length_expand.
  ycrush.
  
  yinversion H.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  yinversion H8.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  yinversion H7.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  yinversion H8.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  ycrush.
  
  assert (is_ltup y = false).
  assert (is_ltup y = true -> False).
  yinversion H7; pose lem_contr_s_preserves_is_ltup; ycrush.
  ycrush.
  ycrush.
  yinversion H8; yintuition.
  assert (All_pairs (tuple_of_lterm y) ErasedEqv).
  pose lem_all_pairs_expand; ycrush.
  pose lem_exp_s_preserves_no_nested_tuple; pose lem_tuple_length_expand.
  ycrush.
Qed.

Lemma lem_snfm_contr_s_in_tuple_preserved :
  forall x y, sNFm x -> Contr_clc_s_in_tuple x y -> sNFm y.
Proof.
  assert (forall y z, Contr_clc_s_minus y z -> forall x, sNFm x -> Contr_clc_s_in_tuple x y -> False).
  unfold sNFm, not in *; intros y z H.
  induction H.
  pose lem_expand_s_in_tuple; pose lem_rcontr_s_minus_to_contr_s_minus; ycrush.
  yintros.
  yinversion H1.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  assert ((exists y0 : lterm, Contr_clc_s_minus x1 y0) -> False).
  yintro; pose_s_minus; ycrush.
  ycrush.
  pose_s_minus; ycrush.
  yintros.
  yinversion H1.
  pose lem_contr_s_preserves_is_ltup; ycrush.
  pose_s_minus; ycrush.
  assert ((exists y : lterm, Contr_clc_s_minus y0 y) -> False).
  yintro; pose_s_minus; ycrush.
  ycrush.
  unfold sNFm, not in *; yelles 1.
Qed.

Lemma lem_snfm_preserved : forall x y, sNFm x -> Contr_clc_s x y -> sNFm y.
Proof.
  eauto using lem_snfm_contr_s_in_tuple, lem_snfm_contr_s_in_tuple_preserved.  
Qed.

(* lemma 26 *)
Lemma lem_contr_s_minus_to_f1 :
  forall t, (forall x, Red_clc_s t x -> sNF x -> x = F1) -> Red_clc_s_minus t F1.
Proof.
  intros.
  assert (forall x, Red_clc_s t x -> sNFm x -> x = F1).
  intro x.
  assert (HH: Acc (fun x y : lterm => Contr_clc_s y x) x).
  pose lem_contr_clc_s_sn; unfold well_founded in *; eauto.
  induction HH.
  intros.
  assert ((exists y, Contr_clc_s x y) \/ ~(exists y, Contr_clc_s x y)).
  apply classic.
  destruct H4.
  simp_hyps.
  assert (sNFm x0) by eauto using lem_snfm_preserved.
  assert (Red_clc_s t x0).
  Reconstr.hobvious (@H4, @H2)
		    (lem_contr_s_minus_to_contr_s, sred.lem_red_s_trans, lem_rcontr_s_minus_to_contr_s_minus, lem_red_s_minus_to_red_s, sred.lem_contr_s_to_red_s)
		    Reconstr.Empty.
  assert (x0 = F1) by ycrush.
  assert (Contr_clc_s_in_tuple x x0) by eauto using lem_snfm_contr_s_in_tuple.
  yinversion H8; pose lem_contr_s_preserves_is_ltup; ycrush.
  assert (sNF x).
  Reconstr.htrivial (@H4)
		    (sred.lem_subterm_redex, sred.lem_basic_is_snf)
		    (sred.lterm_basic, sred.sNF, lterms.Redex_clc_s).
  ycrush.
  assert (exists x, Red_clc_s_minus t x /\ sNFm x) by auto using lem_red_s_minus_wn.
  pose lem_red_s_minus_to_red_s; ycrush.
Qed.

(* lemma 7 *)
Lemma lem_erase_contr_s_minus :
  forall t t' q, Erasure t q -> Contr_clc_s_minus t t' ->
                 exists q', Contr_clc q q' /\ Erasure t' q'.
Proof.
  Ltac mytac1 := eexists; unfold RootContr_clc; split; [ exists 0 | idtac ]; pose_erasure; yelles 1.
  assert (forall t t', Contr_clc_s_minus t t' -> forall q, Erasure t q -> 
                         exists q', Contr_clc q q' /\ Erasure t' q').
  intros t t' H.
  induction H; intros.
  
  assert (exists q' : iterm, RootContr_clc q q' /\ Erasure t2 q').
  invert_rcontr_clc_s_minus; yintuition; simp_hyps; try subst; invert_erasure; try mytac1.
  exists y'0; unfold RootContr_clc; split; [ exists 1; simpl | auto ].
  assert (EqvClose_i (RootContr_clc_base eq) y'0 y').
  pose lem_erasure_eqv; unfold Eqv_clc0, RootContr_clc0 in *.
  ycrush.
  ydestruct y'1; yelles 1.
  
  exists (y'1 @i y' @i (y'0 @i y')).
  split.
  unfold RootContr_clc; exists 0; ycrush.
  ydestruct x1; ydestruct x2; yintuition.
  invert_erasure.
  assert (forall y, In y (x1_1 :: x1_2 :: l) -> Erasure y y'0).
  Reconstr.hcrush (@H3, @H10, @H11)
		  (@Coq.Lists.List.Add_in, @Coq.Lists.List.not_in_cons, @Coq.Lists.List.in_inv, @Coq.Lists.List.NoDup_Add, @Coq.Init.Peano.f_equal_nat)
		  (@Coq.Lists.List.In, @All_pairs).
  assert (forall z, In z (x2_1 :: x2_2 :: l0) -> Erasure z y').
  Reconstr.hcrush (@H9, @H15, @H16)
		  (@Coq.Lists.List.Add_in, @Coq.Lists.List.not_in_cons, @Coq.Lists.List.in_inv, @Coq.Lists.List.NoDup_Add, @Coq.Init.Peano.f_equal_nat)
		  (@Coq.Lists.List.In, @All_pairs).
  assert (is_nonempty x).
  ydestruct x; yisolve; simpl in *; omega.
  apply (lem_s_result_erasure x x0 (x1_1 :: x1_2 :: l) (x2_1 :: x2_2 :: l0) y'1 y'0 y');
    ycrush.
  
  exists (y'1 @i y' @i (y'0 @i y')).
  split.
  unfold RootContr_clc; exists 0; ycrush.
  ydestruct x2; yintuition.
  invert_erasure.
  assert (forall y, In y (x2_1 :: x2_2 :: l) -> Erasure y y').
  Reconstr.hcrush (@H7, @H9, @H13)
		  (@Coq.Lists.List.Add_in, @Coq.Lists.List.not_in_cons, @Coq.Lists.List.in_inv, @Coq.Lists.List.NoDup_Add, @Coq.Init.Peano.f_equal_nat)
		  (@Coq.Lists.List.In, @All_pairs).
  auto using lem_s2_result_erasure.

  unfold Contr_clc; pose_ctx_i; ycrush.
  invert_erasure; pose_erasure; unfold Contr_clc; pose_ctx_i; ycrush.
  invert_erasure; pose_erasure; unfold Contr_clc; pose_ctx_i; ycrush.
  ycrush.
Qed.

Lemma lem_erase_red_s_minus :
  forall t t' q, Erasure t q -> Red_clc_s_minus t t' ->
                 exists q', Red_clc q q' /\ Erasure t' q'.
Proof.
  assert (forall t t', Red_clc_s_minus t t' ->
                       forall q, Erasure t q ->
                                 exists q', Red_clc q q' /\ Erasure t' q').
  intros t t' H.
  induction H.
  pose lem_erase_contr_s_minus; pose_rt; ycrush.
  ycrush.
  unfold Red_clc in *; pose_rt; ycrush.
  ycrush.
Qed.
