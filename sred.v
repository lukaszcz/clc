(* This file contains the formalisation of basic properties of s-reduction *)

Require Import general.
Require Import list_facts.
Require Import lterms.
Require Import erase_facts.
Require Import subterms.
Require Import svars.
Require Import red.
Require Import sn.

Lemma lem_red_s_refl : forall x, Red_clc_s x x.
Proof.
  unfold Red_clc_s; pose_rt; ycrush.
Qed.

Lemma lem_red_s_trans : forall x y z, Red_clc_s x y -> Red_clc_s y z -> Red_clc_s x z.
Proof.
  unfold Red_clc_s; pose_rt; ycrush.
Qed.

Lemma lem_rcontr_s_to_contr_s : forall x y, RootContr_clc_s x y -> Contr_clc_s x y.
Proof.
  unfold Contr_clc_s; pose_ctx_l; ycrush.
Qed.

Lemma lem_contr_s_to_red_s : forall x y, Contr_clc_s x y -> Red_clc_s x y.
Proof.
  unfold Red_clc_s; pose_rt; ycrush.
Qed.

Lemma lem_rcontr_s_to_red_s : forall x y, RootContr_clc_s x y -> Red_clc_s x y.
Proof.
  auto using lem_rcontr_s_to_contr_s, lem_contr_s_to_red_s.
Qed.

Lemma lem_red_s_cong_l : forall x y z, Red_clc_s x y -> Red_clc_s (x @l z) (y @l z).
Proof.
  unfold Red_clc_s; intros; induction H.
  unfold Contr_clc_s in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_s_cong_r : forall x y z, Red_clc_s x y -> Red_clc_s (z @l x) (z @l y).
Proof.
  unfold Red_clc_s; intros; induction H.
  unfold Contr_clc_s in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_s_ltup_0 : forall x x' y l, Red_clc_s x x' -> Red_clc_s (ltup x y l) (ltup x' y l).
Proof.
  unfold Red_clc_s; intros; induction H.
  unfold Contr_clc_s in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_s_ltup_1 : forall x y y' l, Red_clc_s y y' -> Red_clc_s (ltup x y l) (ltup x y' l).
Proof.
  unfold Red_clc_s; intros; induction H.
  unfold Contr_clc_s in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_s_ltup_2 : forall x y z z' l l', Red_clc_s z z' ->
                                               Red_clc_s (ltup x y (l ++ z :: l'))
                                                         (ltup x y (l ++ z' :: l')).
Proof.
  unfold Red_clc_s; intros; induction H.
  unfold Contr_clc_s in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_contr_s_cong_l : forall x y z, Contr_clc_s x y -> Contr_clc_s (x @l z) (y @l z).
Proof.
  unfold Contr_clc_s; intros; induction H; pose_ctx_l; ycrush.
Qed.

Lemma lem_contr_s_cong_r : forall x y z, Contr_clc_s x y -> Contr_clc_s (z @l x) (z @l y).
Proof.
  unfold Contr_clc_s; intros; induction H; pose_ctx_l; ycrush.
Qed.

Lemma lem_contr_s_ltup_0 : forall x x' y l, Contr_clc_s x x' ->
                                            Contr_clc_s (ltup x y l) (ltup x' y l).
Proof.
  unfold Contr_clc_s; intros; induction H; pose_ctx_l; ycrush.
Qed.

Lemma lem_contr_s_ltup_1 : forall x y y' l, Contr_clc_s y y' ->
                                            Contr_clc_s (ltup x y l) (ltup x y' l).
Proof.
  unfold Contr_clc_s; intros; induction H; pose_ctx_l; ycrush.
Qed.

Lemma lem_contr_s_ltup_2 : forall x y z z' l l', Contr_clc_s z z' ->
                                               Contr_clc_s (ltup x y (l ++ z :: l'))
                                                           (ltup x y (l ++ z' :: l')).
Proof.
  unfold Contr_clc_s; intros; induction H; pose_ctx_l; ycrush.
Qed.

Ltac pose_contr_s := pose lem_contr_s_cong_l; pose lem_contr_s_cong_r; pose lem_rcontr_s_to_contr_s;
                     pose lem_contr_s_ltup_0; pose lem_contr_s_ltup_1; pose lem_contr_s_ltup_2.

Lemma lem_red_s_ind :
  forall P : lterm -> Prop,
    (forall x y, P x -> Contr_clc_s x y -> P y) ->
    forall x y, P x -> Red_clc_s x y -> P y.
Proof.
  intros; induction H1; eauto.
Qed.

Definition lterm_basic x := x = C1 \/ x = C2 \/ x = T1 \/ x = F1 \/ x = I1 \/ x = K1 \/
                            (exists l, x = S1 l) \/ (exists n, x = S2 n) \/
                            (exists i, x = itm i).
Hint Unfold lterm_basic : yhints.

Lemma lem_contr_s_basic :
  forall x y, Contr_clc_s x y -> lterm_basic x -> False.
Proof.
  unfold lterm_basic; intros; yinversion H; yauto 2.
Qed.

Lemma lem_red_s_basic : forall x y, Red_clc_s x y -> lterm_basic x -> x = y.
Proof.
  intros; induction H; try subst; pose lem_contr_s_basic; ycrush.
Qed.

Lemma lem_contr_s_subterm : forall x y x', Contr_clc_s x y -> Subterm x x' ->
                                           exists y', Contr_clc_s x' y' /\ Subterm y y'.
Proof.
  Ltac mytac :=
    intros H0 H;
    pose lem_contr_s_basic;
    pose subterm_i;
    match goal with [ H : Subterm ?x ?y |- ?G ] => exists y end;
    yinversion H; yelles 2.
  intros x y x'; lterm_induction x'; try mytac.
  intros H0 H; yinversion H.
  pose lem_subterm_app; simp_hyps; yauto 1.
  pose lem_contr_s_cong_l; simp_hyps; exists (x0 @l x'2); pose_subterm; yauto 1.
  pose lem_contr_s_cong_r; simp_hyps; exists (x'1 @l x0); pose_subterm; yauto 1.
  intros H0 H; yinversion H.
  yauto 1.
  pose lem_contr_s_ltup_0; simp_hyps; exists (ltup x0 x'2 l1); pose_subterm; yauto 1.
  pose lem_contr_s_ltup_1; simp_hyps; exists (ltup x'1 x0 l1); pose_subterm; yauto 1.
  generalize (IHx'3 z); clear IHx'3; intro; simp_hyps.
  clear H H2 H0 H6.
  assert (exists l l', l1 = l ++ z :: l').
  Reconstr.htrivial (@H4)
		    (@Coq.Lists.List.in_split)
		    Reconstr.Empty.
  simp_hyps; subst.
  assert (In x0 (x1 ++ x0 :: x2)).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Lists.List.in_eq, @Coq.Lists.List.in_app_iff)
		    (@Coq.Init.Datatypes.app).
  pose lem_contr_s_ltup_2; exists (ltup x'1 x'2 (x1 ++ x0 :: x2)); pose_subterm; yauto 1.
  yauto 1.
  yauto 2.
Qed.

Lemma lem_red_s_subterm : forall x y x', Red_clc_s x y -> Subterm x x' ->
                                         exists y', Red_clc_s x' y' /\ Subterm y y'.
Proof.
  assert (forall x y, Red_clc_s x y -> forall x', Subterm x x' ->
                         exists y', Red_clc_s x' y' /\ Subterm y y').
  pose lem_contr_s_subterm.
  unfold Red_clc_s.
  intros x y H.
  induction H; intros; pose_rt; ycrush.
  ycrush.
Qed.

Ltac pose_red_s := pose lem_red_s_refl; pose lem_red_s_trans; pose lem_rcontr_s_to_red_s;
                   pose lem_contr_s_to_red_s; pose lem_red_s_subterm; pose lem_red_s_cong_l;
                   pose lem_red_s_cong_r; pose lem_red_s_ltup_0; pose lem_red_s_ltup_1;
                   pose lem_red_s_ltup_2.

Lemma lem_contr_s_ltup_inv_red_s : forall x y l z, Contr_clc_s (ltup x y l) z ->
                                                   exists x' y' l', z = ltup x' y' l' /\
                                                                    Red_clc_s x x' /\
                                                                    Red_clc_s y y' /\
                                                                    list_closure Red_clc_s l l'.
Proof.
  intros.
  yinversion H.
  ycrush.
  pose_red_s; pose_lc; ycrush.
  pose_red_s; pose_lc; ycrush.
  pose_red_s; pose_lc; ycrush.
Qed.

Lemma lem_red_s_ltup_inv : forall x y l z, Red_clc_s (ltup x y l) z ->
                                                 exists x' y' l', z = ltup x' y' l' /\
                                                                  Red_clc_s x x' /\
                                                                  Red_clc_s y y' /\
                                                                  list_closure Red_clc_s l l'.
Proof.
  assert (forall z z' x y l, Red_clc_s z z' -> z = ltup x y l ->
                             exists x' y' l', z' = ltup x' y' l' /\
                                              Red_clc_s x x' /\
                                              Red_clc_s y y' /\
                                              list_closure Red_clc_s l l').
  intros.
  apply lem_red_s_ind with (x := z) (y := z');
    yintros; pose lem_contr_s_ltup_inv_red_s; pose_red_s; pose_lc; ycrush.
  ycrush.
Qed.

Definition sNF x := not (exists y, Subterm y x /\ Redex_clc_s y).
Hint Unfold sNF : unfold_hints.

Lemma lem_subterm_redex : forall x, (exists y, Subterm y x /\ Redex_clc_s y) <->
                                    (exists y, Contr_clc_s x y).
Proof.
  pose lem_rcontr_clc_s_implies_redex.
  pose lem_redex_clc_s_implies_rcontr.
  pose lem_contr_s_subterm.
  unfold Contr_clc_s in *.
  intros.
  yintuition; simp_hyps.
  pose_ctx_l; ycrush.
  induction H; pose_subterm; yauto 1.
Qed.

Lemma lem_contr_s_snf : forall x y, Contr_clc_s x y -> sNF x -> False.
Proof.
  unfold sNF; intros.
  pose lem_subterm_redex; ycrush.
Qed.

Lemma lem_red_s_preserves_snf : forall x y, Red_clc_s x y -> sNF x -> x = y.
Proof.
  intros x y H; induction H; pose lem_contr_s_snf; ycrush.
Qed.

Lemma lem_red_s_wn : forall x, exists y, Red_clc_s x y /\ sNF y.
Proof.
  intro.
  assert (Acc (fun x y : lterm => Contr_clc_s y x) x).
  pose lem_contr_clc_s_sn; unfold well_founded in *; eauto.
  induction H.
  assert ((exists y, Contr_clc_s x y) \/ not (exists y, Contr_clc_s x y)).
  apply classic.
  destruct H1.
  pose lem_contr_s_to_red_s; pose lem_red_s_trans; ycrush.
  assert (sNF x).
  pose lem_subterm_redex; unfold sNF in *; ycrush.
  ycrush.
Qed.

Lemma lem_basic_is_snf : forall x, lterm_basic x -> sNF x.
Proof.
  unfold lterm_basic, sNF; destruct x; ycrush.
Qed.

Lemma lem_contr_s_preserves_is_ltup : forall x y, Contr_clc_s x y -> is_ltup x = true ->
                                                  is_ltup y = true.
Proof.
  intros.
  induction H; try yauto 1.
  invert_rcontr_clc_s.
  ydestruct H1; try yauto 1.
  repeat (ydestruct H; yintuition; try yauto 1).
Qed.

Lemma lem_red_s_preserves_is_ltup : forall x y, Red_clc_s x y -> is_ltup x = true ->
                                                is_ltup y = true.
Proof.
  pose lem_contr_s_preserves_is_ltup.
  intros; induction H; ycrush.
Qed.

Lemma lem_exp_s_preserves_not_is_ltup : forall x y, Contr_clc_s x y -> is_ltup y = false ->
                                                    is_ltup x = false.
Proof.
  intros.
  induction H; try yauto 1.
  invert_rcontr_clc_s.
  ydestruct H1; try yauto 1.
Qed.

Lemma lem_red_s_ltup_closure_0 :
  forall l l', list_closure Red_clc_s l l' ->
               forall x y l0, Red_clc_s (ltup x y (l0 ++ l)) (ltup x y (l0 ++ l')).
Proof.
  pose (lem_red_ltup_closure_0 Red_clc_s); pose_red_s; ycrush.
Qed.

Lemma lem_red_s_ltup_closure :
  forall x y x' y' l l', Red_clc_s x x' -> Red_clc_s y y' -> list_closure Red_clc_s l l' ->
                                 Red_clc_s (ltup x y l) (ltup x' y' l').
Proof.
  pose (lem_red_ltup_closure Red_clc_s); pose_red_s; ycrush.
Qed.

Ltac invert_contr_clc_s :=
  match goal with
  | [ H : Contr_clc_s (_ @l _) _ |- _ ] =>  yinversion H; fold Contr_clc_s in *; yisolve
  end.

Lemma lem_contr_s_s_result_1 :
  forall ns x x' l1 l2,
    is_nonempty ns ->
    Contr_clc_s x x' ->
    Contr_clc_s (build_s_result ns x l1 l2) (build_s_result ns x' l1 l2).
Proof.
  apply lem_s_result_1; pose_contr_s; ycrush.
Qed.

Lemma lem_contr_s_ltup_inv :
  forall (x y : lterm) (l : list lterm) (w : lterm),
    Contr_clc_s (ltup x y l) w ->
    (exists x' : lterm, w = ltup x' y l /\ Contr_clc_s x x') \/
    (exists y' : lterm, w = ltup x y' l /\ Contr_clc_s y y') \/
    (exists (l1 l2 : list lterm) (z z' : lterm),
        l = l1 ++ z :: l2 /\ w = ltup x y (l1 ++ z' :: l2) /\ Contr_clc_s z z').
Proof.
  intros; yinversion H; yisolve.
Qed.

Lemma lem_contr_s_s_result_2 :
  forall ns x y y' l,
    (forall z, In z (tuple_of_lterm y) -> R_glue_iterms_l Contr_clc_s z) ->
    is_ltup y = true ->
    lst_sum ns < length l ->
    length (tuple_of_lterm y) = length ns ->
    Contr_clc_s y y' ->
    Contr_clc_s (build_s_result ns x (tuple_of_lterm y) l)
                (build_s_result ns x (tuple_of_lterm y') l).
Proof.
  apply lem_s_result_2; pose lem_contr_s_ltup_inv; pose_contr_s; ycrush.
Qed.

Lemma lem_contr_s_s_result_3 :
  forall ns x l y y',
    (forall z, In z (tuple_of_lterm y) -> R_glue_iterms_r Contr_clc_s z) ->
    is_ltup y = true ->
    lst_sum ns < length (tuple_of_lterm y) ->
    length l = length ns ->
    Contr_clc_s y y' ->
    Contr_clc_s (build_s_result ns x l (tuple_of_lterm y))
                (build_s_result ns x l (tuple_of_lterm y')).
Proof.
  apply lem_s_result_3; pose lem_contr_s_ltup_inv; pose_contr_s; ycrush.
Qed.

Lemma lem_contr_s_s2_result :
  forall n x y z z',
    (forall u, In u (tuple_of_lterm z) -> R_glue_iterms_r Contr_clc_s u) ->
    is_ltup z = true ->
    Contr_clc_s z z' ->
    Contr_clc_s (x @l lterm_of_tuple (firstn n (tuple_of_lterm z)) @l
                   glue_iterms y (lterm_of_tuple (skipn n (tuple_of_lterm z))))
                (x @l lterm_of_tuple (firstn n (tuple_of_lterm z')) @l
                   glue_iterms y (lterm_of_tuple (skipn n (tuple_of_lterm z')))).
Proof.
  apply lem_s2_result; pose lem_contr_s_ltup_inv; pose_contr_s; ycrush.
Qed.

Lemma lem_contr_s_all_pairs_erased_eqv :
  forall y y', is_ltup y = true -> Contr_clc_s y y' ->
               All_pairs (tuple_of_lterm y) ErasedEqv ->
               All_pairs (tuple_of_lterm y') ErasedEqv.
Proof.
  intros y y'; apply lem_all_pairs_erased_eqv; pose lem_contr_s_implies_erased_eqv;
    pose lem_contr_s_ltup_inv; pose_contr_s; ycrush.
Qed.

Lemma lem_contr_s_length :
  forall x y, is_ltup x = true -> is_ltup y = true ->
              Contr_clc_s x y -> length (tuple_of_lterm x) = length (tuple_of_lterm y).
Proof.
  induction x, y; try yelles 2.
  intros.
  yinversion H1.
  yinversion H2.
  fold Contr_clc_s in *; ycrush.
  fold Contr_clc_s in *; ycrush.
  induction l1; ycrush.
Qed.

Lemma lem_contr_s_ltup_extend :
  forall x y l x' y' l', Contr_clc_s (ltup x y l) (ltup x' y' l') ->
                         forall a, Contr_clc_s (ltup x y (a :: l)) (ltup x' y' (a :: l')).
Proof.
  intros.
  yinversion H; fold Contr_clc_s in *.
  ycrush.
  pose_contr_s; ycrush.
  pose_contr_s; ycrush.
  assert (Contr_clc_s (ltup x' y' ((a :: l0) ++ z :: l'0)) (ltup x' y' ((a :: l0) ++ z' :: l'0))).
  pose_contr_s; ycrush.
  ycrush.
Qed.

Lemma lem_red_s_ltup_extend :
  forall x y l x' y' l', Red_clc_s (ltup x y l) (ltup x' y' l') ->
                         forall a, Red_clc_s (ltup x y (a :: l)) (ltup x' y' (a :: l')).
Proof.
  assert (forall a b, Red_clc_s a b ->
                      forall x y l x' y' l', a = ltup x y l -> b = ltup x' y' l' ->
                                             forall a, Red_clc_s (ltup x y (a :: l))
                                                                 (ltup x' y' (a :: l'))).
  intros a b H.
  induction H; fold Red_clc_s in *.
  pose lem_contr_s_ltup_extend; pose_red_s; ycrush.
  yintros; pose_red_s; ycrush.
  yintros.
  assert (is_ltup x = true) by ycrush.
  assert (is_ltup y = true).
  pose lem_red_s_preserves_is_ltup; ycrush.
  ydestruct y; yisolve.
  subst; pose_red_s; ycrush.
  ycrush.
Qed.

Lemma lem_red_s_basic_app_1 :
  forall a x y, lterm_basic a -> a <> I1 -> Red_clc_s (a @l x) y ->
              exists x', y = (a @l x') /\ Red_clc_s x x'.
Proof.
  assert (forall a y u, lterm_basic a -> a <> I1 -> Red_clc_s u y ->
                        forall x, u = a @l x ->
                                  exists x', y = (a @l x') /\ Red_clc_s x x').
  intros a y u H0 H1 H.
  induction H; fold Red_clc_s in *.
  yinversion H; fold Contr_clc_s in *; pose lem_contr_s_basic; pose_red_s; ycrush.
  pose_red_s; ycrush.
  yintros.
  yforwarding.
  yforwarding.
  pose_red_s; ycrush.  
  ycrush.
Qed.

Lemma lem_red_s_basic_app_2 :
  forall a x1 x2 y, lterm_basic a -> a <> I1 -> a <> K1 -> Red_clc_s (a @l x1 @l x2) y ->
                    exists x1' x2', y = (a @l x1' @l x2') /\
                                    Red_clc_s x1 x1' /\ Red_clc_s x2 x2'.
Proof.
  assert (forall a y u, lterm_basic a -> a <> I1 -> a <> K1 -> Red_clc_s u y ->
                        forall x1 x2, u = a @l x1 @l x2 ->
                                      exists x1' x2', y = (a @l x1' @l x2') /\
                                                      Red_clc_s x1 x1' /\ Red_clc_s x2 x2').
  intros a y u H0 H1 H2 H.
  induction H; fold Red_clc_s in *.
  yinversion H; fold Contr_clc_s in *.
  ycrush.
  intros; yinversion H; pose lem_red_s_basic_app_1; pose_red_s; ycrush.
  pose_red_s; ycrush.
  pose_red_s; ycrush.
  pose_red_s; ycrush.
  pose_red_s; ycrush.
  pose_red_s; ycrush.
  yintros.
  yforwarding.
  yforwarding.
  pose_red_s; ycrush.  
  ycrush.
Qed.

Lemma lem_exp_s_preserves_no_nested_tuple :
  forall y y', Contr_clc_s y y' ->
               (forall x, In x (tuple_of_lterm y') -> is_ltup x = false) ->
               forall x, In x (tuple_of_lterm y) -> is_ltup x = false.
Proof.
  intros.
  assert (is_ltup y = true \/ is_ltup y = false) by ycrush.
  yintuition.
  ydestruct y; yisolve; simpl in *.
  yinversion H; fold Contr_clc_s in *; simpl in *.
  ycrush.
  pose lem_exp_s_preserves_not_is_ltup; ycrush.
  pose lem_exp_s_preserves_not_is_ltup; ycrush.
  yintuition; try yelles 1.
  induction l0; simpl in *.
  pose lem_exp_s_preserves_not_is_ltup; ycrush.
  intuition; firstorder.
  assert (HH: tuple_of_lterm y = y :: nil) by ycrush.
  rewrite HH in *; clear HH.
  simpl in *; ycrush.
Qed.
