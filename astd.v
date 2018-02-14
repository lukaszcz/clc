(* This file contains the formalisation of lemmas 21, 22, 23 *)

Require Import general.
Require Import list_facts.
Require Import basic_defs.
Require Import lterms.
Require Import erase_facts.
Require Import subterms.
Require Import standard.
Require Import sred.
Require Import ared.
Require Import sexpand_std.
Require Import acommute.

(* lemma 21 *)
Lemma lem_standard_expand_below_a_redex :
  forall r1 r2 t, RootContr_clc_a r1 r2 -> StronglyStandard r2 -> Subterm t r1 -> t <> r1 ->
                  Standard t.
Proof.
  autounfold; intros.
  invert_rcontr_clc_a.
  assert (Standard r2).
  unfold StronglyStandard in *; pose_red_s; ycrush.
  yintuition; simp_hyps; subst; simpl in *.
  
  yinversion H1; yisolve.
  assert (Standard T1).
  pose lem_basic_standard; ycrush.
  assert (Sterm C1).
  pose_sterm; ycrush.
  assert (Standard (C1 @l T1 @l x)).
  apply lem_standard_basic_app_2; ycrush.
  pose lem_subterm_standard; ycrush.
  pose lem_iterm_standard; ycrush.

  yinversion H1; yisolve.
  assert (Standard F1).
  pose lem_basic_standard; ycrush.
  assert (Standard x).
  pose lem_iterm_standard; pose_subterm; ycrush.
  assert (Sterm C1).
  pose_sterm; ycrush.
  assert (Standard (C1 @l F1 @l x)).
  apply lem_standard_basic_app_2; ycrush.
  pose lem_subterm_standard; ycrush.
  pose lem_subterm_standard; ycrush.

  yinversion H1; yisolve.
  assert (Standard x1).
  pose lem_iterm_standard; pose_subterm; ycrush.
  assert (Standard x) by ycrush.
  assert (Sterm C2) by ycrush.
  assert (Standard (C2 @l x1 @l x)).
  apply lem_standard_basic_app_2; ycrush.
  pose lem_subterm_standard; ycrush.
  pose lem_subterm_standard; ycrush.

  yinversion H1; yisolve.
  Reconstr.hobvious (@H0, @H6, @H)
		    (@subterms.lem_subterm_trans, @standard.lem_strongly_standard_implies_standard, @standard.lem_basic_standard, @standard.lem_subterm_standard)
		    (@standard.Standard, @standard.StronglyStandard, @sred.lterm_basic, @Coq.Logic.Decidable.decidable).
  Reconstr.hobvious (@H, @H6)
		    (@standard.lem_subterm_standard)
		    Reconstr.Empty.

  yinversion H1; yisolve.
  assert (Sterm K1) by ycrush.
  assert (Standard (K1 @l x)).
  apply lem_standard_basic_app_1; ycrush.
  pose lem_subterm_standard; ycrush.
  pose lem_iterm_standard; ycrush.

  apply lem_standard_expand_below_S_redex with (r1 := r1) (r2 := r2); ycrush.
Qed.

(* lemma 22 *)
Lemma lem_exp_a_sterm : forall y x, Contr_clc_a x y -> Sterm y -> Sterm x.
Proof.
  induction y; try yelles 1;
    intros x H H1; yinversion H; invert_rcontr_clc_a;
      yintuition; try solve [ yintuition; pose_sterm; yelles 2 ];
        invert_rcontr_S; yintuition; try solve [ yintuition; pose_sterm; yelles 3 ].
Qed.

Lemma lem_a_std : forall t1 t2, StronglyStandard t2 -> Contr_clc_a t1 t2 -> Std t1.
Proof.
  Ltac mytac :=
    solve [ invert_rcontr_clc_a; yisolve; yintuition; yintuition | yelles 1 |
            exfalso; pose lem_contr_a_basic; yelles 2 ].
  
  intros.
  assert (Std t2).
  pose lem_strongly_standard_implies_std; ycrush.
  ydestruct t1; try yelles 1; try solve [ exfalso; pose lem_contr_a_basic; yelles 2 ].

  unfold Std.
  assert (Sterm t2).
  invert_contr_clc_a; ycrush.
  split.
  pose lem_exp_a_sterm; ycrush.
  split.
  intros.
  assert (exists u, (Contr_clc_a t' u \/ t' = u) /\ Red_clc_s t2 u).
  pose lem_a_commute_red; ycrush.
  simp_hyps.
  assert (Sterm x).
  unfold Std in *; ycrush.
  pose lem_exp_a_sterm; ycrush.
  ydestruct t1_1; yisolve.
  ydestruct t1_1_1; yisolve.
  ydestruct t1_1_1_1; yisolve.

  repeat invert_contr_clc_a; pose lem_contr_a_snf; mytac.
  
  repeat invert_contr_clc_a; try mytac.
  invert_rcontr_clc_a; yintuition; yintuition;
    yinversion H0; pose lem_red_s_implies_erased_eqv; pose_erased_eqv; ycrush.
  simpl in *; simp_hyps; pose lem_contr_a_to_erased_eqv; pose_erased_eqv; ycrush.
  simpl in *; simp_hyps; pose lem_contr_a_to_erased_eqv; pose_erased_eqv; ycrush.

  repeat invert_contr_clc_a; try mytac.
  simpl in *; simp_hyps.
  assert (is_ltup t1_1_2 = true).
  ydestruct y'; yisolve; yinversion H5; try invert_rcontr_clc_a; ycrush.
  assert (length (tuple_of_lterm y') = length (tuple_of_lterm t1_1_2)).
  ydestruct y'; yisolve.
  yinversion H5.
  invert_rcontr_clc_a; ycrush.
  ycrush.
  ycrush.
  simpl; clear; induction l1; simpl; omega.
  ycrush.
  simpl in *; simp_hyps.
  assert (is_ltup t1_2 = true).
  ydestruct y'; yisolve; yinversion H6; try invert_rcontr_clc_a; ycrush.
  assert (length (tuple_of_lterm y') = length (tuple_of_lterm t1_2)).
  ydestruct y'; yisolve.
  yinversion H6.
  invert_rcontr_clc_a; ycrush.
  ycrush.
  ycrush.
  simpl; clear; induction l1; simpl; omega.
  ycrush.

  repeat invert_contr_clc_a; try mytac.
  simpl in *; simp_hyps.
  assert (is_ltup t1_1_2 = false).
  assert (HH: is_ltup t1_1_2 = true \/ is_ltup t1_1_2 = false) by ycrush.
  destruct HH; pose lem_contr_a_preserves_is_ltup; ycrush.
  ycrush.
  simpl in *; simp_hyps.
  assert (is_ltup t1_2 = true).
  ydestruct y'; yisolve; yinversion H6; try invert_rcontr_clc_a; ycrush.
  assert (length (tuple_of_lterm y') = length (tuple_of_lterm t1_2)).
  ydestruct y'; yisolve.
  yinversion H6.
  invert_rcontr_clc_a; ycrush.
  ycrush.
  ycrush.
  simpl; clear; induction l0; simpl; omega.
  ycrush.

  yinversion H0; simpl in *; fold Contr_clc_a in *; simp_hyps.
  invert_rcontr_clc_a; yisolve.
  pose lem_exp_a_preserves_not_ltup; ycrush.
  pose lem_exp_a_preserves_not_ltup; ycrush.
  yintuition; yisolve.
  clear H.
  induction l0.
  pose lem_exp_a_preserves_not_ltup; ycrush.
  ycrush.
Qed.

(* lemma 23 *)
Lemma lem_a_standard : forall t1 t2, StronglyStandard t2 -> Contr_clc_a t1 t2 -> Standard t1.
Proof.
  unfold Standard; intros t1 t2 H0 H.
  assert (HStd: Std t1).
  eapply lem_a_std; ycrush.
  induction H; fold Contr_clc_a in *.
  
  intros.
  assert (x = t1 \/ x <> t1).
  apply classic.
  destruct H2.
  ycrush.
  eapply lem_standard_expand_below_a_redex; ycrush.

  assert (StronglyStandard x').
  eapply lem_reduce_subterm_strongly_standard; pose_subterm; ycrush.
  assert (Standard y).
  pose lem_reduce_subterm_strongly_standard; apply lem_strongly_standard_implies_standard;
    pose_red_s; pose_subterm; ycrush.
  assert (Std x).
  eapply lem_a_std; pose lem_strongly_standard_implies_std; ycrush.
  assert (forall x0 : lterm, Subterm x0 x -> Std x0) by ycrush.
  intros x0 HH; yinversion HH; unfold Standard in *; pose_subterm; ycrush.

  assert (StronglyStandard y').
  eapply lem_reduce_subterm_strongly_standard; pose_subterm; ycrush.
  assert (Standard x).
  pose lem_reduce_subterm_strongly_standard; apply lem_strongly_standard_implies_standard;
    pose_red_s; pose_subterm; ycrush.
  assert (Std y).
  eapply lem_a_std; pose lem_strongly_standard_implies_std; ycrush.
  assert (forall x : lterm, Subterm x y -> Std x) by ycrush.
  intros x0 HH; yinversion HH; unfold Standard in *; pose_subterm; ycrush.

  assert (StronglyStandard x').
  eapply lem_reduce_subterm_strongly_standard; pose_subterm; ycrush.
  assert (Standard y).
  pose lem_reduce_subterm_strongly_standard; apply lem_strongly_standard_implies_standard;
    pose_red_s; pose_subterm; ycrush.
  assert (forall u, In u l -> Standard u).
  pose lem_reduce_subterm_strongly_standard; pose lem_strongly_standard_implies_standard;
    pose_red_s; pose_subterm; ycrush.
  assert (Std x).
  eapply lem_a_std; pose lem_strongly_standard_implies_std; ycrush.
  assert (forall x0 : lterm, Subterm x0 x -> Std x0) by ycrush.
  intros x0 HH; yinversion HH; unfold Standard in *; pose_subterm; ycrush.

  assert (StronglyStandard y').
  eapply lem_reduce_subterm_strongly_standard; pose_subterm; ycrush.
  assert (Standard x).
  pose lem_reduce_subterm_strongly_standard; apply lem_strongly_standard_implies_standard;
    pose_red_s; pose_subterm; ycrush.
  assert (forall u, In u l -> Standard u).
  pose lem_reduce_subterm_strongly_standard; pose lem_strongly_standard_implies_standard;
    pose_red_s; pose_subterm; ycrush.
  assert (Std y).
  eapply lem_a_std; pose lem_strongly_standard_implies_std; ycrush.
  assert (forall x : lterm, Subterm x y -> Std x) by ycrush.
  intros x0 HH; yinversion HH; unfold Standard in *; pose_subterm; ycrush.

  assert (StronglyStandard z').
  eapply lem_reduce_subterm_strongly_standard; pose_subterm; ycrush.
  assert (Standard x).
  pose lem_reduce_subterm_strongly_standard; apply lem_strongly_standard_implies_standard;
    pose_red_s; pose_subterm; ycrush.
  assert (Standard y).
  pose lem_reduce_subterm_strongly_standard; apply lem_strongly_standard_implies_standard;
    pose_red_s; pose_subterm; ycrush.
  assert (Std z).
  eapply lem_a_std; pose lem_strongly_standard_implies_std; ycrush.
  assert (Standard z).
  unfold Standard in *; ycrush.
  assert (forall u, In u l' -> Standard u).
  intros.
  assert (In u (l ++ z' :: l')).
  Reconstr.hobvious (@H6)
		    (@at_lem_in_app_2)
		    Reconstr.Empty.
  pose lem_reduce_subterm_strongly_standard; pose lem_strongly_standard_implies_standard;
    pose_red_s; pose_subterm; ycrush.
  assert (forall u, In u l -> Standard u).
  intros.
  assert (In u (l ++ z' :: l')).
  Reconstr.hobvious (@H7)
		    (@at_lem_in_app_2)
		    Reconstr.Empty.
  pose lem_reduce_subterm_strongly_standard; pose lem_strongly_standard_implies_standard;
    pose_red_s; pose_subterm; ycrush.
  assert (forall u, In u (l ++ z :: l') -> Standard u).
  induction l.
  simpl in *; eauto.
  ycrush.
  simpl in *; simp_hyps.
  assert (forall u : lterm, In u (l ++ z :: l') -> Standard u).
  Reconstr.hsimple (@H6, @H5, @H7)
		   (@at_lem_in_app_1)
		   Reconstr.Empty.
  ycrush.
  clear -HStd H2 H3 H8.
  unfold Standard in *; pose_subterm; ycrush.
Qed.

Lemma lem_a_strongly_standard :
  forall t1 t2, StronglyStandard t2 -> Contr_clc_a t1 t2 -> StronglyStandard t1.
Proof.
  intros.
  unfold StronglyStandard.
  intros.
  assert (exists u, Red_clc_s t2 u /\ (Contr_clc_a x u \/ x = u)).
  pose lem_a_commute_red; ycrush.
  simp_hyps.
  destruct H3; pose lem_reduce_subterm_strongly_standard;
    pose lem_a_standard; pose_subterm; ycrush.
Qed.
