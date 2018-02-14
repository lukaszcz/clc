(* This file contains the formalisation of lemmas 12 and 13 *)

Require Import general.
Require Import iterms.
Require Import lterms.
Require Import erase_facts.
Require Import subterms.
Require Import standard.
Require Import erasure.
Require Import sred.
Require Import ired.
Require Import icommute.

Lemma lem_i_std : forall t t', Std t -> Contr_exp_clc_i t t' -> Std t'.
Proof.
  intros.
  ydestruct t; try yelles 1.
  assert (Sterm t1).
  unfold Std in *; simp_hyps; iauto 1.
  assert (exists t1' t2', t' = t1' @l t2' /\ Contr_exp_eq_clc_i t1 t1' /\ Contr_exp_eq_clc_i t2 t2').
  unfold Contr_exp_eq_clc_i; yinversion H0; ycrush.
  simp_hyps; subst.
  unfold Std.
  split.
  pose lem_contr_exp_i_preserves_sterm; pose_sterm; ycrush.
  split.
  intros.
  assert (exists u, Red_clc_s (t1 @l t2) u /\ Contr_exp_eq_clc_i u t').
  pose lem_contr_exp_i_postpone_red; ycrush.
  simp_hyps.
  assert (Sterm x1).
  unfold Std in *; simp_hyps; ycrush.
  clear -H7 H6; unfold Contr_exp_eq_clc_i in *; pose lem_contr_exp_i_preserves_sterm; ycrush.
  ydestruct x; yisolve.
  ydestruct x1; yisolve.
  ydestruct x1_1; yisolve.
  yinversion H3; [ idtac | ycrush ].
  invert_contr_exp_i_app.
  pose lem_contr_exp_i_sym; pose lem_contr_exp_i_preserves_snf; ycrush.
  invert_contr_exp_i_app; pose lem_contr_exp_i_implies_erased_eqv; pose_erased_eqv; ycrush.
  invert_contr_exp_i_app; pose lem_contr_exp_i_sym; pose lem_contr_exp_i_preserves_ltup;
    pose lem_contr_exp_i_length_preserved; ycrush.
  yinversion H3.
  invert_contr_exp_i_app; pose lem_contr_exp_i_sym; pose lem_contr_exp_i_preserves_ltup;
    pose lem_contr_exp_i_length_preserved; ycrush.
  yinversion H.
  destruct H4; [ idtac | ycrush ].
  pose lem_contr_exp_i_sym; pose lem_contr_exp_i_preserves_ltup;
    pose lem_contr_exp_i_length_preserved; ycrush.
  ydestruct t'; try yelles 1.
  simpl in *; simp_hyps.
  yinversion H0; yisolve; fold Contr_exp_clc_i in *.
  ycrush.
  ycrush.
  split; [ ycrush | split; [ ycrush | idtac ] ].
  induction l1.
  simpl in *.
  assert (is_ltup z = false).
  ycrush.
  ycrush.
  intros.
  assert (In x (a :: l1 ++ z' :: l')) by auto with datatypes.
  yintuition; ycrush.
Qed.

(* lemma 12 *)
Lemma lem_i_standard : forall t t', Standard t -> Contr_exp_clc_i t t' -> Standard t'.
Proof.
  assert (forall t' t, Standard t -> Contr_exp_clc_i t t' -> Standard t').
  unfold Standard; intro t'; lterm_induction t'.
  unfold Std; iauto 1.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  intros; invert_contr_exp_i_app; yinversion H1; pose lem_i_std; pose_subterm; cei_crush.
  
  intros.
  yinversion H0; yisolve; fold Contr_exp_clc_i in *.
  yinversion H1; pose lem_i_std; pose_subterm; cei_crush.
  yinversion H1; pose lem_i_std; pose_subterm; cei_crush.
  yinversion H1.
  pose lem_i_std; pose_subterm; cei_crush.
  pose lem_i_std; pose_subterm; cei_crush.
  pose lem_i_std; pose_subterm; cei_crush.
  induction l.
  yintuition.
  assert (forall y, Subterm y z -> Std y).
  intros; apply H.
  assert (Subterm z (ltup t'1 t'2 (nil ++ z :: l'))).
  pose_subterm; ycrush.
  pose lem_subterm_trans; ycrush.
  ycrush.
  apply H.
  assert (In z0 (z :: l')) by ycrush.
  pose_subterm; ycrush.
  yintuition.
  apply H.
  Reconstr.hobvious (@H7)
                    (@subterms.subterm_ltup_2, @Coq.Lists.List.in_eq)
		    Reconstr.Empty.
  apply H2; yisolve.
  clear -H H7 H3.
  intros.
  yinversion H0.
  assert (Std (ltup t'1 t'2 (a :: l ++ z :: l'))).
  pose_subterm; ycrush.
  pose lem_std_ltup; ycrush.
  pose_subterm; ycrush.
  pose_subterm; ycrush.
  assert (In z1 (a :: l ++ z :: l')) by auto with datatypes.
  pose_subterm; ycrush.

  ycrush.
  intros; destruct H; try subst; ycrush.
  ycrush.
Qed.

(* lemma 13 *)
Lemma lem_contr_exp_i_preserves_leadsto_f1 :
  forall t t', Leadsto t F1 -> Contr_exp_clc_i t t' -> Leadsto t' F1.
Proof.
  unfold Leadsto, StronglyStandard; yintros; split.
  pose lem_contr_exp_i_postpone_red; pose lem_i_standard; ycrush.
  intros.
  assert (exists u, Red_clc_s t u /\ Contr_exp_eq_clc_i u x).
  pose lem_contr_exp_i_postpone_red; ycrush.
  simp_hyps.
  destruct H5.
  assert (sNF x0).
  pose lem_contr_exp_i_preserves_snf; pose lem_contr_exp_i_sym; ycrush.
  ycrush.
  ycrush.
Qed.
