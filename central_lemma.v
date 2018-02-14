(* This file contains the formalisation of the central lemma 27 *)

Require Import general.
Require Import iterms.
Require Import lterms.
Require Import standard.
Require Import erasure.
Require Import sred.
Require Import contraction.
Require Import expansion.
Require Import smred.

Lemma lem_clc_to_leadsto : forall q, Eqv_clc q F -> exists t, Erasure t q /\ Leadsto t F1.
Proof.
  intros.
  assert (HH: Eqv_clc0 q F).
  Reconstr.htrivial (@H)
		    (lem_eqv_clc_to_eqv_clc0)
		    Reconstr.Empty.
  clear H.
  unfold Eqv_clc0, EqvClose_i in HH.
  rst_induction q; fold Contr_clc0 in *.
  pose cor_contraction; ycrush.
  pose cor_expansion; ycrush.
  exists F1; split.
  pose_erasure; ycrush.
  unfold Leadsto, StronglyStandard.
  assert (sNF F1).
  Reconstr.hobvious Reconstr.Empty
		    (@sred.lem_basic_is_snf)
		    (@sred.sNF, @sred.lterm_basic).
  pose lem_basic_standard; pose lem_red_s_preserves_snf; ycrush.
Qed.

(* lemma 27 *)
Lemma lem_central_lemma : forall q, Eqv_clc q F -> Red_clc q F.
Proof.
  intros.
  assert (exists t, Erasure t q /\ Leadsto t F1).
  pose lem_clc_to_leadsto; ycrush.
  unfold Leadsto in *; simp_hyps.
  assert (Red_clc_s_minus x F1).
  apply lem_contr_s_minus_to_f1; ycrush.
  assert (exists q', Red_clc q q' /\ Erasure F1 q').
  apply lem_erase_red_s_minus with (t := x); ycrush.
  simp_hyps.
  assert (x0 = erase F1).
  Reconstr.htrivial (@H5)
		    (@erasure.lem_erasure_leftmost)
		    Reconstr.Empty.
  ycrush.
Qed.

Lemma lem_t_red_clc : forall y, Red_clc T y -> y = T.
Proof.
  assert (forall x y, x = T -> Red_clc x y -> y = T).
  intros x y H0 H; induction H; try yelles 1.
  induction H; try yelles 1.
  subst; unfold RootContr_clc in *; simp_hyps; ycrush.
  ycrush.
Qed.

Corollary cor_t_not_f : not (Eqv_clc T F).
Proof.
  pose lem_central_lemma; pose lem_t_red_clc; ycrush.
Qed.
