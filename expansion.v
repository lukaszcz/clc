(* This file contains the formalisation of lemma 24 and corollary 25 *)

Require Import general.
Require Import iterms.
Require Import lterms.
Require Import standard.
Require Import erasure.
Require Import sred.
Require Import ared.
Require Import ired.
Require Import istd.
Require Import acommute.
Require Import aexpand.
Require Import astd.

(* lemma 24 *)
Lemma lem_exp_a_preserves_leadsto_f1 :
  forall t t', Leadsto t' F1 -> Contr_clc_a t t' -> Leadsto t F1.
Proof.
  unfold Leadsto; yintros; split.
  pose lem_a_strongly_standard; ycrush.
  unfold StronglyStandard; intros.
  assert (exists u, Red_clc_s t' u /\ (Contr_clc_a x u \/ u = x)).
  pose lem_a_commute_red; ycrush.
  simp_hyps.
  destruct H5.
  Reconstr.hobvious (@H3, @H5)
		    (@ared.lem_contr_a_snf)
		    Reconstr.Empty.
  ycrush.
Qed.

Lemma lem_exp_red_i_a_preserves_leadsto_f1 :
  forall t t', Leadsto t' F1 -> Red_clc_i_a t t' -> Leadsto t F1.
Proof.
  assert (forall t t', Red_clc_i_a t t' -> Leadsto t' F1 -> Leadsto t F1).
  intros t t' H.
  induction H; yisolve.
  destruct H.
  pose lem_contr_exp_i_preserves_leadsto_f1; pose lem_contr_exp_i; ycrush.
  pose lem_exp_a_preserves_leadsto_f1; ycrush.
  ycrush.
Qed.

(* corollary 25 *)
Corollary cor_expansion :
  forall t q q', Leadsto t F1 -> Erasure t q -> Contr_clc0 q' q ->
                 exists t', Erasure t' q' /\ Leadsto t' F1.
Proof.
  intros.
  assert (exists t', Red_clc_i_a t' t /\ Erasure t' q').
  pose lem_clc0_expansion; pose lem_strongly_standard_implies_standard; unfold Leadsto in *; ycrush.
  pose lem_exp_red_i_a_preserves_leadsto_f1; ycrush.
Qed.
