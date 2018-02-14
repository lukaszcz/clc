(* This file contains the formalisation of lemma 14 and corollary 15 *)

Require Import general.
Require Import iterms.
Require Import lterms.
Require Import standard.
Require Import erasure.
Require Import sred.
Require Import ired.
Require Import icontr.
Require Import istd.

(* lemma 14 *)
Lemma lem_contr_s_preserves_leadsto_f1 :
  forall t t', Leadsto t F1 -> Contr_clc_s t t' -> Leadsto t' F1.
Proof.
  unfold Leadsto, StronglyStandard; pose_red_s; ycrush.
Qed.

Lemma lem_red_i_s_preserves_leadsto_f1 :
  forall t t', Leadsto t F1 -> Red_clc_i_s t t' -> Leadsto t' F1.
Proof.
  assert (forall t t', Red_clc_i_s t t' -> Leadsto t F1 -> Leadsto t' F1).
  intros t t' H.
  induction H; yisolve.
  destruct H.
  pose lem_contr_exp_i_preserves_leadsto_f1; pose lem_contr_exp_i; ycrush.
  pose lem_contr_s_preserves_leadsto_f1; ycrush.
  ycrush.
Qed.

(* corollary 15 *)
Corollary cor_contraction :
  forall t q q', Leadsto t F1 -> Erasure t q -> Contr_clc0 q q' ->
                 exists t', Erasure t' q' /\ Leadsto t' F1.
Proof.
  intros.
  assert (exists t', Red_clc_i_s t t' /\ Erasure t' q').
  pose lem_clc0_contraction; ycrush.
  pose lem_red_i_s_preserves_leadsto_f1; ycrush.
Qed.
