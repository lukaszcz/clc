(* This file contains the formalisation of Theorem 32 (for CL-pc^1 only) *)

Require Import general.
Require Import basic_defs.
Require Import iterms.
Require Import aux.

Theorem thm_clc_confluent : forall x y z, Red_clc x y -> Red_clc x z ->
                                          exists u, Red_clc y u /\ Red_clc z u.
Proof.
  intros.
  assert (Eqv_clc x y).
  apply lem_red_clc_to_eqv_clc; ycrush.
  assert (Eqv_clc x z).
  apply lem_red_clc_to_eqv_clc; ycrush.
  assert (Eqv_clc y z).
  unfold Eqv_clc in *; eauto using eqv_sym, eqv_trans.
  assert (HH: Eqv_aux y z).
  apply lem_eqv_clc_to_eqv_aux; ycrush.
  clear -HH.
  pose lem_aux_cr; pose lem_red_aux_to_red_clc; ycrush.
Qed.

Check thm_clc_confluent.

Print Assumptions thm_clc_confluent.
