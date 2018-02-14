(* This file contains the definitions of i-contraction/reduction,
   i-expansion, i,s-reduction, and the formalisation of their basic
   properties *)

Require Import general.
Require Import iterms.
Require Import lterms.
Require Import erase_facts.

Definition Contr_clc_i :=
  CtxClose_l (fun x y => match x, y with itm i1, itm i2 => Contr_clc i1 i2 | _, _ => False end).

Definition Red_clc_i := clos_refl_trans lterm Contr_clc_i.

Definition Contr_exp_clc_i :=
  CtxClose_l (fun x y => match x, y with
                         | itm i1, itm i2 =>
                           Contr_clc i1 i2 \/ Contr_clc i2 i1
                         | _, _ => False end).
Definition Contr_exp_eq_clc_i t1 t2 := Contr_exp_clc_i t1 t2 \/ t1 = t2.

Definition Contr_clc_i_s x y := Contr_clc_i x y \/ Contr_clc_s x y.
Definition Red_clc_i_s := clos_refl_trans lterm Contr_clc_i_s.

Lemma lem_contr_i_implies_erased_eqv : forall t1 t2, Contr_clc_i t1 t2 -> ErasedEqv t1 t2.
Proof.
  pose lem_contr_clc_implies_eqv_clc.
  unfold ErasedEqv, Eqv_clc.
  intros t1 t2 H; induction H; simpl; eqv_solve 1.
Qed.

Lemma lem_contr_exp_i_implies_erased_eqv : forall t1 t2, Contr_exp_clc_i t1 t2 -> ErasedEqv t1 t2.
Proof.
  pose lem_contr_clc_implies_eqv_clc.
  unfold ErasedEqv, Eqv_clc.
  intros t1 t2 H; induction H; simpl; try eqv_solve 1.
  ydestruct t1; ydestruct t2; try yelles 1.
  yintuition.
  eqv_solve 1.
  pose eqv_sym; pose eqv_lift; ycrush.
Qed.

Lemma lem_red_s_implies_red_i_s : forall x y, Red_clc_s x y -> Red_clc_i_s x y.
Proof.
  unfold Red_clc_s, Red_clc_i_s, Contr_clc_i_s.
  intros x y H; induction H; pose_rt; ycrush.
Qed.

Lemma lem_contr_clc0_implies_contr_i_s :
  forall q1 q2, Contr_clc0 q1 q2 -> Contr_clc_i_s (itm q1) (itm q2).
Proof.
  pose lem_contr_clc0_implies_contr_clc.
  unfold Contr_clc_i_s, Contr_clc_i; pose_ctx_l; ycrush.
Qed.

Lemma lem_rcontr_s_implies_red_i_s : forall x y, RootContr_clc_s x y -> Red_clc_i_s x y.
Proof.
  unfold Red_clc_i_s, Contr_clc_i_s, Contr_clc_s; pose_rt; pose_ctx_l; ycrush.
Qed.

Lemma lem_red_i_s_refl : forall x, Red_clc_i_s x x.
Proof.
  unfold Red_clc_i_s; pose_rt; ycrush.
Qed.

Lemma lem_red_i_s_trans : forall x y z, Red_clc_i_s x y -> Red_clc_i_s y z -> Red_clc_i_s x z.
Proof.
  unfold Red_clc_i_s; pose_rt; ycrush.
Qed.

Lemma lem_contr_i_s_to_red_i_s : forall x y, Contr_clc_i_s x y -> Red_clc_i_s x y.
Proof.
  unfold Red_clc_i_s; pose_rt; ycrush.
Qed.

Lemma lem_red_i_s_cong_l : forall x y z, Red_clc_i_s x y -> Red_clc_i_s (x @l z) (y @l z).
Proof.
  unfold Red_clc_i_s; intros; induction H.
  unfold Contr_clc_i_s, Contr_clc_i, Contr_clc_s in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_i_s_cong_r : forall x y z, Red_clc_i_s x y -> Red_clc_i_s (z @l x) (z @l y).
Proof.
  unfold Red_clc_i_s; intros; induction H.
  unfold Contr_clc_i_s, Contr_clc_i, Contr_clc_s in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_i_s_ltup_0 : forall x x' y l, Red_clc_i_s x x' -> Red_clc_i_s (ltup x y l) (ltup x' y l).
Proof.
  unfold Red_clc_i_s; intros; induction H.
  unfold Contr_clc_i_s, Contr_clc_i, Contr_clc_s in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_i_s_ltup_1 : forall x y y' l, Red_clc_i_s y y' -> Red_clc_i_s (ltup x y l) (ltup x y' l).
Proof.
  unfold Red_clc_i_s; intros; induction H.
  unfold Contr_clc_i_s, Contr_clc_i, Contr_clc_s in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_i_s_ltup_2 : forall x y z z' l l', Red_clc_i_s z z' ->
                                                 Red_clc_i_s (ltup x y (l ++ z :: l'))
                                                             (ltup x y (l ++ z' :: l')).
Proof.
  unfold Red_clc_i_s; intros; induction H.
  unfold Contr_clc_i_s, Contr_clc_i, Contr_clc_s in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Ltac pose_red_i_s := pose lem_red_i_s_refl; pose lem_red_i_s_trans; pose lem_contr_i_s_to_red_i_s;
                     pose lem_red_i_s_cong_l; pose lem_red_i_s_cong_r;
                     pose lem_red_i_s_ltup_0; pose lem_red_i_s_ltup_1; pose lem_red_i_s_ltup_2.

Ltac cei_crush := unfold Contr_exp_clc_i in *; pose_ctx_l; ycrush.

Lemma lem_contr_exp_i : forall x y, Contr_exp_clc_i x y <-> Contr_clc_i x y \/ Contr_clc_i y x.
Proof.
  yintuition.
  induction H; [ ydestruct t1; ydestruct t2; try yelles 1 | .. ];
    unfold Contr_clc_i; pose_ctx_l; ycrush.
  induction H0; cei_crush.
  induction H0; cei_crush.
Qed.

Lemma lem_contr_exp_i_sym : forall x y, Contr_exp_clc_i x y -> Contr_exp_clc_i y x.
Proof.
  pose lem_contr_exp_i; ycrush.
Qed.
