(* This file contains the definition of the auxiliary system R, and
   the formalisations of lemmas 29, 30, 31. *)

Require Import general.
Require Import iterms.
Require Import central_lemma.

(* definition 28 *)
Definition RootContr_aux t1 t2 :=
  match t1 with
  | C @i z @i x @i y =>
    (z = T /\ t2 = x) \/ (Eqv_clc z F /\ t2 = y) \/ (~(Eqv_clc z F) /\ Eqv_clc x y /\ t2 = x)
  | I @i x => t2 = x
  | K @i x @i y => t2 = x
  | Si @i x @i y @i z =>
    match t2 with
    | x1 @i z1 @i (y1 @i z2) =>  x = x1 /\ y = y1 /\ z = z1 /\ z = z2
    | _ => False
    end
  | _ => False
  end.

Definition Contr_aux := CtxClose_i RootContr_aux.
Definition Red_aux := clos_refl_trans iterm Contr_aux.
Definition Eqv_aux := EqvClose_i RootContr_aux.

Lemma lem_rcontr_aux_to_contr_aux : forall x y, RootContr_aux x y -> Contr_aux x y.
Proof.
  intros; unfold Contr_aux; pose_ctx_i; ycrush.
Qed.

Lemma lem_red_aux_refl : forall x, Red_aux x x.
Proof.
  unfold Red_aux; pose_rt; ycrush.
Qed.

Lemma lem_red_aux_trans : forall x y z, Red_aux x y -> Red_aux y z -> Red_aux x z.
Proof.
  unfold Red_aux; pose_rt; ycrush.
Qed.

Lemma lem_contr_aux_to_red_aux : forall x y, Contr_aux x y -> Red_aux x y.
Proof.
  unfold Red_aux; pose_rt; ycrush.
Qed.

Lemma lem_contr_aux_to_eqv_aux : forall x y, Contr_aux x y -> Eqv_aux x y.
Proof.
  unfold Eqv_aux; intros x y H; induction H; eqv_solve 1.
Qed.

Lemma lem_rcontr_aux_to_red_aux : forall x y, RootContr_aux x y -> Red_aux x y.
Proof.
  auto using lem_rcontr_aux_to_contr_aux, lem_contr_aux_to_red_aux.
Qed.

Lemma lem_red_aux_cong_l : forall x y z, Red_aux x y -> Red_aux (x @i z) (y @i z).
Proof.
  unfold Red_aux; intros; induction H.
  unfold Contr_aux in *; pose_rt; pose_ctx_i; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_aux_cong_r : forall x y z, Red_aux x y -> Red_aux (z @i x) (z @i y).
Proof.
  unfold Red_aux; intros; induction H.
  unfold Contr_aux in *; pose_rt; pose_ctx_i; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_contr_aux_cong_l : forall x y z, Contr_aux x y -> Contr_aux (x @i z) (y @i z).
Proof.
  unfold Contr_aux; intros; induction H; pose_ctx_i; ycrush.
Qed.

Lemma lem_contr_aux_cong_r : forall x y z, Contr_aux x y -> Contr_aux (z @i x) (z @i y).
Proof.
  unfold Contr_aux; intros; induction H; pose_ctx_i; ycrush.
Qed.

Ltac pose_contr_aux := pose lem_contr_aux_cong_l; pose lem_contr_aux_cong_r;
                       pose lem_rcontr_aux_to_contr_aux.

Ltac red_aux_induction z := unfold Red_aux in *; rt_induction z; fold Contr_aux Red_aux in *.

Ltac pose_red_aux := pose lem_red_aux_refl; pose lem_red_aux_trans; pose lem_rcontr_aux_to_red_aux;
                     pose lem_contr_aux_to_red_aux; pose lem_red_aux_cong_l; pose lem_red_aux_cong_r.

Lemma lem_rcontr_aux_to_red_clc : forall x y, RootContr_aux x y -> Red_clc x y.
Proof.
  intros.
  ydestruct x; yisolve.
  ydestruct x1; yisolve.
  rc0_crush.
  ydestruct x1_1; yisolve.
  rc0_crush.
  ydestruct x1_1_1; yisolve.
  yintuition.
  rc0_crush.
  assert (Red_clc x1_1_2 F) by auto using lem_central_lemma.
  assert (Red_clc (C @i F @i x1_2 @i x2) x2) by rc0_crush.
  pose_red_clc; ycrush.
  assert (Eqv_clc0 x1_2 x2).
  pose lem_eqv_clc_to_eqv_clc0; ycrush.
  apply lem_contr_clc_to_red_clc; apply lem_contr_clc_to_1.
  assert (RootContr_clc_n 1 (C @i x1_1_2 @i x1_2 @i x2) x1_2).
  unfold Eqv_clc0, RootContr_clc0 in *; ycrush.
  unfold Contr_clc_n; pose_ctx_i; ycrush.
  rc0_crush.
Qed.

(* lemma 30 *)
Lemma lem_contr_aux_to_red_clc : forall x y, Contr_aux x y -> Red_clc x y.
Proof.
  intros x y H; induction H.
  pose lem_rcontr_aux_to_red_clc; ycrush.
  pose_red_clc; ycrush.
  pose_red_clc; ycrush.
Qed.

Lemma lem_red_aux_to_red_clc : forall x y, Red_aux x y -> Red_clc x y.
Proof.
  intros x y H; induction H.
  pose lem_contr_aux_to_red_clc; ycrush.
  pose_red_clc; ycrush.
  pose_red_clc; ycrush.
Qed.

Lemma lem_rcontr_clc0_to_rcontr_aux : forall x y, RootContr_clc0 x y -> RootContr_aux x y.
Proof.
  intros.
  ydestruct x; yisolve.
  ydestruct x1; yisolve.
  ydestruct x1_1; yisolve.
  ydestruct x1_1_1; yisolve.
  unfold RootContr_clc0 in *; simpl in *; yintuition.
  assert (Eqv_clc y y) by eqv_solve 1.
  tauto.
Qed.

(* lemma 29 *)
Lemma lem_contr_clc0_to_contr_aux : forall x y, Contr_clc0 x y -> Contr_aux x y.
Proof.
  intros x y H; induction H.
  apply lem_rcontr_aux_to_contr_aux; apply lem_rcontr_clc0_to_rcontr_aux; ycrush.
  pose_contr_aux; ycrush.
  pose_contr_aux; ycrush.
Qed.

Lemma lem_red_clc0_to_red_aux : forall x y, Red_clc0 x y -> Red_aux x y.
Proof.
  intros x y H; induction H.
  apply lem_contr_aux_to_red_aux; apply lem_contr_clc0_to_contr_aux; ycrush.
  ycrush.
  pose_red_aux; ycrush.
Qed.

Lemma lem_eqv_clc0_to_eqv_aux : forall x y, Eqv_clc0 x y -> Eqv_aux x y.
Proof.
  intros x y H; induction H; fold Contr_clc0 in *.
  apply lem_contr_aux_to_eqv_aux; apply lem_contr_clc0_to_contr_aux; ycrush.
  ycrush.
  unfold Eqv_aux in *; eqv_solve 1.
  unfold Eqv_aux in *; eqv_solve 1.
Qed.

Lemma lem_eqv_clc_to_eqv_aux : forall x y, Eqv_clc x y -> Eqv_aux x y.
Proof.
  auto using lem_eqv_clc0_to_eqv_aux, lem_eqv_clc_to_eqv_clc0.
Qed.

Inductive Par_aux : iterm -> iterm -> Prop :=
| par_aux_base : forall x y, RootContr_aux x y -> Par_aux x y
| par_aux_eq : forall x, Par_aux x x
| par_aux_app : forall x x' y y', Par_aux x x' -> Par_aux y y' -> Par_aux (x @i y) (x' @i y').

Ltac pose_par_aux := pose par_aux_base; pose par_aux_eq; pose par_aux_app.

Lemma lem_contr_aux_to_par_aux : forall x y, Contr_aux x y -> Par_aux x y.
Proof.
  intros x y H; induction H; pose_par_aux; ycrush.
Qed.

Lemma lem_par_aux_to_red_aux : forall x y, Par_aux x y -> Red_aux x y.
Proof.
  intros x y H; induction H; pose_red_aux; ycrush.
Qed.

Lemma lem_par_aux_rcontr :
  forall x y, Par_aux x y -> forall z, RootContr_aux x z ->
                                       exists u, Par_aux y u /\ Par_aux z u.
Proof.
  intros x y H; induction H.
  intros.
  ydestruct x; yisolve.
  ydestruct x1; yisolve.
  ycrush.
  ydestruct x1_1; yisolve.
  ycrush.
  ydestruct x1_1_1; yisolve.
  yintuition; yisolve.
  pose cor_t_not_f; ycrush.
  pose cor_t_not_f; ycrush.
  ycrush.
  pose_par_aux; ycrush.
  intros.
  ydestruct x; yisolve.
  yinversion H; yisolve.
  pose_par_aux; ycrush.
  ydestruct x1; yisolve.
  yinversion H; yisolve.
  pose_par_aux; ycrush.
  yinversion H4; yisolve.
  pose_par_aux; ycrush.
  ydestruct x1_1; yisolve.
  yinversion H; yisolve.
  yintuition; yisolve.
  assert (RootContr_aux (C @i T @i x2 @i y') x2) by ycrush.
  pose_par_aux; ycrush.
  assert (RootContr_aux (C @i x1_2 @i x2 @i y') y') by ycrush.
  pose_par_aux; ycrush.
  assert (RootContr_aux (C @i x1_2 @i x2 @i y') x2).
  assert (Eqv_clc x2 y').
  assert (Eqv_clc y y').
  pose lem_par_aux_to_red_aux; pose lem_red_aux_to_red_clc; pose lem_red_clc_to_eqv_clc; ycrush.
  unfold Eqv_clc in *; eqv_solve 1.
  ycrush.
  pose_par_aux; ycrush.
  yinversion H4; yisolve.
  yintuition; yisolve.
  assert (RootContr_aux (C @i T @i y'0 @i y') y'0) by ycrush.
  pose_par_aux; ycrush.
  assert (RootContr_aux (C @i x1_2 @i y'0 @i y') y') by ycrush.
  pose_par_aux; ycrush.
  assert (Eqv_clc y'0 y').
  assert (Eqv_clc y y').
  pose lem_par_aux_to_red_aux; pose lem_red_aux_to_red_clc; pose lem_red_clc_to_eqv_clc; ycrush.
  assert (Eqv_clc x2 y'0).
  pose lem_par_aux_to_red_aux; pose lem_red_aux_to_red_clc; pose lem_red_clc_to_eqv_clc; ycrush.
  unfold Eqv_clc in *; eauto using eqv_sym, eqv_trans.
  assert (RootContr_aux (C @i x1_2 @i y'0 @i y') y'0) by ycrush.
  pose_par_aux; ycrush.
  yinversion H3; yisolve.
  yintuition.
  yinversion H7; yisolve.
  assert (RootContr_aux (C @i T @i y'0 @i y') y'0) by ycrush.
  pose_par_aux; ycrush.
  assert (Eqv_clc y'1 F).
  assert (Eqv_clc x1_2 y'1).
  pose lem_par_aux_to_red_aux; pose lem_red_aux_to_red_clc; pose lem_red_clc_to_eqv_clc; ycrush.
  unfold Eqv_clc in *; eauto using eqv_sym, eqv_trans.
  assert (RootContr_aux (C @i y'1 @i y'0 @i y') y') by ycrush.
  pose_par_aux; ycrush.
  assert (Eqv_clc y'0 y').
  assert (Eqv_clc y y').
  pose lem_par_aux_to_red_aux; pose lem_red_aux_to_red_clc; pose lem_red_clc_to_eqv_clc; ycrush.
  assert (Eqv_clc x2 y'0).
  pose lem_par_aux_to_red_aux; pose lem_red_aux_to_red_clc; pose lem_red_clc_to_eqv_clc; ycrush.
  unfold Eqv_clc in *; eauto using eqv_sym, eqv_trans.
  assert (~(Eqv_clc y'1 F)).
  unfold not; intro HH.
  assert (Eqv_clc x1_2 y'1).
  pose lem_par_aux_to_red_aux; pose lem_red_aux_to_red_clc; pose lem_red_clc_to_eqv_clc; ycrush.
  unfold Eqv_clc in *; eqv_solve 1.
  assert (RootContr_aux (C @i y'1 @i y'0 @i y') y'0) by ycrush.
  pose_par_aux; ycrush.
  ydestruct z; yisolve.
  ydestruct z1; yisolve.
  ydestruct z2; yisolve.
  simpl in *; simp_hyps; subst.
  yinversion H; yisolve.
  assert (RootContr_aux (Si @i z1_1 @i z2_1 @i y') (z1_1 @i y' @i (z2_1 @i y'))) by ycrush.
  exists (z1_1 @i y' @i (z2_1 @i y')).
  pose_par_aux; ycrush.
  yinversion H3; yisolve.
  assert (RootContr_aux (Si @i z1_1 @i y'0 @i y') (z1_1 @i y' @i (y'0 @i y'))) by ycrush.
  exists (z1_1 @i y' @i (y'0 @i y')).
  pose_par_aux; ycrush.
  yinversion H2; yisolve.
  assert (RootContr_aux (Si @i y'1 @i y'0 @i y') (y'1 @i y' @i (y'0 @i y'))) by ycrush.
  exists (y'1 @i y' @i (y'0 @i y')).
  pose_par_aux; ycrush.
Qed.

Lemma lem_par_aux_confluent : forall x y z, Par_aux x y -> Par_aux x z ->
                                            exists u, Par_aux y u /\ Par_aux z u.
Proof.
  induction x.
  intros; exists C; ycrush.
  intros; exists T; ycrush.
  intros; exists F; ycrush.
  intros; exists I; ycrush.
  intros; exists K; ycrush.
  intros; exists Si; ycrush.
  intros; exists (var n); ycrush.
  intros.
  yinversion H.
  assert (exists u : iterm, Par_aux z u /\ Par_aux y u).
  eapply lem_par_aux_rcontr; ycrush.
  ycrush.
  pose_par_aux; ycrush.
  yinversion H0.
  eapply lem_par_aux_rcontr with (x := (x1 @i x2)); pose_par_aux; ycrush.
  pose_par_aux; ycrush.
  assert (exists u : iterm, Par_aux x' u /\ Par_aux x'0 u) by ycrush.
  assert (exists u : iterm, Par_aux y' u /\ Par_aux y'0 u) by ycrush.
  pose_par_aux; ycrush.
Qed.

Lemma lem_aux_commute : forall x y z, Par_aux x y -> Red_aux x z ->
                                      exists u, Red_aux y u /\ Par_aux z u.
Proof.
  assert (forall x z, Red_aux x z -> forall y, Par_aux x y ->
                                               exists u, Red_aux y u /\ Par_aux z u).
  intros x z H; induction H; fold Red_aux in *.
  intros.
  assert (exists u, Par_aux y0 u /\ Par_aux y u).
  pose lem_par_aux_confluent; pose lem_contr_aux_to_par_aux; ycrush.
  pose lem_par_aux_to_red_aux; ycrush.
  pose_red_aux; ycrush.
  pose_red_aux; ycrush.
  ycrush.
Qed.

(* lemma 31 *)
Lemma lem_aux_confluent : forall x y z, Red_aux x y -> Red_aux x z ->
                                        exists u, Red_aux y u /\ Red_aux z u.
Proof.
  assert (forall x y, Red_aux x y -> forall z, Red_aux x z ->
                                               exists u, Red_aux y u /\ Red_aux z u).
  intros x y H; induction H; fold Contr_aux Red_aux in *.
  pose lem_aux_commute; pose lem_contr_aux_to_par_aux; pose lem_par_aux_to_red_aux; ycrush.
  ycrush.
  pose_red_aux; ycrush.
  ycrush.
Qed.

Lemma lem_aux_cr : forall x y, Eqv_aux x y -> exists u, Red_aux x u /\ Red_aux y u.
Proof.
  intros x y H; induction H; fold Contr_aux Red_aux in *.
  pose_red_aux; ycrush.
  pose_red_aux; ycrush.
  pose_red_aux; ycrush.
  simp_hyps.
  assert (exists u, Red_aux x1 u /\ Red_aux x0 u).
  pose lem_aux_confluent; ycrush.
  pose_red_aux; ycrush.
Qed.
