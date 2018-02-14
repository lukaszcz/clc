(* This file contains the formalisation of the basic properties of the
   systems CL-pc, CL-pc^1 and CL-pc^L, including lemma 2 *)

Require Import general.
Require Export basic_defs.

Hint Unfold RootContr_clc0 Contr_clc0 Eqv_clc0 : unfold_hints.
Hint Unfold RootContr_clc Contr_clc Eqv_clc : unfold_hints.
Hint Unfold RootContr_clc_plus Eqv_clc_plus : unfold_hints.

Ltac pose_ctx_i := pose close_ibase; pose close_iapp_l; pose close_iapp_r.

Ltac eqv_tac n := unfold EqvClose_i in *; pose_rst; simp_hyps; yelles n.
Ltac ctx_eqv_tac n := pose_ctx_i; eqv_tac n.

(***********************************************************************************)
(* lemmas *)

Lemma lem_contr_clc0_implies_eqv_clc0 : forall x y, Contr_clc0 x y -> Eqv_clc0 x y.
Proof.
  unfold Contr_clc0; unfold Eqv_clc0; pose_rt; pose_rst; ycrush.
Qed.

Lemma lem_contr_clc_implies_eqv_clc : forall x y, Contr_clc x y -> Eqv_clc x y.
Proof.
  unfold Contr_clc; unfold Eqv_clc; pose_rt; pose_rst; ycrush.
Qed.

Lemma ctx_closure :
  forall (R Q : iterm -> iterm -> Prop),
    (forall x y, R x y -> Q x y) ->
    (forall x y, CtxClose_i R x y -> CtxClose_i Q x y).
Proof.
  intros R Q H.
  pose (@close_ibase Q); pose (@close_iapp_l Q); pose (@close_iapp_r Q).
  induction x; yelles 2.
Qed.

Lemma eqv_closure :
  forall (R Q : iterm -> iterm -> Prop),
    (forall x y, R x y -> Q x y) ->
    (forall x y, EqvClose_i R x y -> EqvClose_i Q x y).
Proof.
  intros.
  pose (ctx_closure R Q).
  induction H0; eqv_tac 1.
Qed.

Lemma eqv_trans : forall R x y z, EqvClose_i R x y -> EqvClose_i R y z -> EqvClose_i R x z.
Proof.
  eqv_tac 1.
Qed.

Lemma eqv_sym : forall R x y, EqvClose_i R x y -> EqvClose_i R y x.
Proof.
  eqv_tac 1.
Qed.

Lemma eqv_refl : forall R x, EqvClose_i R x x.
Proof.
  eqv_tac 1.
Qed.

Ltac eqv_tac_0 n := pose eqv_sym; pose eqv_trans; pose eqv_refl; yauto n.

Lemma eqv_lift : forall (R : iterm -> iterm -> Prop) x y, R x y -> EqvClose_i R x y.
Proof.
  pose_ctx_i; eqv_tac 1.
Qed.

Lemma eqv_cong_l :
  forall (R : iterm -> iterm -> Prop) x x' y,
    EqvClose_i R x x' -> EqvClose_i R (x @i y) (x' @i y).
Proof.
  intros.
  induction H; pose_ctx_i; eqv_tac 1.
Qed.

Lemma eqv_cong_r :
  forall (R : iterm -> iterm -> Prop) x y y',
    EqvClose_i R y y' -> EqvClose_i R (x @i y) (x @i y').
Proof.
  intros.
  induction H; pose_ctx_i; eqv_tac 1.
Qed.

Lemma ctx_eqv_collapse :
  forall (R : iterm -> iterm -> Prop) x y,
    CtxClose_i (EqvClose_i R) x y -> EqvClose_i R x y.
Proof.
  induction x; try eqv_tac 1.
  pose eqv_cong_l; pose eqv_cong_r; yelles 2.
Qed.

Lemma eqv_collapse :
  forall (R : iterm -> iterm -> Prop) x y,
    EqvClose_i (EqvClose_i R) x y -> EqvClose_i R x y.
Proof.
  intros.
  pose ctx_eqv_collapse.
  induction H; eqv_tac 1.
Qed.

Ltac eqv_solve n :=
  pose eqv_sym; pose eqv_trans; pose eqv_refl;
  pose eqv_lift; pose eqv_cong_l; pose eqv_cong_r; pose eqv_collapse; yauto n.

Ltac eqv_eauto :=
  pose eqv_sym; pose eqv_trans; pose eqv_refl;
  pose eqv_lift; pose eqv_cong_l; pose eqv_cong_r; pose eqv_collapse; eauto with yhints.

Lemma contr_to_eqv : forall R x y, CtxClose_i R x y -> EqvClose_i R x y.
Proof.
  eqv_tac 1.
Qed.

Lemma contr_clc_n_subset : forall n x y, RootContr_clc_n 0 x y -> RootContr_clc_n n x y.
Proof.
  induction n; yelles 2.
Qed.

Lemma lem_rcontr_clc0_implies_rcontr_clc : forall x y, RootContr_clc0 x y -> RootContr_clc x y.
Proof.
  pose contr_clc_n_subset; unfold RootContr_clc in *; yelles 1.
Qed.

Lemma lem_contr_clc0_implies_contr_clc : forall x y, Contr_clc0 x y -> Contr_clc x y.
Proof.
  pose lem_rcontr_clc0_implies_rcontr_clc.
  pose ctx_closure.
  unfold Contr_clc0, Contr_clc; ycrush.
Qed.

Lemma lem_eqv_clc0_implies_eqv_clc : forall x y, Eqv_clc0 x y -> Eqv_clc x y.
Proof.
  unfold Eqv_clc, Eqv_clc0.
  pose lem_rcontr_clc0_implies_rcontr_clc.
  pose (eqv_closure RootContr_clc0 RootContr_clc).
  pose (contr_to_eqv RootContr_clc0).
  auto.
Qed.

Lemma lem_rcontr_clc0_inversion :
  forall t1 t2, RootContr_clc0 t1 t2 ->
                (exists x y, t1 = C @i T @i x @i y /\ t2 = x) \/
                (exists x y, t1 = C @i F @i x @i y /\ t2 = y) \/
                (exists x y z, t1 = C @i z @i x @i y /\ t2 = x /\ x = y) \/
                (exists x, t1 = I @i x /\ t2 = x) \/
                (exists x y, t1 = K @i x @i y /\ t2 = x) \/
                (exists x y z, t1 = Si @i x @i y @i z /\ t2 = x @i z @i (y @i z)).
Proof.
  unfold RootContr_clc0; intros; ydestruct t1; simpl in *; yisolve.
Qed.

Ltac invert_rcontr_clc0 :=
  repeat match goal with
         | [ H : (RootContr_clc0 ?x ?y) |- ?G ] =>
           generalize (lem_rcontr_clc0_inversion x y H); yintro; clear H
         end.

Lemma contr_clc_base_closure :
  (forall (R Q : iterm -> iterm -> Prop) x y, (forall x y, R x y -> Q x y) ->
                                              RootContr_clc_base R x y -> RootContr_clc_base Q x y).
Proof.
  intros; unfold RootContr_clc_base; ydestruct x; yelles 1.
Qed.

Lemma contr_clc_to_contr_clc_plus : forall x y, RootContr_clc x y -> RootContr_clc_plus x y.
Proof.
  pose contr_clc_base_closure.
  assert (forall R x y, RootContr_clc_base R x y -> RootContr_clc_bp R x y).
  unfold RootContr_clc_bp; auto.
  assert (forall n x y, RootContr_clc_n n x y -> RootContr_clc_plus_n n x y).
  induction n.
  simpl; auto.
  pose (eqv_closure (RootContr_clc_n n) (RootContr_clc_plus_n n)); yelles 1.
  unfold RootContr_clc_plus in *; yelles 1.
Qed.

Lemma eqv_clc_to_eqv_clc_plus : forall x y, Eqv_clc x y -> Eqv_clc_plus x y.
Proof.
  unfold Eqv_clc, Eqv_clc_plus.
  pose contr_clc_to_contr_clc_plus.
  pose eqv_closure.
  eauto.
Qed.

Ltac ctx_i_yauto n := pose_ctx_i; autounfold with unfold_hints in *; yauto n.

Lemma contr_clc_plus_level :
  forall x y, CtxClose_i RootContr_clc_plus x y <-> exists n, CtxClose_i (RootContr_clc_plus_n n) x y.
Proof.
  intros; unfold iff; split; generalize y; clear y.
  induction x; try ctx_i_yauto 1.
  destruct y; try ctx_i_yauto 1.
  intro H.
  yinversion H.
  pose_ctx_i; yelles 1.
  assert (exists n : nat, CtxClose_i (RootContr_clc_plus_n n) x1 y1); ctx_i_yauto 1.
  assert (exists n : nat, CtxClose_i (RootContr_clc_plus_n n) x2 y2); ctx_i_yauto 1.
  (* the other direction *)
  induction x; try ctx_i_yauto 2.
  yintros.
  yinversion H; ctx_i_yauto 4.
Qed.

Lemma contr_clc_bp_closure :
  forall (R Q : iterm -> iterm -> Prop), (forall x y, R x y -> Q x y) ->
                                         forall x y, RootContr_clc_bp R x y -> RootContr_clc_bp Q x y.
Proof.
  pose contr_clc_base_closure; unfold RootContr_clc_bp; intros; yelles 2.
Qed.

Lemma contr_clc_plus_n_inc :
  forall n x y, RootContr_clc_plus_n n x y -> RootContr_clc_plus_n (S n) x y.
Proof.
  induction n; simpl in *.
  assert (forall x y, x = y -> EqvClose_i (RootContr_clc_bp eq) x y).
  pose ctx_closure; eqv_tac 1.
  pose contr_clc_bp_closure; yelles 1.
  pose contr_clc_bp_closure; pose eqv_closure.
  assert (forall x y, EqvClose_i (RootContr_clc_plus_n n) x y ->
                      EqvClose_i (RootContr_clc_bp (EqvClose_i (RootContr_clc_plus_n n))) x y) by yelles 1.
  yelles 1.
Qed.

Lemma contr_clc_plus_n_ge :
  forall x y n m, RootContr_clc_plus_n n x y -> m >= n -> RootContr_clc_plus_n m x y.
Proof.
  induction m.
  yelles 1.
  intros.
  assert (S m = n \/ m >= n).
  Reconstr.hobvious (@H0)
		    (@Coq.Arith.PeanoNat.Nat.le_succ_r, @Coq.Arith.PeanoNat.Nat.le_0_l, @Coq.Arith.PeanoNat.Nat.lt_succ_r, @Coq.Arith.PeanoNat.Nat.lt_0_succ, @CtxClose_i_ind, @Coq.Init.Datatypes.nat_ind, @Coq.Arith.PeanoNat.Nat.lt_eq_cases)
		    (@Coq.Init.Peano.ge).
  pose contr_clc_plus_n_inc; yauto 1.
Qed.

Lemma contr_clc_plus_n_max :
  forall x y n m, RootContr_clc_plus_n n x y \/ RootContr_clc_plus_n m x y ->
                  RootContr_clc_plus_n (max n m) x y.
Proof.
  Reconstr.hsimple Reconstr.Empty
		   (@Coq.Arith.PeanoNat.Nat.max_spec_le, @contr_clc_plus_n_ge, @Coq.Arith.PeanoNat.Nat.max_r_iff, @Coq.Arith.PeanoNat.Nat.max_l)
		   (@Coq.Init.Peano.ge).
Qed.

Lemma eqv_clc_plus_level :
  forall x y, Eqv_clc_plus x y <-> exists n, EqvClose_i (RootContr_clc_plus_n n) x y.
Proof.
  generalize contr_clc_plus_level.
  intros; unfold iff; split.
  unfold Eqv_clc_plus; intro.
  induction H0; try yauto 1.
  assert (exists n : nat, CtxClose_i (RootContr_clc_plus_n n) x y) by yelles 1.
  eqv_tac 1.
  eqv_tac 1.
  clear -IHclos_refl_sym_trans1 IHclos_refl_sym_trans2.
  simp_hyps.
  exists (max x0 x1).
  assert (forall x y, RootContr_clc_plus_n x0 x y -> RootContr_clc_plus_n (max x0 x1) x y).
  Reconstr.hobvious Reconstr.Empty
		(@contr_clc_plus_n_max, @Coq.Arith.PeanoNat.Nat.max_comm)
		Reconstr.Empty.
  assert (forall x y, RootContr_clc_plus_n x1 x y -> RootContr_clc_plus_n (max x0 x1) x y).
  Reconstr.hobvious Reconstr.Empty
		(@contr_clc_plus_n_max, @Coq.Arith.PeanoNat.Nat.max_comm)
		Reconstr.Empty.
  pose eqv_closure.
  assert (EqvClose_i (RootContr_clc_plus_n (max x0 x1)) y z) by yelles 1.
  assert (EqvClose_i (RootContr_clc_plus_n (max x0 x1)) x y) by yelles 1.
  eqv_tac 1.
  (* the other direction *)
  unfold Eqv_clc_plus; pose eqv_closure; ctx_i_yauto 2.
Qed.

Lemma contr_clc0_eqv_compose : forall x y z, RootContr_clc0 x y -> Eqv_clc0 y z -> Eqv_clc0 x z.
Proof.
  unfold Eqv_clc0.
  pose (eqv_lift RootContr_clc0).
  pose (eqv_trans RootContr_clc0).
  yelles 1.
Qed.

Lemma lem_eqv_cond_l : forall x y z, Eqv_clc0 x y -> Eqv_clc0 (C @i z @i x @i y) x.
Proof.
  intros.
  assert (RootContr_clc0 (C @i z @i x @i x) x).
  unfold RootContr_clc0; simpl; yelles 1.
  unfold Eqv_clc0 in *.
  eauto using eqv_lift, eqv_trans, eqv_sym, eqv_cong_l, eqv_cong_r.
Qed.

Lemma lem_eqv_cond_r : forall x y z, Eqv_clc0 x y -> Eqv_clc0 (C @i z @i x @i y) y.
Proof.
  intros.
  assert (RootContr_clc0 (C @i z @i y @i y) y).
  unfold RootContr_clc0; simpl; yelles 1.
  unfold Eqv_clc0 in *.
  eauto using eqv_lift, eqv_trans, eqv_sym, eqv_cong_l, eqv_cong_r.
Qed.

Lemma eqv_s : forall x y z, Eqv_clc0 (Si @i x @i y @i z) (x @i z @i (y @i z)).
Proof.
  unfold Eqv_clc0.
  unfold RootContr_clc0.
  simpl.
  intros.
  assert (RootContr_clc_base eq (Si @i x @i y @i z) (x @i z @i (y @i z))).
  now unfold RootContr_clc_base.
  auto using eqv_lift.
Qed.

Lemma contr_clc_plus_to_eqv_clc0 : forall n x y, RootContr_clc_plus_n n x y -> Eqv_clc0 x y.
Proof.
  unfold Eqv_clc0, RootContr_clc0.
  induction n; simpl in *.
  assert (forall x y, RootContr_clc_bp eq x y -> RootContr_clc_base eq x y).
  induction x; unfold RootContr_clc_bp; yelles 1.
  pose eqv_lift; yelles 1.
  unfold RootContr_clc_bp.
  yintros.
  destruct x; try eqv_tac 1; try yauto 1.
  yinversion H.
  simpl in H0.
  destruct x1; try eqv_tac 1.
  subst; apply rst_step; apply close_ibase; ycrush.
  destruct x1_1; try ctx_eqv_tac 1.
  destruct x1_1_1; try eqv_tac 1.
  ydestruct H0; simp_hyps; try subst.
  apply rst_step; apply close_ibase; ycrush.
  ydestruct H; simp_hyps; try subst.
  apply rst_step; apply close_ibase; ycrush.
  pose lem_eqv_cond_l; unfold Eqv_clc0 in *; unfold RootContr_clc0 in *; simpl in *;    
     pose eqv_collapse; pose eqv_closure; yelles 2.
  destruct y; isolve; try eqv_tac 1.
  pose eqv_s; unfold Eqv_clc0 in *; unfold RootContr_clc0 in *; simpl in *; yelles 1.
  destruct x1; isolve.
  pose lem_eqv_cond_l; unfold Eqv_clc0 in *; unfold RootContr_clc0 in *; simpl in *.
  assert (EqvClose_i (RootContr_clc_base eq) (C @i x1_1_2 @i x1_2 @i y) x1_2);
    pose eqv_collapse; pose eqv_closure; pose eqv_trans; yelles 2.
Qed.

Lemma clc_plus_to_clc0 : forall x y, Eqv_clc_plus x y -> Eqv_clc0 x y.
Proof.
  intros.
  assert (exists n, EqvClose_i (RootContr_clc_plus_n n) x y).
  Reconstr.htrivial (@H)
		    (@eqv_clc_plus_level)
		    Reconstr.Empty.
  clear H.
  destruct H0.
  generalize x y H; clear x y H.
  pose contr_clc_plus_to_eqv_clc0.
  pose eqv_closure.
  pose eqv_collapse.
  unfold Eqv_clc0 in *; unfold RootContr_clc0 in *.
  eauto.
Qed.

Lemma lem_eqv_clc_to_eqv_clc0 : forall x y, Eqv_clc x y -> Eqv_clc0 x y.
Proof.
  eauto using eqv_clc_to_eqv_clc_plus, clc_plus_to_clc0.
Qed.

Lemma lem_rcontr_clc_to_rcontr_clc_1 : forall x y, RootContr_clc x y -> RootContr_clc_n 1 x y.
Proof.
  unfold RootContr_clc.
  yintros.
  move x0 after x.
  generalizing.
  induction x0.
  ycrush.
  yintros; simpl in *.
  ydestruct x; try ycrush.
  ydestruct x1; try ycrush.
  ydestruct x1_1; try ycrush.
  ydestruct x1_1_1; try ycrush.
  Ltac mytac n :=
      pose (HH := eqv_closure (RootContr_clc_n n) RootContr_clc);
      pose lem_eqv_clc_to_eqv_clc0; unfold Eqv_clc, Eqv_clc0, RootContr_clc0 in *;
      unfold RootContr_clc in HH; simpl in *;
      ycrush.
  ydestruct x1_1_2; try mytac x0.
Qed.

Lemma lem_contr_clc_to_1 : forall x y, Contr_clc x y <-> Contr_clc_n 1 x y.
Proof.
  intros; split.
  intro H.
  induction H.
  assert (RootContr_clc_n 1 t1 t2) by auto using lem_rcontr_clc_to_rcontr_clc_1.
  unfold Contr_clc_n; pose_ctx_i; ycrush.
  unfold Contr_clc_n in *; pose_ctx_i; ycrush.
  unfold Contr_clc_n in *; pose_ctx_i; ycrush.
  (* the other direction *)
  intro H.
  induction H.
  unfold Contr_clc, RootContr_clc.
  assert (exists n, RootContr_clc_n n t1 t2) by ycrush.
  pose_ctx_i; ycrush.
  unfold Contr_clc in *; pose_ctx_i; ycrush.
  unfold Contr_clc in *; pose_ctx_i; ycrush.
Qed.

Lemma lem_rcontr_clc_to_contr_clc : forall x y, RootContr_clc x y -> Contr_clc x y.
Proof.
  intros; unfold Contr_clc; pose_ctx_i; ycrush.
Qed.

Lemma lem_red_clc_refl : forall x, Red_clc x x.
Proof.
  unfold Red_clc; pose_rt; ycrush.
Qed.

Lemma lem_red_clc_trans : forall x y z, Red_clc x y -> Red_clc y z -> Red_clc x z.
Proof.
  unfold Red_clc; pose_rt; ycrush.
Qed.

Lemma lem_contr_clc_to_red_clc : forall x y, Contr_clc x y -> Red_clc x y.
Proof.
  unfold Red_clc; pose_rt; ycrush.
Qed.

Lemma lem_contr_clc_to_eqv_clc : forall x y, Contr_clc x y -> Eqv_clc x y.
Proof.
  intros x y H; induction H; unfold Eqv_clc in *; eqv_solve 1.
Qed.

Lemma lem_red_clc_to_eqv_clc : forall x y, Red_clc x y -> Eqv_clc x y.
Proof.
  intros x y H; induction H.
  apply lem_contr_clc_to_eqv_clc; ycrush.
  unfold Eqv_clc in *; eqv_solve 1.
  unfold Eqv_clc in *; eqv_solve 1.
Qed.

Lemma lem_rcontr_clc_to_red_clc : forall x y, RootContr_clc x y -> Red_clc x y.
Proof.
  auto using lem_rcontr_clc_to_contr_clc, lem_contr_clc_to_red_clc.
Qed.

Lemma lem_red_clc_cong_l : forall x y z, Red_clc x y -> Red_clc (x @i z) (y @i z).
Proof.
  unfold Red_clc; intros; induction H.
  unfold Contr_clc in *; pose_rt; pose_ctx_i; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_clc_cong_r : forall x y z, Red_clc x y -> Red_clc (z @i x) (z @i y).
Proof.
  unfold Red_clc; intros; induction H.
  unfold Contr_clc in *; pose_rt; pose_ctx_i; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_contr_clc_cong_l : forall x y z, Contr_clc x y -> Contr_clc (x @i z) (y @i z).
Proof.
  unfold Contr_clc; intros; induction H; pose_ctx_i; ycrush.
Qed.

Lemma lem_contr_clc_cong_r : forall x y z, Contr_clc x y -> Contr_clc (z @i x) (z @i y).
Proof.
  unfold Contr_clc; intros; induction H; pose_ctx_i; ycrush.
Qed.

Ltac pose_contr_clc := pose lem_contr_clc_cong_l; pose lem_contr_clc_cong_r;
                       pose lem_rcontr_clc_to_contr_clc.

Ltac red_clc_induction z := unfold Red_clc in *; rt_induction z; fold Contr_clc Red_clc in *.

Ltac pose_red_clc := pose lem_red_clc_refl; pose lem_red_clc_trans; pose lem_rcontr_clc_to_red_clc;
                     pose lem_contr_clc_to_red_clc; pose lem_red_clc_cong_l; pose lem_red_clc_cong_r.

Ltac rc0_crush := apply lem_rcontr_clc_to_red_clc; apply lem_rcontr_clc0_implies_rcontr_clc; ycrush.
