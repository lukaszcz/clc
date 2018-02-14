(* This file contains the definition of a-contraction/reduction and
   the formalisation of its basic properties, including lemma 17 *)

Require Import general.
Require Import iterms.
Require Import lterms.
Require Import erase_facts.
Require Import subterms.
Require Import standard.
Require Import ired.
Require Import sred.
Require Import svars.

Definition RootContr_clc_a t1 t2 :=
  Sterm t2 /\
  match t1 with
  | C1 @l T1 @l x @l q => is_iterm q = true /\ t2 = x
  | C1 @l F1 @l q @l x => is_iterm q = true /\ t2 = x
  | C2 @l q @l x @l y => is_iterm q = true /\ Red_clc_s t2 x /\ Red_clc_s t2 y
  | I1 @l x => t2 = x
  | K1 @l x @l q => is_iterm q = true /\ t2 = x
  | _ => RootContr_S t1 t2
  end.

Definition Contr_clc_a := CtxClose_l RootContr_clc_a.
Definition Red_clc_a := clos_refl_trans lterm Contr_clc_a.

Definition Contr_clc_i_a x y := Contr_clc_i x y \/ Contr_clc_a x y.
Definition Red_clc_i_a := clos_refl_trans lterm Contr_clc_i_a.

Lemma rcontr_clc_a_inversion :
  forall t1 t2, RootContr_clc_a t1 t2 -> Sterm t2 /\
                ((exists x y, t1 = C1 @l T1 @l x @l y /\ t2 = x /\ is_iterm y = true) \/
                 (exists x y, t1 = C1 @l F1 @l x @l y /\ t2 = y /\ is_iterm x = true) \/
                 (exists x y z, t1 = C2 @l z @l x @l y /\ Red_clc_s t2 x /\
                                Red_clc_s t2 y /\ is_iterm z = true) \/
                 (t1 = I1 @l t2) \/
                 (exists x y, t1 = K1 @l x @l y /\ t2 = x /\ is_iterm y = true) \/
                 RootContr_S t1 t2).
Proof.
  intros; unfold RootContr_clc_a in H; simp_hyps; ydestruct t1; yisolve; yelles 1.
Qed.

Ltac invert_rcontr_clc_a :=
  repeat match goal with
         | [ H : (RootContr_clc_a ?x ?y) |- ?G ] =>
           generalize (rcontr_clc_a_inversion x y H); yintro; clear H
         end.

Ltac racrush := unfold RootContr_clc_a in *; pose lem_standard_sterm; pose_red_s; ycrush.

Lemma lem_rcontr_a_to_contr_a : forall x y, RootContr_clc_a x y -> Contr_clc_a x y.
Proof.
  unfold Contr_clc_a; pose_ctx_l; ycrush.
Qed.

Lemma lem_contr_a_cong_l : forall x y z, Contr_clc_a x y -> Contr_clc_a (x @l z) (y @l z).
Proof.
  unfold Contr_clc_a; intros; induction H; pose_ctx_l; ycrush.
Qed.

Lemma lem_contr_a_cong_r : forall x y z, Contr_clc_a x y -> Contr_clc_a (z @l x) (z @l y).
Proof.
  unfold Contr_clc_a; intros; induction H; pose_ctx_l; ycrush.
Qed.

Lemma lem_contr_a_ltup_0 : forall x x' y l, Contr_clc_a x x' ->
                                            Contr_clc_a (ltup x y l) (ltup x' y l).
Proof.
  unfold Contr_clc_a; intros; induction H; pose_ctx_l; ycrush.
Qed.

Lemma lem_contr_a_ltup_1 : forall x y y' l, Contr_clc_a y y' ->
                                            Contr_clc_a (ltup x y l) (ltup x y' l).
Proof.
  unfold Contr_clc_a; intros; induction H; pose_ctx_l; ycrush.
Qed.

Lemma lem_contr_a_ltup_2 : forall x y z z' l l', Contr_clc_a z z' ->
                                                 Contr_clc_a (ltup x y (l ++ z :: l'))
                                                             (ltup x y (l ++ z' :: l')).
Proof.
  unfold Contr_clc_a; intros; induction H; pose_ctx_l; ycrush.
Qed.

Ltac pose_contr_a := pose lem_contr_a_cong_l; pose lem_contr_a_cong_r; pose lem_rcontr_a_to_contr_a;
                     pose lem_contr_a_ltup_0; pose lem_contr_a_ltup_1; pose lem_contr_a_ltup_2.

Lemma lem_contr_a_basic :
  forall x y, Contr_clc_a x y -> lterm_basic x -> False.
Proof.
  unfold lterm_basic; intros; yinversion H; yauto 2.
Qed.

Lemma lem_contr_a_preserves_is_ltup : forall x y, Contr_clc_a x y -> is_ltup x = true ->
                                                  is_ltup y = true.
Proof.
  intros.
  induction H; try yauto 1.
  invert_rcontr_clc_a.
  ydestruct H2; try yauto 1.
  repeat (ydestruct H; yintuition; try yauto 1).
  yauto 2.
Qed.

Lemma lem_contr_a_preserves_not_ltup : forall x y, Contr_clc_a x y -> is_ltup x = false ->
                                                   is_ltup y = false.
Proof.
  intros.
  induction H; try yauto 1.
  invert_rcontr_clc_a; yauto 1.
Qed.

Lemma lem_exp_a_preserves_not_ltup : forall x y, Contr_clc_a x y -> is_ltup y = false ->
                                                 is_ltup x = false.
Proof.
  intros.
  induction H; try yauto 1.
  invert_rcontr_clc_a; yintuition; yintuition; try yauto 1.
  invert_rcontr_S; yintuition; yintuition.
Qed.

Ltac invert_contr_clc_a :=
  match goal with
  | [ H : Contr_clc_a (_ @l _) _ |- _ ] =>  yinversion H; fold Contr_clc_a in *; yisolve
  end.

Lemma lem_contr_a_s_result_1 :
  forall ns x x' l1 l2,
    is_nonempty ns ->
    Contr_clc_a x x' ->
    Contr_clc_a (build_s_result ns x l1 l2) (build_s_result ns x' l1 l2).
Proof.
  apply lem_s_result_1; pose_contr_a; ycrush.
Qed.

Lemma lem_contr_a_ltup_inv :
  forall (x y : lterm) (l : list lterm) (w : lterm),
    Contr_clc_a (ltup x y l) w ->
    (exists x' : lterm, w = ltup x' y l /\ Contr_clc_a x x') \/
    (exists y' : lterm, w = ltup x y' l /\ Contr_clc_a y y') \/
    (exists (l1 l2 : list lterm) (z z' : lterm),
        l = l1 ++ z :: l2 /\ w = ltup x y (l1 ++ z' :: l2) /\ Contr_clc_a z z').
Proof.
  intros; yinversion H; yisolve.
  racrush.
Qed.

Lemma lem_contr_a_glue_l : forall x, R_glue_iterms_l Contr_clc_a x.
Proof.
  unfold R_glue_iterms_l.
  intros x x' y H.
  induction H; fold Contr_clc_a in *.
  destruct t1; try solve [ unfold RootContr_clc_a in *; simpl in *; yelles 1 ].
  destruct t2; try solve [ unfold RootContr_clc_a in *; simpl in *; yisolve ];
    simpl; pose_ctx_l; unfold Contr_clc_a in *; yelles 1.
  pose_ctx_l; unfold Contr_clc_a in *; yelles 1.
  pose_ctx_l; unfold Contr_clc_a in *; yelles 1.
  pose_ctx_l; unfold Contr_clc_a in *; yelles 1.
  pose_ctx_l; unfold Contr_clc_a in *; yelles 1.
  pose_ctx_l; unfold Contr_clc_a in *; yelles 1.
Qed.

Lemma lem_contr_a_glue_r : forall x, R_glue_iterms_r Contr_clc_a x.
Proof.
  unfold R_glue_iterms_l.
  intros x y x' H.
  induction H; fold Contr_clc_a in *.
  destruct t1; try solve [ unfold RootContr_clc_a in *; simpl in *; yelles 1 ].
  destruct t2; try solve [ unfold RootContr_clc_a in *; simpl in *; yisolve ];
    simpl; pose_ctx_l; unfold Contr_clc_a in *; yelles 2.
  pose_ctx_l; unfold Contr_clc_a in *; yelles 2.
  pose_ctx_l; unfold Contr_clc_a in *; yelles 2.
  pose_ctx_l; unfold Contr_clc_a in *; yelles 2.
  pose_ctx_l; unfold Contr_clc_a in *; yelles 2.
  pose_ctx_l; unfold Contr_clc_a in *; yelles 2.
Qed.

Lemma lem_contr_a_s_result_2 :
  forall ns x y y' l,
    is_ltup y = true ->
    lst_sum ns < length l ->
    length (tuple_of_lterm y) = length ns ->
    Contr_clc_a y y' ->
    Contr_clc_a (build_s_result ns x (tuple_of_lterm y) l)
                (build_s_result ns x (tuple_of_lterm y') l).
Proof.
  intros.
  assert (forall z, In z (tuple_of_lterm y) -> R_glue_iterms_l Contr_clc_a z).
  pose lem_contr_a_glue_l; ycrush.
  apply lem_s_result_2; pose lem_contr_a_ltup_inv; pose_contr_a; ycrush.
Qed.

Lemma lem_contr_a_s_result_3 :
  forall ns x l y y',
    is_ltup y = true ->
    lst_sum ns < length (tuple_of_lterm y) ->
    length l = length ns ->
    Contr_clc_a y y' ->
    Contr_clc_a (build_s_result ns x l (tuple_of_lterm y))
                (build_s_result ns x l (tuple_of_lterm y')).
Proof.
  intros.
  assert (forall z, In z (tuple_of_lterm y) -> R_glue_iterms_r Contr_clc_a z).
  pose lem_contr_a_glue_r; ycrush.
  apply lem_s_result_3; pose lem_contr_a_ltup_inv; pose_contr_a; ycrush.
Qed.

Lemma lem_contr_a_s2_result :
  forall n x y z z',
    is_ltup z = true ->
    Contr_clc_a z z' ->
    Contr_clc_a (x @l lterm_of_tuple (firstn n (tuple_of_lterm z)) @l
                   glue_iterms y (lterm_of_tuple (skipn n (tuple_of_lterm z))))
                (x @l lterm_of_tuple (firstn n (tuple_of_lterm z')) @l
                   glue_iterms y (lterm_of_tuple (skipn n (tuple_of_lterm z')))).
Proof.
  intros.
  assert (forall u, In u (tuple_of_lterm z) -> R_glue_iterms_r Contr_clc_a u).
  pose lem_contr_a_glue_r; ycrush.
  apply lem_s2_result; pose lem_contr_a_ltup_inv; pose_contr_a; ycrush.
Qed.

Lemma lem_contr_a_length :
  forall x y, is_ltup x = true -> is_ltup y = true ->
              Contr_clc_a x y -> length (tuple_of_lterm x) = length (tuple_of_lterm y).
Proof.
  induction x, y; try yelles 2.
  intros.
  yinversion H1.
  yinversion H2.
  fold Contr_clc_a in *; ycrush.
  fold Contr_clc_a in *; ycrush.
  fold Contr_clc_a in *; ycrush.
  induction l1; ycrush.
Qed.

Lemma lem_contr_a_ltup_extend :
  forall x y l x' y' l', Contr_clc_a (ltup x y l) (ltup x' y' l') ->
                         forall a, Contr_clc_a (ltup x y (a :: l)) (ltup x' y' (a :: l')).
Proof.
  intros.
  yinversion H; fold Contr_clc_a in *.
  ycrush.
  pose_contr_a; ycrush.
  pose_contr_a; ycrush.
  assert (Contr_clc_a (ltup x' y' ((a :: l0) ++ z :: l'0)) (ltup x' y' ((a :: l0) ++ z' :: l'0))).
  pose_contr_a; ycrush.
  ycrush.
Qed.

Lemma lem_red_a_implies_red_i_a : forall x y, Red_clc_a x y -> Red_clc_i_a x y.
Proof.
  unfold Red_clc_a, Red_clc_i_a, Contr_clc_i_a.
  intros x y H; induction H; pose_rt; ycrush.
Qed.

Lemma lem_contr_clc0_implies_contr_i_a :
  forall q1 q2, Contr_clc0 q1 q2 -> Contr_clc_i_a (itm q1) (itm q2).
Proof.
  pose lem_contr_clc0_implies_contr_clc.
  unfold Contr_clc_i_a, Contr_clc_i; pose_ctx_l; ycrush.
Qed.

Lemma lem_rcontr_a_implies_red_i_a : forall x y, RootContr_clc_a x y -> Red_clc_i_a x y.
Proof.
  unfold Red_clc_i_a, Contr_clc_i_a, Contr_clc_a; pose_rt; pose_ctx_l; ycrush.
Qed.

Lemma lem_red_i_a_refl : forall x, Red_clc_i_a x x.
Proof.
  unfold Red_clc_i_a; pose_rt; ycrush.
Qed.

Lemma lem_red_i_a_trans : forall x y z, Red_clc_i_a x y -> Red_clc_i_a y z -> Red_clc_i_a x z.
Proof.
  unfold Red_clc_i_a; pose_rt; ycrush.
Qed.

Lemma lem_contr_i_a_to_red_i_a : forall x y, Contr_clc_i_a x y -> Red_clc_i_a x y.
Proof.
  unfold Red_clc_i_a; pose_rt; ycrush.
Qed.

Lemma lem_red_i_a_cong_l : forall x y z, Red_clc_i_a x y -> Red_clc_i_a (x @l z) (y @l z).
Proof.
  unfold Red_clc_i_a; intros; induction H.
  unfold Contr_clc_i_a, Contr_clc_i, Contr_clc_a in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_i_a_cong_r : forall x y z, Red_clc_i_a x y -> Red_clc_i_a (z @l x) (z @l y).
Proof.
  unfold Red_clc_i_a; intros; induction H.
  unfold Contr_clc_i_a, Contr_clc_i, Contr_clc_a in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_i_a_ltup_0 : forall x x' y l, Red_clc_i_a x x' -> Red_clc_i_a (ltup x y l) (ltup x' y l).
Proof.
  unfold Red_clc_i_a; intros; induction H.
  unfold Contr_clc_i_a, Contr_clc_i, Contr_clc_a in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_i_a_ltup_1 : forall x y y' l, Red_clc_i_a y y' -> Red_clc_i_a (ltup x y l) (ltup x y' l).
Proof.
  unfold Red_clc_i_a; intros; induction H.
  unfold Contr_clc_i_a, Contr_clc_i, Contr_clc_a in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Lemma lem_red_i_a_ltup_2 : forall x y z z' l l', Red_clc_i_a z z' ->
                                                 Red_clc_i_a (ltup x y (l ++ z :: l'))
                                                             (ltup x y (l ++ z' :: l')).
Proof.
  unfold Red_clc_i_a; intros; induction H.
  unfold Contr_clc_i_a, Contr_clc_i, Contr_clc_a in *; pose_rt; pose_ctx_l; ycrush.
  pose_rt; ycrush.
  pose_rt; ycrush.
Qed.

Ltac pose_red_i_a := pose lem_rcontr_a_implies_red_i_a; pose lem_red_i_a_refl;
                     pose lem_red_i_a_trans; pose lem_contr_i_a_to_red_i_a;
                     pose lem_red_i_a_cong_l; pose lem_red_i_a_cong_r;
                     pose lem_red_i_a_ltup_0; pose lem_red_i_a_ltup_1; pose lem_red_i_a_ltup_2.

Lemma lem_rcontr_a_to_s :
  forall x y, RootContr_clc_a x y -> exists z, RootContr_clc_s x z /\ Red_clc_s y z.
Proof.
  intros.
  ydestruct x; yisolve; try solve [ pose_red_s; yelles 1 ].
  ydestruct x1; yisolve; try solve [ pose_red_s; yelles 1 ].
  ydestruct x1_1; yisolve; try solve [ pose_red_s; yelles 1 ].
  ydestruct x1_1_1; yisolve; try solve [ pose_red_s; yelles 1 ].
  yinversion H; simp_hyps.
  assert (ErasedEqv x1_2 x2).
  pose lem_red_s_implies_erased_eqv; pose_erased_eqv; ycrush.
  pose_red_s; ycrush.
  yinversion H; simp_hyps; pose_red_s; ycrush.
  yinversion H; simp_hyps; pose_red_s; ycrush.
Qed.

(* lemma 17 *)
Lemma lem_contr_a_to_s :
  forall x y, Contr_clc_a x y -> exists z, Contr_clc_s x z /\ Red_clc_s y z.
Proof.
  intros x y H.
  induction H; try solve [ pose_contr_s; pose_red_s; yelles 1 ].
  pose lem_rcontr_a_to_s; pose_contr_s; ycrush.
Qed.

Lemma lem_contr_a_to_erased_eqv :
  forall x y, Contr_clc_a x y -> ErasedEqv x y.
Proof.
  pose lem_contr_a_to_s; pose lem_red_s_implies_erased_eqv; pose_erased_eqv;
    pose lem_contr_s_to_red_s; ycrush.
Qed.

Lemma lem_contr_a_all_pairs_erased_eqv :
  forall y y', is_ltup y = true -> Contr_clc_a y y' ->
               All_pairs (tuple_of_lterm y) ErasedEqv ->
               All_pairs (tuple_of_lterm y') ErasedEqv.
Proof.
  intros y y'; apply lem_all_pairs_erased_eqv; pose lem_contr_a_to_erased_eqv;
    pose lem_contr_a_ltup_inv; pose_contr_a; ycrush.
Qed.

Lemma lem_contr_a_snf : forall x y, Contr_clc_a x y -> sNF x -> False.
Proof.
  intros x y H.
  induction H; fold Contr_clc_a in *.
  pose lem_rcontr_a_to_s; pose lem_contr_s_snf; pose lem_rcontr_s_to_contr_s; ycrush.
  Reconstr.hyelles 3 (@IHCtxClose_l)
		   (@subterms.subterm_lapp_r, @subterms.subterm_lapp_l, @subterms.subterm_eq)
		   sNF.
  Reconstr.hyelles 3 (@IHCtxClose_l)
		   (@subterms.subterm_lapp_r, @subterms.subterm_lapp_l, @subterms.subterm_eq)
		   sNF.
  Reconstr.hcrush (@IHCtxClose_l)
		  (@subterms.subterm_ltup_1, @subterms.subterm_ltup_0, @subterms.subterm_eq)
		  sNF.
  Reconstr.hsimple (@IHCtxClose_l)
		   (@subterms.subterm_ltup_1)
		   (@sred.sNF).
  Reconstr.hsimple (@IHCtxClose_l)
		   (@subterms.lem_subterm_ltup_2_prime)
		   (@sred.sNF).
Qed.
