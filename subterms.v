
Require Import general.
Require Import iterms.
Require Import lterms.

Inductive Subterm_i : iterm -> iterm -> Prop :=
| subterm_i_eq : forall x, Subterm_i x x
| subterm_i_lapp_l : forall x y1 y2, Subterm_i x y1 -> Subterm_i x (y1 @i y2)
| subterm_i_lapp_r : forall x y1 y2, Subterm_i x y2 -> Subterm_i x (y1 @i y2).

Ltac pose_subterm_i := pose subterm_i_eq; pose subterm_i_lapp_l; pose subterm_i_lapp_r.

Inductive Subterm : lterm -> lterm -> Prop :=
| subterm_i : forall x y, Subterm_i x y -> Subterm (itm x) (itm y)
| subterm_eq : forall x, Subterm x x
| subterm_lapp_l : forall x y1 y2, Subterm x y1 -> Subterm x (y1 @l y2)
| subterm_lapp_r : forall x y1 y2, Subterm x y2 -> Subterm x (y1 @l y2)
| subterm_ltup_0
  : forall x y1 y2 ys, Subterm x y1 -> Subterm x (ltup y1 y2 ys)
| subterm_ltup_1 : forall x y1 y2 ys, Subterm x y2 -> Subterm x (ltup y1 y2 ys)
| subterm_ltup_2 : forall x y1 y2 ys z, In z ys -> Subterm x z -> Subterm x (ltup y1 y2 ys).

Lemma lem_subterm_ltup_2_prime :
  forall a x y z l l', Subterm a z -> Subterm a (ltup x y (l ++ z :: l')).
Proof.
  pose subterm_ltup_2; eauto with datatypes.
Qed.

Ltac pose_subterm := pose subterm_i; pose subterm_eq; pose subterm_lapp_l; pose subterm_lapp_r;
                     pose subterm_ltup_0; pose subterm_ltup_1; pose subterm_ltup_2;
                     pose lem_subterm_ltup_2_prime.

Lemma lem_subterm_i_app : forall x y z, Subterm_i (x @i y) z -> Subterm_i x z /\ Subterm_i y z.
Proof.
  induction z; try yelles 1.
  intro H; yinversion H; pose_subterm_i; ycrush.
Qed.

Lemma lem_subterm_i_trans : forall x y z, Subterm_i x y -> Subterm_i y z -> Subterm_i x z.
Proof.
  induction x; induction y;
    solve [ yelles 1 |
            intros z H; yinversion H; pose lem_subterm_i_app; pose_subterm_i; ycrush ].
Qed.

Lemma lem_subterm_app : forall x y z, Subterm (x @l y) z -> Subterm x z /\ Subterm y z.
Proof.
  intros x y z; lterm_induction z; try yelles 1.
  intro H; yinversion H; pose_subterm; ycrush.
  intro H; yinversion H.
  pose_subterm; ycrush.
  pose_subterm; ycrush.
  assert (Subterm x z /\ Subterm y z) by auto.
  pose_subterm; ycrush.
  intros z0 H; yinversion H; pose_subterm; ycrush.
Qed.

Lemma lem_subterm_ltup : forall x y l z, Subterm (ltup x y l) z ->
                                         Subterm x z /\ Subterm y z /\
                                         (forall u, In u l -> Subterm u z).
Proof.
  intros until z; lterm_induction z; simp_hyps; try yelles 1.
  pose_subterm; yelles 2.
  intro H5; yinversion H5; pose_subterm; try yelles 1.
  assert (Subterm x z /\ Subterm y z /\ (forall u : lterm, In u l -> Subterm u z)) by auto.
  yelles 1.
  intros z0 HH; yinversion HH; pose_subterm; ycrush.
Qed.

Lemma lem_subterm_trans : forall x y z, Subterm x y -> Subterm y z -> Subterm x z.
Proof.
  Ltac mytac z :=
    intro z; lterm_induction z; simp_hyps; pose_subterm; try iauto 1; try iauto 2.
  induction x.
  induction y; try yelles 1.
  pose lem_subterm_i_trans; mytac z.
  mytac z.
  mytac z.
  mytac z.
  pose lem_subterm_app; simp_hyps; iauto 1.
  pose lem_subterm_ltup; simp_hyps; iauto 1.
  mytac z.
  pose lem_subterm_app; simp_hyps; iauto 1.
  pose lem_subterm_ltup; simp_hyps; iauto 1.
  mytac z.
  pose lem_subterm_app; simp_hyps; iauto 1.
  pose lem_subterm_ltup; simp_hyps; iauto 1.
  mytac z.
  pose lem_subterm_app; simp_hyps; iauto 1.
  pose lem_subterm_ltup; simp_hyps; iauto 1.
  mytac z.
  pose lem_subterm_app; simp_hyps; iauto 1.
  pose lem_subterm_ltup; simp_hyps; iauto 1.
  mytac z.
  intros z H; yinversion H.
  pose lem_subterm_app; simp_hyps; iauto 1.
  pose lem_subterm_app; simp_hyps; iauto 1.
  pose lem_subterm_ltup; simp_hyps; iauto 1.
  mytac z.
  pose lem_subterm_app; simp_hyps; iauto 1.
  pose lem_subterm_ltup; simp_hyps; iauto 1.
  mytac z.
  pose lem_subterm_app; simp_hyps; iauto 1.
  pose lem_subterm_ltup; simp_hyps; iauto 1.
  mytac z.
  pose lem_subterm_app; simp_hyps; iauto 1.
  pose lem_subterm_ltup; simp_hyps; iauto 1.
  mytac z.
  pose lem_subterm_app; simp_hyps; iauto 1.
  pose lem_subterm_ltup; simp_hyps; iauto 1.
Qed.

Lemma lem_subterm_lterm_of_tuple :
  forall l t u, Subterm t u -> In u l -> Subterm t (lterm_of_tuple l).
Proof.
  induction l.
  ycrush.
  ydestruct l; pose_subterm; ycrush.
Qed.
