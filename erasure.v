(* This file contains the definition of the relation \succ from the
   paper (t \succ q holds if *all* erasures of t are identical with q)
   and the formalisation of its basic properties *)

Require Import general.
Require Import list_facts.
Require Import iterms.
Require Import lterms.

(* `Erasure t q' holds if *all* erasures of t are identical with q *)
Inductive Erasure : lterm -> iterm -> Prop :=
| erasure_itm : forall x, Erasure (itm x) x
| erasure_c1 : Erasure C1 C
| erasure_c2 : Erasure C2 C
| erasure_t1 : Erasure T1 T
| erasure_f1 : Erasure F1 F
| erasure_i1 : Erasure I1 I
| erasure_k1 : Erasure K1 K
| erasure_s1 : forall l, Erasure (S1 l) Si
| erasure_s2 : forall n, Erasure (S2 n) Si
| erasure_lapp : forall x y x' y', Erasure x x' -> Erasure y y' -> Erasure (x @l y) (x' @i y')
| erasure_ltup : forall x y l z, Erasure x z -> Erasure y z -> (forall u, In u l -> Erasure u z) ->
                                 Erasure (ltup x y l) z.

Ltac pose_erasure := pose erasure_itm; pose erasure_c1; pose erasure_c2; pose erasure_t1;
                     pose erasure_f1; pose erasure_k1; pose erasure_s1; pose erasure_lapp;
                     pose erasure_ltup.
Ltac erasure_tac n := pose_erasure; yauto n.

Ltac invert_erasure :=
  repeat match goal with
         | [ H : Erasure C1 _ |- _ ] => yinversion H
         | [ H : Erasure C2 _ |- _ ] => yinversion H
         | [ H : Erasure T1 _ |- _ ] => yinversion H
         | [ H : Erasure F1 _ |- _ ] => yinversion H
         | [ H : Erasure K1 _ |- _ ] => yinversion H
         | [ H : Erasure (S1 _) _ |- _ ] => yinversion H
         | [ H : Erasure (S2 _) _ |- _ ] => yinversion H
         | [ H : Erasure (_ @l _) _ |- _ ] => yinversion H
         | [ H : Erasure (ltup _ _ _) _ |- _ ] => yinversion H
         end.

Ltac invert_sterm_erasure n :=
  lazymatch n with
  | 0 => yisolve
  | S ?k =>
    try match goal with
        | [ H1 : Sterm (?t @l _), H2 : Erasure ?t _ |- _ ] =>
          assert (Sterm t) by iauto 1;
          yinversion H2; try iauto 1
        end;
    invert_sterm_erasure k
  end.

Lemma lem_erasure_leftmost : forall t q, Erasure t q -> q = erase t.
Proof.
  induction t; try yelles 1.
  intros q H; yinversion H; ycrush.
Qed.

Lemma lem_erasure_eqv : forall t t' q q', Erasure t q -> Erasure t' q' -> ErasedEqv t t' ->
                                          Eqv_clc0 q q'.
Proof.
  unfold ErasedEqv; intros; pose lem_erasure_leftmost; pose lem_eqv_clc_to_eqv_clc0; ycrush.
Qed.

Lemma lem_erasure_lterm_of_tuple :
  forall l y, is_nonempty l -> (forall x, In x l -> Erasure x y) -> Erasure (lterm_of_tuple l) y.
Proof.
  induction l.
  ycrush.
  intros; simpl in *.
  ydestruct l.
  ycrush.
  pose_erasure; ycrush.
Qed.

Lemma lem_erasure_lterm_of_tuple_inv :
  forall l y, Erasure (lterm_of_tuple l) y -> (forall x, In x l -> Erasure x y).
Proof.
  induction l.
  ycrush.
  ydestruct l; ycrush.
Qed.

Lemma lem_erasure_glue_iterms : forall x1 x2 q1 q2, Erasure x1 q1 -> Erasure x2 q2 ->
                                                    Erasure (glue_iterms x1 x2) (q1 @i q2).
Proof.
  destruct x1, x2; try solve [ pose_erasure; yelles 1 ].
  ycrush.
Qed.

Lemma lem_erasure_build_ys :
  forall ys zs y z, (forall x, In x ys -> Erasure x y) ->
                    (forall l, In l zs -> is_nonempty l) ->
                    (forall x l, In l zs -> In x l -> Erasure x z) ->
                    forall x, In x (build_ys ys zs) -> Erasure x (y @i z).
Proof.
  induction ys.
  ycrush.
  intros; simpl in *.
  ydestruct zs.
  ycrush.
  simpl in *.
  ydestruct H2.
  subst.
  assert (Erasure (lterm_of_tuple l) z).
  pose lem_erasure_lterm_of_tuple; pose_erasure; yelles 2.
  apply lem_erasure_glue_iterms; pose_erasure; ycrush.
  pose_erasure; ycrush.
Qed.

Lemma lem_s_result_erasure :
  forall ns x ys zs x' y' z', is_nonempty ys ->
    is_nonempty ns -> (forall n, In n ns -> n > 0) -> (lst_sum ns < length zs) ->
    Erasure x x' -> (forall y, In y ys -> Erasure y y') -> (forall z, In z zs -> Erasure z z') ->
    Erasure (build_s_result ns x ys zs) (x' @i z' @i (y' @i z')).
Proof.
  unfold build_s_result.
  intros.
  ydestruct ns.
  ycrush.
  pose (lem_split_result n ns zs).
  simp_hyps.
  assert (forall x y, In y (x0 :: x1 :: x2) -> In x y -> In x zs).
  pose (lem_split_preserves_elements (n :: ns) zs).
  rewrite H6 in *; eauto.
  assert (forall x, In x x0 -> In x zs) by ycrush.
  assert (forall x y, In x y -> In y (x1 :: x2) -> In x zs) by ycrush.
  rewrite H6 in *.
  assert (is_nonempty x0).
  pose (lem_split_nonempty (n :: ns) zs).
  rewrite H6 in *; ycrush.
  assert (forall (x : lterm) (l : list lterm), In l (x1 :: x2) -> In x l -> Erasure x z') by ycrush.
  assert (forall l : list lterm, In l (x1 :: x2) -> is_nonempty l).
  pose (lem_split_nonempty (n :: ns) zs).
  rewrite H6 in *; ycrush.
  assert (forall x : lterm, In x (build_ys ys (x1 :: x2)) -> Erasure x (y' @i z')).
  pose (lem_erasure_build_ys ys (x1 :: x2) y' z'); ycrush.
  assert (Erasure (lterm_of_tuple x0) z').
  pose (lem_erasure_lterm_of_tuple x0); ycrush.
  assert (is_nonempty (build_ys ys (x1 :: x2))).
  ydestruct ys; ycrush.
  assert (Erasure (lterm_of_tuple (build_ys ys (x1 :: x2))) (y' @i z')).
  pose (lem_erasure_lterm_of_tuple (build_ys ys (x1 :: x2)) (y' @i z')); ycrush.
  pose_erasure; ycrush.
Qed.

Lemma lem_s2_result_erasure :
  forall n x y zs x' y' z',
    n > 0 -> n < length zs ->
    Erasure x x' -> Erasure y y' -> (forall z, In z zs -> Erasure z z') ->
    Erasure
      (x @l lterm_of_tuple (firstn n zs) @l
         glue_iterms y (lterm_of_tuple (skipn n zs)))
      (x' @i z' @i (y' @i z')).
Proof.
  intros.
  assert (is_nonempty (firstn n zs)) by ycrush.
  assert (is_nonempty (skipn n zs)).
  pose (lem_skipn_nonempty n zs); ycrush.
  assert (Erasure (lterm_of_tuple (firstn n zs)) z').
  pose (lem_firstn_preserves_elements n zs).
  pose (lem_erasure_lterm_of_tuple (firstn n zs) z').
  ycrush.
  assert (Erasure (lterm_of_tuple (skipn n zs)) z').
  pose (lem_skipn_preserves_elements n zs).
  pose (lem_erasure_lterm_of_tuple (skipn n zs) z').
  ycrush.
  pose lem_erasure_glue_iterms; pose_erasure; ycrush.
Qed.

Lemma lem_erasure_equal : forall x q, Erasure x q -> All_pairs (tuple_of_lterm x) ErasedEqv.
Proof.
  unfold All_pairs, ErasedEqv.
  intros.
  ydestruct x.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  ycrush.
  yinversion H; yintuition; pose lem_erasure_leftmost; ycrush.
Qed.

Lemma lem_erasure_tuple : forall x q, Erasure x q ->
                                      (forall y : lterm, In y (tuple_of_lterm x) ->
                                                         Erasure y q).
Proof.
  destruct x; ycrush.
Qed.

Lemma lem_all_pairs_erasure : forall l q, (forall x, In x l -> Erasure x q) ->
                                          All_pairs l ErasedEqv.
Proof.
  induction l.
  ycrush.
  unfold All_pairs in *; simpl.
  unfold ErasedEqv in *.
  yintros.
  assert (Erasure x q) by ycrush.
  assert (Erasure y q) by ycrush.
  assert (q = erase x).
  pose lem_erasure_leftmost; ycrush.
  assert (q = erase y).
  pose lem_erasure_leftmost; ycrush.
  ycrush.
Qed.
