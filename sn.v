(* This file contains the formalisation of the proof that s-reduction
   is strongly normalising (lemma 5) *)

Require Import general.
Require Import lterms.

Fixpoint lst_lsize (l : list lterm) : nat :=
  match l with
  | nil => 0
  | h :: l' => lsize h + lst_lsize l'
  end.

Lemma ltup_lsize : forall x y l, lsize (ltup x y l) = lsize x + lsize y + lst_lsize l.
Proof.
  induction l; simpl; yisolve.
Qed.

Lemma lem_glue_iterms_lsize : forall x y, lsize (glue_iterms x y) = lsize x + lsize y.
Proof.
  destruct x, y; auto.
Qed.

Lemma lsize_lttp : forall a l, lsize (lterm_of_tuple (a :: l)) = lsize a + lst_lsize l.
Proof.
  induction l.
  yisolve.
  pose ltup_lsize.
  unfold lterm_of_tuple.
  assert (lst_lsize (a0 :: l) = lsize a0 + lst_lsize l) by yisolve.
  rewrite H; rewrite e; omega.
Qed.

Lemma lsize_lterm_of_tuple : forall l, lsize (lterm_of_tuple l) = lst_lsize l.
Proof.
  pose lsize_lttp; destruct l; yisolve.
Qed.

Lemma lsize_tuple_of_lterm : forall t, lst_lsize (tuple_of_lterm t) = lsize t.
Proof.
  induction t; simpl; try yelles 1.
  omega.
  fold lst_lsize; omega.
Qed.

Fixpoint lst2_lsize (l : list (list lterm)) : nat :=
  match l with
  | nil => 0
  | h :: l' => lst_lsize h + lst2_lsize l'
  end.

Lemma lsize_build_ys :
  forall ys zs, lst_lsize (build_ys ys zs) <= lst_lsize ys + lst2_lsize zs.
Proof.
  induction ys; destruct zs; simpl in *; try omega.
  rewrite lem_glue_iterms_lsize.
  rewrite (lsize_lterm_of_tuple l).
  generalize (IHys zs).
  omega.
Qed.

Lemma lsize_split : forall ns l, lst2_lsize (split_in_groups ns l) = lst_lsize l.
Proof.
  induction ns; simpl.
  yisolve.
  induction a.
  simpl; yisolve.
  induction l; simpl; yisolve.
  induction ns.
  simpl; yisolve.
  simpl; yelles 1.
  generalize (IHa l).
  omega.
Qed.

Lemma lsize_s_result :
  forall ns x l1 l2, (forall k, In k ns -> k > 0) ->
                     lsize (build_s_result ns x l1 l2) <= lsize x + lst_lsize l1 + lst_lsize l2.
Proof.
  intros.
  assert (forall n t, t = split_in_groups ns l2 -> n = lst2_lsize t ->
                    lsize (build_s_result ns x l1 l2) <= lsize x + lst_lsize l1 + lst_lsize l2).
  induction n.
  destruct ns.
  unfold build_s_result.
  simpl.
  intros.
  subst.
  pose (lsize_lterm_of_tuple l2).
  omega.
  unfold build_s_result.
  simpl.
  assert (n > 0).
  Reconstr.hexhaustive 0 (@H)
	(@Coq.Lists.List.not_in_cons, @Coq.omega.OmegaLemmas.fast_Zred_factor6, @Coq.Arith.Gt.gt_0_eq)
	(@Coq.Init.Peano.gt).
  intros.
  subst.
  simpl in *.
  assert (lst_lsize (firstn n l2) = 0) by omega.
  destruct (split_in_groups ns (skipn n l2)).
  rewrite lsize_lterm_of_tuple.
  omega.
  simpl.
  rewrite lsize_lterm_of_tuple.
  rewrite lsize_lterm_of_tuple.
  generalize (lsize_build_ys l1 (l :: l0)).
  omega.
  intros.
  unfold build_s_result.
  assert (lst_lsize l2 = S n).
  generalize (lsize_split ns l2).
  yelles 1.
  rewrite <- H0.
  destruct t.
  simpl; omega.
  destruct t.
  simpl in *.
  assert (lst_lsize l = lst_lsize l2) by omega.
  rewrite lsize_lterm_of_tuple.
  omega.
  simpl.
  rewrite lsize_lterm_of_tuple.
  rewrite lsize_lterm_of_tuple.
  generalize (lsize_build_ys l1 (l0 :: t)).
  simpl in *.
  omega.
  yelles 1.
Qed.

Lemma lem_lst_lsize_first_skip :
  forall n l, lst_lsize (firstn n l) + lst_lsize (skipn n l) = lst_lsize l.
Proof.
  induction n.
  yintuition.
  intros; simpl.
  ydestruct l.
  yintuition.
  simpl; generalize (IHn l0); omega.
Qed.

Lemma lsize_s2_result :
  forall n x y l, n > 0 ->
                  lsize (x @l (lterm_of_tuple (firstn n l)) @l
                           (y @l lterm_of_tuple (skipn n l))) <= lsize x + lsize y + lst_lsize l.
Proof.
  induction n.
  yintuition.
  intros.
  simpl.
  ydestruct l.
  simpl; omega.
  rewrite lsize_lterm_of_tuple.
  rewrite lsize_lterm_of_tuple.
  simpl.
  generalize (lem_lst_lsize_first_skip n l0).
  omega.
Qed.

Lemma lem_rcontr_clc_s_decrease : forall x y, RootContr_clc_s x y -> lsize y < lsize x.
Proof.
  induction x; try solve [ intros y HH; yinversion HH; yelles 1 ].
  intros.
  ydestruct x1; try yelles 1.
  ydestruct x1_1; try yelles 1.
  simpl in *; subst; omega.
  ydestruct x1_1_1; try yelles 1.
  assert (y = x1_2 \/ y = x2) by eauto using invert_rcontr_c.
  destruct H0; simpl; subst; omega.
  assert (y = x1_2 \/ y = x2) by eauto using invert_rcontr_c.
  destruct H0; simpl; subst; omega.
  simpl in *; simp_hyps; subst.
  assert (lsize (build_s_result l x1_1_2 (tuple_of_lterm x1_2) (tuple_of_lterm x2)) <=
          lsize x1_1_2 + lst_lsize (tuple_of_lterm x1_2) + lst_lsize (tuple_of_lterm x2)).
  eauto using lsize_s_result.
  rewrite lsize_tuple_of_lterm in H7.
  rewrite lsize_tuple_of_lterm in H7.
  omega.
  invert_rcontr_clc_s.
  repeat (ydestruct H0; yintuition; try yelles 1).
  yintuition.
  yinversion H.
  rewrite lem_glue_iterms_lsize.
  generalize (lsize_s2_result x x0 x1 (tuple_of_lterm x3)); simpl.
  generalize (lsize_tuple_of_lterm x3).
  omega.
Qed.

Lemma lem_contr_clc_s_decrease : forall x y, Contr_clc_s x y -> lsize y < lsize x.
Proof.
  unfold Contr_clc_s.
  intros x y H; induction H; simpl; try omega.
  auto using lem_rcontr_clc_s_decrease.
  induction l; simpl; omega.
Qed.

(* lemma 5 *)
Lemma lem_contr_clc_s_sn : well_founded (fun x y => Contr_clc_s y x).
Proof.
  unfold well_founded.
  assert (forall n a, lsize a <= n -> Acc (fun x y : lterm => Contr_clc_s y x) a).
  induction n; intros; constructor; intros;
    assert (lsize y < lsize a) by eauto using lem_contr_clc_s_decrease.
  omega.
  assert (lsize y <= n) by omega; eauto.
  eauto.
Qed.
